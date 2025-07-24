// VecBook JavaScript Functions using jQuery

// Global variables
let targetStrings = [];
let testStrings = [];

// Initialize the page when DOM is ready
$(document).ready(function() {
    console.log('VecBook interface loaded');
    updateDataIndexes();
    
    // Set up event handlers using jQuery
    setupEventHandlers();
});

// Set up event handlers
function setupEventHandlers() {
    // Add button click handlers
    $('.add-btn').on('click', function() {
        const type = $(this).closest('.target-strings, .test-strings').hasClass('target-strings') ? 'target' : 'test';
        addString(type);
    });
    
    // Calculate button click handler
    $('.calculate-btn').on('click', function() {
        calculateSimilarity();
    });
    
    // Remove button click handlers (using event delegation for dynamically added elements)
    $(document).on('click', '.remove-btn', function() {
        const type = $(this).closest('#target-inputs, #test-inputs').attr('id').replace('-inputs', '');
        removeString($(this), type);
    });
}

// Add a new string input field
function addString(type) {
    const $container = $(`#${type}-inputs`);
    const newIndex = $container.children().length;
    
    const $inputGroup = $(`
        <div class="input-group">
            <input type="text" class="string-input" placeholder="Enter ${type} string ${newIndex + 1}" data-index="${newIndex}">
            <button type="button" class="remove-btn">Remove</button>
        </div>
    `);
    
    $container.append($inputGroup);
    updateDataIndexes();
}

// Remove a string input field
function removeString($button, type) {
    const $container = $(`#${type}-inputs`);
    const $inputGroup = $button.closest('.input-group');
    
    // Don't remove if it's the last input
    if ($container.children().length > 1) {
        $inputGroup.remove();
        updateDataIndexes();
    }
}

// Update data-index attributes for all inputs
function updateDataIndexes() {
    $('#target-inputs .string-input').each(function(index) {
        $(this).attr('data-index', index);
    });
    
    $('#test-inputs .string-input').each(function(index) {
        $(this).attr('data-index', index);
    });
}

// Collect all string values from inputs
function collectStrings(type) {
    const strings = [];
    
    $(`#${type}-inputs .string-input`).each(function() {
        const value = $(this).val().trim();
        if (value) {
            strings.push(value);
        }
    });
    
    return strings;
}

// Calculate similarity using the VecBook API
function calculateSimilarity() {
    console.log('Calculating similarity...');
    
    // Collect target and test strings
    targetStrings = collectStrings('target');
    testStrings = collectStrings('test');
    
    // Validate inputs
    if (targetStrings.length === 0) {
        showError('Please enter at least one target string');
        return;
    }
    
    if (testStrings.length === 0) {
        showError('Please enter at least one test string');
        return;
    }
    
    console.log('Target strings:', targetStrings);
    console.log('Test strings:', testStrings);
    
    // Show loading state
    showLoading();
    hideError();
    
    // Call the cosine-similarity endpoint
    callAPI('/cosine-similarity', {
        target_strings: targetStrings,
        test_strings: testStrings
    })
    .done(function(response) {
        console.log('API response:', response);
        
        if (response.results && response.results.length > 0) {
            // Transform the results to match our display format
            const formattedResults = response.results.map(result => ({
                test_string: result.text,
                similarity: parseFloat(result.cosine_similarity)
            }));
            
            showResults(formattedResults);
        } else {
            showError('No results returned from the server');
        }
    })
    .fail(function(xhr, status, error) {
        console.error('API call failed:', error);
        let errorMessage = 'Failed to calculate similarity';
        
        if (xhr.responseJSON && xhr.responseJSON.detail) {
            errorMessage = xhr.responseJSON.detail;
        } else if (xhr.status === 0) {
            errorMessage = 'Unable to connect to server. Please check if the VecBook server is running.';
        } else if (xhr.status === 404) {
            errorMessage = 'API endpoint not found. Please check server configuration.';
        } else if (xhr.status >= 500) {
            errorMessage = 'Server error. Please try again later.';
        }
        
        showError(errorMessage);
    })
    .always(function() {
        hideLoading();
    });
}

// Display results
function showResults(results) {
    const $resultsSection = $('#results-section');
    const $resultsContainer = $('#results-container');
    
    // Clear previous results
    $resultsContainer.empty();
    
    // Sort results by similarity score (highest first)
    const sortedResults = results.sort((a, b) => b.similarity - a.similarity);
    
    // Add new results
    $.each(sortedResults, function(index, result) {
        const $resultItem = $(`
            <div class="result-item">
                <span class="test-string-text">${escapeHtml(result.test_string)}</span>
                <span class="similarity-score">${(result.similarity * 100).toFixed(1)}%</span>
            </div>
        `);
        
        $resultsContainer.append($resultItem);
    });
    
    // Show results section
    $resultsSection.show();
    
    // Scroll to results with smooth animation
    $('html, body').animate({
        scrollTop: $resultsSection.offset().top - 20
    }, 500);
}

// API call function
function callAPI(endpoint, data) {
    return $.ajax({
        url: endpoint,
        method: 'POST',
        contentType: 'application/json',
        data: JSON.stringify(data),
        dataType: 'json'
    });
}

// Utility function to show loading state
function showLoading() {
    $('.calculate-btn').prop('disabled', true).text('Calculating...');
}

// Utility function to hide loading state
function hideLoading() {
    $('.calculate-btn').prop('disabled', false).text('Calculate Similarity');
}

// Utility function to show error message
function showError(message) {
    // Create error alert if it doesn't exist
    if ($('#error-alert').length === 0) {
        const $errorAlert = $(`
            <div id="error-alert" class="error-alert" style="display: none;">
                <span class="error-message"></span>
                <button type="button" class="error-close">&times;</button>
            </div>
        `);
        $('.container').prepend($errorAlert);
        
        // Set up close button
        $(document).on('click', '.error-close', function() {
            $('#error-alert').fadeOut();
        });
    }
    
    $('#error-alert .error-message').text(message);
    $('#error-alert').fadeIn();
}

// Utility function to hide error message
function hideError() {
    $('#error-alert').fadeOut();
}

// Utility function to escape HTML to prevent XSS
function escapeHtml(text) {
    const div = document.createElement('div');
    div.textContent = text;
    return div.innerHTML;
}
