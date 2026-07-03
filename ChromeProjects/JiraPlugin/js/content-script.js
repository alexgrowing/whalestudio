document.onkeyup = function(event){
    if (event.ctrlKey){
        var button2Click = null;
        if (event.keyCode==78) {
            button2Click = document.getElementById("next-issue")
        } else if (event.keyCode == 80) {
            button2Click = document.getElementById("previous-issue")
        }

        if (button2Click != null) {
            button2Click.click();
        }
    }
}