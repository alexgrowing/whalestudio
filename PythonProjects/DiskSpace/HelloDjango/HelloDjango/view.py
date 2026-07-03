from django.http import HttpResponse

def hello(request):
    return HttpResponse("Hello Django! %s" % (request.GET['abc']) )