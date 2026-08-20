using Test

@testset "CthulhuWeb" begin
    @testset "core" begin
        include("core.jl")
    end
    @testset "server" begin
        include("server.jl")
    end
end
