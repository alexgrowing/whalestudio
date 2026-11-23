import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.RhoFrob

open UpperTheory.V.Z.Kato.Joint

theorem UpperTheory.V.Z.Kato.Joint.mono :
    UpperTheory.V.Z.Kato.Joint.Mono := by
  intro l _ Ω _ _ c c' h
  refine ⟨?_, ?_, ?_⟩
  · rintro W y S' ⟨h1, h2, h3, h4, h5⟩
    refine ⟨fun s i j => h (h1 s i j), h2, fun s i => h (h3 s i), h4, fun n hn w hw hd ψ hk hs => ?_⟩
    obtain ⟨Y, P, u, b, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h5 n hn w hw hd ψ hk hs
    refine ⟨Y, P, u, b, a1, fun s x i => h (a2 s x i), h a3, a4, fun i => h (a5 i), a6, a7, a8, fun q hq hl => ?_⟩
    obtain ⟨B, hB, t, ht, ht'⟩ := a9 q hq hl
    exact ⟨B, hB, t, fun x i => h (ht x i), ht'⟩
  · rintro A ν Z ⟨h1, h2, h3⟩
    exact ⟨h1, fun r => ⟨fun s x => h ((h2 r).1 s x), (h2 r).2⟩, h3⟩
  · rintro A Z j m₀ c₀ Rhs ⟨ζ, hζ, H⟩
    refine ⟨ζ, hζ, fun m hm => ?_⟩
    obtain ⟨ι, inst, P, o, ⟨p1, p2, p3, p4, p5⟩, hc⟩ := H m hm
    exact ⟨ι, inst, P, o, ⟨p1, p2, fun i => h (p3 i), p4, p5⟩, hc⟩
