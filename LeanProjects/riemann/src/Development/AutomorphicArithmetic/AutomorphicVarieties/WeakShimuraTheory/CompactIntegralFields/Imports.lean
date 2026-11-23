import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ConjTrans
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ConTrace
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Pur
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.MapRepComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.CharpolyMapRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.AmbZero

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.main :
    CohomologyHyp → UpperTheory.V.Published.FerreroWashington → SeedII → SeedIII → PMEx → UpperTheory.V.Aut.Sp4In := by
  intro hP hFW h2 h3 hPM Ω _ _ _ h t hB l _ c e _ he0 het ψ hψ D hD hcase
  have hctx : Ctx2 D ∨ Ctx3 D :=
    hcase.imp (fun hc => ⟨hD, h, t, e, ψ, hB, he0, het, hψ, hc.1, hc.2⟩)
      (fun hc => ⟨hD, h, t, e, ψ, hB, he0, het, hψ, hc.1, hc.2⟩)
  obtain ⟨ι⟩ := (UpperTheory.V.Ws.ambZero l).2
  have hA := UpperTheory.V.Ws.thmA hP hFW h2 h3 hPM D hctx ι
  have hcon : Con D := fun 𝔞 hch r u hK hS =>
    UpperTheory.V.Ws.con D hD ι 𝔞 hch r u hK (hA 𝔞 r u hK hS) hS
  have hpur : Pur D ι := fun 𝔞 e' he' r u hK hS =>
    UpperTheory.V.Ws.pur D hD ι 𝔞 e' he' r (hA 𝔞 r u hK hS)
  have haut : Autm D ι := fun 𝔞 e' he' r u hK hI =>
    UpperTheory.V.Ws.aut D hD ι 𝔞 e' he' r u hK (hA 𝔞 r u hK (Or.inl hI)) hI
  obtain ⟨hF, hN, hAll⟩ := UpperTheory.V.Ws.sp4Of hP D hD ι hcon hpur haut
  exact ⟨hF, hN, ι, hAll⟩
