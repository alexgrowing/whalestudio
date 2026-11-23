import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.ROrdAway
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Rwwd
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Monosep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharPolCharCongr

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial ValuativeRel
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.SmGL UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd
open private rep_retr iwahori_level_zero_eq from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.ROrdAway

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.GalN.V.rw_of_ordForm (PH : HypothesesH) (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ξ : G F Ω →* (Qbar l)ˣ) (s c m a π r)
    (H : OrdForm ι ξ s c m a π r) : UpperTheory.GalN.V.RW ι r := by
  have P := PH.toClassicalTheorems
  refine UpperTheory.GalN.V.L.rwwd F Ω l ι 2 r H.cont fun w hl A h => ?_
  obtain ⟨χ, hχ⟩ := H.pol
  obtain ⟨-, wt, HT, -, -, hall⟩ := UpperTheory.GalN.V.exRN (exR PH) F Ω l ι 2 one_le_two π χ H.reg hχ
  have hG := hall r H.cont H.att
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := locCompR P F 2 π w
  obtain ⟨rc, hrc⟩ := P.exists_rec h
  refine hG.ratio w hl A h rc hrc σ hσ ?_
  by_cases hc : c w = 0
  · obtain ⟨v, hv, hf⟩ := H.sph w hc
    obtain ⟨T, hT, hTv⟩ := rep_retr σ.ρ σ.irred (π.locRep w) (hiso σ hσ).2 v hv
    obtain ⟨B, hB⟩ := (satLoc P F 2 w σ).1 ⟨T v, hTv, fun u hu => by rw [← hT, hf u (iwahori_level_zero_eq w ▸ hu)]⟩
    exact WD.unr_mono0 _ (UpperTheory.GalN.V.unr_algNorm hrc σ B hB)
  · have hA : ¬ A.valuation (l : Ω) < 1 := fun e => hl (((UpperTheory.V.Base.places F Ω l A).2.2.1 w h).1 e)
    obtain ⟨s₀, hs₀, h0⟩ := SetLike.not_le_iff_exists.1 fun e => ((H.ram w A h).1 e).elim hc hl
    obtain ⟨g, hg⟩ := UpperTheory.V.Sd.ordAway_n PH F Ω l ι ξ s c m a π r H A hA
    refine UpperTheory.GalN.V.L.monosep F Ω A w h _ (ineIncl h ⟨s₀, hs₀⟩) (deg_ineIncl _) ?_
    have k : UpperTheory.GalN.V.WDN ι r (rc (algNorm σ)) :=
      .of_aw hl H.cont ⟨(hG.away w hl A h rc hrc σ hσ).pol, (hG.away w hl A h rc hrc σ hσ).n0⟩
    have e : (r s₀ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly = (X - C 1) * (X - C (ξ s₀ : Qbar l)) := by
      rw [← Matrix.charpoly_units_conj g, ← Matrix.coe_units_inv, ← Units.val_mul, ← Units.val_mul, hg s₀ hs₀,
        Matrix.charpoly_diagonal, Fin.prod_univ_two]
      rfl
    rw [WD.eig, ← k.charpoly hl, coe_ineIncl, e]
    have h1 : ι (ξ s₀ : Qbar l) ≠ 1 := fun e' => h0 (Units.ext (ι.injective (by simpa using e')))
    rw [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_sub, map_X, map_C, map_C]
    rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)), roots_X_sub_C, roots_X_sub_C]
    simpa using h1.symm
