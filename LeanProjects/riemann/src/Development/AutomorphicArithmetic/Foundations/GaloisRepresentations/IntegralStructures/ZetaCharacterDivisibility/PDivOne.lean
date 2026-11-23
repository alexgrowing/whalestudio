import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

private theorem satPol_facts {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (s : Multiset ℂ) :
    (((s.map fun b => X - C b).prod).map ι.symm.toRingHom).Monic ∧
    (((s.map fun b => X - C b).prod).map ι.symm.toRingHom).natDegree = Multiset.card s ∧
    (((s.map fun b => X - C b).prod).map ι.symm.toRingHom).coeff 0 = ι.symm ((-1) ^ Multiset.card s * s.prod) ∧
    (((s.map fun b => X - C b).prod).map ι.symm.toRingHom).map ι.toRingHom = (s.map fun b => X - C b).prod := by
  refine ⟨(monic_multiset_prod_of_monic _ _ fun b _ => monic_X_sub_C b).map _, ?_, ?_, ?_⟩
  · rw [natDegree_map, natDegree_multiset_prod_X_sub_C_eq_card]
  · rw [coeff_map, coeff_zero_eq_eval_zero, eval_multiset_prod, Multiset.map_map]
    have : (s.map ((fun p : ℂ[X] => eval 0 p) ∘ fun b => X - C b)) = s.map Neg.neg := by
      refine Multiset.map_congr rfl fun b _ => ?_
      simp
    rw [this, Multiset.prod_map_neg]
    rfl
  · rw [Polynomial.map_map]
    have : ι.toRingHom.comp ι.symm.toRingHom = RingHom.id ℂ := by
      ext z
      simp
    rw [this, Polynomial.map_id]

theorem UpperTheory.Gal.Int.Div.divOne_of :
    DivSet → DenseUs → DetFrob → InFacts → SepPin → DivOne := by
  intro hDiv hDense hDet hIn hSep E Ω _ _ _ _ _ _ l _ ι a d hd U hU ψ hψ dd ρ hV
  obtain ⟨hc, hs, ⟨X, hX⟩, hr⟩ := hV
  have hcard : ∀ (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), SatU U w B →
      Multiset.card (algSat a (normV w) B) = a := by
    rintro w B ⟨σ, -, hB⟩
    have h : Multiset.card (algSat a (normV w) B) = Multiset.card B := by
      unfold algSat
      simp
    rw [h]
    exact GlobalTheory.LFun.HasSatGL.card hB
  have hD := (hDense E Ω l a d hd U hU X).preimage (Homeomorph.inv (G E Ω)).isOpenMap
  obtain ⟨r, hrc, hrs, hin, hco, hop, hde⟩ := hDiv E Ω l a dd ρ hc hs hr ψ hψ.1 (hD.mono (by
    rintro g ⟨w, hw, hu, hl, ⟨B, hB⟩, A, hA, hf⟩
    have hf' : IsFrob A (normV w) g⁻¹ := hf
    obtain ⟨q1, q2, q3, -⟩ := satPol_facts ι (algSat a (normV w) B)
    rw [hcard w B hB] at q2 q3
    refine ⟨_, q1, q2, ?_, ?_⟩
    · have := (hX w hw hu hl B hB A hA).2 g⁻¹ hf'
      rwa [inv_inv] at this
    · have h := (hDet E Ω l ι a U ψ hψ w hu.1 hl B hB A hA).2 g⁻¹ hf'
      rw [inv_inv] at h
      rw [q3]
      apply ι.injective
      have h1 : ((-1 : ℂ) ^ a) * (-1) ^ a = 1 := by
        rw [← mul_pow]; simp
      simp only [map_mul, map_pow, map_neg, map_one, RingEquiv.apply_symm_apply]
      rw [h, ← mul_assoc, h1, one_mul]))
  refine ⟨r, ⟨hrc, hrs, (fun g : G E Ω => g⁻¹) ⁻¹' {g | (r g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.Separable}, X,
    hop.preimage continuous_inv, hde.preimage (Homeomorph.inv (G E Ω)).isOpenMap, ?_⟩, hin, hco⟩
  intro w hw hu hl B hB A hA
  have hE := hX w hw hu hl B hB A hA
  have hF := hIn (G E Ω) (Qbar l) a dd r ρ hin
  refine ⟨fun s hs' => hF.2.1 s (hE.1 s hs'), fun s hf hsV => ?_⟩
  obtain ⟨q1, q2, -, q4⟩ := satPol_facts ι (algSat a (normV w) B)
  rw [hcard w B hB] at q2
  rw [hSep (Qbar l) a _ _ q1 q2 (hF.2.2 s⁻¹ _ (hE.2 s hf)) hsV, q4]
