import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsPolynomialPairFunctionalEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.RegroupBC
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.PairGOps
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EulerProductAdjointEqStandard
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.AdjointEta.EtaOK

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL
open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HenQ UpperTheory.V.Z.Inf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3P.DihedralUnramifiedPlaces (toH)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

private theorem sign_ex (c : HeckeCharacter ℚ) :
    ∃ δ : Bool, ∀ w : InfinitePlace ℚ, (c.infiniteComponent w (-1) : ℂ) = if δ then -1 else 1 := by
  have hsq : ∀ w : InfinitePlace ℚ, (c.infiniteComponent w (-1) : ℂ) * (c.infiniteComponent w (-1) : ℂ) = 1 := by
    intro w
    rw [← Circle.coe_mul, ← map_mul, neg_mul_neg, one_mul, map_one, Circle.coe_one]
  rcases mul_self_eq_one_iff.1 (hsq default) with h | h
  · exact ⟨false, fun w => by rw [Subsingleton.elim w default, h]; rfl⟩
  · exact ⟨true, fun w => by rw [Subsingleton.elim w default, h]; rfl⟩

private theorem unr_of {η : HeckeCharacter ℚ} {v : Ad3.Pl} (h : (toH η).UnrAt v) :
    IsUnramifiedChar (localChar η v) := by
  refine isUnramifiedChar_iff.2 fun x hx => ?_
  rw [← Ad3P.DihedralUnramifiedPlaces.loc_eq]
  apply h x
  show Valued.v (x : Ad3.Qv v) = 1
  rw [Ad3P.DihedralUnramifiedPlaces.ord_eq v x.ne_zero, neg_eq_zero] at hx
  have h0 : Valued.v (x : Ad3.Qv v) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  rw [← WithZero.exp_log h0, hx, WithZero.exp_zero]

private theorem unr_mul {c η : HeckeCharacter ℚ} {v : Ad3.Pl} (h₁ : IsUnramifiedChar (localChar c v))
    (h₂ : IsUnramifiedChar (localChar η v)) : IsUnramifiedChar (localChar (c * η) v) := by
  refine isUnramifiedChar_iff.2 fun x hx => ?_
  have e : localChar (c * η) v x = localChar c v x * localChar η v x := Units.ext rfl
  rw [e, isUnramifiedChar_iff.1 h₁ x hx, isUnramifiedChar_iff.1 h₂ x hx, one_mul]

private theorem val_mul' (c η : HeckeCharacter ℚ) (v : Ad3.Pl) :
    (toH (c * η)).val v = (toH c).val v * (toH η).val v := Units.ext rfl

private theorem norm_val (c : HeckeCharacter ℚ) (v : Ad3.Pl) : ‖((toH c).val v : ℂ)‖ = 1 :=
  Circle.norm_coe _

private theorem tri_mul (a x y : ℂˣ) : tri a (x * y) = (tri a x).map (· * (y : ℂ)) := by
  simp [tri, mul_assoc]

private theorem tri_norm {a x : ℂˣ} (ha : ‖(a : ℂ)‖ = 1) (hx : ‖(x : ℂ)‖ = 1) : ∀ b ∈ tri a x, ‖b‖ = 1 := by
  intro b hb
  simp only [tri, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.mem_cons,
    Multiset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl <;> simp [ha, hx]

theorem UpperTheory.euler_product_induction_unramified :
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ D : Ad3.Dat, Ad3.An D →
        ∀ (η c : HeckeCharacter ℚ), EtaOK K η → IsOfFinOrder c → ∀ (S : Finset Ad3.Pl) (v : Ad3.Pl), D.bad ⊆ S → v ∈ S →
        (∀ u ∉ S, IsUnramifiedChar (localChar c u)) →
        (∀ u ∉ S, (toH η).UnrAt u ∧ ∀ w : PlacesOver K u, IsPrimitiveRoot ((toH η).val u) (fdeg w) ∧
          Fintype.card (PlacesOver K u) * fdeg w = 2) →
        (∀ u ∈ S, u ≠ v → Ram3 (D.ν u) (localChar c u) ∧ Ram3 (D.ν u) (localChar (c * η) u)) →
        ∀ (MainNotions : Set (HeightOneSpectrum (𝓞 K))) (BL : HeightOneSpectrum (𝓞 K) → Multiset ℂ),
        (∀ w, w ∈ MainNotions ↔ w.under (𝓞 ℚ) ∈ (S : Set Ad3.Pl)) →
        (∀ p ∉ S, ∀ w : PlacesOver K p, BL w.1 = (par D (toH c) p).map (· ^ fdeg w)) →
        ∃ β : ℂ[X], β ≠ 0 ∧ PairG (eulerL K BL MainNotions) (eulerLd K BL MainNotions) β (Ideal.absNorm v.asIdeal : ℝ)
          (lin3 (D.ν v) (localChar c v) * lin3 (D.ν v) (localChar (c * η) v)) := by
  intro K _ _ _ _ D hD η c hη hc S v hbad hv hcu hηu hram MainNotions BL hSK hBL
  obtain ⟨δ, hδ⟩ := sign_ex c
  have A₁ : Ad3.admitted D c δ S := ⟨hc, hδ, hbad, hcu⟩
  have A₂ : Ad3.admitted D (c * η) (!δ) S := by
    refine ⟨hc.mul hη.fin, fun w => ?_, hbad, fun u hu => unr_mul (hcu u hu) (unr_of (hηu u hu).1)⟩
    have e : ((c * η).infiniteComponent w (-1) : ℂ) =
        (c.infiniteComponent w (-1) : ℂ) * (η.infiniteComponent w (-1) : ℂ) := rfl
    rw [e, hδ w, hη.sgn w]
    cases δ <;> simp
  obtain ⟨β, hβ, hP⟩ := UpperTheory.exists_polynomial_pair_functional_eq D hD c (c * η) δ S v A₁ A₂ hv hram
  obtain ⟨a, ha⟩ := UpperTheory.V.Z.Gam.regroupBC ℚ K 2 (S : Set Ad3.Pl) MainNotions (par D (toH c)) BL
    (fun p => ((toH η).val p : ℂ)) 0 3 Nat.prime_two hSK (by
      intro p hp
      have hp' : p ∉ S := fun h => hp (Finset.mem_coe.2 h)
      refine ⟨by simp [par, tri], fun b hb => ?_, fun w => ⟨?_, ((hηu p hp').2 w).2, hBL p hp' w⟩⟩
      · have hb1 : ‖b‖ = 1 := tri_norm ((D.unit p).2 _) (norm_val c p) b hb
        rw [norm_inv, hb1, Real.rpow_zero, inv_one]
        exact ⟨le_rfl, le_rfl⟩
      · exact IsPrimitiveRoot.coe_units_iff.2 ((hηu p hp').2 w).1)
  have e0 : (fun p => (par D (toH c) p).map (· * ((toH η).val p : ℂ) ^ 0)) = par D (toH c) := by
    funext p
    simp
  have e1 : (fun p => (par D (toH c) p).map (· * ((toH η).val p : ℂ) ^ 1)) = par D (toH (c * η)) := by
    funext p
    simp only [pow_one]
    unfold par
    rw [val_mul', tri_mul]
  refine ⟨β, hβ, UpperTheory.V.Z.Gam.pairGOps.2.2.1 _ _ _ _ β _ _ a hP (fun s hs => ?_) (fun s hs => ?_)⟩
  · rw [← (ha s).1 hs, Finset.prod_range_succ, Finset.prod_range_one, e0, e1,
      (UpperTheory.euler_product_adjoint_eq_standard D c δ S A₁ s).1, (UpperTheory.euler_product_adjoint_eq_standard D (c * η) _ S A₂ s).1]
  · rw [← (ha s).2 hs, Finset.prod_range_succ, Finset.prod_range_one, e0, e1,
      (UpperTheory.euler_product_adjoint_eq_standard D c δ S A₁ s).2, (UpperTheory.euler_product_adjoint_eq_standard D (c * η) _ S A₂ s).2]
