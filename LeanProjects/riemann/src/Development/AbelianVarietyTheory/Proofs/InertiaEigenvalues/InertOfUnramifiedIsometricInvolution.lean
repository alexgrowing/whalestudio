import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramifiedNonsplitExistsConjInvolutionUniformise

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.InertOfUnramInv

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem exists_int_approx (w : HeightOneSpectrum (𝓞 L)) (x : w.adicCompletion L) (hx : Valued.v x ≤ 1) :
    ∃ a : 𝓞 L, Valued.v (x - algebraMap L (w.adicCompletion L) (a : L)) < 1 := by
  have hval : ∀ k : L, Valued.v (algebraMap L (w.adicCompletion L) k) = w.valuation L k :=
    fun k => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := w) k
  have hU : IsOpen {z : w.adicCompletion L | Valued.v (z - x) < 1} := by
    have h := (Valued.isOpen_ball (w.adicCompletion L) 1).preimage (continuous_sub_right x)
    simpa [Valuation.restrict_lt_one_iff] using h
  obtain ⟨y, hy⟩ :=
    (HeightOneSpectrum.denseRange_algebraMap (K := L) (v := w)).exists_mem_open hU ⟨x, by simp⟩
  have hy' : Valued.v (algebraMap L (w.adicCompletion L) y - x) < 1 := hy
  have hyv : w.valuation L y ≤ 1 := by
    rw [← hval]
    calc Valued.v (algebraMap L (w.adicCompletion L) y)
        = Valued.v ((algebraMap L (w.adicCompletion L) y - x) + x) := by rw [sub_add_cancel]
      _ ≤ max (Valued.v (algebraMap L (w.adicCompletion L) y - x)) (Valued.v x) := Valuation.map_add _ _ _
      _ ≤ 1 := max_le hy'.le hx
  obtain ⟨a, ha⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer (K := L) (v := w) hyv 1
  refine ⟨a, ?_⟩
  have e : x - algebraMap L (w.adicCompletion L) (a : L) =
      -(algebraMap L (w.adicCompletion L) y - x) + -(algebraMap L (w.adicCompletion L) (a : L) -
        algebraMap L (w.adicCompletion L) y) := by ring
  rw [e]
  refine Valuation.map_add_lt _ (by rw [Valuation.map_neg]; exact hy') ?_
  rw [Valuation.map_neg, ← map_sub, hval]
  simpa using ha

theorem inert_of_isUnramInv : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L) (q : ℕ), (∀ x : L, s (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → Formalism.UG.IsUnramInv ϖ s q → Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal ∧ ¬ IsSplitAt w ∧ q = Formalism.UG.qV (maximalRealSubfield L) v := by
  intro L _ _ _ v w hvw s ϖ q hsc hU
  unfold Formalism.UG.IsUnramInv at hU
  obtain ⟨-, hsv, -, -, ⟨x, hxO, hx1⟩, -, hcard⟩ := hU
  have hvw' : w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L)) = v.asIdeal := hvw
  have hlo : w.asIdeal.LiesOver v.asIdeal := ⟨hvw'.symm⟩
  let φ : 𝓞 L →+* w.adicCompletion L := (algebraMap L (w.adicCompletion L)).comp (algebraMap (𝓞 L) L)
  have hφ : ∀ b : 𝓞 L, Valued.v (φ b) = w.valuation L (algebraMap (𝓞 L) L b) :=
    fun b => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := w) (algebraMap (𝓞 L) L b)
  have hval : ∀ b : 𝓞 L, Valued.v (φ b) < 1 ↔ b ∈ w.asIdeal := by
    intro b
    rw [hφ]
    exact HeightOneSpectrum.valuation_lt_one_iff_mem (K := L) w b
  have hfix : ∀ a : 𝓞 (maximalRealSubfield L),
      s (φ (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) a)) = φ (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) a) := by
    intro a
    show s (algebraMap L _ _) = algebraMap L _ _
    rw [hsc]
    congr 1
    exact (IsCMField.complexConj L).commutes (a : maximalRealSubfield L)
  have hxv : Valued.v x ≤ 1 := hxO

  have hf1 : w.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield L)) ≠ 1 := by
    intro hf
    have hn := Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal
    rw [hf, pow_one, Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
      Submodule.cardQuot_apply] at hn
    have hle : v.asIdeal ≤ w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L)) := hvw'.ge
    have hinj : Function.Injective (Ideal.quotientMap w.asIdeal _ hle) :=
      Ideal.quotientMap_injective' hvw'.le
    have hbij := (Nat.bijective_iff_injective_and_card _).mpr ⟨hinj, hn⟩
    obtain ⟨b, hb⟩ := exists_int_approx w x hxv
    obtain ⟨a, ha⟩ := hbij.2 (Ideal.Quotient.mk w.asIdeal b)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at ha
    have hsz := hfix a
    set z := φ (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) a) with hz
    have h1 : Valued.v (x - z) < 1 := by
      have e : x - z = (x - φ b) + -(φ (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) a - b)) := by
        rw [map_sub]; ring
      rw [e]
      refine Valuation.map_add_lt _ hb ?_
      rw [Valuation.map_neg, hval]
      exact ha
    have h2 : s x - x = s (x - z) + -(x - z) := by
      rw [map_sub, hsz]; ring
    have h3 : Valued.v (s x - x) < 1 := by
      rw [h2]
      refine Valuation.map_add_lt _ ?_ ?_
      · rw [hsv]; exact h1
      · rw [Valuation.map_neg]; exact h1
    exact absurd hx1 (ne_of_lt h3)
  have hfpos := Ideal.inertiaDeg_pos w.asIdeal (𝓞 (maximalRealSubfield L))
  have hepos := Ideal.ramificationIdx_pos w.asIdeal (𝓞 (maximalRealSubfield L))

  have hG2 : Nat.card (L ≃ₐ[maximalRealSubfield L] L) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]
  have hsum := Ideal.sum_ramification_inertia_eq_card v.asIdeal (𝓞 L)
    (G := L ≃ₐ[maximalRealSubfield L] L)
  let F : v.asIdeal.primesOver (𝓞 L) → ℕ := fun P =>
    P.1.ramificationIdx (𝓞 (maximalRealSubfield L)) * P.1.inertiaDeg (𝓞 (maximalRealSubfield L))
  have hsum' : ∑ P, F P = 2 := by
    rw [← hG2, ← hsum]
  let W : v.asIdeal.primesOver (𝓞 L) := ⟨w.asIdeal, w.isPrime, hlo⟩
  have hW : F W ≤ 2 := by
    rw [← hsum']
    exact Finset.single_le_sum (f := F) (fun _ _ => Nat.zero_le _) (Finset.mem_univ W)
  have hW' : w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield L)) *
      w.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield L)) ≤ 2 := hW
  have hf2 : w.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield L)) = 2 := by
    have : 2 ≤ w.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield L)) := by omega
    nlinarith
  have he1 : w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield L)) = 1 := by
    rw [hf2] at hW'
    omega
  refine ⟨?_, ?_, ?_⟩
  · have : (w.asIdeal.under (𝓞 (maximalRealSubfield L))).IsMaximal := by
      rw [← hlo.over]
      exact v.isMaximal
    exact Ideal.ramificationIdx_eq_one_iff.mp he1
  · rintro ⟨u, hne, hu⟩
    have hlu : u.asIdeal.LiesOver v.asIdeal := ⟨by
      rw [hlo.over]
      exact (congrArg HeightOneSpectrum.asIdeal hu).symm⟩
    let U : v.asIdeal.primesOver (𝓞 L) := ⟨u.asIdeal, u.isPrime, hlu⟩
    have hWU : W ≠ U := fun h => hne (HeightOneSpectrum.ext (congrArg Subtype.val h).symm)
    have h2 : F W + F U ≤ 2 := by
      rw [← hsum', ← Finset.sum_pair hWU]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have hu1 := Ideal.inertiaDeg_pos u.asIdeal (𝓞 (maximalRealSubfield L))
    have hu2 := Ideal.ramificationIdx_pos u.asIdeal (𝓞 (maximalRealSubfield L))
    have hFU : 1 ≤ F U := Nat.mul_pos hu2 hu1
    have hFW : F W = 2 := by
      show w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield L)) *
        w.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield L)) = 2
      rw [he1, hf2]
    omega
  ·
    let O := (Valued.v : Valuation (w.adicCompletion L) (WithZero (Multiplicative ℤ))).valuationSubring
    have hmemO : ∀ b : 𝓞 L, φ b ∈ O := by
      intro b
      show Valued.v (φ b) ≤ 1
      rw [hφ]
      exact HeightOneSpectrum.valuation_le_one (K := L) w b
    let g : 𝓞 L →+* O := φ.codRestrict O hmemO
    have hmax : ∀ y : O, y ∈ IsLocalRing.maximalIdeal O ↔ Valued.v (y : w.adicCompletion L) < 1 := by
      intro y
      have hle : Valued.v (y : w.adicCompletion L) ≤ 1 := y.2
      have hu : IsUnit y ↔ Valued.v (y : w.adicCompletion L) = 1 :=
        HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one (K := L) (v := w) (a := y)
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hu]
      exact ⟨fun h => lt_of_le_of_ne hle h, fun h => ne_of_lt h⟩
    let G := (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)).comp g
    have hGs : Function.Surjective G := by
      intro Y
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective Y
      obtain ⟨b, hb⟩ := exists_int_approx w (y : w.adicCompletion L) y.2
      refine ⟨b, ?_⟩
      show Ideal.Quotient.mk _ (g b) = Ideal.Quotient.mk _ y
      rw [Ideal.Quotient.eq, hmax]
      show Valued.v (φ b - (y : w.adicCompletion L)) < 1
      rw [← Valuation.map_neg, neg_sub]
      exact hb
    have hker : RingHom.ker G = w.asIdeal := by
      ext b
      rw [RingHom.mem_ker]
      show Ideal.Quotient.mk _ (g b) = 0 ↔ _
      rw [Ideal.Quotient.eq_zero_iff_mem, hmax]
      exact hval b
    have hc := Nat.card_congr (RingHom.quotientKerEquivOfSurjective hGs).toEquiv
    rw [hker] at hc
    have hcard' : Nat.card (O ⧸ IsLocalRing.maximalIdeal O) = q ^ 2 := hcard
    have hn := Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal
    rw [hf2, Ideal.absNorm_apply w.asIdeal, Submodule.cardQuot_apply, hc, hcard'] at hn
    show q = Ideal.absNorm v.asIdeal
    exact Nat.pow_left_injective (n := 2) (by norm_num) hn.symm

end GlobalTheory.InertOfUnramInv
