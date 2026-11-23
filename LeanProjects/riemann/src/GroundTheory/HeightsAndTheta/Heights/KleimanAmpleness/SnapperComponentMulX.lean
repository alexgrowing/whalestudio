import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreFurther
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CechHcSubsingletonOfBlock
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestBis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgCechSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PQuotPartGraded
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsVerticalDivOfIsVerticalDivisorAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc quotPart CechC)

noncomputable section

section Lemmas

variable {F : Type} [Field F] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

omit [LinearOrder K] [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] in

theorem snapper_component_mul_X [DecidableEq K] (f : MvPolynomial (Σ k, ι k) F) (b : K → ℕ) (v : Σ k, ι k) :
    weightedHomogeneousComponent (NumbersDVR.blockWeight ι) (b + NumbersDVR.blockWeight ι v) (f * X v) =
      weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f * X v := by
  have h := DirectSum.coe_decompose_mul_add_of_right_mem
    (weightedHomogeneousSubmodule F (NumbersDVR.blockWeight ι)) (a := f) (i := b)
    (isWeightedHomogeneous_X F (NumbersDVR.blockWeight ι) v)
  have key : ∀ (φ : MvPolynomial (Σ k, ι k) F) (c : K → ℕ),
      (DirectSum.decompose (weightedHomogeneousSubmodule F (NumbersDVR.blockWeight ι)) φ c :
        MvPolynomial (Σ k, ι k) F) = weightedHomogeneousComponent (NumbersDVR.blockWeight ι) c φ :=
    fun φ c => weightedDecomposition.decompose'_apply F (NumbersDVR.blockWeight ι) φ c
  rw [key, key] at h
  exact h

omit [LinearOrder K] [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] in

theorem snapper_colon_X [DecidableEq K] {J : Ideal (MvPolynomial (Σ k, ι k) F)} (hJ : NumbersDVR.IsMultiHomogIdeal J)
    (v : Σ k, ι k) : NumbersDVR.IsMultiHomogIdeal (J.colon (Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)})) := by
  intro f hf b
  rw [Submodule.mem_colon_span_singleton, smul_eq_mul] at hf ⊢
  rw [← snapper_component_mul_X]
  exact hJ _ hf _

omit [Fintype K] [LinearOrder K] in

theorem snapper_eval_shift (p : MvPolynomial K ℚ) (e m : K → ℤ) :
    eval (fun k => ((m - e) k : ℚ)) p =
      eval (fun k => (m k : ℚ)) (bind₁ (fun j => X j - C ((e j : ℤ) : ℚ)) p) := by
  have hb : ∀ (x : K → ℚ) (g : K → MvPolynomial K ℚ), eval x (bind₁ g p) = eval (fun j => eval x (g j)) p :=
    fun x g => eval₂Hom_bind₁ _ _ _ _
  rw [hb]
  refine congrArg (fun x => eval x p) (funext fun j => ?_)
  simp

theorem snapper_top (V : Ideal (MvPolynomial (Σ k, ι k) F)) (m : K → ℤ) (n : ℕ)
    (hn : ∑ k, (Fintype.card (ι k) - 1) < n) : Subsingleton (cechHc ι (quotPart F V) m n) := by
  have hI : ∀ I : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n, False := fun I => by
    have h1 : ∑ k, ((I.1 k).card - 1) ≤ ∑ k, (Fintype.card (ι k) - 1) :=
      Finset.sum_le_sum fun k _ => Nat.sub_le_sub_right (Finset.card_le_univ _) 1
    have := I.2.2
    omega
  have : Subsingleton (CechC F ι (MvPolynomial (Σ k, ι k) F ⧸ V) n) :=
    ⟨fun f g => funext fun I => (hI I).elim⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [Subsingleton.elim x y]

theorem snapper_finite (hS : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.TheoremSStatement) (V : Ideal (MvPolynomial (Σ k, ι k) F))
    (hV : NumbersDVR.IsMultiHomogIdeal V) (m : K → ℤ) (i : ℕ) :
    FiniteDimensional F (cechHc ι (quotPart F V) m i) :=
  (hS F K ι (MvPolynomial (Σ k, ι k) F ⧸ V) (quotPart F V) inferInstance inferInstance
    (HilbertSamuel.QuotPartGraded.proof F K ι V ((NumbersDVR.Objects.isMultiHomogIdeal_iff V).1 hV))).1 m i

end Lemmas

theorem EulerPoly.proof (hS : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.TheoremSStatement) (hE : EulerVar.Statement)
    (hD : PolyOfDiffsExact.Statement) : EulerPoly.Statement := by
  intro F _ K _ _ ι _ _ V hV
  have hfin : ∀ J : Ideal (MvPolynomial (Σ k, ι k) F), NumbersDVR.IsMultiHomogIdeal J →
      ∀ (m : K → ℤ) (i : ℕ), FiniteDimensional F (cechHc ι (quotPart F J) m i) :=
    fun J hJ => snapper_finite hS J hJ
  have key : ∀ J : Ideal (MvPolynomial (Σ k, ι k) F), NumbersDVR.IsMultiHomogIdeal J →
      ∃ p : MvPolynomial K ℚ, ∀ m, eulerChar F ι J m = eval (fun k => (m k : ℚ)) p := by
    intro J hJ
    refine IsNoetherian.induction (P := fun J : Ideal (MvPolynomial (Σ k, ι k) F) =>
      NumbersDVR.IsMultiHomogIdeal J → ∃ p : MvPolynomial K ℚ, ∀ m, eulerChar F ι J m = eval (fun k => (m k : ℚ)) p)
      (fun J ih hJ => ?_) J hJ
    have hlt2 : ∀ v : Σ k, ι k, (X v : MvPolynomial (Σ k, ι k) F) ∉ J →
        J < J ⊔ Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)} := fun v hvJ =>
      lt_of_le_of_ne le_sup_left fun h => hvJ (h ▸ Ideal.mem_sup_right (Ideal.subset_span rfl))
    have hSup : ∀ v : Σ k, ι k, NumbersDVR.IsMultiHomogIdeal (J ⊔ Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)}) :=
      fun v => FieldNumbers.isMultiHomogIdeal_sup_span hJ (isWeightedHomogeneous_X F (NumbersDVR.blockWeight ι) v)
    by_cases hA : ∃ v : Σ k, ι k, (X v : MvPolynomial (Σ k, ι k) F) ∉ J ∧
        J.colon (Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)}) ≠ J
    · obtain ⟨v, hvJ, hne⟩ := hA
      have hle : J ≤ J.colon (Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)}) := fun f hf => by
        rw [Submodule.mem_colon_span_singleton, smul_eq_mul]
        exact Ideal.mul_mem_right _ J hf
      obtain ⟨p1, hp1⟩ := ih _ (lt_of_le_of_ne hle (Ne.symm hne)) (snapper_colon_X hJ v)
      obtain ⟨p2, hp2⟩ := ih _ (hlt2 v hvJ) (hSup v)
      refine ⟨bind₁ (fun j => X j - C (((Pi.single v.1 1 : K → ℤ) j : ℤ) : ℚ)) p1 + p2, fun m => ?_⟩
      rw [hE F K ι J v hJ (hfin J hJ) (hfin _ (snapper_colon_X hJ v)) (hfin _ (hSup v)) m, hp1, hp2, map_add,
        ← snapper_eval_shift]
    · push Not at hA
      by_cases hB : ∃ k, ∀ i, (X ⟨k, i⟩ : MvPolynomial (Σ k, ι k) F) ∈ J
      · obtain ⟨k, hk⟩ := hB
        refine ⟨0, fun m => ?_⟩
        rw [map_zero, eulerChar]
        refine Finset.sum_eq_zero fun i _ => ?_
        have := cechHc_subsingleton_of_block hk m i
        rw [Module.finrank_zero_of_subsingleton]
        simp
      · push Not at hB
        refine hD K (eulerChar F ι J) fun k => ?_
        obtain ⟨i, hi⟩ := hB k
        obtain ⟨q, hq⟩ := ih _ (hlt2 ⟨k, i⟩ hi) (hSup ⟨k, i⟩)
        refine ⟨q, fun m => ?_⟩
        have h := hE F K ι J ⟨k, i⟩ hJ (hfin J hJ) (hfin _ (snapper_colon_X hJ _)) (hfin _ (hSup _)) m
        rw [hA _ hi] at h
        rw [← hq m]
        linarith
  obtain ⟨p, hp⟩ := key V hV
  exact ⟨∑ k, (Fintype.card (ι k) - 1), p, hfin V hV, fun m i hi => snapper_top V m i hi, hp⟩

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
