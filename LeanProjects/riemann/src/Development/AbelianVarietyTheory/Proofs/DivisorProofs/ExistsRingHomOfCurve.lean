import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfCurveDegreesNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfSurjectivePullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsumSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegDataOfCurveData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FiniteDegreeMorphisms
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.IndefiniteRowSideFullHecke.FrobeniusTwistEigen

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CurveRootGeometry

theorem curveData_of_hasSeq {T : Type} [Fintype T] {N : ℕ} (q : ℕ) [Fact q.Prime] (j : ℕ) (r : T → Fin N → ℝ)
    {k : Type} [Field k] [IsAlgClosed k] [CharP k q] {O : Type} [CommRing O] (hs : Splits O k) {c : O →+* O}
    (hc : Function.Involutive c) {C₀ C : Scheme.{0}} [Algebra k Γ(C₀, ⊤)] [IsIntegral C₀] [Algebra k Γ(C, ⊤)] [IsIntegral C]
    (hC : IsSmoothProjCurve k C) {G₀ : Over C₀} [GrpObj G₀] [QuasiSeparated G₀.hom] {G : Over C} [GrpObj G]
    [QuasiSeparated G.hom] {i₀ : OAct O G₀} {i : OAct O G} {m : ℕ} (hm : DegRel k i₀ i m) (hi : HasSeq q k c i)
    (te : T → (O →+* k)) (hte : Function.Injective te) (hΨ : ∀ σ, σ ∈ Set.range te ↔ σ.comp c ∉ Set.range te)
    (h0 : ∀ τ, PowerSumSmul.psum r τ j = (deg k (lieSub i₀ (scal C₀ (te τ))) : ℝ))
    (hN : ∀ τ, PowerSumSmul.psum r τ N =
      (deg k (lieSub i₀ (scal C₀ (te τ))) : ℝ) - deg k (lieSub i₀ (scal C₀ ((te τ).comp c))))
    (hlo : ∀ τ (n : ℕ), 1 ≤ n → n ≤ j → n < N → ∃ d ∈ subDegs k (Lie G₀), PowerSumSmul.psum r τ n ≤ (d : ℝ))
    (hhi : ∀ τ (n : ℕ), j < n → n < N → ∃ d ∈ subDegs k (Lie G₀), PowerSumSmul.psum r τ n ≤
      (deg k (lieSub i₀ (scal C₀ (te τ))) : ℝ) - deg k (lieSub i₀ (scal C₀ ((te τ).comp c))) + d) :
    CurveSemiAbelianConjecture.CurveData q j fun τ x => (m : ℝ) * r τ x := by
  classical
  obtain ⟨κ, _, t, ht⟩ := hs
  have : Finite (O →+* k) := Finite.of_surjective t ht.exists_eq
  have : PerfectRing k q := PerfectRing.ofSurjective k q (surjective_frobenius k q)
  obtain ⟨H, rL, rH, D, g, hL, hH, h1, h2, hM, hD, hMD, hv, hsum⟩ := hi
  have cc (σ : O →+* k) : (σ.comp c).comp c = σ := RingHom.ext fun a => congrArg σ (hc a)
  let φ : Equiv.Perm (O →+* k) :=
    { toFun := fun σ => (frobenius k q).comp σ
      invFun := fun σ => ((frobeniusEquiv k q).symm : k →+* k).comp σ
      left_inv := fun σ => RingHom.ext fun a => (frobeniusEquiv k q).symm_apply_apply _
      right_inv := fun σ => RingHom.ext fun a => (frobeniusEquiv k q).apply_symm_apply _ }
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have e1 (σ : O →+* k) : (deg k (lieSub i (scal C σ)) : ℝ) = m * deg k (lieSub i₀ (scal C₀ σ)) := by
    exact_mod_cast hm.1 σ
  refine ⟨k, inferInstance, inferInstance, inferInstance, C, inferInstance, inferInstance, hC, O →+* k, Fintype.ofFinite _,
    φ, fun σ => σ.comp c, fun σ => lieSub i (scal C (σ.comp c)), H, fun σ => rL (σ.comp c), rH, Lie G, D, g, te, cc,
    fun σ => hL _, hH, fun σ => ?_, fun σ => ?_, hM, hD, hMD, hv, hsum, hte, hΨ, fun τ => ?_, fun τ => ?_,
    fun τ n a b d => ?_, fun τ n a b => ?_⟩
  · simp only [cc]
    exact h1 σ
  · simp only [cc]
    exact h2 σ
  · simp only [cc]
    rw [PowerSumSmul.psum_smul, h0, e1]
  · simp only [cc]
    rw [PowerSumSmul.psum_smul, hN, e1, e1]
    ring
  · obtain ⟨d, hd, e⟩ := hlo τ n a b d
    obtain ⟨_, ⟨S, s, hS, rfl⟩, e'⟩ := hm.2 d hd
    refine ⟨S, s, hS, ?_⟩
    rw [PowerSumSmul.psum_smul]
    have : (m : ℝ) * d ≤ deg k S := by exact_mod_cast e'
    exact (mul_le_mul_of_nonneg_left e hm0).trans this
  · obtain ⟨d, hd, e⟩ := hhi τ n a b
    obtain ⟨_, ⟨S, s, hS, rfl⟩, e'⟩ := hm.2 d hd
    refine ⟨S, s, hS, ?_⟩
    simp only [cc]
    rw [PowerSumSmul.psum_smul, e1, e1]
    have : (m : ℝ) * d ≤ deg k S := by exact_mod_cast e'
    have := mul_le_mul_of_nonneg_left e hm0
    linarith

theorem appTop_comp_scal {k O : Type} [Field k] [CommRing O] {C C' : Scheme.{0}} [Algebra k Γ(C, ⊤)]
    [Algebra k Γ(C', ⊤)] {π : C' ⟶ C} (h : π ≫ strHom k C = strHom k C') (σ : O →+* k) :
    π.appTop.hom.comp (scal C σ) = scal C' σ := by
  refine RingHom.ext fun a => ?_
  change π.appTop (algebraMap k _ (σ a)) = algebraMap k _ (σ a)
  rw [algebraMap_eq_strHom, algebraMap_eq_strHom, ← h, Scheme.Hom.comp_appTop]
  rfl

theorem degRel_of_scalesDeg {k O : Type} [Field k] [CommRing O] (hs : Splits O k) {C C' : Scheme.{0}}
    [Algebra k Γ(C, ⊤)] [IsIntegral C] [Algebra k Γ(C', ⊤)] [IsIntegral C'] {π : C' ⟶ C}
    (h : π ≫ strHom k C = strHom k C') {m : ℕ} (hm : IndefiniteRowSideFullHecke.FiniteDegreeMorphisms.ScalesDeg k π m) {G : Over C} [GrpObj G]
    [IsSemiAbelian G] {G' : Over C'} [GrpObj G'] [IsSemiAbelian G'] {i : OAct O G} {i' : OAct O G'}
    {φ : G'.left ⟶ G.left} (hp : IsActPull i' i π φ) : DegRel k i i' m := by
  classical
  obtain ⟨κ, _, t, ht⟩ := hs
  obtain ⟨g, hω, hL⟩ := exists_isVB_of_isSemiAbelian G
  have := hL.isFiniteQC
  refine ⟨fun σ => ?_, ?_⟩
  · obtain ⟨j, rfl⟩ := ht.exists_eq σ
    have := isIso_lieSubBase hp.1 hp.2 ht hω j
    have e := deg_congr k (asIso (lieSubBase (scal C (t j)) hp.1 hp.2))
    rw [appTop_comp_scal h] at e
    rw [← e]
    exact ((hm _ g hL).2 _ (eigenι _ _) ⟨inferInstance, ht.isFiniteQC_eigen _ j⟩).2
  · rintro _ ⟨S, s, hS, rfl⟩
    obtain ⟨h₁, h₂⟩ := (hm _ g hL).2 S s hS
    have := isIso_lieBase hp.1 hω
    exact ⟨_, (h₁.comp (lieBase hp.1)).deg_mem, h₂.ge⟩

theorem exists_ringHom_of_curve {k R : Type} [Field k] [IsAlgClosed k] [CommRing R] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)]
    [IsIntegral C] (hC : IsProjCurve k C) (s : C ⟶ Sp R) : ∃ β : R →+* k, s = strHom k C ≫ spMap β := by
  have := hC.isProperCurve.isProper
  have := ProperFunctions.isIso_appTop_of_isAlgClosed (strHom k C)
  let β := (Scheme.ΓSpecIso (.of R)).inv ≫ s.appTop ≫ inv (strHom k C).appTop ≫ (Scheme.ΓSpecIso (.of k)).hom
  refine ⟨β.hom, ext_of_isAffine ?_⟩
  rw [Scheme.Hom.comp_appTop]
  change _ = (Spec.map β).appTop ≫ _
  rw [← cancel_epi (Scheme.ΓSpecIso (.of R)).inv, ← Scheme.ΓSpecIso_inv_naturality_assoc]
  simp [β]

section Emb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
  {q : ℕ} [Fact q.Prime] {k : Type} [Field k] [CharP k q] (hd : ¬ q ∣ (discr E).natAbs) (β : 𝓞 c.F →+* k)

include hd in

theorem isSplitBy_intEmb : IsSplitBy fun τ : E →+* ℂ => β.comp (intEmb c τ) := by
  have h : EigenSplit.IsSplitting fun τ : E →+* ℂ => β.comp (intEmb c τ) := by
    refine EigenSplit.isSplitting_of_isDomain (fun σ τ h => ?_) (NumberField.Embeddings.card E ℂ) β ?_
    · exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
        (RingHom.ext fun a => congrArg (fun f : 𝓞 E →+* 𝓞 c.F => (((f a : 𝓞 c.F) : c.F) : ℂ)) h)
    · rw [isUnit_iff_ne_zero, Ne, CharP.intCast_eq_zero_iff k q]
      exact fun h => hd (Int.natCast_dvd.1 h)
  refine isSplitBy_of_injective h.injective ?_
  rw [NumberField.Embeddings.card, RingOfIntegers.rank]

theorem intEmb_conjEmb (τ : E →+* ℂ) : intEmb c (conjEmb τ) = (intEmb c τ).comp (H.bar : 𝓞 E →+* 𝓞 E) := by
  refine RingHom.ext fun a => RingOfIntegers.ext (Subtype.ext ?_)
  change starRingEnd ℂ (τ (a : E)) = τ ((H.bar a : 𝓞 E) : E)
  rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]

theorem bar_involutive (H : Host E) : Function.Involutive (H.bar : 𝓞 E →+* 𝓞 E) := fun a => by
  refine RingOfIntegers.ext ?_
  change ((H.bar (H.bar a) : 𝓞 E) : E) = _
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

end Emb

theorem psum_root {T : Type} [Fintype T] {N j : ℕ} (hj : j ≤ N) (r : T → Fin N → ℝ) (τ : T) (a b : ℕ → ℝ)
    (h : ∀ x : Fin N, r τ x = if (x : ℕ) < j then a x else -b (N - 1 - x)) (n : ℕ) (hn : n ≤ N) :
    (n ≤ j → PowerSumSmul.psum r τ n = ∑ m ∈ Finset.range n, a m) ∧
      (j ≤ n → PowerSumSmul.psum r τ n = ∑ m ∈ Finset.range j, a m - ∑ m ∈ Finset.range (N - j), b m +
        ∑ m ∈ Finset.range (N - n), b m) := by
  have e (m : ℕ) (hm : m < N) : PowerSumSmul.ext (r τ) m = if m < j then a m else -b (N - 1 - m) := by
    simpa [PowerSumSmul.ext, hm] using h ⟨m, hm⟩
  have lo (n : ℕ) (h₁ : n ≤ j) : ∑ m ∈ Finset.range n, PowerSumSmul.ext (r τ) m = ∑ m ∈ Finset.range n, a m :=
    Finset.sum_congr rfl fun m hm => by
      have := Finset.mem_range.1 hm
      rw [e m (by omega), if_pos (by omega)]
  rw [PowerSumSmul.psum_eq r τ hn]
  refine ⟨lo n, fun h₁ => ?_⟩
  induction n, h₁ using Nat.le_induction with
  | base => rw [lo j le_rfl]; ring
  | succ n h₁ ih =>
    rw [Finset.sum_range_succ, ih (by omega), e n (by omega), if_neg (by omega),
      show N - n = (N - (n + 1)) + 1 by omega, Finset.sum_range_succ, show N - 1 - n = N - (n + 1) by omega]
    ring

theorem degLB_pull_dual {k : Type} [Field k] {C X : Scheme.{0}} [Algebra k Γ(C, ⊤)] [IsIntegral C] (hC : IsProjCurve k C)
    (f : C ⟶ X) {L : LB X} (hL : L.IsLB) : degLB k ((CechPic.dual L).pull f) = -degLB k (L.pull f) := by
  have e := congrArg (fun x => hC.degPic (CechPic.pull f x)) (CechPic.cls_dual_add hL)
  simp only [map_add, map_zero] at e
  exact eq_neg_of_add_eq_zero_left e

end GlobalTheory.CurveRootGeometry
