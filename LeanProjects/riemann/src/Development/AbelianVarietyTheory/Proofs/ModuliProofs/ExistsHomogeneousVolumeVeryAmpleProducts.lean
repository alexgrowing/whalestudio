import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsProjByOfIsPullback
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsMultigradedHilbertPoly
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHomogeneousFormEqHighPowerSection
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsHaveFiniteDimensionInvarianceIsomorphism
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarizedAbelianAmpleExistsPositiveVolume
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.VolPoly
section
open Filter Topology

theorem eq_coeff_of_tendsto (q : Polynomial ℝ) (g : ℕ) (δ : ℝ)
    (h : Tendsto (fun e : ℕ => q.eval (e : ℝ) / (e : ℝ) ^ g) atTop (𝓝 δ)) : δ = q.coeff g := by
  have hX : (Polynomial.X ^ g : Polynomial ℝ).degree = g := Polynomial.degree_X_pow g
  have h0 : (Polynomial.X ^ g : Polynomial ℝ) ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
  rcases lt_trichotomy q.degree g with hq | hq | hq
  · have := (Polynomial.div_tendsto_atTop_zero_of_degree_lt q (Polynomial.X ^ g) (hX ▸ hq)).comp
      tendsto_natCast_atTop_atTop
    rw [Polynomial.coeff_eq_zero_of_degree_lt hq]
    exact tendsto_nhds_unique h (by simpa [Function.comp_def] using this)
  · have := (Polynomial.div_tendsto_atTop_leadingCoeff_div_of_degree_eq q (Polynomial.X ^ g) (hX ▸ hq)).comp
      tendsto_natCast_atTop_atTop
    rw [← Polynomial.natDegree_eq_of_degree_eq_some hq]
    exact tendsto_nhds_unique h (by simpa [Function.comp_def] using this)
  · have := (Polynomial.abs_div_tendsto_atTop_atTop_of_degree_gt q (Polynomial.X ^ g) (hX ▸ hq) h0).comp
      tendsto_natCast_atTop_atTop
    exact (not_tendsto_nhds_of_tendsto_atTop (by simpa [Function.comp_def, abs_div] using this) _ (by simpa [abs_div] using h.abs)).elim

theorem exists_poly_line {σ : Type} (Ψ : MvPolynomial σ ℚ) (n : σ → ℚ) :
    ∃ q : Polynomial ℚ, (∀ e : ℚ, q.eval e = MvPolynomial.eval (fun k => e * n k) Ψ) ∧
      ∀ g, q.coeff g = MvPolynomial.eval n (MvPolynomial.homogeneousComponent g Ψ) := by
  induction Ψ using MvPolynomial.induction_on' with
  | monomial d c =>
    refine ⟨Polynomial.monomial d.degree (MvPolynomial.eval n (MvPolynomial.monomial d c)), fun e => ?_, fun g => ?_⟩
    · simp only [Polynomial.eval_monomial, MvPolynomial.eval_monomial, Finsupp.prod, mul_pow,
        Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]
      ring
    · rw [MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_monomial c rfl),
        Polynomial.coeff_monomial]
      split_ifs with h1 h2 h2
      · rfl
      · exact (h2 h1.symm).elim
      · exact (h1 h2.symm).elim
      · simp
  | add p p' hp hp' =>
    obtain ⟨q, h1, h2⟩ := hp
    obtain ⟨q', h1', h2'⟩ := hp'
    exact ⟨q + q', fun e => by simp [h1, h1'], fun g => by simp [h2, h2']⟩

theorem eq_eval_homogeneousComponent {σ : Type} (Ψ : MvPolynomial σ ℚ) (n : σ → ℕ) (g : ℕ) (δ : ℝ) (h : ℕ → ℕ)
    (hh : ∀ᶠ e : ℕ in atTop, (h e : ℚ) = MvPolynomial.eval (fun k => ((e * n k : ℕ) : ℚ)) Ψ)
    (ht : Tendsto (fun e : ℕ => (h e : ℝ) / (e : ℝ) ^ g) atTop (𝓝 δ)) :
    δ = ((MvPolynomial.eval (fun k => (n k : ℚ)) (MvPolynomial.homogeneousComponent g Ψ) : ℚ) : ℝ) := by
  obtain ⟨q, h1, h2⟩ := exists_poly_line Ψ (fun k => (n k : ℚ))
  rw [← h2, eq_coeff_of_tendsto (q.map (algebraMap ℚ ℝ)) g δ (ht.congr' (hh.mono fun e he => ?_))]
  · simp
  · have : ((e : ℕ) : ℝ) = algebraMap ℚ ℝ (e : ℚ) := by simp
    beta_reduce
    congr 1
    rw [this, Polynomial.eval_map_algebraMap, Polynomial.aeval_algebraMap_apply, Polynomial.coe_aeval_eq_eval, h1]
    push_cast at he
    rw [← he]; simp

theorem isWeightedHomogeneous_aeval {K σ τ M : Type} [CommRing K] [AddCommMonoid M] (w : σ → M) (n : M)
    (G : τ → MvPolynomial σ K) (hG : ∀ a, (G a).IsWeightedHomogeneous w n) (F : MvPolynomial τ K) (e : ℕ)
    (hF : F.IsHomogeneous e) : (MvPolynomial.aeval G F).IsWeightedHomogeneous w (e • n) := by
  rw [F.as_sum, map_sum]
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  rw [MvPolynomial.aeval_monomial]
  have h1 : d.degree = e := by
    rw [Finsupp.degree_eq_weight_one]; exact hF (MvPolynomial.mem_support_iff.1 hd)
  have h2 := MvPolynomial.IsWeightedHomogeneous.prod d.support (fun a => G a ^ d a) (fun a => d a • n)
    (w := w) fun a _ => (hG a).pow _
  rw [← Finset.sum_smul, ← Finsupp.degree_apply, h1] at h2
  exact h2.C_mul _

theorem exists_homogeneous_core {K σ M R : Type} [CommRing K] [AddCommMonoid M] [DecidableEq M] [CommRing R] (w : σ → M)
    (ev : MvPolynomial σ K →+* R) : ∃ I : Ideal (MvPolynomial σ K),
      (∀ F ∈ I, ∀ n, MvPolynomial.weightedHomogeneousComponent w n F ∈ I) ∧
      ∀ n (F : MvPolynomial σ K), F.IsWeightedHomogeneous w n → (F ∈ I ↔ ev F = 0) := by
  letI := MvPolynomial.weightedGradedAlgebra K w
  let J := (RingHom.ker ev).homogeneousCore (MvPolynomial.weightedHomogeneousSubmodule K w)
  refine ⟨J.toIdeal, fun F hF n => ?_, fun n F hF => ⟨fun h => Ideal.toIdeal_homogeneousCore_le _ _ h,
    fun h => Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨n, hF⟩ h⟩⟩
  have := J.isHomogeneous n hF
  rwa [← MvPolynomial.weightedDecomposition.decompose'_apply K w]

theorem finrank_eq_of_surj {K V R : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup R] [Module K R]
    (W I : Submodule K V) [Module.Finite K W] (ev : V →ₗ[K] R) (S : Submodule K R) (h : W.map ev = S)
    (hI : ∀ F ∈ W, F ∈ I ↔ ev F = 0) :
    Module.finrank K W = Module.finrank K S + Module.finrank K ↥(W ⊓ I) := by
  rw [← (ev.domRestrict W).finrank_range_add_finrank_ker, LinearMap.range_domRestrict, h]
  congr 1
  have : LinearMap.ker (ev.domRestrict W) = (W ⊓ I).comap W.subtype := by
    ext x; simp [hI x.1 x.2]
  rw [this]
  exact (Submodule.comapSubtypeEquivOfLe inf_le_left).finrank_eq
end
end GlobalTheory.VolPoly

noncomputable section
namespace GlobalTheory.VolPoly
open GlobalTheory.AbLaw GlobalTheory.AbLaw.Segre ReciprocityTheory.ChartRestriction.G.Out

variable {K : Type} [Field K] {X : Scheme.{0}}

theorem ap_id {U W : X.Opens} (f : X ⟶ X) (hf : f = 𝟙 X) (h : W ≤ f ⁻¹ᵁ U) (h' : W ≤ U) (x : Γ(X, U)) :
    ap f h x = rs X h' x := by
  subst hf
  rfl

theorem ap_ap {P Y : Scheme.{0}} (d : Y ⟶ P) (f : P ⟶ X) {U : X.Opens} {V : P.Opens} {W : Y.Opens}
    (h : V ≤ f ⁻¹ᵁ U) (h' : W ≤ d ⁻¹ᵁ V) (h'' : W ≤ (d ≫ f) ⁻¹ᵁ U) (x : Γ(X, U)) :
    ap d h' (ap f h x) = ap (d ≫ f) h'' x :=
  congr($(Scheme.Hom.appLE_comp_appLE d f U V W h h').hom x)

theorem affine_inf_generated (p : X ⟶ Sp K) [IsSeparated p] {U V W : X.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (e : W = U ⊓ V) : IsAffineOpen W ∧ ∀ A : Subring Γ(X, W),
      (∀ a, rs X (e.le.trans inf_le_left) a ∈ A) → (∀ a, rs X (e.le.trans inf_le_right) a ∈ A) → A = ⊤ := by
  have sq := IsPullback.of_hasPullback p p
  let W' : (pullback p p).Opens := pullback.fst p p ⁻¹ᵁ U ⊓ pullback.snd p p ⁻¹ᵁ V
  have loc : W' = pullback.fst p p ⁻¹ᵁ U ⊓ pullback.snd p p ⁻¹ᵁ V := rfl
  have hW' : IsAffineOpen W' := by
    have : IsAffine _ := hU
    have : IsAffine _ := hV
    have : IsAffine _ := isAffineOpen_top (Sp K)
    exact .of_isIso (Scheme.Hom.isPullback_resLE sq (US := ⊤) le_top le_top loc).isoPullback.hom
  have e' : W = pullback.diagonal p ⁻¹ᵁ W' := by
    rw [loc, Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage,
      pullback.diagonal_fst, pullback.diagonal_snd, e]
    rfl
  have hs : Function.Surjective (ap (pullback.diagonal p) e'.le) := by
    subst e'
    have := (pullback.diagonal p).app_surjective W' hW'
    rwa [Scheme.Hom.app_eq_appLE] at this
  refine ⟨e' ▸ hW'.preimage _, fun A h₁ h₂ => ?_⟩
  have po := (isIso_pushoutSection_iff sq (US := ⊤) le_top le_top loc).1
    (isIso_pushoutSection_of_isAffineOpen sq _ _ _ (isAffineOpen_top _) hV hU)
  have : A.comap (ap (pullback.diagonal p) e'.le) = ⊤ := by
    rw [← top_le_iff, ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨d, rfl⟩)
    · change ap (pullback.diagonal p) e'.le (ap (pullback.fst p p) inf_le_left d) ∈ A
      rw [ap_ap _ _ _ _ (by rw [pullback.diagonal_fst]; exact e.le.trans inf_le_left),
        ap_id _ (pullback.diagonal_fst p) _ (e.le.trans inf_le_left)]
      exact h₁ d
    · change ap (pullback.diagonal p) e'.le (ap (pullback.snd p p) inf_le_right d) ∈ A
      rw [ap_ap _ _ _ _ (by rw [pullback.diagonal_snd]; exact e.le.trans inf_le_right),
        ap_id _ (pullback.diagonal_snd p) _ (e.le.trans inf_le_right)]
      exact h₂ d
  refine top_le_iff.1 fun x _ => ?_
  obtain ⟨y, rfl⟩ := hs x
  exact (this.ge (Subring.mem_top y) :)

def Emb (f : X ⟶ Sp K) (H : LB X) {σ : Type} (s : σ → LB.Sec H) : Prop :=
  (⨆ i, nonzeroLocus (s i) = ⊤) ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i)) ∧
    ∃ r : σ → Γ(X, nonzeroLocus (s i)),
      (∀ j k, rs X (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s j).f k) =
        rs X (inf_le_left : nonzeroLocus (s i) ⊓ H.U k ≤ nonzeroLocus (s i)) (r j) *
          rs X (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s i).f k)) ∧
      Function.Surjective (MvPolynomial.eval₂Hom (AbLaw.cst f (nonzeroLocus (s i))) r)

theorem emb_of_vAmp {f : X ⟶ Sp K} {H : LB X} {σ : Type} {s : σ → LB.Sec H} (h : VAmp f H s) : Emb f H s := by
  refine ⟨h.1, fun i => ⟨(h.2 i).1, ?_⟩⟩
  obtain ⟨r, h₁, h₂⟩ := (h.2 i).2
  refine ⟨r, h₁, fun x => ?_⟩
  obtain ⟨F, hF⟩ := h₂ x
  exact ⟨F, hF.symm⟩

theorem Emb.veryAmpleBy {f : X ⟶ Sp K} {H : LB X} {σ : Type} {s : σ → LB.Sec H} (h : Emb f H s) {m : ℕ}
    (e : Fin (m + 1) ≃ σ) : VeryAmpleBy f H (fun j => s (e j)) := by
  refine ⟨by rw [← h.1]; exact e.iSup_comp (g := fun i => nonzeroLocus (s i)), fun i => ?_⟩
  obtain ⟨h₁, r, h₂, h₃⟩ := h.2 (e i)
  refine ⟨h₁, fun j => r (e j), fun j k => h₂ _ _, fun x => ?_⟩
  obtain ⟨p, rfl⟩ := h₃ x
  refine ⟨MvPolynomial.rename e.symm p, ?_⟩
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_rename]
  congr 1
  funext a
  simp

variable {J : Type} {U : J → X.Opens}

def mulSec {g g' : ∀ i j, Γ(X, U i ⊓ U j)ˣ} (s : LB.Sec ⟨J, U, g⟩) (s' : LB.Sec ⟨J, U, g'⟩) :
    LB.Sec ⟨J, U, fun i j => g i j * g' i j⟩ where
  f j := (show Γ(X, U j) from s.f j) * (show Γ(X, U j) from s'.f j)
  compat i j := by
    have h := s.compat i j
    have h' := s'.compat i j
    dsimp only at h h' ⊢
    rw [map_mul, map_mul, h, h', Units.val_mul]
    ring

theorem nonzeroLocus_mulSec {g g' : ∀ i j, Γ(X, U i ⊓ U j)ˣ} (hc : ⨆ i, U i = ⊤) (s : LB.Sec ⟨J, U, g⟩)
    (s' : LB.Sec ⟨J, U, g'⟩) : nonzeroLocus (mulSec s s') = nonzeroLocus s ⊓ nonzeroLocus s' := by
  ext y
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ i, U i by rw [hc]; trivial)
  have e : X.basicOpen ((mulSec s s').f k) = X.basicOpen (s.f k) ⊓ X.basicOpen (s'.f k) := X.basicOpen_mul _ _
  rw [← nonzeroLocus_inf_chart, ← nonzeroLocus_inf_chart, ← nonzeroLocus_inf_chart] at e
  exact ⟨fun h => ⟨(e.le ⟨h, hk⟩).1.1, (e.le ⟨h, hk⟩).2.1⟩, fun h => (e.ge ⟨⟨h.1, hk⟩, h.2, hk⟩).1⟩

theorem Emb.mul {p : X ⟶ Sp K} [IsSeparated p] {g g' : ∀ i j, Γ(X, U i ⊓ U j)ˣ} (hc : ⨆ i, U i = ⊤) {σ τ : Type}
    {s : σ → LB.Sec ⟨J, U, g⟩} {t : τ → LB.Sec ⟨J, U, g'⟩} (hs : Emb p _ s) (ht : Emb p _ t) :
    Emb p _ (fun a : σ × τ => mulSec (s a.1) (t a.2)) := by
  refine ⟨top_le_iff.1 fun y _ => ?_, fun a => ?_⟩
  · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show y ∈ ⨆ i, nonzeroLocus (s i) by rw [hs.1]; trivial)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show y ∈ ⨆ i, nonzeroLocus (t i) by rw [ht.1]; trivial)
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j), ?_⟩
    rw [nonzeroLocus_mulSec hc]
    exact ⟨hi, hj⟩
  obtain ⟨aff₁, r₁, hr₁, sj₁⟩ := hs.2 a.1
  obtain ⟨aff₂, r₂, hr₂, sj₂⟩ := ht.2 a.2
  have loc := nonzeroLocus_mulSec hc (s a.1) (t a.2)
  have l₁ := loc.le.trans inf_le_left
  have l₂ := loc.le.trans inf_le_right
  have o₁ : r₁ a.1 = 1 := ratio_self _ _ (hr₁ _)
  have o₂ : r₂ a.2 = 1 := ratio_self _ _ (hr₂ _)
  obtain ⟨k₁, k₂⟩ := affine_inf_generated p aff₁ aff₂ loc
  refine ⟨k₁, fun b => rs X l₁ (r₁ b.1) * rs X l₂ (r₂ b.2), fun b k => ?_, ?_⟩
  · have e₁ := congrArg (rs X (inf_le_inf_right (U k) l₁)) (hr₁ b.1 k)
    have e₂ := congrArg (rs X (inf_le_inf_right (U k) l₂)) (hr₂ b.2 k)
    simp only [map_mul, AbLaw.rs_rs] at e₁ e₂
    refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) e₁ e₂).trans ((mul_mul_mul_comm _ _ _ _).trans ?_))
    refine congrArg₂ (· * ·) ?_ (map_mul _ _ _).symm
    rw [map_mul, AbLaw.rs_rs, AbLaw.rs_rs]
  · rw [← RingHom.range_eq_top]
    refine k₂ _ (fun d => ?_) fun d => ?_
    · obtain ⟨F, rfl⟩ := sj₁ d
      induction F using MvPolynomial.induction_on with
      | C c => exact ⟨MvPolynomial.C c, by rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, rs_cst]⟩
      | add F G hF hG => rw [map_add, map_add]; exact Subring.add_mem _ hF hG
      | mul_X F i hF =>
        rw [map_mul, map_mul]
        refine Subring.mul_mem _ hF ⟨MvPolynomial.X (i, a.2), ?_⟩
        simp only [MvPolynomial.eval₂Hom_X', o₂, map_one, _root_.mul_one]
    · obtain ⟨F, rfl⟩ := sj₂ d
      induction F using MvPolynomial.induction_on with
      | C c => exact ⟨MvPolynomial.C c, by rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, rs_cst]⟩
      | add F G hF hG => rw [map_add, map_add]; exact Subring.add_mem _ hF hG
      | mul_X F i hF =>
        rw [map_mul, map_mul]
        refine Subring.mul_mem _ hF ⟨MvPolynomial.X (a.1, i), ?_⟩
        simp only [MvPolynomial.eval₂Hom_X', o₁, map_one, _root_.one_mul]

def IsSec (g : ∀ i j, Γ(X, U i ⊓ U j)ˣ) (f : ∀ j, Γ(X, U j)) : Prop :=
  ∀ i j, rs X inf_le_left (f i) = (g i j).val * rs X inf_le_right (f j)

theorem IsSec.mul {g g' : ∀ i j, Γ(X, U i ⊓ U j)ˣ} {f f' : ∀ j, Γ(X, U j)} (h : IsSec g f) (h' : IsSec g' f') :
    IsSec (g * g') (f * f') := fun i j => by
  simp only [Pi.mul_apply, map_mul, h i j, h' i j, Units.val_mul]
  ring

def cstPi (p : X ⟶ Sp K) (U : J → X.Opens) : K →+* ∀ j, Γ(X, U j) := RingHom.pi fun j => AbLaw.cst p (U j)

theorem isSec_cst (p : X ⟶ Sp K) (c : K) : IsSec (U := U) 1 (cstPi p U c) := fun i j => by
  change rs X _ (AbLaw.cst p _ c) = 1 * rs X _ (AbLaw.cst p _ c)
  rw [rs_cst, rs_cst, _root_.one_mul]

theorem IsSec.add {g : ∀ i j, Γ(X, U i ⊓ U j)ˣ} {f f' : ∀ j, Γ(X, U j)} (h : IsSec g f) (h' : IsSec g f') :
    IsSec g (f + f') := fun i j => by
  simp only [Pi.add_apply, map_add, h i j, h' i j, mul_add]

theorem isSec_zero (g : ∀ i j, Γ(X, U i ⊓ U j)ˣ) : IsSec g 0 := fun i j => by simp

theorem IsSec.pow {g : ∀ i j, Γ(X, U i ⊓ U j)ˣ} {f : ∀ j, Γ(X, U j)} (h : IsSec g f) (m : ℕ) :
    IsSec (g ^ m) (f ^ m) := fun i j => by
  simp only [Pi.pow_apply, map_pow, h i j, mul_pow, Units.val_pow_eq_pow_val]

variable {r : ℕ} {σ : Type} (G : Fin r → ∀ i j, Γ(X, U i ⊓ U j)ˣ)

def gpow (n : Fin r → ℕ) : ∀ i j, Γ(X, U i ⊓ U j)ˣ := ∏ k, G k ^ n k

theorem gpow_add (n n' : Fin r → ℕ) : gpow G (n + n') = gpow G n * gpow G n' := by
  simp only [gpow, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

theorem gpow_zero : gpow G 0 = 1 := by simp [gpow]

theorem gpow_smul (e : ℕ) (n : Fin r → ℕ) : gpow G (e • n) = gpow G n ^ e := by
  simp only [gpow, Pi.smul_apply, smul_eq_mul, ← Finset.prod_pow, ← pow_mul, mul_comm]

theorem gpow_single (k : Fin r) : gpow G (Pi.single k 1) = G k := by
  rw [gpow, Finset.prod_eq_single k (fun b _ hb => by rw [Pi.single_eq_of_ne hb, pow_zero]) (by simp),
    Pi.single_eq_same, pow_one]

variable {G}

theorem isSec_eval (p : X ⟶ Sp K) (col : σ → Fin r) (v : σ → ∀ j, Γ(X, U j)) (hv : ∀ a, IsSec (G (col a)) (v a))
    (n : Fin r → ℕ) (F : MvPolynomial σ K)
    (hF : F.IsWeightedHomogeneous (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) n) :
    IsSec (gpow G n) (MvPolynomial.eval₂Hom (cstPi p U) v F) := by
  have key : ∀ d : σ →₀ ℕ, IsSec (gpow G (Finsupp.weight (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) d))
      (d.prod fun a m => v a ^ m) := fun d => by
    induction d using Finsupp.induction_linear with
    | zero => simpa [gpow_zero] using isSec_cst (U := U) p 1
    | add d d' h h' =>
      rw [map_add, gpow_add, Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
      exact h.mul h'
    | single a m =>
      rw [Finsupp.weight_single, gpow_smul, gpow_single, Finsupp.prod_single_index (h := fun a m => v a ^ m) (pow_zero _)]
      exact (hv a).pow m
  rw [F.as_sum, map_sum]
  refine Finset.sum_induction _ _ (fun _ _ => IsSec.add) (isSec_zero _) fun d hd => ?_
  rw [MvPolynomial.eval₂Hom_monomial, ← hF (MvPolynomial.mem_support_iff.1 hd), ← _root_.one_mul (gpow _ _)]
  exact (isSec_cst p _).mul (key d)

def HasFormSystem (p : X ⟶ Sp K) (w : σ → Fin r → ℕ) (v : σ → ∀ j, Γ(X, U j)) (g : ∀ i j, Γ(X, U i ⊓ U j)ˣ)
    (n : Fin r → ℕ) : Prop :=
  ∃ (τ : Type) (_ : Finite τ) (_ : Nonempty τ) (t : τ → LB.Sec ⟨J, U, g⟩), Emb p _ t ∧
    ∀ a, ∃ F : MvPolynomial σ K, F.IsWeightedHomogeneous w n ∧ (t a).f = MvPolynomial.eval₂Hom (cstPi p U) v F

theorem HasFormSystem.mul {p : X ⟶ Sp K} [IsSeparated p] (hc : ⨆ i, U i = ⊤) {w : σ → Fin r → ℕ}
    {v : σ → ∀ j, Γ(X, U j)} {g g' : ∀ i j, Γ(X, U i ⊓ U j)ˣ} {n n' : Fin r → ℕ}
    (h : HasFormSystem p w v g n) (h' : HasFormSystem p w v g' n') : HasFormSystem p w v (g * g') (n + n') := by
  obtain ⟨τ, _, _, t, ht, hF⟩ := h
  obtain ⟨τ', _, _, t', ht', hF'⟩ := h'
  refine ⟨τ × τ', inferInstance, inferInstance, _, ht.mul hc ht', fun a => ?_⟩
  obtain ⟨F, h₁, h₂⟩ := hF a.1
  obtain ⟨F', h₁', h₂'⟩ := hF' a.2
  refine ⟨F * F', h₁.mul h₁', ?_⟩
  rw [map_mul, ← h₂, ← h₂']
  rfl

theorem hasFormSystem_gpow {p : X ⟶ Sp K} [IsSeparated p] (hc : ⨆ i, U i = ⊤) {w : σ → Fin r → ℕ}
    {v : σ → ∀ j, Γ(X, U j)} (h : ∀ k, HasFormSystem p w v (G k) (Pi.single k 1)) (n : Fin r → ℕ) (hn : n ≠ 0) :
    HasFormSystem p w v (gpow G n) n := by
  let S : AddSubmonoid (Fin r → ℕ) :=
    { carrier := {n | n = 0 ∨ HasFormSystem p w v (gpow G n) n}
      zero_mem' := Or.inl rfl
      add_mem' := by
        rintro a b (rfl | ha) (rfl | hb)
        · exact Or.inl (add_zero _)
        · exact Or.inr (by rwa [zero_add])
        · exact Or.inr (by rwa [add_zero])
        · exact Or.inr (by rw [gpow_add]; exact ha.mul hc hb) }
  have : n ∈ S := by
    have e : n = ∑ k, n k • (Pi.single k 1 : Fin r → ℕ) := by
      ext i; simp [Finset.sum_apply, Pi.single_apply]
    rw [e]
    exact S.sum_mem fun k _ => S.nsmul_mem (Or.inr (by rw [gpow_single]; exact h k)) _
  exact this.resolve_left hn

theorem HasFormSystem.veryAmple {p : X ⟶ Sp K} {w : σ → Fin r → ℕ}
    {v : σ → ∀ j, Γ(X, U j)} {g : ∀ i j, Γ(X, U i ⊓ U j)ˣ} {n : Fin r → ℕ}
    (h : HasFormSystem p w v g n) : ∃ (m : ℕ) (t : Fin (m + 1) → LB.Sec ⟨J, U, g⟩), VeryAmpleBy p _ t ∧
      ∀ a, ∃ F : MvPolynomial σ K, F.IsWeightedHomogeneous w n ∧
        (t a).f = MvPolynomial.eval₂Hom (cstPi p U) v F := by
  obtain ⟨τ, _, _, t, ht, hF⟩ := h
  have := Fintype.ofFinite τ
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_pos (α := τ)).ne'
  exact ⟨m, _, ht.veryAmpleBy (Fintype.equivFinOfCardEq hm).symm, fun a => hF _⟩

theorem HasFormSystem.eventually_surj {p : X ⟶ Sp K} {w : σ → Fin r → ℕ}
    {v : σ → ∀ j, Γ(X, U j)} {g : ∀ i j, Γ(X, U i ⊓ U j)ˣ} {n : Fin r → ℕ} (hg : LB.IsLB ⟨J, U, g⟩)
    (h : HasFormSystem p w v g n) : ∃ e₀ : ℕ, ∀ e, e₀ ≤ e → ∀ f, IsSec (g ^ e) f →
      ∃ F : MvPolynomial σ K, F.IsWeightedHomogeneous w (e • n) ∧ MvPolynomial.eval₂Hom (cstPi p U) v F = f := by
  obtain ⟨m, t, ht, hF⟩ := h.veryAmple
  choose F hF hF' using hF
  obtain ⟨e₀, he₀⟩ := exists_form_eq_sec_pw K X p _ m t hg ht
  refine ⟨e₀, fun e he f hf => ?_⟩
  obtain ⟨E, hE, hE'⟩ := he₀ e he ⟨f, fun i j => (hf i j).trans (by
    change _ = ((g i j ^ (e : ℤ)).val) * _
    rw [zpow_natCast]; rfl)⟩
  refine ⟨MvPolynomial.aeval F E, isWeightedHomogeneous_aeval w n F hF E e hE, funext fun k => ?_⟩
  refine Eq.trans ?_ (hE' k).symm
  clear hE hE'
  induction E using MvPolynomial.induction_on with
  | C c => simp only [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.eval₂Hom_C]; rfl
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]
  | mul_X a i ha =>
    simp only [map_mul, Pi.mul_apply, ha, MvPolynomial.aeval_X, MvPolynomial.eval₂Hom_X', ← hF']

theorem finrank_eq_of_h0Is {p : X ⟶ Sp K} {g : ∀ i j, Γ(X, U i ⊓ U j)ˣ} {d : ℕ} (h : SectionsHaveFiniteDimension p ⟨J, U, g⟩ d)
    (v : σ → ∀ j, Γ(X, U j)) (W I : Submodule K (MvPolynomial σ K)) [Module.Finite K W]
    (h₁ : ∀ F ∈ W, IsSec g (MvPolynomial.eval₂Hom (cstPi p U) v F))
    (h₂ : ∀ f, IsSec g f → ∃ F ∈ W, MvPolynomial.eval₂Hom (cstPi p U) v F = f)
    (hI : ∀ F ∈ W, F ∈ I ↔ MvPolynomial.eval₂Hom (cstPi p U) v F = 0) :
    Module.finrank K W = d + Module.finrank K ↥(W ⊓ I) := by
  letI : Algebra K (∀ j, Γ(X, U j)) := (cstPi p U).toAlgebra
  obtain ⟨s, hs⟩ := h
  let b : Fin d → ∀ j, Γ(X, U j) := fun i => (s i).f
  have hb : ∀ (a : Fin d → K) j, (∑ i, a i • b i) j = ∑ i, constFn p (U j) (a i) * b i j := fun a j => by
    rw [Finset.sum_apply]; rfl
  have hsec : ∀ a : Fin d → K, IsSec g (∑ i, a i • b i) := fun a =>
    Finset.sum_induction _ _ (fun _ _ => IsSec.add) (isSec_zero _) fun i _ => by
      have := (isSec_cst p (a i)).mul (show IsSec g (b i) from (s i).compat)
      rwa [_root_.one_mul] at this
  have li : LinearIndependent K b := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    obtain ⟨a₀, -, hu⟩ := hs ⟨0, isSec_zero g⟩
    have e₁ := hu a fun j => ((congrFun ha j).symm.trans (hb a j))
    have e₂ := hu 0 fun j => by
      refine Eq.trans ?_ (hb 0 j)
      simp
    exact congrFun (e₁.trans e₂.symm)
  have := finrank_eq_of_surj W I (MvPolynomial.aeval v).toLinearMap (Submodule.span K (Set.range b)) ?_ hI
  · rwa [finrank_span_eq_card li, Fintype.card_fin] at this
  ext f
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨F, hF, rfl⟩
    obtain ⟨a, ha, -⟩ := hs ⟨_, h₁ F hF⟩
    exact ⟨a, funext fun j => (hb a j).trans (ha j).symm⟩
  · rintro ⟨a, rfl⟩
    exact h₂ _ (hsec a)

theorem linComb_eq_gpow {Y : Scheme.{0}} (L : LB Y) {I : Type} [Fintype I] (φ : I → (X ⟶ Y)) (ε : Fin r → I → ℤ)
    (n : Fin r → ℕ) : LB.LinComb L φ (fun i => ∑ k, (n k : ℤ) * ε k i) =
      ⟨I → L.ι, LB.wchart L φ, gpow (fun k => (LB.LinComb L φ (ε k)).g) n⟩ := by
  unfold LB.LinComb gpow
  congr 1
  funext j j'
  simp only [Finset.prod_apply, Pi.pow_apply, ← Finset.prod_pow]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  generalize res _ _ = u
  induction (Finset.univ : Finset (Fin r)) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add, ih, mul_comm (n a : ℤ), zpow_mul,
      zpow_natCast]

theorem lbIso_lbPow_linComb {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) {I : Type} [Fintype I] (φ : I → (X ⟶ Y))
    (ε : Fin r → I → ℤ) (n : Fin r → ℕ) (e : ℕ) :
    LBIso (lbPow (LB.LinComb L φ (fun i => ∑ k, (n k : ℤ) * ε k i)) e)
      (LB.LinComb L φ (fun i => ∑ k, ((e • n) k : ℤ) * ε k i)) := by
  have h := LB.isLB_linComb hL φ (fun i => ∑ k, (n k : ℤ) * ε k i)
  refine (CechPic.cls_eq_iff (LB.isLB_linComb h _ _) (LB.isLB_linComb hL _ _)).1 ?_
  rw [CechPic.cls_lbPow h, CechPic.cls_linComb hL, CechPic.cls_linComb hL, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← natCast_zsmul, smul_smul, Finset.mul_sum]
  simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_mul, _root_.mul_assoc]

theorem exists_polynomial_sectionsDim_multidegree (p : X ⟶ Sp K) [IsSeparated p] (hc : ⨆ j, U j = ⊤) (hr : 1 ≤ r) {m : Fin r → ℕ}
    (th : ∀ k, Fin (m k + 1) → LB.Sec ⟨J, U, G k⟩) (hth : ∀ k, VAmp p _ (th k)) :
    ∃ Ψ : MvPolynomial (Fin r) ℚ, ∀ n : Fin r → ℕ, (∀ k, 1 ≤ n k) → LB.IsLB ⟨J, U, gpow G n⟩ →
      IsAmpleLB ⟨J, U, gpow G n⟩ ∧ ∀ᶠ e : ℕ in Filter.atTop, ∀ d, SectionsHaveFiniteDimension p ⟨J, U, gpow G (e • n)⟩ d →
        (d : ℚ) = MvPolynomial.eval (fun k => ((e * n k : ℕ) : ℚ)) Ψ := by
  let σ := Σ k, Fin (m k + 1)
  let col : σ → Fin r := Sigma.fst
  let v : σ → ∀ j, Γ(X, U j) := fun a => (th a.1 a.2).f
  have hv : ∀ a, IsSec (G (col a)) (v a) := fun a => (th a.1 a.2).compat
  obtain ⟨I, hI₁, hI₂⟩ := exists_homogeneous_core (fun i => (Pi.single (col i) 1 : Fin r → ℕ))
    (MvPolynomial.eval₂Hom (cstPi p U) v)
  obtain ⟨Ψ, n₀, hΨ⟩ := GlobalTheory.exists_multigraded_hilbertPoly K σ r col I hI₁
  refine ⟨Ψ, fun n hn hM => ?_⟩
  have hn0 : n ≠ 0 := fun h => by
    have := hn ⟨0, hr⟩
    rw [h] at this
    exact absurd this (by simp)
  have hsys : HasFormSystem p (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) v (gpow G n) n := by
    refine hasFormSystem_gpow hc (fun k => ?_) n hn0
    refine ⟨Fin (m k + 1), inferInstance, inferInstance, th k, emb_of_vAmp (hth k), fun a => ?_⟩
    refine ⟨MvPolynomial.X ⟨k, a⟩,
      MvPolynomial.isWeightedHomogeneous_X K (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) ⟨k, a⟩, ?_⟩
    rw [MvPolynomial.eval₂Hom_X']
  refine ⟨?_, ?_⟩
  · obtain ⟨_, t, ht, -⟩ := hsys.veryAmple
    exact isAmpleLB_of_veryAmpleBy ht
  obtain ⟨e₀, he₀⟩ := hsys.eventually_surj hM
  filter_upwards [Filter.eventually_ge_atTop e₀, Filter.eventually_ge_atTop n₀] with e he he' d h₁
  have := GlobalTheory.MultiHilbert.finite_colourPiece (K := K) col (e • n)
  have h₂ := finrank_eq_of_h0Is h₁ v
    (MvPolynomial.weightedHomogeneousSubmodule K (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) (e • n))
    (I.restrictScalars K) (fun F hF => isSec_eval _ col v hv _ F hF)
    (fun f hf => he₀ e he f (by rwa [← gpow_smul])) (fun F hF => hI₂ _ F hF)
  have h₃ := hΨ (e • n) fun k => he'.trans (Nat.le_mul_of_pos_right _ (hn k))
  rw [h₂, Nat.cast_add, add_sub_cancel_right] at h₃
  exact h₃

theorem exists_polynomial_sectionsDim_linComb {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (p : X ⟶ Sp K) [IsSeparated p]
    {I : Type} [Fintype I] (φ : I → (X ⟶ Y)) (ε : Fin r → I → ℤ) (hr : 1 ≤ r)
    (hva : ∀ k, ∃ (m : ℕ) (th : Fin (m + 1) → (LB.LinComb L φ (ε k)).Sec), VAmp p _ th) :
    ∃ Ψ : MvPolynomial (Fin r) ℚ, ∀ n : Fin r → ℕ, (∀ k, 1 ≤ n k) →
      IsAmpleLB (LB.LinComb L φ (fun i => ∑ k, (n k : ℤ) * ε k i)) ∧ ∀ᶠ e : ℕ in Filter.atTop, ∀ d,
        SectionsHaveFiniteDimension p (lbPow (LB.LinComb L φ (fun i => ∑ k, (n k : ℤ) * ε k i)) e) d →
        (d : ℚ) = MvPolynomial.eval (fun k => ((e * n k : ℕ) : ℚ)) Ψ := by
  choose m th hth using hva
  obtain ⟨Ψ, hΨ⟩ := exists_polynomial_sectionsDim_multidegree (U := LB.wchart L φ) (G := fun k => (LB.LinComb L φ (ε k)).g) p
    (LB.isLB_linComb hL φ 0).cover hr th hth
  refine ⟨Ψ, fun n hn => ?_⟩
  have hM := LB.isLB_linComb hL φ (fun i => ∑ k, (n k : ℤ) * ε k i)
  obtain ⟨h₁, h₂⟩ := hΨ n hn (by rw [← linComb_eq_gpow]; exact hM)
  refine ⟨by rw [linComb_eq_gpow]; exact h₁, h₂.mono fun e he d hd => he d ?_⟩
  rw [← linComb_eq_gpow]
  exact ((GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K _ p _ (LB.isLB_linComb hM _ _)).2.1 _ (LB.isLB_linComb hL _ _)
    (lbIso_lbPow_linComb hL φ ε n e)).1 _ hd

theorem exists_homogeneous_vol : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (I : Type) [Fintype I] (φ : I → (P.A.left ⟶ P.A.left)) (r : ℕ) (ε : Fin r → I → ℤ), 1 ≤ r → (∀ k, ∃ (m : ℕ) (th : Fin (m + 1) → (LB.LinComb P.L φ (ε k)).Sec), VAmp P.A.hom _ th) → ∃ Φ : MvPolynomial (Fin r) ℚ, Φ.IsHomogeneous P.g ∧ ∀ n : Fin r → ℕ, (∀ k, 1 ≤ n k) → Vol P.A.hom (LB.LinComb P.L φ (fun i => ∑ k, (n k : ℤ) * ε k i)) P.g ((MvPolynomial.eval (fun k => (n k : ℚ)) Φ : ℚ) : ℝ) := by
  intro hL₁ hL₂ K _ _ P I _ φ r ε hr hva
  have := P.isAb.proper
  obtain ⟨Ψ, hΨ⟩ := @exists_polynomial_sectionsDim_linComb K _ _ r _ _ P.isLB P.A.hom (inferInstanceAs (IsSeparated P.A.hom))
    I _ φ ε hr hva
  refine ⟨MvPolynomial.homogeneousComponent P.g Ψ, MvPolynomial.homogeneousComponent_isHomogeneous _ _,
    fun n hn => ?_⟩
  have hM := LB.isLB_linComb P.isLB φ (fun i => ∑ k, (n k : ℤ) * ε k i)
  obtain ⟨h₁, h₂⟩ := hΨ n hn
  obtain ⟨δ, -, h, hh, hlim⟩ := GlobalTheory.VolEx.exists_vol hL₁ hL₂ K P _ hM ((relAmple_iff_isAmpleLB_of_isAffine P.A hM).2 h₁)
  refine ⟨h, hh, ?_⟩
  rw [← eq_eval_homogeneousComponent Ψ n P.g δ h (h₂.mono fun e he => he _ (hh e)) hlim]
  exact hlim

end GlobalTheory.VolPoly
end
