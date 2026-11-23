import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeGram
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGrpObjPolarised
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl.Test

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Frames

variable {S : Scheme.{0}} {R : Type} [CommRing R] {O : Type} [CommRing O]

theorem lieMult_iff_exists_frame {k : Type} [Field k] {G : Over S} [GrpObj G] (act : OAct O G) (t : Sp k ⟶ S)
    (τ : O →+* k) (n : ℕ) : LieMult act t τ n ↔ ∃ v : Fin n → (epsAt t ⟶ G), IsEigFrame act t τ v := Iff.rfl

variable {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {V : Type} [AddCommGroup V] [Module R V]

theorem pt_zero (M : LieModel G x V) : M.pt 0 = 1 := by
  have h := M.add 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem pt_sum (M : LieModel G x V) {n : ℕ} (e : Fin n → V) :
    M.pt (∑ i, e i) = (List.ofFn fun i => M.pt (e i)).prod := by
  induction n with
  | zero => simp [pt_zero]
  | succ n ih => rw [Fin.sum_univ_succ, M.add, ih, List.ofFn_succ, List.prod_cons]

theorem isComb_iff (M : LieModel G x V) {n : ℕ} (c : Fin n → R) (e : Fin n → V) (w : V) :
    IsComb c (fun i => M.pt (e i)) (M.pt w) ↔ w = ∑ i, c i • e i := by
  constructor
  · rintro ⟨u, hu, hw⟩
    have : u = fun i => M.pt (c i • e i) := funext fun i => Over.OverMorphism.ext ((hu i).trans (M.smul _ _).symm)
    rw [this, ← pt_sum] at hw
    exact M.inj hw
  · rintro rfl
    exact ⟨fun i => M.pt (c i • e i), fun i => M.smul _ _, pt_sum M _⟩

theorem isEigVec_iff (M : LieModel G x V) (act : OAct O G) (ρ : O →+* Module.End R V) (h : M.IsActOf act.act ρ)
    (τ : O →+* R) (e : V) : IsEigVec act x τ (M.pt e) ↔ e ∈ eigSp ρ τ := by
  simp only [IsEigVec, M.tan, true_and, eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  refine forall_congr' fun a => ?_
  rw [← h a e]
  constructor
  · intro H
    exact M.inj (Over.OverMorphism.ext (H.trans (M.smul _ _).symm))
  · intro H
    rw [H]; exact M.smul _ _

theorem isEigFrame_iff (M : LieModel G x V) (act : OAct O G) (ρ : O →+* Module.End R V) (h : M.IsActOf act.act ρ)
    (τ : O →+* R) {n : ℕ} (e : Fin n → V) : IsEigFrame act x τ (fun i => M.pt (e i)) ↔
      LinearIndependent R e ∧ Submodule.span R (Set.range e) = eigSp ρ τ := by
  simp only [IsEigFrame, isEigVec_iff M act ρ h]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨Fintype.linearIndependent_iff.2 fun c hc => ?_, le_antisymm ?_ fun w hw => ?_⟩
    · obtain ⟨c0, -, hu⟩ := h2 (M.pt 0) ((isEigVec_iff M act ρ h τ 0).2 (Submodule.zero_mem _))
      have a := hu c ((isComb_iff M c e 0).2 hc.symm)
      have b := hu 0 ((isComb_iff M 0 e 0).2 (by simp))
      exact fun i => congrFun (a.trans b.symm) i
    · rintro _ hw
      exact Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact h1 i) hw
    · obtain ⟨c, hc, -⟩ := h2 (M.pt w) ((isEigVec_iff M act ρ h τ w).2 hw)
      rw [(isComb_iff M c e w).1 hc]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => h2 ▸ Submodule.subset_span ⟨i, rfl⟩, fun w hw => ?_⟩
    obtain ⟨w, rfl⟩ := M.onto w hw.1
    have hw' := (isEigVec_iff M act ρ h τ w).1 hw
    rw [← h2, Submodule.mem_span_range_iff_exists_fun] at hw'
    obtain ⟨c, hc⟩ := hw'
    refine ⟨c, (isComb_iff M c e w).2 hc.symm, fun d hd => ?_⟩
    have hd' := (isComb_iff M d e w).1 hd
    have := Fintype.linearIndependent_iff.1 h1 (d - c) (by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, hc, ← hd', sub_self])
    exact funext fun i => sub_eq_zero.1 (this i)

open GlobalTheory.Diag in

def torusModel (x : Sp R ⟶ S) (X : Type) [AddCommGroup X] : LieModel (splitTorus S X) x (X →+ R) where
  pt c := epsVec _ c
  tan c := (reduces_iff (by rw [← Category.assoc, fstHom_base, Category.id_comp]) _).2
    ((exists_epsVec_iff _).1 ⟨c, rfl⟩)
  inj := epsVec_injective
  onto v hv := (exists_epsVec_iff _).2
    ((reduces_iff (by rw [← Category.assoc, fstHom_base, Category.id_comp]) _).1 hv)
  add := epsVec_add
  smul a c := (left_eq_epsScaleR_iff a (by rw [← Category.assoc, ← epsScaleR_base]) c _).2 rfl

def regAct (O R : Type) [CommRing O] [CommRing R] : O →+* Module.End R (O →+ R) where
  toFun a :=
    { toFun := fun c => c.comp (DistribSMul.toAddMonoidHom O a)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by ext c y; simp
  map_mul' a b := by
    ext c y
    simp only [AddMonoidHom.comp_apply, DistribSMul.toAddMonoidHom_apply, smul_eq_mul, LinearMap.coe_mk, AddHom.coe_mk,
      Module.End.mul_apply]
    congr 1
    ring
  map_zero' := by ext c y; simp
  map_add' a b := by ext c y; simp [add_mul]

theorem torusModel_act (x : Sp R ⟶ S) :
    (torusModel x O).IsActOf (GlobalTheory.Diag.diagAct S O O).act (regAct O R) :=
  fun _ c => (GlobalTheory.Diag.epsVec_comp_diagMap c _).symm

theorem mem_eigSp_regAct (τ : O →+* R) (c : O →+ R) : c ∈ eigSp (regAct O R) τ ↔ ∀ a y, c (a * y) = τ a * c y := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero, AddMonoidHom.ext_iff, regAct]

theorem torus_frame (x : Sp R ⟶ S) (τ : O →+* R) :
    IsEigFrame (GlobalTheory.Diag.diagAct S O O) x τ (fun _ : Fin 1 => (torusModel x O).pt τ.toAddMonoidHom) := by
  refine (isEigFrame_iff (torusModel x O) _ _ (torusModel_act x) τ (fun _ : Fin 1 => τ.toAddMonoidHom)).2
    ⟨Fintype.linearIndependent_iff.2 fun c hc i => ?_, le_antisymm ?_ fun w hw => ?_⟩
  · have := DFunLike.congr_fun hc 1
    rw [Subsingleton.elim i 0]
    simpa using this
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact (mem_eigSp_regAct τ _).2 (by simp)
  · rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun _ => w 1, ?_⟩
    ext a
    have := (mem_eigSp_regAct τ w).1 hw a 1
    rw [_root_.mul_one] at this
    simp [this, mul_comm]

theorem torus_not_eig (x : Sp R ⟶ S) {τ σ : O →+* R} (h : τ ≠ σ) :
    ¬ IsEigVec (GlobalTheory.Diag.diagAct S O O) x σ ((torusModel x O).pt τ.toAddMonoidHom) := fun H => h <| by
  have := (mem_eigSp_regAct σ _).1 ((isEigVec_iff _ _ _ (torusModel_act x) σ _).1 H)
  ext a
  simpa using this a 1

theorem torus_not_frame_nonunit (x : Sp R ⟶ S) (τ : O →+* R) {r : R} (hr : ¬ IsUnit r) :
    ¬ IsEigFrame (GlobalTheory.Diag.diagAct S O O) x τ (fun _ : Fin 1 => (torusModel x O).pt (r • τ.toAddMonoidHom)) :=
  fun H => hr <| by
    have h := ((isEigFrame_iff (torusModel x O) _ _ (torusModel_act x) τ
      (fun _ : Fin 1 => r • τ.toAddMonoidHom)).1 H).2
    have hm : τ.toAddMonoidHom ∈ eigSp (regAct O R) τ := (mem_eigSp_regAct τ _).2 (by simp)
    rw [← h, Submodule.mem_span_range_iff_exists_fun] at hm
    obtain ⟨c, hc⟩ := hm
    have := DFunLike.congr_fun hc 1
    exact IsUnit.of_mul_eq_one (c 0) (by simpa [mul_comm] using this)

end Frames

section Gram

theorem gram_herm {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {x : Sp ℂ ⟶ S} {n : ℕ}
    {v : Fin n → (epsAt x ⟶ G)} {Γ : Matrix (Fin n) (Fin n) ℂ} (h : IsHodgeGram G L x v Γ) :
    Γ.IsHermitian ∧ ∀ i, 0 ≤ (Γ i i).re := by
  obtain ⟨Q, ψ, v', u, Hm, χ, W, -, -, hA, -, hΓ⟩ := h
  refine ⟨?_, fun i => ?_⟩
  · ext i j
    rw [Matrix.conjTranspose_apply, hΓ, hΓ]
    have e : star (hermForm Hm (W j) (W i)) = hermForm Hm (W i) (W j) := by
      simp only [hermForm, dotProduct, Matrix.mulVec, star_sum, star_mul', Finset.mul_sum, Pi.star_apply, star_star]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [hA.1.apply a b]; ring
    rw [star_mul', e]; simp
  · rw [hΓ, Complex.re_ofReal_mul]
    refine mul_nonneg Real.pi_pos.le ?_
    by_cases h0 : W i = 0
    · simp [h0, hermForm]
    · exact (hA.2.1 _ h0).le

theorem gram_exists (hT : ThetaUnifAV) (P : Out.PolAV (Sp ℂ)) :
    ∃ (v : Fin P.g → (epsAt (𝟙 (Sp ℂ)) ⟶ P.A)) (Γ : Matrix (Fin P.g) (Fin P.g) ℂ),
      (∀ i, IsTanAt P.A (𝟙 _) (v i)) ∧ IsHodgeGram P.A P.L (𝟙 _) v Γ ∧ ∀ i, 0 < (Γ i i).re := by
  obtain ⟨rig, hr⟩ := P.rigid
  obtain ⟨u, Hm, χ, -, hA, -, -, hv, -⟩ := hT P rig hr
  choose v' hv' using fun i : Fin P.g => (hv (Pi.single i 1)).exists
  refine ⟨fun i => Over.homMk (v' i).left ((Over.w (v' i)).trans (Category.comp_id _).symm),
    fun i j => Real.pi * hermForm Hm (Pi.single i 1) (Pi.single j 1), fun i => ?_,
    ⟨P, 𝟙 _, v', u, Hm, χ, fun i => Pi.single i 1, ?_, ?_, hA, fun i => ⟨Category.comp_id _, (hv' i).2⟩,
      fun _ _ => rfl⟩, fun i => ?_⟩
  · exact (hv' i).1.trans (congrArg Over.Hom.left (one_eq_one (M := P.A)))
  · haveI : IsMonHom (Iso.refl P.A).hom := inferInstanceAs (IsMonHom (𝟙 P.A))
    exact isGrpPullback_of_iso (Iso.refl P.A)
  · exact (GlobalTheory.ThetaAffineGlue.lbIso_pull_id P.isLB).symm
  · rw [Complex.re_ofReal_mul]
    exact mul_pos Real.pi_pos (hA.2.1 _ (by simp))

theorem gram_inhabited : ∃ (P : Out.PolAV (Sp ℂ)) (v : Fin P.g → (epsAt (𝟙 (Sp ℂ)) ⟶ P.A))
    (Γ : Matrix (Fin P.g) (Fin P.g) ℂ), P.g = 1 ∧ (∀ i, IsTanAt P.A (𝟙 _) (v i)) ∧
      IsHodgeGram P.A P.L (𝟙 _) v Γ ∧ ∀ i, 0 < (Γ i i).re := by
  have hΔ : IsUnit (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℂ).Δ := by
    simp [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
  obtain ⟨P, -, -, hP, -⟩ := GlobalTheory.WeierstrassCurve.exists_polAV ℂ _ hΔ
  obtain ⟨v, Γ, h⟩ := gram_exists GlobalTheory.thetaUnifAV_all P
  exact ⟨P, v, Γ, hP, h⟩

end Gram

section Form

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem tauIn_coe {l : Level H} (c : Coeff l) (τ : E →+* ℂ) (a : 𝓞 E) : ((tauIn c τ a : c.F) : ℂ) = τ a := rfl

theorem trace_basis_mul_sesq (D : Datum H) (x y : D.La) (j) :
    Algebra.trace ℚ E ((RingOfIntegers.basis E j : E) * sesq D x y) = D.EF (RingOfIntegers.basis E j • x) y := by
  classical
  have key : ∀ k, Algebra.trace ℚ E ((RingOfIntegers.basis E j : E) * HT.dualInt E k) = if j = k then 1 else 0 := by
    intro k
    have := LinearMap.BilinForm.apply_dualBasis_left (B := Algebra.traceForm ℚ E) (traceForm_nondegenerate ℚ E)
      (integralBasis E) k j
    rw [Algebra.traceForm_apply, integralBasis_apply, mul_comm] at this
    convert this
    unfold HT.dualInt
    congr!
  simp only [sesq, Finset.mul_sum, map_sum]
  have : ∀ k, Algebra.trace ℚ E ((RingOfIntegers.basis E j : E) *
      ((D.EF (RingOfIntegers.basis E k • x) y : E) * HT.dualInt E k)) =
      (D.EF (RingOfIntegers.basis E k • x) y : ℚ) * if j = k then 1 else 0 := by
    intro k
    rw [mul_left_comm, ← zsmul_eq_mul, map_zsmul, key, zsmul_eq_mul]
  simp [this]

theorem trace_mul_sesq (D : Datum H) (x y : D.La) (a : 𝓞 E) :
    Algebra.trace ℚ E ((a : E) * sesq D x y) = D.EF (a • x) y := by
  have h : a ∈ Submodule.span ℤ (Set.range (RingOfIntegers.basis E)) := by simp
  induction h using Submodule.span_induction with
  | mem b hb => obtain ⟨j, rfl⟩ := hb; exact trace_basis_mul_sesq D x y j
  | zero => simp
  | add b c _ _ hb hc => simp [add_mul, add_smul, hb, hc]
  | smul m b _ hb =>
    have e : ((m • b : 𝓞 E) : E) * sesq D x y = m • ((b : E) * sesq D x y) := by
      simp only [zsmul_eq_mul, ← _root_.mul_assoc]; simp
    rw [e, map_zsmul, hb, smul_assoc]; simp

theorem eq_of_trace {s t : E} (h : ∀ a : 𝓞 E, Algebra.trace ℚ E ((a : E) * s) = Algebra.trace ℚ E ((a : E) * t)) :
    s = t := by
  rw [← sub_eq_zero]
  refine (traceForm_nondegenerate ℚ E).1 _ fun z => ?_
  have : (Algebra.traceForm ℚ E) (s - t) = 0 := (integralBasis E).ext fun k => by
    rw [Algebra.traceForm_apply, integralBasis_apply, sub_mul, map_sub, mul_comm s, mul_comm t]
    exact sub_eq_zero.2 (h _)
  simp [this]

theorem sesq_smul_left (D : Datum H) (c : 𝓞 E) (x y : D.La) : sesq D (c • x) y = c * sesq D x y :=
  eq_of_trace fun a => by
    rw [trace_mul_sesq, ← _root_.mul_assoc, ← mul_smul, ← trace_mul_sesq]; simp

theorem sesq_smul_right (D : Datum H) (c : 𝓞 E) (x y : D.La) : sesq D x (H.bar c • y) = c * sesq D x y :=
  eq_of_trace fun a => by
    rw [trace_mul_sesq, ← D.adj, ← mul_smul, ← trace_mul_sesq, ← _root_.mul_assoc, mul_comm (a : E)]; simp

theorem sesq_swap (D : Datum H) (x y : D.La) : sesq D y x = -IsCMField.complexConj E (sesq D x y) :=
  eq_of_trace fun a => by
    have hs : D.EF (a • y) x = -D.EF x (a • y) := by
      have := D.alt (a • y + x)
      simp only [map_add, LinearMap.add_apply, D.alt] at this
      linarith
    have h1 : D.EF x (a • y) = D.EF (H.bar.symm a • x) y := by rw [D.adj]; simp
    have h2 : (a : E) = IsCMField.complexConj E (H.bar.symm a : 𝓞 E) := by rw [← H.bar_eq]; simp
    rw [trace_mul_sesq, hs, h1, mul_neg, map_neg, h2, ← map_mul, Int.cast_neg, ← trace_mul_sesq]
    exact congrArg _ (Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) _).symm

theorem eq_zero_of_sesq (D : Datum H) (x : D.La) (h : ∀ y, sesq D x y = 0) : x = 0 :=
  D.unimod.1 (by
    ext y
    have := trace_mul_sesq D x y 1
    simp only [h, mul_zero, map_zero, one_smul] at this
    simpa using this.symm)

omit [NumberField E] [IsCMField E] in
theorem sum_tyPart [Fintype (E →+* ℂ)] {g : ℕ} (ty : Fin g → (E →+* ℂ)) (z : Fin g → ℂ) : ∑ τ, tyPart ty τ z = z := by
  classical
  funext k
  simp [tyPart, Finset.sum_apply]

end Form

end GlobalTheory.CompanionTheory.Ar.Fl.Test
