import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.PureTypeModel

open PureType

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in

theorem _root_.GlobalTheory.PureTypeModel.exists_isTypeFn (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (p q : ℕ) :
    ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTypeFn H p q ty := by
  classical
  let n : (E →+* ℂ) → ℕ := fun τ => if τ H.rt = H.rt0 then p else q
  let e := Fintype.equivFin (Σ τ : E →+* ℂ, Fin (n τ))
  refine ⟨_, fun i => (e.symm i).1, ?_⟩
  have hcard : ∀ τ, Nat.card {i // (e.symm i).1 = τ} = n τ := by
    intro τ
    rw [Nat.card_congr ((e.symm.subtypeEquiv (p := fun i => (e.symm i).1 = τ)
      (q := fun s => s.1 = τ) (fun i => Iff.rfl)).trans (Equiv.sigmaSubtype τ)),
      Nat.card_eq_fintype_card, Fintype.card_fin]
  intro τ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hcard]
    simp [n, h]
  · rw [hcard]
    simp [n, h]

theorem hypotheses_of_curve (h₁ : N1ab) (h₂ : N1c) (hT : ThetaUnifAV) (hB : Out.PolBaseChangeSt) (hC : CMCurve)
    (D : Datum H) (hD : 1 ≤ D.p + D.q) (l : Level H) :
    ∃ (Xo : Moduli D l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n)
      (Pe : (FU.Di i).La →+ (Fin g → ℂ)) (_ : IsPeriod (FU.Di i) ty Pe) (k : IntermediateField ℚ ℂ)
      (P₀ : Out.PolAV (Sp k)) (v₀ : epsR k ⟶ P₀.A) (PC : Out.PolAV (Sp ℂ)) (ψ : PC.A.left ⟶ P₀.A.left)
      (u₀ : HolUnif PC.A PC.L PC.g) (c : ℂ),
      KA l ≤ k ∧ FiniteDimensional ℚ k ∧ P₀.g = 1 ∧ IsTangent v₀ ∧ PC.g = 1 ∧
      IsGrpPullback PC.A P₀.A (spMap (algebraMap k ℂ)) ψ ∧ LBIso PC.L (P₀.L.pull ψ) ∧ IsThetaUnif u₀ ∧ c ≠ 0 ∧
      IsQuadLattice u₀.Λ H.d c ∧
      ∃ (M : IntermediateField ℚ ℂ) (P : Out.PolAV (Sp (𝓞 M))) (v : epsR (𝓞 M) ⟶ P.A) (f : 𝓞 M →+* k)
        (π : P₀.A.left ⟶ P.A.left), IsLieBasis ![v] ∧ IsGrpPullback P₀.A P.A (spMap f) π ∧ IsVecOver f π v v₀ := by
  have hm := H.d_mod
  obtain ⟨K, _, h2, hr⟩ := exists_quadraticField_sq_eq_neg (d := H.d) (by omega)
  obtain ⟨M, _, w, P, v, hw, hg, hv, -, hΛ, -⟩ := hC H.d (by omega) H.d_prime.squarefree (by omega) K h2 hr
  obtain ⟨Xo, g, ty, FU, i, Pe, hP, k, P₀, v₀, PC, ψ, u₀, c, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, b₁, ⟨f, π, b₂, b₃⟩, -⟩ :=
    hypotheses_inhabited h₁ h₂ hT hB
      (fun D => ⟨exists_isTypeFn H D.p D.q, fun g ty h => PeriodNonempty.exists_isPeriod E H D g ty h⟩) M P hg v (hv.1 0)
      (fun PC ψ u e h hL _ => by
        obtain ⟨c, -, hc⟩ := hΛ PC ψ ⟨e.trans hg.symm, h, LBIso.symm hL⟩ u
        exact ⟨c, fun z => by rw [hc z, hw]⟩) D hD l
  exact ⟨Xo, g, ty, FU, i, Pe, hP, k, P₀, v₀, PC, ψ, u₀, c, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, b₁, M, P, v, f, π, hv, b₂, b₃⟩

theorem exists_point_cyclotomic (h₁ : N1ab) (h₂ : N1c) (hT : ThetaUnifAV) (hB : Out.PolBaseChangeSt) (hC : CMCurve)
    (h : CMPoint) (A : ℕ) (hA : 0 < A) :
    ∃ (Xo : Moduli (HostModel.hypDatum HostModel.host) (HostModel.level HostModel.host A hA))
      (k : IntermediateField ℚ ℂ) (R : Subalgebra k ℂ) (y : Sp R ⟶ Xo.X) (t : SAB HostModel.host (Sp R)),
      R.FG ∧ Nonempty (SABMap t Xo.univ.t y) := by
  obtain ⟨Xo, g, ty, FU, i, Pe, hP, k, P₀, v₀, PC, ψ, u₀, c, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, b₁, -⟩ :=
    hypotheses_of_curve h₁ h₂ hT hB hC (HostModel.hypDatum HostModel.host) (by simp) (HostModel.level HostModel.host A hA)
  obtain ⟨R, hR, -, y, t, m, -⟩ := h _ _ _ _ Xo g ty FU i Pe hP k a₁ a₂ P₀ v₀ a₃ a₄ PC ψ u₀ c a₅ a₆ a₇ a₈ a₉ b₁
    (fun _ => {0}) (fun _ => Set.finite_singleton _) ⊥ Subalgebra.fg_bot
  exact ⟨Xo, k, R, y, t, hR, ⟨m⟩⟩

section Linear

variable {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe)

theorem smul_mem_range (ε : ℤˣ) {a : D.La} (ha : a ∈ lat hP (((ε : ℤ) : ℂ) * H.rt0)) (m n : ℤ) :
    ((m : ℂ) + n * ((1 + Complex.I * Real.sqrt H.d) / 2)) • Pe a ∈ Pe.range := by
  have hs : (((ε : ℤ) : ℂ) * H.rt0) ^ 2 = (Complex.I * Real.sqrt H.d) ^ 2 := by
    have e : ((ε : ℤ) : ℂ) ^ 2 = 1 := by exact_mod_cast (Int.units_sq ε ▸ rfl : ((ε ^ 2 : ℤˣ) : ℤ) = 1)
    rw [mul_pow, mul_pow, e, H.sqrt_neg_disc_sq, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    simp
  have hw := period_w0_smul hP ha
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hs with h | h
  · refine ⟨m • a + n • H.w0 • a, ?_⟩
    rw [map_add, map_zsmul, map_zsmul, hw, h]
    funext j; simp; ring
  · refine ⟨m • a + n • (a - H.w0 • a), ?_⟩
    rw [map_add, map_zsmul, map_zsmul, map_sub, hw, h]
    funext j; simp; ring

theorem eq_zero_of_opposite_sign {ρ : ℂ} (hρ : ρ ≠ 0) {a : D.La} (ha : a ∈ lat hP ρ)
    (h : Pe (H.rt • a) = (-ρ) • Pe a) : a = 0 := by
  rw [period_rt_smul hP ha] at h
  apply hP.2.1
  rw [map_zero]
  funext j
  have e := congrFun h j
  simp only [Pi.smul_apply, smul_eq_mul] at e
  have e' : (2 * ρ) * Pe a j = 0 := by linear_combination e
  exact (mul_eq_zero.1 e').resolve_left (mul_ne_zero two_ne_zero hρ)

end Linear

theorem smul_mem_range_of_exp {D : Datum H} {l : Level H} {Xo : Moduli D l} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) {Pe : (FU.Di i).La →+ (Fin g → ℂ)}
    (hP : IsPeriod (FU.Di i) ty Pe) {k : IntermediateField ℚ ℂ} (P₀ : Out.PolAV (Sp k))
    {PC : Out.PolAV (Sp ℂ)} {ψ : PC.A.left ⟶ P₀.A.left} (hψ : IsGrpPullback PC.A P₀.A (spMap (algebraMap k ℂ)) ψ)
    (u₀ : HolUnif PC.A PC.L PC.g) (c : ℂ) (hΛ : IsQuadLattice u₀.Λ H.d c)
    {R : Type} [CommRing R] [Algebra k R] (j : R →ₐ[k] ℂ)
    (f : pullback P₀.A.hom (spMap (algebraMap k R)) ⟶ Xo.univ.t.G.left) (a : (FU.Di i).La)
    (h : ∀ (z : ℂ) (x : Sp ℂ ⟶ pullback P₀.A.hom (spMap (algebraMap k R))),
      x ≫ pullback.fst _ _ = (u₀.ex fun _ => c * z).left ≫ ψ → x ≫ pullback.snd _ _ = spMap j.toRingHom →
      x ≫ f = (FU.ex i Pe (z • Pe a)).left) (m n : ℤ) :
    ((m : ℂ) + n * ((1 + Complex.I * Real.sqrt H.d) / 2)) • Pe a ∈ Pe.range := by
  set z : ℂ := (m : ℂ) + n * ((1 + Complex.I * Real.sqrt H.d) / 2)
  have w : ((u₀.ex fun _ => c * z).left ≫ ψ) ≫ P₀.A.hom = spMap j.toRingHom ≫ spMap (algebraMap k R) := by
    rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w]
    show 𝟙 _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [Category.id_comp, ← Spec.map_comp]
    congr 1
    ext x; simp
  have e₁ : (u₀.ex fun _ => c * z) = 1 := (u₀.ker _).2 ((hΛ _).2 ⟨m, n, rfl⟩)
  have e₀ : (u₀.ex fun _ => c * 0) = 1 := (u₀.ker _).2 (by
    rw [mul_zero]; exact u₀.Λ.zero_mem)
  have ha := h z (pullback.lift _ _ w) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  have hb := h 0 (pullback.lift _ _ w) (by rw [pullback.lift_fst, e₁, e₀]) (pullback.lift_snd _ _ _)
  rw [hb, zero_smul, (FU.ex_ker i Pe hP 0).2 (zero_mem _)] at ha
  exact (FU.ex_ker i Pe hP _).1 (Over.OverMorphism.ext ha).symm

theorem map_zero_neg {D : Datum H} {R : Type} [CommRing R] {t : SAB H (Sp R)} {B : Over (Sp R)} [GrpObj B]
    {M : LB B.left} {v : epsR R ⟶ B} {L : Submodule (𝓞 E) D.La} {ρ : R} {S : Set L} {φ : L → (B ⟶ t.G)}
    (h : IsHomFamily t B M v L ρ S φ) : φ 0 = 1 ∧ ∀ a, φ (-a) = (φ a)⁻¹ := by
  have h0 : φ 0 = 1 := by
    have e := h.2.1 0 0
    rw [add_zero] at e
    exact left_eq_mul.1 e
  exact ⟨h0, fun a => eq_inv_of_mul_eq_one_left (by rw [← h.2.1, neg_add_cancel, h0])⟩

section Mixed

open HostModel PeriodNonempty
open scoped TensorProduct

theorem isPeriod_of_coord (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ)) (J : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La)
    (hinv : ∀ x y, D.EF.baseChange ℝ (J x) (J y) = D.EF.baseChange ℝ x y)
    (hpos : ∀ x, x ≠ 0 → 0 < D.EF.baseChange ℝ (J x) x) (e : (ℝ ⊗[ℤ] D.La) ≃ₗ[ℝ] (Fin g → ℂ))
    (heJ : ∀ v, e (J v) = Complex.I • e v) (heρ : ∀ (a : 𝓞 E) x i, e (1 ⊗ₜ (a • x)) i = ty i (a : E) * e (1 ⊗ₜ x) i) :
    ∃ P : D.La →+ (Fin g → ℂ), IsPeriod D ty P ∧ ∀ x, P x = e (1 ⊗ₜ x) := by
  classical
  haveI := D.fin
  haveI := D.proj
  haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  haveI : Module.Flat ℤ D.La := Module.Flat.trans ℤ (𝓞 E) D.La
  haveI : Module.Free ℤ D.La := inferInstance
  let P : D.La →+ (Fin g → ℂ) :=
    { toFun := fun x => e (1 ⊗ₜ x)
      map_zero' := by simp
      map_add' := fun x y => by rw [TensorProduct.tmul_add, map_add] }
  have hP : ∀ x, P x = e (1 ⊗ₜ x) := fun _ => rfl
  let b := Module.Free.chooseBasis ℤ D.La
  let c := (b.baseChange ℝ).map e
  have hc : ∀ i, c i = P (b i) := fun i => by simp [c, hP]
  have hrange : P.range = (Submodule.span ℤ (Set.range c)).toAddSubgroup := by
    have h1 : Set.range c = P.toIntLinearMap '' Set.range b := by
      rw [← Set.range_comp]; congr 1; funext i; exact hc i
    rw [h1, ← Submodule.map_span, b.span_eq]
    ext z; simp
  refine ⟨P, ⟨heρ, ?_, ?_, ?_, ?_⟩, hP⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    rw [hP, e.map_eq_zero_iff] at hx
    apply b.ext_elem
    intro i
    have := congrArg (fun v => (b.baseChange ℝ).repr v i) hx
    simpa using this
  · rw [hrange]; infer_instance
  · rw [eq_top_iff, ← c.span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨b i, (hc i).symm⟩
  · have halt0 : ∀ x y, D.EF x y = -D.EF y x := fun x y => by
      have := D.alt (x + y)
      simp only [map_add, LinearMap.add_apply, D.alt] at this
      linarith
    have halt : ∀ x y, D.EF.baseChange ℝ x y = -D.EF.baseChange ℝ y x := fun x y => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x x' h h' => simp only [map_add, LinearMap.add_apply, h, h']; ring
      | tmul r x =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | add y y' h h' => simp only [map_add, LinearMap.add_apply, h, h']; ring
        | tmul r' y => simp [halt0 x y, mul_comm]
    have hs : ∀ z, e.symm (Complex.I • z) = J (e.symm z) := fun z => by
      rw [e.symm_apply_eq, heJ, e.apply_symm_apply]
    obtain ⟨Hm, h1, h2, h3⟩ := exists_herm
      ((D.EF.baseChange ℝ).comp e.symm.toLinearMap e.symm.toLinearMap)
      (fun x y => halt _ _) (fun x y => by simp [hs, hinv])
      (fun x hx => by simpa [hs] using hpos (e.symm x) (by simpa using hx))
    refine ⟨Hm, h1, h2, fun x y => ?_⟩
    rw [h3]
    simp [hP]

def scale (H : Host E) (s t : ℝ) : ℝ ⊗[ℤ] HypLattice H →ₗ[ℝ] ℝ ⊗[ℤ] HypLattice H :=
  s • (LinearMap.inl ℤ _ _ ∘ₗ LinearMap.fst ℤ _ _).baseChange ℝ + t • (LinearMap.inr ℤ _ _ ∘ₗ LinearMap.snd ℤ _ _).baseChange ℝ

theorem scale_tmul (s t r : ℝ) (u : HypLattice H) :
    scale H s t (r ⊗ₜ u) = s • r ⊗ₜ (u.1, 0) + t • r ⊗ₜ (0, u.2) := by simp [scale]

theorem scale_scale {s t : ℝ} (h : s * t = 1) (x) : scale H s t (scale H t s x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul r u =>
    rw [scale_tmul, map_add, map_smul, map_smul, scale_tmul, scale_tmul]
    simp only [Prod.mk_zero_zero, TensorProduct.tmul_zero, smul_zero, add_zero, zero_add, smul_smul, h, mul_comm t s,
      one_smul, ← TensorProduct.tmul_add, Prod.mk_add_mk]

theorem form_scale {s t : ℝ} (h : s * t = 1) (x y) :
    (hypForm H).baseChange ℝ (scale H s t x) (scale H s t y) = (hypForm H).baseChange ℝ x y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul r u =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul r' v =>
      simp [scale_tmul]
      linear_combination ((ConjDual.toDual H u.2 v.1 : ℤ) - (ConjDual.toDual H v.2 u.1 : ℤ) : ℝ) * r * r' * h

theorem exists_period_both_types (H : Host E) : ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ))
    (Pe : (hypDatum H).La →+ (Fin g → ℂ)) (hP : IsPeriod (hypDatum H) ty Pe), IsTypeFn H 1 1 ty ∧
    ∀ ε : ℤˣ, lat hP (((ε : ℤ) : ℂ) * H.rt0) ≠ ⊥ := by
  obtain ⟨g, ty, hty⟩ := exists_isTypeFn H 1 1
  let ρ₀ : 𝓞 E →+* Module.End ℤ (HypLattice H) :=
    (Algebra.lsmul ℤ ℤ (HypLattice H) : 𝓞 E →ₐ[ℤ] Module.End ℤ (HypLattice H))
  let ρ : 𝓞 E →+* Module.End ℝ (ℝ ⊗[ℤ] HypLattice H) :=
    (Module.End.baseChangeHom ℤ ℝ (HypLattice H) : Module.End ℤ _ →+* Module.End ℝ (ℝ ⊗[ℤ] HypLattice H)).comp ρ₀
  have hρ : ∀ a x, ρ a (1 ⊗ₜ x) = 1 ⊗ₜ (a • x) := fun a x => rfl
  obtain ⟨e, heJ, heρ⟩ := exists_diag_real (hypJ H) (hypJ_hypJ H) ρ ty (fun a => by
    have ht := sum_type H hty (a : E)
    simp only [Nat.cast_one, _root_.one_mul, sum_add_conj_eq_trace] at ht
    refine ⟨hypJ_comm H a _ (hρ a), ?_, ?_⟩
    · rw [trace_of_smul H a _ (hρ a), ht, Complex.intCast_re]
    · rw [trace_hypJ_comp H a _ (hρ a), ht, Complex.intCast_im, mul_zero])
  have hd : (0 : ℝ) < H.d := Nat.cast_pos.2 H.d_prime.pos
  obtain ⟨s, hs0, hs⟩ : ∃ s : ℝ, s ≠ 0 ∧ s ^ 4 = H.d := ⟨√(√H.d), by positivity, by
    rw [show 4 = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by positivity), Real.sq_sqrt hd.le]⟩
  have h₁ := mul_inv_cancel₀ hs0
  have h₂ := inv_mul_cancel₀ hs0
  let T : (ℝ ⊗[ℤ] HypLattice H) ≃ₗ[ℝ] (ℝ ⊗[ℤ] HypLattice H) := LinearEquiv.ofLinear (scale H s s⁻¹) (scale H s⁻¹ s)
    (LinearMap.ext (scale_scale h₁)) (LinearMap.ext (scale_scale h₂))
  have hT : ∀ x, T x = scale H s s⁻¹ x := fun _ => rfl
  have he : ∀ (a : 𝓞 E) (x : HypLattice H) i, e (1 ⊗ₜ (a • x)) i = ty i (a : E) * e (1 ⊗ₜ x) i := fun a x i => by
    rw [← hρ, heρ]
  obtain ⟨P, hP, hPe⟩ := isPeriod_of_coord (hypDatum H) ty (scale H s⁻¹ s ∘ₗ hypJ H ∘ₗ scale H s s⁻¹)
    (fun x y => by
      simp only [LinearMap.comp_apply]
      exact (form_scale h₂ _ _).trans ((hypForm_hypJ_hypJ H _ _).trans (form_scale h₁ _ _)))
    (fun x hx => by
      have h := hypForm_hypJ_pos H (T x) (by simpa using hx)
      rw [← form_scale h₂, hT, scale_scale h₂] at h
      exact h)
    (T.trans e) (fun v => by
      simp only [LinearEquiv.trans_apply, LinearMap.comp_apply, hT]
      rw [scale_scale h₁, heJ])
    (fun a x i => by
      have e₁ := he a (x.1, 0) i
      have e₂ := he a (0, x.2) i
      simp only [Prod.smul_mk, smul_zero] at e₁ e₂
      simp only [LinearEquiv.trans_apply, hT, scale_tmul, map_add, map_smul, Pi.add_apply, Pi.smul_apply,
        Complex.real_smul, Prod.smul_fst, Prod.smul_snd, e₁, e₂]
      ring)
  refine ⟨g, ty, P, hP, hty, fun ε hε => ?_⟩
  have hsq : ∀ j, ty j (H.rt : E) ^ 2 = -(H.d : ℂ) := fun j => by
    have := congrArg (fun x : 𝓞 E => ty j (x : E)) H.rt_sq
    simpa using this
  have hsC : (s : ℂ) ^ 4 = H.d := by exact_mod_cast hs
  have hs0' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0
  have hε2 : (((ε : ℤ) : ℂ) * H.rt0) ^ 2 = -(H.d : ℂ) := by
    have e : ((ε : ℤ) : ℂ) ^ 2 = 1 := by exact_mod_cast (Int.units_sq ε ▸ rfl : ((ε ^ 2 : ℤˣ) : ℤ) = 1)
    rw [mul_pow, e, H.sqrt_neg_disc_sq, _root_.one_mul]
  obtain ⟨δ, hδ⟩ : ∃ δ : ℤ, (δ : ℂ) * Complex.I * (((ε : ℤ) : ℂ) * H.rt0) = s ^ 2 := by
    have : (Complex.I * (((ε : ℤ) : ℂ) * H.rt0)) ^ 2 = ((s : ℂ) ^ 2) ^ 2 := by
      rw [mul_pow, hε2, Complex.I_sq, ← hsC]; ring
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 this with h | h
    · exact ⟨1, by push_cast; linear_combination h⟩
    · exact ⟨-1, by push_cast; linear_combination -h⟩
  have hm : (((1 : 𝓞 E), traceDual H ((δ * H.rt) • 1)) : (hypDatum H).La) ∈ lat hP (((ε : ℤ) : ℂ) * H.rt0) := by
    intro j hj
    have hj' : ty j (H.rt : E) = -(((ε : ℤ) : ℂ) * H.rt0) :=
      (sq_eq_sq_iff_eq_or_eq_neg.1 ((hsq j).trans hε2.symm)).resolve_left hj
    have e₁ := he (δ * H.rt) (1, 0) j
    simp only [Prod.smul_mk, smul_zero] at e₁
    rw [hPe]
    simp only [LinearEquiv.trans_apply, hT, scale_tmul, map_add, LinearEquiv.map_smul, Pi.add_apply, Pi.smul_apply,
      Complex.real_smul, ← hypJ_inl, heJ, smul_eq_mul] at e₁ ⊢
    rw [e₁]
    push_cast
    rw [map_mul, show ty j ((δ : 𝓞 E) : E) = δ by simp, hj']
    field_simp
    linear_combination -(e (1 ⊗ₜ (1, 0)) j) * hδ
  rw [hε, Submodule.mem_bot] at hm
  exact one_ne_zero (congrArg Prod.fst hm)

end Mixed

end GlobalTheory.PureTypeModel
