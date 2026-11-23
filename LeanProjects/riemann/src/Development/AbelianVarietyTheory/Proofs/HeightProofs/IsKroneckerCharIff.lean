import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LinePeriodExponential
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveLieCharacterOfAdjoinGenerator
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPosKeyArchAt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexConjugate

noncomputable section
namespace GlobalTheory.CM.Compare

open GlobalTheory.IndefiniteRowSideFullHecke

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem conj_LFunction_conj {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d} (h₁ : χ ≠ 1)
    (hr : ∀ a, conj (χ a) = χ a) : (conj ∘ χ.LFunction ∘ conj : ℂ → ℂ) = χ.LFunction := by
  have hd := DirichletCharacter.differentiable_LFunction h₁
  have hd' : Differentiable ℂ (conj ∘ χ.LFunction ∘ conj : ℂ → ℂ) := fun z =>
    differentiableAt_conj_conj_iff.mpr (hd _)
  refine AnalyticOnNhd.eq_of_eventuallyEq (z₀ := 2) (fun z _ => hd'.analyticAt z) (fun z _ => hd.analyticAt z) ?_
  refine Filter.eventuallyEq_of_mem
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num))
    fun z (hz : 1 < z.re) => ?_
  simp only [Function.comp]
  rw [χ.LFunction_eq_LSeries hz, χ.LFunction_eq_LSeries (by rwa [Complex.conj_re]), LSeries, LSeries,
    Complex.conj_tsum]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀, hr,
      ← Complex.conj_cpow _ _ (by rw [Complex.natCast_arg]; positivity), Complex.conj_natCast]

theorem logDeriv_im {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d} (h₁ : χ ≠ 1) (hr : ∀ a, conj (χ a) = χ a) :
    (((deriv χ.LFunction 1 / χ.LFunction 1).re : ℝ) : ℂ) = deriv χ.LFunction 1 / χ.LFunction 1 := by
  have e := conj_LFunction_conj h₁ hr
  have e₀ : conj (χ.LFunction 1) = χ.LFunction 1 := by simpa using congrFun e 1
  have e₁ : conj (deriv χ.LFunction 1) = deriv χ.LFunction 1 := by
    have := congrFun (deriv_conj_conj (f := χ.LFunction)) 1
    rw [e] at this
    simpa using this.symm
  rw [← Complex.conj_eq_iff_re, map_div₀, e₀, e₁]

theorem isKroneckerChar_iff (χ : DirichletCharacter ℂ H.d) : IsKroneckerChar χ ↔ χ = LogarithmicDifferentialCharacter.chi H := by
  have h₀ : IsKroneckerChar (LogarithmicDifferentialCharacter.chi H) := isKroneckerChar_quadraticChar (by have := H.d_mod; omega)
  refine ⟨fun h => MulChar.ext' fun a => ?_, fun h => h ▸ h₀⟩
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective a
  rcases Nat.even_or_odd n with hn | hn
  · have ho : Odd (n + H.d) := hn.add_odd (Nat.odd_iff.2 (by have := H.d_mod; omega))
    have := (h _ ho).trans (h₀ _ ho).symm
    simpa using this
  · exact (h n hn).trans (h₀ n hn).symm

theorem dlogL_eq [NeZero H.d] {χ : DirichletCharacter ℂ H.d} (h : IsKroneckerChar χ) :
    (LogarithmicDifferentialCharacter.dlogL H : ℂ) = deriv χ.LFunction 1 / χ.LFunction 1 := by
  obtain rfl := (isKroneckerChar_iff χ).1 h
  exact logDeriv_im (LogarithmicDifferentialCharacter.chi_ne_one H) fun a => by simp [LogarithmicDifferentialCharacter.chi]

theorem logOm_eq [NeZero H.d] {χ : DirichletCharacter ℂ H.d} (h : IsKroneckerChar χ) :
    logOm E χ = (LogarithmicDifferentialCharacter.logOm H : ℝ) := by
  rw [logOm, LogarithmicDifferentialCharacter.logOm, Complex.ofReal_sub, dlogL_eq h]

theorem logOm_eq_logOmCurve [NeZero H.d] {χ : DirichletCharacter ℂ H.d} (h : IsKroneckerChar χ) {K : Type} [Field K]
    [NumberField K] (h2 : Module.finrank ℚ K = 2) (hD : discr K = -H.d) : logOm K χ = (LogarithmicDifferentialCharacter.logOmCurve H : ℝ) := by
  rw [logOm_of_finrank_eq_two h2 hD, LogarithmicDifferentialCharacter.logOmCurve, Complex.ofReal_sub, dlogL_eq h]

section Curve

variable {R R' : Type} [CommRing R] [CommRing R'] {ω : R} {ω' : R'}

theorem ellMap_iff (C' : Ell H R' ω') (C : Ell H R ω) (f : R →+* R') (φ : C'.P.A.left ⟶ C.P.A.left) :
    EllMap C' C f φ ↔ LogarithmicDifferentialCharacter.IsCurveFibre f C C' φ :=
  ⟨fun ⟨a, b, c, d⟩ => ⟨a.symm, b, d, c⟩, fun ⟨a, b, c, d⟩ => ⟨a.symm, b, d, c⟩⟩

theorem eigenvalue_eq (C : Ell H R ω) (s : R →+* ℂ) :
    s ω = (1 + Complex.I * Real.sqrt H.d) / 2 ∨ s ω = 1 - (1 + Complex.I * Real.sqrt H.d) / 2 := by
  obtain ⟨τ, hτ, -⟩ := LieChar.ell_char E H R ω C
  have h : (2 * wK H - 1) ^ 2 = -(H.d : OK H) := by
    apply Subtype.ext
    show (2 * H.w0 - 1) ^ 2 = -(H.d : 𝓞 E)
    rw [H.two_weight_eq_one_add_root, ← H.rt_sq]; ring
  have h₁ : (2 * s ω - 1) ^ 2 = -(H.d : ℂ) := by simpa [hτ, map_ofNat] using congrArg (fun a => s (τ a)) h
  have h₂ : (Complex.I * Real.sqrt H.d) ^ 2 = -(H.d : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (h₁.trans h₂.symm) with e | e
  · left; linear_combination e / 2
  · right; linear_combination e / 2

theorem isPrincipalAt_iff (C : Ell H R ω) (s : R →+* ℂ) : C.IsPrincipalAt s ↔ LogarithmicDifferentialCharacter.IsPrincipalAt C s := by
  refine forall₄_congr fun Q φ _ u => exists_congr fun c => and_congr_right fun _ => forall_congr' fun z =>
    iff_congr Iff.rfl ?_
  rcases eigenvalue_eq C s with e | e
  · rw [e]
  · rw [e]
    constructor <;> rintro ⟨m, n, rfl⟩ <;> exact ⟨m + n, -n, funext fun _ => by push_cast; ring⟩

end Curve

theorem hasPeriod_iff {M : Type} [Field M] [NumberField M] {ω : 𝓞 M} (C : Ell H (𝓞 M) ω) (x : ℝ) :
    C.HasPeriod x ↔ LogarithmicDifferentialCharacter.HasPeriod C x :=
  exists_congr fun _ => and_congr_right fun _ => eq_comm

section Family

variable {R : Type} [CommRing R] {ω : R} {C : Ell H R ω} {T : PAT H (Sp R)} {D : Datum H} {L : Submodule (𝓞 E) D.La}
  {φ : L → (C.P.A ⟶ T.t.G)}

theorem isFam_iff_isHomFam (h : D.La → D.La → OK H) : IsFam C T h L φ ↔ LogarithmicDifferentialCharacter.IsHomFam C T.t L φ ∧
    ∀ a b : L, LamEq T.t.PP.L (φ a) (φ b) C.P.L (C.act.act (h a b)) (𝟙 C.P.A) :=
  ⟨fun ⟨a, b, c, d⟩ => ⟨⟨fun x => (a x).1, b, c, fun k x => (a x).2 k⟩, d⟩,
    fun ⟨a, d⟩ => ⟨fun x => ⟨a.hom x, fun k => a.lin k x⟩, a.add, a.smul, d⟩⟩

theorem isKForm_unique {ε : ℤˣ} {h h' : D.La → D.La → OK H} (a : IsKForm D ε h) (b : IsKForm D ε h') : h = h' :=
  funext₂ fun x y => Subtype.ext ((a x y).trans (b x y).symm)

theorem isPolFam_iff_exists (ε : ℤˣ) : LogarithmicDifferentialCharacter.IsPolFam C T.t L ε φ ↔ ∃ h, IsKForm D ε h ∧ IsFam C T h L φ :=
  ⟨fun ⟨a, h, b, c⟩ => ⟨h, b, (isFam_iff_isHomFam h).2 ⟨a, c⟩⟩,
    fun ⟨h, b, c⟩ => ⟨((isFam_iff_isHomFam h).1 c).1, h, b, ((isFam_iff_isHomFam h).1 c).2⟩⟩

theorem isFam_iff {ε : ℤˣ} {h : D.La → D.La → OK H} (hh : IsKForm D ε h) :
    IsFam C T h L φ ↔ LogarithmicDifferentialCharacter.IsPolFam C T.t L ε φ := by
  rw [isPolFam_iff_exists]
  exact ⟨fun a => ⟨h, hh, a⟩, fun ⟨h', b, c⟩ => isKForm_unique b hh ▸ c⟩

end Family

theorem ontoAt_iff {S : Scheme.{0}} {I : Type} [Fintype I] {B : I → Over S} [∀ i, GrpObj (B i)] {A : Over S} [GrpObj A]
    [IsCommMonObj A] (φ : ∀ i, B i ⟶ A) (hφ : ∀ i, IsMonHom (φ i)) {k : Type} [Field k] (t : Sp k ⟶ S) :
    OntoAt φ t ↔ ∀ y : Over.mk t ⟶ A, ∃ x : ∀ i, Over.mk t ⟶ B i, y = ∏ i, x i ≫ φ i := by
  classical
  refine forall_congr' fun y => ⟨?_, ?_⟩
  · rintro ⟨n, i, x, rfl⟩
    rw [List.prod_ofFn]
    refine Finset.prod_induction _ (fun y : Over.mk t ⟶ A => ∃ x : ∀ i, Over.mk t ⟶ B i, y = ∏ i, x i ≫ φ i) ?_ ?_ ?_
    · rintro _ _ ⟨x, rfl⟩ ⟨x', rfl⟩
      exact ⟨fun i => x i * x' i, by simp only [MonObj.mul_comp, Finset.prod_mul_distrib]⟩
    · exact ⟨fun _ => 1, by simp only [MonObj.one_comp, Finset.prod_const_one]⟩
    · intro m _
      refine ⟨Function.update (fun _ => 1) (i m) (x m), ?_⟩
      rw [Finset.prod_eq_single (i m) (fun j _ hj => by rw [Function.update_of_ne hj, MonObj.one_comp]) (by simp),
        Function.update_self]
  · rintro ⟨x, rfl⟩
    refine ⟨_, (Fintype.equivFin I).symm, fun m => x _, ?_⟩
    rw [List.prod_ofFn]
    exact ((Fintype.equivFin I).symm.prod_comp fun i => x i ≫ φ i).symm

theorem isExp_iff {R : Type} [CommRing R] (T : PAT H (Sp R)) (σ : R →+* ℂ) (D : Datum H) {g : ℕ}
    (ty : Fin g → (E →+* ℂ)) (Pe : D.La →+ (Fin g → ℂ)) (e : (Fin g → ℂ) → (Over.mk (spMap σ) ⟶ T.t.G)) :
    IsExp T σ D ty Pe e ↔ LogarithmicDifferentialCharacter.IsExp T.t (spMap σ) D ty Pe e :=
  ⟨fun ⟨a, b, c, d, f, g, h⟩ => ⟨a, c, d, f, g, b, h⟩, fun h => ⟨h.period, h.hol, h.add, h.onto, h.ker, h.lin, h.weil⟩⟩

section Lattice

theorem span_iff {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M] {I : Type}
    [Fintype I] {N : I → Type} [∀ i, AddCommGroup (N i)] [∀ i, Module O (N i)] (f : ∀ i, N i →ₗ[O] M) :
    (∃ n : ℕ, 0 < n ∧ ∀ a : M, ∃ x : ∀ i, N i, n • a = ∑ i, f i (x i)) ↔
      ∀ a : M, ∃ n : ℕ, 0 < n ∧ n • a ∈ ⨆ i, LinearMap.range (f i) := by
  classical
  have key : ∀ a : M, a ∈ ⨆ i, LinearMap.range (f i) ↔ ∃ x : ∀ i, N i, a = ∑ i, f i (x i) := fun a => by
    refine ⟨fun h => ?_, ?_⟩
    · refine Submodule.iSup_induction _ (motive := fun a => ∃ x : ∀ i, N i, a = ∑ i, f i (x i)) h ?_ ⟨0, by simp⟩ ?_
      · rintro i _ ⟨b, rfl⟩
        refine ⟨Pi.single i b, ?_⟩
        rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, map_zero]) (by simp),
          Pi.single_eq_same]
      · rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        exact ⟨x + y, by simp [Finset.sum_add_distrib]⟩
    · rintro ⟨x, rfl⟩
      exact Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ⟨_, rfl⟩
  simp only [← key]
  refine ⟨fun ⟨n, hn, h⟩ a => ⟨n, hn, h a⟩, fun h => ?_⟩
  choose n hn h using h
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := O) (M := M)
  refine ⟨∏ a ∈ s, n a, Finset.prod_pos fun a _ => hn a, fun a => ?_⟩
  have : Submodule.span O (s : Set M) ≤
      (⨆ i, LinearMap.range (f i)).comap ((∏ a ∈ s, n a) • (LinearMap.id : M →ₗ[O] M)) :=
    Submodule.span_le.2 fun b hb => by
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n (show b ∈ s from hb)
      show (∏ a ∈ s, n a) • b ∈ ⨆ i, LinearMap.range (f i)
      rw [hc, mul_comm, mul_smul]
      exact nsmul_mem (h b) c
  exact this (hs ▸ Submodule.mem_top)

variable {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe)

def latEquiv (Λ : ℝ) : LogarithmicDifferentialCharacter.LatData hP Λ ≃
    {Z : CMLat hP D.p D.q // 1 ≤ Λ ∧ ∀ j (τ : E →+* ℂ), ‖τ (Z.hh j : E)‖ ≤ Λ ^ 2} where
  toFun X := ⟨⟨X.A, X.sigP, X.sigM, X.ψ, X.pure, X.hh, X.form, (haveI := D.fin; span_iff X.ψ).2 X.span⟩,
    X.one_le, X.bound⟩
  invFun Z := ⟨Z.1.D₁, Z.1.sigP, Z.1.sigM, Z.1.f, Z.1.hh, Z.1.pure, Z.1.form,
    (haveI := D.fin; span_iff Z.1.f).1 Z.1.span, Z.2.1, Z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem latEquiv_D₁ {Λ : ℝ} (X : LogarithmicDifferentialCharacter.LatData hP Λ) : (latEquiv hP Λ X).1.D₁ = X.A := rfl

end Lattice

variable {K : Type} [Field K] [NumberField K]

theorem isThetaDeg_iff (x : KeyIn K) (δ : ℝ) : IsThetaDeg x δ ↔ LogarithmicDifferentialCharacter.IsDegDe x δ := by
  refine exists₂_congr fun oa nth => ⟨fun ⟨a, b, c, d⟩ => ⟨a, c, fun σ => ⟨?_, b σ⟩, d⟩,
    fun ⟨a, c, b, d⟩ => ⟨a, fun σ => (b σ).2, c, d⟩⟩
  obtain ⟨x', nη, -, h⟩ := b σ
  exact (LamF.KeyArch.pos_of_isArchNorm thetaUnifAV_all x' h).1

theorem exists_key_iff (P : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) :
    (∃ (F : GenFib P) (hg : _) (rig : _) (hr : _) (th : _) (hth : _), F.key hg rig hr th hth = x) ↔
      ∃ φ : x.P.A.left ⟶ P.A.left, IsPolFibre (algebraMap (𝓞 K) K) P x.P φ := by
  constructor
  · rintro ⟨F, hg, rig, hr, th, hth, rfl⟩
    exact ⟨F.φ, F.fib⟩
  · rintro ⟨φ, h⟩
    exact ⟨⟨x.P, φ, h, x.v, x.basis⟩, x.g_pos, x.rig, x.rig_gen, x.th, x.th_ne, rfl⟩

theorem isDegDeOf_iff (P : Out.PolAV (Sp (𝓞 K))) (δ : ℝ) :
    (∃ (F : GenFib P) (hg : _) (rig : _) (hr : _) (th : _) (hth : _), IsThetaDeg (F.key hg rig hr th hth) δ) ↔
      LogarithmicDifferentialCharacter.IsDegDeOf P δ := by
  constructor
  · rintro ⟨F, hg, rig, hr, th, hth, h⟩
    exact ⟨_, F.φ, F.fib, (isThetaDeg_iff _ _).1 h⟩
  · rintro ⟨x, φ, h, hδ⟩
    obtain ⟨F, hg, rig, hr, th, hth, rfl⟩ := (exists_key_iff P x).2 ⟨φ, h⟩
    exact ⟨F, hg, rig, hr, th, hth, (isThetaDeg_iff _ _).2 hδ⟩

end GlobalTheory.CM.Compare
end
