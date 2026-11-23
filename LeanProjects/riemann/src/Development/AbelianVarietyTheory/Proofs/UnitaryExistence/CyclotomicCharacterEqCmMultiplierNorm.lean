import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearLiftOfIsMonHomPolAV
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolPull
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.AlphaPair

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.MultiplierNorm

def InOrder (d : ℕ) (z : ℂ) : Prop := ∃ m n : ℤ, z = (m : ℂ) + n * ((1 + Complex.I * Real.sqrt d) / 2)

theorem exists_form_eq_one {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (hg : 1 ≤ g)
    (u : HolUnif A L g) (Ef : LinearMap.BilinForm ℤ u.Λ) (hE : Function.Bijective Ef) :
    ∃ a b : u.Λ, Ef a b = 1 := by
  haveI := u.discrete
  haveI : IsZLattice ℝ u.Λ := ⟨u.full⟩
  haveI : Module.Free ℤ u.Λ := ZLattice.module_free ℝ u.Λ
  have hnt : Nontrivial u.Λ := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have hb : u.Λ = ⊥ := Submodule.eq_bot_of_subsingleton
    have := u.full
    rw [hb] at this
    simp only [Submodule.bot_coe, Submodule.span_zero_singleton] at this
    haveI hne : Nonempty (Fin g) := ⟨⟨0, hg⟩⟩
    exact bot_ne_top this
  let B := Module.Free.chooseBasis ℤ u.Λ
  obtain ⟨i⟩ := B.index_nonempty
  obtain ⟨a, ha⟩ := hE.2 (B.coord i)
  exact ⟨a, B i, by rw [ha]; simp⟩

theorem ex_pow {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (n : ℕ) (z : Fin g → ℂ) :
    u.ex z ^ n = u.ex ((n : ℂ) • z) := by
  have h0 : u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem
  induction n with
  | zero => simp [h0]
  | succ n ih => rw [pow_succ, ih, ← u.ex_add]; congr 1; push_cast; rw [add_smul, one_smul]

theorem hermForm_smul {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a b : ℂ) (v : Fin g → ℂ) :
    hermForm Hm (a • v) (b • v) = a * starRingEnd ℂ b * hermForm Hm v v := by
  rw [hermForm, hermForm, smul_dotProduct, star_smul, Matrix.mulVec_smul, dotProduct_smul, RCLike.star_def,
    smul_eq_mul, smul_eq_mul, _root_.mul_assoc]

theorem hermForm_self_im {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) (v : Fin g → ℂ) :
    (hermForm Hm v v).im = 0 := by
  rw [← Complex.conj_eq_iff_im, hermForm, ← RCLike.star_def, ← Matrix.star_dotProduct_star,
    Matrix.star_mulVec, star_star, h.eq, ← Matrix.dotProduct_mulVec]

theorem weilIs_of_quadLattice (P Q : Out.PolAV (Sp ℂ)) (hP : P.g = 1) (hQ : Q.g = 1) (u : HolUnif P.A P.L P.g)
    {d : ℕ} (hd : 0 < d) {c : ℂ} (hc : c ≠ 0) (hΛ : IsQuadLattice u.Λ d c) (f : P.A ⟶ Q.A) (hf : IsMonHom f)
    (hinj : ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, x ≫ f = 1 → x = 1) {α β : ℂ} (hα : InOrder d α) (hβ : InOrder d β)
    {e : ℤ} (he : (e : ℝ) * (√d / 2) = (α * starRingEnd ℂ β).im) {n : ℕ} (hn : 0 < n) (ζ : ℂˣ)
    (hζ : (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (e : ℂ) / n)) :
    Out.WeilIs Q.A Q.L n (u.ex (fun _ => c * (α / n)) ≫ f) (u.ex (fun _ => c * (β / n)) ≫ f) (unitOn ζ) := by
  obtain ⟨rig, hr⟩ := Q.rigid
  obtain ⟨u₁, Hm, χ, Ef, hAH, -, -, -, -, -, hIm, hE, hw⟩ := thetaUnifAV_all Q rig hr
  obtain ⟨F, hF⟩ := exists_linear_lift_of_isMonHom_polAV P Q _ _ u u₁ f hf
  have hd' : (0 : ℝ) < √d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  let i₀ : Fin P.g := ⟨0, by omega⟩
  let v : Fin Q.g → ℂ := F fun _ => c
  have hv : ∀ z : ℂ, z • v = F fun _ => c * z := fun z => by
    rw [← map_smul]; congr 1; funext _; simp [_root_.mul_comm]
  have mem : ∀ z : ℂ, z • v ∈ u₁.Λ ↔ InOrder d z := fun z => by
    rw [← u₁.ker, hv, hF]
    constructor
    · intro h
      obtain ⟨m, k, h'⟩ := (hΛ _).1 ((u.ker _).1 (hinj _ h))
      exact ⟨m, k, mul_left_cancel₀ hc (congrFun h' i₀)⟩
    · rintro ⟨m, k, rfl⟩
      rw [(u.ker _).2 ((hΛ _).2 ⟨m, k, rfl⟩), MonObj.one_comp]
  have v0 : v ≠ 0 := fun h => by
    obtain ⟨m, k, h'⟩ := (mem (1 / 2)).1 (by rw [h, smul_zero]; exact u₁.Λ.zero_mem)
    have h1 := congrArg Complex.im h'
    have h2 := congrArg Complex.re h'
    simp at h1 h2
    have hk : k = 0 := by
      rcases h1 with h1 | h1
      · exact h1
      · exact absurd h1 hd.ne'
    subst hk
    have h3 : ((2 * m : ℤ) : ℝ) = (1 : ℤ) := by push_cast at h2 ⊢; linarith
    have := Int.cast_injective h3
    omega
  have span : ∀ l : Fin Q.g → ℂ, ∃ z : ℂ, l = z • v := fun l => by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 v0
    refine ⟨l j / v j, funext fun i => ?_⟩
    have : i = j := Fin.ext (by omega)
    subst this
    simp only [Pi.zero_apply] at hj
    simp [hj]
  have hpos : 0 < (hermForm Hm v v).re := hAH.2.1 v v0
  have val : ∀ (a b : ℂ) (ha : a • v ∈ u₁.Λ) (hb : b • v ∈ u₁.Λ),
      (Ef ⟨_, ha⟩ ⟨_, hb⟩ : ℝ) = (a * starRingEnd ℂ b).im * (hermForm Hm v v).re := fun a b ha hb => by
    rw [hIm, hermForm_smul, Complex.mul_im, hermForm_self_im hAH.1, mul_zero, zero_add]
  have one : √d / 2 * (hermForm Hm v v).re = 1 := by
    have ha₀ := (mem _).2 ⟨0, 1, rfl⟩
    have hb₀ := (mem _).2 ⟨1, 0, rfl⟩
    have h₀ : (Ef ⟨_, ha₀⟩ ⟨_, hb₀⟩ : ℝ) = √d / 2 * (hermForm Hm v v).re := by
      rw [val]; simp
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := exists_form_eq_one hQ.ge u₁ Ef hE
    obtain ⟨a, rfl⟩ := span a
    obtain ⟨b, rfl⟩ := span b
    obtain ⟨m, k, rfl⟩ := (mem a).1 ha
    obtain ⟨m', k', rfl⟩ := (mem b).1 hb
    have hdvd : Ef ⟨_, ha₀⟩ ⟨_, hb₀⟩ ∣ 1 := by
      refine ⟨k * m' - m * k', Int.cast_injective (α := ℝ) ?_⟩
      rw [Int.cast_mul, h₀, ← hab, val]
      simp [map_ofNat]
      ring
    have hp : 0 < Ef ⟨_, ha₀⟩ ⟨_, hb₀⟩ := by
      have : (0 : ℝ) < Ef ⟨_, ha₀⟩ ⟨_, hb₀⟩ := by rw [h₀]; positivity
      exact_mod_cast this
    rw [← h₀, Int.eq_one_of_dvd_one hp.le hdvd, Int.cast_one]
  have hEe : Ef ⟨_, (mem _).2 hα⟩ ⟨_, (mem _).2 hβ⟩ = e := Int.cast_injective (α := ℝ) (by
    rw [val, ← he, _root_.mul_assoc, one, _root_.mul_one])
  have H := hw n ⟨_, (mem _).2 hα⟩ ⟨_, (mem _).2 hβ⟩ ζ hn (by rw [hEe, hζ])
  have sc : ∀ a : ℂ, u₁.ex ((n : ℂ)⁻¹ • a • v) = u.ex (fun _ => c * (a / n)) ≫ f := fun a => by
    rw [smul_smul, hv, hF, ← div_eq_inv_mul]
  rw [← sc, ← sc]
  exact H

def pullPol {R R' : Type} [CommRing R] [CommRing R'] (P : Out.PolAV (Sp R)) {s : R →+* R'} {A : Over (Sp R')}
    [GrpObj A] {φ : A.left ⟶ P.A.left} (h : IsGrpPullback A P.A (spMap s) φ) : Out.PolAV (Sp R') :=
  have hL := pull_isLB P.isLB φ
  have H := pol_pull _ _ P.A A _ φ P.L _ P.isLB hL P.isAb h (PolBaseChange.lbIso_refl hL)
  { A := A, isAb := H.1, g := P.g
    smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
    L := P.L.pull φ, isLB := hL, rigid := PolBaseChange.rigidified_pull h P.rigid
    sym := PolBaseChange.sym_pull h P.sym, ample := H.2.1 P.ample, ktriv := H.2.2 P.ktriv }

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cmHost_rootComplex_eq_pm_sqrt (H : Host E) : H.rt0 = Complex.I * Real.sqrt H.d ∨ H.rt0 = -(Complex.I * Real.sqrt H.d) := by
  apply sq_eq_sq_iff_eq_or_eq_neg.1
  rw [H.sqrt_neg_disc_sq, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  simp

theorem inOrder_wC (H : Host E) (a : ℤ × ℤ) : InOrder H.d (wC H a) := by
  rcases cmHost_rootComplex_eq_pm_sqrt H with h | h
  · exact ⟨a.1, a.2, by rw [wC, h]⟩
  · exact ⟨a.1 + a.2, -a.2, by rw [wC, h]; push_cast; ring⟩

theorem four_mul_div (H : Host E) : (4 : ℂ) * ((((H.d : ℤ) + 1) / 4 : ℤ) : ℂ) = H.d + 1 := by
  have := H.d_mod
  have h : (4 : ℤ) * (((H.d : ℤ) + 1) / 4) = H.d + 1 := by omega
  exact_mod_cast congrArg (Int.cast : ℤ → ℂ) h

theorem wC_mul (H : Host E) (s a : ℤ × ℤ) : ∃ b, wC H s * wC H a = wC H b := by
  refine ⟨(s.1 * a.1 - s.2 * a.2 * (((H.d : ℤ) + 1) / 4), s.1 * a.2 + s.2 * a.1 + s.2 * a.2), ?_⟩
  have h := four_mul_div H
  have h' := H.sqrt_neg_disc_sq
  simp only [wC, Int.cast_sub, Int.cast_mul, Int.cast_add]
  linear_combination (s.2 * a.2 / 4 : ℂ) * h + (s.2 * a.2 / 4 : ℂ) * h'

theorem wC_norm (H : Host E) (s : ℤ × ℤ) : wC H s * starRingEnd ℂ (wC H s) =
    ((s.1 ^ 2 + s.1 * s.2 + s.2 ^ 2 * (((H.d : ℤ) + 1) / 4) : ℤ) : ℂ) := by
  have hc : starRingEnd ℂ H.rt0 = -H.rt0 := by
    rcases cmHost_rootComplex_eq_pm_sqrt H with h | h <;> rw [h] <;> simp
  have h := four_mul_div H
  have h' := H.sqrt_neg_disc_sq
  simp only [wC, Int.cast_pow, Int.cast_mul, Int.cast_add, map_add, map_mul, map_div₀, map_intCast, map_one,
    map_ofNat, hc]
  linear_combination (-s.2 ^ 2 / 4 : ℂ) * h - (s.2 ^ 2 / 4 : ℂ) * h'

theorem exists_pair (H : Host E) :
    ∃ a b, ((-1 : ℤ) : ℝ) * (√H.d / 2) = (wC H a * starRingEnd ℂ (wC H b)).im := by
  rcases cmHost_rootComplex_eq_pm_sqrt H with h | h
  · exact ⟨(1, 0), (0, 1), by simp [wC, h, map_ofNat]; ring⟩
  · exact ⟨(0, 1), (1, 0), by simp [wC, h]; ring⟩

theorem map_zeta_eq_zpow_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (C : Curve H), ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ (io : C.P.A.left ⟶ C.P.A.left) (n : ℕ) (s : ℤ × ℤ), 0 < n → C.ActsBy τ io n s → τ (zeta n) = zeta n ^ (s.1 ^ 2 + s.1 * s.2 + s.2 ^ 2 * (((H.d : ℤ) + 1) / 4)) := by
  intro E _ _ _ H C τ _ io n s hn ⟨hp, hact⟩
  have hL := firstFiveLaws.1
  have hd := H.d_prime.pos
  obtain ⟨a, b, hab⟩ := exists_pair H
  set N : ℤ := s.1 ^ 2 + s.1 * s.2 + s.2 ^ 2 * (((H.d : ℤ) + 1) / 4) with hN
  let Q := pullPol C.P hp
  let ζ : ℂˣ := Units.mk0 (zeta n) (Complex.exp_ne_zero _)
  have hs : ∀ a, InOrder H.d (wC H s * wC H a) := fun a => by
    obtain ⟨b, hb⟩ := wC_mul H s a
    rw [hb]; exact inOrder_wC H b
  have W₀ := weilIs_of_quadLattice C.P C.P C.g_eq C.g_eq C.u hd C.c_ne C.lat (𝟙 _) inferInstance
    (fun x hx => by rwa [Category.comp_id] at hx) (inOrder_wC H a) (inOrder_wC H b) hab hn ζ
    (by simp [ζ, zeta])
  have W₁ := weilIs_of_quadLattice C.P Q C.g_eq C.g_eq C.u hd C.c_ne C.lat (𝟙 C.P.A)
    (inferInstanceAs (IsMonHom (𝟙 C.P.A)))
    (fun x hx => (Category.comp_id x).symm.trans hx) (hs a) (hs b) (e := -N) (by
      have e : wC H s * wC H a * starRingEnd ℂ (wC H s * wC H b) = (N : ℝ) * (wC H a * starRingEnd ℂ (wC H b)) := by
        rw [Complex.ofReal_intCast, hN, ← wC_norm, map_mul]; ring
      rw [e, Complex.im_ofReal_mul, ← hab]
      push_cast; ring) hn (ζ ^ N) (by
      rw [Units.val_zpow_eq_zpow_val]
      show zeta n ^ N = _
      rw [zeta, ← Complex.exp_int_mul]
      congr 1
      push_cast; ring)
  rw [Category.comp_id, Category.comp_id] at W₀
  have tor : ∀ z, InOrder H.d z → (C.u.ex fun _ => C.c * (z / n)) ^ n = 1 := by
    rintro z ⟨m, k, hz⟩
    rw [ex_pow, C.u.ker]
    refine (C.lat _).2 ⟨m, k, funext fun _ => ?_⟩
    have : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    rw [← hz, Pi.smul_apply, smul_eq_mul]
    field_simp
  obtain ⟨r, hr, ⟨cub⟩⟩ := PolAV_exists_cubical hL.cube Q
  obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl Q.isLB
  have := Q.isAb.comm
  have W₂ := WeilCube.weilIs_pull cub hL.globalFns Q.isAb C.P.isLB hp w hw (T := 𝟙_ _) (T₀ := 𝟙_ _)
    (spMap (τ : ℂ →+* ℂ)) (by simp) (tor _ (hs a)) (tor _ (hs b)) (hact a).symm (hact b).symm W₀
  obtain ⟨c₀, -, hc₀⟩ := (hL.weil _ Q n _).1 _ _ (tor _ (hs a)) (tor _ (hs b))
  have W₁' : Out.WeilIs Q.A Q.L n (C.u.ex fun _ => C.c * (wC H s * wC H a / n))
      (C.u.ex fun _ => C.c * (wC H s * wC H b / n)) (unitOn (ζ ^ N)) := by
    have e₁ : ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ C.P.A, x ≫ 𝟙 C.P.A = x := fun x => Category.comp_id x
    erw [e₁, e₁] at W₁
    exact W₁
  have e := (hc₀ _ W₂).trans (hc₀ _ W₁').symm
  have e' : unitOn (Units.map (τ : ℂ →+* ℂ).toMonoidHom ζ) = unitOn (ζ ^ N) := by
    refine Eq.trans (Units.ext ?_) e
    exact congrArg (fun q => q.hom (ζ : ℂ)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (τ : ℂ →+* ℂ)))
  have e'' := congrArg Units.val (H1.unitOn_injective e')
  rw [Units.val_zpow_eq_zpow_val] at e''
  exact e''

end GlobalTheory.MultiplierNorm
