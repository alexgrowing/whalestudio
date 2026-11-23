import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastNeZeroG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatMatTransposeMulGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthLetters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyResultOfHodgeTateKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralityResult
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateKernelAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteNormEqDrViaPower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorsUniversalBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameCoordinatesComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniqueIntegralLiftNormPInverse
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat
open scoped Classical
open GlobalTheory.EqHalf

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EqHalf.IsoLevel

section Lin

open scoped TensorProduct Matrix

variable {p : ℕ} [Fact p.Prime] {T : Type} [AddCommGroup T] [Module ℤ_[p] T] {N : ℕ}

theorem isUnit_det {G : Matrix (Fin N) (Fin N) ℤ_[p]} {u : ℤ_[p]ˣ} {B J : Matrix (Fin N) (Fin N) ℤ}
    (hBJ : B.transpose * J = 1) (h : ∀ m m', (p : ℤ_[p]) ∣ G m m' - u * (B m m' : ℤ_[p])) : IsUnit G.det := by
  set φ : ℤ_[p] →+* ZMod p := PadicInt.toZMod with hφ
  have hφp : φ (p : ℤ_[p]) = 0 := by rw [map_natCast]; exact ZMod.natCast_self p
  have hGφ : G.map φ = φ u • B.map (Int.castRingHom (ZMod p)) := by
    ext m m'
    obtain ⟨c, hc⟩ := h m m'
    have h1 : G m m' = u * (B m m' : ℤ_[p]) + p * c := by rw [← hc]; ring
    simp [h1, hφp]
  have hdetB : IsUnit B.det := by
    have h := congrArg Matrix.det hBJ
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
    exact ⟨⟨_, _, h, by rw [mul_comm]; exact h⟩, rfl⟩
  by_contra hn
  have hmem : G.det ∈ IsLocalRing.maximalIdeal ℤ_[p] := (IsLocalRing.mem_maximalIdeal _).2 hn
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker] at hmem
  have h2 : φ G.det = (φ u) ^ N * ((B.det : ℤ) : ZMod p) := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hGφ, Matrix.det_smul, Fintype.card_fin,
      ← RingHom.mapMatrix_apply, ← RingHom.map_det, eq_intCast]
  have h3 : IsUnit ((φ u) ^ N * ((B.det : ℤ) : ZMod p)) :=
    ((u.isUnit.map φ).pow N).mul (hdetB.map (Int.castRingHom (ZMod p)))
  rw [← h2, hmem] at h3
  exact not_isUnit_zero h3

theorem exists_basis [Module.Free ℤ_[p] T] [Module.Finite ℤ_[p] T] (hN : Module.finrank ℤ_[p] T = N)
    (e : LinearMap.BilinForm ℤ_[p] T) (s : Fin N → T) (h : IsUnit (Matrix.of fun m m' => e (s m) (s m')).det) :
    ∃ b : Module.Basis (Fin N) ℤ_[p] T, ∀ m, b m = s m := by
  let c := Module.finBasisOfFinrankEq ℤ_[p] T hN
  have hG : (Matrix.of fun m m' => e (s m) (s m')) = (Matrix.of fun m k => e (s m) (c k)) * c.toMatrix s := by
    ext m m'
    rw [Matrix.mul_apply, Matrix.of_apply]
    conv_lhs => rw [← c.sum_repr (s m')]
    simp only [map_sum, map_smul, smul_eq_mul, Matrix.of_apply, Module.Basis.toMatrix_apply, mul_comm]
  rw [hG, Matrix.det_mul] at h
  obtain ⟨h1, h2⟩ := c.is_basis_iff_det.2 (isUnit_of_mul_isUnit_right h)
  exact ⟨Module.Basis.mk h1 h2.ge, fun m => Module.Basis.mk_apply _ _ m⟩

variable [Algebra ℤ_[p] ℂ_[p]]

theorem norm_pair_le (hf : ∀ x : ℤ_[p], ‖algebraMap ℤ_[p] ℂ_[p] x‖ ≤ 1) (e : LinearMap.BilinForm ℤ_[p] T)
    (s : Module.Basis (Fin N) ℤ_[p] T) (b : ℂ_[p] ⊗[ℤ_[p]] T) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ m, ‖e.baseChange ℂ_[p] b (1 ⊗ₜ s m)‖ ≤ r) (y : T) : ‖e.baseChange ℂ_[p] b (1 ⊗ₜ y)‖ ≤ r := by
  rw [← s.sum_repr y, TensorProduct.tmul_sum, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hr fun m _ => ?_
  rw [TensorProduct.tmul_smul, ← algebraMap_smul ℂ_[p], map_smul, smul_eq_mul, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hf _)).trans (h m)

theorem dot_inv_eq_zero (e : LinearMap.BilinForm ℤ_[p] T) (s : Module.Basis (Fin N) ℤ_[p] T)
    {H : Matrix (Fin N) (Fin N) ℤ_[p]} (hH : (Matrix.of fun m m' => e (s m) (s m')) * H = 1)
    {b b' : ℂ_[p] ⊗[ℤ_[p]] T} (hbb : e.baseChange ℂ_[p] b b' = 0) :
    (fun m => e.baseChange ℂ_[p] b (1 ⊗ₜ s m)) ⬝ᵥ
      (H.transpose.map (algebraMap ℤ_[p] ℂ_[p]) *ᵥ fun m => e.baseChange ℂ_[p] b' (1 ⊗ₜ s m)) = 0 := by
  set f := algebraMap ℤ_[p] ℂ_[p]
  set G := Matrix.of fun m m' => e (s m) (s m') with hG
  have hv : ∀ k l, e.baseChange ℂ_[p] (1 ⊗ₜ s k) (1 ⊗ₜ s l) = G.map f k l := fun k l => by
    rw [LinearMap.BilinForm.baseChange_tmul, mul_one, Algebra.smul_def, mul_one]
    rfl
  let x' := (s.baseChange ℂ_[p]).repr b'
  have hb' : b' = ∑ k, x' k • ((1 : ℂ_[p]) ⊗ₜ s k) := by
    conv_lhs => rw [← (s.baseChange ℂ_[p]).sum_repr b']
    simp only [Module.Basis.baseChange_apply, x']
  have h1 : (fun m => e.baseChange ℂ_[p] b' (1 ⊗ₜ s m)) = (G.transpose.map f) *ᵥ x' := by
    funext m
    conv_lhs => rw [hb']
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hv, Matrix.mulVec,
      dotProduct, Matrix.map_apply, Matrix.transpose_apply, mul_comm]
  rw [h1, Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Matrix.transpose_mul, hH, Matrix.transpose_one,
    Matrix.map_one _ (map_zero f) (map_one f), Matrix.one_mulVec, ← hbb]
  conv_rhs => rw [hb']
  simp only [map_sum, map_smul, smul_eq_mul, dotProduct, mul_comm]

omit [Algebra ℤ_[p] ℂ_[p]] in

theorem norm_dot_le {A : Matrix (Fin N) (Fin N) ℂ_[p]} {x y : Fin N → ℂ_[p]} {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hx : ∀ m, ‖x m‖ ≤ a) (hA : ∀ m m', ‖A m m'‖ ≤ b) (hy : ∀ m, ‖y m‖ ≤ c) :
    ‖x ⬝ᵥ (A *ᵥ y)‖ ≤ a * (b * c) := by
  simp only [dotProduct, Matrix.mulVec]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun m _ => ?_
  rw [norm_mul]
  refine mul_le_mul (hx m) ?_ (norm_nonneg _) ha
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun m' _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hA m m') (hy m') (norm_nonneg _) hb

theorem norm_dot_dual_le (hf : ∀ x : ℤ_[p], ‖algebraMap ℤ_[p] ℂ_[p] x‖ ≤ 1) (e : LinearMap.BilinForm ℤ_[p] T)
    (s : Module.Basis (Fin N) ℤ_[p] T) (hG : IsUnit (Matrix.of fun m m' => e (s m) (s m')).det) {u : ℤ_[p]ˣ}
    {B J : Matrix (Fin N) (Fin N) ℤ} (hBJ : B.transpose * J = 1) {n : ℕ}
    (h : ∀ m m', (p : ℤ_[p]) ^ n ∣ e (s m) (s m') - u * (B m m' : ℤ_[p]))
    {b b' : ℂ_[p] ⊗[ℤ_[p]] T} (hbb : e.baseChange ℂ_[p] b b' = 0) {β β' : Fin N → ℂ_[p]} (hβ : ∀ m, ‖β m‖ ≤ 1)
    (hβ' : ∀ m, ‖β' m‖ ≤ 1) {r : ℝ} (hr1 : r ≤ 1) (hr : ‖(p : ℂ_[p])‖ ^ n ≤ r)
    (hγ : ∀ m, ‖β m - e.baseChange ℂ_[p] b (1 ⊗ₜ s m)‖ ≤ r) (hγ' : ∀ m, ‖β' m - e.baseChange ℂ_[p] b' (1 ⊗ₜ s m)‖ ≤ r) :
    ‖β ⬝ᵥ (J.map (Int.castRingHom ℂ_[p]) *ᵥ β')‖ ≤ r := by
  have hr0 : 0 ≤ r := (pow_nonneg (norm_nonneg _) n).trans hr
  have h0 := dot_inv_eq_zero e s (Matrix.mul_nonsing_inv _ hG) hbb
  have hGH := Matrix.mul_nonsing_inv _ hG
  set f := algebraMap ℤ_[p] ℂ_[p]
  set G := Matrix.of fun m m' => e (s m) (s m')
  set γ := fun m => e.baseChange ℂ_[p] b (1 ⊗ₜ s m)
  set γ' := fun m => e.baseChange ℂ_[p] b' (1 ⊗ₜ s m)
  choose D hD using h
  have hGD : G = (u : ℤ_[p]) • B.map (Int.castRingHom ℤ_[p]) + (p : ℤ_[p]) ^ n • Matrix.of D := by
    ext m m'
    simp only [G, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, eq_intCast, ← hD]
    ring
  have hBJ' : (B.map (Int.castRingHom ℤ_[p])).transpose * J.map (Int.castRingHom ℤ_[p]) = 1 := by
    rw [← Matrix.transpose_map, ← Matrix.map_mul, hBJ, Matrix.map_one _ (map_zero _) (map_one _)]
  have hJ : J.map (Int.castRingHom ℤ_[p]) = (u : ℤ_[p]) • G⁻¹.transpose +
      (p : ℤ_[p]) ^ n • (G⁻¹.transpose * (Matrix.of D).transpose * J.map (Int.castRingHom ℤ_[p])) := by
    have h1 : G⁻¹.transpose * G.transpose = 1 := by rw [← Matrix.transpose_mul, hGH, Matrix.transpose_one]
    generalize G⁻¹.transpose = K at h1 ⊢
    conv_lhs => rw [← Matrix.one_mul (J.map _), ← h1, hGD]
    simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_assoc, hBJ', Matrix.mul_one]
  generalize G⁻¹.transpose * (Matrix.of D).transpose * J.map (Int.castRingHom ℤ_[p]) = K at hJ
  have hJc : J.map (Int.castRingHom ℂ_[p]) = f u • G⁻¹.transpose.map f + ((p : ℤ_[p]) ^ n • K).map f := by
    ext m m'
    have := congrArg f (congrFun (congrFun hJ m) m')
    simpa using this
  have hJn : ∀ m m', ‖J.map (Int.castRingHom ℂ_[p]) m m'‖ ≤ 1 := fun m m' => IsUltrametricDist.norm_intCast_le_one _ _
  have hγn : ∀ m, ‖γ m‖ ≤ 1 := fun m => by
    have : γ m = β m + -(β m - γ m) := by ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hβ m) ((norm_neg _).trans_le ((hγ m).trans hr1)))
  have hγn' : ∀ m, ‖γ' m‖ ≤ 1 := fun m => by
    have : γ' m = β' m + -(β' m - γ' m) := by ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hβ' m) ((norm_neg _).trans_le ((hγ' m).trans hr1)))
  have e1 : β ⬝ᵥ (J.map (Int.castRingHom ℂ_[p]) *ᵥ β') = (β - γ) ⬝ᵥ (J.map (Int.castRingHom ℂ_[p]) *ᵥ β') +
      (γ ⬝ᵥ (J.map (Int.castRingHom ℂ_[p]) *ᵥ (β' - γ')) + γ ⬝ᵥ (((p : ℤ_[p]) ^ n • K).map f *ᵥ γ')) := by
    have e2 : γ ⬝ᵥ (J.map (Int.castRingHom ℂ_[p]) *ᵥ γ') = γ ⬝ᵥ (((p : ℤ_[p]) ^ n • K).map f *ᵥ γ') := by
      rw [hJc, Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul, h0, smul_zero, zero_add]
    rw [← e2, sub_dotProduct, Matrix.mulVec_sub, dotProduct_sub]
    ring
  rw [e1]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_
    ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)))
  · exact (norm_dot_le (x := β - γ) hr0 zero_le_one zero_le_one hγ hJn hβ').trans_eq (by ring)
  · exact (norm_dot_le (y := β' - γ') zero_le_one zero_le_one hr0 hγn hJn hγ').trans_eq (by ring)
  · have hK : ∀ m m', ‖((p : ℤ_[p]) ^ n • K).map f m m'‖ ≤ r := fun m m' => by
      rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast, norm_mul, norm_pow]
      exact (mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) (hf _)).trans hr
    simpa using norm_dot_le zero_le_one hr0 zero_le_one hγn hK hγn'

end Lin

section Point

open Limits MonObj Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.ChTor GlobalTheory.LineNorm GlobalTheory.HalfGeo GlobalTheory.LocM.TanPair GlobalTheory.LieMet ReciprocityTheory.ChartRestriction.G.PullbackSections
open Formalism.MainNotions.DIV.Cons (intO)
open ReciprocityTheory.ChartRestriction.G.Pdiv (LieG ptMap dualScale)
open scoped TensorProduct NNReal Matrix

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_unit_exp {p : ℕ} [Fact p.Prime] {C : Type} [Field C] (ε : Eps p C) {n : ℕ} (hn : n ≠ 0) {ζ : Cˣ}
    (hζ : IsPrimitiveRoot ζ (p ^ n)) : ∃ u : ℤ_[p]ˣ, ∀ (a : ℤ_[p]) (b : ℤ), ε.1.lev n ^ GlobalTheory.PDiv.digit n a = ζ ^ b →
      (p : ℤ_[p]) ^ n ∣ a - u * (b : ℤ_[p]) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hε := ε.isPrimitiveRoot n
  obtain ⟨i, -, rfl⟩ := hε.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity _ _).2 hζ.pow_eq_one)
  have hi : i.Coprime (p ^ n) := (hε.pow_iff_coprime (pow_pos hp.pos n) i).1 hζ
  have hi' : IsUnit (i : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Coprime.coprime_dvd_right (dvd_pow_self p hn) hi).symm
  refine ⟨hi'.unit, fun a b hab => ?_⟩
  have h1 : ε.1.lev n ^ ((GlobalTheory.PDiv.digit n a : ℤ) - i * b) = 1 := by
    rw [zpow_sub, zpow_natCast, hab, zpow_mul, zpow_natCast, mul_inv_cancel]
  have h2 := (hε.zpow_eq_one_iff_dvd _).1 h1
  have h3 := map_dvd (Int.castRingHom ℤ_[p]) h2
  have h4 := GlobalTheory.PDiv.pow_dvd_sub_digit n a
  simp only [eq_intCast, Int.cast_natCast, Int.cast_sub, Int.cast_mul, Nat.cast_pow, Int.cast_pow] at h3
  have h5 := dvd_add h4 h3
  rwa [sub_add_sub_cancel] at h5

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X}

theorem exists_omega {R : Type} [CommRing R] {x : Sp R ⟶ X} {G' : Over (Sp R)} [GrpObj G'] {φ : G'.left ⟶ t.G.left}
    (h' : IsGrpPullback G' t.G x φ) (l : TanM x t.G →ₗ[R] R) :
    ∃ f : ReciprocityTheory.ChartRestriction.G.Pdiv.omega G', ∀ y : LieG G', f.1 y = l (tanOf (isTanAtG_lieG h' y)) := by
  refine ⟨⟨fun y => l (tanOf (isTanAtG_lieG h' y)), fun y y' h => ?_, fun a y h => ?_⟩, fun _ => rfl⟩
  · rw [← map_add]
    exact congrArg l (tan_ext (h'.2 _ y.1 y'.1 (tv (tanOf (isTanAtG_lieG h' y))) (tv (tanOf (isTanAtG_lieG h' y')))
      rfl rfl).symm)
  · rw [← smul_eq_mul, ← map_smul]
    refine congrArg l (tan_ext ?_)
    have ha : (dualScale a).toRingHom = epsScaleR a := by
      ext y <;> simp [dualScale, epsScaleR]
    change (ptMap (dualScale a) ≫ y.1).left ≫ φ = _
    rw [Over.comp_left, Category.assoc]
    exact congrArg (fun r => spMap r ≫ y.1.left ≫ φ) ha

theorem exists_coord {R : Type} [CommRing R] {x : Sp R ⟶ X} {g : ℕ} {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)}
    (he : IsTanBasis t x e) (i : Fin g) : ∃ l : TanM x t.G →ₗ[R] R, ∀ a : Fin g → R, l (∑ j, a j • tanOf (he.1 j)) = a i := by
  have h₁ : spMap (RingHom.id R) = 𝟙 _ := Spec.map_id _
  have h₂ : spMap (Formalism.L2.Pj.dualMap (RingHom.id R)) = 𝟙 _ := by
    have : Formalism.L2.Pj.dualMap (RingHom.id R) = RingHom.id _ := by
      refine RingHom.ext fun z => ?_
      ext <;> simp [Formalism.L2.Pj.dualMap]
    rw [this]
    exact Spec.map_id _
  have key (m : TanM x t.G) : ∃! a : Fin g → R, ∑ l, a l • tanOf (he.1 l) = m := by
    have h := he.2 R (RingHom.id R) (tv m).left
    simp only [h₁, h₂, Category.id_comp] at h
    exact (existsUnique_congr fun a => (isComb_iff (fun l => tanOf (he.1 l)) a m).trans eq_comm).1 (h (isTan_tv m))
  let b : Module.Basis (Fin g) R (TanM x t.G) := .mk (v := fun i => tanOf (he.1 i))
    (Fintype.linearIndependent_iffₛ.2 fun f g hfg => congrFun ((key _).unique hfg rfl))
    fun u _ => (Submodule.mem_span_range_iff_exists_fun R).2 (key u).exists
  have hb : ∀ j, tanOf (he.1 j) = b j := fun j => by simp only [b, Module.Basis.mk_apply]
  exact ⟨b.coord i, fun a => by simp only [hb, Module.Basis.coord_apply, Module.Basis.repr_sum_self]⟩

theorem exists_scale {K : Type} [NormedField K] {g : ℕ} (a : Fin g → K) :
    ∃ c : K, c ≠ 0 ∧ (∀ i, ‖c * a i‖ ≤ 1) ∧ (c = 1 ∨ ∃ i, c * a i = 1) := by
  by_cases h : ∀ i, ‖a i‖ ≤ 1
  · exact ⟨1, one_ne_zero, fun i => by rw [_root_.one_mul]; exact h i, Or.inl rfl⟩
  push Not at h
  obtain ⟨i₀, hi₀⟩ := h
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖a i‖) ⟨i₀, Finset.mem_univ _⟩
  have h0 : a i ≠ 0 := norm_pos_iff.1 (zero_lt_one.trans (hi₀.trans_le (hi i₀ (Finset.mem_univ _))))
  refine ⟨(a i)⁻¹, inv_ne_zero h0, fun j => ?_, Or.inr ⟨i, inv_mul_cancel₀ h0⟩⟩
  rw [← div_eq_inv_mul, norm_div]
  exact div_le_one_of_le₀ (hi j (Finset.mem_univ _)) (norm_nonneg _)

theorem exists_approx {p : ℕ} [Fact p.Prime] {v : Valuation ℂ_[p] ℝ≥0} [Fact ¬IsUnit (p : ↥(intO ℂ_[p]))]
    [IsAdicComplete (Ideal.span {(p : ↥(intO ℂ_[p]))}) ↥(intO ℂ_[p])] [HenselianLocalRing ↥(intO ℂ_[p])]
    [a1 : Algebra ℤ_[p] ↥(intO ℂ_[p])] [a2 : Algebra ℤ_[p] ℂ_[p]]
    [@IsScalarTower ℤ_[p] ↥(intO ℂ_[p]) ℂ_[p] a1.toSMul Algebra.toSMul a2.toSMul]
    {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v ↥(intO ℂ_[p]) Λ) (hcok : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.CokernelBound P)
    {z : Sp ↥(intO ℂ_[p]) ⟶ X} {π : P.G.left ⟶ t.G.left} (hπ : IsGrpPullback P.G t.G z π) {n N g : ℕ} (hn : 3 ≤ n)
    (χ : Fin N → TorsChar t z (p ^ n)) (s : Module.Basis (Fin N) ℤ_[p] P.T)
    (hc : ∀ m (w : Over.mk (spMap (algebraMap ↥(intO ℂ_[p]) ↥(intO ℂ_[p])) ≫ z) ⟶ t.G) (a : Pts P.A.A),
      w ^ (p ^ n) = 1 → a.left ≫ P.gen ≫ π = spMap (algebraMap ↥(intO ℂ_[p]) ℂ_[p]) ≫ w.left →
        algebraMap ↥(intO ℂ_[p]) ℂ_[p] ((χ m).χ _ w : ↥(intO ℂ_[p])) = (weil P.A (p ^ n) a ((s m).lev n) : ℂ_[p]))
    {u : Fin g → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)} (hu : ∀ l, IsTanAtG t (spMap (intO ℂ_[p]).subtype ≫ z) (u l))
    {Mc : Matrix (Fin N) (Fin g) ℂ_[p]} (hM : DlogVals t z χ u Mc) (cf : Fin g → ℂ_[p]) (hβ : ∀ m, ‖(Mc *ᵥ cf) m‖ ≤ 1) :
    ∃ b ∈ Submodule.span ℂ_[p] (Set.range P.bLie), ∀ m, ‖(Mc *ᵥ cf) m - P.pairV b (1 ⊗ₜ s m)‖ ≤ ‖(p : ℂ_[p])‖ ^ (n - 2) := by
  have hp1 : ‖(p : ℂ_[p])‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap']
    exact Padic.norm_p_lt_one
  have hp0 : 0 < ‖(p : ℂ_[p])‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hf : ∀ x : ℤ_[p], ‖algebraMap ℤ_[p] ℂ_[p] x‖ ≤ 1 := fun x => by
    rw [IsScalarTower.algebraMap_apply ℤ_[p] ↥(intO ℂ_[p]) ℂ_[p]]
    exact (algebraMap ℤ_[p] ↥(intO ℂ_[p]) x).2
  obtain ⟨d, e, he⟩ := GlobalTheory.LieLocBasis.exists_lie_basis_stable E H X t _ z
  replace he : IsTanBasis t z e := he
  have heC := fun i => GlobalTheory.FactorDepth.isTanAtG_map t (intO ℂ_[p]).subtype (he.1 i)
  choose A hA using fun l => (he.2 _ (intO ℂ_[p]).subtype (u l) (hu l)).exists
  obtain ⟨c, hc0, hc1, hc2⟩ := exists_scale (∑ l, cf l • A l)
  let a : Fin d → ↥(intO ℂ_[p]) := fun i => ⟨c * (∑ l, cf l • A l) i, hc1 i⟩
  have hv := (GlobalTheory.LineNorm.Chart.comb_iff he.1 a _).2 rfl
  have hvt := isTan_tv (∑ j, a j • tanOf (he.1 j))
  have hvC := GlobalTheory.ShFam.CoordComp.comb_map t (intO ℂ_[p]).subtype hv
  have hw := (GlobalTheory.LineNorm.Chart.comb_iff hu (fun l => c * cf l) _).2 rfl
  have hw' := GlobalTheory.LineNorm.Chart.comb_comb heC hA hw
  have ha : (∑ l, (c * cf l) • A l) = fun i => (intO ℂ_[p]).subtype (a i) := by
    funext i
    change _ = c * _
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, _root_.mul_assoc]
  rw [ha] at hw'
  rw [((GlobalTheory.LineNorm.Chart.comb_iff heC _ _).1 hw').trans ((GlobalTheory.LineNorm.Chart.comb_iff heC _ _).1 hvC).symm] at hw
  obtain ⟨y, hy⟩ := exists_lieG hπ hvt
  obtain ⟨x, rfl⟩ := P.lieCmp.surjective y
  have hd : ∀ m, ‖c * (Mc *ᵥ cf) m - P.pairV (P.bLie x) (1 ⊗ₜ s m)‖ ≤ ‖(p : ℂ_[p])‖ ^ n := fun m => by
    obtain ⟨r, hr, hr'⟩ := hM _ _ hvt hw m
    obtain ⟨w, hw⟩ := GlobalTheory.HTLevel.red_ex (Ideal.span {(p : ↥(intO ℂ_[p])) ^ n}) hvt
    have h2 := GlobalTheory.TorsCharDlog.snd_chi_eq t P z π hπ n (χ m) (s m) (hc m) x w (by rw [hy]; exact hw)
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 ((hr' w hw).symm.trans h2))
    have hq' : (r : ℂ_[p]) - ((P.al₀ (s m)).1 x : ℂ_[p]) = (p : ℂ_[p]) ^ n * q := by
      exact_mod_cast congrArg Subtype.val hq
    have h3 : c * (Mc *ᵥ cf) m = r := by
      rw [hr]
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]
    rw [h3, P.pairV_bLie]
    refine (congrArg norm hq').trans_le ?_
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (pow_nonneg hp0.le _) q.2
  have hcc : ‖(p : ℂ_[p])‖ ^ 2 ≤ ‖c‖ := by
    rcases hc2 with rfl | ⟨i, hi⟩
    · rw [norm_one]
      exact pow_le_one₀ hp0.le hp1.le
    obtain ⟨l, hl⟩ := exists_coord he i
    obtain ⟨f, hf'⟩ := exists_omega hπ l
    have h1 : (P.omegaCmp f).1 x = 1 := by
      rw [P.omegaCmp_apply, hf', show tanOf (isTanAtG_lieG hπ (P.lieCmp x)) = ∑ j, a j • tanOf (he.1 j) from tan_ext hy,
        hl]
      exact Subtype.ext hi
    have h2 : ∀ y : P.T, ‖(((P.al₀ y).1 x : ↥(intO ℂ_[p])) : ℂ_[p])‖ ≤ max ‖c‖ (‖(p : ℂ_[p])‖ ^ n) := fun y => by
      refine (congrArg norm (P.pairV_bLie x y)).ge.trans
        (norm_pair_le hf _ s _ (le_max_of_le_left (norm_nonneg _)) (fun m => ?_) y)
      have e1 : P.pairV (P.bLie x) (1 ⊗ₜ s m) =
          c * (Mc *ᵥ cf) m + -(c * (Mc *ᵥ cf) m - P.pairV (P.bLie x) (1 ⊗ₜ s m)) := by ring
      refine (congrArg norm e1).trans_le ((IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le_max ?_ ((norm_neg _).trans_le (hd m))))
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hβ m)
    have h3 : ∀ y, ‖(((P.al y).1 x : ↥(intO ℂ_[p])) : ℂ_[p])‖ ≤ max ‖c‖ (‖(p : ℂ_[p])‖ ^ n) := fun y => by
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' hy hy' =>
        rw [map_add, Submodule.coe_add, Pi.add_apply, Subring.coe_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hy hy')
      | tmul q y =>
        rw [Point.al_tmul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Subring.coe_mul, norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) q.2).trans (h2 y)
    obtain ⟨y, hy⟩ := hcok (P.omegaCmp f)
    have h4 := h3 y
    rw [hy, Submodule.coe_smul, Pi.smul_apply, h1, smul_eq_mul, _root_.mul_one, Subring.coe_pow, Subring.coe_natCast,
      norm_pow] at h4
    exact (le_max_iff.1 h4).resolve_right (not_le.2 (pow_lt_pow_right_of_lt_one₀ hp0 hp1 (by omega)))
  refine ⟨c⁻¹ • P.bLie x, Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩), fun m => ?_⟩
  have e1 : (Mc *ᵥ cf) m - P.pairV (c⁻¹ • P.bLie x) (1 ⊗ₜ s m) =
      c⁻¹ * (c * (Mc *ᵥ cf) m - P.pairV (P.bLie x) (1 ⊗ₜ s m)) := by
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, mul_sub, inv_mul_cancel_left₀ hc0]
  rw [e1, norm_mul, norm_inv, inv_mul_le_iff₀ (norm_pos_iff.2 hc0)]
  refine (hd m).trans ?_
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 + k := ⟨n - 2, by omega⟩
  rw [pow_add, Nat.add_sub_cancel_left]
  exact mul_le_mul_of_nonneg_right hcc (pow_nonneg hp0.le _)

set_option maxHeartbeats 1000000 in

theorem norm_dot_le_of_weil (hK : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint) {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β)
    {p : ℕ} [Fact p.Prime] {z : Sp ↥(intO ℂ_[p]) ⟶ Z.X} {yy : Sp ℂ_[p] ⟶ Xo.XF c} (hP : HasPoint Z.oF.t Z.m.φ z yy)
    {N n g : ℕ} (hN : N = Module.finrank ℤ Dw.La) (hn : 3 ≤ n) {s : Fin N → (Over.mk yy ⟶ Z.oF.t.G)} {ζ : ℂ_[p]ˣ}
    {B J : Matrix (Fin N) (Fin N) ℤ} (hζ : IsPrimitiveRoot ζ (p ^ n)) (hBJ : B.transpose * J = 1)
    (hG : IsGram Z.oF.t (p ^ n) s ζ B) {χ : Fin N → TorsChar Z.t z (p ^ n)}
    (hch : ∀ m, IsWeilChar Z.oF.t Z.m.φ (s m) (χ m)) {u : Fin g → (Sp (DualNumber ℂ_[p]) ⟶ Z.t.G.left)}
    (hu : ∀ l, IsTanAtG Z.t (spMap (intO ℂ_[p]).subtype ≫ z) (u l)) {Mc : Matrix (Fin N) (Fin g) ℂ_[p]}
    (hM : DlogVals Z.t z χ u Mc) (cf cf' : Fin g → ℂ_[p]) (hβ : ∀ m, ‖(Mc *ᵥ cf) m‖ ≤ 1)
    (hβ' : ∀ m, ‖(Mc *ᵥ cf') m‖ ≤ 1) :
    ‖(Mc *ᵥ cf) ⬝ᵥ (J.map (Int.castRingHom ℂ_[p]) *ᵥ (Mc *ᵥ cf'))‖ ≤ ‖(p : ℂ_[p])‖ ^ (n - 2) := by
  obtain ⟨hpu, hcomp, hhens, hint, ⟨io⟩⟩ := GlobalTheory.HalfGeo.IntProof.intSt p
  haveI : Fact ¬IsUnit (p : ↥(intO ℂ_[p])) := ⟨hpu⟩
  letI a1 : Algebra ℤ_[p] ↥(intO ℂ_[p]) := io.toAlgebra
  letI a2 : Algebra ℤ_[p] ℂ_[p] := ((algebraMap ↥(intO ℂ_[p]) ℂ_[p]).comp io).toAlgebra
  haveI a3 : @IsScalarTower ℤ_[p] ↥(intO ℂ_[p]) ℂ_[p] a1.toSMul Algebra.toSMul a2.toSMul :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨v, Λ, _, _, P, π, ψ, hπ, hψ, hsq, hL⟩ := hP
  have hk : 1 ≤ p ^ n := one_le_ppow p n
  have hp1 : ‖(p : ℂ_[p])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ _
  have hg : P.A.g = Module.finrank ℚ E / 2 * (Dw.p + Dw.q) := by
    have h1 := GlobalTheory.ObjDim.smoothOfRelativeDimension Z.oF
    have h2 : SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) P.A.A.hom :=
      (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hψ.1 h1
    exact ReciprocityTheory.ChartRestriction.G.H1.dim_unique P.A.A.hom P.A.smoothDim h2
      ((η[P.A.A]).left (Nonempty.some (inferInstanceAs (Nonempty (Sp ℂ_[p])))))
  have hrk : Module.finrank ℤ_[p] P.T = N := by rw [P.hodgeTateLatticePoint_finrank_tateModule, hg, hN, GlobalTheory.ZM.finrank_int_lattice]
  have hlift : ∀ m, ∃ t : P.T, (Tate.lev t n).left ≫ ψ = (s m).left := fun m => by
    obtain ⟨y, hy⟩ := Iso.exists_lift hψ.1 (s m)
    have hy1 := Iso.pow_eq_one_of_push hψ (T₀ := Over.mk yy) (𝟙 _) (Category.id_comp _) y (s m)
      ((Category.id_comp _).trans hy.symm) (hG.1 m)
    obtain ⟨t, ht⟩ := (tate_free_of_card p _ _ P.card_torsion).2.1 n y hy1
    exact ⟨t, by rw [ht, hy]⟩
  choose t₀ ht using hlift
  obtain ⟨u₀, hu'⟩ := exists_unit_exp P.eps (by omega) hζ
  have hgram : ∀ m m', (p : ℤ_[p]) ^ n ∣ pairT P.A P.eps (t₀ m) (t₀ m') - u₀ * (B m m' : ℤ_[p]) := fun m m' =>
    hu' _ _ ((pow_pairT P.A P.eps (t₀ m) (t₀ m') n).trans (Iso.eq_weil P.A Z.oF.t.PP.isLB hψ hL hk (Tate.lev_pow _ n)
      (Tate.lev_pow _ n) (ht m) (ht m') (hG.2 m m')).symm)
  have hdet : IsUnit (Matrix.of fun m m' => pairT P.A P.eps (t₀ m) (t₀ m')).det :=
    isUnit_det hBJ fun m m' => (dvd_pow_self _ (by omega)).trans (hgram m m')
  obtain ⟨b, hb⟩ := exists_basis hrk (pairT P.A P.eps) t₀ hdet
  obtain rfl : ⇑b = t₀ := funext hb
  obtain ⟨-, -, hcok, -, -, -, -, h5, -, h7⟩ := hK p ℂ_[p] v ↥(intO ℂ_[p]) Λ P
  have key := exists_approx P hcok hπ hn χ b (fun m w' y hw' hy => by
    obtain ⟨σ, hσ⟩ := Iso.exists_push hψ.1 y
    have hy1 := Iso.pow_eq_one_of_push (P.gen_pull.comp hπ)
      (T₀ := Over.mk (spMap (algebraMap ↥(intO ℂ_[p]) ↥(intO ℂ_[p])) ≫ z)) (spMap (algebraMap ↥(intO ℂ_[p]) ℂ_[p])) (by
        change _ ≫ _ ≫ z = _
        rw [← Category.assoc, ← Spec.map_comp]
        rfl) y w' hy.symm hw'
    have h3 := hch m w' σ hw' (by rw [← hσ, Category.assoc, hsq]; exact hy)
    exact congrArg Units.val (Iso.eq_weil P.A Z.oF.t.PP.isLB hψ hL hk hy1 (Tate.lev_pow _ n) hσ (ht m) h3)) hu hM
  obtain ⟨w, hw, hw1⟩ := key cf hβ
  obtain ⟨w', hw', hw1'⟩ := key cf' hβ'
  rw [← h7] at hw hw'
  exact norm_dot_dual_le (fun r => (io r).2) (pairT P.A P.eps) b hdet hBJ hgram ((h5 _).1 hw _ hw') hβ hβ'
    (pow_le_one₀ (norm_nonneg _) hp1) (pow_le_pow_of_le_one (norm_nonneg _) hp1 (Nat.sub_le _ _)) hw1 hw1'

end Point

theorem isotropic_dualForm : Hypotheses2 → HypothesesH → GlobalTheory.Published.RegularAlteration → GlobalTheory.Published.ScholzeWeinsteinB → GlobalTheory.Published.PrismaticDieudonnePerfd →
    ∀ (D : D7) (O : Setup D), O.Core → ∀ (T : Finset ℕ) (R : ℝ), 2 ≤ R → ∀ p : ℕ, p.Prime → p ∈ T → ∀ (c : O.s.Comp)
    (b : Module.Basis (Fin (D.R.f * O.N + D.R.f * O.N)) ℤ O.S.Dw.La) (n : ℕ), 3 ≤ n →
    ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (hp : (resP v).Prime) (e : Ext v) (y : AlgPt (O.Φ.C c).Y) (Ch : Type)
    (inC : Ch → Prop) (M : Ch → Matrix (Fin (D.R.f * O.N + D.R.f * O.N)) (Fin (D.R.f * O.N)) (AlgebraicClosure D.what₂.LL)),
    resP v = p → PtData O c b n hp e y inC M → ∀ k : ℕ, k + 3 ≤ n → ∀ a, inC a → ∀ u u' : Fin (D.R.f * O.N) → AlgebraicClosure D.what₂.LL,
      supN e.w ((M a).mulVec u) ≤ 1 → supN e.w ((M a).mulVec u') ≤ 1 →
      e.w (dotProduct ((M a).mulVec u)
        (((dualForm O.S.Dw b).map (Int.castRingHom (AlgebraicClosure D.what₂.LL))).mulVec ((M a).mulVec u'))) ≤
        e.w (p : AlgebraicClosure D.what₂.LL) ^ k := by
  intro hP _ _ _ _ D O _ T R _ p _ _ c b n hn v hp e y Ch inC M hv hd k hk a ha u u' hu hu'
  subst hv
  haveI : Fact (resP v).Prime := ⟨hp⟩
  obtain ⟨xO, χ, hx, -, ⟨yy, s, ζ, hζ, hPt, hG, hch⟩, -, hM⟩ := hd
  set io := ioOf (resP v) e with hio
  set r := -Real.log (e.w ((resP v : ℕ) : AlgebraicClosure D.what₂.LL)) / Real.log (resP v) with hr_def
  have hw : ∀ z, e.w z = ‖io z‖ ^ r := GlobalTheory.CovHt.Link.w_eq_norm_ioOf_rpow (resP v) v (residueCharacteristic_mem v) e
  have hw1 : e.w ((resP v : ℕ) : AlgebraicClosure D.what₂.LL) < 1 := by
    have e1 : ((resP v : ℕ) : AlgebraicClosure D.what₂.LL) =
        algebraMap D.what₂.LL _ (algebraMap (𝓞 D.what₂.LL) D.what₂.LL ((resP v : ℕ) : 𝓞 D.what₂.LL)) := by simp
    rw [e1, e.w_alg]
    exact (v.adicAbv_coe_lt_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal v) _).2 (residueCharacteristic_mem v)
  have hw0 : 0 < e.w ((resP v : ℕ) : AlgebraicClosure D.what₂.LL) := e.w.pos (Nat.cast_ne_zero.2 hp.ne_zero)
  have hlp : 0 < Real.log (resP v) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hr : 0 < r := div_pos (neg_pos.2 (Real.log_neg hw0 hw1)) hlp
  have hle : ∀ z z', e.w z ≤ e.w z' ↔ ‖io z‖ ≤ ‖io z'‖ := fun z z' => by
    rw [hw, hw]
    exact Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hr
  have hball : ∀ u : Fin (D.R.f * O.N) → AlgebraicClosure D.what₂.LL, supN e.w ((M a).mulVec u) ≤ 1 →
      ∀ m, ‖((M a).map io).mulVec (io ∘ u) m‖ ≤ 1 := fun u hu m => by
    have h1 := (hle ((M a).mulVec u m) 1).1 (by rw [map_one]; exact (le_supN e.w _ m).trans hu)
    rwa [map_one, norm_one, RingHom.map_mulVec] at h1
  have hcm : ∀ {m m' : ℕ} (A : Matrix (Fin m) (Fin m') (AlgebraicClosure D.what₂.LL)) (x : Fin m' → _),
      io ∘ A.mulVec x = (A.map io).mulVec (io ∘ x) := fun A x => funext fun i => RingHom.map_mulVec io A x i
  have hJ : ((dualForm O.S.Dw b).map (Int.castRingHom (AlgebraicClosure D.what₂.LL))).map io =
      (dualForm O.S.Dw b).map (Int.castRingHom ℂ_[resP v]) := by
    ext i j
    simp
  have hBJ : (gram O.S.Dw b).transpose * dualForm O.S.Dw b = 1 := by
    rw [dualForm, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ (isUnit_det_gram _ b), Matrix.transpose_one]
  have key := norm_dot_le_of_weil (GlobalTheory.HTKernel.hodgeTateKernelAtPoint hP) O.s.T.Z hPt
    ((Module.finrank_eq_card_basis b).trans (Fintype.card_fin _)).symm hn hζ hBJ hG hch
    (fun l => by
      rw [hx]
      exact GlobalTheory.FactorDepth.isTanAtG_map _ (psiAt O c e y) ((frAt O c (below y.1)).tan _ _))
    (hM a ha) _ _ (hball u hu) (hball u' hu')
  rw [← map_pow, hle, RingHom.map_dotProduct, hcm, hcm, hcm, hJ, map_pow, map_natCast, norm_pow]
  exact key.trans (pow_le_pow_of_le_one (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _) (by omega))

end GlobalTheory.EqHalf.IsoLevel
