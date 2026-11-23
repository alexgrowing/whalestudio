import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDiscExtensionTateElement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesTransport

set_option linter.unusedSectionVars false

noncomputable section

namespace GlobalTheory.HWL.Cmp

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct Matrix

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
    {Γ : WGam PD LL O v n s}

scoped instance modS (T : LocLat G Qp LL O) : Module (LL ⊗[Qp] B) (T.V ⊗[Qp] B) :=
  Module.compHom _ (actS (LL := LL) T.V B).toRingHom

theorem smulS_def (T : LocLat G Qp LL O) (a : LL ⊗[Qp] B) (m : T.V ⊗[Qp] B) : a • m = actS T.V B a m := rfl

scoped instance towS (T : LocLat G Qp LL O) : IsScalarTower LL (LL ⊗[Qp] B) (T.V ⊗[Qp] B) :=
  ⟨fun c a m => by rw [smulS_def, smulS_def, map_smul, LinearMap.smul_apply]⟩

scoped instance commS (T : LocLat G Qp LL O) : SMulCommClass (LL ⊗[Qp] B) LL (T.V ⊗[Qp] B) :=
  ⟨fun a c m => by rw [smulS_def, smulS_def, map_smul]⟩

variable {R : WSer Γ} {b₀ : LetA O n →+* LL ⊗[Qp] B} {tS zS : BdR}
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {I : WIo R (O ⊗[Zl] Ai) RW inclR φR gR πA} {E : WEt I} {zl : PowerSeries Zl →+* LetA O n}

namespace Disc

variable (Dc : Disc R b₀ tS zS)

def jA : LetA O n →+* ↥Dc.C := (toL O LL n).codRestrict Dc.C Dc.toL_mem

def res (σ : LetA LL n →+* LetA LL n) (hσ : ∀ a ∈ Dc.C, σ a ∈ Dc.C) : ↥Dc.C →+* ↥Dc.C :=
  (σ.comp Dc.C.val.toRingHom).codRestrict Dc.C fun a => hσ a a.2

def cstC (c : ZMod n → LL) : ↥Dc.C := ⟨cst c, Dc.cst_mem c⟩

@[simp] theorem coe_jA (a : LetA O n) : (Dc.jA a : LetA LL n) = toL O LL n a := rfl

@[simp] theorem coe_res (σ : LetA LL n →+* LetA LL n) (hσ : ∀ a ∈ Dc.C, σ a ∈ Dc.C) (a : ↥Dc.C) :
    (Dc.res σ hσ a : LetA LL n) = σ a := rfl

@[simp] theorem coe_cstC (c : ZMod n → LL) : (Dc.cstC c : LetA LL n) = cst c := rfl

theorem J_jA (a : LetA O n) : Dc.J (Dc.jA a) = b₀ a := Dc.J_toL a

theorem ex_jA (i : ZMod n) (ζ : LL) (a : LetA O n) : Dc.ex i ζ (Dc.jA a) = R.lev i ζ a := Dc.ex_toL i ζ a

theorem ex_cstC (i : ZMod n) (ζ : LL) (c : ZMod n → LL) : Dc.ex i ζ (Dc.cstC c) = PowerSeries.C (c i) :=
  Dc.ex_cst i ζ c

theorem Jt_unit : IsUnit (Dc.J Dc.t) := by
  rw [Dc.periodDiscJ_tateElement]
  exact Dc.tb_unit.map (Algebra.TensorProduct.includeRight : B →ₐ[Qp] LL ⊗[Qp] B)

theorem toL_letE (i : ZMod n) : toL O LL n (letE i) = cst (Pi.single i (1 : LL)) := by
  funext k
  by_cases h : k = i
  · subst h; simp [toL, letE, cst]
  · simp [toL, letE, cst, Pi.single_eq_of_ne h]

include Dc in
theorem lev_letE (i j : ZMod n) (ζ : LL) : R.lev i ζ (letE j) = if i = j then 1 else 0 := by
  rw [← Dc.ex_jA, show Dc.jA (letE j) = Dc.cstC (Pi.single j 1) from Subtype.ext (toL_letE j), ex_cstC]
  by_cases h : i = j
  · subst h; simp
  · simp [Pi.single_eq_of_ne h, h]

theorem letE_mul_cst (i : ZMod n) (c : ZMod n → LL) : b₀ (letE i) * Dc.J (Dc.cstC c) = c i • b₀ (letE i) := by
  rw [← Dc.J_jA, ← map_mul, ← map_smul]
  congr 1
  apply Subtype.ext
  change toL O LL n (letE i) * cst c = c i • toL O LL n (letE i)
  rw [toL_letE]
  funext k
  by_cases h : k = i
  · subst h; simp [cst, PowerSeries.smul_eq_C_mul]
  · simp [cst, Pi.single_eq_of_ne h]

include Dc in
theorem b₀_φ (a : LetA O n) : b₀ (letφ R.φ₀ a) = Algebra.TensorProduct.map (AlgHom.id Qp LL) PD.φ (b₀ a) := by
  rw [← Dc.J_jA, ← Dc.J_jA, ← Dc.J_φ]
  congr 1
  exact Subtype.ext (toL_φ R a)

include Dc in
theorem b₀_γ (g : G) (a : LetA O n) : b₀ (letγ (R.γ₀ (Γ.resΓ g)) a) =
    Algebra.TensorProduct.map (AlgHom.id Qp LL) ((PD.actB g).toAlgHom.restrictScalars Qp) (b₀ a) := by
  rw [← Dc.J_jA, ← Dc.J_jA, ← Dc.J_γ]
  congr 1
  exact Subtype.ext (toL_γ R _ a)

include Dc in
theorem Q_unit : IsUnit (b₀ R.Q) := by
  have h1 : ∀ (k : ℕ) (a : LetA O n), IsUnit (b₀ a) → IsUnit (b₀ ((letφ (n := n) R.φ₀ ^ k) a)) := by
    intro k
    induction k with
    | zero => intro a ha; simpa using ha
    | succ k ih =>
      intro a ha
      rw [pow_succ', AlgHom.mul_apply, Dc.b₀_φ]
      exact (ih a ha).map _
  have h2 : letφ (n := n) R.φ₀ letπ = letπ * fun _ => R.q₀ := by
    funext i
    simp [letφ, letπ, R.φ₀_X]
  have h3 := h1 (s - 1 + 1) _ Dc.π_unit
  rw [pow_succ, AlgHom.mul_apply, h2, map_mul, map_mul] at h3
  exact isUnit_of_mul_isUnit_right h3

end Disc

theorem Q_pow_cancel (R : WSer Γ) (m : ℕ) (a : LetA LL n) (h : toL O LL n (R.Q ^ m) * a = 0) : a = 0 := by
  have hp : (PD.p : LL) ≠ 0 := by
    intro h0
    have := Γ.v_l
    rw [h0, AddValuation.map_zero] at this
    exact WithTop.top_ne_coe (this.trans WithTop.coe_one.symm)
  have h0 : ∀ b : PowerSeries O, PowerSeries.constantCoeff (R.φ₀ b) = PowerSeries.constantCoeff b := by
    intro b
    conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const b]
    have : R.φ₀ (PowerSeries.C (PowerSeries.constantCoeff b)) = PowerSeries.C (PowerSeries.constantCoeff b) :=
      R.φ₀.commutes _
    rw [map_add, map_mul, this, R.φ₀_X]
    simp
  have hq : PowerSeries.constantCoeff R.q₀ = (PD.p : O) := by
    have := congrArg (PowerSeries.coeff 1) R.q₀_def
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply] at this
    rw [this, map_sub, PowerSeries.coeff_one_pow]
    simp [PowerSeries.coeff_one]
  have h1 : ∀ (k : ℕ) (i : ZMod n),
      PowerSeries.constantCoeff ((letφ (n := n) R.φ₀ ^ k) (fun _ => R.q₀) i) = (PD.p : O) := by
    intro k
    induction k with
    | zero => intro i; simpa using hq
    | succ k ih =>
      intro i
      rw [pow_succ', AlgHom.mul_apply]
      exact (h0 _).trans (ih (i - 1))
  funext i
  have h2 : toL O LL n R.Q i ≠ 0 := by
    intro hz
    have : PowerSeries.constantCoeff (toL O LL n R.Q i) = (PD.p : LL) := by
      change PowerSeries.constantCoeff (PowerSeries.map (algebraMap O LL) (R.Q i)) = _
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, WSer.Q, h1, map_natCast]
    rw [hz, map_zero] at this
    exact hp this.symm
  have h3 := congrFun h i
  rw [map_pow, Pi.mul_apply, Pi.pow_apply, Pi.zero_apply] at h3
  exact (mul_eq_zero.mp h3).resolve_left (pow_ne_zero _ h2)

structure Frame (Dc : Disc R b₀ tS zS) (Mo : WN E zl) (T : LocLat G Qp LL O) where
  r : ℕ
  w : ℕ
  m : ℕ
  nb : Module.Basis (Fin r) (LetA O n) ↥(Mo.N T)
  U : Matrix (Fin r) (Fin r) (LetA LL n)
  V : Matrix (Fin r) (Fin r) (LetA LL n)
  UV : U * V = 1
  U_mem : ∀ i j, (Dc.t : LetA LL n) ^ w * U i j ∈ Dc.C
  V_mem : ∀ i j, (Dc.t : LetA LL n) ^ w * V i j ∈ Dc.C
  Gm : Γ.Gam → Matrix (Fin r) (Fin r) (LetA O n)
  Gm_def : ∀ g j, E.γD T g (nb j : E.DD T) = ∑ i, Gm g i j • (nb i : E.DD T)
  GU : ∀ g, (Gm g).map (toL O LL n) * U.map (γL R g) = U
  Pm : Matrix (Fin r) (Fin r) (LetA O n)
  Pm_def : ∀ j, R.Q ^ m • E.φD T (nb j : E.DD T) = ∑ i, Pm i j • (nb i : E.DD T)
  Cm : Matrix (Fin r) (Fin r) (ZMod n → LL)
  PU : Pm.map (toL O LL n) * U.map (φL LL n PD.p) = toL O LL n (R.Q ^ m) • (U * Cm.map cst)

namespace Frame

variable {Dc : Disc R b₀ tS zS} {Mo : WN E zl} {T T' : LocLat G Qp LL O}

def Ut (F : Frame Dc Mo T) (i j : Fin F.r) : ↥Dc.C := ⟨_, F.U_mem i j⟩

def a (F : Frame Dc Mo T) (x : ↥(Mo.N T)) (j : Fin F.r) : ↥Dc.C :=
  ∑ k, (⟨_, F.V_mem j k⟩ : ↥Dc.C) * Dc.jA (F.nb.repr x k)

theorem coe_a (F : Frame Dc Mo T) (x : ↥(Mo.N T)) (j : Fin F.r) : (F.a x j : LetA LL n) =
    (Dc.t : LetA LL n) ^ F.w * (F.V *ᵥ fun k => toL O LL n (F.nb.repr x k)) j := by
  simp [a, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

variable (bT : ∀ T : LocLat G Qp LL O, ↥(Mo.N T) →+ T.V ⊗[Qp] B)

def d (F : Frame Dc Mo T) (j : Fin F.r) : T.V ⊗[Qp] B :=
  ((Dc.Jt_unit.unit⁻¹ : (LL ⊗[Qp] B)ˣ) : LL ⊗[Qp] B) ^ F.w • ∑ i, Dc.J (F.Ut i j) • bT T (F.nb i)

theorem d_spec (F : Frame Dc Mo T) (j : Fin F.r) :
    Dc.J Dc.t ^ F.w • F.d bT j = ∑ i, Dc.J (F.Ut i j) • bT T (F.nb i) := by
  rw [d, smul_smul, ← mul_pow, IsUnit.mul_val_inv, one_pow, one_smul]

def Dl (F : Frame Dc Mo T) (i : ZMod n) (j : Fin F.r) : T.V ⊗[Qp] B := b₀ (letE i) • F.d bT j

def lev (F : Frame Dc Mo T) (i : ZMod n) (ζ : LL) : ↥(Mo.N T) →+ (ℤ → T.V ⊗[Qp] B) :=
  AddMonoidHom.mk' (fun x k => ∑ j, cz (Dc.ex i ζ (F.a x j)) (k + (F.w : ℤ)) • F.Dl bT i j) (by
    intro x y
    funext k
    simp [a, mul_add, Finset.sum_add_distrib, cz_add, add_smul])

theorem lev_apply (F : Frame Dc Mo T) (i : ZMod n) (ζ : LL) (x : ↥(Mo.N T)) (k : ℤ) :
    F.lev bT i ζ x k = ∑ j, cz (Dc.ex i ζ (F.a x j)) (k + (F.w : ℤ)) • F.Dl bT i j := rfl

theorem d_transport (F : Frame Dc Mo T) (F' : Frame Dc Mo T') (σ : LetA LL n →+* LetA LL n)
    (hσ : ∀ a ∈ Dc.C, σ a ∈ Dc.C) (σS : LL ⊗[Qp] B →+* LL ⊗[Qp] B)
    (hJ : ∀ a, Dc.J (Dc.res σ hσ a) = σS (Dc.J a)) (h : T.V ⊗[Qp] B →+ T'.V ⊗[Qp] B)
    (hh : ∀ (a : LL ⊗[Qp] B) m, h (a • m) = σS a • h m) (q : LetA O n) (hq : IsUnit (b₀ q))
    (H : Matrix (Fin F'.r) (Fin F.r) (LetA O n))
    (hH : ∀ j, b₀ q • h (bT T (F.nb j)) = ∑ i, b₀ (H i j) • bT T' (F'.nb i))
    (Cm : Matrix (Fin F'.r) (Fin F.r) (ZMod n → LL))
    (hU : H.map (toL O LL n) * F.U.map σ = toL O LL n q • (F'.U * Cm.map cst)) (p : Fin F.r) :
    h (F.d bT p) = ∑ j, Dc.J (Dc.cstC (Cm j p)) • F'.d bT j := by
  refine basis_transport Dc.J.toRingHom (Dc.res σ hσ) σS hJ h hh Dc.t (Dc.jA q) Dc.Jt_unit
    (by rw [← Dc.J_jA] at hq; exact hq) F.w F'.w _ _ _ _ F.Ut F'.Ut (fun i j => Dc.jA (H i j))
    (fun i j => Dc.cstC (Cm i j)) (F.d_spec bT) (F'.d_spec bT) (fun j => ?_) (fun k p => ?_) p
  · change Dc.J (Dc.jA q) • _ = ∑ i, Dc.J (Dc.jA (H i j)) • _
    simp only [Dc.J_jA]
    exact hH j
  · apply Subtype.ext
    have h1 := congrFun (congrFun hU k) p
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at h1
    simp only [Ut, MulMemClass.coe_mul, SubmonoidClass.coe_pow, AddSubmonoidClass.coe_finset_sum, Disc.coe_jA,
      Disc.coe_res, Disc.coe_cstC, map_mul, map_pow]
    simp only [mul_left_comm _ (σ (Dc.t : LetA LL n) ^ F.w), mul_assoc, ← Finset.mul_sum]
    rw [h1]
    ring

theorem lev_transport (F : Frame Dc Mo T) (F' : Frame Dc Mo T') (σ : LetA LL n →+* LetA LL n)
    (hσ : ∀ a ∈ Dc.C, σ a ∈ Dc.C) (i i₀ : ZMod n) (ζ ζ₀ κ : LL) (hκ : κ ≠ 0)
    (hex : ∀ f, Dc.ex i ζ (Dc.res σ hσ f) = PowerSeries.rescale κ (Dc.ex i₀ ζ₀ f)) (q q' : LetA O n)
    (hq : ∀ a, toL O LL n q * a = 0 → a = 0) (H : Matrix (Fin F'.r) (Fin F.r) (LetA O n))
    (Cm : Matrix (Fin F'.r) (Fin F.r) (ZMod n → LL))
    (hU : H.map (toL O LL n) * F.U.map σ = toL O LL n q • (F'.U * Cm.map cst))
    (σA : LetA O n →+* LetA O n) (hσA : ∀ a, toL O LL n (σA a) = σ (toL O LL n a))
    (x : ↥(Mo.N T)) (y : ↥(Mo.N T'))
    (hxy : q • y = q' • ∑ p, σA (F.nb.repr x p) • ∑ j, H j p • F'.nb j)
    (h : T.V ⊗[Qp] B →ₗ[LL] T'.V ⊗[Qp] B) (hD : ∀ p, h (F.Dl bT i₀ p) = ∑ j, Cm j p i • F'.Dl bT i j) (k : ℤ) :
    F'.lev bT i ζ y k = ∑ᶠ j : ℕ, PowerSeries.coeff j (R.lev i ζ q') •
      (κ ^ (k - (j : ℤ)) • h (F.lev bT i₀ ζ₀ x (k - (j : ℤ)))) := by
  have hc : toL O LL n q • (fun k => toL O LL n (F'.nb.repr y k)) =
      toL O LL n q' • H.map (toL O LL n) *ᵥ (σ ∘ fun k => toL O LL n (F.nb.repr x k)) := by
    funext j
    have h1 := congrArg (fun z => toL O LL n (F'.nb.repr z j)) hxy
    simp only [map_smul, map_sum, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.finset_sum_apply,
      Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, map_mul, hσA] at h1
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.map_apply, Function.comp_apply, h1]
    simp only [mul_comm]
  have h2 := coord_transport σ F.U F.V F'.U F'.V _ _ _ _ hq F.UV F'.UV hU _ _ hc
  have h3 : ∀ j, Dc.res σ hσ Dc.t ^ F.w * F'.a y j =
      Dc.t ^ F'.w * (Dc.jA q' * ∑ p, Dc.cstC (Cm j p) * Dc.res σ hσ (F.a x p)) := by
    intro j
    apply Subtype.ext
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, AddSubmonoidClass.coe_finset_sum, Disc.coe_jA,
      Disc.coe_res, Disc.coe_cstC, map_mul, map_pow, coe_a, h2]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Matrix.mulVec, dotProduct]
    simp only [Matrix.map_apply, Function.comp_apply, mul_left_comm _ (σ (Dc.t : LetA LL n) ^ F.w),
      ← Finset.mul_sum]
  simp only [lev_apply]
  refine series_transport F.w F'.w _ _ κ hκ _ (fun j p => Cm j p i) (fun j => ?_) h _ _ hD k
  have h4 := congrArg (Dc.ex i ζ) (h3 j)
  simpa only [map_mul, map_pow, map_sum, hex, Dc.numEx_t_eq_fifteen, Dc.ex_jA, Dc.ex_cstC, PowerSeries.rescale_X] using h4

theorem expand (F : Frame Dc Mo T) (f : E.DD T →ₗ[O] E.DD T') (σA : LetA O n →+* LetA O n)
    (hf : ∀ (a : LetA O n) (x : E.DD T), f (a • x) = σA a • f x) (x : ↥(Mo.N T)) :
    f (x : E.DD T) = ∑ p, σA (F.nb.repr x p) • f (F.nb p : E.DD T) := by
  conv_lhs => rw [← F.nb.sum_repr x]
  simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, map_sum, hf]

theorem γD_smulA (T : LocLat G Qp LL O) (g : Γ.Gam) (a : LetA O n) (x : E.DD T) :
    E.γD T g (a • x) = letγ (R.γ₀ g) a • E.γD T g x := by
  have := E.γD_smul T g (algebraMap (LetA O n) R.EE a) x
  rwa [algebraMap_smul, R.γE_ext, algebraMap_smul] at this

theorem φD_smulA (T : LocLat G Qp LL O) (a : LetA O n) (x : E.DD T) :
    E.φD T (a • x) = letφ R.φ₀ a • E.φD T x := by
  have := E.φD_smul T (algebraMap (LetA O n) R.EE a) x
  rwa [algebraMap_smul, R.φE_ext, algebraMap_smul] at this

theorem one_map_cst {r : ℕ} : (1 : Matrix (Fin r) (Fin r) (ZMod n → LL)).map cst = 1 :=
  Matrix.map_one _ (by funext i; simp [cst]) (by funext i; simp [cst])

theorem sum_one_smul {r : ℕ} {M : Type} [AddCommGroup M] [Module LL M] (D : Fin r → M) (i : ZMod n) (p : Fin r) :
    ∑ j, (1 : Matrix (Fin r) (Fin r) (ZMod n → LL)) j p i • D j = D p := by
  rw [Finset.sum_eq_single p]
  · simp
  · intro j _ hj
    simp [Matrix.one_apply_ne hj]
  · simp

theorem finsum_coeff_one {M : Type} [AddCommGroup M] [Module LL M] (f : ℕ → M) :
    ∑ᶠ j : ℕ, PowerSeries.coeff j (1 : PowerSeries LL) • f j = f 0 := by
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    simp [PowerSeries.coeff_one, hj]

theorem Dl_transport (F : Frame Dc Mo T) (F' : Frame Dc Mo T') (h : T.V ⊗[Qp] B →ₗ[LL] T'.V ⊗[Qp] B)
    (i i₀ : ZMod n) (hh : ∀ m, h (b₀ (letE i₀) • m) = b₀ (letE i) • h m)
    (Cm : Matrix (Fin F'.r) (Fin F.r) (ZMod n → LL))
    (hd : ∀ p, h (F.d bT p) = ∑ j, Dc.J (Dc.cstC (Cm j p)) • F'.d bT j) (p : Fin F.r) :
    h (F.Dl bT i₀ p) = ∑ j, Cm j p i • F'.Dl bT i j := by
  simp only [Dl, hh, hd, Finset.smul_sum, smul_smul, Dc.letE_mul_cst, smul_assoc]

theorem lev_supp (F : Frame Dc Mo T) (i : ZMod n) (ζ : LL) (x : ↥(Mo.N T)) (k : ℤ) (hk : k < -(F.w : ℤ)) :
    F.lev bT i ζ x k = 0 := by
  rw [lev_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [cz_neg _ (by omega), zero_smul]

theorem lev_one_neg (F : Frame Dc Mo T) (i : ZMod n) (x : ↥(Mo.N T)) (k : ℤ) (hk : k < 0) :
    F.lev bT i 1 x k = 0 := by
  rw [lev_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  obtain ⟨f, hf⟩ := Dc.ex_one i (F.a x j) F.w (by
    rw [coe_a, Pi.mul_apply, Pi.pow_apply]
    exact (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.mpr (Dc.t_zero i)) _).mul_right _)
  rw [hf, cz_X_pow_mul, cz_neg _ hk, zero_smul]

theorem lev_smul (F : Frame Dc Mo T) (i : ZMod n) (ζ : LL) (α : LetA O n) (x : ↥(Mo.N T)) (k : ℤ) :
    F.lev bT i ζ (α • x) k =
      ∑ᶠ j : ℕ, PowerSeries.coeff j (R.lev i ζ α) • F.lev bT i ζ x (k - (j : ℤ)) := by
  have := lev_transport bT F F (RingHom.id _) (fun _ h => h) i i ζ ζ 1 one_ne_zero
    (fun f => by rw [PowerSeries.rescale_one]; rfl) 1 α (by simp) 1 1
    (by rw [one_map_cst, Matrix.map_one _ (map_zero _) (map_one _)]; simp) (RingHom.id _) (fun _ => rfl)
    x (α • x) (by
      rw [one_smul]
      congr 1
      conv_lhs => rw [← F.nb.sum_repr x]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp [Matrix.one_apply]) LinearMap.id (fun p => (sum_one_smul (F.Dl bT i) i p).symm) k
  simpa using this

theorem lev_Γ (F : Frame Dc Mo T) (g : Γ.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ)
    (h1 : IsPrimitiveRoot ζ (PD.p ^ j)) (h2 : (j : WithTop ℚ) ≤ v (algebraMap O LL (Γ.χΓ g : O) - (a : LL)))
    (h3 : ζ' = ζ ^ a) (x : ↥(Mo.N T)) (hx : E.γD T g (x : E.DD T) ∈ Mo.N T) (k : ℤ) :
    F.lev bT i ζ ⟨E.γD T g (x : E.DD T), hx⟩ k = (algebraMap O LL (Γ.χΓ g : O)) ^ k • F.lev bT i ζ' x k := by
  have := lev_transport bT F F (γL R g).toRingHom (Dc.γ_mem g) i i ζ ζ' (algebraMap O LL (Γ.χΓ g : O))
    ((Γ.χΓ g).isUnit.map (algebraMap O LL)).ne_zero
    (Dc.ex_γ g i ζ ζ' j a h1 h2 h3) 1 1 (by simp) (F.Gm g) 1
    (by rw [one_map_cst, map_one, one_smul, Matrix.mul_one]; exact F.GU g) (letγ (R.γ₀ g)).toRingHom (toL_γ R g)
    x ⟨E.γD T g (x : E.DD T), hx⟩ (by
      rw [one_smul, one_smul]
      apply Subtype.ext
      simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, ← F.Gm_def]
      exact F.expand _ _ (γD_smulA T g) x) LinearMap.id (fun p => (sum_one_smul (F.Dl bT i) i p).symm) k
  rw [this, map_one, finsum_coeff_one]
  simp

variable {bT} {ιdR : Ai →+* BdR} {p1 : Ai}
  {βdR : ∀ T : LocLat G Qp LL O, TW (O ⊗[Zl] Ai) T →+ T.V ⊗[Qp] BdR} (hP : IsPer Mo b₀ ιdR p1 βdR bT)

include hP

theorem bT_sum (hT : IsCrys PD T.ρ) {r : ℕ} (c : Fin r → LetA O n) (y : Fin r → ↥(Mo.N T)) (x : ↥(Mo.N T))
    (hx : (x : E.DD T) = ∑ i, c i • (y i : E.DD T)) : bT T x = ∑ i, b₀ (c i) • bT T (y i) := by
  have : x = ∑ i, c i • y i := Subtype.ext (by simpa using hx)
  rw [this, map_sum]
  simp only [hP.smul T hT, smulS_def]

theorem d_gal (hT : IsCrys PD T.ρ) (F : Frame Dc Mo T) (g : G) (p : Fin F.r) :
    actVB PD T.ρ g (F.d bT p) = F.d bT p := by
  have := d_transport bT F F (γL R (Γ.resΓ g)).toRingHom (Dc.γ_mem _)
    (Algebra.TensorProduct.map (AlgHom.id Qp LL) ((PD.actB g).toAlgHom.restrictScalars Qp)).toRingHom
    (Dc.J_γ g) (actVB PD T.ρ g).toAddMonoidHom
    (fun a m => map_actS (T.ρ g) ((PD.actB g).toAlgHom.restrictScalars Qp) a m) 1 (by simp) (F.Gm (Γ.resΓ g))
    (fun j => by
      rw [map_one, one_smul, LinearMap.toAddMonoidHom_coe, ← hP.gal T hT]
      exact bT_sum hP hT _ _ _ (F.Gm_def _ j)) 1
    (by rw [one_map_cst, map_one, one_smul, Matrix.mul_one]; exact F.GU _) p
  rw [LinearMap.toAddMonoidHom_coe] at this
  rw [this, Finset.sum_eq_single p]
  · rw [Matrix.one_apply_eq, show Dc.cstC 1 = 1 from Subtype.ext (by funext i; simp [cst]), map_one, one_smul]
  · intro j _ hj
    rw [Matrix.one_apply_ne hj, show Dc.cstC 0 = 0 from Subtype.ext (by funext i; simp [cst]), map_zero,
      zero_smul]
  · simp

theorem lev_mem (hT : IsCrys PD T.ρ) (F : Frame Dc Mo T) (i : ZMod n) (ζ : LL) (x : ↥(Mo.N T)) (k : ℤ) :
    F.lev bT i ζ x k ∈ DcrisL PD T.ρ (Γ.emb i) := by
  rw [lev_apply]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ⟨?_, ?_⟩
  · simp only [Dcris, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
    intro g
    have h1 : letγ (R.γ₀ (Γ.resΓ g)) (letE i : LetA O n) = letE i := by
      funext k
      by_cases h : k = i
      · subst h; simp [letγ, letE]
      · simp [letγ, letE, Pi.single_eq_of_ne h]
    have h2 := map_actS (T.ρ g) ((PD.actB g).toAlgHom.restrictScalars Qp) (b₀ (letE i)) (F.d bT j)
    rw [← Dc.b₀_γ, h1] at h2
    exact h2.trans (congrArg _ (d_gal hP hT F g j))
  · simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    intro c
    rw [mulVB, ← actS_one_tmul, ← smulS_def, Dl, smul_smul, Dc.letter, smul_assoc]

theorem lev_φ (hT : IsCrys PD T.ρ) (F : Frame Dc Mo T) (i : ZMod n) (ζ : LL)
    (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) (x : ↥(Mo.N T)) (m : ℕ)
    (hx : R.Q ^ m • E.φD T (x : E.DD T) ∈ Mo.N T) (k : ℤ) :
    F.lev bT i ζ ⟨R.Q ^ m • E.φD T (x : E.DD T), hx⟩ k =
      ∑ᶠ j : ℕ, PowerSeries.coeff j (R.lev i ζ (R.Q ^ m)) •
        (((PD.p : LL) ^ (k - (j : ℤ))) •
          φVB PD (LL := LL) (V := T.V) (F.lev bT (i - 1) (ζ ^ PD.p) x (k - (j : ℤ)))) := by
  have hp : (PD.p : LL) ≠ 0 := by
    intro h0
    have := Γ.v_l
    rw [h0, AddValuation.map_zero] at this
    exact WithTop.top_ne_coe (this.trans WithTop.coe_one.symm)
  have hd := d_transport bT F F (φL LL n PD.p).toRingHom Dc.φ_mem
    (Algebra.TensorProduct.map (AlgHom.id Qp LL) PD.φ).toRingHom
    Dc.J_φ (φVB PD (LL := LL) (V := T.V)).toAddMonoidHom
    (fun a m => map_actS LinearMap.id PD.φ a m) (R.Q ^ F.m) (by rw [map_pow]; exact Dc.Q_unit.pow _) F.Pm
    (fun j => by
      have hj : R.Q ^ F.m • E.φD T (F.nb j : E.DD T) ∈ Mo.N T := by
        rw [F.Pm_def]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (F.nb i).2
      rw [LinearMap.toAddMonoidHom_coe, smulS_def, ← hP.frob T hT _ _ hj]
      exact bT_sum hP hT _ _ _ (F.Pm_def j)) F.Cm F.PU
  refine lev_transport bT F F (φL LL n PD.p).toRingHom Dc.φ_mem i (i - 1) ζ (ζ ^ PD.p) _ hp
    (Dc.ex_φ i ζ hζ) (R.Q ^ F.m) _ (Q_pow_cancel R _) F.Pm F.Cm F.PU (letφ R.φ₀).toRingHom (toL_φ R) x _ ?_ _
    (Dl_transport bT F F _ i (i - 1) (fun z => ?_) _ hd) k
  · apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, ← F.Pm_def]
    rw [F.expand _ (letφ R.φ₀).toRingHom (φD_smulA T) x]
    simp only [Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun p _ => ?_
    congr 1
    ring
  · have h1 : letφ R.φ₀ (letE (i - 1) : LetA O n) = letE i := by
      funext k
      by_cases h : k = i
      · subst h; simp [letφ, letE]
      · have h' : k - 1 ≠ i - 1 := fun e => h (sub_left_injective e)
        simp [letφ, letE, Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']
    have h2 := map_actS (LinearMap.id : T.V →ₗ[LL] T.V) PD.φ (b₀ (letE (i - 1))) z
    rw [← Dc.b₀_φ, h1] at h2
    exact h2

theorem lev_map (hinv : ∀ a : LetA LL n, γL R Γ.gam a = a → ∃ c, a = cst c)
    (f : LatHom T.L T'.L) (hT : IsCrys PD T.ρ) (hT' : IsCrys PD T'.ρ) (F : Frame Dc Mo T) (F' : Frame Dc Mo T')
    (i : ZMod n) (ζ : LL) (x : ↥(Mo.N T)) (hx : E.map f (x : E.DD T) ∈ Mo.N T') (k : ℤ) :
    F'.lev bT i ζ ⟨E.map f (x : E.DD T), hx⟩ k =
      AlgebraTensorModule.map f.f (LinearMap.id : B →ₗ[Qp] B) (F.lev bT i ζ x k) := by
  let H : Matrix (Fin F'.r) (Fin F.r) (LetA O n) := fun j p =>
    F'.nb.repr ⟨E.map f (F.nb p : E.DD T), Mo.map_N f hT hT' _ (F.nb p).2⟩ j
  have hH : ∀ p, E.map f (F.nb p : E.DD T) = ∑ j, H j p • (F'.nb j : E.DD T') := by
    intro p
    have := congrArg Subtype.val
      (F'.nb.sum_repr ⟨E.map f (F.nb p : E.DD T), Mo.map_N f hT hT' _ (F.nb p).2⟩)
    simpa only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] using this.symm
  have hfA : ∀ (a : LetA O n) (z : E.DD T), E.map f (a • z) = a • E.map f z := by
    intro a z
    rw [← algebraMap_smul R.EE a z, map_smul, algebraMap_smul]
  have hHG : H * F.Gm Γ.gam = F'.Gm Γ.gam * H.map (letγ (R.γ₀ Γ.gam)) := by
    ext1 j p
    have h1 := E.map_γ f Γ.gam (F.nb p : E.DD T)
    rw [F.Gm_def, hH, map_sum, map_sum] at h1
    simp only [hfA, hH, γD_smulA, F'.Gm_def] at h1
    have h2 : ∑ a, F.Gm Γ.gam a p • ∑ b, H b a • F'.nb b =
        ∑ a, letγ (R.γ₀ Γ.gam) (H a p) • ∑ b, F'.Gm Γ.gam b a • F'.nb b := Subtype.ext (by simpa using h1)
    have h3 := congrArg (fun z => F'.nb.repr z j) h2
    simp only [map_smul, map_sum, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.finset_sum_apply,
      Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] at h3
    simp only [Matrix.mul_apply, Matrix.map_apply]
    simpa only [mul_comm] using h3
  have hVU : F'.V * F'.U = 1 := mul_eq_one_comm.mp F'.UV
  have hγV : F'.V.map (γL R Γ.gam) = F'.V * (F'.Gm Γ.gam).map (toL O LL n) := by
    have h2 : F'.U.map (γL R Γ.gam) * F'.V.map (γL R Γ.gam) = 1 := by
      rw [← Matrix.map_mul, F'.UV, Matrix.map_one _ (map_zero _) (map_one _)]
    calc F'.V.map (γL R Γ.gam) = F'.V * ((F'.Gm Γ.gam).map (toL O LL n) * F'.U.map (γL R Γ.gam)) *
          F'.V.map (γL R Γ.gam) := by rw [F'.GU, hVU, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]
  have hfix : (F'.V * H.map (toL O LL n) * F.U).map (γL R Γ.gam) = F'.V * H.map (toL O LL n) * F.U := by
    have h4 : (H.map (toL O LL n)).map (γL R Γ.gam) = (H.map (letγ (R.γ₀ Γ.gam))).map (toL O LL n) := by
      ext1 j p
      exact (toL_γ R _ _).symm
    rw [Matrix.map_mul, Matrix.map_mul, hγV, h4, Matrix.mul_assoc F'.V, ← Matrix.map_mul, ← hHG, Matrix.map_mul,
      Matrix.mul_assoc, Matrix.mul_assoc, F.GU, Matrix.mul_assoc]
  choose Cm hCm using fun j p => hinv _ (congrFun (congrFun hfix j) p)
  have hU : H.map (toL O LL n) * F.U.map (RingHom.id _) =
      toL O LL n 1 • (F'.U * (Matrix.of Cm).map cst) := by
    have : (Matrix.of Cm).map cst = F'.V * H.map (toL O LL n) * F.U := by
      ext1 j p
      exact (hCm j p).symm
    rw [this, map_one, one_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, F'.UV, Matrix.one_mul]
    rfl
  have hh : ∀ (a : LL ⊗[Qp] B) (z : T.V ⊗[Qp] B),
      AlgebraTensorModule.map f.f (LinearMap.id : B →ₗ[Qp] B) (a • z) =
        a • AlgebraTensorModule.map f.f (LinearMap.id : B →ₗ[Qp] B) z := by
    intro a z
    have := map_actS f.f (AlgHom.id Qp B) a z
    rwa [Algebra.TensorProduct.map_id] at this
  have hd := d_transport bT F F' (RingHom.id _) (fun _ h => h) (RingHom.id _) (fun _ => rfl)
    (AlgebraTensorModule.map f.f (LinearMap.id : B →ₗ[Qp] B)).toAddMonoidHom hh 1 (by simp) H
    (fun j => by
      rw [map_one, one_smul, LinearMap.toAddMonoidHom_coe, ← hP.nat f hT hT' _ (Mo.map_N f hT hT' _ (F.nb j).2)]
      exact bT_sum hP hT' _ _ _ (hH j)) _ hU
  have := lev_transport bT F F' (RingHom.id _) (fun _ h => h) i i ζ ζ 1 one_ne_zero
    (fun f => by rw [PowerSeries.rescale_one]; rfl) 1 1 (by simp) H _ hU (RingHom.id _) (fun _ => rfl)
    x ⟨E.map f (x : E.DD T), hx⟩ (by
      rw [one_smul, one_smul]
      apply Subtype.ext
      simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, ← hH, ← hfA, ← map_sum, RingHom.id_apply]
      congr 1
      simpa only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] using
        (congrArg Subtype.val (F.nb.sum_repr x)).symm) _
    (Dl_transport bT F F' _ i i (fun z => hh _ z) _ hd) k
  rw [this, map_one, finsum_coeff_one]
  simp

theorem bT_eq (hT : IsCrys PD T.ρ) (F : Frame Dc Mo T) (x : ↥(Mo.N T)) :
    Dc.J Dc.t ^ F.w • bT T x = ∑ j, Dc.J (F.a x j) • F.d bT j := by
  apply (Dc.Jt_unit.pow F.w).smul_left_cancel.mp
  have h1 : ∀ i, ∑ j, F.a x j * F.Ut i j = Dc.t ^ F.w * (Dc.t ^ F.w * Dc.jA (F.nb.repr x i)) := by
    intro i
    apply Subtype.ext
    have h2 := congrFun (Matrix.mulVec_mulVec (fun k => toL O LL n (F.nb.repr x k)) F.U F.V) i
    rw [F.UV, Matrix.one_mulVec] at h2
    simp only [Ut, MulMemClass.coe_mul, SubmonoidClass.coe_pow, AddSubmonoidClass.coe_finset_sum, Disc.coe_jA,
      coe_a]
    rw [← h2]
    conv_rhs => rw [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [Finset.smul_sum, bT_sum hP hT (F.nb.repr x) F.nb x (by
    simpa only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] using
      (congrArg Subtype.val (F.nb.sum_repr x)).symm)]
  simp only [smul_comm (Dc.J Dc.t ^ F.w) (Dc.J (F.a x _)), d_spec]
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_smul]
  simp only [← map_mul, ← map_sum, h1]
  simp only [map_mul, map_pow, Dc.J_jA, mul_assoc]

omit hP in
theorem ιV_smul_sub (ι : LL →ₐ[Qp] BdR) (a : LL ⊗[Qp] B) (m : T.V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := T.V) (a • m) -
      mulVR T (Algebra.TensorProduct.productMap ι (PD.ι.restrictScalars Qp) a) (ιV PD (LL := LL) (V := T.V) m) ∈
      compKer T ι := by
  induction a using TensorProduct.induction_on with
  | zero =>
    have : mulVR T (0 : BdR) (ιV PD (LL := LL) (V := T.V) m) = 0 := by
      change mulR T.V BdR 0 _ = 0
      simp
    simp [this]
  | add a b ha hb =>
    have : ∀ (u u' : BdR) (z : T.V ⊗[Qp] BdR), mulVR T (u + u') z = mulVR T u z + mulVR T u' z := by
      intro u u' z
      change mulR (LL := LL) T.V BdR (u + u') z = mulR (LL := LL) T.V BdR u z + mulR (LL := LL) T.V BdR u' z
      simp
    rw [add_smul, map_add, map_add, this, add_sub_add_comm]
    exact add_mem ha hb
  | tmul c b =>
    refine Submodule.subset_span ⟨c, mulVR T (PD.ι b) (ιV PD (LL := LL) (V := T.V) m), ?_⟩
    congr 1
    · induction m using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [smul_add, map_add, hx, hy]
      | tmul x y => simp [smulS_def, actS_tmul, ιV, mulVR, smul_tmul']
    · induction m using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul x y => simp [ιV, mulVR, mul_assoc]

theorem dR_basis (hT : IsCrys PD T.ρ) (F : Frame Dc Mo T) (ι : LL →ₐ[Qp] BdR) (x : ↥(Mo.N T)) :
    mulVR T (tS ^ F.w) (ιV PD (LL := LL) (V := T.V) (bT T x)) -
      ∑ j, mulVR T (Algebra.TensorProduct.productMap ι (PD.ι.restrictScalars Qp) (Dc.J (F.a x j)))
        (ιV PD (LL := LL) (V := T.V) (F.d bT j)) ∈ compKer T ι := by
  have h1 := ιV_smul_sub (PD := PD) ι (Dc.J Dc.t ^ F.w) (bT T x)
  have h2 : Algebra.TensorProduct.productMap ι (PD.ι.restrictScalars Qp) (Dc.J Dc.t ^ F.w) = tS ^ F.w := by
    rw [map_pow, Dc.periodDiscJ_tateElement]
    simp [Dc.ι_tb]
  rw [h2, bT_eq hP hT, map_sum] at h1
  have h3 := Submodule.sum_mem (compKer T ι) (t := Finset.univ)
    fun j _ => ιV_smul_sub (PD := PD) ι (Dc.J (F.a x j)) (F.d bT j)
  rw [Finset.sum_sub_distrib] at h3
  have := sub_mem h3 h1
  rwa [sub_sub_sub_cancel_left] at this

omit hP in
theorem dR_lev (F : Frame Dc Mo T) (i : ZMod n) (ζ : LL) (ι : LL →ₐ[Qp] BdR)
    (h1 : ∀ c : K₀, ι (Γ.emb i c) = algebraMap K₀ BdR c) (h2 : ι ζ = zS) (x : ↥(Mo.N T)) (k : ℤ) :
    ιV PD (LL := LL) (V := T.V) (F.lev bT i ζ x k) -
      ∑ j, cz (Dc.ex i ζ (F.a x j)) (k + (F.w : ℤ)) • ιV PD (LL := LL) (V := T.V) (F.d bT j) ∈ compKer T ι := by
  have hψ : Algebra.TensorProduct.productMap ι (PD.ι.restrictScalars Qp) (b₀ (letE i)) = 1 := by
    have h3 : ∀ m : ℕ, Algebra.TensorProduct.productMap ι (PD.ι.restrictScalars Qp) (b₀ (letE i)) - 1 ∈
        PD.Fil ((m + 1 : ℕ) : ℤ) := by
      intro m
      have := Dc.taylor i ζ ι h1 h2 (Dc.jA (letE i)) (m + 1)
      rw [Dc.J_jA, Dc.ex_jA, Dc.lev_letE, if_pos rfl, Finset.sum_eq_single 0] at this
      · simpa using this
      · intro j _ hj
        simp [PowerSeries.coeff_one, hj]
      · simp
    refine sub_eq_zero.mp (PD.Fil_sep _ fun a => ?_)
    exact antitone_int_of_succ_le PD.Fil_anti (show a ≤ ((a.toNat + 1 : ℕ) : ℤ) by omega) (h3 a.toNat)
  rw [lev_apply, map_sum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [map_smul, ← smul_sub]
  refine Submodule.smul_mem _ _ ?_
  have h4 := ιV_smul_sub (PD := PD) ι (b₀ (letE i)) (F.d bT j)
  rw [hψ] at h4
  have h5 : ∀ z : T.V ⊗[Qp] BdR, mulVR T (1 : BdR) z = z := by
    intro z
    change mulR (LL := LL) T.V BdR 1 z = z
    simp
  rwa [h5] at h4

end Frame

end GlobalTheory.HWL.Cmp
