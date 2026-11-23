import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero

noncomputable section

namespace GlobalTheory.HWL.Cmp

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

section Act

variable {Qp LL : Type} [Field Qp] [Field LL] [Algebra Qp LL] (V : Type) [AddCommGroup V] [Module LL V]
  [Module Qp V] [IsScalarTower Qp LL V] (B : Type) [CommRing B] [Algebra Qp B]

def mulR : B →ₐ[Qp] Module.End LL (V ⊗[Qp] B) where
  toFun b := AlgebraTensorModule.map LinearMap.id (LinearMap.mulLeft Qp b)
  map_one' := by ext x y; simp
  map_mul' a b := by ext x y; simp [mul_assoc]
  map_zero' := by ext x y; simp
  map_add' a b := by ext x y; simp [add_mul, tmul_add]
  commutes' c := by
    ext x y
    simp [Algebra.algebraMap_eq_smul_one, smul_tmul']

def actS : LL ⊗[Qp] B →ₐ[LL] Module.End LL (V ⊗[Qp] B) :=
  Algebra.TensorProduct.lift (Algebra.ofId LL _) (mulR V B) (fun c _ => Algebra.commutes c _)

variable {V B}

open TensorProduct in
variable {Qp LL : Type} [Field Qp] [Field LL] [Algebra Qp LL] (V : Type) [AddCommGroup V] [Module LL V]
  [Module Qp V] [IsScalarTower Qp LL V] (B : Type) [CommRing B] [Algebra Qp B] in
variable {V B} in
theorem _root_.GlobalTheory.HWL.Cmp.actS_tmul (c : LL) (b : B) (x : V) (y : B) :
    _root_.GlobalTheory.HWL.Cmp.actS V B (c ⊗ₜ[Qp] b) (x ⊗ₜ[Qp] y) = (c • x) ⊗ₜ[Qp] (b * y) := by
  simp [_root_.GlobalTheory.HWL.Cmp.actS, _root_.GlobalTheory.HWL.Cmp.mulR, smul_tmul']

open TensorProduct in
variable {Qp LL : Type} [Field Qp] [Field LL] [Algebra Qp LL] (V : Type) [AddCommGroup V] [Module LL V]
  [Module Qp V] [IsScalarTower Qp LL V] (B : Type) [CommRing B] [Algebra Qp B] in
variable {V B} in
theorem _root_.GlobalTheory.HWL.Cmp.actS_one_tmul (b : B) (m : V ⊗[Qp] B) :
    _root_.GlobalTheory.HWL.Cmp.actS (LL := LL) V B ((1 : LL) ⊗ₜ[Qp] b) m =
      AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp b) m := by
  simp [_root_.GlobalTheory.HWL.Cmp.actS, _root_.GlobalTheory.HWL.Cmp.mulR]

open TensorProduct in
variable {Qp LL : Type} [Field Qp] [Field LL] [Algebra Qp LL] (V : Type) [AddCommGroup V] [Module LL V]
  [Module Qp V] [IsScalarTower Qp LL V] (B : Type) [CommRing B] [Algebra Qp B] in
variable {V B} in

theorem _root_.GlobalTheory.HWL.Cmp.map_actS {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {B' : Type} [CommRing B'] [Algebra Qp B'] (f : V →ₗ[LL] V') (h : B →ₐ[Qp] B') (a : LL ⊗[Qp] B)
    (m : V ⊗[Qp] B) :
    AlgebraTensorModule.map f h.toLinearMap (_root_.GlobalTheory.HWL.Cmp.actS V B a m) =
      _root_.GlobalTheory.HWL.Cmp.actS V' B' (Algebra.TensorProduct.map (AlgHom.id Qp LL) h a)
        (AlgebraTensorModule.map f h.toLinearMap m) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul c b =>
    induction m using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [_root_.GlobalTheory.HWL.Cmp.actS_tmul]
    | add m₁ m₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | add a₁ a₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]

end Act

def cz {L : Type} [CommRing L] (f : PowerSeries L) (k : ℤ) : L :=
  if 0 ≤ k then PowerSeries.coeff k.toNat f else 0

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
    {Γ : WGam PD LL O v n s}

def toL (O LL : Type) [CommRing O] [Field LL] [Algebra O LL] (n : ℕ) : LetA O n →+* LetA LL n :=
  RingHom.pi fun i => (PowerSeries.map (algebraMap O LL)).comp (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) i)

def cst {L : Type} [CommRing L] {n : ℕ} (c : ZMod n → L) : LetA L n := fun i => PowerSeries.C (c i)

open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
    {Γ : _root_.GlobalTheory.HWL.WGam PD LL O v n s} in
theorem _root_.GlobalTheory.HWL.Cmp.hasSubst_γ (R : _root_.GlobalTheory.HWL.WSer Γ) (g : Γ.Gam) :
    PowerSeries.HasSubst (PowerSeries.map (algebraMap O LL) (R.γ₀ g PowerSeries.X)) := by
  refine PowerSeries.HasSubst.of_constantCoeff_zero' ?_
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, (R.γ₀_X g).1, map_zero]

open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
    {Γ : _root_.GlobalTheory.HWL.WGam PD LL O v n s} in
theorem _root_.GlobalTheory.HWL.Cmp.hasSubst_φ (L : Type) [CommRing L] (p : ℕ) :
    PowerSeries.HasSubst ((1 + PowerSeries.X) ^ p - 1 : PowerSeries L) := by
  refine PowerSeries.HasSubst.of_constantCoeff_zero' ?_
  simp

def γL (R : WSer Γ) (g : Γ.Gam) : LetA LL n →ₐ[LL] LetA LL n :=
  letγ (PowerSeries.substAlgHom (hasSubst_γ R g))

def φL (L : Type) [CommRing L] (n p : ℕ) : LetA L n →ₐ[L] LetA L n :=
  letφ (PowerSeries.substAlgHom (hasSubst_φ L p))

open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
    {Γ : _root_.GlobalTheory.HWL.WGam PD LL O v n s} in
theorem _root_.GlobalTheory.HWL.Cmp.γL_apply (R : _root_.GlobalTheory.HWL.WSer Γ) (g : Γ.Gam) (a : _root_.Formalism.BasicNotions.LetA LL n) : _root_.GlobalTheory.HWL.Cmp.γL R g a =
    fun k => PowerSeries.subst (PowerSeries.map (algebraMap O LL) (R.γ₀ g PowerSeries.X)) (a k) := by
  funext k
  simp [_root_.GlobalTheory.HWL.Cmp.γL, _root_.Formalism.BasicNotions.letγ, PowerSeries.coe_substAlgHom]

open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
    {Γ : _root_.GlobalTheory.HWL.WGam PD LL O v n s} in
theorem _root_.GlobalTheory.HWL.Cmp.φL_apply (L : Type) [CommRing L] (n p : ℕ) (a : _root_.Formalism.BasicNotions.LetA L n) : _root_.GlobalTheory.HWL.Cmp.φL L n p a =
    fun k => PowerSeries.subst ((1 + PowerSeries.X) ^ p - 1 : PowerSeries L) (a (k - 1)) := by
  funext k
  simp [_root_.GlobalTheory.HWL.Cmp.φL, _root_.Formalism.BasicNotions.letφ, PowerSeries.coe_substAlgHom]

open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
    {Γ : _root_.GlobalTheory.HWL.WGam PD LL O v n s} in

theorem _root_.GlobalTheory.HWL.Cmp.ringHom_ext_of_X {O L : Type} [CommRing O] [CommRing L] (f g : PowerSeries O →+* PowerSeries L)
    (hC : ∀ c, f (PowerSeries.C c) = g (PowerSeries.C c)) (hX : f PowerSeries.X = g PowerSeries.X)
    (h0 : PowerSeries.constantCoeff (f PowerSeries.X) = 0) (a : PowerSeries O) : f a = g a := by
  have hpoly : ∀ q : Polynomial O, f (q : PowerSeries O) = g (q : PowerSeries O) := by
    intro q
    induction q using Polynomial.induction_on with
    | C c => simpa using hC c
    | add q r hq hr => simp only [Polynomial.coe_add, map_add, hq, hr]
    | monomial k c _ =>
      simp only [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X, map_mul,
        map_pow, hC, hX]
  obtain ⟨u, hu⟩ := PowerSeries.X_dvd_iff.2 h0
  have hg : g PowerSeries.X = PowerSeries.X * u := hX ▸ hu
  ext N
  obtain ⟨b, hb⟩ : PowerSeries.X ^ (N + 1) ∣ a - (PowerSeries.trunc (N + 1) a : PowerSeries O) := by
    refine PowerSeries.X_pow_dvd_iff.2 fun m hm => ?_
    simp [PowerSeries.coeff_trunc, hm]
  have ha : a = (PowerSeries.trunc (N + 1) a : PowerSeries O) + PowerSeries.X ^ (N + 1) * b := by
    rw [← hb]; ring
  have hdiff : f a - g a = PowerSeries.X ^ (N + 1) * (u ^ (N + 1) * (f b - g b)) := by
    rw [ha, map_add, map_add, hpoly, map_mul, map_mul, map_pow, map_pow, hu, hg]
    ring
  rw [← sub_eq_zero, ← map_sub, hdiff, PowerSeries.coeff_X_pow_mul']
  simp

open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
    {Γ : _root_.GlobalTheory.HWL.WGam PD LL O v n s} in
theorem _root_.GlobalTheory.HWL.Cmp.map_algHom_eq (f : PowerSeries O →ₐ[O] PowerSeries O) {y : PowerSeries LL} (hy : PowerSeries.HasSubst y)
    (h0 : PowerSeries.constantCoeff y = 0) (hX : PowerSeries.map (algebraMap O LL) (f PowerSeries.X) = y)
    (a : PowerSeries O) : PowerSeries.map (algebraMap O LL) (f a) =
      PowerSeries.substAlgHom hy (PowerSeries.map (algebraMap O LL) a) := by
  refine _root_.GlobalTheory.HWL.Cmp.ringHom_ext_of_X ((PowerSeries.map (algebraMap O LL)).comp f.toRingHom)
    ((PowerSeries.substAlgHom hy).toRingHom.comp (PowerSeries.map (algebraMap O LL))) (fun c => ?_) ?_ ?_ a
  · have hfc : f (PowerSeries.C c) = PowerSeries.C c := f.commutes c
    simp [hfc, PowerSeries.coe_substAlgHom]
    rfl
  · simp [hX, PowerSeries.coe_substAlgHom, PowerSeries.subst_X hy]
  · simp [hX, h0]

open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
    {Γ : _root_.GlobalTheory.HWL.WGam PD LL O v n s} in
private lemma constantCoeff_map_gammaAction_X_eq_zero (R : _root_.GlobalTheory.HWL.WSer Γ) (g : Γ.Gam) :
    PowerSeries.constantCoeff (PowerSeries.map (algebraMap O LL) (R.γ₀ g PowerSeries.X)) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, (R.γ₀_X g).1, map_zero]

open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
    {Γ : _root_.GlobalTheory.HWL.WGam PD LL O v n s} in
theorem _root_.GlobalTheory.HWL.Cmp.toL_γ (R : _root_.GlobalTheory.HWL.WSer Γ) (g : Γ.Gam) (a : _root_.Formalism.BasicNotions.LetA O n) :
    _root_.GlobalTheory.HWL.Cmp.toL O LL n (_root_.Formalism.BasicNotions.letγ (R.γ₀ g) a) = _root_.GlobalTheory.HWL.Cmp.γL R g (_root_.GlobalTheory.HWL.Cmp.toL O LL n a) := by
  rw [_root_.GlobalTheory.HWL.Cmp.γL_apply]
  funext k
  have := _root_.GlobalTheory.HWL.Cmp.map_algHom_eq (R.γ₀ g) (_root_.GlobalTheory.HWL.Cmp.hasSubst_γ R g)
    (constantCoeff_map_gammaAction_X_eq_zero R g) rfl (a k)
  rw [PowerSeries.coe_substAlgHom] at this
  simpa [_root_.GlobalTheory.HWL.Cmp.toL, _root_.Formalism.BasicNotions.letγ] using this

open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
    {Γ : _root_.GlobalTheory.HWL.WGam PD LL O v n s} in
theorem _root_.GlobalTheory.HWL.Cmp.toL_φ (R : _root_.GlobalTheory.HWL.WSer Γ) (a : _root_.Formalism.BasicNotions.LetA O n) :
    _root_.GlobalTheory.HWL.Cmp.toL O LL n (_root_.Formalism.BasicNotions.letφ R.φ₀ a) = _root_.GlobalTheory.HWL.Cmp.φL LL n PD.p (_root_.GlobalTheory.HWL.Cmp.toL O LL n a) := by
  rw [_root_.GlobalTheory.HWL.Cmp.φL_apply]
  funext k
  have hX : PowerSeries.map (algebraMap O LL) (R.φ₀ PowerSeries.X) =
      ((1 + PowerSeries.X) ^ PD.p - 1 : PowerSeries LL) := by
    rw [R.φ₀_X, R.q₀_def]
    simp
  have := _root_.GlobalTheory.HWL.Cmp.map_algHom_eq R.φ₀
    (_root_.GlobalTheory.HWL.Cmp.hasSubst_φ LL PD.p) (by simp) hX (a (k - 1))
  rw [PowerSeries.coe_substAlgHom] at this
  simpa [_root_.GlobalTheory.HWL.Cmp.toL, _root_.Formalism.BasicNotions.letφ] using this

structure Disc (R : WSer Γ) (b₀ : LetA O n →+* LL ⊗[Qp] B) (tS zS : BdR) where
  C : Subalgebra LL (LetA LL n)
  toL_mem : ∀ a, toL O LL n a ∈ C
  cst_mem : ∀ c : ZMod n → LL, cst c ∈ C
  γ_mem : ∀ g, ∀ a ∈ C, γL R g a ∈ C
  φ_mem : ∀ a ∈ C, φL LL n PD.p a ∈ C
  t : ↥C
  t_zero : ∀ i, PowerSeries.constantCoeff ((t : LetA LL n) i) = 0
  J : ↥C →ₐ[LL] LL ⊗[Qp] B
  J_toL : ∀ a, J ⟨toL O LL n a, toL_mem a⟩ = b₀ a
  J_φ : ∀ a : ↥C, J ⟨φL LL n PD.p a, φ_mem a a.2⟩ = Algebra.TensorProduct.map (AlgHom.id Qp LL) PD.φ (J a)
  J_γ : ∀ (g : G) (a : ↥C), J ⟨γL R (Γ.resΓ g) a, γ_mem _ a a.2⟩ =
    Algebra.TensorProduct.map (AlgHom.id Qp LL) ((PD.actB g).toAlgHom.restrictScalars Qp) (J a)
  tb : B
  tb_unit : IsUnit tb
  periodDiscJ_tateElement : J t = (1 : LL) ⊗ₜ[Qp] tb
  ι_tb : PD.ι tb = tS
  tS_mem : tS ∈ PD.Fil 1
  π_unit : IsUnit (b₀ letπ)
  letter : ∀ (i : ZMod n) (c : K₀),
    ((1 : LL) ⊗ₜ[Qp] algebraMap K₀ B c) * b₀ (letE i) = Γ.emb i c • b₀ (letE i)
  ex : ZMod n → LL → (↥C →ₐ[LL] PowerSeries LL)
  ex_toL : ∀ i ζ a, ex i ζ ⟨toL O LL n a, toL_mem a⟩ = R.lev i ζ a
  ex_cst : ∀ i ζ c, ex i ζ ⟨cst c, cst_mem c⟩ = PowerSeries.C (c i)
  numEx_t_eq_fifteen : ∀ i ζ, ex i ζ t = PowerSeries.X
  ex_γ : ∀ (g : Γ.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
    IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (Γ.χΓ g : O) - (a : LL)) →
    ζ' = ζ ^ a → ∀ f : ↥C,
    ex i ζ ⟨γL R g f, γ_mem g f f.2⟩ = PowerSeries.rescale (algebraMap O LL (Γ.χΓ g : O)) (ex i ζ' f)
  ex_φ : ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ f : ↥C,
    ex i ζ ⟨φL LL n PD.p f, φ_mem f f.2⟩ = PowerSeries.rescale (PD.p : LL) (ex (i - 1) (ζ ^ PD.p) f)
  ex_one : ∀ (i : ZMod n) (f : ↥C) (w : ℕ), PowerSeries.X ^ w ∣ (f : LetA LL n) i →
    PowerSeries.X ^ w ∣ ex i 1 f
  taylor : ∀ (i : ZMod n) (ζ : LL) (ι : LL →ₐ[Qp] BdR), (∀ c : K₀, ι (Γ.emb i c) = algebraMap K₀ BdR c) →
    ι ζ = zS → ∀ (f : ↥C) (m : ℕ),
    Algebra.TensorProduct.productMap ι (PD.ι.restrictScalars Qp) (J f) -
      ∑ k ∈ Finset.range m, ι (PowerSeries.coeff k (ex i ζ f)) * tS ^ k ∈ PD.Fil (m : ℤ)

variable {R : WSer Γ} {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {I : WIo R (O ⊗[Zl] Ai) RW inclR φR gR πA} {E : WEt I} {zl : PowerSeries Zl →+* LetA O n}

structure IsPer (Mo : WN E zl) (b₀ : LetA O n →+* LL ⊗[Qp] B) (ιdR : Ai →+* BdR) (p1 : Ai)
    (βdR : ∀ T : LocLat G Qp LL O, TW (O ⊗[Zl] Ai) T →+ T.V ⊗[Qp] BdR)
    (bT : ∀ T : LocLat G Qp LL O, ↥(Mo.N T) →+ T.V ⊗[Qp] B) : Prop where
  tmul : ∀ (T : LocLat G Qp LL O) (a : O) (w : Ai) (t : ↥T.L.T),
    βdR T ((a ⊗ₜ[Zl] w) ⊗ₜ[O] t) = ((a • t : ↥T.L.T) : T.V) ⊗ₜ[Qp] ιdR w
  smul : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (a : LetA O n) (x : ↥(Mo.N T)),
    bT T (a • x) = actS T.V B (b₀ a) (bT T x)
  gal : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : G) (x : ↥(Mo.N T)),
    bT T ⟨E.γD T (Γ.resΓ g) (x : E.DD T), Mo.N_Γ T _ x x.2⟩ = actVB PD T.ρ g (bT T x)
  frob : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (x : ↥(Mo.N T)) (m : ℕ)
    (hx : R.Q ^ m • E.φD T (x : E.DD T) ∈ Mo.N T),
    bT T ⟨R.Q ^ m • E.φD T (x : E.DD T), hx⟩ =
      actS T.V B (b₀ (R.Q ^ m)) (φVB PD (LL := LL) (V := T.V) (bT T x))
  nat : ∀ {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L), IsCrys PD T.ρ → IsCrys PD T'.ρ →
    ∀ (x : ↥(Mo.N T)) (hx : E.map f (x : E.DD T) ∈ Mo.N T'),
    bT T' ⟨E.map f (x : E.DD T), hx⟩ = AlgebraTensorModule.map f.f (LinearMap.id : B →ₗ[Qp] B) (bT T x)
  dR : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (x : ↥(Mo.N T)) (k : ℕ) (y : TW (O ⊗[Zl] Ai) T),
    TWincl inclR T y = (inclR ((1 : O) ⊗ₜ[Zl] p1)) ^ k • E.jD T (x : E.DD T) →
    βdR T y = mulVR T (ιdR p1 ^ k) (ιV PD (LL := LL) (V := T.V) (bT T x))

end GlobalTheory.HWL.Cmp
