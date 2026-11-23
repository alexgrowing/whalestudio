import Formalism.FormalDegreeBessel.FormalDegreeRatio.WRWeyl
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RuleGD
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RuleSS
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RuleInv
import Formalism.FormalDegreeBessel.FinalIO
import Formalism.FormalDegreeBessel.FinalBF
import Formalism.SharpRestriction.CuspSpanNormBounds.ChoiceOfModulusAndDiscriminant
import Formalism.SharpRestriction.CuspSpanNormBounds.RadialRules

open scoped ContDiff Topology
open Filter

noncomputable section

namespace Formalism.MainNotions.LevelRaisingOperators

open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WirtingerDerivatives Formalism.MainNotions.S.LevR

variable {m : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def SmU (U : Set (Fin m → ℂ)) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] :
    Submodule ℂ ((Fin m → ℂ) → E) where
  carrier := {f | ContDiffOn ℝ ∞ f U ∧ ∀ x, x ∉ U → f x = 0}
  zero_mem' := ⟨contDiffOn_const, fun _ _ => rfl⟩
  add_mem' := fun {f g} hf hg => ⟨hf.1.add hg.1, fun x hx => by simp [hf.2 x hx, hg.2 x hx]⟩
  smul_mem' := fun a {f} hf => ⟨hf.1.const_smul a, fun x hx => by simp [hf.2 x hx]⟩

structure GoodOp (U : Set (Fin m → ℂ)) (O : Op m E) : Prop where
  smooth : ∀ f, ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ (O f) U
  add : ∀ f g, ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ g U → ∀ x ∈ U, O (f + g) x = O f x + O g x
  smul : ∀ (a : ℂ) f, ContDiffOn ℝ ∞ f U → ∀ x ∈ U, O (a • f) x = a • O f x
  loc : ∀ f g, (∀ x ∈ U, f x = g x) → ∀ x ∈ U, O f x = O g x

open Classical in

def toEnd (U : Set (Fin m → ℂ)) (O : Op m E) : Module.End ℂ (SmU U E) :=
  if h : GoodOp U O then
    { toFun := fun φ => ⟨U.indicator (O φ.1),
        (h.smooth _ φ.2.1).congr (fun x hx => Set.indicator_of_mem hx _),
        fun x hx => Set.indicator_of_notMem hx _⟩
      map_add' := fun φ ψ => by
        apply Subtype.ext; funext x
        by_cases hx : x ∈ U
        · simp [Set.indicator_of_mem hx, h.add _ _ φ.2.1 ψ.2.1 x hx]
        · simp [Set.indicator_of_notMem hx]
      map_smul' := fun a φ => by
        apply Subtype.ext; funext x
        by_cases hx : x ∈ U
        · simp [Set.indicator_of_mem hx, h.smul a _ φ.2.1 x hx]
        · simp [Set.indicator_of_notMem hx] }
  else 0

variable {U : Set (Fin m → ℂ)}

theorem toEnd_apply {O : Op m E} (h : GoodOp U O) (φ : SmU U E) {x : Fin m → ℂ} (hx : x ∈ U) :
    (toEnd U O φ).1 x = O φ.1 x := by
  simp [toEnd, h, Set.indicator_of_mem hx]

theorem toEnd_apply' {O : Op m E} (h : GoodOp U O) (φ : SmU U E) (g : (Fin m → ℂ) → E)
    (hg : ∀ x ∈ U, g x = φ.1 x) {x : Fin m → ℂ} (hx : x ∈ U) :
    (toEnd U O φ).1 x = O g x := by
  rw [toEnd_apply h φ hx]; exact (h.loc g φ.1 hg x hx).symm

theorem end_ext {a b : Module.End ℂ (SmU U E)} (h : ∀ φ : SmU U E, ∀ x ∈ U, (a φ).1 x = (b φ).1 x) :
    a = b := by
  apply LinearMap.ext; intro φ; apply Subtype.ext; funext x
  by_cases hx : x ∈ U
  · exact h φ x hx
  · rw [(a φ).2.2 x hx, (b φ).2.2 x hx]

theorem contDiffOn_clm_apply' {e : (Fin m → ℂ) → E →L[ℂ] E} {f : (Fin m → ℂ) → E}
    (he : ContDiffOn ℝ ∞ e U) (hf : ContDiffOn ℝ ∞ f U) : ContDiffOn ℝ ∞ (fun x => e x (f x)) U := by
  have h1 : ContDiffOn ℝ ∞ (fun x => (e x).restrictScalars ℝ) U :=
    ((ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ).contDiff).comp_contDiffOn he
  exact h1.clm_apply hf

def opD (u w : Fin m → ℂ) (s : ℂ) : Op m E := fun φ x => Wc u w s (fderiv ℝ φ x)

theorem good_mulF {f : (Fin m → ℂ) → ℂ} (hf : ContDiffOn ℝ ∞ f U) : GoodOp U (mulF (E := E) f) where
  smooth := fun g hg => hf.smul hg
  add := fun g g' _ _ x _ => by simp [mulF]
  smul := fun a g _ x _ => by simp only [mulF, Pi.smul_apply]; exact smul_comm _ _ _
  loc := fun g g' h x hx => by simp [mulF, h x hx]

theorem good_mulE {e : (Fin m → ℂ) → E →L[ℂ] E} (he : ContDiffOn ℝ ∞ e U) : GoodOp U (mulE e) where
  smooth := fun g hg => contDiffOn_clm_apply' he hg
  add := fun g g' _ _ x _ => by simp [mulE]
  smul := fun a g _ x _ => by simp [mulE]
  loc := fun g g' h x hx => by simp [mulE, h x hx]

theorem cda (hU : IsOpen U) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : (Fin m → ℂ) → F}
    (hf : ContDiffOn ℝ ∞ f U) {x : Fin m → ℂ} (hx : x ∈ U) : ContDiffAt ℝ ∞ f x :=
  hf.contDiffAt (hU.mem_nhds hx)

theorem Wc_smul_const (u w : Fin m → ℂ) (s a : ℂ) (T : (Fin m → ℂ) →L[ℝ] E) :
    Wc u w s (a • T) = a • Wc u w s T := by
  simp only [Wc_apply, _root_.smul_apply]
  module

theorem good_opD (hU : IsOpen U) (u w : Fin m → ℂ) (s : ℂ) : GoodOp U (opD (E := E) u w s) where
  smooth := fun g hg x hx => (contDiffAt_Wc (cda hU hg hx) u w s).contDiffWithinAt
  add := fun g g' hg hg' x hx => by
    simp only [opD]
    rw [fderiv_add (diff_of_reg (cda hU hg hx)) (diff_of_reg (cda hU hg' hx)), map_add]
  smul := fun a g hg x hx => by
    simp only [opD]
    rw [fderiv_const_smul (diff_of_reg (cda hU hg hx)) a, Wc_smul_const]
  loc := fun g g' h x hx => by
    simp only [opD]
    have : g =ᶠ[𝓝 x] g' := Filter.eventuallyEq_of_mem (hU.mem_nhds hx) h
    rw [this.fderiv_eq]

def fn (U : Set (Fin m → ℂ)) (f : (Fin m → ℂ) → ℂ) : Module.End ℂ (SmU U E) := toEnd U (mulF f)

def fe (U : Set (Fin m → ℂ)) (e : (Fin m → ℂ) → E →L[ℂ] E) : Module.End ℂ (SmU U E) := toEnd U (mulE e)

def dd (U : Set (Fin m → ℂ)) (u w : Fin m → ℂ) (s : ℂ) : Module.End ℂ (SmU U E) := toEnd U (opD u w s)

theorem fn_apply {f : (Fin m → ℂ) → ℂ} (hf : ContDiffOn ℝ ∞ f U) (φ : SmU U E) {x : Fin m → ℂ}
    (hx : x ∈ U) : (fn U f φ).1 x = f x • φ.1 x := toEnd_apply (good_mulF hf) φ hx

theorem fe_apply {e : (Fin m → ℂ) → E →L[ℂ] E} (he : ContDiffOn ℝ ∞ e U) (φ : SmU U E)
    {x : Fin m → ℂ} (hx : x ∈ U) : (fe U e φ).1 x = e x (φ.1 x) := toEnd_apply (good_mulE he) φ hx

theorem dd_apply (hU : IsOpen U) (u w : Fin m → ℂ) (s : ℂ) (φ : SmU U E) {x : Fin m → ℂ}
    (hx : x ∈ U) : (dd U u w s φ).1 x = Wc u w s (fderiv ℝ φ.1 x) := toEnd_apply (good_opD hU u w s) φ hx

theorem fderiv_congr_on (hU : IsOpen U) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g g' : (Fin m → ℂ) → F} (h : ∀ x ∈ U, g x = g' x) {x : Fin m → ℂ} (hx : x ∈ U) :
    fderiv ℝ g x = fderiv ℝ g' x :=
  (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) h).fderiv_eq

theorem fderiv_fn (hU : IsOpen U) {f : (Fin m → ℂ) → ℂ} (hf : ContDiffOn ℝ ∞ f U) (φ : SmU U E)
    {x : Fin m → ℂ} (hx : x ∈ U) : fderiv ℝ (fn U f φ).1 x = fderiv ℝ (fun y => f y • φ.1 y) x :=
  fderiv_congr_on hU (fun _ hy => fn_apply hf φ hy) hx

theorem fderiv_fe (hU : IsOpen U) {e : (Fin m → ℂ) → E →L[ℂ] E} (he : ContDiffOn ℝ ∞ e U) (φ : SmU U E)
    {x : Fin m → ℂ} (hx : x ∈ U) : fderiv ℝ (fe U e φ).1 x = fderiv ℝ (fun y => e y (φ.1 y)) x :=
  fderiv_congr_on hU (fun _ hy => fe_apply he φ hy) hx

theorem fderiv_dd (hU : IsOpen U) (u w : Fin m → ℂ) (s : ℂ) (φ : SmU U E)
    {x : Fin m → ℂ} (hx : x ∈ U) :
    fderiv ℝ (dd U u w s φ).1 x = fderiv ℝ (fun y => Wc u w s (fderiv ℝ φ.1 y)) x :=
  fderiv_congr_on hU (fun _ hy => dd_apply hU u w s φ hy) hx

theorem Wc_clm {e : (Fin m → ℂ) → E →L[ℂ] E} {h : (Fin m → ℂ) → E} {x : Fin m → ℂ}
    (he : DifferentiableAt ℝ e x) (hh : DifferentiableAt ℝ h x) (u w : Fin m → ℂ) (s : ℂ) :
    Wc u w s (fderiv ℝ (fun y => e y (h y)) x) =
      (Wc u w s (fderiv ℝ e x)) (h x) + e x (Wc u w s (fderiv ℝ h x)) := by
  have h1 : HasFDerivAt (fun y => (e y).restrictScalars ℝ)
      ((ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ : (E →L[ℂ] E) →L[ℝ] (E →L[ℝ] E)).comp (fderiv ℝ e x)) x :=
    (ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ).hasFDerivAt.comp x he.hasFDerivAt
  have h2 := h1.clm_apply hh.hasFDerivAt
  have h3 : fderiv ℝ (fun y => e y (h y)) x = _ := h2.fderiv
  rw [h3]
  have e1 : ∀ v, (ContinuousLinearMap.restrictScalars ℝ (e x) ∘SL fderiv ℝ h x +
      ((ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ : (E →L[ℂ] E) →L[ℝ] (E →L[ℝ] E)) ∘SL fderiv ℝ e x).flip (h x)) v =
      e x (fderiv ℝ h x v) + (fderiv ℝ e x v) (h x) := fun v => rfl
  rw [Wc_apply, Wc_apply, Wc_apply, e1, e1]
  simp only [_root_.add_apply, _root_.smul_apply, map_add, map_smul]
  module

theorem fn_comm {f g : (Fin m → ℂ) → ℂ} (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) :
    fn (E := E) U f * fn U g = fn U g * fn U f := by
  apply end_ext; intro φ x hx
  simp only [Module.End.mul_apply, fn_apply hf _ hx, fn_apply hg _ hx]
  exact smul_comm _ _ _

theorem fn_mul {f g : (Fin m → ℂ) → ℂ} (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) :
    fn (E := E) U f * fn U g = fn U (fun x => f x * g x) := by
  apply end_ext; intro φ x hx
  simp only [Module.End.mul_apply, fn_apply hf _ hx, fn_apply hg _ hx, fn_apply (hf.mul hg) _ hx, mul_smul]

theorem fn_mul_one {f g : (Fin m → ℂ) → ℂ} (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (h : ∀ x ∈ U, f x * g x = 1) : fn (E := E) U f * fn U g = 1 := by
  apply end_ext; intro φ x hx
  simp only [Module.End.mul_apply, fn_apply hf _ hx, fn_apply hg _ hx, smul_smul, h x hx, one_smul,
    Module.End.one_apply]

theorem fn_fe_comm {f : (Fin m → ℂ) → ℂ} {e : (Fin m → ℂ) → E →L[ℂ] E} (hf : ContDiffOn ℝ ∞ f U)
    (he : ContDiffOn ℝ ∞ e U) : fn U f * fe U e = fe U e * fn U f := by
  apply end_ext; intro φ x hx
  simp only [Module.End.mul_apply, fn_apply hf _ hx, fe_apply he _ hx, map_smul]

theorem contDiffOn_Wc (hU : IsOpen U) {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : (Fin m → ℂ) → F} (hf : ContDiffOn ℝ ∞ f U) (u w : Fin m → ℂ) (s : ℂ) :
    ContDiffOn ℝ ∞ (fun y => Wc u w s (fderiv ℝ f y)) U :=
  fun _ hx => (contDiffAt_Wc (cda hU hf hx) u w s).contDiffWithinAt

theorem dd_fn (hU : IsOpen U) {f : (Fin m → ℂ) → ℂ} (hf : ContDiffOn ℝ ∞ f U) (u w : Fin m → ℂ) (s : ℂ) :
    dd (E := E) U u w s * fn U f = fn U f * dd U u w s + fn U (fun y => Wc u w s (fderiv ℝ f y)) := by
  apply end_ext; intro φ x hx
  simp only [Module.End.mul_apply, LinearMap.add_apply, Submodule.coe_add, Pi.add_apply,
    fn_apply hf _ hx, fn_apply (contDiffOn_Wc hU hf u w s) _ hx, dd_apply hU _ _ _ _ hx, fderiv_fn hU hf _ hx]
  rw [Wc_smul (diff_of_reg (cda hU hf hx)) (diff_of_reg (cda hU φ.2.1 hx)), add_comm]

theorem dd_fe (hU : IsOpen U) {e : (Fin m → ℂ) → E →L[ℂ] E} (he : ContDiffOn ℝ ∞ e U)
    (u w : Fin m → ℂ) (s : ℂ) :
    dd U u w s * fe U e = fe U e * dd U u w s + fe U (fun y => Wc u w s (fderiv ℝ e y)) := by
  apply end_ext; intro φ x hx
  simp only [Module.End.mul_apply, LinearMap.add_apply, Submodule.coe_add, Pi.add_apply,
    fe_apply he _ hx, fe_apply (contDiffOn_Wc hU he u w s) _ hx, dd_apply hU _ _ _ _ hx, fderiv_fe hU he _ hx]
  rw [Wc_clm (diff_of_reg (cda hU he hx)) (diff_of_reg (cda hU φ.2.1 hx)), add_comm]

theorem dd_comm (hU : IsOpen U) (u w : Fin m → ℂ) (s : ℂ) (u' w' : Fin m → ℂ) (s' : ℂ) :
    dd (E := E) U u w s * dd U u' w' s' = dd U u' w' s' * dd U u w s := by
  apply end_ext; intro φ x hx
  simp only [Module.End.mul_apply, dd_apply hU _ _ _ _ hx, fderiv_dd hU _ _ _ _ hx]
  exact Wc_comm (cda hU φ.2.1 hx) u w s u' w' s'

theorem fn_congr {f g : (Fin m → ℂ) → ℂ} (hf : ContDiffOn ℝ ∞ f U) (h : ∀ x ∈ U, f x = g x) :
    fn (E := E) U f = fn U g := by
  have hg : ContDiffOn ℝ ∞ g U := hf.congr (fun x hx => (h x hx).symm)
  apply end_ext; intro φ x hx
  rw [fn_apply hf _ hx, fn_apply hg _ hx, h x hx]

theorem fn_zero : fn (E := E) U (fun _ => 0) = 0 := by
  apply end_ext; intro φ x hx
  rw [fn_apply contDiffOn_const _ hx]; simp

theorem fn_const (a : ℂ) : fn (E := E) U (fun _ => a) = algebraMap ℂ _ a := by
  apply end_ext; intro φ x hx
  rw [fn_apply contDiffOn_const _ hx]; simp [Module.algebraMap_end_apply]

theorem fe_zero_of {e : (Fin m → ℂ) → E →L[ℂ] E} (he : ContDiffOn ℝ ∞ e U) (h : ∀ x ∈ U, e x = 0) :
    fe U e = 0 := by
  apply end_ext; intro φ x hx
  rw [fe_apply he _ hx, h x hx]; simp

end Formalism.MainNotions.LevelRaisingOperators

namespace Formalism.MainNotions.LevelRaisingOperators

open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WirtingerDerivatives Formalism.MainNotions.S.LevR

section RingLemmas
variable {A : Type} [Ring A] [Algebra ℂ A]

theorem der_mul {d f g k k' : A} (h1 : d * f = f * d + k) (h2 : d * g = g * d + k') :
    d * (f * g) = (f * g) * d + (k * g + f * k') := by
  rw [← mul_assoc, h1, add_mul, mul_assoc, h2]; noncomm_ring

theorem der_inv {d f fi k : A} (h : d * f = f * d + k) (h1 : f * fi = 1) (h2 : fi * f = 1) :
    d * fi = fi * d - fi * k * fi := by
  have e : f * d = d * f - k := by rw [h]; abel
  calc d * fi = (fi * f) * d * fi := by rw [h2, one_mul]
    _ = fi * (f * d) * fi := by noncomm_ring
    _ = fi * d * (f * fi) - fi * k * fi := by rw [e]; noncomm_ring
    _ = fi * d - fi * k * fi := by rw [h1, mul_one]

theorem der_GG {d z zb a b : A} (t : ℂ) (h1 : d * z = z * d + a) (h2 : d * zb = zb * d + b) :
    d * (z * zb - algebraMap ℂ A t) = (z * zb - algebraMap ℂ A t) * d + (a * zb + z * b) := by
  rw [mul_sub, sub_mul, der_mul h1 h2, Algebra.commutes t d]; abel

theorem der_left {x d f k : A} (hx : x * f = f * x) (h : d * f = f * d + k) :
    (x * d) * f = f * (x * d) + x * k := by
  rw [mul_assoc, h, mul_add, ← mul_assoc, hx, mul_assoc]

end RingLemmas

structure Setup (r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] where
  U : Set (Fin (r + 1) → ℂ)
  T : ℝ
  T' : ℝ
  h : (Fin (r + 1) → ℂ) → E →L[ℂ] E
  hs : (Fin (r + 1) → ℂ) → E →L[ℂ] E
  isOpen : IsOpen U
  sub : ∀ x ∈ U, x ∈ OmX (r + 1)
  pos : ∀ x ∈ U, T * T' < Complex.normSq (zOf x)
  h_sm : ContDiffOn ℝ ∞ h U
  hs_sm : ContDiffOn ℝ ∞ hs U
  h_c : ∀ x ∈ U, ∀ (a : Fin r) (v : ℂ), fderiv ℝ h x (Pi.single a.castSucc v) = 0
  hs_c : ∀ x ∈ U, ∀ (a : Fin r) (v : ℂ), fderiv ℝ hs x (Pi.single a.castSucc v) = 0

namespace Setup

variable {r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (S : Setup r E)

abbrev Rg := Module.End ℂ (SmU S.U E)

def X (k : Fin (r + 1)) (i : Fin 6) : S.Rg := fn S.U (coef k i)

def dW (k : Fin (r + 1)) : S.Rg := dd S.U (Pi.single k 1) (Pi.single k Complex.I) (-Complex.I)

def dWb (k : Fin (r + 1)) : S.Rg := dd S.U (Pi.single k 1) (Pi.single k Complex.I) Complex.I

def P (k : Fin (r + 1)) : S.Rg := S.X k 1 * S.dW k

def Pb (k : Fin (r + 1)) : S.Rg := S.X k 4 * S.dWb k
def gG : S.Rg := fn S.U (GG S.T S.T')
def gGi : S.Rg := fn S.U (fun x => (GG S.T S.T' x)⁻¹)
def nab : S.Rg := S.dW (Fin.last r) + fe S.U S.h
def nabs : S.Rg := -S.dWb (Fin.last r) + fe S.U S.hs

theorem hc (k : Fin (r + 1)) (i : Fin 6) : ContDiffOn ℝ ∞ (coef k i) S.U :=
  fun x hx => (coef_contDiffAt (S.sub x hx) i).contDiffWithinAt

theorem GG_eq (x : Fin (r + 1) → ℂ) :
    GG S.T S.T' x = coef (Fin.last r) 1 x * coef (Fin.last r) 4 x - ((S.T * S.T' : ℝ) : ℂ) := by
  simp only [GG, coef, zOf]
  rw [Complex.ofReal_sub, ← Complex.mul_conj]; rfl

theorem GG_ne {x : Fin (r + 1) → ℂ} (hx : x ∈ S.U) : GG S.T S.T' x ≠ 0 := by
  simp only [GG]
  have := S.pos x hx
  exact_mod_cast (sub_pos.2 this).ne'

theorem hGG : ContDiffOn ℝ ∞ (GG S.T S.T') S.U := by
  have : ContDiffOn ℝ ∞ (fun x => coef (Fin.last r) 1 x * coef (Fin.last r) 4 x - ((S.T * S.T' : ℝ) : ℂ)) S.U :=
    ((S.hc _ 1).mul (S.hc _ 4)).sub contDiffOn_const
  exact this.congr (fun x _ => S.GG_eq x)

theorem hGGi : ContDiffOn ℝ ∞ (fun x => (GG S.T S.T' x)⁻¹) S.U :=
  S.hGG.inv (fun _ hx => S.GG_ne hx)

theorem X_comm (k k' : Fin (r + 1)) (i i' : Fin 6) : S.X k i * S.X k' i' = S.X k' i' * S.X k i :=
  fn_comm (S.hc k i) (S.hc k' i')

theorem gG_def : S.gG = S.X (Fin.last r) 1 * S.X (Fin.last r) 4 - algebraMap ℂ S.Rg ((S.T * S.T' : ℝ) : ℂ) := by
  apply end_ext; intro φ x hx
  simp only [gG, X, LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, Pi.sub_apply,
    fn_apply S.hGG _ hx, fn_apply (S.hc _ _) _ hx, Module.algebraMap_end_apply, Submodule.coe_smul,
    Pi.smul_apply, S.GG_eq, sub_smul, mul_smul]

theorem dW_X (j k : Fin (r + 1)) (i : Fin 6) :
    S.dW j * S.X k i = S.X k i * S.dW j +
      fn S.U (fun y => if (i : ℕ) < 3 ∧ j = k then ck k i y else 0) := by
  rw [dW, X, dd_fn S.isOpen (S.hc k i)]
  congr 1
  apply fn_congr (contDiffOn_Wc S.isOpen (S.hc k i) _ _ _)
  intro x hx
  rw [← wirt_eq, wirt_coef (S.sub x hx)]

theorem dWb_X (j k : Fin (r + 1)) (i : Fin 6) :
    S.dWb j * S.X k i = S.X k i * S.dWb j +
      fn S.U (fun y => if ¬ (i : ℕ) < 3 ∧ j = k then ck k i y else 0) := by
  rw [dWb, X, dd_fn S.isOpen (S.hc k i)]
  congr 1
  apply fn_congr (contDiffOn_Wc S.isOpen (S.hc k i) _ _ _)
  intro x hx
  rw [← wirtBar_eq, wirtBar_coef (S.sub x hx)]

theorem fn_one' : fn (E := E) S.U (fun _ => 1) = 1 := by
  rw [fn_const]; simp

theorem holo_deriv_coord_commutator (j k : Fin (r + 1)) : S.dW j * S.X k 1 = S.X k 1 * S.dW j + (if j = k then 1 else 0) := by
  rw [dW_X]; congr 1
  by_cases h : j = k
  · simp [h, ck, fn_one']
  · simp [h, fn_zero]

theorem holo_deriv_commute_conj_coord (j k : Fin (r + 1)) : S.dW j * S.X k 4 = S.X k 4 * S.dW j := by
  rw [dW_X]; simp [fn_zero]

theorem antiholo_deriv_commute_coord (j k : Fin (r + 1)) : S.dWb j * S.X k 1 = S.X k 1 * S.dWb j := by
  rw [dWb_X]; simp [fn_zero]

theorem antiholo_deriv_conj_coord_commutator (j k : Fin (r + 1)) : S.dWb j * S.X k 4 = S.X k 4 * S.dWb j + (if j = k then 1 else 0) := by
  rw [dWb_X]; congr 1
  by_cases h : j = k
  · simp [h, ck, fn_one']
  · simp [h, fn_zero]

theorem coord_mul_inv_coord_eq_one (k : Fin (r + 1)) : S.X k 1 * S.X k 2 = 1 :=
  fn_mul_one (S.hc k 1) (S.hc k 2) (fun x hx => mul_inv_cancel₀ (S.sub x hx k))
theorem inv_coord_mul_coord_eq_one (k : Fin (r + 1)) : S.X k 2 * S.X k 1 = 1 := by rw [X_comm, coord_mul_inv_coord_eq_one]
theorem conj_coord_mul_conj_inv_eq_one (k : Fin (r + 1)) : S.X k 4 * S.X k 5 = 1 :=
  fn_mul_one (S.hc k 4) (S.hc k 5) (fun x hx => mul_inv_cancel₀ (by simpa [coef] using S.sub x hx k))
theorem conj_inv_mul_conj_coord_eq_one (k : Fin (r + 1)) : S.X k 5 * S.X k 4 = 1 := by rw [X_comm, conj_coord_mul_conj_inv_eq_one]

theorem holo_deriv_inv_coord_commutator (j k : Fin (r + 1)) :
    S.dW j * S.X k 2 = S.X k 2 * S.dW j - (if j = k then S.X k 2 * S.X k 2 else 0) := by
  rw [der_inv (S.holo_deriv_coord_commutator j k) (S.coord_mul_inv_coord_eq_one k) (S.inv_coord_mul_coord_eq_one k)]
  by_cases h : j = k <;> simp [h]

theorem holo_deriv_commute_conj_inv_coord (j k : Fin (r + 1)) : S.dW j * S.X k 5 = S.X k 5 * S.dW j := by
  have := der_inv (k := 0) (by simpa using S.holo_deriv_commute_conj_coord j k) (S.conj_coord_mul_conj_inv_eq_one k) (S.conj_inv_mul_conj_coord_eq_one k)
  simpa using this

theorem antiholo_deriv_commute_inv_coord (j k : Fin (r + 1)) : S.dWb j * S.X k 2 = S.X k 2 * S.dWb j := by
  have := der_inv (k := 0) (by simpa using S.antiholo_deriv_commute_coord j k) (S.coord_mul_inv_coord_eq_one k) (S.inv_coord_mul_coord_eq_one k)
  simpa using this

theorem antiholo_deriv_conj_inv_commutator (j k : Fin (r + 1)) :
    S.dWb j * S.X k 5 = S.X k 5 * S.dWb j - (if j = k then S.X k 5 * S.X k 5 else 0) := by
  rw [der_inv (S.antiholo_deriv_conj_coord_commutator j k) (S.conj_coord_mul_conj_inv_eq_one k) (S.conj_inv_mul_conj_coord_eq_one k)]
  by_cases h : j = k <;> simp [h]

theorem momentum_coord_commutator (j k : Fin (r + 1)) : S.P j * S.X k 1 = S.X k 1 * S.P j + (if j = k then S.X k 1 else 0) := by
  rw [P, der_left (S.X_comm _ _ _ _) (S.holo_deriv_coord_commutator j k)]
  by_cases h : j = k <;> simp [h]

theorem momentum_inv_coord_commutator (j k : Fin (r + 1)) : S.P j * S.X k 2 = S.X k 2 * S.P j - (if j = k then S.X k 2 else 0) := by
  have := S.holo_deriv_inv_coord_commutator j k
  rw [sub_eq_add_neg] at this
  rw [P, der_left (S.X_comm _ _ _ _) this]
  by_cases h : j = k
  · subst h; simp [← mul_assoc, S.coord_mul_inv_coord_eq_one, sub_eq_add_neg]
  · simp [h]

theorem momentum_commute_conj_coord (j k : Fin (r + 1)) : S.P j * S.X k 4 = S.X k 4 * S.P j := by
  have := der_left (k := 0) (S.X_comm j k 1 4) (by simpa using S.holo_deriv_commute_conj_coord j k)
  simpa [P] using this

theorem momentum_commute_conj_inv_coord (j k : Fin (r + 1)) : S.P j * S.X k 5 = S.X k 5 * S.P j := by
  have := der_left (k := 0) (S.X_comm j k 1 5) (by simpa using S.holo_deriv_commute_conj_inv_coord j k)
  simpa [P] using this

theorem conj_momentum_conj_coord_commutator (j k : Fin (r + 1)) : S.Pb j * S.X k 4 = S.X k 4 * S.Pb j + (if j = k then S.X k 4 else 0) := by
  rw [Pb, der_left (S.X_comm _ _ _ _) (S.antiholo_deriv_conj_coord_commutator j k)]
  by_cases h : j = k <;> simp [h]

theorem conj_momentum_conj_inv_commutator (j k : Fin (r + 1)) : S.Pb j * S.X k 5 = S.X k 5 * S.Pb j - (if j = k then S.X k 5 else 0) := by
  have := S.antiholo_deriv_conj_inv_commutator j k
  rw [sub_eq_add_neg] at this
  rw [Pb, der_left (S.X_comm _ _ _ _) this]
  by_cases h : j = k
  · subst h; simp [← mul_assoc, S.conj_coord_mul_conj_inv_eq_one, sub_eq_add_neg]
  · simp [h]

theorem conj_momentum_commute_coord (j k : Fin (r + 1)) : S.Pb j * S.X k 1 = S.X k 1 * S.Pb j := by
  have := der_left (k := 0) (S.X_comm j k 4 1) (by simpa using S.antiholo_deriv_commute_coord j k)
  simpa [Pb] using this

theorem conj_momentum_commute_inv_coord (j k : Fin (r + 1)) : S.Pb j * S.X k 2 = S.X k 2 * S.Pb j := by
  have := der_left (k := 0) (S.X_comm j k 4 2) (by simpa using S.antiholo_deriv_commute_inv_coord j k)
  simpa [Pb] using this

end Setup

end Formalism.MainNotions.LevelRaisingOperators

namespace Formalism.MainNotions.LevelRaisingOperators

open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WirtingerDerivatives Formalism.MainNotions.S.LevR

namespace Setup

variable {r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (S : Setup r E)

theorem nab_der {f : (Fin (r + 1) → ℂ) → ℂ} (hf : ContDiffOn ℝ ∞ f S.U) {k : S.Rg}
    (h : S.dW (Fin.last r) * fn S.U f = fn S.U f * S.dW (Fin.last r) + k) :
    S.nab * fn S.U f = fn S.U f * S.nab + k := by
  rw [nab, add_mul, h, ← fn_fe_comm hf S.h_sm, mul_add]; abel

theorem nabs_der {f : (Fin (r + 1) → ℂ) → ℂ} (hf : ContDiffOn ℝ ∞ f S.U) {k : S.Rg}
    (h : S.dWb (Fin.last r) * fn S.U f = fn S.U f * S.dWb (Fin.last r) + k) :
    S.nabs * fn S.U f = fn S.U f * S.nabs - k := by
  rw [nabs, add_mul, neg_mul, h, ← fn_fe_comm hf S.hs_sm, mul_add, mul_neg]; abel

theorem nab_X {k : Fin (r + 1)} {i : Fin 6} {K : S.Rg}
    (h : S.dW (Fin.last r) * S.X k i = S.X k i * S.dW (Fin.last r) + K) :
    S.nab * S.X k i = S.X k i * S.nab + K := S.nab_der (S.hc k i) h

theorem nabs_X {k : Fin (r + 1)} {i : Fin 6} {K : S.Rg}
    (h : S.dWb (Fin.last r) * S.X k i = S.X k i * S.dWb (Fin.last r) + K) :
    S.nabs * S.X k i = S.X k i * S.nabs - K := S.nabs_der (S.hc k i) h

theorem gG_gGi : S.gG * S.gGi = 1 :=
  fn_mul_one S.hGG S.hGGi (fun _ hx => mul_inv_cancel₀ (S.GG_ne hx))
theorem gGi_gG : S.gGi * S.gG = 1 :=
  fn_mul_one S.hGGi S.hGG (fun _ hx => inv_mul_cancel₀ (S.GG_ne hx))

theorem der_gG {d a b : S.Rg} (h1 : d * S.X (Fin.last r) 1 = S.X (Fin.last r) 1 * d + a)
    (h2 : d * S.X (Fin.last r) 4 = S.X (Fin.last r) 4 * d + b) :
    d * S.gG = S.gG * d + (a * S.X (Fin.last r) 4 + S.X (Fin.last r) 1 * b) := by
  rw [gG_def]; exact der_GG _ h1 h2

theorem der_gGi {d a b : S.Rg} (h1 : d * S.X (Fin.last r) 1 = S.X (Fin.last r) 1 * d + a)
    (h2 : d * S.X (Fin.last r) 4 = S.X (Fin.last r) 4 * d + b) :
    d * S.gGi = S.gGi * d - S.gGi * (a * S.X (Fin.last r) 4 + S.X (Fin.last r) 1 * b) * S.gGi :=
  der_inv (S.der_gG h1 h2) S.gG_gGi S.gGi_gG

theorem ne_last (l : Fin r) : l.castSucc ≠ Fin.last r := (Fin.castSucc_lt_last l).ne
theorem last_ne (l : Fin r) : Fin.last r ≠ l.castSucc := (Fin.castSucc_lt_last l).ne'

theorem dW_dW (j k : Fin (r + 1)) : Commute (S.dW j) (S.dW k) := dd_comm S.isOpen _ _ _ _ _ _
theorem dW_dWb (j k : Fin (r + 1)) : Commute (S.dW j) (S.dWb k) := dd_comm S.isOpen _ _ _ _ _ _
theorem dWb_dWb (j k : Fin (r + 1)) : Commute (S.dWb j) (S.dWb k) := dd_comm S.isOpen _ _ _ _ _ _

theorem Wc_zero_of {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] {T : (Fin (r + 1) → ℂ) →L[ℝ] F}
    {k : Fin (r + 1)} (h : ∀ v : ℂ, T (Pi.single k v) = 0) (s : ℂ) :
    Wc (Pi.single k 1) (Pi.single k Complex.I) s T = 0 := by
  rw [Wc_apply, h, h]; simp

theorem dW_fe {e : (Fin (r + 1) → ℂ) → E →L[ℂ] E} (he : ContDiffOn ℝ ∞ e S.U)
    (hc : ∀ x ∈ S.U, ∀ (a : Fin r) (v : ℂ), fderiv ℝ e x (Pi.single a.castSucc v) = 0) (l : Fin r) :
    Commute (S.dW l.castSucc) (fe S.U e) := by
  show _ * _ = _ * _
  rw [dW, dd_fe S.isOpen he, fe_zero_of (contDiffOn_Wc S.isOpen he _ _ _)
    (fun x hx => Wc_zero_of (hc x hx l) _), add_zero]

theorem dWb_fe {e : (Fin (r + 1) → ℂ) → E →L[ℂ] E} (he : ContDiffOn ℝ ∞ e S.U)
    (hc : ∀ x ∈ S.U, ∀ (a : Fin r) (v : ℂ), fderiv ℝ e x (Pi.single a.castSucc v) = 0) (l : Fin r) :
    Commute (S.dWb l.castSucc) (fe S.U e) := by
  show _ * _ = _ * _
  rw [dWb, dd_fe S.isOpen he, fe_zero_of (contDiffOn_Wc S.isOpen he _ _ _)
    (fun x hx => Wc_zero_of (hc x hx l) _), add_zero]

theorem X_fe {e : (Fin (r + 1) → ℂ) → E →L[ℂ] E} (he : ContDiffOn ℝ ∞ e S.U) (k : Fin (r + 1)) (i : Fin 6) :
    Commute (S.X k i) (fe S.U e) := fn_fe_comm (S.hc k i) he

theorem euler_commute_mul_of_fderiv_eq_zero {e : (Fin (r + 1) → ℂ) → E →L[ℂ] E} (he : ContDiffOn ℝ ∞ e S.U)
    (hc : ∀ x ∈ S.U, ∀ (a : Fin r) (v : ℂ), fderiv ℝ e x (Pi.single a.castSucc v) = 0) (l : Fin r) :
    Commute (S.P l.castSucc) (fe S.U e) := (S.X_fe he _ _).mul_left (S.dW_fe he hc l)

theorem Pb_fe {e : (Fin (r + 1) → ℂ) → E →L[ℂ] E} (he : ContDiffOn ℝ ∞ e S.U)
    (hc : ∀ x ∈ S.U, ∀ (a : Fin r) (v : ℂ), fderiv ℝ e x (Pi.single a.castSucc v) = 0) (l : Fin r) :
    Commute (S.Pb l.castSucc) (fe S.U e) := (S.X_fe he _ _).mul_left (S.dWb_fe he hc l)

theorem coord_commute_holo_deriv_of_ne {j k : Fin (r + 1)} (h : j ≠ k) : Commute (S.X j 1) (S.dW k) := by
  have := S.holo_deriv_coord_commutator k j
  simp only [h.symm, if_false, add_zero] at this
  exact this.symm

theorem conj_coord_commute_antiholo_deriv {j k : Fin (r + 1)} (h : j ≠ k) : Commute (S.X j 4) (S.dWb k) := by
  have := S.antiholo_deriv_conj_coord_commutator k j
  simp only [h.symm, if_false, add_zero] at this
  exact this.symm

theorem P_P (j k : Fin (r + 1)) : Commute (S.P j) (S.P k) := by
  by_cases h : j = k
  · subst h; exact Commute.refl _
  · exact ((show Commute (S.X j 1) (S.X k 1) from S.X_comm _ _ _ _).mul_right (S.coord_commute_holo_deriv_of_ne h)).mul_left
      ((S.coord_commute_holo_deriv_of_ne (Ne.symm h)).symm.mul_right (S.dW_dW j k))

theorem Pb_Pb (j k : Fin (r + 1)) : Commute (S.Pb j) (S.Pb k) := by
  by_cases h : j = k
  · subst h; exact Commute.refl _
  · exact ((show Commute (S.X j 4) (S.X k 4) from S.X_comm _ _ _ _).mul_right (S.conj_coord_commute_antiholo_deriv h)).mul_left
      ((S.conj_coord_commute_antiholo_deriv (Ne.symm h)).symm.mul_right (S.dWb_dWb j k))

theorem P_Pb (j k : Fin (r + 1)) : Commute (S.P j) (S.Pb k) :=
  ((show Commute (S.X j 1) (S.X k 4) from S.X_comm _ _ _ _).mul_right
    (show Commute (S.X j 1) (S.dWb k) from (S.antiholo_deriv_commute_coord k j).symm)).mul_left
    ((show Commute (S.dW j) (S.X k 4) from S.holo_deriv_commute_conj_coord j k).mul_right (S.dW_dWb j k))

theorem euler_commute_holo_deriv_of_ne {j k : Fin (r + 1)} (h : j ≠ k) : Commute (S.P j) (S.dW k) :=
  (S.coord_commute_holo_deriv_of_ne h).mul_left (S.dW_dW j k)
theorem euler_commute_antiholo_deriv (j k : Fin (r + 1)) : Commute (S.P j) (S.dWb k) :=
  (show Commute (S.X j 1) (S.dWb k) from (S.antiholo_deriv_commute_coord k j).symm).mul_left (S.dW_dWb j k)
theorem Pb_dW (j k : Fin (r + 1)) : Commute (S.Pb j) (S.dW k) :=
  (show Commute (S.X j 4) (S.dW k) from (S.holo_deriv_commute_conj_coord k j).symm).mul_left (S.dW_dWb k j).symm
theorem Pb_dWb {j k : Fin (r + 1)} (h : j ≠ k) : Commute (S.Pb j) (S.dWb k) :=
  (S.conj_coord_commute_antiholo_deriv h).mul_left (S.dWb_dWb j k)

theorem isFn_of_mem {x : S.Rg}
    (hx : x ∈ Set.range (fun l : Fin r => S.X l.castSucc 1) ∪ Set.range (fun l : Fin r => S.X l.castSucc 2) ∪
      Set.range (fun l : Fin r => S.X l.castSucc 4) ∪ Set.range (fun l : Fin r => S.X l.castSucc 5) ∪
      {S.X (Fin.last r) 1, S.X (Fin.last r) 2, S.X (Fin.last r) 4, S.X (Fin.last r) 5, S.gG, S.gGi}) :
    ∃ f, ContDiffOn ℝ ∞ f S.U ∧ x = fn S.U f := by
  rcases hx with (((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | hx
  · exact ⟨_, S.hc _ _, rfl⟩
  · exact ⟨_, S.hc _ _, rfl⟩
  · exact ⟨_, S.hc _ _, rfl⟩
  · exact ⟨_, S.hc _ _, rfl⟩
  · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, S.hc _ _, rfl⟩
    · exact ⟨_, S.hc _ _, rfl⟩
    · exact ⟨_, S.hc _ _, rfl⟩
    · exact ⟨_, S.hc _ _, rfl⟩
    · exact ⟨_, S.hGG, rfl⟩
    · exact ⟨_, S.hGGi, rfl⟩

open Formalism.FourierDecayAlt.R in

def lev : LevelData S.Rg r where
  p := fun l => S.P l.castSucc
  pb := fun l => S.Pb l.castSucc
  c := fun l => S.X l.castSucc 1
  ci := fun l => S.X l.castSucc 2
  cb := fun l => S.X l.castSucc 4
  cbi := fun l => S.X l.castSucc 5
  ζ := S.X (Fin.last r) 1
  ζi := S.X (Fin.last r) 2
  ζb := S.X (Fin.last r) 4
  ζbi := S.X (Fin.last r) 5
  GG := S.gG
  GGi := S.gGi
  nab := S.nab
  nabs := S.nabs
  TT := ((S.T * S.T' : ℝ) : ℂ)
  fns_comm := fun x hx y hy => by
    obtain ⟨f, hf, rfl⟩ := S.isFn_of_mem hx
    obtain ⟨g, hg, rfl⟩ := S.isFn_of_mem hy
    exact fn_comm hf hg
  c_ci := fun l => S.coord_mul_inv_coord_eq_one _
  ci_c := fun l => S.inv_coord_mul_coord_eq_one _
  cb_cbi := fun l => S.conj_coord_mul_conj_inv_eq_one _
  cbi_cb := fun l => S.conj_inv_mul_conj_coord_eq_one _
  ζ_ζi := S.coord_mul_inv_coord_eq_one _
  ζi_ζ := S.inv_coord_mul_coord_eq_one _
  ζb_ζbi := S.conj_coord_mul_conj_inv_eq_one _
  ζbi_ζb := S.conj_inv_mul_conj_coord_eq_one _
  GG_GGi := S.gG_gGi
  GGi_GG := S.gGi_gG
  GG_def := S.gG_def
  p_c := fun l m => by simpa [Fin.castSucc_inj] using S.momentum_coord_commutator l.castSucc m.castSucc
  p_ci := fun l m => by simpa [Fin.castSucc_inj] using S.momentum_inv_coord_commutator l.castSucc m.castSucc
  p_cb := fun l m => S.momentum_commute_conj_coord _ _
  p_cbi := fun l m => S.momentum_commute_conj_inv_coord _ _
  p_ζ := fun l => by simpa [ne_last l] using S.momentum_coord_commutator l.castSucc (Fin.last r)
  p_ζi := fun l => by simpa [ne_last l] using S.momentum_inv_coord_commutator l.castSucc (Fin.last r)
  p_ζb := fun l => S.momentum_commute_conj_coord _ _
  p_ζbi := fun l => S.momentum_commute_conj_inv_coord _ _
  p_GG := fun l => by
    have := S.der_gG (d := S.P l.castSucc) (a := 0) (b := 0)
      (by simpa [ne_last l] using S.momentum_coord_commutator l.castSucc (Fin.last r)) (by simpa using S.momentum_commute_conj_coord l.castSucc (Fin.last r))
    simpa using this
  p_GGi := fun l => by
    have := S.der_gGi (d := S.P l.castSucc) (a := 0) (b := 0)
      (by simpa [ne_last l] using S.momentum_coord_commutator l.castSucc (Fin.last r)) (by simpa using S.momentum_commute_conj_coord l.castSucc (Fin.last r))
    simpa using this
  pb_cb := fun l m => by simpa [Fin.castSucc_inj] using S.conj_momentum_conj_coord_commutator l.castSucc m.castSucc
  pb_cbi := fun l m => by simpa [Fin.castSucc_inj] using S.conj_momentum_conj_inv_commutator l.castSucc m.castSucc
  pb_c := fun l m => S.conj_momentum_commute_coord _ _
  pb_ci := fun l m => S.conj_momentum_commute_inv_coord _ _
  pb_ζ := fun l => S.conj_momentum_commute_coord _ _
  pb_ζi := fun l => S.conj_momentum_commute_inv_coord _ _
  pb_ζb := fun l => by simpa [ne_last l] using S.conj_momentum_conj_coord_commutator l.castSucc (Fin.last r)
  pb_ζbi := fun l => by simpa [ne_last l] using S.conj_momentum_conj_inv_commutator l.castSucc (Fin.last r)
  pb_GG := fun l => by
    have := S.der_gG (d := S.Pb l.castSucc) (a := 0) (b := 0)
      (by simpa using S.conj_momentum_commute_coord l.castSucc (Fin.last r)) (by simpa [ne_last l] using S.conj_momentum_conj_coord_commutator l.castSucc (Fin.last r))
    simpa using this
  pb_GGi := fun l => by
    have := S.der_gGi (d := S.Pb l.castSucc) (a := 0) (b := 0)
      (by simpa using S.conj_momentum_commute_coord l.castSucc (Fin.last r)) (by simpa [ne_last l] using S.conj_momentum_conj_coord_commutator l.castSucc (Fin.last r))
    simpa using this
  p_p := fun l m => S.P_P _ _
  p_pb := fun l m => S.P_Pb _ _
  pb_pb := fun l m => S.Pb_Pb _ _
  p_nab := fun l => ((S.euler_commute_holo_deriv_of_ne (ne_last l)).add_right (S.euler_commute_mul_of_fderiv_eq_zero S.h_sm S.h_c l)).eq
  pb_nab := fun l => ((S.Pb_dW _ _).add_right (S.Pb_fe S.h_sm S.h_c l)).eq
  p_nabs := fun l => ((S.euler_commute_antiholo_deriv _ _).neg_right.add_right (S.euler_commute_mul_of_fderiv_eq_zero S.hs_sm S.hs_c l)).eq
  pb_nabs := fun l => ((S.Pb_dWb (ne_last l)).neg_right.add_right (S.Pb_fe S.hs_sm S.hs_c l)).eq
  nab_ζ := by simpa using S.nab_X (S.holo_deriv_coord_commutator (Fin.last r) (Fin.last r))
  nab_ζi := by
    have := S.holo_deriv_inv_coord_commutator (Fin.last r) (Fin.last r)
    rw [sub_eq_add_neg] at this
    simpa [sub_eq_add_neg] using S.nab_X this
  nab_ζb := by simpa using S.nab_X (K := 0) (by simpa using S.holo_deriv_commute_conj_coord (Fin.last r) (Fin.last r))
  nab_ζbi := by simpa using S.nab_X (K := 0) (by simpa using S.holo_deriv_commute_conj_inv_coord (Fin.last r) (Fin.last r))
  nab_GG := by
    have := S.der_gG (d := S.nab) (a := 1) (b := 0)
      (by simpa using S.nab_X (S.holo_deriv_coord_commutator (Fin.last r) (Fin.last r)))
      (by simpa using S.nab_X (K := 0) (by simpa using S.holo_deriv_commute_conj_coord (Fin.last r) (Fin.last r)))
    simpa using this
  nab_GGi := by
    have := S.der_gGi (d := S.nab) (a := 1) (b := 0)
      (by simpa using S.nab_X (S.holo_deriv_coord_commutator (Fin.last r) (Fin.last r)))
      (by simpa using S.nab_X (K := 0) (by simpa using S.holo_deriv_commute_conj_coord (Fin.last r) (Fin.last r)))
    rw [this]
    simp only [one_mul, mul_zero, add_zero]
    rw [show S.gGi * S.X (Fin.last r) 4 = S.X (Fin.last r) 4 * S.gGi from fn_comm S.hGGi (S.hc _ 4)]
  nab_c := fun l => by
    simpa [last_ne l] using S.nab_X (S.holo_deriv_coord_commutator (Fin.last r) l.castSucc)
  nab_ci := fun l => by
    have := S.holo_deriv_inv_coord_commutator (Fin.last r) l.castSucc
    rw [sub_eq_add_neg] at this
    simpa [last_ne l] using S.nab_X this
  nab_cb := fun l => by
    simpa using S.nab_X (K := 0) (by simpa using S.holo_deriv_commute_conj_coord (Fin.last r) l.castSucc)
  nab_cbi := fun l => by
    simpa using S.nab_X (K := 0) (by simpa using S.holo_deriv_commute_conj_inv_coord (Fin.last r) l.castSucc)
  nabs_ζb := by simpa using S.nabs_X (S.antiholo_deriv_conj_coord_commutator (Fin.last r) (Fin.last r))
  nabs_ζbi := by
    have := S.antiholo_deriv_conj_inv_commutator (Fin.last r) (Fin.last r)
    rw [sub_eq_add_neg] at this
    simpa [sub_eq_add_neg] using S.nabs_X this
  nabs_ζ := by simpa using S.nabs_X (K := 0) (by simpa using S.antiholo_deriv_commute_coord (Fin.last r) (Fin.last r))
  nabs_ζi := by simpa using S.nabs_X (K := 0) (by simpa using S.antiholo_deriv_commute_inv_coord (Fin.last r) (Fin.last r))
  nabs_GG := by
    have := S.der_gG (d := S.nabs) (a := 0) (b := -1)
      (by simpa using S.nabs_X (K := 0) (by simpa using S.antiholo_deriv_commute_coord (Fin.last r) (Fin.last r)))
      (by simpa [sub_eq_add_neg] using S.nabs_X (S.antiholo_deriv_conj_coord_commutator (Fin.last r) (Fin.last r)))
    simpa [sub_eq_add_neg] using this
  nabs_GGi := by
    have := S.der_gGi (d := S.nabs) (a := 0) (b := -1)
      (by simpa using S.nabs_X (K := 0) (by simpa using S.antiholo_deriv_commute_coord (Fin.last r) (Fin.last r)))
      (by simpa [sub_eq_add_neg] using S.nabs_X (S.antiholo_deriv_conj_coord_commutator (Fin.last r) (Fin.last r)))
    rw [this]
    simp only [zero_mul, zero_add, mul_neg, mul_one, neg_mul, sub_neg_eq_add]
    rw [show S.gGi * S.X (Fin.last r) 1 = S.X (Fin.last r) 1 * S.gGi from fn_comm S.hGGi (S.hc _ 1)]
  nabs_c := fun l => by
    simpa using S.nabs_X (K := 0) (by simpa using S.antiholo_deriv_commute_coord (Fin.last r) l.castSucc)
  nabs_ci := fun l => by
    simpa using S.nabs_X (K := 0) (by simpa using S.antiholo_deriv_commute_inv_coord (Fin.last r) l.castSucc)
  nabs_cb := fun l => by
    simpa [last_ne l] using S.nabs_X (S.antiholo_deriv_conj_coord_commutator (Fin.last r) l.castSucc)
  nabs_cbi := fun l => by
    have := S.antiholo_deriv_conj_inv_commutator (Fin.last r) l.castSucc
    rw [sub_eq_add_neg] at this
    simpa [last_ne l] using S.nabs_X this

end Setup

end Formalism.MainNotions.LevelRaisingOperators

namespace Formalism.MainNotions.LevelRaisingOperators

open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WirtingerDerivatives Formalism.MainNotions.S.LevR

section RepSec

variable {m : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set (Fin m → ℂ)}

def Rep (U : Set (Fin m → ℂ)) (O : Op m E) (a : Module.End ℂ (SmU U E)) : Prop :=
  ∀ (φ : (Fin m → ℂ) → E) (μ : SmU U E), (∀ x ∈ U, φ x = μ.1 x) → ∀ x ∈ U, O φ x = (a μ).1 x

theorem Rep.comp {O O' : Op m E} {a a' : Module.End ℂ (SmU U E)} (h : Rep U O a) (h' : Rep U O' a') :
    Rep U (O ∘ O') (a * a') := fun φ μ e x hx => h (O' φ) (a' μ) (h' φ μ e) x hx

theorem Rep.add {O O' : Op m E} {a a' : Module.End ℂ (SmU U E)} (h : Rep U O a) (h' : Rep U O' a') :
    Rep U (O + O') (a + a') := fun φ μ e x hx => by
  simp only [Pi.add_apply, LinearMap.add_apply, Submodule.coe_add, h φ μ e x hx, h' φ μ e x hx]

theorem Rep.sub {O O' : Op m E} {a a' : Module.End ℂ (SmU U E)} (h : Rep U O a) (h' : Rep U O' a') :
    Rep U (O - O') (a - a') := fun φ μ e x hx => by
  simp only [Pi.sub_apply, LinearMap.sub_apply, Submodule.coe_sub, h φ μ e x hx, h' φ μ e x hx]

theorem Rep.neg {O : Op m E} {a : Module.End ℂ (SmU U E)} (h : Rep U O a) :
    Rep U (-O) (-a) := fun φ μ e x hx => by
  simp only [Pi.neg_apply, LinearMap.neg_apply, Submodule.coe_neg, h φ μ e x hx]

theorem Rep.zero : Rep U (0 : Op m E) 0 := fun φ μ _ x _ => by simp

theorem Rep.one : Rep U (one : Op m E) 1 := fun φ μ e x hx => e x hx

theorem Rep.scal (Y : ℂ) : Rep U (fun f : (Fin m → ℂ) → E => Y • f) (algebraMap ℂ _ Y) :=
  fun φ μ e x hx => by simp [Module.algebraMap_end_apply, e x hx]

theorem Rep.of_good {O : Op m E} (h : GoodOp U O) : Rep U O (toEnd U O) :=
  fun φ μ e _ hx => (toEnd_apply' h μ φ e hx).symm

theorem Rep.cast {O : Op m E} {a b : Module.End ℂ (SmU U E)} (h : Rep U O a) (e : a = b) : Rep U O b := e ▸ h

theorem Rep.eq {O O' : Op m E} {a a' : Module.End ℂ (SmU U E)} (h : Rep U O a) (h' : Rep U O' a')
    (e : a = a') {φ : (Fin m → ℂ) → E} (hφ : ContDiffOn ℝ ∞ φ U) {x : Fin m → ℂ} (hx : x ∈ U) :
    O φ x = O' φ x := by
  classical
  let μ : SmU U E := ⟨U.indicator φ, hφ.congr (fun y hy => Set.indicator_of_mem hy _),
    fun y hy => Set.indicator_of_notMem hy _⟩
  have hμ : ∀ y ∈ U, φ y = μ.1 y := fun y hy => (Set.indicator_of_mem hy _).symm
  rw [h φ μ hμ x hx, h' φ μ hμ x hx, e]

def IsMul (a : Module.End ℂ (SmU U E)) (f : (Fin m → ℂ) → ℂ) : Prop :=
  ∀ (μ : SmU U E), ∀ x ∈ U, (a μ).1 x = f x • μ.1 x

theorem IsMul.fn {f : (Fin m → ℂ) → ℂ} (hf : ContDiffOn ℝ ∞ f U) : IsMul (E := E) (fn U f) f :=
  fun μ _ hx => fn_apply hf μ hx

theorem IsMul.mul {a b : Module.End ℂ (SmU U E)} {f g : (Fin m → ℂ) → ℂ} (ha : IsMul a f) (hb : IsMul b g) :
    IsMul (a * b) (fun x => f x * g x) := fun μ x hx => by
  rw [Module.End.mul_apply, ha _ x hx, hb _ x hx, mul_smul]

theorem IsMul.const (c : ℂ) : IsMul (U := U) (E := E) (algebraMap ℂ _ c) (fun _ => c) :=
  fun μ x _ => by simp [Module.algebraMap_end_apply]

theorem IsMul.one : IsMul (U := U) (E := E) 1 (fun _ => 1) := fun μ x _ => by simp

theorem IsMul.congr {a : Module.End ℂ (SmU U E)} {f g : (Fin m → ℂ) → ℂ} (ha : IsMul a f)
    (e : ∀ x ∈ U, f x = g x) : IsMul a g := fun μ x hx => by rw [ha μ x hx, e x hx]

theorem IsMul.prod : ∀ (n : ℕ) (a : Fin n → Module.End ℂ (SmU U E)) (f : Fin n → (Fin m → ℂ) → ℂ),
    (∀ i, IsMul (a i) (f i)) → IsMul (List.ofFn a).prod (fun x => ∏ i, f i x)
  | 0, _, _, _ => by simpa using IsMul.one
  | n + 1, a, f, h => by
    rw [List.ofFn_succ, List.prod_cons]
    simp only [Fin.prod_univ_succ]
    exact (h 0).mul (IsMul.prod n _ _ (fun i => h i.succ))

theorem IsMul.rep {a : Module.End ℂ (SmU U E)} {f g : (Fin m → ℂ) → ℂ} (ha : IsMul a f)
    (e : ∀ x ∈ U, g x = f x) : Rep U (mulF g) a := fun φ μ h x hx => by
  rw [ha μ x hx, mulF, e x hx, h x hx]

theorem IsMul.ext {a b : Module.End ℂ (SmU U E)} {f g : (Fin m → ℂ) → ℂ} (ha : IsMul a f) (hb : IsMul b g)
    (e : ∀ x ∈ U, f x = g x) : a = b :=
  end_ext fun μ x hx => by rw [ha μ x hx, hb μ x hx, e x hx]

end RepSec

def pp {M : Type} [Monoid M] {r : ℕ} (f : Fin r → M) : (i : ℕ) → i ≤ r → M
  | 0, _ => 1
  | i + 1, h => f ⟨i, h⟩ * pp f i (by omega)

theorem ordered_product_reverse_eq {M : Type} [Monoid M] {r : ℕ} (f : Fin r → M) : ∀ (i : ℕ) (h : i ≤ r),
    pp f i h = ((List.ofFn (fun j : Fin i => f (Fin.castLE h j))).reverse).prod
  | 0, _ => by simp [pp]
  | i + 1, h => by
    rw [pp, ordered_product_reverse_eq f i (by omega), List.ofFn_succ', List.concat_eq_append, List.reverse_append,
      List.reverse_singleton, List.singleton_append, List.prod_cons]
    rfl

theorem pp_eq {M : Type} [Monoid M] {r : ℕ} (f : Fin r → M) :
    pp f r le_rfl = ((List.ofFn f).reverse).prod := by
  rw [ordered_product_reverse_eq]; rfl

namespace Setup

variable {r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (S : Setup r E)

open Formalism.FourierDecayAlt.R

theorem rep_X (k : Fin (r + 1)) (i : Fin 6) : Rep S.U (mulF (coef k i)) (S.X k i) :=
  Rep.of_good (good_mulF (S.hc k i))

theorem rep_dW (k : Fin (r + 1)) : Rep S.U (wirt (E := E) k) (S.dW k) := by
  have : wirt (E := E) k = opD (Pi.single k 1) (Pi.single k Complex.I) (-Complex.I) := by
    funext g; exact wirt_fun k g
  rw [this]; exact Rep.of_good (good_opD S.isOpen _ _ _)

theorem rep_dWb (k : Fin (r + 1)) : Rep S.U (wirtBar (E := E) k) (S.dWb k) := by
  have : wirtBar (E := E) k = opD (Pi.single k 1) (Pi.single k Complex.I) Complex.I := by
    funext g; exact wirtBar_fun k g
  rw [this]; exact Rep.of_good (good_opD S.isOpen _ _ _)

theorem rep_P (k : Fin (r + 1)) : Rep S.U (pOp (E := E) k) (S.P k) := fun φ μ e x hx => by
  have := ((S.rep_X k 1).comp (S.rep_dW k)) φ μ e x hx
  show _ = ((S.X k 1 * S.dW k) μ).1 x
  rw [← this]
  simp [pOp, S.sub x hx, mulF, coef]

theorem rep_Pb (k : Fin (r + 1)) : Rep S.U (pbOp (E := E) k) (S.Pb k) := fun φ μ e x hx => by
  have := ((S.rep_X k 4).comp (S.rep_dWb k)) φ μ e x hx
  show _ = ((S.X k 4 * S.dWb k) μ).1 x
  rw [← this]
  simp [pbOp, S.sub x hx, mulF, coef]

theorem rep_Tmat (l : Fin r) (Y : ℂ) (a b : Fin 2) :
    Rep S.U (Tmat (E := E) l.castSucc Y a b) (S.lev.Tl Y l a b) := by
  fin_cases a <;> fin_cases b
  · exact (Rep.scal Y).add (S.rep_P l.castSucc)
  · exact (S.rep_X l.castSucc 1).neg
  · exact S.rep_X l.castSucc 2
  · exact Rep.zero

theorem rep_TmatV (l : Fin r) (Y : ℂ) (a b : Fin 2) :
    Rep S.U (TmatV (E := E) l.castSucc Y a b) (S.lev.Tvl Y l a b) := by
  fin_cases a <;> fin_cases b
  · exact (Rep.scal Y).sub (S.rep_Pb l.castSucc)
  · exact (S.rep_X l.castSucc 4).neg
  · exact S.rep_X l.castSucc 5
  · exact Rep.zero

theorem rep_vv (Y : ℂ) : ∀ (i : ℕ) (h : i ≤ r) (a : Fin 2),
    Rep S.U (vv (E := E) Y i h a) (pp (S.lev.Tl Y) i h a 0)
  | 0, _, a => by
    fin_cases a
    · exact Rep.one
    · exact Rep.zero
  | i + 1, h, a => by
    have h0 := rep_vv Y i (by omega)
    have : pp (S.lev.Tl Y) (i + 1) h a 0 =
        S.lev.Tl Y ⟨i, h⟩ a 0 * pp (S.lev.Tl Y) i (by omega) 0 0 +
        S.lev.Tl Y ⟨i, h⟩ a 1 * pp (S.lev.Tl Y) i (by omega) 1 0 := by
      rw [pp, Matrix.mul_apply, Fin.sum_univ_two]
    rw [this]
    have e : vv (E := E) Y (i + 1) h a =
        Tmat (⟨i, by omega⟩ : Fin (r + 1)) Y a 0 ∘ vv Y i (by omega) 0 +
        Tmat (⟨i, by omega⟩ : Fin (r + 1)) Y a 1 ∘ vv Y i (by omega) 1 := by
      rw [vv, vecT, Fin.sum_univ_two]
    rw [e]
    exact ((S.rep_Tmat ⟨i, h⟩ Y a 0).comp (h0 0)).add ((S.rep_Tmat ⟨i, h⟩ Y a 1).comp (h0 1))

theorem rep_vvV (Y : ℂ) : ∀ (i : ℕ) (h : i ≤ r) (a : Fin 2),
    Rep S.U (vvV (E := E) Y i h a) (pp (S.lev.Tvl Y) i h a 0)
  | 0, _, a => by
    fin_cases a
    · exact Rep.one
    · exact Rep.zero
  | i + 1, h, a => by
    have h0 := rep_vvV Y i (by omega)
    have : pp (S.lev.Tvl Y) (i + 1) h a 0 =
        S.lev.Tvl Y ⟨i, h⟩ a 0 * pp (S.lev.Tvl Y) i (by omega) 0 0 +
        S.lev.Tvl Y ⟨i, h⟩ a 1 * pp (S.lev.Tvl Y) i (by omega) 1 0 := by
      rw [pp, Matrix.mul_apply, Fin.sum_univ_two]
    rw [this]
    have e : vvV (E := E) Y (i + 1) h a =
        TmatV (⟨i, by omega⟩ : Fin (r + 1)) Y a 0 ∘ vvV Y i (by omega) 0 +
        TmatV (⟨i, by omega⟩ : Fin (r + 1)) Y a 1 ∘ vvV Y i (by omega) 1 := by
      rw [vvV, vecT, Fin.sum_univ_two]
    rw [e]
    exact ((S.rep_TmatV ⟨i, h⟩ Y a 0).comp (h0 0)).add ((S.rep_TmatV ⟨i, h⟩ Y a 1).comp (h0 1))

theorem rep_Ar (Y : ℂ) : Rep S.U (Formalism.MainNotions.S.LevR.Ar (E := E) r Y) (S.lev.Ar Y) := by
  have := S.rep_vv Y r le_rfl 0
  rwa [pp_eq] at this
theorem rep_Br (Y : ℂ) : Rep S.U (Formalism.MainNotions.S.LevR.Br (E := E) r Y) (S.lev.Br Y) := by
  have := S.rep_vv Y r le_rfl 1
  rwa [pp_eq] at this
theorem rep_ArV (Y : ℂ) : Rep S.U (Formalism.MainNotions.S.LevR.ArV (E := E) r Y) (S.lev.Avr Y) := by
  have := S.rep_vvV Y r le_rfl 0
  rwa [pp_eq] at this
theorem rep_BrV (Y : ℂ) : Rep S.U (Formalism.MainNotions.S.LevR.BrV (E := E) r Y) (S.lev.Bvr Y) := by
  have := S.rep_vvV Y r le_rfl 1
  rwa [pp_eq] at this

theorem mul_X (k : Fin (r + 1)) (i : Fin 6) : IsMul (S.X k i) (coef k i) := IsMul.fn (S.hc k i)

theorem mul_Dr : IsMul S.lev.Dr (Dr (r := r)) :=
  (IsMul.prod r _ _ (fun i => S.mul_X i.castSucc 1)).congr (fun x _ => by simp [Dr, cOf, coef])
theorem mul_Drb : IsMul S.lev.Drb (fun x => star (Dr (r := r) x)) :=
  (IsMul.prod r _ _ (fun i => S.mul_X i.castSucc 4)).congr (fun x _ => by simp [Dr, cOf, coef, map_prod])
theorem mul_Dri : IsMul S.lev.Dri (fun x => (Dr (r := r) x)⁻¹) :=
  (IsMul.prod r _ _ (fun i => S.mul_X i.castSucc 2)).congr (fun x _ => by simp [Dr, cOf, coef])
theorem mul_Drbi : IsMul S.lev.Drbi (fun x => (star (Dr (r := r) x))⁻¹) :=
  (IsMul.prod r _ _ (fun i => S.mul_X i.castSucc 5)).congr (fun x _ => by simp [Dr, cOf, coef, map_prod])
theorem mul_GG : IsMul S.lev.GG (GG S.T S.T') := IsMul.fn S.hGG
theorem mul_GGi : IsMul S.lev.GGi (fun x => (GG S.T S.T' x)⁻¹) := IsMul.fn S.hGGi
theorem multiplier_coordinate : IsMul S.lev.ζ (zOf (r := r)) := S.mul_X _ 1
theorem mul_zi : IsMul S.lev.ζi (fun x => (zOf (r := r) x)⁻¹) := S.mul_X _ 2
theorem mul_zb : IsMul S.lev.ζb (fun x => star (zOf (r := r) x)) := S.mul_X _ 4
theorem mul_zbi : IsMul S.lev.ζbi (fun x => (star (zOf (r := r) x))⁻¹) := S.mul_X _ 5

theorem rep_nab : Rep S.U (nabla r S.h) S.lev.nab := (S.rep_dW _).add (Rep.of_good (good_mulE S.h_sm))

theorem lowering_operator_represented (Y : ℂ) : Rep S.U (Formalism.MainNotions.S.LevR.l0 r S.T S.T' S.h Y) (S.lev.l0 Y) :=
  S.rep_nab.neg.sub (((IsMul.const (Y + 1 / 2)).mul (S.mul_zb.mul S.mul_GGi)).rep
    (fun x _ => by rw [div_eq_mul_inv, mul_assoc]))

theorem level_weight_operator_represented (Y : ℂ) : Rep S.U (Formalism.MainNotions.S.LevR.m0 r S.T S.T' S.hs Y) (S.lev.m0 Y) := by
  have h1 : Rep S.U (dZb r - mulE S.hs) (-S.lev.nabs) :=
    ((S.rep_dWb _).sub (Rep.of_good (good_mulE S.hs_sm))).cast (by
      show S.dWb _ - fe S.U S.hs = -(-S.dWb _ + fe S.U S.hs); abel)
  exact h1.sub (((IsMul.const (Y - 1 / 2)).mul (S.multiplier_coordinate.mul S.mul_GGi)).rep
    (fun x _ => by rw [div_eq_mul_inv, mul_assoc]))

theorem rep_Ahat (Y : ℂ) : Rep S.U (Formalism.MainNotions.S.LevR.Ahat (E := E) r Y) (S.lev.Ahat Y) :=
  (S.mul_Dr.rep (fun _ _ => rfl)).comp (S.rep_Ar Y)

theorem rep_AhatV (Y : ℂ) : Rep S.U (Formalism.MainNotions.S.LevR.AhatV (E := E) r Y) (S.lev.Ahatv Y) :=
  (S.mul_Drb.rep (fun _ _ => rfl)).comp (S.rep_ArV Y)

theorem level_raising_represented (Y : ℂ) : Rep S.U (Formalism.MainNotions.S.LevR.R0 r S.T S.T' S.h Y) (S.lev.R0 Y) :=
  ((S.mul_Drb.mul S.mul_GG).rep (fun _ _ => rfl)).comp (((S.lowering_operator_represented Y).comp (S.rep_Ar Y)).add (S.rep_Br Y))

theorem rep_R0V (Y : ℂ) : Rep S.U (Formalism.MainNotions.S.LevR.weightedMirrorLevelOperator r S.T S.T' S.hs Y) (S.lev.R0v Y) :=
  ((S.mul_Dr.mul S.mul_GG).rep (fun _ _ => rfl)).comp (((S.level_weight_operator_represented Y).comp (S.rep_ArV Y)).add (S.rep_BrV Y))

end Setup

end Formalism.MainNotions.LevelRaisingOperators

namespace Formalism.MainNotions.LevelRaisingOperators

open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WirtingerDerivatives Formalism.MainNotions.S.LevR

section Scalar

variable {m : ℕ}

def LogD (u w : Fin m → ℂ) (s : ℂ) (f : (Fin m → ℂ) → ℂ) (x : Fin m → ℂ) (κ : ℂ) : Prop :=
  DifferentiableAt ℝ f x ∧ Wc u w s (fderiv ℝ f x) = κ * f x

theorem LogD.mul {u w : Fin m → ℂ} {s : ℂ} {f g : (Fin m → ℂ) → ℂ} {x : Fin m → ℂ} {κ κ' : ℂ}
    (hf : LogD u w s f x κ) (hg : LogD u w s g x κ') : LogD u w s (fun y => f y * g y) x (κ + κ') := by
  refine ⟨hf.1.mul hg.1, ?_⟩
  have := Wc_smul hf.1 hg.1 u w s
  simp only [smul_eq_mul] at this
  rw [this, hf.2, hg.2]; ring

theorem LogD.prod {u w : Fin m → ℂ} {s : ℂ} {ι : Type} (t : Finset ι) {f : ι → (Fin m → ℂ) → ℂ}
    {x : Fin m → ℂ} {κ : ι → ℂ} (h : ∀ i ∈ t, LogD u w s (f i) x (κ i)) :
    LogD u w s (fun y => ∏ i ∈ t, f i y) x (∑ i ∈ t, κ i) := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨by simp, by simp [Wc_apply]⟩
  | insert a t ha ih =>
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a t)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem Wc_comp_hol {g : ℂ → ℂ} {g' : ℂ} {f : (Fin m → ℂ) → ℂ} {x : Fin m → ℂ}
    (hg : HasDerivAt g g' (f x)) (hf : DifferentiableAt ℝ f x) (u w : Fin m → ℂ) (s : ℂ) :
    Wc u w s (fderiv ℝ (fun y => g (f y)) x) = g' * Wc u w s (fderiv ℝ f x) := by
  have h := (hg.hasFDerivAt.restrictScalars ℝ).comp x hf.hasFDerivAt
  have h3 : fderiv ℝ (fun y => g (f y)) x = _ := h.fderiv
  rw [h3]
  simp only [Wc_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  ring

theorem LogD.cpow {u w : Fin m → ℂ} {s : ℂ} {f : (Fin m → ℂ) → ℂ} {x : Fin m → ℂ} {κ : ℂ}
    (hf : LogD u w s f x κ) (hx : f x ∈ Complex.slitPlane) (t : ℂ) :
    Wc u w s (fderiv ℝ (fun y => f y ^ t) x) = t * κ * f x ^ t := by
  have h0 : f x ≠ 0 := Complex.slitPlane_ne_zero hx
  have hd : HasDerivAt (fun z : ℂ => z ^ t) (t * f x ^ (t - 1) * 1) (f x) := (hasDerivAt_id (f x)).cpow_const hx
  rw [Wc_comp_hol hd hf.1, hf.2, Complex.cpow_sub _ _ h0, Complex.cpow_one]
  field_simp

theorem contDiffOn_cpow {U : Set (Fin m → ℂ)} {f : (Fin m → ℂ) → ℂ} (hf : ContDiffOn ℝ ∞ f U)
    (hx : ∀ x ∈ U, f x ∈ Complex.slitPlane) (t : ℂ) : ContDiffOn ℝ ∞ (fun y => f y ^ t) U := by
  intro x hxU
  have h1 : ContDiffAt ℝ ∞ (fun z : ℂ => z ^ t) (f x) :=
    ((analyticAt_id.cpow analyticAt_const (hx x hxU)).contDiffAt (n := ∞)).restrict_scalars ℝ
  exact h1.comp_contDiffWithinAt x (hf x hxU)

theorem wirt_antihol {f : (Fin m → ℂ) → ℂ} {x : Fin m → ℂ}
    (hf : DifferentiableAt ℂ (fun y => star (f y)) x) (k : Fin m) :
    Wc (Pi.single k 1) (Pi.single k Complex.I) (-Complex.I) (fderiv ℝ f x) = 0 := by
  have h1 := (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp x (hf.hasFDerivAt.restrictScalars ℝ)
  have h2 : (⇑(Complex.conjCLE : ℂ →L[ℝ] ℂ) ∘ fun y => star (f y)) = f := by funext y; simp
  rw [h2] at h1
  rw [h1.fderiv, Wc_apply]
  have hI : (Pi.single k Complex.I : Fin m → ℂ) = Complex.I • Pi.single k 1 := by
    rw [← Pi.single_smul]; simp
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars', hI, map_smul,
    ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, smul_eq_mul, map_mul, Complex.conj_I]
  linear_combination ((starRingEnd ℂ) ((fderiv ℂ (fun y => star (f y)) x) (Pi.single k 1)) / 2) * Complex.I_sq

theorem wirtBar_hol {f : (Fin m → ℂ) → ℂ} {x : Fin m → ℂ} (hf : DifferentiableAt ℂ f x) (k : Fin m) :
    Wc (Pi.single k 1) (Pi.single k Complex.I) Complex.I (fderiv ℝ f x) = 0 := by
  have h1 := hf.hasFDerivAt.restrictScalars ℝ
  rw [h1.fderiv, Wc_apply]
  have hI : (Pi.single k Complex.I : Fin m → ℂ) = Complex.I • Pi.single k 1 := by
    rw [← Pi.single_smul]; simp
  simp only [ContinuousLinearMap.coe_restrictScalars', hI, map_smul, smul_eq_mul]
  linear_combination ((fderiv ℂ f x) (Pi.single k 1) / 2) * Complex.I_sq

end Scalar

end Formalism.MainNotions.LevelRaisingOperators

namespace Formalism.MainNotions.LevelRaisingOperators

open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WirtingerDerivatives Formalism.MainNotions.S.LevR

theorem IsMul.neg {m : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set (Fin m → ℂ)}
    {a : Module.End ℂ (SmU U E)} {f : (Fin m → ℂ) → ℂ} (ha : IsMul a f) : IsMul (-a) (fun x => -f x) :=
  fun μ x hx => by
    rw [LinearMap.neg_apply, Submodule.coe_neg, Pi.neg_apply, ha μ x hx, neg_smul]

theorem IsMul.comm_fe {m : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set (Fin m → ℂ)}
    {a : Module.End ℂ (SmU U E)} {f : (Fin m → ℂ) → ℂ} (ha : IsMul a f) {e : (Fin m → ℂ) → E →L[ℂ] E}
    (he : ContDiffOn ℝ ∞ e U) : a * fe U e = fe U e * a :=
  end_ext fun μ x hx => by
    rw [Module.End.mul_apply, Module.End.mul_apply, ha _ x hx, fe_apply he _ hx, fe_apply he _ hx, ha _ x hx,
      map_smul]

def uk {m : ℕ} (k : Fin m) (t : ℂ) : (Fin m → ℂ) → ℂ := fun y => coef k 1 y * coef k 4 y - t

theorem uk_diff {m : ℕ} {x : Fin m → ℂ} (hx : x ∈ OmX m) (k : Fin m) (t : ℂ) : DifferentiableAt ℝ (uk k t) x :=
  ((diff_of_reg (coef_contDiffAt hx 1)).mul (diff_of_reg (coef_contDiffAt hx 4))).sub_const t

theorem log_deriv_radial_unit_wirtinger {m : ℕ} {x : Fin m → ℂ} (hx : x ∈ OmX m) (j k : Fin m) (t : ℂ) (hne : uk k t x ≠ 0) :
    LogD (Pi.single j 1) (Pi.single j Complex.I) (-Complex.I) (uk k t) x
      (if j = k then star (x k) / uk k t x else 0) := by
  refine ⟨uk_diff hx k t, ?_⟩
  have h1 : fderiv ℝ (uk k t) x = fderiv ℝ (fun y => coef k 1 y • coef k 4 y) x := by
    show fderiv ℝ (fun y => coef k 1 y • coef k 4 y - t) x = _
    rw [fderiv_sub_const]
  rw [h1, Wc_smul (diff_of_reg (coef_contDiffAt hx 1)) (diff_of_reg (coef_contDiffAt hx 4)),
    ← wirt_eq, ← wirt_eq, wirt_coef hx, wirt_coef hx]
  by_cases h : j = k
  · subst h; simp [ck, coef]; field_simp
  · simp [h]

theorem logD_uk_Wb {m : ℕ} {x : Fin m → ℂ} (hx : x ∈ OmX m) (j k : Fin m) (t : ℂ) (hne : uk k t x ≠ 0) :
    LogD (Pi.single j 1) (Pi.single j Complex.I) Complex.I (uk k t) x
      (if j = k then x k / uk k t x else 0) := by
  refine ⟨uk_diff hx k t, ?_⟩
  have h1 : fderiv ℝ (uk k t) x = fderiv ℝ (fun y => coef k 1 y • coef k 4 y) x := by
    show fderiv ℝ (fun y => coef k 1 y • coef k 4 y - t) x = _
    rw [fderiv_sub_const]
  rw [h1, Wc_smul (diff_of_reg (coef_contDiffAt hx 1)) (diff_of_reg (coef_contDiffAt hx 4)),
    ← wirtBar_eq, ← wirtBar_eq, wirtBar_coef hx, wirtBar_coef hx]
  by_cases h : j = k
  · subst h; simp [ck, coef]; field_simp
  · simp [h]

namespace Setup

variable {r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (S : Setup r E)

open Formalism.FourierDecayAlt.R

def tt : ℂ := ((S.T * S.T' : ℝ) : ℂ)

theorem Gfn_eq (x : Fin (r + 1) → ℂ) :
    Gfn S.T S.T' x = (∏ a : Fin r, uk a.castSucc 0 x) * uk (Fin.last r) S.tt x := by
  simp only [Gfn, uk, sub_zero, S.GG_eq, tt]
  congr 1
  rw [← Complex.mul_conj, Dr, map_prod, ← Finset.prod_mul_distrib]
  rfl

theorem radial_unit_ne_zero {x : Fin (r + 1) → ℂ} (hx : x ∈ S.U) (k : Fin (r + 1)) : uk k 0 x ≠ 0 := by
  have := S.sub x hx k
  simp [uk, coef, this]

theorem ukt_eq (x : Fin (r + 1) → ℂ) : uk (Fin.last r) S.tt x = GG S.T S.T' x := (S.GG_eq x).symm

theorem ukt_ne {x : Fin (r + 1) → ℂ} (hx : x ∈ S.U) : uk (Fin.last r) S.tt x ≠ 0 := by
  rw [S.ukt_eq]; exact S.GG_ne hx

theorem Dr_ne {x : Fin (r + 1) → ℂ} (hx : x ∈ S.U) : Dr x ≠ 0 :=
  Finset.prod_ne_zero_iff.2 (fun a _ => S.sub x hx a.castSucc)

theorem Gfn_slit {x : Fin (r + 1) → ℂ} (hx : x ∈ S.U) : Gfn S.T S.T' x ∈ Complex.slitPlane := by
  have h1 : 0 < Complex.normSq (Dr x) := Complex.normSq_pos.2 (S.Dr_ne hx)
  have h2 : 0 < Complex.normSq (zOf x) - S.T * S.T' := sub_pos.2 (S.pos x hx)
  have : Gfn S.T S.T' x = ((Complex.normSq (Dr x) * (Complex.normSq (zOf x) - S.T * S.T') : ℝ) : ℂ) := by
    simp only [Gfn, GG]; push_cast; ring
  rw [this]
  exact Complex.ofReal_mem_slitPlane.2 (mul_pos h1 h2)

theorem hGfn : ContDiffOn ℝ ∞ (Gfn S.T S.T') S.U := by
  have h : ContDiffOn ℝ ∞ (fun x => (∏ a : Fin r, uk a.castSucc 0 x) * uk (Fin.last r) S.tt x) S.U :=
    (contDiffOn_prod (fun a _ => ((S.hc a.castSucc 1).mul (S.hc a.castSucc 4)).sub contDiffOn_const)).mul
      (((S.hc _ 1).mul (S.hc _ 4)).sub contDiffOn_const)
  exact h.congr (fun x _ => S.Gfn_eq x)

theorem hGs (s : ℂ) : ContDiffOn ℝ ∞ (fun x => Gfn S.T S.T' x ^ s) S.U :=
  contDiffOn_cpow S.hGfn (fun _ hx => S.Gfn_slit hx) s

def kW (j : Fin (r + 1)) (x : Fin (r + 1) → ℂ) : ℂ :=
  (∑ a : Fin r, if j = a.castSucc then star (x a.castSucc) / uk a.castSucc 0 x else 0) +
    (if j = Fin.last r then star (x (Fin.last r)) / uk (Fin.last r) S.tt x else 0)

def kWb (j : Fin (r + 1)) (x : Fin (r + 1) → ℂ) : ℂ :=
  (∑ a : Fin r, if j = a.castSucc then x a.castSucc / uk a.castSucc 0 x else 0) +
    (if j = Fin.last r then x (Fin.last r) / uk (Fin.last r) S.tt x else 0)

theorem log_deriv_gauge_wirtinger {x : Fin (r + 1) → ℂ} (hx : x ∈ S.U) (j : Fin (r + 1)) :
    LogD (Pi.single j 1) (Pi.single j Complex.I) (-Complex.I) (Gfn S.T S.T') x (S.kW j x) := by
  have : Gfn S.T S.T' = fun x => (∏ a : Fin r, uk a.castSucc 0 x) * uk (Fin.last r) S.tt x :=
    funext S.Gfn_eq
  rw [this]
  exact (LogD.prod Finset.univ (fun a _ => log_deriv_radial_unit_wirtinger (S.sub x hx) j a.castSucc 0 (S.radial_unit_ne_zero hx _))).mul
    (log_deriv_radial_unit_wirtinger (S.sub x hx) j (Fin.last r) S.tt (S.ukt_ne hx))

theorem logD_G_Wb {x : Fin (r + 1) → ℂ} (hx : x ∈ S.U) (j : Fin (r + 1)) :
    LogD (Pi.single j 1) (Pi.single j Complex.I) Complex.I (Gfn S.T S.T') x (S.kWb j x) := by
  have : Gfn S.T S.T' = fun x => (∏ a : Fin r, uk a.castSucc 0 x) * uk (Fin.last r) S.tt x :=
    funext S.Gfn_eq
  rw [this]
  exact (LogD.prod Finset.univ (fun a _ => logD_uk_Wb (S.sub x hx) j a.castSucc 0 (S.radial_unit_ne_zero hx _))).mul
    (logD_uk_Wb (S.sub x hx) j (Fin.last r) S.tt (S.ukt_ne hx))

theorem kW_c {x : Fin (r + 1) → ℂ} (hx : x ∈ S.U) (l : Fin r) : x l.castSucc * S.kW l.castSucc x = 1 := by
  have h := S.sub x hx l.castSucc
  simp only [kW, Fin.castSucc_inj, Finset.sum_ite_eq, Finset.mem_univ, if_true, ne_last l, if_false, add_zero,
    uk, coef, sub_zero]
  have h' : star (x l.castSucc) ≠ 0 := by simpa using h
  field_simp

theorem kWb_c {x : Fin (r + 1) → ℂ} (hx : x ∈ S.U) (l : Fin r) :
    star (x l.castSucc) * S.kWb l.castSucc x = 1 := by
  have h := S.sub x hx l.castSucc
  simp only [kWb, Fin.castSucc_inj, Finset.sum_ite_eq, Finset.mem_univ, if_true, ne_last l, if_false, add_zero,
    uk, coef, sub_zero]
  have h' : star (x l.castSucc) ≠ 0 := by simpa using h
  field_simp

theorem kW_last_eq_star_mul_inv (x : Fin (r + 1) → ℂ) : S.kW (Fin.last r) x = star (zOf x) * (GG S.T S.T' x)⁻¹ := by
  simp only [kW, last_ne, if_false, Finset.sum_const_zero, zero_add, if_true, S.ukt_eq, div_eq_mul_inv, zOf]

theorem antiholomorphic_kernel_last_eq (x : Fin (r + 1) → ℂ) : S.kWb (Fin.last r) x = zOf x * (GG S.T S.T' x)⁻¹ := by
  simp only [kWb, last_ne, if_false, Finset.sum_const_zero, zero_add, if_true, S.ukt_eq, div_eq_mul_inv, zOf]

def Gs (s : ℂ) : S.Rg := fn S.U (fun x => Gfn S.T S.T' x ^ s)

theorem mul_Gs (s : ℂ) : IsMul (S.Gs s) (fun x => Gfn S.T S.T' x ^ s) := IsMul.fn (S.hGs s)

theorem dW_Gs (j : Fin (r + 1)) (s : ℂ) : ∃ K : S.Rg, IsMul K (fun x => s * S.kW j x * Gfn S.T S.T' x ^ s) ∧
    S.dW j * S.Gs s = S.Gs s * S.dW j + K :=
  ⟨_, (IsMul.fn (contDiffOn_Wc S.isOpen (S.hGs s) _ _ _)).congr
    (fun x hx => (S.log_deriv_gauge_wirtinger hx j).cpow (S.Gfn_slit hx) s), dd_fn S.isOpen (S.hGs s) _ _ _⟩

theorem dWb_Gs (j : Fin (r + 1)) (s : ℂ) : ∃ K : S.Rg, IsMul K (fun x => s * S.kWb j x * Gfn S.T S.T' x ^ s) ∧
    S.dWb j * S.Gs s = S.Gs s * S.dWb j + K :=
  ⟨_, (IsMul.fn (contDiffOn_Wc S.isOpen (S.hGs s) _ _ _)).congr
    (fun x hx => (S.logD_G_Wb hx j).cpow (S.Gfn_slit hx) s), dd_fn S.isOpen (S.hGs s) _ _ _⟩

theorem Gs_inv (s : ℂ) : S.Gs s * S.Gs (-s) = 1 :=
  fn_mul_one (S.hGs s) (S.hGs (-s)) (fun x hx => by
    have h0 : Gfn S.T S.T' x ≠ 0 := Complex.slitPlane_ne_zero (S.Gfn_slit hx)
    rw [Complex.cpow_neg]
    exact mul_inv_cancel₀ (by simp [Complex.cpow_eq_zero_iff, h0]))

theorem Gs_inv' (s : ℂ) : S.Gs (-s) * S.Gs s = 1 := by
  have := S.Gs_inv (-s); rwa [neg_neg] at this

theorem fns_fn {x : S.Rg} (hx : x ∈ S.lev.fns) : ∃ f, ContDiffOn ℝ ∞ f S.U ∧ x = fn S.U f := S.isFn_of_mem hx

theorem ruleG (s Y : ℂ) :
    S.Gs (-s) * S.lev.Ahat Y * S.Gs s = S.lev.Ahat (Y + s) ∧ S.Gs (-s) * S.lev.R0 Y * S.Gs s = S.lev.R0 (Y + s) ∧
      S.Gs (-s) * S.lev.Ahatv Y * S.Gs s = S.lev.Ahatv (Y - s) ∧
      S.Gs (-s) * S.lev.R0v Y * S.Gs s = S.lev.R0v (Y - s) := by
  refine Formalism.FourierDecayAlt.P.gaugeConjugation S.Rg r S.lev s (S.Gs s) (S.Gs (-s)) (S.Gs_inv s) (S.Gs_inv' s) ?_ ?_ ?_ ?_ ?_ Y
  · intro x hx
    obtain ⟨f, hf, rfl⟩ := S.fns_fn hx
    exact fn_comm hf (S.hGs s)
  · intro l
    obtain ⟨K, hK, e⟩ := S.dW_Gs l.castSucc s
    have e2 := der_left (x := S.X l.castSucc 1) (fn_comm (S.hc _ 1) (S.hGs s)) e
    have e3 : S.X l.castSucc 1 * K = algebraMap ℂ S.Rg s * S.Gs s := by
      refine ((S.mul_X _ 1).mul hK).ext ((IsMul.const s).mul (S.mul_Gs s)) (fun x hx => ?_)
      have := S.kW_c hx l
      simp only [coef]
      linear_combination (s * Gfn S.T S.T' x ^ s) * this
    rw [e3] at e2; exact e2
  · intro l
    obtain ⟨K, hK, e⟩ := S.dWb_Gs l.castSucc s
    have e2 := der_left (x := S.X l.castSucc 4) (fn_comm (S.hc _ 4) (S.hGs s)) e
    have e3 : S.X l.castSucc 4 * K = algebraMap ℂ S.Rg s * S.Gs s := by
      refine ((S.mul_X _ 4).mul hK).ext ((IsMul.const s).mul (S.mul_Gs s)) (fun x hx => ?_)
      have := S.kWb_c hx l
      simp only [coef]
      linear_combination (s * Gfn S.T S.T' x ^ s) * this
    rw [e3] at e2; exact e2
  · obtain ⟨K, hK, e⟩ := S.dW_Gs (Fin.last r) s
    have e2 := S.nab_der (S.hGs s) e
    have e3 : K = algebraMap ℂ S.Rg s * (S.lev.ζb * S.lev.GGi * S.Gs s) := by
      refine hK.ext ((IsMul.const s).mul ((S.mul_zb.mul S.mul_GGi).mul (S.mul_Gs s))) (fun x _ => ?_)
      rw [S.kW_last_eq_star_mul_inv]; ring
    rw [e3] at e2; exact e2
  · obtain ⟨K, hK, e⟩ := S.dWb_Gs (Fin.last r) s
    have e2 := S.nabs_der (S.hGs s) e
    have e3 : K = algebraMap ℂ S.Rg s * (S.lev.ζ * S.lev.GGi * S.Gs s) := by
      refine hK.ext ((IsMul.const s).mul ((S.multiplier_coordinate.mul S.mul_GGi).mul (S.mul_Gs s))) (fun x _ => ?_)
      rw [S.antiholomorphic_kernel_last_eq]; ring
    rw [e3] at e2; exact e2

theorem nab_fe {e : (Fin (r + 1) → ℂ) → E →L[ℂ] E} (he : ContDiffOn ℝ ∞ e S.U) {κ : (Fin (r + 1) → ℂ) → ℂ}
    {K : S.Rg} (hK : IsMul K κ)
    (cov : ∀ x ∈ S.U, wirt (Fin.last r) e x + (S.h x).comp (e x) - (e x).comp (S.h x) = κ x • e x) :
    S.nab * fe S.U e = fe S.U e * S.nab + K * fe S.U e := by
  have h1 : fe S.U (fun y => Wc (Pi.single (Fin.last r) 1) (Pi.single (Fin.last r) Complex.I) (-Complex.I)
      (fderiv ℝ e y)) + fe S.U S.h * fe S.U e = fe S.U e * fe S.U S.h + K * fe S.U e := by
    apply end_ext; intro μ x hx
    simp only [LinearMap.add_apply, Module.End.mul_apply, Submodule.coe_add, Pi.add_apply,
      fe_apply (contDiffOn_Wc S.isOpen he _ _ _) _ hx, fe_apply he _ hx, fe_apply S.h_sm _ hx, hK _ x hx]
    have := congrArg (fun T : E →L[ℂ] E => T (μ.1 x)) (cov x hx)
    simp only [wirt_eq, _root_.add_apply, _root_.sub_apply, _root_.smul_apply,
      ContinuousLinearMap.comp_apply] at this
    rw [← this]; abel
  rw [nab, add_mul, dW, dd_fe S.isOpen he, mul_add, add_assoc, h1]; abel

theorem nabs_fe {e : (Fin (r + 1) → ℂ) → E →L[ℂ] E} (he : ContDiffOn ℝ ∞ e S.U) {κ : (Fin (r + 1) → ℂ) → ℂ}
    {K : S.Rg} (hK : IsMul K κ)
    (cov : ∀ x ∈ S.U, -wirtBar (Fin.last r) e x + (S.hs x).comp (e x) - (e x).comp (S.hs x) = κ x • e x) :
    S.nabs * fe S.U e = fe S.U e * S.nabs + K * fe S.U e := by
  have h1 : -fe S.U (fun y => Wc (Pi.single (Fin.last r) 1) (Pi.single (Fin.last r) Complex.I) Complex.I
      (fderiv ℝ e y)) + fe S.U S.hs * fe S.U e = fe S.U e * fe S.U S.hs + K * fe S.U e := by
    apply end_ext; intro μ x hx
    simp only [LinearMap.add_apply, LinearMap.neg_apply, Module.End.mul_apply, Submodule.coe_add, Submodule.coe_neg,
      Pi.add_apply, Pi.neg_apply,
      fe_apply (contDiffOn_Wc S.isOpen he _ _ _) _ hx, fe_apply he _ hx, fe_apply S.hs_sm _ hx, hK _ x hx]
    have := congrArg (fun T : E →L[ℂ] E => T (μ.1 x)) (cov x hx)
    simp only [wirtBar_eq, _root_.add_apply, _root_.sub_apply, _root_.smul_apply, _root_.neg_apply,
      ContinuousLinearMap.comp_apply] at this
    rw [← this]; abel
  rw [nabs, add_mul, neg_mul, dWb, dd_fe S.isOpen he, mul_add, mul_neg, neg_add, add_assoc, h1]; abel

end Setup

end Formalism.MainNotions.LevelRaisingOperators

namespace Formalism.MainNotions.LevelRaisingOperators

open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WirtingerDerivatives Formalism.MainNotions.S.LevR

section CommFSec

variable {m : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set (Fin m → ℂ)}
  {f : (Fin m → ℂ) → ℂ}

structure CommF (U : Set (Fin m → ℂ)) (f : (Fin m → ℂ) → ℂ) (O : Op m E) : Prop where
  loc : ∀ g g', (∀ x ∈ U, g x = g' x) → ∀ x ∈ U, O g x = O g' x
  smooth : ∀ g, ContDiffOn ℝ ∞ g U → ContDiffOn ℝ ∞ (O g) U
  comm : ∀ g, ContDiffOn ℝ ∞ g U → ∀ x ∈ U, O (fun y => f y • g y) x = f x • O g x

variable {O O' : Op m E}

theorem CommF.comp (h : CommF U f O) (h' : CommF U f O') : CommF U f (O ∘ O') where
  loc := fun g g' e x hx => h.loc _ _ (h'.loc g g' e) x hx
  smooth := fun g hg => h.smooth _ (h'.smooth g hg)
  comm := fun g hg x hx => by
    show O (O' fun y => f y • g y) x = f x • O (O' g) x
    rw [h.loc _ (fun y => f y • O' g y) (h'.comm g hg) x hx, h.comm _ (h'.smooth g hg) x hx]

theorem CommF.add (h : CommF U f O) (h' : CommF U f O') : CommF U f (O + O') where
  loc := fun g g' e x hx => by simp only [Pi.add_apply, h.loc g g' e x hx, h'.loc g g' e x hx]
  smooth := fun g hg => (h.smooth g hg).add (h'.smooth g hg)
  comm := fun g hg x hx => by simp only [Pi.add_apply, h.comm g hg x hx, h'.comm g hg x hx, smul_add]

theorem CommF.sub (h : CommF U f O) (h' : CommF U f O') : CommF U f (O - O') where
  loc := fun g g' e x hx => by simp only [Pi.sub_apply, h.loc g g' e x hx, h'.loc g g' e x hx]
  smooth := fun g hg => (h.smooth g hg).sub (h'.smooth g hg)
  comm := fun g hg x hx => by simp only [Pi.sub_apply, h.comm g hg x hx, h'.comm g hg x hx, smul_sub]

theorem CommF.neg (h : CommF U f O) : CommF U f (-O) where
  loc := fun g g' e x hx => by simp only [Pi.neg_apply, h.loc g g' e x hx]
  smooth := fun g hg => (h.smooth g hg).neg
  comm := fun g hg x hx => by simp only [Pi.neg_apply, h.comm g hg x hx, smul_neg]

theorem CommF.zero : CommF U f (0 : Op m E) where
  loc := fun _ _ _ _ _ => rfl
  smooth := fun _ _ => contDiffOn_const
  comm := fun _ _ _ _ => by simp

theorem CommF.one : CommF U f (one : Op m E) where
  loc := fun _ _ e x hx => e x hx
  smooth := fun _ hg => hg
  comm := fun _ _ _ _ => rfl

theorem CommF.scal (Y : ℂ) : CommF U f (fun g : (Fin m → ℂ) → E => Y • g) where
  loc := fun g g' e x hx => by simp only [Pi.smul_apply, e x hx]
  smooth := fun _ hg => hg.const_smul Y
  comm := fun g _ x _ => by simp only [Pi.smul_apply]; exact smul_comm _ _ _

theorem CommF.mulF {a : (Fin m → ℂ) → ℂ} (ha : ContDiffOn ℝ ∞ a U) : CommF U f (mulF (E := E) a) where
  loc := (good_mulF ha).loc
  smooth := (good_mulF ha).smooth
  comm := fun g _ x _ => by simp only [Formalism.MainNotions.S.LevR.mulF]; exact smul_comm _ _ _

theorem CommF.mulE {e : (Fin m → ℂ) → E →L[ℂ] E} (he : ContDiffOn ℝ ∞ e U) : CommF U f (mulE e) where
  loc := (good_mulE he).loc
  smooth := (good_mulE he).smooth
  comm := fun g _ x _ => by simp only [Formalism.MainNotions.S.LevR.mulE, map_smul]

theorem CommF.opD (hU : IsOpen U) {u w : Fin m → ℂ} {s : ℂ} (hd : ∀ x ∈ U, DifferentiableAt ℝ f x)
    (h0 : ∀ x ∈ U, Wc u w s (fderiv ℝ f x) = 0) : CommF U f (opD (E := E) u w s) where
  loc := (good_opD hU u w s).loc
  smooth := (good_opD hU u w s).smooth
  comm := fun g hg x hx => by
    simp only [Formalism.MainNotions.LevelRaisingOperators.opD]
    rw [Wc_smul (hd x hx) (diff_of_reg (cda hU hg hx)), h0 x hx, zero_smul, zero_add]

theorem CommF.congr (h : CommF U f O) (e : ∀ g, ∀ x ∈ U, O' g x = O g x) : CommF U f O' where
  loc := fun g g' e' x hx => by rw [e g x hx, e g' x hx, h.loc g g' e' x hx]
  smooth := fun g hg => (h.smooth g hg).congr (e g)
  comm := fun g hg x hx => by rw [e _ x hx, e g x hx, h.comm g hg x hx]

end CommFSec

namespace Setup

variable {r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (S : Setup r E)
  {f : (Fin (r + 1) → ℂ) → ℂ}

def AH (f : (Fin (r + 1) → ℂ) → ℂ) : Prop := (∀ x ∈ S.U, DifferentiableAt ℝ f x) ∧
  ∀ k, ∀ x ∈ S.U, Wc (Pi.single k 1) (Pi.single k Complex.I) (-Complex.I) (fderiv ℝ f x) = 0

def HO (f : (Fin (r + 1) → ℂ) → ℂ) : Prop := (∀ x ∈ S.U, DifferentiableAt ℝ f x) ∧
  ∀ k, ∀ x ∈ S.U, Wc (Pi.single k 1) (Pi.single k Complex.I) Complex.I (fderiv ℝ f x) = 0

theorem cf_X (k : Fin (r + 1)) (i : Fin 6) : CommF S.U f (mulF (E := E) (coef k i)) := CommF.mulF (S.hc k i)

theorem cf_wirt (hf : S.AH f) (k : Fin (r + 1)) : CommF S.U f (wirt (E := E) k) :=
  (CommF.opD S.isOpen hf.1 (hf.2 k)).congr (fun g x _ => wirt_eq k g x)

theorem cf_wirtBar (hf : S.HO f) (k : Fin (r + 1)) : CommF S.U f (wirtBar (E := E) k) :=
  (CommF.opD S.isOpen hf.1 (hf.2 k)).congr (fun g x _ => wirtBar_eq k g x)

theorem cf_P (hf : S.AH f) (k : Fin (r + 1)) : CommF S.U f (pOp (E := E) k) :=
  ((S.cf_X k 1).comp (S.cf_wirt hf k)).congr (fun g x hx => by simp [pOp, S.sub x hx, mulF, coef])

theorem cf_Pb (hf : S.HO f) (k : Fin (r + 1)) : CommF S.U f (pbOp (E := E) k) :=
  ((S.cf_X k 4).comp (S.cf_wirtBar hf k)).congr (fun g x hx => by simp [pbOp, S.sub x hx, mulF, coef])

theorem cf_Tmat (hf : S.AH f) (l : Fin (r + 1)) (Y : ℂ) (a b : Fin 2) : CommF S.U f (Tmat (E := E) l Y a b) := by
  fin_cases a <;> fin_cases b
  · exact (CommF.scal Y).add (S.cf_P hf l)
  · exact (S.cf_X l 1).neg
  · exact S.cf_X l 2
  · exact CommF.zero

theorem cf_TmatV (hf : S.HO f) (l : Fin (r + 1)) (Y : ℂ) (a b : Fin 2) :
    CommF S.U f (TmatV (E := E) l Y a b) := by
  fin_cases a <;> fin_cases b
  · exact (CommF.scal Y).sub (S.cf_Pb hf l)
  · exact (S.cf_X l 4).neg
  · exact S.cf_X l 5
  · exact CommF.zero

theorem cf_vv (hf : S.AH f) (Y : ℂ) : ∀ (i : ℕ) (h : i ≤ r) (a : Fin 2), CommF S.U f (vv (E := E) Y i h a)
  | 0, _, a => by
    fin_cases a
    · exact CommF.one
    · exact CommF.zero
  | i + 1, h, a => by
    have h0 := cf_vv hf Y i (by omega)
    have e : vv (E := E) Y (i + 1) h a =
        Tmat (⟨i, by omega⟩ : Fin (r + 1)) Y a 0 ∘ vv Y i (by omega) 0 +
        Tmat (⟨i, by omega⟩ : Fin (r + 1)) Y a 1 ∘ vv Y i (by omega) 1 := by
      rw [vv, vecT, Fin.sum_univ_two]
    rw [e]
    exact ((S.cf_Tmat hf _ Y a 0).comp (h0 0)).add ((S.cf_Tmat hf _ Y a 1).comp (h0 1))

theorem cf_vvV (hf : S.HO f) (Y : ℂ) : ∀ (i : ℕ) (h : i ≤ r) (a : Fin 2), CommF S.U f (vvV (E := E) Y i h a)
  | 0, _, a => by
    fin_cases a
    · exact CommF.one
    · exact CommF.zero
  | i + 1, h, a => by
    have h0 := cf_vvV hf Y i (by omega)
    have e : vvV (E := E) Y (i + 1) h a =
        TmatV (⟨i, by omega⟩ : Fin (r + 1)) Y a 0 ∘ vvV Y i (by omega) 0 +
        TmatV (⟨i, by omega⟩ : Fin (r + 1)) Y a 1 ∘ vvV Y i (by omega) 1 := by
      rw [vvV, vecT, Fin.sum_univ_two]
    rw [e]
    exact ((S.cf_TmatV hf _ Y a 0).comp (h0 0)).add ((S.cf_TmatV hf _ Y a 1).comp (h0 1))

theorem hDr : ContDiffOn ℝ ∞ (Dr (r := r)) S.U :=
  contDiffOn_prod (fun a _ => S.hc a.castSucc 1)

theorem hDrb : ContDiffOn ℝ ∞ (fun x => star (Dr (r := r) x)) S.U := by
  have h : ContDiffOn ℝ ∞ (fun x => ∏ a : Fin r, coef a.castSucc 4 x) S.U :=
    contDiffOn_prod (fun a _ => S.hc a.castSucc 4)
  exact h.congr (fun x _ => by simp [Dr, cOf, coef])

theorem hdivGG (c : ℂ) (i : Fin 6) :
    ContDiffOn ℝ ∞ (fun x => c * coef (Fin.last r) i x / GG S.T S.T' x) S.U :=
  ((contDiffOn_const.mul (S.hc (Fin.last r) i)).mul S.hGGi).congr (fun _ _ => div_eq_mul_inv _ _)

theorem cf_Ahat (hf : S.AH f) (Y : ℂ) : CommF S.U f (Formalism.MainNotions.S.LevR.Ahat (E := E) r Y) :=
  (CommF.mulF S.hDr).comp (S.cf_vv hf Y r le_rfl 0)

theorem cf_AhatV (hf : S.HO f) (Y : ℂ) : CommF S.U f (Formalism.MainNotions.S.LevR.AhatV (E := E) r Y) :=
  (CommF.mulF S.hDrb).comp (S.cf_vvV hf Y r le_rfl 0)

theorem coefficient_function_level_raising (hf : S.AH f) (Y : ℂ) : CommF S.U f (Formalism.MainNotions.S.LevR.R0 r S.T S.T' S.h Y) :=
  (CommF.mulF (S.hDrb.mul S.hGG)).comp
    (((((S.cf_wirt hf (Fin.last r)).add (CommF.mulE S.h_sm)).neg.sub
      (CommF.mulF (S.hdivGG (Y + 1 / 2) 4))).comp
        (S.cf_vv hf Y r le_rfl 0)).add (S.cf_vv hf Y r le_rfl 1))

theorem cf_R0V (hf : S.HO f) (Y : ℂ) : CommF S.U f (Formalism.MainNotions.S.LevR.weightedMirrorLevelOperator r S.T S.T' S.hs Y) :=
  (CommF.mulF (S.hDr.mul S.hGG)).comp
    (((((S.cf_wirtBar hf (Fin.last r)).sub (CommF.mulE S.hs_sm)).sub
      (CommF.mulF (S.hdivGG (Y - 1 / 2) 1))).comp
        (S.cf_vvV hf Y r le_rfl 0)).add (S.cf_vvV hf Y r le_rfl 1))

theorem AH_of (hf : DifferentiableOn ℂ (fun x => star (f x)) S.U) : S.AH f := by
  have hd : ∀ x ∈ S.U, DifferentiableAt ℂ (fun y => star (f y)) x :=
    fun x hx => (hf x hx).differentiableAt (S.isOpen.mem_nhds hx)
  refine ⟨fun x hx => ?_, fun k x hx => wirt_antihol (hd x hx) k⟩
  have h1 := ((Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp x
    ((hd x hx).hasFDerivAt.restrictScalars ℝ)).differentiableAt
  have h2 : (⇑(Complex.conjCLE : ℂ →L[ℝ] ℂ) ∘ fun y => star (f y)) = f := by funext y; simp
  rwa [h2] at h1

theorem HO_of (hf : DifferentiableOn ℂ f S.U) : S.HO f := by
  have hd : ∀ x ∈ S.U, DifferentiableAt ℂ f x :=
    fun x hx => (hf x hx).differentiableAt (S.isOpen.mem_nhds hx)
  exact ⟨fun x hx => (hd x hx).restrictScalars ℝ, fun k x hx => wirtBar_hol (hd x hx) k⟩

end Setup

end Formalism.MainNotions.LevelRaisingOperators

namespace Formalism.MainNotions.LevelRaisingOperators

open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WirtingerDerivatives Formalism.MainNotions.S.LevR

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Base E} {r : ℕ}

structure RulesHyp (C : Ctx B r) (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E)
    (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) : Prop where
  isOpen : IsOpen C.Dom
  sub : ∀ x ∈ C.Dom, x ∈ OmX (r + 1)
  pos : ∀ x ∈ C.Dom, B.T * B.T' < Complex.normSq (zOf x)
  cls_sm : ∀ φ ∈ C.cls, ContDiffOn ℝ ∞ φ C.Dom
  h_sm : ContDiffOn ℝ ∞ h C.Dom
  hs_sm : ContDiffOn ℝ ∞ (C.fstar h) C.Dom
  h_c : ∀ x ∈ C.Dom, ∀ (a : Fin r) (v : ℂ), fderiv ℝ h x (Pi.single a.castSucc v) = 0
  hs_c : ∀ x ∈ C.Dom, ∀ (a : Fin r) (v : ℂ), fderiv ℝ (C.fstar h) x (Pi.single a.castSucc v) = 0
  SS_sm : ∀ l, ContDiffOn ℝ ∞ (SS l) C.Dom
  SSs_sm : ∀ l, ContDiffOn ℝ ∞ (C.fstar (SS l)) C.Dom
  SS_c : ∀ l, ∀ x ∈ C.Dom, ∀ (a : Fin r) (v : ℂ), fderiv ℝ (SS l) x (Pi.single a.castSucc v) = 0
  SSs_c : ∀ l, ∀ x ∈ C.Dom, ∀ (a : Fin r) (v : ℂ), fderiv ℝ (C.fstar (SS l)) x (Pi.single a.castSucc v) = 0
  nab_SS : ∀ l, ∀ x ∈ C.Dom, wirt (Fin.last r) (SS l) x + (h x).comp (SS l x) - (SS l x).comp (h x) =
    (-(star (zOf x) * (GG B.T B.T' x)⁻¹)) • SS l x
  nabs_SS : ∀ l, ∀ x ∈ C.Dom,
    -wirtBar (Fin.last r) (SS l) x + (C.fstar h x).comp (SS l x) - (SS l x).comp (C.fstar h x) =
    (-(zOf x * (GG B.T B.T' x)⁻¹)) • SS l x
  nab_SSs : ∀ l, ∀ x ∈ C.Dom,
    wirt (Fin.last r) (C.fstar (SS l)) x + (h x).comp (C.fstar (SS l) x) - (C.fstar (SS l) x).comp (h x) =
    (star (zOf x) * (GG B.T B.T' x)⁻¹) • C.fstar (SS l) x
  nabs_SSs : ∀ l, ∀ x ∈ C.Dom,
    -wirtBar (Fin.last r) (C.fstar (SS l)) x + (C.fstar h x).comp (C.fstar (SS l) x) -
      (C.fstar (SS l) x).comp (C.fstar h x) = (zOf x * (GG B.T B.T' x)⁻¹) • C.fstar (SS l) x

namespace RulesHyp

variable {C : Ctx B r} {h : (Fin (r + 1) → ℂ) → E →L[ℂ] E} {SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E}

def setup (H : RulesHyp C h SS) : Setup r E where
  U := C.Dom
  T := B.T
  T' := B.T'
  h := h
  hs := C.fstar h
  isOpen := H.isOpen
  sub := H.sub
  pos := H.pos
  h_sm := H.h_sm
  hs_sm := H.hs_sm
  h_c := H.h_c
  hs_c := H.hs_c

theorem opEq (H : RulesHyp C h SS) {O O' : Op (r + 1) E} {a a' : H.setup.Rg} (h1 : Rep H.setup.U O a)
    (h2 : Rep H.setup.U O' a') (e : a = a') : C.OpEq O O' :=
  fun φ hφ _ hx => Rep.eq h1 h2 e (H.cls_sm φ hφ) hx

end RulesHyp

open Formalism.FourierDecayAlt.R in

theorem stRules_of_core (C : Ctx B r) (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E)
    (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) (H : RulesHyp C h SS) :
    Formalism.MainNotions.S.UnitaryLevelOperators.stRules C h SS := by
  let S := H.setup
  have rA : ∀ Y, Rep S.U (Ahat (E := E) r Y) (S.lev.Ahat Y) := S.rep_Ahat
  have rR : ∀ Y, Rep S.U (R0 r B.T B.T' h Y) (S.lev.R0 Y) := S.level_raising_represented
  have rAv : ∀ Y, Rep S.U (AhatV (E := E) r Y) (S.lev.Ahatv Y) := S.rep_AhatV
  have rRv : ∀ Y, Rep S.U (weightedMirrorLevelOperator r B.T B.T' (C.fstar h) Y) (S.lev.R0v Y) := S.rep_R0V
  have rG : ∀ s : ℂ, Rep S.U (mulF (E := E) (fun x => Gfn B.T B.T' x ^ s)) (S.Gs s) :=
    fun s => (S.mul_Gs s).rep (fun _ _ => rfl)
  have mD : IsMul S.lev.D (Dr1 (r := r)) := S.mul_Dr.mul S.multiplier_coordinate
  have mDi : IsMul S.lev.Di (fun x => (zOf x)⁻¹ * (Dr x)⁻¹) := S.mul_zi.mul S.mul_Dri
  have mDb : IsMul S.lev.Db (fun x => star (Dr x) * star (zOf x)) := S.mul_Drb.mul S.mul_zb
  have mDbi : IsMul S.lev.Dbi (fun x => (star (zOf x))⁻¹ * (star (Dr x))⁻¹) := S.mul_zbi.mul S.mul_Drbi
  have mG : IsMul S.lev.G (fun x => Dr x * star (Dr x) * GG B.T B.T' x) := (S.mul_Dr.mul S.mul_Drb).mul S.mul_GG
  have rD : Rep S.U (mulF (E := E) (Dr1 (r := r))) S.lev.D := mD.rep (fun _ _ => rfl)
  have rDi : Rep S.U (mulF (E := E) (fun x => (Dr1 (r := r) x)⁻¹)) S.lev.Di :=
    mDi.rep (fun x _ => by simp only [Dr1]; rw [mul_inv_rev])
  have rDb : Rep S.U (mulF (E := E) (fun x => star (Dr1 (r := r) x))) S.lev.Db :=
    mDb.rep (fun x _ => by simp only [Dr1, star_mul'])
  have rDbi : Rep S.U (mulF (E := E) (fun x => (star (Dr1 (r := r) x))⁻¹)) S.lev.Dbi :=
    mDbi.rep (fun x _ => by simp only [Dr1, star_mul']; rw [mul_inv_rev])
  have rzi : Rep S.U (mulF (E := E) (fun x => (zOf (r := r) x)⁻¹)) S.lev.ζi := S.mul_zi.rep (fun _ _ => rfl)
  have rzbi : Rep S.U (mulF (E := E) (fun x => (star (zOf (r := r) x))⁻¹)) S.lev.ζbi :=
    S.mul_zbi.rep (fun _ _ => rfl)
  unfold Formalism.MainNotions.S.UnitaryLevelOperators.stRules
  intro A R Av Rv Gp Dm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro s Y
    obtain ⟨g1, g2, g3, g4⟩ := S.ruleG s Y
    exact ⟨H.opEq ((rG (-s)).comp ((rA Y).comp (rG s))) (rA (Y + s)) ((mul_assoc _ _ _).symm.trans g1),
      H.opEq ((rG (-s)).comp ((rR Y).comp (rG s))) (rR (Y + s)) ((mul_assoc _ _ _).symm.trans g2),
      H.opEq ((rG (-s)).comp ((rAv Y).comp (rG s))) (rAv (Y - s)) ((mul_assoc _ _ _).symm.trans g3),
      H.opEq ((rG (-s)).comp ((rRv Y).comp (rG s))) (rRv (Y - s)) ((mul_assoc _ _ _).symm.trans g4)⟩
  ·
    intro Y
    obtain ⟨d1, d2, d3, d4, -, -⟩ := Formalism.FourierDecayAlt.P.shiftConjugation S.Rg r S.lev Y
    refine ⟨H.opEq (rDi.comp ((rA Y).comp rD)) (rA (Y + 1)) ((mul_assoc _ _ _).symm.trans d1),
      H.opEq (rDi.comp ((rR Y).comp rD)) ((rR (Y + 1)).add
        ((((IsMul.const S.lev.TT).mul (S.mul_Drb.mul mDi)).rep (fun x _ => ?_)).comp (rA (Y + 1))))
        ((mul_assoc _ _ _).symm.trans (d2.trans (by simp only [mul_assoc]))),
      H.opEq (rDbi.comp ((rAv Y).comp rDb)) (rAv (Y - 1)) ((mul_assoc _ _ _).symm.trans d3),
      H.opEq (rDbi.comp ((rRv Y).comp rDb)) ((rRv (Y - 1)).sub
        ((((IsMul.const S.lev.TT).mul (S.mul_Dr.mul mDbi)).rep (fun x _ => ?_)).comp (rAv (Y - 1))))
        ((mul_assoc _ _ _).symm.trans (d4.trans (by simp only [mul_assoc])))⟩
    · show ((B.T * B.T' : ℝ) : ℂ) * star (Dr x) / Dr1 x = ((B.T * B.T' : ℝ) : ℂ) * (star (Dr x) * ((zOf x)⁻¹ * (Dr x)⁻¹))
      simp only [Dr1]; rw [div_eq_mul_inv, mul_inv_rev, mul_assoc]
    · show ((B.T * B.T' : ℝ) : ℂ) * Dr x / star (Dr1 x) = ((B.T * B.T' : ℝ) : ℂ) * (Dr x * ((star (zOf x))⁻¹ * (star (Dr x))⁻¹))
      simp only [Dr1, star_mul']; rw [div_eq_mul_inv, mul_inv_rev, mul_assoc]
  ·
    intro f hf Y
    have hA := S.AH_of hf
    exact ⟨fun φ hφ x hx => ((S.cf_Ahat hA Y).comm φ (H.cls_sm φ hφ) x hx).symm,
      fun φ hφ x hx => ((S.coefficient_function_level_raising hA Y).comm φ (H.cls_sm φ hφ) x hx).symm⟩
  ·
    intro f hf Y
    have hA := S.HO_of hf
    exact ⟨fun φ hφ x hx => ((S.cf_AhatV hA Y).comm φ (H.cls_sm φ hφ) x hx).symm,
      fun φ hφ x hx => ((S.cf_R0V hA Y).comm φ (H.cls_sm φ hφ) x hx).symm⟩
  ·
    intro l Y Sn Sa
    have fnsS : ∀ {e : (Fin (r + 1) → ℂ) → E →L[ℂ] E}, ContDiffOn ℝ ∞ e C.Dom →
        ∀ x ∈ S.lev.fns, x * fe S.U e = fe S.U e * x := by
      intro e he x hx
      obtain ⟨f, hf, rfl⟩ := S.fns_fn hx
      exact fn_fe_comm hf he
    have n1 := S.nab_fe (H.SS_sm l) (S.mul_zb.mul S.mul_GGi).neg (H.nab_SS l)
    have n2 := S.nabs_fe (H.SS_sm l) (S.multiplier_coordinate.mul S.mul_GGi).neg (H.nabs_SS l)
    have n3 := S.nab_fe (H.SSs_sm l) (S.mul_zb.mul S.mul_GGi) (H.nab_SSs l)
    have n4 := S.nabs_fe (H.SSs_sm l) (S.multiplier_coordinate.mul S.mul_GGi) (H.nabs_SSs l)
    rw [neg_mul, ← sub_eq_add_neg] at n1 n2
    obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ := Formalism.FourierDecayAlt.P.intertwinerConjugation S.Rg r S.lev
      (fe S.U (SS l)) (fe S.U (C.fstar (SS l)))
      (fnsS (H.SS_sm l)) (fun a => (S.euler_commute_mul_of_fderiv_eq_zero (H.SS_sm l) (H.SS_c l) a).eq) (fun a => (S.Pb_fe (H.SS_sm l) (H.SS_c l) a).eq)
      n1 n2
      (fnsS (H.SSs_sm l)) (fun a => (S.euler_commute_mul_of_fderiv_eq_zero (H.SSs_sm l) (H.SSs_c l) a).eq)
      (fun a => (S.Pb_fe (H.SSs_sm l) (H.SSs_c l) a).eq) n3 n4 Y
    have rSn : Rep S.U (SSnat (E := E) (SS l)) (S.lev.Drb * S.lev.Dri * fe S.U (SS l)) :=
      ((S.mul_Drb.mul S.mul_Dri).rep (fun x _ => div_eq_mul_inv _ _)).comp (Rep.of_good (good_mulE (H.SS_sm l)))
    have rSa : Rep S.U (mulF (E := E) (fun x => Dr x / star (Dr x)) ∘ mulE (C.fstar (SS l)))
        (fe S.U (C.fstar (SS l)) * (S.lev.Dr * S.lev.Drbi)) :=
      (((S.mul_Dr.mul S.mul_Drbi).rep (fun x _ => div_eq_mul_inv _ _)).comp
        (Rep.of_good (good_mulE (H.SSs_sm l)))).cast ((S.mul_Dr.mul S.mul_Drbi).comm_fe (H.SSs_sm l))
    exact ⟨⟨H.opEq ((rA Y).comp rSn) (rSn.comp (rA (Y - 1))) s1, H.opEq ((rR Y).comp rSn) (rSn.comp (rR (Y - 1))) s2,
        H.opEq ((rAv Y).comp rSn) (rSn.comp (rAv (Y - 1))) s3, H.opEq ((rRv Y).comp rSn) (rSn.comp (rRv (Y - 1))) s4⟩,
      ⟨H.opEq ((rA Y).comp rSa) (rSa.comp (rA (Y + 1))) s5, H.opEq ((rR Y).comp rSa) (rSa.comp (rR (Y + 1))) s6,
        H.opEq ((rAv Y).comp rSa) (rSa.comp (rAv (Y + 1))) s7, H.opEq ((rRv Y).comp rSa) (rSa.comp (rRv (Y + 1))) s8⟩⟩
  ·
    intro Y zi zbi
    obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := Formalism.FourierDecayAlt.P.inverseCommutators S.Rg r S.lev Y
    refine ⟨H.opEq (rzbi.comp (rA Y)) ((rA Y).comp rzbi) i1, H.opEq (rzbi.comp (rR Y)) ((rR Y).comp rzbi) i2,
      H.opEq (rzbi.comp (rAv Y)) ((rAv Y).comp rzbi) i3,
      H.opEq (((rRv Y).comp rzbi).sub (rzbi.comp (rRv Y)))
        ((((mG.mul mDbi).mul mDbi).rep (fun x _ => ?_)).comp (rAv Y)).neg i4,
      H.opEq (rzi.comp (rA Y)) ((rA Y).comp rzi) i5, H.opEq (rzi.comp (rAv Y)) ((rAv Y).comp rzi) i6,
      H.opEq (rzi.comp (rRv Y)) ((rRv Y).comp rzi) i7,
      H.opEq (((rR Y).comp rzi).sub (rzi.comp (rR Y)))
        ((((mG.mul mDi).mul mDi).rep (fun x _ => ?_)).comp (rA Y)) i8⟩
    · simp only [Gfn, Dr1, star_mul']
      rw [← Complex.mul_conj, div_eq_mul_inv, pow_two, mul_inv_rev, mul_inv_rev]
      simp only [Complex.star_def]; ring
    · simp only [Gfn, Dr1]
      rw [← Complex.mul_conj, div_eq_mul_inv, pow_two, mul_inv_rev, mul_inv_rev]
      simp only [Complex.star_def]; ring

theorem level_rules_of_known (C : Ctx B r) (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E)
    (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) (H : RulesHyp C h SS) :
    Formalism.MainNotions.RadialRules.LevelOperatorRules C h SS := stRules_of_core C h SS H

end Formalism.MainNotions.LevelRaisingOperators

namespace Formalism.MainNotions.LevelRaisingOperators

open Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem isOpen_BDom (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : IsOpen (BDom k r z z') := by
  have h : BDom k r z z' = OmX (r + 1) ∩ {x | Tz k r z * Tz k r z' < Complex.normSq (zOf x)} := rfl
  rw [h]
  exact (Formalism.QuantumDeterminants.WirtingerDerivatives.isOpen_omX (r + 1)).inter
    (isOpen_lt continuous_const (Complex.continuous_normSq.comp (continuous_apply (Fin.last r))))

theorem contDiffAt_bc (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hsec : IsSection k r z z' μsec) (x : Fin (r + 1) → ℂ) (hx : x ∈ BDom k r z z') :
    ContDiffAt ℝ ∞ (fun y : Fin (r + 1) → ℂ => bigCell k r (cOf y) (μsec (zOf y))) x := by
  have hc : ∀ a : Fin r, ContDiffAt ℝ ∞ (fun y : Fin (r + 1) → ℂ => cOf y a) x := fun a =>
    (contDiff_apply ℝ ℂ a.castSucc).contDiffAt
  have hz : ContDiffAt ℝ ∞ (fun y : Fin (r + 1) → ℂ => zOf y) x := (contDiff_apply ℝ ℂ (Fin.last r)).contDiffAt
  have hS : {ζ : ℂ | Tz k r z * Tz k r z' < Complex.normSq ζ} ∈ 𝓝 (zOf x) :=
    (isOpen_lt continuous_const Complex.continuous_normSq).mem_nhds hx.2
  refine contDiffAt_pi' fun i => contDiffAt_pi' fun j => ?_
  by_cases hj : j.val < r
  · simp only [bigCell, dif_pos hj]
    split_ifs
    · exact hc _
    · exact contDiffAt_const
  · by_cases hj2 : j.val ≤ r + k
    · simp only [bigCell, dif_neg hj, dif_pos hj2]
      split_ifs with hi
      · exact ((hsec.1 _ _).contDiffAt hS).comp x hz
      · exact contDiffAt_const
    · simp only [bigCell, dif_neg hj, dif_neg hj2]
      split_ifs
      · refine ContDiffAt.inv ((Complex.conjCLE.contDiff.contDiffAt).comp x (hc _)) ?_
        exact star_ne_zero.2 (hx.1 _)
      · exact contDiffAt_const

theorem Btr_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ)
    (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hsec : IsSection k r z z' μsec)
    (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → E) (hJ : SmoothOnH (Hpk k r) J) :
    ContDiffOn ℝ ∞ (Btr k r z z' μsec J) (BDom k r z z') := by
  intro x hB
  apply ContDiffAt.contDiffWithinAt
  have hmem : ∀ y ∈ BDom k r z z', bigCell k r (cOf y) (μsec (zOf y)) ∈ UH (Hpk k r) := fun y hy =>
    Formalism.QuantumDeterminants.bigCellMem k r _ _ (fun a => hy.1 a.castSucc) (hsec.2 (zOf y) hy.2).1
  obtain ⟨U, F, hU, hxU, hF, hJF⟩ := hJ _ (hmem x hB)
  have hβ := contDiffAt_bc k r z z' μsec hsec x hB
  have hev : Btr k r z z' μsec J =ᶠ[𝓝 x] fun y =>
      ((((∏ a : Fin r, ‖cOf y a‖ ^ (Mdim k r a - 1)) *
        (Complex.normSq (zOf y) - Tz k r z * Tz k r z') ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) •
      F (bigCell k r (cOf y) (μsec (zOf y)))) := by
    filter_upwards [(isOpen_BDom k r z z').mem_nhds hB,
      hβ.continuousAt.preimage_mem_nhds (hU.mem_nhds hxU)] with y hy hyU
    unfold Btr
    rw [if_pos hy, hJF _ hyU (hmem y hy)]
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  apply ContDiffAt.smul
  · refine Complex.ofRealCLM.contDiff.contDiffAt.comp x (ContDiffAt.mul ?_ ?_)
    · refine contDiffAt_prod fun a _ => ContDiffAt.pow ?_ _
      exact ContDiffAt.norm ℝ (contDiff_apply ℝ ℂ a.castSucc).contDiffAt (hB.1 a.castSucc)
    · refine ContDiffAt.rpow_const_of_ne ?_ (ne_of_gt (sub_pos.2 hB.2))
      refine ContDiffAt.sub ?_ contDiffAt_const
      simp only [Complex.normSq_eq_norm_sq]
      exact ContDiffAt.norm_sq ℝ (contDiff_apply ℝ ℂ (Fin.last r)).contDiffAt
  · exact (hF.contDiffAt (hU.mem_nhds hxU)).comp x hβ

theorem Img_smooth (L : Lev) (h : L.Std) : ∀ φ ∈ L.Img, ContDiffOn ℝ ∞ φ L.BD := by
  rintro φ ⟨J, ⟨hJ, -⟩, rfl⟩
  exact Btr_smooth (L.k0 + 1) L.r L.z L.z' L.μsec h.2.2.2.2 J hJ.1

end Formalism.MainNotions.LevelRaisingOperators

namespace Formalism.MainNotions.LevelRaisingOperators

open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WirtingerDerivatives Formalism.MainNotions.S.LevR Formalism.MainNotions.S.TopsChoicePartA

theorem pullZ_c {r : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (e : (Fin 1 → ℂ) → F)
    {x : Fin (r + 1) → ℂ} (hd : DifferentiableAt ℝ (pullZ (r := r) e) x) (a : Fin r) (v : ℂ) :
    fderiv ℝ (pullZ (r := r) e) x (Pi.single a.castSucc v) = 0 := by
  rw [← hd.lineDeriv_eq_fderiv, lineDeriv]
  have : (fun t : ℝ => pullZ (r := r) e (x + t • (Pi.single a.castSucc v : Fin (r + 1) → ℂ))) = fun _ => pullZ e x := by
    funext t
    simp [pullZ, zOf, Setup.last_ne a]
  rw [this]; simp

structure RulesOpen (Lt : Lev) (h : (Fin 1 → ℂ) → Lt.Hom →L[ℂ] Lt.Hom)
    (SS : Fin Lt.k0 → (Fin 1 → ℂ) → Lt.Hom →L[ℂ] Lt.Hom) : Prop where
  h_sm : ContDiffOn ℝ ∞ (pullZ (r := Lt.r) h) Lt.BD
  hs_sm : ContDiffOn ℝ ∞ (pullZ (r := Lt.r) (fun y => hsAdj Lt (h y))) Lt.BD
  SS_sm : ∀ l, ContDiffOn ℝ ∞ (pullZ (r := Lt.r) (SS l)) Lt.BD
  SSs_sm : ∀ l, ContDiffOn ℝ ∞ (pullZ (r := Lt.r) (fun y => hsAdj Lt (SS l y))) Lt.BD
  nab_SS : ∀ l, ∀ x ∈ Lt.BD, wirt (Fin.last Lt.r) (pullZ (SS l)) x + (pullZ h x).comp (pullZ (SS l) x) -
    (pullZ (SS l) x).comp (pullZ h x) = (-(star (zOf x) * (GG Lt.T Lt.T' x)⁻¹)) • pullZ (SS l) x
  nabs_SS : ∀ l, ∀ x ∈ Lt.BD, -wirtBar (Fin.last Lt.r) (pullZ (SS l)) x +
    (hsAdj Lt (pullZ h x)).comp (pullZ (SS l) x) - (pullZ (SS l) x).comp (hsAdj Lt (pullZ h x)) =
    (-(zOf x * (GG Lt.T Lt.T' x)⁻¹)) • pullZ (SS l) x
  nab_SSs : ∀ l, ∀ x ∈ Lt.BD, wirt (Fin.last Lt.r) (pullZ (fun y => hsAdj Lt (SS l y))) x +
    (pullZ h x).comp (hsAdj Lt (pullZ (SS l) x)) - (hsAdj Lt (pullZ (SS l) x)).comp (pullZ h x) =
    (star (zOf x) * (GG Lt.T Lt.T' x)⁻¹) • hsAdj Lt (pullZ (SS l) x)
  nabs_SSs : ∀ l, ∀ x ∈ Lt.BD, -wirtBar (Fin.last Lt.r) (pullZ (fun y => hsAdj Lt (SS l y))) x +
    (hsAdj Lt (pullZ h x)).comp (hsAdj Lt (pullZ (SS l) x)) -
      (hsAdj Lt (pullZ (SS l) x)).comp (hsAdj Lt (pullZ h x)) =
    (zOf x * (GG Lt.T Lt.T' x)⁻¹) • hsAdj Lt (pullZ (SS l) x)

theorem RulesOpen.hyp {Lt : Lev} {h : (Fin 1 → ℂ) → Lt.Hom →L[ℂ] Lt.Hom}
    {SS : Fin Lt.k0 → (Fin 1 → ℂ) → Lt.Hom →L[ℂ] Lt.Hom} (K : RulesOpen Lt h SS) (hS : Lt.Std)
    (u u' : Fin (Lt.k0 + 1) → ℝ) (I : Set ℝ) (hr : Lt.r + 0 = Lt.r)
    (R : ℂ → Matrix (Fin 2) (Fin 2) (Lt.down Lt.r 0 hr).POp) :
    RulesHyp (ctx0 Lt u u' I hr R) (pullZ h) (fun l => pullZ (SS l)) where
  isOpen := isOpen_BDom _ _ _ _
  sub := fun _ hx => hx.1
  pos := fun _ hx => hx.2
  cls_sm := fun φ hφ => Img_smooth Lt hS φ hφ
  h_sm := K.h_sm
  hs_sm := K.hs_sm
  h_c := fun x hx a v => pullZ_c h (diff_of_reg (cda (isOpen_BDom _ _ _ _) K.h_sm hx)) a v
  hs_c := fun x hx a v => pullZ_c _ (diff_of_reg (cda (isOpen_BDom _ _ _ _) K.hs_sm hx)) a v
  SS_sm := K.SS_sm
  SSs_sm := K.SSs_sm
  SS_c := fun l x hx a v => pullZ_c _ (diff_of_reg (cda (isOpen_BDom _ _ _ _) (K.SS_sm l) hx)) a v
  SSs_c := fun l x hx a v => pullZ_c _ (diff_of_reg (cda (isOpen_BDom _ _ _ _) (K.SSs_sm l) hx)) a v
  nab_SS := K.nab_SS
  nabs_SS := K.nabs_SS
  nab_SSs := K.nab_SSs
  nabs_SSs := K.nabs_SSs

theorem level_rules_base_context_of_known (Lt : Lev) (u u' : Fin (Lt.k0 + 1) → ℝ) (I : Set ℝ) (hr : Lt.r + 0 = Lt.r)
    (R : ℂ → Matrix (Fin 2) (Fin 2) (Lt.down Lt.r 0 hr).POp) (h : (Fin 1 → ℂ) → Lt.Hom →L[ℂ] Lt.Hom)
    (SS : Fin Lt.k0 → (Fin 1 → ℂ) → Lt.Hom →L[ℂ] Lt.Hom) (hS : Lt.Std) (K : RulesOpen Lt h SS) :
    Formalism.MainNotions.S.UnitaryLevelOperators.stRules (ctx0 Lt u u' I hr R) (pullZ h) (fun l => pullZ (SS l)) :=
  stRules_of_core _ _ _ (K.hyp hS u u' I hr R)

open Formalism.MainNotions.S.UnitaryLevelOperators in

def stLevelOpen (C Cv C1 C2 : ℝ) : Prop :=
  ∀ (Lt : Lev) (u u' : Fin (Lt.k0 + 1) → ℝ) (I : Set ℝ) (hr : Lt.r + 0 = Lt.r),
    HypC Lt u u' I → HypC (Lt.down Lt.r 0 hr) u u' I →
    ∀ R : ℂ → Matrix (Fin 2) (Fin 2) (Lt.down Lt.r 0 hr).POp, (Lt.down Lt.r 0 hr).IsRadQQ R →
    ∃ (h : (Fin 1 → ℂ) → Lt.Hom →L[ℂ] Lt.Hom) (SS : Fin Lt.k0 → (Fin 1 → ℂ) → Lt.Hom →L[ℂ] Lt.Hom),
      (∀ (hh : (Lt.down Lt.r 0 hr).Haar) (A : ℝ) (mm : ℕ), hh.Ok → Big C Lt 0 A mm →
        stLevR (ctxR Lt u u' I hr R ((Lt.down Lt.r 0 hr).ImgK hh A mm)) h SS) ∧
      stLev0 (ctx0 Lt u u' I hr R) (gctxOf Lt) (pullZ h) (fun l => pullZ (SS l)) ∧
      RulesOpen Lt h SS ∧
      stProd (ctx0 Lt u u' I hr R) Cv (pullZ h) (fun l => pullZ (SS l)) ∧
      (∀ (hh : (Lt.down Lt.r 0 hr).Haar) (A : ℝ) (mm : ℕ), hh.Ok →
        stFrameR (ctxR Lt u u' I hr R ((Lt.down Lt.r 0 hr).ImgK hh A mm)) (fun N => Big C Lt N A mm) h SS) ∧
      stFrameG (ctxR Lt u u' I hr R (Lt.down Lt.r 0 hr).Img) (ctx0 Lt u u' I hr R) (Lt.liftDown Lt.r 0 hr)
        pullZ h SS ∧
      stRes (ctxR Lt u u' I hr R (Lt.down Lt.r 0 hr).Img) C1 C2 SS

theorem stLevel_of_open {C Cv C1 C2 : ℝ}
    (hOm : ∀ Lt : Lev, Lt.Std → Formalism.MainNotions.S.UnitaryLevelOperators.stOm (Lt.k0 + 1) Lt.r Lt.z Lt.z') (H : stLevelOpen C Cv C1 C2) :
    Formalism.MainNotions.S.UnitaryLevelOperators.stLevel C Cv C1 C2 := by
  intro Lt u u' I hr h1 h2 R hR
  obtain ⟨h, SS, a, b, c, d, e, f, g⟩ := H Lt u u' I hr h1 h2 R hR
  exact ⟨h, SS, a, b, level_rules_base_context_of_known Lt u u' I hr R h SS h1.1 c, d, e, f,
    hOm Lt h1.1, g⟩

theorem level_statement_of_open (D : Formalism.BasicNotions.D7) {C Cv C1 C2 : ℝ}
    (hOm : ∀ Lt : Lev, Lt.Std → Formalism.MainNotions.S.UnitaryLevelOperators.stOm (Lt.k0 + 1) Lt.r Lt.z Lt.z') (H : stLevelOpen C Cv C1 C2) :
    Formalism.MainNotions.RadialRules.aux₃ D C Cv C1 C2 := stLevel_of_open hOm H

end Formalism.MainNotions.LevelRaisingOperators

namespace Formalism.MainNotions.LevelRaisingOperators

open Formalism.REAL Formalism.QuantumDeterminants

theorem stQ_cap_of_core : Formalism.MainNotions.S.UnitaryLevelOperators.stQ_cap :=
  ⟨capCentralH, capLeftH, capHWH, capComatrix, qMinorLeft, glRelAd, eabHGl, eabHTransport⟩

theorem stQ_anti_of_core : Formalism.MainNotions.S.UnitaryLevelOperators.stQ_anti := by
  intro n t ε E _ _ H P Q f a b σ u g hQP hPQ hH hf hg
  have hsm := ioh_smooth ε H P Q f hPQ hH hf
  have hg' := ioh_inUJ ε H P Q g hPQ hH hg
  obtain ⟨x, hx⟩ := io_rep_mk hsm
  have hR := ioh_repr (ε := ε) (E := E) P Q
  have key : ∀ α β : Fin t → Fin n,
      qminorOp (EabH H) α β u f g = (qminor (iohE ε E P Q) α β u x).1 ⟨_, hg'⟩ := by
    intro α β
    rw [ioh_qminor ε H P Q hQP hPQ hH]
    exact ioh_qminor_rep hR α β u hx _ hg'
  constructor
  · rw [key, key, qSkewRow (Module.End ℂ (ioS ε E)) n t (iohE ε E P Q) a b σ u, Module.End.mul_apply,
      Module.End.intCast_apply, ← Int.cast_smul_eq_zsmul ℂ]
    rfl
  · rw [key, key, qSkewCol (Module.End ℂ (ioS ε E)) n t (iohE ε E P Q) (ioh_gl glRelAd P Q hQP) a b σ u,
      Module.End.mul_apply, Module.End.intCast_apply, ← Int.cast_smul_eq_zsmul ℂ]
    rfl

theorem level_quotient_capacity_of_known (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.RadialRules.adm3 D := stQ_cap_of_core
theorem radial_archimedean_signature_matching (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.RadialRules.ArchimedeanSignatureMatching D := stQ_anti_of_core
theorem quotient_capacity_of_known (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.ChoiceOfModulusAndDiscriminant.adm3 D := stQ_cap_of_core
theorem quotient_antitone_of_known (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.ChoiceOfModulusAndDiscriminant.ArchimedeanSignatureMatching D := stQ_anti_of_core

end Formalism.MainNotions.LevelRaisingOperators
