import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CurveComp
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PublishedIntClosHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SpanSteps

set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeTensorProduct

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.PullbackSections
open scoped TensorProduct

section BaseChange

variable {K L : Type} [Field K] [Field L] [Algebra K L] {σ : K →+* ℂ} {σ' : L →+* ℂ}
  {C W : Type} [AddCommGroup C] [Module K C] [AddCommGroup W] [Module ℂ W]

def bcBil (σ' : L →+* ℂ) (f : C →ₛₗ[σ] W) : L →+ C →+ W where
  toFun t := (DistribSMul.toAddMonoidHom W (σ' t)).comp f.toAddMonoidHom
  map_zero' := by ext F : 1; simp
  map_add' s t := by ext F : 1; simp [add_smul]

theorem bcBil_apply (σ' : L →+* ℂ) (f : C →ₛₗ[σ] W) (t : L) (x : C) : bcBil σ' f t x = σ' t • f x := rfl

def bcAdd (hσ : ∀ a, σ' (algebraMap K L a) = σ a) (f : C →ₛₗ[σ] W) : L ⊗[K] C →+ W :=
  TensorProduct.liftAddHom (bcBil σ' f) fun a t x => by
    rw [bcBil_apply, bcBil_apply, LinearMap.map_smulₛₗ, Algebra.smul_def a t, map_mul, hσ a, smul_smul, mul_comm]

theorem bcAdd_tmul (hσ : ∀ a, σ' (algebraMap K L a) = σ a) (f : C →ₛₗ[σ] W) (t : L) (x : C) :
    bcAdd hσ f (t ⊗ₜ x) = σ' t • f x := rfl

def bcMap (hσ : ∀ a, σ' (algebraMap K L a) = σ a) (f : C →ₛₗ[σ] W) : L ⊗[K] C →ₛₗ[σ'] W where
  toFun := bcAdd hσ f
  map_add' := map_add _
  map_smul' s x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul t F => rw [TensorProduct.smul_tmul', bcAdd_tmul, bcAdd_tmul, smul_eq_mul, map_mul, mul_smul]
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

end BaseChange

variable {D : D7}

section Forms

variable (T : Core D) (j : ℕ)

abbrev Cf (w : WeightFamilies.Wt D j) : Type := cutR T.C j w

instance instAddCommGroupCf (w : WeightFamilies.Wt D j) : AddCommGroup (Cf T j w) := Submodule.addCommGroup _

instance instModuleCf (w : WeightFamilies.Wt D j) : Module T.Q.c.F (Cf T j w) := Submodule.module _

abbrev la (w : WeightFamilies.Wt D j) : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (T.X₀ j k).Ψ D.R.r := laU (T.U j T.σ₀) (wtA w) w.n

def rd (w : WeightFamilies.Wt D j) : Cf T j w →ₛₗ[T.σ₀] FDSec (T.X₀ j) :=
  (rdU (T.U j T.σ₀)).comp (cutR T.C j w).subtype

def RdCusp (w : WeightFamilies.Wt D j) : Prop :=
  ∀ (F : Cf T j w) k, rd T j w F k ∈ (T.X₀ j k).SS (la T j w k)

def RdIndep (w : WeightFamilies.Wt D j) : Prop := IndepToC (rd T j w)

end Forms

section Generic

variable (T : Core D) (j N : ℕ)

abbrev KT : Type := FractionRing (MvPolynomial (Gaps.EtaleWeightGaps.Idx D j N) T.Q.c.F)

def tv (p : Gaps.EtaleWeightGaps.Idx D j N) : KT T j N :=
  algebraMap (MvPolynomial (Gaps.EtaleWeightGaps.Idx D j N) T.Q.c.F) (KT T j N) (MvPolynomial.X p)

variable {T j N}

def IsExt (σ' : KT T j N →+* ℂ) : Prop := ∀ a : T.Q.c.F, σ' (algebraMap T.Q.c.F (KT T j N) a) = T.σ₀ a

variable (T j N) in

def ExtExists : Prop := ∃ σ' : KT T j N →+* ℂ, IsExt σ'

variable (T j N) in

abbrev CfT (w : WeightFamilies.Wt D j) : Type := KT T j N ⊗[T.Q.c.F] Cf T j w

instance instModuleCfT (w : WeightFamilies.Wt D j) : Module (KT T j N) (CfT T j N w) := TensorProduct.leftModule

def rdGen {σ' : KT T j N →+* ℂ} (hσ : IsExt σ') (w : WeightFamilies.Wt D j) : CfT T j N w →ₛₗ[σ'] FDSec (T.X₀ j) :=
  bcMap hσ (rd T j w)

theorem rdGen_tmul {σ' : KT T j N →+* ℂ} (hσ : IsExt σ') (w : WeightFamilies.Wt D j) (t : KT T j N) (F : Cf T j w) :
    rdGen hσ w (t ⊗ₜ F) = σ' t • rd T j w F := rfl

def genSec {wL : WeightFamilies.Wt D j} (w : Fin N → Cf T j wL) (i : Fin (WeightFamilies.dimY D j + 1)) : CfT T j N wL :=
  ∑ k, tv T j N (i, k) ⊗ₜ w k

def rdSec (σ' : KT T j N →+* ℂ) {wL : WeightFamilies.Wt D j} (w : Fin N → Cf T j wL) (i : Fin (WeightFamilies.dimY D j + 1)) :
    FDSec (T.X₀ j) :=
  ∑ k, σ' (tv T j N (i, k)) • rd T j wL (w k)

def GenRd {σ' : KT T j N →+* ℂ} (hσ : IsExt σ') (w : WeightFamilies.Wt D j) : Prop :=
  (∀ (x : CfT T j N w) k, rdGen hσ w x k ∈ (T.X₀ j k).SS (la T j w k)) ∧ IndepToC (rdGen hσ w)

end Generic

section Cusps

variable (T : Core D) (j : ℕ)

def Deep (w : WeightFamilies.Wt D j) (c : ℝ) (P : FDSec (T.X₀ j)) : Prop :=
  ∀ k ξ, (T.X₀ j k).IsIso ξ → ∀ ν : (T.X₀ j k).Ψ → ℝ, ∑ τ, ν τ ≤ c →
    ∀ x ∈ (T.X₀ j k).dom, (T.X₀ j k).fj (la T j w k) ξ ν (P k) x = 0

def DualIsLat : Prop :=
  ∀ (cu : T.Cu j) (v : Fin (WeightFamilies.rho D j) → D.host.E),
    v ∈ WeightFamilies.dualZ D (T.Xc j cu) ↔ ∑ i, v i • cu.1.2.e i ∈ (T.X₀ j cu.1.1).Λ

def CoefZero (cu : T.Cu j) (χ : Matrix (Fin (WeightFamilies.rho D j)) (Fin (WeightFamilies.rho D j)) D.host.E)
    (P : FDSec (T.X₀ j)) : Prop :=
  ∀ x ∈ (T.X₀ j cu.1.1).dom,
    FJ.coefFn (FJ.zAct (T.X₀ j cu.1.1) cu.1.2) (FJ.phZ (T.X₀ j cu.1.1) cu.1.2 χ) (P cu.1.1) x = 0

def MaxCuspsC (w : WeightFamilies.Wt D j) (c : ℝ) : Prop :=
  ∀ P : FDSec (T.X₀ j), IsHolCusp (T.X₀ j) (la T j w) P →
    (Deep T j w c P ↔ ∀ (cu : T.Cu j) (χ : WeightFamilies.ExpoSet D (T.Xc j cu)),
      (∃ v : Fin (WeightFamilies.rho D j) → D.host.E, v ≠ 0 ∧ ∑ i, v i • cu.1.2.e i ∈ (T.X₀ j cu.1.1).Λ ∧
        WeightFamilies.trF D (WeightFamilies.hform D χ.1 v v) ≤ c) → CoefZero T j cu χ.1 P) ∧
    ((∀ k, ∀ x ∈ (T.X₀ j k).dom, P k x = 0) ↔
      ∀ (cu : T.Cu j) (χ : WeightFamilies.ExpoSet D (T.Xc j cu)), CoefZero T j cu χ.1 P)

variable {T} (h : LawsCore T)

def DeepIff (CR Tn c : ℝ) (ka : WeightFamilies.Wt D j) : Prop :=
  ∀ F : Cf T j ka, F ∈ WeightFamilies.MggK (recB h) CR Tn c j ka ↔ Deep T j ka (WeightFamilies.c1 D CR Tn c j) (rd T j ka F)

def DeepDescends (CR Tn c : ℝ) (ka : WeightFamilies.Wt D j) : Prop :=
  ∀ P ∈ Submodule.span ℂ (Set.range (rd T j ka)), Deep T j ka (WeightFamilies.c1 D CR Tn c j) P →
    P ∈ Submodule.span ℂ (rd T j ka '' {F : Cf T j ka | F ∈ WeightFamilies.MggK (recB h) CR Tn c j ka})

def TieReadAt : Prop :=
  (∀ w, RdCusp T j w ∧ RdIndep T j w) ∧
  (∀ N, ExtExists T j N ∧ ∀ (σ' : KT T j N →+* ℂ) (hσ : IsExt σ') w, GenRd hσ w) ∧
  ∀ CR Tn c ka, DeepIff j h CR Tn c ka

end Cusps

def TieRead : Prop :=
  ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ), InR D j → TieReadAt j h.toLawsCore

def MaxCusps : Prop :=
  ∀ (D : D7) (T : Top D), LawsP T → ∀ j, InR D j → DualIsLat T.toCore j ∧ ∀ w c, MaxCuspsC T.toCore j w c

example (T : Core D) (j : ℕ) (w : WeightFamilies.Wt D j) (c : ℝ) (P : FDSec (T.X₀ j)) (hP : IsHolCusp (T.X₀ j) (la T j w) P) :
    Deep T j w c P ↔ ∀ k, P k ∈ (T.X₀ j k).SSgt (la T j w k) c :=
  ⟨fun hd k => ⟨hP k, hd k⟩, fun hd k => (hd k).2⟩

example (T : Core D) (j N : ℕ) {σ' : KT T j N →+* ℂ} (hσ : IsExt σ') (w : WeightFamilies.Wt D j) (F : Cf T j w) :
    rdGen hσ w (1 ⊗ₜ F) = rd T j w F := by
  rw [rdGen_tmul, map_one, one_smul]

end GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeTensorProduct
