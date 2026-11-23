import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger

variable {D : D7}

abbrev Rep (S T : HSp D) : Type := GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)

abbrev Chr (D : D7) : Type := (AE D)ˣ →* Circle

def prodSpan {X X₁ X₂ : Type} (e : X → X₁ × X₂) (P₁ : (X₁ → ℂ) → Prop) (P₂ : (X₂ → ℂ) → Prop) : Submodule ℂ (X → ℂ) :=
  Submodule.span ℂ {g | ∃ f₁ f₂, P₁ f₁ ∧ P₂ f₂ ∧ g = fun w => f₁ (e w).1 * f₂ (e w).2}

def UnifLimit {X : Type} (M : Submodule ℂ (X → ℂ)) (f : X → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ g ∈ M, ∀ w, ‖f w - g w‖ ≤ ε

structure TensorSource (ψ : AddChar (AF D.host.F) ℂ) {S A B : HSp D} (d : OrthDec S A B) (T : HSp D) : Prop where

  box_theta : ∀ fA fB, IsThetaFunO ψ A T fA → IsThetaFunO ψ B T fB → IsThetaFunO ψ S T (d.boxS T fA fB)

  box_zero : ∀ fA fB, d.boxS T fA fB 0 = fA 0 * fB 0

  heis_box : ∀ fA fB,
    (∀ u, heisO ψ S T ((d.resS T).symm (u, 0)) (d.boxS T fA fB) = d.boxS T (heisO ψ A T u fA) fB) ∧
    ∀ v, heisO ψ S T ((d.resS T).symm (0, v)) (d.boxS T fA fB) = d.boxS T fA (heisO ψ B T v fB)

  slice_theta : ∀ f, IsThetaFunO ψ S T f →
    (∀ v, IsThetaFunO ψ A T fun u => f ((d.resS T).symm (u, v))) ∧
    ∀ u, IsThetaFunO ψ B T fun v => f ((d.resS T).symm (u, v))

  dense : ∀ f, IsThetaFunO ψ S T f → UnifLimit (prodSpan (d.resS T) (IsThetaFunO ψ A T) (IsThetaFunO ψ B T)) f

  om_box : ∀ (χA χB χT : Chr D) (omS : Rep S T) (omA : Rep A T) (omB : Rep B T),
    IsWeilDatumO ψ S T (χA * χB) χT omS → IsWeilDatumO ψ A T χA χT omA → IsWeilDatumO ψ B T χB χT omB →
    ∀ a b h fA fB, IsThetaFunO ψ A T fA → IsThetaFunO ψ B T fB →
      omS (d.emb (a, b), h) (d.boxS T fA fB) = d.boxS T (omA (a, h) fA) (omB (b, h) fB)

  om_slice : ∀ (χA χB χT : Chr D) (omS : Rep S T) (omA : Rep A T) (omB : Rep B T),
    IsWeilDatumO ψ S T (χA * χB) χT omS → IsWeilDatumO ψ A T χA χT omA → IsWeilDatumO ψ B T χB χT omB →
    ∀ a b h f, IsThetaFunO ψ S T f → ∀ v,
      IsThetaFunO ψ A T (fun u' => omB (b, h) (fun v' => f ((d.resS T).symm (u', v'))) v) ∧
      ∀ u, omS (d.emb (a, b), h) f ((d.resS T).symm (u, v)) =
        omA (a, h) (fun u' => omB (b, h) (fun v' => f ((d.resS T).symm (u', v'))) v) u

structure TensorTarget (ψ : AddChar (AF D.host.F) ℂ) {T A B : HSp D} (d : OrthDec T A B) (S : HSp D) : Prop where

  box_theta : ∀ fA fB, IsThetaFunO ψ S A fA → IsThetaFunO ψ S B fB → IsThetaFunO ψ S T (d.boxT S fA fB)

  box_zero : ∀ fA fB, d.boxT S fA fB 0 = fA 0 * fB 0

  heis_box : ∀ fA fB,
    (∀ u, heisO ψ S T ((d.resT S).symm (u, 0)) (d.boxT S fA fB) = d.boxT S (heisO ψ S A u fA) fB) ∧
    ∀ v, heisO ψ S T ((d.resT S).symm (0, v)) (d.boxT S fA fB) = d.boxT S fA (heisO ψ S B v fB)

  slice_theta : ∀ f, IsThetaFunO ψ S T f →
    (∀ v, IsThetaFunO ψ S A fun u => f ((d.resT S).symm (u, v))) ∧
    ∀ u, IsThetaFunO ψ S B fun v => f ((d.resT S).symm (u, v))

  dense : ∀ f, IsThetaFunO ψ S T f → UnifLimit (prodSpan (d.resT S) (IsThetaFunO ψ S A) (IsThetaFunO ψ S B)) f

  om_box : ∀ (χS χA χB : Chr D) (omT : Rep S T) (omA : Rep S A) (omB : Rep S B),
    IsWeilDatumO ψ S T χS (χA * χB) omT → IsWeilDatumO ψ S A χS χA omA → IsWeilDatumO ψ S B χS χB omB →
    ∀ g a b fA fB, IsThetaFunO ψ S A fA → IsThetaFunO ψ S B fB →
      omT (g, d.emb (a, b)) (d.boxT S fA fB) = d.boxT S (omA (g, a) fA) (omB (g, b) fB)

  om_slice : ∀ (χS χA χB : Chr D) (omT : Rep S T) (omA : Rep S A) (omB : Rep S B),
    IsWeilDatumO ψ S T χS (χA * χB) omT → IsWeilDatumO ψ S A χS χA omA → IsWeilDatumO ψ S B χS χB omB →
    ∀ g a b f, IsThetaFunO ψ S T f → ∀ v,
      IsThetaFunO ψ S A (fun u' => omB (g, b) (fun v' => f ((d.resT S).symm (u', v'))) v) ∧
      ∀ u, omT (g, d.emb (a, b)) f ((d.resT S).symm (u, v)) =
        omA (g, a) (fun u' => omB (g, b) (fun v' => f ((d.resT S).symm (u', v'))) v) u

def cj {X Y : Type} (e : Y → X) (f : X → ℂ) : Y → ℂ := fun y => starRingEnd ℂ (f (e y))

theorem cj_cj {X Y : Type} (e : Y → X) (e' : X → Y) (h : ∀ x, e (e' x) = x) (f : X → ℂ) : cj e' (cj e f) = f := by
  funext x; simp [cj, h]

def cjEnd {X Y : Type} (e : Y ≃ X) : Module.End ℂ (X → ℂ) →* Module.End ℂ (Y → ℂ) where
  toFun L :=
    { toFun := fun f => cj e (L (cj e.symm f))
      map_add' := fun f f' => by
        have : cj e.symm (f + f') = cj e.symm f + cj e.symm f' := by funext x; simp [cj]
        rw [this, map_add]; funext y; simp [cj]
      map_smul' := fun c f => by
        have : cj e.symm (c • f) = starRingEnd ℂ c • cj e.symm f := by funext x; simp [cj]
        rw [this, map_smul]; funext y; simp [cj] }
  map_one' := LinearMap.ext fun f => cj_cj e.symm e e.symm_apply_apply f
  map_mul' L L' := LinearMap.ext fun f => by
    show cj e (L (L' (cj e.symm f))) = cj e (L (cj e.symm (cj e (L' (cj e.symm f)))))
    rw [cj_cj e e.symm e.apply_symm_apply]

theorem cjEnd_cj {X Y : Type} (e : Y ≃ X) (L : Module.End ℂ (X → ℂ)) (f : X → ℂ) : cjEnd e L (cj e f) = cj e (L f) := by
  show cj e (L (cj e.symm (cj e f))) = _
  rw [cj_cj e e.symm e.apply_symm_apply]

def conjTarget {S T : HSp D} (om : Rep S T) : Rep S (negSp T) :=
  (cjEnd (Equiv.refl (WO S T))).comp (om.comp ((MonoidHom.id _).prodMap (negGA T).symm.toMonoidHom))

def conjSource {S T : HSp D} (om : Rep S T) : Rep (negSp S) T :=
  (cjEnd (Equiv.refl (WO S T))).comp (om.comp ((negGA S).symm.toMonoidHom.prodMap (MonoidHom.id _)))

def dagger (S T : HSp D) (x : WO S T) : WO T S := giA S ⬝ (adj x ⬝ gA T)

theorem dagger_dagger (S T : HSp D) (x : WO S T) : dagger T S (dagger S T x) = x := by
  simp only [dagger, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.mul_assoc, giA_mul_gA, Matrix.mul_one, giA_gA_cancel]

def daggerEquiv (S T : HSp D) : WO T S ≃ WO S T where
  toFun := dagger T S
  invFun := dagger S T
  left_inv := dagger_dagger T S
  right_inv := dagger_dagger S T

def conjAdjoint {S T : HSp D} (om : Rep S T) : Rep T S :=
  (cjEnd (daggerEquiv S T)).comp (om.comp (MulEquiv.prodComm : GA D T × GA D S ≃* GA D S × GA D T).toMonoidHom)

structure ConjAdjoint (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Prop where

  theta_neg : ∀ f : WO S T → ℂ, (IsThetaFunO ψ S (negSp T) (cj id f) ↔ IsThetaFunO ψ S T f) ∧
    (IsThetaFunO ψ (negSp S) T (cj id f) ↔ IsThetaFunO ψ S T f)

  heis_neg : ∀ (w : WO S T) (f : WO S T → ℂ), heisO ψ S (negSp T) w (cj id f) = cj id (heisO ψ S T w f) ∧
    heisO ψ (negSp S) T w (cj id f) = cj id (heisO ψ S T w f)

  conj_target : ∀ (χS χT : Chr D) (om : Rep S T), IsWeilDatumO ψ S T χS χT om →
    IsWeilDatumO ψ S (negSp T) χS⁻¹ χT⁻¹ (conjTarget om) ∧
    ∀ om' : Rep S (negSp T), IsWeilDatumO ψ S (negSp T) χS⁻¹ χT⁻¹ om' → ∀ g h f, IsThetaFunO ψ S T f →
      om' (g, negGA T h) (cj id f) = cj id (om (g, h) f)

  conj_source : ∀ (χS χT : Chr D) (om : Rep S T), IsWeilDatumO ψ S T χS χT om →
    IsWeilDatumO ψ (negSp S) T χS⁻¹ χT⁻¹ (conjSource om) ∧
    ∀ om' : Rep (negSp S) T, IsWeilDatumO ψ (negSp S) T χS⁻¹ χT⁻¹ om' → ∀ g h f, IsThetaFunO ψ S T f →
      om' (negGA S g, h) (cj id f) = cj id (om (g, h) f)

  sympl_dagger : ∀ x y : WO S T, symplO T S (dagger S T x) (dagger S T y) = -symplO S T x y

  act_dagger : ∀ g h (x : WO S T), dagger S T (actO S T g h x) = actO T S h g (dagger S T x)

  theta_dagger : ∀ f : WO S T → ℂ, IsThetaFunO ψ T S (cj (dagger T S) f) ↔ IsThetaFunO ψ S T f

  heis_dagger : ∀ (w : WO S T) (f : WO S T → ℂ),
    heisO ψ T S (dagger S T w) (cj (dagger T S) f) = cj (dagger T S) (heisO ψ S T w f)

  conj_adjoint : ∀ (χS χT : Chr D) (om : Rep S T), IsWeilDatumO ψ S T χS χT om →
    IsWeilDatumO ψ T S χT χS (conjAdjoint om) ∧
    ∀ om' : Rep T S, IsWeilDatumO ψ T S χT χS om' → ∀ g h f, IsThetaFunO ψ S T f →
      om' (h, g) (cj (dagger T S) f) = cj (dagger T S) (om (g, h) f)

def TensorRule (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) →
    (∀ (S A B : HSp D) (d : OrthDec S A B) (T : HSp D), TensorSource ψ d T) ∧
    (∀ (T A B : HSp D) (d : OrthDec T A B) (S : HSp D), TensorTarget ψ d S) ∧
    ∀ S T : HSp D, ConjAdjoint ψ S T

example {S T : HSp D} (om : Rep S T) (g : GA D S) (h : GA D T) (f : WO S T → ℂ) :
    conjTarget om (g, negGA T h) (cj id f) = cj id (om (g, h) f) := by
  have := cjEnd_cj (Equiv.refl (WO S T)) (om (g, h)) f
  simpa [conjTarget] using this

example {S T : HSp D} (om : Rep S T) (g : GA D S) (h : GA D T) (f : WO S T → ℂ) :
    conjAdjoint om (h, g) (cj (dagger T S) f) = cj (dagger T S) (om (g, h) f) :=
  cjEnd_cj (daggerEquiv S T) (om (g, h)) f

example (S T : HSp D) (g : GA D S) (h : GA D T) (x : WO S T) :
    dagger S T (actO S T g h x) = actO T S h g (dagger S T x) := by
  simp only [dagger, actO_eq, adj_mul, mt_inv S g, mt_inv T h, adj_adj, adj_gA, adj_giA, Matrix.mul_assoc,
    giA_gA_cancel, gA_giA_cancel]

example (χA χB χT : Chr D) (x x' y : (AE D)ˣ) :
    splitFacO (χA * χB) χT (x * x') y = splitFacO χA χT x y * splitFacO χB χT x' y := by
  simp only [splitFacO, map_mul, MonoidHom.mul_apply, _root_.mul_inv_rev]
  ac_rfl

end GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger

end
