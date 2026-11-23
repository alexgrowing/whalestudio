import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChoiceSideWithE
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OfFirstStepLoc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TupPrimeEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfRoot

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.PlaceRead

variable {D : D7}

abbrev Amb (D : D7) (j : Fin D.R.m) : Type := Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank

section Choice

variable (c : NChoice D) (w : D.what₂.places.Pl)

abbrev KE : Type := FractionRing (c.Oe w)

abbrev chr : G D.host.E D.nd.Om →* (D.ntw.Ok (c.twI w) (c.k' w))ˣ := (c.psi' w).comp (D.ntw.art (c.twI w) (c.Q w))

variable {c w}

def viaOk (ι : KE c w →+* ℂ) : D.ntw.Ok (c.twI w) (c.k' w) →+* ℂ := ι.comp (algebraMap _ _)

def ringOf (ι : KE c w →+* ℂ) : Subring ℂ := (ι.comp (algebraMap (c.Oe w) _)).range

def twVia (ρ : Setup D.ntw) (ι : KE c w →+* ℂ) : Twist D Circle :=
  twistOf ρ.rc (viaOk ι) (ρ.ch (c.twI w)) (c.Q w) (chr c w)

def Extends (ρ : Setup D.ntw) (ε : KE c w →+* ℂ) : Prop := viaOk ε = ρ.eOk (c.twI w) (c.sd w) (c.k' w)

theorem Extends.twVia_eq {ρ : Setup D.ntw} {ε : KE c w →+* ℂ} (h : Extends ρ ε) :
    twVia ρ ε = ρ.tw (c.twI w) (c.sd w) (c.k' w) (c.Q w) (chr c w) := by
  rw [twVia, h]; rfl

theorem Extends.apply {ρ : Setup D.ntw} {ε : KE c w →+* ℂ} (h : Extends ρ ε) (a : D.ntw.Ok (c.twI w) (c.k' w)) :
    ε (algebraMap _ _ a) = ρ.eOk (c.twI w) (c.sd w) (c.k' w) a := RingHom.congr_fun h a

variable {ρ : Setup D.ntw} {hρ : ρ.Good} {j : Fin D.R.m} {rd : Rd ρ D.nexp (c.twI w) j (c.sd w)}

def rdE (T : CellTie hρ D.nexp rd) {ε : KE c w →+* ℂ} (hε : Extends ρ ε) : Tgt c w (j.1 + 1) →ₛₗ[ε] Amb D j :=
  let φ : Tgt c w (j.1 + 1) →+ Amb D j := TensorProduct.liftAddHom
    { toFun := fun a => (DistribSMul.toAddMonoidHom _ (ε a)).comp (T.rdV (c.k' w) (c.Q w) (chr c w)).toAddMonoidHom
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp [add_mul] }
    fun s a f => by
      change ε (s • a) • T.rdV _ _ _ f = ε a • T.rdV _ _ _ (s • f)
      rw [← algebraMap_smul (FractionRing (D.ntw.Ok (c.twI w) (c.k' w))) s f, LinearMap.map_smulₛₗ, Algebra.smul_def s a, map_mul, hε.apply,
        smul_smul, mul_comm]
      rfl
  { toFun := φ
    map_add' := φ.map_add
    map_smul' := fun s x => by
      induction x using TensorProduct.induction_on with
      | zero => rw [smul_zero, map_zero, smul_zero]
      | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
      | tmul a f =>
        change ε (s • a) • T.rdV _ _ _ f = ε s • ε a • T.rdV _ _ _ f
        rw [smul_eq_mul, map_mul, mul_smul] }

theorem rdE_tmul (T : CellTie hρ D.nexp rd) {ε : KE c w →+* ℂ} (hε : Extends ρ ε) (a : KE c w) (f) :
    rdE T hε (a ⊗ₜ f) = ε a • T.rdV (c.k' w) (c.Q w) (chr c w) f := rfl

variable (rd) in

def rdF (hρ : ρ.Good) {ε : KE c w →+* ℂ} (hε : Extends ρ ε) :
    KE c w ⊗[D.ntw.O (c.twI w)] D.nexp.Fm (c.twI w) (j.1 + 1) (c.sd w) →ₛₗ[ε] (GA D (Wc D j) → ℂ) :=
  let φ : KE c w ⊗[D.ntw.O (c.twI w)] D.nexp.Fm (c.twI w) (j.1 + 1) (c.sd w) →+ (GA D (Wc D j) → ℂ) := TensorProduct.liftAddHom
    { toFun := fun a => (DistribSMul.toAddMonoidHom _ (ε a)).comp rd.toAddMonoidHom
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp [add_mul] }
    fun s a f => by
      change ε (s • a) • rd f = ε a • rd (s • f)
      rw [rd_smul, Algebra.smul_def s a, map_mul, IsScalarTower.algebraMap_apply _ (D.ntw.Ok (c.twI w) (c.k' w)) (KE c w), hε.apply,
        hρ.ek_e, smul_smul, mul_comm]
  { toFun := φ
    map_add' := φ.map_add
    map_smul' := fun s x => by
      induction x using TensorProduct.induction_on with
      | zero => rw [smul_zero, map_zero, smul_zero]
      | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
      | tmul a f =>
        change ε (s • a) • rd f = ε s • ε a • rd f
        rw [smul_eq_mul, map_mul, mul_smul] }

theorem rdF_tmul (hρ : ρ.Good) {ε : KE c w →+* ℂ} (hε : Extends ρ ε) (a : KE c w) (f) :
    rdF rd hρ hε (a ⊗ₜ f) = ε a • rd f := rfl

end Choice

def ConjAt {j : Fin D.R.m} (Φ : VsV D j ℂ →ₗ[ℂ] PolF D (Wc D j).rank (Vc D j).rank) (κ : ℂ) (τ : ℂ ≃+* ℂ) (F F' : Amb D j) : Prop :=
  ∀ h, ∃ x x' : VsV D j ℂ, ConjVec j τ x x' ∧ F h = Φ x ∧ F' h = Φ ((τ κ / κ) • x')

def intLL (D : D7) : Subring ℂ := (D.what₂.embLL.comp (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)).range

theorem used_of_tw {w : D.what₂.places.Pl} (h : D.what₂.muAt w ≠ D.what₂.mu0) : Used0 D (D.what₂.muTw w) :=
  Or.inr ⟨w, ((D.what₂.muAt_or w).resolve_left h).symm⟩

section Rows

variable {X : RealSide D} {X0 : BaseLevelRowSide D} (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0)

def formOf {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m) : D.what₂.Mt μ (j.1 + 1) →ₗ[ℂ] (X.R.HV j (Y.tupT μ)).H :=
  (LinearEquiv.ofInjective _ (Y.hinj j (Y.tupT μ))).symm.toLinearMap ∘ₗ Submodule.inclusion inf_le_left ∘ₗ
    (Y.IL.jMt μ hμ j).toLinearMap

theorem extV_formOf {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m) (x : D.what₂.Mt μ (j.1 + 1)) :
    X.R.toRealDat.extV j (Y.tupT μ) (formOf Y hμ j x) = (Y.IL.jMt μ hμ j x).1 :=
  congrArg Subtype.val ((LinearEquiv.ofInjective _ (Y.hinj j (Y.tupT μ))).apply_symm_apply _)

def fockOf {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m) (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ) :
    D.what₂.Mt μ (j.1 + 1) →ₗ[ℂ] Amb D j :=
  (X.R.ioP j (PiTensorProduct.tprod ℂ u)).compLeft _ ∘ₗ (X.R.HV j (Y.tupT μ)).e ∘ₗ formOf Y hμ j

theorem fockOf_apply {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m) (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ) (x h) :
    fockOf Y hμ j u x h = X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j (Y.tupT μ)).e (formOf Y hμ j x) h) := rfl

variable (X) in

def IsLow (j : Fin D.R.m) (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ) : Prop :=
  ∀ τ, (u τ : (X.R.MW j (sg0 D X.A3.A)).sm τ) = X.geo.v₀ j (sg0 D X.A3.A) τ

variable {S : NX.RatDat D.ntw} {YS : NX.NExpRealS X.R X.cG S} (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl)
  (j : Fin D.R.m)

abbrev baseOf : Base (Vc D j) (Wc D j) := Z.ρ.B (c.twI w) j (c.sd w)

structure AtPlace : Prop where
  pins : GlobalTheory.Mem.R3.Pins X.R X.F X.cG
  intersectionNumber_baseChange : GlobalTheory.Mem.R3.Holds X.R X.F
  field : FieldOk X
  tw : D.what₂.muAt w ≠ D.what₂.mu0
  ok : TwOK (c.twI w) (c.k' w) (c.Q w) (chr c w)
  cls : ClsQ (D := D) (c.Q w)
  emb : ∀ ε : KE c w →+* ℂ, Extends Z.ρ ε → ∀ x : D.LL0, ε (c.embW w (x : D.what₂.LL)) = embLL0 D x
  val : ∀ σ, ∃ y : D.what₂.LL, c.embW w y = algebraMap _ (KE c w) ((chr c w σ : (D.ntw.Ok (c.twI w) (c.k' w))ˣ) : D.ntw.Ok (c.twI w) (c.k' w))
  U_eq : ∀ g : X.Γ, X.cG (X.R.eG g) ∈ D.nexp.U ↔ g ∈ X.F.P0
  psi_eq : ∀ i b (g : X.F.P0) (h : X.cG (X.R.eG g) ∈ D.nexp.U),
    Z.ρ.e i b (D.nexp.psiU i b ⟨_, h⟩ : (FractionRing (D.ntw.O i))ˣ) = (D.what₂.embLL (X.F.ψ0 g : D.what₂.LLˣ))⁻¹
  ks : (S.A (j.1 + 1)).IsKsForm
  rat : RatRow YS X.geo.v₀ Z.good (c.twI w) j (c.sd w)
  tup : ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
    IsTupOf X.R.toRealDat (baseOf Z c w j) (twVia Z.ρ ι) (Y.tupT (D.what₂.muTw w))

end Rows

end GlobalTheory.PlaceRead

end
