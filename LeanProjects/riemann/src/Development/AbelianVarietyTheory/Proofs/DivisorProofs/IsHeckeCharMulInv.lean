import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTwistColumns
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqZeroOfReal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAlgebraMapOfSigRFixed
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumUniqueOnThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTwistHeckeCharactersStatement

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwistFactorProof

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTwistColumns
open scoped TensorProduct

def WeilUnique (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    IsWeilDatumO ψ S T χS χT om' → ∀ p f, IsThetaFunO ψ S T f → om p f = om' p f

def WeilChange (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT νS νT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    IsHeckeChar D νS → IsHeckeChar D νT → ResEta D νS 0 → ResEta D νT 0 →
    ∃ om', IsWeilDatumO ψ S T (χS * νS) (χT * νT) om' ∧ ∀ g h x y, IsDetRoot S g x → IsDetRoot T h y →
      om' (g, h) = ((((νT x)⁻¹ * νS y : Circle) : ℂ)) • om (g, h)

variable {D : D7}

theorem isHeckeChar_mul_inv {χ η : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hη : IsHeckeChar D η) :
    IsHeckeChar D (χ * η⁻¹) :=
  ⟨hχ.1.mul hη.1.inv, fun x => by rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hχ.2, hη.2, inv_one, mul_one]⟩

theorem isDetRoot_one (V : HSp D) : IsDetRoot V 1 1 := by
  unfold IsDetRoot
  rw [map_one, Units.val_one, Units.val_one, Matrix.det_one, map_one, one_mul]

theorem weil_ratio (hU : WeilUnique D) (hC : WeilChange D) {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
    {χS χT χS' χT' : (AE D)ˣ →* Circle} {om om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (ho : IsWeilDatumO ψ S T χS χT om) (ho' : IsWeilDatumO ψ S T χS' χT' om') {g : GA D S} {h : GA D T}
    {x y : (AE D)ˣ} (hx : IsDetRoot S g x) (hy : IsDetRoot T h y) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om' (g, h) f = ((((χT' x * (χT x)⁻¹)⁻¹ * (χS' y * (χS y)⁻¹) : Circle) : ℂ)) • om (g, h) f := by
  obtain ⟨o, h1, h2⟩ := hC ψ ho.std S T χS χT (χS' * χS⁻¹) (χT' * χT⁻¹) om ho
    (isHeckeChar_mul_inv ho'.hecS ho.hecS) (isHeckeChar_mul_inv ho'.hecT ho.hecT)
    (resEta_parity (resEta_mul ho'.resS (resEta_inv ho.resS)) (by omega))
    (resEta_parity (resEta_mul ho'.resT (resEta_inv ho.resT)) (by omega))
  have e : ∀ a b : (AE D)ˣ →* Circle, a * (b * a⁻¹) = b := fun a b => by
    ext1 z
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply]
    rw [mul_comm (b z), mul_inv_cancel_left]
  rw [e, e] at h1
  rw [hU ψ ho.std S T χS' χT' om' o ho' h1 _ f hf, h2 g h x y hx hy]
  rfl

theorem vac_ne_zero {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {f : WO S T → ℂ}
    (h : IsVacO ψ θ S T sS sT LS LT f) : f ≠ 0 := by
  rintro rfl
  obtain ⟨⟨p, hp⟩, hn⟩ := h.2.norm
  have := hn p hp
  simp [nrm2] at this

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem frame_ratio (hU : WeilUnique D) (hC : WeilChange D) (hω : R.thP_ωP) (i : Fin D.R.m) (t t' : T0)
    {h : GA D (Wc D i)} {x : (AE D)ˣ} (hx : IsDetRoot (Wc D i) h x) {f : WO (Vc D i) (Wc D i) → ℂ}
    (hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) f) :
    ((R.xi t x : Circle) : ℂ) • R.ωP i t' (1, h) f = ((R.xi t' x : Circle) : ℂ) • R.ωP i t (1, h) f := by
  rw [weil_ratio hU hC (hω i t) (hω i t') (isDetRoot_one _) hx hf, smul_smul, ← Circle.coe_mul]
  congr 2
  show R.xi t x * (_ * (R.mu0 _ x * R.xi t' x * (R.mu0 _ x * R.xi t x)⁻¹)) = _
  rw [map_one, map_one, mul_inv_cancel, inv_one, one_mul, mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul,
    mul_comm (R.xi t' x), mul_inv_cancel_left]

end GlobalTheory.TwistFactorProof

end
