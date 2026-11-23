import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryAdelicCharOfHeckeChar
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilChange

variable {D : D7}

theorem heisO_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T u (c • f) = c • heisO ψ S T u f := by
  funext w
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem thetaO_smul {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (c : ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (c • f) where
  quasi γ w := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hf.quasi]
    ring
  level := by
    obtain ⟨U, hU, h⟩ := hf.level
    exact ⟨U, hU, fun u hu h0 => by rw [heisO_smul, h u hu h0]⟩
  cont := hf.cont.const_smul c
  smooth k L hL h0 w := (hf.smooth k L hL h0 w).const_smul c

theorem triv_of_resEta_zero {ν : (AE D)ˣ →* Circle} (h : ResEta D ν 0) (a : (AF D.host.F)ˣ) : ν (idF D a) = 1 := by
  obtain ⟨η, hη⟩ := h.1
  rw [h.2 η hη a, pow_zero]

theorem hecke_mul {χ ν : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hν : IsHeckeChar D ν) : IsHeckeChar D (χ * ν) :=
  ⟨hχ.1.mul hν.1, fun x => by rw [MonoidHom.mul_apply, hχ.2, hν.2, mul_one]⟩

theorem hecke_inv {ν : (AE D)ˣ →* Circle} (hν : IsHeckeChar D ν) : IsHeckeChar D ν⁻¹ :=
  ⟨hν.1.inv, fun x => by rw [MonoidHom.inv_apply, hν.2, inv_one]⟩

theorem exists_weilDatum_twist : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (νS νT : (AE D)ˣ →* Circle) (om : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))), IsWeilDatumO ψ S T χS χT om → IsHeckeChar D νS → IsHeckeChar D νT → ResEta D νS 0 → ResEta D νT 0 → ∃ om', IsWeilDatumO ψ S T (χS * νS) (χT * νT) om' ∧ ∀ g h x y, IsDetRoot S g x → IsDetRoot T h y → om' (g, h) = ((((νT x)⁻¹ * νS y : Circle) : ℂ)) • om (g, h) := by
  intro D ψ hψ S T χS χT νS νT om ho hS hT rS rT
  obtain ⟨a, aval, amul, anorm, arat, acont⟩ :=
    GlobalTheory.Member.exists_muVal D S νT⁻¹ (hecke_inv hT) (triv_of_resEta_zero (resEta_inv rT))
  obtain ⟨b, bval, bmul, bnorm, brat, bcont⟩ := GlobalTheory.Member.exists_muVal D T νS hS (triv_of_resEta_zero rS)
  have a1 : a 1 = 1 := arat 1 (one_mem _)
  have b1 : b 1 = 1 := brat 1 (one_mem _)
  let om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ) :=
    { toFun := fun p => (a p.1 * b p.2) • om p
      map_one' := by rw [Prod.fst_one, Prod.snd_one, a1, b1, map_one, one_mul, one_smul]
      map_mul' := fun p q => by
        rw [Prod.fst_mul, Prod.snd_mul, amul, bmul, map_mul, smul_mul_smul_comm, mul_mul_mul_comm] }
  have happ : ∀ p f, om' p f = (a p.1 * b p.2) • om p f := fun p f => rfl
  have hval : ∀ g h x y, IsDetRoot S g x → IsDetRoot T h y →
      a g * b h = (((νT x)⁻¹ * νS y : Circle) : ℂ) := by
    intro g h x y hx hy
    rw [aval.2 g x hx, bval.2 h y hy, Circle.coe_mul, MonoidHom.inv_apply]
  refine ⟨om', ⟨hψ, hecke_mul ho.hecS hS, hecke_mul ho.hecT hT, resEta_mul ho.resS rS, resEta_mul ho.resT rT,
    ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro p f hf
    rw [happ]
    exact thetaO_smul _ (ho.om_pres p f hf)
  · intro g h w₀ f hf
    rw [happ, happ, heisO_smul, ho.om_heis g h w₀ f hf]
  · intro γ hγ γ' hγ' f hf
    rw [happ, arat γ hγ, brat γ' hγ', one_mul, one_smul]
    exact ho.om_aut γ hγ γ' hγ' f hf
  · intro f hf w
    exact ((acont.comp continuous_fst).mul (bcont.comp continuous_snd)).mul (ho.om_cont f hf w)
  · intro μ 𝓕 hμ h𝓕 p f hf
    rw [← ho.om_unit μ 𝓕 hμ h𝓕 p f hf]
    refine lintegral_congr fun w => ?_
    have hn : ‖om' p f w‖ = ‖om p f w‖ := by
      rw [happ, Pi.smul_apply, smul_eq_mul, norm_mul, norm_mul, anorm, bnorm, one_mul, one_mul]
    rw [← ofReal_norm, ← ofReal_norm, hn]
  · intro e he g h hg hh x y hx hy
    obtain ⟨r, hr, H⟩ := ho.om_split e he g h hg hh x y hx hy
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    rw [happ, map_smul, H ℓ hℓ f hf,
      hval g h x y (isDetAt_root he S g hg x hx) (isDetAt_root he T h hh y hy)]
    simp only [splitFacO, MonoidHom.mul_apply, mul_inv, Circle.coe_mul, smul_eq_mul]
    ring
  · intro g h x y hx hy
    rw [← hval g h x y hx hy]
    rfl

end GlobalTheory.WeilChange

end
