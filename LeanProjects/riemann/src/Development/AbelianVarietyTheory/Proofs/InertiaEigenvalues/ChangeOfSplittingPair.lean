import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumUniqueOnThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTwistHeckeCharacters

set_option autoImplicit false

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum Formalism.IndefR.Lift

noncomputable section

namespace GlobalTheory.SplitChange

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χV χW ν : (AE D)ˣ →* Circle}
  {om om' : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}

theorem resEta_zero_of_triv {χ : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n) (hF : ∀ a, ν (idF D a) = 1) :
    ResEta D ν 0 :=
  ⟨h.1, fun η _ a => by rw [hF, pow_zero]⟩

theorem exists_twist_root (ho : IsWeilDatumO ψ V W χV χW om) (hν : IsHeckeChar D ν) (hF : ∀ a, ν (idF D a) = 1) :
    ∃ om', IsWeilDatumO ψ V W (χV * ν) (χW * ν) om' ∧ ∀ h g x y, IsDetRoot V h x → IsDetRoot W g y →
      om' (h, g) = (((ν y : Circle) : ℂ) * ((ν x : Circle) : ℂ)⁻¹) • om (h, g) := by
  obtain ⟨o, h1, h2⟩ := GlobalTheory.WeilChange.exists_weilDatum_twist D ψ ho.std V W χV χW ν ν om ho hν hν
    (resEta_zero_of_triv ho.resS hF) (resEta_zero_of_triv ho.resS hF)
  refine ⟨o, h1, fun h g x y hx hy => ?_⟩
  rw [h2 h g x y hx hy, Circle.coe_mul, Circle.coe_inv, mul_comm]

theorem twist_eq_root (ho : IsWeilDatumO ψ V W χV χW om) (hν : IsHeckeChar D ν) (hF : ∀ a, ν (idF D a) = 1)
    (ho' : IsWeilDatumO ψ V W (χV * ν) (χW * ν) om') {h : GA D V} {g : GA D W} {x y : (AE D)ˣ}
    (hx : IsDetRoot V h x) (hy : IsDetRoot W g y) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    om' (h, g) f = (((ν y : Circle) : ℂ) * ((ν x : Circle) : ℂ)⁻¹) • om (h, g) f := by
  obtain ⟨o, h1, h2⟩ := exists_twist_root ho hν hF
  rw [GlobalTheory.WeilUniq.weilDatum_unique D ψ ho.std V W _ _ om' o ho' h1 _ f hf, h2 h g x y hx hy, LinearMap.smul_apply]

theorem exists_twist (ho : IsWeilDatumO ψ V W χV χW om) (hν : IsHeckeChar D ν) (hF : ∀ a, ν (idF D a) = 1)
    {nV : GA D V → ℂ} {nW : GA D W → ℂ} (hV : MuVal V ν nV) (hW : MuVal W ν nW) :
    ∃ om', IsWeilDatumO ψ V W (χV * ν) (χW * ν) om' ∧ ∀ h g, om' (h, g) = (nW g * (nV h)⁻¹) • om (h, g) := by
  obtain ⟨o, h1, h2⟩ := exists_twist_root ho hν hF
  refine ⟨o, h1, fun h g => ?_⟩
  obtain ⟨x, hx⟩ := hV.1 h
  obtain ⟨y, hy⟩ := hW.1 g
  rw [h2 h g x y hx hy, hV.2 h x hx, hW.2 g y hy]

theorem twist_eq (ho : IsWeilDatumO ψ V W χV χW om) (hν : IsHeckeChar D ν) (hF : ∀ a, ν (idF D a) = 1)
    (ho' : IsWeilDatumO ψ V W (χV * ν) (χW * ν) om') {nV : GA D V → ℂ} {nW : GA D W → ℂ} (hV : MuVal V ν nV)
    (hW : MuVal W ν nW) (h : GA D V) (g : GA D W) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    om' (h, g) f = (nW g * (nV h)⁻¹) • om (h, g) f := by
  obtain ⟨x, hx⟩ := hV.1 h
  obtain ⟨y, hy⟩ := hW.1 g
  rw [twist_eq_root ho hν hF ho' hx hy hf, hV.2 h x hx, hW.2 g y hy]

theorem thetaKO_twist (ho : IsWeilDatumO ψ V W χV χW om) (hν : IsHeckeChar D ν) (hF : ∀ a, ν (idF D a) = 1)
    (ho' : IsWeilDatumO ψ V W (χV * ν) (χW * ν) om') {nV : GA D V → ℂ} {nW : GA D W → ℂ} (hV : MuVal V ν nV)
    (hW : MuVal W ν nW) (h : GA D V) (g : GA D W) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    thetaKO om' h g f = nW g * (nV h)⁻¹ * thetaKO om h g f := by
  unfold thetaKO
  rw [twist_eq ho hν hF ho' hV hW h g hf, Pi.smul_apply, smul_eq_mul]

theorem chrTh_tup {C : Type*} [CommGroup C] (μ : ℕ → C) (η ν : C) (j : ℕ) :
    chrTh (tup μ ν) η j = ((chrTh μ η j).1 * ν, (chrTh μ η j).2 * ν) := by
  unfold chrTh tup
  rw [mul_right_comm]

theorem tup_mul {C : Type*} [CommGroup C] (μ : ℕ → C) (ξ ν : C) : tup μ (ξ * ν) = tup (tup μ ξ) ν := by
  funext j
  unfold tup
  rw [mul_assoc]

theorem change_of_splitting_pair (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW ν : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ho : IsWeilDatumO ψ V W χV χW om) (hν : IsHeckeChar D ν)
    (hF : ∀ a, ν (idF D a) = 1) :
    (∃ (nV : GA D V → ℂ) (nW : GA D W → ℂ), MuVal V ν nV ∧ MuVal W ν nW) ∧
    (∀ (nV : GA D V → ℂ) (nW : GA D W → ℂ), MuVal V ν nV → MuVal W ν nW →
      (∃ om', IsWeilDatumO ψ V W (χV * ν) (χW * ν) om' ∧ ∀ h g, om' (h, g) = (nW g * (nV h)⁻¹) • om (h, g)) ∧
      ∀ om', IsWeilDatumO ψ V W (χV * ν) (χW * ν) om' → ∀ h g f, IsThetaFunO ψ V W f →
        om' (h, g) f = (nW g * (nV h)⁻¹) • om (h, g) f) ∧
    ∀ om₁, IsWeilDatumO ψ V W χV χW om₁ → ∀ p f, IsThetaFunO ψ V W f → om₁ p f = om p f := by
  refine ⟨?_, fun nV nW hV hW => ⟨exists_twist ho hν hF hV hW, fun om' ho' h g f hf => twist_eq ho hν hF ho' hV hW h g hf⟩,
    fun om₁ h1 => GlobalTheory.WeilUniq.weilDatum_unique D ψ ho.std V W χV χW om₁ om h1 ho⟩
  obtain ⟨nV, hV, -⟩ := GlobalTheory.Member.exists_muVal D V ν hν hF
  obtain ⟨nW, hW, -⟩ := GlobalTheory.Member.exists_muVal D W ν hν hF
  exact ⟨nV, nW, hV, hW⟩

theorem change_of_splitting (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (μ : ℕ → (AE D)ˣ →* Circle)
    (η ν : (AE D)ˣ →* Circle) (j : ℕ) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))
    (ho : IsWeilDatumO ψ V W (chrTh μ η j).1 (chrTh μ η j).2 om) (hν : IsHeckeChar D ν) (hF : ∀ a, ν (idF D a) = 1) :
    (∃ (nV : GA D V → ℂ) (nW : GA D W → ℂ), MuVal V ν nV ∧ MuVal W ν nW) ∧
    (∀ (nV : GA D V → ℂ) (nW : GA D W → ℂ), MuVal V ν nV → MuVal W ν nW →
      (∃ om', IsWeilDatumO ψ V W (chrTh (tup μ ν) η j).1 (chrTh (tup μ ν) η j).2 om' ∧
        ∀ h g, om' (h, g) = (nW g * (nV h)⁻¹) • om (h, g)) ∧
      ∀ om', IsWeilDatumO ψ V W (chrTh (tup μ ν) η j).1 (chrTh (tup μ ν) η j).2 om' → ∀ h g f, IsThetaFunO ψ V W f →
        om' (h, g) f = (nW g * (nV h)⁻¹) • om (h, g) f) ∧
    ∀ om₁, IsWeilDatumO ψ V W (chrTh μ η j).1 (chrTh μ η j).2 om₁ → ∀ p f, IsThetaFunO ψ V W f → om₁ p f = om p f := by
  rw [chrTh_tup]
  exact change_of_splitting_pair D ψ V W _ _ ν om ho hν hF

end GlobalTheory.SplitChange

end
