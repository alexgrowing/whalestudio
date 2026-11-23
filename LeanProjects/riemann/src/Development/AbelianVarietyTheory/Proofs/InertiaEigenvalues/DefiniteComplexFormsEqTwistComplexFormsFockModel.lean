import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.IoPTprodInjectiveRangeEqValSpace
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.IoPTprodIntertwinesAction
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.AutomorphicFormIffRationalLevelLaw
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

private theorem eigen_law_absolute {M G Γ A V P : Type*} {J : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup P] [Module ℂ P] (io : V →ₗ[ℂ] P) (hinj : Function.Injective io) (val : Submodule ℂ P)
    (hran : LinearMap.range io = val) (act : A → P → P) (ρ : A → V → V) (hact : ∀ g v, act g (io v) = io (ρ g v))
    (E : M → G → V) (mv : Γ → G → J → G) (a : Γ → A) (lam : J → ℂ)
    (hlaw : ∀ f : G → V, (∃ x, E x = f) ↔ ∀ γ h k, f (mv γ h k) = lam k • ρ (a γ) (f h)) (F : G → P) :
    (∃ x, ∀ h, io (E x h) = F h) ↔ (∀ h, F h ∈ val) ∧ ∀ γ h k, F (mv γ h k) = lam k • act (a γ) (F h) := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun h => ?_, fun γ h k => ?_⟩
    · rw [← hran, ← hx]
      exact ⟨_, rfl⟩
    · rw [← hx, ← hx, (hlaw _).1 ⟨x, rfl⟩ γ h k, map_smul, hact]
  · rintro ⟨hv, hl⟩
    subst hran
    choose f hf using hv
    obtain ⟨x, hx⟩ := (hlaw f).2 fun γ h k => hinj (by rw [map_smul, ← hact, hf, hf, hl])
    exact ⟨x, fun h => by rw [hx, hf]⟩

theorem _root_.GlobalTheory.T.definiteComplexForms_eq_twistComplexForms_fockModel : ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
  ∀ (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ), IsLow X j u → Function.Injective (fockOf Y (used_of_tw H.tw) j u) ∧
  LinearMap.range (fockOf Y (used_of_tw H.tw) j u) = (baseOf Z c w j).formsC (twVia Z.ρ ι) := by
  intro D X X0 Y S YS Z c w j H ι hι u hu
  obtain ⟨hinj, hran⟩ := UpperTheory.KN.ioP_tprod_injective_and_range_eq_valSpace D X X0 Y S YS Z c w j H ι hι u hu
  have hact := UpperTheory.KN.ioP_tprod_intertwines_action D X X0 Y S YS Z c w j H ι hι u hu
  have hlaw := UpperTheory.KN.automorphic_form_iff_rational_level_law D X X0 Y S YS Z c w j H ι hι
  refine ⟨?_, Submodule.ext fun F => ?_⟩
  · intro x y hxy
    have h1 : (X.R.HV j (Y.tupT (D.what₂.muTw w))).e (formOf Y (used_of_tw H.tw) j x) =
        (X.R.HV j (Y.tupT (D.what₂.muTw w))).e (formOf Y (used_of_tw H.tw) j y) :=
      funext fun h => hinj (congrFun hxy h)
    have h2 : X.R.toRealDat.extV j (Y.tupT (D.what₂.muTw w)) (formOf Y (used_of_tw H.tw) j x) =
        X.R.toRealDat.extV j (Y.tupT (D.what₂.muTw w)) (formOf Y (used_of_tw H.tw) j y) := by
      have h3 := (X.char.models.HV j (Y.tupT (D.what₂.muTw w))).1 h1
      rw [h3]
    rw [extV_formOf, extV_formOf] at h2
    exact (Y.IL.jMt _ (used_of_tw H.tw) j).injective (Subtype.ext h2)
  · have key := eigen_law_absolute (X.R.ioP j (PiTensorProduct.tprod ℂ u)) hinj _ hran (fun g P => (baseOf Z c w j).act g P)
      (fun g v => (X.R.cV j).ρ g v) hact
      (fun x => (X.R.HV j (Y.tupT (D.what₂.muTw w))).e (formOf Y (used_of_tw H.tw) j x))
      (fun (γ : Formalism.L2.Theta.GQ (Vc D j)) (h : Bridge.Gf (Vc D j)) (k : (baseOf Z c w j).levJ (twVia Z.ρ ι)) =>
        Bridge.ratF (Vc D j) γ * h * (k : Bridge.Gf (Vc D j))) (fun γ => (γ : GA D (Vc D j)))
      (fun k => (((baseOf Z c w j).levLam (twVia Z.ρ ι) k : ℂˣ) : ℂ)) hlaw F
    refine Iff.trans ?_ (key.trans (Base.mem_formsC _).symm)
    exact ⟨fun ⟨x, hx⟩ => ⟨x, fun h => congrFun hx h⟩, fun ⟨x, hx⟩ => ⟨x, funext hx⟩⟩
