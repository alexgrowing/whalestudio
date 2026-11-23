import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesKillsAvg
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.DefiniteType

theorem adForms_mul {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (f : G → W) (hf : f ∈ Formalism.IndefR.Bridge.AdForms ι ρ J χ)
    (h : G) (k : G) (hk : k ∈ J) : f (h * k) = (χ ⟨k, hk⟩ : ℂ) • f h := by
  have h1 : f (ι 1 * h * k) = (χ ⟨k, hk⟩ : ℂ) • ρ 1 (f h) := hf 1 h ⟨k, hk⟩
  rwa [map_one, one_mul, map_one, Module.End.one_apply] at h1

theorem fin_mem {D : D7} {V : HSp D} (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (L : LevDat D.host.E ℂ V.rank) (κ : GA D V) (hκ : κ ∈ levG V β (flag1L L)) :
    (finHom V).rangeRestrict κ ∈ (levEnv V β L).J :=
  hκ.2

theorem chi_eq {D : D7} {V : HSp D} (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (L : LevDat D.host.E ℂ V.rank) (κ : GA D V) (hk : (finHom V).rangeRestrict κ ∈ (levEnv V β L).J) :
    (((levEnv V β L).χ ⟨_, hk⟩ : ℂˣ) : ℂ) = levChi V β (flag1L L) κ :=
  rfl

theorem ext_mul {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) (f : Formalism.IndefR.Bridge.Gf V → c.W) (κ : GA D V) (hκ : κ ∈ GfC V) (h : GA D V)
    (z : ℂ) (hz : f ((finHom V).rangeRestrict h * (finHom V).rangeRestrict κ) = z • f ((finHom V).rangeRestrict h)) :
    c.ext f (h * κ) = z • c.ext f h := by
  have h3 : c.ρ κ⁻¹ = 1 := hc.1 _ ((GfC V).inv_mem hκ)
  have h4 : c.ρ (h * κ)⁻¹ = c.ρ h⁻¹ := by
    rw [_root_.mul_inv_rev, c.ρ.map_mul, h3, one_mul]
  have h5 : f ((finHom V).rangeRestrict (h * κ)) = z • f ((finHom V).rangeRestrict h) :=
    (congrArg f ((finHom V).rangeRestrict.map_mul h κ)).trans hz
  show c.ρ (h * κ)⁻¹ (f ((finHom V).rangeRestrict (h * κ))) = z • c.ρ h⁻¹ (f ((finHom V).rangeRestrict h))
  rw [h4, h5, map_smul]

theorem ext_mul_lev {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (L : LevDat D.host.E ℂ V.rank) (f : Formalism.IndefR.Bridge.Gf V → c.W)
    (hf : f ∈ Formalism.IndefR.Bridge.AdForms (Formalism.IndefR.Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ)
    (κ : GA D V) (hκ : κ ∈ levG V β (flag1L L)) (h : GA D V) :
    c.ext f (h * κ) = levChi V β (flag1L L) κ • c.ext f h :=
  ext_mul c hc f κ hκ.1 h _ (chi_eq β L κ (fin_mem β L κ hκ) ▸
    adForms_mul (Formalism.IndefR.Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ f hf _ _ (fin_mem β L κ hκ))

theorem hasType_extV : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type)
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F →
    ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (l : (R.cV i).W →ₗ[ℂ] ℂ),
      HasType (Vc D i) (R.βV i) (flag1L (R.datVt i t)) (fun h => l (R.extV i t y h)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hc i t y l κ hκ h
  have hm := (hc.models.HV i t).2.1.le (LinearMap.mem_range_self _ y)
  have h1 := ext_mul_lev (R.cV i) (hc.models.cV i) (R.βV i) (R.datVt i t) ((R.HV i t).e y) hm κ hκ h
  exact (congrArg l h1).trans (map_smul l _ _)

end GlobalTheory.DefiniteType

end
