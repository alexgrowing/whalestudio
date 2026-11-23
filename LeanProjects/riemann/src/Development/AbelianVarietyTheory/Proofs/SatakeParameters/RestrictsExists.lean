import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormVZpowDegEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValSubLtIff
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.AdTransfer

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL.ResEx

variable {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
  [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)}

theorem res_mem_Dec {σ : G L Ω} (hσ : σ ∈ Dec (F := L) A) :
    AlgEquiv.restrictScalarsHom K σ ∈ Dec (F := K) A :=
  GlobalTheory.DelEps.WeilRes.mem_Dec_iff.2 fun x => GlobalTheory.DelEps.WeilRes.mem_Dec_iff.1 hσ x

theorem res_mem_Ine {σ : G L Ω} (hσ : σ ∈ Ine (F := L) A) :
    AlgEquiv.restrictScalarsHom K σ ∈ Ine (F := K) A :=
  ⟨res_mem_Dec hσ.1, fun x hx => hσ.2 x hx⟩

theorem res_mem_Weil (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (σ : Weil h') :
    AlgEquiv.restrictScalarsHom K (σ : G L Ω) ∈ Weil h := by
  obtain ⟨a, b, hab⟩ := (mem_Weil h').1 σ.2
  have hQ : normV v' = normV v ^ v'.asIdeal.inertiaDeg (𝓞 K) := by
    rw [GlobalTheory.DelEps.WeilRes.normV_eq_pow (K := K) v', GlobalTheory.DelEps.WeilRes.under_eq h h']
  refine ⟨v'.asIdeal.inertiaDeg (𝓞 K) * a, v'.asIdeal.inertiaDeg (𝓞 K) * b, res_mem_Dec hab.1,
    fun x hx => ?_⟩
  have h2 := hab.2 x hx
  rw [hQ, ← pow_mul, ← pow_mul] at h2
  exact h2

def resW (h : IsPlaceOver A v) (h' : IsPlaceOver A v') : Weil h' →* Weil h where
  toFun σ := ⟨AlgEquiv.restrictScalarsHom K (σ : G L Ω), res_mem_Weil h h' σ⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' σ τ := Subtype.ext (map_mul _ _ _)

def resI : Ine (F := L) A →* Ine (F := K) A :=
  ((AlgEquiv.restrictScalarsHom K).comp (Ine (F := L) A).subtype).codRestrict (Ine (F := K) A)
    fun σ => res_mem_Ine σ.2

theorem continuous_resI : Continuous (resI (K := K) (L := L) (Ω := Ω) (A := A)) :=
  ((UpperTheory.V.Af.continuous_restrictScalarsHom K L Ω).comp continuous_subtype_val).subtype_mk _

theorem resW_ineIncl (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (τ : Ine (F := L) A) :
    resW h h' (ineIncl h' τ) = ineIncl h (resI τ) := Subtype.ext rfl

def resRep (h : IsPlaceOver A v) (h' : IsPlaceOver A v') {n : ℕ} (a : WDRep h (Fin n → ℂ)) :
    WDRep h' (Fin n → ℂ) where
  ρ := a.ρ.comp (resW h h')
  N := a.N
  smooth := by
    show IsOpen {τ : Ine (F := L) A | a.ρ (resW h h' (ineIncl h' τ)) = 1}
    simp_rw [resW_ineIncl]
    exact a.smooth.preimage continuous_resI
  semisimple σ := a.semisimple _
  nilpotent := a.nilpotent
  comm σ := by
    have hR := normV_zpow_deg_eq σ (resW h h' σ) (fun z => rfl)
    have hC : ((normV v' : ℕ) : ℂ) ^ deg σ = ((normV v : ℕ) : ℂ) ^ deg (resW h h' σ) := by
      have := congrArg (fun r : ℝ => (r : ℂ)) hR
      push_cast at this
      exact this
    show a.ρ (resW h h' σ) * a.N = _ • (a.N * a.ρ (resW h h' σ))
    rw [hC]
    exact a.comm _

end GlobalTheory.AboveL.ResEx

namespace GlobalTheory.AboveL

end GlobalTheory.AboveL

end
