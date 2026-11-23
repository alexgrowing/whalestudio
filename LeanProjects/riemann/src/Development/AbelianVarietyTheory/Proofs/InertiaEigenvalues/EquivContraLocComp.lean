import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.PolarizedGaloisRepPublished
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiAboveLHyp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.WignerVanishingGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiLocalGlobalDual
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairingEquivContra
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.TheRec GlobalTheory.ContraPair

noncomputable section

namespace GlobalTheory.LocDual

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def Maps (V : Submodule ℂ (Sm E a)) (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) : Type :=
  {f : σ.V →ₗ[ℂ] Sm E a // (∀ v, f v ∈ V) ∧ ∀ g v, f (σ.ρ g v) = finRep E a (locGL E a w g) (f v)}

theorem iSup_range_eq (V : Submodule ℂ (Sm E a)) (hs : IsStable V) (hi : ∀ W ≤ V, IsStable W → W = ⊥ ∨ W = V)
    (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (h : GlobalTheory.UnitaryBC.IsLocCompGL V w σ) : ⨆ f : Maps V w σ, LinearMap.range f.1 = V := by
  have comm : ∀ o : Op E a, (∀ g, act o * finRep E a (locGL E a w g) = finRep E a (locGL E a w g) * act o) →
      ∀ (f : Maps V w σ) v, act o (f.1 v) ∈ ⨆ f : Maps V w σ, LinearMap.range f.1 := fun o ho f v =>
    Submodule.mem_iSup_of_mem (⟨act o ∘ₗ f.1, fun v => hs o _ (f.2.1 v), fun g v => by
      rw [LinearMap.comp_apply, f.2.2]; exact LinearMap.congr_fun (ho g) _⟩ : Maps V w σ) ⟨v, rfl⟩
  refine (hi _ (iSup_le fun f => ?_) fun o φ hφ => ?_).resolve_left fun hb => ?_
  · rintro _ ⟨v, rfl⟩; exact f.2.1 v
  · have : (⨆ f : Maps V w σ, LinearMap.range f.1) ≤ (⨆ f : Maps V w σ, LinearMap.range f.1).comap (act o) := by
      refine iSup_le fun f => ?_
      rintro _ ⟨v, rfl⟩
      rw [Submodule.mem_comap]
      cases o with
      | fin k =>
        let g := Matrix.GeneralLinearGroup.map (pLoc E w) k
        have h1 := comm (.fin (k * (locGL E a w g)⁻¹)) (fun g' => by
          change finRep E a _ * _ = _ * finRep E a _
          rw [← map_mul, ← map_mul, GlobalTheory.CuspRep.LocUniq.comm_locGL w
            (by rw [map_mul, map_inv, pLoc_locGL, mul_inv_cancel])]) f (σ.ρ g v)
        have h2 : act (.fin (k * (locGL E a w g)⁻¹)) (f.1 (σ.ρ g v)) = act (.fin k) (f.1 v) := by
          rw [f.2.2, act, act, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
        rwa [h2] at h1
      | cpt k =>
        refine comm (.cpt k) (fun g => ?_) f v
        have h2 := congrArg (rt E a) (infGL_comm (Unitary.toUnits k) (locGL E a w g))
        rw [map_mul, map_mul] at h2
        exact h2
      | lie X => exact comm (.lie X) (fun g => lie_rt_fin X (locGL E a w g)) f v
    exact this hφ
  · obtain ⟨f, h0, h1, hf⟩ := h
    refine h0 (LinearMap.ext fun v => ?_)
    have : f v ∈ ⨆ f : Maps V w σ, LinearMap.range f.1 :=
      Submodule.mem_iSup_of_mem (⟨f, h1, hf⟩ : Maps V w σ) ⟨v, rfl⟩
    rw [hb] at this
    exact this

theorem exists_comp_ne_zero (V : Submodule ℂ (Sm E a)) (hs : IsStable V) (hi : ∀ W ≤ V, IsStable W → W = ⊥ ∨ W = V)
    (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (h : GlobalTheory.UnitaryBC.IsLocCompGL V w σ) {X : Type} [AddCommGroup X] [Module ℂ X] (β : V →ₗ[ℂ] X) (hβ : β ≠ 0) :
    ∃ f : Maps V w σ, β ∘ₗ f.1.codRestrict V f.2.1 ≠ 0 := by
  by_contra hc
  push Not at hc
  refine hβ (LinearMap.ext fun φ => ?_)
  have hle : (⨆ f : Maps V w σ, LinearMap.range f.1) ≤ (LinearMap.ker β).map V.subtype := by
    refine iSup_le fun f => ?_
    rintro _ ⟨v, rfl⟩
    exact ⟨⟨f.1 v, f.2.1 v⟩, LinearMap.congr_fun (hc f) v, rfl⟩
  rw [iSup_range_eq V hs hi w σ h] at hle
  obtain ⟨ψ, h1, h2⟩ := hle φ.2
  obtain rfl : ψ = φ := Subtype.ext h2
  exact h1

theorem equiv_contra_locComp : IrreducibleAdmissibleGL → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (V : Submodule ℂ (Sm E a)), IsStable V → (∀ W ≤ V, IsStable W → W = ⊥ ∨ W = V) → ∀ (w : HeightOneSpectrum (𝓞 E)) (σ σ' : SmIrr (GL (Fin a) (w.adicCompletion E))), GlobalTheory.UnitaryBC.IsLocCompGL V w σ → ∀ β : V →ₗ[ℂ] σ'.V →ₗ[ℂ] ℂ, β ≠ 0 → (∀ (g : GL (Fin a) (w.adicCompletion E)) (φ ψ : V) (v : σ'.V), ψ.1 = finRep E a (locGL E a w g) φ.1 → β ψ (σ'.ρ g v) = β φ v) → Nonempty (σ'.ρ.Equiv (GlobalTheory.SmGL.contra σ.ρ)) := by
  intro hadm E _ _ _ a V hs hi w σ σ' h β hβ hinv
  obtain ⟨f, hf⟩ := exists_comp_ne_zero V hs hi w σ h β hβ
  have hB : ∀ g u v, (β ∘ₗ f.1.codRestrict V f.2.1) (σ.ρ g u) (σ'.ρ g v) = (β ∘ₗ f.1.codRestrict V f.2.1) u v :=
    fun g u v => hinv g _ _ v (f.2.2 g u)
  have hirr : (GlobalTheory.SmGL.contra σ.ρ).IsIrreducible :=
    GlobalTheory.ContraRefl.contra_isIrreducible (GlobalTheory.SqIntUnit.compactOpen_basis _ a)
      (hadm _ a σ.V σ.ρ σ.smooth σ.irred) σ.irred
  exact ⟨(GlobalTheory.InvPairing.pairMap σ.ρ σ'.smooth _ hB).ofBijective
    (GlobalTheory.InvPairing.pairMap_bijective σ.ρ σ'.smooth _ hB hf σ'.irred hirr)⟩

end GlobalTheory.LocDual
