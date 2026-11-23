import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOneOfCharpoly
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU

theorem exists_open_sub_charKer : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w), ∀ (n : ℕ), ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a → ∀ g : Weil h, deg g ≠ 0 → ∃ V : Subgroup (Dec (F := E) A), IsOpen (V : Set (Dec (F := E) A)) ∧ commutator (Dec (F := E) A) ≤ V ∧ (⟨(g : G E Ω), Weil_le_Dec h g.2⟩ : Dec (F := E) A) ∈ V ∧ ∀ t : Ine (F := E) A, ∀ x ∈ V, (x : G E Ω) = t → ∀ j, ξ j (a (ineIncl h t)) = 1 := by
  intro Ω _ E _ _ _ _ w A h n ξ hξ a ha g hg
  let χ : Fin n → Weil h →* ℂˣ := fun j => (ξ j).comp a
  have hχ : ∀ j, IsSmooth (χ j) := fun j => ha.smooth (hξ j)
  let b := WDRep.ofChars h χ hχ
  have hy : AbW (WD.mk b) := by
    intro g₁ g₂
    rw [WD.charPol_mk, WD.lpDim_mk]
    have hc : ∀ i, χ i (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) = 1 := fun i => by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_right_comm (χ i g₁ * χ i g₂),
        mul_inv_cancel_right, mul_inv_cancel]
    have e : b.ρ (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) = 1 := by
      rw [WDRep.ofChars_ρ]
      refine LinearMap.ext fun v => funext fun i => ?_
      rw [diagEnd_apply, hc i, Units.val_one, one_mul, Module.End.one_apply]
    rw [e, LinearMap.charpoly_one]
  obtain ⟨V, hV1, hV2, hV3, hV4⟩ := GlobalTheory.AboveL.AbSub.exists_open_sub E Ω A w h (WD.mk b) hy g hg
  refine ⟨V, hV1, hV2, hV3, ?_⟩
  intro t x hx hxt j
  have hc := hV4 t x hx hxt
  rw [WD.charPol_mk, WD.lpDim_mk] at hc
  have h1 := GlobalTheory.AboveL.AbSub.eq_one_of_charpoly _ (b.semisimple _) hc
  have h2 := congrArg (fun f : Module.End ℂ (Fin n → ℂ) => f (Pi.single j 1) j) h1
  simp only [b, WDRep.ofChars_ρ, diagEnd_apply, Module.End.one_apply, Pi.single_eq_same, mul_one, χ,
    MonoidHom.comp_apply] at h2
  exact Units.ext h2

end GlobalTheory.RoadU
