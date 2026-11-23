import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsDataDualGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelCharacterAtConjugateSplitPlace
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

noncomputable section

namespace GlobalTheory.CosocleComp

variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def subrepOfComp (ρ : Representation ℂ G V) (s : H →* G) (hs : Function.Surjective s) :
    Subrepresentation (ρ.comp s : Representation ℂ H V) ≃o Subrepresentation ρ where
  toFun S := ⟨S.toSubmodule, fun g v hv => by
    obtain ⟨h, rfl⟩ := hs g
    exact S.apply_mem_toSubmodule h hv⟩
  invFun S := ⟨S.toSubmodule, fun h _ hv => S.apply_mem_toSubmodule (s h) hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem isIrreducible_comp {ρ : Representation ℂ G V} {s : H →* G} (hs : Function.Surjective s)
    (h : ρ.IsIrreducible) : Representation.IsIrreducible (ρ.comp s : Representation ℂ H V) :=
  (subrepOfComp ρ s hs).isSimpleOrder_iff.2 h

theorem isCosocle_comp : ∀ (G H V W : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (σ : Representation ℂ G W) (π : Representation ℂ G V) (s : H →* G), Function.Surjective s →
    IsCosocle σ π → IsCosocle (σ.comp s) (π.comp s) := by
  intro G H V W _ _ _ _ _ _ σ π s hs h
  obtain ⟨hi, f, hf, hS⟩ := h
  let f' : Representation.IntertwiningMap (π.comp s : Representation ℂ H V) (σ.comp s : Representation ℂ H W) := ⟨f.toLinearMap, fun g => f.isIntertwining' (s g)⟩
  refine ⟨isIrreducible_comp hs hi, f', hf, fun S hS' => ?_⟩
  have h1 := hS (subrepOfComp π s hs S) ((OrderIso.isCoatom_iff (subrepOfComp π s hs) S).2 hS')
  have h2 := congrArg Subrepresentation.toSubmodule h1
  have inj : Function.Injective (Subrepresentation.toSubmodule (ρ := (π.comp s : Representation ℂ H V))) := by
    rintro ⟨a, _⟩ ⟨b, _⟩ rfl; rfl
  exact inj h2

end GlobalTheory.CosocleComp
