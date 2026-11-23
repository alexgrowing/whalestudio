import Mathlib
import GroundTheory.AutomorphicForms.WhittakerCriterion
import GroundTheory.AutomorphicForms.ContragredientTranspose.GelfandKazhdan
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipApplyCastSuccLast

noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.Whittaker GlobalTheory.BZMir

namespace PositivityTheory.PfBern.ThmA

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def ConjInvariant (H : Subgroup G) (D : Module.Dual ℂ (locallyConstantCompactSupport G ℂ ℂ)) : Prop :=
  ∀ h ∈ H, ∀ f : locallyConstantCompactSupport G ℂ ℂ, D (biTranslL h h f) = D f

theorem ConjInvariant.mono {H K : Subgroup G} (hHK : H ≤ K)
    {D : Module.Dual ℂ (locallyConstantCompactSupport G ℂ ℂ)} (hD : ConjInvariant K D) :
    ConjInvariant H D :=
  fun h hh f => hD h (hHK hh) f

def deltaOne : Module.Dual ℂ (locallyConstantCompactSupport G ℂ ℂ) :=
  (LinearMap.proj (R := ℂ) (φ := fun _ : G => ℂ) (1 : G)).comp (locallyConstantCompactSupport G ℂ ℂ).subtype

theorem conjInvariant_deltaOne (H : Subgroup G) : ConjInvariant H (deltaOne (G := G)) := by
  intro h _ f
  show (biTranslL h h f : G → ℂ) 1 = (f : G → ℂ) 1
  rw [coe_biTranslL]
  simp

def BernsteinTheoremA : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (D : Module.Dual ℂ (locallyConstantCompactSupport (GL (Fin (n + 1)) k) ℂ ℂ)),
    ConjInvariant (Mir k n) D → ConjInvariant ⊤ D

def BernsteinTheoremA' : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (D : Module.Dual ℂ (locallyConstantCompactSupport (GL (Fin (n + 1)) k) ℂ ℂ)),
    (∀ p : GL (Fin (n + 1)) k, p ∈ Mir k n → ∀ f, D (biTranslL p p f) = D f) →
    ∀ (g : GL (Fin (n + 1)) k) f, D (biTranslL g g f) = D f

theorem bernsteinTheoremA_iff : BernsteinTheoremA ↔ BernsteinTheoremA' := by
  constructor
  · intro H k _ _ _ _ n D hD g f
    exact H k n D hD g (Subgroup.mem_top g) f
  · intro H k _ _ _ _ n D hD g _ f
    exact H k n D hD g f

theorem conjInvariant_deltaOne' (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) :
    ConjInvariant (Mir k n) (deltaOne (G := GL (Fin (n + 1)) k)) ∧
      ConjInvariant ⊤ (deltaOne (G := GL (Fin (n + 1)) k)) :=
  ⟨conjInvariant_deltaOne _, conjInvariant_deltaOne _⟩

theorem deltaOne_ne_zero (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) : deltaOne (G := GL (Fin (n + 1)) k) ≠ 0 := by
  obtain ⟨K, hK⟩ := exists_compactOpenSubgroup (G := GL (Fin (n + 1)) k)
  intro h
  let f : locallyConstantCompactSupport (GL (Fin (n + 1)) k) ℂ ℂ :=
    ⟨(K : Set (GL (Fin (n + 1)) k)).indicator (fun _ => (1 : ℂ)),
      indicator_mem_locallyConstantCompactSupport hK K.isOpen 1⟩
  have h1 : deltaOne (G := GL (Fin (n + 1)) k) f = 1 := by
    show (K : Set (GL (Fin (n + 1)) k)).indicator (fun _ => (1 : ℂ)) 1 = 1
    exact Set.indicator_of_mem (one_mem K) _
  rw [h, LinearMap.zero_apply] at h1
  exact zero_ne_one h1

end PositivityTheory.PfBern.ThmA

end
