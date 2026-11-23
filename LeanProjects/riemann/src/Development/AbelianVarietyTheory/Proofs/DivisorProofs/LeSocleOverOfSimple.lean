import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne

noncomputable section

namespace GlobalTheory.ThKLocSS

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def OpStable (T : Set (Module.End ℂ V)) (P : Submodule ℂ V) : Prop := ∀ t ∈ T, ∀ x ∈ P, t x ∈ P

def IsSimpleOver (T : Set (Module.End ℂ V)) (N S : Submodule ℂ V) : Prop :=
  N < S ∧ OpStable T S ∧ ∀ S' : Submodule ℂ V, N ≤ S' → S' ≤ S → OpStable T S' → S' = N ∨ S' = S

def socleOver (T : Set (Module.End ℂ V)) (N D : Submodule ℂ V) : Submodule ℂ V :=
  N ⊔ sSup {S | S ≤ D ∧ IsSimpleOver T N S}

theorem le_socleOver (T : Set (Module.End ℂ V)) (N D : Submodule ℂ V) : N ≤ socleOver T N D := le_sup_left

theorem socleOver_le (T : Set (Module.End ℂ V)) {N D : Submodule ℂ V} (h : N ≤ D) : socleOver T N D ≤ D :=
  sup_le h (sSup_le fun _ hS => hS.1)

theorem le_socleOver_of_simple (T : Set (Module.End ℂ V)) {N D S : Submodule ℂ V} (hSD : S ≤ D)
    (hS : IsSimpleOver T N S) : S ≤ socleOver T N D :=
  le_sup_of_le_right (le_sSup ⟨hSD, hS⟩)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def opsAt {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (om : Rep σ Y W) (v : Pl F) : Set (Module.End ℂ (Fn F n d)) :=
  (fun h => om (1, h)) '' UAt σ W (evFin F v)

theorem opStable_opsAt_iff {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (om : Rep σ Y W) (v : Pl F)
    (P : Submodule ℂ (Fn F n d)) :
    OpStable (opsAt om v) P ↔ ∀ h ∈ UAt σ W (evFin F v), ∀ Φ ∈ P, om (1, h) Φ ∈ P := by
  constructor
  · intro hP h hh Φ hΦ
    exact hP _ ⟨h, hh, rfl⟩ Φ hΦ
  · rintro hP _ ⟨h, hh, rfl⟩ Φ hΦ
    exact hP h hh Φ hΦ

end GlobalTheory.ThKLocSS

end
