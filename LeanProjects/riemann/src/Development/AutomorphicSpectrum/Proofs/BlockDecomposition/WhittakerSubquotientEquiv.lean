import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitImgMono
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerTwoBlockIntertwinersSpanStatement

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.BZNuPair

namespace GlobalTheory.CompanionTheory.BZNuPair.WhitCover

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y : Type} [AddCommGroup Y] [Module ℂ Y]

def toImg (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (J : Representation ℂ (Levi k fun a => Fin (d a)) Y)
    (T : Subrepresentation J) : T.toSubmodule →ₗ[ℂ] (whitImg ψ d J T).toSubmodule :=
  LinearMap.codRestrict _ ((whitKer ψ d J).mkQ ∘ₗ T.toSubmodule.subtype) fun t => ⟨t, t.2, rfl⟩

def stepMap (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (J : Representation ℂ (Levi k fun a => Fin (d a)) Y)
    (T T' : Subrepresentation J) :
    (T.toSubmodule ⧸ T'.toSubmodule.comap T.toSubmodule.subtype) →ₗ[ℂ]
      ((whitImg ψ d J T).toSubmodule ⧸
        (whitImg ψ d J T').toSubmodule.comap (whitImg ψ d J T).toSubmodule.subtype) :=
  Submodule.liftQ _ (Submodule.mkQ _ ∘ₗ toImg ψ d J T) fun t ht => by
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    exact ⟨t, ht, rfl⟩

theorem stepMap_surjective (ψ : AddChar k Circle) (d : Fin 2 → ℕ)
    (J : Representation ℂ (Levi k fun a => Fin (d a)) Y) (T T' : Subrepresentation J) :
    Function.Surjective (stepMap ψ d J T T') := by
  intro y
  obtain ⟨⟨_, t, ht, rfl⟩, rfl⟩ := Submodule.mkQ_surjective _ y
  exact ⟨Submodule.Quotient.mk ⟨t, ht⟩, rfl⟩

theorem whitKer_subQuot_le (ψ : AddChar k Circle) (d : Fin 2 → ℕ)
    (J : Representation ℂ (Levi k fun a => Fin (d a)) Y) (T T' : Subrepresentation J) :
    whitKer ψ d (subQuot T T') ≤ LinearMap.ker (stepMap ψ d J T T') := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨u, v, rfl⟩
  obtain ⟨t, rfl⟩ := Submodule.mkQ_surjective _ v
  let s : T.toSubmodule := T.toRepresentation (secondEmb d (u : GL (Fin (d 1)) k)) t - ((whitChar ψ (d 1) u : ℂˣ) : ℂ) • t
  have h0 : toImg ψ d J T s = 0 := by
    apply Subtype.ext
    exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span ⟨u, (t : Y), rfl⟩)
  show stepMap ψ d J T T' (Submodule.Quotient.mk s) = 0
  show Submodule.mkQ _ (toImg ψ d J T s) = 0
  rw [h0, map_zero]

def coverMap (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (J : Representation ℂ (Levi k fun a => Fin (d a)) Y)
    (T T' : Subrepresentation J) :
    (whit2 ψ d (subQuot T T')).IntertwiningMap (subQuot (whitImg ψ d J T) (whitImg ψ d J T')) :=
  .mk ((whitKer ψ d (subQuot T T')).liftQ (stepMap ψ d J T T') (whitKer_subQuot_le ψ d J T T')) fun g => by
    ext v
    rfl

theorem coverMap_surjective (ψ : AddChar k Circle) (d : Fin 2 → ℕ)
    (J : Representation ℂ (Levi k fun a => Fin (d a)) Y) (T T' : Subrepresentation J) :
    Function.Surjective (coverMap ψ d J T T') := by
  intro y
  obtain ⟨x, rfl⟩ := stepMap_surjective ψ d J T T' y
  exact ⟨Submodule.Quotient.mk x, rfl⟩

theorem iSup_range_of_surjective {G A B C : Type} [Group G] [AddCommGroup A] [Module ℂ A] [AddCommGroup B]
    [Module ℂ B] [AddCommGroup C] [Module ℂ C] {α : Representation ℂ G A} {β : Representation ℂ G B}
    {γ : Representation ℂ G C} (p : β.IntertwiningMap γ) (hp : Function.Surjective p)
    (h : ⨆ f : α.IntertwiningMap β, LinearMap.range f.toLinearMap = ⊤) :
    ⨆ f : α.IntertwiningMap γ, LinearMap.range f.toLinearMap = ⊤ := by
  rw [eq_top_iff]
  have h1 : (⊤ : Submodule ℂ C) = (⊤ : Submodule ℂ B).map p.toLinearMap := by
    rw [Submodule.map_top]
    exact (LinearMap.range_eq_top.2 hp).symm
  rw [h1, ← h, Submodule.map_iSup]
  refine iSup_le fun f => ?_
  refine le_trans ?_ (le_iSup _ (p.comp f))
  rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
  exact ⟨v, rfl⟩

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (Y : Type) [AddCommGroup Y] [Module ℂ Y]
    (J : Representation ℂ (Levi k fun a => Fin (d a)) Y) (T T' : Subrepresentation J) (X : Fin 2 → Type)
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)),
    T' ≤ T → (subQuot T T').Equiv (piTensor ρ) →
    ⨆ f : (ρ 0).IntertwiningMap (subQuot (whitImg ψ d J T) (whitImg ψ d J T')), LinearMap.range f.toLinearMap = ⊤ := by
  intro k _ _ _ _ ψ d Y _ _ J T T' X _ _ ρ _ E
  have hE : Function.Surjective (whitMap ψ d E.symm.toIntertwiningMap) := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
    exact ⟨Submodule.Quotient.mk (E x), by
      show Submodule.Quotient.mk (E.symm (E x)) = _
      rw [E.symm_apply_apply]; rfl⟩
  exact iSup_range_of_surjective ((coverMap ψ d J T T').comp (whitMap ψ d E.symm.toIntertwiningMap))
    ((coverMap_surjective ψ d J T T').comp hE) (GlobalTheory.T.whittaker_two_block_intertwiners_span k ψ d X ρ)

end GlobalTheory.CompanionTheory.BZNuPair.WhitCover

end
