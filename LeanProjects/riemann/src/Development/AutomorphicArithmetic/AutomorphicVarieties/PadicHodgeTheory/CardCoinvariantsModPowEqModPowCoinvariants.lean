import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateDefs
import ReciprocityTheory.GroupCohomology.ImportsAlt

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

theorem UpperTheory.card_coinvariants_mod_pow_eq_mod_pow_coinvariants :
    ∀ {l : ℕ} [Fact l.Prime] {G X : Type} [Group G] [AddCommGroup X] [Module ℤ_[l] X] (χ : G →* ℤ_[l]ˣ) (ρ : Representation ℤ_[l] G X) (m : ℕ), Nat.card ((X ⧸ lSub l X m) ⧸ coSub χ (redRep ρ m)) = Nat.card ((X ⧸ coSub χ ρ) ⧸ lSub l (X ⧸ coSub χ ρ) m) := by
  intro l _ G X _ _ _ χ ρ m
  have hq : ∀ g x, UpperTheory.V.Loc.redRep ρ m g ((lSub l X m).mkQ x) = (lSub l X m).mkQ (ρ g x) :=
    fun g x => rfl
  have hC : coSub χ (UpperTheory.V.Loc.redRep ρ m) = (coSub χ ρ).map (lSub l X m).mkQ := by
    unfold coSub
    rw [Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨g, x, rfl⟩
      obtain ⟨x, rfl⟩ := (lSub l X m).mkQ_surjective x
      exact ⟨ρ g x - (χ g : ℤ_[l]) • x, ⟨g, x, rfl⟩, by rw [map_sub, map_smul, hq]⟩
    · rintro ⟨_, ⟨g, x, rfl⟩, rfl⟩
      exact ⟨g, (lSub l X m).mkQ x, by rw [map_sub, map_smul, hq]⟩
  have hL : lSub l (X ⧸ coSub χ ρ) m = (lSub l X m).map (coSub χ ρ).mkQ := by
    ext y
    rw [mem_lSub, Submodule.mem_map]
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨z, rfl⟩ := (coSub χ ρ).mkQ_surjective z
      exact ⟨(l : ℤ_[l]) ^ m • z, mem_lSub.2 ⟨z, rfl⟩, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨z, rfl⟩ := mem_lSub.1 hx
      exact ⟨(coSub χ ρ).mkQ z, by simp⟩
  rw [hC, hL]
  exact Nat.card_congr ((Submodule.quotientQuotientEquivQuotientSup _ _).toEquiv.trans
    ((Submodule.quotEquivOfEq _ _ (sup_comm _ _)).toEquiv.trans
      (Submodule.quotientQuotientEquivQuotientSup _ _).symm.toEquiv))
