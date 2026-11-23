import Development.EtaleCohomology.EtaleSheaves.CechLevelsGeneration

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.TruncCokPf Opposite

namespace LateralTheory.E.LevelsPf.Tp

def tp {D E : CommRingCat.{0}} (e : D ⟶ E) : ℕ → Σ C : CommRingCat.{0}, (D ⟶ C)
  | 0 => ⟨E, e⟩
  | p + 1 => ⟨pushout (tp e p).2 e, (tp e p).2 ≫ pushout.inl _ _⟩

theorem tp_mem {A D E : CommRingCat.{0}} (d : A ⟶ D) (e : D ⟶ E) (P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop)
    (hP : PushClosed P) (hD : P D d) (hE : P E (d ≫ e)) : ∀ p, P (tp e p).1 (d ≫ (tp e p).2)
  | 0 => hE
  | p + 1 => by
    have := hP d (tp e p).2 e (pushout.inl _ _) (pushout.inr _ _) (IsPushout.of_hasPushout _ _) hD (tp_mem d e P hP hD hE p) hE
    simpa [tp] using this

def CechLevelIso : Prop := ∀ (p : ℕ) {D E Y' Y'' : CommRingCat.{0}} (e : D ⟶ E) (φ' : D ⟶ Y') (u : Y' ⟶ Y'') (φ'' : E ⟶ Y'')
    (hpo : IsPushout φ' e u φ''),
    Nonempty (Arrow.mk ((Arrow.mapCechNerve (sq e φ' u φ'' hpo.w)).app (op (SimplexCategory.mk p))) ≅
      Arrow.mk (yoneda.map (Spec.map (pushout.inr φ' (tp e p).2))))

theorem CechLevel_of (h : CechLevelIso) : LateralTheory.E.LevelsPf.CechLevel := by
  intro p D E Y' Y'' e φ' u φ'' hpo
  exact ⟨(tp e p).1, pushout φ' (tp e p).2, (tp e p).2, pushout.inl _ _, pushout.inr _ _, IsPushout.of_hasPushout _ _,
    fun d P hP hD hE => tp_mem d e P hP hD hE p, h p e φ' u φ'' hpo⟩

theorem Levels_of' (h : CechLevelIso) : LateralTheory.E.TruncCokPf.Levels := Levels_of (CechLevel_of h)

end LateralTheory.E.LevelsPf.Tp
