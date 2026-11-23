import Development.EtaleCohomology.EtaleSheaves.EqvOfCompRight

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.CechSigma_xy1Pf_Lev
open LateralTheory.E.CechSigmaProof

def sqS {Y X : Scheme.{0}} (g : Y ⟶ X) (O : X.Opens) {ι : Type} (V : ι → X.Opens) (hV : ∀ j, V j ≤ O) :
    Arrow.mk (cov (g ⁻¹ᵁ O) (fun j => g ⁻¹ᵁ V j) (fun j => pre_le g (hV j))) ⟶ Arrow.mk (cov O V hV) :=
  Arrow.homMk (Limits.Sigma.map fun j => g ∣_ V j) (g ∣_ O) (sq_cov g O V hV)

def wpMap {A B C D : Scheme.{0}} {p : A ⟶ B} {q : C ⟶ D} (s : Arrow.mk p ⟶ Arrow.mk q) (n : ℕ) :
    widePullback B (fun _ : Fin (n + 1) => A) (fun _ => p) ⟶ widePullback D (fun _ : Fin (n + 1) => C) (fun _ => q) :=
  WidePullback.lift (WidePullback.base _ ≫ s.right) (fun i => WidePullback.π _ i ≫ s.left)
    (fun i => by have := Arrow.w s; simp only [Arrow.mk_hom] at this; simp [this])

def CechYoneda : Prop := ∀ {A B C D : Scheme.{0}} {p : A ⟶ B} {q : C ⟶ D} (s : Arrow.mk p ⟶ Arrow.mk q) (n : ℕ),
  Nonempty (Arrow.mk ((Arrow.mapCechNerve (yoneda.mapArrow.map s)).app (op (SimplexCategory.mk n))) ≅
    Arrow.mk (yoneda.map (wpMap s n)))

def SchemeLevel : Prop := ∀ {Y X : Scheme.{0}} (g : Y ⟶ X) (O : X.Opens) {ι : Type} (V : ι → X.Opens) (hV : ∀ j, V j ≤ O)
  (n : ℕ), Nonempty (Arrow.mk (wpMap (sqS g O V hV) n) ≅
    Arrow.mk (Limits.Sigma.map fun j : Fin (n + 1) → ι => g ∣_ (⨅ k, V (j k))))

theorem LevelIso_of (hY : CechYoneda) (hS : SchemeLevel) : LevelIso := by
  intro Y X g O ι V hV n
  obtain ⟨e1⟩ := hY (sqS g O V hV) n
  obtain ⟨e2⟩ := hS g O V hV n
  exact ⟨e1 ≪≫ yoneda.mapArrow.mapIso e2⟩

theorem CechSigma_of (hY : CechYoneda) (hS : SchemeLevel) : ZariskiLocalCech.CechSigma :=
  LateralTheory.E.CechSigmaProof.CechSigma_of (LevelIso_of hY hS)

end LateralTheory.E.CechSigma_xy1Pf_Lev
