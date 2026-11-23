import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeMapPull

universe w w' w₁ w₁' u v u' v'

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'}
  {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {F : C ⥤ ModuleCat.{w'} R} {F' : C' ⥤ ModuleCat.{w₁'} R'}
  {T : Res.{w} F} {T' : Res.{w₁} F'} {m : Mor F F' σ}

theorem d_pullC (n : ResMor T T' m) (s k : ℕ) (x : Cn (T.K s) k) :
    d (T'.K s) k (n.pullC s k x) = n.pullC s (k + 1) (d (T.K s) k x) := by
  funext t
  change ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • ((T'.K s).map (GlobalTheory.CatH.toLast i t)).hom
      (n.τ s _ (x (GlobalTheory.CatH.face i t ⋙ m.G))) =
    n.τ s _ (∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
      ((T.K s).map (m.G.map (GlobalTheory.CatH.toLast i t))).hom (x (GlobalTheory.CatH.face i t ⋙ m.G)))
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_zsmul, n.nat]

theorem dvC_pullC (n : ResMor T T' m) (s k : ℕ) (x : Cn (T.K s) k) :
    T'.dvC s k (n.pullC s k x) = n.pullC (s + 1) k (T.dvC s k x) :=
  funext fun t => (n.dv s _ (x (t ⋙ m.G))).symm

theorem ιC_pullC (n : ResMor T T' m) (k : ℕ) (z : Cn F k) :
    T'.ιC k (m.pullC k z) = n.pullC 0 k (T.ιC k z) :=
  funext fun t => (n.ι _ (z (t ⋙ m.G))).symm

theorem pullC_zsmul (n : ResMor T T' m) (s k : ℕ) (c : ℤ) (x : Cn (T.K s) k) :
    n.pullC s k (c • x) = c • n.pullC s k x :=
  funext fun t => map_zsmul (n.τ s _) c (x (t ⋙ m.G))

theorem st_pullC (n : ResMor T T' m) {j : ℕ} (z : Cn F j) :
    ∀ (s k : ℕ) (x : Cn (T.K s) k), T.St z s k x → T'.St (m.pullC j z) s k (n.pullC s k x)
  | 0, k, x, h => by
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, ιC_pullC n j z⟩
  | s + 1, k, x, h => by
    obtain ⟨a, rfl, ha⟩ := h
    refine ⟨n.pullC s k a, dvC_pullC n s k a, ?_⟩
    have := st_pullC n z s (k + 1) _ ha
    rwa [pullC_zsmul, ← d_pullC] at this

end GlobalTheory.CompanionTheory.EdgeMapPull

open GlobalTheory.CompanionTheory.EdgeMapPull in

theorem GlobalTheory.CompanionTheory.EdgeMapPull.edgeMap : CrystallineSemistableComparison.E.EdgeMap := by
  intro R R' _ _ σ C C' _ _ F F' T T' m n j x h hE
  obtain ⟨z, hz, hS, rfl⟩ := hE
  exact ⟨m.pullC j z, by rw [m.d_pullC, hz, map_zero], st_pullC n z j 0 x hS, rfl⟩
