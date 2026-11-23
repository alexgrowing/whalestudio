import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureDivisibilityMapStatement
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff

theorem existsUnique_intertwines : ∀ (p : ℕ) [Fact p.Prime] (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (GG : PDivGroup p R) (θ : TorsionMap G GG), IsModel K θ → ∀ f : G ⟶ G, IsMonHom f → ∃! g : GG ⟶ GG, θ.Intertwines f g := by
  intro p _ R K _ _ _ _ _ _ _ _ G _ _ hG GG θ hθ f hf
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have lev := fun n m (h : n ≤ m) => GlobalTheory.T.level_structure_divisibility_map R K G hG (p ^ n) (p ^ m) (pow_ne_zero n hp) (pow_dvd_pow p h)
    (GG.A n) (GG.A m) (θ.level n) (θ.level m) (hθ n) (hθ m) f hf
  choose g hg hu using fun n => lev n n le_rfl
  refine ⟨⟨g, fun n => ?_⟩, fun n B _ _ z z' h => hg n B z z' h, fun g' hg' => PDivGroup.hom_ext fun n => ?_⟩
  · refine (lev n (n + 1) n.le_succ).unique (fun B _ _ z z' h => ?_) (fun B _ _ z z' h => ?_)
    · have h1 := hg (n + 1) B (torsIncl (pow_dvd_pow p n.le_succ) z) z' h
      have h2 := θ.res n B z (torsIncl (pow_dvd_pow p n.le_succ) z) rfl
      change θ.pt (n + 1) B z' = (θ.pt (n + 1) B _).comp _ at h1
      rw [h2] at h1
      exact h1
    · have hz : (z.1 ≫ f) ^ (p ^ n) = 1 := by
        rw [← MonObj.pow_comp, z.2, MonObj.one_comp]
      have h1 := hg n B z ⟨z.1 ≫ f, hz⟩ rfl
      have h2 := θ.res n B ⟨z.1 ≫ f, hz⟩ z' h
      change θ.pt n B _ = (θ.pt n B z).comp _ at h1
      rw [h1] at h2
      exact h2
  · exact hu n (g'.app n) fun B _ _ z z' h => hg' n B z z' h

end GlobalTheory.GroupBplus.Aff
