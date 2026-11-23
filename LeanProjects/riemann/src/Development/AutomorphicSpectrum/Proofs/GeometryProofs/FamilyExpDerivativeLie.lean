import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExponentialFamilyPeriods
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLinearLiftOfAdditiveFamily
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HolDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyFamilyUnifIffUnifAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExpRowsPf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrameDeriv

def rho {R : Type} [CommRing R] (φ : R →+* ℂ) :
    epsAt (spMap φ) ⟶ epsAt (𝟙 (Sp R)) :=
  Over.homMk (spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ)) (by
    have hsq : spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ) ≫ spMap (algebraMap R (DualNumber R)) =
        spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap φ := by
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      refine RingHom.ext fun r => ?_
      ext <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    show spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ) ≫ spMap (algebraMap R (DualNumber R)) ≫ 𝟙 _ =
      spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap φ
    rw [Category.comp_id, hsq])

theorem dualMap_comp_epsMul {R : Type} [CommRing R] (φ : R →+* ℂ) (c : R) :
    (GlobalTheory.CompanionTheory.Ar.dualMap φ).comp (GlobalTheory.CompanionTheory.Ar.epsMul c) =
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (φ c)).comp (GlobalTheory.CompanionTheory.Ar.dualMap φ) := by
  refine RingHom.ext fun r => ?_
  ext <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, GlobalTheory.CompanionTheory.Ar.epsMul, ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul, mul_comm]

theorem lieModel_pt_zero {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {g : ℕ}
    (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) : M.pt 0 = 1 := by
  have h := M.add 0 0
  rw [add_zero] at h
  exact left_eq_mul.mp h

theorem isDerivAt0_pt {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {g n : ℕ}
    {M : LieModel G (𝟙 (Sp R)) (Fin g → R)} {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)}
    (e : FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) (u : Fin g → R) :
    IsDerivAt0 (fun z => (e.ex b z).left) (fun c => ψ b (u c))
      (spMap (GlobalTheory.CompanionTheory.Ar.dualMap (ψ b)) ≫ (M.pt u).left) := by
  have hF0 : (fun z => (e.ex b z).left) 0 = (1 : Over.mk (spMap (ψ b)) ⟶ G).left :=
    congrArg (·.left) (ExpLift.ex_zero e hb)
  let T : (Fin g → R) → (epsPt (spMap (ψ b)) ⟶ G) := fun u => rho (ψ b) ≫ M.pt u
  have hTl : ∀ u, (T u).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (ψ b)) ≫ (M.pt u).left := fun _ => rfl
  have hadd : ∀ u u', T (u + u') = T u * T u' := fun u u' => by
    simp only [T, M.add, MonObj.comp_mul]
  have hone : (T 0).left = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ (fun z => (e.ex b z).left) 0 := by
    let i₀ : epsPt (spMap (ψ b)) ⟶ Over.mk (spMap (ψ b)) :=
      Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl
    have h1 : T 0 = i₀ ≫ (1 : Over.mk (spMap (ψ b)) ⟶ G) := by
      simp only [T, lieModel_pt_zero, MonObj.comp_one]
    rw [h1, hF0]
    rfl
  have h0 : IsDerivAt0 (fun z => (e.ex b z).left) (fun c => ψ b ((0 : Fin g → R) c)) (T 0).left := by
    rw [hone]
    have : (fun c => ψ b ((0 : Fin g → R) c)) = (0 : Fin g → ℂ) := by
      funext c; simp
    rw [this]
    exact GlobalTheory.LocalLift.isDerivAt0_const _ 0 fun _ _ _ => map_zero _
  have hsm : ∀ (c : R) (w : Fin g → R),
      IsDerivAt0 (fun z => (e.ex b z).left) (fun c => ψ b (w c)) (T w).left →
      IsDerivAt0 (fun z => (e.ex b z).left) (fun d => ψ b ((c • w) d)) (T (c • w)).left := by
    intro c w h
    have h1 := ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_smul h (ψ b c)
    have h2 : (T (c • w)).left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (ψ b c)) ≫ (T w).left := by
      rw [hTl, hTl, M.smul, ← Category.assoc, ← Category.assoc]
      congr 1
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [dualMap_comp_epsMul]
    have h3 : (fun d => ψ b ((c • w) d)) = ψ b c • (fun d => ψ b (w d)) := by
      funext d; simp
    rw [h2, h3]
    exact h1
  have hsingle : ∀ a : Fin g,
      IsDerivAt0 (fun z => (e.ex b z).left) (fun c => ψ b ((Pi.single a 1 : Fin g → R) c))
        (T (Pi.single a 1)).left := by
    intro a
    have h3 : (fun c => ψ b ((Pi.single a 1 : Fin g → R) c)) = (Pi.single a 1 : Fin g → ℂ) := by
      funext c
      by_cases h : c = a
      · subst h; simp
      · simp [Pi.single_apply, h]
    rw [h3]
    exact e.diff b hb a
  have hs : ∀ s : Finset (Fin g), IsDerivAt0 (fun z => (e.ex b z).left)
      (fun c => ψ b ((∑ a ∈ s, u a • (Pi.single a 1 : Fin g → R)) c))
      (T (∑ a ∈ s, u a • (Pi.single a 1 : Fin g → R))).left := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, hadd]
      have h1 := GlobalTheory.UnifCompare.isDerivAt0_mul (y := spMap (ψ b)) (G := G) hF0
        (hsm (u a) _ (hsingle a)) ih
      have h3 : (fun c => ψ b ((u a • (Pi.single a 1 : Fin g → R) +
          ∑ a ∈ s, u a • (Pi.single a 1 : Fin g → R)) c)) =
          (fun d => ψ b ((u a • (Pi.single a 1 : Fin g → R)) d)) +
            (fun c => ψ b ((∑ a ∈ s, u a • (Pi.single a 1 : Fin g → R)) c)) := by
        funext c; simp only [Pi.add_apply, map_add]
      rw [h3]
      exact h1
  have hu : ∑ a, u a • (Pi.single a 1 : Fin g → R) = u := by
    funext c
    simp [Finset.sum_apply, Pi.single_apply]
  have := hs Finset.univ
  rw [hu] at this
  exact this

theorem isDerivAt0_frame_section : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : FamExp G M B ψ) (b : Fin n → ℂ), b ∈ B → ∀ u : Fin g → R, IsDerivAt0 (fun z => (e.ex b z).left) (fun c => ψ b (u c)) (spMap (dualMap (ψ b)) ≫ (M.pt u).left) :=
  fun _ _ _ _ _ _ _ _ _ _ e _ hb u => isDerivAt0_pt e hb u

end GlobalTheory.CompanionTheory.Ar.Flat.FrameDeriv
