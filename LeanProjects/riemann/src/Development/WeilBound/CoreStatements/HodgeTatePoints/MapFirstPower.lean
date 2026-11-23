import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBMapPf

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace PositivityTheory.HtPt.Cc

open Formalism.MainNotions.ModuliIntegralCharts.H1.FBMap in
theorem map_first_power {R R₂ : Type} [CommRing R] [CommRing R₂] {f : R →+* R₂} {d : ℕ} {O : Type} [CommRing O]
    [StarRing O] {B : FB R d O} {B₂ : FB R₂ d O} (h : IsMapOf f B B₂) (m : ℕ) :
    pow1 B₂ m = MvPowerSeries.map f (pow1 B m) := by
  have hact : ∀ a : O, mp f (B.A.act a) = B₂.A.act a := fun a => funext fun i => (h.act a i).symm
  unfold pow1
  rw [map_prod]
  refine Finset.prod_congr rfl fun n _ => ?_
  have hc : ∀ (j : Fin 3) (i : Fin d),
      constantCoeff ((![comp1 (B.A.act (n : O)) (pt R d 0), pt R d 0, pt R d 1] : Fin 3 → Pt R 2 d) j i) = 0 := by
    intro j i
    fin_cases j
    · exact cz_comp1 _ (B.A.const _) _ (cz_pt 0) i
    · exact cz_pt 0 i
    · exact cz_pt 1 i
  rw [map_ev' f _ hc B.ph1, ← h.ph1]
  congr 1
  funext j
  fin_cases j
  · simp [mp_comp1 f _ _ (cz_pt 0), mp_pt, hact]
  · simp [mp_pt]
  · simp [mp_pt]

private theorem lin_map' {R R₂ : Type} [CommRing R] [CommRing R₂] (f : R →+* R₂) {d : ℕ}
    (φ : Pt R 1 d) (m : ℕ) : lin (fun i => MvPowerSeries.map f (φ i)) m = (lin φ m).map f := by
  ext i j
  simp [lin, Matrix.map_apply, MvPowerSeries.coeff_map]

private theorem bil_map' {R R₂ : Type} [CommRing R] [CommRing R₂] (f : R →+* R₂) {d : ℕ}
    (g : PS R 2 d) (m n : ℕ) : bil (MvPowerSeries.map f g) m n = (bil g m n).map f := by
  ext i j
  simp [bil, Matrix.map_apply, MvPowerSeries.coeff_map]

theorem map_mats : ∀ (R R₂ : Type) [CommRing R] [CommRing R₂] (f : R →+* R₂) (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (B₂ : FB R₂ d O), IsMapOf f B B₂ → (∀ a, rho B₂ a = (rho B a).map f ∧ bil (B₂.ad a) 1 1 = (bil (B.ad a) 1 1).map f) ∧ bil B₂.sy 1 1 = (bil B.sy 1 1).map f ∧ ∀ p, hw B₂ p = (hw B p).map f ∧ am B₂ p = (am B p).map f := by
  intro R R₂ _ _ f d O _ _ B B₂ h
  have hact : ∀ a : O, B₂.A.act a = fun i => MvPowerSeries.map f (B.A.act a i) :=
    fun a => funext fun i => h.act a i
  refine ⟨fun a => ⟨?_, ?_⟩, ?_, fun p => ⟨?_, ?_⟩⟩
  · show lin (B₂.A.act a) 1 = _
    rw [hact, lin_map']
    rfl
  · rw [h.ad, bil_map']
  · rw [h.sy, bil_map']
  · show lin (B₂.A.act (p : O)) p = _
    rw [hact, lin_map']
    rfl
  · show bil (pow1 B₂ p) p 1 = _
    rw [map_first_power h, bil_map']
    rfl

end PositivityTheory.HtPt.Cc
