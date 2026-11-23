import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private lemma map_sub' {R S : Type} [CommRing R] [CommRing S] (β : R →+* S) {m n d e : ℕ}
    (a : Fin m → Fin d → PS R n e) (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (f : PS R m d)
    (a' : Fin m → Fin d → PS S n e) (h : ∀ i j, MvPowerSeries.map β (a i j) = a' i j) :
    MvPowerSeries.map β (sub a f) = sub a' (MvPowerSeries.map β f) := by
  unfold sub
  rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (a := fun q : Fin m × Fin d => a q.1 q.2) (fun q => ha q.1 q.2))]
  simp only [h]

private lemma cc_sub {R : Type} [CommRing R] {m n d e : ℕ}
    (a : Fin m → Fin d → PS R n e) (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (f : PS R m d)
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (sub a f) = 0 := by
  unfold sub
  exact MvPowerSeries.constantCoeff_subst_eq_zero
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (a := fun q : Fin m × Fin d => a q.1 q.2)
      (fun q => ha q.1 q.2)) (fun q => ha q.1 q.2) hf

private lemma ev_eq {R : Type} [CommRing R] {m n d : ℕ} (a : Fin m → Fin d → PS R n d) (f : PS R m d) :
    ev a f = sub a f := rfl

private lemma map_pt {R S : Type} [CommRing R] [CommRing S] (β : R →+* S) {n d : ℕ} (j : Fin n) (i : Fin d) :
    MvPowerSeries.map β (pt R d j i) = pt S d j i := by simp [pt]

private lemma cc_pt {R : Type} [CommRing R] {n d : ℕ} (j : Fin n) (i : Fin d) :
    MvPowerSeries.constantCoeff (pt R d j i) = 0 := by simp [pt]

private lemma map_subst_single {R S : Type} [CommRing R] [CommRing S] (β : R →+* S) {n d e : ℕ}
    (x : Fin d → PS R n e) (hx : ∀ j, MvPowerSeries.constantCoeff (x j) = 0) (f : PS R 1 d) :
    MvPowerSeries.map β (sub ![x] f) =
      sub ![fun j => MvPowerSeries.map β (x j)] (MvPowerSeries.map β f) :=
  map_sub' β _ (fun i j => by fin_cases i; exact hx j) f _ (fun i j => by fin_cases i; rfl)

private lemma map_sub_pair_eq_sub_map_of_constantCoeff_eq_zero {R S : Type} [CommRing R] [CommRing S] (β : R →+* S) {n d e : ℕ}
    (x y : Fin d → PS R n e) (hx : ∀ j, MvPowerSeries.constantCoeff (x j) = 0)
    (hy : ∀ j, MvPowerSeries.constantCoeff (y j) = 0) (f : PS R 2 d) :
    MvPowerSeries.map β (sub ![x, y] f) =
      sub ![fun j => MvPowerSeries.map β (x j), fun j => MvPowerSeries.map β (y j)] (MvPowerSeries.map β f) :=
  map_sub' β _ (fun i j => by
    fin_cases i
    · exact hx j
    · exact hy j) f _ (fun i j => by fin_cases i <;> rfl)

private lemma constCoeff_subst_single {R : Type} [CommRing R] {n d e : ℕ}
    (x : Fin d → PS R n e) (hx : ∀ j, MvPowerSeries.constantCoeff (x j) = 0) (f : PS R 1 d)
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (sub ![x] f) = 0 :=
  cc_sub _ (fun i j => by fin_cases i; exact hx j) f hf

private lemma constantCoeff_sub2_eq_zero {R : Type} [CommRing R] {n d e : ℕ}
    (x y : Fin d → PS R n e) (hx : ∀ j, MvPowerSeries.constantCoeff (x j) = 0)
    (hy : ∀ j, MvPowerSeries.constantCoeff (y j) = 0) (f : PS R 2 d)
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (sub ![x, y] f) = 0 :=
  cc_sub _ (fun i j => by
    fin_cases i
    · exact hx j
    · exact hy j) f hf

private lemma isHomF_map {R S : Type} [CommRing R] [CommRing S] (β : R →+* S) {d e : ℕ}
    (F : Fin d → PS R 2 d) (F' : Fin e → PS R 2 e) (φ : Fin e → PS R 1 d)
    (hF : ∀ j, MvPowerSeries.constantCoeff (F j) = 0) (h : IsHomF F F' φ) :
    IsHomF (fun j => MvPowerSeries.map β (F j)) (fun j => MvPowerSeries.map β (F' j))
      (fun j => MvPowerSeries.map β (φ j)) := by
  obtain ⟨h0, h1⟩ := h
  refine ⟨fun j => by simp [MvPowerSeries.constantCoeff_map, h0], fun j => ?_⟩
  have := congrArg (MvPowerSeries.map β) (h1 j)
  simp only [ev_eq] at this ⊢
  rw [map_subst_single β _ hF, map_sub_pair_eq_sub_map_of_constantCoeff_eq_zero β _ _ (fun i => constCoeff_subst_single _ (cc_pt _) _ (h0 i))
    (fun i => constCoeff_subst_single _ (cc_pt _) _ (h0 i))] at this
  simp only [map_subst_single β _ (cc_pt _), map_pt] at this
  exact this

private lemma lin_map {R S : Type} [CommRing R] [CommRing S] (β : R →+* S) {d e : ℕ} (φ : Fin e → PS R 1 d) :
    lin (fun j => MvPowerSeries.map β (φ j)) = (lin φ).map β := by
  ext i j
  simp [lin, MvPowerSeries.coeff_map]

private noncomputable def mapLaw {R S : Type} [CommRing R] [CommRing S] (β : R →+* S) {d : ℕ} (F : FGLaw R d) :
    FGLaw S d where
  F := F.mapF β
  const i := by simp [FGLaw.mapF, MvPowerSeries.constantCoeff_map, F.const]
  unit i := by
    have := congrArg (MvPowerSeries.map β) (F.unit i)
    simp only [ev_eq] at this ⊢
    rw [map_sub_pair_eq_sub_map_of_constantCoeff_eq_zero β _ _ (fun _ => by simp) (cc_pt _)] at this
    simp only [map_pt, Pi.zero_apply, map_zero, MvPowerSeries.map_X] at this
    exact this
  comm i := by
    have := congrArg (MvPowerSeries.map β) (F.comm i)
    simp only [ev_eq] at this ⊢
    rw [map_sub_pair_eq_sub_map_of_constantCoeff_eq_zero β _ _ (cc_pt _) (cc_pt _)] at this
    simp only [map_pt] at this
    exact this
  assoc i := by
    have := congrArg (MvPowerSeries.map β) (F.assoc i)
    simp only [ev_eq] at this ⊢
    rw [map_sub_pair_eq_sub_map_of_constantCoeff_eq_zero β _ _ (fun l => constantCoeff_sub2_eq_zero _ _ (cc_pt _) (cc_pt _) _ (F.const l)) (cc_pt _),
      map_sub_pair_eq_sub_map_of_constantCoeff_eq_zero β _ _ (cc_pt _) (fun l => constantCoeff_sub2_eq_zero _ _ (cc_pt _) (cc_pt _) _ (F.const l))] at this
    simp only [map_sub_pair_eq_sub_map_of_constantCoeff_eq_zero β _ _ (cc_pt _) (cc_pt _), map_pt] at this
    exact this

theorem changeCoeff_law_lin_extSer : ∀ (R S : Type) [CommRing R] [CommRing S] (β : R →+* S), (∀ (d : ℕ) (F : FGLaw R d), ∃ F' : FGLaw S d, F'.F = F.mapF β) ∧ (∀ (d e : ℕ) (φ : Fin e → PS R 1 d), lin (fun j => MvPowerSeries.map β (φ j)) = (lin φ).map β) ∧ ∀ (d g r : ℕ) (F : FGLaw R d) (FB : FGLaw R g) (J : Fin d → PS R 1 r) (Q : Fin g → PS R 1 d), ExtSer F.F FB.F J Q → ExtSer (F.mapF β) (FB.mapF β) (fun j => MvPowerSeries.map β (J j)) (fun j => MvPowerSeries.map β (Q j)) := by
  intro R S _ _ β
  refine ⟨fun d F => ⟨mapLaw β F, rfl⟩, fun d e φ => lin_map β φ, fun d g r F FB J Q h => ⟨?_, ?_, ?_⟩⟩
  · have hg : (fun j => MvPowerSeries.map β (gmF R r j)) = gmF S r := by
      funext j; simp [gmF]
    rw [← hg]
    exact isHomF_map β _ _ _ (fun j => by simp [gmF]) h.homI
  · exact isHomF_map β _ _ _ F.const h.homQ
  · rw [lin_map, lin_map]
    obtain ⟨h0, A', B', h1, h2, h3⟩ := h.exact
    refine ⟨?_, A'.map β, B'.map β, ?_, ?_, ?_⟩
    · rw [← Matrix.map_mul, h0]; simp
    · rw [← Matrix.map_mul, h1]; simp
    · rw [← Matrix.map_mul, h2]; simp
    · rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add β), h3]; simp

end GlobalTheory.ChF
