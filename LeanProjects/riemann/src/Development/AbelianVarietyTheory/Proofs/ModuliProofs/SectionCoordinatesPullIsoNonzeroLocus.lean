import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjectiveRepresentationPullbackCoordinates
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubicalSymmetryTransport
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.CoordMove
open GlobalTheory.ZM.RepBC

theorem isUnit_cst_id {R : Type} [CommRing R] (p : Sp R) (a : R) : IsUnit (cst (𝟙 (Sp R)) p a) ↔ a ∉ p.asIdeal := by
  rw [cst, gs_eq _ _ ⊤ trivial]
  refine ((Sp R).mem_basicOpen (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) p trivial).symm.trans ?_
  have := basicOpen_eq_of_affine (R := CommRingCat.of R) a
  exact (congrArg (fun U : (Sp R).Opens => p ∈ U) this).to_iff

theorem secCoord_iff {X : Scheme.{0}} (M : LB X) {I : Type} (th : I → M.Sec) {R : Type} [CommRing R] (x : Sp R ⟶ X)
    (v : I → R) : SecCoord M th x v ↔ ∃ τ : (M.pull x).Gen, τ.IsGen ∧ ∀ (i : I) (j : PUnit → M.ι) (p : Sp R),
      p ∈ (M.pull x).U j → gs x p _ ((th i).f (j PUnit.unit)) =
        cst (𝟙 (Sp R)) p (v i) * (gm (𝟙 (Sp R)) p ((M.pull x).U j) (τ.s j)).val := by
  refine exists_congr fun τ => and_congr_right fun _ => forall₂_congr fun i j => ?_
  have l : ∀ (h : (M.pull x).U j ≤ x ⁻¹ᵁ M.U (j PUnit.unit)) (p : Sp R), p ∈ (M.pull x).U j →
      gs (𝟙 (Sp R)) p ((M.pull x).U j) ((x.appLE _ _ h).hom ((th i).f (j PUnit.unit))) =
        gs x p _ ((th i).f (j PUnit.unit)) := fun h p hp =>
    (gs_appLE x _ _ h (𝟙 _) p hp _).trans (by rw [Category.id_comp])
  have r : ∀ (p : Sp R), p ∈ (M.pull x).U j → gs (𝟙 (Sp R)) p ((M.pull x).U j)
      (resG (Sp R) le_top ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v i)) *
        (show Γ(Sp R, (M.pull x).U j) from (τ.s j).val)) =
      cst (𝟙 (Sp R)) p (v i) * (gm (𝟙 (Sp R)) p ((M.pull x).U j) (τ.s j)).val := fun p hp =>
    (gs_mul _ p _ hp _ _).trans (congrArg₂ (· * ·) (gs_res _ p le_top hp _) (gs_unit _ p _ hp _))
  exact ⟨fun h p hp => (l (pull_le M x j) p hp).symm.trans ((congrArg _ (h _)).trans (r p hp)),
    fun h e => fn_ext fun p hp => (l e p hp).trans ((h p hp).trans (r p hp).symm)⟩

theorem secCoord_down {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB) (hL' : L'.IsLB)
    (H : LBIso L' (L.pull F)) {I : Type} (th : I → L.Sec) :
    ∃ th' : I → L'.Sec, ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X') (v : I → R),
      SecCoord L' th' x v ↔ SecCoord L th (x ≫ F) v := by
  obtain ⟨w, hw⟩ := H
  have hw' := (isGen_iff w).1 hw
  choose th' h' using fun i => sec_pull_down hw' hL hL' (th i)
  refine ⟨th', fun R _ x v => ?_⟩
  have e : ∀ (p : Sp R) (j : PUnit → L.ι) (k : PUnit → L'.ι),
      pw w (fun _ : PUnit => x) (fun _ => 1) (𝟙 _) p j k = gw w x p (j PUnit.unit) (k PUnit.unit) := fun p j k => by
    rw [pw, Fintype.prod_unique, zpow_one, Category.id_comp]
  rw [secCoord_iff, secCoord_iff]
  constructor
  · rintro ⟨τ, hτ, h⟩
    obtain ⟨t, ht, hv⟩ := exists_up hw' hL hL' τ hτ
    refine ⟨t, ht, fun i j p hp => ?_⟩
    obtain ⟨k, hk⟩ := exists_chart hL' (x p)
    have hk' : p ∈ (L'.pull x).U (fun _ => k) := mem_pull.2 hk
    have h₁ := h' i _ x p (j PUnit.unit) k (mem_pull₂.1 hp) hk
    have h₂ := congrArg Units.val (hv _ (𝟙 _) p j (fun _ => k) hp hk')
    rw [e, Units.val_mul] at h₂
    refine h₁.trans ((congrArg (_ * ·) (h i (fun _ => k) p hk')).trans ?_)
    exact (mul_left_comm _ _ _).trans (congrArg (_ * ·) h₂.symm)
  · rintro ⟨τ, hτ, h⟩
    obtain ⟨t, ht, hv⟩ := CubTransport.exists_down_units hw' hL hL' (φ' := fun _ : PUnit => x) τ hτ
    refine ⟨t, ht, fun i k p hp => ?_⟩
    obtain ⟨j, hj⟩ := exists_chart hL (F (x p))
    have hj' : p ∈ (L.pull (x ≫ F)).U (fun _ => j) := mem_pull₂.2 hj
    have h₁ := h' i _ x p j (k PUnit.unit) hj (mem_pull.1 hp)
    have h₂ := congrArg Units.val (hv _ (𝟙 _) p (fun _ => j) k hj' hp)
    rw [e, Units.val_mul] at h₂
    refine (Units.mul_right_inj (gw w x p j (k PUnit.unit))).1 (h₁.symm.trans ((h i (fun _ => j) p hj').trans ?_))
    exact (congrArg (_ * ·) h₂).trans (mul_left_comm _ _ _)

theorem mem_nonzeroLocus_iff {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) {I : Type} {th : I → M.Sec} {R : Type} [CommRing R]
    {x : Sp R ⟶ X} {v : I → R} (i : I) (p : Sp R) (h : SecCoord M th x v) :
    x p ∈ Out.nonzeroLocus (th i) ↔ v i ∉ p.asIdeal := by
  obtain ⟨τ, -, h⟩ := (secCoord_iff M th x v).1 h
  have key : ∀ k, x p ∈ M.U k → (IsUnit (gs (𝟙 X) (x p) _ ((th i).f k)) ↔ v i ∉ p.asIdeal) := fun k hk => by
    have e := h i (fun _ => k) p (mem_pull.2 hk)
    rw [gs_stalkMap x p _ hk] at e
    rw [← isUnit_cst_id, ← isUnit_map_iff (x.stalkMap p).hom]
    exact (congrArg IsUnit e).to_iff.trans (Units.isUnit_mul_units _ _)
  rw [mem_nonzeroLocus]
  refine ⟨fun ⟨k, hk, u⟩ => (key k hk).1 u, fun u => ?_⟩
  obtain ⟨k, hk⟩ := exists_chart hM (x p)
  exact ⟨k, hk, (key k hk).2 u⟩

theorem secCoord_pull_iso_locus : ∀ (X : Scheme.{0}) (M : LB X) (I : Type) (th : I → M.Sec), M.IsLB → (∀ (X' : Scheme.{0}) (π : X' ⟶ X), ∃ th' : I → (M.pull π).Sec, ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X') (v : I → R), SecCoord (M.pull π) th' x v ↔ SecCoord M th (x ≫ π) v) ∧ (∀ M' : LB X, M'.IsLB → LBIso M M' → ∃ th' : I → M'.Sec, ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : I → R), SecCoord M' th' x v ↔ SecCoord M th x v) ∧ ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : I → R) (i : I) (p : Sp R), SecCoord M th x v → (x p ∈ Out.nonzeroLocus (th i) ↔ v i ∉ p.asIdeal) := by
  intro X M I th hM
  refine ⟨fun X' π => ⟨fun i => secPull M π (th i), fun R _ x v => secCoord_pull M th π x v⟩, fun M' hM' H => ?_,
    fun R _ x v i p h => mem_nonzeroLocus_iff hM i p h⟩
  obtain ⟨th', h⟩ := secCoord_down hM hM'
    (LBIso.chartPull (chartPullId M') (chartPullPull M (𝟙 X) (𝟙 X) rfl) (LBIso.symm H)) th
  refine ⟨th', fun R _ x v => ?_⟩
  have := h R x v
  rwa [Category.comp_id] at this

end GlobalTheory.ZM.CoordMove
end
