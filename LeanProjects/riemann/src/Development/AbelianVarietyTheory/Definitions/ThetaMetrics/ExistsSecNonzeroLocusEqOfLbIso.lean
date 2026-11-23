import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

noncomputable section

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X Y Y' Z : Scheme.{0}}

namespace LBGerm

theorem gs_pow (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) (n : ℕ) :
    gs r z U (a ^ n) = gs r z U a ^ n := by simp only [gs_eq r z U h, map_pow]

theorem gs_sub (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a b : Γ(X, U)) :
    gs r z U (a - b) = gs r z U a - gs r z U b := by simp only [gs_eq r z U h, map_sub]

theorem gs_zero (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) :
    gs r z U 0 = 0 := by simp only [gs_eq r z U h, map_zero]

theorem isUnit_gs_iff (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs r z U a) ↔ r z ∈ X.basicOpen a := by
  rw [gs_stalkMap r z U h, isUnit_map_iff (r.stalkMap z).hom, gs_eq (𝟙 X) (r z) U h]
  exact (X.mem_basicOpen a _ h).symm

def secOfGerm {M : LB X} (f : ∀ i, Γ(X, M.U i))
    (h : ∀ (y : X) i j, y ∈ M.U i → y ∈ M.U j →
      gs (𝟙 X) y _ (f i) = (gm (𝟙 X) y (M.U i ⊓ M.U j) (M.g i j)).val * gs (𝟙 X) y _ (f j)) : M.Sec where
  f := f
  compat i j := fn_ext fun y hy => by
    rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_unit _ y _ hy]
    exact h y i j hy.1 hy.2

theorem gs_secOn {M : LB X} {V : X.Opens} {t : ∀ i, Γ(X, V ⊓ M.U i)} (ht : t ∈ secOn M V) (y : X) (i j : M.ι)
    (hV : y ∈ V) (hi : y ∈ M.U i) (hj : y ∈ M.U j) :
    gs (𝟙 X) y _ (t i) = (gm (𝟙 X) y (M.U i ⊓ M.U j) (M.g i j)).val * gs (𝟙 X) y _ (t j) := by
  have hy : y ∈ V ⊓ M.U i ⊓ M.U j := ⟨⟨hV, hi⟩, hj⟩
  have e := congrArg (gs (𝟙 X) y _) (ht i j)
  rwa [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy,
    gs_unit (𝟙 X) y (M.U i ⊓ M.U j) ⟨hi, hj⟩] at e

theorem mem_secOn_of_germ {M : LB X} {V : X.Opens} (t : ∀ i, Γ(X, V ⊓ M.U i))
    (h : ∀ (y : X) i j, y ∈ V → y ∈ M.U i → y ∈ M.U j →
      gs (𝟙 X) y _ (t i) = (gm (𝟙 X) y (M.U i ⊓ M.U j) (M.g i j)).val * gs (𝟙 X) y _ (t j)) :
    t ∈ secOn M V := fun i j => fn_ext fun y hy => by
  rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy,
    gs_unit (𝟙 X) y (M.U i ⊓ M.U j) ⟨hy.1.2, hy.2⟩]
  exact h y i j hy.1.1 hy.1.2 hy.2

end LBGerm

open LBGerm

section Locus

variable {M : LB Y}

theorem basicOpen_le_nonzeroLocus (s : M.Sec) (k : M.ι) : Y.basicOpen (s.f k) ≤ nonzeroLocus s :=
  le_iSup (fun k => Y.basicOpen (s.f k)) k

theorem exists_chart_of_mem_nonzeroLocus {s : M.Sec} {y : Y} (h : y ∈ nonzeroLocus s) : ∃ k, y ∈ M.U k := by
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 h
  exact ⟨k, Y.basicOpen_le _ hk⟩

theorem mem_nonzeroLocus_iff_pull (s : M.Sec) (r : Z ⟶ Y) (z : Z) {k : M.ι} (hk : r z ∈ M.U k) :
    r z ∈ nonzeroLocus s ↔ IsUnit (gs r z _ (s.f k)) := by
  refine ⟨fun h => ?_, fun h => basicOpen_le_nonzeroLocus s k ((isUnit_gs_iff r z _ hk _).1 h)⟩
  obtain ⟨j, hj⟩ := Opens.mem_iSup.1 h
  have hjU : r z ∈ M.U j := Y.basicOpen_le _ hj
  have u := (isUnit_gs_iff r z _ hjU _).2 hj
  rw [gs_compat s r z hjU hk] at u
  exact isUnit_of_mul_isUnit_right u

theorem mem_nonzeroLocus_iff_isUnit (s : M.Sec) {y : Y} {k : M.ι} (hk : y ∈ M.U k) :
    y ∈ nonzeroLocus s ↔ IsUnit (gs (𝟙 Y) y _ (s.f k)) :=
  mem_nonzeroLocus_iff_pull s (𝟙 Y) y hk

theorem nonzeroLocus_inf_chart (s : M.Sec) (k : M.ι) : nonzeroLocus s ⊓ M.U k = Y.basicOpen (s.f k) :=
  le_antisymm (fun y hy => (isUnit_gs_iff (𝟙 Y) y _ hy.2 _).1 ((mem_nonzeroLocus_iff_isUnit s hy.2).1 hy.1))
    (le_inf (basicOpen_le_nonzeroLocus s k) (Y.basicOpen_le _))

theorem mem_nonzeroLocus_iff_basicOpen (s : M.Sec) {y : Y} {k : M.ι} (hk : y ∈ M.U k) :
    y ∈ nonzeroLocus s ↔ y ∈ Y.basicOpen (s.f k) :=
  (mem_nonzeroLocus_iff_isUnit s hk).trans (isUnit_gs_iff (𝟙 Y) y _ hk _)

theorem nonzeroLocus_eq_of (s : M.Sec) (W : Y.Opens) (hW : ∀ y ∈ W, ∃ k, y ∈ M.U k)
    (h : ∀ (y : Y) k, y ∈ M.U k → (IsUnit (gs (𝟙 Y) y _ (s.f k)) ↔ y ∈ W)) : nonzeroLocus s = W := by
  refine le_antisymm (fun y hy => ?_) (fun y hy => ?_)
  · obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus hy
    exact (h y k hk).1 ((mem_nonzeroLocus_iff_isUnit s hk).1 hy)
  · obtain ⟨k, hk⟩ := hW y hy
    exact (mem_nonzeroLocus_iff_isUnit s hk).2 ((h y k hk).2 hy)

theorem nonzeroLocus_secZero : nonzeroLocus (DVR.SecOps.secZero : M.Sec) = ⊥ :=
  le_bot_iff.1 (iSup_le fun k => (Y.basicOpen_zero (M.U k)).le)

theorem nonzeroLocus_secScale (c : Γ(Y, ⊤)) (s : M.Sec) :
    nonzeroLocus (DVR.SecOps.secScale c s) = Y.basicOpen c ⊓ nonzeroLocus s := by
  refine nonzeroLocus_eq_of _ _ (fun y hy => exists_chart_of_mem_nonzeroLocus hy.2) fun y k hk => ?_
  have e : gs (𝟙 Y) y _ ((DVR.SecOps.secScale c s).f k) = gs (𝟙 Y) y ⊤ c * gs (𝟙 Y) y _ (s.f k) :=
    (gs_mul _ y _ hk _ _).trans (congrArg (· * _) (gs_res _ y _ hk _))
  rw [e, IsUnit.mul_iff, isUnit_gs_iff (𝟙 Y) y ⊤ trivial, ← mem_nonzeroLocus_iff_isUnit s hk]
  exact Iff.rfl

theorem nonzeroLocus_genSec (hM : M.IsLB) (t : M.Gen) (ht : t.IsGen) : nonzeroLocus (DVR.genSec t ht) = ⊤ :=
  nonzeroLocus_eq_of _ _ (fun y _ => exists_chart hM y) fun y k hk =>
    ⟨fun _ => trivial, fun _ => (gs_unit (𝟙 Y) y _ hk (t.s k)) ▸ Units.isUnit _⟩

theorem isAffineHom_nonzeroLocus_ι (hM : M.IsLB) (s : M.Sec) : IsAffineHom (nonzeroLocus s).ι := by
  refine isAffineHom_of_forall_exists_isAffineOpen _ fun y => ?_
  obtain ⟨k, hk⟩ := exists_chart hM y
  obtain ⟨W, hW, hy, hle⟩ := exists_isAffineOpen_mem_and_subset hk
  have hle' : W ≤ M.U k := hle
  refine ⟨W, hy, hW, ?_⟩
  rw [← (nonzeroLocus s).ι.isAffineOpen_iff_of_isOpenImmersion, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι]
  have e : nonzeroLocus s ⊓ W = Y.basicOpen (resG Y hle' (s.f k)) := by
    rw [show Y.basicOpen (resG Y hle' (s.f k)) = W ⊓ Y.basicOpen (s.f k) from Y.basicOpen_res _ _,
      ← nonzeroLocus_inf_chart, inf_comm (nonzeroLocus s) (M.U k), ← inf_assoc, inf_eq_left.2 hle', inf_comm]
  rw [e]
  exact hW.basicOpen _

theorem isAffineOpen_nonzeroLocus_inf (hM : M.IsLB) (s : M.Sec) {V : Y.Opens} (hV : IsAffineOpen V) :
    IsAffineOpen (nonzeroLocus s ⊓ V) := by
  have := isAffineHom_nonzeroLocus_ι hM s
  have h := (hV.preimage (nonzeroLocus s).ι).image_of_isOpenImmersion (nonzeroLocus s).ι
  rwa [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι] at h

theorem isAffineOpen_nonzeroLocus [IsAffine Y] (hM : M.IsLB) (s : M.Sec) : IsAffineOpen (nonzeroLocus s) := by
  simpa using isAffineOpen_nonzeroLocus_inf hM s (isAffineOpen_top Y)

theorem nonzeroLocus_secOfIso {A B : LB Y} {u : LB.Iso A B} (t : B.Sec) (hu : u.IsGen) (hA : A.IsLB) (hB : B.IsLB) :
    nonzeroLocus (DVR.secOfIso t hu hA hB) = nonzeroLocus t := by
  refine nonzeroLocus_eq_of _ _ (fun y _ => exists_chart hA y) fun y a ha => ?_
  obtain ⟨b, hb⟩ := exists_chart hB y
  have hy : y ∈ A.U a ⊓ B.U b := ⟨ha, hb⟩
  have e := congrArg (gs (𝟙 Y) y _) (DVR.secOfIso_spec t hu hA hB a b)
  rw [DVR.isoCand, gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_unit _ y _ hy] at e
  rw [mem_nonzeroLocus_iff_isUnit t hb, e, Units.isUnit_units_mul]

theorem exists_sec_nonzeroLocus_eq_of_lbIso {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (H : LBIso A B) (t : B.Sec) :
    ∃ s : A.Sec, nonzeroLocus s = nonzeroLocus t := by
  obtain ⟨u, hu⟩ := H
  exact ⟨_, nonzeroLocus_secOfIso t hu hA hB⟩

end Locus

end GlobalTheory
