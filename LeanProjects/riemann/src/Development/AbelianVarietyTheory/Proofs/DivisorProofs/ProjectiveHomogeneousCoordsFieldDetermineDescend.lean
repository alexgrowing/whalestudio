import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsTwoPoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjectiveRepresentationPullbackCoordinates
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordBcScaleUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecCoordOfSubsingletonPic
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.CrdUniq

theorem exists_spMap' {A B : Type} [CommRing A] [CommRing B] (f : Sp B ⟶ Sp A) : ∃ c : A →+* B, spMap c = f :=
  ⟨(Spec.preimage f).hom, by simp [spMap]⟩

theorem pCrd_iff {o R : Type} [CommRing o] [CommRing R] {n : ℕ} (x : Sp R ⟶ PSpace o n) (c : o →+* R)
    (hx : x ≫ PSpace.str o n = spMap c) (v : Fin (n + 1) → R) :
    PCrd x v ↔ ∃ hv : Ideal.span (Set.range v) = ⊤, x = ProjSpace.pt c v hv := by
  have h := ProjCoord.secCoord_iff (Equiv.refl _) (𝟙 _) c x (by rw [Category.comp_id]; exact hx) v
  have h2 := RepBC.secCoord_pull (ProjSpace.O1 o n) (ProjSpace.coord o n) (𝟙 _) x v
  rw [Category.comp_id] at h2
  simp only [Equiv.refl_symm, Equiv.coe_refl, Function.comp_id, Category.comp_id] at h
  exact h2.symm.trans h

theorem eq_of_pCrd {o R : Type} [CommRing o] [CommRing R] {n : ℕ} {x x' : Sp R ⟶ PSpace o n} {v : Fin (n + 1) → R}
    (hs : x ≫ PSpace.str o n = x' ≫ PSpace.str o n) (h : PCrd x v) (h' : PCrd x' v) : x = x' := by
  obtain ⟨c, hc⟩ := exists_spMap' (x ≫ PSpace.str o n)
  obtain ⟨hv, e⟩ := (pCrd_iff x c hc.symm v).1 h
  obtain ⟨hv', e'⟩ := (pCrd_iff x' c (hs ▸ hc.symm) v).1 h'
  rw [e, e']

theorem exists_ne_zero_of_pCrd {o K : Type} [CommRing o] [Field K] {n : ℕ} {x : Sp K ⟶ PSpace o n}
    {v : Fin (n + 1) → K} (h : PCrd x v) : ∃ k, v k ≠ 0 := by
  obtain ⟨c, hc⟩ := exists_spMap' (x ≫ PSpace.str o n)
  obtain ⟨hv, -⟩ := (pCrd_iff x c hc.symm v).1 h
  by_contra hn
  push_neg at hn
  have : Set.range v ⊆ {0} := by rintro _ ⟨k, rfl⟩; exact hn k
  have h0 : Ideal.span (Set.range v) = ⊥ := by
    rw [Ideal.span_eq_bot]; intro y hy; exact this hy
  rw [h0] at hv
  exact bot_ne_top hv

theorem scalar_of_pCrd {o K : Type} [CommRing o] [Field K] {n : ℕ} {x : Sp K ⟶ PSpace o n}
    {v w : Fin (n + 1) → K} (hv : PCrd x v) (hw : PCrd x w) : ∃ a : K, a ≠ 0 ∧ ∀ j, w j = a * v j := by
  obtain ⟨u, hu⟩ := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ (ProjSpace.O1_isLB o n) hv).2.2 w hw
  exact ⟨u, u.ne_zero, hu⟩

theorem pCrd_of_map {o K K' : Type} [CommRing o] [Field K] [Field K'] {n : ℕ} {x : Sp K ⟶ PSpace o n}
    {v : Fin (n + 1) → K} (i : K →+* K') (h : PCrd (spMap i ≫ x) (fun j => i (v j))) : PCrd x v := by
  obtain ⟨w, hw⟩ := FieldPoint.exists_secCoord o n K x
  have hw' := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ (ProjSpace.O1_isLB o n) hw).1 K' i
  obtain ⟨u, hu⟩ := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ (ProjSpace.O1_isLB o n) hw').2.2 _ h
  obtain ⟨k, hk⟩ := exists_ne_zero_of_pCrd h
  have hvk : v k ≠ 0 := fun e => hk (by simp only [e, map_zero])
  have hwk : w k ≠ 0 := fun e => hk (by rw [hu k]; simp only [e, map_zero, mul_zero])
  have hua : (u : K') = i (v k / w k) := by
    rw [map_div₀, eq_div_iff ((map_ne_zero i).2 hwk), hu k]
  have hvj : ∀ j, v j = (v k / w k) * w j := fun j => by
    apply i.injective
    rw [hu j, hua, map_mul]
  have hs := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ (ProjSpace.O1_isLB o n) hw).2.1
    (Units.mk0 (v k / w k) (div_ne_zero hvk hwk))
  have e : (fun j => ((Units.mk0 (v k / w k) (div_ne_zero hvk hwk) : Kˣ) : K) * w j) = v :=
    funext fun j => (hvj j).symm
  rw [e] at hs
  exact hs

theorem main : (∀ (o K : Type) [CommRing o] [Field K] (n : ℕ) (x x' : Sp K ⟶ PSpace o n) (v : Fin (n + 1) → K), x ≫ PSpace.str o n = x' ≫ PSpace.str o n → PCrd x v → PCrd x' v → x = x') ∧ (∀ (o K : Type) [CommRing o] [Field K] (n : ℕ) (x : Sp K ⟶ PSpace o n) (v w : Fin (n + 1) → K), PCrd x v → PCrd x w → ∃ a : K, a ≠ 0 ∧ ∀ j, w j = a * v j) ∧ ∀ (o K K' : Type) [CommRing o] [Field K] [Field K'] (n : ℕ) (x : Sp K ⟶ PSpace o n) (v : Fin (n + 1) → K) (i : K →+* K'), PCrd (spMap i ≫ x) (fun j => i (v j)) → PCrd x v :=
  ⟨fun _ _ _ _ _ _ _ _ hs h h' => eq_of_pCrd hs h h',
   fun _ _ _ _ _ _ _ _ hv hw => scalar_of_pCrd hv hw,
   fun _ _ _ _ _ _ _ _ _ i h => pCrd_of_map i h⟩

end GlobalTheory.UMin.CrdUniq
