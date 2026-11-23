import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsHomOpenPart
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueIsRatio
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

namespace GlobalTheory.ZH.DivCrd

open GlobalTheory.Points CrdCalc

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {N : RatModel o Ω} {X : Scheme.{0}} {a : N.Z ⟶ X}
  {H : LB X} {J : Type} {s : J → H.Sec} {t : J → Ω}

theorem ratio_eq (ht : Crd H s (N.pt ≫ a) t) {k : J} {z : N.Z} (hz : a z ∈ nonzeroLocus (s k)) :
    t k ≠ 0 ∧ ∀ (j : J) (r : Γ(X, nonzeroLocus (s k))), IsRatio (s j) (s k) _ r →
      valF N.pt (a ⁻¹ᵁ nonzeroLocus (s k)) (a.app _ r) = t j / t k := by
  have h : ⊤ ≤ (N.pt ≫ a) ⁻¹ᵁ nonzeroLocus (s k) :=
    N.top_le_preimage_pt (U := a ⁻¹ᵁ nonzeroLocus (s k)) ⟨z, hz⟩
  have hk : t k ≠ 0 := ((crd_isUnit_iff k ht).2 h).ne_zero
  refine ⟨hk, fun j r hr => ?_⟩
  rw [eq_div_iff hk, crd_ratio ht hr h, valR_comp]
  rfl

theorem div_of_mem (hH : H.IsLB) (ht : Crd H s (N.pt ≫ a) t) {k : J} {z : N.Z}
    (hz : a z ∈ nonzeroLocus (s k)) : N.Div t k z := by
  obtain ⟨hk, h⟩ := ratio_eq ht hz
  refine ⟨hk, fun j => ?_⟩
  obtain ⟨r, hr, -⟩ := GlobalTheory.SecRatio.existsUnique_isRatio hH (s j) (s k) _ le_rfl
  exact ⟨a ⁻¹ᵁ nonzeroLocus (s k), a.app _ r, hz, h j r hr⟩

theorem crd_eq_val_mul (hH : H.IsLB) (ht : Crd H s (N.pt ≫ a) t) {K : Type} [Field K] {x : Sp K ⟶ N.Z}
    {v : J → K} {k : J} (hv : Crd H s (x ≫ a) v)
    (hz : a (x (IsLocalRing.closedPoint K)) ∈ nonzeroLocus (s k)) :
    v k ≠ 0 ∧ ∀ j, v j = N.val x (t j / t k) * v k := by
  have hx : ⊤ ≤ x ⁻¹ᵁ (a ⁻¹ᵁ nonzeroLocus (s k)) := (le_preimage_iff x _).2 hz
  have h : ⊤ ≤ (x ≫ a) ⁻¹ᵁ nonzeroLocus (s k) := hx
  refine ⟨((crd_isUnit_iff k hv).2 h).ne_zero, fun j => ?_⟩
  obtain ⟨r, hr, -⟩ := GlobalTheory.SecRatio.existsUnique_isRatio hH (s j) (s k) _ le_rfl
  rw [RatModel.val_eq ((top_le_preimage_iff _ _).1 hx) ((ratio_eq ht hz).2 j r hr), crd_ratio hv hr h,
    valR_comp]
  rfl

theorem mem_of_div_pt (hH : H.IsLB) (hs : ⨆ j, nonzeroLocus (s j) = ⊤) (ht : Crd H s (N.pt ≫ a) t)
    {K : Type} [Field K] (x : Sp K ⟶ N.Z) {i : J} (hi : N.Div t i (x (IsLocalRing.closedPoint K))) :
    a (x (IsLocalRing.closedPoint K)) ∈ nonzeroLocus (s i) := by
  have hm : a (x (IsLocalRing.closedPoint K)) ∈ ⨆ j, nonzeroLocus (s j) := by rw [hs]; trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
  obtain ⟨v, hv⟩ := crd_exists hH s (x ≫ a)
  obtain ⟨h0, h1⟩ := crd_eq_val_mul hH ht hv hk
  have hd := div_of_mem hH ht hk
  have hu := (RatModel.val_ne_zero_iff (RatModel.range_eq_singleton x _) _).2 ((hd.div_iff_isUnit i).1 hi)
  have hvi : IsUnit (v i) := isUnit_iff_ne_zero.2 (by rw [h1 i]; exact mul_ne_zero hu h0)
  exact (le_preimage_iff (x ≫ a) _).1 ((crd_isUnit_iff i hv).1 hvi)

theorem mem_of_div (hH : H.IsLB) (hs : ⨆ j, nonzeroLocus (s j) = ⊤) (ht : Crd H s (N.pt ≫ a) t)
    {i : J} {z : N.Z} (hi : N.Div t i z) : a z ∈ nonzeroLocus (s i) := by
  let x : Sp (N.Z.residueField z) ⟶ N.Z := N.Z.fromSpecResidueField z
  have e : x (IsLocalRing.closedPoint (N.Z.residueField z)) = z := Scheme.fromSpecResidueField_apply _ _
  have h := mem_of_div_pt hH hs ht x (i := i) (by rw [e]; exact hi)
  rwa [e] at h

theorem div_iff_mem_nonzeroLocus : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (N : RatModel o Ω) (X : Scheme.{0}) (a : N.Z ⟶ X) (H : LB X) (J : Type) (s : J → H.Sec) (t : J → Ω), H.IsLB → ⨆ j, nonzeroLocus (s j) = ⊤ → Crd H s (N.pt ≫ a) t → (∀ (i : J) (z : N.Z), N.Div t i z ↔ a z ∈ nonzeroLocus (s i)) ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ N.Z) (v : J → K) (k : J), Crd H s (x ≫ a) v → N.Div t k (x (IsLocalRing.closedPoint K)) → v k ≠ 0 ∧ ∀ j, v j = N.val x (t j / t k) * v k :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hH hs ht =>
    ⟨fun _ _ => ⟨mem_of_div hH hs ht, div_of_mem hH ht⟩,
      fun _ _ x _ _ hv hk => crd_eq_val_mul hH ht hv (mem_of_div_pt hH hs ht x hk)⟩

end GlobalTheory.ZH.DivCrd
