import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.DcSumEqOfMk
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem hkApply_dc_congr {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]
    (ρ : Representation A G M) (K K' : Subgroup G) {x y : G}
    (h : MulAction.orbit K (x : G ⧸ K') = MulAction.orbit K (y : G ⧸ K')) :
    dc ρ K K' x = dc ρ K K' y := by
  unfold dc
  rw [h]

private theorem hkApply_orbit {G : Type} [Group G] (K K' : Subgroup G) (x : G) {a b : G} (ha : a ∈ K) (hb : b ∈ K') :
    MulAction.orbit K ((a * x * b : G) : G ⧸ K') = MulAction.orbit K (x : G ⧸ K') := by
  have h1 : ((a * x * b : G) : G ⧸ K') = (⟨a, ha⟩ : K) • (x : G ⧸ K') := by
    rw [QuotientGroup.mk_mul_of_mem _ hb]
    rfl
  rw [h1, MulAction.orbit_smul]

theorem UpperTheory.V.AlgebraTools.hkApply :
    ∀ (A G M : Type) [CommRing A] [Group G] [AddCommGroup M] [Module A M] (ρ : Representation A G M) (K K' : Subgroup G) (x : G), FinOrb K K' x → (∀ v : fixd ρ K', (hk2 ρ K K' x v : M) = dc ρ K K' x v) ∧ (∀ s : Finset G, (∀ y ∈ s, (y : G ⧸ K') ∈ MulAction.orbit K (x : G ⧸ K')) → (∀ q ∈ MulAction.orbit K (x : G ⧸ K'), ∃! y, y ∈ s ∧ (y : G ⧸ K') = q) → ∀ v : fixd ρ K', (hk2 ρ K K' x v : M) = ∑ y ∈ s, ρ y v) ∧ ∀ a ∈ K, ∀ b ∈ K', hk2 ρ K K' (a * x * b) = hk2 ρ K K' x := by
  intro A G M _ _ _ _ ρ K K' x hfin
  obtain ⟨h1, h2, -⟩ := UpperTheory.V.Hi.dcSum A G M ρ K K' x hfin
  have hv : ∀ v : fixd ρ K', (hk2 ρ K K' x v : M) = dc ρ K K' x v := by
    intro v
    unfold hk2
    rw [dif_pos h2]
    rfl
  refine ⟨hv, fun s hs hu v => ?_, fun a ha b hb => ?_⟩
  · rw [hv, h1 s hs hu v v.2]
  · have h := hkApply_dc_congr ρ K K' (hkApply_orbit K K' x ha hb)
    unfold hk2
    rw [h]
