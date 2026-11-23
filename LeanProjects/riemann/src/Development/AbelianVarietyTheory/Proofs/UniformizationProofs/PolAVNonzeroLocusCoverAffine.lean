import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AgreeOfCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRingEquiv
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRing

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem polAV_nonzeroLocus_cover_affine (hA : AmpleSt) {S : Scheme.{0}} [IsAffine S] [IsLocallyNoetherian S]
    (P : PolAV S) {N : ℕ} (hN : 4 ≤ N) :
    (∀ x : P.A.left, ∃ s : H0 P.L N, x ∈ nonzeroLocus s) ∧ ∀ s : H0 P.L N, IsAffineOpen (nonzeroLocus s) := by
  classical
  have := P.isAb.proper
  let := P.grp
  obtain ⟨M, s, hs⟩ := AmpleSpan.exists_embedsBy_of_isPullback P.A P.isLB (hA S P N hN).2 (isAffineOpen_top S)
    (φ := 𝟙 P.A.left) (f' := P.A.hom) (g := 𝟙 S ≫ S.topIso.inv)
    (by rw [AmpleSpan.comp_topIso_inv_ι]; exact IsPullback.of_id_fst) (K := Fin 1) (ε := fun _ => (N : ℤ)) (by simp)
  refine ⟨fun x => ?_, fun t => (hs.affine_and_surjective (t := s) (fun j => ⟨Pi.single j 1, fun k => ?_⟩) t).1⟩
  · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hs.1.ge (Set.mem_univ x))
    exact ⟨s i, hi⟩
  · rw [Finset.sum_eq_single j]
    · rw [Pi.single_eq_same, map_one, _root_.one_mul]
    · intro l _ hl
      rw [Pi.single_eq_of_ne hl, map_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ j) h

theorem exists_iso_of_polAV_sectionRing : Laws → ∀ (K : Type) [Field K] (P P' : PolAV (Spec (CommRingCat.of K))), ∀ θ : ∀ n : ℕ, 1 ≤ n → (H0 P'.L n ≃ H0 P.L n), (∀ (n : ℕ) (hn : 1 ≤ n) (c : K) (a b d : H0 P'.L n), (∀ j, d.f j = a.f j + resTop _ (scal P'.A.hom c) * b.f j) → ∀ j, (θ n hn d).f j = (θ n hn a).f j + resTop _ (scal P.A.hom c) * (θ n hn b).f j) → (∀ (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (a : H0 P'.L n) (b : H0 P'.L m) (d : H0 P'.L (n + m)), (∀ j : Fin 1 → P'.L.ι, (show Γ(P'.A.left, LB.wchart P'.L (fun _ : Fin 1 => 𝟙 P'.A.left) j) from d.f j) = (show Γ(P'.A.left, LB.wchart P'.L (fun _ : Fin 1 => 𝟙 P'.A.left) j) from a.f j) * (show Γ(P'.A.left, LB.wchart P'.L (fun _ : Fin 1 => 𝟙 P'.A.left) j) from b.f j)) → ∀ j : Fin 1 → P.L.ι, (show Γ(P.A.left, LB.wchart P.L (fun _ : Fin 1 => 𝟙 P.A.left) j) from (θ (n + m) (hn.trans (Nat.le_add_right n m)) d).f j) = (show Γ(P.A.left, LB.wchart P.L (fun _ : Fin 1 => 𝟙 P.A.left) j) from (θ n hn a).f j) * (show Γ(P.A.left, LB.wchart P.L (fun _ : Fin 1 => 𝟙 P.A.left) j) from (θ m hm b).f j)) → ∃ Φ₀ : P'.A ≅ P.A, ∃ w : LB.Iso P'.L (P.L.pull Φ₀.hom.left), w.IsGen ∧ ∀ (n : ℕ) (hn : 1 ≤ n) (a : H0 P'.L n), (∀ (Z : Scheme.{0}) (r : Z ⟶ P'.A.left) (z : Z) (p : Fin 1 → P.L.ι) (q : Fin 1 → P'.L.ι), (∀ κ, (Φ₀.hom.left) ((fun _ : Fin 1 => 𝟙 P'.A.left) κ (r z)) ∈ P.L.U (p κ)) → (∀ κ, (fun _ : Fin 1 => 𝟙 P'.A.left) κ (r z) ∈ P'.L.U (q κ)) → Geo.Tor.gs (r ≫ Φ₀.hom.left) z (LB.wchart P.L (fun _ : Fin 1 => 𝟙 P.A.left) p) ((θ n hn a).f p) = (∏ κ, Geo.Tor.gw w (r ≫ (fun _ : Fin 1 => 𝟙 P'.A.left) κ) z (p κ) (q κ) ^ (fun _ : Fin 1 => (n : ℤ)) κ).val * Geo.Tor.gs r z (LB.wchart P'.L (fun _ : Fin 1 => 𝟙 P'.A.left) q) ((a).f q)) := by
  intro hL K _ P P' θ hlin hmul
  have := P.isAb.proper
  have := P'.isAb.proper
  have : CompactSpace P.A.left := QuasiCompact.compactSpace_of_compactSpace P.A.hom
  have : CompactSpace P'.A.left := QuasiCompact.compactSpace_of_compactSpace P'.A.hom
  have : QuasiSeparatedSpace P.A.left := quasiSeparatedSpace_of_quasiSeparated P.A.hom
  have : QuasiSeparatedSpace P'.A.left := quasiSeparatedSpace_of_quasiSeparated P'.A.hom
  obtain ⟨c, a⟩ := polAV_nonzeroLocus_cover_affine hL.ample P (le_refl 4)
  obtain ⟨c', a'⟩ := polAV_nonzeroLocus_cover_affine hL.ample P' (le_refl 4)
  obtain ⟨c₅, -⟩ := polAV_nonzeroLocus_cover_affine hL.ample P' (N := 4 + 1) (by norm_num)
  obtain ⟨Φ, hΦ⟩ := exists_iso_of_sectionRing_equiv K P.A P'.A P.L P'.L P.isLB P'.isLB θ hlin hmul
    ⟨4, by norm_num, H0 P'.L 4, id, top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 (c' x),
      top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 (by
        obtain ⟨s, hs⟩ := c x
        obtain ⟨t, rfl⟩ := (θ 4 (by norm_num)).surjective s
        exact ⟨t, hs⟩), fun i => ⟨a' _, a _⟩⟩
  refine ⟨Φ, exists_iso_of_sectionRing K P.A P'.A P.L P'.L P.isLB P'.isLB θ hlin hmul Φ.hom.left hΦ fun x => ?_⟩
  obtain ⟨s, hs⟩ := c' x
  obtain ⟨t, ht⟩ := c₅ x
  exact ⟨4, by norm_num, s, t, hs, ht⟩

end GlobalTheory
