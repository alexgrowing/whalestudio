import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRingEquiv
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecSuccOfRelAmple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOpenNonzeroLocusOfUniversallyClosed

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_iso_of_sectionRing_aut_of_relAmple : ∀ (K : Type) [CommRing K] (X : Over (Spec (CommRingCat.of K))) [IsProper X.hom] (L : LB X.left), L.IsLB → RelAmple X L → ∀ θ : ∀ n : ℕ, 1 ≤ n → (H0 L n ≃ H0 L n), (∀ (n : ℕ) (hn : 1 ≤ n) (c : K) (a b d : H0 L n), (∀ j, d.f j = a.f j + resTop _ (scal X.hom c) * b.f j) → ∀ j, (θ n hn d).f j = (θ n hn a).f j + resTop _ (scal X.hom c) * (θ n hn b).f j) → (∀ (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (a : H0 L n) (b : H0 L m) (d : H0 L (n + m)), (∀ j : Fin 1 → L.ι, (show Γ(X.left, LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) j) from d.f j) = (show Γ(X.left, LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) j) from a.f j) * (show Γ(X.left, LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) j) from b.f j)) → ∀ j : Fin 1 → L.ι, (show Γ(X.left, LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) j) from (θ (n + m) (hn.trans (Nat.le_add_right n m)) d).f j) = (show Γ(X.left, LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) j) from (θ n hn a).f j) * (show Γ(X.left, LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) j) from (θ m hm b).f j)) → ∃ Φ₀ : X ≅ X, ∃ w : LB.Iso L (L.pull Φ₀.hom.left), w.IsGen ∧ ∀ (n : ℕ) (hn : 1 ≤ n) (a : H0 L n), (∀ (Z : Scheme.{0}) (r : Z ⟶ X.left) (z : Z) (p : Fin 1 → L.ι) (q : Fin 1 → L.ι), (∀ κ, (Φ₀.hom.left) ((fun _ : Fin 1 => 𝟙 X.left) κ (r z)) ∈ L.U (p κ)) → (∀ κ, (fun _ : Fin 1 => 𝟙 X.left) κ (r z) ∈ L.U (q κ)) → Geo.Tor.gs (r ≫ Φ₀.hom.left) z (LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) p) ((θ n hn a).f p) = (∏ κ, Geo.Tor.gw w (r ≫ (fun _ : Fin 1 => 𝟙 X.left) κ) z (p κ) (q κ) ^ (fun _ : Fin 1 => (n : ℤ)) κ).val * Geo.Tor.gs r z (LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) q) ((a).f q)) := by
  intro K _ X _ L hL hA θ hlin hmul
  have h := isAmpleLB_of_relAmple_of_isAffine X hL hA
  have := h.compactSpace
  have := h.quasiSeparatedSpace
  obtain ⟨-, m, hm, M, s, hs⟩ := isAffineOpen_nonzeroLocus_of_relAmple K X L hL hA 1 le_rfl
  have hN : 1 ≤ 1 * m := by omega
  have haff := (isAffineOpen_nonzeroLocus_of_relAmple K X L hL hA (1 * m) hN).1
  obtain ⟨Φ, hΦ⟩ := exists_iso_of_sectionRing_equiv K X X L L hL hL θ hlin hmul
    ⟨1 * m, hN, H0 L (1 * m), id,
      top_le_iff.1 (hs.ge.trans (iSup_le fun i => le_iSup (fun a : H0 L (1 * m) => nonzeroLocus a) (s i))),
      top_le_iff.1 (hs.ge.trans (iSup_le fun i => le_iSup_of_le ((θ (1 * m) hN).symm (s i))
        (congrArg nonzeroLocus ((θ (1 * m) hN).apply_symm_apply (s i))).ge)),
      fun a => ⟨haff _, haff _⟩⟩
  exact ⟨Φ, exists_iso_of_sectionRing K X X L L hL hL θ hlin hmul Φ.hom.left hΦ
    (exists_sec_succ_of_relAmple K X L hL hA)⟩

end GlobalTheory
