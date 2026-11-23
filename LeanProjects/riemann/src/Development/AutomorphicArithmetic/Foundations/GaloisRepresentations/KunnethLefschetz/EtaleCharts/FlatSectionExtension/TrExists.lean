import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.KerRes

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.trExists :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α β : B.ι) {N : Z.Opens} (_ : IsAffineOpen N) (h₁ : N ≤ B.V α) (h₂ : N ≤ B.V β), ∃ G : Matrix (Fin d) (Fin d) Γ(Z, N), IsTr B α β h₁ h₂ G := by
  intro K _ W Z Y q i π D d B α β N hN h₁ h₂
  have key : ∀ m, ∃ c : Fin d → Γ(Z, N), ∑ l, c l * tN B α h₁ l = tN B β h₂ m := by
    intro m
    have hm : tN B β h₂ m ∈ Ideal.span (Set.range (tN B α h₁)) := by
      rw [← kerRes B α hN h₁, kerRes B β hN h₂]
      exact Ideal.subset_span ⟨m, rfl⟩
    exact Ideal.mem_span_range_iff_exists_fun.1 hm
  choose G hG using key
  exact ⟨Matrix.of G, fun m => (hG m).symm⟩
