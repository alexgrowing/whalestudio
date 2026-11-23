import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.NzdChart

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem flat_mem_nzd {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R) (hφ : φ.Flat) {a : A}
    (ha : a ∈ nonZeroDivisors A) : φ a ∈ nonZeroDivisors R := by
  algebraize [φ]
  have hreg : IsSMulRegular R a := Module.Flat.isSMulRegular_of_nonZeroDivisors ha
  refine mem_nonZeroDivisors_iff_right.2 fun x hx => hreg ?_
  change a • x = a • (0 : R)
  rw [Algebra.smul_def, smul_zero, mul_comm]
  exact hx

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.nzdRes :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (β : B.ι) (l : Fin d) (Q : Y.Opens), IsAffineOpen Q → ∀ (h : ⊤ ≤ Q.ι ⁻¹ᵁ (B.c β).C l), (Q.ι.appLE ((B.c β).C l) ⊤ h).hom ((π.appLE (B.V β) ((B.c β).C l) ((B.c β).C_le l)).hom ((B.c β).t l)) ∈ nonZeroDivisors Γ((Q : Scheme.{0}), ⊤) := by
  intro K _ W Z Y q i π D d B β l Q hQ h
  have : IsAffine (Q : Scheme.{0}) := hQ
  have hfl : (Q.ι.appLE ((B.c β).C l) ⊤ h).hom.Flat :=
    HasRingHomProperty.appLE (P := @AlgebraicGeometry.Flat) Q.ι inferInstance
      ⟨(B.c β).C l, (B.c β).C_aff l⟩ ⟨⊤, isAffineOpen_top _⟩ h
  exact flat_mem_nzd _ hfl (nzdChart B β l)
