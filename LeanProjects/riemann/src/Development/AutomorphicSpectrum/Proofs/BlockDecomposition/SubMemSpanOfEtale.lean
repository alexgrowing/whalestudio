import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaleLiftingOfNilIdealStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.LiftFlat

theorem flat_of_eval₂Hom_etale {Λ D : Type} [CommRing Λ] [CommRing D] (i : Λ →+* D) {d : ℕ}
    (t : Fin d → D) (het : (MvPolynomial.eval₂Hom i t).Etale) : i.Flat := by
  have h1 : (MvPolynomial.eval₂Hom i t).Flat := by
    letI := (MvPolynomial.eval₂Hom i t).toAlgebra
    haveI : Algebra.Etale (MvPolynomial (Fin d) Λ) D := het
    exact Algebra.Smooth.flat (MvPolynomial (Fin d) Λ) D
  have h2 : (MvPolynomial.C : Λ →+* MvPolynomial (Fin d) Λ).Flat := by
    rw [← MvPolynomial.algebraMap_eq, RingHom.flat_algebraMap_iff]
    infer_instance
  have h3 := RingHom.Flat.comp h2 h1
  rwa [MvPolynomial.eval₂Hom_comp_C] at h3

theorem sub_mem_span_of_etale {Λ D : Type} [CommRing Λ] [CommRing D] (i : Λ →+* D) {d : ℕ}
    (t : Fin d → D) (het : (MvPolynomial.eval₂Hom i t).Etale) (J : Ideal D) (μ : D) (g : D →+* D)
    (hJ : ∀ x ∈ J, IsNilpotent x) (hgi : g.comp i = i)
    (hgt : ∀ k, g (t k) - t k ∈ Ideal.span {μ}) (hgJ : ∀ z, g z - z ∈ J) (z : D) :
    g z - z ∈ Ideal.span {μ} := by
  classical
  letI : Algebra (MvPolynomial (Fin d) Λ) D := (MvPolynomial.eval₂Hom i t).toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin d) Λ) D := het
  let q : D →+* D ⧸ Ideal.span ({μ} : Set D) := Ideal.Quotient.mk _
  have hcomm : (q.comp g).comp (MvPolynomial.eval₂Hom i t) = q.comp (MvPolynomial.eval₂Hom i t) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      rw [← RingHom.comp_apply g i, hgi]
    · intro k
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      exact Ideal.Quotient.eq.mpr (hgt k)
  let φ₁ : D →ₐ[MvPolynomial (Fin d) Λ] D ⧸ Ideal.span ({μ} : Set D) := Ideal.Quotient.mkₐ _ _
  let φ₂ : D →ₐ[MvPolynomial (Fin d) Λ] D ⧸ Ideal.span ({μ} : Set D) :=
    { (q.comp g) with
      commutes' := fun a => by
        change q (g (algebraMap _ D a)) = q (algebraMap _ D a)
        exact RingHom.congr_fun hcomm a }
  obtain ⟨S, hS⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra (MvPolynomial (Fin d) Λ) D).FG)
  let I : Ideal (D ⧸ Ideal.span ({μ} : Set D)) :=
    Ideal.span ((fun s => q (g s - s)) '' (S : Set D))
  have hfg : I.FG := Submodule.fg_span (S.finite_toSet.image _)
  have hnil : IsNilpotent I := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical hfg]
    rw [Ideal.span_le]
    rintro _ ⟨s, -, rfl⟩
    exact mem_nilradical.mpr ((hJ _ (hgJ s)).map q)
  have hψ : (Ideal.Quotient.mkₐ (MvPolynomial (Fin d) Λ) I).comp φ₁ =
      (Ideal.Quotient.mkₐ (MvPolynomial (Fin d) Λ) I).comp φ₂ := by
    apply AlgHom.ext_of_adjoin_eq_top hS
    intro s hs
    have hmem : q (g s - s) ∈ I := Ideal.subset_span ⟨s, hs, rfl⟩
    rw [map_sub] at hmem
    show Ideal.Quotient.mk I (q s) = Ideal.Quotient.mk I (q (g s))
    exact (Ideal.Quotient.eq.mpr hmem).symm
  have hφ : φ₁ = φ₂ := by
    apply Algebra.FormallyUnramified.ext I hnil
    intro x
    exact congrArg (fun ψ : D →ₐ[MvPolynomial (Fin d) Λ] _ => ψ x) hψ
  have hz : q z = q (g z) := congrArg (fun ψ : D →ₐ[MvPolynomial (Fin d) Λ] _ => ψ z) hφ
  exact Ideal.Quotient.eq.mp hz.symm

theorem lift_flat : ∀ {Λ D : Type} [CommRing Λ] [CommRing D] (i : Λ →+* D) {d : ℕ} (t : Fin d → D), (MvPolynomial.eval₂Hom i t).Etale → i.Flat ∧ ∀ (J : Ideal D) (μ : D) (g : D →+* D), (∀ x ∈ J, IsNilpotent x) → g.comp i = i → (∀ k, g (t k) - t k ∈ Ideal.span {μ}) → (∀ z, g z - z ∈ J) → ∀ z, g z - z ∈ Ideal.span {μ} := by
  intro Λ D _ _ i d t het
  exact ⟨flat_of_eval₂Hom_etale i t het, fun J μ g hJ hgi hgt hgJ z =>
    sub_mem_span_of_etale i t het J μ g hJ hgi hgt hgJ z⟩

end GlobalTheory.CompanionTheory.LiftFlat
