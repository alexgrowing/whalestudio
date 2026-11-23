import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.KerRes
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.EtaleSplit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.RegSeq

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private lemma flat_of_etale {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (h : f.Etale) : f.Flat := by
  letI := f.toAlgebra
  haveI : Algebra.Etale A B := h
  exact (inferInstance : Module.Flat A B)

private lemma flat_res {X : Scheme.{0}} {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U) :
    (X.presheaf.map (homOfLE h).op).hom.Flat := by
  have e : V ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ U := h
  have h1 := HasRingHomProperty.appLE (P := @AlgebraicGeometry.Flat) (Q := RingHom.Flat) (𝟙 X)
    (inferInstance : AlgebraicGeometry.Flat (𝟙 X)) ⟨U, hU⟩ ⟨V, hV⟩ e
  have h2 : (𝟙 X : X ⟶ X).appLE U V e = X.presheaf.map (homOfLE h).op := by
    simp [Scheme.Hom.appLE]
    exact Category.id_comp _
  simpa only [h2] using h1

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.trUnique :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α β : B.ι) {N : Z.Opens} (_ : IsAffineOpen N) (h₁ : N ≤ B.V α) (h₂ : N ≤ B.V β) (G G' : Matrix (Fin d) (Fin d) Γ(Z, N)), IsTr B α β h₁ h₂ G → IsTr B α β h₁ h₂ G' → ∀ m l, (i.app N).hom (G m l) = (i.app N).hom (G' m l) := by
  intro K _ W Z Y q i π D d B α β N hN h₁ h₂ G G' hG hG' m l
  let φ₀ : MvPolynomial (Fin d) (MvPolynomial (Fin (B.c α).n) K) →+* Γ(Z, B.V α) :=
    MvPolynomial.eval₂Hom (MvPolynomial.eval₂Hom (Pb.strV q (B.V α)) (B.c α).x) (B.c α).t
  let φ : MvPolynomial (Fin d) (MvPolynomial (Fin (B.c α).n) K) →+* Γ(Z, N) :=
    (Z.presheaf.map (homOfLE h₁).op).hom.comp φ₀
  have hflat : φ.Flat :=
    RingHom.Flat.comp (flat_of_etale φ₀ (etaleSplit B α)) (flat_res (B.c α).affine hN h₁)
  have hX : ∀ l, φ (MvPolynomial.X l) = tN B α h₁ l := by
    intro l
    simp [φ, φ₀, tN]
  have hfun : (fun l => φ (MvPolynomial.X l)) = tN B α h₁ := funext hX
  have hzero : ∑ l, (G m l - G' m l) * φ (MvPolynomial.X l) = 0 := by
    simp only [hX, sub_mul, Finset.sum_sub_distrib]
    rw [← hG m, ← hG' m, sub_self]
  have key := UpperTheory.Gal.KunnethLefschetz.G.regSeq _ _ d φ hflat (fun l => G m l - G' m l)
    (by rw [hzero]; exact zero_mem _) l
  rw [hfun, ← kerRes B α hN h₁, RingHom.mem_ker, map_sub] at key
  exact sub_eq_zero.mp key
