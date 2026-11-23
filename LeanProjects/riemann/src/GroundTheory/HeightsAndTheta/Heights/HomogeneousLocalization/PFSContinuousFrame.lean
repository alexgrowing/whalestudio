import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TensorProduct GroundTheory.Arith.SchemeCoh

universe u

noncomputable section

namespace SectionsLatticeFS

open ProjScheme

lemma rep_ne_zero_of_mem_chartDomain {N : ℕ} {j : Fin (N + 1)} {v : CP N}
    (hv : v ∈ CP.chartDomain j) : v.rep j ≠ 0 := by
  have h := CP.mk_mem_chartDomain j v.rep v.rep_nonzero
  rw [Projectivization.mk_rep] at h
  exact h.mp hv

lemma norm_rep_pow_div {N : ℕ} (n : ℕ) (j : Fin (N + 1)) (v : CP N) :
    ‖v.rep j‖ ^ n / norm2 v.rep ^ n =
      CP.fsNormPoly n ((MvPolynomial.X j : MvPolynomial (Fin (N + 1)) ℂ) ^ n) v := by
  simp [CP.fsNormPoly, norm_pow]

theorem continuousOn_chart (h₁ : FSIndex.Statement.{u}) (h₂ : ComplexMetric.RegularContinuous.Statement.{u})
    {A : Type u} [CommRing A] {N n : ℕ} (ρ : A →+* ℂ) {U : (self A N).X.Opens}
    (e : ((preMod (self A N).X).obj (twistN A N n)).obj (op U)) (j : Fin (N + 1)) :
    ContinuousOn (fun y : {x : (self A N).complexPoints ρ // (self A N).point x ∈ U} =>
        fsFibreNorm n ρ y.1 ((self A N).sectionValue y.1 y.2 e))
      {y | y.1.1 ∈ CP.chartDomain j} := by
  let V : (self A N).X.Opens := U ⊓ ProjSpace.stdOpen A N j
  have hVU : V ≤ U := inf_le_left
  have hVj : V ≤ ProjSpace.stdOpen A N j := inf_le_right

  obtain ⟨f, hf⟩ := (isBasisOn_frame (A := A) j n V hVj).2 (resM _ hVU e)
  have hV : ∀ y : {y : {x : (self A N).complexPoints ρ // (self A N).point x ∈ U} //
      y.1.1 ∈ CP.chartDomain j}, (self A N).point y.1.1 ∈ V := fun y =>
    ⟨y.1.2, point_mem_stdOpen y.1.1 (rep_ne_zero_of_mem_chartDomain y.2)⟩
  let ι := fun y : {y : {x : (self A N).complexPoints ρ // (self A N).point x ∈ U} //
      y.1.1 ∈ CP.chartDomain j} => (⟨y.1.1, hV y⟩ : {x : (self A N).complexPoints ρ // (self A N).point x ∈ V})
  have hι : Continuous ι :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

  have hval : ∀ y : {y : {x : (self A N).complexPoints ρ // (self A N).point x ∈ U} //
      y.1.1 ∈ CP.chartDomain j},
      fsFibreNorm n ρ y.1.1 ((self A N).sectionValue y.1.1 y.1.2 e) =
        ‖(self A N).evalAtPoint y.1.1 (germR (hV y) f)‖ *
          CP.fsNormPoly n ((MvPolynomial.X j : MvPolynomial (Fin (N + 1)) ℂ) ^ n) y.1.1.1 := by
    intro y
    have hyj := rep_ne_zero_of_mem_chartDomain y.2
    have hp := point_mem_stdOpen y.1.1 hyj
    rw [h₁ A N n ρ y.1.1 j hyj, mul_div_assoc, norm_rep_pow_div]
    congr 2
    change (Via.ofComplex ((self A N).evalAtPoint y.1.1)).symm
      (fibreEquiv (X := (self A N).X) (L := twistN A N n) ((self A N).evalAtPoint y.1.1) hp
        (isBasisOn_frame (A := A) j n)
        (fibreMk (X := (self A N).X) (twistN A N n) ((self A N).evalAtPoint y.1.1) 1
          (germM (X := (self A N).X) (L := twistN A N n) y.1.2 e))) = _
    rw [← germM_resM hVU (hV y) e, ← hf, germM_smul, germM_resM hVj (hV y)]
    have key := fibreEquiv_fibreMk (φ := (self A N).evalAtPoint y.1.1) hp
      (isBasisOn_frame (A := A) j n) 1 (germR (hV y) f)
    rw [mul_one] at key
    exact (congrArg (Via.ofComplex ((self A N).evalAtPoint y.1.1)).symm key).trans
      (RingEquiv.symm_apply_apply _ _)
  rw [continuousOn_iff_continuous_domRestrict]
  have hc : Continuous fun y : {y : {x : (self A N).complexPoints ρ // (self A N).point x ∈ U} //
      y.1.1 ∈ CP.chartDomain j} =>
        ‖(self A N).evalAtPoint y.1.1 (germR (hV y) f)‖ *
          CP.fsNormPoly n ((MvPolynomial.X j : MvPolynomial (Fin (N + 1)) ℂ) ^ n) y.1.1.1 :=
    (continuous_norm.comp ((h₂ A N (self A N) ρ V f).comp hι)).mul
      ((CP.continuous_fsNormPoly (MvPolynomial.isHomogeneous_X_pow j n)).comp
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)))
  exact hc.congr fun y => (hval y).symm

theorem FSContinuousFrame.proof (h₁ : FSIndex.Statement.{u})
    (h₂ : ComplexMetric.RegularContinuous.Statement.{u}) : FSContinuousFrame.Statement.{u} := by
  intro A _ N n ρ U e _
  rw [continuous_iff_continuousAt]
  intro y₀
  let j := CP.chartIndex y₀.1.1
  have hW : IsOpen {y : {x : (self A N).complexPoints ρ // (self A N).point x ∈ U} |
      y.1.1 ∈ CP.chartDomain j} :=
    (CP.isOpen_chartDomain j).preimage
      (continuous_subtype_val.comp continuous_subtype_val :
        Continuous fun y : {x : (self A N).complexPoints ρ // (self A N).point x ∈ U} => y.1.1)
  exact (continuousOn_chart h₁ h₂ ρ e j).continuousAt
    (hW.mem_nhds (CP.mem_chartDomain_chartIndex y₀.1.1))

example (h₁ : FSIndex.Statement.{0}) (h₂ : ComplexMetric.RegularContinuous.Statement.{0}) :
    Continuous fun y : {x : (self (NumberField.RingOfIntegers ℚ) 1).complexPoints
        (intEmb (Rat.castHom ℂ)) // (self _ 1).point x ∈ ProjSpace.stdOpen _ 1 0} =>
      fsFibreNorm 1 _ y.1 ((self _ 1).sectionValue y.1 y.2 (stdFrame _ 0 1)) :=
  FSContinuousFrame.proof h₁ h₂ _ _ _ _ _ _ (isBasisOn_frame 0 1)

end SectionsLatticeFS

end

end GroundTheory.Heights₂.Heights
