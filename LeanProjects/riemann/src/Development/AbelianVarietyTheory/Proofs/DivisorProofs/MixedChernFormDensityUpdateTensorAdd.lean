import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem det_perm_update_add {D : ℕ} (F : Fin D → Matrix (Fin D) (Fin D) ℂ) (i : Fin D)
    (P Q : Matrix (Fin D) (Fin D) ℂ) (τ : Equiv.Perm (Fin D)) :
    (Matrix.of fun j l => Function.update F i (P + Q) (τ l) j l).det =
      (Matrix.of fun j l => Function.update F i P (τ l) j l).det +
      (Matrix.of fun j l => Function.update F i Q (τ l) j l).det := by
  have key : ∀ R : Matrix (Fin D) (Fin D) ℂ, (Matrix.of fun j l => Function.update F i R (τ l) j l) =
      (Matrix.of fun j l => Function.update F i 0 (τ l) j l).updateCol (τ.symm i)
        (fun j => R j (τ.symm i)) := by
    intro R
    ext j l
    by_cases h : l = τ.symm i
    · subst h
      simp
    · have hl : τ l ≠ i := fun e => h (by rw [← e, Equiv.symm_apply_apply])
      simp [Matrix.updateCol_ne h, Function.update_of_ne hl]
  rw [key (P + Q), key P, key Q, ← Matrix.det_updateCol_add]
  rfl

theorem dens_update_tens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (L : Fin D → MLine p σ) (i : Fin D) (A B : MLine p σ) (c : AlgChart p σ D), ∀ y ∈ c.e.source, dens (Function.update L i (A.tens B)) c y = dens (Function.update L i A) c y + dens (Function.update L i B) c y := by
  intro k _ X p σ D L i A B c y hy
  let G : MLine p σ → Matrix (Fin D) (Fin D) ℂ := fun M => c.hess M.φ (pick M.φ.isLB y) y
  have hd : ∀ L' : Fin D → MLine p σ, dens L' c y = (Real.pi ^ D)⁻¹ *
      (∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => (G ∘ L') (τ l) j l).det).re := fun _ => rfl
  have hT : G (A.tens B) = G A + G B := by
    have ha := mem_pick A.φ.isLB y
    have hb := mem_pick B.φ.isLB y
    have hab : y ∈ ptsIn p σ ((A.tens B).B.U (pick A.φ.isLB y, pick B.φ.isLB y)) :=
      mem_ptsIn_inf.2 ⟨ha, hb⟩
    show c.hess (A.tens B).φ _ y = _
    rw [c.hess_eq (A.tens B).cInf hy hab (mem_pick _ y)]
    have ho := isOpen_over c.e
      (isOpen_ptsIn (p := p) (σ := σ) (A.B.U (pick A.φ.isLB y) ⊓ B.B.U (pick B.φ.isLB y)))
    have hm := mem_over c.e hy (mem_ptsIn_inf.2 ⟨ha, hb⟩)
    have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho
      ((contDiffOn_chart (A.cInf _) c).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).1⟩)
      ((contDiffOn_chart (B.cInf _) c).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).2⟩) 1 hm
    simp only [one_mul, Complex.ofReal_one, one_smul, Function.comp_apply] at e
    exact e
  rw [hd, hd, hd, Function.comp_update, Function.comp_update, Function.comp_update, hT]
  simp only [det_perm_update_add, Finset.sum_add_distrib, Complex.add_re]
  ring

end GlobalTheory.Mix
