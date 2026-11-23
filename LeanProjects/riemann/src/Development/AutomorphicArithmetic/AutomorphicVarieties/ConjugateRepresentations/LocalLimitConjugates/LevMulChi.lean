import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CptGard
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.QhtFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.ExpOfDeriv
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.EllFacts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousSplitCentre
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem lev_mulChi {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (χ : HChar E) (φ : Sm E a)
    (h : HasLev φ) : HasLev (mulChi a χ φ) := by
  let S : Subgroup (GL (Fin a) (Af E)) :=
    { carrier := {k | finRep E a k (mulChi a χ φ) = mulChi a χ φ}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [map_mul, Module.End.mul_apply, hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  change IsOpen (S : Set (GL (Fin a) (Af E)))
  refine S.isOpen_of_mem_nhds (g := 1) (mem_of_superset
    ((h.inter (isOpen_ker_chiDet (a := a) χ)).mem_nhds ⟨?_, by simp⟩) ?_)
  · change finRep E a 1 φ = φ
    simp
  · rintro k ⟨hk, hk'⟩
    have e1 : rt E a (finGL E a k) φ = φ := hk
    have e2 : chiDet a χ (finGL E a k) = 1 := hk'
    change rt E a (finGL E a k) (mulChi a χ φ) = mulChi a χ φ
    rw [rt_mulChi, e1, e2, Units.val_one, one_smul]

theorem UpperTheory.V.Cj.H.twCpt :
    UpperTheory.V.Cj.H.TwCpt := by
  intro E _ _ _ a ha μ _ _ r χ hχ φ hl hlev hone ⟨R, hR⟩
  obtain ⟨C, hC, hC'⟩ := (qhtFacts E a).2.2.2 R
  have hz : lie E a (oneL E a) (mulChi a χ φ) = (0 : ℂ) • mulChi a χ φ := by
    rw [hχ.2, hone, (ellFacts E a).1 ha, mul_one, ← add_smul, neg_add_cancel, zero_smul, map_zero, zero_smul]
  refine cptGard E a μ _ (lev_mulChi χ φ hlev) (CuspidalL2GL.leftInv_latticeGL (fun γ g => ?_) fun t g => ?_)
    ((fun p : ℝ × GA E a => splitCentre E a p.1 * p.2) '' (Set.Icc (-1 : ℝ) 0 ×ˢ C))
    ((isCompact_Icc.prod hC).image
      ((GlobalTheory.OneRep.SplitTwist.continuous_splitCentre.comp continuous_fst).mul continuous_snd)) fun g hg => ?_
  · rw [mulChi_apply, mulChi_apply, map_mul, chiDet_ratGL, one_mul, hl]
  · rw [aInv E a _ _ hz t g, zero_mul, Complex.exp_zero, one_mul]
  · have h1 : qht g ≤ R := not_lt.1 fun h => hg (by rw [mulChi_apply, hR g h, zero_mul])
    obtain ⟨γ, t, ht⟩ := hC' g h1
    refine ⟨ratGL E a γ * splitCentre E a 1 ^ ⌊t⌋,
      mul_mem (CuspidalL2GL.ratGL_mem_latticeGL γ) (CuspidalL2GL.zpow_mem_latticeGL _),
      (-Int.fract t, ratGL E a γ * splitCentre E a t * g),
      ⟨⟨neg_le_neg (Int.fract_lt_one t).le, neg_nonpos.2 (Int.fract_nonneg t)⟩, ht⟩, ?_⟩
    have e : -Int.fract t + t = ((⌊t⌋ : ℤ) : ℝ) := by rw [Int.fract]; ring
    change splitCentre E a (-Int.fract t) * (ratGL E a γ * splitCentre E a t * g) = _
    rw [← CuspidalL2GL.splitCentre_intCast, ← e, CuspidalL2GL.splitCentre_add, ← mul_assoc, ← mul_assoc,
      CuspidalL2GL.splitCentre_comm (-Int.fract t) (ratGL E a γ), mul_assoc (ratGL E a γ)]
