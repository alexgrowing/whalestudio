import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBlockCosetThetaVectorMemThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealMatrixApproxCongruentOneTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormMulMemHatId
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.StdDatum.LiftCoset

theorem globalIntegralMatrix_mem_stdThetaLattice (D : D7) (δ : ℂ) {a d : ℕ} (x : Matrix (Fin d) (Fin a) D.host.E)
    (hx : ∀ i j, ∃ b : 𝓞 D.host.E, x i j = (b : D.host.E)) :
    pt D (tor0 D ⊤ δ) δ x ∈ La0 D (tor0 D ⊤ δ) a d := by
  refine AddSubgroup.subset_closure ⟨δ, AddSubgroup.subset_closure ⟨1, trivial, by simp⟩, _, ?_, rfl⟩
  refine Submodule.subset_span ⟨1, ?_, _, Submodule.subset_span fun v hv i _ => ?_, (one_smul _ _).symm⟩
  · refine FractionalIdeal.one_mem_inv_coe_ideal fun h => ?_
    have h2 := D.host.𝔟_spec.2
    rw [h, Ideal.smul_bot, sup_bot_eq] at h2
    exact bot_ne_top h2
  · have : ∑ j, x i j * v j ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := sum_mem fun j _ => by
      obtain ⟨b, hb⟩ := hx i j
      have h1 := (1 : Submodule (𝓞 D.host.E) D.host.E).smul_mem b (hv j trivial)
      rw [hb]
      simpa [Algebra.smul_def] using h1
    exact this

end GlobalTheory.FunObj.StdDatum.LiftCoset

namespace GlobalTheory.FunObj.StdDatum.LiftCoset

theorem unitBlock_mul_int (D : D7) {a d : ℕ} (r : GA D a) (hr : r ∈ intG D a) (i : Fin d) (j : Fin a) :
    ((unitBlock D 0 a d).map (inc D) * (((r⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i j ∈
      OhE D := by
  rw [Matrix.mul_apply]
  refine sum_mem fun l _ => mul_mem ?_ ?_
  · rw [Matrix.map_apply]
    by_cases h : i.1 = 0 + l.1
    · simp only [unitBlock, Matrix.of_apply, h, if_true, map_one]; exact one_mem _
    · simp only [unitBlock, Matrix.of_apply, h, if_false, map_zero]; exact zero_mem _
  · rw [Subgroup.coe_inv]
    exact ((mem_intG r).1 hr l j).2

theorem om_cosetV_eq : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) → ∀ (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ (r : GA D a), r ∈ intG D a → ∃ x : Matrix (Fin d) (Fin a) D.host.E, pt D (tor0 D ⊤ δ) δ x ∈ (La0 D (tor0 D ⊤ δ) a d) ∧ (∀ i j, (x.map (inc D) - (unitBlock D 0 a d).map (inc D) * (((r⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i j ∈ hatId D 𝔪) ∧ W.Om r 1 (cosetV D δ 𝔪 0 a d e0) = ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ • Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ x) (W.Om r 1 (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0)) := by
  intro D δ hc a d e0 he W 𝔪 h𝔪 r hr
  set T := tor0 D ⊤ δ
  set G := Iop D T (La0 D T a d) (La D T (stdL D a) (skewLat D 𝔪 d)) e0 with hGdef
  set x₀ := unitBlock D 0 a d with hx₀
  have hT := GlobalTheory.ThetaLevels.levels_closed D ⊤ δ hc a d
  have he' : e0 ∈ TT D T a d := hT.1 _ _ (GlobalTheory.FunObj.CosetTT.sd_stdL a) (GlobalTheory.FunObj.CosetTT.sd_stdL d) e0 he
  obtain ⟨M, hM, hMx⟩ := GlobalTheory.FunObj.CosetTT.la_skew_nsmul (D := D) ⊤ δ 𝔪 a d
  have hG : G ∈ TT D T a d :=
    GlobalTheory.FunObj.CosetTT.iop_mem_TT hc _ (fun y hy => ⟨M, hM, hMx y hy⟩) he'
  have hF : Wd D T (pt D T δ x₀) G ∈ TT D T a d := hT.2.1 _ _ hG
  obtain ⟨m, hm, hlift⟩ := W.lift r 1 x₀ G hG
  have hN : 0 < Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using h𝔪)
  set R : Matrix (Fin a) (Fin a) (AE D) := (((r⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) with hR
  set Tm : Matrix (Fin d) (Fin a) (AE D) := x₀.map (inc D) * R with hTm
  have hTint : ∀ i j, Tm i j ∈ OhE D := fun i j => unitBlock_mul_int D r hr i j
  choose b w hw hbw using fun i j =>
    GlobalTheory.CongApprox.exists_int_approx D (m * Ideal.absNorm 𝔪) (Nat.mul_pos hm hN) (Tm i j) (hTint i j)
  set x : Matrix (Fin d) (Fin a) D.host.E := Matrix.of fun i j => (b i j : D.host.E) with hxdef
  have hdiff : ∀ i j, (x.map (inc D) - Tm) i j = -(((m * Ideal.absNorm 𝔪 : ℕ) : AE D) * w i j) := by
    intro i j
    rw [Matrix.sub_apply, Matrix.map_apply, hbw i j]
    simp [hxdef]
  have hnat : ∀ k : ℕ, ((k : ℕ) : AE D) ∈ OhE D := fun k => natCast_mem _ k
  refine ⟨x, LiftCoset.globalIntegralMatrix_mem_stdThetaLattice D δ x (fun i j => ⟨b i j, rfl⟩), fun i j => ?_, ?_⟩
  · rw [hdiff i j, Nat.cast_mul, mul_comm ((m : ℕ) : AE D), mul_assoc]
    exact neg_mem (GlobalTheory.BotPairSmall.BlockIdx.absNorm_mul_mem_hatId D 𝔪 (mul_mem (hnat m) (hw i j)))
  · have hclose : CloseTo D ⊤ m (r : GL (Fin a) (AE D)) ((1 : GA D d) : GL (Fin d) (AE D)) x₀ x := by
      intro i j
      refine ⟨-(((Ideal.absNorm 𝔪 : ℕ) : AE D) * w i j),
        GlobalTheory.CongApprox.OhE_le_IhE_top D _ (neg_mem (mul_mem (hnat _) (hw i j))), ?_⟩
      have e1 : (((1 : GA D d) : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) = 1 := by simp
      have e2 : (((r : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) = R := by
        rw [hR, Subgroup.coe_inv]
      rw [e1, Matrix.one_mul, e2, ← hTm, hdiff i j, Nat.cast_mul]
      ring
    have hl := hlift x hclose
    show W.Om r 1 (((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ • Wd D T (pt D T δ x₀) G) = _
    rw [W.smul r 1 _ _ hF, hl]

end GlobalTheory.FunObj.StdDatum.LiftCoset

end
