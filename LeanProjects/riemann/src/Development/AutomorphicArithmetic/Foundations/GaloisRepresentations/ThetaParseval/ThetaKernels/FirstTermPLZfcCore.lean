import Development.WeilBound.CoreStatements.AutomorphicKernels.ArchimedeanJacquetFirstTerm.ArchimedeanWhittakerTrace.LZfcCore
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl PositivityTheory.SiegelWeilFormula
namespace PositivityTheory.FTA.ZFC
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
variable {Y : Spc F E n}
theorem chr_ker_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {b : GL (Fin n ⊕ Fin n) E} (hb : IsFrame2 σ Y b)
    (β : nA σ Y b) : (∀ T : nF σ Y b, chr B.ψ b T β = 1) ↔ β ∈ nF σ Y b := by
  have hσ : ∀ a, σ (σ a) = a := GlobalTheory.LeviLine.sigma_invol hB.cm
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hB.cm.2.2.1]; norm_num)
  obtain ⟨ε, hε⟩ := hb.1
  have hβ : β.1 ∈ PositivityTheory.SiegelWeilFormula.kfour.nCond σ n ε := (PositivityTheory.SiegelWeilFormula.kfour.mem_nA_iff hσ hε β.1).1 β.2
  constructor
  · intro h
    refine (PositivityTheory.SiegelWeilFormula.kfour.mem_nF_iff β).2 (rat_of_ker hB.cm hB.std ε β.1 ?_ fun T hT => ?_)
    · have e := hβ
      simp only [PositivityTheory.SiegelWeilFormula.kfour.nCond, AddSubgroup.mem_mk, ] at e
      rw [e, Int.cast_smul_eq_zsmul]
    · have hm : incM F T ∈ nA σ Y b := by
        refine (PositivityTheory.SiegelWeilFormula.kfour.mem_nA_iff hσ hε _).2 ?_
        show (incM F T)ᵀ = -((((ε : ℤ) : AE F E)) • (incM F T).map (cA σ))
        rw [Int.cast_smul_eq_zsmul, ← incM_map_cA]
        ext i j
        have := congrFun (congrFun hT i) j
        simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply] at this ⊢
        simp only [incM, Matrix.map_apply, this, map_neg, map_zsmul]
      have hT' : (⟨incM F T, hm⟩ : nA σ Y b) ∈ nF σ Y b := (PositivityTheory.SiegelWeilFormula.kfour.mem_nF_iff _).2 ⟨T, rfl⟩
      exact h ⟨⟨incM F T, hm⟩, hT'⟩
  · intro hβF T
    obtain ⟨T₀, hT₀⟩ := (PositivityTheory.SiegelWeilFormula.kfour.mem_nF_iff β).1 hβF
    obtain ⟨T₁, hT₁⟩ := (PositivityTheory.SiegelWeilFormula.kfour.mem_nF_iff T.1).1 T.2
    unfold chr
    rw [hT₀, hT₁, ← incM_mul, trace_incM_rat, ← map_neg]
    exact hB.std.2.1 _
theorem fc_inj_pt_per_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (b : GL (Fin n ⊕ Fin n) E) (nb : nA σ Y b → G2 σ Y)
    (lam : Measure (nA σ Y b)) (𝓖 : Set (nA σ Y b)) (hb : IsFrame2 σ Y b) (hc : CoefData (σ := σ) (Y := Y) b nb lam 𝓖)
    (f : G2 σ Y → ℂ) (hf : Continuous f) (hper : ∀ β ∈ nF σ Y b, ∀ g, f (nb β * g) = f g) (x : G2 σ Y)
    (hx : ∀ T : nF σ Y b, fc B.ψ b nb lam 𝓖 f T x = 0) : f x = 0 := by
  obtain ⟨hnb, hlam, hFD, -⟩ := hc
  have hσ : ∀ a, σ (σ a) = a := GlobalTheory.LeviLine.sigma_invol hB.cm
  obtain ⟨i1, i2, i3, i4⟩ := PositivityTheory.SiegelWeilFormula.kfour.nA_top hσ hb
  obtain ⟨K, hK, hcov⟩ := PositivityTheory.SiegelWeilFormula.kfour.nF_cocompact hσ hb
  have hψ := GlobalTheory.StdCharFromIsStd.isCharAF hB.std
  have htr : Continuous (Algebra.trace (AF F) (AE F E)) := IsModuleTopology.continuous_of_linearMap _
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (nA σ Y b) (nF σ Y b) K hK hcov
    (nF σ Y b) (chr B.ψ b)
    (fun T => hψ.1.comp (htr.comp ((continuous_const.matrix_mul continuous_subtype_val).matrix_trace)).neg)
    (fun T β β' => by
      unfold chr
      rw [AddSubgroup.coe_add, Matrix.mul_add, Matrix.trace_add, map_add, neg_add, AddChar.map_add_eq_mul])
    (fun T T' β => by
      unfold chr
      rw [AddSubgroup.coe_add, AddSubgroup.coe_add, Matrix.add_mul, Matrix.trace_add, map_add, neg_add,
        AddChar.map_add_eq_mul])
    (fun β => by
      unfold chr
      rw [ZeroMemClass.coe_zero, ZeroMemClass.coe_zero, Matrix.zero_mul, Matrix.trace_zero, map_zero, neg_zero,
        AddChar.map_zero_eq_one])
    (fun T β => hψ.2.1 _)
    (_root_.PositivityTheory.FTA.ZFC.chr_ker_k hB hb)
    lam 𝓖 hlam hFD (fun β => f (nb β * x))
    (hf.comp ((PositivityTheory.SiegelWeilFormula.kfour.nb_continuous hσ hb hnb).mul continuous_const))
    (fun γ hγ β => by
      show f (nb (γ + β) * x) = f (nb β * x)
      rw [PositivityTheory.SiegelWeilFormula.kfour.nb_add hnb, mul_assoc]
      exact hper γ hγ _)
    (fun T => (integral_congr_ae (.of_forall fun β => mul_comm _ _)).trans (hx T))
  have h0 := congrFun key 0
  simpa [PositivityTheory.SiegelWeilFormula.kfour.nb_zero hnb] using h0
end PositivityTheory.FTA.ZFC
end
end
