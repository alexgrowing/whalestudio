import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TotallyRealSelfAnnihilatorAdeleCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSymplecticPointsSelfAnnihilator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleAdaptedPlaneLocalFactor

import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfCoefficientsSeparatingCharactersEqZero

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl PositivityTheory.SiegelWeilFormula

namespace PositivityTheory.FTA.ZFC

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

def tst (σ : E →ₐ[F] E) (ε : ℤˣ) (γ : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) E :=
  γ - (ε : ℤ) • (γ.map σ)ᵀ

theorem zsmul_zsmul_self (ε : ℤˣ) {M : Type} [AddCommGroup M] (x : M) : (ε : ℤ) • (ε : ℤ) • x = x := by
  rw [smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]

theorem tst_mem (hcm : IsCMExt F E σ) (ε : ℤˣ) (γ : Matrix (Fin n) (Fin n) E) :
    (tst σ ε γ)ᵀ = -((ε : ℤ) • (tst σ ε γ).map σ) := by
  ext i j
  simp only [tst, Matrix.transpose_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.neg_apply,
    map_sub, map_zsmul, GlobalTheory.LeviLine.sigma_invol hcm]
  rw [smul_sub, zsmul_zsmul_self]
  abel

theorem incM_map_cA (γ : Matrix (Fin n) (Fin n) E) : (incM F (γ.map σ)) = (incM F γ).map (cA σ) := by
  ext i j
  simp [incM, Matrix.map_apply, GlobalTheory.LeviLine.cA_inclR]

theorem trace_map_cA (M : Matrix (Fin n) (Fin n) (AE F E)) : (M.map (cA σ)).trace = cA σ M.trace := by
  simp [Matrix.trace, map_sum]

theorem trace_tst (ε : ℤˣ) (γ : Matrix (Fin n) (Fin n) E) (β : Matrix (Fin n) (Fin n) (AE F E))
    (hβ : βᵀ = -((ε : ℤ) • β.map (cA σ))) :
    Matrix.trace (incM F (tst σ ε γ) * β) = Matrix.trace (incM F γ * β) + cA σ (Matrix.trace (incM F γ * β)) := by
  have h1 : incM F (tst σ ε γ) = incM F γ - (ε : ℤ) • ((incM F γ).map (cA σ))ᵀ := by
    ext i j
    simp only [tst, incM, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.transpose_apply, map_sub,
      map_zsmul, GlobalTheory.LeviLine.cA_inclR]
  have h2 : Matrix.trace (((incM F γ).map (cA σ))ᵀ * β) = -((ε : ℤ) • cA σ (Matrix.trace (incM F γ * β))) := by
    rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_transpose, hβ, Matrix.neg_mul,
      Matrix.trace_neg, Matrix.smul_mul, Matrix.trace_smul, ← Matrix.map_mul, trace_map_cA, Matrix.trace_mul_comm]
  rw [h1, Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.trace_smul, h2, smul_neg, zsmul_zsmul_self,
    sub_neg_eq_add]

theorem trace_incM_single (β : Matrix (Fin n) (Fin n) (AE F E)) (i j : Fin n) (c : E) :
    Matrix.trace (incM F (Matrix.single j i c) * β) = inclR (F := F) (AF F) c * β i j := by
  have : incM F (Matrix.single j i c) = Matrix.single j i (inclR (F := F) (AF F) c) := by
    ext a b
    simp only [incM, Matrix.map_apply, Matrix.single_apply]
    split_ifs <;> simp
  rw [this, Matrix.trace_single_mul, smul_eq_mul]

theorem trace_cA (hcm : IsCMExt F E σ) (z : AE F E) :
    Algebra.trace (AF F) (AE F E) (cA σ z) = Algebra.trace (AF F) (AE F E) z :=
  Algebra.trace_eq_of_algEquiv
    (AlgEquiv.ofAlgHom (cA σ) (cA σ) (AlgHom.ext (GlobalTheory.LeviLine.cA_invol hcm)) (AlgHom.ext (GlobalTheory.LeviLine.cA_invol hcm))) z

theorem rat_of_ker (hcm : IsCMExt F E σ) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (ε : ℤˣ)
    (β : Matrix (Fin n) (Fin n) (AE F E)) (hβ : βᵀ = -((ε : ℤ) • β.map (cA σ)))
    (h : ∀ T : Matrix (Fin n) (Fin n) E, Tᵀ = -((ε : ℤ) • T.map σ) →
      ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (incM F T * β)))) = 1) :
    ∃ T₀ : Matrix (Fin n) (Fin n) E, β = incM F T₀ := by
  have : IsTotallyReal F := hcm.1
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hcm.2.2.1]; norm_num)
  have hc := GlobalTheory.StdCharFromIsStd.isCharAF hψ
  have key : ∀ i j (e : E), ψ (Algebra.trace (AF F) (AE F E) ((1 : AF F) ⊗ₜ[F] e * β i j)) = 1 := by
    intro i j e
    have h1 := h _ (tst_mem hcm ε (Matrix.single j i (-(e / 2))))
    rw [trace_tst ε _ β hβ, trace_incM_single, map_add, trace_cA hcm] at h1
    have hI : ∀ c : E, inclR (F := F) (AF F) c = (1 : AF F) ⊗ₜ[F] c := fun c => rfl
    have hadd : ∀ a c : E, Algebra.trace (AF F) (AE F E) ((1 : AF F) ⊗ₜ[F] (a + c) * β i j) =
        Algebra.trace (AF F) (AE F E) ((1 : AF F) ⊗ₜ[F] a * β i j) +
          Algebra.trace (AF F) (AE F E) ((1 : AF F) ⊗ₜ[F] c * β i j) := fun a c => by
      rw [TensorProduct.tmul_add, add_mul, map_add]
    have hneg : ∀ a : E, Algebra.trace (AF F) (AE F E) ((1 : AF F) ⊗ₜ[F] (-a) * β i j) =
        -Algebra.trace (AF F) (AE F E) ((1 : AF F) ⊗ₜ[F] a * β i j) := fun a => by
      rw [TensorProduct.tmul_neg, neg_mul, map_neg]
    have h2 : -(Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) (-(e / 2)) * β i j) +
        Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) (-(e / 2)) * β i j)) =
        Algebra.trace (AF F) (AE F E) ((1 : AF F) ⊗ₜ[F] e * β i j) := by
      rw [hI, ← hadd, ← hneg]
      congr 3
      ring
    rw [h2] at h1
    exact h1
  have hent : ∀ i j, ∃ e : E, β i j = (1 : AF F) ⊗ₜ[F] e := fun i j =>
    GlobalTheory.RatAnnih.tensor_rat (β i j) fun e =>
      (GlobalTheory.SWQ.Annihilator.self_annihilator F inferInstance ψ hc).2 _ fun c =>
        (congrArg ψ (GlobalTheory.RatAnnih.trace_mul_algebraMap (β i j) e c)).trans (key i j (c • e))
  choose M hM using hent
  exact ⟨Matrix.of M, Matrix.ext fun i j => (hM i j).trans rfl⟩

variable {Y : Spc F E n}

def chr (ψ : AddChar (AF F) ℂ) (b : GL (Fin n ⊕ Fin n) E) (T : nF σ Y b) (β : nA σ Y b) : ℂ :=
  ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))

theorem incM_mul (A C : Matrix (Fin n) (Fin n) E) : incM F (A * C) = incM F A * incM F C := by
  simp [incM, Matrix.map_mul]

theorem trace_incM_rat [FiniteDimensional F E] (A : Matrix (Fin n) (Fin n) E) :
    Algebra.trace (AF F) (AE F E) (Matrix.trace (incM F A)) = algebraMap F (AF F) (Algebra.trace F E (Matrix.trace A)) := by
  have : Matrix.trace (incM F A) = (1 : AF F) ⊗ₜ[F] Matrix.trace A := by
    simp [incM, Matrix.trace, inclR, TensorProduct.tmul_sum]
  rw [this, GlobalTheory.LatVac.trace_tmul, one_mul]

theorem chr_ker {B : Base F E} (hB : B.IsGood σ) {b : GL (Fin n ⊕ Fin n) E} (hb : IsFrame2 σ Y b)
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

theorem fc_inj_pt_per {B : Base F E} (hB : B.IsGood σ) (b : GL (Fin n ⊕ Fin n) E) (nb : nA σ Y b → G2 σ Y)
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
    (chr_ker hB hb)
    lam 𝓖 hlam hFD (fun β => f (nb β * x))
    (hf.comp ((PositivityTheory.SiegelWeilFormula.kfour.nb_continuous hσ hb hnb).mul continuous_const))
    (fun γ hγ β => by
      show f (nb (γ + β) * x) = f (nb β * x)
      rw [PositivityTheory.SiegelWeilFormula.kfour.nb_add hnb, mul_assoc]
      exact hper γ hγ _)
    (fun T => (integral_congr_ae (.of_forall fun β => mul_comm _ _)).trans (hx T))
  have h0 := congrFun key 0
  simpa [PositivityTheory.SiegelWeilFormula.kfour.nb_zero hnb] using h0

theorem fc_inj_pt_core {B : Base F E} (hB : B.IsGood σ) (b : GL (Fin n ⊕ Fin n) E) (nb : nA σ Y b → G2 σ Y)
    (lam : Measure (nA σ Y b)) (𝓖 : Set (nA σ Y b)) (hb : IsFrame2 σ Y b) (hc : CoefData (σ := σ) (Y := Y) b nb lam 𝓖)
    (f : G2 σ Y → ℂ) (hf : Continuous f) (hinv : ∀ γ ∈ rat2 σ Y, ∀ y, f (γ * y) = f y) (x : G2 σ Y)
    (hx : ∀ T : nF σ Y b, fc B.ψ b nb lam 𝓖 f T x = 0) : f x = 0 :=
  fc_inj_pt_per hB b nb lam 𝓖 hb hc f hf (fun β hβ g => hinv _ (PositivityTheory.SiegelWeilFormula.kfour.nb_rat hc.1 β hβ) g) x hx

end PositivityTheory.FTA.ZFC

end
