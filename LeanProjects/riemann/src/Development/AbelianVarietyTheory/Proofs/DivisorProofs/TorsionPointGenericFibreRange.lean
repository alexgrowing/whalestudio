import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompReixMemAdm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesFactorizableRestrictionFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelArchimedeanUnipotentSupport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenDoubledCoordsProductFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TotallyRealSelfAnnihilatorAdeleCharacter
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot GlobalTheory.DblBox

noncomputable section

namespace GlobalTheory.DblBoxCoef

open ComplexConjugate

theorem integral_split {R κ κ₂ : Type} [AddCommGroup R] [TopologicalSpace R] [IsTopologicalAddGroup R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [Fintype κ] [Fintype κ₂]
    [MeasurableSpace (κ₂ → R)] [BorelSpace (κ₂ → R)] [MeasurableSpace (κ → R)] [BorelSpace (κ → R)]
    (e : κ ⊕ κ ≃ κ₂) (μ : Measure (κ₂ → R)) [μ.IsAddHaarMeasure] (m : Measure (κ → R)) [m.IsAddHaarMeasure] :
    ∃ C : ℂ, ∀ P Q : (κ → R) → ℂ, ∫ x, P (fun i => x (e (.inl i))) * Q (fun i => x (e (.inr i))) ∂μ =
      C * ((∫ y, P y ∂m) * ∫ y, Q y ∂m) := by
  let T : (κ₂ → R) ≃ₜ+ (κ → R) × (κ → R) :=
    { toFun := fun x => (fun i => x (e (.inl i)), fun i => x (e (.inr i)))
      invFun := fun y k => Sum.elim y.1 y.2 (e.symm k)
      left_inv := fun x => funext fun k => by
        obtain ⟨s, rfl⟩ := e.surjective k
        cases s <;> simp
      right_inv := fun y => by ext i <;> simp
      map_add' := fun _ _ => rfl
      continuous_toFun := (continuous_pi fun i => continuous_apply _).prodMk (continuous_pi fun i => continuous_apply _)
      continuous_invFun := continuous_pi fun k => by
        rcases e.symm k with s | s
        · exact (continuous_apply s).comp continuous_fst
        · exact (continuous_apply s).comp continuous_snd }
  haveI : (μ.map T).IsAddHaarMeasure := T.isAddHaarMeasure_map μ
  have key := Measure.isAddLeftInvariant_eq_smul (μ.map T) (m.prod m)
  refine ⟨((Measure.addHaarScalarFactor (μ.map T) (m.prod m) : ℝ) : ℂ), fun P Q => ?_⟩
  have h1 := integral_map_equiv (μ := μ) T.toHomeomorph.toMeasurableEquiv (fun z => P z.1 * Q z.2)
  have h2 : Measure.map (⇑T.toHomeomorph.toMeasurableEquiv) μ = μ.map T := rfl
  rw [h2, key, integral_smul_nnreal_measure, integral_prod_mul] at h1
  refine Eq.trans (h1.symm : _) ?_
  simp [NNReal.smul_def]

end GlobalTheory.DblBoxCoef

namespace GlobalTheory.DblBoxCoef

open ComplexConjugate

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

theorem actAB_inv {m k : ℕ} {J : Matrix (Fin m) (Fin m) E} {J' : Matrix (Fin k) (Fin k) E} (p : UA σ J × UA σ J')
    (x : Matrix (Fin m) (Fin k) (AE F E)) : actAB (cA σ) p (actAB (cA σ) p⁻¹ x) = x := by
  have h1 : mat p.1 * mat (p⁻¹).1 = 1 := by
    show (((p.1 * p.1⁻¹ : UA σ J) : GL (Fin m) (AE F E)) : Matrix (Fin m) (Fin m) (AE F E)) = 1
    rw [mul_inv_cancel]; rfl
  have h2 : mat p.2 * mat (p⁻¹).2 = 1 := by
    show (((p.2 * p.2⁻¹ : UA σ J') : GL (Fin k) (AE F E)) : Matrix (Fin k) (Fin k) (AE F E)) = 1
    rw [mul_inv_cancel]; rfl
  show mat p.1 * (mat (p⁻¹).1 * x * (mat (p⁻¹).2)ᵀ) * (mat p.2)ᵀ = x
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (mat p.1), h1, Matrix.one_mul, ← Matrix.transpose_mul, h2, Matrix.transpose_one,
    Matrix.mul_one]

theorem upB_blk {R : Type} [CommRing R] (A B : Matrix (Fin n) (Fin n) R) (v : Matrix (Fin (n + n)) (Fin d) R)
    (H : Matrix (Fin d) (Fin d) R) : upB (GlobalTheory.Doubling.blkMat finSumFinEquiv A B * v * H) = A * upB v * H := by
  have : upB (GlobalTheory.Doubling.blkMat finSumFinEquiv A B * v) = A * upB v := by
    funext i j
    simp only [upB, Matrix.mul_apply]
    rw [← finSumFinEquiv.sum_comp]
    simp [GlobalTheory.Doubling.blkMat, Fintype.sum_sum_type]
  rw [← this]; rfl

theorem loB_blk {R : Type} [CommRing R] (A B : Matrix (Fin n) (Fin n) R) (v : Matrix (Fin (n + n)) (Fin d) R)
    (H : Matrix (Fin d) (Fin d) R) : loB (GlobalTheory.Doubling.blkMat finSumFinEquiv A B * v * H) = B * loB v * H := by
  have : loB (GlobalTheory.Doubling.blkMat finSumFinEquiv A B * v) = B * loB v := by
    funext i j
    simp only [loB, Matrix.mul_apply]
    rw [← finSumFinEquiv.sum_comp]
    simp only [GlobalTheory.Doubling.blkMat, Matrix.submatrix_apply, Equiv.symm_apply_apply, Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]
  rw [← this]; rfl

theorem rho_bx {J : Matrix (Fin n) (Fin n) E} {J' : Matrix (Fin d) (Fin d) E} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E}
    {co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J) (incM F J')) (Fin n × Fin d)}
    {cb : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J₂) (incM F J')) (Fin (n + n) × Fin d)} (hb : IsBoxCo co cb)
    (ψ : AddChar (AF F) ℂ) (hψ : ∀ t, ‖ψ t‖ = 1) (u : Matrix (Fin (n + n)) (Fin d) (AE F E)) (f₁ f₂ : Fn F n d) :
    cb.rho ψ u (bx f₁ (cj f₂)) = bx (co.rho ψ (upB u) f₁) (cj (co.rho ψ (loB u) f₂)) := by
  rw [bx, hb.rho_reix]
  exact congrArg (reix (rIdx n d)) (GlobalTheory.DblBoxRho.schr_boxFun ψ hψ (co.e (upB u)) (co.e (loB u)) f₁ f₂)

theorem integral_bx [MeasurableSpace (Fin (n + n) × Fin d → AF F)] [BorelSpace (Fin (n + n) × Fin d → AF F)]
    [MeasurableSpace (Fin n × Fin d → AF F)] [BorelSpace (Fin n × Fin d → AF F)]
    (μ : Measure (Fin (n + n) × Fin d → AF F)) [μ.IsAddHaarMeasure] (m : Measure (Fin n × Fin d → AF F))
    [m.IsAddHaarMeasure] : ∃ C : ℂ, ∀ a b a' b' : Fn F n d,
      ∫ x, bx a (cj b) x * conj (bx a' (cj b') x) ∂μ =
        C * ((∫ y, a y * conj (a' y) ∂m) * conj (∫ y, b y * conj (b' y) ∂m)) := by
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  obtain ⟨C, hC⟩ := integral_split (rIdx n d) μ m
  refine ⟨C, fun a b a' b' => ?_⟩
  rw [← integral_conj, ← hC]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change a (fun i => x (rIdx n d (.inl i))) * conj (b (fun i => x (rIdx n d (.inr i)))) *
      conj (a' (fun i => x (rIdx n d (.inl i))) * conj (b' (fun i => x (rIdx n d (.inr i))))) =
    a (fun i => x (rIdx n d (.inl i))) * conj (a' (fun i => x (rIdx n d (.inl i)))) *
      conj (b (fun i => x (rIdx n d (.inr i))) * conj (b' (fun i => x (rIdx n d (.inr i)))))
  simp only [map_mul, Complex.conj_conj]
  ring

end GlobalTheory.DblBoxCoef

namespace GlobalTheory.DblBoxCoef

open ComplexConjugate

theorem weil_bx_prop : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ →
    ∀ X₂ : Spc F E (n + n), X₂.J = dblGram finSumFinEquiv X.J →
    ∀ i : UA σ X.J × UA σ X.J →* UA σ X₂.J, (∀ g g', mat (i (g, g')) = blkMat finSumFinEquiv (mat g) (mat g')) →
    ∀ (Mb : Model σ X₂ W) (χ χ' : Chr F E) (omb : Rep σ X₂ W) (r₂ s₂ : ℕ), IsPair B Mb χ χ' omb r₂ s₂ r₁ s₁ → IsBoxCo M.co Mb.co →
    ∀ φ₁ ∈ schA F (Fin n × Fin d), ∀ φ₂ ∈ schA F (Fin n × Fin d), ∀ (g₁ g₂ : UA σ X.J) (h : UA σ W.J), ∃ a : ℂ,
      omb (i (g₁, g₂), h) (bx φ₁ (cj φ₂)) = a • bx (om (g₁, h) φ₁) (cj (om (g₂, h) φ₂)) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s' r₁ s₁ hP X₂ _ i hi Mb χ χ' omb r₂ s₂ hPb hbox φ₁ hφ₁ φ₂ hφ₂ g₁ g₂ h
  letI : MeasurableSpace (Fin (n + n) × Fin d → AF F) := borel _
  haveI : BorelSpace (Fin (n + n) × Fin d → AF F) := ⟨rfl⟩
  letI : MeasurableSpace (Fin n × Fin d → AF F) := borel _
  haveI : BorelSpace (Fin n × Fin d → AF F) := ⟨rfl⟩
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  have hF : IsTotallyReal F := hP.base.cm.1
  have hψ := GlobalTheory.StdCharFromIsStd.isCharAF hP.base.std
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hP.weil
  have hWb := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hPb.weil
  set γ : UA σ X₂.J × UA σ W.J := (i (g₁, g₂), h) with hγ
  set γ₁ : UA σ X.J × UA σ W.J := (g₁, h) with hγ₁
  set γ₂ : UA σ X.J × UA σ W.J := (g₂, h) with hγ₂
  have hB0 : bx φ₁ (cj φ₂) ∈ schA F _ := bx_mem_schA hφ₁ (cj_mem_schA hφ₂)
  have hΨ : omb γ (bx φ₁ (cj φ₂)) ∈ schA F _ := hWb.pres γ _ hB0
  have hΦ : bx (om γ₁ φ₁) (cj (om γ₂ φ₂)) ∈ schA F _ :=
    bx_mem_schA (hW.pres γ₁ φ₁ hφ₁) (cj_mem_schA (hW.pres γ₂ φ₂ hφ₂))
  obtain ⟨c1, b1, i1⟩ := GlobalTheory.SplitSvN.schA_facts hF hΦ
  obtain ⟨c2, b2, i2⟩ := GlobalTheory.SplitSvN.schA_facts hF hΨ
  have unitX : ∀ μ : Measure (Fin n × Fin d → AF F), μ.IsAddHaarMeasure → ∀ (p : UA σ X.J × UA σ W.J) (f : Fn F n d),
      f ∈ schA F _ → ∀ z, ∫ x, om p f x * conj (M.co.rho B.ψ z (om p f) x) ∂μ =
        ∫ x, f x * conj (M.co.rho B.ψ (actAB (cA σ) p⁻¹ z) f x) ∂μ := by
    intro μ hμ p f hf z
    have e1 : M.co.rho B.ψ z (om p f) = om p (M.co.rho B.ψ (actAB (cA σ) p⁻¹ z) f) := by
      rw [hW.impl p _ f hf, actAB_inv]
    rw [e1, GlobalTheory.CptCoeff.integral_mul_conj_map (μ := μ) (schA F _)
      (fun f hf => GlobalTheory.WeilM.schA_memLp_two F _ μ hμ f hf) (om p) (fun f hf => hW.pres _ f hf)
      (fun f hf => hW.unit μ hμ _ f hf) hf (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hP.base.std _ f hf)]
  have unitX₂ : ∀ μ : Measure (Fin (n + n) × Fin d → AF F), μ.IsAddHaarMeasure → ∀ (p : UA σ X₂.J × UA σ W.J)
      (f : Fn F (n + n) d), f ∈ schA F _ → ∀ z, ∫ x, omb p f x * conj (Mb.co.rho B.ψ z (omb p f) x) ∂μ =
        ∫ x, f x * conj (Mb.co.rho B.ψ (actAB (cA σ) p⁻¹ z) f x) ∂μ := by
    intro μ hμ p f hf z
    have e1 : Mb.co.rho B.ψ z (omb p f) = omb p (Mb.co.rho B.ψ (actAB (cA σ) p⁻¹ z) f) := by
      rw [hWb.impl p _ f hf, actAB_inv]
    rw [e1, GlobalTheory.CptCoeff.integral_mul_conj_map (μ := μ) (schA F _)
      (fun f hf => GlobalTheory.WeilM.schA_memLp_two F _ μ hμ f hf) (omb p) (fun f hf => hWb.pres _ f hf)
      (fun f hf => hWb.unit μ hμ _ f hf) hf (GlobalTheory.HeisSchA.rho_mem_schA Mb B.ψ hPb.base.std _ f hf)]
  have hinv : mat (γ⁻¹).1 = blkMat finSumFinEquiv (mat g₁⁻¹) (mat g₂⁻¹) := by
    have : (γ⁻¹).1 = i (g₁⁻¹, g₂⁻¹) := by
      show (i (g₁, g₂))⁻¹ = i (g₁⁻¹, g₂⁻¹)
      rw [← map_inv]; rfl
    rw [this, hi]
  have hup : ∀ u, upB (actAB (cA σ) γ⁻¹ u) = actAB (cA σ) γ₁⁻¹ (upB u) := fun u => by
    show upB (mat (γ⁻¹).1 * u * (mat (γ⁻¹).2)ᵀ) = mat (γ₁⁻¹).1 * upB u * (mat (γ₁⁻¹).2)ᵀ
    rw [hinv, upB_blk]; rfl
  have hlo : ∀ u, loB (actAB (cA σ) γ⁻¹ u) = actAB (cA σ) γ₂⁻¹ (loB u) := fun u => by
    show loB (mat (γ⁻¹).1 * u * (mat (γ⁻¹).2)ᵀ) = mat (γ₂⁻¹).1 * loB u * (mat (γ₂⁻¹).2)ᵀ
    rw [hinv, loB_blk]; rfl
  obtain ⟨c, hc⟩ := GlobalTheory.SplitSvN.proportional_of_coeff B.ψ hψ.1 hψ.2.1
    (GlobalTheory.SWQ.Annihilator.self_annihilator F hF B.ψ hψ).1 1 (one_mul 1) (bx (om γ₁ φ₁) (cj (om γ₂ φ₂)))
    (omb γ (bx φ₁ (cj φ₂))) (fun _ => 1) (bx (om γ₁ φ₁) (cj (om γ₂ φ₂))) (omb γ (bx φ₁ (cj φ₂)))
    (fun x => by simp) (fun x => by simp) c1 c2 b1 b2 i1 i2 (fun x₁ y₁ _ _ μ hμ => by
      haveI := hμ
      obtain ⟨C, hC⟩ := integral_bx μ (Measure.addHaar : Measure (Fin n × Fin d → AF F))
      have hm : (Measure.addHaar : Measure (Fin n × Fin d → AF F)).IsAddHaarMeasure := inferInstance
      set u := Mb.co.e.symm (x₁, y₁) with hu
      have hw : schr B.ψ (x₁, y₁) = Mb.co.rho B.ψ u := by
        simp only [Darboux.rho, hu, LinearEquiv.apply_symm_apply]
      rw [hw, unitX₂ μ hμ γ _ hB0 u, rho_bx hbox B.ψ hψ.2.1, rho_bx hbox B.ψ hψ.2.1, hC, hC,
        unitX _ hm γ₁ φ₁ hφ₁, unitX _ hm γ₂ φ₂ hφ₂, hup, hlo])
  exact ⟨c, hc⟩

end GlobalTheory.DblBoxCoef

end
