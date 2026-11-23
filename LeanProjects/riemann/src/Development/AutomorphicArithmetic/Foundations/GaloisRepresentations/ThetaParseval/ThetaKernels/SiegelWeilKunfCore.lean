import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.UnfoldCore
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKunfCover
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKunfCells

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.kunf
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E}
theorem unfoldCore_k (B : Base F E) (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hb : IsFrame2 σ Y b) {nb : nA σ Y b → G2 σ Y}
    {lam : Measure (nA σ Y b)} {𝓖 : Set (nA σ Y b)} (hc : CoefData (σ := σ) (Y := Y) b nb lam 𝓖)
    (φ : G2 σ Y → ℂ) (hφ : Continuous φ) (hrat : ∀ p ∈ par2 σ Y, p ∈ rat2 σ Y → ∀ y, φ (p * y) = φ y)
    (hone : ∀ p t, IsPar p t → Matrix.GeneralLinearGroup.det t = 1 → ∀ y, φ (p * y) = φ y)
    (hmaj : ∀ C : Set (G2 σ Y), IsCompact C → ∃ u : GlobalTheory.Eis.Cosets (par2 σ Y) (rat2 σ Y) → ℝ, Summable u ∧
      ∀ g ∈ C, ∀ q, ‖GlobalTheory.Eis.term (par2 σ Y) (rat2 σ Y) φ g q‖ ≤ u q)
    {ε : ℤˣ} {w : G2 σ Y} (hw : inFrame b w = Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0) (x : G2 σ Y) :
    Integrable (fun β => φ (w * nb β * x)) lam ∧ ∀ T : nF σ Y b, IsND T →
      fc B.ψ b nb lam 𝓖 (GlobalTheory.Eis.cosetSum (par2 σ Y) (rat2 σ Y) φ) T x =
        ∫ β, φ (w * nb β * x) * B.ψ (-(Algebra.trace (AF F) (AE F E) (T.1.1 * β.1).trace)) ∂lam := by
  classical
  obtain ⟨hnb, hHaar, h𝓖, -⟩ := hc
  have := hHaar
  have : Countable (rat2 σ Y) := GlobalTheory.EisBL.DoubledGroupTopology.countable_rational_points_doubled σ Y
  have : Countable (GlobalTheory.Eis.Cosets (par2 σ Y) (rat2 σ Y)) := Quotient.countable
  obtain ⟨ε₀, hε₀⟩ := hb.1
  have hw_rat : w ∈ rat2 σ Y := by
    refine rat_of_inFrame (b := b) (M := Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) ?_
    rw [hw]
    ext (i | i) (j | j) <;> simp [incM, Matrix.one_apply] <;> split_ifs <;> simp
  have hLI : GlobalTheory.AutomorphicL2Unitary.LeftInv (par2 σ Y ⊓ rat2 σ Y) φ := fun γ hγ g => hrat γ hγ.1 hγ.2 g
  let nbR : nF σ Y b → rat2 σ Y := fun ν => ⟨nb ν.1, nb_rat hnb ν.2⟩
  have nbR_zero : nbR 0 = 1 := Subtype.ext (nb_zero hnb)
  have nbR_add : ∀ ν ν', nbR (ν + ν') = nbR ν * nbR ν' := fun ν ν' => Subtype.ext (nb_add hnb ν.1 ν'.1)
  let act : GlobalTheory.Eis.Cosets (par2 σ Y) (rat2 σ Y) → nF σ Y b → GlobalTheory.Eis.Cosets (par2 σ Y) (rat2 σ Y) :=
    fun q ν => GlobalTheory.AutomorphicL2Unitary.rmul _ (nbR ν) q
  have hact0 : ∀ q, act q 0 = q := fun q => by
    show GlobalTheory.AutomorphicL2Unitary.rmul _ (nbR 0) q = q
    rw [nbR_zero, GlobalTheory.AutomorphicL2Unitary.rmul_one]
  have hact : ∀ q ν ν', act (act q ν) ν' = act q (ν + ν') := fun q ν ν' => by
    show GlobalTheory.AutomorphicL2Unitary.rmul _ (nbR ν') (GlobalTheory.AutomorphicL2Unitary.rmul _ (nbR ν) q) = GlobalTheory.AutomorphicL2Unitary.rmul _ (nbR (ν + ν')) q
    rw [nbR_add, GlobalTheory.AutomorphicL2Unitary.rmul_mul]
  let A : GlobalTheory.Eis.Cosets (par2 σ Y) (rat2 σ Y) → nA σ Y b → ℂ := fun q β =>
    GlobalTheory.Eis.term (par2 σ Y) (rat2 σ Y) φ (nb β * x) q
  have hA : ∀ q, Continuous (A q) := fun q =>
    hφ.comp (continuous_const.mul ((continuous_nb hnb).mul continuous_const))
  have hAmk : ∀ (γ : rat2 σ Y) β, A (GlobalTheory.AutomorphicL2Unitary.mk _ γ) β = φ (γ.1 * (nb β * x)) := fun γ β =>
    GlobalTheory.Eis.term_mk hLI (nb β * x) γ
  have hAact : ∀ q ν β, A (act q ν) β = A q (β + (ν : nA σ Y b)) := fun q ν β => by
    have e : act q ν = GlobalTheory.AutomorphicL2Unitary.mk _ (q.out * nbR ν) := by
      show GlobalTheory.AutomorphicL2Unitary.rmul _ (nbR ν) q = _
      conv_lhs => rw [← Quotient.out_eq q]
      rfl
    rw [e, hAmk]
    show φ ((q.out : rat2 σ Y).1 * nb ν.1 * (nb β * x)) = φ ((q.out : rat2 σ Y).1 * (nb (β + ν.1) * x))
    rw [nb_add hnb, nb_comm hnb β]
    simp only [mul_assoc]
  obtain ⟨C, hC, hcov⟩ := _root_.PositivityTheory.SiegelWeilFormula.kunf.exists_cover_k B hB hb
  obtain ⟨u, hu, hAu'⟩ := hmaj ((fun β => nb β * x) '' C) (hC.image ((continuous_nb hnb).mul continuous_const))
  have hAu : ∀ q, ∀ β ∈ C, ‖A q β‖ ≤ u q := fun q β hβ => hAu' _ ⟨β, hβ, rfl⟩ q
  let q₀ : GlobalTheory.Eis.Cosets (par2 σ Y) (rat2 σ Y) := GlobalTheory.AutomorphicL2Unitary.mk _ ⟨w, hw_rat⟩
  have hq₀ : ∀ ν, act q₀ ν = GlobalTheory.AutomorphicL2Unitary.mk _ (⟨w, hw_rat⟩ * nbR ν) := fun ν => rfl
  have hinj : Function.Injective (act q₀) := fun ν ν' h => by
    rw [hq₀, hq₀] at h
    obtain ⟨γ, hγ⟩ := GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.1 h
    have hP : (w * nb ν'.1) * (w * nb ν.1)⁻¹ ∈ par2 σ Y := by
      have e : (w * nb ν'.1) = (γ : rat2 σ Y).1 * (w * nb ν.1) := (congrArg Subtype.val hγ).symm
      rw [e, mul_inv_cancel_right]
      exact Subgroup.mem_subgroupOf.1 γ.2
    exact (Subtype.ext (big_inj hb hw hnb hP)).symm
  have hAq₀ : ∀ β, A q₀ β = φ (w * nb β * x) := fun β => by
    rw [hAmk, mul_assoc]
  have hI := abs_integrable lam (nF σ Y b) 𝓖 h𝓖 act hact0 hact A hA hAact C hC hcov u hu hAu q₀ hinj
  refine ⟨hI.congr (Filter.Eventually.of_forall hAq₀), fun T hT => ?_⟩
  let χ₀ : nA σ Y b → ℂ := fun β => B.ψ (-(Algebra.trace (AF F) (AE F E) (T.1.1 * β.1).trace))
  have htr : Continuous fun M : Matrix (Fin n) (Fin n) (AE F E) => Algebra.trace (AF F) (AE F E) M.trace :=
    (IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF F) (AE F E))).comp continuous_id.matrix_trace
  have hχc : Continuous χ₀ :=
    hB.std.1.comp ((htr.comp (continuous_const.matrix_mul continuous_subtype_val)).neg)
  have hχadd : ∀ β β', χ₀ (β + β') = χ₀ β * χ₀ β' := fun β β' => by
    simp only [χ₀, AddSubgroup.coe_add, Matrix.mul_add, Matrix.trace_add, map_add, neg_add]
    exact AddChar.map_add_eq_mul _ _ _
  have hχΛ : ∀ ν : nF σ Y b, χ₀ (ν : nA σ Y b) = 1 := fun ν => by
    simp only [χ₀, AddChar.map_neg_eq_inv, psi_rat hB.std T ν, inv_one]
  have hsmall : ∀ q, (∀ ν, act q₀ ν ≠ q) →
      ∃ β₀, χ₀ β₀ ≠ 1 ∧ ∀ ν β, A (act q ν) (β + β₀) = A (act q ν) β := fun q hq => by
    rcases _root_.PositivityTheory.SiegelWeilFormula.kunf.cells_k B hB hb hw hnb T hT (q.out : rat2 σ Y).1 (q.out : rat2 σ Y).2 with
      ⟨p, hpP, hpΓ, ν, hνF, hγ⟩ | ⟨β₀, hψ, t, hpar, hdet⟩
    · exfalso
      refine hq ⟨ν, hνF⟩ ?_
      rw [hq₀, ← Quotient.out_eq q]
      refine GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.2 ⟨⟨⟨p, hpΓ⟩, Subgroup.mem_subgroupOf.2 hpP⟩, Subtype.ext ?_⟩
      exact hγ.symm
    · refine ⟨β₀, hψ, fun ν β => ?_⟩
      rw [hAact, hAact]
      show φ ((q.out : rat2 σ Y).1 * (nb (β + β₀ + ν.1) * x)) = φ ((q.out : rat2 σ Y).1 * (nb (β + ν.1) * x))
      set γ := (q.out : rat2 σ Y).1
      have e : γ * (nb (β + β₀ + ν.1) * x) = (γ * nb β₀ * γ⁻¹) * (γ * (nb (β + ν.1) * x)) := by
        rw [show β + β₀ + ν.1 = β₀ + (β + ν.1) by abel, nb_add hnb]
        group
      rw [e, hone _ t hpar hdet]
  obtain ⟨-, -, heq⟩ := abs_unfold lam (nF σ Y b) 𝓖 h𝓖 act hact0 hact A hA hAact χ₀ hχc hχadd hχΛ C hC hcov u hu hAu
    q₀ hinj hsmall
  show ∫ β in 𝓖, GlobalTheory.Eis.cosetSum (par2 σ Y) (rat2 σ Y) φ (nb β * x) * χ₀ β ∂lam = ∫ β, φ (w * nb β * x) * χ₀ β ∂lam
  have e2 : ∫ β, φ (w * nb β * x) * χ₀ β ∂lam = ∫ β, A q₀ β * χ₀ β ∂lam :=
    integral_congr_ae (Filter.Eventually.of_forall fun β => by simp only [hAq₀])
  rw [e2]
  exact heq
end PositivityTheory.SiegelWeilFormula.kunf
end
end
