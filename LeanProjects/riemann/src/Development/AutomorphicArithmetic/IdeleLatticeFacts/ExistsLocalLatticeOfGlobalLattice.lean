import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutEtaB
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepBI
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PLocalLatticeIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIdeleCharTrivialCongruentOneModulo

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA
open UpperTheory.TP.W

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem ev_pair (P : HeightOneSpectrum (𝓞 E)) (α : Af F) :
    ev F E P (algebraMap (AF F) (AEF F E) (pairA F 0 α)) =
      GlobalTheory.LFun.complMap rfl (evalV F (P.under (𝓞 F)) α) := by
  rw [ev_alg]
  rfl

private theorem ev_finIdem (P : HeightOneSpectrum (𝓞 E)) : ev F E P (finIdem F E) = 1 := by
  rw [finIdem, ev_pair, map_one, map_one]

private theorem finPart_lift (y : Af F ⊗[F] E) : finPartF F E (PositivityTheory.ThKW.LatB.liftF F E y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a t => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

private theorem int_mem (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E) :
    algebraMap E (P.adicCompletion E) (r : E) ∈ P.adicCompletionIntegers E := by
  exact HeightOneSpectrum.coe_mem_adicCompletionIntegers P r

private theorem exists_lift (P : HeightOneSpectrum (𝓞 E)) (c : P.adicCompletionIntegers E) :
    ∃ a : AEF F E, finPartF F E a ∈ PositivityTheory.ThKW.LatB.hatO (F := F) E ∧ ev F E P a = c := by
  classical
  have hx : ∀ᶠ Q in Filter.cofinite, Pi.single (M := fun Q : HeightOneSpectrum (𝓞 E) => Q.adicCompletion E) P (c : P.adicCompletion E) Q ∈ (Q.adicCompletionIntegers E : Set (Q.adicCompletion E)) := by
    refine Filter.Eventually.of_forall fun Q => ?_
    by_cases h : Q = P
    · subst h
      rw [Pi.single_eq_same]
      exact c.2
    · rw [Pi.single_eq_of_ne h]
      exact zero_mem _
  let x : FiniteAdeleRing (𝓞 E) E := ⟨_, hx⟩
  have hxQ : ∀ Q, x Q ∈ Q.adicCompletionIntegers E := by
    intro Q
    by_cases h : Q = P
    · subst h
      show Pi.single (M := fun Q : HeightOneSpectrum (𝓞 E) => Q.adicCompletion E) Q (c : Q.adicCompletion E) Q ∈ _
      rw [Pi.single_eq_same]
      exact c.2
    · show Pi.single (M := fun Q : HeightOneSpectrum (𝓞 E) => Q.adicCompletion E) P (c : P.adicCompletion E) Q ∈ _
      rw [Pi.single_eq_of_ne h]
      exact zero_mem _
  refine ⟨PositivityTheory.ThKW.LatB.liftF F E ((finAdEquiv F E).symm x), ?_, ?_⟩
  · rw [finPart_lift]
    show _ ∈ GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E))
    rw [← GlobalTheory.HeckeSplitGen.integralFiniteAdelesTensor_eq_adelicCompletion_integers]
    refine (mem_int_iff _).2 fun Q => ?_
    rw [RingEquiv.apply_symm_apply]
    exact hxQ Q
  · show evalV E P (finAdEquiv F E (finPartF F E _)) = c
    rw [finPart_lift, RingEquiv.apply_symm_apply]
    show Pi.single (M := fun Q : HeightOneSpectrum (𝓞 E) => Q.adicCompletion E) P (c : P.adicCompletion E) P = c
    rw [Pi.single_eq_same]

end SlopeTestRemainingChoices

section Aux2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {nS nT : ℕ}

private theorem map_smul_int (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E) (M : Matrix (Fin nT) (Fin nS) E) :
    (r • M).map (algebraMap E (P.adicCompletion E)) =
      (⟨algebraMap E (P.adicCompletion E) (r : E), int_mem P r⟩ : P.adicCompletionIntegers E) •
        M.map (algebraMap E (P.adicCompletion E)) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply]
  rw [Algebra.smul_def, map_mul]
  rfl

private theorem ev_map_smul (P : HeightOneSpectrum (𝓞 E)) (a : AEF F E) (z : WOF F E nS nT) :
    (a • z).map (ev F E P) = ev F E P a • z.map (ev F E P) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

private theorem ev_ratWF (P : HeightOneSpectrum (𝓞 E)) (γ : Matrix (Fin nT) (Fin nS) E) :
    (ratWF (F := F) γ).map (ev F E P) = γ.map (algebraMap E (P.adicCompletion E)) := by
  refine Matrix.ext fun i j => ?_
  simp only [ratWF, Matrix.map_apply]
  exact ev_inc (F := F) P (γ i j)

private theorem finRat_mem (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) {M : Matrix (Fin nT) (Fin nS) E}
    (hM : M ∈ Λ) : finRatF F M ∈ latF F E nS nT Λ := by
  refine AddSubgroup.subset_closure ⟨1, ?_, M, hM, rfl⟩
  intro v
  rw [map_one]
  exact one_mem _

private theorem ev_finRat (P : HeightOneSpectrum (𝓞 E)) (M : Matrix (Fin nT) (Fin nS) E) :
    ((finRatF F M : XFF F E nS nT) : WOF F E nS nT).map (ev F E P) = M.map (algebraMap E (P.adicCompletion E)) := by
  show (finIdem F E • ratWF (F := F) M).map (ev F E P) = _
  rw [ev_map_smul, ev_finIdem, one_smul, ev_ratWF]

private theorem ev_mem_span (P : HeightOneSpectrum (𝓞 E)) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E))
    {z : WOF F E nS nT} (hz : z ∈ latOF F E nS nT Λ) :
    z.map (ev F E P) ∈ Submodule.span (P.adicCompletionIntegers E)
      {X | ∃ M ∈ Λ, X = M.map (algebraMap E (P.adicCompletion E))} := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, γ, hγ, rfl⟩ := hz
    rw [ev_map_smul, ev_pair, ev_ratWF]
    have hc : GlobalTheory.LFun.complMap rfl (evalV F (P.under (𝓞 F)) α) ∈ P.adicCompletionIntegers E :=
      GlobalTheory.LFun.complMap_mem rfl (hα _)
    exact Submodule.smul_mem _ (⟨_, hc⟩ : P.adicCompletionIntegers E) (Submodule.subset_span ⟨γ, hγ, rfl⟩)
  | zero =>
    rw [Matrix.map_zero _ (map_zero _)]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [Matrix.map_add _ (map_add _)]
    exact add_mem hx hy
  | neg x _ hx =>
    rw [Matrix.map_neg _ (map_neg _)]
    exact neg_mem hx

end Aux2

theorem UpperTheory.exists_local_lattice_of_global_lattice :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {nS nT : ℕ}
        (P : HeightOneSpectrum (𝓞 E)) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)), GoodLat Λ →
        ∃ L : Submodule (P.adicCompletionIntegers E) (Matrix (Fin nT) (Fin nS) (P.adicCompletion E)),
          L.FG ∧ Submodule.span (P.adicCompletion E) (L : Set (Matrix (Fin nT) (Fin nS) (P.adicCompletion E))) = ⊤ ∧
          ∀ v, v ∈ L ↔ ∃ x ∈ latF F E nS nT Λ, (x : WOF F E nS nT).map (ev F E P) = v := by
  intro F E _ _ _ _ _ nS nT P Λ hΛ
  classical
  refine ⟨Submodule.span (P.adicCompletionIntegers E)
    {X | ∃ M ∈ Λ, X = M.map (algebraMap E (P.adicCompletion E))}, ?_, ?_, ?_⟩
  · obtain ⟨G, hG⟩ := hΛ.fg
    refine ⟨G.image (fun M => M.map (algebraMap E (P.adicCompletion E))), ?_⟩
    rw [Finset.coe_image]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨M, hM, rfl⟩
      have hM' : M ∈ Λ := by
        rw [← hG]
        exact Submodule.subset_span hM
      exact Submodule.subset_span ⟨M, hM', rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨M, hM, rfl⟩
      rw [← hG] at hM
      induction hM using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
      | zero =>
        rw [Matrix.map_zero _ (map_zero _)]
        exact zero_mem _
      | add x y _ _ hx hy =>
        rw [Matrix.map_add _ (map_add _)]
        exact add_mem hx hy
      | smul r x _ hx =>
        rw [map_smul_int P r x]
        exact Submodule.smul_mem _ _ hx
  · rw [eq_top_iff]
    rintro X -
    rw [Matrix.matrix_eq_sum_single X]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨N, hN, hNM⟩ := hΛ.den (Matrix.single i j (1 : E))
    have hN0 : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    have key : Matrix.single i j (X i j) =
        (X i j * algebraMap E (P.adicCompletion E) (N : E)⁻¹) •
          (N • Matrix.single i j (1 : E)).map (algebraMap E (P.adicCompletion E)) := by
      ext a b
      simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.single_apply, smul_eq_mul]
      split_ifs with h
      · rw [nsmul_eq_mul, mul_one, mul_assoc, ← map_mul, inv_mul_cancel₀ hN0, map_one, mul_one]
      · rw [smul_zero, map_zero, mul_zero]
    rw [key]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.subset_span ⟨_, hNM, rfl⟩))
  · intro v
    constructor
    · intro hv
      induction hv using Submodule.span_induction with
      | mem X hX =>
        obtain ⟨M, hM, rfl⟩ := hX
        exact ⟨finRatF F M, finRat_mem Λ hM, ev_finRat P M⟩
      | zero =>
        refine ⟨0, zero_mem _, ?_⟩
        show (0 : WOF F E nS nT).map (ev F E P) = 0
        exact Matrix.map_zero _ (map_zero _)
      | add X Y _ _ hX hY =>
        obtain ⟨x, hx, rfl⟩ := hX
        obtain ⟨y, hy, rfl⟩ := hY
        refine ⟨x + y, add_mem hx hy, ?_⟩
        show ((x : WOF F E nS nT) + (y : WOF F E nS nT)).map (ev F E P) = _
        exact Matrix.map_add _ (map_add _) _ _
      | smul c X _ hX =>
        obtain ⟨x, hx, rfl⟩ := hX
        obtain ⟨a, ha, hac⟩ := exists_lift (F := F) P c
        refine ⟨a • x, PositivityTheory.ThKW.LatB.int_smul_mem ha hx, ?_⟩
        rw [GlobalTheory.FinLatF.XFF.coe_asmul, ev_map_smul, hac]
        rfl
    · rintro ⟨x, hx, rfl⟩
      exact ev_mem_span P Λ hx
