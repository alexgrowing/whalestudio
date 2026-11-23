import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSkewModelGood
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WeilLieAlgebraScalarAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSkewModelGoodStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift
namespace GlobalTheory.KStableSums
open scoped Classical in
theorem kStable_subspace_sums : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) {r s r' s' : ℕ},
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M.IsWeil B.ψ χX χW om →
    ∀ {Pi : Type} [AddCommGroup Pi] [Module ℂ Pi] (Q : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] Pi) (N : Submodule ℂ Pi),
    (∀ (w : InfinitePlace F) (Z : Matrix (Fin d) (Fin d) ℂ) (γ : Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J),
      γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ W →
      (∀ t : ℝ, (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t))).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (B.emb w)) =
        NormedSpace.exp (t • Z)) →
      (∀ (t : ℝ) (w' : InfinitePlace F), w' ≠ w →
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t))).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (B.emb w')) = 1) →
      ∀ (m : ℕ) (f f₁ : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
        (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      (∀ i, (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = M.vac v) →
      (∀ i, f i ∈ M.Pol B.ψ B.emb ∧ f₁ i ∈ M.Pol B.ψ B.emb) →
      (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (f i) (f₁ i)) →
      Q (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) ∈ N → Q (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)) ∈ N) →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W B.emb, ∀ Ψ ∈ GlobalTheory.SquareAgree.algD M B.ψ B.emb,
      om (1, k) Ψ ∈ GlobalTheory.SquareAgree.algD M B.ψ B.emb ∧ (Q Ψ ∈ N → Q (om (1, k) Ψ) ∈ N) := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hb hX hW hM hw Pv _ _ Q N hlie k hk Ψ hΨ
  have hAL : ActsLaws := GlobalTheory.RealLift.actsLaws
  have hfr : FrameEx := GlobalTheory.T.cartanEigen_orthonormalFrame_exists
  have hder : DerEx := GlobalTheory.T.archHeisenbergDerivatives_exist
  have hvl : VacLine := GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hder
  have hfe : FockEx := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives hder
  have hls : LieScalar := _root_.GlobalTheory.T.weil_lie_algebra_scalar_action hP hder hvl
  have hpr : PolRange := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws hAL hder hvl
  choose A hA hAθ using fun w => hfr _ _ _ _ _ (hX.sig w) (hX.cartan w)
  choose C hC hCθ using fun w => hfr _ _ _ _ _ (hW.sig w) (hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [GlobalTheory.PolCompact.incM_map_piInf', one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [GlobalTheory.PolCompact.incM_map_piInf']; exact hC w
  have fr : Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := hpr F E σ _ _ _ _ _ _ X W M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (incM F W.J) M.co χX χW om := hw
  obtain ⟨c, hact⟩ := hls F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C Φ _ hb.cm hb.std fr hΦ hwp.1.1
  have hadm := fun g => (hwp.isUSplitting).adm g
  obtain ⟨γ, hγ, Yg, hgen, hYu, hKC, hγ1⟩ :=
    exists_line_upq σ r' s' B.emb (incM F W.J) Complex.I C W.θ hb.cm hC1 hCθ k hk.1 hk.2
  have hloc := GlobalTheory.RealLift.locFin_sumPl _ _ _
    (fun w => GlobalTheory.PolCompact.locFin_second r s r' s' (Yg w) (hKC w) (c w * (Yg w).trace))
  obtain ⟨U, hU, hSA⟩ := GlobalTheory.T.weakExponential_action_on_fockVectors F (Fin n × Fin d) _ Φ _ ((om.comp (MonoidHom.inr _ _)).comp γ) hloc
    (fun t l hl => hadm _ l hl) (fun T => hact γ hγ Yg hgen T)
  obtain ⟨m, f, φ, hf, hφ, rfl⟩ := exists_sum_pure M B.ψ B.emb hΨ
  have hf' : ∀ i, ∃ y, Φ y = f i := fun i => LinearMap.mem_range.1 (by rw [hr]; exact hf i)
  choose T hT using hf'
  obtain rfl : f = fun i => Φ (T i) := funext fun i => (hT i).symm
  let G : (Fin m → Tens F r s r' s') →ₗ[ℂ] ((Fin n × Fin d → AF F) → ℂ) :=
    ∑ i, (pureL (φ i)) ∘ₗ Φ ∘ₗ LinearMap.proj i
  have hG : ∀ y, G y = ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Φ (y i)) (φ i) := fun y => by
    simp only [G, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]; rfl
  have hplace : ∀ (w : InfinitePlace F) (y : Fin m → Tens F r s r' s'), Q (G y) ∈ N →
      Q (G (piEnd m (atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol r s r' s') w
        (fockAct2 r s r' s' (Yg w) + (c w * (Yg w).trace) • 1)) y)) ∈ N := by
    intro w y hy
    rw [hG] at hy ⊢
    obtain ⟨A', hCA, hAC⟩ := GlobalTheory.RealLift.KLineProof.frame_inv (hC1 w)
    have hsu : ∀ w', (Pi.single w (Yg w) : InfinitePlace F → Matrix (Ix r' s') (Ix r' s') ℂ) w' ∈ upq r' s' := by
      intro w'
      by_cases h : w' = w
      · subst h; simpa using hYu w'
      · rw [Pi.single_eq_of_ne h]
        show (0 : Matrix (Ix r' s') (Ix r' s') ℂ)ᴴ * Jm r' s' + Jm r' s' * 0 = 0
        simp
    obtain ⟨γw, hγw, hgw⟩ := GlobalTheory.T.unitaryLieElements_generate_oneParamLines F E σ (Fin d) r' s' B.emb (incM F W.J) Complex.I C hb.cm hC1 _ hsu
    refine hlie w (C w * Yg w * A') γw hγw ?_ ?_ m (fun i => Φ (y i)) _ φ hφ
      (fun i => ⟨by rw [← hr]; exact LinearMap.mem_range_self Φ _, by rw [← hr]; exact LinearMap.mem_range_self Φ _⟩)
      ?_ hy
    · intro t
      have h1 := hgw t w
      simp only [Pi.single_eq_same] at h1
      calc (mat (γw (Multiplicative.ofAdd t))).map (piInf (B.emb w))
          = ((γw (Multiplicative.ofAdd t)).1 : Matrix (Fin d) (Fin d) (AE F E)).map (piInf (B.emb w)) * C w * A' := by
            rw [Matrix.mul_assoc, hCA, Matrix.mul_one]; rfl
        _ = C w * NormedSpace.exp (t • Yg w) * A' := by rw [h1]
        _ = NormedSpace.exp (t • (C w * Yg w * A')) := by
            rw [show t • (C w * Yg w * A') = C w * (t • Yg w) * A' by rw [Matrix.mul_smul, Matrix.smul_mul],
              exp_conj_rect _ _ hCA hAC]
    · intro t w' hw'
      have h1 := hgw t w'
      rw [Pi.single_eq_of_ne hw', smul_zero, NormedSpace.exp_zero, Matrix.mul_one] at h1
      obtain ⟨A'', hCA', -⟩ := GlobalTheory.RealLift.KLineProof.frame_inv (hC1 w')
      calc (mat (γw (Multiplicative.ofAdd t))).map (piInf (B.emb w'))
          = ((γw (Multiplicative.ofAdd t)).1 : Matrix (Fin d) (Fin d) (AE F E)).map (piInf (B.emb w')) * C w' * A'' := by
            rw [Matrix.mul_assoc, hCA', Matrix.mul_one]; rfl
        _ = 1 := by rw [h1, hCA']
    · intro i
      have hsd := hact γw hγw _ hgw (y i)
      rw [sumPl_single] at hsd
      exact (hAL F (Fin n × Fin d) _ _ (Φ (y i))).1 _ (fun t => map_zero _) hsd
  let N' : Submodule ℂ (Fin m → Tens F r s r' s') := N.comap (Q ∘ₗ G)
  have hstab : ∀ y ∈ N', piEnd m (sumPl fun w => fockAct2 r s r' s' (Yg w) + (c w * (Yg w).trace) • 1) y ∈ N' := by
    intro y hy
    have e : piEnd m (sumPl fun w => fockAct2 r s r' s' (Yg w) + (c w * (Yg w).trace) • 1) y =
        ∑ w, piEnd m (atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol r s r' s') w
          (fockAct2 r s r' s' (Yg w) + (c w * (Yg w).trace) • 1)) y := by
      funext i
      simp only [piEnd_apply, sumPl, LinearMap.sum_apply, Finset.sum_apply]
    rw [e]
    exact N'.sum_mem fun w _ => hplace w y hy
  have hk1 : ∀ i, om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Φ (T i)) (φ i)) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Φ (U (T i))) (φ i) := by
    intro i
    have h1 := hSA (T i)
    rw [MonoidHom.comp_apply, hγ1] at h1
    have hg := GlobalTheory.AdelicCoordSB.finprod_mem_SB F (Fin n × Fin d) (φ i) (hφ i).1
      (((hφ i).2.and hM.std).mono fun v hv => hv.1.trans hv.2)
    exact h1 _ hg
  have hsum : om (1, k) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Φ (T i)) (φ i)) =
      ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Φ (U (T i))) (φ i) := by
    rw [map_sum]; exact Finset.sum_congr rfl fun i _ => hk1 i
  refine ⟨?_, fun hQ => ?_⟩
  · rw [hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.subset_span
      ⟨Φ (U (T i)), φ i, by rw [← hr]; exact LinearMap.mem_range_self Φ _, (hφ i).1, (hφ i).2, rfl⟩
  · have h0 : T ∈ N' := by
      show Q (G T) ∈ N
      rw [hG]; exact hQ
    have h2 := GlobalTheory.KStableLie.mem_of_isExp (isExp_piEnd hU m) N' hstab h0
    have e := hG (piEnd m U T)
    simp only [piEnd_apply] at e
    rw [hsum, ← e]
    exact h2
end GlobalTheory.KStableSums
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algD_and_preimage_stable_under_KInf : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) {r s r' s' : ℕ},
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M.IsWeil B.ψ χX χW om →
    ∀ {Pi : Type} [AddCommGroup Pi] [Module ℂ Pi] (Q : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] Pi) (N : Submodule ℂ Pi),
    (∀ (w : InfinitePlace F) (Z : Matrix (Fin d) (Fin d) ℂ) (γ : Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J),
      γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ W →
      (∀ t : ℝ, (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t))).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (B.emb w)) =
        NormedSpace.exp (t • Z)) →
      (∀ (t : ℝ) (w' : InfinitePlace F), w' ≠ w →
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t))).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (B.emb w')) = 1) →
      ∀ (m : ℕ) (f f₁ : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
        (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      (∀ i, (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = M.vac v) →
      (∀ i, f i ∈ M.Pol B.ψ B.emb ∧ f₁ i ∈ M.Pol B.ψ B.emb) →
      (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (f i) (f₁ i)) →
      Q (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) ∈ N → Q (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)) ∈ N) →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W B.emb, ∀ Ψ ∈ GlobalTheory.SquareAgree.algD M B.ψ B.emb,
      om (1, k) Ψ ∈ GlobalTheory.SquareAgree.algD M B.ψ B.emb ∧ (Q Ψ ∈ N → Q (om (1, k) Ψ) ∈ N) := by
  first | exact @_root_.GlobalTheory.KStableSums.kStable_subspace_sums | exact _root_.GlobalTheory.KStableSums.kStable_subspace_sums | (intros; apply _root_.GlobalTheory.KStableSums.kStable_subspace_sums <;> assumption)
end
