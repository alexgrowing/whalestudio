import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoBarZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalAddCharUnramifiedOfSplitsCompletelyAbovePla
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StoneVonNeumannSchwartzBruhatAnyCharacterStatement
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFourSwap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairEqTrace

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny
open GlobalTheory.ThK GlobalTheory.KSplit

noncomputable section

namespace GlobalTheory.LinWSplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem pairM_comm {K : Type} [CommRing K] {n d : ℕ} (P Q : Matrix (Fin n) (Fin d) K) :
    GlobalTheory.FlipMatch.pairM P Q = GlobalTheory.FlipMatch.pairM Q P := by
  simp only [GlobalTheory.FlipMatch.pairM, mul_comm]

theorem pairM_chart {K : Type} [Field K] {n d : ℕ} (A : Matrix (Fin n) (Fin n) K) (B : Matrix (Fin d) (Fin d) K)
    (b : GL (Fin n) K) (c : GL (Fin d) K) (P Q : Matrix (Fin n) (Fin d) K) :
    GlobalTheory.FlipMatch.pairM ((b⁻¹).1 * P * (c⁻¹).1ᵀ) (-(b.1ᵀ * A * Q * Bᵀ * c.1)) =
      -∑ i : Fin n, ∑ j : Fin d, ∑ k : Fin n, ∑ l : Fin d, P i j * A i k * B j l * Q k l := by
  first
  | exact @_root_.GlobalTheory.PairingTraceExpansion.main
  | exact _root_.GlobalTheory.PairingTraceExpansion.main
  | (apply _root_.GlobalTheory.PairingTraceExpansion.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PairingTraceExpansion.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PairingTraceExpansion.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PairingTraceExpansion.main ..)

theorem sum_four_swap_pairs_alt {R α β : Type} [AddCommMonoid R] [Fintype α] [Fintype β] (f : α → β → α → β → R) :
    ∑ a, ∑ b, ∑ c, ∑ e, f a b c e = ∑ c, ∑ e, ∑ a, ∑ b, f a b c e := by
  first
  | exact @_root_.GlobalTheory.FourTermSumSwap.sum_four_swap
  | exact _root_.GlobalTheory.FourTermSumSwap.sum_four_swap
  | (apply _root_.GlobalTheory.FourTermSumSwap.sum_four_swap <;> assumption)
  | (intros; apply _root_.GlobalTheory.FourTermSumSwap.sum_four_swap <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FourTermSumSwap.sum_four_swap <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FourTermSumSwap.sum_four_swap ..)

theorem piW_cA {σ : E →ₐ[F] E} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (τ : E →ₐ[F] Fv F v) (w : AE F E) :
    piW τ (cA σ w) = piW (τ.comp σ) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem piW_incl {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (τ : E →ₐ[F] Fv F v) (e : E) :
    piW τ (inclR (F := F) (AF F) e) = τ e := by
  change GlobalTheory.AdelicU.evFin F v 1 * τ e = τ e
  simp

theorem evFin_symp {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {n d : ℕ} (X : Spc F E n) (Y : Spc F E d)
    (hX : ∀ r s, σ (X.J s r) = X.J r s) (hY : ∀ r s, σ (Y.J s r) = -Y.J r s) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (t : E →ₐ[F] Fv F v)
    (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)) (x u : Matrix (Fin n) (Fin d) (AE F E))
    (hx : At (evFin F v) x) :
    evFin F v (GlobalTheory.WeilM.symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F Y.J) x u) =
      GlobalTheory.FlipMatch.pairM (GlobalTheory.FlipMatch.coX t b c x) (GlobalTheory.FlipMatch.coY σ X Y t b c u) -
        GlobalTheory.FlipMatch.pairM (GlobalTheory.FlipMatch.coY σ X Y t b c x) (GlobalTheory.FlipMatch.coX t b c u) := by
  have hss := GlobalTheory.AdelicU.comp_conj_conj hcm t
  have hz : At (evFin F v) ((-1 : AE F E) * GlobalTheory.WeilM.hTens (cA σ) (incM F X.J) (incM F Y.J) x u) := by
    intro r hr
    have h : ∀ i j, r • x i j = 0 := fun i j => by
      have := congrFun (congrFun (hx r hr) i) j
      simpa using this
    rw [← mul_smul_comm]
    unfold GlobalTheory.WeilM.hTens
    simp only [Finset.smul_sum, ← smul_mul_assoc, h, zero_mul, Finset.sum_const_zero, mul_zero]
  unfold GlobalTheory.WeilM.symp
  rw [GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm v t _ hz, GlobalTheory.LatVac.evFin_liftV]
  rw [pairM_comm (GlobalTheory.FlipMatch.coY σ X Y t b c x), GlobalTheory.FlipMatch.coX, GlobalTheory.FlipMatch.coX, GlobalTheory.FlipMatch.coY,
    GlobalTheory.FlipMatch.coY, pairM_chart, pairM_chart]
  simp only [map_mul, map_neg, map_one, neg_one_mul, GlobalTheory.WeilM.hTens, map_sum, piW_cA, piW_incl,
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.map_apply, hss, AlgHom.comp_apply, hX, hY]
  rw [sub_eq_add_neg]
  congr 1
  rw [neg_neg]
  refine Eq.trans ?_ (sum_four_swap_pairs_alt _).symm
  simp only [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem locCo_form {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : Darboux B κ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (x u : W) :
    (GlobalTheory.LatVac.locCo co v x).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v u).2 -
      (GlobalTheory.LatVac.locCo co v u).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v x).2 = evFin F v (B x u) := by
  rw [co.form]
  simp [GlobalTheory.LatVac.locCo, dotProduct, map_sum, map_mul, map_sub]

theorem locCo_surj {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : Darboux B κ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (w : (κ → Fv F v) × (κ → Fv F v)) : ∃ u : W, At (evFin F v) u ∧ GlobalTheory.LatVac.locCo co v u = w := by
  refine ⟨co.e.symm (fun k => GlobalTheory.LatVac.liftV v (w.1 k), fun k => GlobalTheory.LatVac.liftV v (w.2 k)), ?_, ?_⟩
  · intro a ha
    rw [← LinearEquiv.map_smul, ← co.e.symm.map_zero]
    congr 1
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · exact GlobalTheory.LatVac.at_liftV v _ a ha
    · exact GlobalTheory.LatVac.at_liftV v _ a ha
  · refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
      simp [GlobalTheory.LatVac.locCo, GlobalTheory.LatVac.evFin_liftV]

theorem at_symp (σ : E →ₐ[F] E) {n d : ℕ} (JA : Matrix (Fin n) (Fin n) (AE F E)) (JB : Matrix (Fin d) (Fin d) (AE F E))
    {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (x u : Matrix (Fin n) (Fin d) (AE F E)) (hx : At (evFin F v) x) :
    At (evFin F v) (symp (R := AF F) (cA σ) (-1) JA JB x u) := by
  intro a ha
  have h := GlobalTheory.LatVac.symp_smul_smul σ JA JB (-1) a 1 x u
  rw [hx a ha, one_smul, mul_one, GlobalTheory.VacIndic.symp_zero_left] at h
  rw [smul_eq_mul]
  exact h.symm

theorem locCo_eq_zero {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {n d : ℕ} (X : Spc F E n) (Y : Spc F E d)
    (hX : ∀ r s, σ (X.J s r) = X.J r s) (hY : ∀ r s, σ (Y.J s r) = -Y.J r s) (M : Model σ X Y) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F}
    (t : E →ₐ[F] Fv F v) (z : Matrix (Fin n) (Fin d) (AE F E)) (hz : At (evFin F v) z)
    (h0 : z.map (piW t) = 0) (h1 : z.map (piW (t.comp σ)) = 0) : GlobalTheory.LatVac.locCo M.co v z = 0 := by
  have hf : ∀ w : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v),
      (GlobalTheory.LatVac.locCo M.co v z).1 ⬝ᵥ w.2 - w.1 ⬝ᵥ (GlobalTheory.LatVac.locCo M.co v z).2 = 0 := by
    intro w
    obtain ⟨u, -, rfl⟩ := locCo_surj M.co v w
    rw [locCo_form, evFin_symp hcm X Y hX hY t 1 1 z u hz]
    simp [GlobalTheory.FlipMatch.coX, GlobalTheory.FlipMatch.coY, h0, h1, GlobalTheory.FlipMatch.pairM]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · have := hf (0, Pi.single i 1)
    simpa using this
  · have := hf (Pi.single i 1, 0)
    simpa using this

theorem locCo_eq_of {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {n d : ℕ} (X : Spc F E n) (Y : Spc F E d)
    (hX : ∀ r s, σ (X.J s r) = X.J r s) (hY : ∀ r s, σ (Y.J s r) = -Y.J r s) (M : Model σ X Y) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F}
    (t : E →ₐ[F] Fv F v) (u u' : Matrix (Fin n) (Fin d) (AE F E)) (hu : At (evFin F v) u) (hu' : At (evFin F v) u')
    (h0 : u.map (piW t) = u'.map (piW t)) (h1 : u.map (piW (t.comp σ)) = u'.map (piW (t.comp σ))) :
    GlobalTheory.LatVac.locCo M.co v u = GlobalTheory.LatVac.locCo M.co v u' := by
  rw [← sub_eq_zero, ← map_sub]
  apply locCo_eq_zero hcm X Y hX hY M t
  · intro r hr
    rw [smul_sub, hu r hr, hu' r hr, sub_zero]
  · rw [Matrix.map_sub _ (map_sub _), h0, sub_self]
  · rw [Matrix.map_sub _ (map_sub _), h1, sub_self]

end GlobalTheory.LinWSplit

namespace GlobalTheory.LinWSplit

theorem exists_isLinW_at : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∃ ι, M.IsLinW B.ψ t b c ι := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v t b c
  have hcm : IsCMExt F E σ := hP.base.cm
  have hstd := hP.base.std
  have hX := hP.herm.herm
  have hY := hP.skew.skew
  obtain ⟨w0⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdX : X.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hP.herm.sig w0)
    have e : (X.J.map (B.emb w0).1).det = (B.emb w0).1 X.J.det := (RingHom.map_det _ _).symm
    rw [e, h0, map_zero]
  have hdW : W.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hP.skew.sig w0)
    have e : (W.J.map (B.emb w0).1).det = (B.emb w0).1 W.J.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_smul, e, h0, map_zero, mul_zero]
  have hA : IsUnit (X.J.map t).det := by
    rw [show (X.J.map t).det = (t : E →+* Fv F v) X.J.det from (RingHom.map_det _ _).symm]
    exact isUnit_iff_ne_zero.2 fun h => hdX ((t : E →+* Fv F v).injective (by rw [map_zero]; exact h))
  have hB : IsUnit (W.J.map t)ᵀ.det := by
    rw [Matrix.det_transpose, show (W.J.map t).det = (t : E →+* Fv F v) W.J.det from (RingHom.map_det _ _).symm]
    exact isUnit_iff_ne_zero.2 fun h => hdW ((t : E →+* Fv F v).injective (by rw [map_zero]; exact h))
  choose U hUat hU0 hU1 using fun (P₀ P₁ : Matrix (Fin n) (Fin d) (Fv F v)) => GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hcm v t P₀ P₁
  have hat_add : ∀ x y : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) x → At (evFin F v) y →
      At (evFin F v) (x + y) := fun x y hx hy r hr => by rw [smul_add, hx r hr, hy r hr, add_zero]
  have heq := fun (u u' : Matrix (Fin n) (Fin d) (AE F E)) => locCo_eq_of hcm X W hX hY M t u u'

  let P0 : Matrix (Fin n) (Fin d) (Fv F v) → Matrix (Fin n) (Fin d) (Fv F v) := fun Y => b.1 * Y * c.1ᵀ
  let Q : Matrix (Fin n) (Fin d) (Fv F v) → Matrix (Fin n) (Fin d) (Fv F v) :=
    fun z => -((X.J.map t)⁻¹ * (b⁻¹).1ᵀ * z * (c⁻¹).1 * ((W.J.map t)ᵀ)⁻¹)
  have hP0 : ∀ P, P0 ((b⁻¹).1 * P * (c⁻¹).1ᵀ) = P := by
    intro P
    simp only [P0, ← Matrix.mul_assoc]
    rw [show b.1 * (b⁻¹).1 = 1 by simp, Matrix.one_mul, Matrix.mul_assoc,
      show (c⁻¹).1ᵀ * c.1ᵀ = 1 by rw [← Matrix.transpose_mul]; simp, Matrix.mul_one]
  have hQ : ∀ P, Q (-(b.1ᵀ * X.J.map t * P * (W.J.map t)ᵀ * c.1)) = P := by
    intro P
    simp only [Q, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((b⁻¹).1ᵀ), show (b⁻¹).1ᵀ * b.1ᵀ = 1 by rw [← Matrix.transpose_mul]; simp,
      Matrix.one_mul, ← Matrix.mul_assoc (c.1), show c.1 * (c⁻¹).1 = 1 by simp, Matrix.one_mul,
      Matrix.mul_nonsing_inv _ hB, Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_left _ _ hA]
  have hcoX0 : ∀ Y, GlobalTheory.FlipMatch.coX t b c (U (P0 Y) 0) = Y := by
    intro Y
    simp only [GlobalTheory.FlipMatch.coX, hU0, P0, ← Matrix.mul_assoc]
    rw [show (b⁻¹).1 * b.1 = 1 by simp, Matrix.one_mul, Matrix.mul_assoc,
      show c.1ᵀ * (c⁻¹).1ᵀ = 1 by rw [← Matrix.transpose_mul]; simp, Matrix.mul_one]
  have hcoY1 : ∀ z, GlobalTheory.FlipMatch.coY σ X W t b c (U 0 (Q z)) = z := by
    intro z
    simp only [GlobalTheory.FlipMatch.coY, hU1, Q, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hA, Matrix.nonsing_inv_mul_cancel_left _ _ hB,
      ← Matrix.mul_assoc (b.1ᵀ), show b.1ᵀ * (b⁻¹).1ᵀ = 1 by rw [← Matrix.transpose_mul]; simp, Matrix.one_mul,
      show (c⁻¹).1 * c.1 = 1 by simp, Matrix.mul_one]
  have hcoY0 : ∀ P, GlobalTheory.FlipMatch.coY σ X W t b c (U P 0) = 0 := by
    intro P; simp [GlobalTheory.FlipMatch.coY, hU1]
  have hcoX1 : ∀ P, GlobalTheory.FlipMatch.coX t b c (U 0 P) = 0 := by
    intro P; simp [GlobalTheory.FlipMatch.coX, hU0]
  have hU00 : GlobalTheory.LatVac.locCo M.co v (U 0 0) = 0 :=
    locCo_eq_zero hcm X W hX hY M t _ (hUat 0 0) (hU0 0 0) (hU1 0 0)
  have hadd0 : ∀ P P', GlobalTheory.LatVac.locCo M.co v (U (P + P') 0) =
      GlobalTheory.LatVac.locCo M.co v (U P 0) + GlobalTheory.LatVac.locCo M.co v (U P' 0) := by
    intro P P'
    rw [← map_add]
    apply heq _ _ (hUat _ _) (hat_add _ _ (hUat _ _) (hUat _ _))
    · rw [Matrix.map_add _ (map_add _), hU0, hU0, hU0]
    · rw [Matrix.map_add _ (map_add _), hU1, hU1, hU1, add_zero]
  have hadd1 : ∀ P P', GlobalTheory.LatVac.locCo M.co v (U 0 (P + P')) =
      GlobalTheory.LatVac.locCo M.co v (U 0 P) + GlobalTheory.LatVac.locCo M.co v (U 0 P') := by
    intro P P'
    rw [← map_add]
    apply heq _ _ (hUat _ _) (hat_add _ _ (hUat _ _) (hUat _ _))
    · rw [Matrix.map_add _ (map_add _), hU0, hU0, hU0, add_zero]
    · rw [Matrix.map_add _ (map_add _), hU1, hU1, hU1]
  let wT : Matrix (Fin n) (Fin d) (Fv F v) →+ (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) :=
    { toFun := fun Y => GlobalTheory.LatVac.locCo M.co v (U (P0 Y) 0)
      map_zero' := by
        show GlobalTheory.LatVac.locCo M.co v (U (b.1 * 0 * c.1ᵀ) 0) = 0
        rw [Matrix.mul_zero, Matrix.zero_mul]; exact hU00
      map_add' := fun Y Y' => by
        show GlobalTheory.LatVac.locCo M.co v (U (b.1 * (Y + Y') * c.1ᵀ) 0) = _
        rw [Matrix.mul_add, Matrix.add_mul]; exact hadd0 _ _ }
  let wM : Matrix (Fin n) (Fin d) (Fv F v) →+ (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) :=
    { toFun := fun z => GlobalTheory.LatVac.locCo M.co v (U 0 (Q z))
      map_zero' := by
        show GlobalTheory.LatVac.locCo M.co v (U 0 (Q 0)) = 0
        have : Q 0 = 0 := by simp [Q]
        rw [this]; exact hU00
      map_add' := fun z z' => by
        show GlobalTheory.LatVac.locCo M.co v (U 0 (Q (z + z'))) = _
        have : Q (z + z') = Q z + Q z' := by simp only [Q, Matrix.mul_add, Matrix.add_mul, neg_add]
        rw [this]; exact hadd1 _ _ }
  have hwT : ∀ Y, wT Y = GlobalTheory.LatVac.locCo M.co v (U (P0 Y) 0) := fun _ => rfl
  have hwM : ∀ z, wM z = GlobalTheory.LatVac.locCo M.co v (U 0 (Q z)) := fun _ => rfl
  have hform := fun (x u : Matrix (Fin n) (Fin d) (AE F E)) (hx : At (evFin F v) x) =>
    (locCo_form M.co v x u).trans (evFin_symp hcm X W hX hY t b c x u hx)
  haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F _).injective
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.SchrSB.continuous_psiAt B.ψ hstd.1 v
  have hψne : GlobalTheory.LatVac.psiAt B.ψ v ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hstd v
  obtain ⟨ι, hbij, htr, hmu⟩ := GlobalTheory.T.stoneVonNeumann_schwartzBruhat_anyCharacter (GlobalTheory.LatVac.psiAt B.ψ v) hψc hψne wT wM
    (fun Y Y' => by
      rw [hwT, hwT, hform _ _ (hUat _ _), hcoX0, hcoX0, hcoY0, hcoY0]
      simp [GlobalTheory.FlipMatch.pairM])
    (fun z z' => by
      rw [hwM, hwM, hform _ _ (hUat _ _), hcoX1, hcoX1, hcoY1, hcoY1]
      simp [GlobalTheory.FlipMatch.pairM])
    (fun Y z => by
      rw [hwT, hwM, hform _ _ (hUat _ _), hcoX0, hcoX1, hcoY0, hcoY1]
      simp [GlobalTheory.FlipMatch.pairM])
    (fun w => by
      obtain ⟨u, hu, rfl⟩ := locCo_surj M.co v w
      refine ⟨GlobalTheory.FlipMatch.coX t b c u, GlobalTheory.FlipMatch.coY σ X W t b c u, ?_⟩
      rw [hwT, hwM, ← map_add]
      apply heq _ _ (hat_add _ _ (hUat _ _) (hUat _ _)) hu
      · rw [Matrix.map_add _ (map_add _), hU0, hU0, add_zero]
        exact hP0 _
      · rw [Matrix.map_add _ (map_add _), hU1, hU1, zero_add]
        exact hQ _)
  have hφ₁ : ∀ (u : Matrix (Fin n) (Fin d) (AE F E)), At (evFin F v) u →
      ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ₁, Acts (evFin F v) (M.co.rho B.ψ u) φ φ₁ →
        φ₁ = GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v u) φ :=
    fun u hu φ hφ φ₁ hact => GlobalTheory.TensUniq.eq_of_tens_eq v φ φ₁ _ hφ fun r hr =>
      (hact r hr).symm.trans (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v u hu φ r hr)
  refine ⟨ι, hbij, ?_, ?_⟩
  · intro u hu hu0 φ hφ φ₁ _ hact Y
    have e1 := hφ₁ u hu φ hφ φ₁ hact
    have e2 : GlobalTheory.LatVac.locCo M.co v u = wT (GlobalTheory.FlipMatch.coX t b c u) := by
      rw [hwT]
      apply heq _ _ hu (hUat _ _)
      · rw [hU0]; exact (hP0 _).symm
      · rw [hU1]; exact hu0
    rw [e1, e2]
    exact congrFun (htr _ φ hφ) Y
  · intro u hu hu1 φ hφ φ₁ _ hact x hx hx0
    have e1 := hφ₁ u hu φ hφ φ₁ hact
    have e2 : GlobalTheory.LatVac.locCo M.co v u = wM (GlobalTheory.FlipMatch.coY σ X W t b c u) := by
      rw [hwM]
      apply heq _ _ hu (hUat _ _)
      · rw [hU0]; exact hu1
      · rw [hU1]; exact (hQ _).symm
    have hcx : GlobalTheory.FlipMatch.coY σ X W t b c x = 0 := by simp [GlobalTheory.FlipMatch.coY, hx0]
    rw [e1, e2, congrFun (hmu _ φ hφ), GlobalTheory.VacIndic.psi_of_at B.ψ (at_symp σ _ _ x u hx),
      evFin_symp hcm X W hX hY t b c x u hx, hcx, ← GlobalTheory.LatVac.psiAt_apply]
    simp [GlobalTheory.FlipMatch.pairM, GlobalTheory.FlipMatch.coX]

end GlobalTheory.LinWSplit
