import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
import Formalism.LocalRingCardinality.DataExtra
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryAdelicHeightCosetLeNormInfPow
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MultMem

section LinOn

variable {M : Type} [AddCommGroup M] [Module ℂ M] {S : Submodule ℂ M}

def LinOn (S : Submodule ℂ M) (L : M → M) : Prop :=
  (∀ f ∈ S, L f ∈ S) ∧ (∀ f ∈ S, ∀ g ∈ S, L (f + g) = L f + L g) ∧ ∀ c : ℂ, ∀ f ∈ S, L (c • f) = c • L f

theorem LinOn.id : LinOn S fun f => f :=
  ⟨fun _ hf => hf, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem LinOn.comp {L L' : M → M} (h : LinOn S L) (h' : LinOn S L') : LinOn S fun f => L (L' f) := by
  refine ⟨fun f hf => h.1 _ (h'.1 f hf), fun f hf g hg => ?_, fun c f hf => ?_⟩
  · show L (L' (f + g)) = L (L' f) + L (L' g)
    rw [h'.2.1 f hf g hg, h.2.1 _ (h'.1 f hf) _ (h'.1 g hg)]
  · show L (L' (c • f)) = c • L (L' f)
    rw [h'.2.2 c f hf, h.2.2 c _ (h'.1 f hf)]

theorem LinOn.add_smul {L L' : M → M} (h : LinOn S L) (h' : LinOn S L') (a : ℂ) :
    LinOn S fun f => L f + a • L' f := by
  refine ⟨fun f hf => S.add_mem (h.1 f hf) (S.smul_mem a (h'.1 f hf)), fun f hf g hg => ?_, fun c f hf => ?_⟩
  · show L (f + g) + a • L' (f + g) = (L f + a • L' f) + (L g + a • L' g)
    rw [h.2.1 f hf g hg, h'.2.1 f hf g hg, smul_add]
    abel
  · show L (c • f) + a • L' (c • f) = c • (L f + a • L' f)
    rw [h.2.2 c f hf, h'.2.2 c f hf, smul_add, smul_comm a c]

theorem LinOn.sum {ι : Type} [Fintype ι] {L : ι → M → M} (h : ∀ i, LinOn S (L i)) :
    LinOn S fun f => ∑ i, L i f := by
  refine ⟨fun f hf => S.sum_mem fun i _ => (h i).1 f hf, fun f hf g hg => ?_, fun c f hf => ?_⟩
  · show ∑ i, L i (f + g) = ∑ i, L i f + ∑ i, L i g
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => (h i).2.1 f hf g hg
  · show ∑ i, L i (c • f) = c • ∑ i, L i f
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => (h i).2.2 c f hf

theorem LinOn.foldr {α : Type} (F : α → M → M) (l : List α) (h : ∀ a ∈ l, LinOn S (F a)) :
    LinOn S fun f => l.foldr F f := by
  induction l with
  | nil => exact LinOn.id
  | cons a l ih =>
    exact (h a (by simp)).comp (ih fun b hb => h b (List.mem_cons_of_mem a hb))

end LinOn

variable {D : D7} (θ : InfFam D) (V : HSp D)

def smFun : Submodule ℂ (GA D V → ℂ) where
  carrier := {φ | ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
    (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
      ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)}
  add_mem' := fun h h' k τs Xs hX g => (h k τs Xs hX g).add (h' k τs Xs hX g)
  zero_mem' := fun _ _ _ _ _ => contDiff_const
  smul_mem' := fun c _ h k τs Xs hX g => contDiff_const.mul (h k τs Xs hX g)

variable {θ V}

theorem diff_oneP {φ : GA D V → ℂ} (h : φ ∈ smFun θ V) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (g : GA D V) : Differentiable ℝ fun t : ℝ => φ (g * oneP θ V τ X t) := by
  have h1 := h 1 (fun _ => τ) (fun _ => X) (fun _ => hX) g
  have h2 := h1.comp (contDiff_pi.2 fun _ => contDiff_id : ContDiff ℝ ∞ fun t : ℝ => fun _ : Fin 1 => t)
  simp only [Function.comp_def, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one] at h2
  exact h2.differentiable (by simp)

theorem contDiff_deriv_snoc {k : ℕ} {F : (Fin (k + 1) → ℝ) → ℂ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ fun t : Fin k → ℝ => deriv (fun s : ℝ => F (Fin.snoc t s)) 0 := by

  have hline : ∀ (t : Fin k → ℝ) (s : ℝ),
      (Fin.snoc t s : Fin (k + 1) → ℝ) = Fin.snoc t 0 + s • Pi.single (Fin.last k) 1 := by
    intro t s
    funext i
    induction i using Fin.lastCases with
    | last => simp
    | cast j => simp [(Fin.castSucc_lt_last j).ne]
  have hd : ∀ t : Fin k → ℝ, deriv (fun s : ℝ => F (Fin.snoc t s)) 0 =
      fderiv ℝ F (Fin.snoc t 0) (Pi.single (Fin.last k) 1) := by
    intro t
    have hl : HasDerivAt (fun s : ℝ => (Fin.snoc t s : Fin (k + 1) → ℝ)) (Pi.single (Fin.last k) 1) 0 := by
      have hlin : HasDerivAt (fun s : ℝ => (Fin.snoc t 0 : Fin (k + 1) → ℝ) + s • Pi.single (Fin.last k) (1 : ℝ))
          (Pi.single (Fin.last k) 1) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single (Fin.last k) (1 : ℝ) : Fin (k + 1) → ℝ)).const_add
          (Fin.snoc t 0 : Fin (k + 1) → ℝ)
      exact hlin.congr_of_eventuallyEq (Filter.Eventually.of_forall (hline t))
    have hF' : HasFDerivAt F (fderiv ℝ F (Fin.snoc t 0)) (Fin.snoc t 0) :=
      ((hF.differentiable (by simp)) _).hasFDerivAt
    exact (HasFDerivAt.comp_hasDerivAt (l := F) (f := fun s : ℝ => (Fin.snoc t s : Fin (k + 1) → ℝ)) 0 hF' hl).deriv
  have hs : ContDiff ℝ ∞ fun t : Fin k → ℝ => (Fin.snoc t 0 : Fin (k + 1) → ℝ) := by
    refine contDiff_pi.2 fun i => ?_
    induction i using Fin.lastCases with
    | last => simp only [Fin.snoc_last]; exact contDiff_const
    | cast j => simp only [Fin.snoc_castSucc]; exact (contDiff_pi.1 contDiff_id) j
  rw [funext hd]
  exact (((contDiff_infty_iff_fderiv.1 hF).2).comp hs).clm_apply contDiff_const

theorem linOn_Rder {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    LinOn (smFun θ V) (Rder θ V τ X) := by
  refine ⟨fun φ hφ => ?_, fun φ hφ ψ hψ => ?_, fun c φ hφ => ?_⟩
  · intro k τs Xs hXs g
    have hX' : ∀ i, (Fin.snoc Xs X : Fin (k + 1) → _) i ∈ lieAt V ((Fin.snoc τs τ : Fin (k + 1) → _) i) := by
      intro i
      induction i using Fin.lastCases with
      | last => simpa using hX
      | cast j => simpa using hXs j
    have hF := hφ (k + 1) (Fin.snoc τs τ) (Fin.snoc Xs X) hX' g
    convert contDiff_deriv_snoc hF using 1
    funext t
    simp only [Rder, List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append, List.prod_append,
      List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  · funext g
    simp only [Rder, Pi.add_apply]
    exact deriv_add (diff_oneP hφ hX g).differentiableAt (diff_oneP hψ hX g).differentiableAt
  · funext g
    simp only [Rder, Pi.smul_apply, smul_eq_mul]
    exact deriv_const_mul c (diff_oneP hφ hX g).differentiableAt

theorem linOn_gelf (τ : D.what₂.Tau) (k : ℕ) : LinOn (smFun θ V) (gelf θ V τ k) := by

  have hC : ∀ Z, LinOn (smFun θ V) (RderC θ V τ Z) := fun Z =>
    LinOn.add_smul (linOn_Rder (GlobalTheory.SmoothAutCheck.parts_mem V τ Z).1)
      (linOn_Rder (GlobalTheory.SmoothAutCheck.parts_mem V τ Z).2) Complex.I
  unfold gelf
  refine LinOn.sum fun idx => LinOn.foldr (fun (f : (GA D V → ℂ) → GA D V → ℂ) acc => f acc) _ fun a ha => ?_
  simp only [List.mem_ofFn] at ha
  obtain ⟨i, rfl⟩ := ha
  exact hC _

theorem normInf_cases : (∀ g, normInf θ V g = 0) ∨ ∀ g, 1 ≤ normInf θ V g := by
  by_cases h : Nonempty D.what₂.Tau ∧ 0 < V.rank
  · right
    intro g
    obtain ⟨⟨τ0⟩, hr⟩ := h

    have key : ∀ A B : Matrix (Fin V.rank) (Fin V.rank) ℂ, A * B = 1 →
        1 ≤ ∑ i, ∑ j, (‖A i j‖ + ‖B i j‖) := by
      intro A B hAB
      let i0 : Fin V.rank := ⟨0, hr⟩
      have hx : 0 ≤ ∑ i, ∑ j, ‖A i j‖ := by positivity
      have hy : 0 ≤ ∑ i, ∑ j, ‖B i j‖ := by positivity
      have hb : ∀ i j, ‖B i j‖ ≤ ∑ i, ∑ j, ‖B i j‖ := fun i j =>
        (Finset.single_le_sum (f := fun j => ‖B i j‖) (fun j _ => norm_nonneg _) (Finset.mem_univ j)).trans
          (Finset.single_le_sum (f := fun i => ∑ j, ‖B i j‖)
            (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ i))
      have ha : ∑ k, ‖A i0 k‖ ≤ ∑ i, ∑ j, ‖A i j‖ :=
        Finset.single_le_sum (f := fun i => ∑ j, ‖A i j‖)
          (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ i0)
      have e : (1 : ℂ) = ∑ k, A i0 k * B k i0 := by
        have := congrFun (congrFun hAB i0) i0
        rw [Matrix.mul_apply, Matrix.one_apply_eq] at this
        exact this.symm
      have h1 : (1 : ℝ) ≤ (∑ i, ∑ j, ‖A i j‖) * ∑ i, ∑ j, ‖B i j‖ :=
        calc (1 : ℝ) = ‖∑ k, A i0 k * B k i0‖ := by rw [← e, norm_one]
          _ ≤ ∑ k, ‖A i0 k‖ * ‖B k i0‖ := (norm_sum_le _ _).trans (le_of_eq (by simp only [norm_mul]))
          _ ≤ ∑ k, ‖A i0 k‖ * ∑ i, ∑ j, ‖B i j‖ :=
            Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hb k i0) (norm_nonneg _)
          _ = (∑ k, ‖A i0 k‖) * ∑ i, ∑ j, ‖B i j‖ := by rw [Finset.sum_mul]
          _ ≤ (∑ i, ∑ j, ‖A i j‖) * ∑ i, ∑ j, ‖B i j‖ := mul_le_mul_of_nonneg_right ha hy
      rw [Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib, Finset.sum_add_distrib]
      nlinarith [sq_nonneg ((∑ i, ∑ j, ‖A i j‖) - ∑ i, ∑ j, ‖B i j‖)]
    have hAB : infMat D.sp.cm.sig V.gram (θ τ0) g * infMat D.sp.cm.sig V.gram (θ τ0) g⁻¹ = 1 := by
      rw [← GlobalTheory.SmoothForms.HeightCoset.infMat_mul', mul_inv_cancel, GlobalTheory.SmoothForms.HeightCoset.infMat_one']
    refine (key _ _ hAB).trans ?_
    unfold normInf
    exact Finset.single_le_sum (f := fun τ => ∑ i, ∑ j, (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ +
      ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖)) (fun τ _ => by positivity) (Finset.mem_univ τ0)
  · left
    intro g
    unfold normInf
    apply Finset.sum_eq_zero
    intro τ _
    apply Finset.sum_eq_zero
    intro i _
    exact absurd ⟨⟨τ⟩, Nat.zero_lt_of_lt i.2⟩ h

theorem exists_exponent (N N' : ℕ) :
    ∃ K : ℕ, ∀ g, normInf θ V g ^ N ≤ normInf θ V g ^ K ∧ normInf θ V g ^ N' ≤ normInf θ V g ^ K := by
  rcases normInf_cases (θ := θ) (V := V) with h | h
  · refine ⟨0, fun g => ?_⟩
    rw [h g, pow_zero]
    exact ⟨pow_le_one₀ le_rfl zero_le_one, pow_le_one₀ le_rfl zero_le_one⟩
  · exact ⟨max N N', fun g => ⟨pow_le_pow_right₀ (h g) (le_max_left _ _), pow_le_pow_right₀ (h g) (le_max_right _ _)⟩⟩

theorem mem_smFun {φ : GA D V → ℂ} (h : IsAutFunSm θ V φ) : φ ∈ smFun θ V := h.smooth

theorem linOn_word (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) :
    LinOn (smFun θ V) fun φ => l.foldr (fun p f => Rder θ V p.1 p.2 f) φ := by
  refine LinOn.foldr (S := smFun θ V) (fun (p : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ) f => Rder θ V p.1 p.2 f) l ?_
  intro p hp
  exact linOn_Rder (hl p hp)

theorem isAutFunSm_add {φ ψ : GA D V → ℂ} (h : IsAutFunSm θ V φ) (h' : IsAutFunSm θ V ψ) :
    IsAutFunSm θ V (φ + ψ) where
  left γ hγ g := by simp only [Pi.add_apply, h.left γ hγ g, h'.left γ hγ g]
  level := by
    obtain ⟨U, hU, hUk⟩ := h.level
    obtain ⟨U', hU', hUk'⟩ := h'.level
    refine ⟨U ⊓ U', by simpa using hU.inter hU', fun k hk hk' g => ?_⟩
    simp only [Pi.add_apply, hUk k (Subgroup.mem_inf.1 hk).1 hk' g, hUk' k (Subgroup.mem_inf.1 hk).2 hk' g]
  cont := h.cont.add h'.cont
  smooth k τs Xs hX g := (h.smooth k τs Xs hX g).add (h'.smooth k τs Xs hX g)
  zfin := by

    obtain ⟨W, hW, hφ, hWg⟩ := h.zfin
    obtain ⟨W', hW', hψ, hWg'⟩ := h'.zfin
    have := hW
    have := hW'
    have : FiniteDimensional ℂ (W ⊓ smFun θ V : Submodule ℂ (GA D V → ℂ)) :=
      Submodule.finiteDimensional_of_le inf_le_left
    have : FiniteDimensional ℂ (W' ⊓ smFun θ V : Submodule ℂ (GA D V → ℂ)) :=
      Submodule.finiteDimensional_of_le inf_le_left
    refine ⟨W ⊓ smFun θ V ⊔ W' ⊓ smFun θ V, inferInstance,
      Submodule.add_mem_sup (Submodule.mem_inf.2 ⟨hφ, mem_smFun h⟩) (Submodule.mem_inf.2 ⟨hψ, mem_smFun h'⟩),
      fun τ k f hf => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hf
    have hl := linOn_gelf (θ := θ) (V := V) τ k
    rw [Submodule.mem_inf] at ha hb
    rw [hl.2.1 a ha.2 b hb.2]
    exact Submodule.add_mem_sup (Submodule.mem_inf.2 ⟨hWg τ k a ha.1, hl.1 a ha.2⟩)
      (Submodule.mem_inf.2 ⟨hWg' τ k b hb.1, hl.1 b hb.2⟩)
  growth := by
    obtain ⟨N, hN⟩ := h.growth
    obtain ⟨N', hN'⟩ := h'.growth
    obtain ⟨K, hK⟩ := exists_exponent (θ := θ) (V := V) N N'
    refine ⟨K, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl x
    obtain ⟨C', hC'⟩ := hN' l hl x
    refine ⟨max C 0 + max C' 0, fun g hg => ?_⟩
    have e : l.foldr (fun p f => Rder θ V p.1 p.2 f) (φ + ψ) =
        l.foldr (fun p f => Rder θ V p.1 p.2 f) φ + l.foldr (fun p f => Rder θ V p.1 p.2 f) ψ :=
      (linOn_word (θ := θ) (V := V) l hl).2.1 φ (mem_smFun h) ψ (mem_smFun h')
    rw [e, Pi.add_apply]
    have h0 : 0 ≤ normInf θ V g := by unfold normInf; positivity
    have t1 : C * normInf θ V g ^ N ≤ max C 0 * normInf θ V g ^ K :=
      (mul_le_mul_of_nonneg_right (le_max_left C 0) (pow_nonneg h0 N)).trans
        (mul_le_mul_of_nonneg_left (hK g).1 (le_max_right C 0))
    have t2 : C' * normInf θ V g ^ N' ≤ max C' 0 * normInf θ V g ^ K :=
      (mul_le_mul_of_nonneg_right (le_max_left C' 0) (pow_nonneg h0 N')).trans
        (mul_le_mul_of_nonneg_left (hK g).2 (le_max_right C' 0))
    rw [add_mul]
    linarith [norm_add_le (l.foldr (fun p f => Rder θ V p.1 p.2 f) φ (x * g))
      (l.foldr (fun p f => Rder θ V p.1 p.2 f) ψ (x * g)), hC g hg, hC' g hg]

theorem isAutFunSm_smul (c : ℂ) {φ : GA D V → ℂ} (h : IsAutFunSm θ V φ) : IsAutFunSm θ V (c • φ) where
  left γ hγ g := by simp only [Pi.smul_apply, h.left γ hγ g]
  level := by
    obtain ⟨U, hU, hUk⟩ := h.level
    exact ⟨U, hU, fun k hk hk' g => by simp only [Pi.smul_apply, hUk k hk hk' g]⟩
  cont := h.cont.const_smul c
  smooth k τs Xs hX g := (h.smooth k τs Xs hX g).const_smul c
  zfin := by
    obtain ⟨W, hW, hφ, hWg⟩ := h.zfin
    have := hW
    have : FiniteDimensional ℂ (W ⊓ smFun θ V : Submodule ℂ (GA D V → ℂ)) :=
      Submodule.finiteDimensional_of_le inf_le_left
    refine ⟨W ⊓ smFun θ V, inferInstance, Submodule.smul_mem _ c (Submodule.mem_inf.2 ⟨hφ, mem_smFun h⟩),
      fun τ k f hf => ?_⟩
    rw [Submodule.mem_inf] at hf ⊢
    exact ⟨hWg τ k f hf.1, (linOn_gelf (θ := θ) (V := V) τ k).1 f hf.2⟩
  growth := by
    obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl x
    refine ⟨‖c‖ * C, fun g hg => ?_⟩
    have e : l.foldr (fun p f => Rder θ V p.1 p.2 f) (c • φ) = c • l.foldr (fun p f => Rder θ V p.1 p.2 f) φ :=
      (linOn_word (θ := θ) (V := V) l hl).2.2 c φ (mem_smFun h)
    rw [e, Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC g hg) (norm_nonneg c)

theorem isCuspFun_add {φ ψ : GA D V → ℂ} (h : IsAutFun V φ) (h' : IsAutFun V ψ) (c : IsCuspFun V φ)
    (c' : IsCuspFun V ψ) : IsCuspFun V (φ + ψ) := by
  have hφ := (GlobalTheory.AutFunCompare.isCuspFun_iff V φ h.cont h.left).1 c
  have hψ := (GlobalTheory.AutFunCompare.isCuspFun_iff V ψ h'.cont h'.left).1 c'
  exact (GlobalTheory.AutFunCompare.isCuspFun_iff V (φ + ψ) (h.cont.add h'.cont)
    (fun γ hγ g => by simp only [Pi.add_apply, h.left γ hγ g, h'.left γ hγ g])).2 (add_mem hφ hψ)

theorem isCuspFun_smul (a : ℂ) {φ : GA D V → ℂ} (c : IsCuspFun V φ) : IsCuspFun V (a • φ) := by
  intro r C hC μ 𝓕 hμ h𝓕 g
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul, c r C hC μ 𝓕 hμ h𝓕 g, mul_zero]

section Sob

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Lie : Set (Matrix (Fin n) (Fin n) ℂ)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem sobCont_zero : Sobolev₂ Lie σ 0 := by
  unfold Sobolev₂
  exact ⟨[], 0, by simp, fun w _ => by simp⟩

theorem sobCont_smul (c : ℂ) {ℓ : H →ₗ[ℂ] ℂ} (h : Sobolev₂ Lie σ ℓ) : Sobolev₂ Lie σ (c • ℓ) := by
  unfold Sobolev₂ at *
  obtain ⟨L, C, hL, hC⟩ := h
  refine ⟨L, ‖c‖ * C, hL, fun w hw => ?_⟩
  rw [LinearMap.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC w hw) (norm_nonneg c)

theorem sobCont_add {ℓ ℓ' : H →ₗ[ℂ] ℂ} (h : Sobolev₂ Lie σ ℓ) (h' : Sobolev₂ Lie σ ℓ') : Sobolev₂ Lie σ (ℓ + ℓ') := by
  unfold Sobolev₂ at *
  obtain ⟨L, C, hL, hC⟩ := h
  obtain ⟨L', C', hL', hC'⟩ := h'
  refine ⟨L ++ L', |C| + |C'|, fun l hl X hX => ?_, fun w hw => ?_⟩
  · rcases List.mem_append.1 hl with hl | hl
    exacts [hL l hl X hX, hL' l hl X hX]
  · rw [LinearMap.add_apply, List.map_append, List.sum_append]
    have ha : 0 ≤ (L.map fun l => ‖l.foldr (dRep σ) w‖).sum := List.sum_nonneg (by simp)
    have hb : 0 ≤ (L'.map fun l => ‖l.foldr (dRep σ) w‖).sum := List.sum_nonneg (by simp)
    have e1 := hC w hw
    have e2 := hC' w hw
    nlinarith [norm_add_le (ℓ w) (ℓ' w), le_abs_self C, le_abs_self C', abs_nonneg C, abs_nonneg C',
      mul_nonneg (sub_nonneg.2 (le_abs_self C)) ha, mul_nonneg (sub_nonneg.2 (le_abs_self C')) hb,
      mul_nonneg (abs_nonneg C) hb, mul_nonneg (abs_nonneg C') ha]

end Sob

variable {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ}

private theorem isAutFunSm_zero' : IsAutFunSm θ V (0 : GA D V → ℂ) where
  left _ _ _ := rfl
  level := ⟨⊤, by simp, fun _ _ _ _ => rfl⟩
  cont := continuous_const
  smooth _ _ _ _ _ := contDiff_const
  zfin := by
    refine ⟨⊥, inferInstance, Submodule.zero_mem _, fun τ k f hf => ?_⟩
    rw [Submodule.mem_bot] at hf ⊢
    subst hf

    have := (linOn_gelf (θ := θ) (V := V) τ k).2.2 0 0 (Submodule.zero_mem _)
    simpa using this
  growth := by
    refine ⟨0, fun l hl x => ⟨0, fun g _ => ?_⟩⟩
    have := (linOn_word (θ := θ) (V := V) l hl).2.2 0 0 (Submodule.zero_mem _)
    simp only [zero_smul] at this
    rw [this]
    simp

theorem isMultMap_zero : IsMultMap θ M J χ 0 where
  aut _ := isAutFunSm_zero'
  cusp _ := by
    intro r C hC μ 𝓕 hμ h𝓕 g
    simp
  lev _ _ _ _ := by simp
  equiv _ _ _ _ _ _ := rfl
  cont _ _ _ := ⟨0, sobCont_zero, fun _ => by simp⟩

theorem isMultMap_add {T T' : MMap M} (h : IsMultMap θ M J χ T) (h' : IsMultMap θ M J χ T') :
    IsMultMap θ M J χ (T + T') where
  aut v := isAutFunSm_add (h.aut v) (h'.aut v)
  cusp v := isCuspFun_add (h.aut v).toIsAutFun (h'.aut v).toIsAutFun (h.cusp v) (h'.cusp v)
  lev v k hk g := by
    simp only [_root_.add_apply, Pi.add_apply, h.lev v k hk g, h'.lev v k hk g, mul_add]
  equiv τ g hg v w hw := by
    simp only [_root_.add_apply, h.equiv τ g hg v w hw, h'.equiv τ g hg v w hw]
    rfl
  cont τ v x := by
    obtain ⟨ℓ, hℓ, e⟩ := h.cont τ v x
    obtain ⟨ℓ', hℓ', e'⟩ := h'.cont τ v x
    exact ⟨ℓ + ℓ', sobCont_add hℓ hℓ', fun w => by simp only [LinearMap.add_apply, e w, e' w,
      _root_.add_apply, Pi.add_apply]⟩

theorem isMultMap_smul (c : ℂ) {T : MMap M} (h : IsMultMap θ M J χ T) : IsMultMap θ M J χ (c • T) where
  aut v := isAutFunSm_smul c (h.aut v)
  cusp v := isCuspFun_smul c (h.cusp v)
  lev v k hk g := by
    simp only [_root_.smul_apply, Pi.smul_apply, smul_eq_mul, h.lev v k hk g]
    ring
  equiv τ g hg v w hw := by
    simp only [_root_.smul_apply, h.equiv τ g hg v w hw]
    rfl
  cont τ v x := by
    obtain ⟨ℓ, hℓ, e⟩ := h.cont τ v x
    exact ⟨c • ℓ, sobCont_smul c hℓ, fun w => by simp only [LinearMap.smul_apply, e w,
      _root_.smul_apply, Pi.smul_apply]⟩

theorem mem_mult_iff : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), T ∈ Mult θ M J χ ↔ IsMultMap θ M J χ T := by
  intro D θ V S M J χ T
  unfold Formalism.IndefR.Mult.Mult
  constructor
  · intro hT
    induction hT using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact isMultMap_zero
    | add x y _ _ hx hy => exact isMultMap_add hx hy
    | smul a x _ hx => exact isMultMap_smul a hx
  · intro hT
    exact Submodule.subset_span hT

end GlobalTheory.MultMem

end
