import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockOfMatrix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeInertPlaceSelfDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdelicLatticeAtFinitePlaceIffInert
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadraticUnramifiedIffInertOrSplit
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitDict

open GlobalTheory.InertLocField GlobalTheory.InertSelfDual

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem nonempty_emb {σ : E →ₐ[F] E} (h : IsCMExt F E σ) [Algebra.Unramified (𝓞 F) (𝓞 E)] (v : Pl F)
    (hv : ∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w) : Nonempty (E →ₐ[F] Fv F v) := by
  rcases (GlobalTheory.quadratic_unramified_iff_inert_or_split F E h.2.2.1 v).1 (fun w _ => inferInstance) with hp | hp
  · refine (hv ⟨_, hp, fun h0 => v.ne_bot ?_⟩ rfl).elim
    exact (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))).1 h0
  · exact (nonempty_split_iff h).2 hp

omit [NumberField E] in
theorem piW_apply {v : Pl F} (τ : E →ₐ[F] Fv F v) (z : AE F E) : piW τ z = splitProj τ (evT E v z) := rfl

omit [NumberField E] in
theorem piW_cA {v : Pl F} (τ : E →ₐ[F] Fv F v) (σ : E →ₐ[F] E) (z : AE F E) :
    piW τ (cA σ z) = piW (τ.comp σ) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

omit [NumberField E] in
theorem piW_algebraMap {v : Pl F} (τ : E →ₐ[F] Fv F v) (a : AF F) :
    piW τ (algebraMap (AF F) (AE F E) a) = evFin F v a := by
  show evFin F v a * τ 1 = _
  rw [map_one, mul_one]

omit [NumberField E] in
theorem piW_inclR {v : Pl F} (τ : E →ₐ[F] Fv F v) (e : E) : piW τ (inclR (F := F) (AF F) e) = τ e := by
  show evFin F v 1 * τ e = _
  rw [map_one, one_mul]

theorem mem_latAt_iff {d : ℕ} (W : Spc F E d) (v : Pl F) (z : Fin d → AE F E) :
    z ∈ GlobalTheory.InertSph.latAt W v ↔ At (evFin F v) z ∧ (fun i => evT E v (z i)) ∈ latLoc F W.L v := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, haO, y, hy, rfl⟩ := hz
      refine ⟨fun u hu => ?_, ?_⟩
      · rw [smul_smul, ← smul_eq_mul, ha u hu, zero_smul]
      · convert tmul_mem_latLoc haO hy using 1
        funext i
        rw [Pi.smul_apply, GlobalTheory.InertSphLat.smul_inclR]
        rfl
    | zero => exact ⟨fun u _ => smul_zero u, by
        convert zero_mem (latLoc F W.L v) using 1
        funext i; simp⟩
    | add x y _ _ hx hy =>
      refine ⟨fun u hu => by rw [smul_add, hx.1 u hu, hy.1 u hu, add_zero], ?_⟩
      convert add_mem hx.2 hy.2 using 1
      funext i; simp
    | neg x _ hx =>
      refine ⟨fun u hu => by rw [smul_neg, hx.1 u hu, neg_zero], ?_⟩
      convert neg_mem hx.2 using 1
      funext i; simp
  · rintro ⟨hz, hm⟩
    have key : ∀ y ∈ latLoc F W.L v, (fun i => liftT E v (y i)) ∈ GlobalTheory.InertSph.latAt W v := fun y hy => by
      refine latLoc_induction (p := fun y => (fun i => liftT E v (y i)) ∈ GlobalTheory.InertSph.latAt W v)
        (fun a ha x hx => GlobalTheory.InertSphLat.gen_mem W ha hx) ?_ (fun p q hp hq => ?_) (fun p hp => ?_) hy
      · convert zero_mem (GlobalTheory.InertSph.latAt W v) using 1
        funext i; simp
      · convert add_mem hp hq using 1
        funext i; simp
      · convert neg_mem hp using 1
        funext i; simp
    convert key _ hm using 1
    funext i
    obtain ⟨y, hy⟩ := (at_iff v (z i)).1 fun u hu => congrFun (hz u hu) i
    rw [← hy, evT_liftT]

theorem mem_of_trace_int {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {v : Pl F} (hu : PsiUnr ψ v) (t : F)
    (ht : ∀ a : 𝓞 F, ∃ k : ℤ, Algebra.trace ℚ F ((a : F) * t) = k) :
    algebraMap F (Fv F v) t ∈ v.adicCompletionIntegers F := by
  refine (hu _).1 fun y hy => ?_
  have h := GlobalTheory.LatVacArith.psi_int hψ t ht (singleFin v y) fun w => by
    by_cases hw : w = v
    · subst hw
      rw [evalV_singleFin_self]
      exact hy
    · rw [evalV_singleFin_ne hw]
      exact zero_mem _
  rw [mul_comm, ← Algebra.smul_def, ← LinearMap.map_smul, Algebra.smul_def] at h
  exact h

theorem form_mem {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) {d r s : ℕ} {W : Spc F E d}
    (hW : W.IsSkew σ B r s) {v : Pl F} (hu : PsiUnr B.ψ v) (τ : E →ₐ[F] Fv F v) {x y : Fin d → E}
    (hx : x ∈ W.L) (hy : y ∈ W.L) : τ (form σ W.J x y) ∈ v.adicCompletionIntegers F := by
  haveI := hB.unram
  obtain ⟨m, p, c, hsc⟩ := exists_traceFamily (F := F) (E := E)
  rw [← hsc (form σ W.J x y), map_sum]
  refine sum_mem fun i _ => ?_
  rw [map_smul, Algebra.smul_def]
  refine mul_mem (mem_of_trace_int hB.std hu _ fun a => ?_) (apply_coe_mem τ _)
  have h := (hW.dual x).1 hx y hy (algebraMap (𝓞 F) (𝓞 E) a * c i)
  have e : (a : F) * Algebra.trace F E ((c i : E) * form σ W.J x y) =
      Algebra.trace F E (((algebraMap (𝓞 F) (𝓞 E) a * c i : 𝓞 E) : E) * form σ W.J x y) := by
    rw [← smul_eq_mul, ← LinearMap.map_smul, Algebra.smul_def, ← mul_assoc]
    rfl
  rw [e, Algebra.trace_trace]
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  exact ⟨k, by rw [← hk]; simp⟩

omit [NumberField E] in
theorem splitLat_induction {d : ℕ} {L : Submodule (𝓞 E) (Fin d → E)} {v : Pl F} {τ : E →ₐ[F] Fv F v}
    (N : Submodule (v.adicCompletionIntegers F) (Fin d → Fv F v)) (hN : ∀ x ∈ L, (fun i => τ (x i)) ∈ N)
    {u : Fin d → Fv F v} (hu : u ∈ splitLat τ L) : u ∈ N := by
  obtain ⟨y, hy, rfl⟩ := hu
  refine latLoc_induction (p := fun y => splitVec τ y ∈ N) (fun a ha x hx => ?_) ?_ (fun p q hp hq => ?_)
    (fun p hp => ?_) hy
  · exact N.smul_mem ⟨a, ha⟩ (hN x hx)
  · convert N.zero_mem using 1
    funext i; simp [splitVec]
  · rw [splitVec_add]; exact N.add_mem hp hq
  · convert N.neg_mem hp using 1
    funext i; simp [splitVec]

omit [NumberField E] in
theorem apply_mem_splitLat {d : ℕ} {L : Submodule (𝓞 E) (Fin d → E)} {v : Pl F} (τ : E →ₐ[F] Fv F v)
    {x : Fin d → E} (hx : x ∈ L) : (fun i => τ (x i)) ∈ splitLat τ L :=
  ⟨_, tmul_mem_latLoc (one_mem _) hx, funext fun i => by simp [splitVec]⟩

theorem pairing_mem {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) {d r s : ℕ} {W : Spc F E d}
    (hW : W.IsSkew σ B r s) {v : Pl F} (hu : PsiUnr B.ψ v) (τ : E →ₐ[F] Fv F v) {u₁ u₂ : Fin d → Fv F v}
    (h₁ : u₁ ∈ splitLat τ W.L) (h₂ : u₂ ∈ splitLat (τ.comp σ) W.L) :
    u₁ ⬝ᵥ W.J.map τ *ᵥ u₂ ∈ v.adicCompletionIntegers F := by
  let O : Submodule (v.adicCompletionIntegers F) (Fv F v) :=
    { carrier := v.adicCompletionIntegers F
      add_mem' := add_mem
      zero_mem' := zero_mem _
      smul_mem' := fun c _ hx => mul_mem c.2 hx }
  let β : (Fin d → Fv F v) →ₗ[Fv F v] (Fin d → Fv F v) →ₗ[Fv F v] Fv F v := Matrix.toLinearMap₂' (Fv F v) (W.J.map τ)
  have hβ : ∀ a b, β a b = a ⬝ᵥ W.J.map τ *ᵥ b := fun a b => Matrix.toLinearMap₂'_apply' _ a b
  rw [← hβ]
  refine splitLat_induction (O.comap ((β.flip u₂).restrictScalars _)) (fun x hx => ?_) h₁
  refine splitLat_induction (O.comap ((β fun i => τ (x i)).restrictScalars _)) (fun y hy => ?_) h₂
  show β _ _ ∈ v.adicCompletionIntegers F
  rw [hβ]
  convert form_mem hB hW hu τ hx hy using 1
  simp [form, dotProduct, Matrix.mulVec, map_sum]

omit [NumberField E] in
theorem col_mem {d : ℕ} {L : Submodule (𝓞 E) (Fin d → E)} {v : Pl F} {τ : E →ₐ[F] Fv F v}
    {b : GL (Fin d) (Fv F v)} (hb : IsSplitBasis τ L b) (j : Fin d) : (fun i => b.1 i j) ∈ splitLat τ L := by
  have := (hb (Pi.single j 1)).1 fun i => by
    by_cases e : i = j
    · subst e; simp
    · simp [e]
  rwa [Matrix.mulVec_single_one] at this

theorem exists_gram {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) {d r s : ℕ} {W : Spc F E d}
    (hW : W.IsSkew σ B r s) {v : Pl F} (hu : PsiUnr B.ψ v) (τ : E →ₐ[F] Fv F v) {b₁ b₂ : GL (Fin d) (Fv F v)}
    (h₁ : IsSplitBasis τ W.L b₁) (h₂ : IsSplitBasis (τ.comp σ) W.L b₂) :
    ∃ S : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), IsUnit S.det ∧
      S.map (fun x => (x : Fv F v)) = b₁.1ᵀ * W.J.map τ * b₂.1 := by
  obtain ⟨k, S, T, hS, hT, hTS⟩ := exists_formFrame σ W.J (det_ne_zero_of_skew σ B hW) W.L hW.lat
    (fun y hy => (hW.dual y).2 fun x hx o => by
      obtain ⟨r, hr⟩ := hy x hx
      rw [← hr]
      exact Algebra.isIntegral_trace ((RingOfIntegers.isIntegral_coe o).mul (RingOfIntegers.isIntegral_coe r)))
  have hG : ∀ i j, (b₁.1ᵀ * W.J.map τ * b₂.1) i j ∈ v.adicCompletionIntegers F := fun i j => by
    rw [Matrix.mul_assoc]
    exact pairing_mem hB hW hu τ (col_mem h₁ i) (col_mem h₂ j)
  have hA : ∀ i j, ((b₂⁻¹).1 * S.map (τ.comp σ)) i j ∈ v.adicCompletionIntegers F := fun i j =>
    h₂.mem_iff.1 (apply_mem_splitLat _ (hS j)) i
  have hC : ∀ i j, ((b₁⁻¹).1 * T.map τ) i j ∈ v.adicCompletionIntegers F := fun i j =>
    h₁.mem_iff.1 (apply_mem_splitLat _ (hT j)) i
  have hH : ∀ i j, (((b₂⁻¹).1 * S.map (τ.comp σ)) * ((b₁⁻¹).1 * T.map τ)ᵀ) i j ∈ v.adicCompletionIntegers F :=
    fun i j => sum_mem fun l _ => mul_mem (hA i l) (hC j l)
  have e1 : W.J.map τ * S.map (τ.comp σ) * (T.map τ)ᵀ = 1 := by
    have e0 : W.J * S.map σ * Tᵀ = 1 := by
      rw [← Matrix.transpose_inj, Matrix.transpose_mul, Matrix.transpose_transpose, hTS, Matrix.transpose_one]
    have := congrArg (fun M => Matrix.map M (τ : E →+* Fv F v)) e0
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at this
    exact this
  have e2 : (b₁.1ᵀ * W.J.map τ * b₂.1) * (((b₂⁻¹).1 * S.map (τ.comp σ)) * ((b₁⁻¹).1 * T.map τ)ᵀ) = 1 := by
    calc _ = b₁.1ᵀ * (W.J.map τ * (b₂.1 * (b₂⁻¹).1) * S.map (τ.comp σ) * (T.map τ)ᵀ) * ((b₁⁻¹).1)ᵀ := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by
          rw [Units.mul_inv, Matrix.mul_one, e1, Matrix.mul_one, ← Matrix.transpose_mul, Units.inv_mul,
            Matrix.transpose_one]
  refine ⟨Matrix.of fun i j => ⟨_, hG i j⟩, ?_, rfl⟩
  refine Matrix.isUnit_det_of_right_inverse (B := Matrix.of fun i j => ⟨_, hH i j⟩) ?_
  refine Matrix.map_injective (v.adicCompletionIntegers F).subtype_injective ?_
  simp only
  rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  exact e2

end GlobalTheory.SplitDict

namespace GlobalTheory.SplitDict

open GlobalTheory.InertLocField

theorem exists_split_dictionary : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (v : Pl F), (∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w) → PsiUnr B.ψ v →
    ∃ (π₁ π₂ : AE F E →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
      ((∀ z, π₁ (cA σ z) = π₂ z) ∧ (∀ z, π₂ (cA σ z) = π₁ z) ∧
      (∀ a : AF F, π₁ (algebraMap (AF F) (AE F E) a) = evFin F v a) ∧
      (∀ a : AF F, π₂ (algebraMap (AF F) (AE F E) a) = evFin F v a) ∧
      (∀ z : AE F E, At (evFin F v) z → π₁ z = 0 → π₂ z = 0 → z = 0) ∧
      (∀ x₁ x₂ : Fv F v, ∃ z : AE F E, At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) ∧
      (∀ z : Fin d → AE F E, z ∈ GlobalTheory.InertSph.latAt W v ↔ At (evFin F v) z ∧
        (∀ i, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₁ (z j)) i ∈
          v.adicCompletionIntegers F) ∧
        (∀ i, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₂ (z j)) i ∈
          v.adicCompletionIntegers F))) ∧
      ∃ S : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), IsUnit S.det ∧
        S.map (fun x => (x : Fv F v)) =
          (b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) := by
  intro F E _ _ _ _ _ σ B d W r s hB hW v hv hu
  haveI := hB.unram
  haveI := hW.lat
  have h := hB.cm
  obtain ⟨τ⟩ := nonempty_emb h v hv
  obtain ⟨b₁, h₁⟩ := exists_isSplitBasis τ W.L h
  obtain ⟨b₂, h₂⟩ := exists_isSplitBasis (τ.comp σ) W.L h
  refine ⟨piW τ, piW (τ.comp σ), b₁, b₂, ⟨piW_cA τ σ, fun z => ?_, piW_algebraMap τ, piW_algebraMap _,
    fun z hz e₁ e₂ => ?_, fun x₁ x₂ => ?_, fun z => ?_⟩, ?_⟩
  · rw [piW_cA, comp_conj_conj h]
  · obtain ⟨y, rfl⟩ := (at_iff v z).1 hz
    rw [piW_apply, evT_liftT] at e₁ e₂
    rw [split_ext h τ (y := y) (z := 0) (by rw [e₁, map_zero]) (by rw [e₂, map_zero]), map_zero]
  · refine ⟨liftT E v ((splitAlgEquiv h τ).symm (x₁, x₂)), at_liftT v _, ?_, ?_⟩
    · rw [piW_apply, evT_liftT, splitProj_symm]
    · rw [piW_apply, evT_liftT, splitProj_comp_symm]
  · rw [mem_latAt_iff, mem_latLoc_iff_split τ h, h₁.mem_iff, h₂.mem_iff]
    rfl
  · have e : (incM F W.J).map (piW τ) = W.J.map τ := Matrix.ext fun i j => piW_inclR τ (W.J i j)
    rw [e]
    exact exists_gram hB hW hu τ h₁ h₂

end GlobalTheory.SplitDict
