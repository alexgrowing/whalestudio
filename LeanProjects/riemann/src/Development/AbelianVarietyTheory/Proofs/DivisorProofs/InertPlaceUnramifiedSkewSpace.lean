import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.XmApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeInertPlaceSelfDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentCoprimeAtGoodPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.InertGramSkew

section Sesq

variable {L : Type} [Field L]

def sesq (σL : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (x y : Fin n → L) : L :=
  ∑ k, ∑ l, x k * J k l * σL (y l)

variable (σL : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L)

theorem sesq_add_left (x₁ x₂ y : Fin n → L) : sesq σL J (x₁ + x₂) y = sesq σL J x₁ y + sesq σL J x₂ y := by
  simp only [sesq, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem sesq_add_right (x y₁ y₂ : Fin n → L) : sesq σL J x (y₁ + y₂) = sesq σL J x y₁ + sesq σL J x y₂ := by
  simp only [sesq, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem sesq_neg_left (x y : Fin n → L) : sesq σL J (-x) y = -sesq σL J x y := by
  simp only [sesq, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

theorem sesq_neg_right (x y : Fin n → L) : sesq σL J x (-y) = -sesq σL J x y := by
  simp only [sesq, Pi.neg_apply, map_neg, mul_neg, Finset.sum_neg_distrib]

theorem sesq_mem_of_closure (O : Subring L) (S : Set (Fin n → L))
    (hS : ∀ x ∈ S, ∀ y ∈ S, sesq σL J x y ∈ O) :
    ∀ x ∈ AddSubgroup.closure S, ∀ y ∈ AddSubgroup.closure S, sesq σL J x y ∈ O := by
  intro x hx
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy => exact hS x hx y hy
    | zero => simp [sesq]
    | add y₁ y₂ _ _ h₁ h₂ => rw [sesq_add_right]; exact add_mem h₁ h₂
    | neg y _ h => rw [sesq_neg_right]; exact neg_mem h
  | zero => intro y _; simp [sesq]
  | add x₁ x₂ _ _ h₁ h₂ => intro y hy; rw [sesq_add_left]; exact add_mem (h₁ y hy) (h₂ y hy)
  | neg x _ h => intro y hy; rw [sesq_neg_left]; exact neg_mem (h y hy)

theorem sesq_skew (hσσ : ∀ x, σL (σL x) = x) (hJ : ∀ k l, σL (J k l) = -J l k) (x y : Fin n → L) :
    σL (sesq σL J x y) = -sesq σL J y x := by
  simp only [sesq, map_sum, map_mul, hσσ, hJ]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end Sesq

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sesq_smul_map {L : Type} [Field L] (σ : E →ₐ[F] E) (σL : L →+* L) (φ : E →+* L)
    (hφσ : ∀ e, σL (φ e) = φ (σ e)) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (t t' : L) (y y' : Fin n → E) :
    sesq σL (J.map φ) (t • fun i => φ (y i)) (t' • fun i => φ (y' i)) = t * σL t' * φ (form σ J y y') := by
  simp only [sesq, form, Pi.smul_apply, smul_eq_mul, Matrix.map_apply, map_mul, hφσ, dotProduct, Matrix.mulVec,
    map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem gram_apply {L : Type} [Field L] (σL : L →+* L) (ι : L →+ AE F E) {n : ℕ} (P : GL (Fin n) L)
    (J : Matrix (Fin n) (Fin n) E) (i j : Fin n) :
    GlobalTheory.InertLocFrame.gram σL ι P J i j = sesq σL (GlobalTheory.InertLocFrame.tJ ι J)
      (fun k => (P : Matrix (Fin n) (Fin n) L) k i) (fun l => (P : Matrix (Fin n) (Fin n) L) l j) := by
  simp only [GlobalTheory.InertLocFrame.gram, sesq, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  exact Finset.sum_comm

def gens {L : Type} [Field L] (O : Subring L) (φ : E →+* L) {n : ℕ} (Lat : Submodule (𝓞 E) (Fin n → E)) :
    Set (Fin n → L) :=
  {z | ∃ t ∈ O, ∃ y ∈ Lat, z = t • fun i => φ (y i)}

theorem exists_mul_mem [Algebra.Unramified (𝓞 F) (𝓞 E)] (v : Pl F) (hv : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal)
    (e : E) (he : ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) :
    ∃ d : 𝓞 F, d ∉ v.asIdeal ∧ algebraMap F E (algebraMap (𝓞 F) F d) * e ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨d, hd, hdv⟩ := SetLike.not_le_iff_exists.mp hv
  refine ⟨d, hdv, GlobalTheory.InertSelfDual.mem_of_trace (F := F) _ fun a => ?_⟩
  have hco : ∀ c : 𝓞 F, ((algebraMap (𝓞 F) (𝓞 E) c : 𝓞 E) : E) = algebraMap F E (algebraMap (𝓞 F) F c) := by
    intro c
    rw [← IsScalarTower.algebraMap_apply (𝓞 F) F E, IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E]
  have hxd : Algebra.trace F E (e * (a : E)) ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))]
    intro b hb
    obtain ⟨b', rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hb
    rw [Algebra.traceForm_apply]
    have e1 : Algebra.trace F E (e * (a : E)) * algebraMap (𝓞 F) F b' =
        Algebra.trace F E (((algebraMap (𝓞 F) (𝓞 E) b' * a : 𝓞 E) : E) * e) := by
      rw [mul_comm, ← smul_eq_mul, ← map_smul, Algebra.smul_def]
      congr 1
      rw [show ((algebraMap (𝓞 F) (𝓞 E) b' * a : 𝓞 E) : E) = ((algebraMap (𝓞 F) (𝓞 E) b' : 𝓞 E) : E) * (a : E) from rfl, hco]
      ring
    rw [e1, Algebra.trace_trace]
    exact IsIntegrallyClosed.isIntegral_iff.mp (he _)
  have hmem : algebraMap (𝓞 F) F d * Algebra.trace F E (e * (a : E)) ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    have h1 : algebraMap (𝓞 F) F d ∈ ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) :=
      (FractionalIdeal.mem_coeIdeal _).2 ⟨d, hd, rfl⟩
    rw [coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)] at h1
    have h2 := FractionalIdeal.mul_mem_mul h1 hxd
    rwa [inv_mul_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F)))] at h2
  obtain ⟨y, hy⟩ := (FractionalIdeal.mem_one_iff _).1 hmem
  refine ⟨y, ?_⟩
  rw [hy, mul_assoc, ← Algebra.smul_def (algebraMap (𝓞 F) F d) (e * (a : E)), map_smul, smul_eq_mul]

theorem gram_skew_unimodular : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ (n r s : ℕ) (X : Spc F E n), X.IsSkew σ B r s →
    ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L) (ι : L →+ AE F E),
      Formalism.UG.IsUnramInv ϖ σL q → Odd q → (Valued.v δ = 1 ∧ σL δ = -δ) → Function.Injective ι → (∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) → (∀ x, ι (σL x) = cA σ (ι x)) →
      (∀ x, x ∈ Formalism.UG.intL L ↔ ι x ∈ AddSubgroup.closure {z : AE F E | ∃ a : AF F, At (evFin F v) a ∧
        evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}) →
      ∀ P : GL (Fin n) L, (∀ x : Fin n → L, (∀ i, x i ∈ Formalism.UG.intL L) ↔
        (fun i => ι (((P : Matrix (Fin n) (Fin n) L) *ᵥ x) i)) ∈ GlobalTheory.InertSph.latAt X v) →
      ∃ JT : GL (Fin n) L, JT ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) ∧
        (JT : Matrix (Fin n) (Fin n) L) = -δ⁻¹ • (GlobalTheory.InertLocFrame.gram σL ι P X.J)ᵀ ∧
        ∀ i j, σL ((JT : Matrix (Fin n) (Fin n) L) i j) = (JT : Matrix (Fin n) (Fin n) L) j i := by
  intro F E _ _ _ _ _ σ B hB v w hvw n r s X hX L _ _ ϖ σL q δ ι hUI hq hδ hinj himg hmul hσ hO P hP
  classical
  obtain ⟨hσσ, hσv, -⟩ := hUI
  obtain ⟨hδv, hδσ⟩ := hδ
  haveI := hB.unram
  have hvd : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal :=
    GlobalTheory.DiffCoprimeP.not_le_differentIdeal_of_psiUnr hB.std v (hB.inert v w hvw).2.2

  set a0 : AF F := GlobalTheory.LatVac.liftV v 1 with ha0
  have ha0at : At (evFin F v) a0 := GlobalTheory.LatVac.at_liftV v 1
  have ha0ev : evFin F v a0 = 1 := GlobalTheory.LatVac.evFin_liftV v 1
  have hfix : ∀ z : AE F E, At (evFin F v) z → a0 • z = z := fun z hz => by
    have h := hz (1 - a0) (by rw [map_sub, map_one, ha0ev, sub_self])
    rw [sub_smul, one_smul, sub_eq_zero] at h
    exact h.symm
  have hι1 : ∀ x, ι x * ι 1 = ι x := fun x => by rw [← hmul, mul_one]
  have hat_img : ∀ x, At (evFin F v) (ι x) := fun x => (himg _).2 ⟨x, rfl⟩
  have hat_mul : ∀ z y : AE F E, At (evFin F v) z → At (evFin F v) (z * y) := fun z y hz u hu => by
    rw [← smul_mul_assoc, hz u hu, zero_mul]
  have hat_smul : ∀ (a : AF F) (y : AE F E), At (evFin F v) a → At (evFin F v) (a • y) := fun a y ha u hu => by
    rw [smul_smul, ← smul_eq_mul, ha u hu, zero_smul]

  obtain ⟨φ, hφ⟩ : ∃ φ : E →+* L, ∀ e, ι (φ e) = ι 1 * inclR (F := F) (AF F) e := by
    have hpre : ∀ e, ι (GlobalTheory.InertLocFrame.pre ι (ι 1 * inclR (F := F) (AF F) e)) = ι 1 * inclR (F := F) (AF F) e :=
      fun e => GlobalTheory.InertLocFrame.pre_spec ι ((himg _).1 (hat_mul _ _ (hat_img 1)))
    have h11 : ι 1 * ι 1 = ι 1 := hι1 1
    have hone : GlobalTheory.InertLocFrame.pre ι (ι 1 * inclR (F := F) (AF F) (1 : E)) = 1 :=
      hinj (by rw [hpre, map_one (inclR (F := F) (AF F)), mul_one])
    have hzero : GlobalTheory.InertLocFrame.pre ι (ι 1 * inclR (F := F) (AF F) (0 : E)) = 0 :=
      hinj (by rw [hpre, map_zero (inclR (F := F) (AF F)), mul_zero, map_zero ι])
    have hadd : ∀ e₁ e₂ : E, GlobalTheory.InertLocFrame.pre ι (ι 1 * inclR (F := F) (AF F) (e₁ + e₂)) =
        GlobalTheory.InertLocFrame.pre ι (ι 1 * inclR (F := F) (AF F) e₁) + GlobalTheory.InertLocFrame.pre ι (ι 1 * inclR (F := F) (AF F) e₂) :=
      fun e₁ e₂ => hinj (by rw [hpre, map_add ι, hpre, hpre, map_add (inclR (F := F) (AF F)), mul_add])
    have hmul' : ∀ e₁ e₂ : E, GlobalTheory.InertLocFrame.pre ι (ι 1 * inclR (F := F) (AF F) (e₁ * e₂)) =
        GlobalTheory.InertLocFrame.pre ι (ι 1 * inclR (F := F) (AF F) e₁) * GlobalTheory.InertLocFrame.pre ι (ι 1 * inclR (F := F) (AF F) e₂) :=
      fun e₁ e₂ => hinj (by rw [hmul, hpre, hpre, hpre, map_mul (inclR (F := F) (AF F)), mul_mul_mul_comm, h11])
    exact ⟨⟨⟨⟨fun e => GlobalTheory.InertLocFrame.pre ι (ι 1 * inclR (F := F) (AF F) e), hone⟩, hmul'⟩, hzero, hadd⟩, hpre⟩
  have hφa : ∀ e, ι (φ e) = a0 • inclR (F := F) (AF F) e := by
    intro e
    obtain ⟨x, hx⟩ := (himg (a0 • inclR (F := F) (AF F) e)).1 (hat_smul _ _ ha0at)
    rw [hφ]
    calc ι 1 * inclR (F := F) (AF F) e = a0 • (ι 1 * inclR (F := F) (AF F) e) :=
          (hfix _ (hat_mul _ _ (hat_img 1))).symm
      _ = (a0 • inclR (F := F) (AF F) e) * ι 1 := by rw [smul_mul_assoc, mul_comm (ι 1)]
      _ = ι x * ι 1 := by rw [hx]
      _ = ι x := hι1 x
      _ = a0 • inclR (F := F) (AF F) e := hx
  have hσint : ∀ x ∈ Formalism.UG.intL L, σL x ∈ Formalism.UG.intL L := fun x hx => by
    have h : Valued.v x ≤ 1 := hx
    show Valued.v (σL x) ≤ 1
    rw [hσv]; exact h
  have hφσ : ∀ e, σL (φ e) = φ (σ e) := fun e => hinj (by
    rw [hσ, hφa, hφa, map_smul, GlobalTheory.InertSelfDual.cA_inclR])
  have hφO : ∀ o : 𝓞 E, φ (algebraMap (𝓞 E) E o) ∈ Formalism.UG.intL L := fun o => (hO _).2 (by
    rw [hφa]
    exact AddSubgroup.subset_closure ⟨a0, ha0at, by rw [ha0ev]; exact one_mem _, o, rfl⟩)
  have hφdual : ∀ e : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) → φ e ∈ Formalism.UG.intL L := by
    intro e he
    obtain ⟨d, hdv, o, ho⟩ := exists_mul_mem v hvd e he
    have hd0 : algebraMap (𝓞 F) F d ≠ 0 := by
      intro h0
      apply hdv
      rw [(FaithfulSMul.algebraMap_injective (𝓞 F) F) (h0.trans (map_zero _).symm)]
      exact zero_mem _
    have he' : e = algebraMap F E (algebraMap (𝓞 F) F d)⁻¹ * algebraMap (𝓞 E) E o := by
      rw [ho, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hd0, map_one, one_mul]
    rw [he', map_mul]
    refine mul_mem ?_ (hφO o)
    apply (hO _).2
    rw [hφa]
    refine AddSubgroup.subset_closure ⟨a0 * algebraMap F (AF F) (algebraMap (𝓞 F) F d)⁻¹, fun u hu => ?_, ?_, 1, ?_⟩
    · rw [← smul_mul_assoc, ha0at u hu, zero_mul]
    · rw [map_mul, ha0ev, one_mul, AlgHom.commutes, HeightOneSpectrum.mem_adicCompletionIntegers]
      apply le_of_eq
      have hvF : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F d)⁻¹) =
          v.valuation F (algebraMap (𝓞 F) F d)⁻¹ := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 F) v _
      refine hvF.trans ?_
      rw [map_inv₀, HeightOneSpectrum.valuation_of_algebraMap,
        HeightOneSpectrum.intValuation_eq_one_iff.mpr hdv, inv_one]
    · rw [Algebra.algebraMap_eq_smul_one (A := E) (algebraMap (𝓞 F) F d)⁻¹, GlobalTheory.InertSelfDual.inclR_smul, smul_smul]
      first | rfl | simp
  have hlift : ∀ a : AF F, At (evFin F v) a → evFin F v a ∈ v.adicCompletionIntegers F →
      ∃ t ∈ Formalism.UG.intL L, ι t = a • (1 : AE F E) := by
    intro a ha hai
    obtain ⟨t, ht⟩ := (himg _).1 (hat_smul a 1 ha)
    refine ⟨t, (hO t).2 ?_, ht⟩
    rw [ht]
    exact AddSubgroup.subset_closure ⟨a, ha, hai, 1, by simp⟩

  set Pm : Matrix (Fin n) (Fin n) L := (P : Matrix (Fin n) (Fin n) L) with hPm
  set Q : Matrix (Fin n) (Fin n) L := ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hQ
  have hPQ : Pm * Q = 1 := P.mul_inv
  have hQP : Q * Pm = 1 := P.inv_mul
  have hΛ : ∀ x : Fin n → L, (fun i => ι (x i)) ∈ GlobalTheory.InertSph.latAt X v → ∀ i, (Q *ᵥ x) i ∈ Formalism.UG.intL L :=
    fun x hx => (hP (Q *ᵥ x)).2 (by rwa [Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec])
  have hφL : ∀ y ∈ X.L, (fun i => ι (φ (y i))) ∈ GlobalTheory.InertSph.latAt X v := by
    intro y hy
    have e : (fun i => ι (φ (y i))) = a0 • fun i => inclR (F := F) (AF F) (y i) := by
      funext i; rw [hφa]; rfl
    rw [e]
    exact AddSubgroup.subset_closure ⟨a0, ha0at, by rw [ha0ev]; exact one_mem _, y, hy, rfl⟩
  have hA' : ∀ x : Fin n → L, (fun i => ι (x i)) ∈ GlobalTheory.InertSph.latAt X v →
      x ∈ AddSubgroup.closure (gens (Formalism.UG.intL L) φ X.L) := by
    have key : ∀ z ∈ GlobalTheory.InertSph.latAt X v, ∃ x ∈ AddSubgroup.closure (gens (Formalism.UG.intL L) φ X.L),
        (fun i => ι (x i)) = z := by
      intro z hz
      unfold GlobalTheory.InertSph.latAt at hz
      induction hz using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, ha, hai, y, hy, rfl⟩ := hz
        obtain ⟨t, ht, hta⟩ := hlift a ha hai
        refine ⟨t • fun i => φ (y i), AddSubgroup.subset_closure ⟨t, ht, y, hy, rfl⟩, ?_⟩
        funext i
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [hmul, hφ, ← mul_assoc, hι1, hta, smul_mul_assoc, one_mul]
      | zero => exact ⟨0, zero_mem _, by funext i; simp⟩
      | add z₁ z₂ _ _ h₁ h₂ =>
        obtain ⟨x₁, hx₁, rfl⟩ := h₁
        obtain ⟨x₂, hx₂, rfl⟩ := h₂
        exact ⟨x₁ + x₂, add_mem hx₁ hx₂, by funext i; simp⟩
      | neg z _ h =>
        obtain ⟨x, hx, rfl⟩ := h
        exact ⟨-x, neg_mem hx, by funext i; simp⟩
    intro x hx
    obtain ⟨x', hx', e⟩ := key _ hx
    have : x' = x := funext fun i => hinj (congrFun e i)
    rwa [← this]

  have hsesq : ∀ x ∈ AddSubgroup.closure (gens (Formalism.UG.intL L) φ X.L),
      ∀ y ∈ AddSubgroup.closure (gens (Formalism.UG.intL L) φ X.L), sesq σL (X.J.map φ) x y ∈ Formalism.UG.intL L := by
    refine sesq_mem_of_closure σL _ _ _ ?_
    rintro _ ⟨t, ht, y, hy, rfl⟩ _ ⟨t', ht', y', hy', rfl⟩
    rw [sesq_smul_map σ σL φ hφσ]
    exact mul_mem (mul_mem ht (hσint _ ht')) (hφdual _ ((hX.dual y).1 hy y' hy'))
  have htJ : GlobalTheory.InertLocFrame.tJ ι X.J = X.J.map φ := by
    ext i j
    apply hinj
    rw [Matrix.map_apply, hφ]
    exact GlobalTheory.InertLocFrame.pre_spec ι ((himg _).1 (hat_mul _ _ (hat_img 1)))
  set G := GlobalTheory.InertLocFrame.gram σL ι P X.J with hGdef
  have hGe : ∀ i j, G i j = sesq σL (X.J.map φ) (fun k => Pm k i) (fun l => Pm l j) := fun i j => by
    rw [hGdef, gram_apply, htJ]
  have hcol : ∀ i, (fun k => Pm k i) ∈ AddSubgroup.closure (gens (Formalism.UG.intL L) φ X.L) := by
    intro i
    apply hA'
    have h := (hP (Pi.single i 1)).1 (fun k => by
      rcases eq_or_ne k i with rfl | hki
      · rw [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne hki]; exact zero_mem _)
    have e : Pm *ᵥ Pi.single i 1 = fun k => Pm k i := by
      funext k; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [e] at h
    exact h
  have hGint : ∀ i j, G i j ∈ Formalism.UG.intL L := fun i j => by
    rw [hGe]; exact hsesq _ (hcol i) _ (hcol j)
  have hJskew : ∀ k l, σL (X.J.map φ k l) = -(X.J.map φ l k) := fun k l => by
    rw [Matrix.map_apply, Matrix.map_apply, hφσ, hX.skew l k, map_neg]
  have hGskew : ∀ i j, σL (G j i) = -G i j := fun i j => by
    rw [hGe, hGe]; exact sesq_skew σL _ hσσ hJskew _ _

  obtain ⟨k, S, T, hS, hT, hTS⟩ := GlobalTheory.InertSelfDual.exists_formFrame σ X.J
    (GlobalTheory.InertSelfDual.det_ne_zero_of_skew σ B hX) X.L hX.lat (fun y hy => (hX.dual y).2 fun x hx o => by
      obtain ⟨c, hc⟩ := hy x hx
      rw [← hc]
      exact Algebra.isIntegral_trace ((RingOfIntegers.isIntegral_coe o).mul (RingOfIntegers.isIntegral_coe c)))
  have hcolL : ∀ M : Matrix (Fin n) (Fin k) E, (∀ j, (fun i => M i j) ∈ X.L) →
      ∀ i j, (Q * M.map φ) i j ∈ Formalism.UG.intL L := by
    intro M hM i j
    have h := hΛ _ (hφL _ (hM j)) i
    convert h using 1
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hid : T.map φ * (X.J.map φ * (S.map φ).map σL)ᵀ = 1 := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) E => M.map φ) hTS
    simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_one _ (map_zero φ) (map_one φ)] at h
    have e : (S.map φ).map σL = (S.map σ).map φ := by
      ext i j; simp [hφσ]
    rw [e]; exact h
  have hSC : S.map φ = Pm * (Q * S.map φ) := by rw [← Matrix.mul_assoc, hPQ, Matrix.one_mul]
  have hTA : T.map φ = Pm * (Q * T.map φ) := by rw [← Matrix.mul_assoc, hPQ, Matrix.one_mul]
  have hKG : (Q * T.map φ) * ((Q * S.map φ).map σL)ᵀ * Gᵀ = 1 := by
    have hid' := hid
    rw [hSC, hTA, Matrix.map_mul] at hid'
    rw [hGdef, GlobalTheory.InertLocFrame.gram, htJ]
    calc _ = Q * (Pm * (Q * T.map φ) * (X.J.map φ * (Pm.map σL * (Q * S.map φ).map σL))ᵀ) * Pm := by
          simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Q Pm, hQP, Matrix.one_mul]
      _ = 1 := by rw [hid', Matrix.mul_one, hQP]
  have hGK : Gᵀ * ((Q * T.map φ) * ((Q * S.map φ).map σL)ᵀ) = 1 := mul_eq_one_comm.mp hKG
  have hKint : ∀ i j, ((Q * T.map φ) * ((Q * S.map φ).map σL)ᵀ) i j ∈ Formalism.UG.intL L := fun i j => by
    rw [Matrix.mul_apply]
    exact sum_mem fun l _ => mul_mem (hcolL T hT i l) (by
      rw [Matrix.transpose_apply, Matrix.map_apply]; exact hσint _ (hcolL S hS j l))

  have hδ0 : δ ≠ 0 := fun h => by rw [h, map_zero] at hδv; exact zero_ne_one hδv
  have hδint : δ ∈ Formalism.UG.intL L := by
    show Valued.v δ ≤ 1
    exact le_of_eq hδv
  have hδi : δ⁻¹ ∈ Formalism.UG.intL L := by
    show Valued.v δ⁻¹ ≤ 1
    exact le_of_eq (by rw [map_inv₀, hδv, inv_one])

  have hprod : (-δ⁻¹ • Gᵀ) * (-δ • ((Q * T.map φ) * ((Q * S.map φ).map σL)ᵀ)) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hGK, neg_mul_neg, inv_mul_cancel₀ hδ0, one_smul]
  have hprod' : (-δ • ((Q * T.map φ) * ((Q * S.map φ).map σL)ᵀ)) * (-δ⁻¹ • Gᵀ) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hKG, neg_mul_neg, mul_inv_cancel₀ hδ0, one_smul]
  have hM1 : ∀ i j, (-δ⁻¹ • Gᵀ) i j ∈ Formalism.UG.intL L := fun i j => by
    rw [Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul]
    exact mul_mem (neg_mem hδi) (hGint j i)
  have hM2 : ∀ i j, (-δ • ((Q * T.map φ) * ((Q * S.map φ).map σL)ᵀ)) i j ∈ Formalism.UG.intL L := fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul]
    exact mul_mem (neg_mem hδint) (hKint i j)
  let g1 : Matrix (Fin n) (Fin n) (Formalism.UG.intL L) := fun i j => ⟨_, hM1 i j⟩
  let g2 : Matrix (Fin n) (Fin n) (Formalism.UG.intL L) := fun i j => ⟨_, hM2 i j⟩
  have hmap1 : (Formalism.UG.intL L).subtype.mapMatrix g1 = -δ⁻¹ • Gᵀ := by ext i j; rfl
  have hmap2 : (Formalism.UG.intL L).subtype.mapMatrix g2 = -δ • ((Q * T.map φ) * ((Q * S.map φ).map σL)ᵀ) := by
    ext i j; rfl
  have hinjM : Function.Injective ((Formalism.UG.intL L).subtype.mapMatrix :
      Matrix (Fin n) (Fin n) (Formalism.UG.intL L) → Matrix (Fin n) (Fin n) L) := fun a b h => by
    ext i j; exact congrFun (congrFun h i) j
  have h12 : g1 * g2 = 1 := hinjM (by rw [map_mul, hmap1, hmap2, map_one]; exact hprod)
  have h21 : g2 * g1 = 1 := hinjM (by rw [map_mul, hmap1, hmap2, map_one]; exact hprod')
  have hJTm : ((Formalism.UG.bc (Formalism.UG.intL L).subtype ⟨g1, g2, h12, h21⟩ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      -δ⁻¹ • Gᵀ := hmap1
  refine ⟨Formalism.UG.bc (Formalism.UG.intL L).subtype ⟨g1, g2, h12, h21⟩, ⟨⟨g1, g2, h12, h21⟩, rfl⟩, hJTm, fun i j => ?_⟩
  rw [hJTm]
  simp only [Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, map_mul, map_neg, map_inv₀, hδσ, hGskew]
  rw [inv_neg]
  ring

end GlobalTheory.InertGramSkew
