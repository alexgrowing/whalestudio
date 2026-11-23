import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerSetEqRangeNormalFormStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicLeviEmbeddingHomomorphismProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LintegralInvEqOfBiInvariantMatGroup

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.StabHaar

theorem exists_mp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] [AddCommGroup F] [Module ℝ F] (ι : E →ₗ[ℝ] F)
    (hι : Function.Injective ι) (N : Module.End ℝ F) (hN : IsNilpotent N) (h : ∀ x, N (ι x) ∈ Set.range ι) (x₀ : E) :
    ∃ T : E → E, MeasurePreserving T μ μ ∧ ∀ x, ι (T x) = ι x₀ + (ι x + N (ι x)) := by
  obtain ⟨g, hg⟩ := ι.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hι)
  let M : Module.End ℝ E := g ∘ₗ N ∘ₗ ι
  have hM : ∀ x, ι (M x) = N (ι x) := fun x => by
    obtain ⟨y, hy⟩ := h x
    have : g (ι y) = y := LinearMap.congr_fun hg y
    simp only [M, LinearMap.comp_apply, ← hy, this]
  have hp : ∀ (n : ℕ) x, ι ((M ^ n) x) = (N ^ n) (ι x) := fun n => by
    induction n with
    | zero => simp
    | succ n ih => intro x; rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, hM, ih]
  have hMn : IsNilpotent M := by
    obtain ⟨n, hn⟩ := hN
    exact ⟨n, LinearMap.ext fun x => hι (by rw [hp, hn]; simp)⟩
  have hd : LinearMap.det (1 + M) = 1 := by
    have h1 := hMn.neg.charpoly_eq_X_pow_finrank
    have h2 := LinearMap.eval_charpoly (-M) 1
    rw [h1] at h2
    simpa using h2.symm
  have hm : MeasurePreserving (1 + M : Module.End ℝ E) μ μ := by
    refine ⟨(LinearMap.continuous_of_finiteDimensional _).measurable, ?_⟩
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar μ (by rw [hd]; exact one_ne_zero), hd]
    simp
  refine ⟨fun x => x₀ + (1 + M) x, (measurePreserving_add_left μ x₀).comp hm, fun x => ?_⟩
  simp [hM]

variable {r : ℕ}

theorem nilp_of_strict (A : Matrix (Fin r) (Fin r) ℂ) (hA : ∀ a b, ¬ a < b → A a b = 0) : IsNilpotent A := by
  have : ∀ (n : ℕ) (a b : Fin r), b.val < a.val + n → (A ^ n) a b = 0 := fun n => by
    induction n with
    | zero => intro a b h; rw [pow_zero, Matrix.one_apply_ne]; rintro rfl; omega
    | succ n ih =>
      intro a b h
      rw [pow_succ, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hc : c < b
      · rw [ih a c (by have : c.val < b.val := hc; omega), zero_mul]
      · rw [hA c b hc, mul_zero]
  exact ⟨r, Matrix.ext fun a b => this r a b (by omega)⟩

def strIn (β : Fin r → ℕ) : (UTin β → ℂ) →ₗ[ℝ] Matrix (Fin r) (Fin r) ℂ where
  toFun x := Matrix.of fun a b => if h : a < b ∧ β a = β b then x ⟨⟨(a, b), h.1⟩, h.2⟩ else 0
  map_add' x y := by ext a b; simp only [Matrix.add_apply, Matrix.of_apply]; split_ifs <;> simp
  map_smul' c x := by ext a b; simp only [Matrix.smul_apply, Matrix.of_apply]; split_ifs <;> simp

theorem strIn_apply (β : Fin r → ℕ) (x : UTin β → ℂ) (a b : Fin r) :
    strIn β x a b = if h : a < b ∧ β a = β b then x ⟨⟨(a, b), h.1⟩, h.2⟩ else 0 := rfl

theorem strIn_zero (β : Fin r → ℕ) (x : UTin β → ℂ) {a b : Fin r} (h : ¬ (a < b ∧ β a = β b)) : strIn β x a b = 0 :=
  dif_neg h

theorem upperIn_eq (β : Fin r → ℕ) (x : UTin β → ℂ) : upperIn β x = 1 + strIn β x := by
  ext a b
  simp only [upperIn, upper, Matrix.add_apply, strIn_apply, Matrix.one_apply]
  by_cases h : a < b
  · by_cases h' : β a = β b <;> simp [h, h', h.ne]
  · simp [h]

theorem strIn_inj (β : Fin r → ℕ) : Function.Injective (strIn β) := fun x y h => by
  funext p
  have := congrFun (congrFun h p.1.1.1) p.1.1.2
  rwa [strIn_apply, strIn_apply, dif_pos ⟨p.1.2, p.2⟩, dif_pos ⟨p.1.2, p.2⟩] at this

theorem mem_strIn (β : Fin r → ℕ) (A : Matrix (Fin r) (Fin r) ℂ) (hA : ∀ a b, ¬ (a < b ∧ β a = β b) → A a b = 0) :
    A ∈ Set.range (strIn β) := by
  refine ⟨fun p => A p.1.1.1 p.1.1.2, ?_⟩
  ext a b
  rw [strIn_apply]
  split_ifs with h
  · rfl
  · exact (hA a b h).symm

theorem strIn_nilp (β : Fin r → ℕ) (x : UTin β → ℂ) : IsNilpotent (strIn β x) :=
  nilp_of_strict _ fun _ _ h => strIn_zero β x fun h' => h h'.1

theorem strIn_mul (β : Fin r → ℕ) (x y : UTin β → ℂ) : strIn β x * strIn β y ∈ Set.range (strIn β) := by
  refine mem_strIn β _ fun a b h => ?_
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases h1 : a < c ∧ β a = β c
  · rw [strIn_zero β y fun h2 => h ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩, mul_zero]
  · rw [strIn_zero β x h1, zero_mul]

theorem upperIn_left (β : Fin r → ℕ) (x₀ : UTin β → ℂ) : ∃ T : (UTin β → ℂ) → (UTin β → ℂ),
    MeasurePreserving T volume volume ∧ ∀ x, upperIn β x₀ * upperIn β x = upperIn β (T x) := by
  obtain ⟨T, hT, h⟩ := exists_mp volume (strIn β) (strIn_inj β) (LinearMap.mulLeft ℝ (strIn β x₀))
    ((LinearMap.isNilpotent_mulLeft_iff _ _).2 (strIn_nilp β x₀)) (fun x => strIn_mul β x₀ x) x₀
  refine ⟨T, hT, fun x => ?_⟩
  simp only [upperIn_eq, h, LinearMap.mulLeft_apply]
  noncomm_ring

theorem upperIn_right (β : Fin r → ℕ) (x₀ : UTin β → ℂ) : ∃ T : (UTin β → ℂ) → (UTin β → ℂ),
    MeasurePreserving T volume volume ∧ ∀ x, upperIn β x * upperIn β x₀ = upperIn β (T x) := by
  obtain ⟨T, hT, h⟩ := exists_mp volume (strIn β) (strIn_inj β) (LinearMap.mulRight ℝ (strIn β x₀))
    ((LinearMap.isNilpotent_mulRight_iff _ _).2 (strIn_nilp β x₀)) (fun x => strIn_mul β x x₀) x₀
  refine ⟨T, hT, fun x => ?_⟩
  simp only [upperIn_eq, h, LinearMap.mulRight_apply]
  noncomm_ring

variable {k : ℕ}

def gm (B B' : Matrix (Fin r) (Fin (k + 1)) ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => herm (Hb k) (B' b) (B a)

theorem gm_eq (B B' : Matrix (Fin r) (Fin (k + 1)) ℂ) : gm B B' = Bᴴᵀ * Hb k * B'ᵀ := by
  ext a b
  simp only [gm, Matrix.of_apply, Rad.herm_Hb, Matrix.mul_apply, Rad.Hb_apply, Matrix.transpose_apply,
    Matrix.conjTranspose_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp [mul_assoc]

theorem gm_conj (v : Matrix (Fin r) (Fin r) ℂ) (B : Matrix (Fin r) (Fin (k + 1)) ℂ) :
    gm (vᴴᵀ * B) (vᴴᵀ * B) = v * gm B B * vᴴ := by
  have : (vᴴᵀ)ᴴᵀ = v := by ext a b; simp
  simp only [gm_eq, Matrix.conjTranspose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, this, Matrix.mul_assoc]

theorem unitary_embed_parabolic_commute (v : Matrix (Fin r) (Fin r) ℂ) (B B' : Fin r → Fin (k + 1) → ℂ) (S S' : Matrix (Fin r) (Fin r) ℂ)
    (e1 : ∀ a i, B' a i = ∑ c, star (v a c) * B c i)
    (e2 : ∀ a b, ∑ c, v a c * (S c b - herm (Hb k) (B b) (B c) / 2) =
      ∑ d, (S' a d - herm (Hb k) (B' d) (B' a) / 2) * star (v⁻¹ b d))
    (e3 : ∀ i b, B b i = ∑ d, B' d i * star (v⁻¹ b d)) :
    uEmb k r v * pEl k r B S = pEl k r B' S' * uEmb k r v := by
  have em : ∀ a j, uEmb k r v (eI k r a) (wI k r j) = 0 := UEmb.u_em v
  have me : ∀ a j, uEmb k r v (wI k r j) (eI k r a) = 0 := fun a j => UEmb.u_me v a j
  have mm : ∀ i j, uEmb k r v (wI k r i) (wI k r j) = if i = j then 1 else 0 := UEmb.u_mm v
  have ms : ∀ a j, uEmb k r v (wI k r j) (esI k r a) = 0 := fun a j => UEmb.u_ms v a j
  have sm : ∀ a j, uEmb k r v (esI k r a) (wI k r j) = 0 := UEmb.u_sm v
  ext x y
  rw [Matrix.mul_apply, Matrix.mul_apply, Rad.sum3, Rad.sum3]
  induction x using Rad.cases3 <;> induction y using Rad.cases3 <;>
    simp only [Rad.pEl_ee, Rad.pEl_ew, Rad.pEl_es, Rad.pEl_we, Rad.pEl_ww, Rad.pEl_ws, Rad.pEl_se, Rad.pEl_sw, Rad.pEl_ss,
      UEmb.u_ee, UEmb.u_es, UEmb.u_se, UEmb.u_ss, em, me, mm, ms, sm, mul_zero, zero_mul, Finset.sum_const_zero,
      add_zero, zero_add, mul_ite, ite_mul, mul_one, one_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · simp [e1, Finset.sum_mul, mul_assoc]
  · exact e2 _ _
  · exact e3 _ _

theorem uEmb_pEl (v : Matrix (Fin r) (Fin r) ℂ) (hv : IsUnit v.det) (B : Matrix (Fin r) (Fin (k + 1)) ℂ)
    (S : Matrix (Fin r) (Fin r) ℂ) :
    uEmb k r v * pEl k r B S = pEl k r (vᴴᵀ * B : Matrix _ _ ℂ) (v * S * vᴴ) * uEmb k r v := by
  have h1 : vᴴ * (v⁻¹)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul v hv, Matrix.conjTranspose_one]
  have h2 : v * (S - (2⁻¹ : ℂ) • gm B B) =
      (v * S * vᴴ - (2⁻¹ : ℂ) • gm (vᴴᵀ * B) (vᴴᵀ * B)) * (v⁻¹)ᴴ := by
    rw [gm_conj, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc _ vᴴ, Matrix.mul_assoc _ vᴴ, h1]
    simp [Matrix.mul_sub]
  have h3 : Bᵀ = (vᴴᵀ * B)ᵀ * (v⁻¹)ᴴ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, h1, Matrix.mul_one]
  refine unitary_embed_parabolic_commute v _ _ _ _ (fun a i => rfl) (fun a b => ?_) fun i b => congrFun (congrFun h3 i) b
  have := congrFun (congrFun h2 a) b
  rw [Matrix.mul_apply, Matrix.mul_apply] at this
  simpa only [Matrix.sub_apply, Matrix.smul_apply, gm, Matrix.of_apply, smul_eq_mul, Matrix.conjTranspose_apply,
    inv_mul_eq_div] using this

abbrev Amb (k r : ℕ) := Matrix (Fin r) (Fin (k + 1)) ℂ × Matrix (Fin r) (Fin r) ℂ

def topL (k r j : ℕ) : PTop k r j →ₗ[ℝ] Amb k r where
  toFun q := (Matrix.of fun a => if h : j ≤ a.val then q.1 ⟨a, h⟩ else 0,
    skewM (fun p => if h : j ≤ p.1.1.val then q.2.1 ⟨p, h⟩ else 0) (fun a => if h : j ≤ a.val then q.2.2 ⟨a, h⟩ else 0))
  map_add' x y := by
    ext a b
    · simp only [Prod.fst_add, Matrix.add_apply, Matrix.of_apply]; split_ifs <;> simp
    · simp only [Prod.snd_add, Matrix.add_apply, skewM]; split_ifs <;> simp <;> ring
  map_smul' c x := by
    ext a b
    · simp only [Prod.smul_fst, Matrix.smul_apply, Matrix.of_apply, RingHom.id_apply]; split_ifs <;> simp
    · simp only [Prod.smul_snd, Matrix.smul_apply, skewM, RingHom.id_apply]; split_ifs <;> simp <;> ring

variable {j : ℕ}

theorem pTop_eq (q : PTop k r j) : pTop k r j q = pEl k r (topL k r j q).1 (topL k r j q).2 := rfl

theorem topL_fst (q : PTop k r j) (a : Fin r) : (topL k r j q).1 a = if h : j ≤ a.val then q.1 ⟨a, h⟩ else 0 := rfl

theorem topL_snd (q : PTop k r j) : (topL k r j q).2 =
  skewM (fun p => if h : j ≤ p.1.1.val then q.2.1 ⟨p, h⟩ else 0) (fun a => if h : j ≤ a.val then q.2.2 ⟨a, h⟩ else 0) := rfl

theorem topL_inj : Function.Injective (topL k r j) := fun x y h => by
  refine Prod.ext (funext fun a => ?_) (Prod.ext (funext fun p => ?_) (funext fun a => ?_))
  · have := congrFun (congrArg Prod.fst h) a.1
    rwa [topL_fst, topL_fst, dif_pos a.2, dif_pos a.2] at this
  · have := congrFun (congrFun (congrArg Prod.snd h) p.1.1.1) p.1.1.2
    simpa [topL_snd, skewM, p.1.2, p.2] using this
  · have := congrFun (congrFun (congrArg Prod.snd h) a.1) a.1
    simpa [topL_snd, skewM, a.2] using this

def TopC (j : ℕ) (y : Amb k r) : Prop :=
  (∀ a : Fin r, a.val < j → y.1 a = 0) ∧ y.2ᴴ = -y.2 ∧ ∀ a b : Fin r, a.val < j → y.2 a b = 0

theorem topC_topL (q : PTop k r j) : TopC j (topL k r j q) := by
  refine ⟨fun a ha => by rw [topL_fst, dif_neg (by omega)], Rad.skewM_skew _ _, fun a b ha => ?_⟩
  simp only [topL_snd, skewM]
  split_ifs with h1 h2 h3 h4 h5
  · omega
  · rfl
  · have : b.val < a.val := h3
    omega
  · simp
  · omega
  · simp

theorem TopC.mem {y : Amb k r} (h : TopC j y) : y ∈ Set.range (topL k r j) := by
  obtain ⟨p, hp, -⟩ := Rad.skewM_unique y.2 h.2.1
  refine ⟨(fun a => y.1 a.1, fun q => p.1 q.1, fun a => p.2 a.1), Prod.ext ?_ ?_⟩
  · funext a
    rw [topL_fst]
    split_ifs with ha
    · rfl
    · exact (h.1 a (by omega)).symm
  · rw [topL_snd, hp]
    congr 1
    · funext q
      split_ifs with ha
      · rfl
      · have := h.2.2 q.1.1 q.1.2 (by omega)
        rw [hp] at this
        simpa [skewM, q.2] using this.symm
    · funext a
      split_ifs with ha
      · rfl
      · have := h.2.2 a a (by omega)
        rw [hp] at this
        symm; simpa [skewM] using this

instance : (volume : Measure (PTop k r j)).IsAddHaarMeasure :=
  haveI : (volume : Measure ({a : Fin r // j ≤ a.val} → Fin (k + 1) → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (({p : UT r // j ≤ p.1.1.val} → ℂ) × ({a : Fin r // j ≤ a.val} → ℝ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  Measure.prod.instIsAddHaarMeasure _ _

def hm (B : Matrix (Fin r) (Fin (k + 1)) ℂ) : Matrix (Fin r) (Fin (k + 1)) ℂ →ₗ[ℝ] Matrix (Fin r) (Fin r) ℂ where
  toFun B' := (2⁻¹ : ℂ) • (gm B' B - gm B B')
  map_add' x y := by
    simp only [gm_eq, Matrix.conjTranspose_add, Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, ← smul_add]
    congr 1; abel
  map_smul' c x := by
    simp only [gm_eq, Matrix.conjTranspose_smul, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, star_trivial,
      RingHom.id_apply, ← smul_sub]
    exact smul_comm _ _ _

theorem hm_apply (B B' : Matrix (Fin r) (Fin (k + 1)) ℂ) (a b : Fin r) :
    hm B B' a b = (herm (Hb k) (B b) (B' a) - herm (Hb k) (B' b) (B a)) / 2 := by
  show (2⁻¹ : ℂ) * (herm (Hb k) (B b) (B' a) - herm (Hb k) (B' b) (B a)) = _
  ring

theorem pEl_mul' (y y' : Amb k r) :
    pEl k r y.1 y.2 * pEl k r y'.1 y'.2 = pEl k r (y.1 + y'.1) (y.2 + y'.2 + hm y.1 y'.1) := by
  refine (Rad.pEl_mul _ _ _ _).trans ?_
  congr 2
  ext a b
  exact (hm_apply _ _ a b).symm

theorem hm_swap (B B' : Matrix (Fin r) (Fin (k + 1)) ℂ) : hm B B' = (-1 : ℝ) • hm B' B := by
  ext a b
  rw [neg_one_smul, Matrix.neg_apply, hm_apply, hm_apply]; ring

theorem pTop_shear (c : ℝ) (q₀ : PTop k r j) : ∃ T : PTop k r j → PTop k r j, MeasurePreserving T volume volume ∧
    ∀ q, topL k r j (T q) = ((topL k r j q₀).1 + (topL k r j q).1,
      (topL k r j q₀).2 + (topL k r j q).2 + c • hm (topL k r j q₀).1 (topL k r j q).1) := by
  let N : Module.End ℝ (Amb k r) := LinearMap.inr ℝ _ _ ∘ₗ (c • hm (topL k r j q₀).1) ∘ₗ LinearMap.fst ℝ _ _
  have hN : ∀ y, N y = (0, c • hm (topL k r j q₀).1 y.1) := fun _ => rfl
  obtain ⟨T, hT, h⟩ := exists_mp volume (topL k r j) topL_inj N
    ⟨2, LinearMap.ext fun y => by rw [pow_two, Module.End.mul_apply, hN, hN]; simp⟩ (fun q => TopC.mem (by
      rw [hN]
      refine ⟨fun a _ => rfl, ?_, fun a b ha => ?_⟩
      · ext a b
        simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Matrix.smul_apply, hm_apply, star_smul, star_trivial,
          star_div₀, star_sub, Rad.herm_star, star_ofNat, Complex.real_smul]
        simp [Rad.herm_star]
        ring
      · simp only [Matrix.smul_apply, hm_apply, (topC_topL q).1 a ha, (topC_topL q₀).1 a ha]
        simp [herm])) q₀
  refine ⟨T, hT, fun q => ?_⟩
  rw [h, hN]
  ext <;> simp [add_assoc]

theorem pTop_left (q₀ : PTop k r j) : ∃ T : PTop k r j → PTop k r j, MeasurePreserving T volume volume ∧
    ∀ q, pTop k r j q₀ * pTop k r j q = pTop k r j (T q) := by
  obtain ⟨T, hT, h⟩ := pTop_shear 1 q₀
  exact ⟨T, hT, fun q => by rw [pTop_eq, pTop_eq, pTop_eq, h, pEl_mul', one_smul]⟩

theorem pTop_right (q₀ : PTop k r j) : ∃ T : PTop k r j → PTop k r j, MeasurePreserving T volume volume ∧
    ∀ q, pTop k r j q * pTop k r j q₀ = pTop k r j (T q) := by
  obtain ⟨T, hT, h⟩ := pTop_shear (-1) q₀
  exact ⟨T, hT, fun q => by
    rw [pTop_eq, pTop_eq, pTop_eq, h, pEl_mul', hm_swap, add_comm (topL k r j q).1, add_comm (topL k r j q).2]⟩

theorem pTop_conj {β : Fin r → ℕ} (hβ : ∀ a b : Fin r, j ≤ b.val → (β a = β b ↔ j ≤ a.val)) (x : UTin β → ℂ) :
    ∃ T : PTop k r j → PTop k r j, MeasurePreserving T volume volume ∧
      ∀ q, uEmb k r (upperIn β x) * pTop k r j q = pTop k r j (T q) * uEmb k r (upperIn β x) := by
  set A := strIn β x with hA
  have hAn : IsNilpotent A := strIn_nilp β x
  have hA0 : ∀ a c : Fin r, a.val < j → j ≤ c.val → A a c = 0 := fun a c ha hc =>
    strIn_zero β x fun h => by have := (hβ a c hc).1 h.2; omega
  let N₁ : Module.End ℝ (Matrix (Fin r) (Fin (k + 1)) ℂ) :=
    { toFun := fun B => Aᴴᵀ * B, map_add' := fun _ _ => Matrix.mul_add _ _ _, map_smul' := fun _ _ => Matrix.mul_smul _ _ _ }
  let L : Module.End ℝ (Matrix (Fin r) (Fin r) ℂ) := LinearMap.mulLeft ℝ A
  let R : Module.End ℝ (Matrix (Fin r) (Fin r) ℂ) := LinearMap.mulRight ℝ Aᴴ
  have hL : IsNilpotent L := (LinearMap.isNilpotent_mulLeft_iff _ _).2 hAn
  have hR : IsNilpotent R := (LinearMap.isNilpotent_mulRight_iff _ _).2 (by
    obtain ⟨n, hn⟩ := hAn
    exact ⟨n, by rw [← Matrix.conjTranspose_pow, hn, Matrix.conjTranspose_zero]⟩)
  have hc : Commute L R := LinearMap.commute_mulLeft_right _ _
  have h2 : IsNilpotent (L + R + L * R) :=
    Commute.isNilpotent_add (((Commute.refl L).mul_right hc).add_left (hc.symm.mul_right (Commute.refl R)))
      (hc.isNilpotent_add hL hR) (hc.isNilpotent_mul_right hL)
  have h1 : IsNilpotent N₁ := by
    obtain ⟨n, hn⟩ := nilp_of_strict Aᴴᵀ fun a b h => by
      rw [Matrix.transpose_apply, Matrix.conjTranspose_apply, hA, strIn_zero β x fun h' => h h'.1, star_zero]
    have : ∀ (m : ℕ) B, (N₁ ^ m) B = Aᴴᵀ ^ m * B := fun m => by
      induction m with
      | zero => simp
      | succ m ih => intro B; rw [pow_succ', pow_succ', Module.End.mul_apply, ih, Matrix.mul_assoc]; rfl
    exact ⟨n, LinearMap.ext fun B => by rw [this, hn]; simp⟩
  let N : Module.End ℝ (Amb k r) := LinearMap.prodMap N₁ (L + R + L * R)
  have hN : ∀ y : Amb k r, y + N y = ((1 + A)ᴴᵀ * y.1, (1 + A) * y.2 * (1 + A)ᴴ) := fun y => by
    refine Prod.ext ?_ ?_
    · show y.1 + Aᴴᵀ * y.1 = _
      simp [Matrix.add_mul]
    · show y.2 + (A * y.2 + y.2 * Aᴴ + A * (y.2 * Aᴴ)) = (1 + A) * y.2 * (1 + A)ᴴ
      rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one]; noncomm_ring
  have hNn : IsNilpotent N := by
    obtain ⟨n, hn⟩ := h1
    obtain ⟨m, hm⟩ := h2
    have : ∀ p : ℕ, N ^ p = LinearMap.prodMap (N₁ ^ p) ((L + R + L * R) ^ p) := fun p => by
      induction p with
      | zero => exact LinearMap.prodMap_id.symm
      | succ p ih => rw [pow_succ, ih, pow_succ, pow_succ]; rfl
    exact ⟨n + m, by rw [this, pow_add, pow_add, hn, hm, zero_mul, mul_zero]; exact LinearMap.prodMap_zero⟩
  obtain ⟨T, hT, h⟩ := exists_mp volume (topL k r j) topL_inj N hNn (fun q => TopC.mem (by
    have hq := topC_topL q
    have hS : ∀ a b : Fin r, a.val < j → (A * (topL k r j q).2) a b = 0 := fun a b ha => by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hc : c.val < j
      · rw [hq.2.2 c b hc, mul_zero]
      · rw [hA0 a c ha (by omega), zero_mul]
    refine ⟨fun a ha => funext fun i => ?_, ?_, fun a b ha => ?_⟩
    · show (Aᴴᵀ * (topL k r j q).1) a i = 0
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hc : c.val < j
      · rw [hq.1 c hc]; simp
      · rw [Matrix.transpose_apply, Matrix.conjTranspose_apply, hA0 a c ha (by omega), star_zero, zero_mul]
    · show (A * (topL k r j q).2 + (topL k r j q).2 * Aᴴ + A * ((topL k r j q).2 * Aᴴ))ᴴ =
        -(A * (topL k r j q).2 + (topL k r j q).2 * Aᴴ + A * ((topL k r j q).2 * Aᴴ))
      simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hq.2.1]
      noncomm_ring
    · show (A * (topL k r j q).2 + (topL k r j q).2 * Aᴴ + A * ((topL k r j q).2 * Aᴴ)) a b = 0
      rw [← Matrix.mul_assoc, Matrix.add_apply, Matrix.add_apply, hS a b ha, Matrix.mul_apply, Matrix.mul_apply]
      simp [hS a _ ha, hq.2.2 a _ ha])) 0
  refine ⟨T, hT, fun q => ?_⟩
  have hd : IsUnit (upperIn β x).det := by rw [upperIn, UEmb.det_upper]; exact isUnit_one
  rw [pTop_eq, pTop_eq, h, map_zero, zero_add, hN, uEmb_pEl _ hd, upperIn_eq]

theorem measurable_uIn (β : Fin r → ℕ) :
    Measurable fun x : UTin β → ℂ => (Matrix.of.symm (uEmb k r (upperIn β x)) : Mt k r) := by
  have h1 : Continuous (upperIn β) := by
    rw [funext (upperIn_eq β)]
    exact continuous_const.add (strIn β).continuous_of_finiteDimensional
  have h2 : ∀ x, (upperIn β x)⁻¹ = (upperIn β x).adjugate := fun x => by
    rw [Matrix.inv_def, upperIn, UEmb.det_upper]; simp
  refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b => Continuous.measurable ?_
  simp only [Matrix.of_symm_apply, uEmb, h2]
  split_ifs
  · exact h1.matrix_elem _ _
  · exact (h1.matrix_adjugate.matrix_elem _ _).star
  · exact continuous_const
  · exact continuous_const

theorem continuous_pEl {X : Type*} [TopologicalSpace X] (f : X → Fin r → Fin (k + 1) → ℂ)
    (g : X → Matrix (Fin r) (Fin r) ℂ) (hf : ∀ a i, Continuous fun q => f q a i) (hg : ∀ a b, Continuous fun q => g q a b)
    (a b : Fin (2 * r + k + 1)) : Continuous fun q => pEl k r (f q) (g q) a b := by
  induction a using Rad.cases3 <;> induction b using Rad.cases3 <;>
    simp only [Rad.pEl_ee, Rad.pEl_ew, Rad.pEl_es, Rad.pEl_we, Rad.pEl_ww, Rad.pEl_ws, Rad.pEl_se, Rad.pEl_sw, Rad.pEl_ss,
      Rad.herm_Hb] <;> fun_prop

theorem measurable_pTop : Measurable fun q : PTop k r j => (Matrix.of.symm (pTop k r j q) : Mt k r) := by
  have h := (topL k r j).continuous_of_finiteDimensional
  exact measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b => Continuous.measurable
    (continuous_pEl (fun q => (topL k r j q).1) (fun q => (topL k r j q).2)
      (fun a i => (continuous_fst.comp h).matrix_elem a i) (fun a b => (continuous_snd.comp h).matrix_elem a b) a b)

theorem pTop_inj : Function.Injective (pTop k r j) := fun q q' h => by
  refine topL_inj ?_
  have h1 : (topL k r j q).1 = (topL k r j q').1 := Matrix.ext fun b i =>
    (Rad.pEl_ws _ _ b i).symm.trans ((congrFun (congrFun h _) _).trans (Rad.pEl_ws _ _ b i))
  refine Prod.ext h1 (Matrix.ext fun a b => ?_)
  have := (Rad.pEl_es _ _ a b).symm.trans ((congrFun (congrFun h _) _).trans (Rad.pEl_es _ _ a b))
  change (topL k r j q).2 a b - herm _ ((topL k r j q).1 b) ((topL k r j q).1 a) / 2 =
    (topL k r j q').2 a b - herm _ ((topL k r j q').1 b) ((topL k r j q').1 a) / 2 at this
  rwa [h1, sub_left_inj] at this

theorem isUnit_uIn (β : Fin r → ℕ) (x : UTin β → ℂ) : IsUnit (uEmb k r (upperIn β x)).det := by
  have hd : IsUnit (upperIn β x).det := by rw [upperIn, UEmb.det_upper]; exact isUnit_one
  exact Matrix.isUnit_det_of_left_inverse (B := uEmb k r (upperIn β x)⁻¹)
    (by rw [← UEmb.uEmb_mul, Matrix.nonsing_inv_mul _ hd, UEmb.uEmb_one])

theorem rEl_inj (β : Fin r → ℕ) : Function.Injective (rEl k r j β) := fun q q' h => by
  have e : ∀ (q : (UTin β → ℂ) × PTop k r j) a b, rEl k r j β q (eI k r a) (eI k r b) = upperIn β q.1 a b := fun q a b => by
    have e1 : ∀ c, pTop k r j q.2 (eI k r c) (eI k r b) = if c = b then 1 else 0 := fun c => Rad.pEl_ee _ _ c b
    have e2 : ∀ c, pTop k r j q.2 (wI k r c) (eI k r b) = 0 := fun c => Rad.pEl_we _ _ b c
    have e3 : ∀ c, pTop k r j q.2 (esI k r c) (eI k r b) = 0 := fun c => Rad.pEl_se _ _ c b
    rw [rEl, Matrix.mul_apply, Rad.sum3]
    simp [e1, e2, e3, UEmb.u_ee]
  have h1 : q.1 = q'.1 := strIn_inj β (add_left_cancel (a := 1) (by
    rw [← upperIn_eq, ← upperIn_eq]
    ext a b
    rw [← e, ← e, h]))
  refine Prod.ext h1 (pTop_inj (k := k) ?_)
  rw [rEl, rEl, h1] at h
  exact ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_uIn β q'.1)).mul_left_cancel h

theorem measurable_mul {α : Type*} [MeasurableSpace α] {u v : α → Mat k r}
    (hu : Measurable fun a => (Matrix.of.symm (u a) : Mt k r)) (hv : Measurable fun a => (Matrix.of.symm (v a) : Mt k r)) :
    Measurable fun a => (Matrix.of.symm (u a * v a) : Mt k r) :=
  GlobalTheory.HaarInversion.measurable_mulM hu hv

theorem measurable_rEl (β : Fin r → ℕ) : Measurable fun q => (Matrix.of.symm (rEl k r j β q) : Mt k r) :=
  measurable_mul ((measurable_uIn β).comp measurable_fst) (measurable_pTop.comp measurable_snd)

theorem map_eq_of_lift {Q Y : Type*} [MeasurableSpace Q] [MeasurableSpace Y] {μ : Measure Q} {φ : Q → Y} (hφ : Measurable φ)
    {f : Y → Y} (hf : Measurable f) {T : Q → Q} (hT : MeasurePreserving T μ μ) (h : ∀ q, f (φ q) = φ (T q)) :
    (μ.map φ).map f = μ.map φ := by
  rw [Measure.map_map hf hφ, show f ∘ φ = φ ∘ T from funext h, ← Measure.map_map hφ hT.measurable, hT.map_eq]

theorem measurable_rEl' (β : Fin r → ℕ) : Measurable fun q : (UTin β → ℂ) × PTop k r j =>
    (Matrix.of.symm (pTop k r j q.2 * uEmb k r (upperIn β q.1)) : Mt k r) :=
  measurable_mul (measurable_pTop.comp measurable_snd) ((measurable_uIn β).comp measurable_fst)

theorem pEl_mul_neg (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ) : pEl k r B S * pEl k r (-B) (-S) = 1 := by
  rw [Rad.pEl_mul, ← Rad.pEl_zero]
  congr 1
  · simp
  · ext a b; simp [Rad.herm_neg_left, Rad.herm_neg_right]

set_option synthInstance.maxSize 1024 in

theorem range_eq_and_injective_parabolic_unipotent_product {β : Fin r → ℕ} (hβ : ∀ a b : Fin r, j ≤ b.val → (β a = β b ↔ j ≤ a.val)) :
    lebR0 k r j β = (volume : Measure ((UTin β → ℂ) × PTop k r j)).map fun q =>
      (Matrix.of.symm (pTop k r j q.2 * uEmb k r (upperIn β q.1)) : Mt k r) := by
  choose T hT h using pTop_conj (k := k) hβ
  have hemb : MeasurableEmbedding fun q : PTop k r j => (Matrix.of.symm (pTop k r j q) : Mt k r) :=
    measurable_pTop.measurableEmbedding (Matrix.of.symm.injective.comp pTop_inj)
  have hm : Measurable (Function.uncurry T) := by
    rw [← hemb.measurable_comp_iff]
    have : ((fun q : PTop k r j => (Matrix.of.symm (pTop k r j q) : Mt k r)) ∘ Function.uncurry T) =
        fun q => Matrix.of.symm (rEl k r j β q * (uEmb k r (upperIn β q.1))⁻¹) := by
      funext q
      rw [rEl, h, Matrix.mul_nonsing_inv_cancel_right _ _ (isUnit_uIn β q.1)]
      rfl
    rw [this]
    exact measurable_mul (measurable_rEl β) (measurable_invM.comp ((measurable_uIn β).comp measurable_fst))
  have hs : MeasurePreserving (fun q : (UTin β → ℂ) × PTop k r j => (id q.1, T q.1 q.2)) volume volume :=
    (MeasurePreserving.id volume).skew_product hm (Filter.Eventually.of_forall fun x => (hT x).map_eq)
  rw [← hs.map_eq, Measure.map_map (measurable_rEl' β) hs.measurable, lebR0]
  congr 1
  funext q
  exact congrArg Matrix.of.symm (h q.1 q.2)

theorem measurable_lmulM (a : Mat k r) : Measurable (lmulM a : Mt k r → Mt k r) :=
  measurable_mul (u := fun _ => a) (v := fun x : Mt k r => Matrix.of x) measurable_const measurable_id

theorem lebesgue_left_mul_invariant {β : Fin r → ℕ} (hβ : ∀ a b : Fin r, j ≤ b.val → (β a = β b ↔ j ≤ a.val))
    (q₀ : (UTin β → ℂ) × PTop k r j) : (lebR0 k r j β).map (lmulM (rEl k r j β q₀)) = lebR0 k r j β := by
  have h1 : (lebR0 k r j β).map (lmulM (uEmb k r (upperIn β q₀.1))) = lebR0 k r j β := by
    obtain ⟨T, hT, h⟩ := upperIn_left β q₀.1
    refine map_eq_of_lift (measurable_rEl β) (measurable_lmulM _) (hT.prod (MeasurePreserving.id volume)) fun q => ?_
    show uEmb k r (upperIn β q₀.1) * (uEmb k r (upperIn β q.1) * pTop k r j q.2) =
      uEmb k r (upperIn β (T q.1)) * pTop k r j q.2
    rw [← Matrix.mul_assoc, ← UEmb.uEmb_mul, h]
  have h2 : (lebR0 k r j β).map (lmulM (pTop k r j q₀.2)) = lebR0 k r j β := by
    obtain ⟨T, hT, h⟩ := pTop_left q₀.2
    rw [range_eq_and_injective_parabolic_unipotent_product hβ]
    refine map_eq_of_lift (measurable_rEl' β) (measurable_lmulM _) ((MeasurePreserving.id volume).prod hT) fun q => ?_
    show pTop k r j q₀.2 * (pTop k r j q.2 * uEmb k r (upperIn β q.1)) =
      pTop k r j (T q.2) * uEmb k r (upperIn β q.1)
    rw [← Matrix.mul_assoc, h]
  have e : (lmulM (rEl k r j β q₀) : Mt k r → Mt k r) = lmulM (uEmb k r (upperIn β q₀.1)) ∘ lmulM (pTop k r j q₀.2) :=
    funext fun x => Matrix.mul_assoc _ _ (Matrix.of x : Mat k r)
  rw [e, ← Measure.map_map (measurable_lmulM _) (measurable_lmulM _), h2, h1]

theorem lebesgue_right_mul_invariant {β : Fin r → ℕ} (hβ : ∀ a b : Fin r, j ≤ b.val → (β a = β b ↔ j ≤ a.val))
    (q₀ : (UTin β → ℂ) × PTop k r j) : (lebR0 k r j β).map (rmulM (rEl k r j β q₀)) = lebR0 k r j β := by
  have h1 : (lebR0 k r j β).map (rmulM (uEmb k r (upperIn β q₀.1))) = lebR0 k r j β := by
    obtain ⟨T, hT, h⟩ := upperIn_right β q₀.1
    rw [range_eq_and_injective_parabolic_unipotent_product hβ]
    refine map_eq_of_lift (measurable_rEl' β) (continuous_rmulM _).measurable
      (hT.prod (MeasurePreserving.id volume)) fun q => ?_
    show pTop k r j q.2 * uEmb k r (upperIn β q.1) * uEmb k r (upperIn β q₀.1) =
      pTop k r j q.2 * uEmb k r (upperIn β (T q.1))
    rw [Matrix.mul_assoc, ← UEmb.uEmb_mul, h]
  have h2 : (lebR0 k r j β).map (rmulM (pTop k r j q₀.2)) = lebR0 k r j β := by
    obtain ⟨T, hT, h⟩ := pTop_right q₀.2
    refine map_eq_of_lift (measurable_rEl β) (continuous_rmulM _).measurable
      ((MeasurePreserving.id volume).prod hT) fun q => ?_
    show uEmb k r (upperIn β q.1) * pTop k r j q.2 * pTop k r j q₀.2 =
      uEmb k r (upperIn β q.1) * pTop k r j (T q.2)
    rw [Matrix.mul_assoc, h]
  have e : (rmulM (rEl k r j β q₀) : Mt k r → Mt k r) = rmulM (pTop k r j q₀.2) ∘ rmulM (uEmb k r (upperIn β q₀.1)) :=
    funext fun x => (Matrix.mul_assoc (Matrix.of x : Mat k r) _ _).symm
  rw [e, ← Measure.map_map (continuous_rmulM _).measurable (continuous_rmulM _).measurable, h1, h2]

set_option synthInstance.maxSize 1024 in

theorem isHaarOn_range {β : Fin r → ℕ} (hβ : ∀ a b : Fin r, j ≤ b.val → (β a = β b ↔ j ≤ a.val)) :
    IsHaarOn (Set.range (rEl k r j β)) (lebR0 k r j β) := by
  have hemb : MeasurableEmbedding fun q => (Matrix.of.symm (rEl k r j β q) : Mt k r) :=
    (measurable_rEl β).measurableEmbedding (Matrix.of.symm.injective.comp (rEl_inj β))
  refine ⟨hemb.sigmaFinite_map, ?_, ?_, ?_⟩
  · rw [lebR0, Ne, Measure.map_eq_zero_iff hemb.measurable.aemeasurable]
    haveI : (volume : Measure ((UTin β → ℂ) × PTop k r j)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
    exact NeZero.ne _
  · rw [lebR0, hemb.map_apply]
    convert measure_empty (μ := (volume : Measure ((UTin β → ℂ) × PTop k r j)))
    exact Set.eq_empty_of_forall_notMem fun q hq => hq ⟨q, rfl⟩
  · rintro _ ⟨q, rfl⟩
    exact lebesgue_left_mul_invariant hβ q

theorem lebesgue_haar_unimodular_stabilizer : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ), inWb k r z → inWb k r z' → 0 < Tz k r z → IsNormal0 k r hj β c z z' g₀ → IsHaarOn (Rset k r g₀) (lebR0 k r j β) ∧ IsUnimod (Rset k r g₀) (lebR0 k r j β) := by
  intro k r j hj z z' g₀ β c hz hz' hT hg
  obtain ⟨e, hS⟩ := GlobalTheory.T.commonStabilizerSet_eq_range_normalForm k r j hj z z' g₀ β c hz hz' hT hg
  have hβ := hg.2.2.2.2.1
  rw [e] at hS ⊢
  have hH := isHaarOn_range (k := k) hβ
  have hR : ∀ s ∈ Set.range (rEl k r j β), (lebR0 k r j β).map (rmulM s) = lebR0 k r j β := by
    rintro _ ⟨q, rfl⟩
    exact lebesgue_right_mul_invariant hβ q
  refine ⟨hH, hR, ?_⟩
  have hG : PI.IsMatGroup (Set.range (rEl k r j β)) := by
    refine ⟨hS.2.1, hS.2.2.1, hS.2.2.2.1, fun a ha => ⟨hS.2.2.2.2 a ha, Matrix.mul_nonsing_inv _ ?_⟩⟩
    obtain ⟨q, rfl⟩ := ha
    rw [rEl, Matrix.det_mul]
    exact (isUnit_uIn β q.1).mul (Matrix.isUnit_det_of_right_inverse (pEl_mul_neg _ _))
  ext s hs
  have := GlobalTheory.HaarInversion.lintegral_inv_eq _ _ _ hG hH hR (s.indicator 1) (measurable_one.indicator hs)
  rw [lintegral_indicator_one hs] at this
  rw [← lintegral_indicator_one hs, lintegral_map (measurable_one.indicator hs) measurable_invM]
  exact this

end GlobalTheory.Amp.StabHaar
