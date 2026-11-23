import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Partners
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass

abbrev HCo (a : ℕ) : Type := (Fin a → ℝ) × ({p : Fin a × Fin a // p.1 < p.2} → ℂ)

def hOf {a : ℕ} (t : HCo a) : Matrix (Fin a) (Fin a) ℂ := fun i j =>
  if h : i < j then t.2 ⟨(i, j), h⟩ else if h' : j < i then star (t.2 ⟨(j, i), h'⟩) else (t.1 i : ℂ)

theorem hOf_isHermitian {a : ℕ} (t : HCo a) : (hOf t).IsHermitian := by
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · simp [hOf, Matrix.conjTranspose_apply, h, h.not_gt]
  · simp [hOf, Matrix.conjTranspose_apply]
  · simp [hOf, Matrix.conjTranspose_apply, h, h.not_gt]

abbrev Tup (k r a : ℕ) : Type := Fin (2 * r + k + 1) → Fin a → ℂ

def gramC {k r a : ℕ} (X : Tup k r a) : Matrix (Fin a) (Fin a) ℂ :=
  (Matrix.of X)ᴴ * Hpk k r * Matrix.of X

def DefPerp {k r a : ℕ} (X : Tup k r a) : Prop :=
  (gramC X).det ≠ 0 ∧ PosOnPerp (Hpk k r) (Matrix.of X)

def DefGram (k r a : ℕ) : Set (HCo a) := {t | ∃ X : Tup k r a, gramC X = hOf t ∧ DefPerp X}

def IsGramConst (k r a : ℕ) (μ : Measure (Mt k r)) (C : ℝ) : Prop :=
  0 < C ∧ ∀ Φ : Tup k r a → ℝ≥0∞, Measurable Φ → ∀ s : HCo a → Tup k r a,
    (∀ t ∈ DefGram k r a, gramC (s t) = hOf t) →
    (2 : ℝ≥0∞) ^ ((2 * r + k + 1) * a) * ∫⁻ X in {X | DefPerp X}, Φ X =
      (2 : ℝ≥0∞) ^ (a * (a - 1) / 2) * ∫⁻ t in DefGram k r a,
        ENNReal.ofReal (C * ‖(hOf t).det‖ ^ (2 * r + k + 1 - a)) *
          ∫⁻ g, Φ (Matrix.of.symm (Matrix.of g * Matrix.of (s t))) ∂μ

def IsSec (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    Prop :=
  (∀ i j, Measurable fun ζ => μsec ζ i j) ∧ ∀ ζ : ℂ, Tz k r z * Tz k r z' < Complex.normSq ζ →
    (μsec ζ)ᴴ * Hb k * μsec ζ = Hb k ∧ herm (Hpk k r) (bigCell k r 1 (μsec ζ) *ᵥ z') z = ζ

def IsIntC (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (μG μW μN μW' : Measure (Mt k r)) (C : ℝ) : Prop :=
  0 < C ∧ ∀ f : Mt k r → ℝ≥0∞, Measurable f →
    ∫⁻ g, f g ∂μG = ENNReal.ofReal C * ∫⁻ q : (Fin r → ℂ) × ℂ,
      ENNReal.ofReal (bcWeight k r (Tz k r z) (Tz k r z') q) *
        ∫⁻ p : (Mt k r × Mt k r) × (Mt k r × Mt k r),
          f (Matrix.of.symm (Matrix.of p.1.1 * Matrix.of p.1.2 * bigCell k r q.1 (μsec q.2) *
            (Matrix.of p.2.1 * Matrix.of p.2.2)⁻¹)) ∂((μW.prod μN).prod (μW'.prod μN))

section Glob

variable {E : Type} [Field E] [NumberField E]

def tupLat {n a : ℕ} (𝔞 : Fin a → FractionalIdeal (𝓞 E)⁰ E) (P : Matrix (Fin n) (Fin a) E) :
    Submodule (𝓞 E) (Fin n → E) :=
  Submodule.span (𝓞 E) {v | ∃ (b : Fin a) (x : E), x ∈ 𝔞 b ∧ v = x • fun i => P i b}

def ConfT (σ : E →+* E) {n a : ℕ} (J : Matrix (Fin n) (Fin n) E) (𝔞 : Fin a → FractionalIdeal (𝓞 E)⁰ E)
    (T : Matrix (Fin a) (Fin a) E) : Set (Submodule (𝓞 E) (Fin n → E) × Matrix (Fin n) (Fin a) E) :=
  {x | GlobalTheory.SgGlob.SelfDual σ J x.1 ∧ Free x.2 ∧ pairM σ J x.2 x.2 = T ∧ PrimIn (tupLat 𝔞 x.2) x.1}

def IsoT (σ : E →+* E) {n a : ℕ} (J : Matrix (Fin n) (Fin n) E) (γ : Matrix (Fin n) (Fin n) E)
    (x y : Submodule (𝓞 E) (Fin n → E) × Matrix (Fin n) (Fin a) E) : Prop :=
  IsUn σ J γ ∧ latMap γ x.1 = y.1 ∧ γ * x.2 = y.2

def MassT (σ : E →+* E) {n a : ℕ} (J : Matrix (Fin n) (Fin n) E) (𝔞 : Fin a → FractionalIdeal (𝓞 E)⁰ E)
    (T : Matrix (Fin a) (Fin a) E) : ℝ≥0∞ := massOf (ConfT σ J 𝔞 T) (IsoT σ J)

def dualM (σ : E →+* E) {a : ℕ} (𝔞 : Fin a → FractionalIdeal (𝓞 E)⁰ E) (T : Matrix (Fin a) (Fin a) E) :
    Submodule (𝓞 E) (Fin a → E) :=
  Submodule.span (𝓞 E) {x | ∀ y ∈ tupLat 𝔞 (1 : Matrix (Fin a) (Fin a) E),
    form σ T x y ∈ (algebraMap (𝓞 E) E).range}

theorem mem_dualM (σ : E →+* E) {a : ℕ} (𝔞 : Fin a → FractionalIdeal (𝓞 E)⁰ E)
    (T : Matrix (Fin a) (Fin a) E) (x : Fin a → E) :
    x ∈ dualM σ 𝔞 T ↔ ∀ y ∈ tupLat 𝔞 (1 : Matrix (Fin a) (Fin a) E),
      form σ T x y ∈ (algebraMap (𝓞 E) E).range := by
  refine ⟨fun hx => ?_, fun hx => Submodule.subset_span hx⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => intro y _; simp [form]
  | add x x' _ _ h h' =>
    intro y hy
    have : form σ T (x + x') y = form σ T x y + form σ T x' y := by
      simp [form, Matrix.mulVec_add]
    rw [this]; exact add_mem (h y hy) (h' y hy)
  | smul c x _ h =>
    intro y hy
    have : form σ T (c • x) y = algebraMap (𝓞 E) E c * form σ T x y := by
      rw [← algebraMap_smul E c x, form, form, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
    rw [this]; exact mul_mem ⟨c, rfl⟩ (h y hy)

theorem mem_dualM_iff_mulVec (σ : E →+* E) {a : ℕ} (𝔞 : Fin a → FractionalIdeal (𝓞 E)⁰ E)
    (T : Matrix (Fin a) (Fin a) E) (x : Fin a → E) :
    x ∈ dualM σ 𝔞 T ↔ T *ᵥ x ∈ dualM σ 𝔞 1 := by
  simp [mem_dualM, form]

theorem latMap_dualM (σ : E →+* E) {a : ℕ} (𝔞 : Fin a → FractionalIdeal (𝓞 E)⁰ E)
    {T : Matrix (Fin a) (Fin a) E} (hT : T.det ≠ 0) : latMap T (dualM σ 𝔞 T) = dualM σ 𝔞 1 := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_dualM_iff_mulVec σ 𝔞 T y).1 hy
  · intro hx
    have e : T *ᵥ (T⁻¹ *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit hT), Matrix.one_mulVec]
    exact ⟨T⁻¹ *ᵥ x, (mem_dualM_iff_mulVec σ 𝔞 T _).2 (e.symm ▸ hx), e⟩

variable {F : Type} [Field F] [NumberField F] [Algebra F E]

def cork (σ : E →+* E) {a : ℕ} (𝔞 : Fin a → FractionalIdeal (𝓞 E)⁰ E) (T : Matrix (Fin a) (Fin a) E)
    (v : HeightOneSpectrum (𝓞 F)) : ℕ :=
  Nat.log (Ideal.absNorm v.asIdeal ^ 2)
    ((latMap T (tupLat 𝔞 (1 : Matrix (Fin a) (Fin a) E)) ⊔
      (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))) • dualM σ 𝔞 1).toAddSubgroup.relIndex
        (dualM σ 𝔞 1).toAddSubgroup)

theorem relIndex_map_submodule {R M N : Type} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module R M]
    [Module R N] (f : M →ₗ[R] N) (hf : Function.Injective f) (A B : Submodule R M) :
    (A.map f).toAddSubgroup.relIndex (B.map f).toAddSubgroup = A.toAddSubgroup.relIndex B.toAddSubgroup :=
  AddSubgroup.relIndex_map_map_of_injective (f := f.toAddMonoidHom) A.toAddSubgroup B.toAddSubgroup hf

theorem cork_eq_of_det_ne_zero (σ : E →+* E) {a : ℕ} (𝔞 : Fin a → FractionalIdeal (𝓞 E)⁰ E)
    {T : Matrix (Fin a) (Fin a) E} (hT : T.det ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    cork σ 𝔞 T v = Nat.log (Ideal.absNorm v.asIdeal ^ 2)
      ((tupLat 𝔞 (1 : Matrix (Fin a) (Fin a) E) ⊔
        (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))) • dualM σ 𝔞 T).toAddSubgroup.relIndex
          (dualM σ 𝔞 T).toAddSubgroup) := by
  have hinj : Function.Injective (T.mulVecLin.restrictScalars (𝓞 E)) :=
    Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det T).2 (Ne.isUnit hT))
  have key : ∀ (I : Ideal (𝓞 E)) (M D D' : Submodule (𝓞 E) (Fin a → E)), latMap T D = D' →
      (latMap T M ⊔ I • D').toAddSubgroup.relIndex D'.toAddSubgroup =
        (M ⊔ I • D).toAddSubgroup.relIndex D.toAddSubgroup := by
    rintro I M D _ rfl
    rw [← relIndex_map_submodule _ hinj (M ⊔ I • D) D, Submodule.map_sup, Submodule.map_smul'']
    rfl
  exact congrArg _ (key _ _ _ _ (latMap_dualM σ 𝔞 hT))

theorem mem_tupLat_one {a : ℕ} (x : Fin a → E) :
    x ∈ tupLat (fun _ : Fin a => (1 : FractionalIdeal (𝓞 E)⁰ E)) (1 : Matrix (Fin a) (Fin a) E) ↔
      ∀ i, x i ∈ (algebraMap (𝓞 E) E).range := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, c, hc, rfl⟩ := hx
      obtain ⟨d, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hc
      intro i
      by_cases h : i = b <;> simp [Matrix.one_apply, h]
    | zero => simp
    | add x y _ _ h h' => exact fun i => add_mem (h i) (h' i)
    | smul c x _ h => exact fun i => mul_mem ⟨c, rfl⟩ (h i)
  · intro hx
    have : x = ∑ b, x b • fun i => (1 : Matrix (Fin a) (Fin a) E) i b := by
      ext i; simp [Finset.sum_apply, Matrix.one_apply]
    rw [this]
    exact Submodule.sum_mem _ fun b _ =>
      Submodule.subset_span ⟨b, x b, (FractionalIdeal.mem_one_iff _).2 (hx b), rfl⟩

theorem dualM_one_one (σ : E →+* E) {a : ℕ} :
    dualM σ (fun _ : Fin a => (1 : FractionalIdeal (𝓞 E)⁰ E)) 1 =
      tupLat (fun _ : Fin a => (1 : FractionalIdeal (𝓞 E)⁰ E)) (1 : Matrix (Fin a) (Fin a) E) := by
  ext x
  rw [mem_dualM, mem_tupLat_one]
  constructor
  · intro h i
    have := h (Pi.single i 1) ((mem_tupLat_one _).2 fun j => by
      by_cases hj : j = i <;> simp [Pi.single_apply, hj])
    simpa [form, dotProduct, Pi.single_apply, apply_ite σ] using this
  · intro h y hy
    rw [mem_tupLat_one] at hy
    simp only [form, Matrix.one_mulVec, dotProduct]
    refine sum_mem fun i _ => mul_mem ?_ (h i)
    obtain ⟨d, hd⟩ := hy i
    exact ⟨RingOfIntegers.mapRingHom σ d, by rw [← hd]; rfl⟩

theorem cork_one_one (σ : E →+* E) {a : ℕ} (v : HeightOneSpectrum (𝓞 F)) :
    cork σ (fun _ : Fin a => (1 : FractionalIdeal (𝓞 E)⁰ E)) 1 v = 0 := by
  rw [cork_eq_of_det_ne_zero σ _ (by simp), dualM_one_one,
    AddSubgroup.relIndex_eq_one.2 (fun x hx => Submodule.mem_sup_left hx), Nat.log_one_right]

theorem cork_one_zero (σ : E →+* E) (h2 : Module.finrank F E = 2) {a : ℕ}
    (v : HeightOneSpectrum (𝓞 F)) :
    cork σ (fun _ : Fin a => (1 : FractionalIdeal (𝓞 E)⁰ E)) 0 v = a := by
  set I := v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) with hI
  let φ : (Fin a → 𝓞 E) →ₗ[𝓞 E] (Fin a → E) := (Algebra.linearMap (𝓞 E) E).compLeft (Fin a)
  have hφ : Function.Injective φ.toAddMonoidHom := fun x y h =>
    funext fun i => RingOfIntegers.coe_injective (congrFun h i)
  have h1 : tupLat (fun _ : Fin a => (1 : FractionalIdeal (𝓞 E)⁰ E)) (1 : Matrix (Fin a) (Fin a) E) =
      (⊤ : Submodule (𝓞 E) (Fin a → 𝓞 E)).map φ := by
    ext x
    rw [mem_tupLat_one]
    constructor
    · intro h
      choose y hy using h
      exact ⟨y, trivial, funext hy⟩
    · rintro ⟨y, -, rfl⟩ i
      exact ⟨y i, rfl⟩
  have h3 : (I • (⊤ : Submodule (𝓞 E) (Fin a → 𝓞 E))).toAddSubgroup =
      AddSubgroup.pi Set.univ fun _ => I.toAddSubgroup := by
    ext x
    simp only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_pi, Set.mem_univ, true_imp_iff]
    constructor
    · intro hx i
      refine Submodule.smul_induction_on hx (fun r hr y _ => I.mul_mem_right _ hr) ?_
      exact fun y z hy hz => I.add_mem hy hz
    · intro hx
      have : x = ∑ b, x b • (Pi.single b 1 : Fin a → 𝓞 E) := by
        ext i; simp [Finset.sum_apply, Pi.single_apply]
      rw [this]
      exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem_smul (hx b) trivial
  have h4 : I.toAddSubgroup.index = Ideal.absNorm v.asIdeal ^ 2 := by
    rw [← h2, IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E, ← Ideal.absNorm_algebraMap, Ideal.absNorm_apply,
      Submodule.cardQuot_apply]
    rfl
  have h5 : latMap (0 : Matrix (Fin a) (Fin a) E) ((⊤ : Submodule (𝓞 E) (Fin a → 𝓞 E)).map φ) = ⊥ := by
    simp [latMap]
  have hq : 1 < Ideal.absNorm v.asIdeal ^ 2 :=
    Nat.one_lt_pow two_ne_zero (NumberField.HeightOneSpectrum.one_lt_absNorm v)
  rw [cork, dualM_one_one, h1, h5, bot_sup_eq, ← hI, ← Submodule.map_smul'']
  have := AddSubgroup.relIndex_map_map_of_injective
    (I • (⊤ : Submodule (𝓞 E) (Fin a → 𝓞 E))).toAddSubgroup ⊤ hφ
  rw [AddSubgroup.relIndex_top_right, h3, AddSubgroup.index_pi] at this
  simp only [h4, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
  rw [← h3] at this
  refine Eq.trans ?_ (Nat.log_pow hq a)
  rw [← this]
  rfl

open scoped Classical in

def eta₃ (E : Type) [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  if (v.asIdeal.primesOver (𝓞 E)).ncard = 2 then 1 else -1

def densV (σ : E →+* E) (n : ℕ) {a : ℕ} (𝔞 : Fin a → FractionalIdeal (𝓞 E)⁰ E)
    (T : Matrix (Fin a) (Fin a) E) (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  GlobalTheory.SgDen.densF (Ideal.absNorm v.asIdeal) (eta₃ E v) n a (cork σ 𝔞 T v)

example (σ : E →+* E) (h2 : Module.finrank F E = 2) (v : HeightOneSpectrum (𝓞 F)) :
    densV σ 1 (fun _ : Fin 1 => (1 : FractionalIdeal (𝓞 E)⁰ E)) 0 v = 0 := by
  rw [densV, cork_one_zero σ h2, GlobalTheory.SgDen.densF]
  exact Finset.prod_eq_zero (i := 0) (by simp) (by simp)

example (σ : E →+* E) (v : HeightOneSpectrum (𝓞 F)) :
    densV σ 1 (fun _ : Fin 1 => (1 : FractionalIdeal (𝓞 E)⁰ E)) 1 v =
      1 - eta₃ E v * (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  rw [densV, cork_one_one, GlobalTheory.SgDen.densF]
  simp

def locLat (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) :
    AddSubgroup (Fin n → Fv F v ⊗[F] E) :=
  AddSubgroup.closure {y | ∃ c ∈ v.adicCompletionIntegers F, ∃ x ∈ Λ, y = fun i => c ⊗ₜ[F] x i}

def locId (v : HeightOneSpectrum (𝓞 F)) (I : FractionalIdeal (𝓞 E)⁰ E) : AddSubgroup (Fv F v ⊗[F] E) :=
  AddSubgroup.closure {y | ∃ c ∈ v.adicCompletionIntegers F, ∃ x ∈ I, y = c ⊗ₜ[F] x}

def IntLoc (v : HeightOneSpectrum (𝓞 F)) {n a : ℕ} (𝔞 : Fin a → FractionalIdeal (𝓞 E)⁰ E)
    (L : AddSubgroup (Fin n → Fv F v ⊗[F] E)) : Set (Fin a → Fin n → Fv F v ⊗[F] E) :=
  {X | ∀ b, ∀ x ∈ locId v (𝔞 b), x • X b ∈ L}

def PrimLoc (v : HeightOneSpectrum (𝓞 F)) {n a : ℕ} (𝔞 : Fin a → FractionalIdeal (𝓞 E)⁰ E)
    (L : AddSubgroup (Fin n → Fv F v ⊗[F] E)) : Set (Fin a → Fin n → Fv F v ⊗[F] E) :=
  {X | X ∈ IntLoc v 𝔞 L ∧ LinearIndependent (Fv F v ⊗[F] E) X ∧
    ∀ c : Fin a → Fv F v ⊗[F] E, ∑ b, c b • X b ∈ L → ∀ b, c b ∈ locId v (𝔞 b)}

def normAt (v : HeightOneSpectrum (𝓞 F)) (I : FractionalIdeal (𝓞 E)⁰ E) : ℝ :=
  ((locId v I).relIndex (locId v (1 : FractionalIdeal (𝓞 E)⁰ E)) : ℝ) /
    ((locId v (1 : FractionalIdeal (𝓞 E)⁰ E)).relIndex (locId v I) : ℝ)

def difAt (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  (Ideal.absNorm v.asIdeal : ℝ) ^
    (FractionalIdeal.count F v ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F))

def StdAt (v : HeightOneSpectrum (𝓞 F)) (ψ : Fv F v → ℂ) : Prop :=
  ∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ (x * y) = 1) ↔
    ∀ d ∈ differentIdeal ℤ (𝓞 F), x * algebraMap F (Fv F v) (d : F) ∈ v.adicCompletionIntegers F

def IsStdChar (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) : Prop :=
  IsCharAF F ψ ∧ (∀ x : Ainf F, psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I *
      ((∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ))) ∧
    ∀ v, StdAt v (psiV F ψ v)

variable (σ : E →ₐ[F] E) {k r : ℕ} (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)

def IsModelAt (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  ∀ w, (A w)ᴴ * Hpk k r * A w = J.map w.embedding

def IsVolM (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E))
    (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (μw : InfinitePlace E → Measure (Mt k r)) (μ : Measure (HA (AF F) σ J)) : Prop :=
  μ.IsHaarMeasure ∧
  AllSome (fun θ : InfinitePlace E → (Ainf F ⊗[F] E →+* ℂ) =>
    ∀ w, Formalism.MainNotions.StandardLattice.IsInfEmb w.embedding (θ w)) fun θ =>
  ∀ B : InfinitePlace E → Set (Mt k r), (∀ w, MeasurableSet (B w)) →
    μ {h | (∀ y, y ∈ Formalism.MainNotions.StandardLattice.latHat F E (Λ : Set (Fin (2 * r + k + 1) → E)) ↔
          (Formalism.MainNotions.StandardLattice.finMat σ J h).mulVec y ∈ Formalism.MainNotions.StandardLattice.latHat F E (Λ : Set (Fin (2 * r + k + 1) → E))) ∧
        ∀ w, ∃ b ∈ B w, Matrix.of b * A w = A w * Formalism.MainNotions.StandardLattice.infMat σ J (θ w) h} =
      ∏ w, μw w (B w)

def GlobData (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E))
    (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (μw : InfinitePlace E → Measure (Mt k r)) (V₀ : ℝ≥0∞) : Prop :=
  IsCMExt F E σ ∧ Algebra.FormallyUnramified (𝓞 F) (𝓞 E) ∧ IsHermND σ J ∧
    GlobalTheory.SgGlob.SelfDual (σ : E →+* E) J Λ ∧ IsModelAt J A ∧ (∀ w, IsHaarOn (UH (Hpk k r)) (μw w)) ∧
    ∃ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsVolM σ J Λ A μw μ ∧
      IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ ∧ μ 𝓕 = V₀

end Glob

end GlobalTheory.SnMass
