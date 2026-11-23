import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal ComplexConjugate

namespace GlobalTheory.StdPar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}

variable (F) in

def colSpan (C : Matrix (Fin n) (Fin r) E) (I : Set (Fin r)) : Submodule (AF F ⊗[F] E) (Fin n → AF F ⊗[F] E) :=
  Submodule.span _ ((fun i => (adMat F C)ᵀ i) '' I)

def colPerp (C : Matrix (Fin n) (Fin r) E) (I : Set (Fin r)) : Submodule (AF F ⊗[F] E) (Fin n → AF F ⊗[F] E) :=
  ⨅ i ∈ I, LinearMap.ker (LinearMap.proj i ∘ₗ (adMat F (cT (σ : E →+* E) C * J)).mulVecLin)

def trivOn (A B : Submodule (AF F ⊗[F] E) (Fin n → AF F ⊗[F] E)) : Subgroup (GAd σ J) where
  carrier := {g | (∀ y, y ∈ A ↔ (matHom _ σ J g).1 *ᵥ y ∈ A) ∧ ∀ y ∈ B, (matHom _ σ J g).1 *ᵥ y - y ∈ A}
  one_mem' := ⟨fun y => by simp, fun y _ => by simp⟩
  mul_mem' := fun {a b} ha hb => ⟨fun y => by rw [map_mul, Units.val_mul, ← mulVec_mulVec, ← ha.1, ← hb.1], fun y hy => by
    have := add_mem ((ha.1 _).1 (hb.2 y hy)) (ha.2 y hy)
    rwa [mulVec_sub, sub_add_sub_cancel, mulVec_mulVec, ← Units.val_mul, ← map_mul] at this⟩
  inv_mem' := fun {a} ha =>
    have e : ∀ y, (matHom _ σ J a).1 *ᵥ (matHom _ σ J a⁻¹).1 *ᵥ y = y := fun y => by
      rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, one_mulVec]
    ⟨fun y => by rw [ha.1 ((matHom _ σ J a⁻¹).1 *ᵥ y), e], fun y hy => by
      rw [ha.1, mulVec_sub, e, ← neg_sub]; exact neg_mem (ha.2 y hy)⟩

def frameStab {k : ℕ} (C : Matrix (Fin n) (Fin k) E) (H : Subgroup (GL (Fin k) (AF F ⊗[F] E))) : Subgroup (GAd σ J) where
  carrier := {g | ∃ B ∈ H, (matHom _ σ J g).1 * adMat F C = adMat F C * B.1}
  one_mem' := ⟨1, one_mem _, by simp⟩
  mul_mem' := fun ⟨B, h, e⟩ ⟨B', h', e'⟩ => ⟨B * B', mul_mem h h', by
    rw [map_mul, Units.val_mul, Matrix.mul_assoc, e', ← Matrix.mul_assoc, e, Matrix.mul_assoc, Units.val_mul]⟩
  inv_mem' := fun {a} ⟨B, h, e⟩ => ⟨B⁻¹, inv_mem h, by
    have : adMat F C = (matHom _ σ J a).1 * (adMat F C * B⁻¹.1) := by
      rw [← Matrix.mul_assoc, e, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    conv_lhs => rw [this, ← Matrix.mul_assoc, map_inv, Units.inv_mul, Matrix.one_mul]⟩

def initCols (C : Matrix (Fin n) (Fin r) E) (k : Fin r) : Matrix (Fin n) (Fin (k.val + 1)) E :=
  C.submatrix id (Fin.castLE k.2)

variable (X Y : Matrix (Fin n) (Fin r) E) (S : Finset (Fin r))

def unip : Subgroup (GAd σ J) :=
  (⨅ j : Fin r, trivOn σ J (colSpan F X {i | ∃ k ∈ S, i ≤ k ∧ k < j}) (colSpan F X {j})) ⊓
    trivOn σ J (colSpan F X {i | ∃ k ∈ S, i ≤ k}) (colPerp σ J X {i | ∃ k ∈ S, i ≤ k})

def levi : Subgroup (GAd σ J) := ⨅ k ∈ S, frameStab σ J (initCols X k) ⊤ ⊓ frameStab σ J (initCols Y k) ⊤

def leviOne : Subgroup (GAd σ J) :=
  levi σ J X Y S ⊓ ⨅ k ∈ S, frameStab σ J (initCols X k) ((absE F E).comp Matrix.GeneralLinearGroup.det).ker

def stepSum (u : Fin r → ℝ) (i : Fin r) : ℝ := ∑ k ∈ S with i ≤ k, u k

def IsSplitElt (u : Fin r → ℝ) (a : GAd σ J) : Prop := IsTorusElt σ J X Y (fun i => Real.exp (stepSum S u i)) a

structure IsAutOn (K : Subgroup (GAd σ J)) (φ : GAd σ J → ℂ) : Prop where
  leftN : ∀ u ∈ unip σ J X S, ∀ g, φ (u * g) = φ g
  leftM : ∀ γ ∈ ratPts σ J, γ ∈ levi σ J X Y S → ∀ g, φ (γ * g) = φ g
  level : ∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ k ∈ U, k ∈ finPts σ J → ∀ g, φ (g * k) = φ g
  cont : Continuous φ
  smooth : IsSm σ J φ
  growth : ∃ N : ℕ, ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
    ∃ C : ℝ, ∀ g, ‖l.foldr lineDer φ g‖ ≤ C * (height σ J g : ℝ) ^ N
  kfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun g => φ (g * k)))
  zfin : FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ z, IsCentral σ J z ∧ f = dop z φ})

def IsConstAlong (φ c : GAd σ J → ℂ) : Prop :=
  ∀ (μ : Measure (unip σ J X S)) (𝓕 : Set (unip σ J X S)), μ.IsHaarMeasure →
    IsFundamentalDomain ((ratPts σ J).subgroupOf (unip σ J X S)) 𝓕 μ → μ 𝓕 = 1 →
    ∀ g, c g = ∫ u in 𝓕, φ ((u : GAd σ J) * g) ∂μ

def IsCuspOn (K : Subgroup (GAd σ J)) (ψ : GAd σ J → ℂ) : Prop :=
  IsAutOn σ J X Y S K ψ ∧ ∀ S' : Finset (Fin r), S ⊂ S' → IsConstAlong σ J X S' ψ 0

def IsCuspComp (K : Subgroup (GAd σ J)) (φ φc : GAd σ J → ℂ) : Prop :=
  IsCuspOn σ J X Y S K φc ∧ ∃ c, IsConstAlong σ J X S φ c ∧ ∀ ψ, IsCuspOn σ J X Y S K ψ →
    ∀ (μ : Measure (leviOne σ J X Y S)) (𝓕 : Set (leviOne σ J X Y S)), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratPts σ J).subgroupOf (leviOne σ J X Y S)) 𝓕 μ → ∀ g g',
        IntegrableOn (fun m : leviOne σ J X Y S => c (m * g) * conj (ψ (m * g'))) 𝓕 μ ∧
        IntegrableOn (fun m : leviOne σ J X Y S => φc (m * g) * conj (ψ (m * g'))) 𝓕 μ ∧
        ∫ m in 𝓕, c (m * g) * conj (ψ (m * g')) ∂μ = ∫ m in 𝓕, φc (m * g) * conj (ψ (m * g')) ∂μ

def IsSqIntOn (φ : GAd σ J → ℂ) : Prop :=
  ∀ (μ : Measure (leviOne σ J X Y S)) (𝓕 : Set (leviOne σ J X Y S)), μ.IsHaarMeasure →
    IsFundamentalDomain ((ratPts σ J).subgroupOf (leviOne σ J X Y S)) 𝓕 μ → ∀ g,
      IntegrableOn (fun m : leviOne σ J X Y S => ‖φ (m * g)‖ ^ 2) 𝓕 μ

variable (F n) in

def expChar (s : Fin r → ℂ) (v : Fin r → ℝ) : ℂ :=
  √(modulus F n fun i => Real.exp (v i)) * Complex.exp (2 * Module.finrank ℚ F * ∑ i, s i * v i)

def IsExponent (f : GAd σ J → ℂ) (s : Fin r → ℂ) : Prop :=
  ∃ f' ∈ Submodule.span ℂ {f₁ : GAd σ J → ℂ | ∃ u a, IsSplitElt σ J X Y S u a ∧ f₁ = fun g => f (a * g)}, f' ≠ 0 ∧
    ∀ u a, IsSplitElt σ J X Y S u a → ∀ g, f' (a * g) = expChar F n s (stepSum S u) * f' g

def IsCuspExp (K : Subgroup (GAd σ J)) (φ : GAd σ J → ℂ) (s : Fin r → ℂ) : Prop :=
  ∃ φc, IsCuspComp σ J X Y S K φ φc ∧ IsExponent σ J X Y S φc s

def NegExp (T : Finset (Fin r)) (s : Fin r → ℂ) : Prop :=
  ∃ y : Fin r → ℝ, ∀ k ∈ S, (k ∈ T → ∑ i with i ≤ k, ((s i).re - stepSum T y i) = 0) ∧
    (k ∉ T → ∑ i with i ≤ k, ((s i).re - stepSum T y i) < 0)

section Empty

variable {σ J X Y}

omit [NumberField E] in

theorem unip_empty : unip σ J X ∅ = ⊥ := eq_bot_iff.2 fun g hg => by
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  have h := hg.2.2 (Pi.single j 1) (by simp [colPerp])
  have e : colSpan F X {i | ∃ k ∈ (∅ : Finset (Fin r)), i ≤ k} = ⊥ := by simp [colSpan]
  rw [e, Submodule.mem_bot, sub_eq_zero, mulVec_single_one] at h
  exact (congrFun h i).trans (Pi.single_apply _ _ _)

omit [NumberField E] in
@[simp] theorem levi_empty : levi σ J X Y ∅ = ⊤ := by simp [levi]

@[simp] theorem leviOne_empty : leviOne σ J X Y ∅ = ⊤ := by simp [leviOne]

theorem isAutOn_empty {K : Subgroup (GAd σ J)} {φ : GAd σ J → ℂ} : IsAutOn σ J X Y ∅ K φ ↔ IsAut σ J K φ :=
  ⟨fun h => ⟨⟨fun γ hγ => h.leftM γ hγ (by simp), h.level, h.cont, h.smooth, h.growth⟩, h.kfin, h.zfin⟩,
    fun h => ⟨fun u hu g => by rw [unip_empty, Subgroup.mem_bot] at hu; rw [hu, one_mul], fun γ hγ _ => h.mod.left γ hγ,
      h.mod.level, h.mod.cont, h.mod.smooth, h.mod.growth, h.kfin, h.zfin⟩⟩

theorem isSqIntOn_empty {φ : GAd σ J → ℂ} : IsSqIntOn σ J X Y ∅ φ ↔ IsSqInt σ J φ := by
  unfold IsSqIntOn
  rw [leviOne_empty]
  let t : (⊤ : Subgroup (GAd σ J)) ≃ₜ* GAd σ J :=
    { Subgroup.topEquiv with continuous_toFun := continuous_subtype_val, continuous_invFun := continuous_id.subtype_mk _ }
  refine ⟨fun h μ 𝓕 h1 h2 => ?_, fun h μ 𝓕 h1 h2 g => ?_⟩
  · let e := t.toHomeomorph.toMeasurableEquiv
    have hp : MeasurePreserving e (μ.map t.symm) μ := (MeasurePreserving.symm e.symm ⟨e.symm.measurable, rfl⟩ :)
    have := h (μ.map t.symm) (e ⁻¹' 𝓕) inferInstance (h2.preimage_of_equiv hp.quasiMeasurePreserving
      (e := fun δ => ⟨⟨δ, trivial⟩, δ.2⟩) ⟨fun a b hab => Subtype.ext (congrArg (·.1.1) hab), fun δ => ⟨⟨δ.1, δ.2⟩, rfl⟩⟩
      fun _ _ => rfl) 1
    refine (hp.integrableOn_comp_preimage e.measurableEmbedding).1 ?_
    simp only [mul_one] at this
    exact this
  · let e := t.toHomeomorph.toMeasurableEquiv.trans (MeasurableEquiv.mulRight g)
    have hp : MeasurePreserving e.symm ((μ.map t).map (· * g)) μ := MeasurePreserving.symm e
      ⟨e.measurable, (Measure.map_map (measurable_mul_const g) t.continuous.measurable).symm⟩
    have := h ((μ.map t).map (· * g)) (e.symm ⁻¹' 𝓕) inferInstance (h2.preimage_of_equiv hp.quasiMeasurePreserving
      (e := fun δ => ⟨δ.1, δ.2⟩) ⟨fun a b hab => Subtype.ext (Subtype.ext (congrArg (·.1) hab)), fun δ => ⟨⟨⟨δ, trivial⟩, δ.2⟩, rfl⟩⟩
      fun _ _ => Subtype.ext (mul_assoc _ _ _))
    refine (hp.integrableOn_comp_preimage e.symm.measurableEmbedding).1 ?_
    convert this using 2 with x
    exact congrArg (‖φ ·‖ ^ 2) (e.apply_symm_apply x)

theorem negExp_empty {s : Fin r → ℂ} : NegExp S ∅ s ↔ ∀ k ∈ S, ∑ i with i ≤ k, (s i).re < 0 := by
  simp [NegExp, stepSum]

end Empty

theorem isAutOn_const (K : Subgroup (GAd σ J)) (c : ℂ) : IsAutOn σ J X Y S K fun _ => c := by
  have h := isSmoothModerate_const σ J c
  have h1 : ∀ l : List (ℝ → GAd σ J), ∃ c' : ℂ, l.foldr lineDer (fun _ => c) = fun _ => c' := fun l => by
    induction l with
    | nil => exact ⟨c, rfl⟩
    | cons γ l ih =>
      obtain ⟨c', h⟩ := ih
      exact ⟨0, by rw [List.foldr_cons, h]; funext g; simp [lineDer]⟩
  choose d hd using h1
  refine ⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl, h.level, h.cont, h.smooth, h.growth, ?_, ?_⟩ <;>
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {(fun _ => 1 : GAd σ J → ℂ)}) (Submodule.span_le.2 ?_)
  · rintro _ ⟨k, rfl⟩
    exact Submodule.mem_span_singleton.2 ⟨c, by funext g; simp⟩
  · rintro _ ⟨z, -, rfl⟩
    exact Submodule.mem_span_singleton.2 ⟨z.sum fun l a => a * d l, by funext g; simp [dop, hd]⟩

omit [NumberField E] in

theorem isConstAlong_const (c : ℂ) : IsConstAlong σ J X S (fun _ => c) fun _ => c := fun μ 𝓕 _ _ h _ => by
  simp [Measure.real, h]

theorem isCuspOn_univ {K : Subgroup (GAd σ J)} {ψ : GAd σ J → ℂ} :
    IsCuspOn σ J X Y Finset.univ K ψ ↔ IsAutOn σ J X Y Finset.univ K ψ :=
  and_iff_left fun _ h => absurd (Finset.subset_univ _) h.2

variable (n r) in

def negRho (i : Fin r) : ℂ := ((i.val - (n - 1) / 2 : ℝ) : ℂ)

theorem expChar_negRho (v : Fin r → ℝ) : expChar F n (negRho n r) v = 1 := by
  have h : (modulus F n fun i => Real.exp (v i)) =
      Real.exp (-(2 * Module.finrank ℚ F * ∑ i : Fin r, (i.val - (n - 1) / 2 : ℝ) * v i)) ^ 2 := by
    rw [← Real.exp_nat_mul, Finset.mul_sum, ← Finset.sum_neg_distrib, Finset.mul_sum, Real.exp_sum, modulus]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Real.rpow_intCast, ← Real.exp_mul]
    congr 1
    push_cast
    ring
  rw [expChar, h, Real.sqrt_sq (Real.exp_pos _).le, Complex.ofReal_exp, ← Complex.exp_add]
  simp [negRho]

variable {σ J X Y} in

theorem isExponent_one (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    IsExponent σ J X Y S (fun _ => 1) (negRho n r) :=
  let ⟨a, ha⟩ := exists_isTorusElt h hJ hW (t := fun i => Real.exp (stepSum S 0 i)) fun _ => Real.exp_ne_zero _
  ⟨_, Submodule.subset_span ⟨0, a, ha, rfl⟩, one_ne_zero, fun _ _ _ _ => by rw [expChar_negRho, one_mul]⟩

example : NegExp Finset.univ ∅ (negRho 2 1) ∧ ¬ NegExp Finset.univ ∅ (-negRho 2 1) := by
  simp only [negExp_empty, Finset.mem_univ, forall_const, Fin.forall_fin_one, Finset.sum_filter, Fin.sum_univ_one]
  norm_num [negRho]

example (s : Fin 2 → ℂ) : NegExp Finset.univ {1} s ↔ (s 0).re < (s 1).re := by
  simp only [NegExp, stepSum, Finset.mem_univ, forall_const, Fin.forall_fin_two, Finset.sum_filter, Fin.sum_univ_two]
  simp
  exact ⟨fun ⟨y, h1, h2⟩ => by linarith, fun h => ⟨fun _ => ((s 0).re + (s 1).re) / 2, by linarith, by linarith⟩⟩

section Single

variable {σ J X Y}

omit [NumberField E] in
theorem mem_colSpan_iff {k : Fin r} {y : Fin n → AF F ⊗[F] E} :
    y ∈ colSpan F X {i | i ≤ k} ↔ ∃ a, adMat F (initCols X k) *ᵥ a = y := by
  have : (fun i => (adMat F X)ᵀ i) '' {i | i ≤ k} = Set.range (adMat F (initCols X k)).col := Set.ext fun _ =>
    ⟨fun ⟨i, hi, e⟩ => ⟨⟨i, Nat.lt_succ_of_le hi⟩, e⟩, fun ⟨i, e⟩ => ⟨i.castLE k.2, Nat.le_of_lt_succ i.2, e⟩⟩
  rw [colSpan, this, ← Matrix.range_mulVecLin]
  rfl

omit [NumberField E] in
theorem mem_colPerp_iff {k : Fin r} {y : Fin n → AF F ⊗[F] E} :
    y ∈ colPerp σ J X {i | i ≤ k} ↔ adMat F (cT (σ : E →+* E) (initCols X k) * J) *ᵥ y = 0 := by
  simp only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker]
  exact ⟨fun h => funext fun i => h (i.castLE k.2) (Nat.le_of_lt_succ i.2),
    fun h i hi => congrFun h ⟨i, Nat.lt_succ_of_le hi⟩⟩

theorem unip_singleton (hW : IsWittFrame σ J X Y) (k : Fin r) : unip σ J X {k} = unipRad σ J (initCols X k) := by
  have e1 : {i | ∃ k' ∈ ({k} : Finset (Fin r)), i ≤ k'} = {i | i ≤ k} := by simp
  have e2 : ∀ j, k < j → {i | ∃ k' ∈ ({k} : Finset (Fin r)), i ≤ k' ∧ k' < j} = {i | i ≤ k} := fun j h => by simp [h]
  have e3 : ∀ j, ¬ k < j → colSpan F X {i | ∃ k' ∈ ({k} : Finset (Fin r)), i ≤ k' ∧ k' < j} = ⊥ := fun j h => by
    simp [h, colSpan]
  have c1 : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E), cT (sigR (AF F) σ) (adMat F Z) = adMat F (cT (σ : E →+* E) Z) :=
    fun Z => rfl
  have fix : ∀ g ∈ unip σ J X {k}, (matHom _ σ J g).1 * adMat F (initCols X k) = adMat F (initCols X k) := fun g hg =>
    Matrix.ext_col fun i => by
      have := (Subgroup.mem_iInf.1 hg.1 (i.castLE k.2)).2 _ (Submodule.subset_span ⟨_, rfl, rfl⟩)
      rw [e3 _ (not_lt.2 (Nat.le_of_lt_succ i.2)), Submodule.mem_bot, sub_eq_zero] at this
      exact this
  refine le_antisymm (fun g hg => ?_) ((Subgroup.closure_le _).2 ?_)
  on_goal 1 =>
    apply Subgroup.subset_closure
    refine ⟨?_, ?_, fun x hx => ?_⟩
  · rw [Matrix.sub_mul, fix g hg, Matrix.one_mul, sub_self]
  · have hu : cT (sigR (AF F) σ) (matHom _ σ J g).1 * adMat F J * (matHom _ σ J g).1 = adMat F J := g.2
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero, adMat, Matrix.map_mul]
    change adMat F _ * adMat F J * _ = adMat F _ * adMat F J
    conv_lhs => rw [← c1, ← fix g hg, Formalism.UG.cT_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ (adMat F J), hu, c1]
  · have := hg.2.2 (fun i => inclR (F := F) (AF F) (x i)) (by
      rw [e1, mem_colPerp_iff]
      funext i
      exact (RingHom.map_mulVec (inclR (F := F) (AF F)) _ x i).symm.trans (by rw [hx]; exact map_zero _))
    rw [e1, mem_colSpan_iff] at this
    exact this.imp fun a ha => by rw [sub_mulVec, one_mulVec, ha]
  · rintro g ⟨h1, -, h3⟩
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
    have s1 : ∀ y, y ∈ colSpan F X {i | i ≤ k} ↔ (matHom _ σ J g).1 *ᵥ y ∈ colSpan F X {i | i ≤ k} := fun y => by
      simp only [mem_colSpan_iff]
      refine exists_congr fun a => ?_
      conv_rhs => rw [← h1, ← mulVec_mulVec]
      exact (Matrix.mulVec_injective_of_isUnit (Units.isUnit _)).eq_iff.symm
    have s2 : ∀ y ∈ colPerp σ J X {i | i ≤ k}, (matHom _ σ J g).1 *ᵥ y - y ∈ colSpan F X {i | i ≤ k} := fun y hy => by
      set T := cT (σ : E →+* E) (initCols X k) * J
      have hT : T * initCols Y k = 1 := Matrix.ext fun i j =>
        (congrFun (congrFun hW.xy (i.castLE k.2)) (j.castLE k.2)).trans (by simp [Matrix.one_apply])
      have hQ : T * (1 - initCols Y k * T) = 0 := by
        rw [Matrix.mul_sub, ← Matrix.mul_assoc, hT, Matrix.one_mul, Matrix.mul_one, sub_self]
      have hy' : y = adMat F (1 - initCols Y k * T) *ᵥ y := by
        rw [adMat, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_mul, sub_mulVec,
          one_mulVec, ← mulVec_mulVec, mem_colPerp_iff.1 hy, mulVec_zero, sub_zero]
      have : (matHom _ σ J g).1 *ᵥ y - y = ((matHom _ σ J g).1 - 1).mulVecLin y := by simp [sub_mulVec]
      rw [this, hy', mulVec_eq_sum, map_sum]
      refine sum_mem fun j _ => ?_
      rw [op_smul_eq_smul, map_smul]
      obtain ⟨a, ha⟩ := h3 (fun i => (1 - initCols Y k * T : Matrix (Fin n) (Fin n) E) i j) (funext fun i => congrFun (congrFun hQ i) j)
      exact Submodule.smul_mem _ _ (mem_colSpan_iff.2 ⟨a, ha.symm⟩)
    refine ⟨Subgroup.mem_iInf.2 fun j => ?_, e1.symm ▸ ⟨s1, s2⟩⟩
    by_cases hj : k < j
    · rw [e2 j hj]
      refine ⟨s1, fun y hy => s2 y (Submodule.span_le.2 ?_ hy)⟩
      rintro _ ⟨l, -, rfl⟩
      refine mem_colPerp_iff.2 (funext fun i => ?_)
      exact (RingHom.map_mulVec (inclR (F := F) (AF F)) _ (Xᵀ l) i).symm.trans
        ((congrArg _ (congrFun (congrFun hW.xx (i.castLE k.2)) l)).trans (map_zero _))
    · rw [e3 j hj]
      refine ⟨fun y => ?_, fun y hy => ?_⟩
      · simp only [Submodule.mem_bot]
        exact ⟨fun h => by rw [h, mulVec_zero],
          fun h => Matrix.mulVec_injective_of_isUnit (Units.isUnit _) (h.trans (mulVec_zero _).symm)⟩
      · obtain ⟨a, rfl⟩ := mem_colSpan_iff.1 (Submodule.span_mono (Set.image_mono
          (show {j} ⊆ {i | i ≤ k} from fun _ h => h ▸ not_lt.1 hj)) hy)
        rw [mulVec_mulVec, h1, sub_self]
        exact zero_mem _

theorem isConstAlong_singleton (hW : IsWittFrame σ J X Y) (k : Fin r) {φ c : GAd σ J → ℂ} :
    IsConstAlong σ J X {k} φ c ↔ IsConstTerm σ J (initCols X k) φ c := by
  unfold IsConstAlong
  rw [unip_singleton hW]
  rfl

end Single

section Closed

variable {σ J X Y}

theorem ring_facts : IsTopologicalRing (AF F ⊗[F] E) ∧ T2Space (AF F ⊗[F] E) :=
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  ⟨IsModuleTopology.isTopologicalRing (AF F) _,
    .of_injective_continuous (f := (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).equivFun)
      (LinearEquiv.injective _) (IsModuleTopology.continuous_of_linearMap
        (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).equivFun.toLinearMap)⟩

theorem continuous_mat : Continuous fun g : GAd σ J => (matHom _ σ J g).1 := Units.continuous_val.comp continuous_subtype_val

theorem isClosed_colSpan {L : Matrix (Fin r) (Fin n) E} (hL : L * X = 1) (I : Set (Fin r)) :
    IsClosed (colSpan F X I : Set (Fin n → AF F ⊗[F] E)) := by
  classical
  obtain ⟨_, _⟩ := ring_facts (F := F) (E := E)
  have hL' : adMat F L * adMat F X = 1 := by rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  let P := adMat F X * diagonal (fun i => if i ∈ I then (1 : AF F ⊗[F] E) else 0) * adMat F L
  have : (colSpan F X I : Set (Fin n → AF F ⊗[F] E)) = {y | P *ᵥ y = y} := by
    refine Set.ext fun y => ⟨fun hy => ?_, fun hy => ?_⟩
    · refine (Submodule.span_le (p := LinearMap.eqLocus P.mulVecLin LinearMap.id)).2 ?_ hy
      rintro _ ⟨i, hi, rfl⟩
      change (P * adMat F X).col i = _
      rw [Matrix.mul_assoc, hL', Matrix.mul_one]
      funext j
      simp [hi]
    · rw [← show P *ᵥ y = y from hy]
      unfold P
      rw [Matrix.mul_assoc, ← mulVec_mulVec, mulVec_eq_sum]
      refine sum_mem fun i _ => ?_
      rw [op_smul_eq_smul]
      by_cases hi : i ∈ I
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
      · rw [← mulVec_mulVec, mulVec_diagonal, if_neg hi, zero_mul, zero_smul]
        exact zero_mem _
  exact this ▸ isClosed_eq (continuous_const.matrix_mulVec continuous_id) continuous_id

theorem isClosed_trivOn {A B : Submodule (AF F ⊗[F] E) (Fin n → AF F ⊗[F] E)} (hA : IsClosed (A : Set (Fin n → AF F ⊗[F] E))) :
    IsClosed (trivOn σ J A B : Set (GAd σ J)) := by
  obtain ⟨_, _⟩ := ring_facts (F := F) (E := E)
  have e : ∀ (a : GAd σ J) y, (matHom _ σ J a⁻¹).1 *ᵥ (matHom _ σ J a).1 *ᵥ y = y := fun a y => by
    rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec]
  have : (trivOn σ J A B : Set (GAd σ J)) = (⋂ y ∈ A, {g | (matHom _ σ J g).1 *ᵥ y ∈ A} ∩ {g | (matHom _ σ J g⁻¹).1 *ᵥ y ∈ A}) ∩
      ⋂ y ∈ B, {g | (matHom _ σ J g).1 *ᵥ y - y ∈ A} := Set.ext fun g => by
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨fun y hy => ⟨(h.1 y).1 hy, ((inv_mem h).1 y).1 hy⟩, h.2⟩,
      fun h => ⟨fun y => ⟨fun hy => (h.1 y hy).1, fun hy => e g y ▸ (h.1 _ hy).2⟩, h.2⟩⟩
  rw [this]
  exact (isClosed_biInter fun y _ => (hA.preimage (continuous_mat.matrix_mulVec continuous_const)).inter
    (hA.preimage ((continuous_mat.comp continuous_inv).matrix_mulVec continuous_const))).inter
    (isClosed_biInter fun y _ => hA.preimage ((continuous_mat.matrix_mulVec continuous_const).sub continuous_const))

theorem isClosed_frameStab {k : ℕ} {C : Matrix (Fin n) (Fin k) E} {L : Matrix (Fin k) (Fin n) E} (hL : L * C = 1)
    {H : Subgroup (GL (Fin k) (AF F ⊗[F] E))} (hH : IsClosed (H : Set (GL (Fin k) (AF F ⊗[F] E)))) :
    IsClosed (frameStab σ J C H : Set (GAd σ J)) := by
  obtain ⟨_, _⟩ := ring_facts (F := F) (E := E)
  have hL' : adMat F L * adMat F C = 1 := by rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  let b : GAd σ J → Matrix (Fin k) (Fin k) (AF F ⊗[F] E) := fun g => adMat F L * ((matHom _ σ J g).1 * adMat F C)
  have hb : Continuous b := continuous_const.matrix_mul (continuous_mat.matrix_mul continuous_const)
  have : (frameStab σ J C H : Set (GAd σ J)) = {g | (matHom _ σ J g).1 * adMat F C = adMat F C * b g} ∩
      (fun g => (b g, MulOpposite.op (b g⁻¹))) ⁻¹' (Units.embedProduct _ '' H) := Set.ext fun g => by
    refine ⟨fun ⟨B, hB, e⟩ => ?_, fun ⟨h1, B, hB, e⟩ => ⟨B, hB, h1.trans (congrArg _ (congrArg Prod.fst e).symm)⟩⟩
    have h1 : b g = B := (congrArg (adMat F L * ·) e).trans (by rw [← Matrix.mul_assoc, hL', Matrix.one_mul])
    have h2 : b g⁻¹ = B⁻¹.1 := by
      have : adMat F C = (matHom _ σ J g).1 * (adMat F C * B⁻¹.1) := by
        rw [← Matrix.mul_assoc, e, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      simp only [b]
      rw [this, ← Matrix.mul_assoc (Units.val _), map_inv, Units.inv_mul, Matrix.one_mul, ← Matrix.mul_assoc, hL', Matrix.one_mul]
    exact ⟨e.trans (by rw [h1]), B, hB, by simp only [h1, h2]; rfl⟩
  rw [this]
  exact (isClosed_eq (continuous_mat.matrix_mul continuous_const) (continuous_const.matrix_mul hb)).inter
    ((Units.isClosedEmbedding_embedProduct.isClosedMap _ hH).preimage
      (hb.prodMk (MulOpposite.continuous_op.comp (hb.comp continuous_inv))))

variable (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
include h hJ hW

theorem yx : cT (σ : E →+* E) Y * J * X = 1 := by
  have := congrArg (cT (σ : E →+* E)) hW.xy
  rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, show cT (σ : E →+* E) (cT (σ : E →+* E) X) = X from Matrix.ext fun _ _ => sigma_sigma h _,
    show cT (σ : E →+* E) J = J from Matrix.ext fun i j => hJ.1 i j, Formalism.UG.cT_one, ← Matrix.mul_assoc] at this

theorem isClosed_unip : IsClosed (unip σ J X S : Set (GAd σ J)) := by
  rw [unip, Subgroup.coe_inf, Subgroup.coe_iInf]
  exact (isClosed_iInter fun _ => isClosed_trivOn (isClosed_colSpan (yx h hJ hW) _)).inter
    (isClosed_trivOn (isClosed_colSpan (yx h hJ hW) _))

theorem isClosed_levi : IsClosed (levi σ J X Y S : Set (GAd σ J)) ∧ IsClosed (leviOne σ J X Y S : Set (GAd σ J)) := by
  obtain ⟨_, _⟩ := ring_facts (F := F) (E := E)
  have key : ∀ {L : Matrix (Fin r) (Fin n) E} {C : Matrix (Fin n) (Fin r) E}, L * C = 1 → ∀ k : Fin r,
      L.submatrix (Fin.castLE k.2) id * initCols C k = 1 := fun hL k => Matrix.ext fun i j =>
    (congrFun (congrFun hL (i.castLE k.2)) (j.castLE k.2)).trans (by simp [Matrix.one_apply])
  have h1 : IsClosed (levi σ J X Y S : Set (GAd σ J)) := by
    simp only [levi, Subgroup.coe_iInf, Subgroup.coe_inf]
    exact isClosed_biInter fun k _ => (isClosed_frameStab (key (yx h hJ hW) k) isClosed_univ).inter
      (isClosed_frameStab (key hW.xy k) isClosed_univ)
  refine ⟨h1, ?_⟩
  simp only [leviOne, Subgroup.coe_iInf, Subgroup.coe_inf]
  exact h1.inter (isClosed_biInter fun k _ => isClosed_frameStab (key (yx h hJ hW) k)
    (isClosed_eq (GlobalTheory.Doubling.continuous_absE.comp Matrix.GeneralLinearGroup.continuous_det) continuous_const))

theorem exists_haar_leviOne : ∃ (μ : Measure (leviOne σ J X Y S)) (𝓕 : Set (leviOne σ J X Y S)), μ.IsHaarMeasure ∧
    IsFundamentalDomain ((ratPts σ J).subgroupOf (leviOne σ J X Y S)) 𝓕 μ :=
  haveI := (isClosed_levi S h hJ hW).2.locallyCompactSpace
  ⟨Measure.haar, _, inferInstance, GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom _ _⟩

theorem exists_isSplitElt (u : Fin r → ℝ) : ∃ a, IsSplitElt σ J X Y S u a :=
  exists_isTorusElt h hJ hW fun _ => Real.exp_ne_zero _

end Closed

end GlobalTheory.StdPar

end
