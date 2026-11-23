import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CongAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartReadsAtClassGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsDefiniteLaws
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CongruentOneMemStepLevelLevelCharEqOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalCharDetEqOneOfCongrOneModPow

noncomputable section

namespace GlobalTheory.Transport.Entry

open NumberField IsDedekindDomain Matrix

section Val

variable {L Γ : Type} [Field L] [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ) {a b c : ℕ}

def MLe (A : Matrix (Fin a) (Fin b) L) (γ : Γ) : Prop := ∀ i j, v (A i j) ≤ γ

variable {v}

theorem MLe.mono {A : Matrix (Fin a) (Fin b) L} {γ δ : Γ} (h : MLe v A γ) (hγ : γ ≤ δ) : MLe v A δ :=
  fun i j => (h i j).trans hγ

theorem MLe.mul {A : Matrix (Fin a) (Fin b) L} {B : Matrix (Fin b) (Fin c) L} {γ δ : Γ} (h : MLe v A γ) (h' : MLe v B δ) :
    MLe v (A * B) (γ * δ) := fun i j => by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun t _ => ?_
  rw [map_mul]
  exact mul_le_mul' (h i t) (h' t j)

theorem MLe.add {A B : Matrix (Fin a) (Fin b) L} {γ : Γ} (h : MLe v A γ) (h' : MLe v B γ) : MLe v (A + B) γ :=
  fun i j => Valuation.map_add_le _ (h i j) (h' i j)

theorem MLe.sub {A B : Matrix (Fin a) (Fin b) L} {γ : Γ} (h : MLe v A γ) (h' : MLe v B γ) : MLe v (A - B) γ :=
  fun i j => Valuation.map_sub_le _ (h i j) (h' i j)

theorem mle_one : MLe v (1 : Matrix (Fin a) (Fin a) L) 1 := fun i j => by
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem exists_mle (A : Matrix (Fin a) (Fin b) L) : ∃ m : Γ, 1 ≤ m ∧ MLe v A m := by
  obtain ⟨m, hm⟩ := (Set.finite_range fun p : Fin a × Fin b => v (A p.1 p.2)).bddAbove
  exact ⟨max 1 m, le_max_left _ _, fun i j => (hm ⟨(i, j), rfl⟩).trans (le_max_right _ _)⟩

theorem mle_of_fix {Z W : Matrix (Fin a) (Fin b) L} {D : Matrix (Fin a) (Fin a) L} {γ δ : Γ} (hδ : δ < 1) (hD : MLe v D δ)
    (hW : MLe v W γ) (e : Z = W + D * Z) : MLe v Z γ := by
  intro i j
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ (fun p : Fin a × Fin b => v (Z p.1 p.2)) ⟨(i, j), Finset.mem_univ _⟩
  have hZ : MLe v Z (v (Z p.1 p.2)) := fun r s => hp (r, s) (Finset.mem_univ _)
  refine (hZ i j).trans ?_
  by_contra hlt
  rw [not_le] at hlt
  have h0 : 0 < v (Z p.1 p.2) := lt_of_le_of_lt zero_le' hlt
  have h1 : v ((D * Z) p.1 p.2) < v (Z p.1 p.2) := ((hD.mul hZ) p.1 p.2).trans_lt (mul_lt_of_lt_one_left h0 hδ)
  have h2 := Valuation.map_add_lt v ((hW p.1 p.2).trans_lt hlt) h1
  rw [← Matrix.add_apply, ← e] at h2
  exact lt_irrefl _ h2

theorem exists_inv_of_near {A : Matrix (Fin a) (Fin a) L} {δ : Γ} (hδ : δ < 1) (hA : MLe v (A - 1) δ) :
    ∃ B : Matrix (Fin a) (Fin a) L, A * B = 1 ∧ B * A = 1 ∧ MLe v (B - 1) δ := by
  have hA' : MLe v (1 - A) δ := fun i j => by
    rw [← neg_sub, Matrix.neg_apply, Valuation.map_neg]
    exact hA i j
  have hu : IsUnit A := by
    rw [← Matrix.mulVec_injective_iff_isUnit, ← Matrix.coe_mulVecLin, injective_iff_map_eq_zero]
    intro x hx
    have hx' : A *ᵥ x = 0 := hx
    have h := mle_of_fix (Z := Matrix.of fun i (_ : Fin 1) => x i) (W := 0) (γ := 0) hδ hA' (fun i j => by simp) (by
      ext i j
      have := congrFun hx' i
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
      simp [Matrix.sub_mul, Matrix.mul_apply, this])
    funext i
    simpa using h i 0
  obtain ⟨u, rfl⟩ := hu
  refine ⟨(u⁻¹ : (Matrix (Fin a) (Fin a) L)ˣ), u.mul_inv, u.inv_mul, mle_of_fix hδ hA' hA' ?_⟩
  rw [Matrix.mul_sub, Matrix.sub_mul, u.mul_inv]
  simp

theorem MLe.of_near {A : Matrix (Fin a) (Fin a) L} {δ : Γ} (hδ : δ ≤ 1) (hA : MLe v (A - 1) δ) : MLe v A 1 := by
  have := (hA.mono hδ).add mle_one
  rwa [sub_add_cancel] at this

theorem MLe.near_mul {A B : Matrix (Fin a) (Fin a) L} {δ : Γ} (hδ : δ ≤ 1) (hA : MLe v (A - 1) δ) (hB : MLe v (B - 1) δ) :
    MLe v (A * B - 1) δ := by
  have e : A * B - 1 = A * (B - 1) + (A - 1) := by noncomm_ring
  rw [e]
  have := (hA.of_near hδ).mul hB
  rw [one_mul] at this
  exact this.add hA

end Val

section Approx

open Formalism.L2.Col

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {a b : ℕ}

theorem exists_approx (U : Matrix (Fin a) (Fin b) (P.adicCompletion E)) {δ : WithZero (Multiplicative ℤ)} (hδ : δ ≠ 0) :
    ∃ u : Matrix (Fin a) (Fin b) E, MLe Valued.v (u.map (algebraMap E (P.adicCompletion E)) - U) δ := by
  have h : ∀ z : P.adicCompletion E, ∃ r : E, Valued.v (algebraMap E (P.adicCompletion E) r - z) ≤ δ := fun z => by
    obtain ⟨t, ht⟩ := P.valuation_surjective E δ
    have ht' : Valued.v (algebraMap E (P.adicCompletion E) t) = δ := (GlobalTheory.Mem.Col2.valued_algebraMap P t).trans ht
    have h0 : algebraMap E (P.adicCompletion E) t ≠ 0 := fun h => hδ (by rw [← ht', h, map_zero])
    have ho : IsOpen {y : P.adicCompletion E | y - z / algebraMap E _ t ∈ (Valued.integer (P.adicCompletion E) : Set _)} :=
      (Valued.isOpen_integer (P.adicCompletion E)).preimage (continuous_sub_right _)
    obtain ⟨r, hr⟩ := (P.denseRange_algebraMap E).exists_mem_open ho ⟨z / algebraMap E _ t, by simp⟩
    have hr' : Valued.v (algebraMap E (P.adicCompletion E) r - z / algebraMap E _ t) ≤ 1 := hr
    refine ⟨t * r, ?_⟩
    have e : algebraMap E (P.adicCompletion E) (t * r) - z =
        algebraMap E (P.adicCompletion E) t * (algebraMap E (P.adicCompletion E) r - z / algebraMap E _ t) := by
      rw [map_mul]
      field_simp
    rw [e, map_mul, ht']
    exact mul_le_of_le_one_right' hr'
  choose f hf using h
  exact ⟨Matrix.of fun i j => f (U i j), fun i j => hf _⟩

end Approx

section Local

open Formalism.L2.Col

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {a b : ℕ}

omit [StarRing E] in
theorem mle_map_iff {A : Matrix (Fin a) (Fin b) E} {γ : WithZero (Multiplicative ℤ)} :
    MLe Valued.v (A.map (algebraMap E (P.adicCompletion E))) γ ↔ MLe (P.valuation E) A γ :=
  forall₂_congr fun i j => by rw [Matrix.map_apply, GlobalTheory.Mem.Col2.valued_algebraMap]

theorem intAt_inv_mul {c z : E} (hc : c ≠ 0) (h : P.valuation E z ≤ P.valuation E c) : IntAt P (c⁻¹ * z) := by
  rw [qth_intAt_iff, map_mul, map_inv₀]
  exact inv_mul_le_one_of_le₀ h zero_le'

theorem eq_of_near {K : Type} (Ξ : HomE E a b → K) {c d : E} (hc0 : c ≠ 0) (hc : P.valuation E c < 1) (hd0 : d ≠ 0)
    (hcong : ∀ (k : Sp E a ≃ₗ[E] Sp E a) (k' : Sp E b ≃ₗ[E] Sp E b),
      (∀ s l, IntAt P (c⁻¹ * (k (Pi.single s (1 : E)) l - (Pi.single s (1 : E) : Sp E a) l))) →
      (∀ s l, IntAt P (c⁻¹ * (k' (Pi.single s (1 : E)) l - (Pi.single s (1 : E) : Sp E b) l))) → ∀ x, Ξ (inFr k k' x) = Ξ x)
    (hinv : ∀ x z : HomE E a b, (∀ s l, IntAt P (d⁻¹ * z (Pi.single s 1) l)) → Ξ (x + z) = Ξ x)
    (x x' : HomE E a b) (U : Matrix (Fin a) (Fin a) (P.adicCompletion E)) (U' : Matrix (Fin b) (Fin b) (P.adicCompletion E))
    (hU : MLe Valued.v (U - 1) (P.valuation E c)) (hU' : MLe Valued.v (U' - 1) (P.valuation E c))
    (h : MLe Valued.v (U' * (LinearMap.toMatrix' x').map (algebraMap E (P.adicCompletion E)) -
      (LinearMap.toMatrix' x).map (algebraMap E (P.adicCompletion E)) * U) (P.valuation E d)) : Ξ x' = Ξ x := by
  set ι := algebraMap E (P.adicCompletion E) with hι
  set X := LinearMap.toMatrix' x with hX
  set X' := LinearMap.toMatrix' x' with hX'
  obtain ⟨m, hm1, hm⟩ := exists_mle (v := Valued.v) (X.map ι)
  obtain ⟨m', hm1', hm'⟩ := exists_mle (v := Valued.v) (X'.map ι)
  have m0 : m ≠ 0 := (zero_lt_one.trans_le hm1).ne'
  have m0' : m' ≠ 0 := (zero_lt_one.trans_le hm1').ne'
  have vc : P.valuation E c ≠ 0 := (Valuation.ne_zero_iff _).2 hc0
  have vd : P.valuation E d ≠ 0 := (Valuation.ne_zero_iff _).2 hd0
  obtain ⟨u, hu⟩ := exists_approx P U (δ := min (P.valuation E c) (m⁻¹ * P.valuation E d))
    (lt_min (zero_lt_iff.2 vc) (zero_lt_iff.2 (mul_ne_zero (inv_ne_zero m0) vd))).ne'
  obtain ⟨u', hu'⟩ := exists_approx P U' (δ := min (P.valuation E c) (P.valuation E d * m'⁻¹))
    (lt_min (zero_lt_iff.2 vc) (zero_lt_iff.2 (mul_ne_zero vd (inv_ne_zero m0')))).ne'
  have near : ∀ {n : ℕ} {w : Matrix (Fin n) (Fin n) E} {V : Matrix (Fin n) (Fin n) (P.adicCompletion E)},
      MLe Valued.v (V - 1) (P.valuation E c) → MLe Valued.v (w.map ι - V) (P.valuation E c) →
      MLe (P.valuation E) (w - 1) (P.valuation E c) := fun {n w V} h1 h2 => by
    rw [← mle_map_iff, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
    have := h2.add h1
    rwa [sub_add_sub_cancel] at this
  have n1 := near hU (hu.mono (min_le_left _ _))
  have n2 := near hU' (hu'.mono (min_le_left _ _))
  obtain ⟨t, ht1, ht2, -⟩ := exists_inv_of_near hc n1
  obtain ⟨t', ht1', ht2', ht'⟩ := exists_inv_of_near hc n2
  have hW : MLe (P.valuation E) (u' * X' - X * u) (P.valuation E d) := by
    rw [← mle_map_iff, Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul]
    have e : u'.map ι * X'.map ι - X.map ι * u.map ι =
        (U' * X'.map ι - X.map ι * U) + (u'.map ι - U') * X'.map ι - X.map ι * (u.map ι - U) := by
      rw [Matrix.sub_mul, Matrix.mul_sub]
      abel
    rw [e]
    refine (h.add ?_).sub ?_
    · have := (hu'.mono (min_le_right _ _)).mul hm'
      rwa [inv_mul_cancel_right₀ m0'] at this
    · have := hm.mul (hu.mono (min_le_right _ _))
      rwa [mul_inv_cancel_left₀ m0] at this
  have hZ : MLe (P.valuation E) (t' * (u' * X' - X * u)) (P.valuation E d) := by
    have := (ht'.of_near hc.le).mul hW
    rwa [one_mul] at this
  have hk : ∀ {n : ℕ} {w s : Matrix (Fin n) (Fin n) E} (h1 : w * s = 1) (h2 : s * w = 1), MLe (P.valuation E) (w - 1) (P.valuation E c) →
      ∀ j l, IntAt P (c⁻¹ * (Matrix.toLin'OfInv h2 h1 (Pi.single j (1 : E)) l - (Pi.single j (1 : E) : Sp E n) l)) :=
    fun {n w s} h1 h2 hw j l => by
      refine intAt_inv_mul hc0 ?_
      convert hw l j using 2
      simp [Matrix.one_apply, Pi.single_apply]
  have e : x' = inFr (Matrix.toLin'OfInv ht2 ht1) (Matrix.toLin'OfInv ht2' ht1') x + Matrix.toLin' (t' * (u' * X' - X * u)) := by
    apply LinearMap.toMatrix'.injective
    have e1 : LinearMap.toMatrix' (inFr (Matrix.toLin'OfInv ht2 ht1) (Matrix.toLin'OfInv ht2' ht1') x) = t' * (X * u) := by
      unfold inFr
      rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp]
      congr 2
      · exact LinearMap.toMatrix'_toLin' _
      · exact LinearMap.toMatrix'_toLin' _
    rw [map_add, e1, LinearMap.toMatrix'_toLin', Matrix.mul_sub, ← Matrix.mul_assoc t' u', ht2', Matrix.one_mul]
    abel
  refine (congrArg Ξ e).trans ((hinv _ _ fun s l => intAt_inv_mul hd0 ?_).trans (hcong _ _ (hk ht1 ht2 n1) (hk ht1' ht2' n2) x))
  have e2 : Matrix.toLin' (t' * (u' * X' - X * u)) (Pi.single s 1) l = (t' * (u' * X' - X * u)) l s := by
    rw [Matrix.toLin'_apply, Matrix.mulVec_single_one, Matrix.col_apply]
  rw [e2]
  exact hZ l s

end Local

section Frames

open Formalism.L2.Col Formalism.L2.DIV Formalism.BasicNotions Formalism.UG GlobalTheory.Mem.Col2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] {hc : CMData F E} {a b : ℕ}
  {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

omit [StarRing E] in
theorem val_qOf_lt_one (P : HeightOneSpectrum (𝓞 E)) : P.valuation E ((qOf P : ℕ) : E) < 1 := by
  have h := (P.valuation_lt_one_iff_mem (K := E) ((qOf P : ℕ) : 𝓞 E)).2 (Ideal.absNorm_mem _)
  simpa using h

omit [StarRing E] in
theorem qOf_pos (P : HeightOneSpectrum (𝓞 E)) : 0 < qOf P :=
  Nat.pos_of_ne_zero fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)

theorem mle_frame {g : GL (Fin a) (AfE F E)} {p : DecoF E a ST SG Q} (h : IsPtOf hc g p) (w : SG) :
    MLe Valued.v ((g⁻¹ : GL (Fin a) (AfE F E)).1.map (adAt F w.1) *
      (LinearMap.toMatrix' (p.deco.1.liftFr w).toLinearMap).map (algebraMap E (w.1.adicCompletion E)) - 1) (WithZero.exp (-((1 : ℕ) : ℤ))) := by
  intro r s
  refine AdT.FrameMove.le_exp_neg_one_of_lt_one' ?_
  convert AdT.FrameMove.val_sub_lt_of_liftFr h w r s using 2
  rw [Matrix.sub_apply, Matrix.mul_apply]
  unfold GlobalTheory.Mem.Col2.pullV
  rw [Matrix.mulVec, dotProduct, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_mul, adAt_inclE]
  simp

omit [NumberField E] [StarRing E] in
theorem frame_mul_inFr (f : Sp E a ≃ₗ[E] Sp E a) (f' : Sp E b ≃ₗ[E] Sp E b) (x : HomE E a b) :
    LinearMap.toMatrix' f'.toLinearMap * LinearMap.toMatrix' (inFr f f' x) = LinearMap.toMatrix' x * LinearMap.toMatrix' f.toLinearMap := by
  rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp]
  exact congrArg _ (LinearMap.ext fun z => f'.apply_symm_apply _)

theorem exists_modulus {k y : GL (Fin a) (AfE F E)} {k' y' : GL (Fin b) (AfE F E)} {p q : DecoF E a ST SG Q} {p' q' : DecoF E b ST SG Q}
    (hp : IsPtOf hc k p) (hp' : IsPtOf hc k' p') (hq : IsPtOf hc (y * k) q) (hq' : IsPtOf hc (y' * k') q') (w : SG) {d : E} (hd : d ≠ 0) :
    ∃ M : ℕ, 0 < M ∧ ∀ M₀ : ℕ, M ∣ M₀ → ∀ x x₀ : HomE E a b,
      (∀ r s, Valued.v (adAt F w.1 (((y'⁻¹ : GL (Fin b) (AfE F E)).1 *
        ((LinearMap.toMatrix' x).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin b) (Fin a) (AfE F E)) * y.1 -
          ((LinearMap.toMatrix' x₀).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin b) (Fin a) (AfE F E))) r s)) ≤
        Valued.v ((M₀ : ℕ) : w.1.adicCompletion E)) →
      ∃ (U : Matrix (Fin a) (Fin a) (w.1.adicCompletion E)) (U' : Matrix (Fin b) (Fin b) (w.1.adicCompletion E)),
        MLe Valued.v (U - 1) (WithZero.exp (-((1 : ℕ) : ℤ))) ∧ MLe Valued.v (U' - 1) (WithZero.exp (-((1 : ℕ) : ℤ))) ∧
        MLe Valued.v (U' * (LinearMap.toMatrix' (inFr (q.deco.1.liftFr w) (q'.deco.1.liftFr w) x)).map (algebraMap E (w.1.adicCompletion E)) -
          (LinearMap.toMatrix' (inFr (p.deco.1.liftFr w) (p'.deco.1.liftFr w) x₀)).map (algebraMap E (w.1.adicCompletion E)) * U)
          (w.1.valuation E d) := by
  have h1 : (WithZero.exp (-((1 : ℕ) : ℤ)) : WithZero (Multiplicative ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hA := mle_frame hp w
  have hA' := mle_frame hp' w
  have hC := mle_frame hq w
  have hC' := mle_frame hq' w
  obtain ⟨Ai, e1, -, hAi⟩ := exists_inv_of_near h1 hA
  obtain ⟨Ai', -, e2, hAi'⟩ := exists_inv_of_near h1 hA'
  set ι := algebraMap E (w.1.adicCompletion E) with hι
  set φ := adAt F w.1 with hφ
  have hinv : ∀ {n : ℕ} (g : GL (Fin n) (AfE F E)), g.1.map φ * (g⁻¹ : GL (Fin n) (AfE F E)).1.map φ = 1 := fun g => by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨m, hm1, hm⟩ := exists_mle (v := Valued.v) (k.1.map φ)
  obtain ⟨m', hm1', hm'⟩ := exists_mle (v := Valued.v) ((k'⁻¹ : GL (Fin b) (AfE F E)).1.map φ)
  have m0 : m ≠ 0 := (zero_lt_one.trans_le hm1).ne'
  have m0' : m' ≠ 0 := (zero_lt_one.trans_le hm1').ne'
  have vd : w.1.valuation E d ≠ 0 := (Valuation.ne_zero_iff _).2 hd
  obtain ⟨n, hn⟩ := exists_pow_lt₀ (val_qOf_lt_one w.1)
    (Units.mk0 (m'⁻¹ * w.1.valuation E d * m⁻¹) (mul_ne_zero (mul_ne_zero (inv_ne_zero m0') vd) (inv_ne_zero m0)))
  refine ⟨qOf w.1 ^ n, pow_pos (qOf_pos _) n, fun M₀ hM x x₀ hx => ⟨_, _, hAi.near_mul h1.le hC, hAi'.near_mul h1.le hC', ?_⟩⟩
  have hM₀ : Valued.v ((M₀ : ℕ) : w.1.adicCompletion E) ≤ m'⁻¹ * w.1.valuation E d * m⁻¹ := by
    obtain ⟨c, rfl⟩ := hM
    rw [← map_natCast ι, valued_algebraMap, Nat.cast_mul, map_mul, Nat.cast_pow, map_pow]
    refine (mul_le_of_le_one_right' ?_).trans hn.le
    simpa using w.1.valuation_le_one (K := E) (c : 𝓞 E)
  have hin : ∀ z : HomE E a b, ((LinearMap.toMatrix' z).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin b) (Fin a) (AfE F E)).map φ = (LinearMap.toMatrix' z).map ι := fun z => Matrix.ext fun i j => adAt_inclE F w.1 _
  have hZ : MLe Valued.v ((y'⁻¹ : GL (Fin b) (AfE F E)).1.map φ * (LinearMap.toMatrix' x).map ι * y.1.map φ -
      (LinearMap.toMatrix' x₀).map ι) (m'⁻¹ * w.1.valuation E d * m⁻¹) := fun r s => by
    rw [← hin, ← hin, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_sub _ (map_sub _)]
    exact (hx r s).trans hM₀
  have f1 := congrArg (fun A => Matrix.map A ι) (frame_mul_inFr (q.deco.1.liftFr w) (q'.deco.1.liftFr w) x)
  have f2 := congrArg (fun A => Matrix.map A ι) (frame_mul_inFr (p.deco.1.liftFr w) (p'.deco.1.liftFr w) x₀)
  simp only [Matrix.map_mul] at f1 f2
  have i1 := hinv (y * k)
  have i2 := hinv k
  rw [Units.val_mul, Matrix.map_mul] at i1
  have i3 : ((y' * k')⁻¹ : GL (Fin b) (AfE F E)).1.map φ =
      (k'⁻¹ : GL (Fin b) (AfE F E)).1.map φ * (y'⁻¹ : GL (Fin b) (AfE F E)).1.map φ := by
    rw [_root_.mul_inv_rev, Units.val_mul, Matrix.map_mul]
  rw [i3]
  have key := (((hAi'.of_near h1.le).mul hm').mul hZ).mul (hm.mul (hC.of_near h1.le))
  rw [one_mul, mul_one, mul_assoc m'⁻¹, mul_inv_cancel_left₀ m0', inv_mul_cancel_right₀ m0] at key
  convert key using 1
  generalize (LinearMap.toMatrix' (inFr (q.deco.1.liftFr w) (q'.deco.1.liftFr w) x)).map ι = Xq at *
  generalize (LinearMap.toMatrix' (inFr (p.deco.1.liftFr w) (p'.deco.1.liftFr w) x₀)).map ι = Xp at *
  generalize (LinearMap.toMatrix' (q.deco.1.liftFr w).toLinearMap).map ι = Fq at *
  generalize (LinearMap.toMatrix' (q'.deco.1.liftFr w).toLinearMap).map ι = Fq' at *
  generalize (LinearMap.toMatrix' (p.deco.1.liftFr w).toLinearMap).map ι = Fp at *
  generalize (LinearMap.toMatrix' (p'.deco.1.liftFr w).toLinearMap).map ι = Fp' at *
  generalize (LinearMap.toMatrix' x).map ι = X at *
  generalize (LinearMap.toMatrix' x₀).map ι = X₀ at *
  generalize ((y * k)⁻¹ : GL (Fin a) (AfE F E)).1.map φ = G at *
  generalize (k⁻¹ : GL (Fin a) (AfE F E)).1.map φ = Ki at *
  generalize (k'⁻¹ : GL (Fin b) (AfE F E)).1.map φ = Ki' at *
  generalize (y'⁻¹ : GL (Fin b) (AfE F E)).1.map φ = Yi' at *
  generalize k.1.map φ = Km at *
  generalize y.1.map φ = Ym at *
  have g1 : Fq = Ym * (Km * (G * Fq)) := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, i1, Matrix.one_mul]
  have g2 : Fp * Ai = Km := by
    rw [← Matrix.one_mul (Fp * Ai), ← i2, Matrix.mul_assoc, ← Matrix.mul_assoc Ki, e1, Matrix.mul_one]
  have g3 : Xp = Ai' * (Ki' * (X₀ * Fp)) := by rw [← f2, ← Matrix.mul_assoc Ki', ← Matrix.mul_assoc, e2, Matrix.one_mul]
  rw [Matrix.mul_sub, Matrix.sub_mul]
  congr 1
  · simp only [Matrix.mul_assoc]
    rw [f1, ← g1]
  · rw [g3, ← g2]
    simp only [Matrix.mul_assoc]

end Frames

section Chain

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col

theorem xiAt_inFr {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}
    (hX : X.AbelianUnramifiedExtensionConditions) (hPr : Pr.Ok) (hCh : Ch.Ok) (hsel : IsSel X sel) (hL : L.Ok Ch sel mu cst G m2) {i : ℕ} (hi : i < m2) (al : L.β i) (be : L.β (i + 1))
    (P : rowSG Pr sel mu) (k : Sp X.E (R.N i) ≃ₗ[X.E] Sp X.E (R.N i)) (k' : Sp X.E (R.N (i + 1)) ≃ₗ[X.E] Sp X.E (R.N (i + 1)))
    (hk : ∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k (Pi.single s (1 : X.E)) l - (Pi.single s (1 : X.E) : Sp X.E (R.N i)) l)))
    (hk' : ∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k' (Pi.single s (1 : X.E)) l - (Pi.single s (1 : X.E) : Sp X.E (R.N (i + 1))) l)))
    (x : HomE X.E (R.N i) (R.N (i + 1))) :
    XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) (inFr k k' x) = XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) x := by
  obtain ⟨r, hr, hrk, hc⟩ := GlobalTheory.LevOne.cong_mem_level_chr_one Ch sel mu cst L G m2 hX hPr hCh hsel hL i hi.le al P k hk
  obtain ⟨r', hr', hrk', hc'⟩ := GlobalTheory.LevOne.cong_mem_level_chr_one Ch sel mu cst L G m2 hX hPr hCh hsel hL (i + 1) hi be P k' hk'
  have h := GlobalTheory.UnfoldTwoSided.xiAt_two_sided Ch sel mu cst L G m2 hX hPr hCh hsel hL i hi al be P r r' k k' hr hr' hrk hrk' x
  rw [hc, hc', GlobalTheory.AwayMat.muAt_det_congr_one Ch sel mu cst L G m2 hX hPr hsel hL i P _ k hk,
    GlobalTheory.AwayMat.muAt_det_congr_one Ch sel mu cst L G m2 hX hPr hsel hL i P _ k' hk'] at h
  simpa only [one_mul] using h

theorem exp_le_val_qOf {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} (h : GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P) :
    WithZero.exp (-((1 : ℕ) : ℤ)) ≤ P.valuation E ((qOf P : ℕ) : E) := by
  have h1 : ¬ P.valuation E ((qOf P : ℕ) : E) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := fun h1 => h.2 <| by
    rw [← P.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := E)]
    simpa using h1
  have h0 : P.valuation E ((qOf P : ℕ) : E) ≠ 0 := fun h0 => h1 (h0 ▸ zero_le')
  rw [← WithZero.exp_log h0, WithZero.exp_le_exp] at h1 ⊢
  omega

end Chain

end GlobalTheory.Transport.Entry

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Transport.Entry

theorem entry_transport : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (u : B.Word) (i : ℕ) (hm : i + 2 < B.R.m) (al : (I.idx I.mu0).β i) (be : (I.idx I.mu0).β (i + 1)) (P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup I.mu0))
    (p q : PtAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) u (i)) (p' q' : PtAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) u (i + 1))
    (k y : TC.GA B (B.R.N (i))) (k' y' : TC.GA B (B.R.N (i + 1))),
    TC.PtOf k p.1.1 → p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i)) →
    TC.PtOf k' p'.1.1 → p'.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i + 1)) →
    TC.PtOf (y * k) q.1.1 → TC.PtOf (y' * k') q'.1.1 →
    ∃ M : ℕ, 0 < M ∧ ∀ M₀ : ℕ, M ∣ M₀ → ∀ x x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)),
      GlobalTheory.Transport.CongAt B P.1 M₀ y y' x x₀ →
      Formalism.L2.Col.XiAt I.Ch I.sel (I.tup I.mu0) (I.cst I.mu0) i P ((I.idx I.mu0).h i al P) ((I.idx I.mu0).h (i + 1) be P)
                (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup I.mu0) p.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup I.mu0) p'.1.1 P) x₀) =
        Formalism.L2.Col.XiAt I.Ch I.sel (I.tup I.mu0) (I.cst I.mu0) i P ((I.idx I.mu0).h i al P) ((I.idx I.mu0).h (i + 1) be P)
          (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup I.mu0) q.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup I.mu0) q'.1.1 P) x) := by
  intro B X I hI l u i hm al be P p q p' q' k y k' y' hp _ hp' _ hq hq'
  have hX := (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).1
  have hL := hI.idx_ok I.mu0
  have hP : P.1 ∈ (B.primes X).vGs := (Finset.mem_union.1 P.2).resolve_right fun h => by
    have h' : P.1 ∈ I.Q I.mu0 := h
    rw [I.twistPrimes_reference_tuple_eq_empty] at h'
    exact Finset.notMem_empty _ h'
  have hq0 : ((Formalism.L2.Col.qOf P.1 : ℕ) : B.fields.E) ≠ 0 := Nat.cast_ne_zero.2 (qOf_pos P.1).ne'
  obtain ⟨M, hM, H⟩ := exists_modulus hp hp' hq hq' ⟨P.1, hP⟩ (pow_ne_zero (I.cst I.mu0).B hq0)
  refine ⟨M, hM, fun M₀ hM₀ x x₀ hx => ?_⟩
  obtain ⟨U, U', hU, hU', h⟩ := H M₀ hM₀ x x₀ hx
  have hu := exp_le_val_qOf (GlobalTheory.UnfoldTwoSided.degOne_bad hX.ok l.pr hI.sel_ok P)
  unfold Formalism.L2.Col.frsF
  simp only [dif_pos hP]
  refine (eq_of_near (P := P.1) _ hq0 (val_qOf_lt_one P.1) (pow_ne_zero (I.cst I.mu0).B hq0) (fun κ κ' hκ hκ' z => ?_)
    (hL.xiInv i (by omega) al be P) _ _ U U' (hU.mono hu) (hU'.mono hu) h).symm
  refine xiAt_inFr hX l.pr hI.ch_ok hI.sel_ok hL (by omega) al be P κ κ' ?_ ?_ z
  · rw [hL.depthG P hP, pow_one]
    exact hκ
  · rw [hL.depthG P hP, pow_one]
    exact hκ'

end GlobalTheory.Transport.Entry
