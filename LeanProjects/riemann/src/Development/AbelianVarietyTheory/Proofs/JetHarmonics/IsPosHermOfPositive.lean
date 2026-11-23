import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETPointStatement
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.SpansOverField
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.BalancedHermitianSpace
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.PremisesInhabited
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumPosOfTensorPos

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PointStepCompare

open NumberField IsLocalRing ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.IndefiniteRowSideFullHecke.PairingFromOuterAgreement
open GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace (Bil leastExponent IsIntegralFn IsPositiveFn IsBalancedSpace evalSum)

def SpanOneModulus : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y]
    [Module.Finite ℤ Y] (R' : ℕ), 2 ≤ R' → ∀ (r : ℕ) (y z : Fin r → Y),
    (∀ a : Y, ∃ u ∈ Submodule.span (𝓞 E) (Set.range y), ∃ t : Y, a = u + R' • t) →
    ∀ a : Y, ∃ n : ℕ, 0 < n ∧
      n • a ∈ Submodule.span (𝓞 E) (Set.range fun b => y b + R' • z b)

section Lattice

variable (E : Type) [Field E] {X : Type} [AddCommGroup X] [Module (𝓞 E) X]

variable (X) in

def intTorsion : Submodule (𝓞 E) X where
  carrier := {x | ∃ n : ℕ, 0 < n ∧ n • x = 0}
  add_mem' := by
    rintro x y ⟨n, hn, hx⟩ ⟨m, hm, hy⟩
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    rw [smul_add, mul_smul n m y, hy, mul_comm, mul_smul, hx, smul_zero, smul_zero, add_zero]
  zero_mem' := ⟨1, one_pos, smul_zero _⟩
  smul_mem' := by
    rintro c x ⟨n, hn, hx⟩
    exact ⟨n, hn, by rw [smul_comm, hx, smul_zero]⟩

end Lattice

section Phi

variable (E : Type) [Field E] [NumberField E]

theorem trace_pos {u : 𝓞 E} (h : ∀ τ : E →+* ℂ, 0 < (τ (u : E)).re) :
    0 < Algebra.trace ℤ (𝓞 E) u := by
  have h1 := congrArg Complex.re (trace_eq_sum_embeddings ℂ (K := ℚ) (L := E) (x := (u : E)))
  rw [← Algebra.coe_trace_int, Complex.re_sum] at h1
  have h2 : 0 < ∑ σ : E →ₐ[ℚ] ℂ, (σ (u : E)).re := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact Finset.sum_pos (fun σ _ => h σ.toRingHom) ⟨τ.toRatAlgHom, Finset.mem_univ _⟩
  rw [← h1] at h2
  simpa using h2

variable {X : Type} [AddCommGroup X] [Module (𝓞 E) X]

theorem smul_ne_zero_of_free [Module.Free ℤ X] {c : 𝓞 E} {x : X} (hc : c ≠ 0) (hx : x ≠ 0) :
    c • x ≠ 0 := by
  intro h
  obtain ⟨r, hr, α, hα⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) c).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hc)
  have : r • x = 0 := by
    rw [← algebraMap_smul (𝓞 E) r x, hα, mul_comm, mul_smul, h, smul_zero]
  exact hx ((smul_eq_zero.1 this).resolve_left hr)

theorem projective_of_free [Module.Free ℤ X] [Module.Finite ℤ X] : Module.Projective (𝓞 E) X := by
  have : Module.Finite (𝓞 E) X := Module.Finite.of_restrictScalars_finite ℤ _ _
  have : Module.Flat (𝓞 E) X := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    rintro x ⟨c, hc⟩
    by_contra hx
    exact smul_ne_zero_of_free E (nonZeroDivisors.coe_ne_zero c) hx hc
  have : Module.FinitePresentation (𝓞 E) X := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

variable [IsCMField E]

theorem bar_bar (a : 𝓞 E) : bar E (bar E a) = a := by
  ext; simp [IsCMField.coe_ringOfIntegersComplexConj]

theorem emb_bar (τ : E →+* ℂ) (a : 𝓞 E) : τ (bar E a : E) = starRingEnd ℂ (τ (a : E)) :=
  IsCMField.complexEmbedding_complexConj E τ _

theorem trace_bar (a : 𝓞 E) : Algebra.trace ℤ (𝓞 E) (bar E a) = Algebra.trace ℤ (𝓞 E) a :=
  Algebra.trace_eq_of_algEquiv ((IsCMField.ringOfIntegersComplexConj E).restrictScalars ℤ) a

theorem sum_pos_of_isPosHerm [Module.Free ℤ X] [Module.Finite ℤ X] {n : ℕ} {x x' : Fin n → X}
    (hl : IsPosHerm E (outer E x x')) (γ : Bil X) (hγ : GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.IsBalanced E γ)
    (hp : ∀ a, 0 ≤ γ a a) (h0 : γ ≠ 0) : 0 < ∑ i, γ (x i) (x' i) := by
  obtain ⟨N, ι, _, ω, θ, hN, hsum, htr⟩ := exists_traceDual E
  have htr' : ∀ (f : X →ₗ[ℤ] ℤ) (a : X) (α : 𝓞 E),
      Algebra.trace ℤ (𝓞 E) (α * ∑ s, f (ω s • a) • θ s) = N * f (α • a) := fun f a α =>
    htr (f ∘ₗ (LinearMap.toSpanSingleton (𝓞 E) X a).restrictScalars ℤ) α
  let up : (X →ₗ[ℤ] ℤ) → Module.Dual (𝓞 E) X := fun f =>
    { toFun := fun a => ∑ s, f (ω s • a) • θ s
      map_add' := fun a b => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c a => by
        rw [← sub_eq_zero]
        refine eq_zero_of_trace_mul E fun α => ?_
        rw [mul_sub, map_sub, htr', RingHom.id_apply, smul_eq_mul, ← mul_assoc, htr', mul_smul,
          sub_self] }
  have hup : ∀ f a, up f a = ∑ s, f (ω s • a) • θ s := fun _ _ => rfl
  have key : ∀ f g : X →ₗ[ℤ] ℤ, Algebra.trace ℤ (𝓞 E) (outer E x x' (up f) (up g)) =
      N * ∑ p : Fin n × ι, f (ω p.2 • x p.1) * g (bar E (θ p.2) • x' p.1) := by
    intro f g
    rw [outer, map_sum, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hup f, Finset.sum_mul, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    have e : θ s * bar E (up g (x' i)) = bar E (bar E (θ s) * up g (x' i)) := by
      conv_lhs => rw [← bar_bar E (θ s)]
      exact (map_mul (IsCMField.ringOfIntegersComplexConj E) _ _).symm
    rw [smul_mul_assoc, map_smul, e, trace_bar, hup g, htr', smul_eq_mul]
    ring
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  have h1 := sum_pos_of_tensor_pos X (Fin n × ι) (fun p => ω p.2 • x p.1) (fun p => bar E (θ p.2) • x' p.1)
    (fun f g => by
      apply mul_left_cancel₀ hN'.ne'
      rw [← key, ← key, hl.1 (up g) (up f), trace_bar])
    (fun f hf => by
      have hne : up f ≠ 0 := by
        intro h
        apply hf
        ext a
        have := htr' f a 1
        rw [← hup, h] at this
        simpa [hN.ne'] using this
      have := trace_pos E (hl.2 _ hne)
      rw [key] at this
      exact pos_of_mul_pos_right this hN'.le) γ hγ.1 hp h0
  have h2 : ∑ p : Fin n × ι, γ (ω p.2 • x p.1) (bar E (θ p.2) • x' p.1) =
      N * ∑ i, γ (x i) (x' i) := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : ∀ s, γ (ω s • x i) (bar E (θ s) • x' i) = γ ((θ s * ω s) • x i) (x' i) := fun s => by
      rw [← hγ.2, mul_smul]
    simp only [this]
    rw [← LinearMap.sum_apply, ← map_sum, ← Finset.sum_smul, hsum, Nat.cast_smul_eq_nsmul, map_nsmul,
      LinearMap.smul_apply, nsmul_eq_mul]
  rw [h2] at h1
  exact pos_of_mul_pos_right h1 (Nat.cast_nonneg N)

def rankOne (η : Module.Dual (𝓞 E) X) (τ : E →+* ℂ) : Bil X :=
  LinearMap.mk₂ ℤ (fun a c => (τ (η a : E) * starRingEnd ℂ (τ (η c : E))).re)
    (fun a a' c => by simp [add_mul])
    (fun k a c => by simp [mul_assoc, mul_add])
    (fun a c c' => by simp [mul_add])
    (fun k a c => by simp [mul_add, mul_left_comm])

omit [IsCMField E] in
theorem rankOne_apply (η : Module.Dual (𝓞 E) X) (τ : E →+* ℂ) (a c : X) :
    rankOne E η τ a c = (τ (η a : E) * starRingEnd ℂ (τ (η c : E))).re := rfl

theorem rankOne_balanced (η : Module.Dual (𝓞 E) X) (τ : E →+* ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.IsBalanced E (rankOne E η τ) := by
  refine ⟨fun a c => by simp [rankOne_apply, mul_comm], fun e a c => ?_⟩
  rw [rankOne_apply, rankOne_apply, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  push_cast
  rw [map_mul, map_mul, emb_bar E τ e, map_mul, Complex.conj_conj]
  congr 1; ring

theorem outer_append {n : ℕ} (x x' : Fin n → X) (η η' : Module.Dual (𝓞 E) X) :
    outer E (Fin.append x x') (Fin.append x' x) η η' = outer E x x' η η' + outer E x' x η η' := by
  simp only [outer, Fin.sum_univ_add, Fin.append_left, Fin.append_right]

omit [NumberField E] [IsCMField E] [Module (𝓞 E) X] in
theorem pairing_append (γ : Bil X) (hγ : ∀ a c, γ a c = γ c a) {n : ℕ} (x x' : Fin n → X) :
    pairing (fun a c => γ a c) (Fin.append x x') (Fin.append x' x) = ∑ i, γ (x i) (x' i) := by
  simp only [pairing, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  rw [Finset.sum_congr rfl fun i _ => hγ (x' i) (x i)]
  ring

theorem bar_outer {n : ℕ} (x x' : Fin n → X) (η η' : Module.Dual (𝓞 E) X) :
    bar E (outer E x x' η η') = outer E x' x η' η := by
  have := bar_bar E
  simp only [outer, bar, map_sum, map_mul] at this ⊢
  simp only [this, mul_comm]

theorem re_outer {n : ℕ} (x x' : Fin n → X) (η : Module.Dual (𝓞 E) X) (τ : E →+* ℂ) :
    (τ (outer E x x' η η : E)).re = ∑ i, rankOne E η τ (x i) (x' i) := by
  simp only [outer, rankOne_apply]
  push_cast
  rw [map_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← emb_bar]

variable {S : Submodule ℝ (Bil X)}

theorem isPosHerm_of_positive (hS : IsBalancedSpace E S) {n : ℕ} {x x' : Fin n → X}
    (h : ∀ γ : S, (∀ a, 0 ≤ (γ : Bil X) a a) → γ ≠ 0 → 0 < ∑ i, (γ : Bil X) (x i) (x' i)) :
    IsPosHerm E (outer E (Fin.append x x') (Fin.append x' x)) := by
  refine ⟨fun η η' => ?_, fun η hη τ => ?_⟩
  · rw [outer_append, outer_append, ← bar_outer E x' x η η', ← bar_outer E x x' η η', add_comm]
    exact (map_add (IsCMField.ringOfIntegersComplexConj E) _ _).symm
  · have h1 := pairing_append _ (rankOne_balanced E η τ).1 x x'
    have h2 := h ⟨_, (hS _).2 (rankOne_balanced E η τ)⟩
      (fun a => by
        show 0 ≤ rankOne E η τ a a
        rw [rankOne_apply, Complex.mul_conj, Complex.ofReal_re]; exact Complex.normSq_nonneg _)
      (fun h0 => hη (LinearMap.ext fun a => by
        have : rankOne E η τ a a = 0 := congrArg (fun β : S => (β : Bil X) a a) h0
        rw [rankOne_apply, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_zero] at this
        simpa using this))
    rw [re_outer]
    simp only [pairing] at h1
    simp only at h2
    linarith

variable [Module.Free ℤ X] [Module.Finite ℤ X]

theorem exists_exponent (hS : IsBalancedSpace E S) (l : S →ₗ[ℝ] ℝ) (hi : IsIntegralFn S l)
    (hp : IsPositiveFn S l) : ∃ (n : ℕ) (x x' : Fin n → X), IsPosHerm E (outer E x x') ∧
      ∀ β : S, l β = pairing (fun a c => (β : Bil X) a c) x x' := by
  obtain ⟨m, x, x', hx⟩ := exists_eq_sum_eval X S (fun γ hγ => (hS γ).2
    ⟨fun a c => hγ _ _ _ _ fun β hβ => ((hS β).1 hβ).1 a c,
      fun e a c => hγ _ _ _ _ fun β hβ => ((hS β).1 hβ).2 e a c⟩) l hi
  exact ⟨_, _, _, isPosHerm_of_positive E hS fun γ h1 h2 => hx γ ▸ hp γ h1 h2,
    fun β => by rw [pairing_append _ ((hS _).1 β.2).1, hx]⟩

theorem exists_functional (hS : IsBalancedSpace E S) {w : 𝓞 E} (hw : w + bar E w = 1) {n : ℕ}
    {x x' : Fin n → X} (hl : IsPosHerm E (outer E x x')) :
    ∃ l : S →ₗ[ℝ] ℝ, IsIntegralFn S l ∧ IsPositiveFn S l ∧
      ∀ β : S, l β = pairing (fun a c => (β : Bil X) a c) x x' := by
  have : Module.Finite (𝓞 E) X := Module.Finite.of_restrictScalars_finite ℤ _ _
  have := projective_of_free E (X := X)
  have ho : outer E (Fin.append (fun i => w • x i) x') (Fin.append x' fun i => w • x i) =
      outer E x x' := by
    funext η η'
    have e1 : outer E (fun i => w • x i) x' η η' = w * outer E x x' η η' := by
      simp [outer, Finset.mul_sum, mul_assoc]
    have e2 : outer E (fun i => w • x i) x' η' η = w * outer E x x' η' η := by
      simp [outer, Finset.mul_sum, mul_assoc]
    rw [outer_append, ← bar_outer E (fun i => w • x i) x' η' η, e1, e2, hl.1 η η']
    have e3 : bar E (w * bar E (outer E x x' η η')) = bar E w * outer E x x' η η' := by
      conv_rhs => rw [← bar_bar E (outer E x x' η η')]
      exact map_mul (IsCMField.ringOfIntegersComplexConj E) _ _
    rw [e3, ← add_mul, hw, one_mul]
  have hv : ∀ β : S, evalSum S (fun i => w • x i) x' β =
      pairing (fun a c => (β : Bil X) a c) x x' := fun β => by
    rw [← pairing_eq_of_outer_eq E (β : Bil X) ((hS _).1 β.2).2 _ _ _ _ ho,
      pairing_append _ ((hS _).1 β.2).1]
    rfl
  refine ⟨_, GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.isIntegralFn_evalSum S _ _, fun γ h1 h2 => ?_, hv⟩
  rw [hv, pairing]
  exact half_pos (sum_pos_of_isPosHerm E hl _ ((hS _).1 γ.2) h1 fun h => h2 (Subtype.ext h))

theorem exists_admissible (hS : IsBalancedSpace E S) :
    ∃ l : S →ₗ[ℝ] ℝ, IsIntegralFn S l ∧ IsPositiveFn S l := by
  let b := Module.finBasis ℤ X
  refine ⟨evalSum S b b, GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.isIntegralFn_evalSum S _ _, fun γ h1 h2 => ?_⟩
  refine sum_pos_of_isPosHerm E ⟨fun η η' => (bar_outer E _ _ _ _).symm, fun η hη τ => ?_⟩ _
    ((hS _).1 γ.2) h1 fun h => h2 (Subtype.ext h)
  rw [re_outer]
  simp only [rankOne_apply, Complex.mul_conj, Complex.ofReal_re]
  refine lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) fun h0 => hη ?_
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Complex.normSq_nonneg _).1 h0.symm
  have : η.restrictScalars ℤ = 0 := b.ext fun i => by simpa using hz i (Finset.mem_univ _)
  exact LinearMap.ext fun a => LinearMap.congr_fun this a

end Phi

abbrev FormSpaces : Type 1 :=
  ∀ (E : Type) [Field E] [NumberField E] (_ : E → E) (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y],
    Submodule ℝ (Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ)

abbrev FormValues (S : FormSpaces) : Type 1 :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E) (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y],
    S E cj Y → ℝ

def AreBalancedSpaces (S : FormSpaces) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E) (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y]
    (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ), β ∈ S E cj Y ↔ (∀ a b, β a b = β b a) ∧
      ∀ c c' : 𝓞 E, (c' : E) = cj c → ∀ a b, β (c • a) b = β a (c' • b)

def AreLeastValues (S : FormSpaces) (φ : FormValues S) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E) (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y]
    (b : S E cj Y), φ E cj Y b = sInf {x | ∃ l : S E cj Y →ₗ[ℝ] ℝ,
      (∀ β : S E cj Y, (∀ a c, ∃ z : ℤ, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) → ∃ z : ℤ, l β = z) ∧
      (∀ β : S E cj Y, (∀ a, 0 ≤ (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) → β ≠ 0 → 0 < l β) ∧ x = l b}

def PointOver (S : FormSpaces) (φ : FormValues S) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E),
    (∀ c : 𝓞 E, ∃ c' : 𝓞 E, (c' : E) = cj c) →
    ∀ w₀ : 𝓞 E, (w₀ : E) + cj w₀ = 1 →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) [Module (𝓞 E) D.toPre.X] (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q →
    ∀ β : S E cj D.toPre.X, (∀ a b, (β : D.toPre.X →ₗ[ℤ] D.toPre.X →ₗ[ℤ] ℝ) a b = QForm.bOf D.toPre Q a b) →
    (∀ a, (β : D.toPre.X →ₗ[ℤ] D.toPre.X →ₗ[ℤ] ℝ) a a = 2 * (Q a : ℝ)) →
    (∀ a, 0 ≤ (β : D.toPre.X →ₗ[ℤ] D.toPre.X →ₗ[ℤ] ℝ) a a) →
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
    ∀ (R' R₀ : ℕ), 2 ≤ R' → 2 ≤ R₀ → R₀ ∣ R' → ∀ (r : ℕ) (y : Fin r → D.toPre.X),
      (∀ a : D.toPre.X, ∃ u ∈ Submodule.span (𝓞 E) (Set.range y), ∃ t : D.toPre.X, a = u + R₀ • t) →
    ∀ (s : Fin r → Fam D.toPre F (R' ^ 2)) (w : Fin r → F),
      (∀ b (α : D.toPre.X), (∀ z : D.toPre.X, α ≠ y b + R' • z) → ∀ j, ((s b).s α).f j = 0) →
      (∀ b, NuGe D Q F v (R' ^ 2) (s b) 0) → (∀ b, ValAt0 D F v (R' ^ 2) (s b) (w b)) →
      ∀ q : ℚ, (q : ℝ) ≤ φ E cj D.toPre.X β / (R' ^ 2 : ℝ) → ((q : ℚ) : WithTop ℚ) ≤ ∑ b, v (w b)

def ValuationStepFor (C : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Prop) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Module (𝓞 E) D.toPre.X], C E →
      IsBalanced E (fun χ χ' : D.toPre.X => (QForm.bOf D.toPre Q χ χ' : ℝ)) →
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
    ∀ (r₁ R : ℕ), 2 ≤ r₁ → 1 ≤ R → r₁ ∣ R →
    ∀ (r : ℕ) (y : Fin r → D.toPre.X), GenMod E r₁ y →
    ∀ (s : Fin r → Fam D.toPre F (R ^ 2)) (w : Fin r → F),
      (∀ b, NuGe D Q F v (R ^ 2) (s b) 0) →
      (∀ b, ∀ α : D.toPre.X, (∀ z : D.toPre.X, α ≠ y b + R • z) → ∀ j, ((s b).s α).f j = 0) →
      (∀ b, ValAt0 D F v (R ^ 2) (s b) (w b)) →
      phiC E (fun χ χ' : D.toPre.X => (QForm.bOf D.toPre Q χ χ' : ℝ)) / (((R : ℝ) ^ 2 : ℝ) : EReal) ≤
        valToEReal (∑ b, v (w b))

def HasHalf (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop := ∃ w : 𝓞 E, w + bar E w = 1

section Clauses

variable {S : FormSpaces} {φ : FormValues S}

theorem isBalancedSpace (hS : AreBalancedSpaces S) (E : Type) [Field E] [NumberField E] [IsCMField E]
    {cj : E → E} (hcj : ∀ c : 𝓞 E, (bar E c : E) = cj c) (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] :
    IsBalancedSpace E (S E cj Y) := by
  intro β
  rw [hS]
  refine and_congr Iff.rfl ⟨fun h c => h c _ (hcj c), fun h c c' hc => ?_⟩
  obtain rfl : c' = bar E c := RingOfIntegers.ext (hc.trans (hcj c).symm)
  exact h c

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  (D : DegData V (maximalIdeal V)) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q)

def intForm : D.toPre.X →ₗ[ℤ] D.toPre.X →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ (fun a b => QForm.bHom hϖ D hQ a b) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
    (fun _ _ _ => by simp) (fun _ _ _ => by simp)

def realForm : Bil D.toPre.X := (intForm hϖ D hQ).compr₂ (Int.castAddHom ℝ).toIntLinearMap

end Clauses

end GlobalTheory.PointStepCompare
