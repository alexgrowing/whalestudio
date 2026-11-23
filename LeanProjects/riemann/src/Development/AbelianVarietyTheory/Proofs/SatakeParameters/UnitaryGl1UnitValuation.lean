import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam

noncomputable section
namespace GlobalTheory.Hk3.LatModel
open Classical

section Abstract
variable {W G : Type} [AddCommGroup W] [Group G]

def rho0 (c : W → W → ℂ) (x : W) : Module.End ℂ (W → ℂ) where
  toFun f z := c z x * f (z + x)
  map_add' f g := by funext z; simp [mul_add]
  map_smul' r f := by funext z; simp; ring

def om0 (a : G → W → W) (a1 : ∀ x, a 1 x = x) (am : ∀ g h x, a (g * h) x = a g (a h x)) : G →* Module.End ℂ (W → ℂ) where
  toFun g := { toFun := fun f z => f (a g⁻¹ z), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  map_one' := by ext f z; simp [a1]
  map_mul' g h := by ext f z; simp [am]

def s0 (A : AddSubgroup W) : W → ℂ := fun z => if z ∈ A then 1 else 0

theorem exists_model (A : AddSubgroup W) (c : W → W → ℂ)
    (hl : ∀ x y z, c (x + y) z = c x z * c y z) (hr : ∀ x y z, c x (y + z) = c x y * c x z)
    (hs : ∀ x, c x x = 1) (h0 : ∀ x, c x 0 = 1) (hA : ∀ u ∈ A, ∀ v ∈ A, c u v = 1)
    (hnd : ∀ z, z ∉ A → ∃ u ∈ A, c z u * c z u ≠ 1)
    (a : G → W → W) (a1 : ∀ x, a 1 x = x) (am : ∀ g h x, a (g * h) x = a g (a h x))
    (aa : ∀ g x y, a g (x + y) = a g x + a g y) (ha : ∀ g x y, c (a g x) (a g y) = c x y) (haA : ∀ g x, a g x ∈ A ↔ x ∈ A) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module ℂ M) (ρ : W → Module.End ℂ M) (ω : G →* Module.End ℂ M) (s : M),
      s ≠ 0 ∧ ρ 0 = 1 ∧ (∀ x y, ρ x * ρ y = c x y • ρ (x + y)) ∧ (∀ u ∈ A, ρ u s = s) ∧
      Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ ∧ (∀ g x, ω g * ρ x = ρ (a g x) * ω g) ∧
      (∀ g t, (∀ u ∈ A, ρ u t = t) → ω g t = t) ∧ ∀ x, x ∉ A → ρ x s ∉ Submodule.span ℂ {s} := by
  have mul0 : ∀ x y, rho0 c x * rho0 c y = c x y • rho0 c (x + y) := by
    intro x y; ext f z
    simp [rho0, hl, hr, add_assoc]; ring
  have nrm : ∀ g x, om0 a a1 am g * rho0 c x = rho0 c (a g x) * om0 a a1 am g := by
    intro g x; ext f z
    have h1 : c (a g⁻¹ z) x = c z (a g x) := by
      rw [← ha g, ← am]; simp [a1]
    have h2 : a g⁻¹ (a g x) = x := by rw [← am]; simp [a1]
    simp [rho0, om0, h1, aa, h2]
  have oms : ∀ g, om0 a a1 am g (s0 A) = s0 A := by
    intro g; funext z
    show s0 A (a g⁻¹ z) = s0 A z
    simp only [s0, haA]
  have vac : ∀ u ∈ A, rho0 c u (s0 A) = s0 A := by
    intro u hu; funext z
    show c z u * s0 A (z + u) = s0 A z
    by_cases hz : z ∈ A
    · simp [s0, hz, A.add_mem hz hu, hA z hz u hu]
    · have : z + u ∉ A := fun h => hz (by simpa using A.sub_mem h hu)
      simp [s0, hz, this]
  let N : Submodule ℂ (W → ℂ) := Submodule.span ℂ (Set.range fun x => rho0 c x (s0 A))
  have hρ : ∀ x, ∀ f ∈ N, rho0 c x f ∈ N := by
    intro x f hf
    have : N.map (rho0 c x) ≤ N := by
      rw [Submodule.map_span_le]
      rintro _ ⟨y, rfl⟩
      have := congrArg (fun T => T (s0 A)) (mul0 x y)
      simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
      rw [this]
      exact N.smul_mem _ (Submodule.subset_span ⟨_, rfl⟩)
    exact this ⟨f, hf, rfl⟩
  have hω : ∀ g, ∀ f ∈ N, om0 a a1 am g f ∈ N := by
    intro g f hf
    have : N.map (om0 a a1 am g) ≤ N := by
      rw [Submodule.map_span_le]
      rintro _ ⟨y, rfl⟩
      have := congrArg (fun T => T (s0 A)) (nrm g y)
      simp only [Module.End.mul_apply, oms] at this
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩
    exact this ⟨f, hf, rfl⟩
  have r0 : rho0 c 0 = 1 := by ext f z; simp [rho0, h0]
  have hs0 : s0 A ∈ N := Submodule.subset_span ⟨0, by simp [r0]⟩
  have anti : ∀ x y, c x y * c y x = 1 := by
    intro x y
    have := hs (x + y)
    rw [hl, hr, hr, hs, hs] at this
    simpa using this
  have eqv : ∀ f ∈ N, ∀ u ∈ A, ∀ z, f (z + u) = c z u * f z := by
    intro f hf u hu
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨x, rfl⟩ := hf
      intro z
      show c (z + u) x * s0 A (z + u + x) = c z u * (c z x * s0 A (z + x))
      by_cases hz : z + x ∈ A
      · have h2 : z + u + x ∈ A := by have := A.add_mem hz hu; rwa [add_right_comm] at this
        have h3 := hA u hu _ hz
        rw [hr] at h3
        have h4 := anti z u
        have h5 : c u x = c z u := by
          calc c u x = (c z u * c u z) * c u x := by rw [h4, one_mul]
            _ = c z u := by rw [mul_assoc, h3, mul_one]
        simp [s0, hz, h2, hl, h5]; ring
      · have h2 : z + u + x ∉ A := fun h => hz (by have := A.sub_mem h hu; rwa [show z + u + x - u = z + x by abel] at this)
        simp [s0, hz, h2]
    | zero => intro z; simp
    | add f g _ _ h1 h2 => intro z; simp [h1 z, h2 z, mul_add]
    | smul r f _ h1 => intro z; simp [h1 z]; ring
  refine ⟨N, inferInstance, inferInstance, fun x => (rho0 c x).restrict (hρ x),
    { toFun := fun g => (om0 a a1 am g).restrict (hω g), map_one' := ?_, map_mul' := ?_ }, ⟨s0 A, hs0⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext f z; simp
  · intro g h; ext f z; simp
  · intro h
    have := congrFun (congrArg Subtype.val h) 0
    simp [s0] at this
  · ext f z; simp [r0]
  · intro x y; refine LinearMap.ext fun f => Subtype.ext ?_
    exact congrArg (fun T => T f.1) (mul0 x y)
  · intro u hu; exact Subtype.ext (vac u hu)
  · apply Submodule.map_injective_of_injective N.injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
    rfl
  · intro g x; refine LinearMap.ext fun f => Subtype.ext ?_
    exact congrArg (fun T => T f.1) (nrm g x)
  · rintro g ⟨t, ht⟩ hv
    have hv' : ∀ u ∈ A, ∀ z, c z u * t (z + u) = t z := fun u hu z => congrFun (congrArg Subtype.val (hv u hu)) z
    have ht0 : t = t 0 • s0 A := by
      funext z
      by_cases hz : z ∈ A
      · have := eqv t ht z hz 0
        rw [hA 0 A.zero_mem z hz] at this
        simpa [s0, hz] using this
      · obtain ⟨u, hu, hne⟩ := hnd z hz
        have h1 := hv' u hu z
        rw [eqv t ht u hu, ← mul_assoc] at h1
        have : t z = 0 := by
          by_contra h
          exact hne (mul_right_cancel₀ h (by rw [h1, one_mul]))
        simp [s0, hz, this]
    apply Subtype.ext
    show om0 a a1 am g t = t
    rw [ht0, map_smul, oms]
  · intro x hx h
    obtain ⟨r, hr'⟩ := Submodule.mem_span_singleton.1 h
    have h1 := congrFun (congrArg Subtype.val hr') (-x)
    have hx' : -x ∉ A := fun h => hx (by simpa using A.neg_mem h)
    have h2 : c (-x) x ≠ 0 := left_ne_zero_of_mul_eq_one (anti _ _)
    change r * s0 A (-x) = c (-x) x * s0 A (-x + x) at h1
    simp [s0, hx'] at h1
    exact h2 h1.symm
end Abstract

section Concrete
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def ratCirc : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
  QuotientAddGroup.map _ _ (Rat.castHom ℝ).toAddMonoidHom (by
    rintro _ ⟨k, rfl⟩
    exact ⟨k, by simp⟩)

theorem ratCirc_ne (x : AddCircle (1 : ℚ)) (hx : x ≠ 0) : ratCirc x ≠ 0 := by
  induction x using QuotientAddGroup.induction_on with
  | H r =>
    intro h
    apply hx
    have h' : ((r : ℝ) : AddCircle (1 : ℝ)) = 0 := h
    obtain ⟨k, hk⟩ := (QuotientAddGroup.eq_zero_iff _).1 h'
    refine (QuotientAddGroup.eq_zero_iff _).2 ⟨k, ?_⟩
    have : ((k : ℚ) : ℝ) = r := by simpa using hk
    simpa using (by exact_mod_cast this : (k : ℚ) = r)

theorem exists_psi (ϖ : L) (hϖ : ϖ⁻¹ ∉ Formalism.UG.intL L) :
    ∃ ψ : AddChar L ℂ, (∀ a ∈ Formalism.UG.intL L, ψ a = 1) ∧ ψ ϖ⁻¹ ≠ 1 := by
  let O : AddSubgroup L := (Formalism.UG.intL L).toAddSubgroup
  have hne : (QuotientAddGroup.mk ϖ⁻¹ : L ⧸ O) ≠ 0 := by
    rw [Ne, QuotientAddGroup.eq_zero_iff]; exact hϖ
  obtain ⟨χ, hχ⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hne
  let φ : L →+ AddCircle (1 : ℝ) := ratCirc.comp ((χ : (L ⧸ O) →+ AddCircle (1 : ℚ)).comp (QuotientAddGroup.mk' O))
  refine ⟨{ toFun := fun a => (AddCircle.toCircle (φ a) : ℂ), map_zero_eq_one' := by simp, map_add_eq_mul' := by intro a b; simp [AddCircle.toCircle_add] }, ?_, ?_⟩
  · intro a ha
    have h1 : (QuotientAddGroup.mk' O) a = 0 := (QuotientAddGroup.eq_zero_iff _).2 ha
    have : φ a = 0 := by
      show ratCirc ((χ : (L ⧸ O) →+ AddCircle (1 : ℚ)) ((QuotientAddGroup.mk' O) a)) = 0
      rw [h1, map_zero, map_zero]
    show (AddCircle.toCircle (φ a) : ℂ) = 1
    simp [this]
  · intro h
    have h1 : AddCircle.toCircle (φ ϖ⁻¹) = AddCircle.toCircle (0 : AddCircle (1 : ℝ)) := by
      apply Subtype.ext; rw [AddCircle.toCircle_zero]; exact h
    exact ratCirc_ne _ hχ (AddCircle.injective_toCircle one_ne_zero h1)

theorem v_two {ϖ : L} {σ : L →+* L} {q : ℕ} (h : Formalism.UG.IsUnramInv ϖ σ q) (hq : Odd q) : Valued.v (2 : L) = 1 := by
  obtain ⟨-, -, -, -, -, h2, hc⟩ := h
  by_contra hne
  have hle : Valued.v (2 : L) ≤ 1 := by
    have := (Valued.v (R := L)).integer.add_mem (one_mem _) (one_mem _)
    rw [one_add_one_eq_two] at this; exact this
  have hlt := lt_of_le_of_ne hle hne
  set R := (Valued.v (R := L)).valuationSubring
  change Nat.card (R ⧸ IsLocalRing.maximalIdeal R) = q ^ 2 at hc
  have hm : (2 : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [Valuation.mem_maximalIdeal_iff]; exact hlt
  have h20 : (2 : R ⧸ IsLocalRing.maximalIdeal R) = 0 := by
    have := Ideal.Quotient.eq_zero_iff_mem.2 hm
    rwa [map_ofNat] at this
  have hodd : Odd (Nat.card (R ⧸ IsLocalRing.maximalIdeal R)) := by rw [hc]; exact hq.pow
  obtain ⟨k, hk⟩ := hodd
  have h3 : ((Nat.card (R ⧸ IsLocalRing.maximalIdeal R) : ℕ) : R ⧸ IsLocalRing.maximalIdeal R) = 0 := by
    rw [← nsmul_one]; exact card_nsmul_eq_zero'
  rw [hk] at h3
  push_cast at h3
  rw [h20] at h3
  simp at h3

theorem unitary_gl1_unit_valuation {σ : L →+* L} (hv : ∀ x, Valued.v (σ x) = Valued.v x)
    (g : Formalism.UG.UJ σ ((1 : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L)) :
    σ ((g : GL (Fin 1) L) 0 0) * (g : GL (Fin 1) L) 0 0 = 1 ∧ Valued.v ((g : GL (Fin 1) L) 0 0) = 1 := by
  have h : Formalism.UG.cT σ ((g : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) * _ * _ = _ := g.2
  have h1 := congrFun (congrFun h 0) 0
  simp [Matrix.mul_apply, Formalism.UG.cT] at h1
  refine ⟨h1, ?_⟩
  have h2 := congrArg Valued.v h1
  rw [map_mul, hv, map_one, ← sq] at h2
  rcases lt_trichotomy (Valued.v ((g : GL (Fin 1) L) 0 0)) 1 with h | h | h
  · exact absurd h2 (pow_lt_one₀ zero_le h two_ne_zero).ne
  · exact h
  · exact absurd h2 (one_lt_pow₀ h two_ne_zero).ne'

theorem local_hermitian_form_gl1 (σ : L →+* L) (δ : L) (x y : Matrix (Fin 1) (Fin 1) L) :
    locH σ δ (1 : GL (Fin 1) L) (1 : GL (Fin 1) L) x y = δ * (σ (y 0 0) * x 0 0) := by
  simp [locH, Matrix.trace, Matrix.mul_apply]

theorem exists_locPair [CharZero L] {ϖ : L} {σ : L →+* L} {q : ℕ} (h : Formalism.UG.IsUnramInv ϖ σ q) (hq : Odd q) :
    ∃ (δ : L) (ψ : AddChar L ℂ) (M : Type) (_ : AddCommGroup M) (_ : Module ℂ M)
      (ρ : Matrix (Fin 1) (Fin 1) L → Module.End ℂ M)
      (ω : Formalism.UG.UJ σ ((1 : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) × Formalism.UG.UJ σ ((1 : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) →* Module.End ℂ M) (s : M),
      LocPair ϖ σ q δ 1 1 ψ ρ ω ∧ s ≠ 0 ∧ LocVac ρ s ∧ Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ ∧
        ∃ x, ρ x s ∉ Submodule.span ℂ {s} := by
  have h2 := v_two h hq
  obtain ⟨hσ, hv, hϖσ, hϖ, ⟨x0, -, hx0⟩, -, -⟩ := id h
  have hmem : ∀ a : L, a ∈ Formalism.UG.intL L ↔ Valued.v a ≤ 1 := fun a => Iff.rfl
  have hϖi : Valued.v ϖ⁻¹ = WithZero.exp 1 := by
    rw [map_inv₀, hϖ]; rfl
  have hϖn : ϖ⁻¹ ∉ Formalism.UG.intL L := by
    rw [hmem, hϖi, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  obtain ⟨ψ, hψ1, hψ2⟩ := exists_psi ϖ hϖn
  set δ := σ x0 - x0 with hδ
  have hσδ : σ δ = -δ := by rw [hδ, map_sub, hσ]; ring
  have hδ0 : δ ≠ 0 := by intro h0; rw [h0] at hx0; simp at hx0
  let A : AddSubgroup (Matrix (Fin 1) (Fin 1) L) := (Formalism.UG.intL L).toAddSubgroup.comap (Matrix.entryAddMonoidHom L 0 0)
  have hAm : ∀ u, u ∈ A ↔ Valued.v (u 0 0) ≤ 1 := fun u => Iff.rfl
  have hAm' : ∀ u : Matrix (Fin 1) (Fin 1) L, (∀ i j, u i j ∈ Formalism.UG.intL L) ↔ u ∈ A := fun u =>
    ⟨fun hu => hu 0 0, fun hu i j => by rw [Subsingleton.elim i 0, Subsingleton.elim j 0]; exact hu⟩
  let c : Matrix (Fin 1) (Fin 1) L → Matrix (Fin 1) (Fin 1) L → ℂ := fun x y =>
    ψ ((locH σ δ (1 : GL (Fin 1) L) (1 : GL (Fin 1) L) x y + σ (locH σ δ (1 : GL (Fin 1) L) (1 : GL (Fin 1) L) x y)) / 2)
  have hc : ∀ x y, c x y = ψ (δ * (σ (y 0 0) * x 0 0 - y 0 0 * σ (x 0 0)) / 2) := by
    intro x y
    simp only [c, local_hermitian_form_gl1, map_mul, hσ, hσδ]
    congr 1; ring
  let U := Formalism.UG.UJ σ ((1 : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L)
  let a : U × U → Matrix (Fin 1) (Fin 1) L → Matrix (Fin 1) (Fin 1) L := fun p x =>
    ((p.2 : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) * x * (((p.1 : GL (Fin 1) L)⁻¹ : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L)
  have ha0 : ∀ p (_ : Matrix (Fin 1) (Fin 1) L), ∃ t : L, σ t * t = 1 ∧ Valued.v t = 1 ∧ ∀ x, a p x 0 0 = t * x 0 0 := by
    intro p
    obtain ⟨e1, e2⟩ := unitary_gl1_unit_valuation hv p.2
    obtain ⟨f1, f2⟩ := unitary_gl1_unit_valuation hv p.1⁻¹
    refine fun _ => ⟨(p.2 : GL (Fin 1) L) 0 0 * ((p.1⁻¹ : U) : GL (Fin 1) L) 0 0, ?_, by rw [map_mul, e2, f2, one_mul], fun x => ?_⟩
    · rw [map_mul]; linear_combination e1 * (σ (((p.1⁻¹ : U) : GL (Fin 1) L) 0 0) * ((p.1⁻¹ : U) : GL (Fin 1) L) 0 0) + f1
    · simp only [a, Matrix.mul_apply, Fin.sum_univ_one, Fin.default_eq_zero, Finset.univ_unique, Finset.sum_singleton, Subgroup.coe_inv]; ring
  obtain ⟨M, i1, i2, ρ, ω, s, s0', r0, rm, rv, rs, rn, rf, rx⟩ := exists_model (G := U × U) A c
    (by intro x y z; rw [hc, hc, hc, ← AddChar.map_add_eq_mul]; congr 1; simp only [Matrix.add_apply, map_add]; ring)
    (by intro x y z; rw [hc, hc, hc, ← AddChar.map_add_eq_mul]; congr 1; simp only [Matrix.add_apply, map_add]; ring)
    (by intro x; rw [hc]; simp [mul_comm])
    (by intro x; rw [hc]; simp)
    (by
      intro u hu w hw
      rw [hc]; apply hψ1
      rw [hmem, map_div₀, h2, div_one, map_mul, hx0, one_mul]
      rw [hAm] at hu hw
      refine (Valuation.map_sub_le _ ?_ ?_)
      · rw [map_mul, hv]; exact mul_le_one' hw hu
      · rw [map_mul, hv]; exact mul_le_one' hw hu)
    (by
      intro z hz
      rw [hAm, not_le] at hz
      have hz0 : z 0 0 ≠ 0 := by intro h0; rw [h0] at hz; simp at hz
      have hϖ0 : ϖ ≠ 0 := by intro h0; rw [h0] at hϖ; simp at hϖ
      refine ⟨Matrix.of fun _ _ => σ (ϖ⁻¹ / (2 * δ * z 0 0)), ?_, ?_⟩
      · rw [hAm, Matrix.of_apply, hv, map_div₀, hϖi, map_mul, map_mul, h2, hx0, one_mul, one_mul]
        have hne : Valued.v (z 0 0) ≠ 0 := (zero_lt_one.trans hz).ne'
        rw [div_le_one₀ (zero_lt_one.trans hz)]
        rw [← WithZero.exp_log hne] at hz ⊢
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hz
        rw [WithZero.exp_le_exp]; omega
      · rw [hc, ← AddChar.map_add_eq_mul]
        have hσz : σ (z 0 0) ≠ 0 := (map_ne_zero σ).2 hz0
        convert hψ2 using 2
        have e : σ (ϖ⁻¹ / (2 * δ * z 0 0)) = ϖ⁻¹ / (2 * -δ * σ (z 0 0)) := by
          rw [map_div₀, map_inv₀, hϖσ, map_mul, map_mul, hσδ, map_ofNat]
        rw [Matrix.of_apply, hσ, e]
        field_simp
        ring)
    a (by intro x; simp [a]) (by
      intro g k x
      obtain ⟨t1, -, -, h1⟩ := ha0 g x
      ext i j
      rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
      simp only [a, Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, mul_inv_rev, Units.val_mul, Matrix.mul_assoc])
    (by intro g x y; simp only [a, Matrix.mul_add, Matrix.add_mul])
    (by
      intro g x y
      obtain ⟨t, t1, -, h1⟩ := ha0 g x
      rw [hc, hc, h1, h1]; congr 2
      simp only [map_mul]
      linear_combination δ * (σ (y 0 0) * x 0 0 - y 0 0 * σ (x 0 0)) * t1)
    (by
      intro g x
      obtain ⟨t, -, t2, h1⟩ := ha0 g x
      rw [hAm, hAm, h1, map_mul, t2, one_mul])
  have hs : LocVac ρ s := fun u hu => rv u ((hAm' u).1 hu)
  refine ⟨δ, ψ, M, i1, i2, ρ, ω, s, ⟨h, hq, one_mem _, one_mem _, ?_, ?_, ⟨hx0, hσδ⟩, fun a ha _ => hψ1 a ha,
    ⟨1, one_mem _, map_one σ, by simpa using hψ2⟩, r0, rm, ?_, fun g k x => rn (g, k) x, ?_⟩, s0', hs, rs, ⟨fun _ _ => ϖ⁻¹, rx _ hϖn⟩⟩
  · intro i j; rw [Subsingleton.elim i 0, Subsingleton.elim j 0]; simp
  · intro i j; rw [Subsingleton.elim i 0, Subsingleton.elim j 0]; simp
  · rw [eq_top_iff, ← rs]
    apply Submodule.span_mono
    rintro _ ⟨x, rfl⟩
    exact ⟨x, s, hs, rfl⟩
  · intro g k _ _ t ht
    exact rf (g, k) t fun u hu => ht u ((hAm' u).2 hu)

end Concrete

end GlobalTheory.Hk3.LatModel
end
