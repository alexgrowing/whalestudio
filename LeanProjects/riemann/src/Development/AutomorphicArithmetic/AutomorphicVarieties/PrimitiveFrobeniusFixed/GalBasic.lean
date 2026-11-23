import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem lifts_cls {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (b : (ZMod N)ˣ)
    (g : G ℚ Ω) : Lifts N b g ↔ Chr.cls ℚ Ω N g = b := by
  constructor
  · intro h
    exact (Chr.clsFacts ℚ Ω N).2.2.1 g b h
  · rintro rfl x hx
    exact Chr.cls_spec N g x hx

private theorem fix_cls {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] :
    fixMu ℚ Ω N = (Chr.cls ℚ Ω N).ker := by
  have hmod : ∀ x : Ω, x ^ N = 1 → ∀ k : ℕ, x ^ (k % N) = x ^ k := by
    intro x hx k
    conv_rhs => rw [← Nat.mod_add_div k N]
    rw [pow_add, pow_mul, hx, one_pow, mul_one]
  ext g
  rw [MonoidHom.mem_ker, ← lifts_cls N 1 g]
  constructor
  · intro h
    have h' : ∀ x : Ω, x ^ N = 1 → g x = x := h
    show ∀ x : Ω, x ^ N = 1 → g x = x ^ ((1 : (ZMod N)ˣ) : ZMod N).val
    intro x hx
    rw [h' x hx, Units.val_one, ZMod.val_one_eq_one_mod, hmod x hx, pow_one]
  · intro h
    have h' : ∀ x : Ω, x ^ N = 1 → g x = x ^ ((1 : (ZMod N)ˣ) : ZMod N).val := h
    show ∀ x : Ω, x ^ N = 1 → g x = x
    intro x hx
    rw [h' x hx, Units.val_one, ZMod.val_one_eq_one_mod, hmod x hx, pow_one]

private theorem cls_onto {Ω : Type} [Field Ω] [inst : Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] :
    Function.Surjective (Chr.cls ℚ Ω N) := by
  haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap ℚ Ω).injective).mp inferInstance
  convert (Chr.clsOnto Ω N).1
  all_goals first
    | exact Subsingleton.elim (α := Algebra ℚ Ω) _ _
    | (convert ‹IsAlgClosure ℚ Ω›; exact Subsingleton.elim (α := Algebra ℚ Ω) _ _)

private theorem act_eq {Ω : Type} [Field Ω] [Algebra ℚ Ω] {N : ℕ} {x : Ω} (hx : ∀ g ∈ fixMu ℚ Ω N, g x = x)
    {g h : G ℚ Ω} (e : g⁻¹ * h ∈ fixMu ℚ Ω N) : g x = h x := by
  calc g x = g ((g⁻¹ * h) x) := by rw [hx _ e]
    _ = h x := by simp [AlgEquiv.mul_apply]

theorem UpperTheory.V.ML.galBasic :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N : ℕ), N ≠ 0 →
    (fixMu ℚ Ω N).Normal ∧ IsOpen (fixMu ℚ Ω N : Set (G ℚ Ω)) ∧ (∀ g h : G ℚ Ω, g * h * g⁻¹ * h⁻¹ ∈ fixMu ℚ Ω N) ∧
    (∀ b : (ZMod N)ˣ, ∃ g : G ℚ Ω, Lifts N b g) ∧ (∀ g : G ℚ Ω, ∃ b : (ZMod N)ˣ, Lifts N b g) ∧
    (∀ (x : Ω), (∀ g ∈ fixMu ℚ Ω N, g x = x) → ∀ g h : G ℚ Ω, g (h x) = h (g x)) ∧
    (∀ (x : Ω), (∀ g ∈ fixMu ℚ Ω N, g x = x) → ∀ h : G ℚ Ω, ∀ g ∈ fixMu ℚ Ω N, g (h x) = h x) ∧
    (∀ (x : Ω), (∀ g ∈ fixMu ℚ Ω N, g x = x) → ∀ (k : ℕ) (g h : G ℚ Ω), Pows N k g → Pows N k h → g x = h x) ∧
    (∀ (M : ℕ), M ∣ N → fixMu ℚ Ω N ≤ fixMu ℚ Ω M) ∧
    ∀ (b c : (ZMod N)ˣ) (g h : G ℚ Ω), Lifts N b g → Lifts N c h → Lifts N (b * c) (g * h) ∧ Lifts N b⁻¹ g⁻¹ ∧ (b = c ↔ g⁻¹ * h ∈ fixMu ℚ Ω N) := by
  intro Ω _ _ _ N hN
  haveI : NeZero N := ⟨hN⟩
  have hnorm : (fixMu ℚ Ω N).Normal := by
    rw [fix_cls]
    infer_instance
  have hopen : IsOpen (fixMu ℚ Ω N : Set (G ℚ Ω)) := by
    rw [fix_cls]
    exact (Chr.clsFacts ℚ Ω N).1
  have hcomm : ∀ g h : G ℚ Ω, g * h * g⁻¹ * h⁻¹ ∈ fixMu ℚ Ω N := by
    intro g h
    rw [fix_cls, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
      mul_comm (Chr.cls ℚ Ω N g) (Chr.cls ℚ Ω N h), mul_inv_cancel_right, mul_inv_cancel]
  have h4 : ∀ b : (ZMod N)ˣ, ∃ g : G ℚ Ω, Lifts N b g := by
    intro b
    obtain ⟨g, hg⟩ := cls_onto (Ω := Ω) N b
    exact ⟨g, (lifts_cls N b g).2 hg⟩
  have h5 : ∀ g : G ℚ Ω, ∃ b : (ZMod N)ˣ, Lifts N b g := fun g => ⟨_, (lifts_cls N _ g).2 rfl⟩
  have h6 : ∀ x : Ω, (∀ g ∈ fixMu ℚ Ω N, g x = x) → ∀ g h : G ℚ Ω, g (h x) = h (g x) := by
    intro x hx g h
    have e : (h * g)⁻¹ * (g * h) ∈ fixMu ℚ Ω N := by
      have := hcomm g⁻¹ h⁻¹
      rwa [inv_inv, inv_inv, mul_assoc (g⁻¹ * h⁻¹), ← mul_inv_rev] at this
    have := act_eq hx e
    simpa [AlgEquiv.mul_apply] using this.symm
  have h7 : ∀ x : Ω, (∀ g ∈ fixMu ℚ Ω N, g x = x) → ∀ h : G ℚ Ω, ∀ g ∈ fixMu ℚ Ω N, g (h x) = h x := by
    intro x hx h g hg
    have e : (g * h)⁻¹ * h ∈ fixMu ℚ Ω N := by
      have := hnorm.conj_mem g⁻¹ (inv_mem hg) h⁻¹
      rwa [inv_inv, ← mul_inv_rev] at this
    simpa [AlgEquiv.mul_apply] using act_eq hx e
  have h8 : ∀ x : Ω, (∀ g ∈ fixMu ℚ Ω N, g x = x) →
      ∀ (k : ℕ) (g h : G ℚ Ω), Pows N k g → Pows N k h → g x = h x := by
    intro x hx k g h hg hh
    apply act_eq hx
    show ∀ ζ : Ω, ζ ^ N = 1 → (g⁻¹ * h) ζ = ζ
    intro ζ hζ
    rw [AlgEquiv.mul_apply, hh ζ hζ, ← hg ζ hζ]
    simp
  have h9 : ∀ M : ℕ, M ∣ N → fixMu ℚ Ω N ≤ fixMu ℚ Ω M := by
    intro M hM g hg
    have hg' : ∀ ζ : Ω, ζ ^ N = 1 → g ζ = ζ := hg
    show ∀ ζ : Ω, ζ ^ M = 1 → g ζ = ζ
    intro ζ hζ
    obtain ⟨j, hj⟩ := hM
    exact hg' ζ (by rw [hj, pow_mul, hζ, one_pow])
  have h10 : ∀ (b c : (ZMod N)ˣ) (g h : G ℚ Ω), Lifts N b g → Lifts N c h →
      Lifts N (b * c) (g * h) ∧ Lifts N b⁻¹ g⁻¹ ∧ (b = c ↔ g⁻¹ * h ∈ fixMu ℚ Ω N) := by
    intro b c g h hb hc
    rw [lifts_cls] at hb hc
    refine ⟨?_, ?_, ?_⟩
    · rw [lifts_cls, map_mul, hb, hc]
    · rw [lifts_cls, map_inv, hb]
    · rw [fix_cls, MonoidHom.mem_ker, map_mul, map_inv, hb, hc, inv_mul_eq_one]
  exact ⟨hnorm, hopen, hcomm, h4, h5, h6, h7, h8, h9, h10⟩
