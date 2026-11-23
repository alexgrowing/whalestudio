import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStrictIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinRepsProjectiveFinrankLeNumberField

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.CompanionTheory.Ar.Fan

structure CMOrd (O : Type) [CommRing O] (bar : O → O) : Prop where

  conj : ∀ (σ : O →+* ℂ) (a : O), σ (bar a) = starRingEnd ℂ (σ a)

  emb : ∃ σ : O →+* ℂ, Function.Injective σ

  ded : IsDedekindDomain O

  fin : Module.Finite ℤ O

namespace CMOrd

variable {O : Type} [CommRing O] {bar : O → O}

theorem add (h : CMOrd O bar) : ∀ a b, bar (a + b) = bar a + bar b := fun a b => by
  obtain ⟨σ, hσ⟩ := h.emb
  exact hσ (by simp [h.conj])

theorem mul (h : CMOrd O bar) : ∀ a b, bar (a * b) = bar a * bar b := fun a b => by
  obtain ⟨σ, hσ⟩ := h.emb
  exact hσ (by simp [h.conj])

theorem one (h : CMOrd O bar) : bar 1 = 1 := by
  obtain ⟨σ, hσ⟩ := h.emb
  exact hσ (by simp [h.conj])

theorem comm (h : CMOrd O bar) : ∀ (τ : O ≃+* O) (a : O), τ (bar a) = bar (τ a) := fun τ a => by
  obtain ⟨σ, hσ⟩ := h.emb
  exact hσ (by rw [h.conj]; exact h.conj (σ.comp τ.toRingHom) a)

theorem bar_unique {bar' : O → O} (h : CMOrd O bar) (h' : CMOrd O bar') : bar = bar' := by
  obtain ⟨σ, hσ⟩ := h.emb
  exact funext fun a => hσ ((h.conj σ a).trans (h'.conj σ a).symm)

theorem charZero (h : CMOrd O bar) : CharZero O := by
  obtain ⟨σ, -⟩ := h.emb
  exact σ.charZero

theorem finite_classGroup (O : Type) [CommRing O] [IsDedekindDomain O] [Module.Finite ℤ O] [CharZero O] :
    Finite (ClassGroup O) := by
  classical
  have : Module.Free ℤ O := Module.free_of_finite_type_torsion_free'
  have := ClassGroup.fintypeOfAdmissibleOfAlgebraic (Module.finBasis ℤ O) AbsoluteValue.absIsAdmissible
  infer_instance

open GlobalTheory.ProjModClasses in

theorem classes (h : CMOrd O bar) : ∀ q : ℕ, ∃ (n : ℕ) (R : Fin n → ModuleCat.{0} O),
    (∀ k, Module.Finite O (R k) ∧ Module.Projective O (R k) ∧ Module.finrank O (R k) ≤ q) ∧
    ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
      ∃ k, Nonempty (X ≃ₗ[O] R k) := by
  intro q
  have := h.ded
  have := h.fin
  have := h.charZero
  have := finite_classGroup O
  let T := Σ r : Fin (q + 1), (Fin r → ClassGroup O)
  let g : T → ModuleCat.{0} O := fun t => ModuleCat.of O (Model t.2)
  let P : T → Prop := fun t => Module.Finite O (g t) ∧ Module.Projective O (g t) ∧ Module.finrank O (g t) ≤ q
  let S := {t : T // P t}
  have : Finite S := inferInstance
  let eS := Finite.equivFin S
  refine ⟨Nat.card S, fun k => g (eS.symm k).1, fun k => (eS.symm k).2, ?_⟩
  intro X _ _ _ _ hq
  obtain ⟨c, ⟨eX⟩⟩ := exists_equiv_model (R := O) (Module.finrank O X) X rfl
  let t : T := ⟨⟨Module.finrank O X, Nat.lt_succ_of_le hq⟩, c⟩
  have ht : P t := by
    refine ⟨Module.Finite.equiv eX, Module.Projective.of_equiv eX, ?_⟩
    change Module.finrank O (Model c) ≤ q
    rw [← eX.finrank_eq]
    exact hq
  refine ⟨eS ⟨t, ht⟩, ?_⟩
  show Nonempty (X ≃ₗ[O] (g (eS.symm (eS ⟨t, ht⟩)).1))
  rw [Equiv.symm_apply_apply]
  exact ⟨eX⟩

theorem int : CMOrd ℤ id :=
  ⟨fun σ a => by simp, ⟨Int.castRingHom ℂ, Int.cast_injective⟩, inferInstance, inferInstance⟩

theorem exists_extend {E : Type} [Field E] [NumberField E] (σ : 𝓞 E →+* ℂ) :
    ∃ φ : E →+* ℂ, ∀ x : 𝓞 E, φ (x : E) = σ x := by
  have hσ : Function.Injective σ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    have hk : RingHom.ker σ ≠ ⊥ := fun h => h0 (by simpa [h] using (RingHom.mem_ker.2 hx : x ∈ RingHom.ker σ))
    obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (Ideal.IsIntegral.comap_ne_bot ℤ hk)
    exact hn0 (by simpa [Ideal.mem_comap, RingHom.mem_ker] using hn)
  exact ⟨IsFractionRing.lift hσ, fun x => IsFractionRing.lift_algebraMap hσ x⟩

theorem of_field {E : Type} [Field E] [NumberField E] {b : 𝓞 E → 𝓞 E}
    (hb : ∀ (φ : E →+* ℂ) (a : 𝓞 E), φ (b a : E) = starRingEnd ℂ (φ (a : E))) : CMOrd (𝓞 E) b := by
  refine ⟨fun σ a => ?_, ?_, inferInstance, inferInstance⟩
  · obtain ⟨φ, h⟩ := exists_extend σ
    rw [← h, ← h, hb]
  · obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact ⟨φ.comp (algebraMap _ E), φ.injective.comp RingOfIntegers.coe_injective⟩

theorem gauss : CMOrd GaussianInt star := by
  have d : ∀ a : GaussianInt, a = (a.re : GaussianInt) + (a.im : GaussianInt) * Zsqrtd.sqrtd := fun a => by
    ext <;> simp
  refine ⟨fun σ a => ?_, ⟨GaussianInt.toComplex, fun _ _ h => GaussianInt.toComplex_inj.1 h⟩, inferInstance, ?_⟩
  · have d' : star a = (a.re : GaussianInt) - (a.im : GaussianInt) * Zsqrtd.sqrtd := by ext <;> simp
    have s : (Zsqrtd.sqrtd : GaussianInt) * Zsqrtd.sqrtd = -1 := by ext <;> simp
    have h : σ Zsqrtd.sqrtd ^ 2 = Complex.I ^ 2 := by
      rw [sq, ← map_mul, s]; simp
    have h2 : starRingEnd ℂ (σ Zsqrtd.sqrtd) = - σ Zsqrtd.sqrtd := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with e | e <;> simp [e]
    rw [d']
    conv_rhs => rw [d a]
    simp only [map_add, map_sub, map_mul, map_intCast, h2]
    ring
  · refine ⟨⟨{1, Zsqrtd.sqrtd}, ?_⟩⟩
    rw [eq_top_iff]
    intro a _
    rw [Finset.coe_pair, Submodule.mem_span_pair]
    exact ⟨a.re, a.im, by ext <;> simp⟩

theorem of_equiv {O' : Type} [CommRing O'] (h : CMOrd O bar) (e : O ≃+* O') : CMOrd O' fun a => e (bar (e.symm a)) := by
  have := h.ded
  have := h.fin
  refine ⟨fun σ a => ?_, ?_, ?_, Module.Finite.equiv e.toAddEquiv.toIntLinearEquiv⟩
  · simpa using h.conj (σ.comp e.toRingHom) (e.symm a)
  · obtain ⟨σ, hσ⟩ := h.emb
    exact ⟨σ.comp e.symm.toRingHom, hσ.comp e.symm.injective⟩
  · have : IsDomain O' := MulEquiv.isDomain O e.symm.toMulEquiv
    have : IsNoetherianRing O' := isNoetherianRing_of_ringEquiv O e
    have : IsIntegrallyClosed O' := IsIntegrallyClosed.of_equiv e
    have : Ring.DimensionLEOne O' := ⟨fun {p} hp hp' => by
      have hm : (p.comap e).IsMaximal := Ring.DimensionLEOne.maximalOfPrime
        (fun h0 => hp (by rw [← Ideal.map_comap_of_surjective e e.surjective p, h0, Ideal.map_bot])) (Ideal.comap_isPrime e p)
      rw [← Ideal.map_comap_of_surjective e e.surjective p]
      exact hm.map_bijective e e.bijective⟩
    exact {}

end CMOrd

example : ¬ CMOrd ℚ id := fun h => by
  have := h.fin
  have : Algebra.IsIntegral ℤ ℚ := inferInstance
  exact Int.not_isField (isField_of_isIntegral_of_isField (R := ℤ) (S := ℚ) Int.cast_injective (Field.toIsField ℚ))

example : ¬ CMOrd GaussianInt id := fun h => by
  have := congrFun (h.bar_unique CMOrd.gauss) Zsqrtd.sqrtd
  simpa using congrArg Zsqrtd.im this

def IsTwG {O : Type} [CommRing O] (w : O) (φ : InvFun O) : Prop :=
  ∀ σ : O ≃+* O, σ w = w → ∀ (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ),
    φ.toFun n (fun a b => B (fun i => σ (a i)) (fun i => σ (b i))) = φ.toFun n B

def zeroFun : InvFun ℤ where
  toFun _ _ := 0
  inv _ _ _ _ _ := rfl
  zero _ := rfl

def vorFun (O : Type) [CommRing O] [Module.Finite ℤ O] (g : ℕ) : InvFun O := baseFun O (fineDen g {1}) zeroFun {1}

variable {X : Type} [AddCommGroup X]

def IsMin2 (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (y : X) : Prop := ∀ x : X, B y y ≤ B (y + (x + x)) (y + (x + x))

def Covers2 {ι : Type} (a : ι → X) : Prop := ∀ y : X, ∃ (i : ι) (x : X), y = a i + (x + x)

def contact {O : Type} [CommRing O] (bar : O → O) [Module O X] {ι : Type} (a : ι → X) : Set (X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :=
  {B | B ∈ psdCone bar X ∧ ∀ i, IsMin2 B (a i)}

def IsSpanned {O : Type} [CommRing O] (bar : O → O) [Module O X] (K : Set (X →ₗ[ℤ] X →ₗ[ℤ] ℝ)) : Prop :=
  ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), (∀ i, γ i ∈ balForms bar X) ∧ (∀ i y, 0 ≤ γ i y y) ∧
    (∀ i, toReal (γ i) ∈ K) ∧ K ⊆ rcone γ

theorem zero_mem_contact {O : Type} [CommRing O] (bar : O → O) [Module O X] {ι : Type} (a : ι → X) :
    (0 : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) ∈ contact bar a := ⟨zero_mem_psdCone, fun _ _ => le_rfl⟩

example : Covers2 (![0, 1] : Fin 2 → ℤ) := fun y => by
  rcases Int.even_or_odd' y with ⟨k, h | h⟩
  · exact ⟨0, k, by simp; omega⟩
  · exact ⟨1, k, by simp; omega⟩

theorem vorFun_eval_eq_fineMean {O : Type} [CommRing O] [Module.Finite ℤ O] (g : ℕ) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] [Module.Finite ℤ X] (B : X → X → ℝ) :
    (vorFun O g).eval X B = 2 ^ g * (fineMean 1).eval X B := by
  rw [vorFun, eval_baseFun]
  have : zeroFun.eval X B = 0 := rfl
  simp [this, fineDen]

example (g : ℕ) : (vorFun ℤ g).eval ℤ (fun a b => ((a * b : ℤ) : ℝ)) = 2 ^ g / 2 := by
  rw [vorFun_eval_eq_fineMean, (fineMean 1).eval_eq (n := 1) (r := LinearMap.proj 0) fun x => ⟨fun _ => x, rfl⟩]
  have h0 : classMin 1 (fun a b : Fin 1 → ℤ => ((a 0 * b 0 : ℤ) : ℝ)) (fun _ => 0) = 0 := by
    refine IsLeast.csInf_eq ⟨⟨0, funext fun i => by simp [redV], by simp⟩, ?_⟩
    rintro x ⟨a, -, rfl⟩
    show (0 : ℝ) ≤ ((a 0 * a 0 : ℤ) : ℝ)
    exact_mod_cast mul_self_nonneg (a 0)
  have h1 : classMin 1 (fun a b : Fin 1 → ℤ => ((a 0 * b 0 : ℤ) : ℝ)) (fun _ => 1) = 1 := by
    refine IsLeast.csInf_eq ⟨⟨1, funext fun i => by simp [redV], by simp⟩, ?_⟩
    rintro x ⟨a, ha, rfl⟩
    have h2 : a 0 ≠ 0 := fun h => by
      have := congrFun ha 0
      simp [redV, h] at this
    have : (1 : ℤ) ≤ a 0 * a 0 := mul_self_pos.2 h2
    show (1 : ℝ) ≤ ((a 0 * a 0 : ℤ) : ℝ)
    exact_mod_cast this
  have hs : ∀ f : (Fin 1 → ZMod (1 + 1)) → ℝ, ∑ y, f y = f (fun _ => 0) + f (fun _ => 1) := fun f => by
    rw [← (Equiv.funUnique (Fin 1) (ZMod (1 + 1))).symm.sum_comp f]
    exact Fin.sum_univ_two _
  show 2 ^ g * (((((1 : ℕ) : ℝ) + 1) ^ 1)⁻¹ * ∑ y, classMin 1 (fun a b : Fin 1 → ℤ => ((a 0 * b 0 : ℤ) : ℝ)) y - ((0 * 0 : ℤ) : ℝ)) = _
  rw [hs, h0, h1]
  norm_num
  ring

end GlobalTheory.CompanionTheory.Ar.Fan
