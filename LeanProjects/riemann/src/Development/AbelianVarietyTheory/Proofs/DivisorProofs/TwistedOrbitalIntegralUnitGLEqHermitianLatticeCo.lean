import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulHomInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLLatticeSpannedByGLColumnsEqFullLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSpannedByGLColumnsEqIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerEqMapNormOneTorusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactClosureZpowersLeftMulGLIffIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjIntegralIffLatticeUnimodularStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TwOrbLat

open GlobalTheory.UnitLemma

variable {K : UQ} {B : InvAlg K}

theorem mulLat_mem_iff (t : B.Aˣ) (L : Submodule K.O B.A) (y : B.A) :
    y ∈ mulLat K.O (t : B.A) L ↔ ((t⁻¹ : B.Aˣ) : B.A) * y ∈ L := by
  constructor
  · intro h
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 h
    simpa [← mul_assoc] using hx
  · intro h
    exact Submodule.mem_map.2 ⟨_, h, by simp [← mul_assoc]⟩

theorem mem_stabLat_iff (t : B.Aˣ) (L : Submodule K.O B.A) :
    t ∈ stabLat K.O L ↔ mulLat K.O (t : B.A) L = L := by
  constructor
  · intro h
    ext y
    rw [mulLat_mem_iff, h (((t⁻¹ : B.Aˣ) : B.A) * y), ← mul_assoc, Units.mul_inv, one_mul]
  · intro h y
    conv_rhs => rw [← h]
    rw [mulLat_mem_iff, ← mul_assoc, Units.inv_mul, one_mul]

theorem stabLat_mulLat (t : B.Aˣ) (L : Submodule K.O B.A) :
    stabLat K.O (mulLat K.O (t : B.A) L) = stabLat K.O L := by
  ext s
  change (∀ y, y ∈ mulLat K.O (t : B.A) L ↔ (s : B.A) * y ∈ mulLat K.O (t : B.A) L) ↔ ∀ y, y ∈ L ↔ (s : B.A) * y ∈ L
  simp only [mulLat_mem_iff]
  constructor
  · intro h y
    have := h ((t : B.A) * y)
    have e1 : ((t⁻¹ : B.Aˣ) : B.A) * ((t : B.A) * y) = y := by rw [← mul_assoc, Units.inv_mul, one_mul]
    have e2 : ((t⁻¹ : B.Aˣ) : B.A) * ((s : B.A) * ((t : B.A) * y)) = s * y := by rw [mul_left_comm, e1]
    rwa [e1, e2] at this
  · intro h y
    rw [h (((t⁻¹ : B.Aˣ) : B.A) * y), mul_left_comm]

theorem avg_const {H : Type} [Group H] (c : ℂ) : avg (fun _ : H => c) = c := by
  have hR : rStab (fun _ : H => c) = ⊤ := by
    ext k; simp [GlobalTheory.TwOrbConj.mem_rStab]
  unfold avg
  have h1 : ∀ x : H ⧸ (⊤ : Subgroup H), x = 1 := fun x =>
    QuotientGroup.induction_on x fun g => (QuotientGroup.eq_one_iff g).2 (Subgroup.mem_top g)
  rw [hR, Subgroup.index_top, finsum_eq_single _ (1 : H ⧸ (⊤ : Subgroup H)) (fun x hx => absurd (h1 x) hx)]
  simp

theorem cast_finsum {α : Type} (f : α → ℚ) : ((∑ᶠ i, f i : ℚ) : ℂ) = ∑ᶠ i, (f i : ℂ) := by
  by_cases h : (Function.support f).Finite
  · exact (Rat.castHom ℂ).toAddMonoidHom.map_finsum h
  · have h' : ¬ (Function.support fun i => (f i : ℂ)).Finite := by
      have : (Function.support fun i => (f i : ℂ)) = Function.support f := by ext i; simp
      rwa [this]
    rw [finsum_of_infinite_support h, finsum_of_infinite_support h', Rat.cast_zero]

end GlobalTheory.TwOrbLat

open GlobalTheory.UnitLemma GlobalTheory.TwOrbLat in
theorem GlobalTheory.TwOrbLat.twOrb_unit_eq_orbSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (a : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K), B.P.Separable → ∀ (β : B.Aˣ) (ε : B.A), (ε = 1 ∨ ε = -1) → B.σ (β : B.A) = β * (ε * B.g) → ∀ (b : Module.Basis (Fin a) K.E B.A) (δ : GLw a w), (∀ i j, ((δ.val * GlobalTheory.Tw.Phi a (w.adicCompletion E))⁻¹)ᵀ i j = e (B.herm β (b i) (b j))) → twOrb (thL a w) (GlobalTheory.LFun.KGL w a) δ ((GlobalTheory.LFun.KGL w a : Set (GLw a w)).indicator 1) = ((GlobalTheory.UnitLemma.orbSum K.O B.T {L : Submodule K.O B.A | GlobalTheory.UnitLemma.IsLat K.O K.E L ∧ ∀ z, z ∈ L ↔ ∀ y ∈ L, B.herm β y z ∈ (algebraMap K.O K.E).range} (fun _ => 1) : ℚ) : ℂ) := by
  intro E _ _ _ hU w hw K e he hO a B hP β ε hε hβ b δ hδ
  set θ := thL a w with hθ
  set Kg := GlobalTheory.LFun.KGL w a with hKg
  set ι := mulGL e b with hι
  set T' := twCent θ δ with hT'
  have hCent : T' = B.T.map ι := GlobalTheory.T.twistedCentralizer_eq_map_normOneTorus E w hw K e he a B hP β ε hε hβ b δ hδ
  have hinj : Function.Injective ι := mulGL_injective e b
  have hθK : ∀ k ∈ Kg, θ k ∈ Kg := GlobalTheory.BCT.ThBasic.thL_mem_KGL hU a w

  have hstab : ∀ (t : B.Aˣ) (q : GLw a w), ι t ∈ Kg.map (MulAut.conj q).toMonoidHom ↔
      t ∈ stabLat K.O (GlobalTheory.TwLat.lat e b q) := by
    intro t q
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, mem_stabLat_iff,
      ← latOf_mul e b t q, eq_comm, GlobalTheory.T.latticeSpannedByGLColumns_eq_iff E w K e hO a B b, mul_assoc]
  have hcpt : cptPart T' = (intUnits K.O B.A ⊓ B.T).map ι := by
    rw [hCent]
    unfold cptPart
    have hS : {x | x ∈ B.T.map ι ∧ IsCompact (closure (Subgroup.zpowers x : Set (GLw a w)))} =
        ι '' ((intUnits K.O B.A ⊓ B.T : Subgroup B.Aˣ) : Set B.Aˣ) := by
      ext x
      constructor
      · rintro ⟨⟨t, ht, rfl⟩, hc⟩
        exact ⟨t, ⟨(GlobalTheory.T.isCompact_closure_zpowers_leftMulGL_iff_integral E w K e hO a B b t).1 hc, ht⟩, rfl⟩
      · rintro ⟨t, ⟨hi, ht⟩, rfl⟩
        exact ⟨⟨t, ht, rfl⟩, (GlobalTheory.T.isCompact_closure_zpowers_leftMulGL_iff_integral E w K e hO a B b t).2 hi⟩
    rw [hS, ← MonoidHom.map_closure, Subgroup.closure_eq]
  have hRel : ∀ y : GLw a w, (T' ⊓ Kg.map (MulAut.conj y).toMonoidHom).relIndex (cptPart T') =
      (stabLat K.O (GlobalTheory.TwLat.lat e b y) ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) := by
    intro y
    have h1 : T' ⊓ Kg.map (MulAut.conj y).toMonoidHom = (stabLat K.O (GlobalTheory.TwLat.lat e b y) ⊓ B.T).map ι := by
      ext x
      rw [Subgroup.mem_inf, hCent]
      constructor
      · rintro ⟨⟨t, ht, rfl⟩, hx⟩
        exact ⟨t, ⟨(hstab t y).1 hx, ht⟩, rfl⟩
      · rintro ⟨t, ⟨hs, ht⟩, rfl⟩
        exact ⟨⟨t, ht, rfl⟩, (hstab t y).2 hs⟩
    rw [h1, hcpt, Subgroup.relIndex_map_map_of_injective _ _ hinj]

  set P : GLw a w → Prop := fun y => y⁻¹ * δ * θ y ∈ Kg with hP_def
  have hPinv : ∀ (y t k : GLw a w), t ∈ T' → k ∈ Kg → (P (t * y * k) ↔ P y) := by
    intro y t k ht hk
    have hd : t⁻¹ * δ * θ t = δ := by
      rw [mul_assoc, ← (GlobalTheory.TwOrbConj.mem_twCent θ δ t).1 ht, inv_mul_cancel_left]
    have e1 : (t * y * k)⁻¹ * δ * θ (t * y * k) = k⁻¹ * (y⁻¹ * δ * θ y) * θ k := by
      calc (t * y * k)⁻¹ * δ * θ (t * y * k) = k⁻¹ * (y⁻¹ * (t⁻¹ * δ * θ t) * θ y) * θ k := by
            simp only [map_mul, _root_.mul_inv_rev]; group
        _ = k⁻¹ * (y⁻¹ * δ * θ y) * θ k := by rw [hd]
    simp only [hP_def]
    rw [e1]
    constructor
    · intro h
      have := Kg.mul_mem (Kg.mul_mem hk h) (Kg.inv_mem (hθK k hk))
      simpa [mul_assoc] using this
    · intro h
      exact Kg.mul_mem (Kg.mul_mem (Kg.inv_mem hk) h) (hθK k hk)

  have hsum : ∀ y : GLw a w, GlobalTheory.TwOrbConj.summand θ Kg δ ((Kg : Set (GLw a w)).indicator 1) y =
      if P y then ((((stabLat K.O (GlobalTheory.TwLat.lat e b y) ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) : ℕ) : ℂ)) else 0 := by
    intro y
    have hconst : (fun k : Kg => (Kg : Set (GLw a w)).indicator 1 ((y * k)⁻¹ * δ * θ (y * k))) =
        fun _ => (if P y then (1 : ℂ) else 0) := by
      funext k
      have := hPinv y 1 k (T'.one_mem) k.2
      rw [one_mul] at this
      simp only [Set.indicator_apply, SetLike.mem_coe, Pi.one_apply]
      by_cases h : P y
      · rw [if_pos h, if_pos ((this.2 h))]
      · rw [if_neg h, if_neg (fun h' => h (this.1 h'))]
    unfold GlobalTheory.TwOrbConj.summand
    rw [hconst, avg_const, hRel]
    split_ifs <;> simp

  set X : Set (Submodule K.O B.A) := {L : Submodule K.O B.A | IsLat K.O K.E L ∧
    ∀ z, z ∈ L ↔ ∀ y ∈ L, B.herm β y z ∈ (algebraMap K.O K.E).range} with hX
  have hUni : ∀ y : GLw a w, P y ↔ GlobalTheory.TwLat.lat e b y ∈ X := by
    intro y
    simp only [hP_def, hX, Set.mem_setOf_eq]
    rw [GlobalTheory.T.twistedConj_integral_iff_lattice_unimodular E w hw K e he hO a B β b δ hδ y]
    exact ⟨fun h => ⟨latOf_isLat e b y, h⟩, fun h => h.2⟩
  let r : X → X → Prop := fun L M => ∃ t ∈ B.T, (M : Submodule K.O B.A) = mulLat K.O (t : B.A) (L : Submodule K.O B.A)
  have hr : Equivalence r := by
    refine ⟨fun L => ⟨1, B.T.one_mem, ?_⟩, fun {L M} ⟨t, ht, h⟩ => ⟨t⁻¹, B.T.inv_mem ht, ?_⟩,
      fun {L M N} ⟨t, ht, h⟩ ⟨s, hs, h'⟩ => ⟨s * t, B.T.mul_mem hs ht, ?_⟩⟩
    · ext y; rw [mulLat_mem_iff]; simp
    · ext y; rw [mulLat_mem_iff, h, mulLat_mem_iff]; simp
    · ext y; rw [h', mulLat_mem_iff, h, mulLat_mem_iff, mulLat_mem_iff, ← mul_assoc]; simp [mul_comm]

  let φ : {q : DoubleCoset.Quotient (T' : Set (GLw a w)) (Kg : Set (GLw a w)) // P (Quotient.out q)} →
      Orb K.O B.T X := fun q => Quot.mk _ ⟨GlobalTheory.TwLat.lat e b (Quotient.out q.1), (hUni _).1 q.2⟩
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨q, hq⟩ ⟨q', hq'⟩ h
      obtain ⟨t, ht, h1⟩ := hr.eqvGen_iff.1 (Quot.eqvGen_exact h)
      simp only at h1
      rw [← latOf_mul e b t, GlobalTheory.T.latticeSpannedByGLColumns_eq_iff E w K e hO a B b] at h1
      apply Subtype.ext
      simp only
      rw [← DoubleCoset.out_eq' T' Kg q, ← DoubleCoset.out_eq' T' Kg q', DoubleCoset.eq]
      refine ⟨ι t, by rw [hCent]; exact ⟨t, ht, rfl⟩, _, Kg.inv_mem h1, ?_⟩
      rw [_root_.mul_inv_rev, inv_inv, mul_inv_cancel_left]
    · intro o
      induction o using Quot.ind with
      | mk L =>
        obtain ⟨q0, hq0⟩ := GlobalTheory.T.exists_GL_latticeSpannedByGLColumns_eq_fullLattice E w K e a B b L.1 L.2.1
        obtain ⟨t', ht', k, hk, he'⟩ := (DoubleCoset.eq _ _ _ _).1
          (DoubleCoset.out_eq' T' Kg (DoubleCoset.mk T' Kg q0)).symm
        have hP0 : P q0 := (hUni q0).2 (hq0 ▸ L.2)
        refine ⟨⟨DoubleCoset.mk _ _ q0, by rw [he']; exact (hPinv q0 t' k ht' hk).2 hP0⟩, ?_⟩
        apply Quot.sound
        rw [hCent] at ht'
        obtain ⟨t, ht, rfl⟩ := ht'
        refine ⟨t⁻¹, B.T.inv_mem ht, ?_⟩
        show L.1 = _
        simp only
        rw [he', mul_assoc, latOf_mul e b t,
          ← (GlobalTheory.T.latticeSpannedByGLColumns_eq_iff E w K e hO a B b q0 (q0 * k)).2 (by simpa using hk), hq0]
        ext y; rw [mulLat_mem_iff, mulLat_mem_iff]; simp

  rw [GlobalTheory.TwOrbConj.twOrb_eq, orbSum, cast_finsum]
  simp_rw [hsum]
  rw [show (∑ᶠ q : DoubleCoset.Quotient (T' : Set (GLw a w)) (Kg : Set (GLw a w)), if P (Quotient.out q) then
      ((((stabLat K.O (GlobalTheory.TwLat.lat e b (Quotient.out q)) ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) : ℕ) : ℂ)) else 0) =
      ∑ᶠ q : {q : DoubleCoset.Quotient (T' : Set (GLw a w)) (Kg : Set (GLw a w)) // P (Quotient.out q)},
        ((((stabLat K.O (GlobalTheory.TwLat.lat e b (Quotient.out q.1)) ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) : ℕ) : ℂ)) by
    exact (finsum_congr fun q => finsum_eq_if.symm).trans (finsum_subtype_eq_finsum_cond
      (fun q : DoubleCoset.Quotient (T' : Set (GLw a w)) (Kg : Set (GLw a w)) => P (Quotient.out q))
      (f := fun q => ((((stabLat K.O (GlobalTheory.TwLat.lat e b (Quotient.out q)) ⊓ B.T).relIndex
        (intUnits K.O B.A ⊓ B.T) : ℕ) : ℂ)))).symm]
  refine finsum_eq_of_bijective φ hφ fun q => ?_
  obtain ⟨s, hs, hs'⟩ := hr.eqvGen_iff.1 (Quot.eqvGen_exact (Quot.out_eq (φ q)))
  have hs2 : GlobalTheory.TwLat.lat e b (Quotient.out q.1) = mulLat K.O (s : B.A) (Quot.out (φ q)).1 := hs'
  rw [hs2, stabLat_mulLat]
  push_cast
  simp
