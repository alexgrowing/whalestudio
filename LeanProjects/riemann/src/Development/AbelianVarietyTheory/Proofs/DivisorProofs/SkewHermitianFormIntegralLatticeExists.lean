import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFundamentalDomainMulRight
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.AdelicIsomorphismStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.UnitaryPointsRankZeroSubsingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BridgeSIsBridge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanEqTopOfSmul
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThetaCplV
open Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SkewSelfDual

open GlobalTheory.ModularLattice
open scoped nonZeroDivisors

section Form

variable {E : Type} [Field E] (σ : E →+* E) {d : ℕ} (H : Matrix (Fin d) (Fin d) E)

theorem hform_eq (y x : Fin d → E) : Formalism.UG.hform σ H y x = (fun i => σ (y i)) ⬝ᵥ H *ᵥ x := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_add (y x x' : Fin d → E) :
    Formalism.UG.hform σ H y (x + x') = Formalism.UG.hform σ H y x + Formalism.UG.hform σ H y x' := by
  rw [hform_eq, hform_eq, hform_eq, Matrix.mulVec_add, dotProduct_add]

theorem hform_smul (y : Fin d → E) (a : E) (x : Fin d → E) :
    Formalism.UG.hform σ H y (a • x) = a * Formalism.UG.hform σ H y x := by
  rw [hform_eq, hform_eq, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hform_symm (hσ : ∀ x, σ (σ x) = x) (hH : ∀ i j, σ (H j i) = H i j) (x y : Fin d → E) :
    Formalism.UG.hform σ H y x = σ (Formalism.UG.hform σ H x y) := by
  simp only [Formalism.UG.hform, map_sum, map_mul, hσ, hH]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Form

variable {E : Type} [Field E] [NumberField E]

theorem mem_dual_one_iff (w : E) : w ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔
    ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * w)) := by
  have h10 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    intro h
    have h1 : (1 : E) ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := FractionalIdeal.one_mem_one _
    rw [h, FractionalIdeal.mem_zero_iff] at h1
    exact one_ne_zero h1
  rw [FractionalIdeal.mem_dual h10]
  constructor
  · intro h o
    have h1 := h (o : E) ((FractionalIdeal.mem_one_iff _).2 ⟨o, rfl⟩)
    rw [Algebra.traceForm_apply, mul_comm] at h1
    obtain ⟨q, hq⟩ := h1
    rw [← hq]
    exact isIntegral_algebraMap
  · intro h a ha
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    rw [Algebra.traceForm_apply, mul_comm]
    exact IsIntegrallyClosed.isIntegral_iff.1 (h o)

theorem trace_conj {σ : E →+* E} (hσ : ∀ x, σ (σ x) = x) (z : E) : Algebra.trace ℚ E (σ z) = Algebra.trace ℚ E z :=
  Algebra.trace_eq_of_algEquiv
    (AlgEquiv.ofBijective σ.toRatAlgHom (Function.Involutive.bijective (f := σ) hσ)) z

theorem eq_zero_of_line {d : ℕ} {L : Submodule (𝓞 E) (Fin d → E)} (hL : L.FG) {v : Fin d → E}
    (hv : ∀ e : E, e • v ∈ L) : v = 0 := by
  by_contra h
  obtain ⟨i, hi⟩ := Function.ne_iff.1 h
  have htop : L.map (LinearMap.proj i : (Fin d → E) →ₗ[𝓞 E] E) = ⊤ := by
    refine eq_top_iff.2 fun e _ => ⟨_, hv (e / v i), ?_⟩
    simpa using div_mul_cancel₀ e hi
  haveI : Module.Finite (𝓞 E) E := ⟨htop ▸ hL.map _⟩
  exact RingOfIntegers.not_isField E
    ((Algebra.IsIntegral.isField_iff_isField (IsFractionRing.injective (𝓞 E) E)).2 (Field.toIsField E))

theorem exists_conj_sub_notMem {F : Type} [Field F] [NumberField F] [Algebra F E] (σ : E →ₐ[F] E)
    (hun : Algebra.Unramified (𝓞 F) (𝓞 E)) {c : E} (hc : σ c ≠ c) (p : Ideal (𝓞 E)) (hp : p.IsMaximal) :
    ∃ θ, conjO (σ : E →+* E) θ - θ ∉ p := by
  by_contra hcon
  push Not at hcon
  have h1 : RingOfIntegers.mapAlgHom σ = AlgHom.id (𝓞 F) (𝓞 E) :=
    Algebra.FormallyUnramified.ext_of_iInf p (Ideal.iInf_pow_eq_bot_of_isDomain p hp.ne_top)
      fun x => Ideal.Quotient.eq.2 (hcon x)
  have h2 : ∀ o : 𝓞 E, σ (algebraMap (𝓞 E) E o) = algebraMap (𝓞 E) E o := fun o =>
    congrArg (algebraMap (𝓞 E) E) (AlgHom.congr_fun h1 o)
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) c
  exact hc (by rw [map_div₀, h2, h2])

theorem exists_selfDual_smul_skew : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d r s : ℕ) (W : Spc F E d), B.IsGood σ → W.IsSkew σ B r s → Even d → ∀ c : E, c ≠ 0 → σ c = -c → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ (c • W.J.map σ) ∧ ∃ L : Submodule (𝓞 E) (Fin d → E), L.FG ∧ Submodule.span E (L : Set (Fin d → E)) = ⊤ ∧ ∀ x : Fin d → E, x ∈ L ↔ ∀ y ∈ L, Formalism.UG.hform (σ : E →+* E) (c • W.J.map σ) y x ∈ (algebraMap (𝓞 E) E).range := by
  intro F E _ _ _ _ _ σ B d r s W hB hW hd c hc0 hc
  have hσ : ∀ x, (σ : E →+* E) ((σ : E →+* E) x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    exact (hB.cm.2.2.2 τ _).trans ((congrArg star (hB.cm.2.2.2 τ x)).trans (star_star _))
  have hσ' : ∀ x, σ (σ x) = x := hσ
  have hH : ∀ i j, σ ((c • W.J.map σ) j i) = (c • W.J.map σ) i j := by
    intro i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, hc, hσ', hW.skew j i]
    ring
  have hform : ∀ y x, Formalism.UG.hform (σ : E →+* E) (c • W.J.map σ) y x = c * -form σ W.J x y := by
    intro y x
    simp only [Formalism.UG.hform, form, dotProduct, Matrix.mulVec, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      RingHom.coe_coe, Finset.mul_sum, mul_neg, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hW.skew i j]; ring
  let D := FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)
  let A := FractionalIdeal.spanSingleton (𝓞 E)⁰ c * D
  have hneg : ∀ z ∈ D, -z ∈ D := fun z hz => D.coeToSubmodule.neg_mem hz
  have hA : ∀ z, c * -z ∈ A ↔ z ∈ D := by
    intro z
    rw [FractionalIdeal.mem_singleton_mul]
    refine ⟨fun ⟨y, hy, e⟩ => ?_, fun hz => ⟨_, hneg z hz, rfl⟩⟩
    have := hneg y hy
    rwa [← mul_left_cancel₀ hc0 e, neg_neg] at this
  have hDσ : ∀ z ∈ D, σ z ∈ D := by
    intro z hz
    rw [mem_dual_one_iff] at hz ⊢
    intro o
    rw [← trace_conj hσ, map_mul]
    have e : (σ : E →+* E) (σ z) = z := hσ' z
    rw [e]
    exact hz (conjO (σ : E →+* E) o)
  have hAσ : ∀ z ∈ A, (σ : E →+* E) z ∈ A := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := FractionalIdeal.mem_singleton_mul.1 hz
    have e : (σ : E →+* E) (c * y) = c * -σ y := by
      rw [RingHom.coe_coe, map_mul, hc]; ring
    rw [e, hA]
    exact hDσ y hy
  have hA0 : A ≠ 0 := mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 hc0)
    (FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero)
  have hdual : ∀ x, x ∈ W.L ↔ ∀ y ∈ W.L, Formalism.UG.hform (σ : E →+* E) (c • W.J.map σ) y x ∈ A := by
    intro x
    rw [hW.dual]
    refine forall₂_congr fun y _ => ?_
    rw [hform, hA, mem_dual_one_iff]
  refine ⟨⟨hH, fun hdet => ?_⟩, ?_⟩
  · obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    refine hv0 (eq_zero_of_line hW.lat.fg fun e => (hdual _).2 fun y _ => ?_)
    rw [hform_smul, hform_eq, hv, dotProduct_zero, mul_zero]
    exact FractionalIdeal.zero_mem _
  · obtain ⟨L, h1, h2, h3⟩ := HasModular.one hσ (hform_add _ _) (hform_smul _ _) (hform_symm _ _ hσ hH) hd
      (exists_conj_sub_notMem σ hB.unram (c := c) fun e => hc0 (by linear_combination (e.symm.trans hc) / 2))
      hA0 hAσ ⟨W.L, hW.lat.fg, hW.lat.span_eq_top, hdual⟩
    refine ⟨L, h1, h2, fun x => ?_⟩
    rw [h3]
    refine forall₂_congr fun y _ => ?_
    rw [FractionalIdeal.mem_one_iff]
    rfl

end GlobalTheory.SkewSelfDual
