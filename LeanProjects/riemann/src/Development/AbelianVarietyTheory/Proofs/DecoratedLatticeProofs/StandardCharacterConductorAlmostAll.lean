import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddCharTrivialIntegralFiniteAdeleMul

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer NumberField Filter
open IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.Conductor

theorem exists_denominator (E : Type) [Field E] [NumberField E] :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ x : E, (∀ o : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (x * o) = n) → ∃ o : 𝓞 E, (o : E) = N • x := by
  classical
  let b := NumberField.integralBasis E
  obtain ⟨N, hN, h⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image b.traceDual)
  refine ⟨N, hN, fun x hx => ?_⟩
  have hi : IsIntegral ℤ (N • x) := by
    rw [← b.traceDual.sum_repr x, Finset.smul_sum]
    refine IsIntegral.sum _ fun i _ => ?_
    obtain ⟨n, hn⟩ := hx (RingOfIntegers.basis E i)
    have e : b.traceDual.repr x i = (n : ℚ) := by
      rw [← hn, Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply]
      simp [b]
    rw [e, Int.cast_smul_eq_zsmul, smul_comm]
    exact (h _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))).zsmul n
  exact ⟨⟨_, hi⟩, rfl⟩

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]

theorem af_ext {a b : Af F} (h : ∀ w, evalV F w a = evalV F w b) : a = b :=
  DFunLike.ext _ _ h

theorem ev_same (v : HeightOneSpectrum (𝓞 F)) : evalV F v (singleV F v 1) = 1 :=
  GlobalTheory.LatVac.evalV_singleV_same F v

theorem ev_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) : evalV F w (singleV F v 1) = 0 :=
  GlobalTheory.LatVac.evalV_singleV_ne F v w h

theorem idem_mul (v : HeightOneSpectrum (𝓞 F)) (z : Af F ⊗[F] E)
    (h : ∀ w, w ≠ v → Algebra.TensorProduct.map (evalV F w) (AlgHom.id F E) z = 0) :
    (singleV F v 1 ⊗ₜ[F] (1 : E)) * z = z := by
  classical
  let b := Module.finBasis F E
  have key : ∀ (w) (z : Af F ⊗[F] E) i,
      (Algebra.TensorProduct.basis (Fv F w) b).repr (Algebra.TensorProduct.map (evalV F w) (AlgHom.id F E) z) i =
        evalV F w ((Algebra.TensorProduct.basis (Af F) b).repr z i) := by
    intro w z i
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [Algebra.TensorProduct.basis_repr_tmul]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  have e : (singleV F v 1 ⊗ₜ[F] (1 : E)) * z = singleV F v 1 • z := by
    rw [Algebra.smul_def]; rfl
  rw [e]
  refine (Algebra.TensorProduct.basis (Af F) b).ext_elem fun i => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  refine af_ext fun w => ?_
  rw [map_mul]
  by_cases hw : w = v
  · subst hw; rw [ev_same, one_mul]
  · rw [ev_ne hw, zero_mul, ← key, h w hw, map_zero, Finsupp.zero_apply]

theorem idem_mul_mem {v : HeightOneSpectrum (𝓞 F)} {α : Af F} (h : evalV F v α ∈ v.adicCompletionIntegers F) :
    singleV F v 1 * α ∈ intAf F := fun w => by
  rw [map_mul]
  by_cases hw : w = v
  · subst hw; rwa [ev_same, one_mul]
  · rw [ev_ne hw, zero_mul]; exact zero_mem _

theorem tmul_denominator {A : Type} [CommRing A] [Algebra F A] (a : A) {N : ℤ} (hN : N ≠ 0) (x : E) :
    (a ⊗ₜ[F] (1 : E)) * (1 ⊗ₜ[F] x) = (a * algebraMap F A (N : F)⁻¹) ⊗ₜ[F] (N • x) := by
  have hN' : (N : F) ≠ 0 := Int.cast_ne_zero.2 hN
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul,
    ← Int.cast_smul_eq_zsmul F, smul_smul, inv_mul_cancel₀ hN', one_smul]

theorem trace_map {A B : Type} [CommRing A] [Algebra F A] [CommRing B] [Algebra F B] (f : A →ₐ[F] B) (z : A ⊗[F] E) :
    Algebra.trace B (B ⊗[F] E) (Algebra.TensorProduct.map f (AlgHom.id F E) z) = f (Algebra.trace A (A ⊗[F] E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a e =>
    rw [Algebra.TensorProduct.map_tmul, GlobalTheory.LatVac.trace_tmul, GlobalTheory.LatVac.trace_tmul, map_mul, AlgHom.commutes]; rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end General

variable {D : D7}

theorem trace_parts (s : AE D) : Algebra.trace (AF D.host.F) (AE D) s =
    pairA D.host.F (Algebra.trace (Ainf D.host.F) _ (infPart D s)) (Algebra.trace (Af D.host.F) _ (finPart D s)) :=
  Prod.ext (trace_map (fstA D.host.F) s).symm (trace_map (sndA D.host.F) s).symm

def chi (ψ : AddChar (AF D.host.F) ℂ) (z : Af D.host.F ⊗[D.host.F] D.host.E) : ℂ :=
  ψ (pairA D.host.F 0 (Algebra.trace (Af D.host.F) _ z))

theorem chi_add (ψ : AddChar (AF D.host.F) ℂ) (x y : Af D.host.F ⊗[D.host.F] D.host.E) :
    chi ψ (x + y) = chi ψ x * chi ψ y := by
  rw [chi, map_add, GlobalTheory.LatVac.pair_add, ψ.map_add_eq_mul]; rfl

theorem chi_zero (ψ : AddChar (AF D.host.F) ℂ) : chi ψ 0 = 1 := by
  rw [chi, map_zero]; exact ψ.map_zero_eq_one

theorem psiE_eq_chi (ψ : AddChar (AF D.host.F) ℂ) {s : AE D} (h : infPart D s = 0) : psiE ψ s = chi ψ (finPart D s) := by
  rw [psiE, trace_parts, h, map_zero]; rfl

theorem chi_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (x : D.host.E) :
    chi ψ (1 ⊗ₜ[D.host.F] x) = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ D.host.E x = n := by
  rw [chi, GlobalTheory.LatVac.trace_tmul, one_mul, GlobalTheory.LatVac.char_rat hψ]

theorem chi_int {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {z : Af D.host.F ⊗[D.host.F] D.host.E}
    (hz : z ∈ intAE D) : chi ψ z = 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, o, rfl⟩ := hw
    rw [chi, GlobalTheory.LatVac.trace_tmul]
    refine GlobalTheory.IntDense.addChar_eq_one_of_integral D.host.F ψ hψ.1.1 _ (fun a => ?_) _ hα
    rw [← smul_eq_mul, ← map_smul, GlobalTheory.LatVac.char_rat hψ]
    have hi : IsIntegral ℤ ((a : D.host.F) • (o : D.host.E)) := by
      rw [Algebra.smul_def]
      exact (a.isIntegral_coe.map (IsScalarTower.toAlgHom ℤ D.host.F D.host.E)).mul o.isIntegral_coe
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_trace (L := ℚ) hi)
    exact ⟨n, hn.symm⟩
  | zero => exact chi_zero ψ
  | add x y _ _ hx hy => rw [chi_add, hx, hy, one_mul]
  | neg x _ hx =>
    have := chi_add ψ x (-x)
    rwa [add_neg_cancel, chi_zero, hx, one_mul, eq_comm] at this

theorem tmul_mem {α : Af D.host.F} (hα : α ∈ intAf D.host.F) (o : 𝓞 D.host.E) :
    α ⊗ₜ[D.host.F] (o : D.host.E) ∈ intAE D :=
  AddSubgroup.subset_closure ⟨α, hα, o, rfl⟩

theorem mul_mem_int {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, o, rfl⟩ := hw
    induction hy using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨β, hβ, o', rfl⟩ := hw
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact tmul_mem (GlobalTheory.LatVac.mul_mem_intAf hα hβ) (o * o')
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | neg x _ hx => rw [mul_neg]; exact neg_mem hx
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

theorem approx (z : Af D.host.F ⊗[D.host.F] D.host.E) :
    ∃ x : D.host.E, ∃ u ∈ intAE D, z = 1 ⊗ₜ[D.host.F] x + u := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | add x y hx hy =>
    obtain ⟨a, u, hu, rfl⟩ := hx
    obtain ⟨b, u', hu', rfl⟩ := hy
    exact ⟨a + b, u + u', add_mem hu hu', by rw [TensorProduct.tmul_add, add_add_add_comm]⟩
  | tmul a x =>
    obtain ⟨N, hN, h⟩ := exists_integral_multiples ℤ ℚ ({x} : Finset D.host.E)
    have hi : IsIntegral ℤ (N.natAbs • x) := by
      have := h x (Finset.mem_singleton_self x)
      rcases Int.natAbs_eq N with e | e
      · rwa [e, natCast_zsmul] at this
      · rw [e, neg_smul, natCast_zsmul] at this
        simpa using this.neg
    obtain ⟨a0, β, hβ, hab⟩ :=
      (GlobalTheory.AdLat.strong_approximation_mod_nat D.host.F N.natAbs (Int.natAbs_pos.2 hN)).1 a
    refine ⟨a0 • x, _, tmul_mem (α := β) hβ ⟨_, hi⟩, ?_⟩
    rw [hab]
    exact GlobalTheory.LatVac.approx_tmul a0 _ β x

theorem lift_mem (v : Pl D) (o : 𝓞 D.host.E) :
    pairA D.host.F 0 (singleV D.host.F v 1) ⊗ₜ[D.host.F] (o : D.host.E) ∈ intAt D (· = v) := by
  refine ⟨⟨GlobalTheory.LatVac.infPart_pair _ _, ?_⟩, ?_⟩
  · refine (Submodule.mem_iInf _).2 fun w => ?_
    have : compAt D w.1 (pairA D.host.F 0 (singleV D.host.F v 1) ⊗ₜ[D.host.F] (o : D.host.E)) =
        evalV D.host.F w.1 (singleV D.host.F v 1) ⊗ₜ[D.host.F] (o : D.host.E) := rfl
    rw [RingHom.mem_ker, this, ev_ne w.2, TensorProduct.zero_tmul]
  · rw [GlobalTheory.LatVac.finPart_pair]
    have := idem_mul_mem (v := v) (α := 1) (by rw [map_one]; exact one_mem _)
    rw [mul_one] at this
    exact tmul_mem this o

theorem eventually_conductor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ᶠ v : Pl D in cofinite, ∀ s ∈ idAt D (· = v),
      (∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1) ↔ s ∈ intAt D (· = v) := by
  intro D ψ hψ
  obtain ⟨N, hN, hden⟩ := exists_denominator D.host.E
  have hev : ∀ᶠ v : Pl D in cofinite,
      evalV D.host.F v (algebraMap D.host.F (Af D.host.F) (N : D.host.F)⁻¹) ∈ v.adicCompletionIntegers D.host.F :=
    (algebraMap D.host.F (Af D.host.F) (N : D.host.F)⁻¹).2
  filter_upwards [hev] with v hv s hs
  have hinf : ∀ o, infPart D (s * o) = 0 := fun o => by
    have : infPart D s = 0 := hs.1
    rw [RingHom.map_mul, this, zero_mul]
  refine ⟨fun h => ⟨hs, ?_⟩, fun h o ho => ?_⟩
  · have hz : (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * finPart D s = finPart D s :=
      idem_mul v _ fun w hw => (Submodule.mem_iInf _).1 hs.2 ⟨w, hw⟩
    obtain ⟨x, u, hu, e⟩ := approx (finPart D s)
    have hε : singleV D.host.F v 1 ∈ intAf D.host.F := by
      have := idem_mul_mem (v := v) (α := 1) (by rw [map_one]; exact one_mem _)
      rwa [mul_one] at this
    obtain ⟨y, hy⟩ := hden x fun o => by
      have h1 := h _ (lift_mem v o)
      have e1 : singleV D.host.F v 1 ⊗ₜ[D.host.F] (o : D.host.E) =
          (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * (1 ⊗ₜ[D.host.F] (o : D.host.E)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [psiE_eq_chi ψ (hinf _), RingHom.map_mul, GlobalTheory.LatVac.finPart_pair, e1, ← mul_assoc, mul_comm (finPart D s), hz, e,
        add_mul, chi_add, chi_int hψ (mul_mem_int hu (tmul_mem (GlobalTheory.LatVac.one_mem_intAf _) o)), mul_one,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one] at h1
      exact (chi_rat hψ _).1 h1
    rw [← hz, e, mul_add]
    refine add_mem ?_ (mul_mem_int (tmul_mem hε 1) hu)
    rw [tmul_denominator _ hN, ← hy]
    exact tmul_mem (idem_mul_mem hv) y
  · rw [psiE_eq_chi ψ (hinf _), RingHom.map_mul]
    exact chi_int hψ (mul_mem_int h.2 ho.2)

end GlobalTheory.FinPl.Conductor
