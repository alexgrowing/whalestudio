import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatVac.RatDual

open Formalism.L2.Pj

variable {D : D7}

theorem mem_mul_of_trace (D : D7) (z : D.host.E)
    (h : ∀ a : 𝓞 D.host.E, ∃ n : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * (a * z)) = n) :
    z ∈ D.host.AA * D.host.AAbar := by
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have hξ := cmHost_imaginaryGenerator_ne_zero hP D
  have hz : D.host.xi0 * z ∈
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    rw [FractionalIdeal.mem_dual
      (@one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) _ _ _)]
    intro a ha
    rw [FractionalIdeal.mem_one_iff] at ha
    obtain ⟨c, rfl⟩ := ha
    obtain ⟨n, hn⟩ := h c
    rw [Algebra.traceForm_apply, mul_assoc, mul_comm z]
    exact ⟨n, (eq_intCast (algebraMap ℤ ℚ) _).trans hn.symm⟩
  rw [← dual_eq hP D] at hz
  have h4 := FractionalIdeal.mul_mem_mul
    (FractionalIdeal.mem_spanSingleton_self (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0⁻¹) hz
  have e1 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0⁻¹ *
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0 * D.host.AA * D.host.AAbar) =
      D.host.AA * D.host.AAbar := by
    rw [mul_assoc, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hξ,
      FractionalIdeal.spanSingleton_one, one_mul]
  rwa [e1, ← mul_assoc, inv_mul_cancel₀ hξ, one_mul] at h4

theorem mem_AA_of_trace (D : D7) (z : D.host.E)
    (h : ∀ a ∈ D.host.AA, ∃ n : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * (star a * z)) = n) :
    z ∈ D.host.AA := by
  have hAb : D.host.AAbar ≠ 0 := by
    intro h
    have h1 := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
    rw [h, mul_zero, zero_mul] at h1
    exact zero_ne_one h1
  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) z *
      D.host.AAbar ≤ D.host.AA * D.host.AAbar := by
    rw [FractionalIdeal.spanSingleton_mul_le_iff]
    intro b hb
    refine mem_mul_of_trace D _ fun c => ?_
    have hcb : (c : D.host.E) * b ∈ D.host.AAbar :=
      Submodule.smul_mem (D.host.AAbar : Submodule (𝓞 D.host.E) D.host.E) c hb
    have := h _ (conj_mem_AA D hcb)
    have hs : star (D.host.conj ((c : D.host.E) * b)) = (c : D.host.E) * b :=
      (bridge_star_holds D.R D.host _).trans (conj_conj D _)
    rwa [hs, mul_assoc, mul_comm b] at this
  have hle2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) z ≤ D.host.AA := by
    calc FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) z
        = D.host.AAbar⁻¹ * (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E))
            z * D.host.AAbar) := by
          rw [mul_comm _ D.host.AAbar, ← mul_assoc, inv_mul_cancel₀ hAb, one_mul]
      _ ≤ D.host.AAbar⁻¹ * (D.host.AA * D.host.AAbar) := CovariantClass.elim D.host.AAbar⁻¹ hle
      _ = D.host.AA := by rw [mul_comm D.host.AA, ← mul_assoc, inv_mul_cancel₀ hAb, one_mul]
  exact hle2 (FractionalIdeal.mem_spanSingleton_self _ _)

theorem form_smul (T : HSp D) (e : D.host.E) (t y : Fin T.rank → D.host.E) :
    ∑ c, ∑ d, star (t c) * T.gram c d * (e • y) d = e * ∑ c, ∑ d, star (t c) * T.gram c d * y d := by
  simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem genMap_mulVec (S T : HSp D) (a : D.host.E) (s' s : Fin S.rank → D.host.E)
    (t : Fin T.rank → D.host.E) :
    genMap S T a s' t *ᵥ s = (a * ∑ c, ∑ d, star (s' c) * S.gram c d * s d) • t := by
  funext i
  rw [Finset.sum_comm]
  simp only [genMap, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem hRat_add_left (S T : HSp D) (x x' y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    hRat S T (x + x') y = hRat S T x y + hRat S T x' y := by
  simp only [hRat, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem hRat_add_right (S T : HSp D) (x y y' : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    hRat S T x (y + y') = hRat S T x y + hRat S T x y' := by
  simp only [hRat, Matrix.add_apply, star_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem hRat_neg_left (S T : HSp D) (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    hRat S T (-x) y = -hRat S T x y := by
  simp only [hRat, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem hRat_neg_right (S T : HSp D) (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    hRat S T x (-y) = -hRat S T x y := by
  simp only [hRat, Matrix.neg_apply, star_neg, mul_neg, neg_mul, Finset.sum_neg_distrib]

theorem hRat_mem (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    {ρ ℓ : Matrix (Fin T.rank) (Fin S.rank) D.host.E}
    (hρ : ρ ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)))
    (hℓ : ℓ ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))) :
    hRat S T ρ ℓ ∈ NAA D := by
  induction hρ using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a', ha', s', hs', t', ht', rfl⟩ := hw
    induction hℓ using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hw
      obtain ⟨p, hp⟩ := (hS.2 s).1 hs s' hs'
      obtain ⟨q, hq⟩ := (hT.2 t').1 ht' t ht
      rw [hRat_genMap, genMap_mulVec, form_smul, ← hp, ← hq]
      have hs : star a = D.host.conj a := bridge_star_holds D.R D.host a
      have e : star a * (a' * (p : D.host.E) * (q : D.host.E)) = (p * q) • (a' * D.host.conj a) := by
        rw [hs, Algebra.smul_def, map_mul]
        change _ = (p : D.host.E) * (q : D.host.E) * _
        ring
      rw [e]
      exact Submodule.smul_mem _ _ (FractionalIdeal.mul_mem_mul ha' (conj_mem_AAbar D ha))
    | zero => simp [hRat]
    | add x y _ _ hx hy => rw [hRat_add_right]; exact add_mem hx hy
    | neg x _ hx => rw [hRat_neg_right]; exact neg_mem hx
  | zero => simp [hRat]
  | add x y _ _ hx hy => rw [hRat_add_left]; exact add_mem hx hy
  | neg x _ hx => rw [hRat_neg_left]; exact neg_mem hx

end GlobalTheory.LatVac.RatDual

namespace GlobalTheory.LatVac

open RatDual Formalism.L2.Pj

theorem latRat_selfDual : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (∃ (n : ℕ) (s s' : Fin n → Fin S.rank → D.host.E), (∀ i, s i ∈ ΛS ∧ s' i ∈ ΛS) ∧ ∀ a j, ∑ i, s i a * ∑ k, star (s' i k) * S.gram k j = if a = j then 1 else 0) → ∀ ρ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ρ ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) ↔ ∀ ℓ ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)), ∃ n : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * hRat S T ρ ℓ) = n := by
  intro D S T ΛS ΛT hS hT ⟨n, s, s', hss, hdual⟩ ρ
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have hAA := AA_ne_zero hP D
  refine ⟨fun hρ ℓ hℓ => trace_int_of_mem hP D (hRat_mem S T ΛS ΛT hS hT hρ hℓ), fun h => ?_⟩
  have h5 : ∀ v ∈ ΛS, ∀ t ∈ ΛT, ∑ c, ∑ d, star (t c) * T.gram c d * (ρ *ᵥ v) d ∈ D.host.AA := by
    intro v hv t ht
    refine mem_AA_of_trace D _ fun a ha => ?_
    rw [← hRat_genMap]
    exact h _ (AddSubgroup.subset_closure ⟨a, ha, v, hv, t, ht, rfl⟩)
  have h6 : ∀ v ∈ ΛS, ∀ b ∈ D.host.AA⁻¹, b • (ρ *ᵥ v) ∈ ΛT := by
    intro v hv b hb
    refine (hT.2 _).2 fun t ht => ?_
    rw [form_smul]
    have := FractionalIdeal.mul_mem_mul hb (h5 v hv t ht)
    rw [inv_mul_cancel₀ hAA, FractionalIdeal.mem_one_iff] at this
    exact this
  have h7 : ∀ v ∈ ΛS, ∀ v' ∈ ΛS, ∀ e ∈ D.host.AA * D.host.AA⁻¹, genMap S T e v' (ρ *ᵥ v) ∈
      latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) := by
    intro v hv v' hv' e he
    refine FractionalIdeal.mul_induction_on (C := fun e => genMap S T e v' (ρ *ᵥ v) ∈
      latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))) he
      (fun a ha c hc => ?_) (fun u w hu hw => ?_)
    · refine AddSubgroup.subset_closure ⟨a, ha, v', hv', c • (ρ *ᵥ v), h6 v hv c hc, ?_⟩
      ext i j
      simp only [genMap, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
    · have e : genMap S T (u + w) v' (ρ *ᵥ v) = genMap S T u v' (ρ *ᵥ v) + genMap S T w v' (ρ *ᵥ v) := by
        ext i j
        simp only [genMap, Matrix.of_apply, Matrix.add_apply, add_mul]
      show genMap S T (u + w) v' (ρ *ᵥ v) ∈ _
      rw [e]
      exact add_mem hu hw
  have e : ρ = ∑ i, genMap S T 1 (s' i) (ρ *ᵥ s i) := by
    refine Matrix.ext fun a j => ?_
    have h8 : ρ a j = ∑ b, ρ a b * ∑ i, s i b * ∑ k, star (s' i k) * S.gram k j := by
      simp only [hdual, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [h8, Matrix.sum_apply]
    simp only [genMap, Matrix.of_apply, one_mul, Matrix.mulVec, dotProduct]
    simp only [Finset.mul_sum (s := Finset.univ (α := Fin n))]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [← mul_assoc]
    exact (Finset.sum_mul _ _ _).symm
  rw [e]
  exact sum_mem fun i _ => h7 _ (hss i).1 _ (hss i).2 1
    (by rw [mul_inv_cancel₀ hAA]; exact FractionalIdeal.one_mem_one _)

end GlobalTheory.LatVac
