import Mathlib
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime

noncomputable section
open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators ComplexOrder

namespace GlobalTheory.MomOne.FrameChange

variable {g : ℕ}

theorem beta_sum_left {κ : Type} [Fintype κ] (d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (c : κ → ℂ)
    (v : κ → Fin g → ℂ) (w : Fin g → ℂ) :
    beta d Hm (∑ k, c k • v k) w = ∑ k, c k * beta d Hm (v k) w := by
  simp only [beta, hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun _ => Finset.univ) (h := by simp)]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin g))) (t := (Finset.univ : Finset κ))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem beta_conj (d : ℕ) {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) (z w : Fin g → ℂ) :
    conj (beta d Hm z w) = beta d Hm w z := by
  simp only [beta, hf, map_mul, map_sum, Complex.conj_ofReal, Complex.conj_conj]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : conj (Hm j i) = Hm i j := h.apply i j
  rw [this]; ring

theorem eq_sum_frame (d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ)
    (hx : ∀ i j, beta d Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) (ha : ∀ i, (a i : ℂ) ≠ 0)
    (v : Fin g → ℂ) : v = ∑ i, (beta d Hm v (x i) / (a i : ℂ)) • x i := by
  have key : ∀ (z : Fin g → ℂ) k, beta d Hm (∑ i, z i • x i) (x k) = z k * a k := by
    intro z k
    rw [beta_sum_left]
    simp [hx]
  have hli : LinearIndependent ℂ x := by
    refine Fintype.linearIndependent_iff.2 fun z hz k => ?_
    have h := key z k
    rw [hz] at h
    have h0 : beta d Hm 0 (x k) = 0 := by simp [beta, hf]
    rw [h0] at h
    exact (mul_eq_zero.1 h.symm).resolve_right (ha k)
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by simp)
  have hv : v ∈ Submodule.span ℂ (Set.range x) := by rw [hsp]; trivial
  obtain ⟨z, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hv
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [key, mul_div_cancel_right₀ _ (ha i)]

def zcHom (q : ℕ) [Fact q.Prime] : ℤ_[q] →+* ℂ_[q] := (algebraMap ℚ_[q] ℂ_[q]).comp PadicInt.Coe.ringHom

theorem zcHom_injective (q : ℕ) [Fact q.Prime] : Function.Injective (zcHom q) :=
  (algebraMap ℚ_[q] ℂ_[q]).injective.comp Subtype.val_injective

end GlobalTheory.MomOne.FrameChange

namespace GlobalTheory.MomOne
open FrameChange

theorem frameChange : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (g : ℕ) (S : Setup g) (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ) (r : ℕ) (b : Fin r → Fin g → ℂ), S.Ok → Split S.d q → (∀ i, x i ∈ S.La) → (∀ i j, beta S.d S.Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) → (∀ i, 0 < a i ∧ Nat.Coprime (a i) q) → S.NNBasis q b → ∃ T : (Fin r → ℤ_[q]) ≃ₜ (Fin g → ℤ_[q]), ∀ A i, GlobalTheory.MomOne.zc (T A i) = ∑ j, GlobalTheory.MomOne.zc (A j) * ι (beta S.d S.Hm (x i) (b j)) := by
  intro q _ ι g S x a r b hS hsp hxL hx ha hb
  obtain ⟨hd, hd7, hpos, -, -, -, hβ, -⟩ := hS
  obtain ⟨hbL, hgen, hind⟩ := hb
  have hq : q.Prime := Fact.out
  have hH : S.Hm.IsHermitian := hpos.isHermitian
  obtain ⟨⟨h1, -, hR⟩, hZ, -⟩ := okArith S.d q ι hd hd7 hsp
  let O : Subring ℂ :=
    { carrier := {z | InOK S.d z}
      one_mem' := h1
      zero_mem' := ⟨0, 0, by simp⟩
      mul_mem' := fun {u v} hu hv => (hR u v hu hv).2.1
      add_mem' := fun {u v} hu hv => (hR u v hu hv).1
      neg_mem' := fun {u} hu => (hR u u hu hu).2.2.1 }
  have hconj : ∀ u, InOK S.d u → InOK S.d (conj u) := fun u hu => (hR u u hu hu).2.2.2
  choose s hs c hc hsc using fun i => hgen (x i) (hxL i)
  have hs0 : ∀ i, (s i : ℂ) ≠ 0 := fun i h => by
    have h' : s i = 0 := by exact_mod_cast h
    have := hs i
    rw [h', Nat.coprime_zero_left] at this
    exact hq.one_lt.ne' this
  have ha0 : ∀ i, (a i : ℂ) ≠ 0 := fun i => by exact_mod_cast (ha i).1.ne'

  have hMN : ∀ i k, ∑ j, beta S.d S.Hm (x i) (b j) * (conj (c k j) / (s k * a k)) = if i = k then 1 else 0 := by
    intro i k
    have e := beta_sum_left S.d S.Hm (c k) b (x i)
    have e2 := beta_sum_left S.d S.Hm (fun _ : Unit => (s k : ℂ)) (fun _ => x k) (x i)
    simp only [Finset.univ_unique, Finset.sum_singleton] at e2
    rw [← hsc k, e2] at e
    have e3 := congrArg conj e
    simp only [map_sum, map_mul, beta_conj S.d hH, map_natCast] at e3
    simp_rw [← mul_div_assoc, mul_comm (beta _ _ _ _)]
    rw [← Finset.sum_div, ← e3, hx]
    split_ifs with h
    · subst h; exact div_self (mul_ne_zero (hs0 i) (ha0 i))
    · simp
  have hNM : ∀ j l, ∑ i, (conj (c i j) / (s i * a i)) * beta S.d S.Hm (x i) (b l) = if j = l then 1 else 0 := by
    intro j l
    set P : ℂ := ∏ i, ((s i : ℂ) * a i) with hP
    have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero (hs0 i) (ha0 i)
    let e : Fin r → ℂ := fun j => ∑ i, c i j / (s i * a i) * beta S.d S.Hm (b l) (x i)
    have hmem : ∀ j, P * (e j - if j = l then 1 else 0) ∈ O := by
      intro j
      have hPO : P ∈ O := O.prod_mem fun i _ => O.mul_mem (natCast_mem O _) (natCast_mem O _)
      rw [mul_sub, Finset.mul_sum]
      refine O.sub_mem (O.sum_mem fun i _ => ?_) (O.mul_mem hPO (by split_ifs; exacts [O.one_mem, O.zero_mem]))
      have : P * (c i j / (s i * a i) * beta S.d S.Hm (b l) (x i)) =
          (∏ k ∈ Finset.univ.erase i, ((s k : ℂ) * a k)) * c i j * beta S.d S.Hm (b l) (x i) := by
        rw [hP, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
        have := hs0 i
        have := ha0 i
        field_simp
      rw [this]
      exact O.mul_mem (O.mul_mem (O.prod_mem fun i _ => O.mul_mem (natCast_mem O _) (natCast_mem O _)) (hc i j))
        (hβ _ (hbL l) _ (hxL i))
    have hsum : ∑ j, e j • b j = b l := by
      conv_rhs => rw [eq_sum_frame S.d S.Hm x a hx ha0 (b l)]
      simp only [e, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hxi : x i = (s i : ℂ)⁻¹ • ∑ j, c i j • b j := by
        rw [← hsc i, smul_smul, inv_mul_cancel₀ (hs0 i), one_smul]
      generalize beta S.d S.Hm (b l) (x i) = t
      rw [hxi, smul_smul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul]
      congr 1
      have := hs0 i
      have := ha0 i
      field_simp
    have h0 := hind _ hmem (by
      simp only [mul_smul, sub_smul, ← Finset.smul_sum, Finset.sum_sub_distrib, hsum]
      simp [ite_smul]) j
    have h2 : e j = if j = l then 1 else 0 := sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_left hP0)
    have h3 := congrArg conj h2
    simp only [e, map_sum, map_mul, map_div₀, beta_conj S.d hH, map_natCast] at h3
    rw [h3]
    split_ifs <;> simp

  choose m hm using fun i j => (hZ _ (hβ _ (hxL i) _ (hbL j))).1
  choose n hn using fun i j => (hZ _ (hconj _ (hc i j))).1
  have hu : ∀ i, ∃ u : ℤ_[q], ι ((s i * a i : ℂ)⁻¹) = zcHom q u := by
    intro i
    have hun : IsUnit ((s i * a i : ℕ) : ℤ_[q]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      exact (Nat.Coprime.mul_left (hs i) (ha i).2).symm
    obtain ⟨u, hu⟩ := hun.exists_left_inv
    refine ⟨u, ?_⟩
    have := congrArg (zcHom q) hu
    rw [map_mul, map_natCast, map_one] at this
    rw [map_inv₀, eq_inv_of_mul_eq_one_left this]
    simp
  choose u hu using hu
  let M : Matrix (Fin g) (Fin r) ℤ_[q] := Matrix.of m
  let N : Matrix (Fin r) (Fin g) ℤ_[q] := Matrix.of fun j i => n i j * u i
  have hM : ∀ i j, zcHom q (M i j) = ι (beta S.d S.Hm (x i) (b j)) := fun i j => (hm i j).symm
  have hN : ∀ j i, zcHom q (N j i) = ι (conj (c i j) / (s i * a i)) := fun j i => by
    rw [div_eq_mul_inv, map_mul, hu, hn]
    exact map_mul (zcHom q) _ _
  have e1 : M * N = 1 := by
    ext i k : 2
    apply zcHom_injective q
    rw [Matrix.mul_apply, map_sum]
    simp_rw [map_mul, hM, hN, ← map_mul]
    rw [← map_sum, hMN, Matrix.one_apply]
    split_ifs <;> simp
  have e2 : N * M = 1 := by
    ext i k : 2
    apply zcHom_injective q
    rw [Matrix.mul_apply, map_sum]
    simp_rw [map_mul, hM, hN, ← map_mul]
    rw [← map_sum, hNM, Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨{ toFun := M.mulVec
            invFun := N.mulVec
            left_inv := fun A => by rw [Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]
            right_inv := fun A => by rw [Matrix.mulVec_mulVec, e1, Matrix.one_mulVec]
            continuous_toFun := continuous_const.matrix_mulVec continuous_id
            continuous_invFun := continuous_const.matrix_mulVec continuous_id }, fun A i => ?_⟩
  show zcHom q (∑ j, M i j * A j) = ∑ j, zcHom q (A j) * _
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_mul, hM, mul_comm]

end GlobalTheory.MomOne
