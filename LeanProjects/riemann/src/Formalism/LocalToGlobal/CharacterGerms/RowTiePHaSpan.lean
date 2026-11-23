import Formalism.LocalToGlobal.CharacterGerms.RowTiePHaDefs
import Formalism.LocalToGlobal.CharacterGerms.RowTiePDescSpanSt

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.HaP

open MvPolynomial Formalism.L2.Pj

section Sub

variable {Ty : Type} (r : Ty → ℕ) (n : ℕ) (k : Type) [Field k] (cc : Ty → Ty) (isX : Ty → Prop) (a : Ty → ℕ → ℕ)

theorem hha_zero : (0 : MvPolynomial (Letter Ty r n) k) ∈ HHa r n k cc isX a := by
  refine ⟨Submodule.zero_mem _, fun σ i i' _ t => map_zero _, fun m hm => by simp at hm⟩

theorem hha_add {P Q : MvPolynomial (Letter Ty r n) k} (hP : P ∈ HHa r n k cc isX a) (hQ : Q ∈ HHa r n k cc isX a) :
    P + Q ∈ HHa r n k cc isX a := by
  obtain ⟨hP1, hP2, hP3⟩ := hP
  obtain ⟨hQ1, hQ2, hQ3⟩ := hQ
  refine ⟨Submodule.add_mem _ hP1 hQ1, fun σ i i' hii t => ?_, fun m hm => ?_⟩
  · rw [map_add, hP2 σ i i' hii t, hQ2 σ i i' hii t]
  · rcases Finset.mem_union.mp (support_add hm) with h | h
    · exact hP3 m h
    · exact hQ3 m h

theorem hha_smul (c : k) {P : MvPolynomial (Letter Ty r n) k} (hP : P ∈ HHa r n k cc isX a) :
    c • P ∈ HHa r n k cc isX a := by
  obtain ⟨hP1, hP2, hP3⟩ := hP
  refine ⟨Submodule.smul_mem _ c hP1, fun σ i i' hii t => ?_, fun m hm => hP3 m (support_smul hm)⟩
  rw [map_smul, hP2 σ i i' hii t]

end Sub

section Maps

variable {Ty : Type} (r : Ty → ℕ) (n : ℕ)

theorem lap_map {k k' : Type} [Field k] [Field k'] (φ : k →+* k') (τ τ' : Ty) (a0 : Fin (r τ)) (a1 : Fin (r τ'))
    (p : MvPolynomial (Letter Ty r n) k) :
    lap r n k' 1 τ τ' a0 a1 (map φ p) = map φ (lap r n k 1 τ τ' a0 a1 p) := by
  simp [lap, Matrix.one_apply, pderiv_map]

theorem rowShift_map {k k' : Type} [Field k] [Field k'] (φ : k →+* k') (σ0 : Ty) (i i' : Fin (r σ0)) (t : k)
    (p : MvPolynomial (Letter Ty r n) k) :
    rowShift r n k' σ0 i i' (φ t) (map φ p) = map φ (rowShift r n k σ0 i i' t p) := by
  simp only [rowShift, aeval_def, algebraMap_eq, map_eval₂]
  congr 1
  funext ℓ
  simp only [Function.comp_apply]
  split_ifs <;> simp

end Maps

section Comp

variable {K : Type} [Field K] [CharZero K] {σ : Type}

def comp (lam : K →ₗ[ℚ] ℚ) (P : MvPolynomial σ K) : MvPolynomial σ ℚ :=
  ∑ m ∈ P.support, monomial m (lam (P.coeff m))

theorem coeff_comp (lam : K →ₗ[ℚ] ℚ) (P : MvPolynomial σ K) (m : σ →₀ ℕ) :
    coeff m (comp lam P) = lam (coeff m P) := by
  by_cases h : coeff m P = 0 <;> simp [comp, coeff_sum, coeff_monomial, h]

theorem comp_zero (lam : K →ₗ[ℚ] ℚ) : comp lam (0 : MvPolynomial σ K) = 0 := by
  simp [comp]

theorem comp_sum (lam : K →ₗ[ℚ] ℚ) {α : Type} (s : Finset α) (f : α → MvPolynomial σ K) :
    comp lam (∑ i ∈ s, f i) = ∑ i ∈ s, comp lam (f i) := by
  ext m
  simp only [coeff_comp, coeff_sum, map_sum]

theorem comp_smul_map (lam : K →ₗ[ℚ] ℚ) (c : K) (p : MvPolynomial σ ℚ) :
    comp lam (c • map (algebraMap ℚ K) p) = lam c • p := by
  ext m
  simp only [coeff_comp, coeff_smul, coeff_map, smul_eq_mul]
  rw [mul_comm c, ← Algebra.smul_def, map_smul, smul_eq_mul]
  exact mul_comm _ _

theorem comp_comm (lam : K →ₗ[ℚ] ℚ) (Φ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K)
    (Ψ : MvPolynomial σ ℚ →ₗ[ℚ] MvPolynomial σ ℚ)
    (h : ∀ m, Φ (monomial m 1) = map (algebraMap ℚ K) (Ψ (monomial m 1))) (P : MvPolynomial σ K) :
    comp lam (Φ P) = Ψ (comp lam P) := by
  have hP : P = ∑ m ∈ P.support, coeff m P • monomial m (1 : K) := by
    conv_lhs => rw [P.as_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_monomial, smul_eq_mul, mul_one]
  have hc : comp lam P = ∑ m ∈ P.support, lam (coeff m P) • monomial m (1 : ℚ) := by
    unfold comp
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hc, map_sum]
  conv_lhs => rw [hP]
  rw [map_sum, comp_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul Φ, h, comp_smul_map, map_smul Ψ]

variable {Ty : Type} (r : Ty → ℕ) (n : ℕ) {cc : Ty → Ty} {isX : Ty → Prop} {a : Ty → ℕ → ℕ}

theorem comp_mem (lam : K →ₗ[ℚ] ℚ) {P : MvPolynomial (Letter Ty r n) K} (hP : P ∈ HHa r n K cc isX a) :
    comp lam P ∈ HHa r n ℚ cc isX a := by
  obtain ⟨h1, h2, h3⟩ := hP
  have hmono : ∀ m : Letter Ty r n →₀ ℕ, monomial m (1 : K) = map (algebraMap ℚ K) (monomial m (1 : ℚ)) := by
    intro m
    rw [map_monomial, (algebraMap ℚ K).map_one]
  refine ⟨?_, fun σ i i' hii t => ?_, fun m hm => ?_⟩
  · simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker] at h1 ⊢
    intro τ hτ a0 a1
    have hc := comp_comm lam (lap r n K 1 τ (cc τ) a0 a1) (lap r n ℚ 1 τ (cc τ) a0 a1)
      (fun m => by rw [hmono, lap_map]) P
    rw [h1 τ hτ a0 a1, comp_zero] at hc
    exact hc.symm
  · have hc := comp_comm lam (rowShift r n K σ i i' (algebraMap ℚ K t)).toLinearMap
      (rowShift r n ℚ σ i i' t).toLinearMap (fun m => by
        simp only [AlgHom.toLinearMap_apply]
        rw [hmono, rowShift_map]) P
    simp only [AlgHom.toLinearMap_apply] at hc
    rw [h2 σ i i' hii] at hc
    exact hc.symm
  · rw [mem_support_iff, coeff_comp] at hm
    exact h3 m (mem_support_iff.mpr fun h0 => hm (by rw [h0, map_zero]))

end Comp

section Up

variable {Ty : Type} {r : Ty → ℕ} {n : ℕ} {cc : Ty → Ty} {isX : Ty → Prop} {a : Ty → ℕ → ℕ}

theorem map_mem (hR : RowInvUpSt) (K : Type) [Field K] [CharZero K] (p : MvPolynomial (Letter Ty r n) ℚ)
    (hp : p ∈ HHa r n ℚ cc isX a) : map (algebraMap ℚ K) p ∈ HHa r n K cc isX a := by
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨?_, hR Ty r n K _ fun σ i i' hii q => ?_, fun m hm => h3 m (support_map_subset _ _ hm)⟩
  · simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker] at h1 ⊢
    intro τ hτ a0 a1
    rw [lap_map, h1 τ hτ a0 a1, map_zero]
  · have e : ((q : ℚ) : K) = algebraMap ℚ K q := (eq_ratCast (algebraMap ℚ K) q).symm
    rw [e, rowShift_map, h2 σ i i' hii q]

theorem map_int_mem (hR : RowInvUpSt) (K : Type) [Field K] [CharZero K] (z : MvPolynomial (Letter Ty r n) ℤ)
    (hz : map (Int.castRingHom ℚ) z ∈ HHa r n ℚ cc isX a) : map (Int.castRingHom K) z ∈ HHa r n K cc isX a := by
  have e : map (Int.castRingHom K) z = map (algebraMap ℚ K) (map (Int.castRingHom ℚ) z) := by
    rw [map_map, RingHom.ext_int (Int.castRingHom K) ((algebraMap ℚ K).comp (Int.castRingHom ℚ))]
  rw [e]
  exact map_mem hR K _ hz

end Up

section Poly

variable {L : Type}

def poly {R : Type} [CommRing R] (Bd : Finset (L →₀ ℕ)) (v : Bd → R) : MvPolynomial L R :=
  ∑ b : Bd, monomial b.1 (v b)

theorem coeff_poly {R : Type} [CommRing R] (Bd : Finset (L →₀ ℕ)) (v : Bd → R) (m : L →₀ ℕ) :
    coeff m (poly Bd v) = if h : m ∈ Bd then v ⟨m, h⟩ else 0 := by
  unfold poly
  rw [coeff_sum]
  simp only [coeff_monomial]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨m, h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro hbm
      exact hb (Subtype.ext hbm)
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · apply Finset.sum_eq_zero
    intro b _
    rw [if_neg]
    intro hbm
    exact h (hbm ▸ b.2)

theorem coeff_map_poly {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (Bd : Finset (L →₀ ℕ)) (v : Bd → R)
    (m : L →₀ ℕ) : coeff m (map φ (poly Bd v)) = if h : m ∈ Bd then φ (v ⟨m, h⟩) else 0 := by
  rw [coeff_map, coeff_poly, apply_dite φ, map_zero]

end Poly

section Main

variable {Ty : Type} (r : Ty → ℕ) (n : ℕ) (cc : Ty → Ty) (isX : Ty → Prop) (a : Ty → ℕ → ℕ)

def Wsub (Bd : Finset (Letter Ty r n →₀ ℕ)) : Submodule ℤ (Bd → ℤ) where
  carrier := {z | map (Int.castRingHom ℚ) (poly Bd z) ∈ HHa r n ℚ cc isX a}
  add_mem' := by
    intro x y hx hy
    have e : map (Int.castRingHom ℚ) (poly Bd (x + y)) =
        map (Int.castRingHom ℚ) (poly Bd x) + map (Int.castRingHom ℚ) (poly Bd y) := by
      ext m
      rw [coeff_add, coeff_map_poly, coeff_map_poly, coeff_map_poly]
      split_ifs <;> simp
    show map (Int.castRingHom ℚ) (poly Bd (x + y)) ∈ HHa r n ℚ cc isX a
    rw [e]
    exact hha_add r n ℚ cc isX a hx hy
  zero_mem' := by
    have e : map (Int.castRingHom ℚ) (poly Bd (0 : Bd → ℤ)) = 0 := by
      ext m
      rw [coeff_zero, coeff_map_poly]
      split_ifs <;> simp
    show map (Int.castRingHom ℚ) (poly Bd (0 : Bd → ℤ)) ∈ HHa r n ℚ cc isX a
    rw [e]
    exact hha_zero r n ℚ cc isX a
  smul_mem' := by
    intro c x hx
    have e : map (Int.castRingHom ℚ) (poly Bd (c • x)) = (c : ℚ) • map (Int.castRingHom ℚ) (poly Bd x) := by
      ext m
      rw [coeff_smul, coeff_map_poly, coeff_map_poly]
      split_ifs <;> simp
    show map (Int.castRingHom ℚ) (poly Bd (c • x)) ∈ HHa r n ℚ cc isX a
    rw [e]
    exact hha_smul r n ℚ cc isX a _ hx

theorem wsub_sat (Bd : Finset (Letter Ty r n →₀ ℕ)) (z : ℤ) (x : Bd → ℤ) (hz : z ≠ 0)
    (hx : z • x ∈ Wsub r n cc isX a Bd) : x ∈ Wsub r n cc isX a Bd := by
  have e : map (Int.castRingHom ℚ) (poly Bd (z • x)) = (z : ℚ) • map (Int.castRingHom ℚ) (poly Bd x) := by
    ext m
    rw [coeff_smul, coeff_map_poly, coeff_map_poly]
    split_ifs <;> simp
  have hx' : map (Int.castRingHom ℚ) (poly Bd (z • x)) ∈ HHa r n ℚ cc isX a := hx
  rw [e] at hx'
  have hz' : (z : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hz
  have h2 := hha_smul r n ℚ cc isX a ((z : ℚ)⁻¹) hx'
  rw [smul_smul, inv_mul_cancel₀ hz', one_smul] at h2
  show map (Int.castRingHom ℚ) (poly Bd x) ∈ HHa r n ℚ cc isX a
  exact h2

end Main

section Assembly

theorem exists_clear (s : Type) [Fintype s] (u : s → ℚ) :
    ∃ N : ℕ, N ≠ 0 ∧ ∃ z : s → ℤ, ∀ b, (z b : ℚ) = N * u b := by
  refine ⟨∏ b, (u b).den, Finset.prod_ne_zero_iff.mpr fun b _ => (u b).den_nz,
    fun b => (∏ b' ∈ Finset.univ.erase b, ((u b').den : ℤ)) * (u b).num, fun b => ?_⟩
  have hq : u b * ((u b).den : ℚ) = ((u b).num : ℚ) := Rat.mul_den_eq_num (u b)
  rw [← Finset.mul_prod_erase Finset.univ (fun b' => (u b').den) (Finset.mem_univ b)]
  push_cast
  rw [← hq]
  ring

private theorem fix_sum_lemma {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : (ι → ℤ) →ₗ[ℤ] (ι → ℤ)) (z : ι → ℤ)
    (hz : ρ z = z) (j : ι) : z j = ∑ b, z b * ρ (Pi.single b 1) j := by
  have hz' : z = ∑ b, z b • (Pi.single b (1 : ℤ) : ι → ℤ) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  calc z j = ρ z j := (congrFun hz j).symm
    _ = ρ (∑ b, z b • (Pi.single b (1 : ℤ) : ι → ℤ)) j := by rw [← hz']
    _ = ∑ b, z b * ρ (Pi.single b 1) j := by
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem haSpanSt_of (hS : SatRetrSt) (hR : RowInvUpSt) : HaSpanSt := by
  unfold HaSpanSt
  intro Ty _ r n cc isX a K _ _ O P hP
  obtain ⟨hPH, hPO⟩ := hP
  obtain ⟨Bd, hBd⟩ : ∃ Bd, Bd = P.support := ⟨_, rfl⟩
  obtain ⟨ρ, hρW, hρfix⟩ := hS Bd (Wsub r n cc isX a Bd) (fun z x hz hx => wsub_sat r n cc isX a Bd z x hz hx)
  have key : ∀ j : Bd, coeff j.1 P = ∑ b : Bd, coeff b.1 P * ((ρ (Pi.single b 1) j : ℤ) : K) := by
    intro j
    rw [← sub_eq_zero]
    refine (Module.forall_dual_apply_eq_zero_iff ℚ _).mp fun lam => ?_
    obtain ⟨N, hN, z, hz⟩ := exists_clear Bd (fun b => lam (coeff b.1 P))
    have hzW : z ∈ Wsub r n cc isX a Bd := by
      have e : map (Int.castRingHom ℚ) (poly Bd z) = (N : ℚ) • comp lam P := by
        ext m
        rw [coeff_map_poly, coeff_smul, coeff_comp, smul_eq_mul]
        split_ifs with h
        · simpa using hz ⟨m, h⟩
        · have h0 : coeff m P = 0 := by
            by_contra hc
            exact h (by rw [hBd]; exact mem_support_iff.mpr hc)
          rw [h0, map_zero, mul_zero]
      show map (Int.castRingHom ℚ) (poly Bd z) ∈ HHa r n ℚ cc isX a
      rw [e]
      exact hha_smul r n ℚ cc isX a _ (comp_mem r n lam hPH)
    have hfix := fix_sum_lemma ρ z (hρfix z hzW) j
    have hN' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    have hq : (z j : ℚ) = ∑ b, (z b : ℚ) * ((ρ (Pi.single b 1) j : ℤ) : ℚ) := by exact_mod_cast hfix
    simp only [hz] at hq
    rw [map_sub, map_sum, sub_eq_zero]
    have hl : lam (coeff j.1 P) = ∑ b : Bd, lam (coeff b.1 P) * ((ρ (Pi.single b 1) j : ℤ) : ℚ) := by
      apply mul_left_cancel₀ hN'
      rw [hq, Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [hl]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hs : coeff b.1 P * ((ρ (Pi.single b 1) j : ℤ) : K) = (ρ (Pi.single b 1) j) • coeff b.1 P := by
      rw [zsmul_eq_mul, mul_comm]
    rw [hs, map_zsmul, zsmul_eq_mul, mul_comm]
  have hmain : P = ∑ b : Bd, coeff b.1 P • map (Int.castRingHom K) (poly Bd (ρ (Pi.single b 1))) := by
    ext m
    rw [coeff_sum]
    simp only [coeff_smul, coeff_map_poly, smul_eq_mul]
    by_cases h : m ∈ Bd
    · simp only [dif_pos h, eq_intCast]
      exact key ⟨m, h⟩
    · simp only [dif_neg h, mul_zero, Finset.sum_const_zero]
      by_contra hc
      exact h (by rw [hBd]; exact mem_support_iff.mpr hc)
  have hsum : ∑ i : Fin (Fintype.card Bd), coeff ((Fintype.equivFin Bd).symm i).1 P •
      map (Int.castRingHom K) (poly Bd (ρ (Pi.single ((Fintype.equivFin Bd).symm i) 1))) =
      ∑ b : Bd, coeff b.1 P • map (Int.castRingHom K) (poly Bd (ρ (Pi.single b 1))) :=
    Equiv.sum_comp (Fintype.equivFin Bd).symm
      (fun b : Bd => coeff b.1 P • map (Int.castRingHom K) (poly Bd (ρ (Pi.single b 1))))
  refine ⟨Fintype.card Bd, fun i => coeff ((Fintype.equivFin Bd).symm i).1 P,
    fun i => poly Bd (ρ (Pi.single ((Fintype.equivFin Bd).symm i) 1)), fun i => hPO _,
    fun i K' _ _ => map_int_mem hR K' _ (hρW _), ?_⟩
  exact hmain.trans hsum.symm

end Assembly

end Formalism.L2.FormalSeriesBounds.HaP
