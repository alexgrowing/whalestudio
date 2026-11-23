import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeOfFiniteProjective
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeFiniteProjectiveBaseChange

open GlobalTheory.CompanionTheory.Ar.Num

namespace PositivityTheory.Xgn.A_summand_of_quot

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
  {E : Type} [AddCommGroup E] [Module Ω E]

def toSub (L : AddSubgroup E) (h : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) : Submodule R E where
  carrier := L
  add_mem' := fun ha hb => L.add_mem ha hb
  zero_mem' := L.zero_mem
  smul_mem' := fun a e he => h a a.2 e he

theorem exists_dual {r : ℕ} {L : AddSubgroup E} (h : LocFree R r L) :
    Module.finrank Ω E = r ∧ ∃ (k : ℕ) (φ : Fin k × Fin r → Module.Dual Ω E) (v : Fin k × Fin r → E),
      (∀ i, v i ∈ L) ∧ (∀ i, ∀ e ∈ L, φ i e ∈ R) ∧ ∀ e, ∑ i, φ i e • v i = e := by
  have h' : LocFree R r (toSub R L h.1).toAddSubgroup := h
  refine ⟨(LocFreeProj.main R r (toSub R L h.1) h').2.2.1, ?_⟩
  obtain ⟨k, f, c, B, hsum, hgen, hcoord⟩ := LocFreeProj.exists_charts h'
  choose n0 hn0 using hgen
  have hs : ∀ j q, ((f j : Ω) ^ (Finset.univ.sup fun i : Fin k × Fin r => n0 i.1 i.2)) • B j q ∈ toSub R L h.1 :=
    fun j q => LocFreeProj.pow_smul_mem (f j)
      (Finset.le_sup (f := fun i : Fin k × Fin r => n0 i.1 i.2) (Finset.mem_univ (j, q))) (hn0 j q)
  generalize hN0 : (Finset.univ.sup fun i : Fin k × Fin r => n0 i.1 i.2) = N0 at hs
  have hP0 : ∀ (l : Fin k) (p : Fin r) (jq : Fin k × Fin r),
      ∃ n, (f l : Ω) ^ n * (B l).repr ((f jq.1 : Ω) ^ N0 • B jq.1 jq.2) p ∈ R :=
    fun l p jq => hcoord l p _ (hs jq.1 jq.2)
  choose nP hnP using hP0
  have hbound : ∀ e ∈ toSub R L h.1, ∀ l p,
      (f l : Ω) ^ (Finset.univ.sup fun i : Fin k × Fin r × (Fin k × Fin r) => nP i.1 i.2.1 i.2.2) * (B l).repr e p ∈ R := by
    intro e he l p
    choose m hm using fun (jq : Fin k × Fin r) => hcoord jq.1 jq.2 e he
    obtain ⟨d, hd⟩ := LocFreeProj.exists_pow_cover f c hsum (Finset.univ.sup m + N0)
    have hexp := LocFreeProj.expand f d B (Finset.univ.sup m) N0 hd e
    have key : (B l).coord p e = ∑ i : Fin k × Fin r,
        ((d i.1 : Ω) * ((f i.1 : Ω) ^ (Finset.univ.sup m) * (B i.1).repr e i.2)) *
          (B l).coord p ((f i.1 : Ω) ^ N0 • B i.1 i.2) := by
      conv_lhs => rw [← hexp]
      simp only [map_sum, map_smul, smul_eq_mul]
    rw [← Module.Basis.coord_apply, key, Finset.mul_sum]
    refine R.sum_mem fun i _ => ?_
    rw [mul_left_comm]
    refine R.mul_mem (R.mul_mem (d i.1).2
      (LocFreeProj.pow_mul_mem (f i.1) (Finset.le_sup (Finset.mem_univ i)) (hm i))) ?_
    rw [Module.Basis.coord_apply]
    exact LocFreeProj.pow_mul_mem (f l)
      (Finset.le_sup (f := fun i : Fin k × Fin r × (Fin k × Fin r) => nP i.1 i.2.1 i.2.2)
        (Finset.mem_univ (l, p, i))) (hnP l p i)
  generalize (Finset.univ.sup fun i : Fin k × Fin r × (Fin k × Fin r) => nP i.1 i.2.1 i.2.2) = P at hbound
  obtain ⟨d', hd'⟩ := LocFreeProj.exists_pow_cover f c hsum (P + N0)
  refine ⟨k, fun i => ((d' i.1 : Ω) * (f i.1 : Ω) ^ P) • (B i.1).coord i.2,
    fun i => (f i.1 : Ω) ^ N0 • B i.1 i.2, fun i => hs i.1 i.2, ?_, ?_⟩
  · intro i e he
    simp only [LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul]
    rw [mul_assoc]
    exact R.mul_mem (d' i.1).2 (hbound e he i.1 i.2)
  · intro e
    have hx := LocFreeProj.expand f d' B P N0 hd' e
    convert hx using 2 with i
    simp only [LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul, mul_assoc]

theorem locFree_of_dual {ι : Type} [Fintype ι] {r : ℕ} {L : AddSubgroup E}
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) (hr : Module.finrank Ω E = r)
    (φ : ι → Module.Dual Ω E) (v : ι → E) (hvL : ∀ i, v i ∈ L) (hφ : ∀ i, ∀ e ∈ L, φ i e ∈ R)
    (hv : ∀ e, ∑ i, φ i e • v i = e) : LocFree R r L := by
  have h1 := LocFreeProj.finite_projective (L := toSub R L hL) φ (fun i => ⟨v i, hvL i⟩) hφ hv
  have h2 := LocFreeProj.isBaseChange (L := toSub R L hL) φ (fun i => ⟨v i, hvL i⟩) hφ hv
  exact LocFreeProj.locFree_of_projective R r (toSub R L hL) h1.1 h1.2 hr h2

end PositivityTheory.Xgn.A_summand_of_quot

open PositivityTheory.Xgn.A_summand_of_quot in
theorem PositivityTheory.Xgn.summand_iff_locFree_quot : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {V : Type} [AddCommGroup V] [Module Ω V] (U : Submodule Ω V) (N m : ℕ) (L : AddSubgroup V), LocFree R N L → (LocFree R m (L.map U.mkQ.toAddMonoidHom) → Summand L U) ∧ (Summand L U → LocFree R (Module.finrank Ω U) (L.comap U.subtype.toAddMonoidHom) ∧ LocFree R (N - Module.finrank Ω U) (L.map U.mkQ.toAddMonoidHom)) := by
  intro o Ω _ _ _ R V _ _ U N m L hN
  have hst : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L := hN.1
  constructor
  · intro hm
    obtain ⟨-, k, φ, v, hv, hφ, hsum⟩ := PositivityTheory.Xgn.A_summand_of_quot.exists_dual R hm
    have hlift : ∀ i, ∃ e ∈ L, U.mkQ e = v i := fun i => by
      obtain ⟨e, he, hev⟩ := AddSubgroup.mem_map.1 (hv i)
      exact ⟨e, he, hev⟩
    choose w hw hwv using hlift
    have hkey : ∀ x : V ⧸ U, U.mkQ (∑ i, φ i x • w i) = x := by
      intro x
      rw [map_sum]
      simp only [map_smul, hwv]
      exact hsum x
    refine ⟨LinearMap.id - (∑ i, LinearMap.smulRight (φ i) (w i)) ∘ₗ U.mkQ, ?_, ?_, ?_⟩
    · intro x
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, LinearMap.sum_apply,
        LinearMap.smulRight_apply, map_sub, hkey, sub_self]
    · intro u hu
      have h0 : U.mkQ u = 0 := (Submodule.Quotient.mk_eq_zero U).2 hu
      simp [h0]
    · intro e he
      have hme : U.mkQ e ∈ AddSubgroup.map U.mkQ.toAddMonoidHom L := AddSubgroup.mem_map_of_mem _ he
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, LinearMap.sum_apply,
        LinearMap.smulRight_apply]
      exact sub_mem he (AddSubgroup.sum_mem _ fun i _ => hst _ (hφ i _ hme) _ (hw i))
  · rintro ⟨ρ, hρU, hρid, hρL⟩
    obtain ⟨hrank, k, φ, v, hv, hφ, hsum⟩ := PositivityTheory.Xgn.A_summand_of_quot.exists_dual R hN
    have hfin : Module.Finite Ω V := by
      refine Module.Finite.of_surjective (∑ i, LinearMap.smulRight (LinearMap.proj i : (Fin k × Fin N → Ω) →ₗ[Ω] Ω) (v i)) ?_
      intro e
      refine ⟨fun i => φ i e, ?_⟩
      simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
      exact hsum e
    constructor
    · refine PositivityTheory.Xgn.A_summand_of_quot.locFree_of_dual R (fun a ha e he => hst a ha _ he) rfl
        (fun i => (φ i).comp U.subtype) (fun i => ⟨ρ (v i), hρU _⟩) (fun i => hρL _ (hv i))
        (fun i e he => hφ i _ he) ?_
      intro e
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, LinearMap.comp_apply, Submodule.subtype_apply]
      calc ∑ i, φ i e • ρ (v i) = ρ (∑ i, φ i e • v i) := by simp [map_sum, map_smul]
        _ = e := by rw [hsum]; exact hρid _ e.2
    · have hker : ∀ i, U ≤ LinearMap.ker ((φ i).comp (LinearMap.id - ρ)) := by
        intro i u hu
        simp [LinearMap.mem_ker, hρid u hu]
      refine PositivityTheory.Xgn.A_summand_of_quot.locFree_of_dual R ?_ ?_
        (fun i => U.liftQ ((φ i).comp (LinearMap.id - ρ)) (hker i)) (fun i => U.mkQ (v i))
        (fun i => AddSubgroup.mem_map_of_mem _ (hv i)) ?_ ?_
      · intro a ha x hx
        obtain ⟨e, he, rfl⟩ := AddSubgroup.mem_map.1 hx
        refine AddSubgroup.mem_map.2 ⟨a • e, hst a ha e he, ?_⟩
        simp
      · rw [← hrank, ← Submodule.finrank_quotient_add_finrank U]
        omega
      · intro i x hx
        obtain ⟨e, he, rfl⟩ := AddSubgroup.mem_map.1 hx
        simp only [LinearMap.toAddMonoidHom_coe, Submodule.mkQ_apply, Submodule.liftQ_apply,
          LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
        exact hφ i _ (sub_mem he (hρL e he))
      · intro x
        obtain ⟨e, rfl⟩ := U.mkQ_surjective x
        simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.comp_apply, LinearMap.sub_apply,
          LinearMap.id_apply]
        have h1 : ∑ i, φ i (e - ρ e) • (Submodule.Quotient.mk (v i) : V ⧸ U) =
            U.mkQ (∑ i, φ i (e - ρ e) • v i) := by
          simp [map_sum, map_smul]
        rw [h1, hsum, map_sub, Submodule.mkQ_apply, Submodule.mkQ_apply,
          (Submodule.Quotient.mk_eq_zero U).2 (hρU e), sub_zero]
