import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsPermOfCapPEq

noncomputable section

namespace GlobalTheory.CompanionTheory.RgCOBlock

open Finset Polynomial

theorem exists_linear_factors_indexed {ι : Type} [DecidableEq ι] (F : Finset ι) :
    ∀ P : ℂ[X], P.Monic → P.natDegree = F.card → ∃ r : ι → ℂ, P = ∏ a ∈ F, (X - C (r a)) := by
  induction F using Finset.induction_on with
  | empty =>
    intro P hm hd
    refine ⟨fun _ => 0, ?_⟩
    simpa using eq_one_of_monic_natDegree_zero hm (by simpa using hd)
  | insert a F ha ih =>
    intro P hm hd
    rw [Finset.card_insert_of_notMem ha] at hd
    have hdeg : P.degree ≠ 0 := by
      intro h
      have : P.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.mpr h.le
      omega
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root P hdeg
    obtain ⟨Q, hQ⟩ := dvd_iff_isRoot.mpr hz
    have hmQ : Q.Monic := by
      have h := hm
      rw [hQ] at h
      exact (monic_X_sub_C z).of_mul_monic_left h
    have hdQ : Q.natDegree = F.card := by
      have h := congrArg natDegree hQ
      rw [(monic_X_sub_C z).natDegree_mul hmQ, natDegree_X_sub_C] at h
      omega
    obtain ⟨r, hr⟩ := ih Q hmQ hdQ
    refine ⟨Function.update r a z, ?_⟩
    rw [Finset.prod_insert ha, Function.update_self, hQ, hr]
    congr 1
    refine Finset.prod_congr rfl fun b hb => ?_
    rw [Function.update_of_ne (fun h : b = a => ha (h ▸ hb))]

theorem exists_perm_of_monic_factors (n M : ℕ) (lev : Fin n → ℕ) (χ : Fin n → ℂ) (P : Fin M → ℂ[X]) (s : Fin M → ℂ)
    (hlev : ∀ a, lev a < M)
    (hP : ∀ i, (P i).Monic ∧ (P i).natDegree = (univ.filter fun a => lev a = (i : ℕ)).card)
    (hcap : ∀ Y : ℂ, ∏ i, (P i).eval (Y + s i) = Formalism.QuantumDeterminants.capP χ Y) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i : Fin M,
      ∑ a ∈ univ.filter (fun a => lev a = (i : ℕ)), χ (σ a) =
        (P i).nextCoeff + ((univ.filter fun a => lev a = (i : ℕ)).card : ℂ) * s i := by
  choose r hr using fun i => exists_linear_factors_indexed _ (P i) (hP i).1 (hP i).2
  let lv : Fin n → Fin M := fun a => ⟨lev a, hlev a⟩
  let g : Fin n → ℂ := fun a => s (lv a) - r (lv a) a
  have hfil : ∀ i : Fin M, (univ.filter fun a => lev a = (i : ℕ)) = univ.filter fun a => lv a = i := by
    intro i
    ext a
    simp [lv, Fin.ext_iff]
  have hg : ∀ i : Fin M, ∀ a ∈ univ.filter (fun a => lev a = (i : ℕ)), g a = s i - r i a := by
    intro i a ha
    have : lv a = i := by
      rw [hfil] at ha
      exact (Finset.mem_filter.mp ha).2
    simp only [g, this]
  have hpoly : ∀ Y, Formalism.QuantumDeterminants.capP g Y = Formalism.QuantumDeterminants.capP χ Y := by
    intro Y
    rw [← hcap Y]
    unfold Formalism.QuantumDeterminants.capP
    rw [← Finset.prod_fiberwise univ lv]
    refine Finset.prod_congr rfl fun i _ => ?_
    conv_rhs => rw [hr i, eval_prod]
    rw [hfil i]
    refine Finset.prod_congr rfl fun a ha => ?_
    rw [← hfil i] at ha
    rw [hg i a ha]
    simp only [eval_sub, eval_X, eval_C]
    ring
  obtain ⟨σ, hσ⟩ := GlobalTheory.CompanionTheory.CharOfLowK.exists_perm_of_capelliPolynomial_eq g χ hpoly
  refine ⟨σ, fun i => ?_⟩
  have h1 : ∑ a ∈ univ.filter (fun a => lev a = (i : ℕ)), χ (σ a) =
      ∑ a ∈ univ.filter (fun a => lev a = (i : ℕ)), (s i - r i a) :=
    Finset.sum_congr rfl fun a ha => by rw [← hσ a, hg i a ha]
  rw [h1, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  conv_rhs => rw [hr i, prod_X_sub_C_nextCoeff]
  ring

end GlobalTheory.CompanionTheory.RgCOBlock
