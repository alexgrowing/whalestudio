import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColengthRangeMapGeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentKernelEqCokerOmegaMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientKernelSupFrobeniusKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankQuotKernelIdealEqBeyondExponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenousPDivGroupFinrankOmegaDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFrobeniusKernelHopfLePowCotangent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRigidExtensionsEqHeightAndDimAddDual
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu.ColengthHtOne

open Module

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k]

theorem le_finrank_coker_omegaMap [CharP k p] (G H : PDivGroup p k) (q : G ⟶ H) (q' : H ⟶ G) (e : ℕ)
    (h1 : q ≫ q' = (p : ℤ_[p]) • 𝟙 G) (hF : frobKerIdeal p k (G.A 1) ≤ kerIdeal (q.app 1))
    (he : HasLogDeg q e) : e ≤ finrank k (G.omega ⧸ LinearMap.range (omegaMap G H q)) := by
  obtain ⟨N, hN⟩ := he
  have hlev : finrank k (G.A 1 ⧸ kerIdeal (q.app 1)) = p ^ e := by
    rw [← GlobalTheory.Dieu.finrank_quot_kerIdeal_eq p k G H 1 (max N 1) q q' (by rw [pow_one]; exact h1)
      (le_max_right _ _)]
    exact hN _ (le_max_left _ _)
  obtain ⟨C, _, _, _, _, π, hπ, hker, hnil, hFaug⟩ := GlobalTheory.T.exists_quotient_kernel_sup_frobeniusKernel p k G H q
  have hker' : RingHom.ker π = kerIdeal (q.app 1) := by rw [hker]; exact sup_eq_left.2 hF
  have hC : finrank k C = p ^ e := by
    rw [← hlev, ← hker']
    exact ((Ideal.quotientKerAlgEquivOfSurjective (f := (π : G.A 1 →ₐ[k] C)) hπ).toLinearEquiv.finrank_eq).symm
  have hfrobC : frobKerIdeal p k C = ⊥ := by
    rw [eq_bot_iff]
    refine Ideal.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    simp [hnil a ha]
  have hCq : finrank k C = finrank k (C ⧸ frobKerIdeal p k C) := by
    refine LinearEquiv.finrank_eq (LinearEquiv.ofBijective (Ideal.Quotient.mkₐ k (frobKerIdeal p k C)).toLinearMap
      ⟨fun a b h => ?_, Ideal.Quotient.mkₐ_surjective k _⟩)
    have h' := Ideal.Quotient.eq.1 h
    rwa [hfrobC, Ideal.mem_bot, sub_eq_zero] at h'
  have hle := GlobalTheory.PDiv.FrobKerOrder.finrank_le_pow_finrank_cot p k C
  rw [← hCq, hC] at hle
  have hcot := (GlobalTheory.T.cotangent_kernel_eq_coker_omegaMap p k G H q C π hπ).2.1 (by rw [hker]; exact sup_le_sup_left hFaug _) hker'.ge
  rw [hcot]
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).1 hle

theorem finrank_coker_lieMap {A B : PDivGroup p k} (f : A ⟶ B) [FiniteDimensional k A.omega]
    [FiniteDimensional k B.omega] (hd : finrank k A.omega = finrank k B.omega) :
    finrank k (B.Lie ⧸ LinearMap.range (lieMap A B f)) =
      finrank k (A.omega ⧸ LinearMap.range (omegaMap A B f)) := by
  have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.range (lieMap A B f))
  have h2 := Submodule.finrank_quotient_add_finrank (LinearMap.range (omegaMap A B f))
  have h3 : finrank k (LinearMap.range (lieMap A B f)) = finrank k (LinearMap.range (omegaMap A B f)) :=
    LinearMap.finrank_range_dualMap_eq_finrank_range (omegaMap A B f)
  have h4 : finrank k B.Lie = finrank k B.omega := Subspace.dual_finrank_eq
  omega

theorem finrank_coker_lieMap_congr {A B A' B' : PDivGroup p k} (eA : A ≅ A') (eB : B ≅ B') (f : A ⟶ B)
    (f' : A' ⟶ B') (hc : eA.hom ≫ f' = f ≫ eB.hom) :
    finrank k (B'.Lie ⧸ LinearMap.range (lieMap A' B' f')) =
      finrank k (B.Lie ⧸ LinearMap.range (lieMap A B f)) := by
  let L : B.Lie ≃ₗ[k] B'.Lie := LinearEquiv.ofLinear (lieMap B B' eB.hom) (lieMap B' B eB.inv)
    (by rw [← lieMap_comp, eB.inv_hom_id, lieMap_id]) (by rw [← lieMap_comp, eB.hom_inv_id, lieMap_id])
  have hA : LinearMap.range (lieMap A A' eA.hom) = ⊤ := by
    refine LinearMap.range_eq_top.2 fun x => ⟨lieMap A' A eA.inv x, ?_⟩
    rw [← LinearMap.comp_apply, ← lieMap_comp, eA.inv_hom_id, lieMap_id, LinearMap.id_apply]
  have hr : LinearMap.range (lieMap A' B' f') = (LinearMap.range (lieMap A B f)).map (L : B.Lie →ₗ[k] B'.Lie) := by
    rw [← LinearMap.range_comp_of_range_eq_top _ hA, ← lieMap_comp, hc, lieMap_comp, LinearMap.range_comp]
    rfl
  rw [hr]
  exact (Submodule.Quotient.equiv _ _ L rfl).finrank_eq.symm

end GlobalTheory.Dieu.ColengthHtOne

open GlobalTheory.Dieu.ColengthHtOne in

theorem GlobalTheory.Dieu.le_colength_of_htOne : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) (q' : H ⟶ G) (e : ℕ), q ≫ q' = (p : ℤ_[p]) • 𝟙 G →
    q' ≫ q = (p : ℤ_[p]) • 𝟙 H → frobKerIdeal p k (G.A 1) ≤ kerIdeal (q.app 1) → HasLogDeg q e →
    (e : ℕ∞) ≤ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ∧
    (e : ℕ∞) ≤ Module.length (WittVector p k) (T.M H.dual ⧸ LinearMap.range (T.map (dualHom G H q))) ∧
    e ≤ Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G H q)) := by
  intro p _ T k _ _ _ G H q q' e h1 h2 hF he
  have h3 := le_finrank_coker_omegaMap G H q q' e h1 hF he
  have hp0 : (p : k) = 0 := CharP.cast_eq_zero k p
  haveI := GlobalTheory.PDivGroup.finite_omega_of_eq_zero hp0 G
  haveI := GlobalTheory.PDivGroup.finite_omega_of_eq_zero hp0 H
  have hiso : IsIsog q := ⟨1, q', by rw [pow_one]; exact h1, by rw [pow_one]; exact h2⟩
  have hd := (GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k G H q hiso).2.2.1
  have hL := (GlobalTheory.T.finrank_quot_range_le_length_quot_range_map p T k H.dual G.dual (dualHom G H q)).2
  rw [finrank_coker_lieMap_congr G.bidual H.bidual q _ (bidual_hom_dualHom_dualHom q),
    finrank_coker_lieMap q hd] at hL
  refine ⟨le_trans (by exact_mod_cast h3) (GlobalTheory.T.finrank_quot_range_le_length_quot_range_map p T k G H q).1, le_trans (by exact_mod_cast h3) hL, h3⟩
