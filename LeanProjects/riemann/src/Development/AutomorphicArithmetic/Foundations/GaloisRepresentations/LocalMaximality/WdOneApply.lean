import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFunctionalVanishesOnOmegaFormsStatement

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma resP_eq_zero {F V : Type} [Field F] [Algebra ℂ F] [AddCommGroup V] [Module ℂ V]
    (ρ : F →ₗ[ℂ] ℂ) (A : Submodule ℂ F) (B : Submodule ℂ V) (hA : ∀ f ∈ A, ρ f = 0)
    {m : F ⊗[ℂ] V} (hm : m ∈ Submodule.map₂ (TensorProduct.mk ℂ F V) A B) :
    resP V ρ m = 0 := by
  rw [Submodule.map₂_eq_span_image2] at hm
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    simp [resP, hA a ha]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul r x _ hx => rw [map_smul, hx, smul_zero]

private lemma residueCharacteristic_mem {F V : Type} [Field F] [Algebra ℂ F] [AddCommGroup V] [Module ℂ V]
    (ρ : F →ₗ[ℂ] ℂ) (A : Submodule ℂ F) (B : Submodule ℂ V)
    {m : F ⊗[ℂ] V} (hm : m ∈ Submodule.map₂ (TensorProduct.mk ℂ F V) A B) :
    resP V ρ m ∈ B := by
  rw [Submodule.map₂_eq_span_image2] at hm
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    simpa [resP] using B.smul_mem (ρ a) hb
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact B.add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact B.smul_mem r hx

private lemma wd_one_apply {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] (c : Finset ι → E) (t : Finset ι) :
    wd (fun _ : ι => (1 : Module.End ℂ E)) c t = ∑ i ∈ t, GlobalTheory.cubeSign t i • c (t.erase i) := by
  simp [wd, LinearMap.sum_apply]

theorem UpperTheory.Gal.productCup_of_system.pInt_of :
    WdUni → GoodZ → PInt := by
  intro hW _ F K _ _ _ _ _ _ d x hx τ _ ρ hρ a p t ht
  simp only [UpperTheory.Gal.productCup_of_system.Sys.mix, GlobalTheory.WH.acx, GlobalTheory.PD.Cx.B, Submodule.mem_map,
    Submodule.mem_pi] at ht
  obtain ⟨c, hc, rfl⟩ := ht
  have hU := fun I J : Finset (Fin (d + 1)) =>
    hW (Fin (d + 1)) (Fin (d + 1)) (F ⊗[ℂ] DR ℂ K) (fun _ => 1) c I J
  have hcu : ∀ I J : Finset (Fin (d + 1)), c (uni I J) ≠ 0 →
      I.Nonempty ∧ J.Nonempty ∧ I.card + J.card = d + p + 1 ∧
        c (uni I J) ∈ (sysP K x a).M I J := by
    intro I J h0
    have h := hc (uni I J) (Set.mem_univ _)
    obtain ⟨_, hl, hr, hcard, _⟩ := hU I J
    split_ifs at h with h1
    · simp only [GlobalTheory.WH.mixF, hl, hr] at h
      split_ifs at h with h2
      · refine ⟨h2.1, h2.2, ?_, h⟩
        rw [hcard] at h1
        omega
      · exact absurd ((Submodule.mem_bot ℂ).mp h) h0
    · exact absurd ((Submodule.mem_bot ℂ).mp h) h0
  have hz : ∀ (i : Fin (d + 1)) (J : Finset (Fin (d + 1))),
      resP (DR ℂ K) ρ (c (uni (Finset.univ.erase i) J)) = 0 := by
    intro i J
    by_cases h0 : c (uni (Finset.univ.erase i) J) = 0
    · rw [h0, map_zero]
    obtain ⟨hI, _, _, hm⟩ := hcu _ _ h0
    exact resP_eq_zero ρ _ _
      (fun f hf => GlobalTheory.T.residue_functional_vanishes_on_omega_forms ℂ F d (xv x) hx.pd ρ hρ i _ hI (by simp) f hf) hm
  refine ⟨fun L => ((-1 : ℤ) ^ (d + 1)) • resP (DR ℂ K) ρ (c (uni Finset.univ L)), ?_, ?_⟩
  · simp only [Lef.omCx, GlobalTheory.PD.cech, GlobalTheory.PD.cechC, Submodule.mem_pi]
    intro L _
    by_cases h0 : c (uni Finset.univ L) = 0
    · simp [h0]
    obtain ⟨_, hL, hcard, hm⟩ := hcu _ _ h0
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    dsimp only
    rw [if_pos (show L.Nonempty ∧ (L.card : ℤ) = ↑p - 1 + 1 from ⟨hL, by omega⟩)]
    exact Submodule.smul_of_tower_mem _ _ (residueCharacteristic_mem ρ _ _ hm)
  · funext J
    simp only [Lef.omCx, GlobalTheory.PD.cech, GlobalTheory.PD.deltaL, LinearMap.coe_mk, AddHom.coe_mk, GlobalTheory.DI.delta]
    rw [(hU Finset.univ J).1]
    simp only [wd_one_apply, map_add, map_zsmul, map_sum, hz, smul_zero, Finset.sum_const_zero,
      zero_add, Finset.card_univ, Fintype.card_fin, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_comm]
