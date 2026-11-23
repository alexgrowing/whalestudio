import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDifferentialAdjointCupProductPairingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFunctionalVanishesOnOmegaFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraClosurePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedDualRegularFormsFiniteCoverStatement
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open GlobalTheory.W1.Lef
open scoped TensorProduct

set_option autoImplicit false

namespace UpperTheory.Gal.productCup_of_system.RCT

private theorem wd_one {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] (c : Finset ι → E) (s : Finset ι) :
    wd (fun _ : ι => (1 : Module.End ℂ E)) c s = deltaL ℂ ι E c s := by
  show _ = ∑ i ∈ s, GlobalTheory.cubeSign s i • c (s.erase i)
  simp [wd, Units.smul_def]

private theorem card_filters {n : ℕ} (i : Fin n) :
    (Finset.univ.filter (· ≤ i)).card + (Finset.univ.filter (i ≤ ·)).card = n + 1 := by
  have h1 : (Finset.univ.filter (· ≤ i)) ∪ (Finset.univ.filter (i ≤ ·)) = Finset.univ := by
    ext j; simp [le_total]
  have h2 : (Finset.univ.filter (· ≤ i)) ∩ (Finset.univ.filter (i ≤ ·)) = {i} := by
    ext j; simp [le_antisymm_iff]
  have := Finset.card_union_add_card_inter (Finset.univ.filter (· ≤ i)) (Finset.univ.filter (i ≤ ·))
  rw [h1, h2] at this
  simp at this
  omega

variable {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K]

private theorem muP_tmul (τ : DR ℂ K →ₗ[K] K) (w' w'' w : DR ℂ K) :
    muP F K τ (w' ⊗ₜ w'') w = (Algebra.trace F K (τ (w' * w))) ⊗ₜ w'' := by
  simp [muP]

private theorem res_tmul (ρ : F →ₗ[ℂ] ℂ) (f : F) (w : DR ℂ K) : resP (DR ℂ K) ρ (f ⊗ₜ w) = ρ f • w := by
  simp [resP]

private noncomputable def bil (τ : DR ℂ K →ₗ[K] K) (ρ : F →ₗ[ℂ] ℂ) :
    DR ℂ K ⊗[ℂ] DR ℂ K →ₗ[ℂ] DR ℂ K →ₗ[ℂ] DR ℂ K :=
  (muP F K τ).compr₂ (resP (DR ℂ K) ρ)

private theorem bil_tmul (τ : DR ℂ K →ₗ[K] K) (ρ : F →ₗ[ℂ] ℂ) (w' w'' w : DR ℂ K) :
    bil τ ρ (w' ⊗ₜ w'') w = ρ (Algebra.trace F K (τ (w' * w))) • w'' := by
  simp [bil, muP_tmul, res_tmul]

variable {d : ℕ} {x : Fin (d + 1) → Fˣ}

private theorem bil_mem (τ : DR ℂ K →ₗ[K] K) (ρ : F →ₗ[ℂ] ℂ) {a : ℕ} {I J : Finset (Fin (d + 1))}
    {e : DR ℂ K ⊗[ℂ] DR ℂ K} (he : e ∈ MZ F K (xv x) a I J) (v : DR ℂ K) :
    bil τ ρ e v ∈ omB ℂ K (rB ℂ K (xv x) J) a := by
  have h : MZ F K (xv x) a I J ≤ (omB ℂ K (rB ℂ K (xv x) J) a).comap ((bil τ ρ).flip v) :=
    Submodule.map₂_le.2 fun m _ n hn => by
      show bil τ ρ (m ⊗ₜ n) v ∈ omB ℂ K (rB ℂ K (xv x) J) a
      rw [bil_tmul]
      exact Submodule.smul_mem _ _ hn
  exact h he

private theorem bil_face (hc : IsFinCover ℂ K (xv x)) {τ : DR ℂ K →ₗ[K] K} (hτ : IsTop ℂ K (xv x) τ)
    {ρ : F →ₗ[ℂ] ℂ} (hρ : IsRes ℂ (xv x) ρ) {a : ℕ} (had : a ≤ d) (i : Fin (d + 1))
    (hne : (Finset.univ.erase i).Nonempty) (J : Finset (Fin (d + 1)))
    {e : DR ℂ K ⊗[ℂ] DR ℂ K} (he : e ∈ MZ F K (xv x) a (Finset.univ.erase i) J)
    {v : DR ℂ K} (hv : v ∈ omB ℂ K (rB ℂ K (xv x) (Finset.univ.erase i)) a) :
    bil τ ρ e v = 0 := by
  have hdeg : v ∈ ⋀[K]^a Ω[K⁄ℂ] := ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties ℂ K _ a 0).2.1 v hv).2.2.1
  have h : MZ F K (xv x) a (Finset.univ.erase i) J ≤ LinearMap.ker ((bil τ ρ).flip v) :=
    Submodule.map₂_le.2 fun m hm n _ => by
      show bil τ ρ (m ⊗ₜ n) v = 0
      rw [bil_tmul]
      have hmem := (GlobalTheory.T.twistedDual_regularForms_finiteCover ℂ F K d (xv x) hc τ hτ (Finset.univ.erase i) hne (d - a) a
        (by omega) v hdeg).2 hv m hm
      rw [GlobalTheory.T.residue_functional_vanishes_on_omega_forms ℂ F d (xv x) hc.pd ρ hρ i _ hne (Finset.notMem_erase i _) _ hmem, zero_smul]
  exact h he

private theorem top_zero (hc : IsFinCover ℂ K (xv x)) {τ : DR ℂ K →ₗ[K] K} (hτ : IsTop ℂ K (xv x) τ)
    {ρ : F →ₗ[ℂ] ℂ} (hρ : IsRes ℂ (xv x) ρ) {a p : ℕ} (had : a ≤ d)
    (monoM : ∀ I I' J J' : Finset (Fin (d + 1)), I.Nonempty → J.Nonempty → I ⊆ I' → J ⊆ J' →
      MZ F K (xv x) a I J ≤ MZ F K (xv x) a I' J')
    (monoB : ∀ s t : Finset (Fin (d + 1)), s.Nonempty → s ⊆ t →
      omB ℂ K (rB ℂ K (xv x) s) a ≤ omB ℂ K (rB ℂ K (xv x) t) a)
    (α : Finset (Fin (d + 1)) → DR ℂ K) (hα : α ∈ (omCx (rB ℂ K (xv x)) a).Z p)
    (J : Finset (Fin (d + 1))) (u : Finset (Fin (d + 1)) → DR ℂ K ⊗[ℂ] DR ℂ K)
    (hJ : J.Nonempty)
    (hu : u ∈ (cech fun I => MZ F K (xv x) a I J).C ((d : ℤ) - p - 1)) :
    ∑ i, bil τ ρ (deltaL ℂ _ _ u (Finset.univ.filter (· ≤ i))) (α (Finset.univ.filter (i ≤ ·))) = 0 := by
  obtain ⟨hαC, hαZ⟩ := Submodule.mem_inf.1 hα
  have hαZ' : deltaL ℂ _ _ α = 0 := LinearMap.mem_ker.1 hαZ
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun φ => ?_
  have adj := GlobalTheory.T.cechDifferential_adjoint_cupProductPairing ℂ d _ _ (fun I => MZ F K (xv x) a I J)
    (fun I => omB ℂ K (rB ℂ K (xv x) I) a) ((bil τ ρ).compr₂ φ)
    (fun s t hs hst => monoM s t J J hs hJ hst subset_rfl) monoB
    (fun i hne e he v hv => by
      show φ (bil τ ρ e v) = 0
      rw [bil_face hc hτ hρ had i hne J he hv, map_zero])
  obtain ⟨ε, hε⟩ := adj ((d : ℤ) - p - 1)
  have h1 := hε u hu α (by
    have : (d : ℤ) - ((d : ℤ) - p - 1) - 1 = p := by ring
    rw [this]; exact hαC)
  have h2 : (cech fun I => omB ℂ K (rB ℂ K (xv x) I) a).D α = 0 := hαZ'
  rw [h2, map_zero, smul_zero] at h1
  have h3 : cupPair ((bil τ ρ).compr₂ φ) ((cech fun I => MZ F K (xv x) a I J).D u) α =
      φ (∑ i, bil τ ρ (deltaL ℂ _ _ u (Finset.univ.filter (· ≤ i))) (α (Finset.univ.filter (i ≤ ·)))) := by
    simp [cupPair, cech, map_sum]
  rw [← h3]; exact h1

end UpperTheory.Gal.productCup_of_system.RCT

open UpperTheory.Gal.productCup_of_system.RCT in
theorem UpperTheory.Gal.productCup_of_system.rCupTop_of :
    WdUni → GoodZ → RCupTop := by
  intro hW hG F K _ _ _ _ _ _ d x hc τ hτ ρ hρ a p had t ht α hα
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 ht
  have hgood := hG F K d x hc a
  have monoM : ∀ I I' J J' : Finset (Fin (d + 1)), I.Nonempty → J.Nonempty → I ⊆ I' → J ⊆ J' →
      MZ F K (xv x) a I J ≤ MZ F K (xv x) a I' J' := hgood.1.monoM
  have monoB := hgood.2.2
  have hU := fun I J => hW (Fin (d + 1)) (Fin (d + 1)) (DR ℂ K ⊗[ℂ] DR ℂ K) (fun _ => 1) y I J
  have hs : ∀ s, y s ∈ (if (s.card : ℤ) = ((d : ℤ) + 2 - 1) then mixF (sysZ K x a).M s else ⊥ :
      Submodule ℂ (DR ℂ K ⊗[ℂ] DR ℂ K)) := fun s => (Submodule.mem_pi.1 hy) s (Set.mem_univ _)
  have hy0 : ∀ I J : Finset (Fin (d + 1)), ¬ (I.Nonempty ∧ J.Nonempty ∧ I.card + J.card = d + 1) →
      y (uni I J) = 0 := by
    intro I J hn
    obtain ⟨e1, e2, e3, -⟩ := (hU I J).2
    have h := hs (uni I J)
    rw [e3] at h
    by_cases hcd : (((I.card + J.card : ℕ)) : ℤ) = (d : ℤ) + 2 - 1
    · rw [if_pos hcd, mixF, e1, e2, if_neg (fun hh => hn ⟨hh.1, hh.2, by omega⟩)] at h
      exact (Submodule.mem_bot ℂ).1 h
    · rw [if_neg hcd] at h
      exact (Submodule.mem_bot ℂ).1 h
  have hy1 : ∀ I J : Finset (Fin (d + 1)), y (uni I J) ∈ MZ F K (xv x) a I J := by
    intro I J
    by_cases hn : I.Nonempty ∧ J.Nonempty ∧ I.card + J.card = d + 1
    · obtain ⟨e1, e2, e3, -⟩ := (hU I J).2
      have h := hs (uni I J)
      rw [e3, if_pos (by omega), mixF, e1, e2, if_pos ⟨hn.1, hn.2.1⟩] at h
      exact h
    · rw [hy0 I J hn]; exact Submodule.zero_mem _
  have hα0 : ∀ s : Finset (Fin (d + 1)), s.card ≠ p + 1 → α s = 0 := by
    intro s hsc
    have h : α s ∈ (if s.Nonempty ∧ (s.card : ℤ) = (p : ℤ) + 1 then omB ℂ K (rB ℂ K (xv x) s) a else ⊥ :
        Submodule ℂ (DR ℂ K)) := (Submodule.mem_pi.1 (Submodule.mem_inf.1 hα).1) s (Set.mem_univ _)
    rw [if_neg (fun hh => hsc (by omega))] at h
    exact (Submodule.mem_bot ℂ).1 h
  refine Submodule.mem_map.2 ⟨fun J' => ∑ i, ((-1 : ℤ) ^ (Finset.univ.filter (· ≤ i)).card) •
    bil τ ρ (y (uni (Finset.univ.filter (· ≤ i)) J')) (α (Finset.univ.filter (i ≤ ·))), ?_, ?_⟩
  · refine Submodule.mem_pi.2 fun J' _ => ?_
    show _ ∈ (if J'.Nonempty ∧ (J'.card : ℤ) = (p : ℤ) - 1 + 1 then omB ℂ K (rB ℂ K (xv x) J') a else ⊥ :
      Submodule ℂ (DR ℂ K))
    split_ifs with hJ
    · exact Submodule.sum_mem _ fun i _ => Submodule.smul_of_tower_mem _ _ (bil_mem τ ρ (hy1 _ _) _)
    · refine (Submodule.mem_bot ℂ).2 (Finset.sum_eq_zero fun i _ => ?_)
      have hcf := card_filters i
      by_cases h2 : (Finset.univ.filter (i ≤ ·)).card = p + 1
      · rw [hy0 _ J' ?_, map_zero, LinearMap.zero_apply, smul_zero]
        rintro ⟨-, hJn, hcard⟩
        exact hJ ⟨hJn, by omega⟩
      · rw [hα0 _ h2, map_zero, smul_zero]
  · funext J
    have hD : ∀ i, (sysZ K x a).mix.D y (uni (Finset.univ.filter (· ≤ i)) J) =
        deltaL ℂ _ _ (fun b' => y (uni b' J)) (Finset.univ.filter (· ≤ i)) +
        ((-1 : ℤ) ^ (Finset.univ.filter (· ≤ i)).card) •
          deltaL ℂ _ _ (fun L' => y (uni (Finset.univ.filter (· ≤ i)) L')) J := by
      intro i
      have h := (hU (Finset.univ.filter (· ≤ i)) J).1
      refine Eq.trans h ?_
      rw [wd_one, wd_one]
    have hI : ∑ i, bil τ ρ (deltaL ℂ _ _ (fun b' => y (uni b' J)) (Finset.univ.filter (· ≤ i)))
        (α (Finset.univ.filter (i ≤ ·))) = 0 := by
      by_cases hJ : J.Nonempty ∧ J.card = p + 1
      · refine top_zero hc hτ hρ had monoM monoB α hα J _ hJ.1 ?_
        refine Submodule.mem_pi.2 fun s _ => ?_
        show _ ∈ (if s.Nonempty ∧ (s.card : ℤ) = (d : ℤ) - p - 1 + 1 then MZ F K (xv x) a s J else ⊥ :
          Submodule ℂ (DR ℂ K ⊗[ℂ] DR ℂ K))
        split_ifs with hsc
        · exact hy1 s J
        · exact (Submodule.mem_bot ℂ).2 (hy0 s J fun hh => hsc ⟨hh.1, by omega⟩)
      · refine Finset.sum_eq_zero fun i _ => ?_
        have hcf := card_filters i
        by_cases h2 : (Finset.univ.filter (i ≤ ·)).card = p + 1
        · have hz : deltaL ℂ _ _ (fun b' => y (uni b' J)) (Finset.univ.filter (· ≤ i)) = 0 := by
            show ∑ s ∈ Finset.univ.filter (· ≤ i), GlobalTheory.cubeSign (Finset.univ.filter (· ≤ i)) s •
              y (uni ((Finset.univ.filter (· ≤ i)).erase s) J) = 0
            refine Finset.sum_eq_zero fun s hs' => ?_
            rw [hy0 _ J ?_, smul_zero]
            rintro ⟨-, hJn, hcard⟩
            rw [Finset.card_erase_of_mem hs'] at hcard
            have := Finset.card_pos.2 ⟨s, hs'⟩
            exact hJ ⟨hJn, by omega⟩
          rw [hz, map_zero, LinearMap.zero_apply]
        · rw [hα0 _ h2, map_zero]
    have hB : ∀ i, bil τ ρ (((-1 : ℤ) ^ (Finset.univ.filter (· ≤ i)).card) •
          deltaL ℂ _ _ (fun L' => y (uni (Finset.univ.filter (· ≤ i)) L')) J) (α (Finset.univ.filter (i ≤ ·))) =
        ∑ j ∈ J, GlobalTheory.cubeSign J j • (((-1 : ℤ) ^ (Finset.univ.filter (· ≤ i)).card) •
          bil τ ρ (y (uni (Finset.univ.filter (· ≤ i)) (J.erase j))) (α (Finset.univ.filter (i ≤ ·)))) := by
      intro i
      show (bil τ ρ).flip _ (((-1 : ℤ) ^ (Finset.univ.filter (· ≤ i)).card) •
        ∑ j ∈ J, GlobalTheory.cubeSign J j • y (uni (Finset.univ.filter (· ≤ i)) (J.erase j))) = _
      simp only [Units.smul_def, map_zsmul, map_sum, LinearMap.flip_apply, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
    show ∑ j ∈ J, GlobalTheory.cubeSign J j • ∑ i, ((-1 : ℤ) ^ (Finset.univ.filter (· ≤ i)).card) •
        bil τ ρ (y (uni (Finset.univ.filter (· ≤ i)) (J.erase j))) (α (Finset.univ.filter (i ≤ ·))) =
      resP (DR ℂ K) ρ (∑ i, muP F K τ ((sysZ K x a).mix.D y (uni (Finset.univ.filter (· ≤ i)) J))
        (α (Finset.univ.filter (i ≤ ·))))
    have hR : resP (DR ℂ K) ρ (∑ i, muP F K τ ((sysZ K x a).mix.D y (uni (Finset.univ.filter (· ≤ i)) J))
        (α (Finset.univ.filter (i ≤ ·)))) =
        ∑ i, bil τ ρ ((sysZ K x a).mix.D y (uni (Finset.univ.filter (· ≤ i)) J))
          (α (Finset.univ.filter (i ≤ ·))) := map_sum _ _ _
    rw [hR]
    simp only [hD, map_add, LinearMap.add_apply, Finset.sum_add_distrib, hI, zero_add, hB]
    rw [Finset.sum_comm]
    simp only [Finset.smul_sum]
