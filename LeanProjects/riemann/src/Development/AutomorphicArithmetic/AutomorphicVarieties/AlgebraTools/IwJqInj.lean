import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameParahoricRepSplitsAsProduct
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwDomSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwDomMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools GlobalTheory.PRep

section

open GlobalTheory.IwahoriInj GlobalTheory.IwahoriTraceProof

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem jqInj_compact (C : Subgroup 𝓀[k]ˣ) : IsCompact (iwC k n C : Set (GL (Fin n) k)) := by
  have ho : IsOpen (iwC k n C : Set (GL (Fin n) k)) :=
    Subgroup.isOpen_mono (H₁ := KOne k (Fin n)) (le_sup_left.trans le_sup_left) GlobalTheory.StepData.isOpen_KOne
  exact GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho)
    fun g hg => iwahori_le_KO k _ (((memIwC k n C).1 g).1 hg).1

private theorem jqInj_dom {x : kˣ} (hx : valuation k (x : k) = uniformizer k) (m : ℕ) :
    Dom fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ))) := by
  intro i j hij
  simp only [Units.val_zpow_eq_zpow_val, map_zpow₀, hx]
  refine zpow_le_zpow_right_of_le_one₀ unif_pos uniformizer_lt_one.le ?_
  have : ((i : ℕ) : ℤ) ≤ (j : ℕ) := by exact_mod_cast Fin.le_def.1 hij
  nlinarith

private theorem jqInj_ev {x : kˣ} (hx : valuation k (x : k) = uniformizer k) {u : GL (Fin n) k}
    (hu : u ∈ unipB k (Fin n)) : ∀ᶠ m : ℕ in Filter.atTop,
      diagT k (Fin n) (fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ)))) * u *
        (diagT k (Fin n) (fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ)))))⁻¹ ∈ unipO k n := by
  have key : ∀ u ∈ unipB k (Fin n), ∀ᶠ m : ℕ in Filter.atTop, GlobalTheory.StepData.IntM
      (diagT k (Fin n) (fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ)))) * u *
        (diagT k (Fin n) (fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ)))))⁻¹).val := by
    intro u hu
    simp only [GlobalTheory.StepData.IntM, Filter.eventually_all]
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · filter_upwards [eventually_deep (u.val i j)] with m hm
      rw [← map_inv, diag_mul_mul_diag]
      have h1 : Deep (-((m : ℤ) * (i : ℕ)) + (m : ℤ) * (j : ℕ))
          ((x ^ (-((m : ℤ) * (i : ℕ))) * (x ^ (-((m : ℤ) * (j : ℕ))))⁻¹ : kˣ) : k) := by
        rw [← _root_.zpow_neg, neg_neg, ← _root_.zpow_add, Deep, Units.val_zpow_eq_zpow_val, map_zpow₀, hx]
      have h2 : ((i : ℕ) : ℤ) + 1 ≤ (j : ℕ) := by exact_mod_cast Fin.lt_def.1 h
      exact deep_zero_iff.1 ((h1.mul hm).mono (by nlinarith))
    · refine Filter.Eventually.of_forall fun m => ?_
      rw [((mem_unipB k).1 (conj_mem_unipB _ hu)).2 i]
      exact one_mem _
    · refine Filter.Eventually.of_forall fun m => ?_
      rw [((mem_unipB k).1 (conj_mem_unipB _ hu)).1 i j h]
      exact zero_mem _
  filter_upwards [key u hu, key _ (inv_mem hu)] with m h1 h2
  refine ⟨conj_mem_unipB _ hu, GlobalTheory.StepData.mem_KO.2 ⟨h1, ?_⟩⟩
  convert h2 using 2
  group

end

theorem UpperTheory.V.AlgebraTools.jqInj :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → ∀ v : fixd π (iwC k n C), (Submodule.Quotient.mk (v : V) : Jacquet π (unipB k (Fin n))) = 0 → v = 0 := by
  intro k _ _ _ _ n C V _ _ π hπ v hv
  have h1 : (v : V) ∈ twKer π (unipB k (Fin n)) 1 := (Submodule.Quotient.mk_eq_zero _).1 hv
  obtain ⟨c, hc⟩ := valuation_surjective (uniformizer k)
  have hc0 : c ≠ 0 := fun h => by
    rw [h, map_zero] at hc
    exact GlobalTheory.IwahoriInj.unif_pos.ne hc
  have hx : valuation k ((Units.mk0 c hc0 : kˣ) : k) = uniformizer k := hc
  generalize Units.mk0 c hc0 = x at hx
  have hle : unipO k n ≤ iwC k n C := le_sup_right.trans le_sup_left
  have h2 : ∀ w ∈ twKer π (unipB k (Fin n)) 1, ∀ᶠ m : ℕ in Filter.atTop,
      π (diagT k (Fin n) (fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ))))) w ∈ twKer π (iwC k n C) 1 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, w, rfl⟩ := hy
      filter_upwards [jqInj_ev hx u.2] with m hm
      have := GlobalTheory.IwahoriInj.sub_mem_twKer (π := π) (hle hm)
        (π (diagT k (Fin n) (fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ))))) w)
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply, ← map_sub] at this
      simpa only [MonoidHom.one_apply, Units.val_one, one_smul] using this
    | zero => simp
    | add a b _ _ ha hb =>
      filter_upwards [ha, hb] with m h1 h2
      rw [map_add]
      exact add_mem h1 h2
    | smul a y _ hy =>
      filter_upwards [hy] with m h1
      rw [map_smul]
      exact Submodule.smul_mem _ a h1
  obtain ⟨m, hm⟩ := (h2 _ h1).exists
  have hd := jqInj_dom (n := n) hx m
  obtain ⟨s, hs, -, hsum⟩ := domSum k n _ hd
  have hq : IsUnit (resCard k : ℂ) := by
    refine Ne.isUnit (Nat.cast_ne_zero.2 ?_)
    exact Nat.card_pos.ne'
  have hu := (domMul k n C ℂ V π).2.1 hq _ hd
  have h0 : hk π (iwC k n C) (diagT k (Fin n) (fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ))))) v = 0 := by
    refine Subtype.ext (GlobalTheory.IwahoriInj.eq_zero_of_fixed hπ (jqInj_compact C)
      (GlobalTheory.IwahoriInj.mem_fixed.2 (hk π (iwC k n C) _ v).2) ?_)
    rw [hsum]
    refine Submodule.sum_mem _ fun u hu => ?_
    rw [map_mul, Module.End.mul_apply]
    exact GlobalTheory.IwahoriInj.apply_mem_twKer (hle (hs u hu)) hm
  exact ((Module.End.isUnit_iff _).1 hu).1 (h0.trans (map_zero _).symm)
