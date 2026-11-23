import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleWeightAntisymmetricEqStatement

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.ZcWords

section Maps

variable {α β : Type*}

theorem interleave_map (f : α → β) {u v w : List α} (h : Comb.Interleave u v w) :
    Comb.Interleave (u.map f) (v.map f) (w.map f) := by
  induction h with
  | nil => exact .nil
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih

theorem shuffle_map (f : α → β) {us : List (List α)} {w : List α} (h : Comb.Shuffle us w) :
    Comb.Shuffle (us.map (List.map f)) (w.map f) := by
  induction h with
  | nil => exact .nil
  | cons _ hi ih => exact .cons ih (interleave_map f hi)

end Maps

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_sNu_iterate (x : CuspT k) (j : ℕ) : (sNu^[j] x).1 = x.1.nu j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    show (sNu^[j] x).1.nu 1 = _
    rw [ih, IrrGL.nu_nu]
    push_cast
    rfl

theorem sNu_injective : Function.Injective (sNu (k := k)) := by
  intro x y h
  have h1 : x.1.nu 1 = y.1.nu 1 := congrArg Subtype.val h
  have h2 := congrArg (fun r => IrrGL.nu r (-1)) h1
  simp only [IrrGL.nu_nu, add_neg_cancel, IrrGL.nu_zero] at h2
  exact Subtype.ext h2

theorem sNu_aperiodic (t : CuspT k) (j : ℕ) (hj : 0 < j) : sNu^[j] t ≠ t := by
  intro h
  have h1 : t.1.nu j = t.1 := (val_sNu_iterate t j).symm.trans (congrArg Subtype.val h)
  have h2 : t.1.nu ((j : ℝ) : ℂ) = t.1 := by simpa using h1
  have h3 : (j : ℝ) = 0 := (IrrGL.nu_ofReal_eq_self t.2.1).1 h2
  have h4 : j = 0 := by exact_mod_cast h3
  omega

theorem toA_injective : Function.Injective (toA (k := k)) := by
  intro Δ Δ' h
  have h1 : Δ.first = Δ'.first := congrArg (fun a => (Comb.ASeg.start a).1) h
  have h2 : Δ.len = Δ'.len := congrArg Comb.ASeg.len h
  exact Segment.ext_first h1 h2

theorem image_carrier (Δ : Segment k) : Subtype.val '' ((toA Δ).carrier sNu) = Δ.carrier := by
  ext x
  rw [Segment.mem_carrier]
  constructor
  · rintro ⟨y, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i, hi, (val_sNu_iterate (toA Δ).start i).symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨sNu^[a] (toA Δ).start, ⟨a, ha, rfl⟩, val_sNu_iterate (toA Δ).start a⟩

theorem carrier_subset {Δ Δ' : Segment k} (h : Δ.carrier ⊆ Δ'.carrier) :
    (toA Δ).carrier sNu ⊆ (toA Δ').carrier sNu :=
  (Set.image_subset_image_iff Subtype.val_injective).1 (by rwa [image_carrier, image_carrier])

theorem precedes_of_aPrecedes {Δ Δ' : Segment k} (h : Comb.APrecedes sNu (toA Δ) (toA Δ')) : Δ.Precedes Δ' := by
  obtain ⟨⟨⟨Γ, hΓ⟩, h1, h2⟩, j, hj, hs⟩ := h
  refine ⟨⟨⟨Segment.ofFirst Γ.start.1 Γ.start.2 Γ.len Γ.len_pos, ?_⟩, fun e => h1 (carrier_subset e),
    fun e => h2 (carrier_subset e)⟩, j, hj, ?_⟩
  · have e : toA (Segment.ofFirst Γ.start.1 Γ.start.2 Γ.len Γ.len_pos) = Γ := rfl
    rw [← image_carrier, e, hΓ, Set.image_union, image_carrier, image_carrier]
  · exact (congrArg Subtype.val hs).trans (val_sNu_iterate _ j)

theorem decW_eq (Δ : Segment k) : decW Δ = ((toA Δ).dec sNu).map Subtype.val := by
  apply List.ext_getElem
  · simp [decW, Comb.ASeg.dec, toA]
  · intro i h1 h2
    have hl : i < Δ.len := by simpa [decW] using h1
    simp only [decW, Comb.ASeg.dec, List.getElem_ofFn, List.getElem_map, List.getElem_reverse, List.getElem_range,
      Segment.term, val_sNu_iterate, Fin.val_rev]
    simp only [toA, List.length_range]
    rw [show Δ.len - 1 - i = Δ.len - (i + 1) by omega]

theorem reverse_ofFn {α : Type*} {h : ℕ} (f : Fin h → α) :
    (List.ofFn f).reverse = List.ofFn fun i => f (Fin.rev i) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [Fin.rev]
    congr 2
    omega

theorem wtW_eq {h : ℕ} (Δ : Fin h → Segment k) :
    wtW Δ = (Comb.wt sNu ((List.ofFn Δ).map toA)).map Subtype.val := by
  rw [wtW, Comb.wt, List.map_flatten, ← List.map_reverse, reverse_ofFn, List.map_map, List.map_map, List.map_ofFn]
  congr 2
  funext i
  exact decW_eq _

instance : Nonempty (CuspT k) :=
  ⟨⟨IrrGL.ofChar 1 isSmoothChar_one, IrrGL.isCusp_ofChar 1 isSmoothChar_one⟩⟩

theorem inSh_of_inShW {𝔫 : Multiset (Segment k)} {h : ℕ} {Δ : Fin h → Segment k} (H : InShW 𝔫 (wtW Δ)) :
    Comb.InSh sNu (𝔫.map toA) (Comb.wt sNu ((List.ofFn Δ).map toA)) := by
  obtain ⟨Ls, rfl, hS⟩ := H
  have hg : Function.LeftInverse (Function.invFun (Subtype.val : CuspT k → IrrGL k)) Subtype.val :=
    Function.leftInverse_invFun Subtype.val_injective
  have hback : ∀ l : List (CuspT k), (l.map Subtype.val).map (Function.invFun (Subtype.val : CuspT k → IrrGL k)) = l :=
    fun l => by
      rw [List.map_map, hg.comp_eq_id, List.map_id]
  refine ⟨Ls.map toA, by simp, ?_⟩
  have h1 := shuffle_map (Function.invFun (Subtype.val : CuspT k → IrrGL k)) hS
  rw [wtW_eq, hback, List.map_map] at h1
  have h2 : (List.map (Function.invFun (Subtype.val : CuspT k → IrrGL k))) ∘ decW = Comb.ASeg.dec sNu ∘ toA := by
    funext D
    simp only [Function.comp, decW_eq, hback]
  rw [h2, ← List.map_map] at h1
  exact h1

theorem aOrdered_of_isOrderedForm {h : ℕ} {Δ : Fin h → Segment k} {𝔪 : Multiset (Segment k)}
    (H : IsOrderedForm Δ 𝔪) : Comb.AOrdered sNu ((List.ofFn Δ).map toA) := by
  rw [Comb.AOrdered, List.pairwise_map, List.pairwise_ofFn]
  exact fun i j hij hp => H.2 i j hij (precedes_of_aPrecedes hp)

theorem coe_map_ofFn {h : ℕ} {Δ : Fin h → Segment k} {𝔪 : Multiset (Segment k)} (H : IsOrderedForm Δ 𝔪) :
    (((List.ofFn Δ).map toA : List _) : Multiset _) = 𝔪.map toA := by
  rw [← H.1, Fin.univ_val_map, Multiset.map_coe]

theorem eq_of_inShW_wtW : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), ∀ (𝔪 𝔫 : Multiset (Segment k)) (h h' : ℕ) (Δ : Fin h → Segment k)
    (Γ : Fin h' → Segment k), IsOrderedForm Δ 𝔪 → IsOrderedForm Γ 𝔫 → InShW 𝔫 (wtW Δ) → InShW 𝔪 (wtW Γ) → 𝔪 = 𝔫 := by
  intro k _ _ _ _ _ 𝔪 𝔫 h h' Δ Γ hΔ hΓ h1 h2
  have hL := coe_map_ofFn hΔ
  have hM := coe_map_ofFn hΓ
  have key := GlobalTheory.T.shuffle_weight_antisymmetric_eq sNu sNu_injective sNu_aperiodic ((List.ofFn Δ).map toA) ((List.ofFn Γ).map toA)
    (aOrdered_of_isOrderedForm hΔ) (aOrdered_of_isOrderedForm hΓ) (by rw [hM]; exact inSh_of_inShW h1)
    (by rw [hL]; exact inSh_of_inShW h2)
  rw [hL, hM] at key
  exact Multiset.map_injective toA_injective key

end GlobalTheory.CompanionTheory.ZcWords

end
