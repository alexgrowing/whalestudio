import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientBundleFrameExists

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.Vert GlobalTheory.TriFrame GlobalTheory.FlagCell
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM germ_resM)

namespace GlobalTheory.TriFrame.FlagOf

theorem span_image_eq {K M : Type*} [Field K] [AddCommGroup M] [Module K M] {r : ℕ}
    (b c : Module.Basis (Fin r) K M) (h : ∀ i l, i < l → b.repr (c i) l = 0) (n : ℕ) :
    Submodule.span K (c '' {j | (j : ℕ) < n}) = Submodule.span K (b '' {j | (j : ℕ) < n}) := by
  classical
  have := Module.Finite.of_basis b
  refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨i, hi, rfl⟩
    rw [SetLike.mem_coe, Module.Basis.mem_span_image]
    intro l hl
    by_contra hn
    simp only [Set.mem_setOf_eq] at hi hn
    exact Finsupp.mem_support_iff.1 hl (h i l (Fin.lt_def.2 (by omega)))
  · rw [Set.image_eq_range, Set.image_eq_range]
    exact (finrank_span_eq_card (c.linearIndependent.comp _ Subtype.val_injective)).trans
      (finrank_span_eq_card (b.linearIndependent.comp _ Subtype.val_injective)).symm

variable {X : Scheme.{0}} {F : X.Modules} {r : ℕ}

theorem stalkBasis_repr_germ {U V : X.Opens} {e : Fin r → Γ(F, U)} (he : IsFrame e) (h : V ≤ U)
    (x : X) (hx : x ∈ V) (t : Γ(F, V)) (i : Fin r) :
    (he.stalkBasis x (h hx)).repr (F.presheaf.germ V x hx t) i =
      X.presheaf.germ V x hx ((he.basis h).repr t i) := by
  conv_lhs => rw [← (he.basis h).sum_repr t]
  simp only [map_sum, QCoh.germ_smul, IsFrame.basis_apply, germ_resM]
  simp only [← he.stalkBasis_apply x (h hx)]
  rw [← map_sum, Module.Basis.repr_sum_self]

theorem exists_isFrame_sub {U : X.Opens} (P : Sub F) (c : Fin r → Γ(F, U)) (hc : IsFrame c) (l : ℕ) (hl : l ≤ r)
    (hP : ∀ (V : X.Opens) (h : V ≤ U) (a : Fin r → Γ(X, V)),
      (∑ j, a j • resM F h (c j)) ∈ P.sec V ↔ ∀ j : Fin r, l ≤ (j : ℕ) → a j = 0) :
    ∃ t : Fin l → Γ(P.toMod, U), IsFrame t ∧ ∀ j, P.incl.app U (t j) = c (Fin.castLE hl j) := by
  classical
  have hmem (j : Fin l) : c (Fin.castLE hl j) ∈ P.sec U := by
    have := (hP U le_rfl (Pi.single (Fin.castLE hl j) 1)).2 fun j' hj' => by
      rw [Pi.single_apply, if_neg (fun e => by subst e; have := j.2; simp at hj'; omega)]
    simpa [Pi.single_apply, resM_self] using this
  refine ⟨fun j => P.mkSec _ (hmem j), isFrame_iff.2 fun V h => ⟨?_, fun t _ => ?_⟩, fun _ => rfl⟩
  · refine LinearIndependent.of_comp (QCoh.appLinear P.incl V) ?_
    have := (hc.basis h).linearIndependent.comp _ (Fin.castLE_injective hl)
    convert this using 1
    funext j
    simp only [Function.comp_apply, IsFrame.basis_apply, QCoh.appLinear_apply, app_resM,
      Sub.incl_app_mkSec]
  · have h1 := P.incl_app_mem t
    rw [← (hc.basis h).sum_repr (P.incl.app V t)] at h1
    simp only [IsFrame.basis_apply] at h1
    have h2 := (hP V h _).1 h1
    have h3 : t = ∑ j : Fin l, (hc.basis h).repr (P.incl.app V t) (Fin.castLE hl j) •
        resM P.toMod h (P.mkSec _ (hmem j)) := by
      apply P.incl_app_injective V
      conv_lhs => rw [← (hc.basis h).sum_repr (P.incl.app V t)]
      simp only [map_sum, Scheme.Modules.Hom.app_smul, app_resM, Sub.incl_app_mkSec,
        IsFrame.basis_apply]
      symm
      refine Finset.sum_of_injOn (Fin.castLE hl) (Fin.castLE_injective hl).injOn
        (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) (fun j _ hj => ?_) (fun _ _ => rfl)
      rw [h2 j (Nat.le_of_not_lt fun hlt => hj ⟨⟨j, hlt⟩, by simp, rfl⟩), zero_smul]
    rw [h3]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

variable [IsIntegral X] {A : X.Opens} {s : Fin r → Γ(F, A)}

def stepSub (hs : IsFrame s) (hA : genericPoint X ∈ A) (n : ℕ) : Sub F :=
  Sub.ofGeneric (Submodule.span X.functionField
    ((show Module.Basis (Fin r) X.functionField (genStalk F) from hs.stalkBasis _ hA) '' {j | (j : ℕ) < n}))

theorem mem_stepSub_iff (hs : IsFrame s) (hA : genericPoint X ∈ A) (n : ℕ) {U : X.Opens}
    {e : Fin r → Γ(F, U)} (he : IsFrame e) (ht : IsTri hs e) (V : X.Opens) (h : V ≤ U)
    (a : Fin r → Γ(X, V)) :
    (∑ j, a j • resM F h (e j)) ∈ (stepSub hs hA n).sec V ↔ ∀ j : Fin r, n ≤ (j : ℕ) → a j = 0 := by
  rw [stepSub, Sub.mem_ofGeneric]
  by_cases hV : genericPoint X ∈ V
  swap
  · refine ⟨fun _ j _ => ?_, fun _ h => (hV h).elim⟩
    obtain rfl : V = ⊥ := by
      by_contra hne
      obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
      exact hV (genericPoint_mem hx)
    exact Subsingleton.elim _ _
  have hsp := span_image_eq (K := X.functionField) (M := genStalk F) (hs.stalkBasis _ hA)
    (he.stalkBasis _ (h hV)) (fun i l hil => by
      have hUA : genericPoint X ∈ U ⊓ A := ⟨h hV, hA⟩
      have := stalkBasis_repr_germ hs (inf_le_right : U ⊓ A ≤ A) _ hUA
        (resM F inf_le_left (e i)) l
      rw [germ_resM] at this
      rw [IsFrame.stalkBasis_apply]
      refine this.trans ?_
      exact (congrArg _ (ht i l hil)).trans (map_zero _)) n
  have hco (j : Fin r) : (he.stalkBasis _ (h hV)).repr
      (F.presheaf.germ V _ hV (∑ j, a j • resM F h (e j))) j = X.presheaf.germ V _ hV (a j) := by
    rw [stalkBasis_repr_germ he h]
    simp only [← he.basis_apply h]
    rw [Module.Basis.repr_sum_self]
  have key : F.presheaf.germ V _ hV (∑ j, a j • resM F h (e j)) ∈ Submodule.span X.functionField
      ((show Module.Basis (Fin r) X.functionField (genStalk F) from he.stalkBasis _ (h hV)) ''
        {j | (j : ℕ) < n}) ↔ ∀ j : Fin r, n ≤ (j : ℕ) → a j = 0 := by
    rw [Module.Basis.mem_span_image]
    constructor
    · intro H j hj
      by_contra hne
      have h0 : X.presheaf.germ V _ hV (a j) ≠ 0 := fun h0 =>
        hne (germ_injective_of_isIntegral X _ hV (h0.trans (map_zero _).symm))
      have := H (Finsupp.mem_support_iff.2 (fun h1 => h0 ((hco j).symm.trans h1)))
      simp only [Set.mem_setOf_eq] at this
      omega
    · intro H j hj
      by_contra hn
      simp only [Set.mem_setOf_eq] at hn
      refine Finsupp.mem_support_iff.1 hj ((hco j).trans ?_)
      rw [H j (by omega), map_zero]
  rw [← key]
  exact ⟨fun H => hsp.ge (H hV), fun H _ => hsp.le H⟩

theorem stepSub_mono (hs : IsFrame s) (hA : genericPoint X ∈ A) {m n : ℕ} (hmn : m ≤ n) (V : X.Opens) :
    (stepSub hs hA m).sec V ≤ (stepSub hs hA n).sec V := fun _ ht hV =>
  Submodule.span_mono (Set.image_mono fun _ hj => lt_of_lt_of_le hj hmn) (ht hV)

end GlobalTheory.TriFrame.FlagOf

open GlobalTheory.TriFrame.FlagOf in

theorem GlobalTheory.TriFrame.exists_flag_spans :
    ∀ (X : Scheme.{0}) [IsIntegral X] (A : X.Opens) (F : X.Modules) (r : ℕ) (s : Fin r → Γ(F, A)) (hs : IsFrame s),
      genericPoint X ∈ A →
      (∀ x : X, ∃ (V : X.Opens) (e : Fin r → Γ(F, V)), x ∈ V ∧ IsFrame e ∧ IsTri hs e) →
      ∃ fl : Vert.Flag F r, ∀ (V : X.Opens) (e : Fin r → Γ(F, V)), IsFrame e → IsTri hs e → Spans fl V e := by
  intro X _ A F r s hs hA H
  have fr {V : X.Opens} {e : Fin r → Γ(F, V)} (he : IsFrame e) (ht : IsTri hs e) (l : ℕ) (hl : l ≤ r) :=
    exists_isFrame_sub (stepSub hs hA l) e he l hl (mem_stepSub_iff hs hA l he ht)
  refine ⟨{ F i := (stepSub hs hA i).toMod
            ι i := (stepSub hs hA i).incl
            isSubbundle i := ⟨inferInstance, r - i, fun x => ?_⟩
            isVB i x := ?_
            step i := (stepSub hs hA i.succ).lift (stepSub hs hA i.castSucc).incl fun V t =>
              stepSub_mono hs hA (by simp) V ((stepSub hs hA i.castSucc).incl_app_mem t)
            step_ι i := rfl
            isIso_last := isIso_of_frames (ι := Fin r) _ fun x => ?_ },
    fun V e he ht l => fr he ht l l.is_le⟩
  · obtain ⟨V, e, hx, he, ht⟩ := H x
    obtain ⟨e', he'⟩ := exists_isFrame_cokernel_of_frame (stepSub hs hA i) e he i i.is_le
      (mem_stepSub_iff hs hA i he ht)
    exact ⟨V, e', hx, he'⟩
  · obtain ⟨V, e, hx, he, ht⟩ := H x
    obtain ⟨t, h1, -⟩ := fr he ht i i.is_le
    exact ⟨V, t, hx, h1⟩
  · obtain ⟨V, e, hx, he, ht⟩ := H x
    obtain ⟨t, h1, h2⟩ := fr he ht r le_rfl
    refine ⟨V, t, hx, h1, ?_⟩
    have h3 : (fun j => (stepSub hs hA r).incl.app V (t j)) = e := funext h2
    rw [← h3] at he
    exact he

end
