import Formalism.LocalToGlobal.GlobalTheory.ElemZeroZeroMulApply
import Formalism.SharpRestriction.GlobalSchurBounds.TotallyPositiveTraceGeOfNormDiscr
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
import Formalism.GradedWeylDivisibility.FinalD

open MvPolynomial

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.BasicNotions Formalism.GradedWeylDivisibility

section IntW

variable {LL : Type} [Field LL] (Pl : Rows.Places LL) (w : Pl.Pl)

theorem intW_isUnit_iff (x : intW Pl w) : IsUnit x ↔ Pl.val w (x : LL) = 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    have e : ((u : intW Pl w) : LL) * (((u⁻¹ : (intW Pl w)ˣ) : intW Pl w) : LL) = 1 := congrArg Subtype.val u.mul_inv
    have h1 : Pl.val w ((u : intW Pl w) : LL) + Pl.val w (((u⁻¹ : (intW Pl w)ˣ) : intW Pl w) : LL) = 0 := by
      rw [← AddValuation.map_mul, e, AddValuation.map_one]
    have ha : (0 : WithTop ℤ) ≤ Pl.val w ((u : intW Pl w) : LL) := (u : intW Pl w).2
    have hb : (0 : WithTop ℤ) ≤ Pl.val w (((u⁻¹ : (intW Pl w)ˣ) : intW Pl w) : LL) := (u⁻¹ : (intW Pl w)ˣ).1.2
    exact ((add_eq_zero_iff_of_nonneg ha hb).1 h1).1
  · intro h
    have hx0 : (x : LL) ≠ 0 := by
      intro h0
      rw [h0, AddValuation.map_zero] at h
      exact WithTop.top_ne_zero h
    have hinv : (x : LL)⁻¹ ∈ intW Pl w := by
      show (0 : WithTop ℤ) ≤ Pl.val w (x : LL)⁻¹
      rw [AddValuation.map_inv, h, neg_zero]
    have hxy : x * ⟨_, hinv⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hx0)
    exact ⟨⟨x, ⟨_, hinv⟩, hxy, by rw [mul_comm]; exact hxy⟩, rfl⟩

instance intW_isLocalRing : IsLocalRing (intW Pl w) := by
  have : Nontrivial (intW Pl w) := ⟨⟨0, 1, fun h => zero_ne_one (congrArg Subtype.val h)⟩⟩
  refine IsLocalRing.of_nonunits_add (fun a b ha hb => ?_)
  rw [mem_nonunits_iff, intW_isUnit_iff] at ha hb ⊢
  have ha0 : (0 : WithTop ℤ) ≤ Pl.val w (a : LL) := a.2
  have hb0 : (0 : WithTop ℤ) ≤ Pl.val w (b : LL) := b.2
  have ha' : 0 < Pl.val w (a : LL) := lt_of_le_of_ne ha0 (Ne.symm ha)
  have hb' : 0 < Pl.val w (b : LL) := lt_of_le_of_ne hb0 (Ne.symm hb)
  have hle : min (Pl.val w (a : LL)) (Pl.val w (b : LL)) ≤ Pl.val w ((a : LL) + (b : LL)) :=
    AddValuation.map_add _ _ _
  exact ne_of_gt (lt_of_lt_of_le (lt_min ha' hb') hle)

theorem zpow_mem_intW (u : (intW Pl w)ˣ) (z : ℤ) : ((u : intW Pl w) : LL) ^ z ∈ intW Pl w := by
  rcases Int.eq_nat_or_neg z with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast]
    exact pow_mem (u : intW Pl w).2 m
  · have e : ((u : intW Pl w) : LL) * (((u⁻¹ : (intW Pl w)ˣ) : intW Pl w) : LL) = 1 := congrArg Subtype.val u.mul_inv
    rw [zpow_neg, zpow_natCast, ← inv_pow, ← eq_inv_of_mul_eq_one_right e]
    exact pow_mem (u⁻¹ : (intW Pl w)ˣ).1.2 m

end IntW

section Row

variable {K : Type} [CommRing K]

theorem rowAct_one {r n : ℕ} (f : MvPolynomial (Fin r × Fin n) K) :
    rowAct K (1 : Matrix (Fin r) (Fin r) K) f = f := by
  have h : rowAct K (n := n) (1 : Matrix (Fin r) (Fin r) K) = AlgHom.id K (MvPolynomial (Fin r × Fin n) K) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [rowAct, aeval_X, AlgHom.id_apply]
    rw [Finset.sum_eq_single v.1]
    · simp
    · intro c _ hc
      simp [Matrix.one_apply_ne' hc]
    · simp
  rw [h, AlgHom.id_apply]

end Row

section WO

variable {K : Type} [Field K] (O : Subring K)

def wO (n : ℕ) (ν : Fin n → ℕ) : Submodule O (MvPolynomial (Fin n × Fin n) K) :=
  Submodule.span O (MvPolynomial.map (Int.castRingHom K) '' (weyl ℤ n n le_rfl ν : Set (MvPolynomial (Fin n × Fin n) ℤ)))

private theorem map_subtype_mem_wO_of_mem_weyl {n : ℕ} (ν : Fin n → ℕ) (p : MvPolynomial (Fin n × Fin n) O)
    (hp : p ∈ weyl O n n le_rfl ν) : MvPolynomial.map O.subtype p ∈ wO O n ν := by
  induction hp using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨w, rfl⟩ := hq
    have e : MvPolynomial.map O.subtype (applyWord O w (hw O le_rfl ν)) =
        MvPolynomial.map (Int.castRingHom K) (applyWord ℤ w (hw ℤ le_rfl ν)) := by
      rw [← Formalism.GradedWeylDivisibility.lclosedeq_hw_map (Int.castRingHom O) le_rfl ν, Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map,
        MvPolynomial.map_map, RingHom.ext_int (O.subtype.comp (Int.castRingHom O)) (Int.castRingHom K)]
    rw [e]
    unfold wO
    exact Submodule.subset_span ⟨_, Submodule.subset_span ⟨w, rfl⟩, rfl⟩
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    have h := Submodule.smul_mem (wO O n ν) c hx
    rw [Subring.smul_def, MvPolynomial.smul_eq_C_mul] at h
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]
    exact h

def stabM (n : ℕ) (ν : Fin n → ℕ) : Submonoid (Matrix (Fin n) (Fin n) O) where
  carrier := {g | ∀ f ∈ wO O n ν, rowAct K (g.map O.subtype) f ∈ wO O n ν}
  one_mem' := by
    intro f hf
    rw [Matrix.map_one _ (map_zero _) (map_one _), rowAct_one]
    exact hf
  mul_mem' := by
    intro g h hg hh f hf
    rw [Matrix.map_mul]
    have := congrArg (fun φ => φ f) (rowActMul K n n (h.map O.subtype) (g.map O.subtype))
    simp only [AlgHom.coe_comp, Function.comp_apply] at this
    rw [← this]
    exact hh _ (hg f hf)

theorem wO_stable [IsLocalRing O] {n : ℕ} (ν : Fin n → ℕ) (g : Matrix (Fin n) (Fin n) O) (hg : IsUnit g.det)
    {f : MvPolynomial (Fin n × Fin n) K} (hf : f ∈ wO O n ν) : rowAct K (g.map O.subtype) f ∈ wO O n ν := by
  unfold wO at hf
  induction hf using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨h, hh, rfl⟩ := hq
    have e : MvPolynomial.map (Int.castRingHom K) h =
        MvPolynomial.map O.subtype (MvPolynomial.map (Int.castRingHom O) h) := by
      rw [MvPolynomial.map_map, RingHom.ext_int (O.subtype.comp (Int.castRingHom O)) (Int.castRingHom K)]
    rw [e, ← Formalism.UG.P.wlocal_map_rowAct]
    apply map_subtype_mem_wO_of_mem_weyl
    have hw1 := Formalism.UG.P.wlocal_map_weyl (Int.castRingHom O) le_rfl ν h hh
    have hst := Formalism.UG.Final.WeylGLStableLocal O n n le_rfl ν (Matrix.nonsingInvUnit g hg)⁻¹ _ hw1
    unfold Formalism.UG.dwAct at hst
    rw [inv_inv] at hst
    exact hst
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [Subring.smul_def, map_smul]
    exact Submodule.smul_mem _ c hx

end WO

theorem prod_mem_prod' {R A ι : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] (s : Finset ι)
    (N : ι → Submodule R A) (x : ι → A) (hx : ∀ i ∈ s, x i ∈ N i) : ∏ i ∈ s, x i ∈ ∏ i ∈ s, N i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact Submodule.mem_one.2 ⟨1, map_one _⟩
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact Submodule.mul_mem_mul (hx a (Finset.mem_insert_self a s))
      (ih (fun i hi => hx i (Finset.mem_insert_of_mem hi)))

def subAll {K : Type} [Field K] {ι : Type} {n : ℕ} (g : ι → Matrix (Fin n) (Fin n) K) :
    MvPolynomial (ι × Fin n × Fin n) K →ₐ[K] MvPolynomial (ι × Fin n × Fin n) K :=
  MvPolynomial.aeval (fun v : ι × Fin n × Fin n => ∑ b, MvPolynomial.C (g v.1 b v.2.1) * MvPolynomial.X (v.1, b, v.2.2))

theorem subAll_rename {K : Type} [Field K] {ι : Type} {n : ℕ} (g : ι → Matrix (Fin n) (Fin n) K) (τ : ι)
    (f : MvPolynomial (Fin n × Fin n) K) :
    subAll g (rename (Prod.mk τ) f) = rename (Prod.mk τ) (rowAct K (g τ).transpose f) := by
  have h : (subAll g).comp (rename (Prod.mk τ)) = (rename (Prod.mk τ)).comp (rowAct K (n := n) (g τ).transpose) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [subAll, rowAct, Matrix.transpose_apply]
  exact AlgHom.congr_fun h f

section Span

variable {LL : Type} [Field LL] (Pl : Rows.Places LL) {Tau : Type} [Fintype Tau] (w : Pl.Pl) {n : ℕ}
  (lam : Tau → DomWeight n)

def isO : Submodule (intW Pl w) (MvPolynomial (Tau × Fin n × Fin n) LL) where
  carrier := (Formalism.MainNotions.flipTwoThree.IntSpanAtG Pl w lam : Set (MvPolynomial (Tau × Fin n × Fin n) LL))
  add_mem' ha hb := (Formalism.MainNotions.flipTwoThree.IntSpanAtG Pl w lam).add_mem ha hb
  zero_mem' := (Formalism.MainNotions.flipTwoThree.IntSpanAtG Pl w lam).zero_mem
  smul_mem' := by
    intro c p hp
    induction hp using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨r, f, hr, hf, rfl⟩ := hx
      refine AddSubgroup.subset_closure ⟨(c : LL) * r, f, (intW Pl w).mul_mem c.2 hr, hf, ?_⟩
      rw [Subring.smul_def, smul_smul]
    | zero => rw [smul_zero]; exact (Formalism.MainNotions.flipTwoThree.IntSpanAtG Pl w lam).zero_mem
    | add x y _ _ hx hy => rw [smul_add]; exact (Formalism.MainNotions.flipTwoThree.IntSpanAtG Pl w lam).add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact (Formalism.MainNotions.flipTwoThree.IntSpanAtG Pl w lam).neg_mem hx

theorem ten_mem {F : Tau → MvPolynomial (Fin n × Fin n) LL}
    (hF : ∀ τ, F τ ∈ wO (intW Pl w) n (lam τ).natW) : Formalism.MainNotions.flipTwoThree.ten F ∈ isO Pl w lam := by
  classical
  have h1 : ∀ τ, MvPolynomial.rename (Prod.mk τ) (F τ) ∈ Submodule.span (intW Pl w)
      ((fun g => MvPolynomial.rename (Prod.mk τ) (MvPolynomial.map (Int.castRingHom LL) g)) ''
        (delSq ℤ n (lam τ) : Set (MvPolynomial (Fin n × Fin n) ℤ))) := by
    intro τ
    have hF' := hF τ
    unfold wO at hF'
    revert hF'
    generalize F τ = x0
    intro hF'
    induction hF' using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨g, hg, rfl⟩ := hq
      exact Submodule.subset_span ⟨g, hg, rfl⟩
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      rw [Subring.smul_def, map_smul]
      exact Submodule.smul_mem _ c hx
  have h2 := prod_mem_prod' Finset.univ _ _ (fun τ _ => h1 τ)
  rw [Submodule.prod_span] at h2
  refine (Submodule.span_le.2 ?_ : _ ≤ isO Pl w lam) h2
  intro a ha
  rw [Set.mem_finset_prod] at ha
  obtain ⟨g, hg, rfl⟩ := ha
  choose h hh hgh using fun τ => hg (Finset.mem_univ τ)
  have e : ∏ τ ∈ Finset.univ, g τ =
      (1 : LL) • Formalism.MainNotions.flipTwoThree.ten (fun τ => MvPolynomial.map (Int.castRingHom LL) (h τ)) := by
    rw [one_smul]
    unfold Formalism.MainNotions.flipTwoThree.ten
    refine Finset.prod_congr rfl (fun τ _ => ?_)
    exact (hgh τ).symm
  rw [e]
  show _ ∈ Formalism.MainNotions.flipTwoThree.IntSpanAtG Pl w lam
  unfold Formalism.MainNotions.flipTwoThree.IntSpanAtG
  exact AddSubgroup.subset_closure ⟨1, h, (intW Pl w).one_mem, hh, rfl⟩

theorem actAll_mem_intSpanAtG (k : Tau → Matrix (Fin n) (Fin n) (intW Pl w))
    (hk : ∀ τ, IsUnit (k τ).det) {p : MvPolynomial (Tau × Fin n × Fin n) LL}
    (hp : p ∈ Formalism.MainNotions.flipTwoThree.IntSpanAtG Pl w lam) :
    Formalism.MainNotions.flipTwoThree.actAll lam (fun τ => (k τ).map (intW Pl w).subtype) p ∈ Formalism.MainNotions.flipTwoThree.IntSpanAtG Pl w lam := by
  induction hp using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, f, hr, hf, rfl⟩ := hx
    have hT : Formalism.MainNotions.flipTwoThree.ten (fun τ => rowAct LL (((k τ).map (intW Pl w).subtype).transpose)
        (MvPolynomial.map (Int.castRingHom LL) (f τ))) ∈ isO Pl w lam := by
      apply ten_mem
      intro τ
      rw [← Matrix.transpose_map]
      refine wO_stable (intW Pl w) _ (k τ).transpose (by rw [Matrix.det_transpose]; exact hk τ) ?_
      unfold wO
      exact Submodule.subset_span ⟨f τ, hf τ, rfl⟩
    have hc : (∏ τ, ((k τ).map (intW Pl w).subtype).det ^ (lam τ).detShift) ∈ intW Pl w := by
      refine prod_mem (fun τ _ => ?_)
      obtain ⟨u, hu⟩ := hk τ
      have hd : ((k τ).map (intW Pl w).subtype).det = (((k τ).det : intW Pl w) : LL) :=
        (RingHom.map_det (intW Pl w).subtype (k τ)).symm
      rw [hd, ← hu]
      first
        | exact zpow_mem_intW Pl w u _
        | exact pow_mem (u : intW Pl w).2 _
    have e : Formalism.MainNotions.flipTwoThree.actAll lam (fun τ => (k τ).map (intW Pl w).subtype)
        (r • Formalism.MainNotions.flipTwoThree.ten (fun τ => MvPolynomial.map (Int.castRingHom LL) (f τ))) =
        (∏ τ, ((k τ).map (intW Pl w).subtype).det ^ (lam τ).detShift) • r •
          Formalism.MainNotions.flipTwoThree.ten (fun τ => rowAct LL (((k τ).map (intW Pl w).subtype).transpose)
            (MvPolynomial.map (Int.castRingHom LL) (f τ))) := by
      unfold Formalism.MainNotions.flipTwoThree.actAll
      congr 1
      rw [map_smul]
      congr 1
      show subAll (fun τ => (k τ).map (intW Pl w).subtype) (Formalism.MainNotions.flipTwoThree.ten _) = _
      unfold Formalism.MainNotions.flipTwoThree.ten
      rw [map_prod]
      refine Finset.prod_congr rfl (fun τ _ => ?_)
      exact subAll_rename _ τ _
    rw [e]
    exact (isO Pl w lam).smul_mem ⟨_, hc⟩ ((isO Pl w lam).smul_mem ⟨r, hr⟩ hT)
  | zero =>
    unfold Formalism.MainNotions.flipTwoThree.actAll
    rw [map_zero, smul_zero]
    exact zero_mem _
  | add x y _ _ hx hy =>
    unfold Formalism.MainNotions.flipTwoThree.actAll at hx hy ⊢
    rw [map_add, smul_add]
    exact add_mem hx hy
  | neg x _ hx =>
    unfold Formalism.MainNotions.flipTwoThree.actAll at hx ⊢
    rw [map_neg, smul_neg]
    exact neg_mem hx

end Span

end Formalism.L2.GlobalTheoryTheory.ColValS
