import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)
open GlobalTheory.QCoh (appLinear appLinear_apply)

namespace GlobalTheory.VBExt

section Algebra

variable {R A B C : Type} [CommRing R] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module R A] [Module R B] [Module R C] {f : A →ₗ[R] B} {g : B →ₗ[R] C}
  {ι κ : Type} [Fintype ι] [Fintype κ]

theorem bijective_sumElim (hfg : Function.Exact f g) (hf : Function.Injective f)
    (a : Module.Basis ι R A) (c : Module.Basis κ R C) (t : κ → B) (ht : ∀ k, g (t k) = c k) :
    Function.Bijective (Fintype.linearCombination R (Sum.elim (fun i => f (a i)) t)) := by
  have hg (x : ι ⊕ κ → R) : g (Fintype.linearCombination R (Sum.elim (fun i => f (a i)) t) x) =
      ∑ k, x (.inr k) • c k := by
    simp [Fintype.linearCombination_apply, Fintype.sum_sum_type, hfg.apply_apply_eq_zero, ht]
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    have h2 : ∀ k, x (.inr k) = 0 :=
      Fintype.linearIndependent_iff.1 c.linearIndependent _ (by rw [← hg, hx, map_zero])
    have h1 : ∀ i, x (.inl i) = 0 :=
      Fintype.linearIndependent_iff.1 a.linearIndependent _ (hf (by
        simpa [Fintype.linearCombination_apply, Fintype.sum_sum_type, h2] using hx))
    funext j
    rcases j with i | k
    exacts [h1 i, h2 k]
  · intro y
    obtain ⟨z, hz⟩ := (hfg (y - ∑ k, c.repr (g y) k • t k)).1 (by
      simp [ht])
    refine ⟨Sum.elim (a.repr z) (c.repr (g y)), ?_⟩
    have : ∑ i, a.repr z i • f (a i) = f z := by
      conv_rhs => rw [← a.sum_repr z]
      simp only [map_sum, map_smul]
    simp [Fintype.linearCombination_apply, Fintype.sum_sum_type, this, hz]

theorem det_sumElim [DecidableEq ι] [DecidableEq κ] (hfg : ∀ x, g (f x) = 0)
    (a : Module.Basis ι R A) (c : Module.Basis κ R C) (b : Module.Basis (ι ⊕ κ) R B)
    (hb : ∀ i, b (.inl i) = f (a i)) (hc : ∀ k, g (b (.inr k)) = c k) (a' : ι → A) (t' : κ → B) :
    b.det (Sum.elim (fun i => f (a' i)) t') = a.det a' * c.det fun k => g (t' k) := by
  have h1 (x : A) : ⇑(b.repr (f x)) = Sum.elim (a.repr x) 0 := by
    have : f x = ∑ j, Sum.elim (a.repr x) 0 j • b j := by
      conv_lhs => rw [← a.sum_repr x]
      simp only [Fintype.sum_sum_type, hb, map_sum, map_smul, Sum.elim_inl, Sum.elim_inr,
        Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]
    rw [this, b.repr_sum_self]
  have h2 (y : B) (k : κ) : b.repr y (.inr k) = c.repr (g y) k := by
    have : g y = ∑ k, b.repr y (.inr k) • c k := by
      conv_lhs => rw [← b.sum_repr y]
      simp only [Fintype.sum_sum_type, hb, hc, hfg, map_sum, map_smul, map_add, smul_zero,
        Finset.sum_const_zero, zero_add]
    rw [this, c.repr_sum_self]
  rw [Module.Basis.det_apply, Module.Basis.det_apply, Module.Basis.det_apply,
    ← Matrix.det_fromBlocks_zero₂₁ _ (Matrix.of fun i k => b.repr (t' k) (.inl i))]
  congr 1
  ext (i | i) (j | j) <;> simp [Module.Basis.toMatrix_apply, h1, h2, hfg]

end Algebra

variable {X : Scheme.{0}} {S : ShortComplex X.Modules} {U U' V : X.Opens} {r s : ℕ}

theorem isFrame_sumElim (hS : S.ShortExact) {ι κ : Type} [Fintype ι] [Fintype κ]
    {e : ι → Γ(S.X₁, U)} {t : κ → Γ(S.X₂, U)} (he : IsFrame e)
    (ht : IsFrame fun k => S.g.app U (t k)) :
    IsFrame (Sum.elim (fun i => S.f.app U (e i)) t) := fun V h => by
  have := hS.mono_f
  have key := bijective_sumElim (f := appLinear S.f V) (g := appLinear S.g V)
    (QCoh.exact_app_of_exact_of_mono hS.exact V) (QCoh.injective_app_of_mono S.f V)
    (he.basis h) (ht.basis h) (fun k => resM _ h (t k))
    (fun k => by rw [IsFrame.basis_apply, appLinear_apply, app_resM])
  convert key using 3
  funext j
  rcases j with i | k
  · simp only [Sum.elim_inl, IsFrame.basis_apply, appLinear_apply, app_resM]
  · rfl

theorem detUnit_sumElim (hS : S.ShortExact) {e : Fin r → Γ(S.X₁, U)} {t : Fin s → Γ(S.X₂, U)}
    (he : IsFrame e) (ht : IsFrame fun k => S.g.app U (t k)) {e' : Fin r → Γ(S.X₁, U')}
    {t' : Fin s → Γ(S.X₂, U')} (he' : IsFrame e') (ht' : IsFrame fun k => S.g.app U' (t' k))
    (h : V ≤ U) (h' : V ≤ U') :
    ((isFrame_sumElim hS he ht).comp_equiv finSumFinEquiv.symm).detUnit
      ((isFrame_sumElim hS he' ht').comp_equiv finSumFinEquiv.symm) h h' =
      he.detUnit he' h h' * ht.detUnit ht' h h' := by
  have := hS.mono_f
  refine Units.ext ?_
  have e₁ : ((isFrame_sumElim hS he ht).comp_equiv finSumFinEquiv.symm).basis h =
      ((isFrame_sumElim hS he ht).basis h).reindex finSumFinEquiv :=
    DFunLike.ext _ _ fun k => by simp
  have key := det_sumElim (f := appLinear S.f V) (g := appLinear S.g V)
    (QCoh.exact_app_of_exact_of_mono hS.exact V).apply_apply_eq_zero
    (he.basis h) (ht.basis h) ((isFrame_sumElim hS he ht).basis h)
    (fun i => by simp only [Sum.elim_inl, IsFrame.basis_apply, appLinear_apply, app_resM])
    (fun i => by simp only [Sum.elim_inr, IsFrame.basis_apply, appLinear_apply, app_resM])
    (fun i => resM _ h' (e' i)) (fun k => resM _ h' (t' k))
  simp only [appLinear_apply, app_resM] at key
  rw [Units.val_mul, IsFrame.val_detUnit, IsFrame.val_detUnit, IsFrame.val_detUnit, e₁,
    Module.Basis.det_reindex, ← key]
  congr 1
  funext j
  rcases j with i | k <;> simp

theorem exists_lifts {F G : X.Modules} (φ : F ⟶ G) [Epi φ] {κ : Type} [Fintype κ]
    (c : κ → Γ(G, U)) {x : X} (hx : x ∈ U) :
    ∃ (W : X.Opens) (h : W ≤ U), x ∈ W ∧ ∃ t : κ → Γ(F, W), ∀ k, φ.app W (t k) = resM G h (c k) := by
  choose W hW hxW t ht using fun k => exists_app_eq_of_epi φ (c k) hx
  have hV (k : κ) : U ⊓ Finset.univ.inf W ≤ W k :=
    inf_le_right.trans (Finset.inf_le (Finset.mem_univ k))
  refine ⟨U ⊓ Finset.univ.inf W, inf_le_left, ⟨hx, by
    rw [Opens.coe_finset_inf]; simpa using hxW⟩, fun k => resM F (hV k) (t k), fun k => ?_⟩
  rw [app_resM, ht, resM_resM]

variable (S r s) in

structure AdaptedChart where

  U : X.Opens

  e : Fin r → Γ(S.X₁, U)

  t : Fin s → Γ(S.X₂, U)

  he : IsFrame e

  ht : IsFrame fun k => S.g.app U (t k)

theorem exists_adaptedChart (hS : S.ShortExact) (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) (x : X) :
    ∃ c : AdaptedChart S r s, x ∈ c.U := by
  have := hS.epi_g
  obtain ⟨U, e, hx, he⟩ := h₁ x
  obtain ⟨U', c, -, hx', hle, hc⟩ := h₃.exists_affine hx
  obtain ⟨W, h, hxW, t, ht⟩ := exists_lifts S.g c hx'
  exact ⟨⟨W, _, t, he.res (h.trans hle), by rw [funext ht]; exact hc.res h⟩, hxW⟩

theorem isVB_and_cls_det_of_shortExact (X : Scheme.{0}) (S : ShortComplex X.Modules) (r s : ℕ)
    (hS : S.ShortExact) (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) :
    ∃ h₂ : IsVB S.X₂ (r + s),
      CechPic.cls _ h₂.isLB_det = CechPic.cls _ h₁.isLB_det + CechPic.cls _ h₃.isLB_det := by
  have hb (c : AdaptedChart S r s) := (isFrame_sumElim hS c.he c.ht).comp_equiv finSumFinEquiv.symm
  let L : LB X :=
    { ι := AdaptedChart S r s
      U := fun c => c.U
      g := fun c c' => (hb c).detUnit (hb c') inf_le_left inf_le_right }
  have hL : L.IsLB := by
    refine ⟨top_le_iff.1 fun x _ => ?_, fun c => ?_, fun c c' c'' => ?_⟩
    · exact Opens.mem_iSup.2 (exists_adaptedChart hS h₁ h₃ x)
    · exact (IsFrame.res_detUnit _ _ _ _ _).trans ((hb c).detUnit_self _ _)
    · exact (congrArg₂ (· * ·) (IsFrame.res_detUnit _ _ _ _ _)
        (IsFrame.res_detUnit _ _ _ _ _)).trans
        ((IsFrame.detUnit_mul _ _ _ _ _ _).trans (IsFrame.res_detUnit _ _ _ _ _).symm)
  obtain ⟨h₂, hi⟩ := lbIso_det_of_frames hL _ hb fun _ _ => rfl
  have hT := CechPic.isLB_tens h₁.isLB_det h₃.isLB_det
  have hj : LBIso L (CechPic.tens (det S.X₁ r) (det S.X₃ s)) := CechPic.iso_of_chart hT
    ⟨fun c => (⟨c.U, c.e, c.he⟩, ⟨c.U, _, c.ht⟩), fun _ _ h => ⟨h, h⟩, fun y c c' hc hc' =>
      ((congrArg _ (detUnit_sumElim hS c.he c.ht c'.he c'.ht _ _)).trans (map_mul _ _ _)).trans
        (CechPic.gm_tens (det S.X₁ r) (det S.X₃ s) (𝟙 X) y (⟨c.U, c.e, c.he⟩, ⟨c.U, _, c.ht⟩)
          (⟨c'.U, c'.e, c'.he⟩, ⟨c'.U, _, c'.ht⟩) ⟨hc, hc⟩ ⟨hc', hc'⟩).symm⟩
  exact ⟨h₂, ((CechPic.cls_eq_iff hL _).2 hi).symm.trans ((CechPic.cls_eq_iff hL hT).2 hj)⟩

end GlobalTheory.VBExt
