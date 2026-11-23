import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFrameCokernelP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSection
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.VB GlobalTheory.LieFilt GlobalTheory.GrFilt
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM germ_resM)
open scoped Classical

namespace GlobalTheory.GrFilt

variable {X : Scheme.{0}} [IsIntegral X] {ι : Type} [Fintype ι] {L : X.Modules} {E E' : ι → X.Modules} {r : ι → ℕ}

theorem FrameMem.mem_iff_repr {o : ι → ℕ} {T : ∀ a, E a ⟶ L} {u : ∀ a, E a ⟶ E' a} (hM : FrameMem r o T u) (k : ℕ)
    {V : X.Opens} {f : ∀ a, Fin (r a) → Γ(E a, V)} (hf : ∀ a, IsFrame (f a)) {f' : ∀ a, Fin (r a) → Γ(E' a, V)}
    {hf' : ∀ a, IsFrame (f' a)} {c : (Σ a, Fin (r a)) → Γ(L, V)} {hc : IsFrame c} (hA : AdaptedAt o T u f f' hf' c hc)
    {U : X.Opens} (h : U ≤ V) (s : Γ(L, U)) :
    s ∈ (filtSub o T k).sec U ↔ ∀ z : Σ a, Fin (r a), k ≤ o z.1 → (hc.basis h).repr s z = 0 := by
  rw [← hM k V f hf f' hf' c hc hA U h]
  have := (hc.basis h).sum_repr s
  simp only [IsFrame.basis_apply] at this
  rw [this]

theorem IsProj.repr_app {o : ι → ℕ} {T : ∀ a, E a ⟶ L} {u : ∀ a, E a ⟶ E' a} (hM : FrameMem r o T u) {b : ι}
    {κ : (filtSub o T (o b + 1)).toMod ⟶ E' b} (hκ : IsProj r o T u b κ)
    {V : X.Opens} {f : ∀ a, Fin (r a) → Γ(E a, V)} (hf : ∀ a, IsFrame (f a)) {f' : ∀ a, Fin (r a) → Γ(E' a, V)}
    {hf' : ∀ a, IsFrame (f' a)} {c : (Σ a, Fin (r a)) → Γ(L, V)} {hc : IsFrame c} (hA : AdaptedAt o T u f f' hf' c hc)
    {U : X.Opens} (h : U ≤ V) (s : Γ((filtSub o T (o b + 1)).toMod, U)) (j : Fin (r b)) :
    ((hf' b).basis h).repr (κ.app U s) j =
      (hc.basis h).repr ((filtSub o T (o b + 1)).incl.app U s) ⟨b, j⟩ := by
  obtain ⟨t, ht, htc⟩ := exists_isFrame_subP (filtSub o T (o b + 1)) c hc (fun z => o z.1 < o b + 1)
    fun V' h' a => by
      rw [hM _ V f hf f' hf' c hc hA V' h' a]
      simp only [not_lt]
  have key : ((hf' b).basis h).coord j ∘ₗ QCoh.appLinear κ U =
      (hc.basis h).coord ⟨b, j⟩ ∘ₗ QCoh.appLinear (filtSub o T (o b + 1)).incl U := by
    refine (ht.basis h).ext fun z => ?_
    simp only [LinearMap.comp_apply, QCoh.appLinear_apply, IsFrame.basis_apply, app_resM, htc,
      Module.Basis.coord_apply]
    rw [hκ V f hf f' hf' c hc hA z.1 (t z) (htc z), ← hc.basis_apply h, Module.Basis.repr_self]
    obtain ⟨⟨a, i⟩, hz⟩ := z
    by_cases hab : a = b
    · subst hab
      rw [dif_pos rfl, ← (hf' a).basis_apply h, Module.Basis.repr_self]
      simp [Finsupp.single_apply]
    · rw [dif_neg hab]
      simp [Finsupp.single_apply, hab]
  exact LinearMap.congr_fun key s

theorem shortExact_stepMap : ∀ {X : Scheme.{0}} [IsIntegral X] {ι : Type} [Fintype ι] {L : X.Modules} {E E' : ι → X.Modules} {r : ι → ℕ}
    (o : ι → ℕ), Function.Injective o → ∀ (T : ∀ a, E a ⟶ L) (u : ∀ a, E a ⟶ E' a),
    (∀ x : X, ∃ V : X.Opens, x ∈ V ∧ LocAdapted r o T u V) → FrameMem r o T u →
    ∀ (b : ι) (κ : (filtSub o T (o b + 1)).toMod ⟶ E' b), IsProj r o T u b κ →
    ∃ w : stepMap o T (o b) ≫ κ = 0, (ShortComplex.mk _ _ w).ShortExact := by
  intro X _ ι _ L E E' r o ho T u hloc hM b κ hκ
  have hstep (U : X.Opens) (s : Γ((filtSub o T (o b)).toMod, U)) :
      (filtSub o T (o b + 1)).incl.app U ((stepMap o T (o b)).app U s) = (filtSub o T (o b)).incl.app U s := rfl
  have w : stepMap o T (o b) ≫ κ = 0 := by
    refine Scheme.Modules.hom_ext _ _ fun W => ?_
    ext s
    change κ.app W ((stepMap o T (o b)).app W s) = 0
    refine TopCat.Presheaf.section_ext ⟨(E' b).presheaf, (E' b).isSheaf⟩ W _ _ fun x hx => ?_
    obtain ⟨V, hxV, f, hf, f', hf', c, hc, hA⟩ := hloc x
    have h0 : resM (E' b) (inf_le_left : W ⊓ V ≤ W) (κ.app W ((stepMap o T (o b)).app W s)) = 0 := by
      rw [← app_resM, ← app_resM]
      refine ((hf' b).basis inf_le_right).ext_elem fun j => ?_
      rw [hκ.repr_app hM hf hA, hstep, map_zero, Finsupp.zero_apply]
      exact (hM.mem_iff_repr _ hf hA _ _).1 ((filtSub o T (o b)).incl_app_mem _) ⟨b, j⟩ le_rfl
    have hx' : x ∈ W ⊓ V := ⟨hx, hxV⟩
    change (E' b).presheaf.germ W x hx _ = (E' b).presheaf.germ W x hx 0
    rw [← germ_resM (inf_le_left : W ⊓ V ≤ W) hx', h0, map_zero, map_zero]
  refine ⟨w, ShortComplex.ShortExact.mk' (DualExact.exact_of_locally _ fun W x hx => ?_) ?_
    (QCoh.epi_of_locally_app_surjective _ fun W x hx => ?_)⟩
  · obtain ⟨V, hxV, f, hf, f', hf', c, hc, hA⟩ := hloc x
    refine ⟨W ⊓ V, inf_le_left, ⟨hx, hxV⟩, fun (t : Γ((filtSub o T (o b + 1)).toMod, W ⊓ V))
      (ht : κ.app _ t = 0) => ?_⟩
    have hmem : (filtSub o T (o b + 1)).incl.app _ t ∈ (filtSub o T (o b)).sec (W ⊓ V) := by
      refine (hM.mem_iff_repr _ hf hA inf_le_right _).2 fun z hz => ?_
      rcases hz.eq_or_lt with he | hlt
      · obtain ⟨a, j⟩ := z
        obtain rfl : b = a := ho he
        rw [← hκ.repr_app hM hf hA, ht, map_zero, Finsupp.zero_apply]
      · exact (hM.mem_iff_repr _ hf hA _ _).1 ((filtSub o T (o b + 1)).incl_app_mem _) z hlt
    exact ⟨(filtSub o T (o b)).mkSec _ hmem, (filtSub o T (o b + 1)).incl_app_injective _ (hstep _ _)⟩
  · have : Mono (stepMap o T (o b) ≫ (filtSub o T (o b + 1)).incl) := by
      rw [stepMap_incl]; exact Sub.mono_incl _
    exact mono_of_mono (stepMap o T (o b)) (filtSub o T (o b + 1)).incl
  · obtain ⟨V, hxV, f, hf, f', hf', c, hc, hA⟩ := hloc x
    refine ⟨W ⊓ V, ⟨hx, hxV⟩, inf_le_left, fun (y : Γ(E' b, W ⊓ V)) => ?_⟩
    have h : W ⊓ V ≤ V := inf_le_right
    let s : Γ(L, W ⊓ V) := ∑ j, ((hf' b).basis h).repr y j • hc.basis h ⟨b, j⟩
    have hs (z : Σ a, Fin (r a)) : (hc.basis h).repr s z =
        ∑ j, if (⟨b, j⟩ : Σ a, Fin (r a)) = z then ((hf' b).basis h).repr y j else 0 := by
      simp only [s, map_sum, map_smul, Module.Basis.repr_self, Finsupp.finsetSum_apply, Finsupp.smul_apply,
        Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    have hmem : s ∈ (filtSub o T (o b + 1)).sec (W ⊓ V) := by
      refine (hM.mem_iff_repr _ hf hA h _).2 fun z hz => ?_
      rw [hs]
      refine Finset.sum_eq_zero fun j _ => if_neg ?_
      rintro rfl
      exact absurd hz (Nat.not_succ_le_self _)
    refine ⟨(filtSub o T (o b + 1)).mkSec _ hmem, ((hf' b).basis h).ext_elem fun j => ?_⟩
    refine (hκ.repr_app hM hf hA h _ j).trans ?_
    rw [Sub.incl_app_mkSec, hs]
    simp

end GlobalTheory.GrFilt

end
