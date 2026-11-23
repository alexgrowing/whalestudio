import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NuInRange
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Formalism.LocalRingCardinality.Lemmas

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.RamRational

section General

variable {K V W M N ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] {σ : K →+* ℂ}

theorem exists_complex_extension [Fintype ι] (e : V →ₛₗ[σ] M) (b : Module.Basis ι K V)
    (hli : LinearIndependent ℂ (fun i => e (b i))) (g : V →ₛₗ[σ] N) :
    ∃ G : M →ₗ[ℂ] N, ∀ x, G (e x) = g x := by
  obtain ⟨G, hG⟩ := LinearMap.exists_extend
    ((Finsupp.linearCombination ℂ (fun i => g (b i))) ∘ₗ hli.repr)
  have hb : ∀ i, G (e (b i)) = g (b i) := by
    intro i
    have hm : e (b i) ∈ Submodule.span ℂ (Set.range (fun i => e (b i))) :=
      Submodule.subset_span ⟨i, rfl⟩
    have h1 := LinearMap.congr_fun hG ⟨e (b i), hm⟩
    have h2 : hli.repr ⟨e (b i), hm⟩ = Finsupp.single i 1 := hli.repr_eq_single i _ rfl
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, h2,
      Finsupp.linearCombination_single, one_smul] at h1
    exact h1
  refine ⟨G, fun x => ?_⟩
  rw [← b.sum_repr x]
  simp only [map_sum, LinearMap.map_smulₛₗ, hb, RingHom.id_apply]

theorem mem_span_of_kernel [Fintype ι] {J : Type} [Fintype J] (e : V →ₛₗ[σ] M)
    (b : Module.Basis ι K V) (hli : LinearIndependent ℂ (fun i => e (b i)))
    (F : J → M →ₗ[ℂ] M) (hF : ∀ j x, ∃ y, e y = F j (e x)) (m : M)
    (hm : m ∈ Submodule.span ℂ (Set.range (fun i => e (b i)))) (h0 : ∀ j, F j m = 0) :
    m ∈ Submodule.span ℂ (e '' {x | ∀ j, F j (e x) = 0}) := by
  classical
  have hinj := inj_of_li σ e b hli
  let f : J → V →ₗ[K] V := fun j => descend e e hinj (F j) (hF j)
  have hf : ∀ j x, e (f j x) = F j (e x) := fun j x => descend_spec e e hinj (F j) (hF j) x
  let g : V →ₗ[K] (J → V) := LinearMap.pi f
  obtain ⟨s, hs⟩ := g.rangeRestrict.exists_rightInverse_of_surjective g.range_rangeRestrict
  obtain ⟨h, hh⟩ := LinearMap.exists_extend s
  have hg : ∀ x, g (h (g x)) = g x := by
    intro x
    have h1 : h (g x) = s (g.rangeRestrict x) := LinearMap.congr_fun hh (g.rangeRestrict x)
    have h2 := LinearMap.congr_fun hs (g.rangeRestrict x)
    rw [h1]
    exact congrArg Subtype.val h2
  choose H hH using fun j : J =>
    exists_complex_extension e b hli (e.comp (h ∘ₗ LinearMap.single K (fun _ : J => V) j))
  let P : M →ₗ[ℂ] M := LinearMap.id - ∑ j, H j ∘ₗ F j
  have hP : ∀ x, P (e x) = e (x - h (g x)) := by
    intro x
    have h1 : g x = ∑ j, Pi.single j (f j x) := (Finset.univ_sum_single (g x)).symm
    rw [h1]
    simp only [P, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.sum_apply,
      LinearMap.comp_apply, map_sub, map_sum, ← hf, hH, LinearMap.coe_single]
  have hPm : P m = m := by
    simp [P, LinearMap.sum_apply, h0]
  rw [← hPm]
  have hle : Submodule.span ℂ (Set.range (fun i => e (b i))) ≤
      (Submodule.span ℂ (e '' {x | ∀ j, F j (e x) = 0})).comap P := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine Submodule.subset_span ⟨b i - h (g (b i)), fun j => ?_, (hP _).symm⟩
    have h1 : g (b i - h (g (b i))) = 0 := by rw [map_sub, hg, sub_self]
    have h2 : f j (b i - h (g (b i))) = 0 := congrFun h1 j
    rw [← hf, h2, map_zero]
  exact hle hm

theorem preserves_of_span (e : V →ₛₗ[σ] M) (S : Set V) (hS : Submodule.span K S = ⊤)
    (F : M →ₗ[ℂ] M) (hF : ∀ x ∈ S, ∃ y, e y = F (e x)) (x : V) : ∃ y, e y = F (e x) := by
  have hx : x ∈ Submodule.span K S := hS ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => exact hF x hx
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨c, hc⟩ := hy
    exact ⟨a + c, by simp [ha, hc]⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨c • a, by simp [LinearMap.map_smulₛₗ, ha]⟩

end General

theorem span_ramSub {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL]
    {embLL : LL →+* ℂ} {Pl : Rows.Places LL} {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R}
    {C : ColumnChain R Tau hc} {A : ColumnsAtT R C} {P : PeriodMap R C}
    (M : MemberForms LL embLL Pl Tau hc C A P) :
    Submodule.span ℂ (M.emb 0 '' (M.ramSub : Set (M.lat 0).V)) = A.Mram := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  · intro m hm
    have hsp : Submodule.span ℂ (Set.range (fun a => M.emb 0 ((M.lat 0).b a))) = A.Mu0 :=
      (M.emb_basis 0).2.trans M.Fi_zero
    have hrho : ∀ v a x, ∃ y, M.emb 0 y = A.rhoT v a (M.emb 0 x) := fun v a =>
      preserves_of_span (M.emb 0) _ (M.lat_good 0).2.2 (A.rhoT v a) (fun x hx => by
        obtain ⟨y, -, hy⟩ := M.rhoT_lat v a x hx
        exact ⟨y, hy⟩)
    have hNm : ∀ v x, ∃ y, M.emb 0 y = A.Nm v (M.emb 0 x) := by
      intro v x
      choose y hy using fun a => hrho v a x
      exact ⟨∑ a, y a, by simp only [map_sum, hy, ColumnsAtT.Nm, LinearMap.sum_apply]⟩
    have hall : ∀ x, M.emb 0 x ∈ A.Mu0 := by
      intro x
      rw [← hsp, ← (M.lat 0).b.sum_repr x, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [LinearMap.map_smulₛₗ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have h := mem_span_of_kernel (M.emb 0) (M.lat 0).b (M.emb_basis 0).1 A.Nm hNm m
      (hsp ▸ hm.1) (fun v => (Submodule.mem_iInf _).1 hm.2 v)
    refine Submodule.span_mono (Set.image_mono ?_) h
    intro x hx
    exact ⟨hall x, (Submodule.mem_iInf _).2 hx⟩

theorem span_ramSub_cols : ∀ (B : Base) (C : Cols B) (u : B.Word),
    Submodule.span ℂ ((C.fm u).emb 0 '' ((C.fm u).ramSub : Set ((C.fm u).lat 0).V)) =
      (C.mem u).A.Mram :=
  fun _ C u => span_ramSub (C.fm u)

end GlobalTheory.RamRational
