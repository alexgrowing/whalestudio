import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFrameCokernelP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagOfTriangularFrames

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.VB GlobalTheory.LieFilt GlobalTheory.GrFilt
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM germ_resM)
open scoped Classical

namespace GlobalTheory.GrFilt

theorem span_blockTriangular {K W : Type*} [Field K] [AddCommGroup W] [Module K W] {ι : Type} [Fintype ι]
    {r : ι → ℕ} {W' : ι → Type*} [∀ a, AddCommGroup (W' a)] [∀ a, Module K (W' a)] (o : ι → ℕ)
    (ho : Function.Injective o) (C : (Σ a, Fin (r a)) → W) (B : ∀ a, Module.Basis (Fin (r a)) K (W' a))
    (t : (Σ a, Fin (r a)) → W) (w : ∀ a, Fin (r a) → W' a) (m : (Σ a, Fin (r a)) → (Σ a, Fin (r a)) → K)
    (ht : ∀ y, t y = ∑ z, m y z • C z) (h0 : ∀ y z, o y.1 < o z.1 → m y z = 0)
    (h1 : ∀ a i j, m ⟨a, i⟩ ⟨a, j⟩ = (B a).repr (w a i) j) (hw : ∀ a, Submodule.span K (Set.range (w a)) = ⊤)
    (k : ℕ) : Submodule.span K (t '' {z | o z.1 < k}) = Submodule.span K (C '' {z | o z.1 < k}) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, ht]
    refine Submodule.sum_mem _ fun z _ => ?_
    by_cases hz : o y.1 < o z.1
    · rw [h0 y z hz, zero_smul]; exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨z, lt_of_le_of_lt (not_lt.1 hz) hy, rfl⟩)
  · have key : ∀ n, ∀ z : Σ a, Fin (r a), o z.1 = n → n < k → C z ∈ Submodule.span K (t '' {z | o z.1 < k}) := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        rintro ⟨b, j⟩ hb hk
        simp only at hb
        set S := Submodule.span K (t '' {z | o z.1 < k})
        let φ : W' b →ₗ[K] W := (B b).constr K fun j => C ⟨b, j⟩
        have hφ : Submodule.span K (Set.range (w b)) ≤ S.comap φ := by
          refine Submodule.span_le.2 ?_
          rintro _ ⟨i, rfl⟩
          have e1 : φ (w b i) = ∑ j, m ⟨b, i⟩ ⟨b, j⟩ • C ⟨b, j⟩ := by
            simp only [φ, Module.Basis.constr_apply_fintype, h1, Module.Basis.equivFun_apply]
          have e2 : t ⟨b, i⟩ = φ (w b i) + ∑ a ∈ Finset.univ.erase b, ∑ j, m ⟨b, i⟩ ⟨a, j⟩ • C ⟨a, j⟩ := by
            rw [ht, e1, Fintype.sum_sigma]
            exact (Finset.add_sum_erase _ (fun a => ∑ j, m ⟨b, i⟩ ⟨a, j⟩ • C ⟨a, j⟩) (Finset.mem_univ b)).symm
          change φ (w b i) ∈ S
          rw [← sub_eq_iff_eq_add] at e2
          rw [← e2]
          refine S.sub_mem (Submodule.subset_span ⟨_, (hb.trans_lt hk : o b < k), rfl⟩)
            (S.sum_mem fun a ha => S.sum_mem fun j _ => ?_)
          rcases lt_trichotomy (o a) (o b) with h | h | h
          · exact S.smul_mem _ (ih (o a) (hb ▸ h) ⟨a, j⟩ rfl (by omega))
          · exact absurd (ho h) (Finset.ne_of_mem_erase ha)
          · rw [h0 ⟨b, i⟩ ⟨a, j⟩ h, zero_smul]; exact S.zero_mem
        have := hφ (hw b ▸ Submodule.mem_top : B b j ∈ _)
        simpa [φ] using this
    rintro _ ⟨z, hz, rfl⟩
    exact key _ z rfl hz

variable {X : Scheme.{0}} [IsIntegral X] {ι : Type} [Fintype ι] {L : X.Modules} {E E' : ι → X.Modules} {r : ι → ℕ}

theorem genSpan_eq_span_frame (o : ι → ℕ) (T : ∀ a, E a ⟶ L) {V : X.Opens} (f : ∀ a, Fin (r a) → Γ(E a, V))
    (hf : ∀ a, IsFrame (f a)) (hV : genericPoint X ∈ V) (k : ℕ) :
    genSpan o T k = Submodule.span X.functionField
      ((fun z : Σ a, Fin (r a) => (L.presheaf.germ V _ hV ((T z.1).app V (f z.1 z.2)) : genStalk L)) ''
        {z | o z.1 < k}) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
  · rintro _ ⟨a, ha, U, hU, s, rfl⟩
    have hUV : genericPoint X ∈ U ⊓ V := ⟨hU, hV⟩
    rw [SetLike.mem_coe, ← germ_resM (inf_le_left : U ⊓ V ≤ U) hUV, ← app_resM,
      ← ((hf a).basis (inf_le_right : U ⊓ V ≤ V)).sum_repr (resM _ inf_le_left s)]
    simp only [map_sum, Scheme.Modules.Hom.app_smul, IsFrame.basis_apply, app_resM, QCoh.germ_smul, germ_resM]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨a, i⟩, ha, rfl⟩)
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨z.1, hz, V, hV, _, rfl⟩

end GlobalTheory.GrFilt

theorem GlobalTheory.GrFilt.genSpan_eq_of_adaptedAt :
    ∀ {X : Scheme.{0}} [IsIntegral X] {ι : Type} [Fintype ι] {L : X.Modules} {E E' : ι → X.Modules} {r : ι → ℕ}
    (o : ι → ℕ), Function.Injective o → ∀ (T : ∀ a, E a ⟶ L) (u : ∀ a, E a ⟶ E' a) {V : X.Opens}
    (f : ∀ a, Fin (r a) → Γ(E a, V)), (∀ a, IsFrame (f a)) → ∀ (f' : ∀ a, Fin (r a) → Γ(E' a, V)) (hf' : ∀ a, IsFrame (f' a))
    (c : (Σ a, Fin (r a)) → Γ(L, V)) (hc : IsFrame c), AdaptedAt o T u f f' hf' c hc → ∀ hV : genericPoint X ∈ V,
    (∀ a, Submodule.span X.functionField
      (Set.range fun i => ((E' a).presheaf.germ V _ hV ((u a).app V (f a i)) : genStalk (E' a))) = ⊤) →
    ∀ k, genSpan o T k = Submodule.span X.functionField ((fun z => L.presheaf.germ V _ hV (c z)) '' {z | o z.1 < k}) := by
  intro X _ ι _ L E E' r o ho T u V f hf f' hf' c hc hA hV hsp k
  rw [genSpan_eq_span_frame o T f hf hV]
  refine span_blockTriangular (K := X.functionField) (W := genStalk L) (W' := fun a => genStalk (E' a)) o ho _
    (fun a => (hf' a).stalkBasis _ hV) _ _
    (fun y z => X.presheaf.germ V _ hV ((hc.basis le_rfl).repr ((T y.1).app V (f y.1 y.2)) z))
    (fun y => ?_) (fun y z h => ?_) (fun a i j => ?_) hsp k
  · conv_lhs => rw [← (hc.basis le_rfl).sum_repr ((T y.1).app V (f y.1 y.2))]
    simp only [map_sum, QCoh.germ_smul, IsFrame.basis_apply, germ_resM]
  · exact (congrArg _ ((hA y.1 y.2).1 z h)).trans (map_zero _)
  · exact (congrArg _ ((hA a i).2 j)).trans
      (TriFrame.FlagOf.stalkBasis_repr_germ (hf' a) le_rfl _ hV _ j).symm

end
