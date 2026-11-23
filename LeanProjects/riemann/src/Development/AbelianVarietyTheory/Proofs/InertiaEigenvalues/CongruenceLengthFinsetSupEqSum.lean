import Mathlib
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
open Formalism.BasicNotions Formalism.L2 NumberField IsDedekindDomain Module

namespace GlobalTheory.CongruenceLengthSum

variable {O V : Type} [CommRing O] [AddCommGroup V] [Module O V]

private theorem sep_lemma' {P₁ P₂ : Submodule O V} (hd : Disjoint P₁ P₂) {x₁ y₁ x₂ y₂ : V}
    (h₁ : x₁ ∈ P₁) (h₁' : y₁ ∈ P₁) (h₂ : x₂ ∈ P₂) (h₂' : y₂ ∈ P₂) (h : x₁ + x₂ = y₁ + y₂) :
    x₁ = y₁ ∧ x₂ = y₂ := by
  have e : x₁ - y₁ = y₂ - x₂ := by
    rw [sub_eq_sub_iff_add_eq_add, h, add_comm y₁ y₂]
  have hz : x₁ - y₁ = 0 :=
    Submodule.disjoint_def.mp hd _ (sub_mem h₁ h₁') (e ▸ sub_mem h₂' h₂)
  have e1 : x₁ = y₁ := sub_eq_zero.mp hz
  refine ⟨e1, ?_⟩
  rw [e1] at h
  exact add_left_cancel h

theorem length_quot_sup (T₁ T₂ S₁ S₂ : Submodule O V) (h₁ : S₁ ≤ T₁) (h₂ : S₂ ≤ T₂)
    (hd : Disjoint T₁ T₂) :
    Module.length O (↥(T₁ ⊔ T₂) ⧸ (S₁ ⊔ S₂).comap (T₁ ⊔ T₂).subtype) =
      Module.length O (↥T₁ ⧸ S₁.comap T₁.subtype) + Module.length O (↥T₂ ⧸ S₂.comap T₂.subtype) := by
  have key : ∀ a ∈ T₁, ∀ b ∈ T₂, a + b ∈ S₁ ⊔ S₂ ↔ a ∈ S₁ ∧ b ∈ S₂ := by
    intro a ha b hb
    constructor
    · intro h
      obtain ⟨s₁, hs₁, s₂, hs₂, hs⟩ := Submodule.mem_sup.mp h
      obtain ⟨e1, e2⟩ := sep_lemma' hd ha (h₁ hs₁) hb (h₂ hs₂) hs.symm
      rw [e1, e2]
      exact ⟨hs₁, hs₂⟩
    · rintro ⟨h1, h2⟩
      exact add_mem (Submodule.mem_sup_left h1) (Submodule.mem_sup_right h2)
  let f : (↥T₁ × ↥T₂) →ₗ[O] ↥(T₁ ⊔ T₂) :=
    LinearMap.codRestrict (T₁ ⊔ T₂) (T₁.subtype.coprod T₂.subtype)
      (fun p => add_mem (Submodule.mem_sup_left p.1.2) (Submodule.mem_sup_right p.2.2))
  let Φ := ((S₁ ⊔ S₂).comap (T₁ ⊔ T₂).subtype).mkQ ∘ₗ f
  let Ψ : (↥T₁ × ↥T₂) →ₗ[O] (↥T₁ ⧸ S₁.comap T₁.subtype) × (↥T₂ ⧸ S₂.comap T₂.subtype) :=
    LinearMap.prodMap (S₁.comap T₁.subtype).mkQ (S₂.comap T₂.subtype).mkQ
  have hΦ : Function.Surjective Φ := by
    intro y
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  have hΨ : Function.Surjective Ψ := by
    rintro ⟨y₁, y₂⟩
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ y₁
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ y₂
    exact ⟨(a, b), rfl⟩
  have hker : LinearMap.ker Φ = LinearMap.ker Ψ := by
    ext ⟨a, b⟩
    simp only [LinearMap.mem_ker, Φ, Ψ, f, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply,
      LinearMap.prodMap_apply, Prod.mk_eq_zero]
    exact key a a.2 b b.2
  calc Module.length O (↥(T₁ ⊔ T₂) ⧸ (S₁ ⊔ S₂).comap (T₁ ⊔ T₂).subtype)
      = Module.length O ((↥T₁ × ↥T₂) ⧸ LinearMap.ker Φ) :=
        (Φ.quotKerEquivOfSurjective hΦ).length_eq.symm
    _ = Module.length O ((↥T₁ × ↥T₂) ⧸ LinearMap.ker Ψ) := (Submodule.quotEquivOfEq _ _ hker).length_eq
    _ = Module.length O ((↥T₁ ⧸ S₁.comap T₁.subtype) × (↥T₂ ⧸ S₂.comap T₂.subtype)) :=
        (Ψ.quotKerEquivOfSurjective hΨ).length_eq
    _ = _ := Module.length_prod _ _ _

theorem sup_inf_split (G₁ B₁ L₁ G₂ B₂ L₂ : Submodule O V) (hd : Disjoint (G₁ ⊔ B₁) (G₂ ⊔ B₂))
    (hL₁ : L₁ ≤ G₁ ⊔ B₁) (hL₂ : L₂ ≤ G₂ ⊔ B₂) :
    (G₁ ⊔ G₂) ⊓ ((L₁ ⊔ L₂) ⊔ (B₁ ⊔ B₂)) = G₁ ⊓ (L₁ ⊔ B₁) ⊔ G₂ ⊓ (L₂ ⊔ B₂) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
    obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := Submodule.mem_sup.mp hx1
    obtain ⟨y, hy, c, hc, hyc⟩ := Submodule.mem_sup.mp hx2
    obtain ⟨l₁, hl₁, l₂, hl₂, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := Submodule.mem_sup.mp hc
    have e : g₁ + g₂ = (l₁ + b₁) + (l₂ + b₂) := by rw [← hyc]; abel
    obtain ⟨e1, e2⟩ := sep_lemma' hd (Submodule.mem_sup_left hg₁)
      (add_mem (hL₁ hl₁) (Submodule.mem_sup_right hb₁)) (Submodule.mem_sup_left hg₂)
      (add_mem (hL₂ hl₂) (Submodule.mem_sup_right hb₂)) e
    refine add_mem (Submodule.mem_sup_left (Submodule.mem_inf.mpr ⟨hg₁, ?_⟩))
      (Submodule.mem_sup_right (Submodule.mem_inf.mpr ⟨hg₂, ?_⟩))
    · rw [e1]
      exact add_mem (Submodule.mem_sup_left hl₁) (Submodule.mem_sup_right hb₁)
    · rw [e2]
      exact add_mem (Submodule.mem_sup_left hl₂) (Submodule.mem_sup_right hb₂)
  · refine sup_le (le_inf (inf_le_left.trans le_sup_left) (inf_le_right.trans ?_))
      (le_inf (inf_le_left.trans le_sup_right) (inf_le_right.trans ?_))
    · exact sup_le_sup le_sup_left le_sup_left
    · exact sup_le_sup le_sup_right le_sup_right

theorem inf_split (G₁ B₁ L₁ G₂ B₂ L₂ : Submodule O V) (hd : Disjoint (G₁ ⊔ B₁) (G₂ ⊔ B₂))
    (hL₁ : L₁ ≤ G₁ ⊔ B₁) (hL₂ : L₂ ≤ G₂ ⊔ B₂) :
    (L₁ ⊔ L₂) ⊓ (G₁ ⊔ G₂) = L₁ ⊓ G₁ ⊔ L₂ ⊓ G₂ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
    obtain ⟨l₁, hl₁, l₂, hl₂, rfl⟩ := Submodule.mem_sup.mp hx1
    obtain ⟨g₁, hg₁, g₂, hg₂, hg⟩ := Submodule.mem_sup.mp hx2
    obtain ⟨e1, e2⟩ := sep_lemma' hd (hL₁ hl₁) (Submodule.mem_sup_left hg₁) (hL₂ hl₂)
      (Submodule.mem_sup_left hg₂) hg.symm
    refine add_mem (Submodule.mem_sup_left (Submodule.mem_inf.mpr ⟨hl₁, ?_⟩))
      (Submodule.mem_sup_right (Submodule.mem_inf.mpr ⟨hl₂, ?_⟩))
    · rw [e1]
      exact hg₁
    · rw [e2]
      exact hg₂
  · exact sup_le (inf_le_inf le_sup_left le_sup_left) (inf_le_inf le_sup_right le_sup_right)

end GlobalTheory.CongruenceLengthSum

open GlobalTheory.CongruenceLengthSum in

theorem GlobalTheory.congruence_length_finset_sup : ∀ (O V ι : Type) [CommRing O] [AddCommGroup V] [Module O V] (F : Finset ι) (L G B : ι → Submodule O V), F.SupIndep (fun i => G i ⊔ B i) → (∀ i ∈ F, Disjoint (G i) (B i)) → (∀ i ∈ F, L i ≤ G i ⊔ B i) → Module.length O (↥(F.sup G ⊓ (F.sup L ⊔ F.sup B)) ⧸ (F.sup L ⊓ F.sup G).comap (F.sup G ⊓ (F.sup L ⊔ F.sup B)).subtype) = ∑ i ∈ F, Module.length O (↥(G i ⊓ (L i ⊔ B i)) ⧸ (L i ⊓ G i).comap (G i ⊓ (L i ⊔ B i)).subtype) := by
  classical
  intro O V ι _ _ _ F L G B
  induction F using Finset.induction_on with
  | empty =>
    intro _ _ _
    rw [Finset.sum_empty, Module.length_eq_zero_iff]
    have : Subsingleton ↥((∅ : Finset ι).sup G ⊓ ((∅ : Finset ι).sup L ⊔ (∅ : Finset ι).sup B)) :=
      ⟨fun a b => Subtype.ext (by
        have ha := a.2
        have hb := b.2
        simp only [Finset.sup_empty, bot_sup_eq, inf_bot_eq, Submodule.mem_bot] at ha hb
        rw [ha, hb])⟩
    exact (Submodule.mkQ_surjective _).subsingleton
  | insert j F hj ih =>
    intro hSI hdis hL
    have hdj : Disjoint (G j ⊔ B j) (F.sup (fun i => G i ⊔ B i)) :=
      hSI (Finset.subset_insert j F) (Finset.mem_insert_self j F) hj
    replace hSI : F.SupIndep (fun i => G i ⊔ B i) := fun t ht i hi hit =>
      hSI (ht.trans (Finset.subset_insert j F)) (Finset.mem_insert_of_mem hi) hit
    have hGB : F.sup (fun i => G i ⊔ B i) = F.sup G ⊔ F.sup B := Finset.sup_sup (s := F) (f := G) (g := B)
    rw [hGB] at hdj
    have hLF : F.sup L ≤ F.sup G ⊔ F.sup B := Finset.sup_le fun i hi =>
      (hL i (Finset.mem_insert_of_mem hi)).trans (sup_le_sup (Finset.le_sup hi) (Finset.le_sup hi))
    have hLj : L j ≤ G j ⊔ B j := hL j (Finset.mem_insert_self j F)
    rw [Finset.sum_insert hj, Finset.sup_insert, Finset.sup_insert, Finset.sup_insert]
    rw [sup_inf_split _ _ _ _ _ _ hdj hLj hLF, inf_split _ _ _ _ _ _ hdj hLj hLF]
    have hS₁ : L j ⊓ G j ≤ G j ⊓ (L j ⊔ B j) := le_inf inf_le_right (inf_le_left.trans le_sup_left)
    have hS₂ : F.sup L ⊓ F.sup G ≤ F.sup G ⊓ (F.sup L ⊔ F.sup B) :=
      le_inf inf_le_right (inf_le_left.trans le_sup_left)
    have hT : Disjoint (G j ⊓ (L j ⊔ B j)) (F.sup G ⊓ (F.sup L ⊔ F.sup B)) :=
      hdj.mono (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_left)
    rw [length_quot_sup _ _ _ _ hS₁ hS₂ hT, ih hSI (fun i hi => hdis i (Finset.mem_insert_of_mem hi))
      (fun i hi => hL i (Finset.mem_insert_of_mem hi))]
