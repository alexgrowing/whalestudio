import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.OnePlusPowerAssembly

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Models.SupModel

variable {k G : Type} [Field k] [Group G]

theorem isHom_comp {A B C : Ob k G} {f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)}
    {g : (Fin B.m → k) →ₗ[k] (Fin C.m → k)} (hf : IsHom A B f) (hg : IsHom B C g) : IsHom A C (g ∘ₗ f) :=
  fun s x => by simp only [LinearMap.comp_apply]; rw [hf, hg]

theorem isHom_add {A B : Ob k G} {f g : (Fin A.m → k) →ₗ[k] (Fin B.m → k)}
    (hf : IsHom A B f) (hg : IsHom A B g) : IsHom A B (f + g) :=
  fun s x => by simp only [LinearMap.add_apply, map_add]; rw [hf, hg]

theorem exists_sum (A B : Ob k G) : ∃ (C : Ob k G) (i : (Fin A.m → k) →ₗ[k] (Fin C.m → k))
    (j : (Fin B.m → k) →ₗ[k] (Fin C.m → k)), IsHom A C i ∧ IsHom B C j ∧ Function.Bijective (i.coprod j) := by
  obtain ⟨C, e, he⟩ := exists_ob (A.ρ.prod B.ρ)
  refine ⟨C, e.toLinearMap ∘ₗ LinearMap.inl k _ _, e.toLinearMap ∘ₗ LinearMap.inr k _ _, ?_, ?_, ?_⟩
  · intro g x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← he]; congr 1; simp [Representation.prod]
  · intro g x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← he]; congr 1; simp [Representation.prod]
  · have : (e.toLinearMap ∘ₗ LinearMap.inl k _ _).coprod (e.toLinearMap ∘ₗ LinearMap.inr k _ _)
        = e.toLinearMap := by
      rw [← LinearMap.comp_coprod, LinearMap.coprod_inl_inr, LinearMap.comp_id]
    rw [this]; exact e.bijective

theorem exists_proj {A B C : Ob k G} {i : (Fin A.m → k) →ₗ[k] (Fin C.m → k)}
    {j : (Fin B.m → k) →ₗ[k] (Fin C.m → k)} (hi : IsHom A C i) (hj : IsHom B C j)
    (hb : Function.Bijective (i.coprod j)) :
    ∃ (π : (Fin C.m → k) →ₗ[k] (Fin A.m → k)) (π' : (Fin C.m → k) →ₗ[k] (Fin B.m → k)),
      IsHom C A π ∧ IsHom C B π' ∧ (∀ x, π (i x) = x) ∧ (∀ x, π (j x) = 0) ∧ (∀ x, π' (i x) = 0) ∧
      (∀ x, π' (j x) = x) ∧ ∀ x, i (π x) + j (π' x) = x := by
  let e := LinearEquiv.ofBijective _ hb
  have h1 : ∀ x y, e.symm (i x + j y) = (x, y) := fun x y => by
    rw [LinearEquiv.symm_apply_eq]; simp [e]
  have h2 : ∀ x, i (e.symm x).1 + j (e.symm x).2 = x := fun x => by
    exact e.apply_symm_apply x
  have h3 : ∀ g x, e.symm (C.ρ g x) = (A.ρ g (e.symm x).1, B.ρ g (e.symm x).2) := fun g x => by
    rw [← h1, hi, hj, ← map_add, h2]
  refine ⟨LinearMap.fst k _ _ ∘ₗ e.symm.toLinearMap, LinearMap.snd k _ _ ∘ₗ e.symm.toLinearMap,
    fun g x => ?_, fun g x => ?_, fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_, fun x => h2 x⟩
  · simp [h3]
  · simp [h3]
  · have := h1 x 0; simp at this; simp [this]
  · have := h1 0 x; simp at this; simp [this]
  · have := h1 x 0; simp at this; simp [this]
  · have := h1 0 x; simp at this; simp [this]

variable {l n : ℕ} {R : RingPG k l}

theorem map_comp_apply (F : DFun R n G) {A B C : Ob k G} {f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)}
    {g : (Fin B.m → k) →ₗ[k] (Fin C.m → k)} {h : (Fin A.m → k) →ₗ[k] (Fin C.m → k)}
    (hA : F.Obj A) (hB : F.Obj B) (hC : F.Obj C) (hf : IsHom A B f) (hg : IsHom B C g)
    (hh : ∀ x, g (f x) = h x) (i : ZMod n) (x : Vc k A.m) :
    F.map B C g i (F.map A B f i x) = F.map A C h i x := by
  have : h = g ∘ₗ f := LinearMap.ext fun x => (hh x).symm
  rw [this, F.map_comp A B C f g hA hB hC hf hg]; rfl

theorem map_zero' (F : DFun R n G) {A B : Ob k G} (hA : F.Obj A) (hB : F.Obj B) (i : ZMod n) (x : Vc k A.m) :
    F.map A B 0 i x = 0 := by
  have := F.map_smul A B 0 0 hA hB (fun g x => by simp) i x
  simpa using this

theorem model_sup : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A : Ob k G) (N N' : Lats k n A.m), M.Model A N → M.Model A N' → M.Model A (fun i => N i ⊔ N' i) := by
  intro k G _ _ l n _ _ _ R F r Dt M A N N' hN hN'
  obtain ⟨B, Nb, A₁, j, p, hB, hj, hji, hp, hps, rfl⟩ := hN
  obtain ⟨B', Nb', A₂, j', p', hB', hj', hji', hp', hps', rfl⟩ := hN'
  obtain ⟨C, i, i', hi, hi', hb, hC⟩ := M.base_sum B Nb B' Nb' hB hB'
  obtain ⟨π, π', hπ, hπ', e1, e2, e3, e4, -⟩ := exists_proj hi hi' hb
  obtain ⟨S, a, a', ha, ha', hab⟩ := exists_sum A₁ A₂
  obtain ⟨q, q', hq, hq', d1, d2, d3, d4, d5⟩ := exists_proj ha ha' hab
  have oB := M.base_obj _ _ hB
  have oB' := M.base_obj _ _ hB'
  have oC := M.base_obj _ _ hC
  have o1 := F.obj_sub _ _ _ hj hji oB
  have o2 := F.obj_sub _ _ _ hj' hji' oB'
  have oS := F.obj_sum _ _ _ _ _ ha ha' hab.2 o1 o2
  have oA := F.obj_quot _ _ _ hp hps o1
  have hJ : IsHom S C (i ∘ₗ j ∘ₗ q + i' ∘ₗ j' ∘ₗ q') :=
    isHom_add (isHom_comp (isHom_comp hq hj) hi) (isHom_comp (isHom_comp hq' hj') hi')
  have hP : IsHom S A (p ∘ₗ q + p' ∘ₗ q') := isHom_add (isHom_comp hq hp) (isHom_comp hq' hp')
  refine ⟨C, _, S, _, _, hC, hJ, ?_, hP, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 := congrArg π hx
    have h2 := congrArg π' hx
    simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add, e1, e2, e3, e4, map_zero, add_zero,
      zero_add] at h1 h2
    have h1' : q x = 0 := hji (by simpa using h1)
    have h2' : q' x = 0 := hji' (by simpa using h2)
    rw [← d5 x, h1', h2']; simp
  · intro y
    obtain ⟨x, rfl⟩ := hps y
    exact ⟨a x, by simp [d1, d3]⟩
  · funext t
    apply le_antisymm
    · apply sup_le
      · rintro _ ⟨y, hy, rfl⟩
        refine ⟨F.map A₁ S a t y, ?_, ?_⟩
        · change F.map S C (i ∘ₗ j ∘ₗ q + i' ∘ₗ j' ∘ₗ q') t (F.map A₁ S a t y) ∈ F.push B C i Nb t ⊔ F.push B' C i' Nb' t
          rw [map_comp_apply F (h := i ∘ₗ j) o1 oS oC ha hJ (fun x => by simp [d1, d3]),
            ← map_comp_apply F o1 oB oC hj hi (fun _ => rfl)]
          exact Submodule.mem_sup_left ⟨_, hy, rfl⟩
        · exact map_comp_apply F o1 oS oA ha hP (fun x => by simp [d1, d3]) t y
      · rintro _ ⟨y, hy, rfl⟩
        refine ⟨F.map A₂ S a' t y, ?_, ?_⟩
        · change F.map S C (i ∘ₗ j ∘ₗ q + i' ∘ₗ j' ∘ₗ q') t (F.map A₂ S a' t y) ∈ F.push B C i Nb t ⊔ F.push B' C i' Nb' t
          rw [map_comp_apply F (h := i' ∘ₗ j') o2 oS oC ha' hJ (fun x => by simp [d2, d4]),
            ← map_comp_apply F o2 oB' oC hj' hi' (fun _ => rfl)]
          exact Submodule.mem_sup_right ⟨_, hy, rfl⟩
        · exact map_comp_apply F o2 oS oA ha' hP (fun x => by simp [d2, d4]) t y
    · rintro _ ⟨s, hs, rfl⟩
      change F.map S C (i ∘ₗ j ∘ₗ q + i' ∘ₗ j' ∘ₗ q') t s ∈ F.push B C i Nb t ⊔ F.push B' C i' Nb' t at hs
      obtain ⟨_, ⟨u, hu, rfl⟩, _, ⟨u', hu', rfl⟩, h⟩ := Submodule.mem_sup.1 hs
      change F.map B C i t u + F.map B' C i' t u' = _ at h
      have h1 := congrArg (F.map C B π t) h
      have h2 := congrArg (F.map C B' π' t) h
      rw [map_add, map_comp_apply F (h := LinearMap.id) oB oC oB hi hπ e1,
        map_comp_apply F (h := 0) oB' oC oB hi' hπ e2, F.map_id B oB, map_zero' F oB' oB,
        map_comp_apply F (h := j ∘ₗ q) oS oC oB hJ hπ (fun x => by simp [e1, e2]),
        ← map_comp_apply F oS o1 oB hq hj (fun _ => rfl), add_zero, LinearMap.id_apply] at h1
      rw [map_add, map_comp_apply F (h := LinearMap.id) oB' oC oB' hi' hπ' e4,
        map_comp_apply F (h := 0) oB oC oB' hi hπ' e3, F.map_id B' oB', map_zero' F oB oB',
        map_comp_apply F (h := j' ∘ₗ q') oS oC oB' hJ hπ' (fun x => by simp [e3, e4]),
        ← map_comp_apply F oS o2 oB' hq' hj' (fun _ => rfl), zero_add, LinearMap.id_apply] at h2
      change F.map S A _ t s ∈ _
      rw [F.map_add S A _ _ oS oA (isHom_comp hq hp) (isHom_comp hq' hp'),
        ← map_comp_apply F oS o1 oA hq hp (fun _ => rfl), ← map_comp_apply F oS o2 oA hq' hp' (fun _ => rfl)]
      refine Submodule.add_mem_sup ⟨_, ?_, rfl⟩ ⟨_, ?_, rfl⟩
      · change F.map A₁ B j t _ ∈ Nb t
        rw [← h1]; exact hu
      · change F.map A₂ B' j' t _ ∈ Nb' t
        rw [← h2]; exact hu'

end GlobalTheory.Models.SupModel
