import Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.StExtInv

open Module NumberField TensorProduct

noncomputable section

namespace Formalism.L2.Geo.ExtensionFiltration.ExtInvMu

open Formalism.BasicNotions Formalism.HN Formalism.HermitianLatticesTheory Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Geo.ExtensionFiltration.ExtInvSk

theorem relIndex_sup_span {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (P : Submodule R W) (x : W) :
    P.toAddSubgroup.relIndex (P ⊔ Submodule.span R {x}).toAddSubgroup =
      (P.comap (LinearMap.toSpanSingleton R W x)).toAddSubgroup.index := by
  set Q := P ⊔ Submodule.span R {x} with hQ
  let f : P.toAddSubgroup × R →+ Q.toAddSubgroup := AddMonoidHom.mk'
    (fun pa => ⟨(pa.1 : W) + pa.2 • x, Submodule.add_mem_sup pa.1.2
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x))⟩)
    (by
      rintro ⟨p, a⟩ ⟨q, c⟩
      ext
      simp only [Prod.mk_add_mk, AddSubgroup.coe_add, add_smul]
      abel)
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨p, hp, z, hz, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
    exact ⟨(⟨p, hp⟩, a), rfl⟩
  have hc : (P.toAddSubgroup.addSubgroupOf Q.toAddSubgroup).comap f =
      (⊤ : AddSubgroup P.toAddSubgroup).prod
        (P.comap (LinearMap.toSpanSingleton R W x)).toAddSubgroup := by
    ext ⟨⟨p, hp⟩, a⟩
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_prod,
      AddSubgroup.mem_top, true_and, Submodule.mem_toAddSubgroup, Submodule.mem_comap,
      LinearMap.toSpanSingleton_apply]
    show (p : W) + a • x ∈ P ↔ a • x ∈ P
    exact Submodule.add_mem_iff_right P hp
  rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hf, hc,
    AddSubgroup.index_prod, AddSubgroup.index_top, one_mul]

section Ext

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  (K' : Type) [Field K'] [NumberField K'] [StarRing K'] [Algebra K K']

abbrev e1 (A : HLat K) (x : A.V) : (baseChange K' A).V := ((1 : K') ⊗ₜ[K] x : K' ⊗[K] A.V)

theorem base_change_emb_smul (A : HLat K) (r : 𝓞 K) (x : A.V) :
    e1 K' A (r • x) = algebraMap (𝓞 K) (𝓞 K') r • e1 K' A x := by
  show (1 : K') ⊗ₜ[K] (r • x) =
    (algebraMap (𝓞 K') K' (algebraMap (𝓞 K) (𝓞 K') r)) • ((1 : K') ⊗ₜ[K] x)
  rw [← algebraMap_smul K r x, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
    TensorProduct.smul_tmul', Algebra.smul_def, smul_eq_mul]
  rfl

theorem root_of_unity_character_add (A : HLat K) (x y : A.V) : e1 K' A (x + y) = e1 K' A x + e1 K' A y :=
  TensorProduct.tmul_add _ _ _

theorem base_change_emb_zero (A : HLat K) : e1 K' A 0 = 0 := TensorProduct.tmul_zero _ _

theorem ext_eq (A : HLat K) (N : Submodule (𝓞 K) A.V) :
    ext K' A N = Submodule.span (𝓞 K') (e1 K' A '' (N : Set A.V)) := rfl

theorem ext_span_set (A : HLat K) (S : Set A.V) :
    ext K' A (Submodule.span (𝓞 K) S) = Submodule.span (𝓞 K') (e1 K' A '' S) := by
  rw [ext_eq]
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro _ ⟨y, hy, rfl⟩
    induction hy using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span ⟨z, hz, rfl⟩
    | zero => rw [SetLike.mem_coe, base_change_emb_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [SetLike.mem_coe, root_of_unity_character_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [SetLike.mem_coe, base_change_emb_smul]; exact Submodule.smul_mem _ _ hy
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem ext_mono (A : HLat K) {M N : Submodule (𝓞 K) A.V} (h : M ≤ N) : ext K' A M ≤ ext K' A N :=
  Submodule.span_mono (Set.image_mono h)

theorem ext_sup_span (A : HLat K) (P : Submodule (𝓞 K) A.V) (x : A.V) :
    ext K' A (P ⊔ Submodule.span (𝓞 K) {x}) =
      ext K' A P ⊔ Submodule.span (𝓞 K') {e1 K' A x} := by
  have h : P ⊔ Submodule.span (𝓞 K) {x} = Submodule.span (𝓞 K) ((P : Set A.V) ∪ {x}) := by
    rw [Submodule.span_union, Submodule.span_eq]
  rw [h, ext_span_set, Set.image_union, Submodule.span_union, Set.image_singleton, ext_eq]

theorem index_step (A : HLat K) (P : Submodule (𝓞 K) A.V) (x : A.V)
    (h : P.toAddSubgroup.relIndex (P ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup ≠ 0) :
    (ext K' A P).toAddSubgroup.relIndex (ext K' A (P ⊔ Submodule.span (𝓞 K) {x})).toAddSubgroup ≠ 0 ∧
    (ext K' A P).toAddSubgroup.relIndex (ext K' A (P ⊔ Submodule.span (𝓞 K) {x})).toAddSubgroup ≤
      P.toAddSubgroup.relIndex (P ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup ^ finrank K K' := by
  rw [ext_sup_span, relIndex_sup_span, relIndex_sup_span] at *
  set I : Ideal (𝓞 K) := P.comap (LinearMap.toSpanSingleton (𝓞 K) A.V x) with hI
  set I' : Ideal (𝓞 K') := (ext K' A P).comap
    (LinearMap.toSpanSingleton (𝓞 K') (baseChange K' A).V (e1 K' A x)) with hI'
  have hle : I.map (algebraMap (𝓞 K) (𝓞 K')) ≤ I' := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    simp only [hI', Ideal.mem_comap, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
    rw [← base_change_emb_smul]
    exact Submodule.subset_span ⟨a • x, ha, rfl⟩
  have hn : (I.map (algebraMap (𝓞 K) (𝓞 K'))).toAddSubgroup.index =
      I.toAddSubgroup.index ^ finrank K K' := by
    have := Ideal.absNorm_algebraMap (𝓞 K) (𝓞 K') I
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply] at this
    rw [IsFractionRing.finrank_eq (𝓞 K) K (𝓞 K') K']
    exact this
  have hd := AddSubgroup.index_dvd_of_le (show (I.map (algebraMap (𝓞 K) (𝓞 K'))).toAddSubgroup ≤
    I'.toAddSubgroup from hle)
  rw [hn] at hd
  have hpos : 0 < I.toAddSubgroup.index ^ finrank K K' := pow_pos (Nat.pos_of_ne_zero h) _
  refine ⟨fun h0 => ?_, Nat.le_of_dvd hpos hd⟩
  rw [h0, zero_dvd_iff] at hd
  exact hpos.ne' hd

theorem index_finset (A : HLat K) (M : Submodule (𝓞 K) A.V) (T : Finset A.V) :
    M.toAddSubgroup.relIndex (M ⊔ Submodule.span (𝓞 K) (T : Set A.V)).toAddSubgroup ≠ 0 →
    (ext K' A M).toAddSubgroup.relIndex
        (ext K' A (M ⊔ Submodule.span (𝓞 K) (T : Set A.V))).toAddSubgroup ≠ 0 ∧
    (ext K' A M).toAddSubgroup.relIndex
        (ext K' A (M ⊔ Submodule.span (𝓞 K) (T : Set A.V))).toAddSubgroup ≤
      M.toAddSubgroup.relIndex (M ⊔ Submodule.span (𝓞 K) (T : Set A.V)).toAddSubgroup ^
        finrank K K' := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro _
    simp only [Finset.coe_empty, Submodule.span_empty, sup_bot_eq, AddSubgroup.relIndex_self,
      one_pow, le_refl, and_true]
    exact one_ne_zero
  | insert x T _ ih =>
    intro h
    set Q := M ⊔ Submodule.span (𝓞 K) (T : Set A.V) with hQ
    have hs : M ⊔ Submodule.span (𝓞 K) ((insert x T : Finset A.V) : Set A.V) =
        Q ⊔ Submodule.span (𝓞 K) {x} := by
      rw [Finset.coe_insert, Set.insert_eq, Submodule.span_union, hQ, sup_assoc,
        sup_comm (Submodule.span (𝓞 K) {x})]
    rw [hs] at h ⊢
    have h1 : M ≤ Q := le_sup_left
    have h2 : Q ≤ Q ⊔ Submodule.span (𝓞 K) {x} := le_sup_left
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ (show M.toAddSubgroup ≤ Q.toAddSubgroup from h1)
      (show Q.toAddSubgroup ≤ (Q ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup from h2)] at h ⊢
    obtain ⟨ha, hb⟩ := mul_ne_zero_iff.1 h
    obtain ⟨ha1, ha2⟩ := ih ha
    obtain ⟨hb1, hb2⟩ := index_step K' A Q x hb
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _
      (show (ext K' A M).toAddSubgroup ≤ (ext K' A Q).toAddSubgroup from ext_mono K' A h1)
      (show (ext K' A Q).toAddSubgroup ≤ (ext K' A (Q ⊔ Submodule.span (𝓞 K) {x})).toAddSubgroup
        from ext_mono K' A h2), mul_pow]
    exact ⟨mul_ne_zero ha1 hb1, Nat.mul_le_mul ha2 hb2⟩

end Ext

theorem orthogonalSplitPolarizationVanishes : S2 := by
  intro K K' _ _ _ _ _ _ _ A M N hN hMN h
  obtain ⟨T, rfl⟩ := hN
  have hs : Submodule.span (𝓞 K) (T : Set A.V) = M ⊔ Submodule.span (𝓞 K) (T : Set A.V) :=
    (sup_eq_right.2 hMN).symm
  rw [hs] at h ⊢
  exact index_finset K' A M T h

end Formalism.L2.Geo.ExtensionFiltration.ExtInvMu
