import Development.EtaleCohomology.TateTwists.MapMapEq

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.EtaleFoundations.columnPf

theorem vanish_fg {S : Type*} [CommRing S] {N G Pv : Type*} [AddCommGroup N] [Module S N] [AddCommGroup G] [Module S G]
    [AddCommGroup Pv] [Module S Pv] (φ : Pv →ₗ[S] N) {k : ℕ} (b : Fin k → G) (q : Fin k → Pv)
    (h : ∑ j, φ (q j) ⊗ₜ[S] b j = 0) :
    ∃ (gs : Finset N) (l : ℕ) (a : Fin k → Fin l → S) (c : gs → Fin l → S) (y : Fin l → G),
      (∀ j, b j = ∑ κ, a j κ • y κ) ∧ (∀ g, 0 = ∑ κ, c g κ • y κ) ∧
      ∀ κ, ∑ j, a j κ • φ (q j) + ∑ g, c g κ • (g : N) = 0 := by
  classical
  set Q0 : Submodule S N := Submodule.span S (Set.range fun j => φ (q j))
  have hQ0 : Q0.FG := Submodule.fg_span (Set.finite_range _)
  let t : Q0 ⊗[S] G := ∑ j, (⟨φ (q j), Submodule.subset_span ⟨j, rfl⟩⟩ : Q0) ⊗ₜ b j
  have ht : LinearMap.rTensor G Q0.subtype t = 0 := by simpa [t, map_sum] using h
  obtain ⟨Q, hQ0Q, hQ, ht'⟩ := TensorProduct.eq_zero_of_fg_of_subtype_eq_zero hQ0 ht
  obtain ⟨gs, hgs⟩ := hQ
  have memg : ∀ g : gs, (g : N) ∈ Q := fun g => hgs ▸ Submodule.subset_span g.2
  let m' : Fin k ⊕ gs → Q := Sum.elim (fun j => Submodule.inclusion hQ0Q ⟨φ (q j), Submodule.subset_span ⟨j, rfl⟩⟩)
    fun g => ⟨g, memg g⟩
  let n' : Fin k ⊕ gs → G := Sum.elim b fun _ => 0
  have hspan : Submodule.span S (Set.range m') = ⊤ := by
    apply Submodule.map_injective_of_injective Q.injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
    refine le_antisymm (Submodule.span_le.2 ?_) ?_
    · rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact (m' i).2
    · intro z hz
      rw [← hgs] at hz
      refine (Submodule.span_le.2 fun g hg => Submodule.subset_span ?_) hz
      exact ⟨m' (Sum.inr ⟨g, hg⟩), ⟨Sum.inr ⟨g, hg⟩, rfl⟩, rfl⟩
  have hsum : ∑ i, m' i ⊗ₜ[S] n' i = 0 := by
    rw [Fintype.sum_sum_type]
    simp only [m', n', Sum.elim_inl, Sum.elim_inr, TensorProduct.tmul_zero, Finset.sum_const_zero, add_zero]
    simpa [t, map_sum] using ht'
  obtain ⟨l, a, y, hn, hm⟩ := TensorProduct.vanishesTrivially_of_sum_tmul_eq_zero S hspan hsum
  refine ⟨gs, l, fun j => a (Sum.inl j), fun g => a (Sum.inr g), y, fun j => hn (Sum.inl j), fun g => hn (Sum.inr g),
    fun κ => ?_⟩
  have := congrArg Subtype.val (hm κ)
  rw [Fintype.sum_sum_type] at this
  simpa [m'] using this

end LateralTheory.EtaleFoundations.columnPf

open LateralTheory.EtaleFoundations.columnPf in
theorem LateralTheory.EtaleFoundations.columnPf.kerLoc_of : kerLoc := by
  classical
  intro R _ M P φ hsurj hker G V u hu
  obtain ⟨k, b, q, rfl⟩ := TensorProduct.exists_sum_tmul_eq u
  have h : ∑ j, (φ.app (op V)).hom (q j) ⊗ₜ[ULift.{1} R] b j = 0 := by
    have := congrArg (TensorProduct.comm _ _ _) hu
    simpa [map_sum] using this
  obtain ⟨gs, l, a, c, y, hb, hc, hrel⟩ := vanish_fg (φ.app (op V)).hom b q h
  refine loc_bind (loc_finset (Finset.univ : Finset gs) fun i _ => hsurj V (i : Sec M V)) ?_
  intro W hW hl
  choose pt hpt using hl
  have nφ : ∀ x, (φ.app (op W)).hom ((P.map hW.op).hom x) = (M.obj.map hW.op).hom ((φ.app (op V)).hom x) := fun x => by
    rw [← ModuleCat.comp_apply, φ.naturality, ModuleCat.comp_apply]
  let e : Fin l → P.obj (op W) := fun κ =>
    ∑ j, a j κ • (P.map hW.op).hom (q j) + ∑ g, c g κ • pt g (Finset.mem_univ g)
  have he : ∀ κ, (φ.app (op W)).hom (e κ) = 0 := fun κ => by
    have := congrArg (M.obj.map hW.op).hom (hrel κ)
    simp only [map_add, map_sum, map_smul, map_zero] at this
    simp only [e, map_add, map_sum, map_smul, nφ]
    rw [← this]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [hpt g (Finset.mem_univ g)]
  have hu' : TensorProduct.map (G.obj.map hW.op).hom (P.map hW.op).hom (∑ j, b j ⊗ₜ[ULift.{1} R] q j) =
      ∑ κ, (G.obj.map hW.op).hom (y κ) ⊗ₜ e κ := by
    have hz : ∀ g : gs, ∑ κ, (G.obj.map hW.op).hom (y κ) ⊗ₜ[ULift.{1} R] (c g κ • pt g (Finset.mem_univ g)) = 0 :=
      fun g => by
        have := congrArg (fun z => (G.obj.map hW.op).hom z ⊗ₜ[ULift.{1} R] pt g (Finset.mem_univ g)) (hc g)
        simp only [map_zero, TensorProduct.zero_tmul, map_sum, map_smul, TensorProduct.sum_tmul] at this
        rw [this]
        refine Finset.sum_congr rfl fun κ _ => ?_
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    simp only [e, TensorProduct.tmul_add, TensorProduct.tmul_sum, Finset.sum_add_distrib]
    rw [Finset.sum_comm (s := Finset.univ) (t := (Finset.univ : Finset gs)), Finset.sum_congr rfl fun g _ => hz g,
      Finset.sum_const_zero, add_zero, map_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.map_tmul, hb j, map_sum, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [map_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  refine loc_mono (loc_finset (Finset.univ : Finset (Fin l)) fun κ _ => hker W (e κ) (he κ)) ?_
  intro W' k' hk'
  have hcomp : TensorProduct.map (G.obj.map (k' ≫ hW).op).hom (P.map (k' ≫ hW).op).hom
      (∑ j, b j ⊗ₜ[ULift.{1} R] q j) = TensorProduct.map (G.obj.map k'.op).hom (P.map k'.op).hom
      (TensorProduct.map (G.obj.map hW.op).hom (P.map hW.op).hom (∑ j, b j ⊗ₜ[ULift.{1} R] q j)) := by
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
    simp only [op_comp, Functor.map_comp, ModuleCat.hom_comp]
  rw [hcomp, hu', map_sum]
  refine Finset.sum_eq_zero fun κ _ => ?_
  rw [TensorProduct.map_tmul, hk' κ (Finset.mem_univ κ), TensorProduct.tmul_zero]

open LateralTheory.EtaleFoundations.columnPf in
theorem LateralTheory.EtaleFoundations.acyc.column_of : LateralTheory.EtaleFoundations.acyc.column := column_of' kerLoc_of
