import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.WKTensFockGenSub
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.DetOneSubEqSumMinors
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.TraceEqTraceRestrictOfRangeLe

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

section Supp

variable {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem tco_physSub_zero {y : TensorProduct ℂ N (Fock n)} (hy : y ∈ physicalSubspace ε) {s : Finset (Fin (n * n))}
    {m : Fin (n * n)} (hm : m ∈ s) (hnp : ¬IsPhys ε (finProdFinEquiv.symm m)) :
    tcoef ((fockBasis n).coord s) y = 0 := by
  set x := finProdFinEquiv.symm m with hxdef
  have h0 : cmT (N := N) x.1 x.2 y = 0 := (mem_physicalSubspace_iff ε y).1 hy x.1 x.2 hnp
  have h1 : tcoef ((fockBasis n).coord s) (cpT (N := N) x.1 x.2 (cmT x.1 x.2 y)) = 0 := by
    rw [h0, map_zero, map_zero]
  change tcoef ((fockBasis n).coord s) (LinearMap.lTensor N (cpFock x.1 x.2)
    (LinearMap.lTensor N (cmFock x.1 x.2) y)) = 0 at h1
  rw [tcoef_lTensor, tcoef_lTensor, tcoef_eq_sum] at h1
  rw [Finset.sum_eq_single s] at h1
  · have hxs : finProdFinEquiv x ∈ s := by rw [hxdef, Equiv.apply_symm_apply]; exact hm
    simpa [lf_num_basis, hxs] using h1
  · intro S _ hS
    simp only [LinearMap.coe_comp, Function.comp_apply, lf_num_basis]
    split_ifs
    · simp [Module.Basis.coord_apply, Finsupp.single_apply, Ne.symm hS]
    · simp
  · simp

theorem tensFock_inf_physSub (L : Submodule ℂ N) :
    tensFock (n := n) L ⊓ physicalSubspace ε = LinearMap.range (TensorProduct.map L.subtype (physFock ε).subtype) := by
  apply le_antisymm
  · rintro y ⟨hyT, hyP⟩
    have hmem : ∀ s, tcoef ((fockBasis n).coord s) y ∈ L := fun s => tcoef_mem hyT _
    refine ⟨∑ S : LfIdx ε, (⟨tcoef ((fockBasis n).coord S.1) y, hmem S.1⟩ : L) ⊗ₜ
      (⟨fockBasis n S.1, physWedge_mem S⟩ : physFock ε), ?_⟩
    rw [map_sum]
    simp only [TensorProduct.map_tmul, Submodule.coe_subtype]
    symm
    calc y = ∑ s, tcoef ((fockBasis n).coord s) y ⊗ₜ fockBasis n s := tcoef_expand y
      _ = ∑ s ∈ univ.filter (fun s => s ⊆ lfPhysModes ε),
          tcoef ((fockBasis n).coord s) y ⊗ₜ fockBasis n s := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun s _ => ?_
        split_ifs with h
        · rfl
        · obtain ⟨m, hm, hmp⟩ := Finset.not_subset.1 h
          have hnp : ¬IsPhys ε (finProdFinEquiv.symm m) := by
            simpa [lfPhysModes, IsPhys] using hmp
          rw [tco_physSub_zero hyP hm hnp, TensorProduct.zero_tmul]
      _ = ∑ S : LfIdx ε, tcoef ((fockBasis n).coord S.1) y ⊗ₜ fockBasis n S.1 :=
        Finset.sum_subtype _ (fun s => by simp) _
  · rintro _ ⟨x, rfl⟩
    refine ⟨?_, ?_⟩
    · refine ⟨TensorProduct.map LinearMap.id (physFock ε).subtype x, ?_⟩
      rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
      rfl
    · show _ ∈ physicalSubspace ε
      rw [mem_physicalSubspace_iff]
      intro j b hjb
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul l f =>
        have hf := f.2
        simp only [physFock, Submodule.mem_iInf, LinearMap.mem_ker] at hf
        simp only [TensorProduct.map_tmul, cmT, LinearMap.id_apply, Submodule.coe_subtype, hf j b hjb,
          TensorProduct.tmul_zero]
      | add x x' hx hx' => rw [map_add, map_add, hx, hx', add_zero]

end Supp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem str_tensFock_physSub (hD : IsDerivedOn ε σ D E) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    {L : Submodule ℂ D} [FiniteDimensional ℂ L] (hL : ∀ x ∈ L, sigD hD hk x ∈ L)
    (hY0 : ∀ y ∈ tensFock (n := n) L ⊓ physicalSubspace ε, (gradT ∘ₗ wK hD hk) y ∈ tensFock L ⊓ physicalSubspace ε) :
    LinearMap.trace ℂ ↥(tensFock (n := n) L ⊓ physicalSubspace (N := D) ε)
        ((gradT ∘ₗ wK hD hk).restrict hY0) =
      LinearMap.trace ℂ L ((sigD hD hk).restrict hL) * physDet ε k := by
  set Φ := TensorProduct.map L.subtype (physFock ε).subtype with hΦ
  have hinj : Function.Injective Φ :=
    TensorProduct.map_injective_of_flat_flat _ _ L.injective_subtype (physFock ε).injective_subtype
  let e : TensorProduct ℂ L (physFock ε) ≃ₗ[ℂ] ↥(tensFock (n := n) L ⊓ physicalSubspace (N := D) ε) :=
    (LinearEquiv.ofInjective Φ hinj).trans (LinearEquiv.ofEq _ _ (tensFock_inf_physSub L).symm)
  have he : ∀ x, ((e x : ↥(tensFock (n := n) L ⊓ physicalSubspace (N := D) ε)) : TensorProduct ℂ D (Fock n)) = Φ x :=
    fun x => rfl
  set sL := (sigD hD hk).restrict hL
  set fP := (CliffordAlgebra.involute.toLinearMap ∘ₗ (ff ε k).toLinearMap).restrict (involute_ff_mapsTo k)
  have hsq : ∀ x, (gradT ∘ₗ wK hD hk) (Φ x) = Φ (TensorProduct.map sL fP x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul l f => rfl
    | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]
  have hconj : (gradT ∘ₗ wK hD hk).restrict hY0 = e.conj (TensorProduct.map sL fP) := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    rw [LinearEquiv.conj_apply_apply, he, LinearMap.restrict_apply]
    show (gradT ∘ₗ wK hD hk) (y : TensorProduct ℂ D (Fock n)) = _
    rw [← hsq, ← he, LinearEquiv.apply_symm_apply]
  have : FiniteDimensional ℂ (Fock n) := Module.Finite.of_basis (fockBasis n)
  rw [hconj, LinearMap.trace_conj', LinearMap.trace_tensorProduct', ← strPhys_eq_trace, strPhys_eq_physDet]

end ReciprocityTheory.ChartRestriction.DS.TRGap
