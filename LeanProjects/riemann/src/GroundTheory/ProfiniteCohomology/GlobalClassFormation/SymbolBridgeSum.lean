import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.SymbolBridge
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain IdeleGroup

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

attribute [local instance] FiniteSubfield.isGalois_of_normal galCommGroup

variable {K : FiniteSubfield} (ι : LocalEmbeddings K) (E : FiniteSubfield) [Fact (K ≤ E)]
  [(E.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal] [IsMulCommutative (E.1 ≃ₐ[K.1] E.1)]

theorem restrictHom_localSymbolAt_inr (v : HeightOneSpectrum (𝓞 K.1)) (a : K.1ˣ) :
    restrictHom (E := E) (localSymbolAt ι (.inr v) a) =
      localSymbol E.1 v (Units.map (algebraMap K.1 (v.adicCompletion K.1) : K.1 →* v.adicCompletion K.1) a) :=
  restrictHom_globalDecomp_of_finite E (ι.fin v) fun y hy ↦
    AlgEquiv.liftNormal_commutes _ _ (⟨y, hy⟩ : GroundTheory.LocalField.maximalAbelianExtension
      (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)))

theorem restrictHom_localSymbolAt_inl (v : InfinitePlace K.1) (a : K.1ˣ) :
    restrictHom (E := E) (localSymbolAt ι (.inl v) a) =
      infiniteLocalSymbol E.1 v (Units.map (algebraMap K.1 v.Completion : K.1 →* v.Completion) a) :=
  restrictHom_globalDecomp_of_infinite E (ι.inf v)
    (exists_eq_one_iff_mem_range_norm v (algebraMap K.1 v.Completion (a : K.1))).choose_spec

theorem finsum_char_localSymbolAt_eq (χ : Additive K.1.fixingSubgroup →ₜ+ QZ)
    (hχ : ∀ h : K.1.fixingSubgroup, (h : ℚ̄ ≃ₐ[ℚ] ℚ̄) ∈ E.1.fixingSubgroup → χ (Additive.ofMul h) = 0)
    (a : K.1ˣ) (g : K.1.fixingSubgroup)
    (hg : restrictHom (E := E) g = ideleSymbol K.1 E.1 (diagonal K.1 a)) :
    ∑ᶠ v : Place K.1, χ (Additive.ofMul (localSymbolAt ι v a)) = χ (Additive.ofMul g) := by
  classical
  set R := (restrictHom : K.1.fixingSubgroup →* (E.1 ≃ₐ[K.1] E.1)) with hR
  set χm : K.1.fixingSubgroup →* Multiplicative QZ :=
    AddMonoidHom.toMultiplicativeRight χ.toAddMonoidHom with hχm
  have hχm_apply : ∀ h, χ (Additive.ofMul h) = Multiplicative.toAdd (χm h) := fun _ ↦ rfl
  have hker : R.ker ≤ χm.ker := by
    intro h hh
    rw [hR, ker_restrictHom, Subgroup.mem_subgroupOf] at hh
    rw [MonoidHom.mem_ker, ← ofAdd_toAdd (χm h), ← hχm_apply, hχ h hh, ofAdd_zero]
  set χ' := R.liftOfSurjective restrictHom_surjective ⟨χm, hker⟩ with hχ'
  have hχ'R : ∀ h, χ' (R h) = χm h := fun h ↦
    R.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv restrictHom_surjective) ⟨χm, hker⟩ h
  have hfin : ∀ v, finiteProj v (diagonal K.1 a) =
      Units.map (algebraMap K.1 (v.adicCompletion K.1) : K.1 →* v.adicCompletion K.1) a := fun v ↦
    Units.ext (coe_finiteProj_diagonal v a)
  have hinf : ∀ w, infiniteProj w (diagonal K.1 a) =
      Units.map (algebraMap K.1 w.Completion : K.1 →* w.Completion) a := fun w ↦
    Units.ext (coe_infiniteProj_diagonal w a)
  have hF_inr : ∀ v, χ (Additive.ofMul (localSymbolAt ι (.inr v) a)) = Multiplicative.toAdd (χ' (localSymbol E.1 v (finiteProj v (diagonal K.1 a)))) := by
    intro v
    rw [hχm_apply, ← hχ'R, hR, restrictHom_localSymbolAt_inr, ← hfin]
  have hF_inl : ∀ w, χ (Additive.ofMul (localSymbolAt ι (.inl w) a)) = Multiplicative.toAdd (χ' (infiniteLocalSymbol E.1 w (infiniteProj w (diagonal K.1 a)))) := by
    intro w
    rw [hχm_apply, ← hχ'R, hR, restrictHom_localSymbolAt_inl, ← hinf]
  obtain ⟨S, hS⟩ : ∃ S : Finset (HeightOneSpectrum (𝓞 K.1)), Function.mulSupport (fun v ↦ localSymbol E.1 v (finiteProj v (diagonal K.1 a))) ⊆ S :=
    ⟨(hasFiniteMulSupport_localSymbol E.1 (diagonal K.1 a)).toFinset, fun v hv ↦
      (Set.Finite.mem_toFinset _).2 hv⟩
  have hψ : ideleSymbol K.1 E.1 (diagonal K.1 a) = (∏ v ∈ S, localSymbol E.1 v (finiteProj v (diagonal K.1 a))) *
      ∏ w, infiniteLocalSymbol E.1 w (infiniteProj w (diagonal K.1 a)) := by
    rw [ideleSymbol_apply, finprod_eq_prod_of_mulSupport_subset _ hS]
  have hsupp : Function.support (fun v : Place K.1 ↦ χ (Additive.ofMul (localSymbolAt ι v a))) ⊆
      (Finset.univ.disjSum S : Finset (Place K.1)) := by
    rintro (w | v) hv
    · exact Finset.inl_mem_disjSum.2 (Finset.mem_univ w)
    · refine Finset.inr_mem_disjSum.2 (hS ?_)
      intro h1
      apply hv
      change χ (Additive.ofMul (localSymbolAt ι (.inr v) a)) = 0
      rw [hF_inr]
      rw [show localSymbol E.1 v (finiteProj v (diagonal K.1 a)) = 1 from h1, map_one, toAdd_one]
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_disjSum, hχm_apply, ← hχ'R, hg, hψ, map_mul,
    toAdd_mul, map_prod χ', map_prod χ', toAdd_prod, toAdd_prod, add_comm]
  congr 1
  · exact Finset.sum_congr rfl fun v _ ↦ hF_inr v
  · exact Finset.sum_congr rfl fun w _ ↦ hF_inl w

end

end GroundTheory.ProfCoh
