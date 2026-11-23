import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.MemUniformizerHermitianIdeal
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FirstStatementA

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory Topology
  Filter
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem isCompact_span_range {ι M : Type} [Fintype ι] [AddCommGroup M] [Module (Fv F v) M]
    [TopologicalSpace M] [ContinuousAdd M] [ContinuousSMul (Fv F v) M] (w : ι → M) :
    IsCompact ((Submodule.span (v.adicCompletionIntegers F) (Set.range w) :
      Submodule (v.adicCompletionIntegers F) M) : Set M) := by
  have : CompactSpace (v.adicCompletionIntegers F) :=
    isCompact_iff_compactSpace.mp (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v)
  have hc : Continuous (fun c : ι → v.adicCompletionIntegers F => ∑ i, ((c i : Fv F v)) • w i) :=
    continuous_finsetSum _ fun i _ =>
      (continuous_subtype_val.comp (continuous_apply i)).smul continuous_const
  have e : ((Submodule.span (v.adicCompletionIntegers F) (Set.range w) :
      Submodule (v.adicCompletionIntegers F) M) : Set M) =
      Set.range (fun c : ι → v.adicCompletionIntegers F => ∑ i, ((c i : Fv F v)) • w i) := by
    ext x
    rw [SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun]
    rfl
  rw [e]
  exact isCompact_range hc

theorem oEv_eq_span : OEv (E := E) v = ((Submodule.span (v.adicCompletionIntegers F)
    (Set.range (fun i => inclR (F := F) (Fv F v) ((RingOfIntegers.basis E i : 𝓞 E) : E)))) :
      Set (Fv F v ⊗[F] E)) := by
  unfold OEv
  congr 1
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, -, rfl⟩
    have hx := congrArg (algebraMap (𝓞 E) E) ((RingOfIntegers.basis E).sum_repr x)
    rw [map_sum] at hx
    simp only [map_zsmul] at hx
    show inclR (F := F) (Fv F v) (algebraMap (𝓞 E) E x) ∈ _
    rw [← hx, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_zsmul]
    exact zsmul_mem (Submodule.subset_span (Set.mem_range_self i)) _
  · apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨_, Set.mem_univ _, rfl⟩

theorem isCompact_oEv : IsCompact (OEv (E := E) v) := by
  rw [oEv_eq_span]
  exact isCompact_span_range v _

theorem isOpen_oEv : IsOpen (OEv (E := E) v) := by
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  set b := Module.finBasis F E with hb
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image b)
  have hyb : ∀ k, IsIntegral ℤ (y • b k) := fun k =>
    hy _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
  set c : Fv F v := algebraMap F (Fv F v) (y : F) with hcdef
  have hc : c ≠ 0 := by
    rw [hcdef, ne_eq, map_eq_zero_iff _ (algebraMap F (Fv F v)).injective]
    exact_mod_cast hy0
  set W : Set (Fv F v ⊗[F] E) := ⋂ k, (fun z => PI.VolStabSW.PositiveNearLattice.crd b (Fv F v) z k * c⁻¹) ⁻¹'
    (v.adicCompletionIntegers F : Set (Fv F v)) with hWdef
  have hWo : IsOpen W := isOpen_iInter_of_finite fun k =>
    (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers v).preimage
      ((PI.VolStabSW.PositiveNearLattice.continuous_crd b (Fv F v) k).mul continuous_const)
  have hW0 : (0 : Fv F v ⊗[F] E) ∈ W := by
    simp only [hWdef, Set.mem_iInter, Set.mem_preimage]
    intro k
    simp [PI.VolStabSW.PositiveNearLattice.crd]
  have hWsub : W ⊆ OEv (E := E) v := by
    intro z hz
    simp only [hWdef, Set.mem_iInter, Set.mem_preimage] at hz
    rw [PI.VolStabSW.PositiveNearLattice.eq_sum_crd b (Fv F v) z]
    unfold OEv
    refine Submodule.sum_mem _ fun k _ => ?_
    have e1 : PI.VolStabSW.PositiveNearLattice.crd b (Fv F v) z k • ((1 : Fv F v) ⊗ₜ[F] b k) =
        (PI.VolStabSW.PositiveNearLattice.crd b (Fv F v) z k * c⁻¹) • inclR (F := F) (Fv F v) (y • b k) := by
      have e2 : inclR (F := F) (Fv F v) (y • b k) = c • ((1 : Fv F v) ⊗ₜ[F] b k) := by
        show (1 : Fv F v) ⊗ₜ[F] (y • b k) = c • ((1 : Fv F v) ⊗ₜ[F] b k)
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, hcdef, Algebra.algebraMap_eq_smul_one,
          TensorProduct.smul_tmul, Int.cast_smul_eq_zsmul]
      rw [e2, smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]
    rw [e1]
    have hgen : inclR (F := F) (Fv F v) (y • b k) ∈ Submodule.span (v.adicCompletionIntegers F)
        ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) :=
      Submodule.subset_span ⟨(⟨y • b k, hyb k⟩ : 𝓞 E), Set.mem_univ _, rfl⟩
    exact Submodule.smul_mem _ (⟨_, hz k⟩ : v.adicCompletionIntegers F) hgen
  have hP : ((Submodule.span (v.adicCompletionIntegers F)
      ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)).toAddSubgroup :
        Set (Fv F v ⊗[F] E)) ∈ 𝓝 (0 : Fv F v ⊗[F] E) :=
    Filter.mem_of_superset (hWo.mem_nhds hW0) hWsub
  exact AddSubgroup.isOpen_of_mem_nhds _ hP

theorem hermOC_holds (σ : E →ₐ[F] E) (a : ℕ) : HermOC σ v a := by
  have := PI.VolStabSW.locallyCompact_Fv F v
  set S : Set (Fin a → Fin a → Fv F v ⊗[F] E) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => OEv (E := E) v with hS
  have hSe : (hermOE σ v a : Set (HermR (Fv F v) σ a)) = Subtype.val ⁻¹' S := by
    ext z
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
  have hc : Continuous (fun z : HermR (Fv F v) σ a => (z : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))) :=
    continuous_subtype_val
  constructor
  · rw [hSe]
    exact IsOpen.preimage hc (isOpen_set_pi Set.finite_univ fun _ _ =>
      isOpen_set_pi Set.finite_univ fun _ _ => isOpen_oEv v)
  · rw [hSe]
    exact (PI.VolStabSW.isClosed_HermR (Fv F v) σ a).isClosedEmbedding_subtypeVal.isCompact_preimage
      (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_oEv v)

variable {n : ℕ} (Λ : Set (Fin n → E))

theorem ratV_add (x y : Fin n → E) :
    ratV (F := F) (Fv F v) (x + y) = ratV (F := F) (Fv F v) x + ratV (F := F) (Fv F v) y := by
  funext i
  simp [ratV, map_add]

theorem ratV_zsmul (c : ℤ) (x : Fin n → E) :
    ratV (F := F) (Fv F v) (c • x) = c • ratV (F := F) (Fv F v) x := by
  funext i
  simp [ratV]

theorem ratV_zero : ratV (F := F) (Fv F v) (0 : Fin n → E) = 0 := by
  funext i
  simp [ratV]

theorem isCompact_latLoc
    (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) :
    IsCompact (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by
  obtain ⟨L, hLat, rfl⟩ := hL
  have hfg : (L.restrictScalars ℤ).FG := hLat.fg.restrictScalars
  obtain ⟨s, hs⟩ := hfg
  have e : latLoc (E := E) v (L : Set (Fin n → E)) = Submodule.span (v.adicCompletionIntegers F)
      (Set.range (fun x : s => ratV (F := F) (Fv F v) (x : Fin n → E))) := by
    apply le_antisymm
    · unfold latLoc
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ Submodule.span ℤ (s : Set (Fin n → E)) := by
        rw [hs]
        exact hx
      clear hx
      induction hx' using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩
      | zero =>
        rw [ratV_zero]
        exact Submodule.zero_mem _
      | add y z _ _ hy hz =>
        rw [ratV_add]
        exact Submodule.add_mem _ hy hz
      | smul c y _ hy =>
        rw [ratV_zsmul]
        exact zsmul_mem hy c
    · rw [Submodule.span_le]
      rintro _ ⟨⟨x, hx⟩, rfl⟩
      have hxL : x ∈ L := by
        have : x ∈ L.restrictScalars ℤ := by
          rw [← hs]
          exact Submodule.subset_span hx
        exact this
      exact Submodule.subset_span ⟨x, hxL, rfl⟩
  rw [e]
  exact isCompact_span_range v _

theorem exists_int_smul_mem (L : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E)
    (hx : x ∈ Submodule.span E (L : Set (Fin n → E))) : ∃ m : ℤ, m ≠ 0 ∧ m • x ∈ L :=
  _root_.UpperTheory.Reformulated.B.FirstStatementA.main L x hx

theorem isOpen_latLoc
    (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) :
    IsOpen (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by
  classical
  obtain ⟨L, hLat, rfl⟩ := hL
  have hsp := hLat.span_eq_top
  have hm : ∀ i : Fin n, ∃ m : ℤ, m ≠ 0 ∧ m • (Pi.single i (1 : E) : Fin n → E) ∈ L := fun i =>
    exists_int_smul_mem L _ (by rw [hsp]; exact Submodule.mem_top)
  choose m hm0 hmL using hm
  set N : ℤ := ∏ i, m i with hNdef
  have hN0 : N ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hm0 i
  have hNL : ∀ i, N • (Pi.single i (1 : E) : Fin n → E) ∈ L := by
    intro i
    have e : N = (∏ j ∈ Finset.univ.erase i, m j) * m i :=
      (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
    rw [e, mul_smul]
    exact zsmul_mem (hmL i) _
  set c : Fv F v := algebraMap F (Fv F v) (N : F) with hcdef
  have hc : c ≠ 0 := by
    rw [hcdef, ne_eq, map_eq_zero_iff _ (algebraMap F (Fv F v)).injective]
    exact_mod_cast hN0
  have hkey : ∀ i, ∀ o ∈ OEv (E := E) v, c • (Pi.single i o : Fin n → Fv F v ⊗[F] E) ∈
      latLoc (E := E) v (L : Set (Fin n → E)) := by
    intro i o ho
    unfold OEv at ho
    rw [SetLike.mem_coe] at ho
    induction ho using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, -, rfl⟩ := hy
      have hxL : (x : E) • (N • (Pi.single i (1 : E) : Fin n → E)) ∈ L := by
        have h := L.smul_mem x (hNL i)
        rwa [← algebraMap_smul E x] at h
      have e : c • (Pi.single i (inclR (F := F) (Fv F v) (x : E)) : Fin n → Fv F v ⊗[F] E) =
          ratV (F := F) (Fv F v) ((x : E) • (N • (Pi.single i (1 : E) : Fin n → E))) := by
        funext j
        by_cases hij : j = i
        · subst hij
          simp only [Pi.smul_apply, Pi.single_eq_same, ratV]
          show c • ((1 : Fv F v) ⊗ₜ[F] (x : E)) = (1 : Fv F v) ⊗ₜ[F] ((x : E) • (N • (1 : E)))
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, hcdef, Algebra.algebraMap_eq_smul_one,
            TensorProduct.smul_tmul]
          congr 1
          rw [Algebra.smul_def, map_intCast, zsmul_eq_mul, mul_one, smul_eq_mul, mul_comm]
        · simp [ratV, hij, inclR]
      rw [e]
      exact Submodule.subset_span ⟨_, hxL, rfl⟩
    | zero => simp
    | add y z _ _ hy hz =>
      rw [Pi.single_add, smul_add]
      exact Submodule.add_mem _ hy hz
    | smul r y _ hy =>
      have e : c • (Pi.single i (r • y) : Fin n → Fv F v ⊗[F] E) =
          r • (c • (Pi.single i y : Fin n → Fv F v ⊗[F] E)) := by
        rw [Pi.single_smul', smul_comm]
      rw [e]
      exact Submodule.smul_mem _ r hy
  set W : Set (Fin n → Fv F v ⊗[F] E) := ⋂ i, (fun y : Fin n → Fv F v ⊗[F] E => c⁻¹ • y i) ⁻¹'
    OEv (E := E) v with hWdef
  have hWo : IsOpen W := isOpen_iInter_of_finite fun i =>
    (isOpen_oEv v).preimage ((continuous_apply i).const_smul c⁻¹)
  have hW0 : (0 : Fin n → Fv F v ⊗[F] E) ∈ W := by
    simp only [hWdef, Set.mem_iInter, Set.mem_preimage, Pi.zero_apply, smul_zero]
    exact fun _ => oEv_zero v
  have hWsub : W ⊆ latLoc (E := E) v (L : Set (Fin n → E)) := by
    intro y hy
    simp only [hWdef, Set.mem_iInter, Set.mem_preimage] at hy
    have e : y = ∑ i, c • (Pi.single i (c⁻¹ • y i) : Fin n → Fv F v ⊗[F] E) := by
      conv_lhs => rw [← Finset.univ_sum_single y]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Pi.single_smul', smul_smul, mul_inv_cancel₀ hc, one_smul]
    rw [e]
    exact Submodule.sum_mem _ fun i _ => hkey i _ (hy i)
  exact AddSubgroup.isOpen_of_mem_nhds (latLoc (E := E) v (L : Set (Fin n → E))).toAddSubgroup
    (Filter.mem_of_superset (hWo.mem_nhds hW0) hWsub)

theorem lamOC_holds (a : ℕ) : LamOC v Λ a := by
  intro hL
  have e : LamT v Λ a = Set.pi Set.univ fun _ => (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by
    ext X
    exact ⟨fun h i _ => h i, fun h i => h i trivial⟩
  rw [e]
  exact ⟨isOpen_set_pi Set.finite_univ fun _ _ => isOpen_latLoc v Λ hL,
    isCompact_univ_pi fun _ => isCompact_latLoc v Λ hL⟩

end PI.OmLocU
