import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HasConductorMulShift
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

open ValuativeRel Matrix IsLocalRing
open scoped Pointwise

noncomputable section
namespace GlobalTheory.LatPair
open SplitWeil

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}

theorem ite_mem_SB {X : Type*} [TopologicalSpace X] {p : X → Prop} [DecidablePred p] (h : IsClopen {x | p x})
    (hc : IsCompact {x | p x}) : (fun x => if p x then (1 : ℂ) else 0) ∈ SB X := by
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, HasCompactSupport.intro' hc h.1 fun x hx => if_neg hx⟩
  by_cases hx : p x
  · exact ⟨_, h.2, hx, fun y hy => (if_pos hy).trans (if_pos hx).symm⟩
  · exact ⟨_, h.compl.2, hx, fun y hy => (if_neg hy).trans (if_neg hx).symm⟩

variable [Fintype n] [Fintype n']

theorem isClopen_lattice (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] : IsClopen (L : Set (n → k)) := by
  classical
  haveI := t2Space k
  obtain ⟨g, rfl⟩ := exists_smul_lat (stdLat k n) L
  have h : ((g • stdLat k n : Submodule 𝒪[k] (n → k)) : Set (n → k)) =
      ⋂ i, (fun x => ((g⁻¹ : GL n k).val *ᵥ x) i) ⁻¹' (𝒪[k] : Set k) := by
    ext x
    simp only [SetLike.mem_coe, mem_smul_iff, mem_stdLat, Set.mem_iInter, Set.mem_preimage]
    rfl
  rw [h]
  refine isClopen_iInter_of_finite fun i => IsClopen.preimage ⟨(isCompact_int k).isClosed, isOpen_int k⟩ ?_
  exact (continuous_apply i).comp (continuous_const.matrix_mulVec continuous_id)

omit [Fintype n] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem maps_stdLat_iff {x : Matrix n n' k} :
    (∀ y ∈ stdLat k n', x *ᵥ y ∈ stdLat k n) ↔ ∀ i j, x i j ∈ 𝒪[k] := by
  classical
  simp only [mem_stdLat]
  refine ⟨fun h i j => ?_, fun h y hy i => sum_mem fun j _ => mul_mem (h i j) (hy j)⟩
  have := h (Pi.single j 1) (fun l => ?_) i
  · simpa using this
  · rw [Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]

theorem isClopen_isCompact_maps (S : Submodule 𝒪[k] (n' → k)) (L : Submodule 𝒪[k] (n → k)) [S.IsLattice k]
    [L.IsLattice k] : IsClopen {x : Matrix n n' k | ∀ y ∈ S, x *ᵥ y ∈ L} ∧
      IsCompact {x : Matrix n n' k | ∀ y ∈ S, x *ᵥ y ∈ L} := by
  classical
  haveI := t2Space k
  obtain ⟨g, rfl⟩ := exists_smul_lat (stdLat k n') S
  obtain ⟨h, rfl⟩ := exists_smul_lat (stdLat k n) L
  let K : Set (Matrix n n' k) := Set.univ.pi fun _ => Set.univ.pi fun _ => (𝒪[k] : Set k)
  have hKc : IsCompact K := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_int k
  have hKo : IsOpen K :=
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => isOpen_int k
  have e : {x : Matrix n n' k | ∀ y ∈ g • stdLat k n', x *ᵥ y ∈ h • stdLat k n} = sideMul g h ⁻¹' K := by
    ext x
    have h1 : sideMul g h x ∈ K ↔ ∀ i j, ((h⁻¹ : GL n k).val * x * g.val) i j ∈ 𝒪[k] :=
      ⟨fun H i j => H i trivial j trivial, fun H i _ j _ => H i j⟩
    rw [Set.mem_preimage, h1, ← maps_stdLat_iff, Set.mem_setOf_eq]
    simp only [mem_smul_iff, ← mulVec_mulVec]
    refine ⟨fun H y hy => H (g • y) (by simpa using hy), fun H y hy => ?_⟩
    have := H _ hy
    rwa [show g.val *ᵥ (g⁻¹ • y) = y from smul_inv_smul g y] at this
  rw [e]
  exact ⟨IsClopen.preimage ⟨hKc.isClosed, hKo⟩ (sideMul g h).continuous, (sideMul g h).isCompact_preimage.2 hKc⟩

theorem latInd_mem_SB (S : Submodule 𝒪[k] (n' → k)) (L : Submodule 𝒪[k] (n → k)) [S.IsLattice k] [L.IsLattice k] :
    latInd S L ∈ SB (Matrix n n' k) := by
  classical
  exact ite_mem_SB (isClopen_isCompact_maps S L).1 (isClopen_isCompact_maps S L).2

theorem isClopen_isCompact_mapsPair (P : Pair k n') (Q : Pair k n) :
    IsClopen {x : Matrix n n' k | Maps P Q x} ∧ IsCompact {x : Matrix n n' k | Maps P Q x} := by
  have e : {x : Matrix n n' k | Maps P Q x} = {x : Matrix n n' k | ∀ y ∈ P.ker, x *ᵥ y ∈ Q.ker} ∩
      (fun x : Matrix n n' k => x *ᵥ P.vec - Q.vec) ⁻¹' (Q.ker : Set (n → k)) := by
    ext x
    exact maps_iff_glue P.hasVal_vec Q.hasVal_vec
  have h2 := (isClopen_lattice Q.ker).preimage (f := fun x : Matrix n n' k => x *ᵥ P.vec - Q.vec)
    ((continuous_id.matrix_mulVec continuous_const).sub continuous_const)
  obtain ⟨h1, hc⟩ := isClopen_isCompact_maps P.ker Q.ker
  rw [e]
  exact ⟨h1.inter h2, hc.inter_right h2.1⟩

theorem phiOne_mem_SB (P : Pair k n') (Q : Pair k n) : phiOne P Q ∈ SB (Matrix n n' k) := by
  classical
  exact ite_mem_SB (isClopen_isCompact_mapsPair P Q).1 (isClopen_isCompact_mapsPair P Q).2

end GlobalTheory.LatPair
