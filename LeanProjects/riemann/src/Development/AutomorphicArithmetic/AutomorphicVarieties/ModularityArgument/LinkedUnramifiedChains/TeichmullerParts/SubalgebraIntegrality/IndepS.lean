import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.StabilizerSubgroup

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open GlobalTheory.BCT.GlobLev GlobalTheory.SplitPts GroundTheory.Automorphic

namespace UpperTheory.V.Z.J.D

private theorem exists_avg {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (R : Representation ℂ G V)
    (K H : Subgroup G) (hfin : Finite (K ⧸ H.subgroupOf K)) :
    ∃ A : V →ₗ[ℂ] V, (∀ v, (∀ k ∈ K, R k v = v) → A v = v) ∧
      (∀ v, (∀ h ∈ H, R h v = v) → ∀ k ∈ K, R k (A v) = A v) ∧
      ∀ M : Submodule ℂ V, (∀ x, ∀ v ∈ M, R x v ∈ M) → ∀ v ∈ M, A v ∈ M := by
  classical
  letI := Fintype.ofFinite (K ⧸ H.subgroupOf K)
  have hc : (Fintype.card (K ⧸ H.subgroupOf K) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨(Fintype.card (K ⧸ H.subgroupOf K) : ℂ)⁻¹ • ∑ q : K ⧸ H.subgroupOf K, R ((q.out : K) : G), ?_, ?_, ?_⟩
  · intro v hv
    simp only [LinearMap.smul_apply, LinearMap.sum_apply]
    rw [Finset.sum_congr rfl fun q _ => hv _ (q.out : K).2]
    simp [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hc]
  · intro v hv k hk
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
    congr 1
    have key : ∀ q : K ⧸ H.subgroupOf K, R k (R ((q.out : K) : G) v) =
        R ((((⟨k, hk⟩ : K) • q).out : K) : G) v := fun q => by
      have e : (QuotientGroup.mk (((⟨k, hk⟩ : K) • q).out) : K ⧸ H.subgroupOf K) =
          QuotientGroup.mk ((⟨k, hk⟩ : K) * q.out) := by
        rw [QuotientGroup.out_eq']
        conv_lhs => rw [← QuotientGroup.out_eq' q]
        rfl
      have h1 := QuotientGroup.eq.1 e
      have h2 : ((((⟨k, hk⟩ : K) • q).out : K) : G)⁻¹ * (k * ((q.out : K) : G)) ∈ H := h1
      have h3 := hv _ h2
      have h4 : k * ((q.out : K) : G) = ((((⟨k, hk⟩ : K) • q).out : K) : G) *
          (((((⟨k, hk⟩ : K) • q).out : K) : G)⁻¹ * (k * ((q.out : K) : G))) := by group
      rw [← Module.End.mul_apply, ← map_mul, h4, map_mul, Module.End.mul_apply, h3]
    rw [Finset.sum_congr rfl fun q _ => key q]
    exact Equiv.sum_comp (MulAction.toPerm (⟨k, hk⟩ : K)) fun q : K ⧸ H.subgroupOf K => R ((q.out : K) : G) v
  · intro M hM v hv
    exact M.smul_mem _ (by
      simp only [LinearMap.sum_apply]
      exact M.sum_mem fun q _ => hM _ v hv)

private theorem is_compact_integral_level {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {S : Set (Pl E)} (hS : IsSection S) :
    IsCompact (globLev S (KL n) : Set (finU E n)) := by
  have hO : IsOpen (globLev S (KL n) : Set (finU E n)) := by
    rw [globLev_KL_eq hS]
    exact (AdelicGLn.isOpen_integralFiniteGL E n).preimage continuous_finPart
  refine IsCompact.of_isClosed_subset (isClosedEmbedding_finU.isCompact_preimage
    ((AdelicGLn.isCompact_integralFiniteGL E n).image continuous_finGL_ad))
    (Subgroup.isClosed_of_isOpen _ hO) fun x hx => ⟨finPart E n x, ?_, ?_⟩
  · rw [globLev_KL_eq hS] at hx
    exact hx
  · have h1 : GeneralLinearGroup.map (pInf E) ((x : UA E n) : GA E n) = 1 := x.2
    exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)

private theorem finite_quot {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {S : Set (Pl E)} (hS : IsSection S)
    {K' : ∀ w : Pl E, Subgroup (UL n w)} (hle : ∀ w, K' w ≤ KL n w) (U : Subgroup (finU E n)) (hU : IsOpen (U : Set (finU E n))) :
    Finite (globLev S K' ⧸ U.subgroupOf (globLev S K')) := by
  have hK : globLev S K' ≤ globLev S (KL n) := fun k hk =>
    (mem_globLev S _ k).2 fun w hw => hle w ((mem_globLev S _ k).1 hk w hw)
  haveI : CompactSpace (globLev S (KL n)) := isCompact_iff_compactSpace.1 (is_compact_integral_level hS)
  have h0 : Finite (globLev S (KL n) ⧸ U.subgroupOf (globLev S (KL n))) :=
    Subgroup.quotient_finite_of_isOpen _ (hU.preimage continuous_subtype_val)
  have h1 : U.relIndex (globLev S (KL n)) ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h2 : U.relIndex (globLev S K') ≠ 0 := mt (Subgroup.relIndex_eq_zero_of_le_right hK) h1
  haveI : (U.subgroupOf (globLev S K')).FiniteIndex := ⟨h2⟩
  exact Subgroup.finite_quotient_of_finiteIndex

private noncomputable def stabG {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (R : Representation ℂ G V) (v : V) : Subgroup G :=
  _root_.UpperTheory.Reformulated.B.StabilizerSubgroup.stabG R v

theorem indepS : IndepS := by
  intro E _ _ _ n S hS lam K' hK' J _ σ hd
  classical
  obtain ⟨h1, h2, -⟩ := hd
  have hst : ∀ j x, ∀ φ ∈ σ j, RU E n x φ ∈ σ j := fun j => (h1 j).1.stable
  intro i
  have hT : ∀ x, ∀ φ ∈ ⨆ (j) (_ : j ≠ i), σ j, RU E n x φ ∈ ⨆ (j) (_ : j ≠ i), σ j := by
    intro x φ hφ
    have hc : (⨆ (j) (_ : j ≠ i), σ j) ≤ (⨆ (j) (_ : j ≠ i), σ j).comap (RU E n x) :=
      iSup₂_le fun j hj y hy => Submodule.mem_comap.2 (le_iSup₂_of_le (f := fun j (_ : j ≠ i) => σ j) j hj le_rfl (hst j x y hy))
    exact hc hφ
  rcases (h1 i).1.irred (σ i ⊓ ⨆ (j) (_ : j ≠ i), σ j) inf_le_left
    (fun x φ hφ => ⟨hst i x φ hφ.1, hT x φ hφ.2⟩) with h0 | h0
  · exact disjoint_iff.2 h0
  exfalso
  obtain ⟨φ, hφ, hφ0⟩ := (Submodule.ne_bot_iff _).1 (h1 i).2.2
  have hφT : φ ∈ ⨆ (j) (_ : j ≠ i), σ j := (inf_eq_left.1 h0) hφ.1
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hφT
  have hfσ : ∀ j, f j ∈ σ j := fun j => by
    by_cases hj : j = i
    · have := hf j
      rw [iSup_neg (not_not.2 hj)] at this
      rw [(Submodule.mem_bot ℂ).1 this]
      exact Submodule.zero_mem _
    · have := hf j
      rwa [iSup_pos hj] at this
  have hfi : f i = 0 := by
    have := hf i
    rw [iSup_neg (not_not.2 rfl)] at this
    exact (Submodule.mem_bot ℂ).1 this
  have hsum' : ∑ j, f j = φ := by
    rw [← hsum]
    exact (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => Finsupp.notMem_support_iff.1 hj).symm
  have hopen : IsOpen ((⨅ j, stabG (RF E n) (f j) : Subgroup (finU E n)) : Set (finU E n)) := by
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun j => ((h1 j).1.aut _ (hfσ j)).level
  obtain ⟨A, hA1, hA2, hA3⟩ := exists_avg (RF E n) (globLev S K') (⨅ j, stabG (RF E n) (f j))
    (finite_quot hS (fun w => (hK'.1 w).2.1) _ hopen)
  have hφfix : ∀ k ∈ globLev S K', RF E n k φ = φ := fun k hk => GlobalTheory.LGrp.mem_fixed.1 hφ.2 k hk
  have hφA : A φ = φ := hA1 φ hφfix
  have ha : ∀ j, A (f j) ∈ σ j ⊓ fixed (RF E n) (globLev S K') := fun j =>
    ⟨hA3 (σ j) (fun x v hv => hst j _ v hv) _ (hfσ j),
      GlobalTheory.LGrp.mem_fixed.2 fun k hk => hA2 _ (fun h hh => (Subgroup.mem_iInf.1 hh j)) k hk⟩
  have hmem : φ ∈ ⨆ (j) (_ : j ≠ i), σ j ⊓ fixed (RF E n) (globLev S K') := by
    rw [← hφA, ← hsum', map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : j = i
    · rw [hj, hfi, map_zero]
      exact Submodule.zero_mem _
    · exact le_iSup₂_of_le (f := fun j (_ : j ≠ i) => σ j ⊓ fixed (RF E n) (globLev S K')) j hj le_rfl (ha j)
  exact hφ0 ((Submodule.disjoint_def.1 (h2 i)) φ hφ hmem)

end UpperTheory.V.Z.J.D
