import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLineAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixedOpenSubgroupGLw

noncomputable section

open GlobalTheory.BCT GlobalTheory.PRep Matrix
open UpperTheory.V.Z.Tf.GlobalTraceComparison

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

section Generic

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

private theorem rStab_ind (K' : Subgroup G) :
    rStab ((K' : Set G).indicator (1 : G → ℂ)) = K' := by
  classical
  ext k
  constructor
  · intro hk
    have h := hk 1
    simp only [one_mul] at h
    by_contra hn
    rw [Set.indicator_of_notMem (by simpa using hn), Set.indicator_of_mem (by simp [K'.one_mem])] at h
    simp at h
  · intro hk x
    by_cases hx : x ∈ K'
    · rw [Set.indicator_of_mem (show x * k ∈ (K' : Set G) from K'.mul_mem hx hk),
        Set.indicator_of_mem (show x ∈ (K' : Set G) from hx)]
      rfl
    · have hxk : x * k ∉ K' := fun h => hx (by simpa using K'.mul_mem h (K'.inv_mem hk))
      rw [Set.indicator_of_notMem (show x * k ∉ (K' : Set G) from hxk),
        Set.indicator_of_notMem (show x ∉ (K' : Set G) from hx)]

private theorem ind_inv (K' : Subgroup G) :
    (fun y : G => (K' : Set G).indicator (1 : G → ℂ) y⁻¹) = (K' : Set G).indicator (1 : G → ℂ) := by
  classical
  funext y
  by_cases hy : y ∈ K'
  · rw [Set.indicator_of_mem (show y⁻¹ ∈ (K' : Set G) from K'.inv_mem hy),
      Set.indicator_of_mem (show y ∈ (K' : Set G) from hy)]
    rfl
  · have : y⁻¹ ∉ K' := fun h => hy (by simpa using K'.inv_mem h)
    rw [Set.indicator_of_notMem (show y⁻¹ ∉ (K' : Set G) from this),
      Set.indicator_of_notMem (show y ∉ (K' : Set G) from hy)]

private theorem levOp_ind (ρ : Representation ℂ G V) (K K' : Subgroup G) (x : V) (hx : x ∈ fixed ρ K') :
    levOp ρ K K' ((K' : Set G).indicator (1 : G → ℂ)) LinearMap.id x = ((K'.relIndex K : ℕ) : ℂ)⁻¹ • x := by
  classical
  have hfx : ∀ h ∈ K', ρ h x = x := fun h hh => by simpa using hx ⟨h, hh⟩
  have hout : ∀ q : G ⧸ K', q.out ∈ K' ↔ q = (QuotientGroup.mk 1 : G ⧸ K') := by
    intro q
    constructor
    · intro h
      have h2 : ((q.out : G) : G ⧸ K') = QuotientGroup.mk 1 :=
        QuotientGroup.eq.2 (by simpa using K'.inv_mem h)
      rwa [QuotientGroup.out_eq'] at h2
    · rintro rfl
      have := QuotientGroup.mk_out_eq_mul K' (1 : G)
      obtain ⟨h, hh⟩ := this
      rw [hh]
      simpa using h.2
  unfold levOp
  rw [finsum_eq_single _ (QuotientGroup.mk 1 : G ⧸ K')]
  · rw [Set.indicator_of_mem (show (QuotientGroup.mk 1 : G ⧸ K').out ∈ (K' : Set G) from (hout _).2 rfl)]
    simp [hfx _ ((hout _).2 rfl)]
  · intro q hq
    rw [Set.indicator_of_notMem (show q.out ∉ (K' : Set G) from fun h => hq ((hout q).1 h))]
    simp

private theorem trc_ind_ne (ρ : Representation ℂ G V) (K K' : Subgroup G) (hle : K' ≤ K) (hi : K'.relIndex K ≠ 0)
    (hfd : FiniteDimensional ℂ (fixed ρ K')) (hne : fixed ρ K' ≠ ⊥) :
    trc ρ K ((K' : Set G).indicator (1 : G → ℂ)) ≠ 0 := by
  have hlev : K ⊓ rStab ((K' : Set G).indicator (1 : G → ℂ)) ⊓
      rStab (fun y : G => (K' : Set G).indicator (1 : G → ℂ) y⁻¹) = K' := by
    rw [ind_inv, rStab_ind, inf_assoc, inf_idem]
    exact inf_eq_right.2 hle
  unfold trc
  rw [hlev]
  have hc : ∀ v ∈ fixed ρ K', levOp ρ K K' ((K' : Set G).indicator (1 : G → ℂ)) LinearMap.id v ∈ fixed ρ K' := by
    intro v hv
    rw [levOp_ind ρ K K' v hv]
    exact Submodule.smul_mem _ _ hv
  have hr : (levOp ρ K K' ((K' : Set G).indicator (1 : G → ℂ)) LinearMap.id).restrict hc =
      ((K'.relIndex K : ℕ) : ℂ)⁻¹ • LinearMap.id := by
    ext v
    simp [LinearMap.restrict_apply, levOp_ind ρ K K' v v.2]
  unfold twTr
  rw [dif_pos hc, hr, map_smul, LinearMap.trace_id, smul_eq_mul]
  have hpos : Module.finrank ℂ (fixed ρ K') ≠ 0 := by
    intro h0
    exact hne (Submodule.finrank_eq_zero.1 h0)
  exact mul_ne_zero (inv_ne_zero (by exact_mod_cast hi)) (by exact_mod_cast hpos)

end Generic

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.levelFn :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.LevelFn := by
  intro E _ _ _ n w τ
  obtain ⟨ho, hc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  have hnt : Nontrivial τ.V := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have hs : Subsingleton (Subrepresentation τ.ρ) :=
      ⟨fun a b => by
        apply Subrepresentation.toSubmodule_injective
        exact Subsingleton.elim _ _⟩
    haveI := τ.irred
    exact not_subsingleton (Subrepresentation τ.ρ) hs
  obtain ⟨v, hv⟩ := exists_ne (0 : τ.V)
  let U : Subgroup (GLw n w) :=
    { carrier := {g | τ.ρ g v = v}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hb, ha]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul]
        simp }
  have hU : IsOpen (U : Set (GLw n w)) := τ.smooth v
  let K' : Subgroup (GLw n w) := U ⊓ GlobalTheory.LFun.KGL w n
  have hKo : IsOpen (K' : Set (GLw n w)) := hU.inter ho
  have hKc : IsCompact (K' : Set (GLw n w)) := hc.inter_left (U.isClosed_of_isOpen hU)
  have hle : K' ≤ GlobalTheory.LFun.KGL w n := inf_le_right
  have hfd : FiniteDimensional ℂ (fixed τ.ρ K') := finiteDimensional_fixed_openSubgroup_GLw E n w τ K' hKo
  have hne : fixed τ.ρ K' ≠ ⊥ := by
    intro hb
    have hm : v ∈ fixed τ.ρ K' := fun h => by
      have h1 : τ.ρ h v = v := h.2.1
      simpa using h1
    rw [hb] at hm
    exact hv ((Submodule.mem_bot ℂ).1 hm)
  have hi : K'.relIndex (GlobalTheory.LFun.KGL w n) ≠ 0 := by
    haveI : CompactSpace (GlobalTheory.LFun.KGL w n) := isCompact_iff_compactSpace.1 hc
    haveI : Finite ((GlobalTheory.LFun.KGL w n) ⧸ K'.subgroupOf (GlobalTheory.LFun.KGL w n)) :=
      Subgroup.quotient_finite_of_isOpen _ (hKo.preimage continuous_subtype_val)
    exact (Subgroup.finiteIndex_of_finite_quotient (H := K'.subgroupOf (GlobalTheory.LFun.KGL w n))).index_ne_zero
  refine ⟨(K' : Set (GLw n w)).indicator 1, ⟨K', hKo, hle, ?_, ?_⟩, UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.trc_ind_ne τ.ρ _ K' hle hi hfd hne⟩
  · exact HasCompactSupport.intro' hKc (K'.isClosed_of_isOpen hKo) fun x hx => Set.indicator_of_notMem hx _
  · classical
    intro k hk x
    have h1 : (k * x ∈ (K' : Set (GLw n w))) ↔ x ∈ (K' : Set (GLw n w)) := K'.mul_mem_cancel_left hk
    have h2 : (x * k ∈ (K' : Set (GLw n w))) ↔ x ∈ (K' : Set (GLw n w)) := K'.mul_mem_cancel_right hk
    show (K' : Set (GLw n w)).indicator 1 (k * x) = _ ∧ (K' : Set (GLw n w)).indicator 1 (x * k) = _
    rw [Set.indicator_apply, Set.indicator_apply, Set.indicator_apply]
    simp only [h1, h2, Pi.one_apply, and_self]
