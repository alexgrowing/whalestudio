import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TraceLevel

theorem apply_out_mk {L W : Type} [Group L] (H : Subgroup L) (ψ : L → W) (hψ : ∀ g, ∀ h ∈ H, ψ (g * h) = ψ g)
    (g : L) : ψ (QuotientGroup.mk g : L ⧸ H).out = ψ g := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [hh, hψ g h h.2]

theorem finsum_out_left {L W : Type} [Group L] [AddCommMonoid W] (H : Subgroup L) (ψ : L → W)
    (hψ : ∀ g, ∀ h ∈ H, ψ (g * h) = ψ g) (l : L) :
    ∑ᶠ q : L ⧸ H, ψ (l * q.out) = ∑ᶠ q : L ⧸ H, ψ q.out := by
  rw [← finsum_comp_equiv (MulAction.toPerm l : Equiv.Perm (L ⧸ H)) (f := fun q : L ⧸ H => ψ q.out)]
  congr 1
  funext q
  have : (MulAction.toPerm l : Equiv.Perm (L ⧸ H)) q = (QuotientGroup.mk (l * q.out) : L ⧸ H) := by
    rw [MulAction.toPerm_apply]
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  show ψ (l * q.out) = ψ ((MulAction.toPerm l : Equiv.Perm (L ⧸ H)) q).out
  rw [this, apply_out_mk H ψ hψ]

theorem mem_fixed_iff {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (H : Subgroup G) (v : V) : v ∈ fixed ρ H ↔ ∀ h ∈ H, ρ h v = v := by
  constructor
  · intro hv h hh
    have := hv ⟨h, hh⟩
    simpa using this
  · intro hv h
    show ρ (h : G) v = ((1 : H →* ℂˣ) h : ℂ) • v
    simpa using hv h h.2

theorem support_out_finite {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G)
    (hH : IsOpen (H : Set G)) (F : G → ℂ) (hF : HasCompactSupport F) :
    (Function.support fun q : G ⧸ H => F q.out).Finite := by
  haveI := QuotientGroup.discreteTopology hH
  refine ((HasCompactSupport.isCompact hF).image QuotientGroup.continuous_mk).finite_of_discrete.subset ?_
  intro q hq
  exact ⟨q.out, subset_tsupport _ hq, QuotientGroup.out_eq' q⟩

end GlobalTheory.TraceLevel

namespace GlobalTheory.TraceLevel

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem levOp_id_apply (ρ : Representation ℂ G V) (K H : Subgroup G) (F : G → ℂ)
    (hfin : (Function.support fun q : G ⧸ H => F q.out).Finite) (v : V) :
    levOp ρ K H F LinearMap.id v = ((H.relIndex K : ℕ) : ℂ)⁻¹ • ∑ᶠ q : G ⧸ H, F q.out • ρ q.out v := by
  unfold levOp
  rw [LinearMap.smul_apply]
  congr 1
  rw [finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (fun q hq => by
      rw [Set.Finite.coe_toFinset]
      exact Function.mem_support.2 fun h0 => (Function.mem_support.1 hq) (by simp [h0])),
    finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (fun q hq => by
      rw [Set.Finite.coe_toFinset]
      exact Function.mem_support.2 fun h0 => (Function.mem_support.1 hq) (by simp [h0])),
    LinearMap.sum_apply]
  simp

theorem levOp_mem_fixed (ρ : Representation ℂ G V) (K K₀ H : Subgroup G) (F : G → ℂ) (hF : IsHecke K₀ F)
    (hH : IsOpen (H : Set G)) (hle : H ≤ K₀) (v : V) (hv : v ∈ fixed ρ H) :
    levOp ρ K H F LinearMap.id v ∈ fixed ρ H := by
  have hfin := support_out_finite H hH F hF.1
  rw [mem_fixed_iff] at hv ⊢
  intro k hk
  rw [levOp_id_apply ρ K H F hfin, map_smul]
  congr 1
  have hfin' : (Function.support fun q : G ⧸ H => F q.out • ρ q.out v).Finite :=
    hfin.subset fun q hq => Function.mem_support.2 fun h0 => (Function.mem_support.1 hq) (by simp [h0])
  rw [map_finsum (ρ k) hfin']
  have := finsum_out_left H (fun g => F g • ρ g v) (fun g h hh => by
    rw [(hF.2 h (hle hh) g).2, map_mul, Module.End.mul_apply, hv h hh]) k
  rw [← this]
  congr 1
  funext q
  rw [map_smul, ← Module.End.mul_apply, ← map_mul, (hF.2 k (hle hk) q.out).1]

theorem twTr_level (ρ : Representation ℂ G V) (K K₀ K'' : Subgroup G) (F : G → ℂ) (hK''o : IsOpen (K'' : Set G))
    (hK : IsCompact (K : Set G)) (hle : K'' ≤ K₀) (hle' : K₀ ≤ K) (hF : IsHecke K₀ F)
    (hfd : FiniteDimensional ℂ (fixed ρ K'')) :
    twTr ρ K K'' F LinearMap.id = twTr ρ K K₀ F LinearMap.id := by
  have hK₀o : IsOpen (K₀ : Set G) := Subgroup.isOpen_mono hle hK''o
  have hc : K''.relIndex K ≠ 0 := by
    haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    have ho : IsOpen ((K''.subgroupOf K : Subgroup K) : Set K) := hK''o.preimage continuous_subtype_val
    haveI := Subgroup.quotient_finite_of_isOpen _ ho
    exact Subgroup.index_ne_zero_of_finite
  have hmul : K''.relIndex K₀ * K₀.relIndex K = K''.relIndex K :=
    Subgroup.relIndex_mul_relIndex (H := K'') (K := K₀) (L := K) hle hle'
  have hd : K''.relIndex K₀ ≠ 0 := left_ne_zero_of_mul (hmul ▸ hc)
  have hcard : Nat.card (↥K₀ ⧸ K''.subgroupOf K₀) ≠ 0 := hd
  haveI : Finite (↥K₀ ⧸ K''.subgroupOf K₀) := Nat.finite_of_card_ne_zero hcard
  letI := Fintype.ofFinite (↥K₀ ⧸ K''.subgroupOf K₀)
  set d : ℕ := K''.relIndex K₀ with hd_def
  obtain ⟨P, hPapp⟩ : ∃ P : V →ₗ[ℂ] V, ∀ v, P v =
      (d : ℂ)⁻¹ • ∑ k : ↥K₀ ⧸ K''.subgroupOf K₀, ρ ((k.out : K₀) : G) v :=
    ⟨(d : ℂ)⁻¹ • ∑ k : ↥K₀ ⧸ K''.subgroupOf K₀, ρ ((k.out : K₀) : G), fun v => by
      simp [LinearMap.sum_apply]⟩
  have hPfix : ∀ v ∈ fixed ρ K'', P v ∈ fixed ρ K₀ := by
    intro v hv
    rw [mem_fixed_iff] at hv ⊢
    intro k hk
    rw [hPapp, map_smul, map_sum]
    congr 1
    have := finsum_out_left (K''.subgroupOf K₀) (fun x : K₀ => ρ (x : G) v) (fun g h hh => by
      simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
      rw [hv _ (Subgroup.mem_subgroupOf.1 hh)]) ⟨k, hk⟩
    simp only [finsum_eq_sum_of_fintype, Subgroup.coe_mul, map_mul, Module.End.mul_apply] at this
    exact this
  have hPid : ∀ v ∈ fixed ρ K₀, P v = v := by
    intro v hv
    rw [mem_fixed_iff] at hv
    rw [hPapp, Finset.sum_congr rfl (fun k _ => hv _ (k.out).2), Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    have : (Fintype.card (↥K₀ ⧸ K''.subgroupOf K₀) : ℂ) = d := by
      rw [← Nat.card_eq_fintype_card]
      rfl
    rw [this, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hd), one_smul]
  have key : ∀ v ∈ fixed ρ K'', levOp ρ K K'' F LinearMap.id v = levOp ρ K K₀ F LinearMap.id (P v) := by
    intro v hv
    have hv' := (mem_fixed_iff ρ K'' v).1 hv
    have hfin'' := support_out_finite K'' hK''o F hF.1
    have hfin₀ := support_out_finite K₀ hK₀o F hF.1
    rw [levOp_id_apply ρ K K'' F hfin'', levOp_id_apply ρ K K₀ F hfin₀]
    have hR : ∀ a : G ⧸ K₀, F a.out • ρ a.out (P v) =
        (d : ℂ)⁻¹ • ∑ᶠ b : ↥K₀ ⧸ K''.subgroupOf K₀, F a.out • ρ (a.out * ((b.out : K₀) : G)) v := by
      intro a
      rw [hPapp, map_smul, map_sum, smul_comm, finsum_eq_sum_of_fintype, Finset.smul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro b _
      rw [map_mul, Module.End.mul_apply]
    simp_rw [hR]
    rw [← smul_finsum, smul_smul]
    have hL : ∑ᶠ q : G ⧸ K'', F q.out • ρ q.out v =
        ∑ᶠ a : G ⧸ K₀, ∑ᶠ b : ↥K₀ ⧸ K''.subgroupOf K₀, F a.out • ρ (a.out * ((b.out : K₀) : G)) v := by
      set e := Subgroup.quotientEquivProdOfLE hle
      rw [← finsum_comp_equiv e.symm]
      have hφ : ∀ g, ∀ h ∈ K'', (fun g => F g • ρ g v) (g * h) = (fun g => F g • ρ g v) g := fun g h hh => by
        simp only
        rw [(hF.2 h (hle hh) g).2, map_mul, Module.End.mul_apply, hv' h hh]
      have he : ∀ p : (G ⧸ K₀) × (↥K₀ ⧸ K''.subgroupOf K₀),
          e.symm p = (QuotientGroup.mk (p.1.out * ((p.2.out : K₀) : G)) : G ⧸ K'') := by
        rintro ⟨a, b⟩
        conv_lhs => rw [← QuotientGroup.out_eq' b]
        rfl
      have h2 : ∀ p : (G ⧸ K₀) × (↥K₀ ⧸ K''.subgroupOf K₀),
          F (e.symm p).out • ρ (e.symm p).out v = F p.1.out • ρ (p.1.out * ((p.2.out : K₀) : G)) v := by
        intro p
        rw [he p]
        have := apply_out_mk K'' (fun g => F g • ρ g v) hφ (p.1.out * ((p.2.out : K₀) : G))
        rw [this, (hF.2 _ (p.2.out).2 p.1.out).2]
      simp_rw [h2]
      rw [finsum_curry]
      refine (hfin₀.prod Set.finite_univ).subset ?_
      rintro ⟨a, b⟩ hp
      refine ⟨?_, Set.mem_univ _⟩
      exact Function.mem_support.2 fun h0 => (Function.mem_support.1 hp) (by simp [h0])
    rw [hL]
    congr 1
    rw [← hmul]
    push_cast
    rw [mul_inv, mul_comm]
  have hVle : fixed ρ K₀ ≤ fixed ρ K'' := by
    intro v hv
    rw [mem_fixed_iff] at hv ⊢
    exact fun h hh => hv h (hle hh)
  haveI : FiniteDimensional ℂ (fixed ρ K₀) := Submodule.finiteDimensional_of_le hVle
  have h'' : ∀ v ∈ fixed ρ K'', levOp ρ K K'' F LinearMap.id v ∈ fixed ρ K'' :=
    fun v hv => levOp_mem_fixed ρ K K₀ K'' F hF hK''o hle v hv
  have h0 : ∀ v ∈ fixed ρ K₀, levOp ρ K K₀ F LinearMap.id v ∈ fixed ρ K₀ :=
    fun v hv => levOp_mem_fixed ρ K K₀ K₀ F hF hK₀o le_rfl v hv
  unfold twTr
  rw [dif_pos h'', dif_pos h0]
  let Pr : fixed ρ K'' →ₗ[ℂ] fixed ρ K₀ :=
    (P.domRestrict (fixed ρ K'')).codRestrict (fixed ρ K₀) (fun v => hPfix v.1 v.2)
  let ι : fixed ρ K₀ →ₗ[ℂ] fixed ρ K'' := Submodule.inclusion hVle
  have h1 : (levOp ρ K K'' F LinearMap.id).restrict h'' =
      ι ∘ₗ (((levOp ρ K K₀ F LinearMap.id).restrict h0) ∘ₗ Pr) := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    show levOp ρ K K'' F LinearMap.id v = levOp ρ K K₀ F LinearMap.id (P v)
    exact key v v.2
  have h2 : Pr ∘ₗ ι = LinearMap.id := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    show P v = v
    exact hPid v v.2
  rw [h1, LinearMap.trace_comp_comm', LinearMap.comp_assoc, h2, LinearMap.comp_id]

end GlobalTheory.TraceLevel
