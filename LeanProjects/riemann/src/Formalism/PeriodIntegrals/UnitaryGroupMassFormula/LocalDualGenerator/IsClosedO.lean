import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.FpDualUnram

noncomputable section

open ValuativeRel IsLocalRing

namespace PI.LocDualGen.FpU

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (l : ℕ) [Fact l.Prime] [Algebra ℚ_[l] K]

theorem t2 : T2Space K := by
  rw [IsTopologicalAddGroup.t2Space_iff_zero_closed, ← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hx0 : x ≠ 0 := hx
  have hv : valuation K x ≠ 0 := (Valuation.ne_zero_iff _).2 hx0
  rw [IsValuativeTopology.mem_nhds_iff]
  refine ⟨Units.mk0 _ hv, ?_⟩
  rintro _ ⟨z, hz, rfl⟩ h0
  have hz' : valuation K z < valuation K x := hz
  have h0' : x + z = 0 := h0
  have : z = -x := by linear_combination h0'
  rw [this, Valuation.map_neg] at hz'
  exact lt_irrefl _ hz'

theorem isClosed_O : IsClosed ((𝒪[K] : Set K)) := by
  haveI : T2Space K := t2 (K := K)
  exact (IsNonarchimedeanLocalField.isCompact_closedBall K 1).isClosed

theorem iota_mem (hcont : Continuous (algebraMap ℚ_[l] K)) (a : ℤ_[l]) :
    algebraMap ℚ_[l] K (a : ℚ_[l]) ∈ 𝒪[K] := by
  have hcl : IsClosed {a : ℤ_[l] | algebraMap ℚ_[l] K (a : ℚ_[l]) ∈ 𝒪[K]} :=
    (isClosed_O (K := K)).preimage (hcont.comp continuous_subtype_val)
  refine PadicInt.denseRange_intCast.induction_on a hcl ?_
  intro n
  simp only [Set.mem_setOf_eq, PadicInt.coe_intCast, map_intCast]
  exact intCast_mem _ n

def iotaR (hcont : Continuous (algebraMap ℚ_[l] K)) : ℤ_[l] →+* 𝒪[K] :=
  ((algebraMap ℚ_[l] K).comp (PadicInt.Coe.ringHom (p := l))).codRestrict 𝒪[K]
    (fun a => iota_mem K l hcont a)

theorem iotaR_coe (hcont : Continuous (algebraMap ℚ_[l] K)) (a : ℤ_[l]) :
    ((iotaR K l hcont a : 𝒪[K]) : K) = algebraMap ℚ_[l] K (a : ℚ_[l]) := rfl

theorem charP_res (huni : Irreducible ((l : ℕ) : 𝒪[K])) : CharP 𝓀[K] l := by
  rw [CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime), ← map_natCast (residue 𝒪[K]) l,
    IsLocalRing.residue_eq_zero_iff]
  exact (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 huni.not_isUnit)

theorem repr_sum {ι R M : Type*} [Fintype ι] [CommRing R] [AddCommGroup M] [Module R M]
    (b : Module.Basis ι R M) (c : ι → R) (i : ι) : b.repr (∑ j, c j • b j) i = c i := by
  exact congrFun (b.repr_sum_self c) i

section Res

variable [CharP 𝓀[K] l]

abbrev algRes : Algebra (ZMod l) 𝓀[K] := ZMod.algebra _ l

attribute [local instance] algRes

theorem res_iotaR (hcont : Continuous (algebraMap ℚ_[l] K)) (a : ℤ_[l]) :
    residue 𝒪[K] (iotaR K l hcont a) = algebraMap (ZMod l) 𝓀[K] (PadicInt.toZMod a) := by
  obtain ⟨-, h⟩ := PadicInt.zmodRepr_spec a
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h
  obtain ⟨b, hb⟩ := h
  have ha : a = ((a.zmodRepr : ℕ) : ℤ_[l]) + b * (l : ℤ_[l]) := by rw [hb]; ring
  rw [ha]
  simp [map_natCast, CharP.cast_eq_zero]

abbrev fdim : ℕ := Module.finrank (ZMod l) 𝓀[K]

def bb : Module.Basis (Fin (fdim K l)) (ZMod l) 𝓀[K] := Module.finBasis (ZMod l) 𝓀[K]

def blift (i : Fin (fdim K l)) : 𝒪[K] := (residue_surjective (bb K l i)).choose

theorem res_blift (i : Fin (fdim K l)) : residue 𝒪[K] (blift K l i) = bb K l i := by
  exact (residue_surjective (bb K l i)).choose_spec

def Phi (hcont : Continuous (algebraMap ℚ_[l] K)) (c : Fin (fdim K l) → ℤ_[l]) : 𝒪[K] :=
  ∑ i, iotaR K l hcont (c i) * blift K l i

theorem Phi_coe (hcont : Continuous (algebraMap ℚ_[l] K)) (c : Fin (fdim K l) → ℤ_[l]) :
    ((Phi K l hcont c : 𝒪[K]) : K) = ∑ i, algebraMap ℚ_[l] K (c i : ℚ_[l]) * (blift K l i : K) := by
  unfold Phi
  push_cast
  simp only [iotaR_coe]

theorem Phi_add (hcont : Continuous (algebraMap ℚ_[l] K)) (c c' : Fin (fdim K l) → ℤ_[l]) (s : ℤ_[l]) :
    Phi K l hcont (c + s • c') = Phi K l hcont c + iotaR K l hcont s * Phi K l hcont c' := by
  simp only [Phi, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

theorem res_Phi (hcont : Continuous (algebraMap ℚ_[l] K)) (c : Fin (fdim K l) → ℤ_[l]) :
    residue 𝒪[K] (Phi K l hcont c) = ∑ i, PadicInt.toZMod (c i) • bb K l i := by
  simp only [Phi, map_sum, map_mul, res_iotaR, res_blift, Algebra.smul_def]

theorem one_step (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K]))
    (x : 𝒪[K]) : ∃ c, ∃ y : 𝒪[K], x = Phi K l hcont c + (l : 𝒪[K]) * y := by
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  set r := (bb K l).repr (residue 𝒪[K] x) with hr
  refine ?_
  have hc : residue 𝒪[K] (Phi K l hcont (fun i => ((r i).val : ℤ_[l]))) = residue 𝒪[K] x := by
    rw [res_Phi]
    have h1 : ∀ i, PadicInt.toZMod (((r i).val : ℕ) : ℤ_[l]) = r i := fun i => by
      rw [map_natCast, ZMod.natCast_zmod_val]
    simp_rw [h1]
    exact (bb K l).sum_repr (residue 𝒪[K] x)
  have hm : x - Phi K l hcont (fun i => ((r i).val : ℤ_[l])) ∈ maximalIdeal 𝒪[K] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hc, sub_self]
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 huni,
    Ideal.mem_span_singleton'] at hm
  obtain ⟨y, hy⟩ := hm
  exact ⟨_, y, by rw [mul_comm, hy]; ring⟩

theorem n_step (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K]))
    (j : ℕ) (x : 𝒪[K]) : ∃ c, ∃ y : 𝒪[K], x = Phi K l hcont c + (l : 𝒪[K]) ^ j * y := by
  induction j with
  | zero => exact ⟨0, x, by simp [Phi]⟩
  | succ j ih =>
    obtain ⟨c, y, hxy⟩ := ih
    obtain ⟨c', y', hy⟩ := one_step K l hcont huni y
    refine ⟨c + ((l : ℤ_[l]) ^ j) • c', y', ?_⟩
    rw [Phi_add, hxy, hy]
    simp only [map_pow, map_natCast]
    ring

theorem span (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K]))
    (x : 𝒪[K]) : ∃ c, x = Phi K l hcont c := by
  haveI : T2Space K := t2 (K := K)
  choose c y hxy using fun j => n_step K l hcont huni j x
  let F : (Fin (fdim K l) → ℤ_[l]) → K := fun c => ((Phi K l hcont c : 𝒪[K]) : K)
  have hF : Continuous F := by
    have : F = fun c => ∑ i, algebraMap ℚ_[l] K (c i : ℚ_[l]) * (blift K l i : K) := by
      funext c
      exact Phi_coe K l hcont c
    rw [this]
    refine continuous_finset_sum _ (fun i _ => ?_)
    exact (hcont.comp (continuous_subtype_val.comp (continuous_apply i))).mul continuous_const
  have hcl : IsClosed (Set.range F) := (isCompact_range hF).isClosed
  have h0 : Filter.Tendsto (fun j => (l : K) ^ j * (y j : K)) Filter.atTop (nhds 0) := by
    have hp : Filter.Tendsto (fun j => (l : ℚ_[l]) ^ j) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one
    have hp' : Filter.Tendsto (fun j => (l : K) ^ j) Filter.atTop (nhds 0) := by
      have := (hcont.tendsto 0).comp hp
      simpa [Function.comp_def, map_pow, map_natCast] using this
    rw [(IsValuativeTopology.hasBasis_nhds_zero K).tendsto_right_iff] at hp' ⊢
    intro γ _
    filter_upwards [hp' γ trivial] with j hj
    have hj' : valuation K ((l : K) ^ j) < γ := hj
    show valuation K ((l : K) ^ j * (y j : K)) < γ
    rw [map_mul]
    have hy1 : valuation K (y j : K) ≤ 1 := (Valuation.mem_integer_iff _ _).1 (y j).2
    calc valuation K ((l : K) ^ j) * valuation K (y j : K) ≤ valuation K ((l : K) ^ j) * 1 :=
          by gcongr
      _ = valuation K ((l : K) ^ j) := mul_one _
      _ < _ := hj'
  have heq : (fun j => F (c j)) = fun j => (x : K) - (l : K) ^ j * (y j : K) := by
    funext j
    have := congrArg (fun z : 𝒪[K] => (z : K)) (hxy j)
    push_cast at this
    simp only [F]
    rw [this]
    ring
  have hlim : Filter.Tendsto (fun j => F (c j)) Filter.atTop (nhds (x : K)) := by
    rw [heq]
    simpa using (tendsto_const_nhds (x := (x : K))).sub h0
  obtain ⟨c0, hc0⟩ := hcl.mem_of_tendsto hlim (Filter.Eventually.of_forall fun j => ⟨c j, rfl⟩)
  exact ⟨c0, Subtype.ext hc0.symm⟩

end Res

end PI.LocDualGen.FpU
