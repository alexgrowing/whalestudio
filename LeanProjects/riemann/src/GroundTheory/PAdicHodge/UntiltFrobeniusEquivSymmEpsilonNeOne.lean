import Mathlib
import GroundTheory.PAdicHodge.BdRAlg
import GroundTheory.PAdicHodge.BdRSeries
import GroundTheory.PAdicHodge.BdRLattice
import GroundTheory.PAdicHodge.BdRGalois
import GroundTheory.PAdicHodge.AInfXi
import GroundTheory.PAdicHodge.TateCpTwist
set_option maxSynthPendingDepth 1

noncomputable section

open Ideal WittVector IsLocalRing

namespace GroundTheory.PAdicHodge

namespace IsPerfectoidField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [CharZero K]

instance instIsAdicCompleteMaximalIdealBdR :
    IsAdicComplete (maximalIdeal (BDeRhamPlus (normInteger K) p)) (BDeRhamPlus (normInteger K) p) :=
  isAdicComplete_maximalIdeal_bDeRhamPlus

end IsPerfectoidField

section Cp

variable {p : ℕ} [Fact p.Prime]

local notation "𝒪" => normInteger ℂ_[p]
local notation "𝒪♭" => PreTilt (normInteger ℂ_[p]) p
local notation "𝕎𝒪♭" => WittVector p (PreTilt (normInteger ℂ_[p]) p)
local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔪" => maximalIdeal (BDeRhamPlus (normInteger ℂ_[p]) p)
local notation "φi" => RingEquiv.symm (_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p)

variable (p) in

def muBdR (ε : PreTilt (normInteger ℂ_[p]) p) : BDeRhamPlus (normInteger ℂ_[p]) p :=
  wittToBDeRhamPlus 𝒪 p (AInf.mu ε)

theorem muBdR_eq (ε : 𝒪♭) : muBdR p ε = wittToBDeRhamPlus 𝒪 p (teichmuller p ε) - 1 := by
  rw [muBdR, AInf.mu, map_sub, map_one]

theorem muBdR_mem {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) : muBdR p ε ∈ 𝔪 := by
  rw [IsPerfectoidField.maximalIdeal_bDeRhamPlus, RingHom.mem_ker, muBdR,
    IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus, AInf.fontaineTheta_mu hε]
  rfl

def fontaineT (ε : PreTilt (normInteger ℂ_[p]) p) (hε : PreTilt.untilt ε = 1) :
    BDeRhamPlus (normInteger ℂ_[p]) p :=
  logOnePlus 𝔪 (muBdR p ε) (muBdR_mem hε)

theorem fontaineT_sub_sum_mem {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (n : ℕ) :
    fontaineT ε hε - ∑ i ∈ Finset.Ico 1 n, algebraMap ℚ 𝔹 ((-1) ^ (i + 1) / i) * muBdR p ε ^ i ∈
      𝔪 ^ n :=
  logOnePlus_sub_sum_mem _ n

theorem tendsto_fontaineT {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) :
    @Filter.Tendsto ℕ 𝔹
      (fun n => ∑ i ∈ Finset.range n,
        algebraMap ℚ 𝔹 (PowerSeries.coeff i (PowerSeries.log ℚ)) * muBdR p ε ^ i)
      Filter.atTop (@nhds 𝔹 (Ideal.adicTopology (maximalIdeal (BDeRhamPlus (normInteger ℂ_[p]) p))) (fontaineT ε hε)) :=
  tendsto_seriesEval _ _

theorem fontaineT_mem {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) : fontaineT ε hε ∈ 𝔪 :=
  logOnePlus_mem _

theorem isUnit_of_sub_one_mem {u : 𝔹} (hu : u - 1 ∈ 𝔪) : IsUnit u := by
  by_contra h
  have h1 : u ∈ 𝔪 := (IsLocalRing.mem_maximalIdeal u).2 h
  have h2 : (1 : 𝔹) ∈ 𝔪 := by
    have := sub_mem h1 hu
    rwa [sub_sub_cancel] at this
  exact (IsLocalRing.maximalIdeal.isMaximal 𝔹).ne_top ((Ideal.eq_top_iff_one _).2 h2)

theorem maximalIdeal_eq_span_fontaineT {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt (φi ε) ≠ 1) : 𝔪 = span {fontaineT ε hε} := by
  have hξ := AInf.ker_fontaineTheta_eq_span_xi hε hζ
  have h1 := IsPerfectoidField.maximalIdeal_bDeRhamPlus_eq_span hξ
  have hv : IsUnit (wittToBDeRhamPlus 𝒪 p ((WittVector.frobeniusEquiv p 𝒪♭).symm (AInf.mu ε))) := by
    by_contra h
    have h2 := (IsLocalRing.mem_maximalIdeal _).2 h
    rw [IsPerfectoidField.maximalIdeal_bDeRhamPlus, RingHom.mem_ker,
      IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus] at h2
    have h3 := AInf.fontaineTheta_frobeniusEquiv_symm_pow_mu ε 1
    rw [pow_one, pow_one] at h3
    rw [h3] at h2
    exact hζ (sub_eq_zero.1 (Subtype.ext h2))
  obtain ⟨u, hu1, ht⟩ := logOnePlus_eq_mul (muBdR_mem hε)
  have hu := isUnit_of_sub_one_mem hu1
  have hμ : muBdR p ε = wittToBDeRhamPlus 𝒪 p (AInf.xi ε) *
      wittToBDeRhamPlus 𝒪 p ((WittVector.frobeniusEquiv p 𝒪♭).symm (AInf.mu ε)) := by
    rw [muBdR, ← map_mul, ← AInf.mu_eq_xi_mul]
  rw [fontaineT, ht, hμ, mul_assoc, Ideal.span_singleton_mul_right_unit (hv.mul hu), h1]

theorem fontaineT_ne_zero {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt (φi ε) ≠ 1) : fontaineT ε hε ≠ 0 := by
  intro h
  have h1 := maximalIdeal_eq_span_fontaineT hε hζ
  rw [h, Ideal.span_singleton_eq_bot.2 rfl] at h1
  exact IsDiscreteValuationRing.not_a_field 𝔹 h1

theorem exists_isPrimitiveRoot_p : ∃ ζ : ℂ_[p], IsPrimitiveRoot ζ p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot ℂ_[p] p

variable (p) in

def rootSeq : ℕ → ℂ_[p]
  | 0 => 1
  | 1 => (exists_isPrimitiveRoot_p (p := p)).choose
  | (n + 2) => (IsAlgClosed.exists_pow_nat_eq (rootSeq (n + 1)) (Fact.out : p.Prime).pos).choose

theorem rootSeq_succ_pow (n : ℕ) : rootSeq p (n + 1) ^ p = rootSeq p n := by
  rcases n with _ | n
  · exact (exists_isPrimitiveRoot_p (p := p)).choose_spec.pow_eq_one
  · exact (IsAlgClosed.exists_pow_nat_eq (rootSeq p (n + 1)) (Fact.out : p.Prime).pos).choose_spec

theorem rootSeq_pow (n : ℕ) : rootSeq p n ^ p ^ n = 1 := by
  induction n with
  | zero => simp [rootSeq]
  | succ n ih => rw [pow_succ, pow_mul', rootSeq_succ_pow, ih]

theorem rootSeq_one_ne_one : rootSeq p 1 ≠ 1 :=
  (exists_isPrimitiveRoot_p (p := p)).choose_spec.ne_one (Fact.out : p.Prime).one_lt

theorem norm_rootSeq (n : ℕ) : ‖rootSeq p n‖ = 1 := by
  have h := congrArg norm (rootSeq_pow (p := p) n)
  rw [norm_pow, norm_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)).1 h

variable (p) in

def rootSeqInt (n : ℕ) : normInteger ℂ_[p] :=
  ⟨rootSeq p n, mem_normInteger.2 (norm_rootSeq n).le⟩

theorem rootSeqInt_succ_pow (n : ℕ) : rootSeqInt p (n + 1) ^ p = rootSeqInt p n :=
  Subtype.ext (by simp [rootSeqInt, rootSeq_succ_pow])

variable (p) in

def epsilon : PreTilt (normInteger ℂ_[p]) p :=
  IsPerfectoidField.ofCompatible p (rootSeqInt p) rootSeqInt_succ_pow

theorem untilt_epsilon : PreTilt.untilt (epsilon p) = 1 := by
  rw [epsilon, IsPerfectoidField.untilt_ofCompatible]
  exact Subtype.ext (by simp [rootSeqInt, rootSeq])

theorem untilt_frobeniusEquiv_symm_epsilon_ne_one : PreTilt.untilt (φi (epsilon p)) ≠ 1 := by
  rw [epsilon, AInf.frobeniusEquiv_symm_ofCompatible, IsPerfectoidField.untilt_ofCompatible]
  intro h
  exact rootSeq_one_ne_one (congrArg Subtype.val h)

variable (p) in

def tBdR : BDeRhamPlus (normInteger ℂ_[p]) p := fontaineT (epsilon p) untilt_epsilon

theorem maximalIdeal_eq_span_tBdR : 𝔪 = span {tBdR p} :=
  maximalIdeal_eq_span_fontaineT untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one

theorem irreducible_tBdR : Irreducible (tBdR p) := by
  exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 maximalIdeal_eq_span_tBdR

end Cp

end GroundTheory.PAdicHodge
