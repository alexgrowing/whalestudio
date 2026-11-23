import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfInAMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocF
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTateEndomorphismUniqueStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.AinfK GroundTheory.LocalField.FormalGroup GlobalTheory.AcrisK GlobalTheory.Prism

namespace GlobalTheory.PZ.TiltHyps

theorem two_le_resCard {l : ℕ} [Fact l.Prime] (K : FinExt l) : 2 ≤ resCard K := by
  unfold resCard
  haveI := K.2
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    Module.Finite.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).injective
  have : 0 < Module.finrank ℚ_[l] ↥(K0 K) := Module.finrank_pos
  calc 2 ≤ l := (Fact.out : l.Prime).two_le
    _ = l ^ 1 := (pow_one l).symm
    _ ≤ _ := Nat.pow_le_pow_right (Fact.out : l.Prime).pos this

theorem norm_le_one_of_lt {l : ℕ} [Fact l.Prime] {c w : ℂ_[l]} {q : ℕ} (hq : 2 ≤ q) (hc : ‖c‖ ≤ 1)
    (h : ‖c * w + w ^ q‖ ≤ 1) : ‖w‖ ≤ 1 := by
  by_contra hw
  push_neg at hw
  have e : w ^ q = (c * w + w ^ q) + (-(c * w)) := by ring
  have h1 : ‖w ^ q‖ ≤ max ‖c * w + w ^ q‖ ‖-(c * w)‖ := by
    have := IsUltrametricDist.norm_add_le_max (c * w + w ^ q) (-(c * w))
    rwa [← e] at this
  have h2 : ‖-(c * w)‖ ≤ ‖w‖ := by
    rw [norm_neg, norm_mul]; nlinarith [norm_nonneg w, norm_nonneg c]
  have h3 : ‖w‖ ^ 2 ≤ ‖w‖ ^ q := pow_le_pow_right₀ hw.le hq
  rw [norm_pow] at h1
  have h4 : ‖w‖ ^ q ≤ ‖w‖ := h1.trans (max_le (h.trans hw.le) h2)
  nlinarith

end GlobalTheory.PZ.TiltHyps

open GlobalTheory.PZ GlobalTheory.PZ.TiltHyps in
theorem GlobalTheory.PZ.ltData_tilt_hyps : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) [Finite (IsLocalRing.ResidueField ↥(OL K))] (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l), LTData K χ π z →
    ∃ (hπ : Irreducible π) (hF : IsLubinTateSeries π (ltSeries K π)) (v : ℕ → OC l),
      (∀ n, ((v n : OC l) : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (z n)) ∧
      (∀ n, HasSum (fun i => ((intToOC K (PowerSeries.coeff i (ltSeries K π)) * v (n + 1) ^ i : OC l) : ℂ_[l])) (v n : ℂ_[l])) ∧
      v 0 = 0 ∧ v 1 ≠ 0 ∧
      ∀ (g : ↥(GK K)) (u : ↥(OL K)), (u : ↥K.1) = (χ g : ↥K.1) → ∀ n,
        HasSum (fun i => ((intToOC K (PowerSeries.coeff i (lubinTateHom hπ hF hF u).toPowerSeries) * v n ^ i : OC l) : ℂ_[l]))
          ((Per.σO (g : GQ l) (v n) : OC l) : ℂ_[l]) := by
  intro l _ K _ χ π z h
  obtain ⟨hπ, hz0, hz1, hrel, hgal⟩ := h
  obtain ⟨hF, hiff⟩ := GlobalTheory.T.lubin_tate_endomorphism_unique l K π hπ
  set q := resCard K with hqdef
  have hq : 2 ≤ q := two_le_resCard K
  set c : ℂ_[l] := (((π : ↥K.1) : Om l) : ℂ_[l]) with hcdef
  have hc : ‖c‖ ≤ 1 := (GlobalTheory.RingBasics.mem_OC _).1 (intToOC K π).2
  have hrelC : ∀ n, c * (z (n + 1) : ℂ_[l]) + (z (n + 1) : ℂ_[l]) ^ q = (z n : ℂ_[l]) := fun n => by
    have := congrArg (algebraMap (Om l) ℂ_[l]) (hrel n)
    rw [map_add, map_mul, map_pow] at this; exact this
  have hnorm : ∀ n, ‖(z n : ℂ_[l])‖ ≤ 1 := by
    intro n
    induction n with
    | zero => rw [hz0]; simp
    | succ n ih => exact norm_le_one_of_lt hq hc (by rw [hrelC n]; exact ih)
  let v : ℕ → OC l := fun n => ⟨(z n : ℂ_[l]), (GlobalTheory.RingBasics.mem_OC _).2 (hnorm n)⟩
  refine ⟨hπ, hF, v, fun n => rfl, ?_, ?_, ?_, ?_⟩
  · intro n
    have hcoef : ∀ i, ((intToOC K (PowerSeries.coeff i (ltSeries K π)) * v (n + 1) ^ i : OC l) : ℂ_[l]) =
        (if i = 1 then c * (z (n + 1) : ℂ_[l]) else 0) + (if i = q then (z (n + 1) : ℂ_[l]) ^ q else 0) := by
      intro i
      have e1 : ltSeries K π = PowerSeries.C π * PowerSeries.X ^ 1 + PowerSeries.X ^ q := by
        rw [pow_one]; rfl
      rw [e1, map_add, PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_X_pow]
      split_ifs with h1 h2 h2 <;> first | (exfalso; omega) | (subst_vars; simp [v, hcdef, coe_intToOC])
    simp_rw [hcoef]
    show HasSum _ (z n : ℂ_[l])
    rw [← hrelC n]
    exact (hasSum_ite_eq 1 _).add (hasSum_ite_eq q _)
  · exact Subtype.ext (by simp [v, hz0])
  · intro h1
    apply hz1
    have : (z 1 : ℂ_[l]) = ((0 : Om l) : ℂ_[l]) := by
      simpa [v] using congrArg Subtype.val h1
    exact (algebraMap (Om l) ℂ_[l]).injective this
  · intro g u hu n
    obtain ⟨a, ha, φ, hφ, hs⟩ := hgal g
    have hau : a = u := Subtype.ext (ha.trans hu.symm)
    subst hau
    have hφe : φ = (lubinTateHom hπ hF hF a).toPowerSeries := (hiff a φ).1 hφ
    rw [← hφe]
    have hm := (hs n).map (algebraMap (Om l) ℂ_[l]).toAddMonoidHom
      (UniformSpace.Completion.continuous_coe (Om l))
    have e2 : ((Per.σO (g : GQ l) (v n) : OC l) : ℂ_[l]) = (((g : GQ l) (z n) : Om l) : ℂ_[l]) := by
      refine (GlobalTheory.RingIface.sigO_coe l (g : GQ l) (v n)).trans ?_
      change Per.σC (g : GQ l) ((z n : Om l) : ℂ_[l]) = _
      rw [GlobalTheory.RingBasics.σC_coe]
    rw [e2]
    convert hm using 1
    funext i
    show (((intToOC K _ : OC l) : ℂ_[l]) * ((z n : Om l) : ℂ_[l]) ^ i) = _
    simp only [Function.comp, coe_intToOC, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, map_mul, map_pow]
    rfl
    rfl
