import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittAnisotropicProjectionUnitaryInvEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqSemiMeasOfCovolOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.JacMeas

open GlobalTheory.SemiHaar

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

def lv : UX D ρ →* GA D S := d.levi.comp (UX D ρ).subtype

theorem lv_mem (u : UX D ρ) : lv d u ∈ flagN d := d.levi_mem_NFlag u.2

theorem radX_le : radX d ≤ flagN d := inf_le_left

theorem lv_conj (n : GA D S) (hn : n ∈ radX d) (u : UX D ρ) : lv d u * n * (lv d u)⁻¹ ∈ radX d := by
  refine ⟨(flagN d).mul_mem ((flagN d).mul_mem (lv_mem d u) hn.1) ((flagN d).inv_mem (lv_mem d u)), ?_⟩
  change mt S (d.levi u.1 * n * (d.levi u.1)⁻¹) ⬝ d.jX = d.jX
  rw [← map_inv, mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.levi_jX, ← Matrix.mul_assoc (mt S n),
    mem_fixer.1 hn.2, ← Matrix.mul_assoc, d.levi_jX, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.mul_one]

theorem anisotropicEmbedding_conj_wittFlagUnipotentFixer (n : GA D S) (hn : n ∈ radX d) (h : GA D S₀) : d.emb0 h * n * (d.emb0 h)⁻¹ ∈ radX d :=
  ⟨(flag_jacobi_structure D S S₀ ρ d).2.2.2.2.1 n hn.1 h,
    (stabX d).mul_mem ((stabX d).mul_mem (wittSmallGroupEmbedding_mem_pointwiseStabilizerIsotropic d h) hn.2) ((stabX d).inv_mem (wittSmallGroupEmbedding_mem_pointwiseStabilizerIsotropic d h))⟩

theorem radX_sup_lv : radX d ⊔ (lv d).range = flagN d := by
  refine le_antisymm (sup_le (radX_le d) (by rintro _ ⟨u, rfl⟩; exact lv_mem d u)) fun n hn => ?_
  obtain ⟨u, hu, b, c, rfl⟩ := ((flag_jacobi_structure D S S₀ ρ d).1 n).1 hn
  exact mul_mem (Subgroup.mem_sup_right ⟨⟨u, hu⟩, rfl⟩)
    (Subgroup.mem_sup_left (mul_mem (nB_mem_radX d b) (nC_mem_radX d c)))

theorem wittFlagUnipotentFixer_sup_anisotropic_eq_stabilizer : radX d ⊔ d.emb0.range = stabX d := by
  refine le_antisymm (sup_le (radX_le_stabX d) (by rintro _ ⟨u, rfl⟩; exact wittSmallGroupEmbedding_mem_pointwiseStabilizerIsotropic d u)) fun g hg => ?_
  obtain ⟨n, hn, h, rfl⟩ := ((flag_jacobi_structure D S S₀ ρ d).2.2.1 g).1 hg
  exact mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨h, rfl⟩)

theorem blockX_mul_lv {n : GA D S} (hn : n ∈ radX d) (u : UX D ρ) : blockX d (n * lv d u) = u.1.1 := by
  change d.pX ⬝ (mt S (n * d.levi u.1) ⬝ d.jX) = _
  rw [mt_mul, Matrix.mul_assoc, d.levi_jX, ← Matrix.mul_assoc (mt S n), mem_fixer.1 hn.2, ← Matrix.mul_assoc, d.pX_jX,
    Matrix.one_mul]

theorem exists_rad_lv {n : GA D S} (hn : n ∈ flagN d) : ∃ n₀ ∈ radX d, ∃ u, n = n₀ * lv d u :=
  exists_mul_of_mem_sup_range (radX d) (lv d) (lv_conj d) (by rw [radX_sup_lv]; exact hn)

theorem continuous_blockX : Continuous (blockX d) :=
  continuous_const.matrix_mul ((continuous_mt S).matrix_mul continuous_const)

theorem isClosed_stabX : IsClosed (stabX d : Set (GA D S)) := by
  haveI := (lattice_Mx D S.rank ρ).2.2.2.1
  exact isClosed_eq ((continuous_mt S).matrix_mul continuous_const) continuous_const

theorem isClosed_flagN : IsClosed (flagN d : Set (GA D S)) := by
  haveI := (lattice_Mx D S.rank ρ).2.2.2.1
  haveI := (lattice_Mx D S₀.rank S₀.rank).2.2.2.1
  have e : (flagN d : Set (GA D S)) = (blockX d ⁻¹' GlobalTheory.UnitU.uniSet D ρ) ∩
      ({g | mt S g ⬝ d.jX = d.jX ⬝ blockX d g} ∩ {g | d.p0 ⬝ (mt S g ⬝ d.j0) = 1}) := by
    ext g
    constructor
    · intro hg
      refine ⟨?_, ?_, (GlobalTheory.JacProj.flag_le d hg).2⟩
      · obtain ⟨n, hn, u, rfl⟩ := exists_rad_lv d hg
        rw [Set.mem_preimage, blockX_mul_lv d hn]
        exact u.2
      · exact GlobalTheory.JacProj.keeps_jX d (GlobalTheory.JacProj.flag_le d hg).1
    · rintro ⟨h1, h2, h3⟩
      let u : UX D ρ := ⟨GlobalTheory.UnitU.toUnit _ h1, h1⟩
      have hs : (lv d u)⁻¹ * g ∈ stabX d := by
        change mt S ((lv d u)⁻¹ * g) ⬝ d.jX = d.jX
        have h4 : mt S g ⬝ d.jX = mt S (lv d u) ⬝ d.jX := (show _ = _ from h2).trans (d.levi_jX u.1).symm
        rw [mt_mul, Matrix.mul_assoc, h4, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
      obtain ⟨n, hn, h, he⟩ := ((flag_jacobi_structure D S S₀ ρ d).2.2.1 _).1 hs
      have hg : g = lv d u * n * d.emb0 h := by rw [mul_assoc, ← he, mul_inv_cancel_left]
      have hn' : lv d u * n ∈ flagN d := mul_mem (lv_mem d u) hn.1
      have h5 := GlobalTheory.JacProj.witt_anisotropic_block_flag_mul_embedded d hn' h
      rw [← hg, show d.p0 ⬝ (mt S g ⬝ d.j0) = 1 from h3] at h5
      have h6 : h = 1 := mt_injective S₀ (h5.symm.trans (mt_one S₀).symm)
      rw [hg, h6, map_one, mul_one]
      exact hn'
  rw [e]
  exact ((GlobalTheory.UnitU.isClosed_uniSet D ρ).preimage (continuous_blockX d)).inter
    ((isClosed_eq ((continuous_mt S).matrix_mul continuous_const) (continuous_const.matrix_mul (continuous_blockX d))).inter
      (isClosed_eq (continuous_const.matrix_mul ((continuous_mt S).matrix_mul continuous_const)) continuous_const))

theorem isClosed_radX : IsClosed (radX d : Set (GA D S)) := (isClosed_flagN d).inter (isClosed_stabX d)

theorem exists_proj_lv : ∃ p : flagN d → UX D ρ, Continuous p ∧
    ∀ (u : UX D ρ) (n : radX d) (hm : n.1 * lv d u ∈ flagN d), p ⟨n.1 * lv d u, hm⟩ = u := by
  choose n₀ hn₀ p hp using fun g : flagN d => exists_rad_lv d g.2
  have hb : ∀ g, (p g).1.1 = blockX d g.1 := fun g => by rw [hp g, blockX_mul_lv d (hn₀ g)]
  refine ⟨p, (GlobalTheory.UnitU.isClosedEmbedding_val D ρ).isInducing.continuous_iff.2 ?_, fun u n hm => ?_⟩
  · exact ((continuous_blockX d).comp continuous_subtype_val).congr fun g => (hb g).symm
  · exact Subtype.ext (Units.ext ((hb _).trans (blockX_mul_lv d n.2 u)))

theorem rat_lv (n : GA D S) (hn : n ∈ radX d) (u : UX D ρ) : n * lv d u ∈ GQ S ↔ n ∈ GQ S ∧ u ∈ UXQ D ρ := by
  have hb : ∀ g ∈ GQ S, blockX d g ∈ ratMx D ρ ρ := fun g hg =>
    ratMx_mul (rat_mem _) (ratMx_mul ((mem_GQ_iff S g).1 hg) (rat_mem _))
  refine ⟨fun h => ?_, fun h => mul_mem h.1 (d.levi_mem_GQ h.2.1 h.2.2)⟩
  have h1 := hb _ h
  have h2 := hb _ (inv_mem h)
  rw [show (n * lv d u)⁻¹ = (lv d u⁻¹ * n⁻¹ * (lv d u⁻¹)⁻¹) * lv d u⁻¹ by simp,
    blockX_mul_lv d (lv_conj d _ (inv_mem hn) _)] at h2
  rw [blockX_mul_lv d hn] at h1
  refine ⟨?_, h1, h2⟩
  rw [show n = n * lv d u * (lv d u)⁻¹ by simp]
  exact mul_mem h (inv_mem (d.levi_mem_GQ h1 h2))

theorem jac_measure : ∀ (D : D7) (ρ : ℕ) (J : JacLev D ρ) (vU : VolU D ρ) (ν₀ : Measure (radX J.d)) (𝓝₀ : Set (radX J.d)), ν₀.IsHaarMeasure → IsFundamentalDomain ((GQ J.W).subgroupOf (radX J.d)) 𝓝₀ ν₀ → ν₀ 𝓝₀ = 1 → IsClosed ((radX J.d ⊔ J.d.emb0.range : Subgroup (GA D J.W)) : Set (GA D J.W)) ∧ (semiMeas (radX J.d) J.d.emb0 J.v0.μ ν₀).IsHaarMeasure ∧ (semiMeas (radX J.d) J.d.emb0 J.v0.μ ν₀).IsInvInvariant ∧ J.μR.IsInvInvariant ∧ ∀ F : GA D J.W → ENNReal, Measurable F → ∫⁻ r : jacGrp J.d, F r ∂J.μR = ∫⁻ u, ∫⁻ r : (radX J.d ⊔ J.d.emb0.range : Subgroup (GA D J.W)), F (r * J.d.levi u.1) ∂(semiMeas (radX J.d) J.d.emb0 J.v0.μ ν₀) ∂vU.ν := by
  intro D ρ J vU ν₀ 𝓝₀ hν₀ h𝓝₀ h𝓝₀1
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W
  obtain ⟨j1, j2, j3, j4, j5, -, j7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W₀
  obtain ⟨k1, k2, k3⟩ := GlobalTheory.UnitU.topology D ρ
  have k4 := (GlobalTheory.UnitU.rational D ρ).1
  have k5 : BorelSpace (UX D ρ) := ⟨rfl⟩
  obtain ⟨hU, 𝓤, h𝓤, h𝓤1⟩ := vU.unit
  obtain ⟨hN, h𝓝, h𝓝1⟩ := J.vN.unit
  obtain ⟨K, hK, hcov⟩ := J.cpt
  have hμ := J.v0.haar
  obtain ⟨p, hpc, hp⟩ := GlobalTheory.JacProj.exists_continuous_proj D J.W J.W₀ ρ J.d
  have hle : radX J.d ⊔ J.d.emb0.range ≤ flagN J.d ⊔ J.d.emb0.range := sup_le_sup_right (radX_le J.d) _
  have H0 := semiMeas_haar_inv (radX J.d) J.d.emb0 (isClosed_radX J.d) J.d.continuous_embed (anisotropicEmbedding_conj_wittFlagUnipotentFixer J.d)
    ⟨fun g => p (Subgroup.inclusion hle g), hpc.comp (continuous_inclusion hle), fun h n => hp h ⟨n.1, n.2.1⟩⟩
    (GQ J.W) (GQ J.W₀) (fun _ h => J.d.wittDecomp_anisotropicEmbedding_mem_rationalPoints h) hK hcov J.v0.μ J.v0.fund ν₀ h𝓝₀
    (by rw [h𝓝₀1]; exact ENNReal.one_ne_top)
  have H1 := semiMeas_haar_inv (flagN J.d) J.d.emb0 (isClosed_flagN J.d) J.d.continuous_embed
    (flag_jacobi_structure D J.W J.W₀ ρ J.d).2.2.2.2.1 ⟨p, hpc, hp⟩
    (GQ J.W) (GQ J.W₀) (fun _ h => J.d.wittDecomp_anisotropicEmbedding_mem_rationalPoints h) hK hcov J.v0.μ J.v0.fund J.vN.ν h𝓝
    (by rw [h𝓝1]; exact ENNReal.one_ne_top)
  refine ⟨by rw [wittFlagUnipotentFixer_sup_anisotropic_eq_stabilizer]; exact isClosed_stabX J.d, H0.1, H0.2, H1.2, fun F hF => ?_⟩
  have l1 : LocallyCompactSpace (radX J.d) := (isClosed_radX J.d).locallyCompactSpace
  have l2 : SecondCountableTopology (radX J.d) := TopologicalSpace.Subtype.secondCountableTopology _
  have l3 : LocallyCompactSpace (flagN J.d) := (isClosed_flagN J.d).locallyCompactSpace
  have l4 : SecondCountableTopology (flagN J.d) := TopologicalSpace.Subtype.secondCountableTopology _
  have hlv : Continuous (lv J.d) := J.d.continuous_levi.comp continuous_subtype_val
  have hs := J.d.continuous_embed
  have e1 : ∫⁻ r : jacGrp J.d, F r ∂J.μR = ∫⁻ h, ∫⁻ n, F (n.1 * J.d.emb0 h) ∂J.vN.ν ∂J.v0.μ :=
    lintegral_semiMeas (flagN J.d) J.d.emb0 hs J.v0.μ J.vN.ν F hF
  have e2 : ∀ h, ∫⁻ n, F (n.1 * J.d.emb0 h) ∂J.vN.ν = ∫⁻ u, ∫⁻ n, F (n.1 * lv J.d u * J.d.emb0 h) ∂ν₀ ∂vU.ν := fun h =>
    lintegral_of_covolOne (radX J.d) (lv J.d) (isClosed_radX J.d) hlv (lv_conj J.d) (flagN J.d) (radX_sup_lv J.d)
      (exists_proj_lv J.d) (GQ J.W) (UXQ D ρ) (rat_lv J.d) vU.ν h𝓤 h𝓤1 ν₀ h𝓝₀ h𝓝₀1 J.vN.ν h𝓝 h𝓝1
      (fun g => F (g * J.d.emb0 h)) (hF.comp (continuous_mul_right _).measurable)
  have e3 : ∀ u : UX D ρ, ∫⁻ r : (radX J.d ⊔ J.d.emb0.range : Subgroup (GA D J.W)), F (r * J.d.levi u.1)
      ∂(semiMeas (radX J.d) J.d.emb0 J.v0.μ ν₀) = ∫⁻ h, ∫⁻ n, F (n.1 * lv J.d u * J.d.emb0 h) ∂ν₀ ∂J.v0.μ := fun u => by
    rw [lintegral_semiMeas (radX J.d) J.d.emb0 hs J.v0.μ ν₀ (fun g => F (g * J.d.levi u.1))
      (hF.comp (continuous_mul_right _).measurable)]
    simp only [mul_assoc, J.d.wittHyperbolic_anisotropic_commute_levi]
    rfl
  have hm : Measurable fun q : (GA D J.W₀ × UX D ρ) × radX J.d => F (q.2.1 * lv J.d q.1.2 * J.d.emb0 q.1.1) :=
    hF.comp (Continuous.measurable (((continuous_subtype_val.comp continuous_snd).mul
      (hlv.comp (continuous_snd.comp continuous_fst))).mul (hs.comp (continuous_fst.comp continuous_fst))))
  rw [e1]
  simp only [e2, e3]
  exact lintegral_lintegral_swap (hm.lintegral_prod_right' (ν := ν₀)).aemeasurable

end GlobalTheory.JacMeas
