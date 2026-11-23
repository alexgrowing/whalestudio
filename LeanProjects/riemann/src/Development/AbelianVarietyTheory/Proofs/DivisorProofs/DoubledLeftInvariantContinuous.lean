import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegFamConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelEisensteinDoubled
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapHaarEqOfLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarInvEqOfLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralEqZeroOfFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetOrbitNonsingularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetOrbitIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetOrbitUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentDetEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentSubgroupClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingEmbeddingContinuousRationalStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling

noncomputable section

namespace GlobalTheory.OrbitVanish

def conjAut {G : Type} [Group G] (N : Subgroup G) (p : G) (h1 : ∀ n ∈ N, p * n * p⁻¹ ∈ N)
    (h2 : ∀ n ∈ N, p⁻¹ * n * p⁻¹⁻¹ ∈ N) : N ≃* N where
  toFun n := ⟨p * n.1 * p⁻¹, h1 n.1 n.2⟩
  invFun n := ⟨p⁻¹ * n.1 * p⁻¹⁻¹, h2 n.1 n.2⟩
  left_inv n := Subtype.ext (by simp [mul_assoc])
  right_inv n := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

end GlobalTheory.OrbitVanish

set_option maxHeartbeats 1600000 in
open GlobalTheory.OrbitVanish in

theorem GlobalTheory.OrbitVanish.integral_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d r s : ℕ) (W : Spc F E d), W.IsSkew σ B r s → IsCMExt F E σ →
    ∀ W₂ : Spc F E (d + d), W₂.J = dblGram finSumFinEquiv W.J →
    ∀ i : UA σ W.J × UA σ W.J →* UA σ W₂.J, (∀ h h', mat (i (h, h')) = blkMat finSumFinEquiv (mat h) (mat h')) →
    ∀ Φ : UA σ W₂.J → ℂ, Continuous Φ →
    GlobalTheory.AutomorphicL2Unitary.LeftInv ((siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) ⊓ ratU σ W₂.J) Φ →
    (∀ p : siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype,
      aOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype p = 1 → ∀ g, Φ (p * g) = Φ g) →
    ∀ w : UA σ W.J → ℂ, Continuous w → (∀ x y, w (x * y) = w x * w y) → (∀ γ ∈ ratU σ W.J, w γ = 1) →
    (∀ x : UA σ W.J, Matrix.GeneralLinearGroup.det x.1 = 1 → w x = 1) →
    ∀ μ : Measure (UA σ W.J), μ.IsHaarMeasure →
    ∀ f : UA σ W.J → ℂ, Continuous f → (∀ γ ∈ ratU σ W.J, ∀ h, f (γ * h) = f h) → GlobalTheory.ThKLiftCusp.IsCuspW W f →
    ∀ γ ∈ ratU σ W₂.J, (¬ ∃ δ ∈ ratU σ W.J, γ * (i (1, δ))⁻¹ ∈ siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) →
    ∀ S : Subgroup (UA σ W.J),
      (∀ g, g ∈ S ↔ g ∈ ratU σ W.J ∧ γ * i (1, g) * γ⁻¹ ∈ siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) →
    ∀ (h : UA σ W.J) (D : Set (UA σ W.J)), IsFundamentalDomain S D μ →
      IntegrableOn (fun x => f x * (Φ (γ * i (h, x)) * w x)) D μ →
      ∫ x in D, f x * (Φ (γ * i (h, x)) * w x) ∂μ = 0 := by
  intro F E _ _ _ _ _ σ B d r s W hW hcm W₂ hW₂ i hi Φ hΦc hΦP hΦa w hwc hwm hwr hwdet μ hμ f hfc hfr hcusp γ hγ hnot S hS h D hD hint
  classical
  haveI := hμ
  set P := siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype with hPdef
  obtain ⟨j, Y, hj, hinj, hiso, hspan⟩ := GlobalTheory.T.double_coset_orbit_nonsingular F E σ hcm B d r s W hW W₂ hW₂ i hi γ hγ hnot
  set N := GlobalTheory.ThKLiftCusp.unipSp σ W Y with hNdef
  have hcP := GlobalTheory.T.double_coset_orbit_integral F E σ hcm B d r s W hW W₂ hW₂ i hi γ hγ j Y hinj hiso hspan
  have hnS := GlobalTheory.T.double_coset_orbit_unipotent F E σ hcm B d r s W hW W₂ hW₂ i hi γ hγ j Y hinj hiso hspan
  have hdet := GlobalTheory.T.unipotent_det_eq_one F E σ d W j Y
  have hcl := GlobalTheory.T.unipotent_subgroup_closed F E σ hcm B d r s W hW j Y hj hinj hiso
  obtain ⟨ν, 𝓕N, hν, h𝓕N, hmass⟩ := GlobalTheory.T.unipotent_fundamental_domain F E σ hcm B d r s W hW j Y hj hinj hiso
  obtain ⟨hic, hirat⟩ := GlobalTheory.T.doubling_embedding_continuous_rational F E σ d W.J W₂.J i hi
  obtain ⟨hTG, hLC, hSC, hT2⟩ := GlobalTheory.UnipMass.topUA σ W.J
  haveI := hTG
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  haveI := hν
  haveI : LocallyCompactSpace N := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology N := hcl.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  haveI := GlobalTheory.UnipMass.countable_ratU' σ W.J N
  haveI := GlobalTheory.UnitaryVol.countable_ratU σ W.J
  have hSle : S ≤ ratU σ W.J := fun x hx => ((hS x).1 hx).1
  haveI : Countable S := (Subgroup.inclusion_injective hSle).countable
  have hnorm : ∀ p ∈ S, ∀ n ∈ N, p * n * p⁻¹ ∈ N := fun p hp n hn =>
    hnS p ((hS p).1 hp).1 ((hS p).1 hp).2 n hn
  have hSN : S.subgroupOf N = (ratU σ W.J).subgroupOf N := by
    ext n
    simp only [Subgroup.mem_subgroupOf]
    refine ⟨fun hn => hSle hn, fun hn => (hS _).2 ⟨hn, (hcP n.1 n.2).1⟩⟩
  have hne : ν 𝓕N ≠ 0 := by rw [hmass]; exact one_ne_zero
  have hnt : ν 𝓕N ≠ ⊤ := by rw [hmass]; exact ENNReal.one_ne_top
  have hconj : ∀ (p : UA σ W.J) (hp : p ∈ S), Measure.map
      (fun n : N => (⟨p * n.1 * p⁻¹, hnorm p hp n.1 n.2⟩ : N)) ν = ν := by
    intro p hp
    refine GlobalTheory.LatticeAut.map_haar_eq_of_lattice _ _ ν 𝓕N h𝓕N hne hnt
      (conjAut N p (hnorm p hp) (hnorm p⁻¹ (inv_mem hp))) ?_ ?_ ?_ ?_
    · exact ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
    · exact ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
    · intro l hl
      exact mul_mem (mul_mem (hSle hp) (show l.1 ∈ ratU σ W.J from hl)) (inv_mem (hSle hp))
    · intro l hl
      exact mul_mem (mul_mem (inv_mem (hSle hp)) (show l.1 ∈ ratU σ W.J from hl)) (inv_mem (inv_mem (hSle hp)))
  have hinv := GlobalTheory.haar_inv_eq_of_lattice _ _ ν 𝓕N h𝓕N hne hnt

  set g : UA σ W.J → ℂ := fun x => f x * (Φ (γ * i (h, x)) * w x) with hg
  obtain ⟨hTG₂, -, -, -⟩ := GlobalTheory.UnipMass.topUA σ W₂.J
  haveI := hTG₂
  have hgc : Continuous g :=
    hfc.mul ((hΦc.comp (continuous_const.mul (hic.comp (continuous_const.prodMk continuous_id)))).mul hwc)
  have hsplit : ∀ p x : UA σ W.J, γ * i (h, p * x) = (γ * i (1, p) * γ⁻¹) * (γ * i (h, x)) := by
    intro p x
    have e : ((h, p * x) : UA σ W.J × UA σ W.J) = (1, p) * (h, x) := by simp
    rw [e, map_mul]
    group
  have hgS : ∀ p ∈ S, ∀ x, g (p * x) = g x := by
    intro p hp x
    obtain ⟨hpr, hpP⟩ := (hS p).1 hp
    have hq : γ * i (1, p) * γ⁻¹ ∈ P ⊓ ratU σ W₂.J :=
      Subgroup.mem_inf.2 ⟨hpP, mul_mem (mul_mem hγ (hirat p hpr)) (inv_mem hγ)⟩
    simp only [hg]
    rw [hfr p hpr x, hsplit, hΦP _ hq, hwm, hwr p hpr, one_mul]
  have h0 : ∀ x, ∫ n in 𝓕N, g (n.1 * x) ∂ν = 0 := by
    intro x
    have e1 : ∀ n : N, g (n.1 * x) = f (n.1 * x) * (Φ (γ * i (h, x)) * w x) := by
      intro n
      obtain ⟨hp, ha⟩ := hcP n.1 n.2
      simp only [hg]
      rw [hsplit, show γ * i (1, n.1) * γ⁻¹ = ((⟨_, hp⟩ : P) : UA σ W₂.J) from rfl, hΦa _ ha, hwm,
        hwdet n.1 (hdet n.1 n.2), one_mul]
    simp only [e1]
    rw [integral_mul_const, hcusp j Y hj hinj hiso ν 𝓕N hν h𝓕N hmass x, zero_mul]
  exact GlobalTheory.UnipotentFibration.setIntegral_eq_zero_of_fibre _ μ S N hcl hnorm ν hconj hinv 𝓕N (hSN ▸ h𝓕N) hmass D hD
    g hgc hgS hint h0

end
