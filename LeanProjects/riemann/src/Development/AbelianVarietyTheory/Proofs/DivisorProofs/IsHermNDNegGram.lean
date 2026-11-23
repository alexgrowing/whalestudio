import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.UnramBridgeHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPtAnti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactFundamentalSetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchACompCoordEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowOfRestrictsToQuadrati
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CosetSumAlongMulEquivSubgroups
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittChangeBasisUnitaryIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelParabolicChartLeviBlockStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCompactUnderWittChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupConjHermitianAutomorphismsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxBasisAdaptedCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamagawaMeasureMatrixAdelesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationSeesawSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarAverageFundamentalDomainDescentStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SWLink

variable {D : D7} {n : ℕ} {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
  {μ : Measure (Mx D V.rank n)} {ω : StdUnn.G D n →* Module.End ℂ (schwartzA θ V.rank n)}
  {J : Matrix (Fin n) (Fin n) D.host.E} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E}
  {T : GL (Fin (n + n)) D.host.E} {κ : UD D J₂ ≃* StdUnn.G D n} {ι : UD D (-V.gram) ≃ₜ* GA D V} {d : ℕ}
  {ε : Module.Basis (Fin d) D.host.F D.host.E} {co : Dbx V J₂ d}
  {om : UD D (-V.gram) × UD D J₂ →* Module.End ℂ ((Fin V.rank × Fin n × Fin d → AF D.host.F) → ℂ)}

theorem unramified_host (D : D7) : Algebra.Unramified (𝓞 D.host.F) (𝓞 D.host.E) := by
  haveI := D.host.isCMField_hostE
  exact Formalism.L2.Pj.unramBridge_holds D.host.E fun P hP => by
    obtain ⟨θ, t, ht, hθ⟩ := D.sp.cm.cmUnram.2.2 P hP
    refine ⟨θ, ?_⟩
    have : RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E) θ = t :=
      RingOfIntegers.ext ht.symm
    rwa [this]

theorem isHermND_neg_gram (V : HSp D) : IsHermND D.sp.cm.sig ((1 : D.host.E) • -V.gram) := by
  rw [one_smul]
  refine ⟨fun i j => ?_, ?_⟩
  · rw [Matrix.neg_apply, Matrix.neg_apply, map_neg]
    exact congrArg Neg.neg (congrFun (congrFun (gram_conjTranspose V) i) j)
  · rw [Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (gram_isUnit_det V).ne_zero

theorem aniso_neg_gram (hV : IsAniso V) (x : Fin V.rank → D.host.E)
    (hx : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig (-V.gram) x x = 0) : x = 0 := by
  by_contra h0
  refine hV 1 (Matrix.of fun i _ => star (x i)) ⟨one_pos, ?_, ?_⟩
  · refine linearIndependent_unique_iff.2 fun h => h0 (funext fun i => ?_)
    exact star_eq_zero.1 (congrFun h i)
  · funext a b
    rw [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, Matrix.neg_mulVec, dotProduct_neg, neg_eq_zero] at hx
    rw [cT_sig, Matrix.mul_assoc, Matrix.zero_apply, ← hx]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, star_star, dotProduct, Matrix.mulVec]
    rfl

theorem height {K : Subgroup (UD D J₂)} {H : StdUnn.G D n → ℝ≥0} (hH : StdUnn.IsHeight H)
    (hP : ∀ g : UD D J₂, g ∈ siegelOf finSumFinEquiv (uinc D J₂) ↔ κ g ∈ StdUnn.P D n)
    (ha : ∀ p : siegelOf finSumFinEquiv (uinc D J₂),
      StdUnn.blkA (StdUnn.mat (κ p)) = (leviOf finSumFinEquiv (uinc D J₂) p).1)
    (hK : ∀ g : UD D J₂, g ∈ K ↔ κ g ∈ StdUnn.K D n) :
    IwasawaOf finSumFinEquiv (uinc D J₂) (absA D) K ∧ ∀ g, hgtOf finSumFinEquiv (uinc D J₂) (absA D) K g = H (κ g) := by
  have h1 : ∀ (p : siegelOf finSumFinEquiv (uinc D J₂)), ∀ k ∈ K,
      H (κ (p * k)) = absA D (aOf finSumFinEquiv (uinc D J₂) p) := fun p k hk => by
    rw [map_mul]
    exact hH _ ((hP p).1 p.2) _ (ha p) _ ((hK k).1 hk)
  have h2 : IwasawaOf finSumFinEquiv (uinc D J₂) (absA D) K := by
    refine ⟨fun g => ?_, fun p hp => ?_⟩
    · obtain ⟨p, hp, k, hk, e⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D n (κ g)
      refine ⟨⟨κ.symm p, (hP _).2 (by rwa [κ.apply_symm_apply])⟩, κ.symm k, (hK _).2 (by rwa [κ.apply_symm_apply]), ?_⟩
      rw [← map_mul, ← e, κ.symm_apply_apply]
    · have e1 := h1 p 1 (one_mem K)
      have e2 := h1 1 p hp
      rw [mul_one] at e1
      rw [OneMemClass.coe_one, one_mul, map_one, map_one] at e2
      exact e1.symm.trans e2
  refine ⟨h2, fun g => ?_⟩
  obtain ⟨p, k, hk, rfl⟩ := h2.1 g
  rw [h2.hgtOf_mul p hk, h1 p k hk]

theorem kfin (hom : IsTrans ε ι κ ω om) {K : Subgroup (UD D J₂)} (hK : ∀ g : UD D J₂, g ∈ K ↔ κ g ∈ StdUnn.K D n)
    {φ : (Fin V.rank × Fin n × Fin d → AF D.host.F) → ℂ}
    (hφ : φ ∈ schA D.host.F (Fin V.rank × Fin n × Fin d)) (Φ : schwartzA θ V.rank n) (e : φ ∘ coord ε = Φ.1)
    (hΦ : RegSch.KFin ω Φ) : FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om (1, k) φ}) := by
  let L : schwartzA θ V.rank n →ₗ[ℂ] ((Fin V.rank × Fin n × Fin d → AF D.host.F) → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (coordL ε V.rank n).symm).comp (schwartzA θ V.rank n).subtype
  haveI : FiniteDimensional ℂ (Submodule.span ℂ {Ψ : schwartzA θ V.rank n | ∃ k ∈ StdUnn.K D n, Ψ = ω k Φ}) := hΦ
  refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ
    {Ψ : schwartzA θ V.rank n | ∃ k ∈ StdUnn.K D n, Ψ = ω k Φ}).map L) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, hk, rfl⟩
  refine ⟨ω (κ k) Φ, Submodule.subset_span ⟨κ k, (hK k).1 hk, rfl⟩, funext fun y => ?_⟩
  obtain ⟨x, rfl⟩ := (coordL ε V.rank n).surjective y
  rw [coordL_apply, hom.right k hφ Φ e]
  exact congrArg (ω (κ k) Φ).1 ((coordL ε V.rank n).symm_apply_apply x)

theorem skew_xi (D : D7) : ∃ δ : D.host.E, δ ≠ 0 ∧ D.sp.cm.sig δ = -δ := by
  refine ⟨D.host.xi0, GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D, D.host.φ₀.injective ?_⟩
  have hd : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  rw [(GlobalTheory.AdelicU.isCMExt_host D).2.2.2, map_neg]
  unfold Host.xi0
  rw [map_div₀, map_neg, map_one, map_mul, map_natCast, hd]
  simp [div_neg]

end GlobalTheory.SWLink

end
