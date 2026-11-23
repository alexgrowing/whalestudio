import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingMapThetaIdentityAnyWeilData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionIntegrableAndContinuous
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionDegeneratePrincipalSeriesLaw
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelHeightFinitePlaceDoublingEmbeddingLeOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjWeilDatumViaAdjointExchangedPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeightIoLe
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DblVacAtInhabited
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DblApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalSourceActsOnOrientedThetaBySubstitution
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubledLagrangianTermFrameIndependent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelEisensteinDoubledThetaTermsEqLagrangianIntStatement

noncomputable section

namespace GlobalTheory.SWAbsGrowth

section Local

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.Doubling Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.UG (bc)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem absNorm_le_sq {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v ⊗[F] E) :
    ‖Algebra.norm (Fv F v) x‖₊ ≤ absFin F v x ^ 2 := by
  have hN := GlobalTheory.Doubling.algebraMap_norm_eq hσ (R := Fv F v) x
  have e1 : absFin F v (algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.norm (Fv F v) x)) =
      ‖Algebra.norm (Fv F v) x‖₊ := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    exact absFin_tmul_one F v _
  have hs : absFin F v (sigR (Fv F v) σ x) ≤ absFin F v x := by
    refine (absFin_le_iff F v).2 fun τ => ?_
    have e2 : ∀ w, finEmb F v τ (sigR (Fv F v) σ w) = finEmb F v ((τ : E →ₐ[F] FvBar F v).comp σ) w := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [sigR]
      | add y z hy hz => simp only [map_add, hy, hz]
    rw [e2]
    exact le_absFin F v _ x
  rw [← e1, hN, sq]
  exact (absFin_mul_le F v _ _).trans (mul_le_mul' le_rfl hs)

theorem entry_le_opNorm {n : Type} [Fintype n] [DecidableEq n] (y : Matrix n n ℂ) (i j : n) : ‖y i j‖₊ ≤ opNorm y := by
  have h1 := (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) y).le_opNNNorm (EuclideanSpace.single j 1)
  have h2 := PiLp.norm_apply_le (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) y (EuclideanSpace.single j 1)) i
  have h3 : (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) y (EuclideanSpace.single j 1)) i = y i j := by
    change ∑ k, y i k * (EuclideanSpace.single j (1 : ℂ)) k = _
    simp
  rw [h3] at h2
  rw [PiLp.nnnorm_single, nnnorm_one, mul_one] at h1
  exact (show ‖y i j‖₊ ≤ _ from h2).trans h1

theorem absE_le_heightGL {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (n : ℕ) :
    ∃ C : ℝ≥0, ∀ (x : GL (Fin (n + n)) (AF F ⊗[F] E)) (u : (AF F ⊗[F] E)ˣ),
      u.1 = (leviMat finSumFinEquiv x.1).det → absE F E u ≤ C * heightGL F x ^ (2 * n) := by
  refine ⟨∏ _w : InfinitePlace F, ((n.factorial : ℝ≥0) * 2 ^ n) ^ 2, fun x u hu => ?_⟩
  rw [absE_apply, heightGL, mul_pow _ _ (2 * n), ← mul_assoc, ← Finset.prod_pow, ← Finset.prod_mul_distrib,
    finprod_pow (finite_mulSupport_htFin F x)]
  refine mul_le_mul' (Finset.prod_le_prod' fun w _ => ?_)
    (finprod_le_finprod' (finite_mulSupport_absEv u) ?_ fun v => ?_)
  · obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
    rw [absEw_eq_sq hσ τ, mul_comm 2 n, pow_mul, ← mul_pow]
    refine pow_le_pow_left' ?_ 2
    set H := htInf F w (bc (compInf F E w) x) with hH
    have hent : ∀ i j, ‖infEmb τ (compInf F E w (x.1 i j))‖₊ ≤ H := fun i j =>
      (entry_le_opNorm ((x.1.map (compInf F E w)).map (infEmb τ)) i j).trans
        (((normInf_le_iff F w).1 le_rfl τ).trans (le_htOf (normInf F w) (bc (compInf F E w) x)))
    have e : infEmb τ (unitInf F E w u).1 =
        (leviMat finSumFinEquiv ((x.1.map (compInf F E w)).map (infEmb τ))).det := by
      rw [leviMat_map, leviMat_map, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
        ← RingHom.map_det, ← hu]
      rfl
    rw [e, Matrix.det_apply]
    refine (nnnorm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ ((2 * H) ^ n) fun s _ => ?_).trans (le_of_eq ?_))
    · have : ‖Equiv.Perm.sign s • ∏ i, leviMat finSumFinEquiv ((x.1.map (compInf F E w)).map (infEmb τ)) (s i) i‖₊ =
          ∏ i, ‖leviMat finSumFinEquiv ((x.1.map (compInf F E w)).map (infEmb τ)) (s i) i‖₊ := by
        rw [← nnnorm_prod]
        rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h | h <;> simp [h]
      rw [this]
      refine (Finset.prod_le_pow_card _ _ (2 * H) fun i _ => ?_).trans (by simp)
      rw [two_mul]
      exact (nnnorm_add_le _ _).trans (add_le_add (hent _ _) (hent _ _))
    · simp [Fintype.card_perm, mul_pow, mul_assoc]
  · exact (finite_mulSupport_htFin F x).subset fun v hv h => hv (by simp only [h, one_pow])
  · have e : (unitFin F E v u).1 = (leviMat finSumFinEquiv (x.1.map (compFin F E v))).det := by
      rw [leviMat_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← hu]
      rfl
    rw [absEv_apply, e, mul_comm 2 n, pow_mul]
    refine (absNorm_le_sq hσ v _).trans (pow_le_pow_left' ((GlobalTheory.Core.Rk.HgtFin.absFin_det_le v _).trans
      (pow_le_pow_left' ((normFin_le_iff F v).2 fun i j => ?_) n)) 2)
    have hent : ∀ i j, absFin F v ((x.1.map (compFin F E v)) i j) ≤ htFin F v (bc (compFin F E v) x) := fun i j =>
      (absFin_le_normFin F v _ i j).trans (le_htOf (normFin F v) (bc (compFin F E v) x))
    exact (absFin_add_le F v _ _).trans (max_le (hent _ _) (hent _ _))

end Local

section Global

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.Doubling
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero delta)
open scoped NNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem hgt_mul_le (A : HSp D) (a : GL (Fin A.rank) (AE D)) (ha : IsMaj A a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : GA D (dblSp A),
      (hgt A a (x * y) : ℝ) ≤ hgt A a x * (C * GlobalTheory.Grow.height (dblSp A) y ^ (2 * A.rank)) := by
  haveI := t2Space_adeleRing' (F := D.host.F)
  have hI := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D A a ha
  have hK := isCompact_Khat A a
  obtain ⟨C, hC⟩ := absE_le_heightGL (isCMExt_host D) A.rank
  obtain ⟨B, hB⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact (dblSp A) hK
  have hB0 : 0 ≤ B := (GlobalTheory.Grow.height_pos _ _).le.trans (hB 1 (one_mem _))
  refine ⟨C * (B * B) ^ (2 * A.rank), by positivity, fun x y => ?_⟩
  obtain ⟨p, k, hk, rfl⟩ := hI x
  obtain ⟨p', k', hk', e⟩ := hI (k * y)
  have h1 : hgt A a (p * k * y) = absA D (aP A p) * absA D (aP A p') := by
    rw [mul_assoc, e, ← mul_assoc, ← Subgroup.coe_mul, hgt_mul A a _ hk', map_mul, map_mul]
  rw [h1, hgt_mul A a _ hk, NNReal.coe_mul]
  refine mul_le_mul_of_nonneg_left ?_ (NNReal.coe_nonneg _)
  have h2 : (absA D (aP A p') : ℝ) ≤ C * GlobalTheory.Grow.height (dblSp A) p' ^ (2 * A.rank) := by
    have := hC (Formalism.L2.Theta.matHom (dblSp A) p') (aP A p') rfl
    unfold GlobalTheory.Grow.height
    exact_mod_cast this
  have h3 : GlobalTheory.Grow.height (dblSp A) p' ≤ B * B * GlobalTheory.Grow.height (dblSp A) y := by
    have e' : (p' : GA D (dblSp A)) = k * y * k'⁻¹ := by rw [e, mul_inv_cancel_right]
    have hy := (GlobalTheory.Grow.height_pos _ y).le
    calc _ = GlobalTheory.Grow.height (dblSp A) (k * y * k'⁻¹) := by rw [e']
      _ ≤ GlobalTheory.Grow.height (dblSp A) k * GlobalTheory.Grow.height (dblSp A) y * GlobalTheory.Grow.height (dblSp A) k'⁻¹ :=
        (GlobalTheory.Grow.height_mul_le _ _ _).trans
          (mul_le_mul_of_nonneg_right (GlobalTheory.Grow.height_mul_le _ _ _) (GlobalTheory.Grow.height_pos _ _).le)
      _ ≤ B * GlobalTheory.Grow.height (dblSp A) y * B :=
        mul_le_mul (mul_le_mul_of_nonneg_right (hB k hk) hy) (hB _ (inv_mem hk')) (GlobalTheory.Grow.height_pos _ _).le
          (by positivity)
      _ = _ := by ring
  rw [mul_assoc, ← mul_pow]
  exact h2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (GlobalTheory.Grow.height_pos _ _).le h3 _) C.coe_nonneg)

theorem norm_swSec_le {ψ : AddChar (AF D.host.F) ℂ} {A B : HSp D} {χ : (AE D)ˣ →* Circle}
    {omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)} (hω : IsWeilDatumO ψ (dblSp A) B 1 χ omh)
    {ν : Measure (WO A B)} {𝓕 : Set (WO A B)} (hν : IsCovolOne (ratL B A) ν 𝓕) {φ : WO (dblSp A) B → ℂ}
    (hφ : IsThetaFunO ψ (dblSp A) B φ) (a : GL (Fin A.rank) (AE D)) (ha : IsMaj A a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖swSec A B omh ν 𝓕 φ x‖ ≤ C * (hgt A a x : ℝ) ^ ((B.rank : ℝ) / 2) := by
  have hI := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D A a ha
  have hc := (GlobalTheory.Core.Rk.IP.swSec_integrable_continuous D ψ A B χ omh hω ν 𝓕 hν φ hφ).2
  obtain ⟨C, hC⟩ := (isCompact_Khat A a).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, (norm_nonneg _).trans (hC 1 (one_mem _)), fun x => ?_⟩
  obtain ⟨p, k, hk, rfl⟩ := hI x
  have ex : (sZero A B + (A.rank : ℂ) / 2).re = (B.rank : ℝ) / 2 := by
    simp only [sZero, Complex.add_re, Complex.div_ofNat_re, Complex.sub_re, Complex.natCast_re]; ring
  rw [GlobalTheory.Core.Rk.SWLaw.swSec_law GlobalTheory.weilRepresentationUnitaryPair D ψ A B χ omh hω ν 𝓕 hν φ hφ p k, norm_mul, norm_mul, Circle.norm_coe,
    one_mul, norm_npow (hom_pos _ _), ex, hgt_mul A a p hk, mul_comm]
  exact mul_le_mul_of_nonneg_right (hC k hk) (by positivity)

theorem tsum_swSec_le {ψ : AddChar (AF D.host.F) ℂ} {A B : HSp D} {χ : (AE D)ˣ →* Circle}
    {omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)} (hω : IsWeilDatumO ψ (dblSp A) B 1 χ omh)
    (hb : 2 * A.rank < B.rank)
    {ν : Measure (WO A B)} {𝓕 : Set (WO A B)} (hν : IsCovolOne (ratL B A) ν 𝓕) {φ : WO (dblSp A) B → ℂ}
    (hφ : IsThetaFunO ψ (dblSp A) B φ) :
    ∃ (M : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ y, ∑' q : GlobalTheory.Eis.SiegelCosets A,
      ‖swSec A B omh ν 𝓕 φ ((q.out : GQ (dblSp A)) * y)‖ₑ ≤ ENNReal.ofReal (C * GlobalTheory.Grow.height (dblSp A) y ^ M) := by
  obtain ⟨a, ha⟩ := exists_isMaj A
  have hI := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D A a ha
  obtain ⟨C₁, hC₁, h₁⟩ := norm_swSec_le hω hν hφ a ha
  obtain ⟨C₂, hC₂, h₂⟩ := hgt_mul_le A a ha
  have hb' : (2 * A.rank : ℝ) < B.rank := by exact_mod_cast hb
  have hs := GlobalTheory.Eis.sphConv D A a hI (((B.rank : ℝ) - A.rank) / 2) (by linarith)
  rw [show ((B.rank : ℝ) - A.rank) / 2 + (A.rank : ℝ) / 2 = (B.rank : ℝ) / 2 by ring] at hs
  set S := ∑' q : GlobalTheory.Eis.SiegelCosets A, (hgt A a (q.out : GQ (dblSp A)) : ℝ) ^ ((B.rank : ℝ) / 2) with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => by positivity
  refine ⟨2 * A.rank * B.rank, C₁ * (max C₂ 1) ^ B.rank * S, by positivity, fun y => ?_⟩
  set H := GlobalTheory.Grow.height (dblSp A) y with hH
  have hH1 : 1 ≤ H := GlobalTheory.Grow.one_le_height _ y
  set c := C₁ * (max C₂ 1 * H ^ (2 * A.rank)) ^ B.rank with hc
  have hc0 : 0 ≤ c := by positivity
  have hone : 1 ≤ max C₂ 1 * H ^ (2 * A.rank) :=
    one_le_mul_of_one_le_of_one_le (le_max_right _ _) (one_le_pow₀ hH1)
  have hq : ∀ x : GA D (dblSp A), ‖swSec A B omh ν 𝓕 φ (x * y)‖ ≤ c * (hgt A a x : ℝ) ^ ((B.rank : ℝ) / 2) := by
    intro x
    refine (h₁ _).trans ?_
    rw [hc, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC₁
    have h3 : (hgt A a (x * y) : ℝ) ≤ hgt A a x * (max C₂ 1 * H ^ (2 * A.rank)) :=
      (h₂ x y).trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (NNReal.coe_nonneg _))
    refine (Real.rpow_le_rpow (NNReal.coe_nonneg _) h3 (by positivity)).trans ?_
    rw [Real.mul_rpow (NNReal.coe_nonneg _) (by positivity), mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [← Real.rpow_natCast _ B.rank]
    exact Real.rpow_le_rpow_of_exponent_le hone (by linarith [(Nat.cast_nonneg B.rank : (0 : ℝ) ≤ _)])
  calc _ ≤ ∑' q : GlobalTheory.Eis.SiegelCosets A,
        ENNReal.ofReal (c * (hgt A a (q.out : GQ (dblSp A)) : ℝ) ^ ((B.rank : ℝ) / 2)) :=
        ENNReal.tsum_le_tsum fun q => by
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hq _)
    _ = ENNReal.ofReal (c * S) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) (hs.mul_left c), tsum_mul_left]
    _ = _ := by
        congr 1
        rw [hc, mul_pow, ← pow_mul]; ring

end Global

section Main

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

theorem tsum_lagTerm_le : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → ∃ (M : ℕ) (C : ℝ), ∀ g₁ g₂ : GA D W, ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ ≤ ENNReal.ofReal (C * ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ W g₁ : ℝ) * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ W g₂ : ℝ)) ^ M) := by
  intro D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hs θ hθ f₁ f₂ h₁ h₂
  have hw := hs.weil
  have hS := GlobalTheory.AdjLawPf.adjLaw D ψ hw.std V W
  have hom' := GlobalTheory.ConjAdjWeil.isWeilDatumO_conjAdjoint D ψ V W χV χW om hw
  have hr : ResEta D 1 (GlobalTheory.Doubling.dblSp W).rank := by
    have := GlobalTheory.Eis.SimplePoleModel.resEta_one_two_mul D W.rank
    convert this using 2
    simp [GlobalTheory.Doubling.dblSp]
    omega
  obtain ⟨omh, hω⟩ := GlobalTheory.weilRepresentationUnitaryPair D ψ (GlobalTheory.Doubling.dblSp W) V 1 χV hw.std
    ⟨continuous_const, fun _ => rfl⟩ hw.hecS hr hw.resS
  have TC := GlobalTheory.DoublingTheta.thetaClause D ψ W V χW χV (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjAdjoint om) omh hom' hω
  obtain ⟨hF, hrest⟩ := TC (GlobalTheory.PairLift.dag V W f₂) (GlobalTheory.PairLift.dag V W f₁) (hS.theta _ h₂) (hS.theta _ h₁)
  have dd : ∀ f : WO V W → ℂ, GlobalTheory.PairLift.dag W V (GlobalTheory.PairLift.dag V W f) = f := fun f => by
    funext y; simp only [GlobalTheory.PairLift.dag, hS.invol, Complex.conj_conj]
  obtain ⟨ν, 𝓖', hν⟩ := GlobalTheory.Size.exists_isCovolOne W V
  obtain ⟨M, C, hC, H⟩ := tsum_swSec_le hω hs.big hν hF
  obtain ⟨K, hK, hcmp⟩ := GlobalTheory.Grow.height_comparison W hθ
  refine ⟨M, C * (K * K) ^ M, fun g₁ g₂ => ?_⟩
  have h₁' := hw.om_pres (1, g₁) f₁ h₁
  have h₂' := hw.om_pres (1, g₂) f₂ h₂
  have hF' : IsThetaFunO ψ (GlobalTheory.Doubling.dblSp W) V (GlobalTheory.SWPairProof.dbl V W (om (1, g₁) f₁) (om (1, g₂) f₂)) :=
    (TC _ _ (hS.theta _ h₂') (hS.theta _ h₁')).1
  obtain ⟨e, he⟩ := GlobalTheory.T.siegelEisenstein_doubledTheta_terms_eq_lagrangianIntegrals D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hs _ _ h₁' h₂' ν 𝓖' hν
  have hmove := (hrest g₂ g₁ 1).1
  rw [GlobalTheory.ConjAdjWeil.conjAdjoint_apply, GlobalTheory.ConjAdjWeil.conjAdjoint_apply, dd, dd] at hmove
  have hterm : ∀ q, ‖lagTerm μ 𝓕 (fr (e q)) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ =
      ‖GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.swSec W V omh ν 𝓖' (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta W V (GlobalTheory.PairLift.dag V W f₂) (GlobalTheory.PairLift.dag V W f₁))
        ((q.out : GQ (GlobalTheory.Doubling.dblSp W)) * GlobalTheory.Doubling.io W (g₂, g₁))‖ₑ := by
    intro q
    obtain ⟨c, hc, hq⟩ := he q
    rw [← lagTerm_frame_indep D ψ V W μ 𝓕 hs.covol hw.std _ _ h₁' h₂' (e q) c (fr (e q)) hc (hs.frame _), ← hq]
    have e1 : ((((q.out : GQ (GlobalTheory.Doubling.dblSp W)) : GA D (GlobalTheory.Doubling.dblSp W)) * GlobalTheory.Doubling.io W (g₂, g₁), 1) :
        GA D (GlobalTheory.Doubling.dblSp W) × GA D V) =
        (((q.out : GQ (GlobalTheory.Doubling.dblSp W)) : GA D (GlobalTheory.Doubling.dblSp W)), 1) * (GlobalTheory.Doubling.io W (g₂, g₁), 1) := by
      simp
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.swSec, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.evZero]
    rw [e1, map_mul, Module.End.mul_apply, hmove, map_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul, enorm_mul, ← ofReal_norm ((_ : Circle) : ℂ), Circle.norm_coe, ENNReal.ofReal_one,
      one_mul]
    congr 2
    funext y
    exact (GlobalTheory.RatSubst.om_rat_left_apply D ψ _ V 1 χV omh hω _ hF' _ (q.out : GQ (GlobalTheory.Doubling.dblSp W)).2 _).symm
  rw [← e.tsum_eq]
  simp only [hterm]
  refine (H _).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [mul_assoc, ← mul_pow]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (GlobalTheory.Grow.height_pos _ _).le ?_ M) hC
  refine (GlobalTheory.Grow.IoHeight.height_io_le D W g₂ g₁).trans ?_
  refine (mul_le_mul (hcmp g₂).2 (hcmp g₁).2 (GlobalTheory.Grow.height_pos _ _).le (by positivity)).trans (le_of_eq ?_)
  ring

end Main

end GlobalTheory.SWAbsGrowth

end
