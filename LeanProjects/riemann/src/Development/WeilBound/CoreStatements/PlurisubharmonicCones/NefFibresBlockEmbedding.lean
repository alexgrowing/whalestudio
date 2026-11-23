import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExists
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeLatticeFlagStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.TrivFlagHodgeStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsCurvePoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

open GroundTheory.Heights₂.Heights ReciprocityTheory.ChartRestriction.G.AI.I1 MvPolynomial in
theorem LevelTowerAlt.nef_fibres_block_embedding : PB.Inputs → ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] [CharZero Ω] (i : Ω →+* Ω') (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (a : K → ℤ) (a' : K' → ℤ), Function.Injective bk → (∀ k x, y' ⟨bk k, bx k x⟩ = i (y ⟨k, x⟩)) → (∀ k, ∃ x, y' ⟨k, x⟩ ≠ 0) → (∀ k, a' (bk k) = a k) → (∀ k', k' ∉ Set.range bk → a' k' = 0) → NefOnFibres (mCoordIdeal y') a' → NefOnFibres (mCoordIdeal y) a := by
  classical
  intro _ Ω Ω' _ _ _ i K K' _ _ J J' _ _ y y' bk bx a a' hbk hy hy' ha ha' hnef W hW hle hchar hdim
  have hp : (charOf W).Prime := PB.prime_charOf_of_ne_zero hW.1 hchar
  have hpW := Inter.C_charOf_mem W
  generalize charOf W = p at hp hpW
  have : Fact p.Prime := ⟨hp⟩
  let v : (Σ k, J k) → Σ k, J' k := fun x => ⟨bk x.1, bx x.1 x.2⟩
  have hv : IsBlockMap bk v := by
    refine ⟨hbk, ?_, fun _ => rfl, ?_⟩
    · rintro ⟨k, x⟩ ⟨k₁, x₁⟩ h
      obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.1 h
      obtain rfl := hbk h1
      obtain rfl := (bx k).injective (eq_of_heq h2)
      rfl
    · rintro ⟨_, x⟩ ⟨k, rfl⟩
      exact ⟨⟨k, (bx k).symm x⟩, by simp [v]⟩
  obtain ⟨L, _, _, w, c, hL, hc, hw⟩ := LevelTowerAlt.exists_curve_point p hW hpW hdim
  have hle' : mCoordIdeal (fun x : Σ k, J k => y' ⟨bk x.1, bx x.1 x.2⟩) ≤ mCoordIdeal w := by
    simp only [hy]
    rw [hw, CoordinateConeArithVar.mCoordIdeal_comp i y]
    exact hle
  obtain ⟨k₀, L₁, _, _, σ, _, _, w₀, w', h1, h2, h3, h4⟩ := LevelTowerAlt.exists_lift_blk y' bk bx hbk hy' w c hc hle'
  have : CharP L p := charP_of_injective_algebraMap (algebraMap (ZMod p) L).injective p
  have : CharP k₀ p := σ.charP σ.injective p
  have : CharP L₁ p := charP_of_injective_algebraMap (algebraMap k₀ L₁).injective p
  let _ : Algebra (ZMod p) k₀ := ZMod.algebra k₀ p
  let _ : Algebra (ZMod p) L₁ := ZMod.algebra L₁ p
  have : IsScalarTower (ZMod p) k₀ L₁ := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hL₁ : Algebra.trdeg (ZMod p) L₁ ≤ 1 := by
    rw [← trdeg_add_eq (ZMod p) k₀, trdeg_eq_zero (R := k₀), add_zero, ← hL]
    exact trdeg_le_of_injective ⟨σ, fun r => RingHom.congr_fun
      (Subsingleton.elim (σ.comp (algebraMap (ZMod p) k₀)) (algebraMap (ZMod p) L)) r⟩ σ.injective
  obtain ⟨hpW', m, hm, hmd⟩ := LevelTowerAlt.dim_le p hL₁ w'
  choose c' hc' using h3
  have hW' : IsMultiProjPrime (mCoordIdeal w') := ⟨RingHom.ker_isPrime _, CoordinateConeArithVar.isMultiHomogIdeal w',
    CoordinateConeArithVar.relevant w' c' hc'⟩
  have himg : AI.I4.imageZ v (mCoordIdeal w') = W := by
    rw [← Inter.BlockRatioAlgebraic.mCoordIdeal_comp_v hv, ← hw, ← funext h1,
      CoordinateConeArithVar.mCoordIdeal_comp σ w₀, ← CoordinateConeArithVar.mCoordIdeal_comp (algebraMap k₀ L₁) w₀]
    exact congrArg _ (funext h2)
  have hQ' := LevelTowerAlt.map_red_prime p hW' hpW'
  have hcm' := Bridge.GeoNum.comap_map_eq p (LevelTowerAlt.ker_red_le p hpW')
  have hcm := Bridge.GeoNum.comap_map_eq p (LevelTowerAlt.ker_red_le p hpW)
  set Q' := (mCoordIdeal w').map (Bridge.GeoNum.red p) with hQ'_def
  set Q := W.map (Bridge.GeoNum.red p) with hQ_def
  have hiv : imageVar (ZMod p) v Q' = Q := by
    ext f
    obtain ⟨g, rfl⟩ := Bridge.GeoNum.red_surjective p f
    change rename v (Bridge.GeoNum.red p g) ∈ Q' ↔ g ∈ Q.comap (Bridge.GeoNum.red p)
    rw [hcm, ← himg, Bridge.GeoNum.red, ← map_rename]
    change rename v g ∈ Q'.comap (Bridge.GeoNum.red p) ↔ _
    rw [hcm']
    rfl
  have hQd : ringKrullDim (MRingOver (ZMod p) J ⧸ Q) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [← ringKrullDim_eq_of_ringEquiv (Bridge.GeoNum.quotEquiv p Q), hcm]
    exact hdim
  have hcd : FieldNumbers.relDim (FieldNumbers.contractPrime (Targets.ProjContract.emb hv) Q') =
      ((1 : ℕ) : WithBot (WithTop ℤ)) := by
    rw [FieldNumbers.CutRegular.relDim_eq_natCast_iff, ← Targets.ProjContract.ringKrullDim_imageVar hv, hiv]
    exact hQd
  have hge := FieldNumbers.ContractRelDimLe.proof (ZMod p) K K' (Targets.ProjContract.emb hv) J' Q' hQ'
  have hrel : FieldNumbers.relDim Q' = ((((m : ℤ) - Fintype.card K' : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) := by
    unfold FieldNumbers.relDim
    rw [hmd]
    rfl
  have hm' : m = 1 + Fintype.card K' := by
    rw [hcd, hrel] at hge
    have h5 : ((1 : ℕ) : ℤ) ≤ (m : ℤ) - Fintype.card K' :=
      WithTop.coe_le_coe.1 (WithBot.coe_le_coe.1 hge)
    omega
  subst hm'
  have hQ'd := (FieldNumbers.CutRegular.relDim_eq_natCast_iff Q' 1).2 hmd
  have hdim' : ringKrullDim (MRing J' ⧸ mCoordIdeal w') = ((1 + Fintype.card K' : ℕ) : WithBot ℕ∞) := by
    rw [← hcm', ringKrullDim_eq_of_ringEquiv (Bridge.GeoNum.quotEquiv p Q')]
    exact hmd
  have h6 := hnef _ hW' h4 (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.charOf_ne_zero_of_mem hp.ne_zero (by simpa using hpW')) hdim'
  rw [← Bridge.intNum_map_eq_geoNum p 1 _ hW' hpW' hdim'] at h6
  rw [← Bridge.intNum_map_eq_geoNum p 1 _ hW hpW hdim]
  have := hQ'.isPrime
  have h7 := (GlobalTheory.CompanionTheory.FieldNumbers.projectionFormulaDegree (ZMod p) K K' (Targets.ProjContract.emb hv) J' Q' hQ' 1
    hQ'd hcd fun _ => a).2
  have h8 := FieldNumbers.FunctionFieldFinite.proof FieldNumbers.MChartDehomog.proof
    (FieldNumbers.MChartTrdeg.proof FieldNumbers.MChartHomog.proof) (ZMod p) K K' (Targets.ProjContract.emb hv) J' Q'
    hQ' (hcd.trans hQ'd.symm)
  have h9 : FieldNumbers.pullDeg (Targets.ProjContract.emb hv) a = a' := by
    funext k'
    by_cases hk : k' ∈ Set.range bk
    · obtain ⟨k, rfl⟩ := hk
      rw [ha]
      exact hbk.extend_apply _ _ k
    · rw [ha' k' hk]
      exact Function.extend_apply' _ _ _ hk
  have h10 := FieldNumbers.RenameIntNum.full (ZMod p) K K J (fun k => J' (Targets.ProjContract.emb hv k))
    (Equiv.refl K) (Targets.ProjContract.blockEquiv hv)
    (fun x => hbk ((congrArg Sigma.fst (Targets.ProjContract.blockIncl_blockEquiv hv x))))
    (FieldNumbers.contractPrime (Targets.ProjContract.emb hv) Q') 1 fun _ => a
  have h11 : NumbersDVR.intNum (ZMod p) Q (fun _ : Fin 1 => a) =
      NumbersDVR.intNum (ZMod p) (FieldNumbers.contractPrime (Targets.ProjContract.emb hv) Q') (fun _ : Fin 1 => a) := by
    rw [← hiv, Targets.ProjContract.imageVar_eq hv]
    exact h10
  rw [h9, ← h11] at h7
  change 0 ≤ NumbersDVR.intNum (ZMod p) Q' (fun _ : Fin 1 => a') at h6
  rw [h7] at h6
  exact nonneg_of_mul_nonneg_right h6 (by exact_mod_cast Nat.pos_of_ne_zero h8)
