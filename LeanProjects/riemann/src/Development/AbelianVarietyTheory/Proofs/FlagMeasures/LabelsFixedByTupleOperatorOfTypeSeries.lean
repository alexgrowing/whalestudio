import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalActIntertwines
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTIota
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemRowsFixedByLabelTupleOpOfSumFixedStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMaximalCompactReductionStandardFrameStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumSeriesIdempotentCoeffRightTranslationStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedVectorIdentityIsotypicConjugateTypeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

noncomputable section

namespace GlobalTheory.LabPinTop

theorem kap_mem_GfC {D : D7} (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0))
    (k : X.B.I.Gf) : kap X h t k ∈ GfC (Yc D 0) := by
  have aux : ∀ (I : Formalism.MainNotions.S.AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D) (k : I.Gf),
      ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA hI.symm)).symm ((1, k) : I.GA) ∈ GfC (D.sp.Y 0) := by
    intro I hI k
    subst hI
    have e : ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA (rfl : Formalism.L2.SG.InstExistsPf.instOf D = _).symm)).symm (1, k) =
        (Formalism.IndefR.RationalEmbedding.iota D).symm (1, k) := rfl
    rw [e]
    exact (Formalism.L2.SG.EvalTIota.brg_mem_GfC_i (D := D) (1, k)).2 rfl
  have hy : (iotaX X h).symm ((1, k) : X.B.I.GA) ∈ GfC (D.sp.Y 0) := aux X.B.I h k
  show (t⁻¹ * (iotaX X h).symm (1, k) * t : GA D (D.sp.Y 0)) ∈ GfC (D.sp.Y 0)
  unfold GfC at hy ⊢
  rw [MonoidHom.mem_ker] at hy ⊢
  rw [map_mul, map_mul, hy, mul_one, map_inv, inv_mul_cancel]

theorem R_translate_ae {D : D7} (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0))
    (Φ : GA D (D.sp.Y 0) → ℂ) (hinv : ∀ γ ∈ GQ (D.sp.Y 0), ∀ g, Φ (γ * g) = Φ g) (f : L2X X)
    (hf : f =ᵐ[muX X] fun x => Φ ((iotaX X h).symm x * t)) (k : X.B.I.Gf) :
    ((X.B.R (1, k) f : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X] fun x =>
      Φ ((iotaX X h).symm x * t * (show GA D (D.sp.Y 0) from kap X h t k)) := by
  have hU : X.B.μf.IsMulRightInvariant := Formalism.L2.SG.Closed.GfUnimod_holds X.B.I X.B.μf
  have := Formalism.MainNotions.LeviCoordinates.rr_muA_left X.B.I X.B.μf
  have hFD := Formalism.MainNotions.LeviCoordinates.rr_FD_of X.B.I X.B.μf X.B.fund X.B.fund_spec
  have hφinv : ∀ γ ∈ X.B.I.GFset, ∀ y : X.B.I.GA,
      Φ ((iotaX X h).symm (γ * y) * t) = Φ ((iotaX X h).symm y * t) := by
    intro γ hγ y
    rw [map_mul, mul_assoc]
    exact hinv _ (iotaX_symm_rat X h γ hγ) _
  have hP : Formalism.L2.SG.Pf.RPres (X.B.I.muA X.B.μf) ((1, k) : X.B.I.GA) :=
    Formalism.L2.SG.Pf.RowDictPf.rp_fin X.B.I X.B.μf k
  have hPi : Formalism.L2.SG.Pf.RPres (X.B.I.muA X.B.μf) (((1, k) : X.B.I.GA)⁻¹) := by
    have : ((1, k) : X.B.I.GA)⁻¹ = (1, k⁻¹) := Prod.ext inv_one rfl
    rw [this]; exact Formalism.L2.SG.Pf.RowDictPf.rp_fin X.B.I X.B.μf k⁻¹
  obtain ⟨h1, h2⟩ := Formalism.L2.SG.Pf.rp_map hFD hP hPi
  have e1 := X.B.R_spec (1, k) f
  have e3 : ∀ᵐ x ∂(muX X), (f : X.B.I.GA → ℂ) (X.B.I.rep X.B.fund (x * (1, k))) =
      Φ ((iotaX X h).symm (X.B.I.rep X.B.fund (x * (1, k))) * t) := by
    refine ae_of_ae_map (p := fun y => (f : X.B.I.GA → ℂ) y = Φ ((iotaX X h).symm y * t)) h1 ?_
    rw [h2]
    exact hf
  filter_upwards [e1, e3] with x a1 a3
  rw [a1]
  show (f : X.B.I.GA → ℂ) (X.B.I.rep X.B.fund (x * (1, k))) = _
  rw [a3]
  obtain ⟨γ, hγ, hrep, -⟩ := Formalism.MainNotions.LeviCoordinates.rr_rep_spec hFD (x * (1, k))
  rw [Formalism.MainNotions.LeviCoordinates.rr_rep_eq_rep, show (Formalism.MainNotions.LeviCoordinates.rr_rep X.B.I.GFset X.B.fund (x * (1, k))) = γ * (x * (1, k)) from hrep,
    hφinv γ hγ]
  congr 1
  unfold kap
  rw [map_mul]
  group

end GlobalTheory.LabPinTop

namespace GlobalTheory.LabPinTop

theorem labTie_of_series : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)) (PY : RowPsi (Yc D 0) D.R.r) (hF : D.host.F = maximalRealSubfield D.host.E) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H) (G : GoodOp X) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G) (ι : D.s.HH ≃ₗᵢ[ℂ] HHX X) (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (C : Submodule ℂ (MMap (R.MY 0))), StdPsi hF PY → (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ F, ι (D.sEE F) = conjHH X G (j F)) → RowJ R eE X h G t j → (∀ σ, R.HE.e (eE (D.what₂.onb σ)) ∈ isotIn (actM PY (R.MY 0)) C (FinTyp.conjT (rep (D.what₂.ft σ)))) → (∀ σ, ∀ k ∈ X.B.I.Kg X.B.g, ∀ v y, R.HE.e (eE (D.what₂.onb σ)) v (y * kap X h t k) = R.HE.e (eE (D.what₂.onb σ)) v y) → (∀ σ v, ∀ γ ∈ Formalism.L2.Theta.GQ (Yc D 0), ∀ y, R.HE.e (eE (D.what₂.onb σ)) v (γ * y) = R.HE.e (eE (D.what₂.onb σ)) v y) → TypeLab D rep → (∀ σ, D.ntypes.goodTuple (labOf σ)) → LabTie X ι := by
  intro D X h t PY hF G' _ _ Pl0 T A Ks _ _ _ R eE G j ι rep C hStd hHEq hι hJ hiso hK hQ hTL hgood
  let _ : Fintype (G0g D.nd) := Formalism.MainNotions.PrimeDegreeVariant.finiteLevelGroupFintype D
  have hlab : ∀ σ k v, IsLabel D k (D.nd.lab k (D.what₂.ft σ) v) := fun σ k v => ((hTL (D.what₂.ft σ)) k v).1
  refine ⟨hlab, hgood, fun σ => ?_⟩
  obtain ⟨c, red, hFR⟩ := GlobalTheory.T.exists_maximalCompact_reduction_standardFrame D X h t PY hF hStd hHEq
  have hRH : IsRedHom X red := hFR.1
  choose sec hsec using hRH.2.2.1
  have hIS : IsSec X red sec := fun γ => hsec γ
  choose lf hlf using fun γ => PY.onto _ (kap_mem_GfC X h t (sec γ))
  have hser := GlobalTheory.T.sum_seriesIdempotentCoeff_rightTranslation D X h t PY c red sec lf hFR hIS hlf (rep (D.what₂.ft σ)) (labOf σ) (hTL (D.what₂.ft σ))
  have hS := GlobalTheory.T.fixedVectorIdentity_isotypic_conjugateType D D.R.r (MMap (R.MY 0)) (actM PY (R.MY 0)) C (rep (D.what₂.ft σ))
    {κ | ∃ k ∈ X.B.I.Kg X.B.g, PY.ψ κ = kap X h t k} (G0g D.nd) (serCoef (labOf σ)) lf
    (fun φ hφ hU => hser φ hφ (fun k hk κ hκ => hU κ ⟨k, hk, hκ⟩)) (R.HE.e (eE (D.what₂.onb σ))) (hiso σ)
    (by
      rintro κ ⟨k, hk, hκ⟩
      refine MultilinearMap.ext fun v => funext fun y => ?_
      rw [actM_apply, hκ]
      exact hK σ k hk v y)
  have hpt : ∀ v y, ∑ γ, star (serCoef (labOf σ) γ) * R.HE.e (eE (D.what₂.onb σ)) v (y * kap X h t (sec γ)) =
      R.HE.e (eE (D.what₂.onb σ)) v y := by
    intro v y
    have e := congrArg (fun T : MMap (R.MY 0) => T v y) hS
    simp only [finsum_eq_sum_of_fintype] at e
    rw [← e, sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [smul_apply, Pi.smul_apply, smul_eq_mul, actM_apply, hlf]
  obtain ⟨v₀, -, a, -, hj⟩ := hJ
  refine GlobalTheory.T.mem_rowsFixedByLabelTupleOp_of_sum_fixed D X red sec hRH hIS (labOf σ) (fun k v => hlab σ k v) (bRow X ι σ)
    (ι (D.sEE (D.what₂.onb σ))).2 ?_
  set Φ : GA D (D.sp.Y 0) → ℂ := fun y => star ((a : ℂ) * R.HE.e (eE (D.what₂.onb σ)) v₀ y) with hΦ
  have hΦinv : ∀ γ ∈ GQ (D.sp.Y 0), ∀ g, Φ (γ * g) = Φ g := fun γ hγ g =>
    congrArg (fun z => star ((a : ℂ) * z)) (hQ σ v₀ γ hγ g)
  have hb : bRow X ι σ = star ((j (D.what₂.onb σ) : EEC X G) : L2X X) := by
    show ((ι (D.sEE (D.what₂.onb σ)) : HHX X) : L2X X) = _
    rw [hι]
    rfl
  have hbr : (bRow X ι σ : X.B.I.GA → ℂ) =ᵐ[muX X] fun x => Φ ((iotaX X h).symm x * t) := by
    rw [hb]
    filter_upwards [Lp.coeFn_star ((j (D.what₂.onb σ) : EEC X G) : L2X X), hj (D.what₂.onb σ)] with x b1 b2
    rw [b1, Pi.star_apply, b2]
    rfl
  have htr := fun γ => R_translate_ae X h t Φ hΦinv (bRow X ι σ) hbr (sec γ)
  rw [finsum_eq_sum_of_fintype]
  apply Lp.ext
  filter_upwards [coeFn_sum_smul (μ := muX X) (serCoef (labOf σ)) (fun γ => X.B.R ((1, sec γ) : X.B.I.GA) (bRow X ι σ)),
    ae_all_iff.2 htr, hbr] with x b1 b2 b3
  rw [b1, b3]
  simp only [b2, hΦ]
  rw [← hpt v₀ ((iotaX X h).symm x * t)]
  rw [Finset.mul_sum, star_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  have e : ∀ (c b s : ℂ), c * star (b * s) = star (b * (star c * s)) := fun c b s => by
    simp only [star_mul', star_star]; ring
  exact e _ _ _

end GlobalTheory.LabPinTop
