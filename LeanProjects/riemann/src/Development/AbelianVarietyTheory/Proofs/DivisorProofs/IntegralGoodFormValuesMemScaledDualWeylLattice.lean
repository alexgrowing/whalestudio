import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Definitions.Divisors.FrameSignSimple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfinitePsiBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorDecompositionEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalFormCoordinatesCoeffMemCoefficientField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BranchingPairingMemCoefficientField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSmulMemOfLeLocP
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeExtensionAlongFieldEmbeddingDuals
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FormFinVal

open GlobalTheory.CoefModel
open scoped TensorProduct

section Lat

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}

private theorem nabAt_map (emb : ι → E →+* K) (lam : ι → DomWeight n) (γ : GL (Fin n) E) (M : Submodule (𝓞 E) (Fin n → E))
    (x : VV K lam) (hx : x ∈ nabAt emb lam M) :
    rhoV emb lam γ x ∈ nabAt emb lam (M.map ((Matrix.mulVecLin (γ : Matrix (Fin n) (Fin n) E)).restrictScalars (𝓞 E))) := by
  unfold nabAt
  simp_rw [tauLatG E K ι n emb]
  exact (Formalism.L2.Col.nabK_gLat lam _ (embGL emb γ)).ge ⟨x, hx, rfl⟩

omit [NumberField K] in
private theorem invTr_invTr (B : GL (Fin n) K) : inside₂ K n (inside₂ K n B) = B := by
  apply Units.ext
  simp [inside₂]

private theorem isBasisAt_of_dualFr (w : HeightOneSpectrum (𝓞 K)) {M : Submodule (𝓞 K) (Fin n → K)}
    (hM : Submodule.IsLattice K M) {B : GL (Fin n) K} (hB : IsBasisAt w (dualFr M) B) : IsBasisAt w M (inside₂ K n B) := by
  obtain ⟨B₀, h₀⟩ := GlobalTheory.LatBasisAt.basisAtEx K n M hM w
  have h1 : IsBasisAt w (colLat (inside₂ K n B₀)) B :=
    Eq.trans (Eq.symm (GlobalTheory.DualWeylDual.isBasisAt_dualFr w hM.fg h₀)) hB
  have h2 := GlobalTheory.DualWeylDual.isBasisAt_dualFr w (Submodule.fg_span (Set.finite_range _)) h1
  rw [show Submodule.span (𝓞 K) _ = colLat (inside₂ K n B₀) from rfl, GlobalTheory.DualWeylDual.dualFr_colLat, invTr_invTr] at h2
  exact Eq.trans h₀ h2

private theorem funEquiv_nabK (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K))
    (hM : ∀ τ, Submodule.IsLattice K (M τ)) (F : VV K lam) (hF : F ∈ nabK lam M) :
    funEquiv lam F ∈ nabK (fun τ => (lam τ).dual) fun τ => dualFr (M τ) := by
  have hF' : F.1 ∈ transLat lam (nabStd K lam) M := hF
  show (funEquiv lam F).1 ∈ transLat _ (nabStd K _) _
  simp only [transLat, Submodule.mem_iInf] at hF' ⊢
  intro w B hB
  obtain ⟨s, hs, h⟩ := hF' w (invTrK B) fun τ => isBasisAt_of_dualFr w (hM τ) (hB τ)
  refine ⟨s, hs, ?_⟩
  have h1 := (funEquiv_mem_nabStd lam ((s : K) • rhoK lam (invTrK B)⁻¹ F)).1 h
  have e : invTrK (invTrK B)⁻¹ = B⁻¹ := by
    rw [map_inv]
    exact congrArg (·⁻¹) (funext fun τ => invTr_invTr (B τ))
  rw [map_smul, funEquiv_rhoK, e] at h1
  exact h1

private theorem funEquiv_mapVV {K : Type} [Field K] (φ : K →+* ℂ) (lam : ι → DomWeight n) (F : VV K lam) :
    funEquiv lam (mapVV φ lam F) = mapVV φ _ (funEquiv lam F) :=
  ((isFunForm_iff_eq lam _ _).1 (GlobalTheory.BrRat.isFunForm_map φ lam (isFunForm_funEquiv lam F))).symm

end Lat

section Ad

variable {D : D7}

private theorem mem_hLat (V : HSp D) (g : Bridge.Gf V) (x : Fin V.rank → D.host.E) :
    x ∈ Bridge.hLat V g ↔ (g.1⁻¹).1 *ᵥ (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i) ∈
      GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
  rw [← SetLike.mem_coe, GlobalTheory.RepsCompare.coe_hLat, ← GlobalTheory.RepsCompare.inv_mulVec_mem_iff]
  rfl

private theorem hLat_mul_lev {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) (L : LevDat D.host.E ℂ V.rank) (h : Bridge.Gf V) (k : (levEnv V β L).J) :
    Bridge.hLat V (h * k) = Bridge.hLat V h := by
  have key : ∀ (h : Bridge.Gf V) (k : Bridge.Gf V), k ∈ (levEnv V β L).J → Bridge.hLat V h ≤ Bridge.hLat V (h * k) := by
    intro h k hk x hx
    rw [mem_hLat, ← GlobalTheory.PrincInLevel.eq_latC hβ] at hx ⊢
    have h1 := GlobalTheory.RepsCompare.mulVec_mem_hat hβ L (inv_mem hk) hx
    rw [Matrix.mulVec_mulVec, ← Units.val_mul] at h1
    rwa [Subgroup.coe_mul, _root_.mul_inv_rev]
  refine le_antisymm ?_ (key h k k.2)
  have := key (h * k) (k : Bridge.Gf V)⁻¹ (inv_mem k.2)
  rwa [mul_inv_cancel_right] at this

private theorem hLat_rat (V : HSp D) (γ : GQ V) (γE : GL (Fin V.rank) D.host.E) (hγ : Bridge.IsRatMat V γ γE) (h : Bridge.Gf V) :
    Bridge.hLat V (Bridge.ratF V γ * h) = (Bridge.hLat V h).map (γE.1.mulVecLin.restrictScalars (𝓞 D.host.E)) := by
  let φ : D.host.E →+* Af D.host.F ⊗[D.host.F] D.host.E := inclR (F := D.host.F) (Af D.host.F)
  have e1 : (Bridge.ratF V γ).1 = Formalism.UG.bc φ γE := by
    show Formalism.UG.bc _ (matHom V γ.1) = _
    rw [show matHom V γ.1 = _ from hγ]
    apply Units.ext
    ext i j
    rfl
  have e2 : ∀ x : Fin V.rank → D.host.E, x ∈ Bridge.hLat V (Bridge.ratF V γ * h) ↔ (γE⁻¹).1 *ᵥ x ∈ Bridge.hLat V h := by
    intro x
    have e3 : (Formalism.UG.bc φ γE⁻¹).1 *ᵥ (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i) =
        fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] ((γE⁻¹).1 *ᵥ x) i := by
      funext i
      exact (RingHom.map_mulVec φ (γE⁻¹).1 x i).symm
    rw [mem_hLat, mem_hLat, Subgroup.coe_mul, _root_.mul_inv_rev, e1, Units.val_mul, ← Matrix.mulVec_mulVec, ← map_inv, e3]
  ext x
  rw [e2]
  constructor
  · intro hx
    refine ⟨_, hx, ?_⟩
    show γE.1 *ᵥ ((γE⁻¹).1 *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  · rintro ⟨z, hz, rfl⟩
    show (γE⁻¹).1 *ᵥ (γE.1 *ᵥ z) ∈ _
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

private theorem globLat_eq {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) (g : GA D V) :
    Formalism.UG.CS.globLat (Lev.finE V g) Λ = Bridge.hLat V ((finHom V).rangeRestrict g) := by
  ext x
  rw [mem_hLat, ← GlobalTheory.PrincInLevel.eq_latC hβ]
  have e : ((Formalism.UG.bc (Lev.swapAE D) (finHom V g))⁻¹).1 *ᵥ
      (fun i => Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i)) =
      fun i => Algebra.TensorProduct.comm D.host.F _ D.host.E
        ((((finHom V g)⁻¹).1 *ᵥ (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i)) i) := by
    rw [← map_inv]
    funext i
    change _ = Lev.swapAE D _
    rw [RingHom.map_mulVec (Lev.swapAE D)]
    rfl
  change ((Formalism.UG.bc (Lev.swapAE D) (finHom V g))⁻¹).1 *ᵥ
    (fun i => Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔ _
  rw [e]
  constructor
  · intro hz
    have := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ hz
    simp only [AlgEquiv.symm_apply_apply] at this
    exact this
  · intro hz
    exact GlobalTheory.PrincInLevel.swap_mem_hatL Λ _ hz

private theorem ext_mem {V : HSp D} {C : Bridge.CoefDat D V} {S : CSD D.what₂.LL} {J : Subgroup (Bridge.Gf V)}
    {χ : J →* ℂˣ} {P : Bridge.ClassPres (Bridge.ratF V) S D.what₂.embLL C.ρ J χ} {lam : D.what₂.Tau → DomWeight V.rank}
    {c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] C.W} {pair del}
    (hc : Bridge.CoefTie V C P lam c0 pair (nabAt (labLL D) lam) del) (hm : Bridge.CoefMapTie V C c0 (rhoV (labLL D) lam))
    (hJ : ∀ h (k : J), Bridge.hLat V (h * k) = Bridge.hLat V h)
    (f : S.Forms) (hf : ∀ c, (f : S.Cl → S.V) c ∈ S.Nab c) (g : Bridge.Gf V) :
    ∃ (k : J) (u : VV D.what₂.LL lam), u ∈ nabAt (labLL D) lam (Bridge.hLat V g) ∧ P.extL f g = (χ k : ℂ) • c0 u := by
  obtain ⟨e, -, he, -, hN, -⟩ := hc
  obtain ⟨γE, hγ⟩ := GlobalTheory.RationalValues.exists_isRatMat (P.decG g)
  have h1 : e ((f : S.Cl → S.V) (P.decC g)) ∈ nabAt (labLL D) lam (Bridge.hLat V (P.y (P.decC g))) := by
    rw [← hN (P.decC g)]
    exact ⟨_, hf _, rfl⟩
  have e3 : Bridge.hLat V g = (Bridge.hLat V (P.y (P.decC g))).map
      ((γE : Matrix (Fin V.rank) (Fin V.rank) D.host.E).mulVecLin.restrictScalars (𝓞 D.host.E)) :=
    (congrArg (Bridge.hLat V) (P.dec_spec g)).trans ((hJ _ _).trans (hLat_rat V _ γE hγ _))
  refine ⟨P.decK g, rhoV (labLL D) lam γE (e ((f : S.Cl → S.V) (P.decC g))), ?_, ?_⟩
  · exact (congrArg (nabAt (labLL D) lam) e3).ge (nabAt_map (labLL D) lam γE _ _ h1)
  · exact congrArg ((χ (P.decK g) : ℂ) • ·) ((congrArg (C.ρ (P.decG g)) (he _)).trans (hm.1 _ γE hγ _).symm)

private theorem inLat_value {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) (Y : LSp D) (hY : Y = ⟨V, Λ⟩) (h : V.rank = Y.sp.rank) (lam : D.what₂.Tau → DomWeight V.rank)
    (lam' : D.what₂.Tau → DomWeight Y.sp.rank) (hw : ∀ τ a, (lam' τ).w (Fin.cast h a) = (lam τ).w a) (y : GfC Y.sp)
    (v : VV D.what₂.LL lam)
    (hv : v ∈ nabAt (labLL D) lam
      (Bridge.hLat V ((finHom V).rangeRestrict (cast (congrArg (fun X : LSp D => GA D X.sp) hY) y.1))))
    (U : VV ℂ lam')
    (hU : U.1 = MvPolynomial.rename (Prod.map id (Prod.map (Fin.cast h) (Fin.cast h))) (MvPolynomial.map D.what₂.embLL v.1))
    (fr : GL (Fin Y.sp.rank) D.host.E) (w : PlL D) :
    InLat (fun τ => (lam' τ).dual) w 0
      ((Formalism.UG.CS.globLat (finG Y.sp y) Y.lat).comap (fr.1.mulVecLin.restrictScalars (𝓞 D.host.E)))
      (rhoVr (tauE D) _ fr⁻¹ (funOf lam' U)) := by
  subst hY
  have e : lam' = lam := funext fun τ => by
    have := hw τ
    generalize lam' τ = a at this
    generalize lam τ = b at this
    cases a
    cases b
    congr
    funext i
    exact this i
  subst e
  have hr : (Prod.map id (Prod.map (Fin.cast h) (Fin.cast h)) : D.what₂.Tau × Fin V.rank × Fin V.rank → _) = id := by
    funext x
    rfl
  rw [hr, MvPolynomial.rename_id_apply] at hU
  obtain rfl : U = mapVV D.what₂.embLL lam' v := Subtype.ext hU
  rw [(isFunForm_iff_eq _ _ _).1 ((SumModel.readOK lam').1 _), funEquiv_mapVV, TestFunctionNorms.GlobalTheory.CompanionTheory.TestVal.rhoVr_mapVV]
  refine TestFunctionNorms.GlobalTheory.CompanionTheory.TestVal.inLat_of_mem _ w ?_
  have e1 : Formalism.UG.CS.globLat (finG V y) Λ = Bridge.hLat V ((finHom V).rangeRestrict y.1) := globLat_eq hβ y.1
  have e2 := TestFunctionNorms.GlobalTheory.CompanionTheory.TestVal.comap_eq_map fr 1 (Bridge.hLat V ((finHom V).rangeRestrict y.1))
    (Formalism.UG.CS.globLat (finG V y) Λ) fun z => by rw [e1, Units.val_one, Matrix.one_mulVec]
  rw [mul_one] at e2
  refine e2 ▸ TestFunctionNorms.GlobalTheory.CompanionTheory.TestVal.nabAtr_map _ _ _ _ _ ?_
  exact funEquiv_nabK lam' _
    (fun τ => GlobalTheory.TauLat.tauLatLattice _ _ _ _ (labLL D) τ _ (GlobalTheory.RepsCompare.isLattice_hLat _ _)) v hv

end Ad

end GlobalTheory.FormFinVal

set_option maxHeartbeats 1600000 in
open GlobalTheory.FormFinVal in
theorem _root_.GlobalTheory.T.integralGoodForm_values_mem_scaledDualWeylLattice : BigC fun {D} {_} _ _ {_} {_} {A} {_} _ _ _ {R} F ch _ _ => ∀ (t : _) (w : PlL D), ∀ x ∈ (A.fam.R t).Mt (A.fam.lvl F.P0 F.ψ0), ∀ y,
  InLat _ w 0 (latAt ch.S.toGridChoice (.grid 0 D.R.m) y) (rowVal ch.S.toGridChoice (ch.S.formC t (R.jX t (formOf F t x)) y)) := by
  refine ⟨0, fun CF _ => ⟨0, fun ε C _ => ⟨0, ?_⟩⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ _ t w x hx y
  obtain ⟨gram, c₀, c₁, hT, hco⟩ := ch.S.co_is
  have hc := hS.core
  have hf : ∀ c : (A.MtildeCSD t).Cl, (formOf F t x).1 c ∈ (A.MtildeCSD t).Nab c := fun c => hx c (Set.mem_univ c)
  obtain ⟨k, u, hu, hv⟩ := ext_mem (hT.coefR t) hT.mapR (fun h k => hLat_mul_lev hc.lev.βX (R.datXt t) h k) (formOf F t x)
    hf (toXf y)
  have h0 := (congrFun (hc.models.jX t (formOf F t x)) (toXf y)).trans hv
  have i0 : Fin D.R.m := ⟨0, by have := D.R.two_le_m; omega⟩
  obtain ⟨a, ha⟩ := GlobalTheory.FormCoef.typeX_mem R t D.what₂.embLL.fieldRange (GlobalTheory.RationalValues.chiVal_of_chiW R hc.grp.chiW)
    (GlobalTheory.RationalValues.xiR_mem R hc.lev hc.fam.pl_onto hc.fam.muVal hT.ok i0 t) k
  obtain ⟨n, hn, hak⟩ : ∃ n : ℕ, 0 < n ∧ (levEnv D.sp.X' R.βX (R.datXt t)).χ k ^ n = 1 :=
    isOfFinOrder_iff_pow_eq_one.1 (GlobalTheory.LevSplit.levFn_finOrd _ _ _)
  have hak' : a ^ n = 1 := D.what₂.embLL.injective (by rw [map_pow, ha, ← Units.val_pow_eq_pow_val, hak, map_one, Units.val_one])
  have hai : IsIntegral ℤ a := IsIntegral.of_pow hn (by rw [hak']; exact isIntegral_one)
  have h1 : (R.HX t).e (R.jX t (formOf F t x)) (toXf y) = c₀ (a • u) :=
    h0.trans (GlobalTheory.RationalValues.smul_eq_of c₀ ha rfl)
  have hw : ∀ τ a, (listedWt ch.G (.grid 0 D.R.m) τ).w (Fin.cast (rank_zero_m ch.G) a) =
      (Bridge.lamRdef (Ptw D) τ).w a := fun τ a => by
    change (wtOf _ (GlobalTheory.SignedHC.entries (parV D ch.sc.cGap 0 D.R.m τ))).w _ = _
    rw [parV_zero D ch.sc.cGap le_rfl τ]
    exact wtOf_entries_eq (rank_zero_m ch.G) (GlobalTheory.ForcedWeights.lamRForced D τ) a
  exact inLat_value hc.lev.βX (ch.G.node (.grid 0 D.R.m)) (colY_m _) (rank_zero_m ch.G) _ _ hw y (a • u)
    (Submodule.smul_mem _ (⟨a, hai⟩ : 𝓞 D.what₂.LL) hu) _ (by rw [SumChoice.formC, h1, hco]) _ w
