import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseRatAtOfPhaseOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicLiftEqGeometricClassSumAllTuples
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameConstantsOfCharacterisationCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstUpToCenter
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EmbeddingsDifferOnInteger
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortThetaValueComplexPointEqClassicalTheta
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IteratedFDerivSmulAll
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DualHalfLevelMarkingExistsAndMatch
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLiftMarked
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FgOfSmulLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemLatGHat
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AdmissibleColumnsLeAndHarmonicMapCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHomogeneousOfRowDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelsAtRecordCore
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

noncomputable section

namespace GlobalTheory.ShortPtVal

set_option maxHeartbeats 2000000 in

theorem short_value_at_point : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (χ : (AE D)ˣ →* Circle) (c0' : ℂ), (∀ (X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E D.R.r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin D.R.r) (e : Fin g ≃ Lt1 (T.Q.Dw ((i : ℕ) + 1))) (k : GA D (Wc D i)) (xk : (AE D)ˣ) (mk : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)), GlobalTheory.AdTh.IsMod (Wc D i) (rank_Wc i) X → X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q → GlobalTheory.ThFr.IsSympl X bas → GlobalTheory.AdTh.IdxIs T.Q.c (O i).s0 X idx e → GlobalTheory.AdTh.latR (rank_Wc i) (latG (Wc D i) k) = X.Λ → IsDetRoot (Wc D i) k xk → GlobalTheory.Dict.IsMark (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ X.Λ mk → GlobalTheory.AdTh.MarkAd (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ (Wc D i) (rank_Wc i) (iotaW T.J i) k mk → letI : Algebra (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F ℂ := ((O i).s0.comp ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).eF.symm : (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F →+* T.Q.c.F)).toAlgebra; ∀ (y₂ : FrPt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).Xo₂ (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂ ℂ) (A₂ : GlobalTheory.Dict.AnFib X bas idx e (GlobalTheory.AdTh.frMove R.θ (Wc D i) (rank_Wc i) X k (fun τ => T.J.x₀ ((i : ℕ) + 1) (O i).s0 τ.1)) X.Λ y₂), A₂.Marked mk → evR (T.dδ ((i : ℕ) + 1) (Vc D i).rank).Xo₂ (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂ (T.dδ ((i : ℕ) + 1) (Vc D i).rank).cδ y₂ = c0' * ((χ xk : Circle) : ℂ)) → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → ∀ (ζ : ℂ) (φc : (Fin (Vc D i).rank → LevQc (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) → ℂ), ζ ≠ 0 → GlobalTheory.AdTh.hatC (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ φc = (fun q => ζ * (O i).s0 ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).eF.symm ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).w x₀ q))) → ∀ (F₀ : Rul (T.Q.Xo ((i : ℕ) + 1)) T.Q.c), IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N x₀ P F₀ → ∀ (X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E D.R.r) (g' : ℕ) (Dc : GlobalTheory.Dict.Dic (T.Q.Dw ((i : ℕ) + 1)) T.Q.c (O i).s0 X g' (T.Q.Dw ((i : ℕ) + 1)).p (Vc D i).rank (wtA (κ i))) (k : GA D (Wc D i)) (xk : (AE D)ˣ), IsDetRoot (Wc D i) k xk → GlobalTheory.AdTh.IsMod (Wc D i) (rank_Wc i) X → X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q → GlobalTheory.AdTh.latR (rank_Wc i) (latG (Wc D i) k) = X.Λ → GlobalTheory.SW.SelfD X X.Λ → ∀ (x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ D.R.r), x ∈ X.dom → x = GlobalTheory.AdTh.frMove R.θ (Wc D i) (rank_Wc i) X k (fun τ => T.J.x₀ ((i : ℕ) + 1) (O i).s0 τ.1) → ∀ (mk : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)), GlobalTheory.Dict.IsMark T.Q.l X.Λ mk → GlobalTheory.AdTh.MarkAd T.Q.l (Wc D i) (rank_Wc i) (iotaW T.J i) k mk → ∀ (v : GlobalTheory.SW.TF (Vc D i).rank g') (ϑ : (Fin g' → ℂ) → ℂ) (κ' : ℂ), GlobalTheory.SW.IsVac X Dc.bas (T.Q.H.w0 : D.host.E) (GlobalTheory.SW.tens (GlobalTheory.SW.stdL D.host.E (Vc D i).rank) X.Λ) v → (∀ z : Fin (Vc D i).rank → Fin g' → ℂ, ∏ b, ϑ (z b) = κ' * GlobalTheory.SW.thA X Dc.bas Dc.idx v x z) → letI : Algebra T.Q.c.F ℂ := (O i).s0.toAlgebra; ∀ (y : FrPt (T.Q.Xo ((i : ℕ) + 1)) T.Q.c ℂ) (B : GlobalTheory.Dict.AnFib X Dc.bas Dc.idx Dc.e x X.Λ y), B.Marked mk → B.Reads 1 y.s ϑ → ∃ (mk₂ : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)) (Y : (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E), GlobalTheory.Dict.IsMark (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ X.Λ mk₂ ∧ GlobalTheory.AdTh.MarkAd (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ (Wc D i) (rank_Wc i) (iotaW T.J i) k mk₂ ∧ GlobalTheory.Dict.IsRoots (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ X.Λ mk₂ N Y ∧ evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c F₀ y = c0' * ((χ xk : Circle) : ℂ) * ((((O i).s0 (betaH (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ))⁻¹ * ((Λ.mIdx N D.R.r : ℂ))⁻¹ * ((Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) : ℂ))⁻¹ * (Λ.zCard N D.R.r : ℂ)) * κ' * ζ⁻¹ * GlobalTheory.SW.thP X Dc.hr Dc.bas Dc.idx (GlobalTheory.Dict.gphi X Dc.bas (T.Q.H.w0 : D.host.E) Λ.La X.Λ v (GlobalTheory.AdTh.hatC (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ φc) Y) (MvPolynomial.rename Dc.eL (MvPolynomial.map (O i).s0 P)) x) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i hpins χ c0' hcov Λ N x₀ P hUn hTb hTl hLev hAdm hP ζ φc hζ hhat F₀ hF₀
    X g' Dc k xk hk hX hp hΛ hsd x hx hxk mk hm hma v ϑ κ' hv hκ
  intro y B hB hϑ
  subst hxk
  letI : Algebra T.Q.c.F ℂ := (O i).s0.toAlgebra
  letI : Algebra (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F ℂ :=
    ((O i).s0.comp ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).eF.symm :
      (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F →+* T.Q.c.F)).toAlgebra
  have hj := inR i
  have halg : ∀ t : T.Q.c.F, algebraMap (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F ℂ
      ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).eF t) = algebraMap T.Q.c.F ℂ t := fun t => rfl
  have hTie : TieIn T.J R κ v₀ := ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩
  have hs : (O i).s0 = T.J.toCore.σ₀ := sOv_eq _ _ _
  have hσ : GoodEmb T.J.Q.c (O i).s0 := hs ▸ T.J.toCore.good_σ₀
  have hmod := GlobalTheory.AdTh.models_at_record_core D G Pl0 T0 A T.J R F κ v₀ hC hTie i (O i).s0 hs
  obtain ⟨-, -, -, -, hrk, hpq, -, -, -, -, hD, -⟩ := hmod ((O i).dict k).1
  obtain ⟨hemb, -, -, -⟩ := GlobalTheory.PtId.dict_cast T.J hT.j _ hj (O i).s0 hσ (Wc D i) (O i).hV (rank_Wc i)
  have hlev := hT.sh.dLev _ hj (Vc D i).rank
  have hA₂ := hT.lvA _ hj (Vc D i).rank
  have hA : T.Q.l.A = 1 := hT.j.pins.2.1.2
  obtain ⟨mk₂, hm₂, ha₂, hov⟩ := GlobalTheory.AdMark.exists_marking D _ _ T.Q.l (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ (Wc D i) _
    (rank_Wc i) (iotaW T.J i) hemb (hlev.2.1 ▸ dvd_mul_right _ _) (hlev.2.2.2.1 ▸ Ideal.mul_le_left) k
  rw [hΛ] at hm₂ hov
  have hM : 0 < (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M := lt_of_lt_of_le (by norm_num) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.three_le
  obtain ⟨Y, hY⟩ := (GlobalTheory.Dict.DualMark.dual_marking _ _ _ (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ _ _ _ mk₂ _ hsd hm₂
    (Complex.isPrimitiveRoot_exp _ hM.ne')).2.2.2.2 (Vc D i).rank N hLev.1.pos
  refine ⟨mk₂, Y, hm₂, ha₂, hY, ?_⟩
  obtain ⟨y₂, B₂, hov₂, hB₂, hrd⟩ := GlobalTheory.Dict.MarkLift.exists_lift_marked _ _ _ _ _ T.Q.c _
    (T.dδ ((i : ℕ) + 1) (Vc D i).rank) halg hlev hA hA₂ (fun e0 => absurd e0 hpq) _ g' X Dc.bas Dc.idx Dc.e _ X.Λ y B
    Dc.sympl hx hsd mk mk₂ hm hB hm₂ (hov mk hm.mem hma)
  obtain ⟨vv, hvv, hev⟩ := hF₀ ℂ halg y y₂ hov₂
  obtain ⟨_, hnab'⟩ := hT.sh.dNab _ hj (Vc D i).rank
  have hVset : Λ.La ∈ GlobalTheory.SW.Vset D.host.E (Vc D i).rank (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M :=
    (GlobalTheory.Dict.GenLatCmp.genLat_vset _ _ Λ.La).2.1 _ N hM hUn hTl hLev
  have hP2 := (GlobalTheory.admissible_columns_le_and_harmonic_map_cover _ _ _ _ _ _ _ (T.dδ ((i : ℕ) + 1) (Vc D i).rank)).2 (wtA (κ i)) _ hP.1
  have e1 := GlobalTheory.Dict.shortValAt_eq_thP GlobalTheory.ChartFree.chartIndep _ _ _ _ _ _ D.R.r g' X Dc.bas Dc.idx Dc.e _ X.Λ y₂ B₂
    Dc.sympl hx hsd _ (Vc D i).rank Dc.hr Dc.eL hrk hD.2 Dc.dir_eq _ hnab' ϑ v κ' (hrd ϑ hϑ) hv hκ mk₂ hm₂ hB₂
    Λ.La hVset N hLev Y hY (wtA (κ i)) _ hP2 _ _ vv hvv
  have hc := hcov X g' Dc.bas Dc.idx Dc.e k xk mk₂ hX hp Dc.sympl ⟨Dc.per_eq, Dc.ty_eq⟩ hΛ hk hm₂ ha₂ y₂ B₂ hB₂
  rw [hev, e1, hc]
  have hW : (fun q => algebraMap (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F ℂ ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).w x₀ q)) =
      ζ⁻¹ • GlobalTheory.AdTh.hatC (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ φc := by
    funext q
    rw [hhat, Pi.smul_apply, smul_eq_mul, inv_mul_cancel_left₀ hζ]
    rfl
  have hpoly : MvPolynomial.map (algebraMap (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F ℂ)
      (MvPolynomial.map ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).eF : T.Q.c.F →+* (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F) P) =
      MvPolynomial.map (O i).s0 P := by
    rw [MvPolynomial.map_map]
    congr 1
  have hg : ∀ (W : (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) → ℂ) (a : ℂ),
      GlobalTheory.Dict.gphi X Dc.bas (T.Q.H.w0 : D.host.E) Λ.La X.Λ v (a • W) Y =
        a • GlobalTheory.Dict.gphi X Dc.bas (T.Q.H.w0 : D.host.E) Λ.La X.Λ v W Y := fun W a => by
    simp only [GlobalTheory.Dict.gphi, Pi.smul_apply, smul_eq_mul, mul_smul]
    rw [smul_finsum]
  have hs0 : ∀ t : T.Q.c.F, algebraMap T.Q.c.F ℂ t = (O i).s0 t := fun t => rfl
  rw [hW, hpoly, hg, GlobalTheory.Dict.ShortPt.theta_smul₂]
  simp only [map_mul, map_inv₀, map_natCast, halg, hs0]
  ring

end GlobalTheory.ShortPtVal
