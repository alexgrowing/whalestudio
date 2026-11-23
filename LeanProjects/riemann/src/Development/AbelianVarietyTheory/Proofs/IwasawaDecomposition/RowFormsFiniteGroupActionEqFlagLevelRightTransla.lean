import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsDeco
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagRTup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoratedRowLatticesFlagLevelRightTranslationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RTupQEqOneIff
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.RowAct

section Forms

variable {Xf : Formalism.L2.Col.Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 Xf.E))}
  (C : Formalism.L2.Col.CoefPk Xf n (Formalism.L2.Col.DecoSet Xf.E n ST SG)) (Λ : Formalism.L2.Col.LevFam Xf.E Xf.K n SG)

theorem eqFun_smul_grp (φ : (Formalism.L2.Col.formGSD C Λ).EqFun) (u : Λ.grp) (a : Formalism.L2.Col.GLG Xf.E n SG)
    (d : Formalism.L2.Col.DecoSet Xf.E n ST SG) :
    (φ : Formalism.L2.Col.DecoSet Xf.E n ST SG → C.V) (((1 : Formalism.L2.Col.UF Xf.E n), (u : Formalism.L2.Col.GLG Xf.E n SG) * a) • d) =
      ((Λ.chr u : Xf.Kˣ) : Xf.K) • (φ : Formalism.L2.Col.DecoSet Xf.E n ST SG → C.V) (((1 : Formalism.L2.Col.UF Xf.E n), a) • d) := by
  have e := φ.2 ((1, u) : Formalism.L2.Col.FormG Λ) (((1 : Formalism.L2.Col.UF Xf.E n), a) • d)
  have e' : ((1, u) : Formalism.L2.Col.FormG Λ) • (((1 : Formalism.L2.Col.UF Xf.E n), a) • d) =
      ((1 : Formalism.L2.Col.UF Xf.E n), (u : Formalism.L2.Col.GLG Xf.E n SG) * a) • d := by
    show ((1 : Formalism.L2.Col.UF Xf.E n), (u : Formalism.L2.Col.GLG Xf.E n SG)) • (((1 : Formalism.L2.Col.UF Xf.E n), a) • d) = _
    rw [smul_smul, Prod.mk_mul_mk, one_mul]
  rw [e'] at e
  rw [e]
  show ((Λ.chr u : Xf.Kˣ) : Xf.K) • C.rho 1 _ = _
  rw [map_one]
  rfl

end Forms

theorem semilin_inv_smul {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    {σ : K →+* ℂ} (m : V →ₛₗ[σ] W) (k : K) (c : ℂˣ) (hk : σ k = c) (x : V) :
    m x = ((c⁻¹ : ℂˣ) : ℂ) • m (k • x) := by
  rw [LinearMap.map_smulₛₗ, hk, smul_smul, Units.inv_mul, one_smul]

end GlobalTheory.Mem.R3.RowAct

namespace GlobalTheory.Mem.R3.RowAct

theorem act_tie : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E)
    (c0R : VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W),
    cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) →
    Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) →
    ∀ t, ∀ P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ, GlobalTheory.Mem.R3.RowAd.ReadsDeco X I hX Xg tr cX t P →
      ∃ a : Bridge.ActTie (Bridge.ratF X.toD7.sp.X') P (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q (levEnv X.toD7.sp.X' L.βX (L.datXt t)).ch ((famR X I hX U Xg tr).A.leftGroupActionRight t),
        ∀ q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q,
          eG (a.red q) = rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _)) := by
  intro X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hcX hgram hTie hinner t P hRD
  refine ⟨{
      red := eG.symm.toMonoidHom.comp (rTupQ X.toD7.sp.X' L.βX (L.datXt t))
      red_surj := ?_
      red_ker := ?_
      act_eq := ?_ }, ?_⟩
  · intro g
    have key := GlobalTheory.Mem.R3.FlagOnto.exists_flag_rTup X px I hX U L hI hV hL t (eG g)
    obtain ⟨q, hq⟩ := key
    refine ⟨q, ?_⟩
    have e : rTupQ X.toD7.sp.X' L.βX (L.datXt t) q = eG g := hq
    show eG.symm (rTupQ X.toD7.sp.X' L.βX (L.datXt t) q) = g
    rw [e, MulEquiv.symm_apply_apply]
  · intro q
    have e := rTupQ_eq_one_iff X.toD7.sp.X' L.βX (L.datXt t) q
    show eG.symm (rTupQ X.toD7.sp.X' L.βX (L.datXt t) q) = 1 ↔ _
    exact (MulEquiv.map_eq_one_iff eG.symm).trans e
  · intro g κ hκ f
    obtain ⟨m, hm⟩ := hRD
    obtain ⟨u, hdeco, hch⟩ := GlobalTheory.T.decoratedRowLattices_flagLevel_rightTranslation X px I hX U L eG hI hV hL hG t κ
    have hg : eG.symm (rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((κ : Bridge.Gf X.toD7.sp.X') : GL _ _))) = g := hκ
    rw [hg] at hdeco
    funext h
    have e1 := hm ((famR X I hX U Xg tr).A.leftGroupActionRight t g f) h
    have e2 := hm f (h * (κ : Bridge.Gf X.toD7.sp.X'))
    refine e1.trans ?_
    refine Eq.trans ?_ (congrArg (fun v => (((((levEnv X.toD7.sp.X' L.βX (L.datXt t)).ch κ)⁻¹ : ℂˣ) : ℂ)) • v) e2).symm
    have e3 : ((Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm
        ((famR X I hX U Xg tr).A.leftGroupActionRight t g f) = Formalism.L2.Col.g0HatRepEqFunX X.B.wts I.Ch I.sel t.1 g
          (((Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm f) :=
      LinearEquiv.symm_apply_apply _ _
    have e4 := eqFun_smul_grp _ _ (((Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm f)
      u (Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R) g)⁻¹ (RowAd.decoAd X I t h)
    refine (congrArg (fun ψ : (Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).EqFun =>
      m ((ψ : (Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).D → (Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).V)
        (RowAd.decoAd X I t h))) e3).trans ?_
    refine (semilin_inv_smul m _ _ hch _).trans ?_
    refine congrArg (fun v => (((((levEnv X.toD7.sp.X' L.βX (L.datXt t)).ch κ)⁻¹ : ℂˣ) : ℂ)) • m v) ?_
    exact e4.symm.trans (congrArg _ (hdeco h).symm)
  · intro q
    have e : eG (eG.symm (rTupQ X.toD7.sp.X' L.βX (L.datXt t) q)) = rTupQ X.toD7.sp.X' L.βX (L.datXt t) q :=
      MulEquiv.apply_symm_apply _ _
    exact e

end GlobalTheory.Mem.R3.RowAct
