import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOmPinsLev
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralOfLine
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TensorMapDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisConjDefiniteFormsSemilinearEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicCoreTransportEnlargedCoefficientBase
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.R3.Rw.OmExt

def mapVVι {K K' : Type} [Field K] [Field K'] (ι : K →+* K') {T : Type} [Fintype T] {n : ℕ} (lam : T → DomWeight n)
    (v : VV K lam) : VV K' lam :=
  ⟨MvPolynomial.map ι v.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV ι lam _ v.2⟩

theorem exists_smul_eq_enl {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) {K' : Type} [Field K'] (ι : D.what₂.LL →+* K')
    (emb' : K' →+* ℂ) (hι : ∀ x, emb' (ι x) = D.what₂.embLL x) (tau : D.what₂.Tau → D.host.E →+* D.what₂.LL)
    (tau' : D.what₂.Tau → D.host.E →+* K') (htau : ∀ τ, emb'.comp (tau' τ) = D.what₂.embLL.comp (tau τ))
    {lam : D.what₂.Tau → DomWeight V.rank}
    (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W) (h0 : Bridge.CoefMapTie V c.coef c0 (rhoVr tau lam))
    (c' : CoefA V) (hcc : c' = c) (c0' : VV K' lam →ₛₗ[emb'] c'.W)
    (h1 : ∀ γ γE, Bridge.IsRatMat V γ γE → ∀ v, c0' (rhoVr tau' lam γE v) = c'.coef.ρ γ (c0' v)) :
    ∃ μ : ℂ, ∀ (v : VV D.what₂.LL lam) (v' : VV K' lam),
      MvPolynomial.map emb' v'.1 = MvPolynomial.map D.what₂.embLL v.1 → HEq (c0' v') (μ • c0 v) := by
  subst c'
  have hcomp : emb'.comp ι = D.what₂.embLL := RingHom.ext hι
  have hinj : ∀ a b : VV K' lam, MvPolynomial.map emb' a.1 = MvPolynomial.map emb' b.1 → a = b := fun a b h =>
    Subtype.ext (MvPolynomial.map_injective emb' emb'.injective h)
  have hmap : ∀ v : VV D.what₂.LL lam, MvPolynomial.map emb' (mapVVι ι lam v).1 = MvPolynomial.map D.what₂.embLL v.1 := fun v => by
    show MvPolynomial.map emb' (MvPolynomial.map ι v.1) = _
    rw [MvPolynomial.map_map, hcomp]
  have hsm : ∀ (a : D.what₂.LL) (v : VV D.what₂.LL lam), mapVVι ι lam (a • v) = ι a • mapVVι ι lam v := fun a v =>
    Subtype.ext (by
      show MvPolynomial.map ι (a • v.1) = ι a • MvPolynomial.map ι v.1
      rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul])
  let c1 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W :=
    { toFun := fun v => c0' (mapVVι ι lam v)
      map_add' := fun a b => by
        rw [← map_add]
        congr 1
        exact Subtype.ext (map_add _ _ _)
      map_smul' := fun a v => by
        show c0' (mapVVι ι lam (a • v)) = D.what₂.embLL a • c0' (mapVVι ι lam v)
        rw [hsm, map_smulₛₗ, hι] }
  have hrho : ∀ γE v, mapVVι ι lam (rhoVr tau lam γE v) = rhoVr tau' lam γE (mapVVι ι lam v) := fun γE v => by
    refine hinj _ _ ?_
    rw [hmap]
    have e1 := congrArg Subtype.val (GlobalTheory.ConjTwist.mapVV_rhoVr D.what₂.embLL tau lam γE v)
    have e2 := congrArg Subtype.val (GlobalTheory.ConjTwist.mapVV_rhoVr emb' tau' lam γE (mapVVι ι lam v))
    rw [GlobalTheory.CoefModel.mapVV_coe] at e1 e2
    rw [e1, e2]
    have e3 : (fun τ => emb'.comp (tau' τ)) = fun τ => D.what₂.embLL.comp (tau τ) := funext htau
    have e4 : GlobalTheory.CoefModel.mapVV emb' lam (mapVVι ι lam v) = GlobalTheory.CoefModel.mapVV D.what₂.embLL lam v :=
      Subtype.ext (hmap v)
    rw [e3, e4]
  obtain ⟨μ, hμ⟩ := RowCoord.exists_smul_eq c hc h0 c1 fun γ γE hγ v => by
    show c0' (mapVVι ι lam (rhoVr tau lam γE v)) = c.coef.ρ γ (c0' (mapVVι ι lam v))
    rw [hrho]
    exact h1 γ γE hγ _
  refine ⟨μ, fun v v' hv => heq_of_eq ?_⟩
  have : v' = mapVVι ι lam v := hinj _ _ (hv.trans (hmap v).symm)
  subst this
  exact hμ v

end GlobalTheory.Mem.R3.Rw.OmExt
end

noncomputable section
namespace GlobalTheory.Mem.R3.Rw.OmExt

theorem coefA_eq {D : D7} {V : HSp D} (c c' : CoefA V) (hW : HEq c'.W c.W) (hρ : HEq c'.ρ c.ρ) (hn : HEq c'.nW c.nW)
    (hi : HEq c'.iW c.iW) : c' = c := by
  cases c
  cases c'
  dsimp only at hW hρ hn hi
  cases hW
  cases hn
  cases hi
  cases hρ
  rfl

set_option maxHeartbeats 4000000 in

theorem coef_schur : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
  (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → z.Std →
  ∀ {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
    (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks)
    (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
    Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') R'.toLevCh →
    BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr R'.toRealDat → RSideW z Wt' R' →
    ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    ∀ c0L, GlobalTheory.Mem.R3.Rw.OmExt.CoefFam z.R.toRealDat c0L →
    ∀ c0L'', GlobalTheory.Mem.R3.Rw.OmExt.CoefFam R'.toRealDat c0L'' →
    ∃ μ : ℂ, ∀ (v : Formalism.IndefR.FWT.VsV (w.st Z).toD7 i (w.st Z).toD7.what₂.LL) (v' : Formalism.IndefR.FWT.VsV (w'.st Z').toD7 i' (w'.st Z').toD7.what₂.LL),
      HEq (MvPolynomial.map (w'.st Z').toD7.what₂.embLL v'.1) (MvPolynomial.map (w.st Z).toD7.what₂.embLL v.1) → HEq (c0L'' i' v') (μ • c0L i v) := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hff hpx hstd Ks _ _ _ Xg tr R' cG' hP hL hB hRS i i' hii c0L hc c0L'' hc''
  obtain ⟨gR, c0R, ht⟩ := hc
  obtain ⟨gR', c0R', ht'⟩ := hc''
  obtain ⟨hW, hρ, hnW, hiW, -⟩ := hRS.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' hii
  have hcI := z.pins.char.base.models.cV i
  have hmapL := ht.mapL i
  have hmapL' := ht'.mapL i'
  have htau := ht.tauL_ok
  have htau' := ht'.tauL_ok
  obtain ⟨hpre, -, -, hR⟩ := hE
  cases B with | mk P => cases B' with | mk P' =>
  dsimp only at hpre
  subst hpre
  obtain rfl : i = i' := Fin.ext hii
  let ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL := (enlEmb hR)
  have hι : ∀ x, (w'.st Z').toD7.what₂.embLL (ι x) = (w.st Z).toD7.what₂.embLL x := (enlEmb_spec hR)
  let c'' : CoefA (Vc (w.st Z).toD7 i) :=
    { W := (R'.cV i).W, nW := (R'.cV i).nW, iW := (R'.cV i).iW, fW := (R'.cV i).fW, ρ := (R'.cV i).ρ }
  have hcc : c'' = z.R.cV i := coefA_eq _ _ hW hρ hnW hiW
  obtain ⟨μ, hμ⟩ := exists_smul_eq_enl (z.R.cV i) hcI ι (w'.st Z').toD7.what₂.embLL hι (labLL (w.st Z).toD7)
    (labLL (w'.st Z').toD7) (fun τ => (htau' τ).trans (htau τ).symm) (c0L i) hmapL c'' hcc (c0L'' i) hmapL'.1
  exact ⟨μ, fun v v' hv => hμ v v' (eq_of_heq hv)⟩

end GlobalTheory.Mem.R3.Rw.OmExt
end
