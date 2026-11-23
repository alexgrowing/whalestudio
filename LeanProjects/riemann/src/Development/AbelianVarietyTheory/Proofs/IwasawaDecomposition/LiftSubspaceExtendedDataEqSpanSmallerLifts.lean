import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankSpanImage
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RangeAdjointRat
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.SubExt

private theorem core {X X' Y Y' : Type} {aX : AddCommGroup X} {mX : Module ℂ X} {aX' : AddCommGroup X'} {mX' : Module ℂ X'}
    {aY : AddCommGroup Y} {mY : Module ℂ Y} {aY' : AddCommGroup Y'} {mY' : Module ℂ Y'}
    (hX : X' = X ∧ HEq aX' aX ∧ HEq mX' mX) (hY : Y' = Y ∧ HEq aY' aY ∧ HEq mY' mY)
    (M : HMod X) (M' : HMod X') (N : HMod Y) (N' : HMod Y') (hM : HEq M' M) (hN : HEq N' N)
    (θ : M.H →ₗ[ℂ] N.H) (θ' : M'.H →ₗ[ℂ] N'.H) (hθ : HEq θ' θ)
    {K K' V V' : Type} [Field K] [Field K'] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K' V']
    {σ : K →+* ℂ} {σ' : K' →+* ℂ} (j : V →ₛₗ[σ] M.H) (j' : V' →ₛₗ[σ'] M'.H) (L : V → V')
    (hinj : Function.Injective M.e) (hL : ∀ v, HEq (M'.e (j' (L v))) (M.e (j v)))
    {ι : Type} [Fintype ι] (b : Module.Basis ι K' V') (hb : LinearIndependent ℂ fun i => j' (b i))
    (hU : LinearMap.range (LinearMap.adjoint θ) ≤
      Submodule.span ℂ (j '' ((LinearMap.range (LinearMap.adjoint θ)).comap j))) :
    (LinearMap.range (LinearMap.adjoint θ')).comap j' =
      Submodule.span K' (L '' ((LinearMap.range (LinearMap.adjoint θ)).comap j)) := by
  obtain ⟨rfl, h1, h2⟩ := hX
  obtain ⟨rfl, h3, h4⟩ := hY
  cases h1; cases h2; cases h3; cases h4
  cases hM; cases hN; cases hθ
  exact GlobalTheory.RatSpan.comap_eq_span j j' L (fun v => hinj (eq_of_heq (hL v))) b hb _ hU

section Twist

variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [NormedAddCommGroup F]
  [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] {K V : Type} [Field K] [AddCommGroup V] [Module K V] {σ σ' : K →+* ℂ}

private theorem tw_range (s : Bool) (θ : E →ₗ[ℂ] F) {c : ℂ} (hc : c = 1) :
    LinearMap.range (LinearMap.adjoint (c • Tw.map s θ)) = Tw.sub s (LinearMap.range (LinearMap.adjoint θ)) := by
  rw [hc, one_smul, Tw.adjoint_map]
  ext x
  exact Iff.rfl

private theorem tw_comap (s : Bool) (θ : E →ₗ[ℂ] F) {c : ℂ} (hc : c = 1) (h : ∀ a, σ' a = cj s (σ a)) (j : V →ₛₗ[σ] E) :
    (LinearMap.range (LinearMap.adjoint (c • Tw.map s θ))).comap (Tw.semi s h j) =
      (LinearMap.range (LinearMap.adjoint θ)).comap j := by
  rw [tw_range s θ hc]
  ext x
  exact Iff.rfl

private theorem tw_rat (s : Bool) (θ : E →ₗ[ℂ] F) {c : ℂ} (hc : c = 1) (h : ∀ a, σ' a = cj s (σ a)) (j : V →ₛₗ[σ] E)
    (H : Submodule.span ℂ (Tw.semi s h j '' ((LinearMap.range (LinearMap.adjoint (c • Tw.map s θ))).comap (Tw.semi s h j) : Set V)) =
      LinearMap.range (LinearMap.adjoint (c • Tw.map s θ))) :
    LinearMap.range (LinearMap.adjoint θ) ≤ Submodule.span ℂ (j '' ((LinearMap.range (LinearMap.adjoint θ)).comap j)) := by
  rw [tw_comap s θ hc, tw_range s θ hc] at H
  intro x hx
  have h1 : Submodule.span ℂ (Tw.semi s h j '' ((LinearMap.range (LinearMap.adjoint θ)).comap j : Set V)) ≤
      Tw.sub s (Submodule.span ℂ (j '' ((LinearMap.range (LinearMap.adjoint θ)).comap j : Set V))) := by
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    have h2 : j y ∈ Submodule.span ℂ (j '' ((LinearMap.range (LinearMap.adjoint θ)).comap j : Set V)) :=
      Submodule.subset_span ⟨y, hy, rfl⟩
    exact h2
  exact h1 (H.ge (show Tw.mk s x ∈ Tw.sub s _ from hx))

omit [FiniteDimensional ℂ E] in
private theorem tw_li (s : Bool) {ι : Type} {v : ι → E}
    (h : LinearIndependent ℂ fun i => Tw.mk s (v i)) : LinearIndependent ℂ v := by
  rw [linearIndependent_iff'] at h ⊢
  intro u g hg i hi
  have h1 : ∑ i ∈ u, cj s (g i) • Tw.mk s (v i) = 0 := by
    simp only [← Tw.mk_smul]
    exact hg
  have := congrArg (cj s) (h u (fun i => cj s (g i)) h1 i hi)
  rwa [cj_cj, map_zero] at this

end Twist

private theorem cx_rat {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
    (cv : CrdV A) (hK : X.KFormL) (hJ : X.JIsoL cv) (hT : Formalism.IndefR.Rat.LiftTest X) (j : Bs.J) (t : Bs.Tup) :
    Submodule.span ℂ (X.jL j t '' ((LinearMap.range (LinearMap.adjoint (X.θ' j t))).comap (X.jL j t) : Set (A.FL j t))) =
      LinearMap.range (LinearMap.adjoint (X.θ' j t)) := by
  obtain ⟨N, ψ, hψ, hr⟩ := hT j
  exact Formalism.IndefR.Rat.range_adjoint_rat Bs.v0.embedding (X.jL j t) (cv.hL j t) _ (hK j t).1 (hK j t).2 (hJ j t)
    (X.θ' j t) ψ hψ (fun i x => hr t i x)

section One

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3)

set_option maxHeartbeats 1000000 in
private theorem zl_eq (hp : ∀ i, R.phs i = 1) (i : Fin D.R.m) (t : T) :
    (zsOf R F).Zl i t = (LinearMap.range (LinearMap.adjoint (R.thG i t))).comap (R.jV i t) := (by with_unfolding_all exact (tw_comap (twAt D.what₂.embLL A3.A.v0) (R.thG i t) (hp i) R.toRealDat.emb0 (R.jV i t) :))

set_option maxHeartbeats 1000000 in
private theorem rat (hp : ∀ i, R.phs i = 1) (hM : R.toRealDat.IsModels) (hT : Formalism.IndefR.Rat.LiftTest (R.toCx3 F))
    (i : Fin D.R.m) (t : T) :
    LinearMap.range (LinearMap.adjoint (R.thG i t)) ≤
      Submodule.span ℂ (R.jV i t '' ((LinearMap.range (LinearMap.adjoint (R.thG i t))).comap (R.jV i t))) := by
  have h := cx_rat (R.toCx3 F) F.cv (RealDat3.kFormL_of (F := F) hM) (RealDat3.jIsoL_of (F := F) hM) hT i t
  exact (by with_unfolding_all exact (tw_rat (twAt D.what₂.embLL A3.A.v0) (R.thG i t) (hp i) R.toRealDat.emb0 (R.jV i t) ((h)) : _))

include F in
set_option maxHeartbeats 1000000 in
private theorem li (hM : R.toRealDat.IsModels) (i : Fin D.R.m) (t : T) :
    LinearIndependent ℂ fun k => R.jV i t (Module.Basis.ofVectorSpace D.what₂.LL (A3.A.fam.amb.FL i t) k) :=
  tw_li (twAt D.what₂.embLL A3.A.v0) ((by with_unfolding_all exact ((RealDat3.kFormL_of (F := F) hM i t).1 :)))

end One

set_option maxHeartbeats 2000000 in
private theorem gen {D D' : D7} {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 I0 T Pl0' I0' T' : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {A3' : FamIn3 D'.what₂.LL G' Pl0' I0' (List ℕ) T' D'.R.m}
    {Ks Ks' : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] [Field Ks'] [NumberField Ks'] [Algebra Ks' D'.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3) (R' : RealDat3 D' A3' Ks') (F' : Face3 D' A3')
    (hp : ∀ i, R.phs i = 1) (hp' : ∀ i, R'.phs i = 1) (hM : R.toRealDat.IsModels) (hM' : R'.toRealDat.IsModels)
    (hT : Formalism.IndefR.Rat.LiftTest (R.toCx3 F)) (i : Fin D.R.m) (t : T) (i' : Fin D'.R.m) (t' : T')
    (hX : (Bridge.Gf (Vc D' i') → (R'.cV i').W) = (Bridge.Gf (Vc D i) → (R.cV i).W) ∧
      HEq (inferInstance : AddCommGroup (Bridge.Gf (Vc D' i') → (R'.cV i').W))
        (inferInstance : AddCommGroup (Bridge.Gf (Vc D i) → (R.cV i).W)) ∧
      HEq (inferInstance : Module ℂ (Bridge.Gf (Vc D' i') → (R'.cV i').W))
        (inferInstance : Module ℂ (Bridge.Gf (Vc D i) → (R.cV i).W)))
    (hY : Mult.MMap (R'.MW i' D'.what₂.embLL) = Mult.MMap (R.MW i D.what₂.embLL) ∧
      HEq (inferInstance : AddCommGroup (Mult.MMap (R'.MW i' D'.what₂.embLL)))
        (inferInstance : AddCommGroup (Mult.MMap (R.MW i D.what₂.embLL))) ∧
      HEq (inferInstance : Module ℂ (Mult.MMap (R'.MW i' D'.what₂.embLL)))
        (inferInstance : Module ℂ (Mult.MMap (R.MW i D.what₂.embLL))))
    (hW : HEq (R'.HW i' D'.what₂.embLL) (R.HW i D.what₂.embLL)) (hV : HEq (R'.HV i' t') (R.HV i t))
    (hθ : HEq (R'.thG i' t') (R.thG i t))
    (L : (A3.fam3.F.L i t).S.Forms → (A3'.fam3.F.L i' t').S.Forms)
    (hL : ∀ x, HEq (R'.B.jL i' t' (L x)) (R.B.jL i t x)) :
    (zsOf R' F').Zl i' t' = Submodule.span D'.what₂.LL (L '' ((zsOf R F).Zl i t : Set (A3.fam3.F.L i t).S.Forms)) := by
  have e : D.what₂.embLL = sg0 D A3.A := (sgAt_mk _ R.hv0).symm
  have e' : D'.what₂.embLL = sg0 D' A3'.A := (sgAt_mk _ R'.hv0).symm
  have key : ∀ σ σ', D.what₂.embLL = σ → D'.what₂.embLL = σ' → (Mult.MMap (R'.MW i' σ') = Mult.MMap (R.MW i σ) ∧
      HEq (inferInstance : AddCommGroup (Mult.MMap (R'.MW i' σ')))
        (inferInstance : AddCommGroup (Mult.MMap (R.MW i σ))) ∧
      HEq (inferInstance : Module ℂ (Mult.MMap (R'.MW i' σ')))
        (inferInstance : Module ℂ (Mult.MMap (R.MW i σ)))) ∧ HEq (R'.HW i' σ') (R.HW i σ) := by
    rintro _ _ rfl rfl
    exact ⟨hY, hW⟩
  obtain ⟨k1, k2⟩ := key _ _ e e'
  have hli := li R' F' hM' i' t'
  haveI := hli.finite
  letI := Fintype.ofFinite (Module.Basis.ofVectorSpaceIndex D'.what₂.LL (A3'.A.fam.amb.FL i' t'))
  rw [zl_eq R F hp, zl_eq R' F' hp']
  exact core hX k1 (R.HV i t) (R'.HV i' t') _ _ hV k2 (R.thG i t) (R'.thG i' t') hθ (R.jV i t) (R'.jV i' t') L (hM.HV i t).1
    (fun v => (heq_of_eq (hM'.jV i' t' (L v))).trans ((hL v).trans (heq_of_eq (hM.jV i t v)).symm)) _ hli (rat R F hp hM hT i t)

section Two

variable {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt}

set_option maxHeartbeats 4000000 in
private theorem mmap_eq (q : B'.toPre = B.toPre) (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i')
    {S : (w.st Z).toD7.what₂.Tau → SPar} {S' : (w'.st Z').toD7.what₂.Tau → SPar}
    (M : Mult.DSModel (Wc (w.st Z).toD7 i) S) (M' : Mult.DSModel (Wc (w'.st Z').toD7 i') S')
    (a : HEq M'.H M.H) (b : HEq M'.nacg M.nacg) (c : HEq M'.ips M.ips) (d : HEq M'.σ M.σ) (l : HEq M'.lam M.lam) (e : HEq M'.ε M.ε)
    (g : HEq M'.fr M.fr) :
    Mult.MMap M' = Mult.MMap M ∧
      HEq (inferInstance : AddCommGroup (Mult.MMap M')) (inferInstance : AddCommGroup (Mult.MMap M)) ∧
      HEq (inferInstance : Module ℂ (Mult.MMap M')) (inferInstance : Module ℂ (Mult.MMap M)) := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  cases M
  cases M'
  dsimp only at a b c d l e g
  cases a; cases b; cases c; cases d; cases l; cases e; cases g
  exact ⟨rfl, HEq.rfl, HEq.rfl⟩

set_option maxHeartbeats 4000000 in
private theorem gf_eq (q : B'.toPre = B.toPre) (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i')
    (c : CoefA (Vc (w.st Z).toD7 i)) (c' : CoefA (Vc (w'.st Z').toD7 i'))
    (a : HEq c'.W c.W) (b : HEq c'.nW c.nW) (d : HEq c'.iW c.iW) :
    (Bridge.Gf (Vc (w'.st Z').toD7 i') → c'.W) = (Bridge.Gf (Vc (w.st Z).toD7 i) → c.W) ∧
      HEq (inferInstance : AddCommGroup (Bridge.Gf (Vc (w'.st Z').toD7 i') → c'.W))
        (inferInstance : AddCommGroup (Bridge.Gf (Vc (w.st Z).toD7 i) → c.W)) ∧
      HEq (inferInstance : Module ℂ (Bridge.Gf (Vc (w'.st Z').toD7 i') → c'.W))
        (inferInstance : Module ℂ (Bridge.Gf (Vc (w.st Z).toD7 i) → c.W)) := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  cases c
  cases c'
  dsimp only at a b d
  cases a; cases b; cases d
  exact ⟨rfl, HEq.rfl, HEq.rfl⟩

set_option maxHeartbeats 4000000 in
private theorem jL_of {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
    {z : Dat (w.st Z) w.I hX T Wt} {z' : Dat (w'.st Z') w'.I hX' T' Wt'} (e : ExtN z z')
    (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i')
    (ok : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).Ok) (ok' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 ((i' : ℕ) + 1)).Ok)
    (x : ((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).toCSD ok).Forms) (x' : ((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 ((i' : ℕ) + 1)).toCSD ok').Forms)
    (h : ∀ d d', HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) ((((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 ((i' : ℕ) + 1)).res ok').symm x').1 d').1)
        (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) ((((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).res ok).symm x).1 d).1)) :
    HEq (z'.R.B.jL i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) ((by with_unfolding_all exact (x' :)))) (z.R.B.jL i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) ((by with_unfolding_all exact (x :)))) := by
  obtain ⟨y, rfl⟩ := ((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).res ok).surjective x
  obtain ⟨y', rfl⟩ := ((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 ((i' : ℕ) + 1)).res ok').surjective x'
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply] at h
  exact (by with_unfolding_all exact (e.jL i i' hi ok ok' y y' h :))

end Two

end GlobalTheory.Mem.R3.SubExt

set_option maxHeartbeats 4000000 in
theorem _root_.GlobalTheory.T.liftSubspace_extendedData_eq_span_smallerLifts : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (L : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms →+ ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Forms), (∀ (a : (w.st Z).toD7.what₂.LL) (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms), L (a • f) = φ a • L f) → (∀ (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms) (d : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D) (d' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D), HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))).symm (L f) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).V) d').1) (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))).symm f : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).V) d).1)) → ((zsOf z'.R z'.F).Zl j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0) = Submodule.span (w'.st Z').toD7.what₂.LL (L '' (((zsOf z.R z.F).Zl j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) : Set ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms))) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE hf _ hpx Z hX Wt z _ _ _ hH Z' hX' _ _ _ z' _ hx j j' hj φ hφ L _ hC => ?_
  have m := hx.MW j j' hj
  have r := hx.ref j j' hj
  have hY := GlobalTheory.Mem.R3.SubExt.mmap_eq hE.1 j j' hj _ _ m.1 m.2.1 m.2.2.1 m.2.2.2.1 m.2.2.2.2.1 m.2.2.2.2.2.1 m.2.2.2.2.2.2.1
  have hXX := GlobalTheory.Mem.R3.SubExt.gf_eq hE.1 j j' hj _ _ (hx.BV j j' hj).1 (hx.cV j j' hj).1 (hx.cV j j' hj).2
  have hL := fun x => GlobalTheory.Mem.R3.SubExt.jL_of hx j j' hj _ _ x (L x) (hC x)
  exact (by with_unfolding_all exact (GlobalTheory.Mem.R3.SubExt.gen z.R z.F z'.R z'.F z.pins.phs z'.pins.phs z.pins.char.base.models z'.pins.char.base.models
    hH.liftTest j _ j' _ hXX hY m.2.2.2.2.2.2.2.2.1 r.2.1 r.2.2.2.1 (((fun x => L x))) ((hL)) : _))
