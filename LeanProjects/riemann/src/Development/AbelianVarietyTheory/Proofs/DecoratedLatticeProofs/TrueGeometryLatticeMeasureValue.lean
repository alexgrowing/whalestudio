import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepIndexLeS
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrXLeKOOfPrCat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelsRepsRepresentUnitaryDoubleCosets
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsContinuousLocalGLEmbeddingSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSupportedSubgroupOfSuppAtSplitPlaceMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGAtAllPlacesMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistLocalData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceProjectionEqOfPrimeComponentEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdAtKStdOfTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsPtOfOfRat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm

noncomputable section
namespace GlobalTheory.LevProd.Fwd

section Columns
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open GlobalTheory.Mem.ColAd GlobalTheory.Mem.Col2.PtExist
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem ratM_inj {E : Type} [Field E] [NumberField E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) {f g : Sp E n ≃ₗ[E] Sp E n}
    (h : ratM P f = ratM P g) : f = g := by
  refine LinearEquiv.ext fun x => funext fun i => (algebraMap E (P.adicCompletion E)).injective ?_
  have h1 := congrFun (ratM_mulVec (P := P) f x) i
  have h2 := congrFun (ratM_mulVec (P := P) g x) i
  rw [← h1, ← h2, h]

theorem exists_gl_mat {E : Type} [Field E] [NumberField E] {n : ℕ} (f : Sp E n ≃ₗ[E] Sp E n) : ∃ γ : GL (Fin n) E, γ.1 = mat f := by
  have h1 : mat (1 : Sp E n ≃ₗ[E] Sp E n) = 1 := by
    ext i j
    show (Pi.single j 1 : Sp E n) i = _
    rw [Matrix.one_apply, Pi.single_apply]
  exact ⟨⟨mat f, mat f⁻¹, by rw [← mat_mul, mul_inv_cancel, h1], by rw [← mat_mul, inv_mul_cancel, h1]⟩, rfl⟩

theorem mem_levQ {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) {u : B.Word} {a : I.ι} {i : ℕ} {Ch : Type}
    {chOf : (I.stp u a i).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)} {U : Ch → Subgroup (GA B (B.R.N i))} {chi : ∀ β, U β →* ℂˣ}
    {y : (I.stp u a i).Cl → GA B (B.R.N i)} {st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E}
    {k : Ch → GA B (B.R.N i)} (hR : I.Reads u a i chOf Lb U chi y st k) (c : (I.stp u a i).Cl) (x : GA B (B.R.N i))
    (hx : x ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N i)) (hxU : x ∈ U (chOf c))
    (hk1 : ∀ P : I.Q a, locM P.1 (k (chOf c)) = 1)
    (γ : I.Q a → (Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)))
    (hγ : ∀ P : I.Q a, locM P.1 x = ratM P.1 (γ P)) (P : I.Q a) :
    ∃ κ ∈ (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) i c.1 P).H, κ.1 = γ P := by
  haveI : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
  have hd : Disjoint (B.primes X).vGs (I.Q a) :=
    Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I a) (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).2.1
  have hp : PtOf (y c * k (chOf c)) ((I.stp u a i).rep c).1.1 :=
    IsPtOf.of_extTo (ColIn.Q_subset_SQ I a) hd (hR.pt c)
  obtain ⟨pk, hpk, -⟩ := hR.k_std (chOf c)
  have hk : k (chOf c) ∈ UAd B.sp.cm (B.R.N i) := hpk.uni
  have hg' : y c * x * k (chOf c) ∈ UAd B.sp.cm (B.R.N i) := by
    have e : y c * x * k (chOf c) = y c * k (chOf c) * ((k (chOf c))⁻¹ * x * k (chOf c)) := by group
    rw [e]
    exact mul_mem hp.uni (mul_mem (mul_mem (inv_mem hk) hx) hk)
  have hy : ∀ P : I.Q a, locM P.1 (y c * x * k (chOf c)) = ratM P.1 (((I.stp u a i).rep c).1.1.fr P * γ P) := by
    intro P
    have h1 : locM P.1 (y c * k (chOf c)) = ratM P.1 (((I.stp u a i).rep c).1.1.fr P) := Matrix.ext fun r s => hp.fr P r s
    rw [locM_mul, hk1, Matrix.mul_one] at h1
    rw [locM_mul, locM_mul, hk1, Matrix.mul_one, ratM_mul, h1, hγ]
  obtain ⟨q, hq⟩ := GlobalTheory.Mem.Col2.RatFrPt.exists_isPtOf_of_rat B.sp.cm ((B.primes X).vT u) (B.primes X).vGs (I.Q a) _ hg' fun P hP => by
    obtain ⟨δ, hδ⟩ := exists_gl_mat (((I.stp u a i).rep c).1.1.fr ⟨P, hP⟩ * γ ⟨P, hP⟩)
    refine ⟨δ, fun r s => ?_⟩
    rw [hδ]
    exact congrFun (congrFun (hy ⟨P, hP⟩) r) s
  obtain ⟨κ, hκ1, hκq, -⟩ := (hR.lev c x q hq).1 hxU
  have hκ : κ.1 = 1 := by
    have h1 : toGLm B.fields.E (B.R.N i) κ.1.1 = toGLm B.fields.E (B.R.N i) 1 := by
      rw [map_one]
      exact hκ1
    exact Subtype.ext ((toGLm B.fields.E (B.R.N i)).injective h1)
  have h2 : locM P.1 (y c * x * k (chOf c)) = ratM P.1 (q.fr P) := Matrix.ext fun r s => hq.fr P r s
  have h3 : q.fr P = κ.1.1 * ((I.stp u a i).rep c).1.1.fr P * ((κ.2.2.1 P)⁻¹).1 := by
    rw [← hκq]
    rfl
  rw [hy, h3, hκ] at h2
  have h4 := ratM_inj P.1 h2
  refine ⟨(κ.2.2.1 P)⁻¹, inv_mem (κ.2.2.2 P (Set.mem_univ _)), ?_⟩
  have h5 : ((1 : UF B.fields.E (B.R.N i)).1 : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) = 1 := rfl
  rw [h5, one_mul] at h4
  exact (mul_left_cancel h4).symm

end Columns

section Local
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

theorem prCat_iff (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀)
    (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k]
    [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν) (hok : cst.Ok) (hat : AtTwist (R := R) sel mu cst σ₀ P ι s W)
    (j c : ℕ) (h : j + (c + 1) = s + 1) (γ : AutY X R j) (g : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k)
    (hg : IsGL ι γ g) (e₀ : XIx (Fin R.k) (Fin R.t) j ≃ Fin (R.N j)) (he₀ : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e₀) :
    IsOpen (prX (Cgrp ((W.T s R).lev j (c + 1) h).J g) : Set (GL (XIx (Fin R.k) (Fin R.t) j) k)) ∧
    ∀ y, y ∈ prCat (Pr := Pr) cst.sharp j P.1 γ ↔ GlobalTheory.VolBridge.locHom ι e₀ y ∈ prX (Cgrp ((W.T s R).lev j (c + 1) h).J g) := by
  have hLev := GlobalTheory.TwBridge.Lev.levelAgree X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hok hat
  obtain ⟨e, he, hge⟩ := hg
  have hcc : cOf R j = c + 1 := by unfold cOf; have := hat.steps; omega
  have heR : ∀ i : Fin (c + 1), (e (Sum.inr i)).val = R.N j + i.val := fun i => he (Sum.inr i)
  have hgφ : g = GlobalTheory.VolBridge.locHom ι e γ := Units.ext hge
  have hreg : (W.T s R).Regular := Chain.ofTwist_regular _ _ _ _ _
  obtain ⟨hJo, -, -⟩ := hreg.2.2 j (c + 1) h
  set J := ((W.T s R).lev j (c + 1) h).J with hJdef
  set φ := GlobalTheory.VolBridge.locHom ι e with hφ
  have hcompl := hat.compl
  have hIsGL : ∀ x : AutY X R j, IsGL ι (γ⁻¹ * x * γ) (g⁻¹ * φ x * g) := by
    intro x
    refine ⟨e, he, ?_⟩
    rw [hgφ, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hC : ∀ x : AutY X R j, x ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) γ ↔ φ x ∈ Cgrp J g := by
    intro x
    rw [mem_Cgrp, ← GlobalTheory.RankOneMatrix.mem_rationalFirstParabolic_iff_localGL_mem_rootExchange ι e hcc heR x, (hLev j (c + 1) h _ _ (hIsGL x)).1]
    simp [Loc.Cbe, Subgroup.mem_comap, MulAut.conj_apply]
  have hN1 := GlobalTheory.UnipRead.mem_N1_iff_local_hom ι e hcc heR
  have hdN := GlobalTheory.VolBridge.exists_N1_local_hom_mem_open ι hcompl.dense e hcc heR
  have hee : e₀ = GlobalTheory.VolBridge.eX e hcc heR := Equiv.ext fun a => Fin.ext ((he₀ a).trans (he (Sum.inl a)).symm)
  have hOo : IsOpen {w : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k | g⁻¹ * w * g ∈ J} :=
    hJo.preimage (by fun_prop)
  have hOR : ∀ z ∈ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1,
      z ∈ Cgrp J g ↔ z ∈ {w | g⁻¹ * w * g ∈ J} := fun z hz => by
    simp [mem_Cgrp, hz]
  have hCR : Cgrp J g ≤ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 := fun z hz => (mem_Cgrp.1 hz).1
  refine ⟨GlobalTheory.OpenPr.isOpen_prX _ _ hOo (by simp [J.one_mem]) (fun z hz hzO => (hOR z hz).2 hzO), ?_⟩
  rw [hee]
  exact GlobalTheory.VolBridge.prX_iff_locHom ι e hcc heR hN1 hdN _ _ _ hOo hOR hCR hC

end Local

section Split
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.AdForm GlobalTheory.Mem.Col2
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem adAt_of_pr (q : GlobalTheory.FinPl.SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)) (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (z : AE D) (x : D.host.E) (h : q.pr z = q.pr (incA D x)) :
    adAt D.host.F PP (toEAf D z) = algebraMap D.host.E (PP.adicCompletion D.host.E) x := by
  have h1 : q.e * z = q.e * incA D x := by rw [← q.sec_pr, ← q.sec_pr, h]
  have h2 := congrArg (fun w => adAt D.host.F PP (toEAf D w)) h1
  simp only [map_mul, GlobalTheory.AdForm.CongAtIdem.adAt_toEAf_of_isIdemAt he, one_mul] at h2
  exact h2.trans (adAt_inclE D.host.F PP x)

theorem locM_of_pr (q : GlobalTheory.FinPl.SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)) (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V) (x : GL (Fin n) (Formalism.L2.DIV.AfE D.host.F D.host.E)) (hx : x.1 = finM V hn g)
    (y : Formalism.L2.Col.Sp D.host.E n ≃ₗ[D.host.E] Formalism.L2.Col.Sp D.host.E n)
    (hy : ∀ r s, q.pr (mt V g (Fin.cast hn.symm r) (Fin.cast hn.symm s)) = q.pr (incA D (y (Pi.single s 1) r))) :
    GlobalTheory.Mem.ColAd.locM PP x = GlobalTheory.Mem.ColAd.ratM PP y :=
  Matrix.ext fun r s => (congrArg (adAt D.host.F PP) (congrFun (congrFun hx r) s)).trans (adAt_of_pr q PP he _ _ (hy r s))

theorem locHom_std (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y)
    (e : Y ≃ Fin S.rank) (hF : F.β = (1 : Matrix (Fin S.rank) (Fin S.rank) k).submatrix id e) (g : GA D S) (r b : Y) :
    (GlobalTheory.LevIdx.locHom q S F g).val r b = q.pr (mt S g (e r) (e b)) := by
  have h := (GlobalTheory.LevIdx.eq_locHom_iff q S F g _).2 rfl
  have h2 := congrFun (congrFun h (e r)) (e b)
  rw [GlobalTheory.Fam.MovedJoin.mul_frameγ_std F e hF, GlobalTheory.Fam.MovedJoin.frameβ_mul_std F e hF] at h2
  exact h2.symm

theorem locHom_eq_one {k' : Type} [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
    {Y : Type} [Fintype Y] [DecidableEq Y] (q' : GlobalTheory.FinPl.SplitPt D k') (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (F : Frame k S.rank Y)
    (hv : q.v ≠ q'.v) {x : GA D S} (hx : x ∈ GlobalTheory.FinPl.grpAt S (· = q'.v)) : GlobalTheory.LevIdx.locHom q S F x = 1 := by
  have h1 : x ∈ GlobalTheory.FinPl.grpOff S (· = q.v) :=
    GlobalTheory.FinPl.SetCut.grpAt_le_grpOff S (· = q'.v) (· = q.v) (fun p hp e => hv (e.symm.trans hp)) hx
  have h2 := GlobalTheory.LocMod.PinInhab.map_mt_eq_one_of_off q (P := (· = q.v)) rfl h1
  symm
  rw [← GlobalTheory.LevIdx.eq_locHom_iff, h2]
  simp [F.βγ]

end Split

theorem list_prod_map_mulSingle {n : ℕ} {G : Fin n → Type*} [∀ i, Monoid (G i)] (x : ∀ i, G i) (k : Fin n) :
    ∀ l : List (Fin n), l.Nodup → ((l.map fun i => Pi.mulSingle i (x i) k).prod = if k ∈ l then x k else 1)
  | [], _ => by simp
  | b :: l, hl => by
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, list_prod_map_mulSingle x k l hl.2]
    by_cases hb : b = k
    · subst hb
      simp [hl.1]
    · rw [Pi.mulSingle_eq_of_ne (Ne.symm hb), one_mul]
      simp [List.mem_cons, Ne.symm hb]

theorem list_prod_mulSingle {n : ℕ} {G : Fin n → Type*} [∀ i, Monoid (G i)] (x : ∀ i, G i) :
    ((List.finRange n).map fun i => Pi.mulSingle i (x i)).prod = x := by
  funext k
  rw [Pi.list_prod_apply, List.map_map]
  have := list_prod_map_mulSingle x k (List.finRange n) (List.nodup_finRange n)
  simpa [Function.comp_def] using this

end GlobalTheory.LevProd.Fwd

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil

namespace GlobalTheory.LevProd.Fwd

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word} {a : GeoAll W u} {t : W.P.T}

set_option maxHeartbeats 1000000 in

theorem mem_prCat (hW : AllTrue W) (J : QJ a t) (hJ : J.Reads) (j : ℕ) (hj : j + 2 ≤ B.R.m) (β : J.Ch₀ j)
    (g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) (hg : g ∈ J.A.U j β)
    (y : Fin J.r → (Formalism.L2.Col.Sp B.fields.E (B.R.N j) ≃ₗ[B.fields.E] Formalism.L2.Col.Sp B.fields.E (B.R.N j)))
    (hy : ∀ i r s, (J.G i).q.pr (mt _ g (Fin.cast (rankN (I.rec7 l Z) j (show j ≤ B.R.m by omega)).symm r)
      (Fin.cast (rankN (I.rec7 l Z) j (show j ≤ B.R.m by omega)).symm s)) = (J.G i).q.pr (incA (I.rec7 l Z) (y i (Pi.single s 1) r))) (i : Fin J.r) :
    y i ∈ Formalism.L2.Col.prCat (Pr := B.primes X) (I.cst (W.P.I.tup t)).sharp j (J.P i).1
      ((I.idx (W.P.I.tup t)).h j ((J.A.b0 j β).get (show j < B.R.m by omega)) (J.P i)) := by
  have hjm : j ≤ B.R.m := by omega
  have hA := hJ.is
  have hI := hW.tr.ok
  have hL := hI.idx_ok (W.P.I.tup t)
  obtain ⟨hP⟩ := hW.tr.pins
  obtain ⟨c, rfl⟩ := hA.chOf_onto j hjm β
  obtain ⟨-, κ, hκ⟩ := (hA.U j hjm _ g).1 hg
  have hd : Disjoint (B.primes X).vGs (I.Q (W.P.I.tup t)) :=
    Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I _) (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).2.1
  have huni : κ.1 ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N j) := by
    have hgram := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 j hjm).1
    have huni : ∀ (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) j hjm) (B.T u)
        (I.rec7 l Z).R.f (J.A.bad j)) (x : TC.GA B (B.R.N j)), x ∈ S.U → x ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N j) := by
      intro S x hx
      have h := ((S.U_eq x).1 hx).1
      rw [hgram] at h
      exact h
    exact huni _ κ.1 κ.2
  have hloc : ∀ PP i, J.pl i = PP →
      GlobalTheory.Mem.ColAd.locM (F := (I.rec7 l Z).host.F) (E := (I.rec7 l Z).host.E) PP κ.1 = GlobalTheory.Mem.ColAd.ratM PP (y i) := by
    rintro _ i rfl
    exact locM_of_pr (J.G i).q (J.pl i) (J.G i).idem _ _ g κ.1 hκ (y i) (hy i)
  have hsurj : ∀ P : I.Q (W.P.I.tup t), ∃ i, J.pl i = P.1 := fun P => hJ.surj P.1 ((hW.tq.Q t P.1).2 P.2)
  choose ι hι using hsurj
  have hmem : J.pl i ∈ I.Q (W.P.I.tup t) := (hW.tq.Q t _).1 (J.mem i)
  obtain ⟨κ', hκ', e'⟩ := mem_levQ I hI (hA.reads j hjm) c κ.1 huni κ.2 (fun P => by
      rw [hJ.std j (by omega)]
      refine Matrix.ext fun r s => ?_
      refine (GlobalTheory.Fam.MovedJoin.adAt_kStd_of_twist hI _ ⟨P.1, Finset.mem_union_right _ P.2⟩
        (Finset.disjoint_right.1 hd P.2) u _ r s).trans ?_
      rw [Matrix.one_apply]
      split_ifs <;> simp)
    (fun P => y (ι P)) (fun P => hloc _ _ (hι P)) ⟨J.pl i, hmem⟩
  have hii : ι ⟨J.pl i, hmem⟩ = i := hJ.inj (hι ⟨J.pl i, hmem⟩)
  rw [hii] at e'
  have hb : levQAt I.sel (I.tup (W.P.I.tup t)) (I.idx (W.P.I.tup t)) (I.Tp (W.P.I.tup t)) j c.1 =
      (I.idx (W.P.I.tup t)).levQ j ((J.A.b0 j (J.A.chOf j c)).get (show j < B.R.m by omega)) := by
    rw [← (hA.rep j hjm c).1]
    unfold levQAt Idx.get
    conv_lhs => rw [← Option.some_get (c.1.2.2 (show j < B.R.m by omega))]
    rfl
  rw [hb, hL.grpQ, Subgroup.mem_subgroupOf, e'] at hκ'
  have hPi : J.P i = ⟨J.pl i, Finset.mem_union_right _ hmem⟩ := Subtype.ext (hJ.eq i)
  rw [hPi]
  exact hκ'

end GlobalTheory.LevProd.Fwd

namespace GlobalTheory.LevProd
open GlobalTheory.LevProd.Fwd

set_option maxHeartbeats 1000000 in

theorem phi_mem_H : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : QJ a t), J.Reads → ∀ (α : J.Ch j), ∀ g ∈ J.A.U j (J.ι j α), ∀ i, GlobalTheory.LevProd.phi J j hj g i ∈ GlobalTheory.LevProd.H J j hj α i := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat j hj t J hJ α g hg
  have hjm : j ≤ B.R.m := by omega
  have hL := hW.tr.ok.idx_ok (W.P.I.tup t)
  obtain ⟨hP⟩ := hW.tr.pins
  have hrk := rankN (I.rec7 l Z) j hjm
  have hstd := fun i : Fin J.r => (ha.stdQ (J.pl i) ⟨t, J.mem i⟩).1 j (by have := step_index_le_s J i hj; exact this.trans (Nat.le_succ _))
  choose e he hF using hstd
  let e₀ : Fin J.r → (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j ≃ Fin ((I.rec7 l Z).R.N j)) := fun i => (e i).trans (finCongr hrk)
  have key := fun i : Fin J.r => prCat_iff _ _ _ I.Ch I.sel _ (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) B.embLL (J.P i) _ _ _ _
      (J.G i).ν (J.G i).unitVol hL.cst_ok (hJ.tw i) j ((J.G i).s - j) (by have := step_index_le_s J i hj; omega) _ _
      (hJ.rep i j ((J.G i).s - j) (Nat.add_sub_cancel' (step_index_le_s J i hj)) (by omega) (J.ι j α)) (e₀ i) (fun r => he i r)
  have hHo : ∀ i, IsOpen (H J j hj α i : Set (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k)) := fun i => by
    have h := (key i).1
    rw [hJ.sec j hjm α i] at h
    exact h
  have hHr : ∀ i y, y ∈ Formalism.L2.Col.prCat (Pr := B.primes X) (I.cst (W.P.I.tup t)).sharp j (J.P i).1
      ((I.idx (W.P.I.tup t)).h j ((J.A.b0 j (J.ι j α)).get (show j < B.R.m by omega)) (J.P i)) →
      GlobalTheory.VolBridge.locHom ((J.G i).q.pr.comp (incA (I.rec7 l Z))) (e₀ i) y ∈ H J j hj α i := fun i y hy => by
    have h := ((key i).2 y).1 hy
    rw [hJ.sec j hjm α i] at h
    exact h
  have hUo := (GlobalTheory.ChartReps.twDat_reps I hW.tr.ok hP l Z u _ _ J.A hJ.is j hjm (J.ι j α)).1.opn
  have hgl := fun i : Fin J.r => GlobalTheory.LocEmb.exists_gl _ _ (J.G i).q ((I.rec7 l Z).sp.X j)
    (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) ((J.G i).FX j (by have := step_index_le_s J i hj; omega))
  choose gl hglc hglp _ using hgl
  have hAt : ∀ i x, gl i x ∈ GlobalTheory.FinPl.grpAt _ (· = (J.G i).q.v) := fun i x =>
    GlobalTheory.SuppGrp.mem_grpAt_of_suppAt _ _ _ _ _ (hglp i x).1 _ rfl
  have hVo : ∀ i, IsOpen {x | gl i x ∈ J.A.U j (J.ι j α)} := fun i =>
    hUo.preimage (f := fun x => (⟨gl i x, GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ (hAt i x)⟩ : GfC _)) ((hglc i).subtype_mk _)
  have hy : ∀ i, ∃ y, GlobalTheory.VolBridge.locHom ((J.G i).q.pr.comp (incA (I.rec7 l Z))) (e₀ i) y ∈
      (fun v => (phi J j hj g i)⁻¹ * v) ⁻¹' ((H J j hj α i : Set _) ∩ {x | gl i x ∈ J.A.U j (J.ι j α)}) := fun i =>
    GlobalTheory.denseGL_completion _ (J.G i).compl.dense (e₀ i) (phi J j hj g i) _
      (((hHo i).inter (hVo i)).preimage (continuous_const.mul continuous_id))
      (by
        rw [Set.mem_preimage, inv_mul_cancel]
        exact ⟨one_mem _, by rw [Set.mem_setOf_eq, map_one]; exact one_mem _⟩)
  choose y hy using hy
  set x : (i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k := fun i =>
    (phi J j hj g i)⁻¹ * GlobalTheory.VolBridge.locHom ((J.G i).q.pr.comp (incA (I.rec7 l Z))) (e₀ i) (y i) with hx
  have hphi : ∀ i, phi J j hj (gl i (x i)) = Pi.mulSingle i (x i) := by
    intro i
    funext i'
    show GlobalTheory.LevIdx.locHom (J.G i').q _ ((J.G i').FX j _) (gl i (x i)) = _
    by_cases h : i' = i
    · subst h
      rw [Pi.mulSingle_eq_same]
      exact ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).1 ((hglp i' (x i')).2)).symm
    · rw [Pi.mulSingle_eq_of_ne h]
      exact locHom_eq_one (J.G i).q (J.G i').q _ _
        (fun hv => h ((GlobalTheory.Fam.QJPlaces.places_under W hW u a ha hat t J hJ).1 hv)) (hAt i _)
  have hg' : g * ((List.finRange J.r).map fun i => gl i (x i)).prod ∈ J.A.U j (J.ι j α) := by
    refine mul_mem hg (Subgroup.list_prod_mem _ fun z hz => ?_)
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hz
    exact (hy i).2
  have hφ' : ∀ i, phi J j hj (g * ((List.finRange J.r).map fun i => gl i (x i)).prod) i =
      GlobalTheory.VolBridge.locHom ((J.G i).q.pr.comp (incA (I.rec7 l Z))) (e₀ i) (y i) := by
    intro i
    rw [map_mul, map_list_prod, List.map_map]
    simp only [Function.comp_def, hphi]
    rw [list_prod_mulSingle x, Pi.mul_apply]
    exact mul_inv_cancel_left _ _
  intro i
  have h1 := hHr i _ (mem_prCat hW J hJ j hj _ _ hg' y (fun i r s => by
    obtain ⟨r, rfl⟩ := (e₀ i).surjective r
    obtain ⟨s, rfl⟩ := (e₀ i).surjective s
    exact (locHom_std (J.G i).q _ _ (e i) (hF i) _ r s).symm.trans (congrArg (fun z => z.val r s) (hφ' i))) i)
  have h2 : x i ∈ H J j hj α i := (hy i).1
  have h3 := mul_mem h1 (inv_mem h2)
  rw [hx] at h3
  simpa using h3

end GlobalTheory.LevProd
end
