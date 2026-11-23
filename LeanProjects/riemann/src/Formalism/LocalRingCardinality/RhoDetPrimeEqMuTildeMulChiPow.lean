import Mathlib
import Formalism.LocalRingCardinality.Params
import Formalism.LocalRingCardinality.DataHost
import Formalism.LocalRingCardinality.DataSpaces
import Formalism.LocalRingCardinality.DataCoeff
import Formalism.LocalRingCardinality.DataArith
import Formalism.LocalRingCardinality.DataKernels
import Formalism.LocalRingCardinality.DataRows
import Formalism.SharpRestriction.CuspSpanNormBounds.DataS
import Formalism.SharpRestriction.GrowthBounds.DataG
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.LocalRingCardinality.DataForms
import Formalism.LocalRingCardinality.DataJet
import Formalism.LocalRingCardinality.DataCD

noncomputable section

namespace Formalism.BasicNotions

open NumberField IsDedekindDomain

namespace Loc

variable {l : ℕ} [Fact l.Prime]

def GoodCoef (N : ℕ) (LL : FinExt l) : Prop := ∀ x : Om l, x ^ Nat.lcm l N = 1 → x ∈ LL.1

theorem GoodCoef.mono {N : ℕ} {LL LL' : FinExt l} (h : GoodCoef N LL) (hle : LL.1 ≤ LL'.1) : GoodCoef N LL' :=
  fun x hx => hle (h x hx)

theorem GoodCoef.good {N : ℕ} {K LL : FinExt l} {s : ℕ} (h : GoodCoef N LL)
    (hK : ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), τ x ∈ LL.1) (hs : l ^ s ∣ Nat.lcm l N) (h1 : 1 ≤ s)
    (h2 : l = 2 → 2 ≤ s) (hle : K.1 ≤ Ks K s) : Good K s LL := by
  refine ⟨h1, h2, hle, fun τ x => ?_⟩
  have e2 : ∀ y : ↥(Ks K s), τ.liftNormal (Om l) (y : Om l) = τ y := fun y => AlgHom.liftNormal_commutes τ (Om l) y
  have key : Ks K s ≤ LL.1.comap (τ.liftNormal (Om l)) := by
    refine sup_le (fun y hy => ?_) (IntermediateField.adjoin_le_iff.2 fun y hy => ?_)
    · exact hK ((τ.liftNormal (Om l)).comp K.1.val) ⟨y, hy.1⟩
    · refine h _ ?_
      obtain ⟨c, hc⟩ := hs
      have hy' : y ^ (l ^ s) = 1 := hy
      rw [← map_pow, hc, pow_mul, hy', one_pow, map_one]
  rw [← e2]
  exact key x.2

theorem GoodCoef.good_one {N : ℕ} {K LL : FinExt l} (h : GoodCoef N LL)
    (hK : ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), τ x ∈ LL.1) (h2 : l ≠ 2) (hle : K.1 ≤ Ks K 1) : Good K 1 LL :=
  h.good hK (by rw [pow_one]; exact Nat.dvd_lcm_left _ _) le_rfl (fun e => absurd e h2) hle

end Loc

def stdH (E : Type) [Field E] [StarRing E] (N : ℕ) (x y : Fin N → E) : E := ∑ i, star (x i) * y i

def IsSDLat (E : Type) [Field E] [NumberField E] [StarRing E] (N : ℕ)
    (L : Submodule (𝓞 E) (Fin N → E)) : Prop :=
  L.FG ∧ Submodule.span E (L : Set (Fin N → E)) = ⊤ ∧
    ∀ y, y ∈ L ↔ ∀ x ∈ L, stdH E N x y ∈ (algebraMap (𝓞 E) E).range

def SDLat (E : Type) [Field E] [NumberField E] [StarRing E] (N : ℕ) : Type :=
  {L : Submodule (𝓞 E) (Fin N → E) // IsSDLat E N L}

def SDLat.smulLat {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
    (γ : Matrix (Fin N) (Fin N) E) (L : Submodule (𝓞 E) (Fin N → E)) : Submodule (𝓞 E) (Fin N → E) :=
  L.map ((Matrix.toLin' γ).restrictScalars (𝓞 E))

def GIdx {R : Ranks} (H : Host R) (T p : ℕ) : Prop :=
  p.Prime ∧ 5 ≤ p ∧ H.cls p = .inertClass ∧ HNeZero H p ∧ p ∉ H.levelPrimes ∧ ¬ p ∣ T

structure Member (R : Ranks) (ι : Type) [Fintype ι] (hc : ι → HCParam R) where
  C : ColumnChain R ι hc
  A : ColumnsAtT R C
  P : PeriodMap R C

structure D7 where

  R : Ranks

  host : Host R

  sp : @Spaces R host.F host.E _ _ _ _ host.cmStar _

  vol : @HSpace host.E _ _ host.cmStar → ℝ
  vol_pos : ∀ W, 0 < vol W

  what₂ : Rows.Data R

  eTau : what₂.Tau ≃ (R.Psi)

  hc : what₂.Tau → HCParam R

  [wordFin : Fintype what₂.Word]
  u₀ : what₂.Word

  hcW : what₂.Word → what₂.Tau → HCParam R
  hcW_base : hcW u₀ = hc
  hcW_v : ∀ u τ, (hcW u τ).v = (hc τ).v
  hcW_b : ∀ u τ, (hcW u τ).b = (hc τ).b
  hcW_e : ∀ u τ, (hcW u τ).e = (hc τ).e
  hcW_first : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨0, h⟩ = (hc τ).u ⟨0, h⟩
  hcW_last : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨R.k - 1, by omega⟩ = (hc τ).u ⟨R.k - 1, by omega⟩

  mem : ∀ u : what₂.Word, Member R what₂.Tau (hcW u)

  [nfLL : NumberField what₂.LL]
  [starLL : StarRing what₂.LL]
  [tcLL : NumberField.IsTotallyComplex what₂.LL]

  [galLL : IsGalois ℚ what₂.LL]

  starLL_cx : ∀ x : what₂.LL, what₂.embLL (star x) = starRingEnd ℂ (what₂.embLL x)

  div : DivData what₂.LL what₂.Word

  div_good : (∀ v, IsUnit (div.RR.X v).det) ∧ ∀ u v, IsUnit ((div.Nu u).X v).det

  embE : host.E →+* what₂.LL

  embE_φ₀ : what₂.embLL.comp embE = host.φ₀

  conjF : host.E →ₐ[host.F] host.E
  conjF_eq : ∀ x, conjF x = host.conj x

  embE_conj : ∀ x : host.E, embE (host.conj x) = star (embE x)

  LL0 : IntermediateField ℚ what₂.LL
  hostField_le_fixedField : ∀ x : host.E, embE x ∈ LL0

  O_int : ∀ y : what₂.O, IsIntegral ℤ (what₂.OtoLL y)

  O_contains : ∀ x : 𝓞 host.E, ∃ y : what₂.O, what₂.OtoLL y = embE (x : host.E)

  plEq : what₂.places.Pl ≃ HeightOneSpectrum (𝓞 what₂.LL)

  val_eq : ∀ w (x : what₂.LL), x ≠ 0 → what₂.places.val w x = ((vAdd (plEq w) x : ℤ) : WithTop ℤ)

  ram_eq : ∀ w, what₂.places.ramIdx w = eWL what₂.LL (plEq w)

  conj_val : ∀ w (x : what₂.LL), what₂.places.val (what₂.places.conj w) x = what₂.places.val w (star x)

  T_level : ∀ u, (mem u).A.T ∈ host.levelPrimes

  T_norm : ∀ u, ∃ π : 𝓞 host.E, (π : host.E) ∈ host.K ∧
    (π : host.E) * host.conj (π : host.E) = ((mem u).A.T : host.E) ∧
    (π - 1) ∈ Ideal.span {((host.QS * host.q * host.d * (host.g 0 * host.g 1) ^ 2 : ℕ) : 𝓞 host.E)}

  sp_T : letI := host.cmStar; sp.T = (mem u₀).A.T
  cOf : what₂.Word → host.E
  cOf_ne : ∀ u, cOf u ≠ 0
  cOf_eq : ∀ u, cOf u * host.conj (cOf u) * ((mem u).A.T : host.E) = ((mem u₀).A.T : host.E)

  T_win : ∀ u, (mem u).A.Tstar ≤ ((mem u).A.T : ℝ) ∧
    ((mem u).A.T : ℝ) ≤ (1 + 1 / ((R.f : ℝ) * R.k)) * (mem u).A.Tstar

  GamP_eq : ∀ u, (mem u).A.GamP = (mem u₀).A.GamP

  T_ne_pde : ∀ u, (mem u).A.T ≠ host.pde ∧ (mem u).A.T ≠ host.pde'

  Dstar_eq : ∀ u, (mem u).A.Dstar = what₂.Dstar

  clsLat : letI := host.cmStar; ∀ u i, (mem u).C.cls i → Submodule (𝓞 host.E) (sp.X i).V
  clsLat_lat : letI := host.cmStar; ∀ u i c, Submodule.IsLattice host.E (clsLat u i c)

  eMu : ∀ u, what₂.Mu u ≃ₗ[ℂ] (mem u).A.Mram

  eMt : ∀ u, (mem u).P.Mt ≃ₗ[ℂ] what₂.Amb what₂.mu0

  perCol_base_eq_PtilCol : ∀ u (φ : what₂.Mu u) (F : what₂.Amb what₂.mu0),
    what₂.perCol u what₂.mu0 φ F = (mem u).P.PtilCol ((eMu u φ : (mem u).A.Mram) :
      (mem u).C.cls 0 → (mem u).C.Y 0 → ℂ) ((eMt u).symm F)

  Bu_linL : ∀ u (F : what₂.EE), IsLinearMap ℂ (fun φ : what₂.Mu u => what₂.Bu u φ F)
  Bu_linR : ∀ u (φ : what₂.Mu u), IsLinearMap ℂ (fun F : what₂.EE => what₂.Bu u φ F)

  chTw : ∀ u, what₂.Tup → ColumnChain R what₂.Tau (hcW u)
  memberColumns_twistedChain_base : ∀ u, chTw u what₂.mu0 = (mem u).C
  e0Tw : ∀ u μ, ((mem u).C.cls 0 → (mem u).C.Y 0 → ℂ) ≃ₗ[ℂ] ((chTw u μ).cls 0 → (chTw u μ).Y 0 → ℂ)
  PTw : ∀ u μ, PeriodMap R (chTw u μ)
  eMtTw : ∀ u μ, (PTw u μ).Mt ≃ₗ[ℂ] what₂.Amb μ
  perCol_tie : ∀ u μ, μ ≠ what₂.mu0 → ∀ (φ : what₂.Mu u) (F : what₂.Amb μ), what₂.perCol u μ φ F =
    (PTw u μ).PtilCol (e0Tw u μ ((eMu u φ : (mem u).A.Mram) : (mem u).C.cls 0 → (mem u).C.Y 0 → ℂ))
      ((eMtTw u μ).symm F)

  jEE : div.RR.V →ₛₗ[what₂.embLL] what₂.EE
  jEE_basis : LinearIndependent ℂ (fun i => jEE (div.RR.b i)) ∧
    Submodule.span ℂ (Set.range (fun i => jEE (div.RR.b i))) = ⊤

  jN : ∀ u, (div.Nu u).V →ₛₗ[what₂.embLL] what₂.Mu u
  jN_basis : ∀ u, LinearIndependent ℂ (fun i => jN u ((div.Nu u).b i)) ∧
    Submodule.span ℂ (Set.range (fun i => jN u ((div.Nu u).b i))) = ⊤

  Dall_eq : div.Dall = what₂.Dall
  delP_eq : div.delP = what₂.delp

  Dt : Type
  [instDt : CommGroup Dt]
  detCls : ∀ u i, (mem u).C.cls i → Dt
  muTil : ℕ → Dt →* ℂˣ
  chiD : Dt →* ℂˣ

  UO : Subgroup Dt
  chiD_UO : ∀ x ∈ UO, chiD x = 1

  e1Dt : letI := host.cmStar; unitary host.E →* Dt

  rest_detCharacter_on_unitary_eq : letI := host.cmStar; ∀ z : unitary host.E,
    ((chiD (e1Dt z) : ℂˣ) : ℂ) = ∏ τ : what₂.Tau, (host.emb ((eTau τ : R.Psi) : R.GG) (z : host.E))⁻¹

  relDet : letI := host.cmStar; ∀ N, SDLat host.E N → SDLat host.E N → Dt ⧸ UO
  relDet_self : letI := host.cmStar; ∀ N L, relDet N L L = 1
  relDet_mul : letI := host.cmStar; ∀ N L L' L'', relDet N L L' * relDet N L' L'' = relDet N L L''
  relDet_smul : letI := host.cmStar; ∀ N (L L' : SDLat host.E N) (γ : Matrix.unitaryGroup (Fin N) host.E),
    L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) host.E) L.1 → relDet N L L' = QuotientGroup.mk (e1Dt ⟨(γ : Matrix (Fin N) (Fin N) host.E).det, Matrix.det_of_mem_unitary γ.2⟩)

  rhoDet_eq_inv_muTilde_chiD_pow : ∀ u i (c : (mem u).C.cls i),
    (mem u).C.rhoDet i c = (((muTil (i + 1) (detCls u i c))⁻¹ *
      (chiD (detCls u i c)) ^ (-(((R.N (i + 1)) / 2 : ℕ) : ℤ)) : ℂˣ) : ℂ)
  rhoDetPrime_eq_muTilde_mul_chi_pow : ∀ u i (c : (mem u).C.cls (i + 1)),
    (mem u).C.rhoDet' i c = ((muTil (i + 1) (detCls u (i + 1) c) *
      (chiD (detCls u (i + 1) c)) ^ ((((R.N i) / 2 : ℕ) : ℤ)) : ℂˣ) : ℂ)

  dsig : what₂.Tau → ℝ
  dsig_pos : ∀ ρ, 0 < dsig ρ

  s : Formalism.MainNotions.S.Draft.SData R host.F host.E conjF what₂.Word what₂.Tau hcW

  s_split : ∀ p, (s.atP p).split.isSome ↔
    Formalism.MainNotions.S.Loc.resChar p ∈ ({host.g 0, host.g 1} : Finset ℕ)

  s_HH : Module.finrank ℂ s.HH = what₂.Dall

  s_Cu : ∀ u, s.Cu u ≃ₗ[ℂ] (mem u).A.Mu0

  s_PlF : s.PlF ≃ HeightOneSpectrum (𝓞 host.F)

  loc : LocTheory

  locA : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (loc l)

  locT : ∀ (l : ℕ) [Fact l.Prime], LocTied l (loc l) (locA l)

  nd : NData R host what₂

  ntw : NTw R host what₂ LL0 nd
  naut : NAut nd

  nbc : NBC naut

  nexp : NExp R host what₂ LL0 nd ntw

  ntypes : NTypes naut

  nStage_trivialCharacter_compat : ntypes.IdempotentMatchesAction

  nStage_trivialCharacter_coeff_eq : ∀ g : G0g nd, what₂.embLL ((nexp.eLL0 g : ↥LL0) : what₂.LL) = ntypes.e0.coeff g

  nth : NTh R host what₂ LL0 nd ntw nexp

  nbr : ∀ (i : nd.Loc) (w : HeightOneSpectrum (𝓞 host.E)), w ∈ Formalism.BasicNotions.placesOver host.E (nd.l i) →
    Formalism.BasicNotions.LocBridge (nd.l i) host.E nd.Om (ReciprocityTheory.Gal.Dec (F := host.E) (nd.plOm.1 w)) (nd.O i)

  nbr_ind : ∀ (i : nd.Loc) (w : HeightOneSpectrum (𝓞 host.E)) (hw : w ∈ Formalism.BasicNotions.placesOver host.E (nd.l i))
    (x : nd.Om), x ∈ nd.plOm.1 w ↔ ‖(nbr i w hw).j x‖ ≤ 1

  self_good : ∀ (i : nd.Loc) (w : HeightOneSpectrum (𝓞 host.E)) (hw : w ∈ Formalism.BasicNotions.placesOver host.E (nd.l i)),
    Formalism.BasicNotions.Loc.GoodCoef host.condN (nbr i w hw).LL

  ntwbr : ∀ (i : ntw.Tw) (w : HeightOneSpectrum (𝓞 host.E)), w ∈ Formalism.BasicNotions.placesOver host.E (ntw.l i) →
    Formalism.BasicNotions.LocBridge (ntw.l i) host.E nd.Om (ReciprocityTheory.Gal.Dec (F := host.E) (nd.plOm.1 w)) (ntw.O0 i)

  ntwbr_ind : ∀ (i : ntw.Tw) (w : HeightOneSpectrum (𝓞 host.E)) (hw : w ∈ Formalism.BasicNotions.placesOver host.E (ntw.l i))
    (x : nd.Om), x ∈ nd.plOm.1 w ↔ ‖(ntwbr i w hw).j x‖ ≤ 1

  loc_tie : Formalism.MainNotions.N.LocTie nd naut loc nbr
  bc_tie : Formalism.MainNotions.N.BcTie nd naut ntypes
  rbar_tie : Formalism.MainNotions.N.RbarTie nd naut ntypes
  mtpar_tie : Formalism.MainNotions.N.MtParTie nd naut ntypes

  Z_tie : ∀ i x, x ∈ nd.Z i ↔ x ∈ Formalism.MainNotions.N.ZN nd naut i
  Zgood_tie : ∀ i x, x ∈ nd.Zgood i ↔ x ∈ Formalism.MainNotions.N.ZgoodN nd naut i

  etaJ_tie : ∀ j w, 1 ≤ j → j ≤ R.m → what₂.etaJ j w = ∑ i ∈ nd.locs j w, nd.etaLoc i

  fm : ∀ u, MemberForms what₂.LL what₂.embLL what₂.places what₂.Tau (hcW u) (mem u).C (mem u).A (mem u).P

  eMu_isom : ∀ u (φ ψ : what₂.Mu u), inner ℂ φ ψ =
    (fm u).ipC 0 ((eMu u φ : (mem u).A.Mram) : (mem u).C.cls 0 → (mem u).C.Y 0 → ℂ)
      ((eMu u ψ : (mem u).A.Mram) : (mem u).C.cls 0 → (mem u).C.Y 0 → ℂ)

  nuIn : ∀ u, (div.Nu u).V →ₗ[what₂.LL] ((fm u).lat 0).V
  nuIn_inj : ∀ u, Function.Injective (nuIn u)
  nuIn_range : ∀ u, LinearMap.range (nuIn u) = (fm u).ramSub
  nuIn_jN : ∀ u (x : (div.Nu u).V),
    ((eMu u (jN u x) : (mem u).A.Mram) : (mem u).C.cls 0 → (mem u).C.Y 0 → ℂ) = (fm u).emb 0 (nuIn u x)

  nuIn_norm : ∀ u v (x : (div.Nu u).V), Formalism.HermitianLatticesTheory.normAt (div.Nu u).b (div.Nu u).X v x =
    Formalism.HermitianLatticesTheory.normAt ((fm u).lat 0).b ((fm u).lat 0).X v (nuIn u x)

  jEE_norm : ∀ x : div.RR.V,
    Formalism.HermitianLatticesTheory.normAt div.RR.b div.RR.X (InfinitePlace.mk what₂.embLL) x = ‖jEE x‖

  s_Cu_isom : ∀ u (x y : s.Cu u), inner ℂ x y =
    (fm u).ipC 0 ((s_Cu u x : (mem u).A.Mu0) : (mem u).C.cls 0 → (mem u).C.Y 0 → ℂ)
      ((s_Cu u y : (mem u).A.Mu0) : (mem u).C.cls 0 → (mem u).C.Y 0 → ℂ)

  sEE : what₂.EE →ₗᵢ⋆[ℂ] s.HH

  cd : CDHaar

  jet : ThetaJet R host

  jetU : jet.Sit → what₂.Word
  jetL : ∀ i, (mem (jetU i)).C.cls (jet.jOf i - 1)
  jetL' : ∀ i, (mem (jetU i)).C.cls (jet.jOf i)

  jetW : jet.Sit → what₂.places.Pl
  jetW_l : ∀ i, what₂.places.resChar (jetW i) = (jet.loc i).l
  jetTau : ∀ i, ZMod (jet.loc i).d → what₂.Tau
  jetW1 : jet.Sit1 → what₂.places.Pl
  resChar_thetaJetPlaceDegOne : ∀ i, what₂.places.resChar (jetW1 i) = (jet.loc1 i).l
  jetTau1 : jet.Sit1 → what₂.Tau
  jetU1 : jet.Sit1 → what₂.Word
  jetL1 : ∀ i, (mem (jetU1 i)).C.cls (jet.j1Of i - 1)
  jetL1' : ∀ i, (mem (jetU1 i)).C.cls (jet.j1Of i)

  gx : GlobalExtra what₂.LL what₂.Tau

  gat : ∀ u (w : what₂.places.Pl), GIdx host (mem u).A.T (what₂.places.resChar w) →
    Formalism.MainNotions.G.GAtP (what₂.places.resChar w)

  gat_d : ∀ u w h, (gat u w h).d = Module.finrank ℂ (mem u).A.Mu0

  Y_sigval : letI := host.cmStar; ∀ j, j ≤ R.m → ∀ τ : host.E →+* ℂ, (sp.Y j).sig τ = sigYD R j

attribute [instance] D7.wordFin D7.nfLL D7.starLL D7.tcLL D7.galLL D7.instDt

namespace D7

variable (D : D7)

def colsS (u : D.what₂.Word) : Set ((D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) :=
  ((D.mem u).A.Mu0 : Set _)

def duS (u : D.what₂.Word) : ℕ :=
  haveI := (D.mem u).A.Mu0_fd; Module.finrank ℂ (D.mem u).A.Mu0

def zmOf (u : D.what₂.Word) : letI := D.host.cmStar; (D.sp.Y 0).V :=
  letI := D.host.cmStar; (D.cOf u)⁻¹ • D.sp.zm

def GatFin : Prop := ∀ u w h, (D.gat u w h).FinClasses

def besS (u : D.what₂.Word) (φ : D.what₂.Mu u) (F : D.what₂.EE) : ℂ :=
  inner ℂ (D.sEE F) (D.s.Pu u ((D.s_Cu u).symm ⟨(D.eMu u φ).1, (D.eMu u φ).2.1⟩))

def RRFull : Prop :=
  D.div.RR.L.FG ∧ Submodule.span D.what₂.LL (D.div.RR.L : Set D.div.RR.V) = ⊤

def NuFull : Prop := ∀ u,
  (D.div.Nu u).L.FG ∧ Submodule.span D.what₂.LL ((D.div.Nu u).L : Set (D.div.Nu u).V) = ⊤

def iota0 : D.what₂.Amb D.what₂.mu0 →ₗ[ℂ] D.what₂.EE := D.what₂.iota D.what₂.mu0

def BuRational : Prop := ∀ u (φ : (D.div.Nu u).V) (x : D.div.RR.V),
  D.what₂.Bu u (D.jN u φ) (D.jEE x) = D.what₂.embLL (D.div.Bk u φ x)

end D7

def bridge_cols_conj : Prop := ∀ (D : D7) (u : D.what₂.Word),
  ∃ (S : Submodule ℂ ((D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ)) (_ : FiniteDimensional ℂ S),
    (S : Set _) = D.colsS u ∧ Module.finrank ℂ S = D.duS u

def FactSigYDceil : Prop := ∀ (R : Ranks) (j : ℕ), j < R.m →
  (sigYD R j).2 = ((R.m - 1 - j + 1) / 2) ∧ (sigYD R j).1 + (sigYD R j).2 = R.rankY j

def FactBuUnique : Prop := ∀ (D : D7), Rows.BuDef D.what₂ →
  (∀ x : D.what₂.EE, ∃ F ∈ D.what₂.V0 D.what₂.mu0, D.iota0 F = x) →
  ∀ B' : ∀ u, D.what₂.Mu u → D.what₂.EE → ℂ,
    (∀ u φ F, F ∈ D.what₂.V0 D.what₂.mu0 → D.what₂.perCol u D.what₂.mu0 φ F = B' u φ (D.iota0 F)) → B' = D.what₂.Bu

def FactDGam (D : D7) (C : ℝ) : Prop := ∀ u, Real.log ((D.mem u).C.DGam : ℝ) ≤ C * D.R.f * D.R.N D.R.m * Real.log ((D.R.f : ℝ) * D.R.N D.R.m)

def FactPsiCardViaTau : Prop := ∀ (D : D7), Nat.card (D.R.Psi) = D.R.f

def AnisotropicLineIndepOfMember : Prop := ∀ (D : D7) (u : D.what₂.Word),
  ∃ c : D.host.E, c ≠ 0 ∧ c * D.host.conj c * ((D.mem u).A.T : D.host.E) = ((D.mem D.u₀).A.T : D.host.E)

def FactUnitRuleAgree : Prop := ∀ (D : D7) (w : D.what₂.places.Pl) (x : ℚ),
  ((Rows.unitRule D.what₂.places w x : ℚ) : ℝ) = unitRule D.what₂.LL (D.plEq w) (x : ℝ)

end Formalism.BasicNotions

end
