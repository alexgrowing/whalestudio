import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RightTranslationActionApply
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HermitianCodeWordWeilElementMemQuadraticField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.XiAtPenultimateEqXiCpl1
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.H90USurjective
import Formalism.LocalToGlobal.Columns.RowFormsSym
import Formalism.LocalRingCardinality.DataKerP
import Formalism.LocalToGlobal.HermitianForms.BothSym

noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Chr

def GStep.NormalFor {E K A : Type} [Field E] [NumberField E] [Field K] {n : ℕ} (S : GStep E K n) (b : S.β) (f : S.D b → A)
    (q : S.D b) : Prop :=
  f q = Classical.epsilon (p := fun r => ∃ g : S.G b, r = f (g • q)) (h := ⟨f q⟩)

def GStep.act {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} (S : GStep E K n) (b : S.β) (g : S.G b) (d : S.D b) : S.D b := g • d

@[reducible] def GStep.reRep {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} (S : GStep E K n) (pref : ∀ b, S.D b → Prop) :
    GStep E K n :=
  { S with rp := fun b => prefRep (pref b), rp_spec := fun b => prefRep_spec (pref b) }

open Classical in

def cosetIn {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
    {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ} (q : PtAt R sel mu cst u j)
    (P : rowSG Pr sel mu) : Set (Sp X.E (R.N j)) :=
  {z | ∃ y ∈ q.1.2, ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ • (z - (frsF sel mu q.1.1 P).symm y) ∈ stdAt X.E (R.N j) P.1}

@[reducible] def starE (B : Base) : StarRing B.fields.E := B.fields.starE

attribute [local instance] starE

abbrev TC (B : Base) (X : PreX B.toPre) := ColIn B X

namespace TC

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

abbrev Ps : LevFam B.fields.E B.fields.K B.R.r (B.primes X).vGs := rPsymF I.Ch

abbrev Tp (a : I.ι) : TopLev B.fields (B.primes X) B.R (I.Q a) := topLev I.Ch I.sel (I.tup a) (I.cst a) I.Ps

abbrev stp0 (u : B.Word) (a : I.ι) (j : ℕ) : GStep B.fields.E B.fields.K (B.R.N j) :=
  stepAt I.sel (I.tup a) (I.cst a) (I.idx a) (I.Tp a) u j

def pref (u : B.Word) (a : I.ι) (j : ℕ) (b : (I.stp0 u a j).β) (q : (I.stp0 u a j).D b) : Prop :=
  (j = 0 → (I.stp0 u a j).NormalFor b (fun q' : (I.stp0 u a j).D b => q'.1.1.deco) q) ∧
    (j + 1 = B.R.m → (I.stp0 u a j).NormalFor b (fun q' : (I.stp0 u a j).D b => cosetIn q') q) ∧ (I.Tp a).pref u j q.1.1

abbrev stp (u : B.Word) (a : I.ι) (j : ℕ) : GStep B.fields.E B.fields.K (B.R.N j) := (I.stp0 u a j).reRep (I.pref u a j)

def rho (u : B.Word) (a : I.ι) (i : ℕ) (b : Idx I.sel (I.tup a) (I.idx a) i) (p : (I.stp u a i).D b) : ℂ :=
  ((rhoAt I.SQ I.C (I.xi a) i p.1.1 : ℂˣ) : ℂ)

def rho' (u : B.Word) (a : I.ι) (i : ℕ) (b : Idx I.sel (I.tup a) (I.idx a) (i + 1)) (p : (I.stp u a (i + 1)).D b) : ℂ :=
  ((rhoAt' I.SQ I.C (I.xi a) i p.1.1 : ℂˣ) : ℂ)

def th (u : B.Word) (a : I.ι) (i : ℕ) (b : Idx I.sel (I.tup a) (I.idx a) i) (b' : Idx I.sel (I.tup a) (I.idx a) (i + 1))
    (p : (I.stp u a i).D b) (p' : (I.stp u a (i + 1)).D b') : VCx B.fields.Tau (B.R.N i) (B.R.N (i + 1)) → ℂ :=
  thAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i b b' p p'

@[reducible] def chIn (u : B.Word) (a : I.ι) : ChainIn B.fields.E B.fields.K B.fields.Tau B.R where
  S := I.stp u a
  rho i c := I.rho u a i c.1 (GStep.rep _ c)
  rho' i c := I.rho' u a i c.1 (GStep.rep _ c)
  jet i c c' := jetMap (jetC I.J.cD (I.th u a i c.1 c'.1 (GStep.rep _ c) (GStep.rep _ c'))) 0
  DG := DGam B.fields.E B.R

@[reducible] def atIn (u : B.Word) (a : I.ι) : AtIn (I.chIn u a) where
  T := B.T u
  ST := (B.primes X).vT u
  A j := { tdatAt I.sel (I.tup a) (I.cst a) (I.idx a) (I.Tp a) u j with }
  psi P := psiWeil P.1 B.host.xi0
  duStar := B.duStar u
  Dstar := B.Dstar
  GamP := B.GamP

open Classical in

def fmIn (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) : FmIn (I.atIn u a) B.places where
  tauOf w := tauAt hPr u w
  seenP w := decide (seenC (B.primes X) u w)
  beOn τ := brNorm (N_m_succ B.R) (B.wts.lamTrue u B.R.m τ) (B.wts.sgTrue τ)
  beOn_nonneg _ := fockOpNorm_nonneg _ _ _
  thFree i s c c' := eNorm I.A s (GStep.rep (I.stp u a i) c).1.1.deco.1.N (GStep.rep (I.stp u a (i + 1)) c').1.1.deco.1.N
  thFree_nonneg _ _ _ _ := eNorm_nonneg _ _ _ _

def perIn (u : B.Word) (a : I.ι) : PerIn (I.chIn u a) where
  S' := stepX I.Ch I.sel (I.tup a) I.Ps
  b0 := idxTop I.sel (I.tup a) (I.idx a)
  til _ p := topPt (R := B.R) I.sel (I.tup a) (I.cst a) u (tilF I.sel (I.tup a) u p.1.1)
  ext _ := (extTop I.Ch I.sel (I.tup a) (I.cst a) I.Ps :
    FrmG (rowTyG I.Ch I.Ps) (levQX B.R I.sel (I.tup a)) →* FrmG ((I.Tp a).levG B.R.m) ((I.Tp a).levQ B.R.m))
  sg := B.wts.sgW
  tz := star (((B.primes X).piT u : 𝓞 B.fields.E) : B.fields.E)
  H _ := ⊤

def pt0 (u : B.Word) (a' a : I.ι) (p : PtAt B.R I.sel (I.tup a') (I.cst a') u 0) : PtAt B.R I.sel (I.tup a) (I.cst a) u 0 :=
  ⟨(extTo (I.Q a) p.1.1, ∅), by
    rw [ysAt_ys_of_ne I.sel (I.tup a) (I.cst a) (by have := B.R.two_le_m; omega)]
    rfl⟩

def cl0 (u : B.Word) (a : I.ι) (b : Idx I.sel (I.tup a) (I.idx a) 0) (c : (I.stp u I.mu0 0).Cl) : (I.stp u a 0).Cl :=
  (I.stp u a 0).cl b (I.pt0 u I.mu0 a ((I.stp u I.mu0 0).rep c))

structure Laws : Prop where
  pr : (B.primes X).Ok
  ch : ∀ u a, (I.chIn u a).Ok
  lev : ∀ u a, (I.atIn u a).Ok
  per : ∀ u a, (I.perIn u a).Ok
  ovr : ∀ u a, (I.perIn u a).Over (I.atIn u a)
  atL : ∀ u a, (I.atIn u a).Laws B.fields.emb B.embLL (B.hcW u)
  fmL : ∀ u a, FmLaws (I.atIn u a) (I.perIn u a) B.fields.emb B.embLL (B.hcW u) B.places (ch u a) (per u a)
  xi0 : I.xi I.mu0 = 1
  idx0 : ∀ a, Nonempty (Idx I.sel (I.tup a) (I.idx a) 0)
  bij0 : ∀ u a b, Function.Bijective (I.cl0 u a b)
  lat : ∀ u a i c, Submodule.IsLattice B.fields.E ((I.stp u a i).rep c).1.1.deco.1.L

structure Pins (B : Base) (X : PreX B.toPre) : Prop where
  iX : letI := B.host.cmStar; ∀ (a : Fin B.sp.X'.rank) (b : Fin (B.sp.X B.R.m).rank), (a : ℕ) = b →
    B.sp.iX' (B.sp.X'.frame a) = (B.sp.X B.R.m).frame b
  cof : ∀ u, B.cOf u * (X.piT u : B.host.E) = (X.piT B.u₀ : B.host.E)

def crd (B : Base) (i : ℕ) (hi : i ≤ B.R.m) :
    letI := B.host.cmStar; (B.sp.X i).V ≃ₗ[B.host.E] (Fin (B.R.N i) → B.host.E) :=
  letI := B.host.cmStar
  (B.sp.X i).frame.equivFun.trans (LinearEquiv.funCongrLeft B.host.E B.host.E (finCongr (B.sp.X_rank i hi)).symm)

open Classical in

def latAt (u : B.Word) (a : I.ι) (i : ℕ) (c : (I.stp u a i).Cl) :
    letI := B.host.cmStar; Submodule (𝓞 B.host.E) (B.sp.X i).V :=
  letI := B.host.cmStar
  if hi : i ≤ B.R.m then
    ((I.stp u a i).rep c).1.1.deco.1.L.map
      (((crd B i hi).symm : (Fin (B.R.N i) → B.host.E) →ₗ[B.host.E] (B.sp.X i).V).restrictScalars (𝓞 B.host.E))
  else (B.sp.X i).L0

variable (l : I.Laws)

abbrev chain (u : B.Word) (a : I.ι) : ColumnChain B.R (Tau B.R) (B.hcW u) :=
  (I.chIn u a).chain B.fields.emb B.embLL (l.ch u a) (B.hcW u)

abbrev atT (u : B.Word) (a : I.ι) : ColumnsAtT B.R (I.chain l u a) :=
  (I.atIn u a).atT B.fields.emb B.embLL (l.ch u a) (l.lev u a) (B.hcW u) (l.atL u a)

abbrev per (u : B.Word) (a : I.ι) : PeriodMap B.R (I.chain l u a) :=
  (I.perIn u a).per B.fields.emb B.embLL (l.ch u a) (l.per u a) (B.hcW u)

def fm (u : B.Word) (a : I.ι) :
    MemberForms B.LL B.embLL B.places (Tau B.R) (B.hcW u) (I.chain l u a) (I.atT l u a) (I.per l u a) :=
  forms (I.atIn u a) (I.perIn u a) B.fields.emb B.embLL (B.hcW u)
    (I.fmIn l.pr u a)
    (l.ch u a) (l.lev u a) (l.per u a) (l.atL u a) (l.fmL u a) (l.ovr u a)

def eCls0 (u : B.Word) (a : I.ι) : (I.stp u I.mu0 0).Cl ≃ (I.stp u a 0).Cl :=
  Equiv.ofBijective (I.cl0 u a (l.idx0 a).some) (l.bij0 u a _)

include l in
theorem latAt_lattice (u : B.Word) (a : I.ι) (i : ℕ) (c : (I.stp u a i).Cl) :
    letI := B.host.cmStar; Submodule.IsLattice B.host.E (I.latAt u a i c) := by
  letI := B.host.cmStar
  unfold latAt
  split_ifs with hi
  · have h := l.lat u a i c
    refine ⟨h.fg.map _, ?_⟩
    have h2 := congrArg (Submodule.map ((crd B i hi).symm : (Fin (B.R.N i) → B.host.E) →ₗ[B.host.E] (B.sp.X i).V)) h.span_eq_top
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at h2
    exact h2
  · exact (B.sp.X i).standardTuple_isLattice

def cols : Cols B where
  mem u := ⟨I.chain l u I.mu0, I.atT l u I.mu0, I.per l u I.mu0⟩
  A_T _ := rfl
  A_duStar _ := rfl
  A_Dstar _ := rfl
  A_GamP _ := rfl
  clsLat u := I.latAt u I.mu0
  clsLat_lat u := I.latAt_lattice l u I.mu0
  Tup := I.ι
  mu0 := I.mu0
  muStar := I.muStar
  muStar' := I.muStar'
  chTw := I.chain l
  memberColumns_twistedChain_base _ := rfl
  e0Tw u a := LinearEquiv.funCongrLeft ℂ _ (I.eCls0 l u a).symm
  PTw := I.per l
  Dt := DtQ B.host I.SQ
  detCls u i c := detPt B.host I.SQ ((I.stp u I.mu0 i).rep c).1.1
  muTil := muTilQ B.host I.SQ I.C.mu0
  chiD := tildeQ B.host I.SQ I.C.chiPsi
  UO := UOQ B.host I.SQ
  chiD_UO := (trueDtPackQ I.SQ I.C).chiD_UO
  e1Dt := e1Q B.host I.SQ
  rest_detCharacter_on_unitary_eq := (trueDtPackQ I.SQ I.C).rest_detCharacter_on_unitary_eq
  relDet := (trueDtPackQ I.SQ I.C).relDet
  relDet_self := (trueDtPackQ I.SQ I.C).relDet_self
  relDet_mul := (trueDtPackQ I.SQ I.C).relDet_mul
  relDet_smul := (trueDtPackQ I.SQ I.C).relDet_smul
  rhoDet_eq_inv_muTilde_chiD_pow u i c := by
    show ((rhoAt I.SQ I.C (I.xi I.mu0) i _ : ℂˣ) : ℂ) = _
    rw [l.xi0, rhoAt_one]
  rhoDetPrime_eq_muTilde_mul_chi_pow u i c := by
    show ((rhoAt' I.SQ I.C (I.xi I.mu0) i _ : ℂˣ) : ℂ) = _
    rw [l.xi0, rhoAt'_one]
  fm u := I.fm l u I.mu0

def Law0 : Prop := ∀ u a, ∃ e : ((I.fm l u I.mu0).lat 0).V ≃ₗ[B.LL] ((I.fm l u a).lat 0).V,
  (∀ x, x ∈ ((I.fm l u I.mu0).lat 0).L ↔ e x ∈ ((I.fm l u a).lat 0).L) ∧
    ∀ x, (I.fm l u a).emb 0 (e x) = (I.cols l).e0Tw u a ((I.fm l u I.mu0).emb 0 x)

structure Later (B : Base) (C : Cols B) where
  W : RowsRest B C
  V : DivStage B C W
  S : SStage B C W
  N : NStage B C W
  G : GJStage B C

abbrev rec7 (Z : Later B (I.cols l)) : D7 := assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G

def tw (l0 : I.Law0 l) (Z : Later B (I.cols l)) : TwForms (I.rec7 l Z) where
  A := I.atT l
  A_T _ _ := rfl
  fm := I.fm l
  e0 u a := (l0 u a).choose
  twist_preserves_base_lattice u a := (l0 u a).choose_spec.1
  embed_mul_block_embedding u a := (l0 u a).choose_spec.2
  eMu0 _ _ _ := LinearEquiv.refl _ _
  eMu0_lat _ _ _ _ := Iff.rfl
  eMu0_emb _ _ _ _ := HEq.rfl

end TC

namespace TC

open Formalism.UG

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

abbrev GA (B : Base) (n : ℕ) : Type := GL (Fin n) (AfE B.host.F B.host.E)

abbrev PtOf {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 B.fields.E))} (g : GA B n) (p : DecoF B.fields.E n ST SG Q) : Prop :=
  IsPtOf B.sp.cm g p

def baseL (B : Base) (n : ℕ) (t : 𝓞 B.host.E) : Set (Fin n → B.host.E) :=
  {x | ∀ j : Fin n, ∃ r : 𝓞 B.host.E, x j = (r : B.host.E) ∧ (j.1 + 1 = n → t ∣ r)}

def UnderQ (a : I.ι) (v : HeightOneSpectrum (𝓞 B.host.F)) : Prop := ∃ P ∈ I.Q a, P.under (𝓞 B.host.F) = v

structure Reads (u : B.Word) (a : I.ι) (i : ℕ) {Ch : Type} (chOf : (I.stp u a i).Cl → Ch)
    (Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)) (U : Ch → Subgroup (GA B (B.R.N i))) (chi : ∀ β, U β →* ℂˣ)
    (y : (I.stp u a i).Cl → GA B (B.R.N i)) (st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E)
    (k : Ch → GA B (B.R.N i)) : Prop where
  key : ∀ c c', chOf c = chOf c' ↔ c.1 = c'.1 ∧ cosetIn ((I.stp u a i).rep c) = cosetIn ((I.stp u a i).rep c')
  onto : Function.Surjective chOf
  lb : ∀ β x, x ∈ Lb β ↔ x ∈ baseL B (B.R.N i) (X.piT u)

  k_std : ∀ β, ∃ p : DecoF B.fields.E (B.R.N i) ∅ ∅ ∅, PtOf (k β) p ∧ p.deco.1.N = stdLat B.fields.E (B.R.N i)
  k_off : ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → ¬ I.UnderQ a v →
    (a = I.mu0 ∨ ∀ j, (B.host.g j : 𝓞 B.host.F) ∉ v.asIdeal) → bc (prV (E := B.host.E) v) (k β) = 1

  k_T : ∀ β (P : (B.primes X).vT u) (r j : Fin (B.R.N i)), r.1 + 1 = B.R.N i →
    HasRes P.1 (adAt B.host.F P.1 (((k β)⁻¹ : GA B (B.R.N i)).1 r j))
      (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0)
  pt : ∀ c, PtOf (y c * k (chOf c)) (extTo I.SQ ((I.stp u a i).rep c).1.1)
  lev : ∀ c (x : GA B (B.R.N i)) (q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u i), PtOf (y c * x * k (chOf c)) q →
    (x ∈ U (chOf c) ↔ ∃ κ : (I.stp u a i).G c.1, (I.stp u a i).gam c.1 κ = 1 ∧ ((I.stp u a i).act c.1 κ ((I.stp u a i).rep c)).1.1 = q ∧
      cosetIn ((I.stp u a i).act c.1 κ ((I.stp u a i).rep c)) = cosetIn ((I.stp u a i).rep c))
  chr : ∀ c (x : U (chOf c)) (κ : (I.stp u a i).G c.1), (I.stp u a i).gam c.1 κ = 1 →
    PtOf (y c * x.1 * k (chOf c)) ((I.stp u a i).act c.1 κ ((I.stp u a i).rep c)).1.1 →
    ((chi (chOf c) x : ℂˣ) : ℂ) = B.embLL (((I.stp u a i).chr c.1 κ : B.LLˣ) : B.LL)
  stab : ∀ c s, st c s = (I.stp u a i).gam c.1 s.1

def kStd (X : PreX B.toPre) (u : B.Word) (n : ℕ) : GA B n :=
  Classical.epsilon fun k : GA B n =>
    (∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf k p ∧ p.deco.1.N = stdLat B.fields.E n) ∧
    (∀ v : HeightOneSpectrum (𝓞 B.host.F), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → bc (prV (E := B.host.E) v) k = 1) ∧
    ∀ (P : (B.primes X).vT u) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt B.host.F P.1 ((k⁻¹ : GA B n).1 r j))
      (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0)

def yStd (u : B.Word) (i : ℕ) (c : (I.stp u I.mu0 i).Cl) : GA B (B.R.N i) :=
  Classical.epsilon fun g : GA B (B.R.N i) => PtOf (g * kStd X u (B.R.N i)) (extTo I.SQ ((I.stp u I.mu0 i).rep c).1.1)

abbrev stX (a : I.ι) : GStep B.fields.E B.fields.K (B.R.N B.R.m - 1) := stepX I.Ch I.sel (I.tup a) I.Ps

structure ReadsP (a : I.ι) (Lb : Submodule (𝓞 B.host.E) (Fin (B.R.N B.R.m - 1) → B.host.E))
    (U : Subgroup (GA B (B.R.N B.R.m - 1))) (chi : U →* ℂˣ) (y : (I.stX a).Cl → GA B (B.R.N B.R.m - 1))
    (lat : (I.stX a).Cl → Submodule (𝓞 B.host.E) (Fin (B.R.N B.R.m - 1) → B.host.E))
    (st : ∀ c, (I.stX a).Stab c → GL (Fin (B.R.N B.R.m - 1)) B.host.E) : Prop where
  lb : ∀ x, x ∈ Lb ↔ x ∈ baseL B (B.R.N B.R.m - 1) 1
  lat : ∀ c, lat c = ((I.stX a).rep c).1.1.deco.1.N
  pt : ∀ c, PtOf (y c) ((I.stX a).rep c).1.1
  lev : ∀ c (x : GA B (B.R.N B.R.m - 1)) (q : XPt (B.primes X) B.R I.sel (I.tup a)), PtOf (y c * x) q →
    (x ∈ U ↔ ∃ κ : (I.stX a).G c.1, (I.stX a).gam c.1 κ = 1 ∧ ((I.stX a).act c.1 κ ((I.stX a).rep c)).1.1 = q)
  chr : ∀ c (x : U) (κ : (I.stX a).G c.1), (I.stX a).gam c.1 κ = 1 → PtOf (y c * x.1) ((I.stX a).act c.1 κ ((I.stX a).rep c)).1.1 →
    ((chi x : ℂˣ) : ℂ) = B.embLL (((I.stX a).chr c.1 κ : B.LLˣ) : B.LL)
  stab : ∀ c s, st c s = (I.stX a).gam c.1 s.1

variable (l : I.Laws) (Z : Later B (I.cols l))

open Formalism.L2.Forms

def ReadsK (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {Ch : Type}
    (chOf : (I.stp u a i).Cl → Ch)
    (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
      (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) : Prop :=
  ∃ k, I.Reads u a i chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi)
    (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k

def IdY (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) : Prop :=
  ∀ y, (eY y).1 = y.1

def resT (u : B.Word) (a : I.ι) (v : (I.atT l u a).vT) : 𝓞 B.host.E →+* (I.atT l u a).Fv v := Ideal.Quotient.mk v.1.asIdeal

def IdV (u : B.Word) (a : I.ι)
    (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 B.host.F) // (B.T u : 𝓞 B.host.F) ∈ v.asIdeal}) : Prop :=
  ∀ v, (eV v).1 = v.1.under (𝓞 B.host.F)

def IdL (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m)
    (L : LevelCompatibleLattices (D := I.rec7 l Z) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)) : Prop :=
  (∀ v c z (h : z.1 ∈ ((I.stp u a i).rep c).1.1.deco.1.N), L.pr v c z = Submodule.Quotient.mk ⟨z.1, h⟩) ∧
    ∀ v c z (h : z.1 ∈ ((I.stp u a i).rep c).1.1.deco.1.dnN v), L.prk v c z = Submodule.Quotient.mk ⟨z.1, h⟩

structure IdG (G : GLoc (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (I.rec7 l Z).host.g) : Prop where
  piG : G.piG = X.piG
  psi : ∀ j v h (w : {w // w ∈ (B.primes X).vGs}), w.1.under (𝓞 B.host.F) = v → ∀ n : ℕ,
    G.psi0 j v h (n : kv B.host.F v) = B.embLL (I.Ch.psi0 w (n : 𝓞 B.fields.E ⧸ w.1.asIdeal))
  chi : ∀ j v h (w : {w // w ∈ (B.primes X).vGs}), w.1.under (𝓞 B.host.F) = v → ∀ (s : Fin B.R.m) (n : ℕ)
    (c : (𝓞 B.fields.E ⧸ w.1.asIdeal)ˣ), (c : 𝓞 B.fields.E ⧸ w.1.asIdeal) = n →
    G.chiB j v h s.1 (n : kv B.host.F v) = B.embLL ((I.Ch.chi s w c : B.LLˣ) : B.LL)

structure StdF (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i}
    (F : FormsTiedSym (I.rec7 l Z) u Ch chOf) : Prop where
  eV : I.IdV l u I.mu0 F.atT.eV
  piU : F.atT.piU = X.piT u
  res : F.atT.res = I.resT l u I.mu0
  gl : I.IdG l Z F.gl
  ends : ∀ i hi h, ∃ k, I.Reads u I.mu0 i (fun _ => ()) (fun _ => (F.cls i hi h).lev.Lb) (fun _ => (F.cls i hi h).lev.U)
    (fun _ => (F.cls i hi h).lev.chi) (fun c => ((F.cls i hi h).y c).1) (fun c s => ((F.cls i hi h).stabI c s).1) k
  yE : ∀ i hi h c, ((F.cls i hi h).y c).1 = I.yStd u i c
  mid : ∀ i h1 h2, I.ReadsK l Z u I.mu0 i (le_of_succ_m h2) (chOf i) (F.ch i h1 h2)
  eY : ∀ i hi h, I.IdY l Z u I.mu0 i hi (F.val i hi h).eY
  eYC : ∀ i h1 h2, I.IdY l Z u I.mu0 i (le_of_succ_m h2) (F.eYC i h1 h2)
  pr : ∀ i hi v c z (h : z.1 ∈ ((I.stp u I.mu0 i).rep c).1.1.deco.1.N), (F.lv i hi).pr v c z = Submodule.Quotient.mk ⟨z.1, h⟩
  prk : ∀ i hi v c z (h : z.1 ∈ ((I.stp u I.mu0 i).rep c).1.1.deco.1.dnN v), (F.lv i hi).prk v c z = Submodule.Quotient.mk ⟨z.1, h⟩
  fr0 : ∀ j v h, F.glev0.fr j v h = 1
  frP : ∀ j v h, F.glevP.fr j v h = 1
  what₂ : I.ReadsP I.mu0 F.clsP.lev.Lb F.clsP.lev.U F.clsP.lev.chi (fun c => (F.clsP.y c).1) F.clsP.lat fun c s => (F.clsP.stabI c s).1
  eW : ∀ z c (s : FrP (I.rec7 l Z)) s', s'.1 = s.1 → F.valP.eW z c s = z c s'
  z0 : ∀ j, F.til.z0 j = if j.1 + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 0
  eWz : ∀ z, F.eWz z = z

def StdC (C : ColsTiedSym (I.rec7 l Z)) : Prop := ∀ u, I.StdF l Z u (C.forms u)

end TC

end GlobalTheory.Mem.Col2

end
