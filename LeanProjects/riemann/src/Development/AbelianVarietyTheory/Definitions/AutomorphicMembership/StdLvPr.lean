import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Formalism.LocalToGlobal.HermitianForms.TiedTwSym
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Chr Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure CarH {D : D7} (H : Formalism.L2.Herm.HermColsCh D) (F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)) : Prop where
  eV : ∀ u, (F u).atT.eV = H.vT u
  fv : ∀ u v (a : 𝓞 D.host.F), H.Fv u v ((F u).atT.res v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a)) = Ideal.Quotient.mk _ a
  car0 : ∀ u, SameCar (rank_eq_first_level D.R) (H.lev0 u).Lb ((F u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Lb
    (H.lev0 u).Uloc ((F u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Uloc
    (H.lev0 u).U ((F u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.U
    (fun c => ((H.lev0 u).y c).1) (fun c => (((F u).cls 0 (Nat.zero_le _) (Or.inl rfl)).y c).1)
    (fun c s => ((H.lev0 u).stabI c s).1) (fun c s => (((F u).cls 0 (Nat.zero_le _) (Or.inl rfl)).stabI c s).1)
  carC : ∀ u i (h1 : 1 ≤ i) (h2 : i + 1 ≤ D.R.m) (β : H.Ch u i),
    SameCar (rankN D i (le_of_succ_m h2)) (H.lev u i h1 (le_of_succ_m h2) β).Lb ((F u).ch i h1 h2 β).lev.Lb
      (H.lev u i h1 (le_of_succ_m h2) β).Uloc ((F u).ch i h1 h2 β).lev.Uloc
      (H.lev u i h1 (le_of_succ_m h2) β).U ((F u).ch i h1 h2 β).lev.U
      (fun c => ((H.cls u i h1 (le_of_succ_m h2) β).y c).1) (fun c => (((F u).ch i h1 h2 β).y c).1)
      (fun c s => ((H.cls u i h1 (le_of_succ_m h2) β).stabI c s).1) (fun c s => (((F u).ch i h1 h2 β).stabI c s).1)
  carM : ∀ u, SameCar (rankN D D.R.m le_rfl) (H.lev u D.R.m (one_le_m D.R) le_rfl (chM H u)).Lb
      ((F u).cls D.R.m le_rfl (Or.inr rfl)).lev.Lb
      (H.lev u D.R.m (one_le_m D.R) le_rfl (chM H u)).Uloc ((F u).cls D.R.m le_rfl (Or.inr rfl)).lev.Uloc
      (H.lev u D.R.m (one_le_m D.R) le_rfl (chM H u)).U ((F u).cls D.R.m le_rfl (Or.inr rfl)).lev.U
      (fun c => ((H.cls u D.R.m (one_le_m D.R) le_rfl (chM H u)).y ⟨c, chOf_m H u c⟩).1)
      (fun c => (((F u).cls D.R.m le_rfl (Or.inr rfl)).y c).1)
      (fun c s => ((H.cls u D.R.m (one_le_m D.R) le_rfl (chM H u)).stabI ⟨c, chOf_m H u c⟩ s).1)
      (fun c s => (((F u).cls D.R.m le_rfl (Or.inr rfl)).stabI c s).1)
  sp : ∀ u, (F u).gl.sp = (H.lev0 u).splitG
  fr0 : ∀ u i v h, (F u).glev0.fr i v h = reGL (rank_eq_first_level D.R) _ ((H.lev0 u).frG i v h)

structure CarT {D : D7} (H : Formalism.L2.Herm.HermColsCh D) (F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u))
    (A : ∀ u, Formalism.L2.Herm.AtT D u (H.vT u) (H.Fv u)) : Prop where
  piU : ∀ u, (F u).atT.piU = (A u).piU
  res : ∀ u, (F u).atT.res = (A u).res
  carP : ∀ u, SameCar (rankP D) (Formalism.L2.Herm.crdLat D.sp.X' D.sp.X'.L0) (F u).clsP.lev.Lb
    (A u).levP.Uloc (F u).clsP.lev.Uloc (A u).levP.U (F u).clsP.lev.U
    (fun c => ((A u).clsP.y c).1) (fun c => ((F u).clsP.y c).1)
    (fun c s => ((A u).clsP.stabI c s).1) (fun c s => ((F u).clsP.stabI c s).1)
  lattice₂ : ∀ u c, (F u).clsP.lat c = ((A u).lattice₂ c).map
    ((crdP D : D.sp.X'.V →ₗ[D.host.E] (Fin (D.R.N D.R.m - 1) → D.host.E)).restrictScalars (𝓞 D.host.E))
  pr : ∀ u (i : ℕ) (hi : i ≤ D.R.m) v c (z : Formalism.L2.Herm.Ld D u i c) (z' : Ld D u i hi c),
    z'.1 = crdN D i hi z.1 → ((F u).lv i hi).pr v c z' = (A u).pr i v c z
  prk : ∀ u (i : ℕ) (hi : i ≤ D.R.m) v c (z : Formalism.L2.Herm.Lk D u ((A u).Pv v) i c) (z' : Lk (F u).atT i hi v c),
    z'.1 = crdN D i hi z.1 → ((F u).lv i hi).prk v c z' = (A u).prk i v c z
  prC : ∀ u (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ D.R.m) v c (z : Formalism.L2.Herm.Ld D u i c)
    (z' : LdG D i (le_of_succ_m h2) (clsCrd D u i (le_of_succ_m h2) c)),
    z'.1 = crdN D i (le_of_succ_m h2) z.1 → ((F u).lvC i h1 h2).pr v c z' = (A u).pr i v c z
  z0 : ∀ u, (F u).til.z0 = crdN D D.R.m le_rfl (A u).z0
  ga : ∀ u c, ((F u).til.ga c).1 = reGL (rankN D D.R.m le_rfl) _
    (Formalism.L2.Herm.toGLb (D.sp.X D.R.m).frame ((A u).tilG c).1)

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : Later B (I.cols l))

def StdLvPr (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i}
    (F : FormsTiedSym (I.rec7 l Z) u Ch chOf) : Prop := ∀ i h1 h2,
  (∀ v c z (h : z.1 ∈ ((I.stp u I.mu0 i).rep c).1.1.deco.1.N), (F.lvC i h1 h2).pr v c z = Submodule.Quotient.mk ⟨z.1, h⟩) ∧
    ∀ v c z (h : z.1 ∈ ((I.stp u I.mu0 i).rep c).1.1.deco.1.dnN v), (F.lvC i h1 h2).prk v c z = Submodule.Quotient.mk ⟨z.1, h⟩

def StdLvC (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i}
    (F : FormsTiedSym (I.rec7 l Z) u Ch chOf) : Prop :=
  I.StdLvPr l Z u F ∧ ∀ j v h, F.glevJ.fr j v h = 1

instance (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf) :
    CoeFun (I.StdLvC l Z u F) fun _ => ∀ i h1 h2,
      (∀ v c z (h : z.1 ∈ ((I.stp u I.mu0 i).rep c).1.1.deco.1.N), (F.lvC i h1 h2).pr v c z = Submodule.Quotient.mk ⟨z.1, h⟩) ∧
        ∀ v c z (h : z.1 ∈ ((I.stp u I.mu0 i).rep c).1.1.deco.1.dnN v), (F.lvC i h1 h2).prk v c z = Submodule.Quotient.mk ⟨z.1, h⟩ :=
  ⟨fun h => h.1⟩

example (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf)
    (h : I.StdLvC l Z u F) (i h1 h2 v c z) (hz : z.1 ∈ ((I.stp u I.mu0 i).rep c).1.1.deco.1.N) :
    (F.lvC i h1 h2).pr v c z = Submodule.Quotient.mk ⟨z.1, hz⟩ := (h i h1 h2).1 v c z hz

def StdDt (dt : Formalism.L2.Herm.unitaryOneFiniteAdeles (I.rec7 l Z).sp.cm →* (I.rec7 l Z).Dt) : Prop :=
  ∀ (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (I.rec7 l Z).sp.cm) (a : GlobalTheory.Mem.Chr.Ideles B.host.E), IsDetLift B.sp.cm x.1 a →
    dt x = (QuotientGroup.mk a : DtQ B.host I.SQ)

def z0 (X : PreX B.toPre) (u : B.Word) : Fin (B.R.N B.R.m) → B.host.E :=
  fun j => if j.1 + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 0

def TopBase (u : B.Word) (a : I.ι) (U : Subgroup (GA B (B.R.N B.R.m))) (y : (I.stp u a B.R.m).Cl → GA B (B.R.N B.R.m)) : Prop :=
  ∀ c (d : XPt (B.primes X) B.R I.sel (I.tup a)) (g' : GA B (B.R.N B.R.m - 1)) (g : GA B (B.R.N B.R.m)),
    ((I.stp u a B.R.m).rep c).1.1 = tilF I.sel (I.tup a) u d → PtOf g' d →
    IsExt (I.rec7 l Z) (z0 X u) (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) g'.1 g.1 → g⁻¹ * y c ∈ U

section Tw

variable (l0 : I.Law0 l) {inQ : (I.rec7 l Z).what₂.Tup → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop}
  {T : Formalism.L2.Herm.TwChTied (I.rec7 l Z) inQ} {H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)} {J : Formalism.L2.Herm.TwChJointS T H}
  {F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)}

structure StdW (W : TwFormsTiedS (I.rec7 l Z) (I.tw l l0 Z) T J F) : Prop where
  eCls0 : ∀ u a, T.eCls0 u a = I.eCls0 l u a
  eY : ∀ u a i hi, T.eY u a i hi = Equiv.refl _
  lat : ∀ u a i, T.lat u a i = I.latAt u a i
  eVT : ∀ u a, (W.atT u a).eVT = Equiv.refl _
  eFv : ∀ u a v (r : 𝓞 B.host.E), (W.atT u a).res (F u).atT v r = I.resT l u a v r
  reads : ∀ u a ha i h1 hm, ∃ k, I.Reads u a i (T.chOf u a i) (fun β => (W.ch u a ha i h1 hm β).lev.Lb)
    (fun β => (W.ch u a ha i h1 hm β).lev.U) (fun β => (W.ch u a ha i h1 hm β).lev.chi)
    (fun c => ((W.ch u a ha i h1 hm (T.chOf u a i c)).y ⟨c, rfl⟩).1) (fun c s => ((W.ch u a ha i h1 hm (T.chOf u a i c)).stabI ⟨c, rfl⟩ s).1) k
  top : ∀ u a ha h1 β, I.TopBase l Z u a (W.ch u a ha B.R.m h1 le_rfl β).lev.U
    fun c => ((W.ch u a ha B.R.m h1 le_rfl (T.chOf u a B.R.m c)).y ⟨c, rfl⟩).1

  topk : ∀ u a ha h1, ∃ k, I.Reads u a B.R.m (T.chOf u a B.R.m) (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.Lb)
    (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.U) (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.chi)
    (fun c => ((W.ch u a ha B.R.m h1 le_rfl (T.chOf u a B.R.m c)).y ⟨c, rfl⟩).1)
    (fun c s => ((W.ch u a ha B.R.m h1 le_rfl (T.chOf u a B.R.m c)).stabI ⟨c, rfl⟩ s).1) k ∧
      ∀ β (d : XPt (B.primes X) B.R I.sel (I.tup a)) (g' : GA B (B.R.N B.R.m - 1)) (g : GA B (B.R.N B.R.m)), PtOf g' d →
        IsExt (I.rec7 l Z) (z0 X u) (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) g'.1 g.1 →
        PtOf (g * k β) (tilF I.sel (I.tup a) u d)

  killed : ∀ u a ha i h1 hm β, FunKilled (W.ch u a ha i h1 hm β).lev (X.piT u)

def StdLv {W : TwFormsTiedS (I.rec7 l Z) (I.tw l l0 Z) T J F} (Lv : SymmetricTwistedLevelData W) : Prop := ∀ u a ha i h1 hm,
  (∀ v c z (h : z.1 ∈ ((I.stp u a i).rep c).1.1.deco.1.N), (Lv.lv u a ha i h1 hm).pr v c z = Submodule.Quotient.mk ⟨z.1, h⟩) ∧
    ∀ v c z (h : z.1 ∈ ((I.stp u a i).rep c).1.1.deco.1.dnN v), (Lv.lv u a ha i h1 hm).prk v c z = Submodule.Quotient.mk ⟨z.1, h⟩

end Tw

open Classical in

def jStd (u : B.Word) (a : I.ι) (G : (I.per l u a).Mt) : (I.per l u a).Wrow :=
  Classical.epsilon fun z => z ∈ (I.fm l u a).ptC ∧ ∀ w, (I.per l u a).period w G = (I.fm l u a).ipP z w

def ipMt (u : B.Word) (a : I.ι) (G G' : (I.per l u a).Mt) : ℂ := (I.fm l u a).ipP (I.jStd l u a G') (I.jStd l u a G)

def cf : Formalism.L2.Host.CharFrame (I.rec7 l Z) :=
  ⟨I.C.P, I.C.W, I.C.mu0, I.C.eta, I.C.chiPsi, I.C.del, I.C.del', I.C.isMu0, I.C.isEta, I.C.isChi, I.C.isDel, I.C.isDel'⟩

def QpIs (Qp : I.ι → Finset ℕ) : Prop := ∀ a (p : ℕ), p ∈ Qp a ↔ p.Prime ∧ ∃ P ∈ I.Q a, (p : 𝓞 B.fields.E) ∈ P.asIdeal

structure StdO (Qp : I.ι → Finset ℕ) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) : Prop where
  mt : ∀ u a, (O u a).mt = fun j => if 1 ≤ j ∧ j ≤ B.R.m then
    (I.rec7 l Z).muTil j * (show (I.rec7 l Z).Dt →* ℂˣ from tildeQ B.host I.SQ (I.xi a)) else (I.rec7 l Z).muTil j
  lat : ∀ u a i c, ((O u a).lat i c).1 = ((I.stp u a i).rep c).1.1.deco.1.N
  dt : ∀ u a i c, (O u a).dt i c = detPt B.host I.SQ ((I.stp u a i).rep c).1.1
  frm : ∀ u a i y, (O u a).frm i y = y.1
  dgen : ∀ u a, (O u a).dgen = I.J.cD
  S : ∀ u a, (O u a).S = insert (B.T u) ({B.host.g 0, B.host.g 1} ∪ Qp a)
  Th : ∀ u a i c c', (O u a).Th i c c' = I.th u a i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c')

structure StdKer {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)}
    {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop where
  X_eq : t.X = B.fields
  seam : HEq t.seam (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G)
  Pr : HEq t.Pr (B.primes X)
  Ch : HEq t.Ch I.Ch
  sel : HEq t.sel I.sel
  S : t.S = I.S
  word : HEq t.word fun u : B.Word => u
  tup : HEq t.tup I.tup
  cst : HEq t.cst I.cst
  idx : HEq t.idx I.idx
  m2 : t.m2 = B.R.m - 2
  glob : HEq t.glob I.glob
  amb : HEq t.amb (I.J.amb B t.χ)
  δ : t.δ = I.J.δ
  O : I.StdO l Z Y.Qp t.O

example (u : B.Word) (j : Fin (B.R.N B.R.m)) (h : j.1 + 1 ≠ B.R.N B.R.m) : z0 X u j = 0 := if_neg h

example (u : B.Word) (j : Fin (B.R.N B.R.m)) (h : j.1 + 1 = B.R.N B.R.m) :
    z0 X u j = ((X.piT u : 𝓞 B.host.E) : B.host.E) := if_pos h

example (Qp : I.ι → Finset ℕ) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (h : I.StdO l Z Qp O)
    (u : B.Word) (a : I.ι) : (O u a).mt 0 = (I.rec7 l Z).muTil 0 := by
  rw [h.mt u a]
  exact if_neg fun h => absurd h.1 (by omega)

end GlobalTheory.Mem.Col2.TC

end
