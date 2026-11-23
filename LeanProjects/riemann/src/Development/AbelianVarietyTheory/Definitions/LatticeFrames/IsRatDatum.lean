import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiPinnedWithFinIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

def intVec (D : D7) (n : ℕ) : Set (Fin n → D.host.E) := {x | ∀ k, IsIntegral ℤ (x k)}

def IsFinComb {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f₀ f : WO S T → ℂ) : Prop :=
  ∃ (n : ℕ) (c : Fin n → ℂ) (x : Fin n → WO S T), (∀ k, (x k).map (infPart D) = 0) ∧ f = ∑ k, c k • heisO ψ S T (x k) f₀

abbrev stdHom {D : D7} (S T : HSp D) : AddSubgroup (WO S T) := latO S T (intVec D S.rank) (intVec D T.rank) fun _ => True

def IsRatDatum {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D)
    (Ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ) (f₀ f : WO S T → ℂ) : Prop :=
  ∃ Φ : WO S T → ℂ, IsSBHalf e (stdHom S T) Φ ∧ (∀ γ, Φ (γ.map fun a => e * incA D a) = Ξ γ) ∧
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e (stdHom S T) 1 f₀ Φ f

section Dat
variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)

structure ColDat (Ch : ℕ → Type) where

  ch : ∀ i, Ch i

  chr : ℕ → ((AE (I.rec7 l Z))ˣ →* Circle)

  om : ∀ i, Om ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))

  vac : ∀ i, WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ

  w : ∀ i, WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ

  μ : ∀ i, Measure (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i))
  fd : ∀ i, Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i))

  e : AE (I.rec7 l Z)

  kb : ∀ i, TC.GA B (B.R.N i)
  b0 : ∀ i, Idx I.sel (I.tup I.mu0) (I.idx I.mu0) i
  p0 : ∀ i, PtAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) u i

variable {I l Z u} {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i}

namespace ColDat
variable (A : ColDat I l Z u Ch) (F : FormsTiedSym (I.rec7 l Z) u Ch chOf)
  (ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ) (θ : InfFam (I.rec7 l Z))

def xi (i : ℕ) (hi : i + 1 ≤ B.R.m)
    (γ : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) : ℂ :=
  B.embLL (xiAt I.Ch I.sel (I.tup I.mu0) (I.cst I.mu0) (I.idx I.mu0) u i (A.b0 i) (A.b0 (i + 1)) (A.p0 i) (A.p0 (i + 1))
    (Matrix.toLin' (γ.reindex (finCongr (rankN (I.rec7 l Z) (i + 1) hi)) (finCongr (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi))))))

abbrev Q (i : ℕ) (hi : i ≤ B.R.m) : Chart (I.rec7 l Z) u i hi := chart F i hi (A.ch i)

structure Is : Prop where
  std : IsStdChar (I.rec7 l Z) ψ (-1)
  inf : IsInfFam θ
  chr : ∀ j : Fin B.R.m, ChrEq (A.chr ((j : ℕ) + 1)) (I.C.mu0 j)
  om : ∀ i, i < B.R.m → IsWeilDatumO ψ _ _ (A.chr (i + 1)) (A.chr (i + 1)) (A.om i)
  vac : ∀ i, i < B.R.m → IsVacO ψ θ _ _ (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) (A.vac i)
  idem : IsIdemSum A.e (Formalism.L2.Col.Sall (Pr := B.primes X) I.sel (I.tup I.mu0) u)
  datum : ∀ i (hi : i + 1 ≤ B.R.m), IsRatDatum ψ _ _ A.e (A.xi i hi) (A.vac i) (A.w i)
  comb : ∀ i, i < B.R.m → IsFinComb ψ _ _ (A.vac i) (A.w i)
  haar : ∀ i, i ≤ B.R.m → (A.μ i).IsHaarMeasure ∧ IsFundamentalDomain (GQ ((I.rec7 l Z).sp.X i)) (A.fd i) (A.μ i)

  base : ∀ i, i ≤ B.R.m → TC.PtOf (A.kb i) (A.p0 i).1.1 ∧ (A.p0 i).1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i)

  chart_ne : ∀ i hi, Nonempty (A.Q F i hi).cl
  rep : ∀ i hi (c : (A.Q F i hi).cl),
    TC.PtOf ((show TC.GA B (B.R.N i) from ((A.Q F i hi).K.y c).1) * A.kb i) ((I.stp u I.mu0 i).rep ((A.Q F i hi).inc c)).1.1 ∧
      (show (I.stp u I.mu0 i).Cl from (A.Q F i hi).inc c).1 = A.b0 i ∧
      cosetIn ((I.stp u I.mu0 i).rep ((A.Q F i hi).inc c)) = cosetIn (A.p0 i)

def IsForm (i : ℕ) (hi : i ≤ B.R.m) (φ : ((I.rec7 l Z).mem u).C.cls i → ((I.rec7 l Z).mem u).C.Y i → ℂ) : Prop :=
  φ ∈ ((I.rec7 l Z).fm u).Fi i ∧ OnChart F i hi (A.ch i) φ

def Keeps : Prop :=
  ∀ i (hi : i + 1 ≤ B.R.m) φ, A.IsForm F i (Nat.le_of_succ_le hi) φ → A.IsForm F (i + 1) hi (((I.rec7 l Z).mem u).C.K i φ)

abbrev rd (i : ℕ) (hi : i ≤ B.R.m) := (A.Q F i hi).rd θ

def pt (i : ℕ) := pureTensorO ψ θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (A.w i)

def KJstep : Prop :=
  ∀ i (hi : i + 1 ≤ B.R.m) (y : ((I.rec7 l Z).mem u).C.Y i) P, ∃ a : ((I.rec7 l Z).mem u).C.Y (i + 1) →₀ ℂ,
    ∀ φ, A.IsForm F i (Nat.le_of_succ_le hi) φ →
      liftT (A.om i) (A.μ i) (A.fd i) (A.rd F θ i (Nat.le_of_succ_le hi) φ y) (A.pt ψ θ i P) =
        a.sum fun y' s => s • A.rd F θ (i + 1) hi (((I.rec7 l Z).mem u).C.K i φ) y'

def KJback : Prop :=
  ∀ i (hi : i + 1 ≤ B.R.m) (y' : ((I.rec7 l Z).mem u).C.Y (i + 1)), ∃ (n : ℕ) (y : Fin n → ((I.rec7 l Z).mem u).C.Y i) (P : Fin n → _),
    ∀ φ, A.IsForm F i (Nat.le_of_succ_le hi) φ →
      A.rd F θ (i + 1) hi (((I.rec7 l Z).mem u).C.K i φ) y' =
        ∑ k, liftT (A.om i) (A.μ i) (A.fd i) (A.rd F θ i (Nat.le_of_succ_le hi) φ (y k)) (A.pt ψ θ i (P k))

def KJCoreAt : Prop :=
  ∀ i (hi : i + 1 ≤ B.R.m), ∃ c₀ s : ℂ, c₀ ≠ 0 ∧ s ≠ 0 ∧
    ∀ (c : (A.Q F i (Nat.le_of_succ_le hi)).cl) (c' : (A.Q F (i + 1) hi).cl) g g', g ∈ GfC _ → g' ∈ GfC _ →
      finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) g = ((A.Q F i (Nat.le_of_succ_le hi)).K.y c).1.1 →
      finM _ (rankN (I.rec7 l Z) (i + 1) hi) g' = ((A.Q F (i + 1) hi).K.y c').1.1 → ∀ P,
      thetaKO (A.om i) g g' (A.pt ψ θ i P) =
        c₀ * (I.chIn u I.mu0).rho i ((A.Q F i (Nat.le_of_succ_le hi)).inc c) * (I.chIn u I.mu0).rho' i ((A.Q F (i + 1) hi).inc c') *
          ∑ k ∈ P.support, P.coeff k * Formalism.L2.Ker.jetC (fun _ => s)
            (I.th u I.mu0 i _ _ ((I.stp u I.mu0 i).rep ((A.Q F i (Nat.le_of_succ_le hi)).inc c))
              ((I.stp u I.mu0 (i + 1)).rep ((A.Q F (i + 1) hi).inc c')))
            (k.mapDomain fun v => (v.1, Fin.cast (rankN (I.rec7 l Z) (i + 1) hi) v.2.1,
              Fin.cast (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) v.2.2))

end ColDat
end Dat

def RamAt {D : D7} (u : D.what₂.Word) (i : ℕ) (φ : (D.mem u).C.cls i → (D.mem u).C.Y i → ℂ) : Prop :=
  ∀ v c, ∑ a : ((D.mem u).A.Fv v)ˣ, (D.fm u).dilT i v a c (φ ((D.fm u).dil i v a c)) = 0

def IsEmbTop {D : D7} (z0 : Fin (D.R.N D.R.m) → D.host.E) (emb : GA D D.sp.X' →* GA D (D.sp.X D.R.m)) : Prop :=
  ∀ h, IsExt D z0 (incA D) ((mt _ h).reindex (finCongr (rankP D)) (finCongr (rankP D)))
    ((mt _ (emb h)).reindex (finCongr (rankN D _ le_rfl)) (finCongr (rankN D _ le_rfl)))

def PerLast {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (F : FormsTiedSym D u Ch chOf)
    (W : Tower D) (L : Link D u W) : Prop :=
  ∀ emb, IsEmbTop F.til.z0 emb → ∀ (y : (D.mem u).C.Y D.R.m) (v : SmT W.MX), ∃ a : ℂ,
    ∀ φ ∈ (D.fm u).Fi D.R.m, ∀ G : (D.mem u).P.Mt,
      ∫ h in W.fdX, (L.eT G).1 v h * (endChart F D.R.m le_rfl (Or.inr rfl)).rd W.θ φ y (emb h) ∂W.νX =
        a * (D.mem u).P.Ptil φ G

def TopForm {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (F : FormsTiedSym D u Ch chOf)
    {par} (M : Formalism.IndefR.Mult.DSModel D.sp.X' par) (eT : (D.mem u).P.Mt → SmT M → GA D D.sp.X' → ℂ) : Prop :=
  ∃ J : SmT M →ₗ[ℂ] (FrP D → ℂ), Function.Injective J ∧ (∀ v, J v ∈ ValC (gramC (gramP D) (embT D)) (sgT u)) ∧
    (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D D.sp.X' τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) →
      ∀ y y' : FrP D, IsTr (Function.update (fun _ => 1) τ (g.reindex (finCongr (rankP D)) (finCongr (rankP D)))) y' y →
        J (PiTensorProduct.tprod ℂ (Function.update v τ w)) y = J (PiTensorProduct.tprod ℂ v) y') ∧
    ∀ (G : (D.mem u).P.Mt) (c : (D.fm u).clsP) (v : SmT M) (h : GA D D.sp.X'), h ∈ GfC D.sp.X' →
      finM _ (rankP D) h = (F.clsP.y c).1.1 →
      eT G v h = (Nat.card ((D.fm u).stabilizer₂ c) : ℂ) * (D.mem u).P.period (F.valP.eW.symm (Pi.single c (J v))) G

structure PinColAt {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word}
    {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (d : GlobalTheory.SeeSaw.Dat (I.rec7 l Z) u)
    (F : FormsTiedSym (I.rec7 l Z) u Ch chOf) (A : ColDat I l Z u Ch) : Prop where
  is : A.Is F d.c.ψ d.c.θ
  keeps : A.Keeps F
  rd : ∀ j (hj : j ≤ B.R.m), d.rd j = A.rd F d.c.θ j hj
  ram : ∀ j (hj : j ≤ B.R.m) φ, φ ∈ d.Ram j ↔ A.IsForm F j hj φ ∧ RamAt (D := I.rec7 l Z) u j φ
  om : ∀ j, j < B.R.m → (d.k j).om = A.om j
  vac : ∀ j, j < B.R.m → (d.k j).vac = A.vac j
  w : ∀ j, j < B.R.m → GlobalTheory.SeeSaw.comb d.c.ψ _ _ (d.k j).c (d.k j).vac = A.w j
  x : ∀ j, j ≤ B.R.m → (d.x j).s = (fun _ => 1) ∧ (d.x j).B = (fun _ => 1) ∧ (∀ z, z ∈ (d.x j).L ↔ z ∈ intVec (I.rec7 l Z) _) ∧
    (d.x j).vol.μ = A.μ j ∧ (d.x j).vol.𝓕 = A.fd j
  emb : IsEmbTop F.til.z0 ((d.oT B.R.m rfl).emb.comp (MonoidHom.inl _ _))
  top : TopForm F d.top.M fun G v => (d.eT G).1 v
  onto : d.TopOnto

def PinCol {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} (w : World I l Z) {u : B.Word}
    (d : GlobalTheory.SeeSaw.Dat (I.rec7 l Z) u) : Prop :=
  ∃ A : ColDat I l Z u (w.C.herm.base.Ch u), PinColAt d (w.C.forms u) A

def KJCore : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (w : World I l Z) (u : B.Word)
    (A : ColDat I l Z u (w.C.herm.base.Ch u)) ψ θ, A.Is (w.C.forms u) ψ θ → A.KJCoreAt (w.C.forms u) ψ θ

def KJ : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (w : World I l Z) (u : B.Word)
    (A : ColDat I l Z u (w.C.herm.base.Ch u)) ψ θ, A.Is (w.C.forms u) ψ θ → A.KJstep (w.C.forms u) ψ θ

def ColDatEx : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (w : World I l Z), I.IsTw → ∀ (u : B.Word) ψ θ,
    IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ →
    ∃ A : ColDat I l Z u (w.C.herm.base.Ch u), A.Is (w.C.forms u) ψ θ ∧ A.Keeps (w.C.forms u)

def PerAll : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (w : World I l Z) (u : B.Word)
    (W : Tower (I.rec7 l Z)) (L : Link (I.rec7 l Z) u W), W.Is → L.TopPin (w.C.forms u) → PerLast (w.C.forms u) W L

end GlobalTheory.AdForm
