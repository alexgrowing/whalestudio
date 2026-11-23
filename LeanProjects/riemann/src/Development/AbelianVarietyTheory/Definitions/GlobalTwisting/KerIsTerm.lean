import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.XiAtPenultimateEqXiCpl1
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BelowFiniteNonempty

noncomputable section

namespace GlobalTheory.LvT.Built

open NumberField IsDedekindDomain Matrix
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
open Formalism.MainNotions.product_first_zeroth_parts (Ow)

section Step

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n}
  {ST : Finset (HeightOneSpectrum (𝓞 E))}

def SameOff (ST : Finset (HeightOneSpectrum (𝓞 E))) (N N' : Submodule (𝓞 E) (Sp E n)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), (∀ P ∈ ST, w ≠ P ∧ w ≠ conjPrime₂ P) → localization₂ w.asIdeal N = localization₂ w.asIdeal N'

structure Split (A : TDat S ST) (T : ℕ) where
  off : ∀ b, Setoid (S.D b)
  off_act : ∀ b (g : S.G b) d d', (off b).r d d' → (off b).r (g • d) (g • d')
  off_lat : ∀ b d d', (off b).r d d' → SameOff ST (A.N b d) (A.N b d')
  ext : ∀ b d d', (off b).r d d' → A.deco b d = A.deco b d' → d = d'
  surj : ∀ b d (e : Deco E n ST ∅), e.Ok → SameOff ST (A.N b d) e.N → ∃ d', (off b).r d d' ∧ A.deco b d' = e
  off_up : ∀ b d P, ∀ x ∈ A.N b d, A.f b d P x = 1 → (off b).r d (A.up b d P x)
  off_dn : ∀ b d P g, ((A.deco b d).dn P g).Ok → (off b).r d (A.dn b d P g)
  off_dia : ∀ b d P a, (off b).r d (A.dia b P a d)
  dia_deco : ∀ b d (P P' : ST) a, P' ≠ P → A.f b (A.dia b P a d) P' = A.f b d P'
  gam_surj : ∀ b (γ : GL (Fin n) E), (γ : Matrix (Fin n) (Fin n) E)ᴴ * (γ : Matrix (Fin n) (Fin n) E) = 1 → ∃ g, S.gam b g = γ
  T_mem : ∀ P ∈ ST, (T : 𝓞 E) ∈ P.asIdeal
  T_nsq : ∀ P ∈ ST, (T : 𝓞 E) ∉ P.asIdeal ^ 2
  nonconj : ∀ P ∈ ST, ∀ Q ∈ ST, Q ≠ conjPrime₂ P

def Above (A : TDat S ST) (b : S.β) (P : ST) (d d₁ : S.D b) : Prop := ∃ x ∈ A.N b d, A.f b d P x = 1 ∧ d₁ = A.up b d P x

end Step

structure Dat (D : D7) (u : D.what₂.Word) : Type 1 where
  E : Type
  [fE : Field E]
  [nE : NumberField E]
  [sE : StarRing E]
  emb : D.what₂.Tau → E →+* D.what₂.LL
  fok : FOk emb D.what₂.embLL
  I : ChainIn E D.what₂.LL D.what₂.Tau D.R
  J : AtIn I
  Q : PerIn I
  Z : FmIn J D.what₂.places
  hI : I.Ok
  hJ : J.Ok
  hQ : Q.Ok
  l : J.Laws emb D.what₂.embLL (D.hcW u)
  lf : FmLaws J Q emb D.what₂.embLL (D.hcW u) D.what₂.places hI hQ
  hT : Q.Over J

attribute [instance] Dat.fE Dat.nE Dat.sE

variable {D : D7} {u : D.what₂.Word} (B : Dat D u)

namespace Dat

def ch : Ch D u := ⟨_, _, _, forms B.J B.Q B.emb D.what₂.embLL (D.hcW u) B.Z B.hI B.hJ B.hQ B.l B.lf B.hT⟩

def pr (v : B.ch.A.vT) : B.J.ST := v

def rs (v : B.ch.A.vT) (a : B.ch.A.Fv v) : Res (B.pr v).1 := a

abbrev lam (_B : Dat D u) (i : ℕ) : D.what₂.Tau → DomWeight (D.R.N i) := GlobalTheory.Mem.Col2.lamT (D.hcW u) i

abbrev V (i : ℕ) : Type := Formalism.L2.DIV.VV D.what₂.LL (B.lam i)

def ev (i : ℕ) (F : B.V i) : Fr B.emb D.what₂.embLL (D.R.N i) → ℂ :=
  evV B.emb (1 : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) B.E) (B.lam i) D.what₂.embLL F

def valAt (w : D.what₂.places.Pl) (i : ℕ) (L : Submodule (𝓞 B.E) (Fin (D.R.N i) → B.E)) : Submodule (𝓞 D.what₂.LL) (B.V i) :=
  localization₂ (D.plEq w).asIdeal (delAtr B.emb (B.lam i) L)

def Sees : Prop :=
  ∀ w, OverT B.ch w → ∀ (P : B.J.ST) (x : B.E),
    B.emb (B.Z.tauOf w P) (if B.Z.seenP w then x else star x) ∈ Ow D w ↔ P.1.valuation B.E x ≤ 1

abbrev Ker (i : ℕ) : Type :=
  ∀ b b', (B.I.S i).D b → (B.I.S (i + 1)).D b' → (B.V i →ₗ[D.what₂.LL] B.V (i + 1))

variable {B} {i : ℕ} (k : B.Ker i)

structure KerEq : Prop where
  equiv : ∀ b b' (g : (B.I.S i).G b) (g' : (B.I.S (i + 1)).G b') d d',
    k b b' (g • d) (g' • d') =
      (B.I.S (i + 1)).rho B.emb (B.lam (i + 1)) b' g' ∘ₗ k b b' d d' ∘ₗ (B.I.S i).rho B.emb (B.lam i) b g⁻¹
  kmap : ∀ c c' F, B.ch.C.Kmap i c c' (B.ev i F) =
    B.ev (i + 1) (k c.1 c'.1 ((B.I.S i).rep c) ((B.I.S (i + 1)).rep c') F)

def KerDil : Prop :=
  ∀ b b' d d' (P : B.J.ST) a, k b b' ((B.J.A i).dia b P a d) ((B.J.A (i + 1)).dia b' P a d') = k b b' d d'

def KerUK : Prop :=
  ∀ b b' d d' (P : B.J.ST) F, (∑ᶠ d₁ ∈ {d₁ | Above (B.J.A (i + 1)) b' P d' d₁}, k b b' d d₁ F) =
    ((B.J.T : D.what₂.LL) ^ ((D.R.t + 1) / 2)) • ∑ᶠ d₀ ∈ {d₀ | Above (B.J.A i) b P d₀ d}, k b b' d₀ d' F

def KerBar : Prop :=
  ∀ w, OverT B.ch w → B.Z.seenP w = false → ∀ b b' d d', ∀ F ∈ B.valAt w i ((B.I.S i).Lsh b d),
    ∃ F' ∈ B.valAt w (i + 1) ((B.I.S (i + 1)).Lsh b' d'),
      k b b' d d' F = ((B.J.T : D.what₂.LL) ^ (D.R.f * ((D.R.t + 1) / 2))) • F'

def KerP : Prop :=
  ∀ w, OverT B.ch w → B.Z.seenP w = true → ∀ b b' d d', ∀ F ∈ B.valAt w i ((B.I.S i).Lsh b d),
    ((B.J.T : D.what₂.LL) ^ (((D.R.f * D.R.N i : ℕ) : ℤ) + ∑ τ, B.ch.C.sDiv i τ)) • k b b' d d' F ∈
      B.valAt w (i + 1) ((B.J.A (i + 1)).deco b' d').L

variable (B)

structure Real (i : ℕ) (sp : Split (B.J.A i) B.J.T) (M : PtModel B.ch i) where
  iK : ∀ P : B.ch.A.vT, B.E ≃+* (M.Lc P).K
  iK_O : ∀ (P : B.ch.A.vT) x, iK P x ∈ (M.Lc P).O ↔ (B.pr P).1.valuation B.E x ≤ 1
  iK_res : ∀ (P : B.ch.A.vT) (r : 𝓞 B.E) (h : iK P (r : B.E) ∈ (M.Lc P).O),
    B.rs P ((M.Lc P).res ⟨_, h⟩) = Ideal.Quotient.mk (B.pr P).1.asIdeal r
  pt : ∀ b, (B.I.S i).D b → M.Pt
  hom : ∀ b, (B.I.S i).G b →* M.G
  zeta : CommGroup.torsion (D.what₂.LL)ˣ →* M.G
  pt_smul : ∀ b g d, pt b (g • d) = hom b g • pt b d
  gen : ∀ b (g : M.G), ∃ ζ g', g = zeta ζ * hom b g'
  comm : ∀ ζ (g : M.G), zeta ζ * g = g * zeta ζ
  surj : ∀ p : M.Pt, ∃ ζ b d, p = zeta ζ • pt b d
  idx : ∀ ζ b b' d d', (zeta ζ • pt b d).1 = (pt b' d').1 → b = b'
  inj : ∀ ζ b d d', zeta ζ • pt b d = pt b d' ↔ ∃ g : (B.I.S i).G b, (B.I.S i).gam b g = 1 ∧ (B.I.S i).chr b g = ζ.1 ∧ g • d = d'
  fst : ∀ ζ b d d', (zeta ζ • pt b d).1 = (pt b d').1 ↔
    ∃ g : (B.I.S i).G b, (B.I.S i).gam b g = 1 ∧ (B.I.S i).chr b g = ζ.1 ∧ (sp.off b).r (g • d) d'
  rep_eq : ∀ c, M.rep c = pt c.1 ((B.I.S i).rep c)
  pt_L : ∀ b d (P : B.ch.A.vT) (x : Fin (D.R.N i) → B.E),
    (fun a => iK P (x a)) ∈ ((pt b d).2 P).1.L ↔ x ∈ localization₂ (B.pr P).1.asIdeal ((B.J.A i).N b d)
  pt_f : ∀ b d (P : B.ch.A.vT) (x : Fin (D.R.N i) → B.E), B.rs P (((pt b d).2 P).1.f (fun a => iK P (x a))) = (B.J.A i).f b d (B.pr P) x
  loc_hom : ∀ b g (P : B.ch.A.vT), M.loc P (hom b g) = Matrix.GeneralLinearGroup.map (iK P).toRingHom ((B.I.S i).gam b g)
  loc_zeta : ∀ ζ (P : B.ch.A.vT), M.loc P (zeta ζ) = 1
  val_eq : M.Val = ValC (Gr B.emb D.what₂.embLL (D.R.N i)) (B.lam i)
  act_hom : ∀ b g (y : M.Val), (M.act (hom b g) y).1 = (B.I.S i).tr B.emb D.what₂.embLL b g y.1
  act_zeta : ∀ ζ (y : M.Val), M.act (zeta ζ) y = D.what₂.embLL ((ζ.1 : (D.what₂.LL)ˣ) : D.what₂.LL) • y

  rat : ∀ g : M.G, ∃ (γ : GL (Fin (D.R.N i)) B.E) (ζ : CommGroup.torsion (D.what₂.LL)ˣ),
      (γ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) B.E)ᴴ * (γ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) B.E) = 1 ∧
      (∀ P : B.ch.A.vT, M.loc P g = Matrix.GeneralLinearGroup.map (iK P).toRingHom γ) ∧
      ∀ y : M.Val, (M.act g y).1 = trFr B.emb D.what₂.embLL γ ζ.1 y.1 := by
    exact fun g => ⟨g.1.1, g.2, g.1.2, fun _ => Units.ext rfl, fun _ => rfl⟩

variable {B}

structure Real.ValIs {sp : Split (B.J.A i) B.J.T} {M : PtModel B.ch i} (R : B.Real i sp M) (Co : M.Coord) : Prop where
  dual : ∀ w, OverT B.ch w → ∀ b d (y : M.Val),
    y ∈ Co.valB w ∅ (R.pt b d) ↔ ∃ F ∈ B.valAt w i ((B.I.S i).Lsh b d), y.1 = B.ev i F
  ker : ∀ w, OverT B.ch w → B.Z.seenP w = true → ∀ b d (y : M.Val),
    y ∈ Co.valB w Finset.univ (R.pt b d) ↔ ∃ F ∈ B.valAt w i ((B.J.A i).deco b d).L, y.1 = B.ev i F

def KerIs {sp : Split (B.J.A i) B.J.T} {sp' : Split (B.J.A (i + 1)) B.J.T} {M : PtModel B.ch i} {M' : PtModel B.ch (i + 1)}
    (R : B.Real i sp M) (R' : B.Real (i + 1) sp' M') (K : KerPt M M') (k : B.Ker i) : Prop :=
  ∀ b b' d d' F (y : M.Val), y.1 = B.ev i F → (K.k (R.pt b d) (R'.pt b' d') y).1 = B.ev (i + 1) (k b b' d d' F)

end Dat

section Conc

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Formalism.L2.Ker.Amb X) (u : Pr.Word) (i : ℕ)

def kAt (b : Idx sel mu L i) (b' : Idx sel mu L (i + 1)) (p : PtAt R sel mu cst u i) (p' : PtAt R sel mu cst u (i + 1)) :
    Formalism.L2.DIV.VV X.K (W.lamTrue u i) →ₗ[X.K] Formalism.L2.DIV.VV X.K (W.lamTrue u (i + 1)) :=
  GlobalTheory.KerT.ker W Ch sel mu cst A u i (i + 1) p.1.1.deco.1.N (frsF sel mu p.1.1) p'.1.1.deco.1.N (frsF sel mu p'.1.1)
    (xiAt Ch sel mu cst L u i b b' p p')

def SameOffPt {j : ℕ} (p q : PtAt R sel mu cst u j) : Prop :=
  SameOff (Pr.vT u) p.1.1.deco.1.N q.1.1.deco.1.N ∧ p.1.1.deco.1.be = q.1.1.deco.1.be ∧ p.1.1.fr = q.1.1.fr ∧ p.1.2 = q.1.2

def KerIsTerm : Prop :=
  ∀ (b : Idx sel mu L i) (b' : Idx sel mu L (i + 1)) (p : PtAt R sel mu cst u i) (p' : PtAt R sel mu cst u (i + 1)),
    ∃ Ξ₀ : HomE X.E (R.N i) (R.N (i + 1)) → X.K,
      GlobalTheory.KerT.InBoxOfRowSelection sel mu cst u p.1.1.deco.1.N p'.1.1.deco.1.N Ξ₀ ∧
      (∀ w : HeightOneSpectrum (𝓞 X.K), ((Pr.T u : ℕ) : 𝓞 X.K) ∈ w.asIdeal → ∀ x, w.valuation X.K (Ξ₀ x) ≤ 1) ∧
      GlobalTheory.KerT.Framed p.1.1.deco.1.N (frsF sel mu p.1.1) ∧ GlobalTheory.KerT.Framed p'.1.1.deco.1.N (frsF sel mu p'.1.1) ∧
      ∀ q q', SameOffPt sel mu cst u p q → SameOffPt sel mu cst u p' q' →
        kAt W Ch sel mu cst L A u i b b' q q' =
          GlobalTheory.KerT.term W Ch sel mu cst A u i (i + 1) q.1.1.deco (frsF sel mu p.1.1) q'.1.1.deco (frsF sel mu p'.1.1) Ξ₀

end Conc

example {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (ST : Finset (HeightOneSpectrum (𝓞 E)))
    (N : Submodule (𝓞 E) (Sp E n)) : SameOff ST N N := fun _ _ => rfl

end GlobalTheory.LvT.Built
