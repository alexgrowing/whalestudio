import Mathlib
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalRingCardinality.DataAmbForm
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalToGlobal.KernelLattices.ThDistC

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.WeightedChainData

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

def cpy (E : Type) [Field E] (a b : ℕ) : Sp E a →ₗ[E] Sp E b :=
  LinearMap.pi fun l : Fin b => atNL E a l.1

theorem cpy_self (E : Type) [Field E] (a : ℕ) (x : Sp E a) : cpy E a a x = x := by
  funext l
  simp [cpy, atNL, l.2]

section Frames

variable (D : D7) {N : ℕ} {Y : Type} (frm : Y → D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ)

def HasWt (lam : D.what₂.Tau → Fin N → ℤ) (f : Y → ℂ) : Prop :=
  (∃ (Q : MvPolynomial (GL3Theta.FrV D N) ℂ) (n : ℕ), ∀ y,
    f y = GL3Theta.evFr D Q (frm y) * ((∏ τ, (frm y τ).det) ^ n)⁻¹) ∧
  ∀ (y y' : Y) (b : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ), (∀ τ, (b τ).BlockTriangular id) →
    (∀ τ, frm y' τ = frm y τ * b τ) → f y' = (∏ τ, ∏ k, b τ k k ^ lam τ k) * f y

theorem hasWt_zero (lam : D.what₂.Tau → Fin N → ℤ) : HasWt D frm lam 0 :=
  ⟨⟨0, 0, fun y => by simp [GL3Theta.evFr]⟩, fun _ _ _ _ _ => by simp⟩

def FixedBy (k : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ) (a : ℂ) (f : Y → ℂ) : Prop :=
  ∀ y y' : Y, (∀ τ, frm y τ = k τ * frm y' τ) → f y = a * f y'

end Frames

structure ChainData (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) where
  X : Fields
  s : Seam D X
  Pr : Primes X

  w : Pr.Word
  Ch : Chars X Pr D.R.m

  sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)
  S : Set ℕ

  xi : Tup X.F X.E X.K S
  cst : LocCst X (rowSG Pr sel xi)
  L : ChIdx X Pr D.R (QE sel (xi : Chr X.F X.E X.K))
  G : ChGlob X D.R.m
  δ : ℂ
  B : Base D D.host.ccK δ
  idl : D.Dt ⧸ D.UO → TaylorLogMetric.IdE D
  O : GL3Theta.LiftObj D (D.chTw u μ)

  lamTop : rowSG Pr sel xi → Submodule (𝓞 X.E) (Sp X.E (D.R.N D.R.m - 1 + 0))

  depth : rowSG Pr sel xi → ℕ

  rep : ∀ i, (D.chTw u μ).cls i →
    Option (L.β i) × DecoF X.E (D.R.N i) (Pr.vT w) ∅ (rowSG Pr sel xi) × Set (Sp X.E (D.R.N i))

namespace ChainData

variable {D : D7} {u : D.what₂.Word} {μ : D.what₂.Tup} (T : ChainData D u μ)

abbrev SB : Finset (HeightOneSpectrum (𝓞 T.X.E)) := rowSG T.Pr T.sel T.xi

abbrev Pt (i : ℕ) : Type := DecoF T.X.E (D.R.N i) (T.Pr.vT T.w) ∅ T.SB

abbrev Lab (i : ℕ) : Type := Option (T.L.β i) × T.Pt i × Set (Sp T.X.E (D.R.N i))

abbrev AutX (i : ℕ) : Type := Sp T.X.E (D.R.N i) ≃ₗ[T.X.E] Sp T.X.E (D.R.N i)

abbrev XP : Type := Sp T.X.E (D.R.N D.R.m - 1 + 0)

def hOf (i : ℕ) (b : Option (T.L.β i)) (P : T.SB) : AutY T.X D.R i :=
  b.elim 1 fun a => T.L.h i a P

open Classical in

def Jtop (P : T.SB) : Subgroup (T.XP ≃ₗ[T.X.E] T.XP) :=
  if P.1 ∈ T.Pr.vGs then
    (if T.cst.sharp then LocE.JGsym P.1 (qOf P.1) D.R.k D.R.rS D.R.r D.R.t (D.R.N D.R.m - 1) 0
      else LocE.JG P.1 (qOf P.1) D.R.k D.R.r D.R.t (D.R.N D.R.m - 1) 0)
  else LocE.JQ P.1 (qOf P.1) D.R.r (D.R.N D.R.m - 1) 0

open Classical in

def lamM (P : T.SB) (h : T.XP ≃ₗ[T.X.E] T.XP) : T.X.K :=
  if P.1 ∈ T.Pr.vGs then
    (if T.cst.sharp then
        LocE.lamGBS (qOf P.1) (psi0P T.Ch P.1) (chiP T.Ch P.1) D.R.k D.R.r D.R.t D.R.m (D.R.N D.R.m - 1) 0 h.toLinearMap
      else LocE.lamGB (qOf P.1) (psi0P T.Ch P.1) (chiP T.Ch P.1) D.R.k D.R.r D.R.t D.R.m (D.R.N D.R.m - 1) 0 h.toLinearMap)
  else LocE.lamQB (resChar (T.xi : Chr T.X.F T.X.E T.X.K) P.1) D.R.r (D.R.N D.R.m - 1) h.toLinearMap

open Classical in

def InTopLat (i : ℕ) (P : T.SB) (y : Sp T.X.E (D.R.N i)) : Prop :=
  cpy T.X.E _ _ y ∈ (if P.1 ∈ T.Pr.vGs then stdAt T.X.E (D.R.N D.R.m - 1 + 0) P.1 else T.lamTop P) ∧
    IntAt P.1 (atNL T.X.E (D.R.N i) (D.R.N D.R.m - 1) y)

open Classical in

def InTopCong (i : ℕ) (P : T.SB) (k : T.AutX i) : Prop :=
  (∀ y, T.InTopLat i P (k y) ↔ T.InTopLat i P y) ∧
    ∀ y, T.InTopLat i P y →
      T.InTopLat i P ((((qOf P.1 : ℕ) : T.X.E) ^ (if P.1 ∈ T.Pr.vGs then 1 else T.depth P))⁻¹ • (k y - y))

def InLev (i : ℕ) (b : Option (T.L.β i)) (κ : T.SB → T.AutX i) (a : ℂ) : Prop :=
  match b with
  | some al => ∃ r : T.SB → AutY T.X D.R i,
      (∀ P, r P ∈ Loc.Cbe (Jat (Pr := T.Pr) T.cst.sharp i P.1) (T.L.h i al P) ∧
        ∀ x, r P (Loc.inX T.X.E (D.R.N i) (cOf D.R i) x) = Loc.inX T.X.E (D.R.N i) (cOf D.R i) (κ P x)) ∧
      a = (T.s.σ₀ (∏ P, chiInv T.Ch T.sel T.xi T.cst i P (T.L.h i al P) (r P)))⁻¹
  | none => ∃ (j : T.SB → (T.XP ≃ₗ[T.X.E] T.XP)) (jx k : T.SB → T.AutX i),
      (∀ P, j P ∈ T.Jtop P ∧ (∀ x, jx P (cpy T.X.E _ _ x) = cpy T.X.E _ _ (j P x)) ∧
        jx P (Loc.eN T.X.E (D.R.N i) (D.R.N D.R.m - 1)) = Loc.eN T.X.E (D.R.N i) (D.R.N D.R.m - 1) ∧
        T.InTopCong i P (k P) ∧ κ P = jx P * k P) ∧
      a = (T.s.σ₀ (∏ P, T.lamM P (j P)))⁻¹

def Moves (i : ℕ) (x x' : T.Lab i) (γ : UF T.X.E (D.R.N i)) (a : ℂ) : Prop :=
  x'.1 = x.1 ∧ x'.2.1.deco = (γ, (1 : GLG T.X.E (D.R.N i) ∅)) • x.2.1.deco ∧ x'.2.2 = (fun v => γ.1 v) '' x.2.2 ∧
    ∃ κ : T.SB → T.AutX i, T.InLev i x.1 κ a ∧ ∀ P, x'.2.1.fr P = γ.1 * x.2.1.fr P * κ P

def Admissible (i : ℕ) (x : T.Lab i) : Prop :=
  (i < D.R.m → x.1.isSome = true) ∧ (i = D.R.m → x.1 = none) ∧ (i + 1 ≠ D.R.m → x.2.2 = Set.univ) ∧
  (i + 1 = D.R.m → x.2.2 ∈ ybSet T.sel T.xi T.cst x.2.1.deco.1.N ∧
    ∀ P : T.SB, ∃ (al : T.L.β (D.R.m - 2)) (x₀ : HomE T.X.E (D.R.N (D.R.m - 2)) (D.R.N (D.R.m - 2 + 1))),
      PsiAt T.Ch T.sel T.xi T.cst (D.R.m - 2) P (T.L.h (D.R.m - 2) al P) x₀
        (cpy T.X.E _ _ ((x.2.1.fr P).symm (repY x.2.2))) ≠ 0)

def matAt (i : ℕ) (γ : UF T.X.E (D.R.N i)) (τ : D.what₂.Tau) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ :=
  Matrix.of fun a b => TaylorLogMetric.embT D τ (T.s.iE (γ.1 (Pi.single b 1) a))

def locDatum (i : ℕ) (p : T.Lab i) (p' : T.Lab (i + 1)) (x : HomE T.X.E (D.R.N i) (D.R.N (i + 1))) (P : T.SB) : T.X.K :=
  if i + 2 < D.R.m then
    XiAt T.Ch T.sel T.xi T.cst i P (T.hOf i p.1 P) (T.hOf (i + 1) p'.1 P) (inFr (p.2.1.fr P) (p'.2.1.fr P) x)
  else if i + 2 = D.R.m then
    PsiAt T.Ch T.sel T.xi T.cst i P (T.hOf i p.1 P) (inFr (p.2.1.fr P) (p'.2.1.fr P) x)
      ((p'.2.1.fr P).symm (repY p'.2.2))
  else
    PhiTop T.Ch T.xi T.cst.sharp (D.R.m - 2) P.1
        (cpy T.X.E _ _ ∘ₗ inFr (p.2.1.fr P) (p'.2.1.fr P) x ∘ₗ cpy T.X.E _ _) *
      ftY T.sel T.xi T.cst P
        (((((T.Pr.piT T.w : 𝓞 T.X.E) : T.X.E))⁻¹ • atNL T.X.E (D.R.N (i + 1)) (D.R.N D.R.m - 1)) ∘ₗ
          inFr (p.2.1.fr P) (p'.2.1.fr P) x)
        ((p.2.1.fr P).symm (repY p.2.2))

def datum (i : ℕ) (p : T.Lab i) (p' : T.Lab (i + 1)) (x : HomE T.X.E (D.R.N i) (D.R.N (i + 1))) : T.X.K :=
  phiT T.X.K p.2.1.deco.1 p'.2.1.deco.1 x * ∏ P : T.SB, T.locDatum i p p' x P

def amb : Amb T.X := ambOf T.s T.B (TaylorLogMetric.chiRec D T.idl) T.O.dgen

def theta (i : ℕ) (p : T.Lab i) (p' : T.Lab (i + 1)) : TaylorLogMetric.VC D (D.R.N i) (D.R.N (i + 1)) → ℂ := fun z =>
  thC (T.X.embC T.amb.σ₀) T.amb.δ T.amb.d T.amb.sc T.amb.AA (Sall T.sel T.xi T.w) p.2.1.deco.1.N p'.2.1.deco.1.N
    (levC T.sel T.xi T.cst T.w) (fun x => T.s.σ₀ (T.datum i p p' x))
    (T.amb.e (D.R.N i) (D.R.N (i + 1)) p.2.1.deco.1.N p'.2.1.deco.1.N) fun τ => z (T.s.iT τ)

def muInv (i n : ℕ) (p : T.Pt n) : ℂ :=
  T.s.σ₀ (muInvDet T.sel T.SB (mUof T.Ch T.xi i) (muAt T.Ch T.sel T.xi T.cst i) p.deco.1.N p.fr)

def FieldTie : Prop :=
  T.X.Ok ∧ T.s.Ok ∧ T.Pr.Ok ∧ (∀ k, T.Pr.g k = D.host.g k) ∧ T.Pr.T T.w = (D.mem u).A.T ∧ IsSel T.X T.sel ∧
    hostS D.host.q D.host.d (D.host.g 0) (D.host.g 1) ({(D.mem u).A.T} ∪ (D.host.small : Set ℕ)) ⊆ T.S ∧
    ∀ p : ℕ, p.Prime → p ∣ Ideal.absNorm D.host.ccK → p ∈ T.S

def CharTie : Prop :=
  T.Ch.Ok ∧ T.G.σ₀ = T.s.σ₀ ∧ T.s.iE T.G.xi0 = D.host.xi0 ∧
    (∀ j, Formalism.L2.Col.IsMu0 T.Ch T.s.σ₀ (fun τ => (D.hcW u (T.s.iT τ)).e j) j (T.G.mu0 j)) ∧
    (∀ (j : Fin D.R.m) (v : HeightOneSpectrum (𝓞 T.X.E)), (∀ k, ((T.Pr.g k : ℕ) : 𝓞 T.X.E) ∉ v.asIdeal) →
      T.s.σ₀ (T.Ch.muVal j v : T.X.K) = (((T.G.mu0 j).val v : ℂˣ) : ℂ)) ∧
    T.L.Ok T.Ch T.sel T.xi T.cst T.G (D.R.m - 2)

def TwistTie (Dx : DivX D) : Prop :=
  (∀ p : ℕ, p ∈ Dx.Qp μ ↔ p ∈ QprimeN (T.xi : Chr T.X.F T.X.E T.X.K)) ∧ (μ = D.what₂.mu0 → T.xi = 1) ∧
    (μ = D.what₂.muStar → IsBaseChar D.host.pde (T.xi : Chr T.X.F T.X.E T.X.K)) ∧
    (μ = D.what₂.muStar' → IsBaseChar D.host.pde' (T.xi : Chr T.X.F T.X.E T.X.K))

def CurveTie : Prop := TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK T.δ ∧ TaylorLogMetric.RelDetPinned D T.idl

def TopTie : Prop :=
  ∀ P : T.SB, P.1 ∉ T.Pr.vGs →
    localization₂ P.1.asIdeal (T.lamTop P) = T.lamTop P ∧ (∀ j ∈ T.Jtop P, ∀ x ∈ T.lamTop P, j x ∈ T.lamTop P) ∧
    (∀ x ∈ stdAt T.X.E (D.R.N D.R.m - 1 + 0) P.1, (((qOf P.1 : ℕ) : T.X.E) ^ D.R.m) • x ∈ T.lamTop P) ∧
    (∀ x ∈ T.lamTop P, (((qOf P.1 : ℕ) : T.X.E) ^ D.R.m) • x ∈ stdAt T.X.E (D.R.N D.R.m - 1 + 0) P.1) ∧
    4 * D.R.m + 1 ≤ T.depth P ∧ 2 * D.R.m + 2 * T.cst.M ≤ T.depth P

def ClassTie : Prop :=
  ∀ i ≤ D.R.m, (∀ c, T.Admissible i (T.rep i c)) ∧
    (∀ x, T.Admissible i x → ∃! c, ∃ γ a, T.Moves i (T.rep i c) x γ a) ∧
    (∀ c, Nat.card ((D.chTw u μ).stab i c) =
      Nat.card {γ : UF T.X.E (D.R.N i) // ∃ a, T.Moves i (T.rep i c) (T.rep i c) γ a}) ∧
    ∀ c, (T.O.lat i c).1 = T.s.lat (T.rep i c).2.1.deco.1.N

def MuTie : Prop :=
  ∀ i < D.R.m,
    (∀ c, (((T.O.mt (i + 1) (T.O.dt i c))⁻¹ : ℂˣ) : ℂ) = T.muInv i i (T.rep i c).2.1) ∧
    ∀ c, (((T.O.mt (i + 1) (T.O.dt (i + 1) c))⁻¹ : ℂˣ) : ℂ) = T.muInv i (i + 1) (T.rep (i + 1) c).2.1

def ThetaTie : Prop :=
  ∀ i < D.R.m, ∀ c c', T.O.Th i c c' = T.theta i (T.rep i c) (T.rep (i + 1) c')

def UnfTie : Prop :=
  ∀ i < D.R.m, ∀ c c' (Q : MvPolynomial (GL3Theta.FrV D (D.R.N i)) ℂ) (y' : (D.chTw u μ).Y (i + 1)),
    (D.chTw u μ).unf i c c' (fun y => GL3Theta.evFr D Q (T.O.frm i y)) y' =
      GL3Theta.applyAt0 D (GL3Theta.polD D T.O.dgen Q (T.O.frm (i + 1) y')) (T.O.Th i c c')

theorem unfTie_of_liftTie (Tr : TaylorLogMetric.Tor D) (e : TaylorLogMetric.FamE D) (h : ∀ i < D.R.m, GL3Theta.liftTie D Tr e T.O i) : T.UnfTie :=
  fun i hi => (h i hi).2

def wtTrue (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (τ : D.what₂.Tau) (k : Fin (D.R.N i)) : ℤ :=
  ((Tw.fm u μ).lam i τ).w k - (i : ℤ) * (((D.R.t + 1) / 2 : ℕ) : ℤ)

def FormTie (Tw : TwForms D) : Prop :=
  ∀ i ≤ D.R.m, ∀ φ : (D.chTw u μ).cls i → (D.chTw u μ).Y i → ℂ, φ ∈ (Tw.fm u μ).Fi i ↔
    ∀ c, HasWt D (T.O.frm i) (wtTrue Tw u μ i) (φ c) ∧
      ∀ γ a, T.Moves i (T.rep i c) (T.rep i c) γ a → FixedBy D (T.O.frm i) (T.matAt i γ) a (φ c)

def Tied (Dx : DivX D) (Tw : TwForms D) : Prop :=
  T.FieldTie ∧ T.CharTie ∧ T.TwistTie Dx ∧ T.CurveTie ∧ T.TopTie ∧ T.ClassTie ∧ T.MuTie ∧ T.ThetaTie ∧ T.UnfTie ∧
    T.FormTie Tw

end ChainData

def CarriesForms (D : D7) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) : Prop :=
  ∀ i < D.R.m, ∀ φ ∈ (Tw.fm u μ).Fi i, (D.chTw u μ).K i φ ∈ (Tw.fm u μ).Fi (i + 1)

def KCarriesForms_at (D : D7) (Dx : DivX D) (Tw : TwForms D) (_E : KerEnt D Dx Tw)
    (T : ∀ (u : D.what₂.Word) (μ : D.what₂.Tup), DV.Used D μ → ChainData D u μ) : Prop :=
  GL3Theta.InducedCMType D → GL3Theta.HostFieldConditions D →
    ∀ u μ (hμ : DV.Used D μ), (T u μ hμ).Tied Dx Tw → CarriesForms D Tw u μ

end GlobalTheory.IndefiniteRowSideFullHecke.WeightedChainData
