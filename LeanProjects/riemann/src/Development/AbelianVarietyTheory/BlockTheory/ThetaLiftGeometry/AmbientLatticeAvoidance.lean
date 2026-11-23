import Mathlib
import Formalism.LocalRingCardinality.DataKerI
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalToGlobal.KernelLattices.ThDistC

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AmbientLatticeAvoidance

def reix (E : Type) [Field E] (n n' : ℕ) : Sp E n →ₗ[E] Sp E n' := LinearMap.pi fun l : Fin n' => atNL E n l.1

section Concrete

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

abbrev rkTop (R : Ranks) : ℕ := (R.N R.m - 1) + 0

open Classical in

def JTop (Pr : Primes X) (R : Ranks) (sharp : Bool) (P : HeightOneSpectrum (𝓞 X.E)) :
    Subgroup (Sp X.E (rkTop R) ≃ₗ[X.E] Sp X.E (rkTop R)) :=
  if P ∈ Pr.vGs then
    (if sharp then LocE.JGsym P (qOf P) R.k R.rS R.r R.t (R.N R.m - 1) 0 else LocE.JG P (qOf P) R.k R.r R.t (R.N R.m - 1) 0)
  else LocE.JQ P (qOf P) R.r (R.N R.m - 1) 0

open Classical in

def lamTop (sharp : Bool) (P : HeightOneSpectrum (𝓞 X.E)) (h : HomE X.E (rkTop R) (rkTop R)) : X.K :=
  if P ∈ Pr.vGs then
    (if sharp then LocE.lamGBS (qOf P) (psi0P Ch P) (chiP Ch P) R.k R.r R.t R.m (R.N R.m - 1) 0 h
      else LocE.lamGB (qOf P) (psi0P Ch P) (chiP Ch P) R.k R.r R.t R.m (R.N R.m - 1) 0 h)
  else LocE.lamQB (resChar (mu : Chr X.F X.E X.K) P) R.r (R.N R.m - 1) h

open Classical in

def latTop (Pr : Primes X) (R : Ranks) (n : ℕ) (π : X.E)
    (abelian₂ : HeightOneSpectrum (𝓞 X.E) → Submodule (𝓞 X.E) (Sp X.E (rkTop R))) (P : HeightOneSpectrum (𝓞 X.E)) :
    Set (Sp X.E n) :=
  if P ∈ Pr.vGs then (stdAt X.E n P : Set (Sp X.E n))
  else {x | reix X.E n (rkTop R) x ∈ abelian₂ P ∧ IntAt P (π⁻¹ * atNL X.E n (R.N R.m - 1) x)}

open Classical in

def TopLev (n : ℕ) (π : X.E) (abelian₂ : HeightOneSpectrum (𝓞 X.E) → Submodule (𝓞 X.E) (Sp X.E (rkTop R)))
    (dep : HeightOneSpectrum (𝓞 X.E) → ℕ) (sharp : Bool) (P : HeightOneSpectrum (𝓞 X.E))
    (κ : Sp X.E n ≃ₗ[X.E] Sp X.E n) (z : X.K) : Prop :=
  ∃ j ∈ JTop Pr R sharp P, ∃ jx k : Sp X.E n ≃ₗ[X.E] Sp X.E n,
    (∀ x, reix X.E n (rkTop R) (jx x) = j (reix X.E n (rkTop R) x)) ∧
    (∀ x, atNL X.E n (R.N R.m - 1) (jx x) = atNL X.E n (R.N R.m - 1) x) ∧
    (∀ x, k x ∈ latTop Pr R n π abelian₂ P ↔ x ∈ latTop Pr R n π abelian₂ P) ∧
    (∀ x ∈ latTop Pr R n π abelian₂ P,
      ((qOf P : X.E) ^ (if P ∈ Pr.vGs then 1 else dep P))⁻¹ • (k x - x) ∈ latTop Pr R n π abelian₂ P) ∧
    κ = jx * k ∧ z = lamTop Ch mu sharp P j.toLinearMap

def TopOk (abelian₂ : HeightOneSpectrum (𝓞 X.E) → Submodule (𝓞 X.E) (Sp X.E (rkTop R)))
    (dep : HeightOneSpectrum (𝓞 X.E) → ℕ) : Prop :=
  ∀ P ∈ QE sel (mu : Chr X.F X.E X.K),
    localization₂ P.asIdeal (abelian₂ P) = abelian₂ P ∧
    JTop Pr R cst.sharp P ≤ stabL X.E (rkTop R) (abelian₂ P) ∧
    (∀ x ∈ stdAt X.E (rkTop R) P, ((qOf P : X.E) ^ R.m) • x ∈ abelian₂ P) ∧
    (∀ x ∈ abelian₂ P, ((qOf P : X.E) ^ R.m) • x ∈ stdAt X.E (rkTop R) P) ∧
    4 * R.m + 1 ≤ dep P ∧ 2 * R.m + 2 * cst.M ≤ dep P

abbrev Pt (u : Pr.Word) (i : ℕ) : Type := ChPt (R := R) sel mu u i × Option (L.β i) × Set (Sp X.E (R.N i))

def YbOk {u : Pr.Word} {i : ℕ} (p : ChPt (R := R) sel mu u i) (Y : Set (Sp X.E (R.N i))) : Prop :=
  Y ∈ ybSet sel mu cst p.deco.1.N ∧
  ∀ P : rowSG Pr sel mu, ∃ (al : L.β (R.m - 2)) (x₀ : HomE X.E (R.N (R.m - 2)) (R.N (R.m - 2 + 1))),
    PsiAt Ch sel mu cst (R.m - 2) P (L.h (R.m - 2) al P) x₀
      (reix X.E (R.N i) (R.N (R.m - 2 + 1)) ((frsF sel mu p P).symm (repY Y))) ≠ 0

def Pt.Valid {u : Pr.Word} {i : ℕ} (a : Pt sel mu L u i) : Prop :=
  (i < R.m → a.2.1 ≠ none) ∧ (R.m ≤ i → a.2.1 = none) ∧
  (i + 1 = R.m → YbOk Ch sel mu cst L a.1 a.2.2) ∧ (i + 1 ≠ R.m → a.2.2 = ∅)

variable (abelian₂ : HeightOneSpectrum (𝓞 X.E) → Submodule (𝓞 X.E) (Sp X.E (rkTop R))) (dep : HeightOneSpectrum (𝓞 X.E) → ℕ)

def Mov {u : Pr.Word} {i : ℕ} (γ : UF X.E (R.N i)) (a a' : Pt sel mu L u i) (z : X.K) : Prop :=
  a'.2.1 = a.2.1 ∧ a'.2.2 = (fun v => γ.1 v) '' a.2.2 ∧
  ∃ (h : GLG X.E (R.N i) Pr.vGs) (c : GLQ X.E (R.N i) (QE sel (mu : Chr X.F X.E X.K))),
    a'.1 = ((γ, h, c) : UF X.E (R.N i) × GLG X.E (R.N i) Pr.vGs × GLQ X.E (R.N i) (QE sel (mu : Chr X.F X.E X.K))) • a.1 ∧
    (∀ b : L.β i, a.2.1 = some b → ∃ (hh : h ∈ (L.levG i b).grp) (hc : c ∈ (L.levQ i b).grp),
      z = (((L.levG i b).chr ⟨h, hh⟩ * (L.levQ i b).chr ⟨c, hc⟩ : X.Kˣ) : X.K)) ∧
    (a.2.1 = none → ∃ (zG : Pr.vGs → X.K) (zQ : QE sel (mu : Chr X.F X.E X.K) → X.K),
      (∀ w : Pr.vGs, ∃ κ : Sp X.E (R.N i) ≃ₗ[X.E] Sp X.E (R.N i),
        TopLev Ch mu (R.N i) ((Pr.piT u : 𝓞 X.E) : X.E) abelian₂ dep cst.sharp w.1 κ (zG w) ∧
        ∀ x ∈ stdAt X.E (R.N i) w.1, redV w.1 (κ x) = (h w).1.mulVec (redV w.1 x)) ∧
      (∀ P : QE sel (mu : Chr X.F X.E X.K),
        TopLev Ch mu (R.N i) ((Pr.piT u : 𝓞 X.E) : X.E) abelian₂ dep cst.sharp P.1 (c P).1 (zQ P)) ∧
      z = (∏ w, zG w) * ∏ P, zQ P)

def XiTop {u : Pr.Word} {i : ℕ} (p : ChPt (R := R) sel mu u i) (Y : Set (Sp X.E (R.N i)))
    (p' : ChPt (R := R) sel mu u (i + 1)) (x : HomE X.E (R.N i) (R.N (i + 1))) : X.K :=
  phiT X.K p.deco.1 p'.deco.1 x *
    ∏ P : rowSG Pr sel mu,
      PhiTop Ch mu cst.sharp (R.m - 2) P.1
          (reix X.E (R.N (i + 1)) (rkTop R) ∘ₗ inFr (frsF sel mu p P) (frsF sel mu p' P) x ∘ₗ
            reix X.E (R.N (R.m - 2 + 1) + cOf R (R.m - 2 + 1)) (R.N i)) *
        ftY sel mu cst P
          ((((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ • atNL X.E (R.N (i + 1)) (R.N R.m - 1)) ∘ₗ
            inFr (frsF sel mu p P) (frsF sel mu p' P) x)
          ((frsF sel mu p P).symm (repY Y))

def XiStep {u : Pr.Word} {i : ℕ} (a : Pt sel mu L u i) (a' : Pt sel mu L u (i + 1))
    (x : HomE X.E (R.N i) (R.N (i + 1))) : X.K :=
  if i + 2 < R.m then
    (match a.2.1, a'.2.1 with
      | some al, some be => XiEntry Ch sel mu cst L i al be a.1 a'.1 x
      | _, _ => 0)
  else if i + 2 = R.m then
    (match a.2.1 with
      | some al => XiCpl1 Ch sel mu cst L i al a.1 a'.1 a'.2.2 x
      | none => 0)
  else XiTop Ch sel mu cst a.1 a.2.2 a'.1 x

def ThStep (A : Amb X) {u : Pr.Word} {i : ℕ} (a : Pt sel mu L u i) (a' : Pt sel mu L u (i + 1)) :
    VCx X.Tau (R.N i) (R.N (i + 1)) → ℂ := fun z =>
  latSum (divLat (cAof sel mu cst) (homAt (Sall sel mu u) a.1.deco.1.N a'.1.deco.1.N))
    (mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) a.1.deco.1.N a'.1.deco.1.N))
    fun x => A.σ₀ (XiStep Ch sel mu cst L a a' x) *
      A.thInd (Sall sel mu u) a.1.deco.1.N a'.1.deco.1.N (cBof sel mu cst u) x z

def muInvAt (i : ℕ) {u : Pr.Word} {j : ℕ} (p : ChPt (R := R) sel mu u j) : X.K :=
  muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) p.deco.1.N (frsF sel mu p)

end Concrete

section Global

variable {D : D7} {X : Fields} (s : Seam D X)

def ambE (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (e : TaylorLogMetric.FamE D) (dgen : D.what₂.Tau → ℂ) : Amb X where
  σ₀ := s.σ₀
  δ := δ
  d := D.host.d
  sc := (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹
  AA := Submodule.span (𝓞 X.E)
    {r | ∃ c ∈ cc, ∃ t ∈ D.host.AA0, r = s.iE.symm ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t)}
  cD τ := dgen (s.iT τ)
  e a b N N' z := e a b (s.lat N) (s.lat N') fun τ => z (s.iT.symm τ)
  chiF a b N N' := Base.chiFac χ a b (s.lat N) (s.lat N')

example {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (dgen : D.what₂.Tau → ℂ) :
    ambE s cc δ χ (B.eNat χ) dgen = ambOf s B χ dgen := rfl

def avoid (D : D7) (Pr : Primes X) : Set ℕ :=
  hostS D.host.q D.host.d (D.host.g 0) (D.host.g 1) (Set.range Pr.T ∪ (D.host.small : Set ℕ))

def FieldTie (Pr : Primes X) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    (wd : D.what₂.Word → Pr.Word) : Prop :=
  X.Ok ∧ s.Ok ∧ Pr.Ok ∧ IsSel X sel ∧ (∀ i, Pr.g i = D.host.g i) ∧ ∀ u, Pr.T (wd u) = (D.mem u).A.T

def CharTie {Pr : Primes X} (Ch : Chars X Pr D.R.m) (G : ChGlob X D.R.m) (eta : Formalism.L2.Host.HChar X.E)
    (cc : Ideal (𝓞 D.host.K)) : Prop :=
  Ch.Ok ∧ G.σ₀ = s.σ₀ ∧ Ch.Tied s.σ₀ (fun j τ => (D.hc (s.iT τ)).e j) G.mu0 eta ∧
    D.host.φ₀ (s.iE G.xi0) = -(((Ideal.absNorm cc : ℕ) : ℂ) * (Complex.I * (Real.sqrt D.host.d : ℂ)))⁻¹

def FamTie (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (e : TaylorLogMetric.FamE D)
    (dgen : D.what₂.Tau → ℂ) : Prop :=
  TaylorLogMetric.IsCurveIdeal D cc ∧ TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ ∧ TaylorLogMetric.IsChi D χ ∧ TaylorLogMetric.vec22 D (TaylorLogMetric.tor0 D cc δ) e ∧
    TaylorLogMetric.eq22 D (TaylorLogMetric.tor0 D cc δ) χ e ∧ IsDgen D dgen

open Classical in

def TupTie (Dx : DivX D) {S : Set ℕ} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    (tup : D.what₂.Tup → Tup X.F X.E X.K S) : Prop :=
  tup D.what₂.mu0 = 1 ∧ ∀ μ, Formalism.MainNotions.LocalQuadraticParts.UsedT D μ → Dx.Qp μ = (QE sel (tup μ : Chr X.F X.E X.K)).image qOf

end Global

section Chain

variable {D : D7} {X : Fields} (s : Seam D X) {Pr : Primes X} (Ch : Chars X Pr D.R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr D.R (QE sel (mu : Chr X.F X.E X.K)))
  (abelian₂ : HeightOneSpectrum (𝓞 X.E) → Submodule (𝓞 X.E) (Sp X.E (rkTop D.R))) (dep : HeightOneSpectrum (𝓞 X.E) → ℕ)
  {u : D.what₂.Word} (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (v : Pr.Word)
  (rep : ∀ i, C.cls i → Pt sel mu L v i)
  (frm : ∀ i, C.Y i → D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ)

def ClsTie : Prop :=
  ∀ i ≤ D.R.m, (∀ c, Pt.Valid Ch sel mu cst L (rep i c)) ∧
    (∀ c c' γ z, Mov Ch sel mu cst L abelian₂ dep γ (rep i c) (rep i c') z → c = c') ∧
    ∀ a : Pt sel mu L v i, Pt.Valid Ch sel mu cst L a → ∃ c γ z, Mov Ch sel mu cst L abelian₂ dep γ (rep i c) a z

def StabTie : Prop :=
  ∀ i ≤ D.R.m, ∀ c, ∃ ι : C.stab i c →* UF X.E (D.R.N i), Function.Injective ι ∧
    ∀ γ, γ ∈ ι.range ↔ ∃ z, Mov Ch sel mu cst L abelian₂ dep γ (rep i c) (rep i c) z

def FrmTie : Prop :=
  ∀ i ≤ D.R.m, Function.Injective (frm i) ∧
    (∀ f : D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ, (∃ y, frm i y = f) ↔ ∀ τ, (f τ).det ≠ 0) ∧
    ∀ y τ, C.de i y τ = (frm i y τ).det

def IsWt (i : ℕ) (lam : D.what₂.Tau → Fin (D.R.N i) → ℤ) (f : C.Y i → ℂ) : Prop :=
  (∃ (n : ℕ) (Q : MvPolynomial (GL3Theta.FrV D (D.R.N i)) ℂ),
    ∀ y, f y * (∏ τ, (frm i y τ).det) ^ n = GL3Theta.evFr D Q (frm i y)) ∧
  ∀ (y y' : C.Y i) (b : D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ),
    (∀ τ, (b τ).BlockTriangular id) → (∀ τ, frm i y' τ = frm i y τ * b τ) →
      f y' = (∏ τ, ∏ k, b τ k k ^ lam τ k) * f y

def matAt {n : ℕ} (γ : UF X.E n) (τ : D.what₂.Tau) : Matrix (Fin n) (Fin n) ℂ :=
  (LinearMap.toMatrix' γ.1.toLinearMap).map fun a => TaylorLogMetric.embT D τ (s.iE a)

def IsForm (i : ℕ) (lam : D.what₂.Tau → Fin (D.R.N i) → ℤ) (φ : C.cls i → C.Y i → ℂ) : Prop :=
  ∀ c, IsWt C frm i lam (φ c) ∧
    ∀ γ z, Mov Ch sel mu cst L abelian₂ dep γ (rep i c) (rep i c) z →
      ∀ y y' : C.Y i, (∀ τ, frm i y' τ = matAt s γ τ * frm i y τ) → φ c y' = s.σ₀ z * φ c y

def FiTie {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
    (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P) : Prop :=
  ∀ i ≤ D.R.m, ∀ φ, φ ∈ M.Fi i ↔
    IsForm s Ch sel mu cst L abelian₂ dep C v rep frm i
      (fun τ k => (M.lam i τ).w k - (i : ℤ) * (((D.R.t + 1) / 2 : ℕ) : ℤ)) φ

def RhoTie (χ : TaylorLogMetric.IdE D → ℂ) : Prop :=
  ∀ i < D.R.m,
    (∀ c, C.rhoDet i c = s.σ₀ (muInvAt Ch sel mu cst i (rep i c).1) *
      χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D (D.R.N i)) (s.lat (rep i c).1.deco.1.N)) ^ (-((D.R.N (i + 1) / 2 : ℕ) : ℤ))) ∧
    ∀ c', C.rhoDet' i c' = (s.σ₀ (muInvAt Ch sel mu cst i (rep (i + 1) c').1))⁻¹ *
      χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D (D.R.N (i + 1))) (s.lat (rep (i + 1) c').1.deco.1.N)) ^ (((D.R.N i / 2 : ℕ) : ℤ))

def UnfTie (A : Amb X) (dgen : D.what₂.Tau → ℂ) : Prop :=
  ∀ i < D.R.m, ∀ (c : C.cls i) (c' : C.cls (i + 1)) (Q : MvPolynomial (GL3Theta.FrV D (D.R.N i)) ℂ) (y' : C.Y (i + 1)),
    C.unf i c c' (fun y => GL3Theta.evFr D Q (frm i y)) y' =
      GL3Theta.applyAt0 D (GL3Theta.polD D dgen Q (frm (i + 1) y'))
        (fun z => ThStep Ch sel mu cst L A (rep i c) (rep (i + 1) c') fun τ => z (s.iT τ))

end Chain

def KForms_at (D : D7) (Dx : DivX D) (Tw : TwForms D) (_E : KerEnt D Dx Tw)
    (X : Fields) (s : Seam D X) (Pr : Primes X) (Ch : Chars X Pr D.R.m) (G : ChGlob X D.R.m)
    (eta : Formalism.L2.Host.HChar X.E) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (e : TaylorLogMetric.FamE D) (dgen : D.what₂.Tau → ℂ)
    (wd : D.what₂.Word → Pr.Word) (tup : D.what₂.Tup → Tup X.F X.E X.K (avoid D Pr))
    (cst : ∀ μ, LocCst X (rowSG Pr sel (tup μ)))
    (L : ∀ μ, ChIdx X Pr D.R (QE sel (tup μ : Chr X.F X.E X.K)))
    (abelian₂ : D.what₂.Tup → HeightOneSpectrum (𝓞 X.E) → Submodule (𝓞 X.E) (Sp X.E (rkTop D.R)))
    (dep : D.what₂.Tup → HeightOneSpectrum (𝓞 X.E) → ℕ)
    (rep : ∀ u μ i, (D.chTw u μ).cls i → Pt sel (tup μ) (L μ) (wd u) i)
    (frm : ∀ u μ i, (D.chTw u μ).Y i → D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ) : Prop :=
  GL3Theta.InducedCMType D → GL3Theta.HostFieldConditions D →
  FieldTie s Pr sel wd → CharTie s Ch G eta cc → FamTie D cc δ χ e dgen → TupTie Dx sel tup →
  ∀ (u : D.what₂.Word) (μ : D.what₂.Tup), Formalism.MainNotions.LocalQuadraticParts.UsedT D μ →
    (L μ).Ok Ch sel (tup μ) (cst μ) G (D.R.m - 2) →
    TopOk sel (tup μ) (cst μ) (abelian₂ μ) (dep μ) →
    (ambE s cc δ χ e dgen).AAUnit (Sall sel (tup μ) (wd u)) →
    ClsTie Ch sel (tup μ) (cst μ) (L μ) (abelian₂ μ) (dep μ) (D.chTw u μ) (wd u) (rep u μ) →
    StabTie Ch sel (tup μ) (cst μ) (L μ) (abelian₂ μ) (dep μ) (D.chTw u μ) (wd u) (rep u μ) →
    FrmTie (D.chTw u μ) (frm u μ) →
    FiTie s Ch sel (tup μ) (cst μ) (L μ) (abelian₂ μ) (dep μ) (D.chTw u μ) (wd u) (rep u μ) (frm u μ) (Tw.fm u μ) →
    RhoTie s Ch sel (tup μ) (cst μ) (L μ) (D.chTw u μ) (wd u) (rep u μ) χ →
    UnfTie s Ch sel (tup μ) (cst μ) (L μ) (D.chTw u μ) (wd u) (rep u μ) (frm u μ) (ambE s cc δ χ e dgen) dgen →
    ∀ i < D.R.m, ∀ φ ∈ (Tw.fm u μ).Fi i, (D.chTw u μ).K i φ ∈ (Tw.fm u μ).Fi (i + 1)

example (E : Type) [Field E] (n : ℕ) (x : Sp E n) : reix E n n x = x := by
  funext l
  simp [reix, atNL]

end GlobalTheory.IndefiniteRowSideFullHecke.AmbientLatticeAvoidance
