import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric

noncomputable section

namespace GlobalTheory.Glob.IntegralWittCoefficients

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions.TaylorLogMetric

def Wp (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] :=
  (Subring.closure {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ ζ ^ n = 1}).topologicalClosure

def InWf {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ∃ k : ℕ, (p : ℂ_[p]) ^ k * x ∈ Wp p

def IntegralW {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, MvPowerSeries.coeff n F ∈ Wp p

def CoefWf {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, InWf (MvPowerSeries.coeff n F)

def logMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    if n = 0 then 0 else (-1 : ℂ_[p]) ^ (n + 1) * MvPowerSeries.coeff α ((F - 1) ^ n) / (n : ℂ_[p])

def Simeq {σ : Type*} {p : ℕ} [Fact p.Prime] (f g : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralMv (expMv (f - g))

def SimeqW {σ : Type*} {p : ℕ} [Fact p.Prime] (f g : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralW (expMv (f - g))

def tauK (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (a : D.host.K) : ℂ_[p] :=
  lamC lam (D.host.φ₀ (a : D.host.E))

def tauKc (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (a : D.host.K) : ℂ_[p] :=
  lamC lam (D.host.φ₀ (D.host.conj (a : D.host.E)))

def OKp (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) : Set (ℂ_[p] × ℂ_[p]) :=
  closure (Set.range fun a : 𝓞 D.host.K => (tauK D lam (a : D.host.K), tauKc D lam (a : D.host.K)))

def hP {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] (x y : ι → ℂ_[p] × ℂ_[p]) : ℂ_[p] × ℂ_[p] :=
  ∑ k, x k * (y k).swap

def IsModelU {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
    (C : WeierstrassCurve.VariableChange ℂ_[p]) : Prop :=
  let W := C • wModel lam Λ
  IsIntP W.a₁ ∧ IsIntP W.a₂ ∧ IsIntP W.a₃ ∧ IsIntP W.a₄ ∧ IsIntP W.a₆ ∧ ‖W.Δ‖ = 1

def ModelOverW {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
    (C : WeierstrassCurve.VariableChange ℂ_[p]) : Prop :=
  let W := C • wModel lam Λ
  W.a₁ ∈ Wp p ∧ W.a₂ ∈ Wp p ∧ W.a₃ ∈ Wp p ∧ W.a₄ ∈ Wp p ∧ W.a₆ ∈ Wp p

structure G1 (p : ℕ) [Fact p.Prime] where
  lam : Qbar →+* ℂ_[p]
  abelian₂ : AddSubgroup ℂ
  C : WeierstrassCurve.VariableChange ℂ_[p]
  wq : PowerSeries ℂ_[p]
  ex : PowerSeries ℂ_[p]

namespace G1

variable {p : ℕ} [Fact p.Prime] (g : G1 p)

def W : WeierstrassCurve ℂ_[p] := g.C • wModel g.lam g.abelian₂

def l : PowerSeries ℂ_[p] := flog g.W g.wq

def Ok : Prop :=
  IsModelU g.lam g.abelian₂ g.C ∧ IsWq g.W g.wq ∧
    PowerSeries.constantCoeff g.ex = 0 ∧ PowerSeries.subst g.ex g.l = PowerSeries.X

def ph : PowerSeries ℂ_[p] := -logMv (ePhi1 g.lam g.abelian₂ g.C g.wq)

variable {σ : Type*}

def lg (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst a g.l

def pt (x : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst x g.ex

def add (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := g.pt (g.lg a + g.lg b)

def sub (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := g.pt (g.lg a - g.lg b)

def mulBy (c : ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  g.pt (MvPowerSeries.C c * g.lg a)

def lin {ι : Type*} [Fintype ι] (c : ι → ℂ_[p]) (a : ι → MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries σ ℂ_[p] :=
  g.pt (∑ j, MvPowerSeries.C (c j) * g.lg (a j))

def phAt (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst a g.ph

def be (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  g.phAt (g.add a b) - g.phAt a - g.phAt b

end G1

def At (D : D7) {p : ℕ} [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p) : Prop :=
  IsCurveIdeal D cc ∧ Nat.Coprime (Ideal.absNorm cc) p ∧ IsDiscriminantTwelfthRootOfIdealLattice D cc δ ∧
    g.abelian₂ = lamOf D cc δ ∧ g.Ok

abbrev Xv {p : ℕ} [Fact p.Prime] {σ : Type*} (i : σ) : MvPowerSeries σ ℂ_[p] := MvPowerSeries.X i

def SplitK (D : D7) (p : ℕ) : Prop := jacobiSym (-(D.host.d : ℤ)) p = 1

def InertK (D : D7) (p : ℕ) : Prop := jacobiSym (-(D.host.d : ℤ)) p = -1

def ser1 {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (G : ℂ → ℂ) : PowerSeries ℂ_[p] :=
  PowerSeries.mk fun n => lamC lam (iteratedDeriv n G 0 / (n.factorial : ℂ))

def G1.atU {p : ℕ} [Fact p.Prime] (g : G1 p) (G : ℂ → ℂ) : PowerSeries ℂ_[p] :=
  PowerSeries.subst (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])) * g.l)
    (ser1 g.lam G)

def Tors1 (p : ℕ) (Λ : AddSubgroup ℂ) (t : ℂ) : Prop :=
  t ∉ Λ ∧ ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ (n : ℂ) * t ∈ Λ

def IsTwoTorsionPointUnkilled (D : D7) (Λ : AddSubgroup ℂ) (t : ℂ) : Prop :=
  2 * t ∈ Λ ∧ ((1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2) * t ∉ Λ ∧
    ((1 - Complex.I * (Real.sqrt D.host.d : ℂ)) / 2) * t ∉ Λ

def th0 (Λ : AddSubgroup ℂ) (t0 : ℂ) : ℂ → ℂ :=
  fun z => U1 Λ t0 (sgStar Λ) z / U1 Λ t0 (sgStar Λ) 0

def G1.jetPh {p : ℕ} [Fact p.Prime] (g : G1 p) (i : ℕ) : ℂ_[p] :=
  (i.factorial : ℂ_[p]) * PowerSeries.coeff i (PowerSeries.subst g.ex g.ph : PowerSeries ℂ_[p])

def InOKp (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {ι : Type*}
    (x : ι → ℂ_[p] × ℂ_[p]) : Prop := ∀ k, x k ∈ OKp D lam

def G1.PhOn {p : ℕ} [Fact p.Prime] (g : G1 p) {κ ι : Type*} [Fintype κ] [Fintype ι]
    (b : ι → κ → ℂ_[p] × ℂ_[p]) : MvPowerSeries ι ℂ_[p] :=
  ∑ k, g.phAt (g.lin (fun e => (b e k).1) (fun e => Xv e))

def Primitive (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {n r : ℕ}
    (b : Fin r → Fin n → ℂ_[p] × ℂ_[p]) : Prop :=
  ∃ (M M' : Matrix (Fin n) (Fin n) (ℂ_[p] × ℂ_[p])) (f : Fin r → Fin n),
    (∀ i, InOKp D lam (M i)) ∧ (∀ i, InOKp D lam (M' i)) ∧ M * M' = 1 ∧ Function.Injective f ∧
    ∀ e k, M k (f e) = b e k

def DualIso {p : ℕ} [Fact p.Prime] {κ ι : Type*} [Fintype κ] (b b' : ι → κ → ℂ_[p] × ℂ_[p]) : Prop :=
  (∀ e e', hP (b e) (b e') = 0) ∧ (∀ e e', hP (b' e) (b' e') = 0) ∧
    ∀ e e', hP (b e) (b' e') = if e = e' then 1 else 0

def G1.beSum {p : ℕ} [Fact p.Prime] (g : G1 p) (ι : Type*) [Fintype ι] : MvPowerSeries (ι ⊕ ι) ℂ_[p] :=
  ∑ e : ι, g.be (Xv (Sum.inl e)) (Xv (Sum.inr e))

abbrev Idx (D : D7) (N N' : ℕ) : Type := D.what₂.Tau × Fin N' × Fin N

def embP (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N N' : ℕ}
    (y : Matrix (Fin N') (Fin N) D.host.E) : Idx D N N' → ℂ_[p] × ℂ_[p] :=
  fun k => (lamC lam (embT D k.1 (y k.2.1 k.2.2)), lamC lam (embT D k.1 (D.host.conj (y k.2.1 k.2.2))))

def YYp (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    Set (Idx D N N' → ℂ_[p] × ℂ_[p]) :=
  closure (embP D lam '' (YYl D L L' : Set (Matrix (Fin N') (Fin N) D.host.E)))

def BasisP (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {κ ι : Type*} [Fintype ι]
    (Y : Set (κ → ℂ_[p] × ℂ_[p])) (b : ι → κ → ℂ_[p] × ℂ_[p]) : Prop :=
  (∀ e, b e ∈ Y) ∧ ∀ y ∈ Y, ∃! c : ι → ℂ_[p] × ℂ_[p], InOKp D lam c ∧ y = fun k => ∑ e, c e * b e k

def G1.atLogP {p : ℕ} [Fact p.Prime] (g : G1 p) {κ ι : Type*} [Fintype ι]
    (b : ι → κ → ℂ_[p] × ℂ_[p]) (F : MvPowerSeries κ ℂ_[p]) : MvPowerSeries ι ℂ_[p] :=
  MvPowerSeries.subst (fun k : κ => ∑ e, MvPowerSeries.C (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (b e k).1) *
    g.lg (Xv e)) F

def G1.ePhI {p : ℕ} [Fact p.Prime] (g : G1 p) (ι : Type) [Fintype ι] : MvPowerSeries ι ℂ_[p] :=
  if p = 2 then 1 else
    ∏ i : ι, (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq))⁻¹

def logF (p : ℕ) [Fact p.Prime] : PowerSeries ℂ_[p] :=
  PowerSeries.mk fun n => ∑ j ∈ Finset.range (n + 1), if n = p ^ (2 * j) then ((p : ℂ_[p]) ^ j)⁻¹ else 0

def G1.thF {p : ℕ} [Fact p.Prime] (g : G1 p) (ep : ℂ_[p]) {σ : Type*} (k : σ) : MvPowerSeries σ ℂ_[p] :=
  g.pt (MvPowerSeries.C (((g.C.u : ℂ_[p]ˣ) : ℂ_[p]) * ep) * PowerSeries.subst (Xv k) (logF p))

def serA (p : ℕ) [Fact p.Prime] : MvPowerSeries (Fin 2) ℂ_[p] :=
  fun n => ∑ i ∈ Finset.range (n 0 + 1), ∑ j ∈ Finset.range (n 1 + 1),
    if i ≤ j ∧ n 0 = p ^ (2 * i) ∧ n 1 = p * p ^ (2 * j) then ((p : ℂ_[p]) ^ (i + j + 1))⁻¹ else 0

def serB (p : ℕ) [Fact p.Prime] : MvPowerSeries (Fin 2) ℂ_[p] :=
  fun n => ∑ i ∈ Finset.range (n 1 + 1), ∑ j ∈ Finset.range (n 0 + 1),
    if i ≤ j ∧ n 1 = p ^ (2 * i) ∧ n 0 = p * p ^ (2 * j) then ((p : ℂ_[p]) ^ (i + j + 1))⁻¹ else 0

def W2pair (p : ℕ) [Fact p.Prime] : Set (ℂ_[p] × ℂ_[p]) :=
  closure (Subring.closure {x : ℂ_[p] × ℂ_[p] | ∃ ζ : ℂ_[p], ζ ^ (p ^ 2 - 1) = 1 ∧ x = (ζ, ζ ^ p)} :
    Set (ℂ_[p] × ℂ_[p]))

def PUnit (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (z : D.host.E) : Prop :=
  ∀ s : D.R.GG, ‖lamC lam (D.host.emb s z)‖ = 1

def PowRat (D : D7) (t : D.Dt) (h : ℕ) (z : letI := D.host.cmStar; unitary D.host.E) : Prop :=
  0 < h ∧ ∃ k ∈ D.UO, t ^ h = D.e1Dt z * k

def rhoOf (D : D7) (mt : ℕ → D.Dt →* ℂˣ) (i : ℕ) : D.Dt →* ℂˣ :=
  (mt (i + 1))⁻¹ * D.chiD ^ (-(((D.R.N (i + 1)) / 2 : ℕ) : ℤ))

def rhoOf' (D : D7) (mt : ℕ → D.Dt →* ℂˣ) (i : ℕ) : D.Dt →* ℂˣ :=
  mt (i + 1) * D.chiD ^ ((((D.R.N i) / 2 : ℕ) : ℤ))

def rhoCh (D : D7) (i : ℕ) : D.Dt →* ℂˣ := rhoOf D D.muTil i

def rhoCh' (D : D7) (i : ℕ) : D.Dt →* ℂˣ := rhoOf' D D.muTil i

def CarriesTupleCharacters (D : D7) {u : D.what₂.Word} (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (mt : ℕ → D.Dt →* ℂˣ)
    (dt : ∀ i, C.cls i → D.Dt) : Prop :=
  ∀ i < D.R.m, (∀ c, C.rhoDet i c = ((rhoOf D mt i (dt i c) : ℂˣ) : ℂ)) ∧
    ∀ c, C.rhoDet' i c = ((rhoOf' D mt i (dt (i + 1) c) : ℂˣ) : ℂ)

def Mod1E (x : ℂ) : Prop := ∃ hx : x ∈ Qbar, ∀ ρ : Qbar →+* ℂ, ‖ρ ⟨x, hx⟩‖ = 1

def applyAt0 (D : D7) {N N' : ℕ} (P : MvPolynomial (Idx D N N') ℂ) (G : VC D N N' → ℂ) : ℂ :=
  ∑ α ∈ P.support, MvPolynomial.coeff α P * (α.prod fun _ n => (n.factorial : ℂ)) * taylor D G α

abbrev FrV (D : D7) (N : ℕ) : Type := D.what₂.Tau × Fin N × Fin N

def evFr (D : D7) {N : ℕ} (Q : MvPolynomial (FrV D N) ℂ) (y : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  MvPolynomial.eval (fun k : FrV D N => y k.1 k.2.1 k.2.2) Q

def polD (D : D7) {N N' : ℕ} (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (FrV D N) ℂ)
    (y' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) : MvPolynomial (Idx D N N') ℂ :=
  MvPolynomial.aeval (fun k : FrV D N => ∑ b : Fin N',
    MvPolynomial.C (s k.1 * (if h : (k.2.2 : ℕ) < N' then y' k.1 b ⟨k.2.2, h⟩ else 0)) *
      MvPolynomial.X ((k.1, b, k.2.1) : Idx D N N')) Q

def IsKer (D : D7) (T : Tor D) (e : FamE D) (S : Finset ℕ) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (Θ : VC D N N' → ℂ) : Prop :=
  ∃ (n : ℕ) (r : Fin n → ℂ) (t : Fin n → VC D N N'),
    (∀ k, r k ∈ Qbar) ∧
    (∀ k (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p ∉ S → ‖lamC lam (r k)‖ ≤ 1) ∧
    (∀ k, ∃ a : ℕ, 0 < a ∧ (∀ q : ℕ, q.Prime → q ∣ a → q ∈ S) ∧ a • t k ∈ La D T L L') ∧
    Θ = fun z => ∑ k, r k * U D T (t k) (e N N' L L') z

structure LiftObj (D : D7) {u : D.what₂.Word} (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) where
  mt : ℕ → D.Dt →* ℂˣ
  L0 : ∀ i, (letI := D.host.cmStar; SDLat D.host.E (D.R.N i))
  lattice_integral_coordinates : ∀ i (x : Fin (D.R.N i) → D.host.E), x ∈ (L0 i).1 ↔ ∀ k, IsIntegral ℤ (x k)
  lat : ∀ i, C.cls i → (letI := D.host.cmStar; SDLat D.host.E (D.R.N i))
  dt : ∀ i, C.cls i → D.Dt
  dt_lat : ∀ i c, (QuotientGroup.mk (dt i c) : D.Dt ⧸ D.UO) = D.relDet (D.R.N i) (L0 i) (lat i c)
  c13 : CarriesTupleCharacters D C mt dt
  frm : ∀ i, C.Y i → D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ
  frm_inj : ∀ i ≤ D.R.m, Function.Injective (frm i)
  frm_range : ∀ i ≤ D.R.m, ∀ f : D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ,
    (∃ y, frm i y = f) ↔ ∀ τ, (f τ).det ≠ 0
  frm_de : ∀ i ≤ D.R.m, ∀ y τ, C.de i y τ = (frm i y τ).det
  dgen : D.what₂.Tau → ℂ
  dgen_gen : ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M), (∀ τ x, embT D τ x ∈ M) ∧ ∀ τ, ∃ s : M, (s : ℂ) = dgen τ ∧
    ellT D M τ = Submodule.span (𝓞 M) {s}
  S : Finset ℕ
  Th : ∀ i, C.cls i → C.cls (i + 1) → VC D (D.R.N i) (D.R.N (i + 1)) → ℂ

def nrmId (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) (𝔞 : IdE D) : ℝ :=
  sSup ((fun x : D.host.E => ‖lamC lam (embT D τ x)‖) '' (𝔞 : Set D.host.E))

def InLaP (D : D7) (T : Tor D) (p : ℕ) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (x : VC D N N') : Prop :=
  ∃ k : ℕ, (p ^ k : ℕ) • x ∈ La D T L L'

def PhiHat (D : D7) (T : Tor D) (δ : ℂ) {N N' r : ℕ} (p n : ℕ) [Fact p.Prime] (ε : 𝓞 D.host.K)
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (Φ : LocallyConstant (Fin r → ℤ_[p]) ℂ)
    (y : Fin r → Fin (p ^ n)) : ℂ :=
  ((p : ℂ) ^ (n * r))⁻¹ * ∑ a : Fin r → Fin (p ^ n), Φ (fun i => (((a i : ℕ) : ℤ_[p]))) *
    (kap D T (vecN D T δ p n b a) (liftY D T δ p n ε b y))⁻¹

def Pinned (D : D7) : Prop := ∃ idl : D.Dt ⧸ D.UO → IdE D, RelDetPinned D idl

def hf1 (Λ : AddSubgroup ℂ) (z w : ℂ) : ℂ := z * (starRingEnd ℂ) w / (area Λ : ℂ)

def al1 (d : ℕ) (Λ : AddSubgroup ℂ) (x : ℂ) : ℂ := (-1 : ℂ) ^ (round (Real.sqrt d / 2 * (hf1 Λ x x).re))

def IsTheta0 (d : ℕ) (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) : Prop :=
  Differentiable ℂ G ∧ (∀ x ∈ Λ, ∀ z, al1 d Λ x * U1 Λ x G z = G z) ∧ G 0 = 1

def normSq1 (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) : ℝ :=
  let Fd : Set ℂ := Classical.epsilon (fun Fd => MeasureTheory.IsAddFundamentalDomain Λ Fd MeasureTheory.volume)
  ⨍ z in Fd, ‖G z‖ ^ 2 * Real.exp (-Real.pi * (hf1 Λ z z).re)

end GlobalTheory.Glob.IntegralWittCoefficients
