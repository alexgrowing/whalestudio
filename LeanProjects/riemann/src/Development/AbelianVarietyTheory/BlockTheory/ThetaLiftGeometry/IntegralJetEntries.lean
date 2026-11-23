import Mathlib
import Formalism.LocalRingCardinality.DataKerI
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IntegralJetEntries

def JetsIntegral {σ : Type} {l : ℕ} [Fact l.Prime] (F : MvPowerSeries σ ℂ_[l]) : Prop :=
  ∀ a : σ →₀ ℕ, ‖(a.prod fun _ n => (n.factorial : ℂ_[l])) * MvPowerSeries.coeff a F‖ ≤ 1

def EntriesIntegral {Lt : Type} [DecidableEq Lt] (N₀ N₁ : ℕ) {l : ℕ} [Fact l.Prime]
    (F : MvPowerSeries (Lt × Fin N₀ × Fin N₁) ℂ_[l]) : Prop :=
  ∀ (P : MvPolynomial (KM.XZ Lt N₀ N₁) ℤ) (m : (Lt × ℕ × Fin N₀) →₀ ℕ),
    ‖MvPolynomial.coeff m (KM.applyAt0 N₀ N₁ l F P)‖ ≤ 1

def CurveTie (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Prop :=
  TaylorLogMetric.IsCurveIdeal D cc ∧ TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ

def levPr {D : D7} (Dx : DivX D) (u : D.what₂.Word) (μ : D.what₂.Tup) : Finset ℕ :=
  insert (D.mem u).A.T (({D.host.g 0, D.host.g 1} : Finset ℕ) ∪ Dx.Qp μ)

def LevTie {D : D7} (Dx : DivX D) (u : D.what₂.Word) (μ : D.what₂.Tup) (O : GL3Theta.LiftObj D (D.chTw u μ)) : Prop :=
  O.S = levPr Dx u μ

def perId (D : D7) (cc : Ideal (𝓞 D.host.K)) : Submodule (𝓞 D.host.E) D.host.E :=
  Submodule.span (𝓞 D.host.E)
    {r | ∃ c ∈ cc, ∃ t ∈ D.host.AA0, r = (((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t}

def IsDataPlaces (D : D7) (cc : Ideal (𝓞 D.host.K)) (S : Finset ℕ) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) : Prop :=
  letI := D.host.cmStar
  ∀ P ∈ SS, Formalism.L2.Col.conjPrime₂ P ∉ SS ∧ ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ ((D.host.q : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧
    ∃ q ∈ S, q.Prime ∧ ((q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal ∧ Nat.Coprime (Ideal.absNorm cc) q

def IsDatum (D : D7) (S : Finset ℕ) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (c : ℕ) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (Φ : Formalism.L2.Col.HomE D.host.E N N' → ℂ) : Prop :=
  (∀ x y, y - x ∈ Formalism.L2.Col.mulLat c (Formalism.L2.Col.homAt SS L L') → Φ y = Φ x) ∧
  (∀ x, Φ x ≠ 0 → x ∈ Formalism.L2.Col.divLat c (Formalism.L2.Col.homAt SS L L')) ∧
  ∀ x, Φ x ∈ TaylorLogMetric.Qbar ∧
    ∀ (p : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]), p ∉ S → ‖TaylorLogMetric.lamC lam (Φ x)‖ ≤ 1

def xiKer (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : TaylorLogMetric.FamE D) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (c : ℕ)
    {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (Φ : Formalism.L2.Col.HomE D.host.E N N' → ℂ) : TaylorLogMetric.VC D N N' → ℂ :=
  letI := D.host.cmStar
  Formalism.L2.Ker.thC (TaylorLogMetric.embT D) δ D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ (perId D cc) SS L L' c Φ (e N N' L L')

def XiTie (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : TaylorLogMetric.FamE D) {u : D.what₂.Word}
    {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} (O : GL3Theta.LiftObj D C) (i : ℕ) : Prop :=
  ∃ (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (c : ℕ), IsDataPlaces D cc O.S SS ∧ 0 < c ∧
    ∀ (k : C.cls i) (k' : C.cls (i + 1)), ∃ Φ : Formalism.L2.Col.HomE D.host.E (D.R.N i) (D.R.N (i + 1)) → ℂ,
      IsDatum D O.S SS c (O.lat i k).1 (O.lat (i + 1) k').1 Φ ∧
      O.Th i k k' = xiKer D cc δ e SS c (O.lat i k).1 (O.lat (i + 1) k').1 Φ

def UnfTie (D : D7) {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} (O : GL3Theta.LiftObj D C) (i : ℕ) : Prop :=
  ∀ k k' (Q : MvPolynomial (GL3Theta.FrV D (D.R.N i)) ℂ) (y' : C.Y (i + 1)),
    C.unf i k k' (fun y => GL3Theta.evFr D Q (O.frm i y)) y' =
      GL3Theta.applyAt0 D (GL3Theta.polD D O.dgen Q (O.frm (i + 1) y')) (O.Th i k k')

def IsRBasis (D : D7) {l : ℕ} [Fact l.Prime] (ρ : D.host.E → ℂ_[l]) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (g : Matrix (Fin N) (Fin N) ℂ_[l]) : Prop :=
  g.det ≠ 0 ∧
    Submodule.span 𝓞_ℂ_[l] (Set.range fun a : Fin N => fun k => g k a) =
      Submodule.span 𝓞_ℂ_[l] ((fun (x : Fin N → D.host.E) k => ρ (x k)) '' (L : Set (Fin N → D.host.E)))

open Classical in

def coordCh (D : D7) {l : ℕ} [Fact l.Prime] {N N' : ℕ} (s : D.what₂.Tau → ℂ_[l])
    (g : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ_[l]) (g' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ_[l])
    (k : D.what₂.Tau × Fin N' × Fin N) (x : (Bool × HH D) × Fin N × Fin N') : ℂ_[l] :=
  if tauPl D x.1 = k.1 then s k.1 * g' k.1 k.2.1 x.2.2 * ((g k.1)⁻¹) x.2.1 k.2.2 else 0

def SerTie {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (O : GL3Theta.LiftObj D (D.chTw u μ)) (w : D.what₂.places.Pl) (i : ℕ)
    (k : (D.chTw u μ).cls i) (k' : (D.chTw u μ).cls (i + 1)) : Prop :=
  ∃ (c₀ : D.what₂.Tau → ℂ_[D.what₂.places.resChar w])
    (g : D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ_[D.what₂.places.resChar w])
    (g' : D.what₂.Tau → Matrix (Fin (D.R.N (i + 1))) (Fin (D.R.N (i + 1))) ℂ_[D.what₂.places.resChar w]),
    (∀ τ, ‖c₀ τ‖ = 1) ∧
    (∀ τ, IsRBasis D (TaylorLogMetric.tauEmb D (E.lam w) τ) (O.lat i k).1 (g τ)) ∧
    (∀ τ, IsRBasis D (TaylorLogMetric.tauEmb D (E.lam w) τ) (O.lat (i + 1) k').1 (g' τ)) ∧
    E.Th u μ w i k k' =
      linAt (coordCh D (fun τ => c₀ τ * TaylorLogMetric.lamC (E.lam w) (O.dgen τ)) g g') (TaylorLogMetric.pSer D (E.lam w) (O.Th i k k'))

def Concl {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) (i : ℕ) (k : (D.chTw u μ).cls i) (k' : (D.chTw u μ).cls (i + 1)) : Prop :=
  JetsIntegral (E.Th u μ w i k k') ∧
  EntriesIntegral (D.R.N i) (D.R.N (i + 1)) (E.Th u μ w i k k') ∧
  ∀ (I : KM.ColChoice (D.R.N (i + 1)) (nuD D u i)) (m : ((Bool × HH D) × ℕ × Fin (D.R.N i)) →₀ ℕ),
    ‖MvPolynomial.coeff m (KM.applyAt0 (D.R.N i) (D.R.N (i + 1)) (D.what₂.places.resChar w) (E.Th u μ w i k k')
      (KM.Gxz (D.R.N i) (D.R.N (i + 1)) (nuD D u i) I))‖ ≤ 1

def JetInt_at (D : D7) (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) : Prop :=
  GL3Theta.InducedCMType D → GL3Theta.HostFieldConditions D → CurveTie D cc δ → TaylorLogMetric.IsChi D χ →
  ∀ (u : D.what₂.Word) (μ : D.what₂.Tup) (O : GL3Theta.LiftObj D (D.chTw u μ)), LevTie Dx u μ O →
  ∀ i, i < D.R.m → XiTie D cc δ (B.eNat χ) O i → UnfTie D O i →
  ∀ w : D.what₂.places.Pl, LevFree Dx u μ w → D.what₂.places.resChar w ≠ D.host.d →
  ∀ k k', SerTie E u μ O w i k k' → Concl E u μ w i k k'

def JetIntKer_at (D : D7) (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) : Prop :=
  GL3Theta.InducedCMType D → GL3Theta.HostFieldConditions D → CurveTie D cc δ → TaylorLogMetric.IsChi D χ →
  ∀ (u : D.what₂.Word) (μ : D.what₂.Tup) (O : GL3Theta.LiftObj D (D.chTw u μ)), LevTie Dx u μ O →
  ∀ i, i < D.R.m → GL3Theta.liftTie D (TaylorLogMetric.tor0 D cc δ) (B.eNat χ) O i →
  ∀ w : D.what₂.places.Pl, LevFree Dx u μ w → D.what₂.places.resChar w ≠ D.host.d →
  ∀ k k', SerTie E u μ O w i k k' → Concl E u μ w i k k'

def Translates_at (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) : Prop :=
  GL3Theta.InducedCMType D → GL3Theta.HostFieldConditions D → CurveTie D cc δ → TaylorLogMetric.IsChi D χ →
  ∀ (S : Finset ℕ) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (c N N' : ℕ)
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (Φ : Formalism.L2.Col.HomE D.host.E N N' → ℂ), TaylorLogMetric.admitted D N N' L L' → IsDataPlaces D cc S SS → 0 < c →
    IsDatum D S SS c L L' Φ →
    GL3Theta.IsKer D (TaylorLogMetric.tor0 D cc δ) (B.eNat χ) S L L' (xiKer D cc δ (B.eNat χ) SS c L L' Φ)

end GlobalTheory.IndefiniteRowSideFullHecke.IntegralJetEntries
