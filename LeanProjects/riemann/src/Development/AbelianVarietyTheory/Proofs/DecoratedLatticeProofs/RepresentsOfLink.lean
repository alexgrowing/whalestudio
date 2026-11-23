import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsFinCombSingleZero
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.UnimodularTower
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralEigenRealDatumFiniteSumFockProductsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BilinearVacuumNonzeroCuspForm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealCentreActsByCharacterOnIsotypicSlicesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BilinearVacuumCentralCharacter
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftFockSumEqSumIteratedLiftsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftFockSumEqSumIteratedLifts
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawWeilBiActionCommutes
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralEigenThetaIsFockVectorBoundedDegree
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmZeroRat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftPeriodRankZeroFubiniCompactQuotient
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealTranslationCuspFormMapsEqSmoothLinearMap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealComponentCentralDefiniteUnitaryEqUnitScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalDefiniteSpaceH
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaUnfoldingEquivariantUnitaryGroups
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsPreserveThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsClosedOfLocallyCompactSpace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RapidValOfCuspRapidDecay
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepWeilDatumNonzeroFockVacuum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KFiniteSpanLeSpanRealIntertwinerValues
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsContAutRTrans
import Formalism.LocalRingCardinality.PosOfIsomEmb

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.IndefiniteRowSideFullHecke.UnimodularTower
open GlobalTheory.ChainOnto (Com PiLocalization₂)
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSawCompare

variable {D : D7} {u : D.what₂.Word}

theorem defSp_is {V : HSp D} (hs : V.SigOK) (hp : V.IsPosDef) {S : D.what₂.Tau → SPar} (M : DSModel V S) (x : DefSp V)
    (h1 : x.s = cart M) (h2 : x.B = onb M) (h3 : IsSelfDualC V x.L) : x.Is := by
  have hs' : ∀ τ, Formalism.UG.HasSignature (gramAt D V τ) V.rank 0 := fun τ => by
    have := hs (tauE D τ)
    rw [hp (tauE D τ)] at this
    exact this
  have hJ : ∀ τ, Formalism.REAL.Jm (M.ε τ) = 1 := fun τ => by
    have := signs_pos_of_frame_gram_posdef (M.ε τ) (M.fr τ) _ (M.fr_gram τ) (hs' τ)
    unfold Formalism.REAL.Jm; simp [this]
  have hd := fun τ => (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hc : ∀ τ, x.s τ = 1 := fun τ => by rw [h1, cart, hJ, Matrix.mul_one, Matrix.nonsing_inv_mul _ (hd τ)]
  refine ⟨hs, Inh.coCpt_of_isDefinite hs fun τ => Or.inl (hp τ), fun τ => ?_, fun τ => Or.inl (hc τ), fun τ => ?_, h3⟩
  · rw [hc]
    exact ⟨by simp, by simp, by simpa using Formalism.IndefR.Fin.Lifts.posDef_of_sig _ (hs' τ)⟩
  · refine ⟨V.rank, fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, ?_, by simp [hc]⟩
    rw [h2, onb, ← M.fr_gram τ, hJ, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul,
      Matrix.mul_nonsing_inv _ (hd τ), Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_nonsing_inv _ (hd τ)]
    simp

abbrev Live (D : D7) (u : D.what₂.Word) : Type := ∀ j, Submodule ℂ (Fn D u j)

variable (W : Live D u) {c : Com D}

structure PassageOn : Prop where
  ff_ram : ∀ i, i + 2 ≤ D.R.m → ∀ ε, ∀ φ ∈ Ram D u i ⊓ W i, ffStar D u i ε φ ∈ Ram D u i ⊓ W i
  ker_ram : ∀ i, i + 3 ≤ D.R.m → ∀ φ ∈ Ram D u i ⊓ W i, Formalism.MainNotions.product_first_zeroth_parts.KT D u i φ ∈ Ram D u (i + 1) ⊓ W (i + 1)
  comm : ∀ i, i + 3 ≤ D.R.m → ∃ a : ℂ, a ≠ 0 ∧ ∀ ε, ∀ φ ∈ Ram D u i ⊓ W i,
    ffStar D u (i + 1) ε (Formalism.MainNotions.product_first_zeroth_parts.KT D u i φ) = a • Formalism.MainNotions.product_first_zeroth_parts.KT D u i (ffStar D u i ε φ)
  bij : ∀ ε, Set.BijOn (ffStar D u 0 ε) (Ram D u 0) (Ram D u 0)

structure ColIsOn {X : HSp D} {j : ℕ} (A : ColOn c u X j) : Prop where
  rank : X.rank = D.R.N j
  sig : ∀ τ : D.host.E →+* ℂ, X.sig τ = (D.R.N j, 0)
  fin : A.K ≤ GfC X
  opn : ∃ U : Subgroup (GA D X), IsOpen (U : Set (GA D X)) ∧ U ⊓ GfC X ≤ A.K
  inj : ∀ φ : Fm D u j, (φ : Fn D u j) ∈ W j → A.a φ = 0 → φ = 0
  cont : ∀ φ v, IsContAut X (A.sc φ v)

structure StepIsOn {X X' : HSp D} {j : ℕ} {A : ColOn c u X j} {A' : ColOn c u X' (j + 1)} (k : ColStep A A') (vol : Vol X) :
    Prop where
  weil : IsWeilDatumO c.ψ X X' (c.μ (j + 1)) (c.μ (j + 1)) k.om
  theta : ∀ P, IsThetaFunO c.ψ X X' (k.pt P)
  maps : ∀ φ ∈ Fm D u j ⊓ W j, Formalism.MainNotions.product_first_zeroth_parts.KT D u j φ ∈ Fm D u (j + 1) ⊓ W (j + 1)
  it_ne : k.it ≠ 0
  sum : ∀ (φ : Fm D u j) (φ' : Fm D u (j + 1)), (φ : Fn D u j) ∈ W j → (φ' : Fn D u (j + 1)) = Formalism.MainNotions.product_first_zeroth_parts.KT D u j φ →
    ∀ P v, k.lift vol (A.sc φ v) P = A'.sc φ' (k.it P v)

structure NodeIsOn {ρ j : ℕ} (N : Node c u ρ j) : Prop where
  row : N.row.Is c j
  col : ColIsOn W N.col
  line : Represents N.B.L (-((D.mem u).A.T : D.host.E))
  base : N.b ∈ GfC N.B.V
  unimod : Unimod (besGrp N.B.d N.B.o) N.B.μR

section Dbl

variable {σ j : ℕ} {N : Node c u (σ + 1) j} {N' : Node c u σ (j + 1 + 1)} (d : Dbl N N')

def SuppA (x : GA D N.B.V) : Prop :=
  ∀ P₁ P₂ (φ : Fm D u j), (φ : Fn D u j) ∈ Ram D u j ⊓ W j → ∀ v,
    ∀ h₁ ∉ dcos (jacGrp d.J.d) d.b d.row.lev, ∀ h₂, d.hand P₁ P₂ (N.col.sc φ v) (x * N.b) h₁ h₂ = 0

def SuppB (x : GA D N.B.V) : Prop :=
  ∀ P₁ P₂ (φ : Fm D u j), (φ : Fn D u j) ∈ Ram D u j ⊓ W j → ∀ v, ∀ x₁ ∈ GinfC d.J.W,
    ∀ h₂ ∉ dcos (besGrp N'.B.d N'.B.o) N'.b N'.row.lev, d.hand P₁ P₂ (N.col.sc φ v) (x * N.b) (x₁ * d.b) h₂ = 0

def ValAt (x : GA D N.B.V) : Prop :=
  ∀ P₁ P₂, ∀ x₁ ∈ GinfC d.J.W, ∀ x₂ ∈ GinfC N'.B.V,
    ∃ (n : ℕ) (Q₁ : Fin n → PolF D d.J.W₀.rank N.B.A.rank) (Q₂ : Fin n → PolF D N'.B.A.rank d.J.W₀.rank),
      ∀ φ φ' : Fm D u j, (φ : Fn D u j) ∈ Ram D u j ⊓ W j → (φ' : Fn D u j) = ffStar D u j d.ε φ → ∀ v,
        d.hand P₁ P₂ (N.col.sc φ v) (x * N.b) (x₁ * d.b) (x₂ * N'.b) =
          ∑ i, d.k₂.lift d.J.v0 (d.k₁.lift N.B.vA (N.col.sc φ' v) (Q₁ i)) (Q₂ i)

structure DblIsOn : Prop where
  row : d.row.Is c (j + 1)
  col : ColIsOn W d.col
  base : d.b ∈ GfC d.J.W
  unimod : Unimod (jacGrp d.J.d) d.J.μR
  step₁ : RowStep (j + 1) d.p₁ d.s₁
  step₂ : RowStep (j + 1 + 1) d.p₂ d.s₂
  ker₁ : StepIsOn W d.k₁ N.B.vA
  ker₂ : StepIsOn W d.k₂ d.J.v0
  supp₁ : ∀ x ∈ GinfC N.B.V, SuppA W d x
  supp₂ : ∀ x ∈ GinfC N.B.V, SuppB W d x
  val : ∀ x ∈ GinfC N.B.V, ValAt W d x

end Dbl

section Fin2

variable {j : ℕ} {N : Node c u 0 j} {T : HSp D} {top : RowOn T} (e : Fin2 N top)

def ValTop : Prop :=
  ∀ P₁ P₂, ∀ x ∈ GinfC N.B.V,
    ∃ (n : ℕ) (Q₁ : Fin n → PolF D e.t.J.W.rank N.B.A.rank) (Q₂ : Fin n → PolF D e.X.rank e.t.J.W.rank),
      ∀ φ φ' : Fm D u j, (φ : Fn D u j) ∈ Ram D u j ⊓ W j → (φ' : Fn D u j) = ffStar D u j e.ε φ → ∀ v h',
        e.inner P₁ P₂ (N.col.sc φ v) (x * N.b) h' =
          ∑ i, e.k₂.lift e.t.s.vW (e.k₁.lift N.B.vA (N.col.sc φ' v) (Q₁ i)) (Q₂ i) (e.o.emb (h', 1))

def PeriodTop : Prop :=
  ∀ (φ : Fm D u (j + 1 + 1)) (φ' : Fn D u D.R.m), (φ : Fn D u (j + 1 + 1)) ∈ W (j + 1 + 1) → HEq φ' (φ : Fn D u (j + 1 + 1)) →
    ∀ (F : (D.mem u).P.Mt) v w,
      ∫ h' in top.fd, PiLocalization₂.val (e.ι F) w h' * e.col₂.sc φ v (e.o.emb (h', 1)) ∂top.ν = e.br v w * (D.mem u).P.Ptil φ' F

structure FinIsOn : Prop where
  idx : j + 1 + 1 = D.R.m
  row : e.row.Is c (j + 1)
  top_is : top.st.Is c (j + 1 + 1)
  top_cont : ∀ (y : top.st.CC c) w, IsContAut T (PiLocalization₂.val y w)
  col₁ : ColIsOn W e.col₁
  col₂ : ColIsOn W e.col₂
  line : e.L.rank = 1 ∧ Represents e.L ((D.mem u).A.T : D.host.E)
  step₁ : RowStep (j + 1) e.p₁ e.t.s
  is₂ : e.p₂.Is (j + 1 + 1)
  onto₂ : e.row.st.KF ≤ Submodule.span ℂ {x | ∃ P, ∃ w ∈ top.st.KF, x = e.p₂.It P w}
  χS : e.t.χS = c.chS (j + 1 + 1)
  χT : e.t.χT = c.chT (j + 1 + 1)
  om : e.t.om = e.p₂.ω
  μ : e.t.vT.μ = top.ν
  fd : e.t.vT.𝓕 = top.fd
  ker₁ : StepIsOn W e.k₁ N.B.vA
  ker₂ : StepIsOn W e.k₂ e.t.s.vW
  val : ValTop W e
  br_ne : e.br ≠ 0
  period : PeriodTop W e

end Fin2

noncomputable def TowerIsOn {T : HSp D} {top : RowOn T} : {ρ j : ℕ} → {N : Node c u ρ j} → Tower c u top ρ j N → Prop
  | _, _, N, .last e => NodeIsOn W N ∧ FinIsOn W e
  | _, _, N, .step _ d t => NodeIsOn W N ∧ DblIsOn W d ∧ TowerIsOn t

def LawsOn : Prop :=
  PassageOn W ∧ ∃ c : Com D, c.Is ∧ IsSharp c ∧ ∃ (T : HSp D) (top : RowOn T) (N : Node c u D.R.rS 0)
    (t : Tower c u top D.R.rS 0 N), TowerIsOn W t ∧ LinkP N

structure Kept : Prop where
  ker : ∀ j, j < D.R.m → ∀ φ ∈ Fm D u j ⊓ W j, Formalism.MainNotions.product_first_zeroth_parts.KT D u j φ ∈ W (j + 1)
  ff : ∀ j, j + 2 ≤ D.R.m → ∀ ε, ∀ φ ∈ Ram D u j ⊓ W j, ffStar D u j ε φ ∈ W j

variable {W}

theorem ColIsOn.is {X : HSp D} {j : ℕ} {A : ColOn c u X j} (h : ColIsOn ⊤ A) : A.Is :=
  ⟨h.rank, h.sig, h.fin, h.opn, (injective_iff_map_eq_zero _).2 fun φ => h.inj φ trivial, h.cont⟩

section Step

variable {X X' : HSp D} {j : ℕ} {A : ColOn c u X j} {A' : ColOn c u X' (j + 1)} {k : ColStep A A'} {vol : Vol X}

theorem StepIsOn.is (h : StepIsOn ⊤ k vol) : k.Is vol :=
  ⟨h.weil, h.theta, fun φ hφ => (h.maps φ ⟨hφ, trivial⟩).1, h.it_ne, fun φ φ' => h.sum φ φ' trivial⟩

end Step

theorem NodeIsOn.is {ρ j : ℕ} {N : Node c u ρ j} (h : NodeIsOn ⊤ N) : N.Is := ⟨h.row, h.col.is, h.line, h.base, h.unimod⟩

end GlobalTheory.SeeSawCompare

end
