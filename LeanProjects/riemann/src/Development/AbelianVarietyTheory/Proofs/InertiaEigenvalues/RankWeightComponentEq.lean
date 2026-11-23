import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DropPlInsert
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CmAdeleIdempotentOfPlaceProperties
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)

noncomputable section

namespace GlobalTheory.DownLift.GenSplit

variable {D : D7}

abbrev OI (v : FinPl D) : Type := v.adicCompletionIntegers D.host.F

def InvForm (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ u, IsHalf e u → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f

def InPow {v : FinPl D} (ϖ : OI v) (N : ℕ) {m n : Type} (x : Matrix m n (Fv D.host.F v)) : Prop :=
  ∀ i j, ∃ o : OI v, x i j = algebraMap (OI v) (Fv D.host.F v) (ϖ ^ N * o)

def Bdd {v : FinPl D} (ϖ : OI v) (N : ℕ) {m n : Type} (x : Matrix m n (Fv D.host.F v)) : Prop :=
  ∀ i j, ∃ o : OI v, algebraMap (OI v) (Fv D.host.F v) (ϖ ^ N) * x i j = algebraMap (OI v) (Fv D.host.F v) o

def comb (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) : WO S T → ℂ :=
  c.sum fun u z => z • heisO ψ S T u f

def RelOff (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Sb : Finset (FinPl D)) (p f : WO S T → ℂ) : Prop :=
  ∀ c : WO S T →₀ ℂ, (∀ u ∈ c.support, OffPl Sb u) → comb ψ S T c p = 0 → comb ψ S T c f = 0

def CoEig (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (p f : WO S T → ℂ) (u : WO S T) : Prop :=
  ∃ c : ℂ, heisO ψ S T u p = c • p ∧ heisO ψ S T u f = c • f

def Shape (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (A : Set (WO S T)) (x₀ : WO S T) (f : WO S T → ℂ) : Prop :=
  (∀ z ∈ A, heisO ψ S T z f = f) ∧
    ∀ y, IsHalf e y → (∀ z ∈ A, ψ (symplO S T z y) = 1) → heisO ψ S T y f = ψ (symplO S T x₀ y) • f

def halfPow {v : FinPl D} (φ : SplitProj D v) (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v))
    (BT : GL (Fin T.rank) (Fv D.host.F v)) (e : AE D) (ϖ : OI v) (N : ℕ) : Set (WO S T) :=
  {z | IsHalf (cA D e) z ∧ InPow ϖ N (adjCo φ S T BS BT z)}

def rowIx {n r t : ℕ} (h : r + t = n) : Fin r ⊕ Fin t ≃ Fin n := finSumFinEquiv.trans (finCongr h)

def co {v : FinPl D} (φ : SplitProj D v) (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v))
    (BT : GL (Fin T.rank) (Fv D.host.F v)) {r t : ℕ} (hS : r + t = S.rank) (hT : r = T.rank) (x : WO S T) :
    Matrix (Fin r ⊕ Fin t) (Fin r) (Fv D.host.F v) :=
  (adjCo φ S T BS BT x).submatrix (rowIx hS) (finCongr hT)

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem rank_V (i : Fin D.R.m) : D.R.r + D.R.t = (Vc D i).rank := (D.sp.V_rank _ (Nat.le_add_left _ _) i.2).symm

theorem rank_weight_component_eq (i : Fin D.R.m) : D.R.r = (Wc D i).rank := (D.sp.W_rank _ (Nat.le_add_left _ _) i.2).symm

def coR (R : RealDat D A Ks) (i : Fin D.R.m) {v : FinPl D} (φ : SplitProj D v) (x : WO (Vc D i) (Wc D i)) :
    Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v) :=
  co φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) (rank_V i) (rank_weight_component_eq i) x

def ActAt (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (PP : Pl D.host.E) {v : FinPl D} (φ : SplitProj D v) (e : AE D)
    (red : OI v →+* kP PP) : Prop :=
  ∀ h : GL (Fin (Vc D i).rank) (OI v), ∃ κ : GA D (Vc D i), Formalism.L2.Theta.SuppAt e (Vc D i) κ ∧ κ ∈ GfC (Vc D i) ∧
    finE (Vc D i) κ ∈ Formalism.L2.DIV.St (R.βV i) ∧
    grpCo φ (Vc D i) (frCo φ (R.βV i)) κ = Matrix.GeneralLinearGroup.map (algebraMap (OI v) (Fv D.host.F v)) h ∧
    redFn (R.βV i) PP (finE (Vc D i) κ) = Matrix.GeneralLinearGroup.map red h ∧
    (∀ PP', PP' ∈ R.Pg ∨ PP' ∈ R.Q t → PP' ≠ PP → redFn (R.βV i) PP' (finE (Vc D i) κ) = 1) ∧
    ∀ ℓ, InvForm R.ψ (Vc D i) (Wc D i) e ℓ → ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f →
      ℓ (R.ωP i t (κ, 1) f) = ((R.chi ((i : ℕ) + 1) PP (Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.map red h)) : ℂˣ) : ℂ) * ℓ f

theorem placeIdem_eq {v : FinPl D} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) :
    algebraMap (AF D.host.F) (AE D) ε = idem D (.inl v) := by
  obtain ⟨α, rfl, h1, h2⟩ := h
  obtain ⟨α', e', h1', h2'⟩ := ((GlobalTheory.PlaceTensor.idem_spec D).2.2.2.1 v).2.2
  have : α = α' := by
    apply Subtype.ext
    funext w
    by_cases hw : w = v
    · subst hw; exact h1.trans h1'.symm
    · exact (h2 w hw).trans (h2' w hw).symm
  rw [this, ← e']
  rfl

theorem suppIn_of_suppAt {v : FinPl D} {φ : SplitProj D v} {e : AE D} (he : IsIdemOf φ e) {Sb : Finset (FinPl D)}
    (hv : v ∈ Sb) {V : HSp D} {g : GA D V} (hg : Formalism.L2.Theta.SuppAt e V g) : SuppIn Sb V g := by
  obtain ⟨-, h2, -, h4, -⟩ := GlobalTheory.PlaceTensor.idem_spec D
  have hg' : ∀ i j, idem D (.inl v) * (Formalism.L2.Theta.mt V g - 1) i j = (Formalism.L2.Theta.mt V g - 1) i j := fun i j => by
    rw [← he.2.1]; exact hg i j
  refine ⟨Matrix.ext fun i j => ?_, fun w hw ε hε i j => ?_⟩
  · rw [Matrix.map_apply, ← hg', map_mul, (h4 v).1, zero_mul]; rfl
  · rw [placeIdem_eq hε, ← hg', ← mul_assoc, h2 _ _ (fun h => hw (by rw [Sum.inl.inj h]; exact hv)), zero_mul]

end GlobalTheory.DownLift.GenSplit

end
