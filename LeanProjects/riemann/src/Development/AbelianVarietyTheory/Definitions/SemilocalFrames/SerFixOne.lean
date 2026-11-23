import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsFinTyp
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAutLoc
import Formalism.LocalToGlobal.IndefiniteReal.TensCastR

noncomputable section

namespace GlobalTheory.LabPin

open MeasureTheory NumberField Polynomial Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.HidaSetting Formalism.L2.SG.RowDict ReciprocityTheory.Aut Formalism.AUTREP

section Events

variable {D : D7} (X : HidaSetting D)

open Classical in

def egA (a : MonoidAlgebra ℂ (G0g D.nd)) (x : X.B.I.Gf) : ℂ :=
  if h : x ∈ X.B.I.Kset ∧ ∃ γ : G0g D.nd, GoodAt X x γ then
    a.coeff (Classical.choose h.2) / ((X.B.μf (X.B.I.Kg X.B.g)).toReal : ℂ)
  else 0

def tupOf (a : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)) : Tup2 D :=
  haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)

def ES (S : Set (Tup2 D)) : MonoidAlgebra ℂ (G0g D.nd) :=
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  MonoidAlgebra.ofCoeff <| Finsupp.equivFunOnFinite.symm fun g : G0g D.nd =>
    ∑ᶠ a : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), (Fin D.R.r → ZMod (D.host.g kv.1))),
      (open Classical in if tupOf a ∈ S then
        ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (g kv) else 0)

def eT (S : Set (Tup2 D)) : X.B.I.Gf → ℂ :=
  X.B.I.convF X.B.μf X.B.e (egA X (ES S))

open Classical in

def ReT (S : Set (Tup2 D)) : X.B.I.L2 X.B.μf X.B.fund →L[ℂ] X.B.I.L2 X.B.μf X.B.fund :=
  if h : ∃ T, X.B.I.IsRConvF X.B.μf X.B.fund X.B.R (eT X S) T then Classical.choose h else 0

def VT (t : Tup2 D) : Submodule ℂ (L2X X) :=
  Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X ⊓ LinearMap.ker ((ReT X {t} : L2X X →ₗ[ℂ] L2X X) - LinearMap.id)

def labOf (σ : Fin D.what₂.Drows) : Tup2 D := fun k => D.nd.lab k (D.what₂.ft σ)

def bRow (ι : D.s.HH ≃ₗᵢ[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) (σ : Fin D.what₂.Drows) : L2X X :=
  ((ι (D.sEE (D.what₂.onb σ)) : Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) : L2X X)

def LabTie (ι : D.s.HH ≃ₗᵢ[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) : Prop :=
  (∀ σ k v, IsLabel D k (D.nd.lab k (D.what₂.ft σ) v)) ∧ (∀ σ, D.ntypes.goodTuple (labOf σ)) ∧
    ∀ σ, bRow X ι σ ∈ VT X (labOf σ)

def IsSec (red : X.B.I.Gf → G0g D.nd) (sec : G0g D.nd → X.B.I.Gf) : Prop := ∀ γ, sec γ ∈ X.B.I.Kset ∧ red (sec γ) = γ

def serCoef (t : Tup2 D) (γ : G0g D.nd) : ℂ :=
  ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (t kv.1 kv.2)).coeff (γ kv)

end Events

section Types

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def RedTo (s : SplitPlace L) {g : ℕ} (x : GAf L n) (γ : GL (Fin n) (ZMod g)) : Prop :=
  ∀ i j, Valued.v ((s.loc n x : Matrix (Fin n) (Fin n) _) i j -
    ((((γ : Matrix (Fin n) (Fin n) (ZMod g)) i j).val : ℕ) : s.v.adicCompletion (maximalRealSubfield L))) < 1

def IsLift (s : SplitPlace L) {g : ℕ} (x : GAf L n) (γ : GL (Fin n) (ZMod g)) : Prop :=
  TrivOutside {s.v} x ∧ RedTo s x γ

def SerFix (π : Formalism.L2.NG.FinTyp L n) (s : SplitPlace L) {g : ℕ} (a : MonoidAlgebra ℂ (GL (Fin n) (ZMod g))) : Prop :=
  ∀ ℓ : GL (Fin n) (ZMod g) → GAf L n, (∀ γ, IsLift s (ℓ γ) γ) → ∀ φ ∈ π.S,
    (∀ x, IsLift s x (1 : GL (Fin n) (ZMod g)) → Formalism.L2.NG.rt L n x φ = φ) → ∑ᶠ γ, a.coeff γ • Formalism.L2.NG.rt L n (ℓ γ) φ = φ

theorem serFix_one (π : Formalism.L2.NG.FinTyp L n) (s : SplitPlace L) {g : ℕ} :
    SerFix π s (1 : MonoidAlgebra ℂ (GL (Fin n) (ZMod g))) := by
  classical
  intro ℓ hℓ φ _ h
  rw [finsum_eq_single _ 1]
  · simpa using h _ (hℓ 1)
  · intro γ hγ
    simp [MonoidAlgebra.one_def, Finsupp.single_apply, Ne.symm hγ]

end Types

local instance instCM (D : D7) : IsCMField D.host.E := D.host.isCMField_hostE

def HasTuple (D : D7) (π : Formalism.L2.NG.FinTyp D.host.E D.R.r) (t : Tup2 D) : Prop :=
  ∀ k v, IsLabel D k (t k v) ∧ ∀ s : SplitPlace D.host.E, s.w = D.naut.plGw k v → SerFix π s (D.ntypes.eSer k (t k v))

def TypeLab (D : D7) (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) : Prop :=
  ∀ σ, HasTuple D (rep σ) fun k => D.nd.lab k σ

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FrameRed {D : D7} (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : Formalism.L2.Theta.GA D (D.sp.Y 0))
    (PY : Formalism.IndefR.principalLevelFrame.RowPsi (Formalism.IndefR.Links.Yc D 0) D.R.r) (c : GAf D.host.E D.R.r) (red : X.B.I.Gf → G0g D.nd) : Prop :=
  Formalism.L2.SG.RowLevelMatch.IsRedHom X red ∧
  (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ∃ s : SplitPlace D.host.E, s.w = D.naut.plGw kv.1 kv.2) ∧
  ∀ (kv : (Σ k : Fin 2, D.nd.PlG k)) (s : SplitPlace D.host.E), s.w = D.naut.plGw kv.1 kv.2 →
    ∀ (x : GAf D.host.E D.R.r) (γ : GL (Fin D.R.r) (ZMod (D.host.g kv.1))), IsLift s x γ →
      ∃ k ∈ X.B.I.Kset, PY.ψ (c * x * c⁻¹) = Formalism.L2.SG.RowLevelMatch.kap X h t k ∧ red k kv = γ ∧ ∀ kv', kv' ≠ kv → red k kv' = 1

end GlobalTheory.LabPin

end
