import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharLocalEqInvTypeCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevQFiniteIndexAndRoot
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalUnfoldingNonvanishingIffEventuallyNonzero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalUnfoldingIntegrandBoundedSchwartz
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastTwoStepsGuarded
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralGlReductionModPrime

noncomputable section

namespace GlobalTheory.Mem.Col2.IdxEx

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal

variable {X : Fields} {Pr : Primes X} {R : Ranks}

variable (Pr) in

def admitted (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (h : AutY X R j) : Prop :=
  (P ∈ Pr.vGs → h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P)) ∧ (P ∉ Pr.vGs → Between j P h)

theorem isAdmissibleIntegralBasisChange_one (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) : admitted Pr j P (1 : AutY X R j) :=
  ⟨fun _ => one_mem _, fun hP => between_of_nf hP (IndefiniteRowSideFullHecke.SandwichNormalForm.nf_one j hP)⟩

def nfMat {E : Type} [Field E] (n c : ℕ) (q : E) (e : Fin c → ℤ) (z : Fin n → E) : Matrix (Fin (n + c)) (Fin (n + c)) E :=
  fun l s => if hs : s.1 < n then (if l = s then 1 else 0)
    else q ^ e ⟨s.1 - n, by omega⟩ * ((if l = s then 1 else 0) + if s.1 = n then Loc.inX E n c z l else 0)

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

abbrev CAt (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j) : Subgroup (AutY X R j) :=
  Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) h

def ChiMul (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j) : Prop :=
  (∀ r ∈ CAt sel mu cst j P h, chiInv Ch sel mu cst j P h r ≠ 0) ∧
    ∀ r ∈ CAt sel mu cst j P h, ∀ r' ∈ CAt sel mu cst j P h,
      chiInv Ch sel mu cst j P h (r * r') = chiInv Ch sel mu cst j P h r * chiInv Ch sel mu cst j P h r'

def ChiTriv (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j) : Prop :=
  ∀ r ∈ CAt sel mu cst j P h, r ∈ Loc.fixX X.E (R.N j) (cOf R j) → chiInv Ch sel mu cst j P h r = 1

def GrpG (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j) (lev : Lev (𝓞 X.E ⧸ P.1.asIdeal) X.K (R.N j)) : Prop :=
  ∀ hbar : GL (Fin (R.N j)) (𝓞 X.E ⧸ P.1.asIdeal), hbar ∈ lev.H ↔ ∃ g ∈ prCat (Pr := Pr) cst.sharp j P.1 h,
    ∀ x ∈ stdAt X.E (R.N j) P.1, redV P.1 (g x) = hbar.1.mulVec (redV P.1 x)

def ChrG (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j) (lev : Lev (𝓞 X.E ⧸ P.1.asIdeal) X.K (R.N j)) : Prop :=
  ∀ (hbar : ↥lev.H) (g : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)) (r : AutY X R j), r ∈ CAt sel mu cst j P h →
    (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (g x)) →
    (∀ x ∈ stdAt X.E (R.N j) P.1, redV P.1 (g x) = hbar.1.1.mulVec (redV P.1 x)) →
    ((lev.lam hbar : X.Kˣ) : X.K) = chiInv Ch sel mu cst j P h r

def GrpQ (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j) (lev : LevI X.E X.K (R.N j) P.1) : Prop :=
  lev.H = (prCat (Pr := Pr) cst.sharp j P.1 h).subgroupOf (GLint X.E (R.N j) P.1)

def ChrQ (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j) (lev : LevI X.E X.K (R.N j) P.1) : Prop :=
  ∀ (g : ↥lev.H) (r : AutY X R j), r ∈ CAt sel mu cst j P h →
    (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (g.1.1 x)) →
    ((lev.lam g : X.Kˣ) : X.K) = chiInv Ch sel mu cst j P h r

theorem exists_char {G H K : Type} [Group G] [Group H] [Field K] (C : Subgroup G) (χ : G → K) (Rel : G → H → Prop)
    (hne : ∀ r ∈ C, χ r ≠ 0) (hmul : ∀ r ∈ C, ∀ r' ∈ C, χ (r * r') = χ r * χ r')
    (hs : ∀ h, ∃ r ∈ C, Rel r h) (hm : ∀ r h r' h', Rel r h → Rel r' h' → Rel (r * r') (h * h'))
    (hw : ∀ h, ∀ r ∈ C, ∀ r' ∈ C, Rel r h → Rel r' h → χ r = χ r') :
    ∃ lam : H →* Kˣ, ∀ h, ∀ r ∈ C, Rel r h → ((lam h : Kˣ) : K) = χ r := by
  choose s hsC hsR using hs
  refine ⟨MonoidHom.mk' (fun h => Units.mk0 (χ (s h)) (hne _ (hsC h))) fun a b => Units.ext ?_, fun h r hr hR => ?_⟩
  · simp only [Units.val_mk0, Units.val_mul]
    rw [← hmul _ (hsC a) _ (hsC b)]
    exact hw _ _ (hsC _) _ (mul_mem (hsC a) (hsC b)) (hsR _) (hm _ _ _ _ (hsR a) (hsR b))
  · exact hw _ _ (hsC _) _ hr (hsR _) hR

end GlobalTheory.Mem.Col2.IdxEx

end
