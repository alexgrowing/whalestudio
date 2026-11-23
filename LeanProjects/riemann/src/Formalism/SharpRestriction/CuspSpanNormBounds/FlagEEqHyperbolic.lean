import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale

noncomputable section

namespace Formalism.MainNotions.S

open NumberField Formalism.BasicNotions Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ZhatOM {K : Type*} [CommRing K] {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  fun a b => (-1) ^ (r - b.val) * Z a b

structure TermTie (D : D7) : Type 1 where

  abelian₂ : ∀ {u u' : D.what₂.Word}, D.s.Term u u' → Submodule (𝓞 D.host.E) (hS D).V

  fl : ∀ {u u' : D.what₂.Word}, D.s.Term u u' → LFlag (hS D) D.R.rS ((Tu D u : ℕ) : D.host.E)
  fl' : ∀ {u u' : D.what₂.Word}, D.s.Term u u' → LFlag (hS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)

  fixed : ∀ {u u'} (t : D.s.Term u u'), FixedHyp D (abelian₂ t) (fl t)
  lift' : ∀ {u u'} (t : D.s.Term u u'), IsLift (abelian₂ t) (fl' t)
  adm : ∀ {u u'} (t : D.s.Term u u'), IsAdmissible (abelian₂ t) (gS D) (fl t) (fl' t)

  conv' : ∀ {u u'} (t : D.s.Term u u'), IsFixedConv (abelian₂ t) (gS D) (fl' t)

  inS_iff : ∀ {u u'} (t : D.s.Term u u'), D.s.inS t ↔
    (∀ a : Fin D.R.rS, (fl' t).fl.e a - (fl t).fl.e a ∈ Xflag (fl t) a.val) ∧ (fl' t).fl.z - (fl t).fl.z ∈ Xsp (fl t)

  isId_iff : ∀ {u u'} (t : D.s.Term u u'), D.s.isId t ↔
    ∃ n ∈ NLam (abelian₂ t) (fl t), (∀ a, n ((fl t).fl.e a) = (fl' t).fl.e a) ∧ n (fl t).fl.z - (fl' t).fl.z ∈ Xsp (fl t)

  G_eq : ∀ {u u'} (t : D.s.Term u u'), algebraMap D.host.F D.host.E (D.s.Gterm t) = Gval (fl t) (fl' t)

  rel_iff : ∀ {u u'} (t : D.s.Term u u'), D.s.relevant t ↔ Relevant D.host.F (fl t).fl (fl' t).fl

  FeqF_iff : ∀ {u u'} (t : D.s.Term u u'), D.s.FeqF t ↔
    ∃ n ∈ NLam (abelian₂ t) (fl t), ∀ a, n (frame (fl t) a) = frame (fl' t) a

  id_G : ∀ {u u'} (t : D.s.Term u u'), D.s.isId t → D.s.Gterm t = 0

  gen_iff : ∀ {u u'} (t : D.s.Term u u'), D.s.generic t ↔ IsGeneric (abelian₂ t) (gS D) (fl t) (fl' t)

  pt_cell : ∀ {u u'} (t : D.s.Term u u'), D.s.Gterm t ≠ 0 → D.s.relevant t →
    IsInCell (ZhatOM (ZhatL (fl t) (fl' t))) (D.s.ptOf t)

  pLam : ∀ {u u'} (p : D.s.Pair u u'), abelian₂ (D.s.pfst p) = abelian₂ (D.s.psnd p)
  pfl : ∀ {u u'} (p : D.s.Pair u u'), fl (D.s.pfst p) = fl (D.s.psnd p)

  beta : ∀ {u u'}, D.s.Pair u u' → ((hS D).V ≃ₗ[D.host.E] (hS D).V)
  isPair : ∀ {u u'} (p : D.s.Pair u u'),
    IsPair (abelian₂ (D.s.pfst p)) (fl (D.s.pfst p)) (fl' (D.s.pfst p)) (fl' (D.s.psnd p)) (beta p) (gS D)

  s0_eq : ∀ {u u'} (p : D.s.Pair u u'), D.s.s0 p =
    Lat.s0 (abelian₂ (D.s.pfst p)) (fl (D.s.pfst p)) (fl' (D.s.pfst p)) (fl' (D.s.psnd p)) (beta p) D.R.k

  scal_iff : ∀ {u u'} (p : D.s.Pair u u'), D.s.s0 p = 1 → (D.s.scalarPair p ↔
    IsScalar (abelian₂ (D.s.pfst p)) (fl (D.s.pfst p)) (fl' (D.s.pfst p)) (fl' (D.s.psnd p)) (beta p))

  wRow : ∀ {u u'}, D.s.Pair u u' → ℝ
  wRow_pos : ∀ {u u'} (p : D.s.Pair u u'), 0 < wRow p
  chi : ∀ {u u'}, D.s.Pair u u' → ℂ
  chi_norm : ∀ {u u'} (p : D.s.Pair u u'), ‖chi p‖ = 1
  Hpi : D.what₂.Word → Type
  [hpN : ∀ u, NormedAddCommGroup (Hpi u)]
  [hpI : ∀ u, InnerProductSpace ℂ (Hpi u)]
  [hpF : ∀ u, FiniteDimensional ℂ (Hpi u)]
  Hpi_dim : ∀ u, (Module.finrank ℂ (Hpi u) : ℝ) = dimPi (hc := D.hcW) u
  Jt : ∀ {u u'}, D.s.Term u u' → (Hpi u' →L[ℂ] Hpi u)
  piB : ∀ {u u'}, D.s.Pair u u' → (Hpi u' →L[ℂ] Hpi u')
  piB_unit : ∀ {u u'} (p : D.s.Pair u u') (x : Hpi u'), ‖piB p x‖ = ‖x‖
  pval_eq : ∀ {u u'} (p : D.s.Pair u u'), D.s.pval p =
    (wRow p : ℂ) * chi p * hsInner ((Jt (D.s.pfst p)).comp (piB p)) (Jt (D.s.psnd p))

attribute [instance] TermTie.hpN TermTie.hpI TermTie.hpF

section Rows

open MeasureTheory

variable (D : D7)

abbrev lf {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) : LFlag (VS D) D.R.rS T := ⟨F0, F0.z⟩

def stabF {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V) :=
  {γ | γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ (∀ j, (F0.Xa j).map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) = F0.Xa j) ∧
    γ F0.z = F0.z}

def XS {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) : Submodule (𝓞 D.host.E) (VS D).V :=
  Submodule.span (𝓞 D.host.E)
    {y | ∃ (a : Fin D.R.rS) (x : D.host.E),
      x ∈ (ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ∧
        y = x • F0.e a}

def IsRowLat {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V) : Prop :=
  Λ ∈ Formalism.HermitianLatticesTheory.genus (VS D).hT (VS D).L0 ∧ FixedHyp D Λ (lf D F0) ∧ XLam Λ (lf D F0) = XS D F0

def IsRowReps {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (s : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  (∀ Λ ∈ s, IsRowLat D F0 Λ) ∧
  ∀ Λ, IsRowLat D F0 Λ → ∃! Λ', Λ' ∈ s ∧ ∃ γ ∈ stabF D F0, Formalism.HermitianLatticesTheory.gmap γ Λ' = Λ

abbrev WbQ {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) : Type :=
  ↥(perpS (VS D) F0.X) ⧸ F0.X.comap (perpS (VS D) F0.X).subtype

def autLz {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    Set (WbQ D F0 → WbQ D F0) :=
  {φ | ∃ γ ∈ stabF D F0, Formalism.HermitianLatticesTheory.gmap γ Λ = Λ ∧
    ∀ (x : perpS (VS D) F0.X) (hx : γ x.1 ∈ perpS (VS D) F0.X),
      φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨γ x.1, hx⟩}

def wRow {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V) : ℝ :=
  ((Nat.card (autLz D F0 Λ) : ℝ))⁻¹

def FrameOK {T' : D.host.E} (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F' : LFlag (VS D) D.R.rS T') : Prop :=
  IsFixedConv Λ (gS D) F' ∧ XLam Λ F' = XS D F'.fl

def FrameEqv {T' : D.host.E} (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (F' F'₂ : LFlag (VS D) D.R.rS T') : Prop :=
  ∃ ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E),
    (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ frame F'₂ = frameAct (fun a => n (frame F' a)) ξ

def cntSW {T : D.host.E} (T' : D.host.E) (F : LFlag (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (Z : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) : ℕ∞ :=
  let X : Set (LFlag (VS D) D.R.rS T') :=
    {F' | IsTerm Λ (gS D) F F' ∧ FrameOK D Λ F' ∧ IsGeneric Λ (gS D) F F' ∧ ZEquiv (ZhatL F F') Z}
  Set.encard {O : Set (LFlag (VS D) D.R.rS T') | ∃ F' ∈ X, O = {F'' | F'' ∈ X ∧
    ∃ n ∈ NLam Λ F, FrameEqv D n F' F''}}

end Rows

section Loop

open MeasureTheory

def rhoF (D : D7) (a : Fin (D.R.rS + 1)) : ℝ := D.host.rdE ^ (-((D.R.rS : ℝ) - (a : ℕ)))

structure LoopTie (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (u u' : D.what₂.Word) (C1 : ℝ) : Type 1 where
  F0 : FlagG (VS D) D.R.rS (Tu D u : D.host.E)
  flag_e_eq_hyperbolic : F0.e = D.sp.hypE
  formsAtZero : F0.z = D.zmOf u
  what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)
  isRows : IsRowReps D F0 what₂
  fl_eq : ∀ t : D.s.Term u u', X.fl t = lf D F0
  Lam_mem : ∀ t : D.s.Term u u', X.abelian₂ t ∈ what₂
  frame_ok : ∀ t : D.s.Term u u', FrameOK D (X.abelian₂ t) (X.fl' t)
  wRow_eq : ∀ p : D.s.Pair u u', X.wRow p = wRow D F0 (X.abelian₂ (D.s.pfst p))
  pair_inj : ∀ p q : D.s.Pair u u', X.abelian₂ (D.s.pfst p) = X.abelian₂ (D.s.pfst q) →
    (∃ n' ∈ NLam (X.abelian₂ (D.s.pfst p)) (lf D F0), ∃ n'' ∈ NLam (X.abelian₂ (D.s.pfst p)) (lf D F0),
      FrameEqv D n' (X.fl' (D.s.pfst p)) (X.fl' (D.s.pfst q)) ∧
      FrameEqv D n'' (X.fl' (D.s.psnd p)) (X.fl' (D.s.psnd q)) ∧
      ∀ x ∈ orth (hS D) (Xsp (X.fl' (D.s.pfst q))),
        X.beta q x - n'' (X.beta p (n'.symm x)) ∈ Xsp (X.fl' (D.s.psnd q))) → p = q
  θ : ℝ

  θ_win : normWin D large₂ C1 θ
  W : D.what₂.Tau → LocW D.R.k D.R.rS
  goodW : ∀ τ, GoodW D τ u u' θ (W τ)
  A : ∀ τ, LocS (W τ)
  goodS : ∀ τ, GoodS D (lamD D τ) (A τ)
  deg_eq : ∀ τ, (A τ).deg = D.dsig τ
  γ : D.s.Term u u' → D.what₂.Tau → MatKR D.R.k D.R.rS
  pt : D.s.Term u u' → D.what₂.Tau → Point ℂ (D.R.rS + 1)
  θR : D.s.Term u u' → D.what₂.Tau → ℝ
  νR : D.s.Term u u' → D.what₂.Tau → Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)
  volR : D.s.Term u u' → ℝ
  volR_pos : ∀ t, 0 < volR t
  gram : ∀ (t : D.s.Term u u') τ a b, Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (W τ).z (W τ).z' (γ t τ) a b =
    ((rhoF D a * rhoF D b : ℝ) : ℂ) * embS D τ (ZhatL (X.fl t) (X.fl' t) a b)
  rel : ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t → ∀ τ,
    RelPt D (W τ).z (W τ).z' (γ t τ) (pt t τ) ∧ normWin D large₂ C1 (θR t τ) ∧
      RMeas D (W τ) (γ t τ) (θR t τ) (νR t τ)
  J_irr : ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → ¬ D.s.relevant t → X.Jt t = 0
  J_norm : ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t →
    hsNormSq (X.Jt t) = volR t ^ 2 * ∏ τ, hsNormSq ((A τ).J (νR t τ) (γ t τ))

end Loop

end Formalism.MainNotions.S
