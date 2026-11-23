import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners

noncomputable section

namespace Formalism.MainNotions.S.TieN

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SameFrameClass (D : D7) (Λ : Submodule (𝓞 D.host.E) (hS D).V) {T T' : D.host.E} (F : LFlag (hS D) D.R.rS T)
    (F' F'₂ : LFlag (hS D) D.R.rS T') : Prop :=
  ∃ n ∈ NLam Λ F, ∃ m ∈ NLam Λ F', ∀ b, frame F'₂ b = n (m (frame F' b))

def TermInj (D : D7) (X : TermTie D) (u u' : D.what₂.Word) : Prop :=
  ∀ t t' : D.s.Term u u', X.abelian₂ t = X.abelian₂ t' → SameFrameClass D (X.abelian₂ t) (X.fl t) (X.fl' t) (X.fl' t') → t = t'

def ATie (D : D7) (X : TermTie D) : Prop :=
  ∀ (u u' : D.what₂.Word) (t : D.s.Term u u'), X.Jt t = 0 → D.s.aTerm u u' t = 0

def AmpCov (D : D7) (X : TermTie D) : Prop :=
  (∀ (u u' : D.what₂.Word) (t : D.s.Term u u'), (X.fl t).fl.e = D.sp.hypE ∧ (X.fl t).fl.z = D.zmOf u) ∧
  ∃ (ρ : ∀ u : D.what₂.Word, ((D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) → (X.Hpi u →L[ℂ] X.Hpi u))
    (δ : ∀ u u' : D.what₂.Word, D.s.Term u u' → ((hS D).V ≃ₗ[D.host.E] (hS D).V)),
    (∀ u, ρ u 1 = ContinuousLinearMap.id ℂ (X.Hpi u) ∧
      ∀ h ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, ∀ h' ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, ρ u (h * h') = (ρ u h).comp (ρ u h')) ∧
    (∀ u u', u ≠ u' → ∀ P : X.Hpi u' →L[ℂ] X.Hpi u,
      (∀ h ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, (ρ u h).comp P = P.comp (ρ u' h)) → P = 0) ∧
    (∀ u u' (t : D.s.Term u u'), δ u u' t ∈ Formalism.HermitianLatticesTheory.isom (hS D).hT ∧
      (∀ a, δ u u' t (D.sp.hypE a) = (X.fl' t).fl.e a) ∧ δ u u' t (D.zmOf u') = (X.fl' t).fl.z) ∧
    ∀ u u' (t : D.s.Term u u'), ∀ σ ∈ Formalism.HermitianLatticesTheory.isom (hS D).hT,
      (∀ x ∈ Xplus (X.fl t) ⊔ Xplus (X.fl' t), σ x = x) →
      ∀ h ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, ∀ h' ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT,
        (∀ w, σ (D.sp.iXY 0 w) - D.sp.iXY 0 (h w) ∈ Submodule.span D.host.E (Set.range D.sp.hypE)) →
        (∀ w, ((δ u u' t)⁻¹ * σ * δ u u' t) (D.sp.iXY 0 w) - D.sp.iXY 0 (h' w) ∈
          Submodule.span D.host.E (Set.range D.sp.hypE)) →
        (ρ u h).comp (X.Jt t) = (X.Jt t).comp (ρ u' h')

section Mass

open Formalism.MainNotions.S.LocalSplitGroups

def RowMassIndep (D : D7) : Prop :=
  ∀ {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (s s' : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
    IsRowReps D F0 s → IsRowReps D F0 s' → ∑ Λ ∈ s, wRow D F0 Λ = ∑ Λ ∈ s', wRow D F0 Λ

def MassDef (D : D7) (X : TermTie D) (Z : TermLocs D X) : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (hA : ∀ p, Agree δ M p)
    (u u' : D.what₂.Word),
    ∃ (F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      F0.e = D.sp.hypE ∧ F0.z = D.zmOf u ∧ IsRowReps D F0 what₂ ∧
      (Z δ M hA u u').massTot = ∑ Λ ∈ what₂, Formalism.MainNotions.S.wRow D F0 Λ ∧
      ∀ γ, (Z δ M hA u u').massT γ = Formalism.MainNotions.S.wRow D F0 (X.abelian₂ γ) / (Z δ M hA u u').massTot

def TermInjAll (D : D7) (X : TermTie D) : Prop := ∀ u u', TermInj D X u u'

end Mass

section Cnt

open IsDedekindDomain MeasureTheory Formalism.MainNotions.S.LocalSplitGroups
open scoped BigOperators
open Classical

variable {D : D7} {X : TermTie D} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
  {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {u u' : D.what₂.Word}

def CntMassOK (Z : TermLoc D X δ M u u') (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  F0.e = D.sp.hypE ∧ F0.z = D.zmOf u ∧ IsRowReps D F0 what₂ ∧ Z.massTot = ∑ Λ ∈ what₂, wRow D F0 Λ ∧
    ∀ γ, Z.massT γ = wRow D F0 (X.abelian₂ γ) / Z.massTot

def CntOnReps (X : TermTie D) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (u' : D.what₂.Word) : Prop :=
  ∀ t : D.s.Term u u', X.abelian₂ t ∈ what₂ ∧ (X.fl t).fl = F0 ∧ FrameOK D (X.abelian₂ t) (X.fl' t)

def CntSurj (X : TermTie D) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (u' : D.what₂.Word) : Prop :=
  ∀ Λ ∈ what₂, ∀ F' : LFlag (hS D) D.R.rS ((Tu D u' : ℕ) : D.host.E),
    IsTerm Λ (gS D) (lf D F0) F' → FrameOK D Λ F' → IsGeneric Λ (gS D) (lf D F0) F' →
      Relevant D.host.F F0 F'.fl →
      ∃ t : D.s.Term u u', X.abelian₂ t = Λ ∧ SameFrameClass D Λ (lf D F0) (X.fl' t) F'

def IntLow {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E] [TopologicalSpace E]
    [MeasurableSpace E] (Mp : Loc.Model F E) {n : ℕ} (l : Matrix (Fin n) (Fin n) E) : Prop :=
  (∀ a, l a a = 1) ∧ (∀ a b, a < b → l a b = 0) ∧ ∀ a b, l a b ∈ Mp.R

def IntUp {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E] [TopologicalSpace E]
    [MeasurableSpace E] (Mp : Loc.Model F E) {n : ℕ} (ρ : Matrix (Fin n) (Fin n) E) : Prop :=
  (∀ a, ρ a a = 1) ∧ (∀ a b, b < a → ρ a b = 0) ∧ ∀ a b, ρ a b ∈ Mp.R

def cntPhaseP (Z : TermLoc D X δ M u u') (t : D.s.Term u u') (p : PlF D) : ℂ :=
  match modPt δ (D.mem u).A.T (D.mem u').A.T p (D.s.ptOf t) with
  | none => 0
  | some w₀ =>
    if h : ∃ xy : (Loc.IL (D.R.rS + 1) → (D.s.atP p).Ep) × (Loc.IN w₀ → (D.s.atP p).Ep),
        (Z.H p).ZZplus (Z.loc t p) =
          Loc.uLow xy.1 * modMat δ (D.mem u).A.T (D.mem u').A.T p (D.s.ptOf t) * Loc.uUp w₀ xy.2 then
      dfac M δ (D.mem u).A.T (D.mem u').A.T p (D.s.ptOf t) *
        (M p).psiR (Loc.simpleLow (Loc.uLow h.choose.1) + Loc.simpleUp (Loc.uUp w₀ h.choose.2))
    else 0

def cntWtP (Z : TermLoc D X δ M u u') (t : D.s.Term u u') (p : PlF D) : ℝ :=
  match modPt δ (D.mem u).A.T (D.mem u').A.T p (D.s.ptOf t) with
  | none => 0
  | some w₀ =>
    (((Measure.pi fun _ : Loc.IL (D.R.rS + 1) => (M p).mu).prod (Measure.pi fun _ : Loc.IN w₀ => (M p).mu))
      {xy | ∃ l ρ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep, IntLow (M p) l ∧ IntUp (M p) ρ ∧
        Loc.uLow xy.1 * modMat δ (D.mem u).A.T (D.mem u').A.T p (D.s.ptOf t) * Loc.uUp w₀ xy.2 =
          l * (Z.H p).ZZplus (Z.loc t p) * ρ}).toReal

structure CntOrb (Z : TermLoc D X δ M u u') : Type where
  orb : D.s.Term u u' → ℕ
  orb_pos : ∀ t, 0 < orb t

  orb_big : ∀ t, (∀ b ∈ (D.s.ptOf t).1, b.2 = 1) → orb t = 1

def CntCoefOK (Z : TermLoc D X δ M u u') (O : CntOrb Z) : Prop :=
  ∀ t : D.s.Term u u', D.s.generic t → D.s.relevant t → D.s.Gterm t ≠ 0 →
    D.s.cTerm t = (∏ᶠ p, cntPhaseP Z t p) * (O.orb t : ℂ) * ((∏ᶠ p, cntWtP Z t p : ℝ) : ℂ)

def CntTies (Z : TermLoc D X δ M u u') (O : CntOrb Z) : Prop :=
  (∃ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
    CntMassOK Z F0 what₂ ∧ CntOnReps X F0 what₂ u' ∧ CntSurj X F0 what₂ u') ∧
  TermInj D X u u' ∧ CntCoefOK Z O

theorem massDef_iff (D : D7) (X : TermTie D) (Z : TermLocs D X) :
    MassDef D X Z ↔ ∀ δ M hA u u', ∃ F0 what₂, CntMassOK (Z δ M hA u u') F0 what₂ := Iff.rfl

end Cnt

def PairValAt (D : D7) (X : TermTie D) {u u' : D.what₂.Word} (B : D.what₂.Tau → LocBessel D.R.k D.R.rS)
    (Vw : ∀ v, List (ℂ × ℕ) → ((B v).Wq →L[ℂ] (B v).Wp)) : Prop :=
  ∀ P : D.s.Pair u u', scalarP D.s P → D.s.Gterm (D.s.pfst P) ≠ 0 → D.s.Gterm (D.s.psnd P) ≠ 0 →
    D.s.relevant (D.s.pfst P) → D.s.relevant (D.s.psnd P) →
    D.s.pval P = (X.wRow P : ℂ) * D.s.cTerm (D.s.pfst P) * star (D.s.cTerm (D.s.psnd P)) *
      ∏ v, hsInner (Vw v (locBlocks D (rhoReal D) v (D.s.ptOf (D.s.pfst P)).1))
        (Vw v (locBlocks D (rhoReal D) v (D.s.ptOf (D.s.psnd P)).1))

section Cnt2

open IsDedekindDomain MeasureTheory Formalism.MainNotions.S.LocalSplitGroups
open scoped BigOperators
open Classical

variable {D : D7} {X : TermTie D} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
  {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {u u' : D.what₂.Word}

def NormFrame (Λ : Submodule (𝓞 D.host.E) (hS D).V) {T T' : D.host.E} (F : LFlag (hS D) D.R.rS T)
    (F' : LFlag (hS D) D.R.rS T') : Prop :=
  AdmWit Λ (gS D) F F' 1

def FrameFixingOrbitRelation (Λ : Submodule (𝓞 D.host.E) (hS D).V) {T : D.host.E} (F : LFlag (hS D) D.R.rS T)
    (f'' f''' : Fin (D.R.rS + 1) → (hS D).V) : Prop :=
  ∃ n ∈ NLam Λ F, (∀ a, n (frame F a) = frame F a) ∧ ∀ b, f''' b = n (f'' b)

def termEZ (X : TermTie D) (t : D.s.Term u u') (Zh : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) :
    Set (Fin (D.R.rS + 1) → (hS D).V) :=
  {f | ∃ F'' : LFlag (hS D) D.R.rS ((Tu D u' : ℕ) : D.host.E), frame F'' = f ∧ NormFrame (X.abelian₂ t) (X.fl t) F'' ∧
    SameFrameClass D (X.abelian₂ t) (X.fl t) (X.fl' t) F'' ∧ ZhatL (X.fl t) F'' = Zh}

def CntOrbOK (Z : TermLoc D X δ M u u') (O : CntOrb Z) : Prop :=
  ∀ t : D.s.Term u u', D.s.generic t → D.s.relevant t → D.s.Gterm t ≠ 0 →
    (∃ F'₁ : LFlag (hS D) D.R.rS ((Tu D u' : ℕ) : D.host.E), NormFrame (X.abelian₂ t) (X.fl t) F'₁ ∧
      SameFrameClass D (X.abelian₂ t) (X.fl t) (X.fl' t) F'₁) ∧
    ∀ F'₁ : LFlag (hS D) D.R.rS ((Tu D u' : ℕ) : D.host.E), NormFrame (X.abelian₂ t) (X.fl t) F'₁ →
      SameFrameClass D (X.abelian₂ t) (X.fl t) (X.fl' t) F'₁ →
      ((O.orb t : ℕ) : ℕ∞) = Set.encard {C : Set (Fin (D.R.rS + 1) → (hS D).V) |
        ∃ f ∈ termEZ X t (ZhatL (X.fl t) F'₁), C = {f' | f' ∈ termEZ X t (ZhatL (X.fl t) F'₁) ∧
          FrameFixingOrbitRelation (X.abelian₂ t) (X.fl t) f f'}}

def CntNormLoc (Z : TermLoc D X δ M u u') : Prop :=
  ∀ t : D.s.Term u u', D.s.generic t → ∀ p (g : Loc.SplitG (M p).L), (M p).split = some g →
    (Z.H p).Admissible g (Z.loc t p)

def CntTies2 (Z : TermLoc D X δ M u u') (O : CntOrb Z) : Prop :=
  CntTies Z O ∧ CntOrbOK Z O ∧ CntNormLoc Z

end Cnt2

section FromLoc

open Formalism.MainNotions.S.LocalSplitGroups

theorem rel_of_at {D : D7} {X : TermTie D} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {u u' : D.what₂.Word} (Z : TermLoc D X δ M u u')
    {γ : D.s.Term u u'} {w : Point D.host.E (D.R.rS + 1)} (h : D.s.ptOf γ = w)
    (hw : Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0) : D.s.Gterm γ ≠ 0 ∧ D.s.relevant γ := by
  exact (Z.G_pt γ).2 (by rw [h]; exact hw)

theorem massDef_of (D : D7) (X : TermTie D) (Z : TermLocs D X) : MassDef D X Z :=
  fun δ M hA u u' => (Z δ M hA u u').mass_def

theorem termInj_of {D : D7} {X : TermTie D} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {u u' : D.what₂.Word} (Z : TermLoc D X δ M u u') :
    TermInj D X u u' :=
  Z.term_inj

end FromLoc

def PairInj (D : D7) (X : TermTie D) (u u' : D.what₂.Word) : Prop :=
  ∀ p q : D.s.Pair u u', X.abelian₂ (D.s.pfst p) = X.abelian₂ (D.s.pfst q) →
    (∃ n' ∈ NLam (X.abelian₂ (D.s.pfst p)) (X.fl (D.s.pfst p)), ∃ n'' ∈ NLam (X.abelian₂ (D.s.pfst p)) (X.fl (D.s.pfst p)),
      ∃ m' ∈ NLam (X.abelian₂ (D.s.pfst p)) (X.fl' (D.s.pfst p)), ∃ m'' ∈ NLam (X.abelian₂ (D.s.pfst p)) (X.fl' (D.s.psnd p)),
      (∀ b, frame (X.fl' (D.s.pfst q)) b = n' (m' (frame (X.fl' (D.s.pfst p)) b))) ∧
      (∀ b, frame (X.fl' (D.s.psnd q)) b = n'' (m'' (frame (X.fl' (D.s.psnd p)) b))) ∧
      ∀ x ∈ orth (hS D) (Xsp (X.fl' (D.s.pfst q))),
        X.beta q x - n'' (X.beta p (n'.symm x)) ∈ Xsp (X.fl' (D.s.psnd q))) → p = q

def JtIrr (D : D7) (X : TermTie D) : Prop :=
  ∀ (u u' : D.what₂.Word) (t : D.s.Term u u'), ¬ D.s.relevant t → X.Jt t = 0

theorem aTerm_irr {D : D7} {X : TermTie D} (hA : ATie D X) (hJ : JtIrr D X) (u u' : D.what₂.Word) (t : D.s.Term u u')
    (h : ¬ D.s.relevant t) : D.s.aTerm u u' t = 0 :=
  hA u u' t (hJ u u' t h)

section Orb

open MeasureTheory Matrix Formalism.QuantumDeterminants

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {Cw : ℝ}

structure RealFr (Y : LoopTie D large₂ X u u' Cw) where
  re : D.what₂.Tau → (hS D).V → (Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
  re_add : ∀ τ x y, re τ (x + y) = re τ x + re τ y
  re_smul : ∀ τ (a : D.host.E) x, re τ (a • x) = embS D τ a • re τ x
  re_form : ∀ τ x y, herm (Hpk D.R.k D.R.rS) (re τ x) (re τ y) = embS D τ (brS (hS D) x y)
  re_F : ∀ τ a, ((rhoF D a : ℝ) : ℂ) • re τ (Y.F0.fvec a) = fvec D.R.k D.R.rS (Y.W τ).z a
  re_F' : ∀ (t : D.s.Term u u') τ b, ((rhoF D b : ℝ) : ℂ) • re τ (frame (X.fl' t) b) =
    (Y.γ t τ) *ᵥ fvec D.R.k D.R.rS (Y.W τ).z' b
  mat : D.what₂.Tau → ((hS D).V ≃ₗ[D.host.E] (hS D).V) → MatKR D.R.k D.R.rS
  mat_re : ∀ τ n x, mat τ n *ᵥ re τ x = re τ (n x)

def RO (X : TermTie D) (t : D.s.Term u u') : Set ((hS D).V ≃ₗ[D.host.E] (hS D).V) :=
  {n | n ∈ NLam (X.abelian₂ t) (X.fl t) ∧ n ∈ NLam (X.abelian₂ t) (X.fl' t)}

def rAt {Y : LoopTie D large₂ X u u' Cw} (Rf : RealFr Y) (t : D.s.Term u u') (τ : D.what₂.Tau)
    (n : (hS D).V ≃ₗ[D.host.E] (hS D).V) : MatKR D.R.k D.R.rS :=
  (Y.γ t τ)⁻¹ * Rf.mat τ n * Y.γ t τ

def IsCovolR {Y : LoopTie D large₂ X u u' Cw} (Rf : RealFr Y) (t : D.s.Term u u')
    (μR : D.what₂.Tau → Measure (Mt D.R.k D.R.rS)) (c : ℝ) : Prop :=
  ∃ 𝔉 : Set (D.what₂.Tau → Mt D.R.k D.R.rS), MeasurableSet 𝔉 ∧
    (∀ x : D.what₂.Tau → Mt D.R.k D.R.rS, (∀ τ, Matrix.of (x τ) ∈ Rset D.R.k D.R.rS (Y.γ t τ)) →
      ∃! n, n ∈ RO X t ∧ (fun τ => fun i j => (rAt Rf t τ n * Matrix.of (x τ)) i j) ∈ 𝔉) ∧
    (Measure.pi μR) 𝔉 = ENNReal.ofReal c

def OrbMeas {Y : LoopTie D large₂ X u u' Cw} (Rf : RealFr Y) (t : D.s.Term u u')
    (μR νR : D.what₂.Tau → Measure (Mt D.R.k D.R.rS)) (c : ℝ) : Prop :=
  0 < c ∧ (∀ τ, IsHaarOn (Rset D.R.k D.R.rS (Y.γ t τ)) (μR τ) ∧ IsQuotMeas (Y.W τ).μG (μR τ) (νR τ)) ∧ IsCovolR Rf t μR c

def JtOrbTie {Y : LoopTie D large₂ X u u' Cw} (Rf : RealFr Y) : Prop :=
  ∀ t : D.s.Term u u', D.s.relevant t → D.s.Gterm t = 0 → ¬ D.s.isId t →
    (∀ τ, Y.γ t τ ∈ UH (Hpk D.R.k D.R.rS)) ∧
    (∃ μR νR c, OrbMeas Rf t μR νR c) ∧
    ∀ μR νR c, OrbMeas Rf t μR νR c →
      hsNormSq (X.Jt t) = c ^ 2 * ∏ τ, hsNormSq ((Y.A τ).J (νR τ) (Y.γ t τ))

def IsCovolN {Y : LoopTie D large₂ X u u' Cw} (Rf : RealFr Y) (t : D.s.Term u u') (c : ℝ) : Prop :=
  ∃ 𝔉 : Set (D.what₂.Tau → Mt D.R.k D.R.rS), MeasurableSet 𝔉 ∧
    (∀ x : D.what₂.Tau → Mt D.R.k D.R.rS, (∀ τ, Matrix.of (x τ) ∈ Nset D.R.k D.R.rS) →
      ∃! n, n ∈ NLam (X.abelian₂ t) (X.fl t) ∧ (fun τ => fun i j => (Rf.mat τ n * Matrix.of (x τ)) i j) ∈ 𝔉) ∧
    (Measure.pi fun τ => (Y.W τ).μN) 𝔉 = ENNReal.ofReal c

def NVolOne {Y : LoopTie D large₂ X u u' Cw} (Rf : RealFr Y) : Prop := ∀ t : D.s.Term u u', IsCovolN Rf t 1

def JtOrbOK (Y : LoopTie D large₂ X u u' Cw) : Prop := ∃ Rf : RealFr Y, JtOrbTie Rf

def JtOrbOKN (Y : LoopTie D large₂ X u u' Cw) : Prop := ∃ Rf : RealFr Y, NVolOne Rf ∧ JtOrbTie Rf

theorem JtOrbOKN.ok {Y : LoopTie D large₂ X u u' Cw} (h : JtOrbOKN Y) : JtOrbOK Y := by
  obtain ⟨Rf, -, hR⟩ := h
  exact ⟨Rf, hR⟩

end Orb

end Formalism.MainNotions.S.TieN
