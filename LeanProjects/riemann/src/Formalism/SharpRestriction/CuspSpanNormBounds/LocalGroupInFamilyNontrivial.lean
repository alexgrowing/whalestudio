import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Formalism.SharpRestriction.CuspSpanNormBounds.LinQRawRange
import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic

noncomputable section

namespace Formalism.MainNotions.S.LocalSplitGroups

open NumberField IsDedekindDomain Formalism.MainNotions.S ValuativeRel
open scoped BigOperators ComplexOrder
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : Formalism.BasicNotions.D7)

abbrev PlF : Type := HeightOneSpectrum (𝓞 D.host.F)

variable {D : Formalism.BasicNotions.D7}

def gpart (p : PlF D) : ℕ :=
  if Loc.resChar p = D.host.g 0 then D.host.g 0
  else if Loc.resChar p = D.host.g 1 then D.host.g 1 else 1

def uP (p : PlF D) : ℚ := (gpart p : ℚ) / (Lat.gS D : ℚ)

def qE (p : PlF D) : (D.s.atP p).Ep :=
  match (D.s.atP p).split with
  | some sg => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (sg.q : (D.s.atP p).Fp)
  | none => 1

def twist (p : PlF D) (s : ℕ) (x : (D.s.atP p).Ep) : (D.s.atP p).Ep :=
  match (D.s.atP p).split with
  | some sg => sg.e.symm ((sg.e x).1, (-1) ^ s * (sg.e x).2)
  | none => x

def nu (r i j : ℕ) : ℕ := 2 * (r + 1) - i - j

def tMod (δ : ∀ p, (D.s.atP p).Fp) (p : PlF D) (ν s : ℕ) (t : D.host.E) : (D.s.atP p).Ep :=
  Ring.inverse ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)) ^ ν) *
    twist p s ((D.s.atP p).ιE t) * Ring.inverse (qE p)

def tau0 (p : PlF D) (T T' : ℕ) : (D.s.atP p).Ep :=
  match (D.s.atP p).split with
  | some sg => sg.e.symm (-(T : (D.s.atP p).Fp), (T' : (D.s.atP p).Fp)) * Ring.inverse (qE p)
  | none => 0

def blkMod (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (a s : ℕ) (t : D.host.E) : (D.s.atP p).Ep :=
  tMod δ p (nu D.R.rS a (a + s - 1)) s t -
    (if a + s - 1 = D.R.rS + 1 ∧ s = 1 then tau0 p T T' else 0)

def nSh {A : Type} [Ring A] (c : A) : ℕ :=
  if hc : ∃ n : Fin 3, IsUnit (c + (((n : Fin 3) : ℕ) : A)) then ((hc.choose : Fin 3) : ℕ) else 0

def blkTop (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (a s : ℕ) (t : D.host.E) : (D.s.atP p).Ep :=
  if a + s - 1 = D.R.rS + 1 ∧ s = 1 then
    blkMod δ T T' p a s t + ((nSh (blkMod δ T T' p a s t) : ℕ) : (D.s.atP p).Ep)
  else blkMod δ T T' p a s t

def mapBlocks {A B : Type} (f : ℕ → ℕ → A → B) : ℕ → List (A × ℕ) → List (B × ℕ)
  | _, [] => []
  | a, (t, s) :: rest => (f a s t, s) :: mapBlocks f (a + s) rest

def modBlocks {A B : Type} [Monoid B] (f : ℕ → ℕ → A → B) : ℕ → List (A × ℕ) → Option (List (Bˣ × ℕ+))
  | _, [] => some []
  | a, (t, s) :: rest =>
    if h : IsUnit (f a s t) ∧ 0 < s then
      (modBlocks f (a + s) rest).map (fun l => (h.1.unit, ⟨s, h.2⟩) :: l)
    else none

def modPt (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) {n : ℕ} (w : Point D.host.E n) :
    Option (Loc.Pt (D.s.atP p).Ep n) :=
  match modBlocks (blkTop δ T T' p) 1 w.1 with
  | none => none
  | some l => if h : (l.map (fun b => (b.2 : ℕ))).sum = n then some ⟨l, h⟩ else none

def modMat (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) {n : ℕ} (w : Point D.host.E n) :
    Matrix (Fin n) (Fin n) (D.s.atP p).Ep :=
  fun a b => ptEntry (mapBlocks (blkMod δ T T' p) 1 w.1) a.val b.val

variable (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)

def locK (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (n : ℕ) (w w' : Point D.host.E n) : ℂ :=
  match modPt δ T T' p w, modPt δ T T' p w' with
  | some a, some b => (M p).Kk n a b
  | _, _ => 0

def detNrmP (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) {n : ℕ} (h : Point D.host.E n) : ℝ :=
  match modPt δ T T' p h with
  | some a => (M p).detMod a
  | none => 0

def ptApp {n : ℕ} (h : Point D.host.E n) (t : D.host.E) (ht : t ≠ 0) (s : ℕ) (hs : 1 ≤ s) :
    Point D.host.E (n + s) :=
  ⟨h.1 ++ [(t, s)], fun b hb => by
    rcases List.mem_append.1 hb with hb | hb
    · exact h.2.1 b hb
    · simp at hb; subst hb; exact ⟨ht, hs⟩, by simp [h.2.2]⟩

def Dmin {n : ℕ} (w : Point D.host.E n) (l : ℕ) : D.host.E :=
  if hl : l ≤ n then ((ptMat w).submatrix (Fin.castLE hl) (Fin.castLE hl)).det else 0

def zetaOf (w : Point D.host.E (D.R.rS + 1)) : D.host.E := Dmin w (D.R.rS + 1) / Dmin w D.R.rS

def kind (w : Point D.host.E (D.R.rS + 1)) : Option D.host.E :=
  if Dmin w D.R.rS = 0 then none else some (zetaOf w)

def dfac (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) : ℂ :=
  match (D.s.atP p).split, w.1.getLast? with
  | some _, some (t, 2) => (M p).psiR (tau0 p T T' * Ring.inverse (blkMod δ T T' p D.R.rS 2 t))
  | _, _ => 1

def KtopP (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (w w' : Point D.host.E (D.R.rS + 1)) : ℂ :=
  dfac M δ T T' p w * locK M δ T T' p (D.R.rS + 1) w w' * starRingEnd ℂ (dfac M δ T T' p w')

def Ktop (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (w w' : Point D.host.E (D.R.rS + 1)) : ℂ :=
  if kind w = kind w' then KtopP M δ T T' p w w' else 0

def KtopG (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (w w' : Point D.host.E (D.R.rS + 1)) : ℂ :=
  if kind w = kind w' then ∏ᶠ p, KtopP M δ T T' p w w' else 0

def Gpt (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) : D.host.E :=
  Dmin w (D.R.rS + 1) * D.conjF (Dmin w (D.R.rS + 1)) -
    (T : D.host.E) * T' * (Dmin w D.R.rS * D.conjF (Dmin w D.R.rS))

def TotPos (x : D.host.E) : Prop := ∀ τ : D.what₂.Tau, 0 < (D.host.emb (D.eTau τ) x).re

def n0 (c : ℝ) (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) : ℝ :=
  c * (Real.sqrt |((Algebra.norm ℚ (Gpt T T' w / ((Lat.gS D : D.host.E) ^ D.R.m)) : ℚ) : ℝ)|) ^ (D.R.k - 1)

def gdd (a b : ℤ) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  FractionalIdeal.spanSingleton _ ((Lat.gS D : D.host.E) ^ a) *
    ((D.host.ddE : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ^ b)

def La (δ : ∀ p, (D.s.atP p).Fp) (ν s : ℕ) : Set D.host.E :=
  {t | ∀ p, tMod δ p ν s t ∈ (M p).R}

def dualPsiG (S : Set D.host.E) : Set D.host.E :=
  {l | ∀ t ∈ S, ∃ z : ℤ, Algebra.trace ℚ D.host.E (l * t / (Lat.gS D : D.host.E)) = z}

def LaP (ν s : ℕ) : Set D.host.E :=
  {x | x ∈ gdd (D := D) (-1) (-(ν : ℤ)) ∧ x - (-1) ^ s * D.conjF x ∈ gdd (D := D) 0 (-(ν : ℤ))}

def frFac (δ : ∀ p, (D.s.atP p).Fp) (p : PlF D) (a : Fin (D.R.rS + 1)) : (D.s.atP p).Ep :=
  Ring.inverse ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)) ^
    (D.R.rS - a.val))

structure TermLoc (D : Formalism.BasicNotions.D7) (Y : TermTie D) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (u u' : D.what₂.Word) : Type 1 where
  V : PlF D → Type
  [acg : ∀ p, AddCommGroup (V p)]
  [mod : ∀ p, Module (D.s.atP p).Ep (V p)]
  H : ∀ p, Loc.HermSp (M p) (V p)

  rank : ∀ p, Module.finrank (D.s.atP p).Ep (V p) = D.R.r

  bc : ∀ p, (Lat.hS D).V →+ V p
  bc_smul : ∀ p (a : D.host.E) (x : (Lat.hS D).V), bc p (a • x) = (D.s.atP p).ιE a • bc p x
  bc_span : ∀ p, Submodule.span (D.s.atP p).Ep (Set.range (bc p)) = ⊤
  bc_form : ∀ p (x y : (Lat.hS D).V), (H p).h (bc p x) (bc p y) = (D.s.atP p).ιE (brS (Lat.hS D) x y)

  sgn : ∀ p, Fin (D.R.rS + 1) → (D.s.atP p).Ep
  sgn' : ∀ p, Fin (D.R.rS + 1) → (D.s.atP p).Ep
  sgn_sq : ∀ p a, sgn p a * sgn p a = 1 ∧ sgn' p a * sgn' p a = 1

  loc : D.s.Term u u' → ∀ p, Loc.Term (V p) (M p) D.R.rS

  loc_Lam : ∀ γ p, (loc γ p).abelian₂ = Submodule.span (M p).L.O (bc p '' (Y.abelian₂ γ : Set (Lat.hS D).V))

  loc_f : ∀ γ p a, (loc γ p).f a = (sgn p a * frFac δ p a) • bc p (Lat.frame (Y.fl γ) a)

  loc_f' : ∀ γ p, ∃ ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E),
    (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧
    ∀ b, (loc γ p).f' b = (sgn' p b * frFac δ p b) • bc p (Lat.frameAct (Lat.frame (Y.fl' γ)) ξ b)

  local_group_in_family_nontrivial : ∀ γ p, (loc γ p).T = ((D.mem u).A.T : (D.s.atP p).Fp) ∧
    (loc γ p).T' = ((D.mem u').A.T : (D.s.atP p).Fp)

  G_pt : ∀ γ : D.s.Term u u', (D.s.Gterm γ ≠ 0 ∧ D.s.relevant γ) ↔
    Gpt (D.mem u).A.T (D.mem u').A.T (D.s.ptOf γ) ≠ 0

  generic_iff : ∀ γ : D.s.Term u u', D.s.Gterm γ ≠ 0 → (D.s.generic γ ↔ ∀ p, (H p).IsGeneric (loc γ p))

  at_pt : ∀ γ : D.s.Term u u', D.s.generic γ → D.s.Gterm γ ≠ 0 → D.s.relevant γ → ∀ p,
    ∃ uL uU : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep,
      (∀ a, uL a a = 1 ∧ uU a a = 1) ∧ (∀ a b, a < b → uL a b = 0 ∧ uU b a = 0) ∧
      (H p).ZZplus (loc γ p) = uL * modMat δ (D.mem u).A.T (D.mem u').A.T p (D.s.ptOf γ) * uU

  scalar_loc : ∀ P : D.s.Pair u u', Formalism.MainNotions.S.scalarP D.s P → D.s.Gterm (D.s.pfst P) ≠ 0 →
    D.s.Gterm (D.s.psnd P) ≠ 0 → ∀ p, (H p).IsScalarPair (loc (D.s.pfst P) p) (loc (D.s.psnd P) p)

  massT : D.s.Term u u' → ℝ
  massT_nonneg : ∀ γ, 0 ≤ massT γ

  massTot : ℝ
  massTot_pos : 0 < massTot

  mass_def : ∃ (F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
    F0.e = D.sp.hypE ∧ F0.z = D.zmOf u ∧ IsRowReps D F0 what₂ ∧ massTot = ∑ Λ ∈ what₂, Formalism.MainNotions.S.wRow D F0 Λ ∧
      ∀ γ, massT γ = Formalism.MainNotions.S.wRow D F0 (Y.abelian₂ γ) / massTot

  term_inj : ∀ γ γ' : D.s.Term u u', Y.abelian₂ γ = Y.abelian₂ γ' →
    (∃ n ∈ Lat.NLam (Y.abelian₂ γ) (Y.fl γ), ∃ m ∈ Lat.NLam (Y.abelian₂ γ) (Y.fl' γ),
      ∀ b, Lat.frame (Y.fl' γ') b = n (m (Lat.frame (Y.fl' γ) b))) → γ = γ'

  massPair_eq : ∀ P : D.s.Pair u u', D.s.massPair P = massT (D.s.pfst P) ∧
    D.s.massPair P = massT (D.s.psnd P) ∧ D.s.massPair P = Y.wRow P / massTot

attribute [instance] TermLoc.acg TermLoc.mod

def clsOf {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Loc.Model F E) {m : ℕ} (Z : Matrix (Fin (m + 1)) (Fin (m + 1)) E) : Option (M.Cls m) :=
  if h : (∀ a b, Z a b ∈ M.R) ∧ IsUnit Z.det then
    some (Quotient.mk (M.isoSetoid m) ⟨Matrix.of fun a b => ⟨Z a b, h.1 a b⟩, by
      have : (Matrix.of fun a b => (⟨Z a b, h.1 a b⟩ : M.R)).map M.R.subtype = Z := rfl
      rw [this]; exact h.2⟩)
  else none

def cornerSh (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) :
    (D.s.atP p).Ep :=
  if Dmin w D.R.rS = 0 then 0
  else ((nSh (blkMod δ T T' p (D.R.rS + 1) 1 (zetaOf w)) : ℕ) : (D.s.atP p).Ep)

section Datum

variable {Y : TermTie D} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
  {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {u u' : D.what₂.Word}

def thCls (X : TermLoc D Y δ M u u') (γ : D.s.Term u u') (p : PlF D) : Option ((M p).Cls D.R.rS) :=
  clsOf (M p) ((X.H p).ZZplus (X.loc γ p) + Matrix.of fun a b =>
    if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then
      cornerSh δ (D.mem u).A.T (D.mem u').A.T p (D.s.ptOf γ) else 0)

def densT (X : TermLoc D Y δ M u u') (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp])
    (γ : D.s.Term u u') : ℝ :=
  ∏' p, (X.H p).dens (ϖ p) (X.loc γ p).abelian₂ ((X.H p).gram ((X.H p).MMfam (X.loc γ p)))

end Datum

def BBtop (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1))
    (c : Option ((M p).Cls D.R.rS)) : ℂ :=
  match modPt δ T T' p w, c with
  | some a, some c => dfac M δ T T' p w * (M p).BB a c
  | _, _ => 0

def BBG (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1))
    (κ : Option D.host.E) (th : ∀ p, Option ((M p).Cls D.R.rS)) : ℂ :=
  if kind w = κ then ∏ᶠ p, BBtop M δ T T' p w (th p) else 0

def autG (th : ∀ p, Option ((M p).Cls D.R.rS)) : ℂ :=
  ∏ᶠ p, (match th p with
    | some c => (((M p).nAut c : ℕ) : ℂ)
    | none => 1)

def Agree (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D) : Prop :=
  (M p).OK ∧ δ p ≠ 0 ∧ (M p).L.cj = (D.s.atP p).cj ∧ (M p).L.O = (D.s.atP p).O ∧
  (∀ y, (M p).L.psi0 y = (D.s.atP p).psiE (-(y * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹))) ∧
  (match (M p).split, (D.s.atP p).split with
    | none, none => True
    | some g, some sg => g.e = sg.e ∧ g.q = sg.q
    | _, _ => False)

abbrev TermLocs (D : Formalism.BasicNotions.D7) (Y : TermTie D) : Type 1 :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ u u' : D.what₂.Word, TermLoc D Y δ M u u'

def Kglob (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (T T' : ℕ)
    (n : ℕ) (w w' : Point D.host.E n) : ℂ :=
  if h : n = D.R.rS + 1 then KtopG M δ T T' (h ▸ w) (h ▸ w')
  else ∏ᶠ p, locK M δ T T' p n w w'

end Formalism.MainNotions.S.LocalSplitGroups
