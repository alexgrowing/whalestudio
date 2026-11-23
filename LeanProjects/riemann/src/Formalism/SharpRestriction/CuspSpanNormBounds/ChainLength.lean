import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.CuspSpanNormBounds.LeSCSCl

noncomputable section

namespace Formalism.MainNotions.JointEigenvalueBoundsFromAnyDatum

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel
open scoped BigOperators ComplexOrder
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

section LocalTheory

open Formalism.MainNotions.S.Loc MeasureTheory ComplexConjugate

def A2at {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) : Prop :=
  (∀ (m : ℕ) (s : ℕ+) (t t' : Eˣ) (h h' : Pt E m),
    ((t⁻¹ : Eˣ) : E) - ((t'⁻¹ : Eˣ) : E) ∉ M.R → M.Ns s t t' h h' = 0) ∧
  (∀ (m : ℕ) (s : ℕ+) (N : ℕ) (t : Fin N → Eˣ) (h : Fin N → Pt E m),
    (Matrix.of fun a b => M.Ns s (t a) (t b) (h a) (h b)).PosSemidef)

open scoped Classical in

def ThOK {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (m : ℕ) (s : ℕ+) (N : ℕ) (h : Fin N → Pt E m)
    (Th : E ⧸ M.Rsub → Fin N → Fin N → ℂ) : Prop :=

  (∀ x, (Matrix.of fun a b => Th x a b).PosSemidef) ∧

  (∀ x a b, M.detMod (h a) ≠ M.detMod (h b) → Th x a b = 0) ∧

  (∃ Λ : Submodule M.R E, IsCompact (Λ : Set E) ∧ IsOpen (Λ : Set E) ∧
    ∀ t ∉ Λ, ∀ a b, Th (Submodule.Quotient.mk t) a b = 0) ∧

  (∀ t : Eˣ, (Matrix.of fun a b => Th (Submodule.Quotient.mk (t : E)) a b -
      M.Ns s t t (h a) (h b)).PosSemidef) ∧

  (∀ c : ℝ, (Matrix.of fun (a b : {a : Fin N // M.detMod (h a) = c}) =>
      ((c⁻¹ ^ (2 * (s : ℕ)) : ℝ) : ℂ) * M.N0 (h a) (h b) - ∑' x : E ⧸ M.Rsub, Th x a b).PosSemidef) ∧

  ((s : ℕ) = 1 →
    (∀ (t : Eˣ) a b, Th (Submodule.Quotient.mk (t : E)) a b = M.Ns s t t (h a) (h b)) ∧
    ∀ a b, M.detMod (h a) = M.detMod (h b) →
      ∑' x : E ⧸ M.Rsub, Th x a b = ((M.detMod (h a))⁻¹ ^ 2 : ℝ) * M.N0 (h a) (h b)) ∧

  ((∀ a, M.InGLR (h a)) →
    (∀ a b, M.N0 (h a) (h b) = 1) ∧
    ∀ x, (Matrix.of fun a b => (if x = 0 then (1 : ℂ) else 0) * M.N0 (h a) (h b) -
      Th x a b).PosSemidef)

def MeasureVanishingDeterminant {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) : Prop :=
  (∀ (m : ℕ) (h h' : Pt E m), M.detMod h ≠ M.detMod h' →
    M.N0 h h' = 0 ∧ ∀ (s : ℕ+) (t : Eˣ), M.Ns s t t h h' = 0) ∧
  ∀ (m : ℕ) (s : ℕ+) (N : ℕ) (h : Fin N → Pt E m),
    ∃ Th : E ⧸ M.Rsub → Fin N → Fin N → ℂ, ThOK M m s N h Th

def SelfDualLatticeNormCongruenceAt {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (g : SplitG M.L), M.split = some g →
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (abelian₂ : Submodule M.L.O V), H.IsSelfDual abelian₂ →
  ∀ (T T' : F), (∃ u v : (𝒪[F])ˣ, ((u : 𝒪[F]) : F) = T ∧ ((v : 𝒪[F]) : F) = T') →
    (∃ c : 𝒪[F], T - T' = (g.q : F) ^ 2 * c) →
  ∀ (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E), IsUnit Zh.det →
    Zh.det * M.L.cj Zh.det - algebraMap F E (T * T') *
      ((Zh.submatrix (Fin.castLE (Nat.le_succ r)) (Fin.castLE (Nat.le_succ r))).det *
        M.L.cj (Zh.submatrix (Fin.castLE (Nat.le_succ r)) (Fin.castLE (Nat.le_succ r))).det) ≠ 0 →
    ((∃ t : Term V M r, t.abelian₂ = abelian₂ ∧ t.T = T ∧ t.T' = T' ∧ H.IsTerm t ∧ H.Zhat t.f t.f' = Zh) ↔
      ∀ a b, HermSp.ZZplusOf M Zh T T' a b ∈ M.R)

def FamilyTheoremThreePassage {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (g : SplitG M.L), M.split = some g →
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t : Term V M r), H.IsTerm t →
  ∀ nn ∈ H.NGrp t.abelian₂ t.f, ∀ nn' ∈ H.NGrp t.abelian₂ t.f',
    (∀ x ∈ t.abelian₂, nn x - nn' x ∈ H.smulLat (algebraMap F E (g.q : F)) t.abelian₂) →
    ∃ uL uU : Matrix (Fin (r + 1)) (Fin (r + 1)) E,
      (∀ a b, uL a b ∈ M.R ∧ uU a b ∈ M.R) ∧
      (∀ a, uL a a = 1 ∧ uU a a = 1) ∧ (∀ a b, a < b → uL a b = 0 ∧ uU b a = 0) ∧
      H.ZZplus ⟨t.abelian₂, fun a => nn (t.f a), fun a => nn' (t.f' a), t.T, t.T'⟩ =
        uL * H.ZZplus t * uU

def SimpleSum {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (_H : HermSp M V) {r : ℕ}
    (f : Fin (r + 1) → V) (ε : Fin (r + 1) → ℤ) (nn : V ≃ₗ[E] V) (σ : E) : Prop :=
  ∃ C : Fin (r + 1) → Fin (r + 1) → E, (∀ a, nn (f a) - f a = ∑ b, C a b • f b) ∧
    σ = ∑ a : Fin r, ((ε a.castSucc * ε a.succ : ℤ) : E) * C a.succ a.castSucc

def NGrpK {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (f : Fin (r + 1) → V) : Set (V ≃ₗ[E] V) :=
  {n | (∀ x y, H.h (n x) (n y) = H.h x y) ∧
    (∀ a : Fin r, n (f a.castSucc) - f a.castSucc ∈
      Submodule.span E ((fun b : Fin r => f b.castSucc) '' {b | b < a})) ∧
    ∀ v ∈ H.perp (H.X f), n v - v ∈ H.X f}

def LowestKTypeDimension {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (g : SplitG M.L), M.split = some g →
  ∃ (ε ε' : Fin (r + 1) → ℤ) (κL κU κ' : ℤ), (∀ a, ε a = 1 ∨ ε a = -1) ∧ (∀ a, ε' a = 1 ∨ ε' a = -1) ∧
    (κL = 1 ∨ κL = -1) ∧ (κU = 1 ∨ κU = -1) ∧ (κ' = 1 ∨ κ' = -1) ∧
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t : Term V M r), H.IsTerm t →
  ∀ nn ∈ NGrpK H t.f, ∀ nn' ∈ NGrpK H t.f',
  ∀ σ σ' : E, SimpleSum H t.f ε nn σ → SimpleSum H t.f' ε' nn' σ' →
    ∃ uL uU : Matrix (Fin (r + 1)) (Fin (r + 1)) E,
      (∀ a, uL a a = 1 ∧ uU a a = 1) ∧ (∀ a b, a < b → uL a b = 0 ∧ uU b a = 0) ∧
      H.ZZplus ⟨t.abelian₂, fun a => nn (t.f a), fun a => nn' (t.f' a), t.T, t.T'⟩ =
        uL * H.ZZplus t * uU ∧
      M.L.psi0 (algebraMap F E ((g.q : F)⁻¹) * σ) *
          M.L.psi0 (algebraMap F E ((g.q : F)⁻¹) * ((κ' : ℤ) : E) * σ') =
        M.psiR (((κL : ℤ) : E) * simpleLow uL + ((κU : ℤ) : E) * simpleUp uU)

def FamilyVolumeFourth {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (r k n : ℕ) (C : ℝ) : Prop :=
  ∀ (ϖ : 𝒪[F]), Irreducible ϖ →
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  (∀ (t : Term V M r), H.IsGeneric t →
    |H.dens ϖ t.abelian₂ (H.gram (H.MMfam t)) - 1| ≤
      C * (2 * (r : ℝ) + 2) * (Nat.card 𝓀[F] : ℝ) ^ (-((k : ℤ) - 2 * r - 2))) ∧
  (∀ (t₁ t₂ : Term V M r), H.IsGeneric t₁ → H.IsGeneric t₂ → H.IsScalarPair t₁ t₂ →
    H.dens ϖ t₁.abelian₂ (H.gram (H.MMfam t₁)) = H.dens ϖ t₂.abelian₂ (H.gram (H.MMfam t₂)))

def FrameK {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (f : Fin (r + 1) → V) (T : F) : Prop :=
  (∀ a b : Fin (r + 1), (a ≠ Fin.last r ∨ b ≠ Fin.last r) → H.h (f a) (f b) = 0) ∧
    H.h (f (Fin.last r)) (f (Fin.last r)) = - algebraMap F E T

def FamilyLocalModel {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r), H.IsGeneric t₁ →
  ∀ (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'),
    FrameK H f₂ t₁.T → FrameK H f₂' t₁.T' →
    H.Ident t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ' →
    H.SendsTo φ.toLinearMap 1 1 (t₁.f (Fin.last r)) (f₂ (Fin.last r)) →
    H.SendsTo φ'.toLinearMap 1 1 (t₁.f' (Fin.last r)) (f₂' (Fin.last r)) →
  let S : Set (Submodule M.L.O V) := {Λ₂ | H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ ∧
    H.Respects t₁ ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ φ φ'}
  let P₁ := H.ZZplus t₁
  let P₂ := HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T'
  (H.Dl t₁.f t₁.f' r = 0 →
    ∀ (Z₁ Z₂ : M.Mat (r + 1)), Z₁.Z.map M.R.subtype = P₁ → Z₂.Z.map M.R.subtype = P₂ →
      Nat.card S = M.nIso Z₁ Z₂) ∧
  (IsUnit (H.Dl t₁.f t₁.f' r) →
    ∀ (Y₁ Y₂ : M.Mat r) (be₁ be₂ al₁ al₂ : Fin r → M.R),
      (∀ a b : Fin r, (Y₁.Z a b : E) = P₁ a.castSucc b.castSucc ∧
        (Y₂.Z a b : E) = P₂ a.castSucc b.castSucc) →
      (∀ a : Fin r, (be₁ a : E) = P₁ a.castSucc (Fin.last r) ∧ (be₂ a : E) = P₂ a.castSucc (Fin.last r) ∧
        (al₁ a : E) = P₁ (Fin.last r) a.castSucc ∧ (al₂ a : E) = P₂ (Fin.last r) a.castSucc) →
      Nat.card S = M.nIsoBA Y₁ Y₂ be₁ be₂ al₁ al₂)

def IsApproximateAnnihilatorAtLevels {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (r : ℕ) : Prop :=
  ∀ (d : M.Cls r → ℝ) (Ds : ℝ), (∀ c, 0 ≤ d c ∧ d c ≤ Ds) →
  ∀ (N : ℕ) (w : Fin N → Pt E (r + 1)),
    (Matrix.of fun a b => (Ds : ℂ) * M.Kk (r + 1) (w a) (w b) -
      ∑' c : M.Cls r, (d c : ℂ) * (M.BB (w a) c * conj (M.BB (w b) c) / (M.nAut c : ℂ))).PosSemidef

def AllLoc (P : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E],
    Model F E → Prop) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK → P M

def T0 (D : Formalism.BasicNotions.D7) : Prop :=
  AllLoc (fun M => SelfDualLatticeNormCongruenceAt M D.R.rS D.R.r) ∧ AllLoc (fun M => FamilyTheoremThreePassage M D.R.rS D.R.r) ∧
    AllLoc (fun M => LowestKTypeDimension M D.R.rS D.R.r)

def T1 (D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := AllLoc (fun M => FamilyVolumeFourth M D.R.rS D.R.k D.R.r C)

def T2 (D : Formalism.BasicNotions.D7) : Prop := AllLoc (fun M => FamilyLocalModel M D.R.rS D.R.r)

def T3 (D : Formalism.BasicNotions.D7) : Prop := AllLoc (fun M => IsApproximateAnnihilatorAtLevels M D.R.rS)

end LocalTheory

def adm1 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Loc.Model F E), M.OK → A2at M

def adm2 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Loc.Model F E), M.OK → MeasureVanishingDeterminant M

def adm3 (D : Formalism.BasicNotions.D7) : Prop := 4 * D.R.rS + 8 ≤ D.R.k → T0 D

def ArchimedeanSignatureMatching (D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := 4 * D.R.rS + 8 ≤ D.R.k → T1 D C

def adm5 (D : Formalism.BasicNotions.D7) : Prop := 4 * D.R.rS + 8 ≤ D.R.k → T2 D

def adm10 (D : Formalism.BasicNotions.D7) : Prop := 4 * D.R.rS + 8 ≤ D.R.k → T3 D

def adm6 (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ U : ∀ p : PlF D, AddSubgroup (D.s.atP p).Ep, (∀ p, IsOpen (U p : Set (D.s.atP p).Ep)) →
    {p | (U p : Set (D.s.atP p).Ep) ≠ ((D.s.atP p).O : Set (D.s.atP p).Ep)}.Finite →
    ∀ x : ∀ p, (D.s.atP p).Ep, {p | x p ∉ (D.s.atP p).O}.Finite →
      ∃ t : D.host.E, ∀ p, (D.s.atP p).ιE t - x p ∈ U p

def adm7 (D : Formalism.BasicNotions.D7) : Prop :=
  (∀ M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep, (∀ p, (M p).OK) →
    ∀ x : D.host.E, x ≠ 0 →
      (Function.mulSupport fun p => (M p).modK ((D.s.atP p).ιE x)).Finite ∧
      ∏ᶠ p, (M p).modK ((D.s.atP p).ιE x) = |((Algebra.norm ℚ x : ℚ) : ℝ)|⁻¹) ∧
  (∀ x : D.host.E,
    (Function.mulSupport fun p : PlF D => (D.s.atP p).psiE ((D.s.atP p).ιE x)).Finite ∧
    ∏ᶠ p : PlF D, (D.s.atP p).psiE ((D.s.atP p).ιE x) =
      Complex.exp (2 * Real.pi * Complex.I * (((Algebra.trace ℚ D.host.E x : ℚ) : ℂ))))

def CNT {Y : TermTie D} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {u u' : D.what₂.Word} (X : TermLoc D Y δ M u u') (c : ℝ) : Prop :=
  0 < c ∧
  ∀ w : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0 →
    {γ : D.s.Term u u' | D.s.generic γ ∧ D.s.ptOf γ = w}.Finite ∧
    (¬ TotPos (Gpt (D.mem u).A.T (D.mem u').A.T w) → ∀ γ : D.s.Term u u', D.s.generic γ → D.s.ptOf γ ≠ w) ∧
    ∀ _ : TotPos (Gpt (D.mem u).A.T (D.mem u').A.T w),
    ∀ ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp], (∀ p, Irreducible (ϖ p)) →
    ∀ γ₀ : D.s.Term u u', D.s.generic γ₀ → Gpt (D.mem u).A.T (D.mem u').A.T (D.s.ptOf γ₀) ≠ 0 →
      ∑' γ : {γ : D.s.Term u u' // D.s.generic γ ∧ D.s.ptOf γ = w ∧
          kind (D.s.ptOf γ₀) = kind w ∧ ∀ p, thCls X γ p = thCls X γ₀ p},
        (X.massT γ.1 : ℂ) * D.s.cTerm γ.1 =
      (n0 c (D.mem u).A.T (D.mem u').A.T w : ℂ) * (densT X ϖ γ₀ : ℂ) *
        BBG M δ (D.mem u).A.T (D.mem u').A.T w (kind (D.s.ptOf γ₀)) (thCls X γ₀) / autG M (thCls X γ₀)

def PartnerSum {Y : TermTie D} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {u u' : D.what₂.Word} (X : TermLoc D Y δ M u u') : Prop :=
  ∀ γ : D.s.Term u u', D.s.generic γ → Gpt (D.mem u).A.T (D.mem u').A.T (D.s.ptOf γ) ≠ 0 →
  ∀ w' : Point D.host.E (D.R.rS + 1), TotPos (Gpt (D.mem u).A.T (D.mem u').A.T w') →
    {P : D.s.Pair u u' | D.s.pfst P = γ ∧ Formalism.MainNotions.S.scalarP D.s P ∧ D.s.ptOf (D.s.psnd P) = w'}.Finite ∧
    ∑' P : {P : D.s.Pair u u' // D.s.pfst P = γ ∧ Formalism.MainNotions.S.scalarP D.s P ∧ D.s.ptOf (D.s.psnd P) = w'},
        starRingEnd ℂ (D.s.cTerm (D.s.psnd P.1)) =
      starRingEnd ℂ (BBG M δ (D.mem u).A.T (D.mem u').A.T w' (kind (D.s.ptOf γ)) (thCls X γ))

def adm8 (D : Formalism.BasicNotions.D7) {Y : TermTie D} (X : TermLocs D Y) (cN : D.what₂.Word → D.what₂.Word → ℝ) : Prop :=
  4 * D.R.rS + 8 ≤ D.R.k →
  ∀ δ M (hA : ∀ p, Agree δ M p) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] → CNT (X δ M hA u u') (cN u u')

def adm9 (D : Formalism.BasicNotions.D7) {Y : TermTie D} (X : TermLocs D Y) : Prop :=
  4 * D.R.rS + 8 ≤ D.R.k →
  ∀ δ M (hA : ∀ p, Agree δ M p) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] → PartnerSum (X δ M hA u u')

def G1root (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) : Prop :=
  ∀ p (x : D.host.E), (D.s.atP p).psiE ((D.s.atP p).ιE (-(x / (Lat.gS D : D.host.E)))) =
    (M p).L.psi0 (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (x * (uP p : D.host.E)) *
      Ring.inverse (qE p))

def G2 (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    {Y : TermTie D}
    (X : ∀ u u' : D.what₂.Word, TermLoc D Y δ M u u') (cN : D.what₂.Word → D.what₂.Word → ℝ) : Prop :=
  ∀ u u' : D.what₂.Word, (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
  ∀ ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp], (∀ p, Irreducible (ϖ p)) →
  ∀ Dsup : ℝ, 0 ≤ Dsup →
    (∀ γ : D.s.Term u u', D.s.generic γ → Gpt (D.mem u).A.T (D.mem u').A.T (D.s.ptOf γ) ≠ 0 →
      densT (X u u') ϖ γ ≤ Dsup) →
    ∀ (ι : Type) [Fintype ι] (w : ι → Point D.host.E (D.R.rS + 1)),
      (∀ x, Gpt (D.mem u).A.T (D.mem u').A.T (w x) ≠ 0) →
      (∀ x y, (Function.mulSupport fun p =>
        KtopP M δ (D.mem u).A.T (D.mem u').A.T p (w x) (w y)).Finite) ∧
      ((Dsup : ℂ) • (Matrix.of fun x y => KtopG M δ (D.mem u).A.T (D.mem u').A.T (w x) (w y)) -
        Matrix.of fun x y => Formalism.MainNotions.S.Kgs D.s u u' (w x) (w y) /
          ((Real.sqrt (n0 (cN u u') (D.mem u).A.T (D.mem u').A.T (w x) *
            n0 (cN u u') (D.mem u).A.T (D.mem u').A.T (w y)) : ℝ) : ℂ)).PosSemidef

def Gfin (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (T T' : ℕ) : Prop :=
  (∀ (n : ℕ) (w w' : Point D.host.E n), n ≤ D.R.rS + 1 →
    (Function.mulSupport fun p => locK M δ T T' p n w w').Finite) ∧
  (∀ (n : ℕ) (h : Point D.host.E n), n ≤ D.R.rS + 1 →
    (Function.mulSupport fun p => detNrmP M δ T T' p h).Finite) ∧
  (∀ (a s : ℕ) (t : D.host.E), t ≠ 0 → 1 ≤ a → 1 ≤ s → a + s - 1 ≤ D.R.rS + 1 →
    (Function.mulSupport fun p => (M p).modK (blkMod δ T T' p a s t)).Finite) ∧
  (∀ w w' : Point D.host.E (D.R.rS + 1), (Function.mulSupport fun p => KtopP M δ T T' p w w').Finite)

def G3blk (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (m s : ℕ) : Prop :=
  let ν := nu D.R.rS (m + 1) (m + s)
  let L := La M δ ν s
  (∀ t, t ∈ L ↔ t ∈ gdd (D := D) 1 ν ∧ t - (-1) ^ s * D.conjF t ∈ gdd (D := D) 2 ν) ∧
  (∀ t ∈ gdd (D := D) 2 ν, t ∈ L) ∧
  (∀ l ∈ dualPsiG (D := D) L, l ∈ gdd (D := D) (-1) (-((ν : ℤ) + 1))) ∧
  ∀ (T T' : ℕ), 0 < T → 0 < T' → T ≡ T' [MOD (Lat.gS D) ^ 2] → Nat.Coprime T (Lat.gS D) → Nat.Coprime T' (Lat.gS D) →
  ∀ (hs : 1 ≤ s),
    Gfin δ M T T' ∧
    (∀ (h h' : Point D.host.E m) (t t' : D.host.E) (ht : t ≠ 0) (ht' : t' ≠ 0),
      Kglob δ M T T' (m + s) (ptApp h t ht s hs) (ptApp h' t' ht' s hs) ≠ 0 →
        t⁻¹ - t'⁻¹ ∈ LaP (D := D) ν s ∧ (m + s = D.R.rS + 1 → s = 1 → t = t')) ∧
    ∀ (ι : Type) [Fintype ι] (hd : ι → Point D.host.E m),
      (∀ x y p, detNrmP M δ T T' p (hd x) = detNrmP M δ T T' p (hd y)) →
      ∃ Th : D.host.E → Matrix ι ι ℂ,
        (∀ t, (Th t).PosSemidef) ∧ (∀ t, ∀ l ∈ L, Th (t + l) = Th t) ∧
        (∀ (t : D.host.E) (ht : t ≠ 0), (Th t - Matrix.of fun x y =>
          ∏ᶠ p, ((((M p).modK (blkMod δ T T' p (m + 1) s t * blkMod δ T T' p (m + 1) s t)) ^
            (s * (s - 1) / 2) : ℝ) : ℂ) *
            locK M δ T T' p (m + s) (ptApp (hd x) t ht s hs) (ptApp (hd y) t ht s hs)).PosSemidef) ∧
        ∃ S : Finset D.host.E, (∀ a ∈ S, ∀ b ∈ S, a - b ∈ L → a = b) ∧
          (∀ t, Th t ≠ 0 → ∃ a ∈ S, t - a ∈ L) ∧
          ∀ x0 : ι, ((((∏ᶠ p, (detNrmP M δ T T' p (hd x0)) ^ (-(2 * (s : ℤ)))) : ℝ) : ℂ) •
            (Matrix.of fun x y => ∏ᶠ p, locK M δ T T' p m (hd x) (hd y)) - ∑ a ∈ S, Th a).PosSemidef

def G4 (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (i : ℕ) : Prop :=
  let r := D.R.rS
  let e : ℤ := 2 * (i : ℤ) - 3 - 2 * r
  let aa := gdd (D := D) (-1) (-((2 * r + 3 - 2 * i : ℕ) : ℤ))
  let L := La M δ (nu r i i) 1
  let g : ℝ := Lat.gS D
  let absl : D.host.E → ℝ := fun l => ∏ τ : D.what₂.Tau, ‖D.host.emb (D.eTau τ) l‖
  let Nh : ℝ := Real.sqrt (FractionalIdeal.absNorm aa : ℝ)
  let bound : (D.what₂.Tau → ℝ) → ℝ := fun c =>
    (∏ τ, c τ) * (2 * Real.pi / D.host.rdE) ^ (e * D.R.f) * g ^ (((D.R.m : ℤ) - 2 * ((i : ℤ) - 1)) * D.R.f)
  (∀ l ∈ dualPsiG (D := D) L, l ∈ aa) ∧
  (AddSubgroup.closure (dualPsiG (D := D) L)).relIndex (aa : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup =
    (Lat.gS D) ^ D.R.f ∧
  (∀ l ∈ aa, l ≠ 0 → Nh ≤ absl l) ∧
  Nh = (g * D.host.rdE ^ (2 * r + 3 - 2 * i)) ^ (-(D.R.f : ℤ)) ∧
  (∀ c : D.what₂.Tau → ℝ, (∏ τ, c τ * (2 * Real.pi / g) ^ e) / Nh = bound c) ∧
  (∀ c : D.what₂.Tau → ℝ, (∀ τ, 0 < c τ) → ∀ l ∈ dualPsiG (D := D) L, l ≠ 0 →
    (∏ τ, c τ * (2 * Real.pi / g) ^ e) / absl l ≤ bound c)

def aux₃ (D : Formalism.BasicNotions.D7) {Y : TermTie D} (X : TermLocs D Y) (cN : D.what₂.Word → D.what₂.Word → ℝ) : Prop :=
  4 * D.R.rS + 8 ≤ D.R.k →
  ∃ (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p), G1root δ M ∧ G2 δ M (X δ M hA) cN ∧
    (∀ m s, 1 ≤ s → m + s ≤ D.R.rS + 1 → G3blk δ M m s) ∧
    (∀ i, 1 ≤ i → i ≤ D.R.rS + 1 → G4 δ M i)

def admitted (D : Formalism.BasicNotions.D7) {Y : TermTie D} (X : TermLocs D Y) (cN : D.what₂.Word → D.what₂.Word → ℝ) (C : ℝ) : Prop :=
  adm1 D ∧ adm2 D ∧ adm3 D ∧ ArchimedeanSignatureMatching D C ∧ adm5 D ∧ adm6 D ∧ adm7 D ∧ adm8 D X cN ∧ adm9 D X ∧ adm10 D

def Stmt (D : Formalism.BasicNotions.D7) {Y : TermTie D} (X : TermLocs D Y) (cN : D.what₂.Word → D.what₂.Word → ℝ) (C : ℝ) : Prop :=
  admitted D X cN C → aux₃ D X cN

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) {Y : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i)}

def admF1 : Prop := OwnEv Fm fun _ _ x i => adm1 (Fm.D x i)
def admF2 : Prop := OwnEv Fm fun _ _ x i => adm2 (Fm.D x i)
def admF3 : Prop := OwnEv Fm fun _ _ x i => adm3 (Fm.D x i)
def admF4 : Prop := ∃ C : ℝ, OwnEv Fm fun _ _ x i => ArchimedeanSignatureMatching (Fm.D x i) C
def admF5 : Prop := OwnEv Fm fun _ _ x i => adm5 (Fm.D x i)
def FamilyRowsCountHypothesis : Prop := OwnEv Fm fun _ _ x i => adm10 (Fm.D x i)
def admF6 : Prop := ∀ x (i : Fm.Ix x), adm6 (Fm.D x i)
def admF7 : Prop := ∀ x (i : Fm.Ix x), adm7 (Fm.D x i)
def admF8 (X : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), TermLocs (Fm.D x i) (Y x hx i))
    (cN : ∀ x (i : Fm.Ix x), (Fm.D x i).what₂.Word → (Fm.D x i).what₂.Word → ℝ) : Prop :=
  OwnEv Fm fun _ _ x i => ∀ hx : Fm.x1 < x, adm8 (Fm.D x i) (X x hx i) (cN x i)
def admF9 (X : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), TermLocs (Fm.D x i) (Y x hx i)) : Prop :=
  OwnEv Fm fun _ _ x i => ∀ hx : Fm.x1 < x, adm9 (Fm.D x i) (X x hx i)

def AdmF (X : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), TermLocs (Fm.D x i) (Y x hx i))
    (cN : ∀ x (i : Fm.Ix x), (Fm.D x i).what₂.Word → (Fm.D x i).what₂.Word → ℝ) : Prop :=
  admF1 Fm ∧ admF2 Fm ∧ admF3 Fm ∧ admF4 Fm ∧ admF5 Fm ∧ admF6 Fm ∧ admF7 Fm ∧ admF8 Fm X cN ∧ admF9 Fm X ∧
    FamilyRowsCountHypothesis Fm

def OrbitValuationBound (X : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), TermLocs (Fm.D x i) (Y x hx i))
    (cN : ∀ x (i : Fm.Ix x), (Fm.D x i).what₂.Word → (Fm.D x i).what₂.Word → ℝ) : Prop :=
  OwnEv Fm fun _ _ x i => ∀ hx : Fm.x1 < x, aux₃ (Fm.D x i) (X x hx i) (cN x i)

def KudlaFamilyStatement (X : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), TermLocs (Fm.D x i) (Y x hx i))
    (cN : ∀ x (i : Fm.Ix x), (Fm.D x i).what₂.Word → (Fm.D x i).what₂.Word → ℝ) : Prop :=
  AdmF Fm X cN → OrbitValuationBound Fm X cN

end Family

end Formalism.MainNotions.JointEigenvalueBoundsFromAnyDatum
