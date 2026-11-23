import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalDataRealPlace
import Formalism.SharpRestriction.CuspSpanNormBounds.IsGramNorm
import Formalism.SharpRestriction.CuspSpanNormBounds.PSDKOnOfPSDK
import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.LinQRawRange
import Formalism.SharpRestriction.CuspSpanNormBounds.LeSCSCl
import Formalism.LocalRingCardinality.DataTies
import Formalism.HermitianLattices.StatementMass
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport

noncomputable section

namespace Formalism.MainNotions.LocalBesselAndTopKernel.TOP

open ValuativeRel MeasureTheory ComplexConjugate ComplexOrder
open Formalism.MainNotions.S.Loc

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

def DensAt {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (r k n : ℕ) : Prop :=
  ∀ (ϖ : 𝒪[F]), Irreducible ϖ →
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t : Term V M r), H.IsGeneric t →
    H.dens ϖ t.abelian₂ (H.gram (H.MMfam t)) ≤
      Real.exp (4 * (Nat.card 𝓀[F] : ℝ) ^ (-((k : ℤ) - 2 * r - 2))) ∧
    (M.split ≠ none → H.dens ϖ t.abelian₂ (H.gram (H.MMfam t)) ≤ 1)

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

def partT (D : Formalism.BasicNotions.D7) (C : ℝ) : Prop :=
  4 * D.R.rS + 8 ≤ D.R.k → T0 D ∧ T1 D C ∧ T2 D ∧ T3 D

end Formalism.MainNotions.LocalBesselAndTopKernel.TOP

namespace Formalism.MainNotions.LocalBesselAndTopKernel.GLOB

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel
open scoped BigOperators ComplexOrder
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

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

def cnt (D : Formalism.BasicNotions.D7) {Y : TermTie D} (X : TermLocs D Y) (cN : D.what₂.Word → D.what₂.Word → ℝ) : Prop :=
  4 * D.R.rS + 8 ≤ D.R.k →
  ∀ δ M (hA : ∀ p, Agree δ M p) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] → CNT (X δ M hA u u') (cN u u')

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

def partG (D : Formalism.BasicNotions.D7) {Y : TermTie D} (X : TermLocs D Y) (cN : D.what₂.Word → D.what₂.Word → ℝ) : Prop :=
  4 * D.R.rS + 8 ≤ D.R.k →
  ∃ (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p), G1root δ M ∧ G2 δ M (X δ M hA) cN ∧
    (∀ m s, 1 ≤ s → m + s ≤ D.R.rS + 1 → G3blk δ M m s) ∧
    (∀ i, 1 ≤ i → i ≤ D.R.rS + 1 → G4 δ M i)

end Formalism.MainNotions.LocalBesselAndTopKernel.GLOB

namespace Formalism.MainNotions.LocalBesselAndTopKernel.SW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

section Ext

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)

def thetaS {n : ℕ} (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (S : Set (Fin n → Fin M → E))
    (h : HA (AF F) σ J) : ℂ :=
  ∑' X : S, Φ (actTup (AF F) (HA.mat (AF F) σ J h⁻¹) (ratTup (AF F) (X : Fin n → Fin M → E)))

def SWc1 : Prop :=
  ∀ (n : ℕ), n + 2 ≤ M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b),
    T.det ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E)
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ)
    (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ),
    Continuous Φinf → RapidDecay b Φinf → IsPureFin b Φf Φv → IsProdInfFin Φ Φinf Φf →
    AllSome (IsHaarH F E σ M J) fun μ => AllSome (IsFDH F E σ M J μ) fun 𝓕 =>
    AllSome (IsCharAF F) fun ψ =>
    AllSome (SdW F E σ M J (Ainf F) (psiInf F ψ) n) fun μinf =>
    AllSome (SdHerm F E σ (Ainf F) (psiInf F ψ) n) fun νinf =>
    AllSome (fun μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E) =>
      ∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) n (μv v)) fun μv =>
    AllSome (fun νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ n) =>
      ∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) n (νv v)) fun νv =>
    ∃ (ginf : HermR (Ainf F) σ n → ℂ) (gv : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → ℂ),
      IsContDensityOn μinf (gramR (Ainf F) σ J) Subtype.val νinf
        {S | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} Φinf ginf ∧
      (∀ v, IsContDensityOn (μv v) (gramR (Fv F v) σ J) Subtype.val (νv v)
        {S | IsUnit (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det} (Φv v) (gv v)) ∧
      Multipliable (fun v => gv v (hermOf (Fv F v) σ T hT)) ∧
      meanC μ 𝓕 (thetaS F E σ M J Φ {X | gramE σ J X = T}) =
        ginf (hermOf (Ainf F) σ T hT) * ∏' v, gv v (hermOf (Fv F v) σ T hT)

def SWc2 : Prop :=
  ∀ (p : ℕ), 2 * p + 1 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E)
    (Φ : (Fin p → Fin M → AF F ⊗[F] E) → ℂ) (Φinf : (Fin p → Fin M → Ainf F ⊗[F] E) → ℂ)
    (Φf : (Fin p → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin p → Fin M → Fv F v ⊗[F] E) → ℂ),
    Continuous Φinf → RapidDecay b Φinf → IsPureFin b Φf Φv → IsProdInfFin Φ Φinf Φf →
    AllSome (IsHaarH F E σ M J) fun μ => AllSome (IsFDH F E σ M J μ) fun 𝓕 =>
    AllSome (IsCharAF F) fun ψ =>
    AllSome (SdW F E σ M J (Ainf F) (psiInf F ψ) p) fun μinf =>
    AllSome (SdHerm F E σ (Ainf F) (psiInf F ψ) p) fun νinf =>
    AllSome (fun μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin p → Fin M → Fv F v ⊗[F] E) =>
      ∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) p (μv v)) fun μv =>
    AllSome (fun νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ p) =>
      ∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) p (νv v)) fun νv =>
    AllSome (fun fibInf : HermR (Ainf F) σ p → Measure (Fin p → Fin M → Ainf F ⊗[F] E) =>
      IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
        {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf) fun fibInf =>
    AllSome (fun fibV : ∀ v : HeightOneSpectrum (𝓞 F),
        HermR (Fv F v) σ p → Measure (Fin p → Fin M → Fv F v ⊗[F] E) =>
      ∀ v, IsFibreFamily (μv v) (gramR (Fv F v) σ J) Subtype.val
        {X | LinearIndependent (Fv F v ⊗[F] E) X} (νv v) Set.univ (fibV v)) fun fibV =>
    Multipliable (fun v => ∫ X, Φv v X ∂(fibV v 0)) ∧
    meanC μ 𝓕 (thetaS F E σ M J Φ {X | LinearIndependent E X ∧ gramE σ J X = 0}) =
      (∫ X, Φinf X ∂(fibInf 0)) * ∏' v, ∫ X, Φv v X ∂(fibV v 0)

def SWc3 : Prop :=
  3 ≤ M → ∀ (x : Fin 1 → Fin M → E) (β : F), β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β →
    (∀ y : Fin 1 → Fin M → AF F ⊗[F] E, qR (AF F) σ J (y 0) = algebraMap F (AF F) β →
      ∃ g : HA (AF F) σ J, g • ratTup (AF F) x = y) →
    AllSome (IsCharAF F) fun ψ =>
    AllSome (IsHaarH F E σ M J) fun μ =>
    AllSome (IsXbetaMeasure F E σ M J ψ β) fun νX =>
    AllSome (fun μ' : Measure (Hstab (AF F) σ J x) =>
      μ'.IsHaarMeasure ∧ IsCompatible F E σ M J x μ μ' νX) fun μ' =>
    AllSome (IsFDH F E σ M J μ) fun 𝓕 =>
    AllSome (fun 𝓕' : Set (Hstab (AF F) σ J x) =>
      IsFundamentalDomain (HstabFin (AF F) σ J x) 𝓕' μ') fun 𝓕' => μ' 𝓕' = μ 𝓕

end Ext

open Formalism.BasicNotions

def AtD (D : D7) (P : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (_σ : E →ₐ[F] E) (M : ℕ) (_J : Matrix (Fin M) (Fin M) E), Prop) : Prop :=
  letI := D.host.cmStar
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) D.host.E), IsHermND D.sp.cm.sig J →
    P D.host.F D.host.E D.sp.cm.sig M J

end Formalism.MainNotions.LocalBesselAndTopKernel.SW

namespace Formalism.MainNotions.LocalBesselAndTopKernel

open Formalism.BasicNotions Formalism.MainNotions.S NumberField IsDedekindDomain
open scoped nonZeroDivisors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def hyp (D : D7) (large₂ : SizeData₂ D) (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  StandingNumericalData D C0 ∧ StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT ∧ 1 ≤ C0

open Classical in

def gsFam (D : D7) (u u' : D.what₂.Word) : D.s.Pair u u' → ℂ := fun P =>
  if scalarP D.s P ∧ D.s.Gterm (D.s.pfst P) ≠ 0 ∧ D.s.Gterm (D.s.psnd P) ≠ 0 then D.s.pval P else 0

def Conclusion1 (D : D7) (CA CA' Ce : ℝ) : Prop :=
  let N : ℝ := NA D
  let r : ℝ := D.R.rS
  ∀ u u' : D.what₂.Word, u ≠ u' → Summable (gsFam D u u') ∧
  ∀ (x : D.what₂.Tau → LocalDataRealPlace D) (L : LatticeDataWithDual D),
    IsLocA D u u' x → IsLatGLOB D L →
    (∀ τ, IsCutS (uS D u τ) (uS D u' τ) (Set.Icc (x τ).a (x τ).b) ∧
      CA * ((D.R.k : ℝ) * N * (r + 1) ^ 2 + N ^ 2 * (r + 1) ^ 2 + N ^ 3) ≤ (x τ).b - (x τ).a ∧
      (x τ).a ≤ (x τ).a1 ∧ (x τ).b1 ≤ (x τ).b ∧ N ^ 3 / 2 ≤ (x τ).b1 - (x τ).a1) →
    (r + 1) * (CA / ThA D CA u u' x L) ^ (D.R.f : ℝ) ≤ 1 → CA' ≤ ThA D CA u u' x L →
    genScal D u u' ≤ (1 + CA * (r + 1) * (CA / ThA D CA u u' x L) ^ (D.R.f : ℝ)) * (1 + eSum D Ce) *
      (∏ᶠ p ∈ typedPl D, (1 + 3 / (Ideal.absNorm p.asIdeal : ℝ))) *
      (D.duS u : ℝ) * (D.duS u' : ℝ) / D.what₂.Dstar

def projection_sandwich_lattice (D : D7) : Prop :=
  UnitaryVolumeMass.cTvA D

def MassRatio₂ (D : D7) (C1 : ℝ) : Prop :=
  UnitaryVolumeMass.cTvB D C1

def kernel_index_full_lattice (D : D7) (C2 : ℝ) : Prop :=
  UnitaryVolumeMass.cTvC D C2

def gram_det_kernel_dual_lattice (D : D7) (C3 : ℝ) : Prop :=
  UnitaryVolumeMass.cTvD D C3

def BesselBoundOneSlotDifference (D : D7) (C4 : ℝ) : Prop :=
  UnitaryVolumeMass.cTvE D C4

def FamilyNonvanishing (D : D7) (large₂ : SizeData₂ D) (c5 CA : ℝ) : Prop :=
  UnitaryVolumeMass.cTvF D large₂ c5 CA

def MidVolumeChain (D : D7) (large₂ : SizeData₂ D) (ep0 CV : ℝ) : Prop :=
  UnitaryVolumeMass.cTvG D large₂ ep0 CV

def Conclusion2 (D : D7) (large₂ : SizeData₂ D) (C1 C2 C3 C4 c5 CA : ℝ) : Prop :=
  projection_sandwich_lattice D ∧ MassRatio₂ D C1 ∧ kernel_index_full_lattice D C2 ∧ gram_det_kernel_dual_lattice D C3 ∧ BesselBoundOneSlotDifference D C4 ∧ FamilyNonvanishing D large₂ c5 CA

def hsM {N : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) : ℝ := Real.sqrt (∑ i, ∑ j, Complex.normSq (x i j))

def family_first_line_of_admitted (D : D7) : Prop :=
  UnitaryVolumeMass.cExp D

def WittOrbitTheorem (D : D7) : Prop :=
  UnitaryVolumeMass.c2aG D ∧
  (∀ (g : ℝ), 1 < g → ∀ k : ℕ,
    g ^ (∑ i ∈ Finset.Ico 1 k, i) / ∏ i ∈ Finset.Ico 1 k, (g ^ i - 1) =
      ∏ i ∈ Finset.Ico 1 k, (1 - (g ^ i)⁻¹)⁻¹) ∧
  (∀ (g : ℝ), 3 ≤ g → ∀ k : ℕ, ∏ i ∈ Finset.Ico 1 k, (1 - (g ^ i)⁻¹)⁻¹ ≤ 1 + 3 / g)

def MLatticeCond : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Formalism.MainNotions.S.Loc.Model F E), M.OK →
    (∀ a : E, (∀ b ∈ M.R, M.psiR (a * b) = 1) ↔ a ∈ M.R) ∧
    (∀ (m : ℕ) (ZZ : M.Mat m),
      (Nat.card (M.Cok ZZ) : ℝ) = (M.modK (ZZ.Z.map M.R.subtype).det)⁻¹) ∧
    (∀ (m : ℕ) (h h' : Formalism.MainNotions.S.Loc.Pt E m), M.detMod h ≠ M.detMod h' →
      M.N0 h h' = 0 ∧ ∀ (s : ℕ+) (t : Eˣ), M.Ns s t t h h' = 0)

def NonvanishingBesselPeriod (D : D7) : Prop :=
  ∀ (τ : D.what₂.Tau) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (H →L[ℂ] H)),
    IsRowsDS D τ σ → ∀ μG : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS),
    IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) μG →
    ∃ d : ℝ, 0 < d ∧ ∀ v w v' w' : H,
      MeasureTheory.Integrable (fun x => inner ℂ w (σ (Matrix.of x) v) * star (inner ℂ w' (σ (Matrix.of x) v'))) μG ∧
      ∫ x, inner ℂ w (σ (Matrix.of x) v) * star (inner ℂ w' (σ (Matrix.of x) v')) ∂μG =
        inner ℂ v' v * inner ℂ w w' / (d : ℂ)

def AdmittedWeylDimension : Prop :=
  ∀ (k' : ℕ) (u : Fin k' → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : Matrix (Fin k') (Fin k') ℂ → (H →L[ℂ] H)), StrictAnti u → IsHCTypeU k' u π →
    (Module.finrank ℂ H : ℝ) = vand u / ∏ i ∈ Finset.range k', (i.factorial : ℝ)

def WittExtensionHermitianForms : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (B : V →ₗ⋆[K] V →ₗ[K] K), (∀ x y, star (B x y) = B y x) → (∀ x, (∀ y, B x y = 0) → x = 0) →
    ∀ (U : Submodule K V) (f : U →ₗ[K] V), Function.Injective f →
      (∀ x y : U, B (f x) (f y) = B x y) →
      ∃ g : V ≃ₗ[K] V, (∀ x y, B (g x) (g y) = B x y) ∧ ∀ x : U, g x = f x

def FormalDegreeDecay (D : D7) (Ca : ℝ) : Prop :=
  ∀ (τ : D.what₂.Tau) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (H →L[ℂ] H)),
    IsRowsDS D τ σ → ∃ a Cd : ℝ, Ca * (D.R.r : ℝ) ^ 5 ≤ a ∧
      (∀ w : H, IsLowUnitH D.R.k D.R.rS (epsSH D.R) (lamSH D.R (D.hc τ)) σ w →
        ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS), ‖inner ℂ w (σ x w)‖ ≤ Cd * hsM x ^ (-a)) ∧
      ∀ v v' : H, IsKFinHpk (k := D.R.k) (r := D.R.rS) σ v → IsKFinHpk (k := D.R.k) (r := D.R.rS) σ v' →
        ∃ C : ℝ, ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS), ‖inner ℂ v' (σ x v)‖ ≤ C * hsM x ^ (-a)

def VolumeFromTheoremThree (D : D7) : Prop :=
  ∀ (τ : D.what₂.Tau) (u : D.what₂.Word) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (H →L[ℂ] H))
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (π : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (Wp →L[ℂ] Wp))
    (z : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (w : H)
    (μG μS ν : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)),
    IsRowsDS D τ σ → IsColsType D u τ z π →
    (∀ a : Fin D.R.rS, z (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) = 0 ∧ z (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) = 0) →
    0 < Formalism.QuantumDeterminants.Tz D.R.k D.R.rS z →
    IsLowUnitH D.R.k D.R.rS (epsSH D.R) (lamSH D.R (D.hc τ)) σ w →
    IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) μG →
    IsHaarOn (Formalism.QuantumDeterminants.Sset D.R.k D.R.rS z) μS → IsQuotMeas μG μS ν →
    ∃ W : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → Wp,
      MeasureTheory.AEStronglyMeasurable (fun x => W (Matrix.of x)) μG ∧
      MeasureTheory.AEStronglyMeasurable (fun x => W (Matrix.of x)) ν ∧
      IsSPsiEquiv (k := D.R.k) (r := D.R.rS) z (psiS D z) π W ∧ l2SG ν W < ⊤ ∧ l2SG ν W ≠ 0 ∧
      ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS), rconv μG (eFun μG σ w) W x = W x

def MultiplicityOneUnitaryBranching (D : D7) : Prop :=
  ∀ (τ : D.what₂.Tau) (u : D.what₂.Word) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (H →L[ℂ] H))
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    (π : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (Wp →L[ℂ] Wp))
    (z : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (B1 B2 : H → Wp),
    IsRowsDS D τ σ → IsColsType D u τ z π →
    (∀ a : Fin D.R.rS, z (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) = 0 ∧ z (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) = 0) →
    0 < Formalism.QuantumDeterminants.Tz D.R.k D.R.rS z →
    IsBesselMapSm (k := D.R.k) (r := D.R.rS) z (psiS D z) σ π B1 →
    IsBesselMapSm (k := D.R.k) (r := D.R.rS) z (psiS D z) σ π B2 →
    ∀ N : ℕ, N ≤ D.R.f * (2 * D.R.rS + D.R.k + 1) ^ 2 / 2 + 1 →
    Formalism.MainNotions.CayleySignature.HasOrdLe D.R.k D.R.rS N σ B1 → Formalism.MainNotions.CayleySignature.HasOrdLe D.R.k D.R.rS N σ B2 →
    (∀ v ∈ smoothVecs (k := D.R.k) (r := D.R.rS) σ, B1 v = 0) ∨
      ∃ c : ℂ, ∀ v ∈ smoothVecs (k := D.R.k) (r := D.R.rS) σ, B2 v = c • B1 v

def TopKernelBoundAllLocalModels (D : D7) (C : ℝ) : Prop := TOP.partT D C

export Formalism.MainNotions.S.LocalFrameAxioms (LocMatch FrameAx PsiAx k_le_nS Nlet)

def admA (D : D7) (C C' : ℝ) (Kst : ℕ) (Vm : ValMap D.R.k D.R.rS) : Prop := LocalFrameAxioms.stThmA D C C' Kst Vm

def FamilySchurFormalDegree (D : D7) : Prop :=
  UnitaryVolumeMass.stMassRatio D

def GL5LogLValueBoundByZeta (D : D7) : Prop :=
  ∀ i : ℕ, 3 ≤ i →
    |Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E i)| ≤ (D.R.f : ℝ) * Real.log (riemannZeta (i : ℂ)).re

def cardGL (q : ℝ) (n : ℕ) : ℝ := ∏ i ∈ Finset.range n, (q ^ n - q ^ i)

def dimNS (D : D7) : ℕ := D.R.rS * (2 * D.R.k + 2 * D.R.rS + 1)

def idxRows (D : D7) : ℝ :=
  ∏ᶠ p ∈ typedPl D, cardGL (Ideal.absNorm p.asIdeal : ℝ) D.R.r /
    ((Ideal.absNorm p.asIdeal : ℝ) ^ dimNS D * (Ideal.absNorm p.asIdeal : ℝ) ^ (D.R.k * (D.R.k - 1) / 2))

def FamilyMidVolume (D : D7) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module D.host.E V] [Module (𝓞 D.host.E) V]
    [IsScalarTower (𝓞 D.host.E) D.host.E V] (h : V →ₗ⋆[D.host.E] V →ₗ[D.host.E] D.host.E)
    (L : Submodule (𝓞 D.host.E) V), h.IsSymm →
    (Formalism.HermitianLatticesTheory.IsOrthoLattice h L D.R.k → ∀ u : D.what₂.Word,
      (D.duS u : ℝ) = Formalism.HermitianLatticesTheory.mass h L * gaG D *
        (∏ τ, vand (uS D u τ) / ∏ i ∈ Finset.range D.R.k, (i.factorial : ℝ)) * (Tr D u ^ D.R.k - 1) ^ D.R.f) ∧
    (Formalism.HermitianLatticesTheory.IsOrthoLattice h L D.R.r →
      D.what₂.Dstar = Formalism.HermitianLatticesTheory.mass h L * idxRows D * ∏ τ, D.dsig τ)

def lamAbs {N : ℕ} (lam : Fin N → ℝ) : ℝ := ⨆ a : Fin N, ⨆ b : Fin N, |lam a - lam b|

def nPl {N : ℕ} (ε : Fin N → Bool) : ℕ := (Finset.univ.filter (fun a => ε a = true)).card
def nMi {N : ℕ} (ε : Fin N → Bool) : ℕ := (Finset.univ.filter (fun a => ε a = false)).card

def DensityTheoremThree (D : D7) (C3 : ℝ) : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (ep0 h0 : ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (w : H),
    Formalism.QuantumDeterminants.IsHCParam lam → Formalism.QuantumDeterminants.GapAtLeast ε lam h0 →
    Real.exp (-(N : ℝ)) ≤ ep0 → ep0 < 1 / 2 →
    C3 * (min (nPl ε) (nMi ε) : ℕ) * ((nPl ε : ℝ) * (nMi ε : ℝ)) ^ 3 * N * Real.log N / ep0 ^ 2 ≤ h0 →
    IsDS ε lam σ → w ≠ 0 →
    (1 - ep0) * Formalism.QuantumDeterminants.fdegHC lam ≤ fdegOf ((D.s.cdScale N ε : ENNReal) • Formalism.REAL.muG ε) σ w ∧
    fdegOf ((D.s.cdScale N ε : ENNReal) • Formalism.REAL.muG ε) σ w ≤
      4 * (Module.finrank ℂ (lowKSub ε lam σ) : ℝ) *
        (C3 * (nPl ε : ℝ) * (nMi ε : ℝ) * N * lamAbs lam) ^ (nPl ε * nMi ε)

def dTauF {N : ℕ} (ε : Fin N → Bool) (lam : Fin N → ℝ) : ℝ :=
  (∏ a : Fin N, ∏ b ∈ Finset.univ.filter (fun b => a < b ∧ ε a = ε b),
      (lam a - lam b + ((Finset.univ.filter (fun c => a < c ∧ c < b ∧ ε c ≠ ε a)).card : ℝ))) /
    ((∏ i ∈ Finset.range (nPl ε), (i.factorial : ℝ)) * ∏ i ∈ Finset.range (nMi ε), (i.factorial : ℝ))

def FamilyMassLastLine : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)),
    Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ → (Module.finrank ℂ (lowKSub ε lam σ) : ℝ) = dTauF ε lam

def DiscreteSeriesFormalDegreeAlt (D : D7) : Prop :=
  ∀ τ : D.what₂.Tau, ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (σ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (H →L[ℂ] H)) (d : ℝ),
    IsDS (epsSH D.R) (lamSH D.R (D.hc τ)) σ ∧
    IsFdeg ((D.s.cdScale _ (epsSH D.R) : ENNReal) • Formalism.REAL.muG (epsSH D.R)) σ d

def ExactLocalDensityAllModels (D : D7) : Prop :=
  4 * D.R.rS + 8 ≤ D.R.k → TOP.AllLoc (fun M => TOP.DensAt M D.R.rS D.R.k D.R.r)

section Glob

open Formalism.MainNotions.S.LocalSplitGroups

def GlobalLatticeMajorantHypothesis (D : D7) {X : TermTie D} (Z : TermLocs D X) (cN : D.what₂.Word → D.what₂.Word → ℝ) : Prop :=
  GLOB.partG D Z cN

def ColumnSpaceRanks (D : D7) {X : TermTie D} (Z : TermLocs D X) (cN : D.what₂.Word → D.what₂.Word → ℝ) : Prop :=
  GLOB.cnt D Z cN

variable {D : D7}

def nMod (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (T T' : ℕ)
    (a s : ℕ) (t : D.host.E) : ℝ :=
  ∏ᶠ p : PlF D, ((M p).modK (blkMod δ T T' p a s t))⁻¹

def phiFrom (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (T T' : ℕ)
    (i : ℕ) : ℕ → List (D.host.E × ℕ) → ℝ
  | _, [] => 1
  | a, (t, s) :: rest =>
    nMod δ M T T' a s t ^ (s * (i - (a + s - 1)) + s * (s - 1) / 2) * phiFrom δ M T T' i (a + s) rest

def phiA (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (T T' : ℕ)
    {i : ℕ} (h : Point D.host.E i) : ℝ :=
  phiFrom δ M T T' i 1 h.1

def KA (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (T T' : ℕ)
    (Dsup : ℝ) (i : ℕ) (h h' : Point D.host.E i) : ℂ :=
  (((if i = D.R.rS + 1 then Dsup else 1 : ℝ) : ℝ) : ℂ) * Kglob δ M T T' i h h' /
    ((phiA δ M T T' h * phiA δ M T T' h' : ℝ) : ℂ)

variable (D)

def ArithmeticGlobalModelCondition (cN : D.what₂.Word → D.what₂.Word → ℝ) : Prop :=
  4 * D.R.rS + 8 ≤ D.R.k →
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → GLOB.G1root δ M →
    (∀ m s, 1 ≤ s → m + s ≤ D.R.rS + 1 → GLOB.G3blk δ M m s) →
    (∀ i, 1 ≤ i → i ≤ D.R.rS + 1 → GLOB.G4 δ M i) →
  ∃ L : LatticeDataWithDual D, IsLatGLOB D L ∧ LatAx D (gE D) L ∧
    (∀ i s, IsBlockSL2Embedding D i s → (L.La i s : Set D.host.E) = La M δ (nu D.R.rS i (i + s - 1)) s ∧
      (L.La' i s : Set D.host.E) = LaP (D := D) (nu D.R.rS i (i + s - 1)) s) ∧
    ∀ u u' : D.what₂.Word, 0 < (D.mem u).A.T → 0 < (D.mem u').A.T →
      (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
      Nat.Coprime (D.mem u).A.T (Lat.gS D) → Nat.Coprime (D.mem u').A.T (Lat.gS D) →
      (∀ Dsup : ℝ, 1 ≤ Dsup → Dsup ≤ 2 → ∃ Kd : KernelData D, ArithAx D L Kd ∧
        (∀ i, i ≤ D.R.rS + 1 → ∀ h h', Kd.K i h h' = KA δ M (D.mem u).A.T (D.mem u').A.T Dsup i h h') ∧
        (∀ i, 1 ≤ i → i ≤ D.R.rS → Kd.e i = 0) ∧ 1 + Kd.e (D.R.rS + 1) = Dsup) ∧
      (0 < cN u u' → ∃ cW : ℝ, 0 < cW ∧ ∀ w : Point D.host.E (D.R.rS + 1),
        TotPos (Gpt (D.mem u).A.T (D.mem u').A.T w) →
        n0 (cN u u') (D.mem u).A.T (D.mem u').A.T w * phiA δ M (D.mem u).A.T (D.mem u').A.T w ^ 2 =
          cW * ptWeightG D L.ρ (Tr D u) (Tr D u') w.1)

variable {D}

def localBesselDatumAtRealPlace {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {Cw : ℝ} (Y : LoopTie D large₂ X u u' Cw)
    (hT : 0 < Tr D u) (hT' : 0 < Tr D u') (v : D.what₂.Tau) : LocBessel D.R.k D.R.rS :=
  toBessel D v u u' Y.θ (Y.W v) (lamD D v) (Y.A v) (Y.goodW v) (Y.goodS v) hT hT'

def IsRegPt (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  (∀ l : Fin (r + 2), 1 ≤ l.val → l.val ≤ r → Formalism.QuantumDeterminants.Dmin k r z z' g l ≠ 0) ∧ Formalism.QuantumDeterminants.Gf k r z z' g ≠ 0

def IsAmpCoef {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {Cw : ℝ} (Y : LoopTie D large₂ X u u' Cw)
    (hT : 0 < Tr D u) (hT' : 0 < Tr D u')
    (f : ∀ v, MatKR D.R.k D.R.rS → ((localBesselDatumAtRealPlace Y hT hT' v).Wq →L[ℂ] (localBesselDatumAtRealPlace Y hT hT' v).Wp)) : Prop :=
  ∀ v, IsKFinCoefH (localBesselDatumAtRealPlace Y hT hT' v).σ (f v) ∧
    ∀ (c : Fin D.R.rS → ℂ) (μ : Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ), (∀ a, c a ≠ 0) →
      μ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hb D.R.k) →
      IsRegPt D.R.k D.R.rS (Y.W v).z (Y.W v).z' (Formalism.QuantumDeterminants.bigCell D.R.k D.R.rS c μ) →
      (localBesselDatumAtRealPlace Y hT hT' v).J (f v) (Formalism.QuantumDeterminants.bigCell D.R.k D.R.rS c μ) =
        (Y.A v).J (Y.W v).μG (Formalism.QuantumDeterminants.bigCell D.R.k D.R.rS c μ)

abbrev GPts (D : D7) (u u' : D.what₂.Word) : Type :=
  {w : Point D.host.E (D.R.rS + 1) // Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0}

def formTerm {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {Cw : ℝ} (Y : LoopTie D large₂ X u u' Cw)
    (hT : 0 < Tr D u) (hT' : 0 < Tr D u') (Vm : ValMap D.R.k D.R.rS)
    (f : ∀ v, MatKR D.R.k D.R.rS → ((localBesselDatumAtRealPlace Y hT hT' v).Wq →L[ℂ] (localBesselDatumAtRealPlace Y hT hT' v).Wp))
    (q : GPts D u u' × GPts D u u') : ℂ :=
  Kgs D.s u u' q.1.1 q.2.1 *
    ∏ v, hsInner (Vm.V (localBesselDatumAtRealPlace Y hT hT' v) (f v) (locBlocks D (rhoReal D) v q.1.1.1))
      (Vm.V (localBesselDatumAtRealPlace Y hT hT' v) (f v) (locBlocks D (rhoReal D) v q.2.1.1))

variable (D)

def SpectralWeightsCM (large₂ : SizeData₂ D) (X : TermTie D) (Cw : ℝ) (Y : ∀ u u', LoopTie D large₂ X u u' Cw)
    (Vm : ValMap D.R.k D.R.rS) : Prop :=
  ∀ (u u' : D.what₂.Word), u ≠ u' → ∀ (hT : 0 < Tr D u) (hT' : 0 < Tr D u')
    (f : ∀ v, MatKR D.R.k D.R.rS → ((localBesselDatumAtRealPlace (Y u u') hT hT' v).Wq →L[ℂ] (localBesselDatumAtRealPlace (Y u u') hT hT' v).Wp)),
    IsAmpCoef (Y u u') hT hT' f →
    Summable (fun P => ‖gsFam D u u' P‖) ∧ Summable (fun q => ‖formTerm (Y u u') hT hT' Vm f q‖) ∧
    (gaG D : ℂ) * ∑' P, gsFam D u u' P =
      (((D.duS u : ℝ) / dimPi (hc := D.hcW) u : ℝ) : ℂ) * ∑' q, formTerm (Y u u') hT hT' Vm f q

end Glob

def CharacterCutVolume (D : D7) : Prop := SW.AtD D SW.SWc1 ∧ SW.AtD D SW.SWc2 ∧ SW.AtD D SW.SWc3

section One

open Formalism.MainNotions.S.LocalSplitGroups

def Adm1 (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (Cw : ℝ) (Y : ∀ u u', LoopTie D large₂ X u u' Cw) (Z : TermLocs D X)
    (cN : D.what₂.Word → D.what₂.Word → ℝ) (Vm : ValMap D.R.k D.R.rS) (Ca Cq CA CA' : ℝ) : Prop :=
  family_first_line_of_admitted D ∧ WittOrbitTheorem D ∧ MLatticeCond ∧ TopKernelBoundAllLocalModels D Cq ∧ NonvanishingBesselPeriod D ∧ WittExtensionHermitianForms ∧ FormalDegreeDecay D Ca ∧ VolumeFromTheoremThree D ∧ MultiplicityOneUnitaryBranching D ∧ admA D CA CA' 5 Vm ∧
    ExactLocalDensityAllModels D ∧ GlobalLatticeMajorantHypothesis D Z cN ∧ ColumnSpaceRanks D Z cN ∧ SpectralWeightsCM D large₂ X Cw Y Vm ∧ ArithmeticGlobalModelCondition D cN ∧ CharacterCutVolume D ∧ AdmittedWeylDimension ∧ FamilyMidVolume D

def Adm2 (D : D7) (C3 : ℝ) : Prop :=
  AdmittedWeylDimension ∧ FamilySchurFormalDegree D ∧ GL5LogLValueBoundByZeta D ∧ FamilyMidVolume D ∧ DensityTheoremThree D C3 ∧ FamilyMassLastLine ∧ DiscreteSeriesFormalDegreeAlt D

def admitted (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (Cw : ℝ) (Y : ∀ u u', LoopTie D large₂ X u u' Cw) (Z : TermLocs D X)
    (cN : D.what₂.Word → D.what₂.Word → ℝ) (Vm : ValMap D.R.k D.R.rS) (Ca Cq CA CA' C3 : ℝ) : Prop :=
  Adm1 D large₂ X Cw Y Z cN Vm Ca Cq CA CA' ∧ Adm2 D C3

def IntegralityFromMetric (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (Cw : ℝ) (Y : ∀ u u', LoopTie D large₂ X u u' Cw) (Z : TermLocs D X)
    (cN : D.what₂.Word → D.what₂.Word → ℝ) (Vm : ValMap D.R.k D.R.rS)
    (Ca Cq C0 C' Cl Cg cb Cu cT CT CA CA' Ce : ℝ) : Prop :=
  Ties D → Adm1 D large₂ X Cw Y Z cN Vm Ca Cq CA CA' → hyp D large₂ C0 C' Cl Cg cb Cu cT CT → Conclusion1 D CA CA' Ce

def HodgeTateFromSandwich (D : D7) (large₂ : SizeData₂ D) (C3 C0 C' Cl Cg cb Cu cT CT C1 C2 C3' C4 c5 CA ep0 CV : ℝ) : Prop :=
  Ties D → Adm2 D C3 → hyp D large₂ C0 C' Cl Cg cb Cu cT CT →
    Conclusion2 D large₂ C1 C2 C3' C4 c5 CA ∧ MidVolumeChain D large₂ ep0 CV

def FamilyExpansionSecond (D : D7) (large₂ : SizeData₂ D) (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  FamilySchurFormalDegree D → GL5LogLValueBoundByZeta D → FamilyMidVolume D → hyp D large₂ C0 C' Cl Cg cb Cu cT CT → projection_sandwich_lattice D
def SecondBoundHyp (D : D7) (large₂ : SizeData₂ D) (C0 C' Cl Cg cb Cu cT CT C1 : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT → MassRatio₂ D C1
def NonvanishingFromUnfolding (D : D7) (large₂ : SizeData₂ D) (C0 C' Cl Cg cb Cu cT CT C1 C2 : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT → projection_sandwich_lattice D → MassRatio₂ D C1 → kernel_index_full_lattice D C2
def BesselBoundOfParamHyp (D : D7) (large₂ : SizeData₂ D) (C3 C0 C' Cl Cg cb Cu cT CT ep0 CV : ℝ) : Prop :=
  Ties D → DensityTheoremThree D C3 → FamilyMassLastLine → DiscreteSeriesFormalDegreeAlt D → hyp D large₂ C0 C' Cl Cg cb Cu cT CT → MidVolumeChain D large₂ ep0 CV
def LocalTiedPairs (D : D7) (large₂ : SizeData₂ D) (C0 C' Cl Cg cb Cu cT CT ep0 CV C3' : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT → MidVolumeChain D large₂ ep0 CV → gram_det_kernel_dual_lattice D C3'
def LowerVolumeImpliesUpper (D : D7) (large₂ : SizeData₂ D) (C0 C' Cl Cg cb Cu cT CT C3' C4 : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT → gram_det_kernel_dual_lattice D C3' → BesselBoundOneSlotDifference D C4
def MassRatioTheoremTwo (D : D7) (large₂ : SizeData₂ D) (C0 C' Cl Cg cb Cu cT CT C4 c5 CA : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT → projection_sandwich_lattice D → BesselBoundOneSlotDifference D C4 → FamilyNonvanishing D large₂ c5 CA

def Stmt (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (Cw : ℝ) (Y : ∀ u u', LoopTie D large₂ X u u' Cw) (Z : TermLocs D X)
    (cN : D.what₂.Word → D.what₂.Word → ℝ) (Vm : ValMap D.R.k D.R.rS)
    (Ca Cq C3 C0 C' Cl Cg cb Cu cT CT CA CA' Ce C1 C2 C3' C4 c5 : ℝ) : Prop :=
  Ties D → admitted D large₂ X Cw Y Z cN Vm Ca Cq CA CA' C3 → hyp D large₂ C0 C' Cl Cg cb Cu cT CT →
    Conclusion1 D CA CA' Ce ∧ Conclusion2 D large₂ C1 C2 C3' C4 c5 CA

theorem statement_of_degree_and_bound {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {Cw : ℝ} {Y : ∀ u u', LoopTie D large₂ X u u' Cw} {Z : TermLocs D X}
    {cN : D.what₂.Word → D.what₂.Word → ℝ} {Vm : ValMap D.R.k D.R.rS}
    {Ca Cq C3 C0 C' Cl Cg cb Cu cT CT CA CA' Ce C1 C2 C3' C4 c5 ep0 CV : ℝ}
    (h1 : IntegralityFromMetric D large₂ X Cw Y Z cN Vm Ca Cq C0 C' Cl Cg cb Cu cT CT CA CA' Ce)
    (h2 : HodgeTateFromSandwich D large₂ C3 C0 C' Cl Cg cb Cu cT CT C1 C2 C3' C4 c5 CA ep0 CV) :
    Stmt D large₂ X Cw Y Z cN Vm Ca Cq C3 C0 C' Cl Cg cb Cu cT CT CA CA' Ce C1 C2 C3' C4 c5 :=
  fun hT hA hH => ⟨h1 hT hA.1 hH, (h2 hT hA.2 hH).1⟩

end One

def GivOk (C0 Cg cb Cu cT CT : ℝ) : Prop := 1 ≤ C0 ∧ 0 < Cg ∧ 0 < cb ∧ 0 < Cu ∧ 0 < cT ∧ cT ≤ CT

section Family

open Formalism.MainNotions.S.LocalSplitGroups

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def UnderF (C0 Cg cb Cu cT CT : ℝ) (P : ∀ D : D7, SizeData₂ D → Prop) : Prop :=
  OwnEv Fm fun C' Cl x i =>
    hyp (Fm.D x i) (Fm.L x i) C0 C' Cl Cg cb Cu cT CT → P (Fm.D x i) (Fm.L x i)

def FamilyWittTheorem (C0 Cg cb Cu cT CT : ℝ) : Prop := UnderF Fm C0 Cg cb Cu cT CT fun D _ => family_first_line_of_admitted D
def FirstSizeFamilyStatement (C0 Cg cb Cu cT CT : ℝ) : Prop := UnderF Fm C0 Cg cb Cu cT CT fun D _ => WittOrbitTheorem D
def FamilyVandermondeRatio : Prop := MLatticeCond
def FamilyWeylLaw (Cq : ℝ) : Prop := ∀ x (i : Fm.Ix x), TopKernelBoundAllLocalModels (Fm.D x i) Cq
def UnfoldingCount : Prop := ∀ x (i : Fm.Ix x), NonvanishingBesselPeriod (Fm.D x i)
def FirstSizeStatement : Prop := AdmittedWeylDimension
def FamilySpectralWeights : Prop := WittExtensionHermitianForms
def FamilyExpansion (C0 Cg cb Cu cT CT Ca : ℝ) : Prop := UnderF Fm C0 Cg cb Cu cT CT fun D _ => FormalDegreeDecay D Ca
def FamilyVolumeSecond (C0 Cg cb Cu cT CT : ℝ) : Prop := UnderF Fm C0 Cg cb Cu cT CT fun D _ => VolumeFromTheoremThree D
def FamilyMultiplicityOneHypothesis : Prop := ∀ x (i : Fm.Ix x), MultiplicityOneUnitaryBranching (Fm.D x i)

def FamilyTheoremA (Vm : ∀ k r, ValMap k r) (CA CA' : ℝ) : Prop :=
  ∀ x (i : Fm.Ix x), admA (Fm.D x i) CA CA' 5 (Vm _ _)
def FamilyDensity : Prop := ∀ x (i : Fm.Ix x), ExactLocalDensityAllModels (Fm.D x i)

def FamilyGlobalLatticeMajorant {X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i)} (Z : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), TermLocs (Fm.D x i) (X x hx i))
    (cN : ∀ x (i : Fm.Ix x), (Fm.D x i).what₂.Word → (Fm.D x i).what₂.Word → ℝ) : Prop :=
  OwnEv Fm fun _ _ x i => ∀ hx : Fm.x1 < x, GlobalLatticeMajorantHypothesis (Fm.D x i) (Z x hx i) (cN x i)
def FamilyFormalDegreeDecay {X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i)} (Z : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), TermLocs (Fm.D x i) (X x hx i))
    (cN : ∀ x (i : Fm.Ix x), (Fm.D x i).what₂.Word → (Fm.D x i).what₂.Word → ℝ) : Prop :=
  OwnEv Fm fun _ _ x i => ∀ hx : Fm.x1 < x, ColumnSpaceRanks (Fm.D x i) (Z x hx i) (cN x i)
def FamilyFormulaUnderLoopData (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i)) (Cw : ℝ)
    (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) u u', LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' Cw) (Vm : ∀ k r, ValMap k r)
    (C0 Cg cb Cu cT CT : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => ∀ hx : Fm.x1 < x, hyp (Fm.D x i) (Fm.L x i) C0 C' Cl Cg cb Cu cT CT →
    SpectralWeightsCM (Fm.D x i) (Fm.L x i) (X x hx i) Cw (Y x hx i) (Vm _ _)
def FamilyArithmetic (cN : ∀ x (i : Fm.Ix x), (Fm.D x i).what₂.Word → (Fm.D x i).what₂.Word → ℝ)
    (C0 Cg cb Cu cT CT : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => hyp (Fm.D x i) (Fm.L x i) C0 C' Cl Cg cb Cu cT CT → ArithmeticGlobalModelCondition (Fm.D x i) (cN x i)
def LocalGenericDensity : Prop := ∀ x (i : Fm.Ix x), CharacterCutVolume (Fm.D x i)
def SecondSizeStatement : Prop := ∀ x (i : Fm.Ix x), FamilySchurFormalDegree (Fm.D x i)
def BesselFormLine : Prop := ∀ x (i : Fm.Ix x), GL5LogLValueBoundByZeta (Fm.D x i)
def FamilyRanksHypothesis (C0 Cg cb Cu cT CT : ℝ) : Prop := UnderF Fm C0 Cg cb Cu cT CT fun D _ => FamilyMidVolume D
def FamilyThirdTheoremHypothesis (C3 : ℝ) : Prop := ∀ x (i : Fm.Ix x), DensityTheoremThree (Fm.D x i) C3
def FamilyMassTheoremTwo : Prop := FamilyMassLastLine
def FamilyDecompositionSumHypothesis (C0 Cg cb Cu cT CT : ℝ) : Prop := UnderF Fm C0 Cg cb Cu cT CT fun D _ => DiscreteSeriesFormalDegreeAlt D

def FirstFiltrationHypotheses (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i)) (Cw : ℝ)
    (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) u u', LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' Cw)
    (Z : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), TermLocs (Fm.D x i) (X x hx i))
    (cN : ∀ x (i : Fm.Ix x), (Fm.D x i).what₂.Word → (Fm.D x i).what₂.Word → ℝ)
    (Vm : ∀ k r, ValMap k r) (C0 Cg cb Cu cT CT Ca Cq CA CA' : ℝ) : Prop :=
  FamilyWittTheorem Fm C0 Cg cb Cu cT CT ∧ FirstSizeFamilyStatement Fm C0 Cg cb Cu cT CT ∧ FamilyVandermondeRatio ∧ FamilyWeylLaw Fm Cq ∧ UnfoldingCount Fm ∧ FamilySpectralWeights ∧
    FamilyExpansion Fm C0 Cg cb Cu cT CT Ca ∧ FamilyVolumeSecond Fm C0 Cg cb Cu cT CT ∧ FamilyMultiplicityOneHypothesis Fm ∧ FamilyTheoremA Fm Vm CA CA' ∧
    FamilyDensity Fm ∧ FamilyGlobalLatticeMajorant Fm Z cN ∧ FamilyFormalDegreeDecay Fm Z cN ∧ FamilyFormulaUnderLoopData Fm X Cw Y Vm C0 Cg cb Cu cT CT ∧
    FamilyArithmetic Fm cN C0 Cg cb Cu cT CT ∧ LocalGenericDensity Fm ∧ FirstSizeStatement ∧ FamilyRanksHypothesis Fm C0 Cg cb Cu cT CT

def SecondFiltrationHypotheses (C0 Cg cb Cu cT CT C3 : ℝ) : Prop :=
  FirstSizeStatement ∧ SecondSizeStatement Fm ∧ BesselFormLine Fm ∧ FamilyRanksHypothesis Fm C0 Cg cb Cu cT CT ∧ FamilyThirdTheoremHypothesis Fm C3 ∧ FamilyMassTheoremTwo ∧
    FamilyDecompositionSumHypothesis Fm C0 Cg cb Cu cT CT

def AdmF (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i)) (Cw : ℝ)
    (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) u u', LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' Cw)
    (Z : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), TermLocs (Fm.D x i) (X x hx i))
    (cN : ∀ x (i : Fm.Ix x), (Fm.D x i).what₂.Word → (Fm.D x i).what₂.Word → ℝ)
    (Vm : ∀ k r, ValMap k r) (C0 Cg cb Cu cT CT Ca Cq CA CA' C3 : ℝ) : Prop :=
  FirstFiltrationHypotheses Fm X Cw Y Z cN Vm C0 Cg cb Cu cT CT Ca Cq CA CA' ∧ SecondFiltrationHypotheses Fm C0 Cg cb Cu cT CT C3

def ConclusionF1 (C0 Cg cb Cu cT CT CA CA' Ce : ℝ) : Prop :=
  UnderF Fm C0 Cg cb Cu cT CT fun D _ => Conclusion1 D CA CA' Ce

def FamilyBesselBoundFirstPart (C0 Cg cb Cu cT CT : ℝ) : Prop := UnderF Fm C0 Cg cb Cu cT CT fun D _ => projection_sandwich_lattice D
def TheoremThreePassage (C0 Cg cb Cu cT CT C1 : ℝ) : Prop := UnderF Fm C0 Cg cb Cu cT CT fun D _ => MassRatio₂ D C1
def FamilyLowestKType (C0 Cg cb Cu cT CT C2 : ℝ) : Prop := UnderF Fm C0 Cg cb Cu cT CT fun D _ => kernel_index_full_lattice D C2
def LocalSplitExponents (C0 Cg cb Cu cT CT C3' : ℝ) : Prop := UnderF Fm C0 Cg cb Cu cT CT fun D _ => gram_det_kernel_dual_lattice D C3'
def SchurOrthogonalityRealPlace (C0 Cg cb Cu cT CT C4 : ℝ) : Prop := UnderF Fm C0 Cg cb Cu cT CT fun D _ => BesselBoundOneSlotDifference D C4
def FamilyLocalBesselBoundWithCharacter (C0 Cg cb Cu cT CT c5 CA : ℝ) : Prop := UnderF Fm C0 Cg cb Cu cT CT fun D large₂ => FamilyNonvanishing D large₂ c5 CA
def FamilyTopBound (C0 Cg cb Cu cT CT ep0 CV : ℝ) : Prop := UnderF Fm C0 Cg cb Cu cT CT fun D large₂ => MidVolumeChain D large₂ ep0 CV

def ConclusionF2 (C0 Cg cb Cu cT CT C1 C2 C3' C4 c5 CA ep0 CV : ℝ) : Prop :=
  FamilyBesselBoundFirstPart Fm C0 Cg cb Cu cT CT ∧ TheoremThreePassage Fm C0 Cg cb Cu cT CT C1 ∧ FamilyLowestKType Fm C0 Cg cb Cu cT CT C2 ∧
    LocalSplitExponents Fm C0 Cg cb Cu cT CT C3' ∧ SchurOrthogonalityRealPlace Fm C0 Cg cb Cu cT CT C4 ∧ FamilyLocalBesselBoundWithCharacter Fm C0 Cg cb Cu cT CT c5 CA ∧
    FamilyTopBound Fm C0 Cg cb Cu cT CT ep0 CV

def PeriodFamilyStatement (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i)) (Cw : ℝ)
    (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) u u', LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' Cw)
    (Z : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), TermLocs (Fm.D x i) (X x hx i))
    (cN : ∀ x (i : Fm.Ix x), (Fm.D x i).what₂.Word → (Fm.D x i).what₂.Word → ℝ) (Vm : ∀ k r, ValMap k r)
    (C0 Cg cb Cu cT CT Ca Cq CA CA' Ce : ℝ) : Prop :=
  GivOk C0 Cg cb Cu cT CT → FirstFiltrationHypotheses Fm X Cw Y Z cN Vm C0 Cg cb Cu cT CT Ca Cq CA CA' →
    ConclusionF1 Fm C0 Cg cb Cu cT CT CA CA' Ce

def DeterminantValueFamily (C0 Cg cb Cu cT CT C3 C1 C2 C3' C4 c5 CA ep0 CV : ℝ) : Prop :=
  GivOk C0 Cg cb Cu cT CT → SecondFiltrationHypotheses Fm C0 Cg cb Cu cT CT C3 →
    ConclusionF2 Fm C0 Cg cb Cu cT CT C1 C2 C3' C4 c5 CA ep0 CV

def FamilyUnfoldingCount (C0 Cg cb Cu cT CT : ℝ) : Prop :=
  SecondSizeStatement Fm → BesselFormLine Fm → FamilyRanksHypothesis Fm C0 Cg cb Cu cT CT → FamilyBesselBoundFirstPart Fm C0 Cg cb Cu cT CT

theorem FamilyUnfoldingCount.ClosedSizeStatements {Fm : Formalism.MainNotions.FamP eps} {C0 Cg cb Cu cT CT C3 : ℝ} (h : FamilyUnfoldingCount Fm C0 Cg cb Cu cT CT)
    (hA : SecondFiltrationHypotheses Fm C0 Cg cb Cu cT CT C3) : FamilyBesselBoundFirstPart Fm C0 Cg cb Cu cT CT :=
  h hA.2.1 hA.2.2.1 hA.2.2.2.1

def OrbitValuationBound (C0 Cg cb Cu cT CT CA CA' Ce C1 C2 C3' C4 c5 ep0 CV : ℝ) : Prop :=
  ConclusionF1 Fm C0 Cg cb Cu cT CT CA CA' Ce ∧ ConclusionF2 Fm C0 Cg cb Cu cT CT C1 C2 C3' C4 c5 CA ep0 CV

def KudlaFamilyStatement (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i)) (Cw : ℝ)
    (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) u u', LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' Cw)
    (Z : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), TermLocs (Fm.D x i) (X x hx i))
    (cN : ∀ x (i : Fm.Ix x), (Fm.D x i).what₂.Word → (Fm.D x i).what₂.Word → ℝ) (Vm : ∀ k r, ValMap k r)
    (C0 Cg cb Cu cT CT Ca Cq C3 CA CA' Ce C1 C2 C3' C4 c5 ep0 CV : ℝ) : Prop :=
  GivOk C0 Cg cb Cu cT CT → AdmF Fm X Cw Y Z cN Vm C0 Cg cb Cu cT CT Ca Cq CA CA' C3 →
    OrbitValuationBound Fm C0 Cg cb Cu cT CT CA CA' Ce C1 C2 C3' C4 c5 ep0 CV

theorem family_statement_of_parts {Fm : Formalism.MainNotions.FamP eps} {X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i)} {Cw : ℝ}
    {Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) u u', LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' Cw}
    {Z : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), TermLocs (Fm.D x i) (X x hx i)}
    {cN : ∀ x (i : Fm.Ix x), (Fm.D x i).what₂.Word → (Fm.D x i).what₂.Word → ℝ} {Vm : ∀ k r, ValMap k r}
    {C0 Cg cb Cu cT CT Ca Cq C3 CA CA' Ce C1 C2 C3' C4 c5 ep0 CV : ℝ}
    (h1 : PeriodFamilyStatement Fm X Cw Y Z cN Vm C0 Cg cb Cu cT CT Ca Cq CA CA' Ce)
    (h2 : DeterminantValueFamily Fm C0 Cg cb Cu cT CT C3 C1 C2 C3' C4 c5 CA ep0 CV) :
    KudlaFamilyStatement Fm X Cw Y Z cN Vm C0 Cg cb Cu cT CT Ca Cq C3 CA CA' Ce C1 C2 C3' C4 c5 ep0 CV :=
  fun hG hA => ⟨h1 hG hA.1, h2 hG hA.2⟩

end Family

section Closed

open Formalism.MainNotions.S.LocalSplitGroups

def ClosedFormWithDensityConstant (𝒞 : Formalism.MainNotions.FamClass) (Vm : ∀ k r, ValMap k r) : Prop :=
  ∀ C0 Cg cb Cu cT CT Cq Cw : ℝ, ∃ Ca₀ CA₁ CA'₁ Ce : ℝ, ∀ Ca ≥ Ca₀, ∀ CA ≥ CA₁, ∀ CA' ≥ CA'₁,
    Formalism.MainNotions.Closed 𝒞 fun Fm _ =>
      ∀ (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
        (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) u u', LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' Cw)
        (Z : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), TermLocs (Fm.D x i) (X x hx i))
        (cN : ∀ x (i : Fm.Ix x), (Fm.D x i).what₂.Word → (Fm.D x i).what₂.Word → ℝ),
        PeriodFamilyStatement Fm X Cw Y Z cN Vm C0 Cg cb Cu cT CT Ca Cq CA CA' Ce

def ClosedFormAtFamilyConstants (𝒞 : Formalism.MainNotions.FamClass) (Vm : ∀ k r, ValMap k r) : Prop :=
  ∃ Ca₀ CA₁ CA'₁ Ce : ℝ, ∀ Ca ≥ Ca₀, ∀ CA ≥ CA₁, ∀ CA' ≥ CA'₁, ∀ C0 Cq Cw : ℝ,
    Formalism.MainNotions.Closed 𝒞 fun Fm _ =>
      ∀ (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
        (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) u u', LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' Cw)
        (Z : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), TermLocs (Fm.D x i) (X x hx i))
        (cN : ∀ x (i : Fm.Ix x), (Fm.D x i).what₂.Word → (Fm.D x i).what₂.Word → ℝ),
        PeriodFamilyStatement Fm X Cw Y Z cN Vm C0 (sCg Fm) sCb sCu scT (sCT Fm) Ca Cq CA CA' Ce

def ClosedFirstSizeStatement (𝒞 : Formalism.MainNotions.FamClass) : Prop :=
  ∀ C0 Cg cb Cu cT CT C3 : ℝ, ∃ C1 C2 C3' C4 CV : ℝ, ∀ CA : ℝ, 0 < CA → ∃ c5 : ℝ, 0 < c5 ∧
    Formalism.MainNotions.Closed 𝒞 fun Fm _ => DeterminantValueFamily Fm C0 Cg cb Cu cT CT C3 C1 C2 C3' C4 c5 CA (1 / 3) CV

def LocalTopSecond (𝒞 : Formalism.MainNotions.FamClass) : Prop :=
  Formalism.MainNotions.Closed 𝒞 fun Fm _ => ∀ C0 Cg cb Cu cT CT : ℝ, FamilyUnfoldingCount Fm C0 Cg cb Cu cT CT

end Closed

end Formalism.MainNotions.LocalBesselAndTopKernel
