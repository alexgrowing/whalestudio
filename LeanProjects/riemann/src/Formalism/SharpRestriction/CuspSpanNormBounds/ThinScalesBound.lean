import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.LinQRawRange
import Formalism.SharpRestriction.ParConsts

noncomputable section

open ValuativeRel MeasureTheory ComplexConjugate ComplexOrder
open Formalism.MainNotions.S.Loc

namespace Formalism.MainNotions.ThinScalesBound

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

def A2 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK → A2at M

def A13 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK → MeasureVanishingDeterminant M

def partA (D : Formalism.BasicNotions.D7) : Prop := A2 D ∧ A13 D

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

def partT (D : Formalism.BasicNotions.D7) (C : ℝ) : Prop :=
  4 * D.R.rS + 8 ≤ D.R.k → T0 D ∧ T1 D C ∧ T2 D ∧ T3 D

def adm1 (_D : Formalism.BasicNotions.D7) : Prop :=
  AllLoc fun {_F} _ _ _ {E} _ _ _ _ M => IsField E →
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (S₁ S₂ : Submodule E V)
    (σ : S₁ ≃ₗ[E] S₂), (∀ x y : S₁, H.h (σ x) (σ y) = H.h x y) →
    ∃ g : V ≃ₗ[E] V, (∀ x y, H.h (g x) (g y) = H.h x y) ∧ ∀ x : S₁, g x = σ x

def adm2 (_D : Formalism.BasicNotions.D7) : Prop :=
  AllLoc fun {_F} _ _ _ {E} _ _ _ _ M =>
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (abelian₂ : Submodule M.L.O V),
    H.IsSelfDual abelian₂ → ∀ (U : Submodule E V) (hU : IsCompl U (H.perp U)),
    (∀ u : V, u ∈ U → ((∃ x ∈ abelian₂, (Submodule.linearProjOfIsCompl U (H.perp U) hU x : V) = u) ↔
        ∀ y ∈ abelian₂, y ∈ U → H.h u y ∈ M.L.O)) ∧
    (∀ u : V, u ∈ H.perp U → ((∃ x ∈ abelian₂,
        (Submodule.linearProjOfIsCompl (H.perp U) U hU.symm x : V) = u) ↔
        ∀ y ∈ abelian₂, y ∈ H.perp U → H.h u y ∈ M.L.O))

def adm3 (_D : Formalism.BasicNotions.D7) : Prop :=
  AllLoc fun {F} _ _ _ {_E} _ _ _ _ _M =>
  ∀ (f : Polynomial 𝒪[F]) (a : 𝒪[F]),
    valuation F ((f.eval a : 𝒪[F]) : F) < valuation F ((f.derivative.eval a : 𝒪[F]) : F) ^ 2 →
    ∃ b : 𝒪[F], f.eval b = 0 ∧
      valuation F (((b - a : 𝒪[F])) : F) < valuation F ((f.derivative.eval a : 𝒪[F]) : F)

def ArithmeticRiemannRochThetaCond (_D : Formalism.BasicNotions.D7) : Prop :=
  AllLoc fun {F} _ _ _ {_E} _ _ _ _ _M =>
  ∀ [MeasurableSpace F] [BorelSpace F] (μ : Measure F), μ.IsAddHaarMeasure →
    μ (𝒪[F] : Set F) = 1 →
  ∀ (ψ : AddChar F ℂ), Continuous ψ → (∀ x : F, (∀ y ∈ 𝒪[F], ψ (x * y) = 1) ↔ x ∈ 𝒪[F]) →
  ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) F), H.IsSymm → H.det ≠ 0 →
  ∀ (L : AddSubgroup (Fin d → F)), IsCompact (L : Set (Fin d → F)) → IsOpen (L : Set (Fin d → F)) →
  ∃ δ : ℝ, 0 < δ ∧ ∀ t : F, t ≠ 0 → (μ ((fun y => t * y) '' (𝒪[F] : Set F))).toReal < δ →
    ‖∫ x in (L : Set (Fin d → F)), ψ (dotProduct x (H.mulVec x) / (2 * t))
        ∂(Measure.pi fun _ : Fin d => μ)‖ =
      (μ ((fun y => (t⁻¹ • H).det * y) '' (𝒪[F] : Set F))).toReal ^ (-(1 / 2 : ℝ))

def Om {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) {n : ℕ} (Φ : Matrix (Fin n) (Fin n) E → ℂ) (w : Pt E n) : ℂ :=
  ∫ xy : (IL n → E) × (IN w → E), Φ (uLow xy.1 * w.mat * uUp w xy.2) *
      M.psiR (simpleLow (uLow xy.1) + simpleUp (uUp w xy.2))
    ∂((Measure.pi fun _ : IL n => M.mu).prod (Measure.pi fun _ : IN w => M.mu))

def ptTC {E : Type} [CommRing E] (m : ℕ) (t c : Eˣ) : Pt E (m + 2) :=
  ⟨[(t, ⟨m + 1, Nat.succ_pos m⟩), (c, 1)], by simp⟩

def ptZ {E : Type} [CommRing E] (m : ℕ) (z : Eˣ) : Pt E (m + 2) :=
  ⟨[(z, ⟨m + 2, Nat.succ_pos (m + 1)⟩)], by simp⟩

def RTTRelation (_D : Formalism.BasicNotions.D7) : Prop :=
  AllLoc fun {_F} _ _ _ {E} _ _ _ _ M =>
  ∀ m : ℕ, ∃ ga : Eˣ → ℂ, (∀ x, ‖ga x‖ = 1) ∧ (∀ x u : Eˣ, ga (x * u ^ 2) = ga x) ∧
  ∀ (Φ : Matrix (Fin (m + 2)) (Fin (m + 2)) E → ℂ) (Ω : Set E), IsCompact Ω → (∀ x ∈ Ω, IsUnit x) →
    (∃ B : Set (Matrix (Fin (m + 2)) (Fin (m + 2)) E), IsCompact B ∧ ∀ Z ∉ B, Φ Z = 0) →
    (∃ U : Set (Matrix (Fin (m + 2)) (Fin (m + 2)) E), IsOpen U ∧ 0 ∈ U ∧
      ∀ Z X, (Z.det ∈ Ω ∨ -Z.det ∈ Ω) → X ∈ U → Φ (Z + X) = Φ Z) →
    ∃ U₀ : Set E, IsOpen U₀ ∧ (0 : E) ∈ U₀ ∧ ∀ t c : Eˣ, (t : E) ∈ U₀ → (c : E) * (t : E) ^ (m + 1) ∈ Ω →
      Om M Φ (ptTC m t c) =
        ((M.modK (t : E) ^ (-(((m : ℝ) + 1) ^ 2 / 2)) * M.modK ((m : E) + 2) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ᶠ (z : Eˣ) (_ : (z : E) ^ (m + 2) = (-1) ^ (m + 1) * ((c : E) * (t : E) ^ (m + 1))),
            ((M.modK (z : E) ^ (((m : ℝ) + 1) ^ 2 / 2) : ℝ) : ℂ) * ga (z * t) *
              M.psiR (((m : E) + 2) * (z : E) * ((t⁻¹ : Eˣ) : E)) * Om M Φ (ptZ m z)

def ArchimedeanSignatureMatching (D : Formalism.BasicNotions.D7) : Prop := ArithmeticRiemannRochThetaCond D ∧ RTTRelation D

def adm5 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (Γ : Type) [AddCommGroup Γ] [Countable Γ] (φ : Γ → ℂ),
    (∀ (N : ℕ) (g : Fin N → Γ) (c : Fin N → ℂ),
      0 ≤ ∑ i, ∑ j, c i * conj (c j) * φ (g i - g j)) →
    letI : TopologicalSpace (Multiplicative Γ) := ⊥
    letI : MeasurableSpace (PontryaginDual (Multiplicative Γ)) := borel _
    ∃ μ : Measure (PontryaginDual (Multiplicative Γ)), IsFiniteMeasure μ ∧
      ∀ γ : Γ, φ γ = ∫ χ, ((χ (Multiplicative.ofAdd γ) : Circle) : ℂ) ∂μ

def aux₃ (D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := partT D C ∧ partA D

def admitted (D : Formalism.BasicNotions.D7) : Prop := adm1 D ∧ adm2 D ∧ adm3 D ∧ ArchimedeanSignatureMatching D ∧ adm5 D

def Stmt (D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := admitted D → aux₃ D C

def ThinScalesBoundExists (D : Formalism.BasicNotions.D7) : Prop := ∃ C : ℝ, aux₃ D C

def UniformExportStatement (D : Formalism.BasicNotions.D7) : Prop := admitted D → ThinScalesBoundExists D

def PartTStatement (D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := adm1 D ∧ adm2 D ∧ adm3 D → partT D C

def IntegralityGoodReduction (D : Formalism.BasicNotions.D7) : Prop := ArchimedeanSignatureMatching D ∧ adm5 D → partA D

def FamilyThinScalesBound {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C : ℝ) : Prop :=
  ∀ x (i : Fm.Ix x), aux₃ (Fm.D x i) C

def OrbitValuationBound {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∃ C : ℝ, FamilyThinScalesBound Fm C

def admF1 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), adm1 (Fm.D x i)
def admF2 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), adm2 (Fm.D x i)
def admF3 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), adm3 (Fm.D x i)
def admF4 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), ArchimedeanSignatureMatching (Fm.D x i)
def admF5 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), adm5 (Fm.D x i)

def AdmF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  admF1 Fm ∧ admF2 Fm ∧ admF3 Fm ∧ admF4 Fm ∧ admF5 Fm

def KudlaFamilyStatement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := AdmF Fm → OrbitValuationBound Fm

def KappaDegreeStatement (DF : Formalism.MainNotions.DFamP) : Prop :=
  ∃ C : ℝ, ∀ (ε : ℝ) (h1 : 0 < ε) (h2 : ε < 1 / 52), AdmF (DF ε h1 h2) → FamilyThinScalesBound (DF ε h1 h2) C

end Formalism.MainNotions.ThinScalesBound

end
