import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Formalism.HermitianLattices.StatementMass

noncomputable section

namespace Formalism.MainNotions.S.UnitaryVolumeMass

open NumberField Matrix Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt
open scoped ENNReal NNReal InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev Lt (D : D7) : Type := Submodule (𝓞 D.host.E) (hS D).V

abbrev Fl (D : D7) (T : ℕ) : Type := LFlag (hS D) D.R.rS ((T : ℕ) : D.host.E)

def DefiniteComplementRank (D : D7) (Λ : Lt D) {T T' : ℕ} (F : Fl D T) (F' : Fl D T') : Prop :=
  finrank D.host.E (Hp Λ F F') = D.R.k - 1 ∧
    ∀ τ : D.host.E →+* ℂ, ∀ x ∈ Hp Λ F F', x ≠ 0 → 0 < nrm (hS D) τ x

def Lem1 (D : D7) (Λ : Lt D) (g : ℕ) {T T' : ℕ} (F : Fl D T) (F' : Fl D T') : Prop :=
  Finite (BQ Λ F F') ∧
  ((iIdx Λ g F F' : ℕ) : ℝ) ≤ (Nat.card (gB Λ g F F') : ℝ) ∧
  (Nat.card (gB Λ g F F') : ℝ) ≤
    (Nat.card (BQ Λ F F') : ℝ) / NE (E := D.host.E) g ^ (D.R.rS + 1) ∧
  latDet (hS D) (La Λ g F F') =
    NG Λ F F' / ((Nat.card (BQ Λ F F') : ℝ) * (iIdx Λ g F F' : ℝ)) ∧
  ∃ φ : (La Λ g F F' ⧸ (Thp Λ F F').comap (La Λ g F F').subtype) →ₗ[𝓞 D.host.E] gB Λ g F F',
    Function.Injective φ ∧ (∀ c, ((φ c : BQ Λ F F') ∈ noZ Λ F F')) ∧
    ∀ (x : La Λ g F F'), ∀ l ∈ Lrep Λ F, ∀ l' ∈ Lrep Λ F',
      (x : (hS D).V) - l ∈ Xsp F → (x : (hS D).V) - l' ∈ Xsp F' →
        ∃ h : l - l' ∈ BLat Λ F F',
          (φ (Submodule.Quotient.mk x) : BQ Λ F F') = Submodule.Quotient.mk ⟨l - l', h⟩

def Lem2 (D : D7) (Λ : Lt D) (T T' : ℕ) (F : Fl D T) (F' : Fl D T') : Prop :=
  (∀ y ∈ Ylift Λ F F', ∀ y' ∈ Ylift' Λ F F',
      ∃! p : D.host.E × D.host.E, SgRel F F' y y' p.1 p.2) ∧
  (∀ y₁ ∈ Ylift Λ F F', ∀ y₂ ∈ Ylift Λ F F', ∀ y₁' ∈ Ylift' Λ F F', ∀ y₂' ∈ Ylift' Λ F F',
      ∀ al al' : D.host.E, SgRel F F' y₁ y₁' al al' → SgRel F F' y₂ y₂' al al' →
        y₁ - y₂ ∈ Xsp F ∧ y₁' - y₂' ∈ Xsp F') ∧
  (∀ al al' : D.host.E, ∃ y ∈ Ylift Λ F F', ∃ y' ∈ Ylift' Λ F F', SgRel F F' y y' al al') ∧
  (∀ τ : D.host.E →+* ℂ, ∀ y ∈ Ylift Λ F F', ∀ y' ∈ Ylift' Λ F F', ∀ al al' : D.host.E,
      SgRel F F' y y' al al' →
        nrm (hS D) τ y - nrm (hS D) τ y' = (T : ℝ) * ‖τ al‖ ^ 2 - (T' : ℝ) * ‖τ al'‖ ^ 2) ∧
  (∀ τ : D.host.E →+* ℂ, ∀ y ∈ Ylift Λ F F', ∀ y' ∈ Xsp F', ∀ al al' : D.host.E,
      SgRel F F' y y' al al' →
        (T : ℝ) * ‖τ al‖ ^ 2 = chSh T T' F F' τ ^ 2 * nrm (hS D) τ y ∧
        (T' : ℝ) * ‖τ al'‖ ^ 2 = invSh T T' F F' τ ^ 2 * nrm (hS D) τ y) ∧
  (∀ τ : D.host.E →+* ℂ, ∀ y ∈ Xsp F, ∀ y' ∈ Ylift' Λ F F', ∀ al al' : D.host.E,
      SgRel F F' y y' al al' →
        (T : ℝ) * ‖τ al‖ ^ 2 = invSh T T' F F' τ ^ 2 * nrm (hS D) τ y' ∧
        (T' : ℝ) * ‖τ al'‖ ^ 2 = chSh T T' F F' τ ^ 2 * nrm (hS D) τ y')

def LatticeSpanEquality (D : D7) (Λ : Lt D) (g : ℕ) {T T' : ℕ} (F : Fl D T) (F' F'' : Fl D T')
    (β : (hS D).V ≃ₗ[D.host.E] (hS D).V) (W : Submodule D.host.E (hS D).V) : Prop :=
  Mlat Λ F F' F'' β g ⊔ toO (hS D) (Xsp F) = Mlat'' Λ F F' F'' β g ⊔ toO (hS D) (Xsp F) ∧
  finrank D.host.E (spanE (hS D) (Psi Λ F F' F'' β W (La Λ g F F'))) = s0 Λ F F' F'' β D.R.k - 1 ∧
  finrank D.host.E (spanE (hS D) (Psi Λ F F' F'' β W (La Λ g F F''))) = s0 Λ F F' F'' β D.R.k - 1 ∧
  latDet (hS D) (Mlat Λ F F' F'' β g) ^ 2 =
    latDet (hS D) (La Λ g F F') * latDet (hS D) (La Λ g F F'') /
      (latDet (hS D) (Psi Λ F F' F'' β W (La Λ g F F')) *
        latDet (hS D) (Psi Λ F F' F'' β W (La Λ g F F''))) ∧
  (∀ x' ∈ La Λ g F F', ∀ x'' ∈ La Λ g F F'',
      ∃ o : 𝓞 D.host.E, bForm β x' x'' = (g : D.host.E) * (o : D.host.E)) ∧
  (∀ x' ∈ La Λ g F F', ∀ x'' ∈ La Λ g F F'',
      (x' ∈ Th Λ F F' F'' β ∨ x'' ∈ Th'' Λ F F' F'' β) → bForm β x' x'' = 0) ∧
  (∀ τ : D.host.E →+* ℂ, ∀ x' ∈ La Λ g F F', ∀ x'' ∈ La Λ g F F'', ∀ s' s'' : (hS D).V,
      IsProjS Λ F F' F'' β W x' s' → IsProjS Λ F F' F'' β W x'' s'' →
        ‖τ (bForm β x' x'')‖ ≤
          2 * Real.sqrt (nrm (hS D) τ s') * Real.sqrt (nrm (hS D) τ s'')) ∧
  (∀ x'₁ ∈ La Λ g F F', ∀ x'₂ ∈ La Λ g F F', ∀ s' : (hS D).V,
      IsProjS Λ F F' F'' β W x'₁ s' → IsProjS Λ F F' F'' β W x'₂ s' →
        ∀ x'' ∈ La Λ g F F'', bForm β x'₁ x'' = bForm β x'₂ x'') ∧
  (∀ x''₁ ∈ La Λ g F F'', ∀ x''₂ ∈ La Λ g F F'', ∀ s'' : (hS D).V,
      IsProjS Λ F F' F'' β W x''₁ s'' → IsProjS Λ F F' F'' β W x''₂ s'' →
        ∀ x' ∈ La Λ g F F', bForm β x' x''₁ = bForm β x' x''₂)

def ThmA (D : D7) (Λ : Lt D) (T T' g : ℕ) (F : Fl D T) (F' F'' : Fl D T')
    (β : (hS D).V ≃ₗ[D.host.E] (hS D).V) : Prop :=
  (BNondeg Λ F F' F'' β →
    latDet (hS D) (Mlat Λ F F' F'' β g) * (iIdx Λ g F F' : ℝ) * (iIdx Λ g F F'' : ℝ) ≤
      (2 / (g : ℝ)) ^ ((s0 Λ F F' F'' β D.R.k - 1) * D.R.f) *
        Real.sqrt (G0 Λ g F F' * G0 Λ g F F'')) ∧
  (¬ BNondeg Λ F F' F'' β →
    finrank D.host.E (radL Λ F F' F'' β) = finrank D.host.E (Th Λ F F' F'' β) + 1 ∧
    finrank D.host.E (radR Λ F F' F'' β) = finrank D.host.E (Th Λ F F' F'' β) + 1 ∧
    latDet (hS D) (Mlat Λ F F' F'' β g) * (iIdx Λ g F F' : ℝ) * (iIdx Λ g F F'' : ℝ) ≤
      (2 / (g : ℝ)) ^ ((s0 Λ F F' F'' β D.R.k - 2) * D.R.f) *
        Real.sqrt (G0 Λ g F F' * G0 Λ g F F'') * ((T : ℝ) ^ D.R.f)⁻¹ *
        placeProd (fun τ : D.host.E →+* ℂ => onePlusChSh T T' F F' τ * onePlusChSh T T' F F'' τ))

def HyperplaneEquality (D : D7) (Λ : Lt D) {T T' : ℕ} (F : Fl D T) (F' F'' : Fl D T')
    (β : (hS D).V ≃ₗ[D.host.E] (hS D).V) : Prop :=
  Hp Λ F F' = Th Λ F F' F'' β ∧ Hp Λ F F'' = Th'' Λ F F' F'' β

def ThmB (D : D7) (Λ : Lt D) (T T' g : ℕ) (F : Fl D T) (F' F'' : Fl D T')
    (β : (hS D).V ≃ₗ[D.host.E] (hS D).V) : Prop :=
  IsScalar Λ F F' F'' β ∨
    ((T : ℝ) * (T' : ℝ) / (g : ℝ) ^ 2) ^ ((D.R.f : ℝ) / 2) ≤
      placeProd (fun τ : D.host.E →+* ℂ =>
        chSh T T' F F' τ * invSh T T' F F'' τ + invSh T T' F F' τ * chSh T T' F F'' τ)

def DefiniteComplementAtWord (D : D7) (u : D.what₂.Word) (T' : ℕ) : Prop :=
  ∀ (Λ : Lt D) (F : Fl D (Tu D u)) (F' : Fl D T'),
    FixedHyp D Λ F → PrimeHyp D u T' → IsTerm Λ (gS D) F F' → DefiniteComplementRank D Λ F F'

def DefiniteComplementAllWords (D : D7) : Prop := ∀ (u : D.what₂.Word) (T' : ℕ), DefiniteComplementAtWord D u T'

def stLem1At (D : D7) (u : D.what₂.Word) (T' : ℕ) : Prop :=
  ∀ (Λ : Lt D) (F : Fl D (Tu D u)) (F' : Fl D T'),
    FixedHyp D Λ F → PrimeHyp D u T' → IsTerm Λ (gS D) F F' → Lem1 D Λ (gS D) F F'

def stLem1 (D : D7) : Prop := ∀ (u : D.what₂.Word) (T' : ℕ), stLem1At D u T'

def stLem2At (D : D7) (u : D.what₂.Word) (T' : ℕ) : Prop :=
  ∀ (Λ : Lt D) (F : Fl D (Tu D u)) (F' : Fl D T'),
    FixedHyp D Λ F → PrimeHyp D u T' → IsTerm Λ (gS D) F F' → Lem2 D Λ (Tu D u) T' F F'

def stLem2 (D : D7) : Prop := ∀ (u : D.what₂.Word) (T' : ℕ), stLem2At D u T'

def HyperplaneRankAtWord (D : D7) (u : D.what₂.Word) (T' : ℕ) : Prop :=
  ∀ (Λ : Lt D) (F : Fl D (Tu D u)) (F' F'' : Fl D T') (β : (hS D).V ≃ₗ[D.host.E] (hS D).V),
    FixedHyp D Λ F → PrimeHyp D u T' → IsTerm Λ (gS D) F F' → IsTerm Λ (gS D) F F'' →
    IsPair Λ F F' F'' β (gS D) → 2 ≤ s0 Λ F F' F'' β D.R.k →
      ∀ W : Submodule D.host.E (hS D).V, WHyp D F W → LatticeSpanEquality D Λ (gS D) F F' F'' β W

def HyperplaneRankAllWords (D : D7) : Prop := ∀ (u : D.what₂.Word) (T' : ℕ), HyperplaneRankAtWord D u T'

def stThmAAt (D : D7) (u : D.what₂.Word) (T' : ℕ) : Prop :=
  ∀ (Λ : Lt D) (F : Fl D (Tu D u)) (F' F'' : Fl D T') (β : (hS D).V ≃ₗ[D.host.E] (hS D).V),
    FixedHyp D Λ F → PrimeHyp D u T' → IsTerm Λ (gS D) F F' → IsTerm Λ (gS D) F F'' →
    IsPair Λ F F' F'' β (gS D) → 2 ≤ s0 Λ F F' F'' β D.R.k →
      ThmA D Λ (Tu D u) T' (gS D) F F' F'' β

def stThmA (D : D7) : Prop := ∀ (u : D.what₂.Word) (T' : ℕ), stThmAAt D u T'

def DefiniteRankOneAtWord (D : D7) (u : D.what₂.Word) (T' : ℕ) : Prop :=
  ∀ (Λ : Lt D) (F : Fl D (Tu D u)) (F' F'' : Fl D T') (β : (hS D).V ≃ₗ[D.host.E] (hS D).V),
    FixedHyp D Λ F → PrimeHyp D u T' → IsTerm Λ (gS D) F F' → IsTerm Λ (gS D) F F'' →
    IsPair Λ F F' F'' β (gS D) → s0 Λ F F' F'' β D.R.k = 1 → HyperplaneEquality D Λ F F' F'' β

def DefiniteRankOneAllWords (D : D7) : Prop := ∀ (u : D.what₂.Word) (T' : ℕ), DefiniteRankOneAtWord D u T'

def stThmBAt (D : D7) (u : D.what₂.Word) (T' : ℕ) : Prop :=
  ∀ (Λ : Lt D) (F : Fl D (Tu D u)) (F' F'' : Fl D T') (β : (hS D).V ≃ₗ[D.host.E] (hS D).V),
    FixedHyp D Λ F → PrimeHyp D u T' → IsTerm Λ (gS D) F F' → IsTerm Λ (gS D) F F'' →
    IsPair Λ F F' F'' β (gS D) → s0 Λ F F' F'' β D.R.k = 1 →
    IsGeneric Λ (gS D) F F' → IsGeneric Λ (gS D) F F'' →
      ThmB D Λ (Tu D u) T' (gS D) F F' F'' β

def stThmB (D : D7) : Prop := ∀ (u : D.what₂.Word) (T' : ℕ), stThmBAt D u T'

def stGlue (D : D7) : Prop :=
  ∀ Λ : Lt D, Submodule.IsLattice D.host.E Λ → Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT Λ →
  ∀ U : Submodule D.host.E (hS D).V, U ⊓ orth (hS D) U = ⊥ →
    {m | m ∈ U ∧ ∃ l ∈ Λ, l - m ∈ orth (hS D) U} =
        (dualIn (hS D) (Λ ⊓ toO (hS D) U) : Set (hS D).V) ∧
    Nonempty
      ((Λ ⧸ ((Λ ⊓ toO (hS D) U) ⊔ (Λ ⊓ toO (hS D) (orth (hS D) U))).comap Λ.subtype) ≃ₗ[𝓞 D.host.E]
        (dualIn (hS D) (Λ ⊓ toO (hS D) U) ⧸
          (Λ ⊓ toO (hS D) U).comap (dualIn (hS D) (Λ ⊓ toO (hS D) U)).subtype)) ∧
    Nonempty
      ((dualIn (hS D) (Λ ⊓ toO (hS D) U) ⧸
          (Λ ⊓ toO (hS D) U).comap (dualIn (hS D) (Λ ⊓ toO (hS D) U)).subtype) ≃ₗ[𝓞 D.host.E]
        (dualIn (hS D) (Λ ⊓ toO (hS D) (orth (hS D) U)) ⧸
          (Λ ⊓ toO (hS D) (orth (hS D) U)).comap
            (dualIn (hS D) (Λ ⊓ toO (hS D) (orth (hS D) U))).subtype)) ∧
    latDet (hS D) (Λ ⊓ toO (hS D) U) = latDet (hS D) (Λ ⊓ toO (hS D) (orth (hS D) U))

def stGlueDisc (D : D7) : Prop :=
  ∀ Λ : Lt D, Submodule.IsLattice D.host.E Λ → Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT Λ →
  ∀ U : Submodule D.host.E (hS D).V, U ⊓ orth (hS D) U = ⊥ →
    Nonempty
      ((dualIn (hS D) (Λ ⊓ toO (hS D) U) ⧸
          (Λ ⊓ toO (hS D) U).comap (dualIn (hS D) (Λ ⊓ toO (hS D) U)).subtype) ≃ₗ[𝓞 D.host.E]
        (dualIn (hS D) (Λ ⊓ toO (hS D) (orth (hS D) U)) ⧸
          (Λ ⊓ toO (hS D) (orth (hS D) U)).comap
            (dualIn (hS D) (Λ ⊓ toO (hS D) (orth (hS D) U))).subtype)) ∧
    latDet (hS D) (Λ ⊓ toO (hS D) U) = latDet (hS D) (Λ ⊓ toO (hS D) (orth (hS D) U))

def stKron (D : D7) : Prop :=
  ∀ α : 𝓞 D.host.E, (∀ τ : D.host.E →+* ℂ, ‖τ (α : D.host.E)‖ = 1) → ∃ n : ℕ, 0 < n ∧ α ^ n = 1

section Cores

variable (D : D7)

def FormAt (u : D.what₂.Word) : Prop :=
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ what₂ : Finset (LatV D), IsRowReps D F0 what₂ →
    gaG D * massRows D F0 what₂ * dimPi (hc := D.hcW) u = D.duS u

def LoopPairSumBound (u u' : D.what₂.Word) (c : ℝ) : Prop :=
  ∀ S : Finset (D.s.Pair u u'), (∀ p ∈ S, loopP D.s p) →
    gaG D * ∑ p ∈ S, ‖D.s.pval p‖ ≤
      Real.exp (-(c * (D.R.k : ℝ) * (D.R.f : ℝ) * Real.log (D.R.k : ℝ))) *
        ((D.duS u : ℝ) * (D.duS u' : ℝ)) / D.what₂.Dstar

def Mass2At (large₂ : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module D.host.E V] [Module (𝓞 D.host.E) V]
    [IsScalarTower (𝓞 D.host.E) D.host.E V]
    (h : V →ₗ⋆[D.host.E] V →ₗ[D.host.E] D.host.E) (L : Submodule (𝓞 D.host.E) V),
    h.IsSymm → Formalism.HermitianLatticesTheory.IsOrthoLattice h L 2 →
      Formalism.HermitianLatticesTheory.mass h L ≤ (large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f)) ^ C

end Cores

section Mass

def stMassRatio (D : D7) : Prop :=
  ∀ (j : ℕ), 3 ≤ j →
    ∀ (V V' : Type) [AddCommGroup V] [Module D.host.E V] [Module (𝓞 D.host.E) V]
      [IsScalarTower (𝓞 D.host.E) D.host.E V] [AddCommGroup V'] [Module D.host.E V']
      [Module (𝓞 D.host.E) V'] [IsScalarTower (𝓞 D.host.E) D.host.E V']
      (h : V →ₗ⋆[D.host.E] V →ₗ[D.host.E] D.host.E) (h' : V' →ₗ⋆[D.host.E] V' →ₗ[D.host.E] D.host.E)
      (L : Submodule (𝓞 D.host.E) V) (L' : Submodule (𝓞 D.host.E) V'),
      h.IsSymm → h'.IsSymm → Formalism.HermitianLatticesTheory.IsOrthoLattice h L j → Formalism.HermitianLatticesTheory.IsOrthoLattice h' L' (j - 1) →
      Formalism.HermitianLatticesTheory.mass h L / Formalism.HermitianLatticesTheory.mass h' L' = Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E j

def stMassL (D : D7) : Prop :=
  ∀ i : ℕ, 2 ≤ i →
    |Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E i)| ≤ (D.R.f : ℝ) * Real.log (riemannZeta (i : ℂ)).re

def stMass2 (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → Mass2At D large₂ C

def stMassVol (D : D7) (G : GlobalTheoryTheory.GenusMassVolumes.GaugeFam D.host.F D.host.E D.sp.cm.sig) : Prop :=
  ∀ (j : ℕ) (e : Fin j → (hS D).V) (U : Submodule D.host.E (hS D).V), 2 ≤ j → LinearIndependent D.host.E e →
    U ≤ Wb D → Submodule.span D.host.E (Set.range e) = Wb D ⊓ orth (hS D) U →
    (∀ τ : D.host.E →+* ℂ, ∀ y ∈ Submodule.span D.host.E (Set.range e), y ≠ 0 → 0 < nrm (hS D) τ y) →
    GlobalTheoryTheory.GenusMassVolumes.volHE G j (Matrix.of fun a b => (hS D).hT (e a) (e b)) = GlobalTheoryTheory.GenusMassVolumes.volHE G j 1

end Mass

section BR

def embU (k : ℕ) (h : Matrix (Fin k) (Fin k) ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks h 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ))

def stBRmult : Prop :=
  ∀ (k : ℕ) (u : Fin (k + 1) → ℝ) (u' : Fin k → ℝ) (H H' : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    (π : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ → (H →L[ℂ] H)) (ρ : Matrix (Fin k) (Fin k) ℂ → (H' →L[ℂ] H')),
    IsHCTypeU (k + 1) u π → IsHCTypeU k u' ρ →
    ∀ A B : H' →L[ℂ] H,
      (∀ h ∈ UJset (allPos k), A.comp (ρ h) = (π (embU k h)).comp A) →
      (∀ h ∈ UJset (allPos k), B.comp (ρ h) = (π (embU k h)).comp B) →
      A ≠ 0 → ∃ c : ℂ, B = c • A

def stBRhad : Prop :=
  ∀ (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ), ‖A.det‖ ≤ ∏ j, Real.sqrt (∑ i, ‖A i j‖ ^ 2)

def succMin {N : ℕ} (M : Submodule ℤ (EuclideanSpace ℝ (Fin N))) (i : ℕ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ ∃ v : Fin i → EuclideanSpace ℝ (Fin N),
    (∀ j, v j ∈ M) ∧ LinearIndependent ℝ v ∧ ∀ j, ‖v j‖ ≤ t}

def dualZ {N : ℕ} (M : Submodule ℤ (EuclideanSpace ℝ (Fin N))) : Submodule ℤ (EuclideanSpace ℝ (Fin N)) where
  carrier := {x | ∀ y ∈ M, ∃ z : ℤ, ⟪x, y⟫_ℝ = z}
  add_mem' := by
    intro a b ha hb y hy
    obtain ⟨z1, h1⟩ := ha y hy
    obtain ⟨z2, h2⟩ := hb y hy
    exact ⟨z1 + z2, by rw [inner_add_left, h1, h2]; push_cast; ring⟩
  zero_mem' := fun y _ => ⟨0, by simp⟩
  smul_mem' := by
    intro c a ha y hy
    obtain ⟨z, h⟩ := ha y hy
    exact ⟨c * z, by rw [← Int.cast_smul_eq_zsmul ℝ c a, real_inner_smul_left, h]; push_cast; ring⟩

def stBRtrans : Prop :=
  ∀ (N : ℕ) (M : Submodule ℤ (EuclideanSpace ℝ (Fin N))),
    DiscreteTopology M → Submodule.span ℝ (M : Set (EuclideanSpace ℝ (Fin N))) = ⊤ →
    ∀ i, 1 ≤ i → i ≤ N → succMin M i * succMin (dualZ M) (N + 1 - i) ≤ N

def stBRmink : Prop :=
  ∀ (N : ℕ) (G : Subgroup (GL (Fin N) ℤ)), Finite G → Nat.card G ∣ (2 * N).factorial

end BR

section Rows

variable (D : D7)

def stSW (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ what₂ : Finset (LatV D), IsRowReps D F0 what₂ →
  ∀ Z : GramM D, RelZ D Z →
    MeanLe D F0 what₂ (fun Λ => cntSW D ((Tu D u' : ℕ) : D.host.E) (lf D F0) Λ Z)
      (HHZ D large₂.sc.b C Z ^ (C * (D.R.rS : ℝ) ^ 2) * ∏ τ, nV D (Tu D u) (Tu D u') Z τ)

def stForm (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → FormAt D u

end Rows

def stTprod (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 δ : ℝ) : Prop :=
  Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ w : D.what₂.Word,
    |D.what₂.Dstar / (D.duS w : ℝ) - ∏ τ, (Tcrit D w τ / Tr D w) ^ D.R.k| ≤
      δ * ∏ τ, (Tcrit D w τ / Tr D w) ^ D.R.k

def stTcritLow (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ (w : D.what₂.Word) (τ : D.what₂.Tau),
    (D.R.k : ℝ) ^ (3 * D.R.rS) ≤ gg D ^ (-(D.R.m : ℝ)) * Tcrit D w τ

section Loc

open MeasureTheory Finset Formalism.QuantumDeterminants

variable (D : D7) (large₂ : SizeData₂ D)

def stPT (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W →
    ∀ lam', l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ A : LocS W, GoodS D lam' A →
      ∀ μsec, IsSection D.R.k D.R.rS W.z W.z' μsec →
      ∀ γ p, RelPt D W.z W.z' γ p → ∀ θ', normWin D large₂ C1 θ' → ∀ νR, RMeas D W γ θ' νR →
        ENNReal.ofReal (ptWeight D.R.k D.R.rS (Tr D w) (Tr D w') p * hsNormSq (A.J νR γ)) ≤
          ENNReal.ofReal (large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 4) *
            (max 1 (Gf D.R.k D.R.rS W.z W.z' γ)⁻¹) ^ (C * (D.R.m : ℝ) ^ 2)) * MMv D w w' A μsec

def stPTsum (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W →
    ∀ (ι : Type) [Fintype ι] (lams : ι → Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (As : ι → LocS W) (a : ι → ℂ),
      (∀ i, l1dist (lams i) (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 ∧ GoodS D (lams i) (As i)) →
      ∀ μsec, IsSection D.R.k D.R.rS W.z W.z' μsec →
      ∀ γ p, RelPt D W.z W.z' γ p → ∀ θ', normWin D large₂ C1 θ' → ∀ νR, RMeas D W γ θ' νR →
        ptWeight D.R.k D.R.rS (Tr D w) (Tr D w') p *
            hsNormSq (∑ i, a i • jhUnit D w w' (As i) μsec νR γ) ≤
          large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 4) *
            (max 1 (Gf D.R.k D.R.rS W.z W.z' γ)⁻¹) ^ (C * (D.R.m : ℝ) ^ 2) * (∑ i, ‖a i‖) ^ 2

def stPTDl (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W →
    ∀ lam', l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ A₀ : LocS W, GoodS D lam' A₀ →
    ∀ l : ℕ, l ≤ D.R.rS + 1 → ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      ∀ AI : Finset (Fin (2 * D.R.rS + D.R.k + 1)) → LocS W,
        (∀ I, I.card = l → (∃ A : LocS W, GoodS D (lam' + s • epsI I) A) → GoodS D (lam' + s • epsI I) (AI I)) →
        ∃ a : Finset (Fin (2 * D.R.rS + D.R.k + 1)) → ℂ,
          (∀ I, I.card = l → (¬ ∃ A : LocS W, GoodS D (lam' + s • epsI I) A) → a I = 0) ∧
          (∑ I ∈ univ.filter (fun I => I.card = l), ‖a I‖) ≤ large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 2) ∧
          ∀ μsec, IsSection D.R.k D.R.rS W.z W.z' μsec →
          ∀ γ p, RelPt D W.z W.z' γ p → ∀ θ', normWin D large₂ C1 θ' → ∀ νR, RMeas D W γ θ' νR →
            DminN W.z W.z' γ l • jhUnit D w w' A₀ μsec νR γ =
              ∑ I ∈ univ.filter (fun I => I.card = l), a I • jhUnit D w w' (AI I) μsec νR γ

def PieriNormDegreeFormula (C' Cl Cg cb Cu cT CT C0 Cn C1 : ℝ) : Prop :=
  Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W →
    ∀ μsec, IsSection D.R.k D.R.rS W.z W.z' μsec → ∃ K : ℝ, 0 < K ∧
      ∀ lam', l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ A : LocS W, GoodS D lam' A →
        MMv D w w' A μsec = ENNReal.ofReal (K / A.deg)

def FormalDegreeUnitStepRatio (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W →
    ∀ lam', l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ A : LocS W, GoodS D lam' A →
      ∀ (i : Fin (2 * D.R.rS + D.R.k + 1)) (s : ℝ), (s = 1 ∨ s = -1) →
        ∀ A' : LocS W, GoodS D (lam' + s • epsI {i}) A' →
          (D.R.r : ℝ) ^ (-C) ≤ A'.deg / A.deg ∧ A'.deg / A.deg ≤ (D.R.r : ℝ) ^ C

def stMOM (C' Cl Cg cb Cu cT CT C0 Cn C1 Cq C : ℝ) : Prop :=
  Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W →
    ∀ lam', l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ A : LocS W, GoodS D lam' A →
      ∀ (a : Fin (D.R.rS + 1)) (q : ℕ), (q : ℝ) ≤ Cq * (D.R.rS : ℝ) ^ 3 →
        ∫⁻ x, ENNReal.ofReal (lA D.R.k D.R.rS W.z (Matrix.of x) a ^ (2 * q)) *
            (‖A.Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂W.νS ≤
          ENNReal.ofReal (large₂.sc.b ^ (2 * C * D.R.m * q)) * l2SG W.νS A.Φ

end Loc

def volU (j : ℕ) : ℝ := ∏ i ∈ Finset.range j, (2 * Real.pi) ^ (i + 1) / (i.factorial : ℝ)

section Loc2

open MeasureTheory Finset Formalism.QuantumDeterminants

variable (D : D7) (large₂ : SizeData₂ D)

def stSchur (C' Cl Cg cb Cu cT CT C0 C1 C : ℝ) : Prop :=
  Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W →
    ∀ A : LocS W, GoodS D (lamD D τ) A →
      ∀ μsec, IsSection D.R.k D.R.rS W.z W.z' μsec →
        MMv D w w' A μsec ≤
          ENNReal.ofReal ((Tr D w * Tr D w') ^ (D.R.k - 1) *
            ((Module.finrank ℂ W.Wp : ℝ) * (Module.finrank ℂ W.Wq : ℝ) * volU D.R.r * volU (D.R.k - 1) /
              (A.deg * volU D.R.k ^ 2 * (2 * D.host.v) ^ (2 * D.R.rS * D.R.k))) *
            large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 2))

def stWeyl : Prop :=
  ∀ (τ : D.what₂.Tau) (w : D.what₂.Word) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (z : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (π : MatKR D.R.k D.R.rS → (H →L[ℂ] H)),
    IsColsType D w τ z π →
      (Module.finrank ℂ H : ℝ) = vand (uS D w τ) / ∏ i ∈ Finset.range D.R.k, (i.factorial : ℝ)

end Loc2

section Amp

open MeasureTheory Finset Formalism.QuantumDeterminants

variable (D : D7) (large₂ : SizeData₂ D)

def ForAmpH (C' Cl Cg cb Cu cT CT C0 A C1 : ℝ)
    (Q : (τ : D.what₂.Tau) → (w w' : D.what₂.Word) → (W : LocW D.R.k D.R.rS) → LocS W →
      MatKR D.R.k D.R.rS → Point ℂ (D.R.rS + 1) → Measure (Mt D.R.k D.R.rS) → Prop) : Prop :=
  ForAmp D large₂ C1 fun τ w w' W S γ p νR => Hyp D large₂ w w' C' Cl Cg cb Cu cT CT C0 A → Q τ w w' W S γ p νR

def stCONST (C' Cl Cg cb Cu cT CT C0 C1 C : ℝ) : Prop :=
  Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W →
    ∀ A : LocS W, GoodS D (lamD D τ) A → A.deg = D.dsig τ →
      ∀ μsec, IsSection D.R.k D.R.rS W.z W.z' μsec →
        ENNReal.ofReal (normalizedLocalScale D w) * MMv D w w' A μsec ≤
          ENNReal.ofReal (Module.finrank ℂ W.Wp * (tvPr D τ w' ^ D.R.k)⁻¹ *
            large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 2))

def L2PointwiseLoss (C' Cl Cg cb Cu cT CT C0 A C1 C : ℝ) : Prop :=
  ForAmpH D large₂ C' Cl Cg cb Cu cT CT C0 A C1 fun τ w w' W S γ p νR =>
    normalizedLocalScale D w * Gf D.R.k D.R.rS W.z W.z' γ ^ D.R.k * hsNormSq (S.J νR γ) / Module.finrank ℂ W.Wp ≤
      lossV large₂.sc.b C D.R.m W.z W.z' γ p * (tvPr D τ w' ^ D.R.k)⁻¹

def stL2prod (C' Cl Cg cb Cu cT CT C0 A C C2 Ch : ℝ) : Prop :=
  ∀ w w' zs zs' γs ps, TermPts D w w' zs zs' γs ps → Hyp D large₂ w w' C' Cl Cg cb Cu cT CT C0 A →
    ∀ P : Finset D.what₂.Tau,
    ∏ τ ∈ P, lossV large₂.sc.b C D.R.m (zs τ) (zs' τ) (γs τ) (ps τ) ≤
      GamS D large₂ * (∏ τ, sizeV (scalePowQuadraticExponent D large₂ Ch) (zs τ) (zs' τ) (γs τ)) ^ (C2 * (D.R.m : ℝ) ^ 2)

def stABS (C' Cl Cg cb Cu cT CT C0 A C1 C : ℝ) : Prop :=
  ForAmpH D large₂ C' Cl Cg cb Cu cT CT C0 A C1 fun _ _ _ W S γ p νR =>
    DminN W.z W.z' γ D.R.rS ≠ 0 →
      ‖S.J νR γ‖ ≤ lossP large₂.sc.b C D.R.m W.z W.z' γ p *
        (C / (D.R.k * D.host.v)) ^ (D.R.rS * (D.R.k - 2 - D.R.rS)) *
        (‖DminN W.z W.z' γ D.R.rS‖ ^ (D.R.k - 2 - D.R.rS))⁻¹

def stABSconv (C' Cl Cg cb Cu cT CT C0 A C1 : ℝ) : Prop :=
  ForAmpH D large₂ C' Cl Cg cb Cu cT CT C0 A C1 fun _ _ _ W S γ _ νR =>
    DminN W.z W.z' γ D.R.rS ≠ 0 →
      Integrable (fun x => (innerSL ℂ (S.Φ' (Matrix.of x))).smulRight (S.Φ (γ * Matrix.of x))) νR

def stABSprod (C' Cl Cg cb Cu cT CT C0 A C C2 Ch : ℝ) : Prop :=
  ∀ w w' zs zs' γs ps, TermPts D w w' zs zs' γs ps → Hyp D large₂ w w' C' Cl Cg cb Cu cT CT C0 A →
    ∀ P : Finset D.what₂.Tau,
    ∏ τ ∈ P, lossP large₂.sc.b C D.R.m (zs τ) (zs' τ) (γs τ) (ps τ) ≤
      Real.exp (C2 * (D.R.m : ℝ) ^ 6 * D.R.f * Real.log large₂.sc.b) *
        (∏ τ, sizeV (scalePowQuadraticExponent D large₂ Ch) (zs τ) (zs' τ) (γs τ)) ^ (C2 * (D.R.m : ℝ) ^ 4)

def stMIN (C' Cl Cg cb Cu cT CT C0 A C1 C δ : ℝ) : Prop :=
  ForAmpH D large₂ C' Cl Cg cb Cu cT CT C0 A C1 fun τ w w' W S γ p νR =>
    normalizedLocalScale D w * Gf D.R.k D.R.rS W.z W.z' γ ^ D.R.k * hsNormSq (S.J νR γ) / Module.finrank ℂ W.Wp ≤
                         lossV large₂.sc.b C D.R.m W.z W.z' γ p * lossP large₂.sc.b C D.R.m W.z W.z' γ p ^ 2 *
                           (tvPr D τ w' ^ D.R.k)⁻¹ * ampMinF D C δ τ w w' W.z W.z' γ ^ D.R.k ∧
      normalizedLocalScale D w * Gf D.R.k D.R.rS W.z W.z' γ ^ D.R.k * hsNormSq (S.J νR γ) *
                           chRatio (Tr D w) (Tr D w') W.z W.z' γ ^ (2 * D.R.k) * (Tr D w ^ D.R.k)⁻¹ /
                           Module.finrank ℂ W.Wp ≤
        lossV large₂.sc.b C D.R.m W.z W.z' γ p * lossP large₂.sc.b C D.R.m W.z W.z' γ p ^ 2 *
          (C / D.R.k) ^ D.R.k

def stDEC (C' Cl Cg cb Cu cT CT C0 A C1 Cpr C Ch δ : ℝ) : Prop :=
  ForAmpH D large₂ C' Cl Cg cb Cu cT CT C0 A C1 fun τ w w' W S γ p νR =>
    ∀ q : ℕ, (q : ℝ) ≤ Cpr * D.R.k * (D.R.m : ℝ) ^ 2 →
    (normalizedLocalScale D w * Gf D.R.k D.R.rS W.z W.z' γ ^ D.R.k * hsNormSq (S.J νR γ) / Module.finrank ℂ W.Wp ≤
      lossV large₂.sc.b C D.R.m W.z W.z' γ p * (tvPr D τ w' ^ D.R.k)⁻¹ *
        sizeV (scalePowQuadraticExponent D large₂ Ch) W.z W.z' γ ^ (-(2 * (q : ℝ) / ((D.R.rS : ℝ) + 1)))) ∧
    (DminN W.z W.z' γ D.R.rS ≠ 0 →
      ‖S.J νR γ‖ ≤ lossP large₂.sc.b C D.R.m W.z W.z' γ p *
        (C / (D.R.k * D.host.v)) ^ (D.R.rS * (D.R.k - 2 - D.R.rS)) *
        (‖DminN W.z W.z' γ D.R.rS‖ ^ (D.R.k - 2 - D.R.rS))⁻¹ *
        sizeV (scalePowQuadraticExponent D large₂ Ch) W.z W.z' γ ^ (-((q : ℝ) / ((D.R.rS : ℝ) + 1)))) ∧
    (normalizedLocalScale D w * Gf D.R.k D.R.rS W.z W.z' γ ^ D.R.k * hsNormSq (S.J νR γ) / Module.finrank ℂ W.Wp ≤
                         lossV large₂.sc.b C D.R.m W.z W.z' γ p * lossP large₂.sc.b C D.R.m W.z W.z' γ p ^ 2 *
                           (tvPr D τ w' ^ D.R.k)⁻¹ * ampMinF D C δ τ w w' W.z W.z' γ ^ D.R.k *
                           sizeV (scalePowQuadraticExponent D large₂ Ch) W.z W.z' γ ^ (-(2 * (q : ℝ) / ((D.R.rS : ℝ) + 1))) ∧
      normalizedLocalScale D w * Gf D.R.k D.R.rS W.z W.z' γ ^ D.R.k * hsNormSq (S.J νR γ) *
                           chRatio (Tr D w) (Tr D w') W.z W.z' γ ^ (2 * D.R.k) * (Tr D w ^ D.R.k)⁻¹ /
                           Module.finrank ℂ W.Wp ≤
        lossV large₂.sc.b C D.R.m W.z W.z' γ p * lossP large₂.sc.b C D.R.m W.z W.z' γ p ^ 2 *
          (C / D.R.k) ^ D.R.k * sizeV (scalePowQuadraticExponent D large₂ Ch) W.z W.z' γ ^ (-(2 * (q : ℝ) / ((D.R.rS : ℝ) + 1))))

end Amp

section Counts

variable (D : D7)

def stX (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C c : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
    Mass2At D large₂ C ∧
    ∀ s : ℕ, 2 ≤ s → s ≤ D.R.k - 2 → ∀ HH : ℝ,
      XiS D u HH C s ≤ Hb large₂.sc.b C D.R.m D.R.f ^ C * C ^ (s * D.R.k * D.R.f) *
        (c / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f)

def stLem3 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module D.host.E V] [FiniteDimensional D.host.E V]
    [Module (𝓞 D.host.E) V] [IsScalarTower (𝓞 D.host.E) D.host.E V]
    (h : V →ₗ⋆[D.host.E] V →ₗ[D.host.E] D.host.E), h.IsSymm → IsPosDef h →
    ∀ M : Submodule (𝓞 D.host.E) V, Submodule.IsLattice D.host.E M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    ∀ de : ℕ, latDetH h M = de → ∀ e : ℕ, DiscGen h M e →
      Formalism.HermitianLatticesTheory.mass h M * levelIdx h M de =
        massU D.host.E (finrank D.host.E V) * (de : ℝ) ^ (finrank D.host.E V) *
          ∏ᶠ p : PrimesOver D.host.F de,
            thP (finrank D.host.E V) (eP h M p.1) (eta₃ D.host.F D.host.E p.1) (Ideal.absNorm p.1) ∧
      (∀ p : Ideal (𝓞 D.host.F), p.IsMaximal →
        thP (finrank D.host.E V) (eP h M p) (eta₃ D.host.F D.host.E p) (Ideal.absNorm p) ≤ (2 : ℝ) ^ e) ∧
      Formalism.HermitianLatticesTheory.mass h M ≤ massU D.host.E (finrank D.host.E V) * (de : ℝ) ^ (finrank D.host.E V) *
        (2 : ℝ) ^ (e * omegaF D.host.F de)

def stLem3L0 (u : D.what₂.Word) : Prop :=
  (Tu D u).Prime → 3 ≤ Tu D u → SplitsCompletely (E := D.host.E) (Tu D u) →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ s : Finset (LatV D), IsRowReps D F0 s →
    massRows D F0 s = massS D D.R.k * ((Tu D u : ℝ) ^ D.R.k - 1) ^ D.R.f ∧
    ∀ Λ : LatV D, IsRowLat D F0 Λ →
      Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT (L0X D Λ (lf D F0)) = massRows D F0 s / ((Tu D u : ℝ) - 1) ^ D.R.f ∧
      massS D D.R.k * NT D u ^ (D.R.k - 1) ≤ Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT (L0X D Λ (lf D F0))

def congruence_at_split_frobenius_holds (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ →
    ∀ reps : Finset (Submodule (𝓞 D.host.E) (D.sp.X 0).V),
      Formalism.ThetaLiftIndependence.IsClassReps (D.sp.X 0).hT (L0X D Λ (lf D F0)) reps →
    ∀ s : ℕ, 2 ≤ s → s ≤ D.R.k → ∀ de : ℕ, 1 ≤ de → ∀ HH : ℝ, Hb large₂.sc.b C D.R.m D.R.f ≤ HH →
      (∑ L' ∈ reps, ENNReal.ofReal ((Nat.card (Formalism.ThetaLiftIndependence.autL (D.sp.X 0).hT L') : ℝ))⁻¹ *
          (cntPrim (D.sp.X 0).hT L' (D.R.k - s) de : ℝ≥0∞)) ≤
        ENNReal.ofReal (Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT (L0X D Λ (lf D F0)) *
          (((de : ℝ) / NT D u) ^ D.R.k * ((de : ℝ) * NT D u) ^ (C * s + C * Real.log D.R.f) * XiS D u HH C s))

def SubmoduleIndexCount (large₂ : SizeData₂ D) (CH C : ℝ) : Prop :=
  (∀ (P : Type) [AddCommGroup P] [Module (𝓞 D.host.E) P] [Module.Projective (𝓞 D.host.E) P]
      [Module.Finite (𝓞 D.host.E) P], finrank (𝓞 D.host.E) P ≤ D.R.k → ∀ j : ℕ, 1 ≤ j →
      ((ENat.card {Q : Submodule (𝓞 D.host.E) P // Nat.card (P ⧸ Q) = j} : ℕ∞) : ℝ≥0∞) ≤
        ENNReal.ofReal ((j : ℝ) ^ ((D.R.k : ℝ) + lg2f D.R.f))) ∧
  (∀ (A : Type) [AddCommGroup A] [Module (𝓞 D.host.E) A] [Finite A] (e : ℕ),
      (∃ s : Finset A, s.card ≤ e ∧ Submodule.span (𝓞 D.host.E) (s : Set A) = ⊤) →
      (Nat.card A : ℝ) ≤ Hb large₂.sc.b CH D.R.m D.R.f →
      (Nat.card (Submodule (𝓞 D.host.E) A) : ℝ) ≤ Hb large₂.sc.b CH D.R.m D.R.f ^ (C * e) ∧
      (Nat.card (A ≃ₗ[𝓞 D.host.E] A) : ℝ) ≤ Hb large₂.sc.b CH D.R.m D.R.f ^ (C * e))

def MeanFlagPairCount (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A Ad C : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ what₂ : Finset (LatV D), IsRowReps D F0 what₂ →
  ∀ (Z' Z'' : GramM D), RelZ D Z' → RelZ D Z'' → ∀ s : ℕ, 2 ≤ s → s ≤ D.R.k →
  ∀ De : ℝ, 1 ≤ De → De ≤ (HHZ D large₂.sc.b C Z' * HHZ D large₂.sc.b C Z'') ^ Ad →
    MeanLe D F0 what₂
      (fun Λ => cntPairs D Λ ((Tu D u' : ℕ) : D.host.E) (lf D F0) Z' Z'' s De)
      ((De / NT D u) ^ D.R.k * XiS D u (HHZ D large₂.sc.b C Z' * HHZ D large₂.sc.b C Z'') C s *
        (HHZ D large₂.sc.b C Z' * HHZ D large₂.sc.b C Z'') ^
          (C * ((s : ℝ) + D.R.m) * D.R.m + C * cF D.R.f) *
        (C * s * D.R.f) ^ (6 * s * D.R.f))

def PartnerCountBound (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ →
  ∀ F' : FlagU D u', IsTermF D Λ (lf D F0) F' → IsGeneric Λ (gS D) (lf D F0) F' →
  RelZ D (ZhatL (lf D F0) F') → ∀ Z : GramM D, RelZ D Z →
    (cntPartners D Λ (lf D F0) F' Z : ℝ≥0∞) ≤
      ENNReal.ofReal (C ^ D.R.f *
        (HHZ D large₂.sc.b C (ZhatL (lf D F0) F') * HHZ D large₂.sc.b C Z) ^ (C * (D.R.rS : ℝ) ^ 2))

end Counts

section HHb

variable (D : D7)

def absMinor (Z : GramM D) {j : ℕ} (I J : Fin j ↪o Fin (D.R.rS + 1)) (τ : D.what₂.Tau) : ℝ :=
  ‖embS D τ (Z.submatrix I J).det‖ * ∏ a, (rhoF D (I a) * rhoF D (J a))

def stHH (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ →
  ∀ F' : FlagU D u', IsTermF D Λ (lf D F0) F' → RelZ D (ZhatL (lf D F0) F') →
    NT D u ≤ HHZ D large₂.sc.b C (ZhatL (lf D F0) F') ∧
    ∏ τ, max 1 (Gz D (Tu D u) (Tu D u') (ZhatL (lf D F0) F') τ) ≤ HHZ D large₂.sc.b C (ZhatL (lf D F0) F') ∧
    ∏ τ, max 1 (Gz D (Tu D u) (Tu D u') (ZhatL (lf D F0) F') τ)⁻¹ ≤ HHZ D large₂.sc.b C (ZhatL (lf D F0) F') ∧
    ∃ Z : GramM D, ZEquiv (ZhatL (lf D F0) F') Z ∧
      ∀ (j : ℕ) (I J : Fin j ↪o Fin (D.R.rS + 1)), (Z.submatrix I J).det ≠ 0 →
        ∏ τ, max 1 (absMinor D Z I J τ) ≤ HHZ D large₂.sc.b C (ZhatL (lf D F0) F') ∧
        ∏ τ, max 1 (absMinor D Z I J τ)⁻¹ ≤ HHZ D large₂.sc.b C (ZhatL (lf D F0) F')

end HHb

def stVol (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (u u' : D.what₂.Word) (C1 : ℝ)
    (Y : LoopTie D large₂ X u u' C1) (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t →
    Y.volR t ≤ HHZ D large₂.sc.b C (ZhatL (X.fl t) (X.fl' t)) ^ (C * (D.R.rS : ℝ) ^ 2)

def VolumeRatioBound (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A c : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → LoopPairSumBound D u u' c

section S0lines

variable (D : D7)

def cExp : Prop := ∀ u u' : D.what₂.Word, KExpansion D.s u u' ∧ KAbsConv D.s u u'

def cIdOne : Prop := ∀ u : D.what₂.Word, IdCellDiag D.s u

def cIdFlag (X : TermTie D) : Prop :=
  ∀ (u : D.what₂.Word) (t : D.s.Term u u),
    ((∀ j, Xflag (X.fl' t) j = Xflag (X.fl t) j) ∧ Xplus (X.fl' t) = Xplus (X.fl t)) → D.s.relevant t → D.s.isId t

def cIrr : Prop :=
  ∀ (u u' : D.what₂.Word) (t : D.s.Term u u'), ¬ D.s.relevant t → D.s.aTerm u u' t = 0

def cGpos (X : TermTie D) : Prop :=
  ∀ (u u' : D.what₂.Word) (t : D.s.Term u u'), D.s.Gterm t ≠ 0 →
    Dl (X.fl t).fl (X.fl' t).fl (D.R.rS + 1) ≠ 0 ∧
    (Dl (X.fl t).fl (X.fl' t).fl D.R.rS ≠ 0 → ∀ τ, 0 < (embS D τ (Gval (X.fl t) (X.fl' t))).re)

def cCells (X : TermTie D) : Prop :=
  ∀ (u u' : D.what₂.Word) (t : D.s.Term u u'), D.s.relevant t →
    ∀ (j : ℕ) (hj : j ≤ D.R.rS + 1), Dl (X.fl t).fl (X.fl' t).fl j ≠ 0 →
      ∃ p : Point D.host.E j,
        IsInCell ((ZhatOM (ZhatL (X.fl t) (X.fl' t))).submatrix (Fin.castLE hj) (Fin.castLE hj)) p

def f3 : ℝ := ∏ᶠ p ∈ typedPl D, (1 + 3 / (Ideal.absNorm p.asIdeal : ℝ))

def c2aG : Prop :=
  ∀ (u u' : D.what₂.Word) (Φ : Set (D.s.Term u u')), IsSat D Φ → (∀ t ∈ Φ, D.s.Gterm t ≠ 0) →
    Summable (fun p : pairsIn D.s Φ => ‖D.s.pval p.1‖) →
    hsNormSq (KOf D.s u u' Φ) ≤ f3 D * gaG D * (∑' p : pairsIn D.s Φ, D.s.pval p.1).re

def c2aAny : Prop :=
  ∀ (u u' : D.what₂.Word) (Φ : Set (D.s.Term u u')), IsSat D Φ →
  Summable (fun p : pairsIn D.s Φ => ‖D.s.pval p.1‖) →
    hsNormSq (KOf D.s u u' Φ) ≤
      (∏ i : Fin 2, (1 + 3 / (D.host.g i : ℝ))) ^ D.R.f * gaG D * (∑' p : pairsIn D.s Φ, D.s.pval p.1).re

def TermsPP (u u' : D.what₂.Word) : Set (D.s.Term u u') := {t | D.s.Gterm t = 0 ∧ ¬ D.s.isId t}

def Kpp (u u' : D.what₂.Word) : D.s.Cu u' →L[ℂ] D.s.Cu u := KOf D.s u u' {t | D.s.Gterm t = 0 ∧ ¬ D.s.isId t}

def cK2diag : Prop :=
  ∀ u : D.what₂.Word,
    Summable (fun t : TermsPP D u u => D.s.aTerm u u t.1) ∧
    hsNormSq (Kpp D u u) ≤ (D.duS u : ℝ) * Real.exp (-((D.R.k : ℝ) * D.R.f * Real.log D.R.k))

def cK2off : Prop :=
  ∀ u u' : D.what₂.Word, u ≠ u' →
    ∀ t : D.s.Term u u', D.s.Gterm t = 0 → D.s.aTerm u u' t = 0

def Kng (u u' : D.what₂.Word) : D.s.Cu u' →L[ℂ] D.s.Cu u := KOf D.s u u' (famNG D.s)

def scalG (u u' : D.what₂.Word) : Set (D.s.Pair u u') :=
  {p | p ∈ pairsIn D.s (famG D.s) ∧ scalarP D.s p}

def NonGenericKernelBound (large₂ : SizeData₂ D) (c C : ℝ) : Prop :=
  ∀ u u' : D.what₂.Word,
    hsNormSq (Kng D u u') ≤
      (Real.exp (-(c * (D.R.k : ℝ) * (D.R.f : ℝ) * Real.log (D.R.k : ℝ))) +
        (2 : ℝ) ^ (-((D.R.k : ℝ) - 2 * (D.R.rS : ℝ) - 5)) *
          Real.exp (C * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L)) *
      ((D.duS u : ℝ) * (D.duS u' : ℝ)) / D.what₂.Dstar

def GenericScalarPairSum (large₂ : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ u : D.what₂.Word,
    Summable (fun p : scalG D u u => D.s.pval p.1) ∧
    ‖(gaG D : ℂ) * ∑' p : scalG D u u, D.s.pval p.1‖ ≤
      Real.exp (C * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L) * (D.duS u : ℝ) ^ 2 / D.what₂.Dstar

end S0lines

def cTvA (D : D7) : Prop :=
  ∀ u, Real.exp (-((D.R.f : ℝ) * (2 : ℝ) ^ ((3 : ℝ) - D.R.k))) * ∏ τ, (Tcrit D u τ / Tr D u) ^ D.R.k ≤
      D.what₂.Dstar / (D.duS u : ℝ) ∧
    D.what₂.Dstar / (D.duS u : ℝ) ≤
      Real.exp ((D.R.f : ℝ) * (2 : ℝ) ^ ((3 : ℝ) - D.R.k)) * ∏ τ, (Tcrit D u τ / Tr D u) ^ D.R.k

def cTvB (D : D7) (C1 : ℝ) : Prop := ∀ u u' τ, Tcrit D u τ / Tcrit D u' τ ≤ C1

def cTvC (D : D7) (C2 : ℝ) : Prop := ∀ u u', Tr D u / Tr D u' ≤ C2

def cTvD (D : D7) (C3 : ℝ) : Prop :=
  ∀ u τ, gg D ^ D.R.m * D.host.ka ^ (-((D.R.m : ℝ) - 1)) * (∏ j ∈ Finset.Icc 1 D.R.m, bOne D τ j) *
      (D.R.k : ℝ) ^ (-C3) / aEff D u τ ≤ Tcrit D u τ

def cTvE (D : D7) (C4 : ℝ) : Prop :=
  ∀ u u' τ (l : ℕ), 1 ≤ l → l ≤ D.R.k - 2 → uOne D u τ (l + 1) ≠ uOne D u' τ (l + 1) →
    ∀ d : ℝ, 5 / 2 ≤ d → d ≤ (D.s.Del : ℝ) / 2 →
      gg D ^ D.R.m * beUU D D.host.ka u u' τ (d - vOne D τ l) ≤
        tV D u u' τ * (D.R.k : ℝ) ^ C4 * Real.sqrt (d / D.s.Del)

def cTvF (D : D7) (large₂ : SizeData₂ D) (c5 CA : ℝ) : Prop :=
  ∀ u u' (l : ℕ), 1 ≤ l → l ≤ D.R.k - 2 → (∀ τ, uOne D u τ (l + 1) ≠ uOne D u' τ (l + 1)) →
    ∀ (x : D.what₂.Tau → LocalDataRealPlace D) (L : LatticeDataWithDual D), IsLocC D u u' l x → IsLatGLOB D L →
      (D.R.k : ℝ) ^ c5 ≤ ThA D CA u u' x L ∧
      ((D.R.rS : ℝ) + 1) * (CA / ThA D CA u u' x L) ^ (D.R.f : ℝ) ≤ large₂.sc.b ^ (-7 : ℝ)

def cTvG (D : D7) (large₂ : SizeData₂ D) (ep0 CV : ℝ) : Prop :=
  ∀ τ, (1 - ep0) * vand (lamSH D.R (D.hc τ)) ≤ VV D τ ∧
    VV D τ ≤ Real.exp (CV * D.R.k * D.R.m * large₂.sc.L) * vand (lamSH D.R (D.hc τ))

def stNGLoc (k r : ℕ) (C : ℝ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Loc.Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V),
      Module.finrank E V = k + 2 * r + 1 →
      ∀ P : LocNG.FPair H r, P.RelG (LocNG.theta M) → LocNG.NGAt k P C

def stNG (D : D7) (C : ℝ) : Prop := 4 * D.R.rS + 7 ≤ D.R.k → stNGLoc D.R.k D.R.rS C

section K2

variable (D : D7) (large₂ : SizeData₂ D)

def KTwoParameterConditions (Cl Cg CT : ℝ) : Prop :=
  Cl * (D.R.m : ℝ) ^ 6 * large₂.sc.L ≤ (D.R.k : ℝ) * Real.log D.R.k ∧
  (∀ i : Fin 2, ((D.R.k : ℝ) * large₂.sc.b) ^ 8 ≤ (D.host.g i : ℝ) ∧ (D.host.g i : ℝ) ≤ large₂.sc.b ^ Cg) ∧
  (∀ (τ : D.what₂.Tau) (a c : Fin D.R.r), a ≠ c →
    Cl * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 3 < |lamS D.R (D.hc τ) a - lamS D.R (D.hc τ) c|) ∧
  Cl * Real.log D.host.rdE ≤ large₂.sc.L ∧
  Real.log (D.R.f : ℝ) ≤ (D.R.rS : ℝ) ^ 2 ∧
  (∀ u : D.what₂.Word, ((D.mem u).A.T : ℝ) ≤ large₂.sc.b ^ (CT * (D.R.m : ℝ)) ∧
    Nat.Coprime (D.mem u).A.T (D.host.g 0 * D.host.g 1)) ∧
  Formalism.HermitianLatticesTheory.IsCMUnram D.host.E

def KTwoHypotheses (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 ∧ KTwoParameterConditions D large₂ Cl Cg CT

def stK2diag (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  KTwoHypotheses D large₂ C' Cl Cg cb Cu cT CT C0 → cK2diag D

def stK2off (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  KTwoHypotheses D large₂ C' Cl Cg cb Cu cT CT C0 → cK2off D

def st2aAny (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → c2aAny D

def stExp (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → cExp D

def stIdFlag (X : TermTie D) (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → cIdFlag D X

def stIdCell (X : TermTie D) (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → cIdFlag D X ∧ cIdOne D

def stExpId (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → cExp D ∧ cIdOne D

def stIrr (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → cIrr D

def stGpos (X : TermTie D) (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → cGpos D X

def stCells (X : TermTie D) (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → cCells D X

def stMass2K (C' Cl Cg cb Cu cT CT C0 C : ℝ) : Prop :=
  KTwoHypotheses D large₂ C' Cl Cg cb Cu cT CT C0 → Mass2At D large₂ C

def stFormK (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  KTwoHypotheses D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ u : D.what₂.Word, FormAt D u

end K2

def stSchurLem : Prop :=
  ∀ (k : ℕ) (u u' : Fin k → ℝ) (H H' : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (ρ : Matrix (Fin k) (Fin k) ℂ → (H' →L[ℂ] H')),
    IsHCTypeU k u π → IsHCTypeU k u' ρ → u ≠ u' →
    ∀ P : H' →L[ℂ] H, (∀ h ∈ UJset (allPos k), P.comp (ρ h) = (π h).comp P) → P = 0

section Size

open MeasureTheory Formalism.QuantumDeterminants

variable (D : D7) (large₂ : SizeData₂ D)

def hNC (τ : D.what₂.Tau) : ℝ :=
  sInf {x | ∃ a b, epsSH D.R a ≠ epsSH D.R b ∧ x = |lamD D τ a - lamD D τ b|}

def CloudNodeShape (τ : D.what₂.Tau) (Cq bv : ℝ) : Prop :=
  Cq * (D.R.r : ℝ) ^ 7 ≤ bv ∧
  (∀ l, 1 ≤ l → l ≤ D.R.k - 1 → 0 ≤ vOne D τ l ∧ vOne D τ l ≤ bv / 8) ∧
  ∀ j, 1 ≤ j → j ≤ D.R.m → bv ≤ bOne D τ j ∧ bOne D τ j ≤ 2 * bv

def q0 (τ : D.what₂.Tau) (cq Cq : ℝ) : ℝ :=
  min (cq * hNC D τ * (D.R.m : ℝ) ^ (-(1 / 2 : ℝ))) (4 * (D.s.Del : ℝ)) / Cq

def stSIZE (C' Cl Cg cb Cu cT CT C0 Cθ C1 cq Cq CH : ℝ) : Prop :=
  Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ (τ : D.what₂.Tau) (u : D.what₂.Word) (bv : ℝ), CloudNodeShape D τ Cq bv →
  ∀ θ, normWin D large₂ Cθ θ → ∀ W, GoodW D τ u u θ W → ∀ A : LocS W, GoodS D (lamD D τ) A →
    IsLowUnitH D.R.k D.R.rS (epsSH D.R) (lamD D τ) A.σ A.v0 →
    ∀ q : ℕ, (q : ℝ) ≤ C1 * D.R.k * D.R.rS → (D.R.m : ℝ) * q ≤ q0 D τ cq Cq →
      (D.R.m : ℝ) * q ≤ bv / (Cq * (D.R.r : ℝ) ^ 4) →
    ∀ la : ℝ, 0 < la →
      ∫⁻ x, Set.indicator {x | ∃ a : Fin (D.R.rS + 1), la * large₂.sc.b ^ (CH * (D.R.m : ℝ)) ≤
              max (lA D.R.k D.R.rS W.z (Matrix.of x) a) (lA D.R.k D.R.rS W.z (Matrix.of x) a)⁻¹}
            (fun x => (‖A.Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2) x ∂W.νS ≤
        ENNReal.ofReal (2 * (D.R.m : ℝ) * la ^ (-(2 * (q : ℝ)))) * l2SG W.νS A.Φ

end Size

def minkM (N : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (N + 2)).filter Nat.Prime, p ^ (∑ j ∈ Finset.range (N + 1), N / (p ^ j * (p - 1)))

def stMinkM : Prop :=
  ∀ (N : ℕ) (G : Subgroup (GL (Fin N) ℤ)), Finite G → Nat.card G ∣ minkM N

end Formalism.MainNotions.S.UnitaryVolumeMass

end
