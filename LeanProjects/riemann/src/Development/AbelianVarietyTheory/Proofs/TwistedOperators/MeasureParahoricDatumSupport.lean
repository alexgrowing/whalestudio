import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurableSetPreSingleton

noncomputable section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

namespace GlobalTheory.SupportVolume

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem residue_eq_zero_iff_lt (x : 𝒪[k]) :
    IsLocalRing.residue 𝒪[k] x = 0 ↔ valuation k (x : k) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
  exact ⟨fun h => lt_of_le_of_ne x.2 h, fun h => h.ne⟩

theorem isUnit_iff_val (x : 𝒪[k]) : IsUnit x ↔ valuation k (x : k) = 1 :=
  (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one

theorem isUnit_red_iff {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n 𝒪[k]) :
    IsUnit (GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex.red A) ↔ valuation k ((A.det : 𝒪[k]) : k) = 1 := by
  rw [← isUnit_iff_val, ← Matrix.isUnit_iff_isUnit_det]
  exact ⟨GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex.isUnit_of_red A, fun h => h.map (IsLocalRing.residue 𝒪[k]).mapMatrix⟩

theorem det_coe {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n 𝒪[k]) :
    ((A.det : 𝒪[k]) : k) = (A.map (algebraMap 𝒪[k] k)).det :=
  by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl

def suppBar (A D E : Type) [Fintype A] [DecidableEq A] :
    Set (Matrix (A ⊕ E) (A ⊕ D) 𝓀[k]) :=
  {B | IsUnit B.toBlocks₁₁ ∧ B.toBlocks₂₁ = 0}

theorem inSupp_eq_pre {A D E : Type} [Fintype A] [DecidableEq A] :
    {x : Matrix (A ⊕ E) (A ⊕ D) k | InSupp x} = GlobalTheory.IndexVolume.pre (suppBar (k := k) A D E) := by
  ext x
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨Matrix.of fun i j => ⟨x i j, h1 i j⟩, rfl, ?_, ?_⟩
    · change IsUnit (GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex.red (Matrix.of fun i j => (⟨x i j, h1 i j⟩ : 𝒪[k])).toBlocks₁₁)
      rw [isUnit_red_iff, det_coe]
      exact h2
    · ext i j
      exact (residue_eq_zero_iff_lt _).2 (h3 i j)
  · rintro ⟨A, rfl, hu, hz⟩
    refine ⟨fun i j => (A i j).2, ?_, fun i j => ?_⟩
    · have := (isUnit_red_iff A.toBlocks₁₁).1 hu
      rw [det_coe] at this
      exact this
    · exact (residue_eq_zero_iff_lt (A (.inr i) (.inl j))).1 (congrFun (congrFun hz i) j)

def unitBar (A : Type) [Fintype A] [DecidableEq A] : Set (Matrix A A 𝓀[k]) := {U | IsUnit U}

theorem KO_eq_pre (A : Type) [Fintype A] [DecidableEq A] :
    Units.val '' (KO k A : Set (GL A k)) = GlobalTheory.IndexVolume.pre (unitBar (k := k) A) := by
  ext x
  constructor
  · rintro ⟨g, ⟨h, rfl⟩, rfl⟩
    exact ⟨h.val, rfl, h.isUnit.map (IsLocalRing.residue 𝒪[k]).mapMatrix⟩
  · rintro ⟨M, rfl, hM⟩
    obtain ⟨u, hu⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex.isUnit_of_red M hM
    refine ⟨Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u, ⟨u, rfl⟩, ?_⟩
    rw [← hu]
    rfl

theorem card_matrix (m n : Type) [Fintype m] [Fintype n] :
    Nat.card (Matrix m n 𝓀[k]) = Nat.card 𝓀[k] ^ (Fintype.card m * Fintype.card n) := by
  change Nat.card (m → n → 𝓀[k]) = _
  rw [Nat.card_fun, Nat.card_fun, ← pow_mul, Nat.card_eq_fintype_card (α := m), Nat.card_eq_fintype_card (α := n), mul_comm]

def suppEquiv (A D E : Type) [Fintype A] [DecidableEq A] :
    suppBar (k := k) A D E ≃ unitBar (k := k) A × Matrix A D 𝓀[k] × Matrix E D 𝓀[k] where
  toFun B := (⟨B.1.toBlocks₁₁, B.2.1⟩, B.1.toBlocks₁₂, B.1.toBlocks₂₂)
  invFun U := ⟨fromBlocks U.1.1 U.2.1 0 U.2.2, ⟨by rw [toBlocks_fromBlocks₁₁]; exact U.1.2, toBlocks_fromBlocks₂₁ _ _ _ _⟩⟩
  left_inv B := by
    obtain ⟨B, h1, h2⟩ := B
    apply Subtype.ext
    simp only
    rw [← h2, fromBlocks_toBlocks]
  right_inv U := by
    obtain ⟨⟨U, hU⟩, X, Y⟩ := U
    simp

theorem card_suppBar (A D E : Type) [Fintype A] [DecidableEq A] [Fintype D] [Fintype E] :
    Nat.card (suppBar (k := k) A D E) = Nat.card (unitBar (k := k) A) *
      (Nat.card 𝓀[k] ^ (Fintype.card A * Fintype.card D) * Nat.card 𝓀[k] ^ (Fintype.card E * Fintype.card D)) := by
  rw [Nat.card_congr (suppEquiv A D E), Nat.card_prod, Nat.card_prod, card_matrix, card_matrix]

theorem measure_support : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν →
    ∀ (r : ℕ) (D E : Type) [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E],
    MeasurableSet {x : Matrix (Fin r ⊕ E) (Fin r ⊕ D) k | InSupp x} ∧
    (volM ν (Fin r ⊕ E) (Fin r ⊕ D)).real {x | InSupp x} = volAdd ν r * ((resCard k : ℝ) ^ (r * Fintype.card E))⁻¹ := by
  intro k _ _ _ _ _ _ ν hν r D E _ _ _ _
  haveI := hν.1
  rw [inSupp_eq_pre]
  refine ⟨GlobalTheory.IndexVolume.measurableSet_pre _, ?_⟩
  have h1 : (volM ν (Fin r ⊕ E) (Fin r ⊕ D)).real (GlobalTheory.IndexVolume.pre (suppBar (k := k) (Fin r) D E)) =
      _ := GlobalTheory.IndexVolume.measureReal_pre ν hν.2 _
  have h2 : (volM ν (Fin r) (Fin r)).real (GlobalTheory.IndexVolume.pre (unitBar (k := k) (Fin r))) =
      _ := GlobalTheory.IndexVolume.measureReal_pre ν hν.2 _
  unfold volAdd
  rw [KO_eq_pre, h1, h2, card_suppBar]
  have hq : (0 : ℝ) < Nat.card 𝓀[k] := by exact_mod_cast Nat.card_pos
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex.resCard, resCard, Fintype.card_sum, Fintype.card_fin]
  push_cast
  set q : ℝ := (Nat.card 𝓀[k] : ℝ)
  set d := Fintype.card D
  set e := Fintype.card E
  have hexp : q ^ ((r + e) * (r + d)) = q ^ (r * r) * q ^ (r * e) * (q ^ (r * d) * q ^ (e * d)) := by
    rw [← pow_add, ← pow_add, ← pow_add]; ring_nf
  rw [hexp]
  have : q ≠ 0 := hq.ne'
  field_simp

end GlobalTheory.SupportVolume
