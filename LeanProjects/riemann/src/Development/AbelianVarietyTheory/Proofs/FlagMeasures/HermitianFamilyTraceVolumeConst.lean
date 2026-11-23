import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualHermitianLatticeTraceOrthogonalVolumeRatStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameLatticeTraceInitialSpanVolumeEqStatement

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FamilyVol

theorem relIndex_symm_of_sub {G : Type*} [AddGroup G] {A A' B B' : AddSubgroup G} {β : ℕ} (hβ : β ≠ 0)
    (hA : B ≤ A) (hA' : B' ≤ A') (h : B.relIndex A = β) (h' : B'.relIndex A' = β)
    (hB : B.relIndex B' = B'.relIndex B) (hB0 : B.relIndex B' ≠ 0) :
    A.relIndex A' = A'.relIndex A := by
  have e1 : (B ⊓ B').relIndex A = B'.relIndex B * β := by
    rw [← h, ← AddSubgroup.relIndex_mul_relIndex (B ⊓ B') B A inf_le_left hA,
      AddSubgroup.inf_relIndex_left]
  have e2 : (B ⊓ B').relIndex A' = B.relIndex B' * β := by
    rw [← h', ← AddSubgroup.relIndex_mul_relIndex (B ⊓ B') B' A' inf_le_right hA',
      AddSubgroup.inf_relIndex_right]
  have hle : B ⊓ B' ≤ A ⊓ A' := inf_le_inf hA hA'
  have e3 := AddSubgroup.relIndex_mul_relIndex (B ⊓ B') (A ⊓ A') A hle inf_le_left
  have e4 := AddSubgroup.relIndex_mul_relIndex (B ⊓ B') (A ⊓ A') A' hle inf_le_right
  rw [AddSubgroup.inf_relIndex_left] at e3
  rw [AddSubgroup.inf_relIndex_right] at e4
  have hne : (B ⊓ B').relIndex (A ⊓ A') ≠ 0 := by
    intro h0
    rw [h0, zero_mul, e2] at e4
    exact mul_ne_zero hB0 hβ e4.symm
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne)
  rw [e3, e4, e1, e2, hB]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem resQ_ne_zero (ϖ : 𝒪[F]) (h : Irreducible ϖ) : resQ ϖ ≠ 0 := by
  have e : Ideal.span {ϖ} = IsLocalRing.maximalIdeal 𝒪[F] := h.maximalIdeal_eq.symm
  unfold resQ
  rw [e]
  have : Finite (𝒪[F] ⧸ IsLocalRing.maximalIdeal 𝒪[F]) := inferInstanceAs (Finite 𝓀[F])
  exact Nat.card_pos.ne'

variable [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E} {r k : ℕ}

theorem exists_basis (S : Frames L r k) (J : ℕ) :
    ∃ (m : ℕ) (y : Fin m → S.V), LinearIndependent E y ∧
      Submodule.span E (Set.range y) = S.spanTo S.f J ⊔ S.spanTo S.f' J := by
  have hli := (GlobalTheory.FrameBasic.main L r k S).1
  let I := {i : Fin (r + 1) // (i : ℕ) < J}
  let φ : I ⊕ I → Fin (r + 1) ⊕ Fin (r + 1) := Sum.map Subtype.val Subtype.val
  have hφ : Function.Injective φ := Subtype.val_injective.sumMap Subtype.val_injective
  let e := (Fintype.equivFin (I ⊕ I)).symm
  refine ⟨_, (Sum.elim S.f S.f' ∘ φ) ∘ e, (hli.comp φ hφ).comp e e.injective, ?_⟩
  rw [e.surjective.range_comp, Frames.spanTo, Frames.spanTo, ← Submodule.span_union]
  congr 1
  ext v
  constructor
  · rintro ⟨i | i, rfl⟩
    · exact Or.inl ⟨i.1, i.2, rfl⟩
    · exact Or.inr ⟨i.1, i.2, rfl⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact ⟨Sum.inl ⟨i, hi⟩, rfl⟩
    · exact ⟨Sum.inr ⟨i, hi⟩, rfl⟩

theorem spanTo_mono (S : Frames L r k) (g : Fin (r + 1) → S.V) {i j : ℕ} (h : i ≤ j) :
    S.spanTo g i ≤ S.spanTo g j :=
  Submodule.span_mono (Set.image_mono fun _ ha => lt_of_lt_of_le ha h)

theorem relIndex_trace (S : Frames L r k) (J : ℕ) (hJ : J ≤ r + 1) (d : S.Datum) (Λ : Submodule L.O S.V)
    (hT : S.IsTerm d Λ) (hl : ∀ y ∈ S.sat Λ, S.levC d Λ y ≤ J) :
    (S.M d Λ ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup.relIndex
      (Λ ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup = S.be d Λ := by
  have hM : S.M d Λ ≤ S.sat Λ := (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT).2.2.1
  have hlev := (GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ hT).2.2.2.2.2.2.2.2.2.2
  set Y := (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O with hY
  have h1 : (S.sat Λ).toAddSubgroup = (Λ ⊓ Y).toAddSubgroup ⊔ (S.M d Λ).toAddSubgroup := by
    apply le_antisymm
    · intro y hy
      obtain ⟨y₁, hy₁, hm⟩ := (hlev y hy J).1 (hl y hy)
      have hy₁Λ : y₁ ∈ Λ := by
        have := Λ.sub_mem hy.1 (hM hm).1
        simpa using this
      have : y = y₁ + (y - y₁) := by abel
      rw [this]
      exact AddSubgroup.add_mem_sup (S := (Λ ⊓ Y).toAddSubgroup) ⟨hy₁Λ, hy₁⟩ hm
    · refine sup_le ?_ hM
      intro y hy
      exact ⟨hy.1, sup_le_sup (spanTo_mono S S.f hJ) (spanTo_mono S S.f' hJ) hy.2⟩
  have h2 : (S.M d Λ ⊓ Y).toAddSubgroup = (S.M d Λ).toAddSubgroup ⊓ (Λ ⊓ Y).toAddSubgroup := by
    ext y
    exact ⟨fun h => ⟨h.1, (hM h.1).1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  rw [h2, AddSubgroup.inf_relIndex_right, Frames.be, h1, AddSubgroup.relIndex_sup_right]

theorem family_vol : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ Λ', S.IsTerm d Λ' → S.InFF β (j + 1) βJ d Λ' → ∀ Yy : Submodule L.O S.V, (Yy = (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)).restrictScalars L.O ∨ Yy = (perp L S.Hm (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1))).restrictScalars L.O) → (Λ ⊓ Yy).toAddSubgroup.relIndex (Λ' ⊓ Yy).toAddSubgroup = (Λ' ⊓ Yy).toAddSubgroup.relIndex (Λ ⊓ Yy).toAddSubgroup ∧ (Λ ⊓ Yy).toAddSubgroup.relIndex (Λ' ⊓ Yy).toAddSubgroup ≠ 0 ∧ (S.M d Λ ⊓ (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)).restrictScalars L.O).toAddSubgroup.relIndex (Λ ⊓ (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)).restrictScalars L.O).toAddSubgroup = β := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hF Λ' hT' hF' Yy hYy
  have hJ : (j : ℕ) + 1 ≤ r + 1 := by have := j.2; omega
  have b1 := relIndex_trace S (j + 1) hJ d Λ hT hF.2.2.1
  have b2 := relIndex_trace S (j + 1) hJ d Λ' hT' hF'.2.2.1
  have hβ : β ≠ 0 := by
    obtain ⟨i, -, hi⟩ := (GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ hT).2.2.2.2.2.1
    rw [← hF.2.1, hi]
    exact pow_ne_zero _ (resQ_ne_zero _ S.ϖ_irr)
  rw [hF.2.1] at b1
  rw [hF'.2.1] at b2
  obtain ⟨hS, -, hM, -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  obtain ⟨hS', -, hM', -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d Λ' hT'
  obtain ⟨v1, v2⟩ := GlobalTheory.T.frameLattice_trace_initialSpan_volume_eq L r k S d Λ hT d Λ' hT' (j + 1) _ hJ rfl
  have hY := relIndex_symm_of_sub hβ
    (Submodule.toAddSubgroup_mono (inf_le_inf_right _ (hM.trans inf_le_left)))
    (Submodule.toAddSubgroup_mono (inf_le_inf_right _ (hM'.trans inf_le_left))) b1 b2 v1 v2
  obtain ⟨m, y, hy, hsp⟩ := exists_basis S (j + 1)
  obtain ⟨p1, p2, p3⟩ := GlobalTheory.T.selfDualHermitianLattice_trace_orthogonal_volume_ratio L S.Hm S.herm Λ Λ' hS hS' m y hy _ _ rfl rfl
  rw [hsp] at p1 p2 p3
  rcases hYy with rfl | rfl
  · exact ⟨hY, p2, b1⟩
  · refine ⟨?_, p1, b1⟩
    rw [← hY] at p3
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero p2) p3

end GlobalTheory.HL.FamilyVol
