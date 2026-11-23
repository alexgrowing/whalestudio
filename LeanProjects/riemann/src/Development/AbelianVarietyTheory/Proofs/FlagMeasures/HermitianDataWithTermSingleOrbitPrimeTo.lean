import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordinateLatticeUniqueTermAlmostAllPlaces
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotField
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsCorrespond
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesLocalHeightEqResidueCard

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver GlobalTheory.HL
open scoped Pointwise Classical

namespace GlobalTheory.HL.PrimeToOrbit

theorem coord_one_orbit {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (r k : ℕ)
    (S : GlobalTheory.HL.Frames L r k) (hgg : S.gg = false) (hvG : vE L S.ϖ S.G = 0)
    (hDu : ∀ l, S.D l ≠ 0 → S.D l ∈ L.O ∧ ∃ y ∈ L.O, S.D l * y = 1)
    {δ δ' : S.Datum} {Λ Λ' : Submodule L.O S.V} (hT : S.IsTerm δ Λ) (hT' : S.IsTerm δ' Λ') :
    ∃ h ∈ S.H0, h • δ = δ' := by
  have ha : S.a = 0 := by simp [GlobalTheory.HL.Frames.a, GlobalTheory.HL.Frames.vth, hgg, hvG]
  obtain ⟨-, -, hall⟩ := GlobalTheory.HL.GoodClass.one_class L r k S hgg hDu
  have hint : ∀ d Λ, S.IsTerm d Λ → S.IsIntCls (S.Fr d Λ) := fun d Λ h =>
    (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ h).2.2.2.2.2.2.1
  have hdd : ∀ d d' Λ, S.IsTerm d Λ → S.IsTerm d' Λ → d' = d := fun d d' Λ h h' =>
    (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ h).2.2.2.2.2.2.2 d' h'
  have hact := GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S
  have hcom := GlobalTheory.HL.ComplAct.main L r k S
  have hcls := GlobalTheory.HL.FrameClass.frame_classes L r k S
  obtain ⟨s, hs, e⟩ := hall _ (hint _ _ hT)
  obtain ⟨s', hs', e'⟩ := hall _ (hint _ _ hT')
  have h1 := hact δ _ hT _ (S.St.inv_mem hs)
  have h1' := hact δ' _ hT' _ (S.St.inv_mem hs')
  have hFr₁ : S.Fr δ (s⁻¹ • Λ) = S.frameCls S.f S.f' := by
    rw [h1.2.2.2.2.1, e, smul_smul, inv_mul_cancel, one_smul]
  have hFr₁' : S.Fr δ' (s'⁻¹ • Λ') = S.frameCls S.f S.f' := by
    rw [h1'.2.2.2.2.1, e', smul_smul, inv_mul_cancel, one_smul]
  have hM : S.M δ (s⁻¹ • Λ) = S.M δ' (s'⁻¹ • Λ') := by
    have h3 : (S.fr δ (s⁻¹ • Λ), S.fr' δ (s⁻¹ • Λ)) ∈ S.Fr δ' (s'⁻¹ • Λ') := by
      rw [hFr₁', ← hFr₁]; exact (hcls _ _).1
    exact ((hcls _ _).2.1 _ h3).2
  obtain ⟨h, hh, e₁⟩ := GlobalTheory.HL.StdPlace.term_orbit L r k S ha h1.1 h1'.1 hM
  have h4 := (hcom δ' _ h1'.1 h hh).1
  rw [e₁] at h4
  refine ⟨h⁻¹, S.H0.inv_mem hh, ?_⟩
  have h5 : h • δ' = δ := hdd _ _ _ h1.1 h4
  rw [← h5, smul_smul, inv_mul_cancel, one_smul]

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (k : ℕ) (P : FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (theta M) → P.PrimeTo → ∀ (d d' : Datum P) (t t' : Term V M r), IsTermOver P d t → IsTermOver P d' t' → Datum.Rel d d' := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hdim hrel hpt d d' t t' ht ht'
  have := hM.loc
  have := hM.char0
  obtain ⟨S, ⟨c⟩⟩ := GlobalTheory.HL.CoordExist.exists_coord M hM H r k P hdim hrel
  obtain ⟨-, -, hgg, hvG, -⟩ : _ ∧ _ ∧ (S.gg = false ∧ vE M.L S.ϖ S.G = 0 ∧ True) := by
    obtain ⟨a1, a2, a3⟩ := GlobalTheory.HL.CoordHeight.height_eq M hM H r k P S c
    obtain ⟨b1, b2, -⟩ := a3 hpt
    exact ⟨a1, a2, b1, b2, trivial⟩
  obtain ⟨-, -, -, -, hD, -⟩ := GlobalTheory.FrameBasic.main M.L r k S
  have hDu : ∀ l, S.D l ≠ 0 → S.D l ∈ M.L.O ∧ ∃ y ∈ M.L.O, S.D l * y = 1 := by
    intro l hl
    by_cases h0 : l = 0
    · have e : S.D l = 1 := by
        subst h0
        unfold GlobalTheory.HL.Frames.D GlobalTheory.HL.lead
        exact Matrix.det_isEmpty (n := Fin 0)
      rw [e]
      exact ⟨M.L.O.one_mem, 1, M.L.O.one_mem, mul_one 1⟩
    · have hmem : (l : ℕ) ∈ P.ends := by
        unfold LocNG.FPair.ends
        simp only [Finset.mem_filter, Finset.mem_range]
        rw [GlobalTheory.HL.CoordHeight.Dm_eq c]
        exact ⟨l.2, Nat.one_le_iff_ne_zero.mpr fun h => h0 (Fin.ext h), hD l hl⟩
      have := hpt.2.2 _ hmem
      rwa [GlobalTheory.HL.CoordHeight.Dm_eq c] at this
  have hT := ((GlobalTheory.HL.CoordTermWt.terms_correspond M hM H r k P S c).1 d t ht).1
  have hT' := ((GlobalTheory.HL.CoordTermWt.terms_correspond M hM H r k P S c).1 d' t' ht').1
  exact ((GlobalTheory.HL.CoordDatum.transport M hM H r k P S c).2.2.1 d d').2
    (coord_one_orbit M.L r k S hgg hvG hDu hT hT')

end GlobalTheory.HL.PrimeToOrbit
