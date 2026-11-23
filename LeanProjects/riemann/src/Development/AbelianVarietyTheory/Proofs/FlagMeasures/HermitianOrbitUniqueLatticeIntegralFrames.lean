import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotField
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportUnitaryMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsCorrespond
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesLocalHeightEqResidueCard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToLePerp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetFrameClassProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitEntries
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfMulVec
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericLocalTermsSelfDualLatticesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryComplementMovesHermitianTermsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDataWithTermSingleOrbitPrimeToStatement
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.GoodFrames

theorem Mof_eq_span {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] {L : LocE F E} {r k : ℕ} (S : Frames L r k) (hth : S.th = 1)
    (g g' : Fin (r + 1) → S.V) :
    S.Mof g g' = Submodule.span L.O (Set.range (Sum.elim g g')) := by
  have hth' : algebraMap F E S.th⁻¹ = 1 := by rw [hth, inv_one, map_one]
  apply le_antisymm
  · rw [Frames.Mof]
    apply Submodule.span_le.2
    rintro _ (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact Submodule.subset_span ⟨Sum.inl j, rfl⟩
    · simp only [hth', one_smul, SetLike.mem_coe]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨Sum.inr j, rfl⟩)
        (Submodule.subset_span ⟨Sum.inl j, rfl⟩)
  · apply Submodule.span_le.2
    rintro _ ⟨j | j, rfl⟩
    · exact Submodule.subset_span (Or.inl ⟨j, rfl⟩)
    · have h1 : g' j = algebraMap F E S.th⁻¹ • (g' j - g j) + g j := by rw [hth']; simp
      simp only [Sum.elim_inr, SetLike.mem_coe]
      rw [h1]
      exact Submodule.add_mem _ (Submodule.subset_span (Or.inr ⟨j, rfl⟩))
        (Submodule.subset_span (Or.inl ⟨j, rfl⟩))

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), 4 * r + 7 ≤ k → Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → P.PrimeTo → ∀ (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (∀ a b, b < a → A a b = 0 ∧ A' a b = 0) → (∀ a, A a a = 1 ∧ A' a a = 1) → (∀ a b, A a b ∈ M.L.O ∧ A' a b ∈ M.L.O) → ∀ (f f' : Fin (r + 1) → V), (∀ j, f j = ∑ i, A i j • P.A.f i) → (∀ j, f' j = ∑ i, A' i j • P.B.f i) → ∀ d0 : LocNG.Datum P, (∃ t, LocNG.IsTermOver P d0 t) → ∀ d : LocNG.Datum P, (LocNG.Datum.Rel d0 d → ∃! Λ : Submodule M.L.O V, LocNG.IsTermOver P d (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧ ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)) ∧ ((∃ t, LocNG.IsTermOver P d t) → LocNG.Datum.Rel d0 d) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hk hdim hrel hpt A A' hAt hAd hAi f f' hf hf' d0 hd0 d
  haveI := hM.loc
  haveI := hM.char0
  obtain ⟨S, ⟨c⟩⟩ := GlobalTheory.HL.CoordExist.exists_coord M hM H r k P hdim hrel
  have hsplit : M.split = none := hpt.1
  obtain ⟨hgg, hvG, -⟩ := (GlobalTheory.HL.CoordHeight.height_eq M hM H r k P S c).2.2 hpt
  have ha : S.a = 0 := by simp [GlobalTheory.HL.Frames.a, GlobalTheory.HL.Frames.vth, hgg, hvG]
  have hth : S.th = 1 := by simp [GlobalTheory.HL.Frames.th, hgg]
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
  have hTC := GlobalTheory.HL.CoordTermWt.terms_correspond M hM H r k P S c
  have hDT := GlobalTheory.HL.CoordDatum.transport M hM H r k P S c
  have hMT := GlobalTheory.HL.CoordMass.transport M hM H r k P S c
  have hNT := GlobalTheory.HL.CoordUnip.transport M hM H r k P S c

  have hfc : ∀ j, c.e (f j) = ∑ i, A i j • S.f i := by
    intro j; rw [hf j, map_sum]; simp [c.f_eq]
  have hfc' : ∀ j, c.e (f' j) = ∑ i, A' i j • S.f' i := by
    intro j; rw [hf' j, map_sum]; simp [c.f'_eq]
  have hfN : ∃ n ∈ P.A.N, f = fun b => n (P.A.f b) := by
    obtain ⟨n, hn, hne⟩ := ((GlobalTheory.HL.FrameOnto.unipotent_onto M.L r k S).2.2 A
      ⟨fun i j h => (hAt i j h).1, fun i => (hAd i).1⟩).1
    refine ⟨c.grp.symm n, (hNT.2.1 _).2 (by simpa using hn), ?_⟩
    funext b
    apply c.e.injective
    change c.e (f b) = c.e (c.e.symm (n (c.e (P.A.f b))))
    rw [LinearEquiv.apply_symm_apply, ← c.f_eq, hne b, hfc b]
  have hf'N : ∃ n ∈ P.B.N, f' = fun b => n (P.B.f b) := by
    obtain ⟨n, hn, hne⟩ := ((GlobalTheory.HL.FrameOnto.unipotent_onto M.L r k S).2.2 A'
      ⟨fun i j h => (hAt i j h).2, fun i => (hAd i).2⟩).2
    refine ⟨c.grp.symm n, (hNT.2.2.1 _).2 (by simpa using hn), ?_⟩
    funext b
    apply c.e.injective
    change c.e (f' b) = c.e (c.e.symm (n (c.e (P.B.f b))))
    rw [LinearEquiv.apply_symm_apply, ← c.f'_eq, hne b, hfc' b]

  set fc : Fin (r + 1) → S.V := fun b => c.e (f b) with hfcdef
  set fc' : Fin (r + 1) → S.V := fun b => c.e (f' b) with hfc'def
  have hAi1 : GlobalTheory.HL.IsIntM M.L A := fun i j => (hAi i j).1
  have hAi2 : GlobalTheory.HL.IsIntM M.L A' := fun i j => (hAi i j).2
  have hcls : (fc, fc') ∈ S.frameCls S.f S.f' :=
    GlobalTheory.HL.GoodClass.mem_cls S hgg S.f S.f' (fc, fc')
      ⟨fun i j h => (hAt i j h).1, fun i => (hAd i).1⟩ ⟨fun i j h => (hAt i j h).2, fun i => (hAd i).2⟩
      hAi1 hAi2 hfc hfc'
  have hMof : S.Mof fc fc' = S.Mof S.f S.f' :=
    ((GlobalTheory.HL.FrameClass.frame_classes M.L r k S S.f S.f').2.1 _ hcls).2
  have hMM : ∀ Λ : Submodule M.L.O V,
      H.MMfam (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) = Sum.elim f f' := by
    intro Λ; simp [HermSp.MMfam, hsplit]
  have hmemlat : ∀ (Λ : Submodule M.L.O V) (v : V), c.e v ∈ c.lat Λ ↔ v ∈ Λ := by
    intro Λ v
    constructor
    · rintro ⟨w, hw, e⟩
      have : w = v := c.e.injective e
      rwa [← this]
    · intro hv; exact ⟨v, hv, rfl⟩
  have hlatspan : c.lat (Submodule.span M.L.O (Set.range (Sum.elim f f'))) =
      Submodule.span M.L.O (Set.range (Sum.elim fc fc')) := by
    rw [Coord.lat, Submodule.map_span, ← Set.range_comp]
    congr 2
    funext x
    cases x <;> rfl
  have hst : ∀ g : Fin (r + 1) → S.V, S.spanTo g (r + 1) = Submodule.span E (Set.range g) := by
    intro g
    have hs : {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.univ := by ext i; simpa using i.2
    rw [Frames.spanTo, hs, Set.image_univ]
  have hME : ∀ v : V, c.e v ∈ S.ME ↔ v ∈ Submodule.span E (Set.range (Sum.elim f f')) := by
    have e1 : S.ME = Submodule.span E (Set.range (Sum.elim fc fc')) := by
      rw [Frames.ME, hst, hst, ← Submodule.span_union, ← Set.Sum.elim_range,
        ← Submodule.span_span_of_tower M.L.O E (Set.range (Sum.elim S.f S.f')),
        ← Submodule.span_span_of_tower M.L.O E (Set.range (Sum.elim fc fc')),
        ← Mof_eq_span S hth, ← Mof_eq_span S hth, hMof]
    have e2 : Submodule.span E (Set.range (Sum.elim fc fc')) =
        (Submodule.span E (Set.range (Sum.elim f f'))).map (c.e : V →ₗ[E] S.V) := by
      rw [Submodule.map_span, ← Set.range_comp]
      congr 2
      funext x
      cases x <;> rfl
    intro v
    rw [e1, e2, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]

  have hKM : ∀ Λ : Submodule M.L.O V,
      ((∀ i, H.MMfam (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) i ∈ Λ) ∧
        ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)) ↔
      S.sat (c.lat Λ) = S.Mof fc fc' := by
    intro Λ
    rw [Mof_eq_span S hth, ← hlatspan]
    simp only [LocNG.BBne, hMM, not_exists, not_and, not_not]
    constructor
    · rintro ⟨hin, hbb⟩
      ext x
      obtain ⟨v, rfl⟩ := c.e.surjective x
      rw [Frames.sat, Submodule.mem_inf, Submodule.restrictScalars_mem, hmemlat, hmemlat, hME]
      constructor
      · rintro ⟨h1, h2⟩; exact hbb v h1 h2
      · intro hv
        refine ⟨(Submodule.span_le.2 ?_) hv, ?_⟩
        · rintro _ ⟨i, rfl⟩; exact hin i
        · exact Submodule.span_le_restrictScalars M.L.O E _ hv
    · intro hsat
      have hsub : ∀ v, v ∈ Submodule.span M.L.O (Set.range (Sum.elim f f')) ↔ v ∈ Λ ∧
          v ∈ Submodule.span E (Set.range (Sum.elim f f')) := by
        intro v
        rw [← hmemlat, ← hsat, Frames.sat, Submodule.mem_inf, Submodule.restrictScalars_mem, hmemlat, hME]
      refine ⟨fun i => ((hsub _).1 (Submodule.subset_span ⟨i, rfl⟩)).1, fun v h1 h2 => (hsub v).2 ⟨h1, h2⟩⟩

  have hloc := GlobalTheory.T.generic_local_terms_selfDual_lattices M hM H r k P hdim hrel f f' hfN hf'N
  have hmov := GlobalTheory.T.unitaryComplement_moves_hermitianTerms M hM H r k P hdim hrel f f' hfN hf'N

  have hex0 : ∃ Λ : Submodule M.L.O V,
      LocNG.IsTermOver P d0 (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧
        ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) := by
    obtain ⟨t0, ht0⟩ := hd0
    have hT0 := (hTC.1 d0 t0 ht0).1
    obtain ⟨s, hs, hsFr⟩ := (GlobalTheory.HL.GoodClass.one_class M.L r k S hgg hDu).2.2 _
      ((GlobalTheory.HL.TermBasic.term_basic M.L r k S _ _ hT0).2.2.2.2.2.2.1)
    have hact := GlobalTheory.FrameAct.stabiliser_acts_on_terms M.L r k S (c.dat d0) _ hT0 s⁻¹ (S.St.inv_mem hs)
    have hT1 : S.IsTerm (c.dat d0) (s⁻¹ • c.lat t0.abelian₂) := hact.1
    have hFr1 : S.Fr (c.dat d0) (s⁻¹ • c.lat t0.abelian₂) = S.frameCls S.f S.f' := by
      rw [hact.2.2.2.2.1, hsFr, smul_smul, inv_mul_cancel, one_smul]
    have hBB1 := (GlobalTheory.HL.UnimodTerm.term_unique M.L r k S _ _ hT1 ha).1
    have hM1 : S.M (c.dat d0) (s⁻¹ • c.lat t0.abelian₂) = S.Mof fc fc' := by
      rw [hMof]
      have hmem : (S.fr (c.dat d0) (s⁻¹ • c.lat t0.abelian₂), S.fr' (c.dat d0) (s⁻¹ • c.lat t0.abelian₂)) ∈
          S.frameCls S.f S.f' := by
        rw [← hFr1]; exact GlobalTheory.HL.FrameClass.refl_mem S _ _
      exact ((GlobalTheory.HL.FrameClass.frame_classes M.L r k S S.f S.f').2.1 _ hmem).2
    obtain ⟨⟨Lam1, g1, g1', T1, T1'⟩, ht1, ht1l⟩ := hTC.2.1 d0 _ hT1
    obtain rfl : T1 = P.A.T := ht1.1
    obtain rfl : T1' = P.B.T := ht1.2.1
    have hsat1 : S.sat (c.lat Lam1) = S.Mof fc fc' := by
      rw [ht1l, ← hBB1, hM1]
    obtain ⟨hin, hbb⟩ := (hKM Lam1).2 hsat1
    have hbb1 : ¬ LocNG.BBne (H := H) (⟨Lam1, g1, g1', P.A.T, P.B.T⟩ : Term V M r) := fun h =>
      ((hTC.1 d0 _ ht1).2.2.1 h) (by rw [ht1l]; exact hBB1)
    obtain ⟨n1, hn1, hn1f, -⟩ := ht1.2.2.1
    obtain ⟨n1', hn1', hn1f', -⟩ := ht1.2.2.2.1
    obtain ⟨hSD, hFG, -, -⟩ := (GlobalTheory.T.generic_local_terms_selfDual_lattices M hM H r k P hdim hrel g1 g1' ⟨n1, hn1, hn1f⟩
      ⟨n1', hn1', hn1f'⟩ Lam1).1.2 ⟨d0, ht1, hbb1⟩
    obtain ⟨d1, hd1, hbb1'⟩ := (hloc Lam1).1.1 ⟨hSD, hFG, hin, hbb⟩
    have hd10 : d1 = d0 := by
      have h2 := (hTC.1 d1 _ hd1).1
      simp only at h2
      rw [ht1l] at h2
      exact hDT.1 ((GlobalTheory.HL.TermBasic.term_basic M.L r k S _ _ hT1).2.2.2.2.2.2.2 _ h2)
    subst hd10
    exact ⟨Lam1, hd1, hbb1'⟩

  have huniq : ∀ (d : LocNG.Datum P) (Λ Λ' : Submodule M.L.O V),
      (LocNG.IsTermOver P d (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧
        ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)) →
      (LocNG.IsTermOver P d (⟨Λ', f, f', P.A.T, P.B.T⟩ : Term V M r) ∧
        ¬ LocNG.BBne (H := H) (⟨Λ', f, f', P.A.T, P.B.T⟩ : Term V M r)) → Λ = Λ' := by
    intro d Λ Λ' h h'
    have key : ∀ Λ : Submodule M.L.O V,
        (LocNG.IsTermOver P d (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧
          ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)) →
        S.IsTerm (c.dat d) (c.lat Λ) ∧ S.M (c.dat d) (c.lat Λ) = S.Mof fc fc' := by
      intro Λ h
      obtain ⟨-, -, hin, hbb⟩ := (hloc Λ).1.2 ⟨d, h⟩
      have h2 := hTC.1 d _ h.1
      refine ⟨h2.1, ?_⟩
      have hz : S.BBzero (c.dat d) (c.lat Λ) := by
        by_contra hn; exact h.2 (h2.2.2.2 hn)
      rw [hz]; exact (hKM Λ).1 ⟨hin, hbb⟩
    obtain ⟨a1, a2⟩ := key Λ h
    obtain ⟨b1, b2⟩ := key Λ' h'
    apply hMT.2.2.1.1
    exact le_antisymm (GlobalTheory.HL.UnimodTerm.le_of_M_eq S b1 a1 ha (a2.trans b2.symm))
      (GlobalTheory.HL.UnimodTerm.le_of_M_eq S a1 b1 ha (b2.trans a2.symm))
  refine ⟨fun hR => ?_, fun ht => ?_⟩
  · obtain ⟨Λ0, h0⟩ := hex0
    obtain ⟨g, hg, hmv⟩ := hR
    have hset := (hmov g hg d0 d hmv).2
    have hmem : LocNG.img g Λ0 ∈ {Λ : Submodule M.L.O V |
        LocNG.IsTermOver P d (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧
          ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)} := by
      rw [← hset]; exact ⟨Λ0, h0, rfl⟩
    exact ⟨LocNG.img g Λ0, hmem, fun Λ hΛ => huniq d _ _ hΛ hmem⟩
  · obtain ⟨t, ht⟩ := ht
    obtain ⟨t0, ht0⟩ := hd0
    exact GlobalTheory.T.hermitianData_with_term_single_orbit_primeTo M hM H r k P hdim hrel hpt d0 d t0 t ht0 ht

end GlobalTheory.HL.GoodFrames
