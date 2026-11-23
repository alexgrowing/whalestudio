import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToLePerp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFrameCoordinatesTransportInnerLatticesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportInnerLatticesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermOverFrameCoordinates
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.HL.CoordTermWt
open GlobalTheory.HL.CoordTerm

lemma unitri_mem {E W : Type} [CommRing E] [AddCommGroup W] [Module E W] {m : ℕ} (g g' : Fin m → W)
    (s : Matrix (Fin m) (Fin m) E) (h0 : ∀ i j, j < i → s i j = 0) (h1 : ∀ i, s i i = 1)
    (hs : ∀ j, g' j = ∑ i, s i j • g i) (A : Submodule E W) :
    (∀ b, g' b ∈ A) ↔ ∀ b, g b ∈ A := by
  constructor
  · intro h j
    induction j using WellFoundedLT.induction with
    | ind j ih =>
      have h2 : g j = g' j - ∑ i ∈ Finset.univ.erase j, s i j • g i := by
        rw [hs, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), h1, one_smul, add_sub_cancel_right]
      rw [h2]
      refine sub_mem (h j) (Submodule.sum_mem _ fun i hi => ?_)
      rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hi) with h3 | h3
      · exact A.smul_mem _ (ih i h3)
      · rw [h0 i j h3, zero_smul]; exact zero_mem _
  · intro h j
    rw [hs]
    exact Submodule.sum_mem _ fun i _ => A.smul_mem _ (h i)

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)

lemma fam_mem {R : Type} [Ring R] [Module R V] (t : Term V M r) (A : Submodule R V) :
    (∀ i, H.MMfam t i ∈ A) ↔ (∀ b, t.f b ∈ A) ∧
      ∀ b, algebraMap F E (LocNG.theta M)⁻¹ • (t.f' b - t.f b) ∈ A := by
  unfold HermSp.MMfam LocNG.theta
  cases M.split with
  | none =>
    simp only [Sum.forall, Sum.elim_inl, Sum.elim_inr, inv_one, map_one, one_smul]
    refine and_congr_right fun h => forall_congr' fun b => ?_
    exact (A.sub_mem_iff_left (h b)).symm
  | some g => simp only [Sum.forall, Sum.elim_inl, Sum.elim_inr]

lemma th_ne (S : Frames M.L r k) : S.th ≠ 0 := by
  unfold Frames.th
  split_ifs
  · intro h
    exact S.ϖ_irr.ne_zero (Subtype.ext h)
  · exact one_ne_zero

lemma lat_span (t : Term V M r) :
    c.lat (Submodule.span M.L.O (Set.range (H.MMfam t))) =
      S.Mof (fun b => c.e (t.f b)) (fun b => c.e (t.f' b)) := by
  refine eq_of_forall_ge_iff fun A => ?_
  unfold Coord.lat Frames.Mof
  rw [Submodule.map_le_iff_le_comap, Submodule.span_le, Submodule.span_le, Set.range_subset_iff,
    Set.union_subset_iff, Set.range_subset_iff, Set.range_subset_iff]
  refine (fam_mem t _).trans ?_
  rw [CoordUnip.theta_eq c]
  simp [Submodule.mem_comap]

lemma map_span (t : Term V M r) (A : Submodule E S.V) :
    (Submodule.span E (Set.range (H.MMfam t))).map (c.e : V →ₗ[E] S.V) ≤ A ↔
      (∀ b, c.e (t.f b) ∈ A) ∧ ∀ b, c.e (t.f' b) ∈ A := by
  rw [Submodule.map_le_iff_le_comap, Submodule.span_le, Set.range_subset_iff]
  refine (fam_mem t _).trans ?_
  rw [CoordUnip.theta_eq c]
  refine and_congr_right fun h => forall_congr' fun b => ?_
  have hu : IsUnit (algebraMap F E S.th⁻¹) := (IsUnit.mk0 _ (inv_ne_zero (th_ne S))).map _
  rw [Submodule.smul_mem_iff_of_isUnit _ hu, Submodule.sub_mem_iff_left _ (h b)]
  rfl

lemma ME_le (S : Frames M.L r k) (A : Submodule E S.V) :
    S.ME ≤ A ↔ (∀ b, S.f b ∈ A) ∧ ∀ b, S.f' b ∈ A := by
  unfold Frames.ME Frames.spanTo
  have h : {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.univ := by
    exact Set.eq_univ_of_forall fun i => i.2
  rw [sup_le_iff, Submodule.span_le, Submodule.span_le, h, Set.image_univ, Set.image_univ,
    Set.range_subset_iff, Set.range_subset_iff]
  rfl

theorem terms_correspond : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), (∀ (d : LocNG.Datum P) (t : Term V M r), LocNG.IsTermOver P d t → S.IsTerm (c.dat d) (c.lat t.abelian₂) ∧ LocNG.om P t = S.om (c.dat d) (c.lat t.abelian₂) ∧ (LocNG.BBne (H := H) t ↔ ¬ S.BBzero (c.dat d) (c.lat t.abelian₂))) ∧ (∀ (d : LocNG.Datum P) Λ, S.IsTerm (c.dat d) Λ → ∃ t, LocNG.IsTermOver P d t ∧ c.lat t.abelian₂ = Λ) ∧ ∀ δ Λ, S.IsTerm δ Λ → ∃ d : LocNG.Datum P, δ = c.dat d := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c
  letI := hM.loc
  haveI := hM.char0
  obtain ⟨hth, hN, hN', -, hpsi, -⟩ := GlobalTheory.HL.CoordUnip.transport M hM H r k P S c
  obtain ⟨-, iA, oA, sA⟩ := GlobalTheory.T.hermitianFrameCoordinates_transport_innerLattices M hM H r k P S c
  obtain ⟨-, iB, oB, sB⟩ := GlobalTheory.T.framePairCoordinates_transport_innerLattices M hM H r k P S c
  have T1 := isTermW_iff M hM H r k P S c
  have hsurj : ∀ Λ : Submodule M.L.O S.V, ∃ Λ₀, c.lat Λ₀ = Λ := by
    intro B
    refine ⟨B.comap ((c.e : V →ₗ[E] S.V).restrictScalars M.L.O), ?_⟩
    ext v
    obtain ⟨v, rfl⟩ := c.e.surjective v
    rw [mem_lat]; rfl
  refine ⟨?_, ?_, ?_⟩
  · rintro d ⟨Λ, f, f', T, T'⟩ ht
    obtain ⟨hT, hT', ⟨n, hn, hf, h1⟩, ⟨n', hn', hf', h2⟩, -⟩ := id ht
    dsimp only at hT hT' hf hf' h1 h2
    subst hT hT' hf hf'
    have hW := (T1 d n n' Λ).1 ⟨ht, hn, hn', h1, h2⟩
    have hI : S.IsTerm (c.dat d) (c.lat Λ) := ⟨(c.grp n, c.grp n'), hW⟩
    obtain ⟨w1, w2, -⟩ := GlobalTheory.HL.WitIndep.witness_independence M.L r k S _ _ _ _ hW
    obtain ⟨-, -, hle, -⟩ := GlobalTheory.HL.TermBasic.term_basic M.L r k S _ _ hI
    refine ⟨hI, ?_, ?_⟩
    · dsimp only
      rw [w1, ← (hpsi n).1, ← (hpsi n').2]
      rfl
    · dsimp only
      set t : Term V M r := ⟨Λ, fun b => n (P.A.f b), fun b => n' (P.B.f b), P.A.T, P.B.T⟩ with htd
      have e1 : ∀ b, c.e (t.f b) = c.grp n (S.f b) := fun b => by rw [c.f_eq, grp_e]
      have e2 : ∀ b, c.e (t.f' b) = c.grp n' (S.f' b) := fun b => by rw [c.f'_eq, grp_e]
      have hO : c.lat (Submodule.span M.L.O (Set.range (H.MMfam t))) = S.M (c.dat d) (c.lat Λ) := by
        rw [lat_span, w2]
        simp only [e1, e2]
      obtain ⟨o1, o2, -⟩ := GlobalTheory.HL.FrameOnto.unipotent_onto M.L r k S
      obtain ⟨s, ⟨s0, s1⟩, hs⟩ := o1 _ hW.2.2.1
      obtain ⟨s', ⟨s0', s1'⟩, hs'⟩ := o2 _ hW.2.2.2.1
      have hE : (Submodule.span E (Set.range (H.MMfam t))).map (c.e : V →ₗ[E] S.V) = S.ME := by
        refine eq_of_forall_ge_iff fun A => ?_
        rw [map_span, ME_le]
        simp only [e1, e2]
        exact and_congr (unitri_mem _ _ s s0 s1 hs A) (unitri_mem _ _ s' s0' s1' hs' A)
      have hE' : ∀ v, c.e v ∈ S.ME ↔ v ∈ Submodule.span E (Set.range (H.MMfam t)) := by
        intro v
        rw [← hE]
        constructor
        · rintro ⟨y, hy, h⟩
          have : y = v := c.e.injective h
          exact this ▸ hy
        · intro h; exact ⟨v, h, rfl⟩
      have hsat : ∀ v, c.e v ∈ S.sat (c.lat Λ) ↔
          v ∈ Λ ∧ v ∈ Submodule.span E (Set.range (H.MMfam t)) := by
        intro v
        rw [← hE', ← mem_lat c]
        rfl
      unfold Frames.BBzero
      constructor
      · rintro ⟨v, hv, hv1, hv2⟩ h
        apply hv2
        rw [← mem_lat c, hO, h, hsat]
        exact ⟨hv, hv1⟩
      · intro h
        by_contra hc
        apply h
        refine le_antisymm hle fun y hy => ?_
        obtain ⟨v, rfl⟩ := c.e.surjective y
        rw [hsat] at hy
        rw [← hO, mem_lat]
        by_contra hv
        exact hc ⟨v, hy.1, hy.2, hv⟩
  · rintro d Λ ⟨⟨n, n'⟩, hW⟩
    obtain ⟨Λ, rfl⟩ := hsurj Λ
    obtain ⟨n, rfl⟩ := c.grp.surjective n
    obtain ⟨n', rfl⟩ := c.grp.surjective n'
    exact ⟨_, ((T1 d n n' Λ).2 hW).1, rfl⟩
  · rintro δ Λ hI
    obtain ⟨⟨n, n'⟩, hA, hB, hn, hn', h1, h2, hc, -⟩ := id hI
    dsimp only at hn hn' h1 h2 hc
    obtain ⟨Λ, rfl⟩ := hsurj Λ
    obtain ⟨n, rfl⟩ := c.grp.surjective n
    obtain ⟨n', rfl⟩ := c.grp.surjective n'
    obtain ⟨L, hL⟩ := oA _ hA
    obtain ⟨L', hL'⟩ := oB _ hB
    rw [hL, ← iA] at hA
    rw [hL', ← iB] at hB
    rw [hL, ← sA, ← lat_img, lat_inj] at h1
    rw [hL', ← sB, ← lat_img, lat_inj] at h2
    rw [← hN] at hn
    rw [← hN'] at hn'
    let d : LocNG.Datum P :=
      { L := L, L' := L', hL := hA, hL' := hB
        io := {q | ∃ g, M.split = some g ∧ q ∈ H.iotaGraph g ⟨Λ, P.A.f, P.B.f, P.A.T, P.B.T⟩}
        io_L := fun h => by simp [h] }
    have hW := (T1 d n n' Λ).1 ⟨⟨rfl, rfl, ⟨n, hn, rfl, h1⟩, ⟨n', hn', rfl, h2⟩, fun g hg => ⟨?_, ?_⟩⟩,
      hn, hn', h1, h2⟩
    · obtain ⟨-, -, -, -, -, -, -, hu⟩ := GlobalTheory.HL.TermBasic.term_basic M.L r k S _ _ hI
      exact ⟨d, (hu _ ⟨(c.grp n, c.grp n'), hW⟩).symm⟩
    · intro b
      have hq : S.th = (g.q : F) := by rw [← hth, LocNG.theta, hg]
      have h := hc b
      rwa [c.f_eq, c.f'_eq, grp_e, grp_e, ← map_sub, inTh_iff, hq] at h
    · ext q
      simp [d, hg]

end GlobalTheory.HL.CoordTermWt
