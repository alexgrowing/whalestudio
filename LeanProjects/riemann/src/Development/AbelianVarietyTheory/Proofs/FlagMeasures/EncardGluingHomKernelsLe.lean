import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardSubmoduleAndHomLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetFrameClassProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGluingHomomorphismDefectGroupStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameLatticeGramDetAndMinorsOrbitInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBasisFgMaximalOrderSpanningFree

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.GluingKernels

theorem encard_le_of_param {R D β : Type} [CommRing R] [AddCommGroup D] [Module R D] [Finite D]
    (m j : ℕ) (Φ : (Fin m → D) → β) (T : Set β)
    (hT : ∀ t ∈ T, ∃ I : Submodule R D, Nat.card I = j ∧ ∃ x : Fin m → D, (∀ i, x i ∈ I) ∧ Φ x = t) :
    T.encard ≤ ((Nat.card (Submodule R D) * j ^ m : ℕ) : ℕ∞) := by
  haveI : Finite (Submodule R D) := Finite.of_injective _ (SetLike.coe_injective (A := Submodule R D))
  let A := Σ I : {I : Submodule R D // Nat.card I = j}, (Fin m → I.1)
  let Ψ : A → β := fun a => Φ fun i => (a.2 i : D)
  have hsub : T ⊆ Ψ '' Set.univ := by
    intro t ht
    obtain ⟨I, hI, x, hx, rfl⟩ := hT t ht
    exact ⟨⟨⟨I, hI⟩, fun i => ⟨x i, hx i⟩⟩, trivial, rfl⟩
  haveI : Fintype {I : Submodule R D // Nat.card I = j} := Fintype.ofFinite _
  have hA : Nat.card A ≤ Nat.card (Submodule R D) * j ^ m := by
    have h1 : Nat.card A = ∑ I : {I : Submodule R D // Nat.card I = j}, j ^ m := by
      rw [Nat.card_sigma]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [Nat.card_fun, I.2, Nat.card_eq_fintype_card, Fintype.card_fin]
    rw [h1, Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]
    exact Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective _ Subtype.val_injective)
  calc T.encard ≤ (Ψ '' Set.univ).encard := Set.encard_le_encard hsub
    _ ≤ (Set.univ : Set A).encard := Set.encard_image_le _ _
    _ = (Nat.card A : ℕ∞) := by
      rw [Set.encard_univ, ENat.card_eq_coe_natCard]
    _ ≤ _ := by exact_mod_cast hA

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E}
  {r k : ℕ} (S : Frames L r k)

theorem sat_gens (d : S.Datum) (Λ : Submodule L.O S.V) (hΛ : S.IsTerm d Λ) :
    ∃ b : Fin ((r + 1) + (r + 1)) → S.V, S.sat Λ = Submodule.span L.O (Set.range b) := by
  obtain ⟨hSD, hW, -, h1, h2, hli, -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hΛ
  haveI : IsPrincipalIdealRing L.O := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.1
  have hfg : (S.sat Λ).FG := by
    haveI : IsNoetherian L.O Λ := isNoetherian_of_fg_of_noetherian Λ hSD.1.1
    exact (isNoetherian_submodule.1 this) _ inf_le_left
  have hsp := (GlobalTheory.T.frameLattice_gramDet_and_minors_orbit_invariant L r k S _ hW.2.2.1 _ hW.2.2.2.1).2.2
  set y := Sum.elim (S.fr d Λ) (S.fr' d Λ) with hy
  have hr : Set.range (y ∘ finSumFinEquiv.symm) = Set.range y :=
    finSumFinEquiv.symm.surjective.range_comp y
  obtain ⟨b, -, hb⟩ := GlobalTheory.OrderBasis.order_basis L (y ∘ finSumFinEquiv.symm)
    (hli.comp _ finSumFinEquiv.symm.injective) (S.sat Λ) hfg (by
      rw [hr]
      apply le_antisymm
      · rw [Submodule.span_le]
        intro x hx
        have hx2 : x ∈ S.ME := hx.2
        rw [← hsp] at hx2
        refine (Submodule.span_le.2 ?_) hx2
        rintro _ ⟨i | i, rfl⟩
        · exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
        · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩)
            (Submodule.subset_span ⟨Sum.inl i, rfl⟩))
      · apply Submodule.span_mono
        rintro _ ⟨i | i, rfl⟩
        · have := (h1 (r + 1) le_rfl (S.fr d Λ i)).2 (Submodule.subset_span ⟨i, i.2, rfl⟩)
          exact ⟨this.1, Submodule.mem_sup_left this.2⟩
        · have := (h2 (r + 1) le_rfl (S.fr' d Λ i)).2 (Submodule.subset_span ⟨i, i.2, rfl⟩)
          exact ⟨this.1, Submodule.mem_sup_right this.2⟩)
  exact ⟨b, hb⟩

theorem tauRel_sum (d : S.Datum) (Λ : Submodule L.O S.V) (hΛ : S.IsTerm d Λ) {ι : Type}
    (s : Finset ι) (c : ι → L.O) (w y : ι → S.V) (h : ∀ i, S.TauRel d Λ (w i) (y i)) :
    S.TauRel d Λ (∑ i ∈ s, c i • w i) (∑ i ∈ s, c i • y i) := by
  obtain ⟨-, -, h3, h4, -⟩ := GlobalTheory.T.exists_gluing_homomorphism_defect_group L r k S d Λ hΛ
  induction s using Finset.induction_on with
  | empty => simpa using ((h4 0 (Submodule.zero_mem _)).1 (Submodule.zero_mem _)).2
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact h3 (c a) (c a).2 _ _ _ _ (h a) ih

theorem encard_kernels_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) C (Mh : Submodule L.O S.V) (j : ℕ), ((((fun Λ : Submodule L.O S.V => Λ ⊓ S.W0.restrictScalars L.O) '' {Λ | S.IsTerm d Λ ∧ S.Fr d Λ = C ∧ S.sat Λ = Mh ∧ S.cardI d Λ = j}).encard : ℕ∞) : ℝ≥0∞) ≤ (S.q : ℝ≥0∞) ^ (S.a.toNat * (2 * r + 2)) * (j : ℝ≥0∞) ^ (k - 1) := by
  intro F _ _ _ _ _ E _ _ _ L r k S d C Mh j
  rcases Set.eq_empty_or_nonempty
    {Λ | S.IsTerm d Λ ∧ S.Fr d Λ = C ∧ S.sat Λ = Mh ∧ S.cardI d Λ = j} with h0 | ⟨Λ₀, h₀, hC₀, hM₀, -⟩
  · rw [h0]; simp
  obtain ⟨-, -, -, -, -, b, -, hb⟩ := GlobalTheory.T.exists_gluing_homomorphism_defect_group L r k S d Λ₀ h₀
  obtain ⟨-, -, -, -, -, ⟨i₀, hi₀, hbe⟩, -⟩ := GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ₀ h₀
  have hq : 2 ≤ S.q := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.2.2.2.1
  let M₀ : Submodule L.O Mh := (S.M d Λ₀).comap Mh.subtype
  have hcard : Nat.card (Mh ⧸ M₀) = S.q ^ i₀ := by
    rw [← hbe, Frames.be, hM₀]
    rfl
  haveI : Finite (Mh ⧸ M₀) := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  obtain ⟨g, hg⟩ := sat_gens S d Λ₀ h₀
  rw [hM₀] at hg
  have hgm : ∀ i, g i ∈ Mh := fun i => by rw [hg]; exact Submodule.subset_span ⟨i, rfl⟩
  have hgen : Submodule.span L.O (Set.range fun i => M₀.mkQ ⟨g i, hgm i⟩) = ⊤ := by
    have h1 : Submodule.span L.O (Set.range fun i => (⟨g i, hgm i⟩ : Mh)) = ⊤ := by
      apply Submodule.map_injective_of_injective Mh.injective_subtype
      rw [Submodule.map_span, ← Set.range_comp, Submodule.map_subtype_top]
      exact hg.symm
    have h2 : (Set.range fun i => M₀.mkQ ⟨g i, hgm i⟩) =
        M₀.mkQ '' Set.range fun i => (⟨g i, hgm i⟩ : Mh) := by
      rw [← Set.range_comp]; rfl
    rw [h2, ← Submodule.map_span, h1, Submodule.map_top, Submodule.range_mkQ]
  have hsub := (GlobalTheory.SubmoduleCount.card_submodule_and_hom_le L (Mh ⧸ M₀) _ _ hgen).1
  have key := encard_le_of_param (R := L.O) (k - 1) j
    (fun x : Fin (k - 1) → Mh ⧸ M₀ =>
      (LinearMap.ker (Fintype.linearCombination L.O x)).map (Fintype.linearCombination L.O b))
    ((fun Λ : Submodule L.O S.V => Λ ⊓ S.W0.restrictScalars L.O) ''
      {Λ | S.IsTerm d Λ ∧ S.Fr d Λ = C ∧ S.sat Λ = Mh ∧ S.cardI d Λ = j}) (by
    rintro _ ⟨Λ, ⟨hΛ, hC, hM, hj⟩, rfl⟩
    obtain ⟨t1, t2, -, t4, t5, -⟩ := GlobalTheory.T.exists_gluing_homomorphism_defect_group L r k S d Λ hΛ
    rw [hM] at t1 t5
    have hMM : S.M d Λ = S.M d Λ₀ := by
      have hmem : (S.fr d Λ, S.fr' d Λ) ∈ S.frameCls (S.fr d Λ₀) (S.fr' d Λ₀) := by
        have := (GlobalTheory.HL.FrameClass.frame_classes L r k S (S.fr d Λ) (S.fr' d Λ)).1
        have h2 : S.frameCls (S.fr d Λ) (S.fr' d Λ) = S.frameCls (S.fr d Λ₀) (S.fr' d Λ₀) :=
          hC.trans hC₀.symm
        rwa [h2] at this
      exact ((GlobalTheory.HL.FrameClass.frame_classes L r k S _ _).2.1 _ hmem).2
    have hbL : ∀ i, b i ∈ S.complementLatticeOfDatum d := fun i => by
      rw [hb]; exact Submodule.subset_span ⟨i, rfl⟩
    choose y hy hty using fun i => t1 (b i) (hbL i)
    refine ⟨((S.Ihat d Λ).comap Mh.subtype).map M₀.mkQ, ?_, fun i => M₀.mkQ ⟨y i, hy i⟩, ?_, ?_⟩
    · rw [← hj, Frames.cardI, hMM,
        ← AddSubgroup.relIndex_addSubgroupOf (L := Mh.toAddSubgroup) t5]
      have hk : (S.M d Λ₀).toAddSubgroup.addSubgroupOf Mh.toAddSubgroup =
          M₀.mkQ.toAddMonoidHom.ker := by
        ext x
        exact (Submodule.Quotient.mk_eq_zero M₀).symm
      rw [hk, AddSubgroup.relIndex_ker]
      rfl
    · intro i
      exact ⟨⟨y i, hy i⟩, Submodule.mem_sup_right (Submodule.subset_span ⟨b i, hbL i, hty i⟩), rfl⟩
    · have hz : ∀ c : Fin (k - 1) → L.O,
          Fintype.linearCombination L.O (fun i => M₀.mkQ ⟨y i, hy i⟩) c = 0 ↔
            S.TauRel d Λ (∑ i, c i • b i) 0 := by
        intro c
        rw [t2 _ _ 0 (tauRel_sum S d Λ hΛ Finset.univ c b y hty), sub_zero, hMM,
          Fintype.linearCombination_apply]
        simp only [← map_smul, ← map_sum]
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        simp [M₀]
      ext w
      simp only [Submodule.mem_map, LinearMap.mem_ker, hz, Submodule.mem_inf,
        Submodule.restrictScalars_mem]
      constructor
      · rintro ⟨c, hc, rfl⟩
        have hL : ∑ i, c i • b i ∈ S.complementLatticeOfDatum d := by
          rw [hb]
          exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
        rw [Fintype.linearCombination_apply]
        exact ⟨(t4 _ hL.1).2 ⟨hL, hc⟩, hL.1⟩
      · rintro ⟨hw, hw0⟩
        obtain ⟨hL, ht⟩ := (t4 w hw0).1 hw
        rw [hb] at hL
        obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).1 hL
        exact ⟨c, ht, Fintype.linearCombination_apply _ _ _⟩)
  have hN : Nat.card (Submodule L.O (Mh ⧸ M₀)) * j ^ (k - 1) ≤
      S.q ^ (S.a.toNat * (2 * r + 2)) * j ^ (k - 1) := by
    refine Nat.mul_le_mul_right _ (hsub.trans ?_)
    rw [hcard, ← pow_mul]
    refine Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul (by omega) (by omega))
  have h3 := key.trans (Nat.cast_le.2 hN)
  have h4 := ENat.toENNReal_le.2 h3
  simpa using h4

end GlobalTheory.HL.GluingKernels
