import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SmallGenTwist.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (L : HermLine ι) (p q : ℕ),
    (∃ (n : ℕ) (w : Fin n → Ω), (∀ j, w j ∈ chartLat y L.a 1) ∧ KH.GeneratesOn y L.a w ∧
      ∀ j, IsSmallH (mCoordIdeal y) y L 1 (w j)) →
    ∃ (n : ℕ) (w : Fin n → Ω), (∀ j, w j ∈ chartLat y (HermLine.zcomb L (fsH ι) q p).a 1) ∧
      KH.GeneratesOn y (HermLine.zcomb L (fsH ι) q p).a w ∧
      ∀ j, IsSmallH (mCoordIdeal y) y (HermLine.zcomb L (fsH ι) q p) 1 (w j)

def SemiposTwist.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P0 P : Ideal (MRing ι)) (L : HermLine ι)
    (p q : ℕ), IsSemipositiveRel P0 P L → IsSemipositiveRel P0 P (HermLine.zcomb L (fsH ι) q p)

def GenDegTwist.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℤ) (n : ℕ) (w : Fin n → Ω) (p q : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → (∀ j, w j ∈ chartLat y a 1) → KH.GeneratesOn y a w →
    0 < genDeg (mCoordIdeal y) D a → 1 ≤ q →
    0 < genDeg (mCoordIdeal y) D ((q : ℤ) • a + fun _ => (p : ℤ))

def GenOnFibres.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ) (w : Fin n → Ω),
    (∀ j, w j ∈ chartLat y a 1) → KH.GeneratesOn y a w →
    KH.GeneratedV ℚ (KH.genIdeal y) a ∧ ∀ ℓ : ℕ, ℓ.Prime → KH.GeneratedV (ZMod ℓ) (fibreIdeal ℓ y) a

def AmpleOfGenTwist.Statement : Prop :=
  ∀ (S : Type) [Field S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (α : K → ℤ) (p q : ℕ),
    IsMultiHomogIdeal V → KH.GeneratedV S V α → 1 ≤ p →
    KH.AmpleV S V ((q : ℤ) • α + fun _ => (p : ℤ))

section Inhabitants

open ProjLine

theorem SmallGenTwist.hyps_inhabited :
    ∃ (n : ℕ) (w : Fin n → FnField), (∀ j, w j ∈ chartLat (ι := GlobalTheory (Fin 2)) y fsLine1.a 1) ∧
      KH.GeneratesOn (ι := GlobalTheory (Fin 2)) y fsLine1.a w ∧
      ∀ j, IsSmallH (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) y fsLine1 1 (w j) :=
  isSmallGeneratedDatum_fs.gen

theorem SemiposTwist.hyps_inhabited :
    IsSemipositiveRel (ι := GlobalTheory (Fin 2)) ⊥ (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) fsLine1 :=
  isSemipositiveRel_fs _ _

theorem GenDegTwist.hyps_inhabited :
    IsArithVar (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) (1 + 1) ∧
      (∀ j : Fin 2, y ⟨(), j⟩ ∈ chartLat (ι := GlobalTheory (Fin 2)) y fsLine1.a 1) ∧
      KH.GeneratesOn (ι := GlobalTheory (Fin 2)) y fsLine1.a (fun j : Fin 2 => y ⟨(), j⟩) ∧
      0 < genDeg (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) 1 fsLine1.a :=
  ⟨isArithVar_y', coord_mem_chartLat, generatesOn_coords, by rw [genDeg_fsLine1]; norm_num⟩

theorem GenOnFibres.hyps_inhabited :
    (∀ j : Fin 2, y ⟨(), j⟩ ∈ chartLat (ι := GlobalTheory (Fin 2)) y fsLine1.a 1) ∧
      KH.GeneratesOn (ι := GlobalTheory (Fin 2)) y fsLine1.a (fun j : Fin 2 => y ⟨(), j⟩) :=
  ⟨coord_mem_chartLat, generatesOn_coords⟩

theorem isMultiHomog_one_over (S : Type) [CommRing S] [Nontrivial S] (a : Unit → ℕ) (ha : ∀ k, a k = 0) :
    IsMultiHomog (1 : MRingOver S (GlobalTheory (Fin 2))) a := by
  intro m hm k
  rw [MvPolynomial.support_one] at hm
  simp [Finset.mem_singleton.mp hm, ha]

theorem one_mem_locPart (T : Submonoid (MRingOver ℚ (GlobalTheory (Fin 2)))) (c : Unit → ℤ) (hc : c = 0) :
    (1 : LocalizedModule T (MRingOver ℚ (GlobalTheory (Fin 2)) ⧸ (⊥ : Ideal (MRingOver ℚ (GlobalTheory (Fin 2)))))) ∈
      KH.locPart (GlobalTheory (Fin 2)) (KH.quotPart ℚ (⊥ : Ideal (MRingOver ℚ (GlobalTheory (Fin 2))))) T c := by
  subst hc
  refine Submodule.subset_span ⟨1, 1, 0, isMultiHomog_one_over ℚ _ fun _ => rfl, ?_, by
    rw [OreLocalization.one_def]; try rfl⟩
  refine Submodule.subset_span ⟨1, ⟨fun k => by simp, ?_⟩, map_one _⟩
  exact isMultiHomog_one_over ℚ _ fun _ => by simp

theorem AmpleOfGenTwist.hyps_inhabited :
    IsMultiHomogIdeal (⊥ : Ideal (MRingOver ℚ (GlobalTheory (Fin 2)))) ∧
      KH.GeneratedV ℚ (⊥ : Ideal (MRingOver ℚ (GlobalTheory (Fin 2)))) 0 := by
  refine ⟨⟨∅, by simp, by simp⟩, fun I => ⟨1, fun _ _ => 1, fun _ => 1, fun _ => ⟨?_, ?_⟩, fun _ => ?_, ?_⟩⟩
  · intro J _
    exact one_mem_locPart _ _ rfl
  · show _ ∈ (LinearMap.ker _).restrictScalars ℚ
    rw [Submodule.restrictScalars_mem, LinearMap.mem_ker]
    funext J
    obtain ⟨J, hJne, hJ⟩ := J
    have hJd : J default = Finset.univ := by
      apply Finset.eq_univ_of_card
      simp only [Finset.univ_unique, Finset.sum_singleton] at hJ
      simp only [Fintype.card_fin]
      omega
    have hres : ∀ i : Fin 2, KH.cellRes ℚ (MRingOver ℚ (GlobalTheory (Fin 2)) ⧸ (⊥ : Ideal (MRingOver ℚ (GlobalTheory (Fin 2)))))
        (Function.update J default ((J default).erase i)) J 1 = 1 := by
      intro i
      have hle : KH.cellMon ℚ (Function.update J default ((J default).erase i)) ≤ KH.cellMon ℚ J := by
        apply Submonoid.closure_mono
        rintro f ⟨k, j, hj, rfl⟩
        refine ⟨k, j, ?_, rfl⟩
        cases k
        simp only [Function.update_self] at hj
        exact Finset.mem_of_mem_erase hj
      unfold KH.cellRes
      rw [dif_pos hle]
      have h1 : (1 : LocalizedModule (KH.cellMon ℚ (Function.update J default ((J default).erase i)))
          (MRingOver ℚ (GlobalTheory (Fin 2)) ⧸ (⊥ : Ideal (MRingOver ℚ (GlobalTheory (Fin 2)))))) =
          LocalizedModule.mkLinearMap _ _ 1 := by
        rw [OreLocalization.one_def]; try rfl
      rw [h1, IsLocalizedModule.liftOfLE_apply]
      rw [OreLocalization.one_def]; try rfl
    have hcond : ∀ i : Fin 2, (∀ l, (Function.update J default ((J default).erase i) l).Nonempty) ∧
        ∑ l, ((Function.update J default ((J default).erase i) l).card - 1) = 0 := by
      intro i
      refine ⟨fun l => ?_, ?_⟩
      · obtain rfl : l = default := Subsingleton.elim _ _
        rw [Function.update_self, hJd]
        fin_cases i <;> decide
      · simp only [Finset.univ_unique, Finset.sum_singleton]
        rw [Function.update_self, hJd]
        fin_cases i <;> decide
    show (KH.cechD ℚ (GlobalTheory (Fin 2)) (MRingOver ℚ (GlobalTheory (Fin 2)) ⧸ (⊥ : Ideal (MRingOver ℚ (GlobalTheory (Fin 2))))) 0
      (fun _ => 1)) ⟨J, hJne, hJ⟩ = 0
    rw [KH.cechD]
    erw [LinearMap.pi_apply]
    simp only [LinearMap.sum_apply, Finset.univ_unique, Finset.sum_singleton]
    have hc' : ∀ i : Fin 2, (∀ l, (Function.update J default ((J default).erase i) l).Nonempty) ∧
        (Function.update J default ((J default).erase i) default).card - 1 = 0 := fun i =>
      ⟨(hcond i).1, by simpa using (hcond i).2⟩
    rw [Finset.sum_congr hJd (fun _ _ => rfl), Fin.sum_univ_two]
    erw [dif_pos (hc' 0), dif_pos (hc' 1)]
    have hs0 : KH.faceSign J default (0 : Fin 2) = 1 := by
      simp [KH.faceSign, hJd]
    have hs1 : KH.faceSign J default (1 : Fin 2) = -1 := by
      simp [KH.faceSign, hJd]
      decide
    erw [hs0, hs1, one_smul ℤ, neg_smul, one_smul ℤ]
    change (KH.cellRes ℚ (MRingOver ℚ (GlobalTheory (Fin 2)) ⧸ (⊥ : Ideal (MRingOver ℚ (GlobalTheory (Fin 2)))))
        (Function.update J default ((J default).erase 0)) J) 1 +
      -((KH.cellRes ℚ (MRingOver ℚ (GlobalTheory (Fin 2)) ⧸ (⊥ : Ideal (MRingOver ℚ (GlobalTheory (Fin 2)))))
        (Function.update J default ((J default).erase 1)) J) 1) = 0
    rw [hres 0, hres 1, add_neg_cancel]
  · exact one_mem_locPart _ _ (by simp)
  · simp

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
