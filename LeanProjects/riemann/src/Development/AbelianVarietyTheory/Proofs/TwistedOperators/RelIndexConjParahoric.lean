import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexMulMatrixVolumeOpenSubgroupIntegralGLStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockVolumeProdStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixEntrywiseProductMeasureUniformizerPowerBoxStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValTwoBlockParahoricInfTorusConjBlockwiseStatement

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition

namespace GlobalTheory.ParahoricConjugateOpen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isOpen_conj_inf {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G)
    (hH : IsOpen (H : Set G)) (g : G) :
    IsOpen ((H.map (MulAut.conj g).toMonoidHom ⊓ H : Subgroup G) : Set G) := by
  rw [Subgroup.coe_inf]
  refine IsOpen.inter ?_ hH
  have : ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) = (fun x => g⁻¹ * x * g) ⁻¹' (H : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
    · intro hx
      exact ⟨_, hx, by simp [mul_assoc]⟩
  rw [this]
  exact hH.preimage (by fun_prop)

theorem isOpen_KO (n : Type) [Fintype n] [DecidableEq n] : IsOpen (KO k n : Set (GL n k)) :=
  Subgroup.isOpen_mono StepData.KOne_le_KO StepData.isOpen_KOne

theorem isOpen_parahoric (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] :
    IsOpen (parahoric k A D : Set (GL (A ⊕ D) k)) := by
  refine Subgroup.isOpen_mono (H₁ := KOne k (A ⊕ D)) (fun g hg => ?_) StepData.isOpen_KOne
  refine mem_parahoric.2 ⟨StepData.KOne_le_KO hg, fun i j => ?_⟩
  simpa using StepData.mem_KOne.1 hg (.inr i) (.inl j)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem torusElt_zero (n : Type) [Fintype n] [DecidableEq n] (ϖ : kˣ) :
    torusElt k n ϖ (fun _ => 0) = 1 := by
  refine Units.ext ?_
  rw [val_torusElt]
  simp

theorem conj_one_inf {G : Type} [Group G] (H : Subgroup G) :
    (H.map (MulAut.conj (1 : G)).toMonoidHom ⊓ H : Subgroup G) = H := by
  have : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by ext x; simp
  rw [this, Subgroup.map_id, inf_idem]

theorem vol_conj_inf [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ϖ : kˣ)
    (hϖ : valuation k (ϖ : k) = uniformizer k)
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (e : D → ℤ) :
    (volM ν (A ⊕ D) (A ⊕ D) (Units.val ''
      (((parahoric k A D).map (MulAut.conj (mtor (A := A) ϖ e)).toMonoidHom ⊓ parahoric k A D :
        Subgroup (GL (A ⊕ D) k)) : Set (GL (A ⊕ D) k)))).toReal =
      (volM ν A A (Units.val '' (KO k A : Set (GL A k)))).toReal *
        (ν (𝒪[k] : Set k)).toReal ^ (2 * (Fintype.card A * Fintype.card D)) *
        (resCard k : ℝ) ^ (-((Fintype.card A : ℤ) * (Fintype.card D + sumAbs e))) *
        (volM ν D D (Units.val '' (((KO k D).map (MulAut.conj (torusElt k D ϖ e)).toMonoidHom ⊓ KO k D :
          Subgroup (GL D k)) : Set (GL D k)))).toReal := by
  have hq : (0 : ℝ) < resCard k := Nat.cast_pos.2 Nat.card_pos
  have h1 := GlobalTheory.T.matrixEntrywiseProductMeasure_uniformizer_power_box k ν ϖ hϖ A D (fun _ j => max 0 (-e j))
  have h2 := GlobalTheory.T.matrixEntrywiseProductMeasure_uniformizer_power_box k ν ϖ hϖ D A (fun i _ => 1 + max 0 (e i))
  rw [GlobalTheory.T.val_twoBlockParahoric_inf_torusConj_blockwise k ϖ hϖ A D e, GlobalTheory.T.volM_blocks_eq_mul, h1, h2]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (zpow_pos hq _).le]
  have hs : -((Fintype.card A : ℤ) * (Fintype.card D + sumAbs e)) =
      (-∑ _i : A, ∑ j : D, max 0 (-e j)) + (-∑ i : D, ∑ _j : A, (1 + max 0 (e i))) := by
    have : sumAbs e = ∑ j : D, max 0 (-e j) + ∑ j : D, max 0 (e j) := by
      rw [sumAbs, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rcases le_total 0 (e j) with h | h
      · rw [abs_of_nonneg h, max_eq_left (by omega), max_eq_right h]; ring
      · rw [abs_of_nonpos h, max_eq_right (by omega), max_eq_left h]; ring
    rw [this, Finset.sum_comm (s := (Finset.univ : Finset D))]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_add_distrib]
    ring
  rw [hs, zpow_add₀ hq.ne', mul_comm (Fintype.card D) (Fintype.card A)]
  ring

theorem relIndex_conj_parahoric (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k)
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (e : D → ℤ) :
    ((((parahoric k A D).map (MulAut.conj (mtor (A := A) ϖ e)).toMonoidHom).relIndex (parahoric k A D) : ℕ) : ℝ) =
      (resCard k : ℝ) ^ ((Fintype.card A : ℤ) * sumAbs e) *
        ((((KO k D).map (MulAut.conj (torusElt k D ϖ e)).toMonoidHom).relIndex (KO k D) : ℕ) : ℝ) := by
  borelize k
  let ν : Measure k := Measure.addHaar
  have hq : (0 : ℝ) < resCard k := Nat.cast_pos.2 Nat.card_pos
  obtain ⟨hp, hJ⟩ := GlobalTheory.T.relIndex_mul_matrixVolume_open_subgroup_integralGL k ν (A ⊕ D) _ (parahoric k A D) inf_le_right
    (fun g hg => (mem_parahoric.1 hg).1) (isOpen_conj_inf _ (isOpen_parahoric A D) (mtor (A := A) ϖ e))
  obtain ⟨-, hK⟩ := GlobalTheory.T.relIndex_mul_matrixVolume_open_subgroup_integralGL k ν D _ (KO k D) inf_le_right le_rfl
    (isOpen_conj_inf _ (isOpen_KO D) (torusElt k D ϖ e))
  rw [Subgroup.inf_relIndex_right] at hJ hK
  have h0 := vol_conj_inf ν ϖ hϖ A D (fun _ => 0)
  have hm : mtor (A := A) ϖ (fun _ : D => 0) = 1 := by
    rw [← torusElt_zero (A ⊕ D) ϖ, mtor]
    congr 1
    funext x
    cases x <;> rfl
  rw [hm, torusElt_zero, conj_one_inf, conj_one_inf] at h0
  refine mul_right_cancel₀ hp.ne' ?_
  rw [hJ, h0, ← hK, vol_conj_inf ν ϖ hϖ A D e]
  have hs : sumAbs (fun _ : D => (0 : ℤ)) = 0 := by simp [sumAbs]
  have hz : (resCard k : ℝ) ^ (-((Fintype.card A : ℤ) * (Fintype.card D + sumAbs (fun _ : D => (0 : ℤ))))) =
      (resCard k : ℝ) ^ ((Fintype.card A : ℤ) * sumAbs e) *
        (resCard k : ℝ) ^ (-((Fintype.card A : ℤ) * (Fintype.card D + sumAbs e))) := by
    rw [← zpow_add₀ hq.ne', hs]
    congr 1
    ring
  rw [hz]
  ring

end GlobalTheory.ParahoricConjugateOpen
