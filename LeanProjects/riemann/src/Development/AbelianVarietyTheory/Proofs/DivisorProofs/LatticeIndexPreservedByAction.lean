import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFormCongrOfEventuallyEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelActionPreservesFlatForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapSymplecticTransform
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapRigidity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricTranslationPullbackFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatCoordsSymplecticPullbackForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcCompHolomorphic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteQuotientOfIsLatLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPeriodMapSimplyConnectedStatement
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe

noncomputable section

namespace GlobalTheory.RatLatIndex

open Module

variable {g : ℕ}

def rowEquiv (B : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ) (hB : IsUnit B.det) : Fl g ≃ₗ[ℝ] Fl g :=
  LinearEquiv.ofLinear (Matrix.vecMulLinear B) (Matrix.vecMulLinear B⁻¹)
    (LinearMap.ext fun x => by
      simp [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hB])
    (LinearMap.ext fun x => by
      simp [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hB])

def rowBasis (B : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ) (hB : IsUnit B.det) :
    Basis (Fin g ⊕ Fin g) ℝ (Fl g) :=
  (Pi.basisFun ℝ (Fin g ⊕ Fin g)).map (rowEquiv B hB)

theorem rowBasis_apply (B : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ) (hB : IsUnit B.det) (i) :
    rowBasis B hB i = B i := by
  ext j
  simp [rowBasis, rowEquiv, Matrix.vecMul, dotProduct, Pi.single_apply]

abbrev rowLat (B : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ) (hB : IsUnit B.det) :
    Submodule ℤ (Fl g) :=
  Submodule.span ℤ (Set.range (rowBasis B hB))

theorem isLat_rowLat (B : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ) (hB : IsUnit B.det) :
    IsLat (rowLat B hB) :=
  ⟨inferInstance, inferInstance⟩

theorem covolume_rowLat (B : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ) (hB : IsUnit B.det) :
    ZLattice.covolume (rowLat B hB) = |B.det| := by
  rw [ZLattice.covolume_eq_det _ ((rowBasis B hB).restrictScalars ℤ)]
  congr 2
  ext i j
  simp [Basis.restrictScalars_apply, rowBasis_apply]

theorem mem_stdLat_iff (x : Fl g) : x ∈ stdLat g ↔ ∀ i, ∃ k : ℤ, x i = k := by
  unfold stdLat
  rw [Basis.mem_span_iff_repr_mem ℤ (Pi.basisFun ℝ (Fin g ⊕ Fin g)) x]
  simp [eq_comm]

theorem stdLat_eq_rowLat_one : stdLat g = rowLat (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ)
    (by simp) := by
  unfold stdLat rowLat
  congr 2
  funext i
  rw [rowBasis_apply]
  ext j
  simp [Matrix.one_apply, Pi.single_apply, eq_comm]

theorem covolume_stdLat : ZLattice.covolume (stdLat g) = 1 := by
  have := covolume_rowLat (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ) (by simp)
  rw [← stdLat_eq_rowLat_one] at this
  simpa using this

scoped instance instDiscreteStdLat : DiscreteTopology (stdLat g) := by
  unfold stdLat; infer_instance

scoped instance instZLatticeStdLat : IsZLattice ℝ (stdLat g) := by
  unfold stdLat; infer_instance

theorem rowLat_le_stdLat (B : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ) (hB : IsUnit B.det)
    (hZ : ∀ i j, ∃ k : ℤ, B i j = k) : rowLat B hB ≤ stdLat g := by
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, mem_stdLat_iff, rowBasis_apply]
  exact hZ i

theorem card_quot_rowLat (B : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ) (hB : IsUnit B.det)
    (hZ : ∀ i j, ∃ k : ℤ, B i j = k) :
    (Nat.card (stdLat g ⧸ (rowLat B hB).submoduleOf (stdLat g)) : ℝ) = |B.det| := by
  have h := ZLattice.covolume_div_covolume_eq_relIndex (rowLat B hB) (stdLat g)
    (rowLat_le_stdLat B hB hZ)
  rw [covolume_stdLat, div_one, covolume_rowLat] at h
  rw [h]
  rfl

end GlobalTheory.RatLatIndex

namespace GlobalTheory.RatLatIndex
open Module

theorem ratSp_inv_map {g : ℕ} (γ : Sp g) (G : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℚ)
    (hG : γ.mat = G.map (Rat.castHom ℝ)) :
    (γ⁻¹).mat = (-(Matrix.J (Fin g) ℚ) * Gᵀ * Matrix.J (Fin g) ℚ).map (Rat.castHom ℝ) := by
  have h1 : (γ⁻¹).mat = -Matrix.J (Fin g) ℝ * (γ.mat)ᵀ * Matrix.J (Fin g) ℝ :=
    SymplecticGroup.coe_inv γ
  rw [h1, hG, Matrix.map_mul, Matrix.map_mul, Matrix.map_neg _ (fun a => map_neg _ a), Matrix.map_J,
    Matrix.transpose_map]

theorem int_of_den_dvd (q : ℚ) (N : ℕ) (h : q.den ∣ N) : ∃ k : ℤ, (N : ℝ) * (q : ℝ) = k := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c * q.num, ?_⟩
  have : (N : ℚ) * q = ((c * q.num : ℤ) : ℚ) := by
    rw [hc]; push_cast
    rw [← Rat.mul_den_eq_num]; ring
  have h2 := congrArg (fun t : ℚ => (t : ℝ)) this
  push_cast at h2 ⊢
  exact h2

end GlobalTheory.RatLatIndex

open GlobalTheory.RatLatIndex in

theorem GlobalTheory.ratSp_exists_sublat_same_index : ∀ (g : ℕ) (γ : GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.Sp g),
    (∀ i l, ∃ r : ℚ, γ.mat i l = r) → ∃ M : Submodule ℤ (Fl g), IsLat M ∧ M ≤ stdLat g ∧
      IsLat (latAct M γ) ∧ latAct M γ ≤ stdLat g ∧
      0 < Nat.card (stdLat g ⧸ M.submoduleOf (stdLat g)) ∧
      Nat.card (stdLat g ⧸ M.submoduleOf (stdLat g)) =
        Nat.card (stdLat g ⧸ (latAct M γ).submoduleOf (stdLat g)) := by
  intro g γ hrat
  choose G hG using hrat
  have hGm : γ.mat = (Matrix.of G).map (Rat.castHom ℝ) := by
    ext i l; simp [hG]
  set Aq := -(Matrix.J (Fin g) ℚ) * (Matrix.of G)ᵀ * Matrix.J (Fin g) ℚ with hAq
  have hA : (γ⁻¹).mat = Aq.map (Rat.castHom ℝ) := ratSp_inv_map γ _ hGm
  set N : ℕ := ∏ i, ∏ j, (Aq i j).den with hN
  have hN0 : N ≠ 0 := by
    rw [hN, Finset.prod_ne_zero_iff]
    intro i _
    rw [Finset.prod_ne_zero_iff]
    intro j _
    exact (Aq i j).den_nz
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN0
  have hAint : ∀ i j, ∃ k : ℤ, (N : ℝ) * (γ⁻¹).mat i j = k := by
    intro i j
    rw [hA, Matrix.map_apply, Rat.coe_castHom]
    apply int_of_den_dvd
    exact (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)).trans
      (Finset.dvd_prod_of_mem (fun i => ∏ j, (Aq i j).den) (Finset.mem_univ i))
  have hdetA : ((γ⁻¹).mat).det = 1 := SymplecticGroup.det_eq_one (γ⁻¹).2
  set B1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ := (N : ℝ) • (1 : Matrix _ _ ℝ) with hB1
  set B2 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ := (N : ℝ) • (γ⁻¹).mat with hB2
  have hd1 : B1.det = (N : ℝ) ^ Fintype.card (Fin g ⊕ Fin g) := by
    rw [hB1, Matrix.det_smul, Matrix.det_one, mul_one]
  have hd2 : B2.det = (N : ℝ) ^ Fintype.card (Fin g ⊕ Fin g) := by
    rw [hB2, Matrix.det_smul, hdetA, mul_one]
  have hu1 : IsUnit B1.det := by rw [hd1]; exact (pow_ne_zero _ hNR).isUnit
  have hu2 : IsUnit B2.det := by rw [hd2]; exact (pow_ne_zero _ hNR).isUnit
  have hZ1 : ∀ i j, ∃ k : ℤ, B1 i j = k := by
    intro i j
    by_cases h : i = j
    · exact ⟨N, by simp [hB1, h]⟩
    · exact ⟨0, by simp [hB1, h]⟩
  have hZ2 : ∀ i j, ∃ k : ℤ, B2 i j = k := by
    intro i j
    obtain ⟨k, hk⟩ := hAint i j
    exact ⟨k, by simp [hB2, hk]⟩
  have hlat : latAct (rowLat B1 hu1) γ = rowLat B2 hu2 := by
    unfold latAct rowLat
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    funext i
    simp only [Function.comp_apply, rowBasis_apply, LinearMap.coe_restrictScalars,
      Matrix.vecMulLinear_apply]
    ext j
    simp [hB1, hB2, Matrix.vecMul, dotProduct, Matrix.one_apply, ite_mul]
  refine ⟨rowLat B1 hu1, isLat_rowLat _ _, rowLat_le_stdLat _ _ hZ1, ?_, ?_, ?_, ?_⟩
  · rw [hlat]; exact isLat_rowLat _ _
  · rw [hlat]; exact rowLat_le_stdLat _ _ hZ2
  · have h := card_quot_rowLat B1 hu1 hZ1
    rw [hd1] at h
    have : (0 : ℝ) < (Nat.card (stdLat g ⧸ (rowLat B1 hu1).submoduleOf (stdLat g)) : ℝ) := by
      rw [h]; positivity
    exact_mod_cast this
  · apply Nat.cast_injective (R := ℝ)
    rw [hlat, card_quot_rowLat B1 hu1 hZ1, card_quot_rowLat B2 hu2 hZ2, hd1, hd2]
