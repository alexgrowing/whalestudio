import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePlacesLocalDatumBlockTriangularLaw

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.LevelMove

section Mat

variable {κ : Type} [CommRing κ] {a b r t j : ℕ}

def IsTopB (r t : ℕ) (y : Matrix (Fin b) (Fin a) κ) (g : GL (Fin a) κ) : Prop :=
  LowZero a y ∧ g.val = topL a y ∧ g ∈ blockTri (blkOf r t)

theorem IsTopB.move (hab : a ≤ b) (ea : a = r + j * t) (eb : b = r + (j + 1) * t)
    {y : Matrix (Fin b) (Fin a) κ} {g : GL (Fin a) κ} {H : GL (Fin b) κ} (h : IsTopB r t y g)
    (hT : H ∈ blockTri (blkOf r t)) :
    IsTopB r t ((H⁻¹).val * y) ((upperLeftBlock hab H)⁻¹ * g) := by
  obtain ⟨h1, h2, h3⟩ := h
  have t2 := GlobalTheory.StepLaw.TypeDatum.mem_twoBlockTriangular_of_blockTriangular ea eb hT
  have tm := GlobalTheory.StepLaw.TypeDatum.top_mem hab t2 hT
  have hinv : upperLeftBlock hab H⁻¹ = (upperLeftBlock hab H)⁻¹ := extendOne_inv _ t2
  have e1 := GlobalTheory.StepLaw.TypeDatum.topL_mul hab (Subgroup.inv_mem _ t2) h1 1
  have e2 := GlobalTheory.StepLaw.TypeDatum.lowZero_mul (Subgroup.inv_mem _ t2) h1 1
  rw [Matrix.mul_one] at e1 e2
  rw [Matrix.mul_one] at e1
  refine ⟨e2, ?_, Subgroup.mul_mem _ (Subgroup.inv_mem _ tm) h3⟩
  rw [e1, hinv, ← h2, Units.val_mul]

theorem restrictBlock_inv_mul_block_triangular_move (hab : a ≤ b) (ha : r ≤ a) (hb : r ≤ b) (ea : a = r + j * t) (eb : b = r + (j + 1) * t)
    {g : GL (Fin a) κ} {H : GL (Fin b) κ} (hg : g ∈ blockTri (blkOf r t)) (hT : H ∈ blockTri (blkOf r t)) :
    upperLeftBlock ha ((upperLeftBlock hab H)⁻¹ * g) = (upperLeftBlock hb H)⁻¹ * upperLeftBlock ha g := by
  have t2 := GlobalTheory.StepLaw.TypeDatum.mem_twoBlockTriangular_of_blockTriangular ea eb hT
  have tm := GlobalTheory.StepLaw.TypeDatum.top_mem hab t2 hT
  have le := blockTri_blkOf_le (κ := κ) (n := a) r t
  have m2 : upperLeftBlock ha ((upperLeftBlock hab H)⁻¹ * g) = upperLeftBlock ha (upperLeftBlock hab H)⁻¹ * upperLeftBlock ha g :=
    extendMatrixByIdentityAlongIndices_mul _ (le (Subgroup.inv_mem _ tm)) (le hg)
  have m3 : upperLeftBlock ha (upperLeftBlock hab H)⁻¹ = (upperLeftBlock ha (upperLeftBlock hab H))⁻¹ := extendOne_inv _ (le tm)
  rw [m2, m3, GlobalTheory.StepLaw.TypeDatum.restrictTopBlock_restrictTopBlock hab ha hb t2 hT]

theorem char_move (hab : a ≤ b) (ea : a = r + j * t) (eb : b = r + (j + 1) * t) {A : Type} [CommGroup A]
    (χ : ℕ → κˣ →* A) {g : GL (Fin a) κ} {H : GL (Fin b) κ} (hg : g ∈ blockTri (blkOf r t))
    (hT : H ∈ blockTri (blkOf r t)) :
    (∏ c ∈ Finset.range j, χ (c + 1) (dBlk (blkOf r t) (c + 1) ((upperLeftBlock hab H)⁻¹ * g))) *
        (χ (j + 1) (Matrix.GeneralLinearGroup.det ((upperLeftBlock hab H)⁻¹ * g)))⁻¹ =
      (∏ c ∈ Finset.range (j + 1), χ (c + 1) (dBlk (blkOf r t) (c + 1) H))⁻¹ *
        χ (j + 1) (Matrix.GeneralLinearGroup.det H) *
        ((∏ c ∈ Finset.range j, χ (c + 1) (dBlk (blkOf r t) (c + 1) g)) *
          (χ (j + 1) (Matrix.GeneralLinearGroup.det g))⁻¹) := by
  have h := GlobalTheory.StepLaw.TypeDatum.char_law hab ea eb χ hg (Subgroup.one_mem _) hT
  have d1 : ∀ c, dBlk (blkOf r t) c (1 : GL (Fin a) κ) = 1 := fun c => blockDiagonalExtendByOnePrimeField_one _ _
  simp only [mul_one, d1, map_one, Finset.prod_const_one, one_mul] at h
  rw [inv_mul_eq_iff_eq_mul] at h
  rw [h]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end Mat

section Dat

variable {D : D7} {a b r t k : ℕ} (ha : r ≤ a) (Pg : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ)
  (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ χj : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
  (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP))

theorem omegaG_of_top (g : ∀ PP : ↥Pg, GL (Fin a) (kP PP.1)) (hg : ∀ PP : ↥Pg, IsTopB r t (y PP.1) (g PP))
    (hm : (fun PP : ↥Pg => upperLeftBlock ha (g PP)) ∈ P.H) :
    omegaG (Lev.datY a r t k ha Pg ∅ P χ ξ Lev.Frm.B) χj y =
      ((P.chi ⟨_, hm⟩ * ∏ PP : ↥Pg, ((∏ c ∈ Finset.range k, χ (c + 1) PP.1 (dBlk (blkOf r t) (c + 1) (g PP))) *
        (χj PP.1 (Matrix.GeneralLinearGroup.det (g PP)))⁻¹) : ℂˣ) : ℂ) := by
  unfold omegaG
  split_ifs with h
  · have e : h.2.choose = g := funext fun PP =>
      Units.ext ((h.2.choose_spec.1 PP).trans (hg PP).2.1.symm)
    have e2 : (Lev.datY a r t k ha Pg ∅ P χ ξ Lev.Frm.B).P.chi
        ⟨fun PP => upperLeftBlock (Lev.datY a r t k ha Pg ∅ P χ ξ Lev.Frm.B).hr (h.2.choose PP), h.2.choose_spec.2.2⟩ =
        P.chi ⟨_, hm⟩ := by
      show P.chi _ = P.chi _
      congr 1
      exact Subtype.ext (funext fun PP => congrArg (fun x => upperLeftBlock ha x) (congrFun e PP))
    rw [e2]
    simp only [e, Finset.prod_mul_distrib, Units.val_mul, Units.coe_prod, Units.val_inv_eq_inv_val, mul_assoc]
    rfl
  · exfalso
    exact h ⟨fun PP hP => (hg ⟨PP, hP⟩).1, g, fun PP => (hg PP).2.1, fun PP => (hg PP).2.2, hm⟩

theorem omegaG_of_notTop (hg : ¬ ∃ g : ∀ PP : ↥Pg, GL (Fin a) (kP PP.1), (∀ PP : ↥Pg, IsTopB r t (y PP.1) (g PP)) ∧
      (fun PP : ↥Pg => upperLeftBlock ha (g PP)) ∈ P.H) :
    omegaG (Lev.datY a r t k ha Pg ∅ P χ ξ Lev.Frm.B) χj y = 0 := by
  unfold omegaG
  split_ifs with h
  · exfalso
    obtain ⟨h1, g, g1, g2, g3⟩ := h
    exact hg ⟨g, fun PP => ⟨h1 PP.1 PP.2, g1 PP, g2 PP⟩, g3⟩
  · rfl

end Dat

end GlobalTheory.ChainOnto.LevelMove

namespace GlobalTheory.ChainOnto

open LevelMove

theorem omegaG_levelP_move : ∀ (D : D7) (a b r t k : ℕ) (ha : r ≤ a) (hb : r ≤ b), a = r + k * t → b = r + (k + 1) * t → ∀ (Pg : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (H : ∀ PP : Pl D.host.E, GL (Fin b) (kP PP)), (∀ PP ∈ Pg, H PP ∈ blockTri (blkOf r t)) → ∀ hP : (fun PP : ↥Pg => upperLeftBlock hb (H PP.1)) ∈ P.H, ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP), omegaG (Lev.datY a r t k ha Pg ∅ P χ ξ Lev.Frm.B) (χ (k + 1)) (fun PP => ((H PP)⁻¹).val * y PP) = (((P.chi ⟨_, hP⟩ * ∏ PP ∈ Pg, ∏ i ∈ Finset.range (k + 1), χ (i + 1) PP (dBlk (blkOf r t) (i + 1) (H PP)))⁻¹ * ∏ PP ∈ Pg, χ (k + 1) PP (Matrix.GeneralLinearGroup.det (H PP)) : ℂˣ) : ℂ) * omegaG (Lev.datY a r t k ha Pg ∅ P χ ξ Lev.Frm.B) (χ (k + 1)) y := by
  intro D a b r t k ha hb ea eb Pg P χ ξ H hH hP y
  have hab : a ≤ b := by rw [ea, eb, add_mul]; omega
  by_cases h : ∃ g : ∀ PP : ↥Pg, GL (Fin a) (kP PP.1), (∀ PP : ↥Pg, IsTopB r t (y PP.1) (g PP)) ∧
      (fun PP : ↥Pg => upperLeftBlock ha (g PP)) ∈ P.H
  · obtain ⟨g, hg, hm⟩ := h
    have hg' : ∀ PP : ↥Pg, IsTopB r t (((H PP.1)⁻¹).val * y PP.1) ((upperLeftBlock hab (H PP.1))⁻¹ * g PP) :=
      fun PP => (hg PP).move hab ea eb (hH _ PP.2)
    have hr : (fun PP : ↥Pg => upperLeftBlock ha ((upperLeftBlock hab (H PP.1))⁻¹ * g PP)) =
        (fun PP : ↥Pg => upperLeftBlock hb (H PP.1))⁻¹ * (fun PP : ↥Pg => upperLeftBlock ha (g PP)) :=
      funext fun PP => restrictBlock_inv_mul_block_triangular_move hab ha hb ea eb (hg PP).2.2 (hH _ PP.2)
    have hm' : (fun PP : ↥Pg => upperLeftBlock ha ((upperLeftBlock hab (H PP.1))⁻¹ * g PP)) ∈ P.H := by
      rw [hr]; exact P.H.mul_mem (P.H.inv_mem hP) hm
    have hc : P.chi ⟨_, hm'⟩ = (P.chi ⟨_, hP⟩)⁻¹ * P.chi ⟨_, hm⟩ := by
      rw [← map_inv, ← map_mul]; congr 1; exact Subtype.ext hr
    have hx : ∀ PP : ↥Pg, (∏ c ∈ Finset.range k, χ (c + 1) PP.1 (dBlk (blkOf r t) (c + 1) ((upperLeftBlock hab (H PP.1))⁻¹ * g PP))) *
        (χ (k + 1) PP.1 (Matrix.GeneralLinearGroup.det ((upperLeftBlock hab (H PP.1))⁻¹ * g PP)))⁻¹ =
        (∏ c ∈ Finset.range (k + 1), χ (c + 1) PP.1 (dBlk (blkOf r t) (c + 1) (H PP.1)))⁻¹ *
          χ (k + 1) PP.1 (Matrix.GeneralLinearGroup.det (H PP.1)) *
          ((∏ c ∈ Finset.range k, χ (c + 1) PP.1 (dBlk (blkOf r t) (c + 1) (g PP))) *
            (χ (k + 1) PP.1 (Matrix.GeneralLinearGroup.det (g PP)))⁻¹) :=
      fun PP => char_move hab ea eb (fun c => χ c PP.1) (hg PP).2.2 (hH _ PP.2)
    rw [omegaG_of_top ha Pg P χ ξ _ (fun PP => ((H PP)⁻¹).val * y PP) _ hg' hm', omegaG_of_top ha Pg P χ ξ _ y g hg hm,
      hc, ← Units.val_mul]
    congr 1
    rw [Finset.prod_congr rfl fun PP _ => hx PP, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_inv_distrib,
      ← Finset.prod_coe_sort Pg (fun PP => χ (k + 1) PP (Matrix.GeneralLinearGroup.det (H PP))),
      ← Finset.prod_coe_sort Pg (fun PP => ∏ i ∈ Finset.range (k + 1), χ (i + 1) PP (dBlk (blkOf r t) (i + 1) (H PP)))]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have h' : ¬ ∃ g : ∀ PP : ↥Pg, GL (Fin a) (kP PP.1),
        (∀ PP : ↥Pg, IsTopB r t ((fun PP => ((H PP)⁻¹).val * y PP) PP.1) (g PP)) ∧ (fun PP : ↥Pg => upperLeftBlock ha (g PP)) ∈ P.H := by
      rintro ⟨g, hg, hm⟩
      refine h ⟨fun PP => (upperLeftBlock hab (H PP.1)⁻¹)⁻¹ * g PP, fun PP => ?_, ?_⟩
      · have e : y PP.1 = ((H PP.1)⁻¹⁻¹).val * (((H PP.1)⁻¹).val * y PP.1) := by
          rw [← Matrix.mul_assoc, ← Units.val_mul, inv_inv, mul_inv_cancel, Units.val_one, Matrix.one_mul]
        rw [e]
        exact (hg PP).move hab ea eb (Subgroup.inv_mem _ (hH _ PP.2))
      · have hr : (fun PP : ↥Pg => upperLeftBlock ha ((upperLeftBlock hab (H PP.1)⁻¹)⁻¹ * g PP)) =
            (fun PP : ↥Pg => upperLeftBlock hb (H PP.1)⁻¹)⁻¹ * (fun PP : ↥Pg => upperLeftBlock ha (g PP)) :=
          funext fun PP => restrictBlock_inv_mul_block_triangular_move hab ha hb ea eb (hg PP).2.2 (Subgroup.inv_mem _ (hH _ PP.2))
        have i2 : (fun PP : ↥Pg => upperLeftBlock hb (H PP.1)⁻¹) = (fun PP : ↥Pg => upperLeftBlock hb (H PP.1))⁻¹ :=
          funext fun PP => extendOne_inv _ (blockTri_blkOf_le r t (hH _ PP.2))
        rw [hr, i2, inv_inv]
        exact P.H.mul_mem hP hm
    rw [omegaG_of_notTop ha Pg P χ ξ _ y h, omegaG_of_notTop ha Pg P χ ξ _ _ h', mul_zero]

end GlobalTheory.ChainOnto

end
