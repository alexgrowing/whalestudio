import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRedMap
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StepVec

variable {D : D7}

def redLevGrp {κ : Type} [CommRing κ] {a : ℕ} (r t : ℕ) (hr : r ≤ a) (H : Subgroup (GL (Fin r) κ)) :
    Subgroup (GL (Fin a) κ) where
  carrier := {kb | kb ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) ∧ Formalism.L2.DIV.upperLeftBlock hr kb ∈ H}
  one_mem' := by
    refine ⟨Subgroup.one_mem _, ?_⟩
    show Formalism.L2.DIV.ext1 _ _ 1 ∈ H
    rw [Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one]; exact H.one_mem
  mul_mem' := by
    rintro x y ⟨hx, hxH⟩ ⟨hy, hyH⟩
    refine ⟨Subgroup.mul_mem _ hx hy, ?_⟩
    have e : Formalism.L2.DIV.upperLeftBlock hr (x * y) = Formalism.L2.DIV.upperLeftBlock hr x * Formalism.L2.DIV.upperLeftBlock hr y :=
      Formalism.L2.DIV.extendMatrixByIdentityAlongIndices_mul _ (Formalism.L2.DIV.blockTri_blkOf_le r t hx) (Formalism.L2.DIV.blockTri_blkOf_le r t hy)
    rw [e]; exact H.mul_mem hxH hyH
  inv_mem' := by
    rintro x ⟨hx, hxH⟩
    refine ⟨Subgroup.inv_mem _ hx, ?_⟩
    have e : Formalism.L2.DIV.upperLeftBlock hr x⁻¹ = (Formalism.L2.DIV.upperLeftBlock hr x)⁻¹ :=
      Formalism.L2.DIV.extendOne_inv _ (Formalism.L2.DIV.blockTri_blkOf_le r t hx)
    rw [e]; exact H.inv_mem hxH

def redLevChar {κ : Type} [CommRing κ] {a : ℕ} (r t s : ℕ) (hr : r ≤ a) (H : Subgroup (GL (Fin r) κ)) (c : H →* ℂˣ)
    (cg : ℕ → κˣ →* ℂˣ) : redLevGrp r t hr H →* ℂˣ where
  toFun kb := Formalism.L2.DIV.ext1 H c (Formalism.L2.DIV.upperLeftBlock hr kb.1) *
    ∏ i ∈ Finset.range s, cg (i + 1) (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) (i + 1) kb.1)
  map_one' := by
    simp only [OneMemClass.coe_one]
    have h1 : Formalism.L2.DIV.upperLeftBlock hr (1 : GL (Fin a) κ) = 1 := Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
    have h2 : ∀ c', Formalism.L2.DIV.dBlk (κ := κ) (n := a) (Formalism.L2.DIV.blkOf r t) c' 1 = 1 := fun _ =>
      Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
    rw [h1, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one]
    simp [h2]
  map_mul' := by
    rintro ⟨x, hx, hxH⟩ ⟨y, hy, hyH⟩
    show Formalism.L2.DIV.ext1 H c (Formalism.L2.DIV.upperLeftBlock hr (x * y)) *
        ∏ i ∈ Finset.range s, cg (i + 1) (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) (i + 1) (x * y)) = _
    have e : Formalism.L2.DIV.upperLeftBlock hr (x * y) = Formalism.L2.DIV.upperLeftBlock hr x * Formalism.L2.DIV.upperLeftBlock hr y :=
      Formalism.L2.DIV.extendMatrixByIdentityAlongIndices_mul _ (Formalism.L2.DIV.blockTri_blkOf_le r t hx) (Formalism.L2.DIV.blockTri_blkOf_le r t hy)
    rw [e, Formalism.L2.DIV.extendMatrixByIdentityAlongIndices_mul c hxH hyH]
    have e2 : ∀ i ∈ Finset.range s, cg (i + 1) (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) (i + 1) (x * y)) =
        cg (i + 1) (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) (i + 1) x) *
          cg (i + 1) (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) (i + 1) y) := fun i _ => by
      rw [Formalism.L2.DIV.diag_block_det_mul hx hy, map_mul]
    rw [Finset.prod_congr rfl e2, Finset.prod_mul_distrib, mul_mul_mul_comm]

theorem exists_isLocLevel : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E)
    (r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP), IsRedMap φ PP r →
    ∀ (a : ℕ) (L : Formalism.L2.DIV.LevDat D.host.E ℂ a) (H : Subgroup (GL (Fin L.r) (Formalism.L2.DIV.kP PP))) (c : H →* ℂˣ),
    ∃ (J : Subgroup (GL (Fin a) (v.adicCompletionIntegers D.host.F))) (lam : J →* ℂˣ), IsLocLevel φ PP L H c J lam := by
  intro D v φ PP r hred a L H c
  let f := Matrix.GeneralLinearGroup.map (n := Fin a) r
  refine ⟨(redLevGrp L.r L.t L.hr H).comap f,
    (redLevChar L.r L.t L.s L.hr H c (fun i => L.cg i PP)).comp
      ((f.subgroupComap (redLevGrp L.r L.t L.hr H))), ?_⟩
  intro k kb hk
  have hkb : kb = f k := by
    ext i j
    obtain ⟨h, e⟩ := (hred.2.2.1 _ _).1 (hk i j)
    rw [← e]
    rfl
  subst hkb
  exact ⟨Iff.rfl, fun _ => rfl⟩

end GlobalTheory.StepVec
