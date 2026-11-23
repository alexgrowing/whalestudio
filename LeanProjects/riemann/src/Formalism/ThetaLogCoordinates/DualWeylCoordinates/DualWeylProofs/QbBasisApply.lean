import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QbIndepField

noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} [NeZero n]

lemma qb_card_Idx {M : GLMod n} (CF : ColFam M) : Fintype.card (qb_Idx CF) = Fintype.card M.ι := by
  rw [Fintype.card_sigma, CF.rank]
  refine sum_congr rfl fun j _ => ?_
  rw [dMu, Nat.card_eq_fintype_card]

def qb_e {M : GLMod n} (CF : ColFam M) : M.ι ≃ qb_Idx CF := Fintype.equivOfCardEq (qb_card_Idx CF).symm

def qb_N {M : GLMod n} (CF : ColFam M) : Matrix M.ι M.ι ℤ :=
  Matrix.of fun k i => CF.vec (qb_e CF k).1 (qb_e CF k).2.1 i

lemma qb_N_row {M : GLMod n} (CF : ColFam M) (R : Type) [CommRing R] :
    ((qb_N CF).map (Int.castRingHom R)).row = qb_vecF CF R ∘ qb_e CF := rfl

theorem qb_N_det (hA : LemmaA) {M : GLMod n} (CF : ColFam M) : IsUnit (qb_N CF).det := by
  rw [Int.isUnit_iff_natAbs_eq, Nat.eq_one_iff_not_exists_prime_dvd]
  intro p hp hdvd
  haveI := Fact.mk hp
  have h1 : LinearIndependent (ZMod p) ((qb_N CF).map (Int.castRingHom (ZMod p))).row := by
    rw [qb_N_row]; exact (linearIndependent_equiv (qb_e CF)).2 (qb_indep_field hA CF (ZMod p))
  rw [Matrix.linearIndependent_rows_iff_isUnit, Matrix.isUnit_iff_isUnit_det] at h1
  have h2 : ((qb_N CF).map (Int.castRingHom (ZMod p))).det = ((qb_N CF).det : ZMod p) := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
  rw [h2] at h1
  apply h1.ne_zero
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact Int.natCast_dvd.2 hdvd

theorem qb_N_unit (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (R : Type) [CommRing R] :
    IsUnit ((qb_N CF).map (Int.castRingHom R)) := by
  rw [Matrix.isUnit_iff_isUnit_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (qb_N_det hA CF).map _

theorem qb_basisR (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (R : Type) [CommRing R] :
    LinearIndependent R (qb_vecF CF R) ∧ Submodule.span R (Set.range (qb_vecF CF R)) = ⊤ := by
  have hu := qb_N_unit hA CF R
  constructor
  · have := Matrix.linearIndependent_rows_of_isUnit hu
    rw [qb_N_row] at this
    exact (linearIndependent_equiv (qb_e CF)).1 this
  · have h1 := Matrix.vecMul_surjective_iff_isUnit.2 hu
    have h2 := _root_.range_vecMulLinear ((qb_N CF).map (Int.castRingHom R))
    rw [qb_N_row, EquivLike.range_comp] at h2
    rw [← h2, LinearMap.range_eq_top]
    exact h1

def qb_basis (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (R : Type) [CommRing R] :
    Module.Basis (qb_Idx CF) R (M.ι → R) :=
  Module.Basis.mk (qb_basisR hA CF R).1 (qb_basisR hA CF R).2.ge

lemma qb_basis_apply (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (R : Type) [CommRing R] (x : qb_Idx CF) :
    qb_basis hA CF R x = qb_vecF CF R x := by
  rw [qb_basis, Module.Basis.mk_apply]

lemma qb_vecF_int {M : GLMod n} (CF : ColFam M) : qb_vecF CF ℤ = fun x => CF.vec x.1 x.2.1 := by
  funext x i
  simp [qb_vecF]

end Formalism.InvariantFactorPaths.ColumnFamilies
