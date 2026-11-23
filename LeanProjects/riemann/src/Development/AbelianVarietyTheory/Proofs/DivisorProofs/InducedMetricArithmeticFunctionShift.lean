import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastNeZeroG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModpFramesPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalCoordinatesExtendProjectiveSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonomialEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionUnitsGenericOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRefinementCovers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoverFunctionFieldEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverMorphismGenericPointSpecializesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangularModulusInverseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangularModulusProductsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmithNormalFormOfNonsingularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPidSubringPIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PIntegralRegularOnCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoverIntegralMatrixConjugationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalSectionWithNormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsCompareOfScaledLocalNormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorTrivialAwayFromBadPrimesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsPullbackAlongCoverMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalGeneratorsCohereNearPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransitionMatrixOfGeneratorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoherentOfCrossWithBoundedInverseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovesOfLinkedSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovesEquivalenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumMovesOverFinitePrimesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoverRegularisingFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinkedOfGeneratorMultiplicationStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

namespace GlobalTheory.LatChain

theorem diag_mul {K : Type} [Field K] {N : ℕ} {A B : Matrix (Fin N) (Fin N) K} (hA : A.BlockTriangular id)
    (hB : B.BlockTriangular id) (i : Fin N) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)]
  rcases lt_or_gt_of_ne hj with h | h
  · rw [hA h, zero_mul]
  · rw [hB h, mul_zero]

theorem exists_smith {K : Type} [Field K] [CharZero K] {p n N : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (P Q : Matrix (Fin N) (Fin N) K) (hPQ : P * Q = 1)
    (hI : ∀ i j, IsIntegral ℤ ((n : K) * P i j) ∧ IsIntegral ℤ ((n : K) * Q i j)) :
    ∃ (u v u' v' : Matrix (Fin N) (Fin N) K) (g : Fin N → K), u * v = 1 ∧ u' * v' = 1 ∧
      (n : K) • P = u * Matrix.diagonal g * u' ∧
      (∀ i j, PInt p (u i j) ∧ PInt p (v i j) ∧ PInt p (u' i j) ∧ PInt p (v' i j)) ∧
      ∀ j, g j ≠ 0 ∧ PInt p (g j) ∧ PInt p ((n : K) ^ 2 / g j) := by
  obtain ⟨R, hR, hs, hP⟩ := GlobalTheory.T.exists_pid_subring_p_integral K p hp
    (Finset.univ.image (fun t : Fin N × Fin N => (n : K) * P t.1 t.2) ∪
      Finset.univ.image (fun t : Fin N × Fin N => (n : K) * Q t.1 t.2)) (by
      intro f hf
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hf
      rcases hf with ⟨t, rfl⟩ | ⟨t, rfl⟩
      exacts [(hI _ _).1, (hI _ _).2])
  let A : Matrix (Fin N) (Fin N) R := fun i j => ⟨n * P i j, hs _ (Finset.mem_union_left _
    (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩))⟩
  let A' : Matrix (Fin N) (Fin N) R := fun i j => ⟨n * Q i j, hs _ (Finset.mem_union_right _
    (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩))⟩
  have eA : R.subtype.mapMatrix A = (n : K) • P := rfl
  have eA' : R.subtype.mapMatrix A' = (n : K) • Q := rfl
  have hn' : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hd : A.det ≠ 0 := fun h => by
    have h₁ := RingHom.map_det R.subtype A
    rw [h, map_zero, eA, Matrix.det_smul] at h₁
    exact mul_ne_zero (pow_ne_zero _ hn') (Matrix.isUnit_det_of_right_inverse hPQ).ne_zero h₁.symm
  obtain ⟨u, v, u', v', g, h₁, h₂, h₃⟩ := GlobalTheory.T.smith_normal_form_of_nonsingular R N A hd
  have e₃ : (n : K) • P = R.subtype.mapMatrix u * Matrix.diagonal (fun j => (g j : K)) * R.subtype.mapMatrix u' := by
    rw [← eA, h₃, map_mul, map_mul, RingHom.mapMatrix_apply _ (Matrix.diagonal g), Matrix.diagonal_map (map_zero _)]
    rfl
  have e₁ : R.subtype.mapMatrix u * R.subtype.mapMatrix v = 1 := by rw [← map_mul, h₁, map_one]
  have key (j) : (g j : K) * ((u' * A' * u) j j : R) = (n : K) ^ 2 := by
    have e : Matrix.diagonal (fun j => (g j : K)) * R.subtype.mapMatrix (u' * A' * u) = ((n : K) ^ 2) • 1 := by
      rw [map_mul, map_mul, eA', ← one_mul (Matrix.diagonal _), ← mul_eq_one_comm.1 e₁]
      calc _ = R.subtype.mapMatrix v * (R.subtype.mapMatrix u * Matrix.diagonal (fun j => (g j : K)) *
            R.subtype.mapMatrix u' * ((n : K) • Q)) * R.subtype.mapMatrix u := by simp only [mul_assoc]
        _ = _ := by
          rw [← e₃, smul_mul_smul_comm, hPQ, mul_smul_comm, smul_mul_assoc, mul_one, sq]
    have := congrFun (congrFun e j) j
    rw [Matrix.diagonal_mul] at this
    simpa using this
  refine ⟨_, _, _, R.subtype.mapMatrix v', _, e₁, by rw [← map_mul, h₂, map_one], e₃,
    fun i j => ⟨hP _ (u i j).2, hP _ (v i j).2, hP _ (u' i j).2, hP _ (v' i j).2⟩, fun j => ?_⟩
  have hg : (g j : K) ≠ 0 := left_ne_zero_of_mul (key j ▸ pow_ne_zero _ hn')
  refine ⟨hg, hP _ (g j).2, ?_⟩
  rw [← key j, mul_div_cancel_left₀ _ hg]
  exact hP _ (Subtype.prop _)

theorem unit_of_frames {K : Type} [Field K] {N : ℕ} {R : Subring K} {h b n : K}
    {M M' P u v u' B B' : Matrix (Fin N) (Fin N) K} {g d : Fin N → K} (hh : Small R h) (hn : n ∈ R) (hn₀ : n ≠ 0) (hb : b ∈ R)
    (huv : u * v = 1) (hP : n • P = u * Matrix.diagonal g * u') (hg : ∀ j, g j ≠ 0 ∧ b / g j ∈ R)
    (hB : B.BlockTriangular id) (hB' : B'.BlockTriangular id) (hM : Fr R (u' * M)) (hM' : Fr R (v * M'))
    (h₁ : Fr R (Matrix.diagonal g * (u' * M) * B)) (h₂ : Fr R (Matrix.diagonal (fun _ => n) * (v * M') * B'))
    (hT : TriMod R (h * b) (M'⁻¹ * P * M) d) (i : Fin N) :
    d i * B i i / B' i i ≠ 0 ∧ d i * B i i / B' i i ∈ R ∧ (d i * B i i / B' i i)⁻¹ ∈ R := by
  have hB'₀ : IsUnit B'.det := by
    have := h₂.1
    rw [Matrix.det_mul] at this
    exact (right_ne_zero_of_mul this).isUnit
  have hdn : Matrix.diagonal (fun _ : Fin N => n) = n • (1 : Matrix (Fin N) (Fin N) K) := by
    rw [Matrix.smul_one_eq_diagonal]
  have hdn₀ : IsUnit (Matrix.diagonal (fun _ : Fin N => n) * (v * M')).det := by
    have := h₂.1
    rw [Matrix.det_mul] at this
    exact (left_ne_zero_of_mul this).isUnit
  have hM'₀ : IsUnit M'.det := by
    have := hM'.1
    rw [Matrix.det_mul] at this
    exact (right_ne_zero_of_mul this).isUnit
  letI := B'.invertibleOfIsUnitDet hB'₀
  have hi : B'⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hB'
  have hii : B'⁻¹ i i = (B' i i)⁻¹ := by
    have := diag_mul hi hB' i
    rw [Matrix.nonsing_inv_mul _ hB'₀, Matrix.one_apply_eq] at this
    exact eq_inv_of_mul_eq_one_left this.symm
  have r₁ : B'⁻¹ ∈ R.matrix := by
    have e : B'⁻¹ = (Matrix.diagonal (fun _ => n) * (v * M') * B')⁻¹ * (Matrix.diagonal (fun _ => n) * (v * M')) := by
      rw [Matrix.mul_inv_rev, mul_assoc, Matrix.nonsing_inv_mul _ hdn₀, mul_one]
    rw [e, hdn]
    refine mul_mem (hdn ▸ h₂.2.2) (mul_mem (fun i j => R.mul_mem hn ((show ∀ i j, (1 : Matrix (Fin N) (Fin N) K) i j ∈ R from
      one_mem R.matrix) i j)) hM'.2.1)
  have r₂ : b • B ∈ R.matrix := by
    have e : b • B = (u' * M)⁻¹ * Matrix.diagonal (fun j => b / g j) * (Matrix.diagonal g * (u' * M) * B) := by
      rw [mul_assoc, ← mul_assoc (Matrix.diagonal _), ← mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal,
        funext fun j => div_mul_cancel₀ b (hg j).1, ← Matrix.smul_one_eq_diagonal, smul_mul_assoc, one_mul, smul_mul_assoc,
        mul_smul_comm, Matrix.nonsing_inv_mul_cancel_left _ _ hM.1.isUnit]
    rw [e]
    refine mul_mem (mul_mem hM.2.2 fun i j => ?_) h₁.2.1
    rw [Matrix.diagonal_apply]
    split_ifs
    exacts [(hg i).2, zero_mem R]
  have t := (GlobalTheory.T.triangular_modulus_products K N R h b _ 1 d d hh.1 hb).2 _ _ hi hB r₁ r₂ hT
  have e : B'⁻¹ * (M'⁻¹ * P * M) * B =
      (Matrix.diagonal (fun _ => n) * (v * M') * B')⁻¹ * (Matrix.diagonal g * (u' * M) * B) := by
    have hv : v⁻¹ = u := Matrix.inv_eq_left_inv huv
    have hni : (n • (1 : Matrix (Fin N) (Fin N) K))⁻¹ = n⁻¹ • 1 :=
      Matrix.inv_eq_left_inv (by rw [smul_mul_smul_comm, inv_mul_cancel₀ hn₀, one_smul, mul_one])
    have hP' : P = n⁻¹ • (u * Matrix.diagonal g * u') := by rw [← hP, smul_smul, inv_mul_cancel₀ hn₀, one_smul]
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_inv_rev, hdn, hni, hv, hP']
    simp only [mul_assoc, mul_smul_comm, smul_mul_assoc, one_mul]
  have f := h₂.inv.mul h₁
  rw [← e] at f
  obtain ⟨t₁, t₂⟩ := GlobalTheory.T.triangular_modulus_inverse K N R h 1 _ _ hh (one_mem R) f.1 (by rw [one_smul]; exact f.2.2)
    (by rwa [mul_one, mul_one])
  have mem {A : Matrix (Fin N) (Fin N) K} {d : Fin N → K} (hA : A ∈ R.matrix) (H : TriMod R h A d) : d i ∈ R := by
    obtain ⟨E, hE, -, H⟩ := H
    rw [← H]
    exact R.sub_mem (hA i i) (R.mul_mem hh.1 (hE i i))
  have e' : d i * B i i / B' i i = B'⁻¹ i i * d i * B i i := by rw [hii]; ring
  rw [e']
  exact ⟨t₁ i, mem f.2.1 t, mem f.2.2 t₂⟩

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem exists_step (V : Cover Y) {p k a N : ℕ} (hp : p.Prime) {M : V.X → Matrix (Fin N) (Fin N) V.X.functionField}
    {c : V.X → Fin N → V.X.functionFieldˣ} (j : Fin N) {γ : V.X.functionField} (hγ : γ ≠ 0)
    (hγ' : ∀ x, Ov p x → RegAt x γ ∧ RegAt x ((p : V.X.functionField) ^ a / γ)) (h : Coh p (k + 1 + a) M c) :
    ∃ (V' : Cover Y) (π : V'.X ⟶ V.X) (hπ : π (genericPoint V'.X) ⤳ genericPoint V.X)
      (B : V'.X → Matrix (Fin N) (Fin N) V'.X.functionField) (c' : V'.X → Fin N → V'.X.functionFieldˣ),
      Lies V' V π ∧ (∀ x, Ov p x → (B x).BlockTriangular id ∧ ∀ i, (c' x i : V'.X.functionField) * B x i i = pf π hπ c x i) ∧
      Coh p (k + 1) (fun x => dg j (SmallSec.fnMap π hπ γ) * pm π hπ M x * B x) c' ∧ Link p (pf π hπ c) c' := by
  obtain ⟨V', π, hπ, -, hl, hG⟩ := GlobalTheory.T.exists_cover_regularising_functions F Y V p hp (Fin (N + 1)) (Option (Fin N))
    (fun x i => gens γ (fun l => (M x)⁻¹ l j) i) fun x hx => ⟨fun i s => by
      rcases s with _ | l
      · exact (hγ' x hx).1
      · change RegAt x (if _ then _ else _)
        split_ifs
        exacts [(h x hx).1.2.2 l j, regAt_zero x], fun i => ⟨none, a, hγ, (hγ' x hx).2⟩,
      (GlobalTheory.T.local_generators_cohere_near_point V.X p k a N M c j γ hγ hγ' h x hx).mono fun z hz hz' => (hz hz').1⟩
  have e (x : V'.X) (i) : (fun s => SmallSec.fnMap π hπ (gens γ (fun l => (M (π x))⁻¹ l j) i s)) =
      gens (SmallSec.fnMap π hπ γ) (fun l => (pm π hπ M x)⁻¹ l j) i := by
    funext s
    rcases s with _ | l
    · rfl
    · simp only [gens, Option.elim, pm, FrameGlue.Pull.matrix_map_inv, Matrix.map_apply,
        apply_ite (SmallSec.fnMap π hπ), map_zero]
  have hη (x : V'.X) (i) : ∃ η : V'.X.functionFieldˣ, Ov p x →
      Gen (loc x) (gens (SmallSec.fnMap π hπ γ) (fun l => (pm π hπ M x)⁻¹ l j) i) η := by
    by_cases hx : Ov p x
    · obtain ⟨η, hη⟩ := hG x hx i
      exact ⟨Units.mk0 η hη.1, fun _ => e x i ▸ hη⟩
    · exact ⟨1, fun h => absurd h hx⟩
  choose η hη using hη
  have hγ₁ : SmallSec.fnMap π hπ γ ≠ 0 := (map_ne_zero _).2 hγ
  have hγ₂ (x : V'.X) (hx : Ov p x) : RegAt x (SmallSec.fnMap π hπ γ) ∧
      RegAt x ((p : V'.X.functionField) ^ a / SmallSec.fnMap π hπ γ) := by
    have H := map_mem_loc π hπ x _ (hγ' _ (hx.map π)).2
    rw [map_div₀, map_pow, map_natCast] at H
    exact ⟨map_mem_loc π hπ x _ (hγ' _ (hx.map π)).1, H⟩
  obtain ⟨B, hB, hC⟩ := GlobalTheory.T.exists_transition_matrix_of_generators V'.X p k a N _ _ j _ hγ₁ hγ₂ (h.pull π hπ) η fun x hx i => hη x i hx
  refine ⟨V', π, hπ, B, _, hl, fun x hx => ⟨(hB x hx).1, fun i => ?_⟩, hC,
    GlobalTheory.T.linked_of_generator_multiplication V'.X p k a N _ _ j _ hγ₁ hγ₂ (h.pull π hπ) η fun x hx i => hη x i hx⟩
  rw [(hB x hx).2]
  simp only [Units.val_div_eq_div_val, Units.val_mul]
  field_simp

theorem exists_chain (V : Cover Y) {p a N : ℕ} (hp : p.Prime) {M : V.X → Matrix (Fin N) (Fin N) V.X.functionField}
    {c : V.X → Fin N → V.X.functionFieldˣ} {g : Fin N → V.X.functionField} (hg : ∀ j, g j ≠ 0)
    (hg' : ∀ j x, Ov p x → RegAt x (g j) ∧ RegAt x ((p : V.X.functionField) ^ a / g j)) (T : Finset (Fin N)) (k : ℕ)
    (h : Coh p (k + 1 + T.card * a) M c) :
    ∃ (V' : Cover Y) (π : V'.X ⟶ V.X) (hπ : π (genericPoint V'.X) ⤳ genericPoint V.X)
      (B : V'.X → Matrix (Fin N) (Fin N) V'.X.functionField) (c' : V'.X → Fin N → V'.X.functionFieldˣ),
      Lies V' V π ∧ (∀ x, Ov p x → (B x).BlockTriangular id ∧ ∀ i, (c' x i : V'.X.functionField) * B x i i = pf π hπ c x i) ∧
      Coh p (k + 1) (fun x => Matrix.diagonal (fun j => if j ∈ T then SmallSec.fnMap π hπ (g j) else 1) * pm π hπ M x * B x) c' ∧
      Relation.EqvGen (Link p) (pf π hπ c) c' := by
  induction T using Finset.induction_on generalizing k with
  | empty =>
    refine ⟨V, 𝟙 _, specializes_rfl, fun _ => 1, _, lies_id V, fun x _ => ⟨Matrix.blockTriangular_one, fun i => ?_⟩, ?_,
      .refl _⟩
    · simp
    · simpa using h.pull (𝟙 V.X) specializes_rfl
  | insert j T hj ih =>
    obtain ⟨V₁, π₁, h₁, B₁, c₁, l₁, b₁, C₁, E₁⟩ := ih (k + a) (by
      rwa [Finset.card_insert_of_notMem hj, show k + 1 + (T.card + 1) * a = k + a + 1 + T.card * a by ring] at h)
    obtain ⟨V₂, π₂, h₂, B₂, c₂, l₂, b₂, C₂, E₂⟩ := exists_step V₁ (k := k) (a := a) hp j
      ((map_ne_zero (SmallSec.fnMap π₁ h₁)).2 (hg j)) (fun x hx => by
        have H := map_mem_loc π₁ h₁ x _ (hg' j _ (hx.map π₁)).2
        rw [map_div₀, map_pow, map_natCast] at H
        exact ⟨map_mem_loc π₁ h₁ x _ (hg' j _ (hx.map π₁)).1, H⟩) (by rwa [add_right_comm] at C₁)
    have h₃ := ProjSpace.comp_genericPoint_specializes π₂ π₁ h₂ h₁
    have t₁ (x) (hx : Ov p x) : (pm π₂ h₂ B₁ x).BlockTriangular id := fun i l hl => by
      rw [pm, Matrix.map_apply, (b₁ _ (hx.map π₂)).1 hl, map_zero]
    refine ⟨V₂, π₂ ≫ π₁, h₃, fun x => pm π₂ h₂ B₁ x * B₂ x, c₂, lies_comp l₂ l₁,
      fun x hx => ⟨(t₁ x hx).mul (b₂ x hx).1, fun i => ?_⟩, ?_, ?_⟩
    · beta_reduce
      rw [diag_mul (t₁ x hx) (b₂ x hx).1, mul_left_comm, (b₂ x hx).2, pf_comp π₂ π₁ h₂ h₁, val_pf π₂ h₂ (pf π₁ h₁ c),
        ← (b₁ _ (hx.map π₂)).2, map_mul, mul_comm]
      rfl
    · convert C₂ using 2 with x
      have e : Matrix.diagonal (fun l => if l ∈ insert j T then SmallSec.fnMap (π₂ ≫ π₁) h₃ (g l) else 1) =
          dg j (SmallSec.fnMap π₂ h₂ (SmallSec.fnMap π₁ h₁ (g j))) *
            (Matrix.diagonal fun l => if l ∈ T then SmallSec.fnMap π₁ h₁ (g l) else 1).map (SmallSec.fnMap π₂ h₂) := by
        rw [dg, Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul_diagonal]
        congr 1
        funext l
        rw [ProjSpace.fnMap_comp π₂ π₁ h₂ h₁]
        by_cases hl : l = j
        · subst hl
          simp [hj]
        · simp [hl, apply_ite (SmallSec.fnMap π₂ h₂)]
      rw [e, pm_comp π₂ π₁ h₂ h₁]
      simp only [pm, Matrix.map_mul, mul_assoc]
    · rw [pf_comp π₂ π₁ h₂ h₁]
      exact .trans _ _ _ (eqvGen_pull π₂ h₂ E₁) (.rel _ _ E₂)

theorem fr_of_mul {K : Type} [Field K] {N : ℕ} {R : Subring K} {u v : Matrix (Fin N) (Fin N) K} (h : u * v = 1)
    (hu : u ∈ R.matrix) (hv : v ∈ R.matrix) : Fr R u :=
  ⟨(Matrix.isUnit_det_of_right_inverse h).ne_zero, hu, by rwa [Matrix.inv_eq_right_inv h]⟩

theorem Coh.mul_left {X : Scheme.{0}} [IsIntegral X] {p k N : ℕ} {M : X → Matrix (Fin N) (Fin N) X.functionField}
    {c : X → Fin N → X.functionFieldˣ} (h : Coh p k M c) {u : Matrix (Fin N) (Fin N) X.functionField}
    (hu : ∀ x, Ov p x → Fr (loc x) u) : Coh p k (fun x => u * M x) c := fun x hx =>
  ⟨(hu x hx).mul (h x hx).1, (h x hx).2.mono fun z hz hz' => by
    rw [Matrix.mul_inv_rev, mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ (hu x hx).1.isUnit]
    exact hz hz'⟩

theorem reads_pf {C : CxSt F} {N p : ℕ} {A : Adl C Y} {V V' : Cover Y} {π : V'.X ⟶ V.X}
    (hπ : π (genericPoint V'.X) ⤳ genericPoint V.X) (hl : Lies V' V π) {c : V.X → Fin N → V.X.functionFieldˣ} {i : Fin N}
    (h : Reads V p A fun x => c x i) : Reads V' p A fun x => pf π hπ c x i :=
  GlobalTheory.T.reads_pullback_along_cover_map F Y C A p V V' π hπ hl (fun x => c x i) h

theorem exists_linked {C : CxSt F} {N : ℕ} {A A' : Fin N → Adl C Y} {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (hD : ∀ i, (A' i).D = (A i).D) (h : ∀ k, RelFlag A A' p n k) :
    ∃ (V : Cover Y) (c c' : V.X → Fin N → V.X.functionFieldˣ),
      (∀ i, Reads V p (A i) (fun x => c x i) ∧ Reads V p (A' i) fun x => c' x i) ∧ Relation.EqvGen (Link p) c c' := by
  obtain ⟨a, r, hr, hnr⟩ := Nat.exists_eq_pow_mul_and_not_dvd (pow_ne_zero 2 hn) p hp.ne_one
  obtain ⟨V, M, M', c, c', P, Q, hPQ, hI, hX, hR⟩ := GlobalTheory.T.exists_cover_integral_matrix_conjugation F Y C N A A' p n (N * a + 1 + 3 * a) hp hD (h _)
  haveI := GlobalTheory.VertOrd.charZero_fn V.ar
  have hn' : (n : V.X.functionField) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hr' : (r : V.X.functionField) ≠ 0 := Nat.cast_ne_zero.2 fun e => hr (e ▸ dvd_zero p)
  have hpa : (p : V.X.functionField) ^ a = (n : V.X.functionField) ^ 2 * (r : V.X.functionField)⁻¹ := by
    rw [← Nat.cast_pow n, hnr]
    push_cast
    field_simp
  have reg {f : V.X.functionField} (hf : PInt p f) (x) (hx : Ov p x) : f ∈ loc x := GlobalTheory.T.p_integral_regular_on_cover F Y V p hp f hf x hx
  have regr (x) (hx : Ov p x) : (r : V.X.functionField)⁻¹ ∈ loc x :=
    reg ⟨r, ((Nat.Prime.coprime_iff_not_dvd hp).2 hr).symm, by rw [mul_inv_cancel₀ hr']; exact isIntegral_one⟩ x hx
  have regs {T : Matrix (Fin N) (Fin N) V.X.functionField} (hT : ∀ i j, IsIntegral ℤ ((n : V.X.functionField) * T i j))
      (x) (hx : Ov p x) : (p : V.X.functionField) ^ a • T ∈ (loc x).matrix := fun i j => by
    have e : ((p : V.X.functionField) ^ a • T) i j = n * (n * T i j) * (r : V.X.functionField)⁻¹ := by
      rw [Matrix.smul_apply, hpa, smul_eq_mul]; ring
    rw [e]
    exact (loc x).mul_mem ((loc x).mul_mem (natCast_mem _ n)
      (reg ⟨1, Nat.coprime_one_left p, by simpa using hT i j⟩ x hx)) (regr x hx)
  obtain ⟨C₁, C₂⟩ := GlobalTheory.T.coherent_of_cross_with_bounded_inverse V.X p (N * a) a N M M' c c' P Q hPQ
    (fun x hx => ⟨regs (fun i j => (hI i j).1) x hx, regs (fun i j => (hI i j).2) x hx⟩) hX
  obtain ⟨u, v, u', v', g, huv, huv', hP, hu, hg⟩ := exists_smith hp hn P Q hPQ hI
  have fu (x) (hx : Ov p x) : Fr (loc x) u' :=
    fr_of_mul huv' (fun i j => reg (hu i j).2.2.1 x hx) fun i j => reg (hu i j).2.2.2 x hx
  have fv (x) (hx : Ov p x) : Fr (loc x) v :=
    fr_of_mul (mul_eq_one_comm.1 huv) (fun i j => reg (hu i j).2.1 x hx) fun i j => reg (hu i j).1 x hx
  have rg (j x) (hx : Ov p x) : RegAt x ((p : V.X.functionField) ^ a / g j) := by
    rw [hpa, mul_div_right_comm]
    exact (loc x).mul_mem (reg (hg j).2.2 x hx) (regr x hx)
  have ek : N * a + 1 = 0 + 1 + (Finset.univ : Finset (Fin N)).card * a := by simp [add_comm]
  obtain ⟨V₁, π₁, h₁, B₁, c₁, l₁, b₁, D₁, E₁⟩ := exists_chain V (a := a) hp (fun j => (hg j).1)
    (fun j x hx => ⟨reg (hg j).2.1 x hx, rg j x hx⟩) Finset.univ 0 (ek ▸ C₁.mul_left fu)
  obtain ⟨V₂, π₂, h₂, B₂, c₂, l₂, b₂, D₂, E₂⟩ := exists_chain V₁ (a := a) hp (g := fun _ => n)
    (fun _ => RelEx.natCast_ne_zero_X V₁ hn) (fun j x hx => ⟨RelEx.regAt_natCast x n, by
      have H := map_mem_loc π₁ h₁ x _ ((loc _).mul_mem (natCast_mem _ n) (regr _ (hx.map π₁)))
      rw [show (n : V.X.functionField) * (r : V.X.functionField)⁻¹ = p ^ a / n by rw [hpa]; field_simp, map_div₀, map_pow,
        map_natCast, map_natCast] at H
      exact H⟩) Finset.univ 0 (ek ▸ (C₂.mul_left fv).pull π₁ h₁)
  refine ⟨V₂, pf π₂ h₂ (pf π₁ h₁ c), pf π₂ h₂ (pf π₁ h₁ c'), fun i => ⟨?_, ?_⟩,
    .trans _ _ _ (eqvGen_pull π₂ h₂ E₁) (.trans _ _ _ (.rel _ c₂ (link_of_unitAt fun x hx i => ?_)) (.symm _ _ E₂))⟩
  · exact reads_pf h₂ l₂ (reads_pf h₁ l₁ (hR i).1)
  · exact reads_pf h₂ l₂ (reads_pf h₁ l₁ (hR i).2)
  let φ := (SmallSec.fnMap π₂ h₂).comp (SmallSec.fnMap π₁ h₁)
  have hx₁ := hx.map π₂
  have hx₀ := hx₁.map π₁
  have hφ : ∀ f ∈ loc (π₁ (π₂ x)), φ f ∈ loc x := fun f hf => map_mem_loc π₂ h₂ x _ (map_mem_loc π₁ h₁ _ _ hf)
  have eφ (T : Matrix (Fin N) (Fin N) V.X.functionField) :
      (T.map (SmallSec.fnMap π₁ h₁)).map (SmallSec.fnMap π₂ h₂) = T.map φ := rfl
  have hT := (((hX _ hx₀).2.2.self_of_nhds hx₀).1).map φ hφ
  rw [show N * a + 1 + 3 * a = (0 + 1) + a + (N * a + 2 * a) by ring, pow_add, map_mul] at hT
  replace hT := hT.of_mul (hφ _ (pow_mem (natCast_mem _ p) _))
  rw [pow_add, map_mul, map_pow, map_natCast, Matrix.map_mul, Matrix.map_mul, ← FrameGlue.Pull.matrix_map_inv] at hT
  have f₁ := (D₁ _ hx₁).1.map _ (map_mem_loc π₂ h₂ x)
  have f₂ := (D₂ _ hx).1
  simp only [Finset.mem_univ, if_true, pm, Matrix.map_mul, eφ, Matrix.diagonal_map (map_zero _), map_natCast] at f₁ f₂
  have H := unit_of_frames (n := (n : V₂.X.functionField)) (u := u.map φ) (v := v.map φ) (u' := u'.map φ)
    (g := fun j => φ (g j)) (B := (B₁ (π₂ x)).map (SmallSec.fnMap π₂ h₂)) (B' := B₂ x) (small_pow hx 0) (natCast_mem _ n)
    (RelEx.natCast_ne_zero_X V₂ hn) (hφ _ (pow_mem (natCast_mem _ p) a))
    (by rw [← Matrix.map_mul, huv, Matrix.map_one _ (map_zero _) (map_one _)])
    (by
      have := congrArg (·.map φ) hP
      simp only [Matrix.map_mul, Matrix.diagonal_map (map_zero φ)] at this
      rw [← this]
      ext i j
      simp)
    (fun j => ⟨(map_ne_zero φ).2 (hg j).1, by rw [← map_div₀]; exact hφ _ (rg j _ hx₀)⟩)
    (fun i l hl => by rw [Matrix.map_apply, (b₁ _ hx₁).1 hl, map_zero]) (b₂ x hx).1
    (by rw [← Matrix.map_mul]; exact ((fu _ hx₀).mul (C₁ _ hx₀).1).map φ hφ)
    (by rw [← Matrix.map_mul]; exact ((fv _ hx₀).mul (C₂ _ hx₀).1).map φ hφ) f₁ f₂ hT i
  have e₁ := congrArg (SmallSec.fnMap π₂ h₂) ((b₁ _ hx₁).2 i)
  have e₂ := (b₂ x hx).2 i
  rw [map_mul] at e₁
  have e : (c₂ x i : V₂.X.functionField) / pf π₂ h₂ c₁ x i =
      φ ((c' (π₁ (π₂ x)) i : V.X.functionField) / c (π₁ (π₂ x)) i) *
        (B₁ (π₂ x)).map (SmallSec.fnMap π₂ h₂) i i / B₂ x i i := by
    have n₁ := right_ne_zero_of_mul (e₁.trans_ne (pf π₂ h₂ (pf π₁ h₁ c) x i).ne_zero)
    have n₂ := right_ne_zero_of_mul (e₂ ▸ (pf π₂ h₂ (pf π₁ h₁ c') x i).ne_zero)
    have n₃ := (pf π₂ h₂ c₁ x i).ne_zero
    rw [map_div₀, show φ (c' (π₁ (π₂ x)) i : V.X.functionField) = _ from e₂.symm,
      show φ (c (π₁ (π₂ x)) i : V.X.functionField) = _ from e₁.symm, Matrix.map_apply]
    rw [val_pf] at n₃ ⊢
    field_simp
  rw [e]
  exact (unitAt_iff H.1).2 H.2

theorem exists_linked_finset {C : CxSt F} {N : ℕ} {A A' : Fin N → Adl C Y} (V₀ : Cover Y) (hD : ∀ i, (A' i).D = (A i).D)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ ∃ n : ℕ, n ≠ 0 ∧ ∀ k, RelFlag A A' p n k) :
    ∃ (V : Cover Y) (c c' : ℕ → V.X → Fin N → V.X.functionFieldˣ), ∀ p ∈ S,
      (∀ i, Reads V p (A i) (fun x => c p x i) ∧ Reads V p (A' i) fun x => c' p x i) ∧
        Relation.EqvGen (Link p) (c p) (c' p) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨V₀, fun _ _ _ => 1, fun _ _ _ => 1, fun p hp => absurd hp (Finset.notMem_empty p)⟩
  | insert p S _ ih =>
    obtain ⟨V₁, c₁, c₁', h₁⟩ := ih fun q hq => hS q (Finset.mem_insert_of_mem hq)
    obtain ⟨hp, n, hn, h⟩ := hS p (Finset.mem_insert_self p S)
    obtain ⟨V₂, c₂, c₂', h₂⟩ := exists_linked hp hn hD h
    obtain ⟨V, π₁, π₂, -, -, l₁, l₂⟩ := CoverCommon.exists_cover_dominating_two F Y V₁ V₂
    have g₁ := GlobalTheory.T.cover_morphism_generic_point_specializes F Y V₁ V π₁ l₁
    have g₂ := GlobalTheory.T.cover_morphism_generic_point_specializes F Y V₂ V π₂ l₂
    refine ⟨V, fun q => if q = p then pf π₂ g₂ c₂ else pf π₁ g₁ (c₁ q),
      fun q => if q = p then pf π₂ g₂ c₂' else pf π₁ g₁ (c₁' q), fun q hq => ?_⟩
    by_cases e : q = p
    · subst e
      simp only [if_true]
      exact ⟨fun i => ⟨reads_pf g₂ l₂ (h₂.1 i).1, reads_pf g₂ l₂ (h₂.1 i).2⟩,
        eqvGen_pull π₂ g₂ h₂.2⟩
    · simp only [if_neg e]
      have h₃ := h₁ q ((Finset.mem_insert.1 hq).resolve_left e)
      exact ⟨fun i => ⟨reads_pf g₁ l₁ (h₃.1 i).1, reads_pf g₁ l₁ (h₃.1 i).2⟩,
        eqvGen_pull π₁ g₁ h₃.2⟩

theorem rep_of_reads {C : CxSt F} {N p m : ℕ} (hp : p.Prime) {A : Adl C Y} {V V' : Cover Y} {π : V'.X ⟶ V.X}
    (hπ : π (genericPoint V'.X) ⤳ genericPoint V.X) (hl : Lies V' V π) {c : V.X → Fin N → V.X.functionFieldˣ} {i : Fin N}
    (h : Reads V p A fun x => c x i) {L : HermLB V'.p} {a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ}
    (hL : Norms V' L (fun x => genAt A.D x ^ m) a fun v e y => m * A.lg v e y) : Rep p L fun x => pf π hπ c x i ^ m := by
  obtain ⟨hη, W, U, hW, h₁, h₂, h₃⟩ := h
  obtain ⟨s, hs, H⟩ := FrameGlue.powOfFrames_of_normsAt F Y C A p hp V hη W V.X U
    (fun x => Units.map (jm V hη).toMonoidHom (c x i)) (fun x => c x i) hW (fun _ => rfl) h₂ h₃ V' π hπ hl L.B m
    (normsAt_of_norms hL p ⊤)
  refine ⟨s, hs, fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := exists_chart L.isLB x
  refine ((presents_divOfRatSec L.isLB hs).isEqn k x hk).iff_unitAt.2 ?_
  have := (H (π x) k x (h₁ _ (hx.map π)) hk hx).inv
  rwa [Units.val_div_eq_div_val, inv_div] at this

theorem powerSum_two_eq : Hypotheses2 → GlobalTheory.Published.RegularAlteration → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (ι : Type) [Fintype ι] (A : ι → Adl (cxSt F) Y) (L : ι → HermLB M.p) (m : ℕ+) (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ), (∀ i, (A i).Induced M (L i) m 0) → (haveI := M.ar.isIntegral; IsArFun L Y.dim Ψ) → ∀ (N : ℕ) (s s' : Fin N → ι), (∀ a, A (s' a) = { A (s a) with lg := (A (s' a)).lg }) → ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ ∃ n : ℕ, n ≠ 0 ∧ ∀ k : ℕ, RelFlag (fun a => A (s a)) (fun a => A (s' a)) p n k) → (∀ a v e y, resP v ∉ S → (A (s a)).lg v e y = (A (s' a)).lg v e y) → ∀ g : MvPolynomial ι ℝ, Ψ ((∑ a, X (s a) ^ 2 - ∑ a, X (s' a) ^ 2) * g) = 0 := by
  intro hP _ F _ _ Y M ι _ A L m Ψ hI hΨ N s s' hs S hS hoff g
  have hC := hP.p4
  have hD (a) : (A (s' a)).D = (A (s a)).D := by rw [hs a]
  obtain ⟨V₀, -⟩ := GlobalTheory.T.exists_cover_function_field_embedding F Y M Y.Fn
  obtain ⟨V, c, c', hc⟩ := exists_linked_finset V₀ hD S hS
  obtain ⟨V', π, L', d, -, hl, hd, hL', hΦ⟩ := GlobalTheory.T.exists_cover_induced_metrics_arith hC F Y M V ι A L m Ψ hI hΨ
  have hπ := GlobalTheory.T.cover_morphism_generic_point_specializes F Y V V' π hl
  refine (mul_eq_zero.1 (show d * _ = 0 from ?_)).resolve_left hd
  change (d • Ψ) _ = 0
  generalize d • Ψ = Φ at hΦ
  induction g using MvPolynomial.induction_on' with
  | add P Q hP hQ => rw [mul_add, map_add, hP, hQ, add_zero]
  | monomial u a =>
    obtain ⟨n, ν, hν⟩ := exists_monomial_eq_prod u
    have e₁ : (monomial u a : MvPolynomial ι ℝ) = a • ∏ j, X (ν j) := by rw [← hν, smul_monomial, smul_eq_mul, mul_one]
    rw [e₁, mul_smul_comm, map_smul, smul_eq_zero]
    refine .inr ?_
    by_cases hn : Y.dim = n + 1
    swap
    · refine hΦ.2 _ (2 + ∑ _j : Fin n, 1) (by simp; omega) ?_
      exact ((IsHomogeneous.sum _ _ _ fun a _ => isHomogeneous_X_pow _ _).sub
        (IsHomogeneous.sum _ _ _ fun a _ => isHomogeneous_X_pow _ _)).mul
        (IsHomogeneous.prod _ _ _ fun j _ => isHomogeneous_X _ _)
    have ar : IsArithVar V'.p (n + 1) := hn ▸ V'.ar
    rw [hn] at hΦ
    obtain ⟨num, hnum, hsy⟩ := GlobalTheory.T.arith_intersection_form_exists hC _ _ V'.p _ ar
    obtain ⟨rt, rd, -, -⟩ := GlobalTheory.T.arith_class_form_properties hC _ _ V'.p _ ar num hnum
    have hterm (b : ι) : Φ (X b ^ 2 * ∏ j, X (ν j)) = bil num (fun j => cl (L' (ν j))) (cl (L' b)) (cl (L' b)) := by
      have := hnum ι L' Φ hΦ (Fin.cons (Pi.single b 1) (Fin.cons (Pi.single b 1) fun j => Pi.single (ν j) 1))
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ] at this
      simp only [Fin.cons_zero, Fin.cons_succ, TrivFlag.lin_single] at this
      rw [sq, mul_assoc, this, bil_apply]
      congr 1
      funext j
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j <;> simp [Pi.single_apply]
    choose r hr hN using fun a => GlobalTheory.T.exists_rational_section_with_norms F Y V' _ _ (norms_div (hs a) (hL' (s a)) (hL' (s' a)))
    have key := GlobalTheory.T.sum_moves_over_finite_primes hP _ V'.X V'.p n ar num hnum hsy (fun j => L' (ν j)) m N (fun p => pf π hπ (c' p))
      (fun p => pf π hπ (c p)) (fun a => L' (s a)) S (fun p hp => ⟨(hS p hp).1, by
        have hE := GlobalTheory.T.moves_equivalence_of_prints2 hP _ V'.X V'.p n ar num hnum hsy (fun j => L' (ν j)) p m N (hS p hp).1
        exact hE.symm (hE.eqvGen_iff.1 (Relation.EqvGen.mono (r := Link p) (fun x y h =>
          GlobalTheory.T.moves_of_linked_sections hP _ V'.X V'.p n ar num hnum hsy (fun j => L' (ν j)) p m N (hS p hp).1 x y h) _ _
          (eqvGen_pull π hπ (hc p hp).2)))⟩) (fun a => L' (s' a)) (fun a => (L' (s a)).tens (L' (s' a)).dual)
      (fun a => HermLB.div _ (hr a)) fun a => ⟨⟨r a, hr a, rfl, (hN a).1⟩, ?_,
        GlobalTheory.T.divisor_trivial_away_from_bad_primes F Y V' _ _ _ _ (hN a) S fun v hv e y => by rw [hoff a v e y hv, sub_self, mul_zero],
        fun p hp => ⟨rep_of_reads (hS p hp).1 hπ hl ((hc p hp).1 a).2 (hL' (s' a)),
          GlobalTheory.T.reads_compare_of_scaled_local_norms F Y _ V' _ _ _ _ (hN a) p m (hS p hp).1 (A (s a)) (A (s' a)) _ _ (hD a)
            (reads_pf hπ hl ((hc p hp).1 a).1) (reads_pf hπ hl ((hc p hp).1 a).2) fun _ _ _ _ => rfl⟩⟩
    · rw [sub_mul, Finset.sum_mul, Finset.sum_mul, map_sub, map_sum, map_sum]
      simp only [hterm]
      exact sub_eq_zero.2 key
    · have := neg_mem (add_mem (rt (L' (s a)) (L' (s' a)).dual) (rd (L' (s' a))))
      convert this using 1
      abel

end GlobalTheory.LatChain

end
