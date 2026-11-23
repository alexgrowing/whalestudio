import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedMY
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.UnramifiedMeasureTuples
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.IsEmptyPlacesReferenceTuple

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta IsDedekindDomain NumberField GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedMeasureTuples Formalism.UG.P

namespace GlobalTheory.MeasTupleEq

theorem indexValue_eq_parIdx (q : ℝ) (r d : ℕ) : indexValue q r d = parIdx q r d := by
  simp only [indexValue, parIdx, zpow_neg, zpow_natCast]

theorem map_residue_surjective (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) :
    Function.Surjective (Matrix.GeneralLinearGroup.map (n := Fin n) (IsLocalRing.residue O)) := by
  intro g
  classical
  let M : Matrix (Fin n) (Fin n) O := fun a b =>
    Function.surjInv (IsLocalRing.residue_surjective (R := O)) ((g : Matrix (Fin n) (Fin n) _) a b)
  have hM : M.map (IsLocalRing.residue O) = (g : Matrix (Fin n) (Fin n) _) := by
    ext a b
    simp only [M]
    exact Function.surjInv_eq _ _
  have hdet : IsUnit M.det := by
    have h1 : IsUnit (IsLocalRing.residue O M.det) := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hM]
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using (Matrix.GeneralLinearGroup.det g).isUnit
    exact (isUnit_map_iff (IsLocalRing.residue O) _).1 h1
  refine ⟨Matrix.GeneralLinearGroup.mk'' M hdet, Units.ext ?_⟩
  exact hM

theorem index_parahoric (O : Type) [CommRing O] [IsLocalRing O] (r d : ℕ) :
    (parahoric (IsLocalRing.maximalIdeal O) r d).index =
      (parahoric (⊥ : Ideal (IsLocalRing.ResidueField O)) r d).index := by
  rw [← Subgroup.index_comap_of_surjective _ (map_residue_surjective O (r + d))]
  congr 1
  ext h
  rw [Subgroup.mem_comap]
  refine forall_congr' fun i => forall_congr' fun k => forall_congr' fun _ => forall_congr' fun _ => ?_
  rw [Ideal.mem_bot]
  exact (IsLocalRing.residue_eq_zero_iff _).symm

def glT {k : Type} [Field k] {n : ℕ} (g : GL (Fin n) k) : GL (Fin n) k :=
  ⟨(g : Matrix (Fin n) (Fin n) k).transpose, ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).transpose,
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]⟩

theorem index_upper_eq_lower (k : Type) [Field k] [Fintype k] (r d : ℕ) :
    (parahoric (⊥ : Ideal k) r d).index = (tjcosets_par (𝔽 := k) (r + d) r).index := by
  classical
  have hc : Nat.card (parahoric (⊥ : Ideal k) r d) = Nat.card (tjcosets_par (𝔽 := k) (r + d) r) :=
    Nat.card_congr
      { toFun := fun g => ⟨glT g.1, fun a b ha hb => Ideal.mem_bot.1 (g.2 b a hb ha)⟩
        invFun := fun g => ⟨glT g.1, fun a b ha hb => Ideal.mem_bot.2 (g.2 b a hb ha)⟩
        left_inv := fun g => Subtype.ext (Units.ext rfl)
        right_inv := fun g => Subtype.ext (Units.ext rfl) }
  have h1 := (parahoric (⊥ : Ideal k) r d).index_mul_card
  have h2 := (tjcosets_par (𝔽 := k) (r + d) r).index_mul_card
  rw [hc, ← h2] at h1
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1

theorem prod_one_sub {q : ℝ} (hq : q ≠ 0) (n : ℕ) :
    (∏ i ∈ Finset.Icc 1 n, (1 - (q ^ i)⁻¹)) * q ^ (∑ i ∈ Finset.range n, (i + 1)) =
      ∏ i ∈ Finset.range n, (q ^ (i + 1) - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega), Finset.sum_range_succ, Finset.prod_range_succ, ← ih,
      pow_add q (∑ i ∈ Finset.range n, (i + 1))]
    have : (1 - (q ^ (n + 1))⁻¹) * q ^ (n + 1) = q ^ (n + 1) - 1 := by field_simp
    rw [← this]; ring

theorem sum_add (r d : ℕ) : ∑ i ∈ Finset.range (r + d), (i + 1) =
    r * d + (∑ i ∈ Finset.range r, (i + 1) + ∑ i ∈ Finset.range d, (i + 1)) := by
  induction d with
  | zero => simp
  | succ d ih => rw [← add_assoc, Finset.sum_range_succ, ih, Finset.sum_range_succ]; ring

theorem eq_indexValue {q : ℝ} (hq : 1 < q) (r d : ℕ) (C : ℝ)
    (h : C * (∏ i ∈ Finset.range r, (q ^ (i + 1) - 1)) * ∏ i ∈ Finset.range d, (q ^ (i + 1) - 1) =
      ∏ i ∈ Finset.range (r + d), (q ^ (i + 1) - 1)) : C = indexValue q r d := by
  have h0 : q ≠ 0 := by linarith
  have hp : ∀ n, (∏ i ∈ Finset.Icc 1 n, (1 - (q ^ i)⁻¹)) ≠ 0 := fun n => by
    have := (GlobalTheory.MeasTuple.prod_pos' hq n).ne'
    simpa only [zpow_neg, zpow_natCast] using this
  rw [← prod_one_sub h0, ← prod_one_sub h0, ← prod_one_sub h0, sum_add, pow_add, pow_add] at h
  unfold indexValue
  rw [eq_div_iff (mul_ne_zero (hp r) (hp d))]
  apply mul_right_cancel₀ (mul_ne_zero (pow_ne_zero (∑ i ∈ Finset.range r, (i + 1)) h0)
    (pow_ne_zero (∑ i ∈ Finset.range d, (i + 1)) h0))
  linear_combination h

theorem index_field (k : Type) [Field k] [Fintype k] (r d : ℕ) :
    ((parahoric (⊥ : Ideal k) r d).index : ℝ) = indexValue (Fintype.card k : ℝ) r d := by
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  have h := tjcosets_arith _ (r + d) r _ hq (by omega) (tjcosets_ff_count (𝔽 := k) (r + d) r (by omega))
  have h2 := tjcosets_prod_shift (Fintype.card k : ℤ) d r
  rw [add_comm d r, ← h, ← index_upper_eq_lower, mul_comm] at h2
  apply eq_indexValue (by exact_mod_cast hq)
  exact_mod_cast h2

theorem indexFormula : IndexFormula := by
  intro F _ _ v r d
  haveI : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) := tjcosets_finite v
  letI := Fintype.ofFinite (IsLocalRing.ResidueField (v.adicCompletionIntegers F))
  have hc := tjcosets_card_residue v
  rw [Nat.card_eq_fintype_card] at hc
  unfold localIndex
  rw [index_parahoric, index_field, hc]
  rfl

theorem localIndex_ne_one {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {r d : ℕ} (hr : 0 < r)
    (hd : 0 < d) : localIndex v r d ≠ 1 := by
  intro h
  unfold localIndex at h
  rw [Subgroup.index_eq_one, eq_top_iff] at h
  let i : Fin (r + d) := ⟨r, by omega⟩
  let k : Fin (r + d) := ⟨0, by omega⟩
  have hik : i ≠ k := fun e => by have := congrArg Fin.val e; simp only [i, k] at this; omega
  have hdet : IsUnit (Matrix.transvection i k (1 : v.adicCompletionIntegers F)).det := by
    rw [Matrix.det_transvection_of_ne i k hik]; exact isUnit_one
  have hm := h (Subgroup.mem_top (Matrix.GeneralLinearGroup.mk'' _ hdet)) i k le_rfl hr
  have he : (Matrix.transvection i k (1 : v.adicCompletionIntegers F)) i k = 1 := by
    simp [Matrix.transvection, Matrix.one_apply_ne hik]
  have hm' : (1 : v.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal _ := he ▸ hm
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 hm')

variable {D : D7} {X : ThetaX D}

theorem myTied_iff_abstract (X : ThetaX D) (Z : DivX D) : ThetaDivisorCompatibility X Z ↔ MeasFactorAbstract X Z := by
  unfold ThetaDivisorCompatibility ThetaX.TieMY MeasFactorAbstract
  simp only [indexValue_eq_parIdx]

theorem prod_localIndex {T : ThetaTied D X} {Z : DivX D} {μ : D.what₂.Tup} (e : Z.QPl μ ≃ ramPlaces T μ)
    (he : ∀ x, Z.qv μ x = Ideal.absNorm (e x).1.asIdeal) (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (hS : (↑S : Set _) = ramPlaces T μ) (r d : ℕ) :
    ∏ v ∈ S, (localIndex v r d : ℝ) = ∏ x : Z.QPl μ, parIdx (Z.qv μ x) r d := by
  symm
  refine Finset.prod_bij (fun x _ => (e x).1) (fun x _ => ?_) (fun x _ y _ hxy => ?_) (fun v hv => ?_) (fun x _ => ?_)
  · exact Finset.mem_coe.mp (hS.symm.subset (e x).2)
  · exact e.injective (Subtype.ext hxy)
  · have hv' : v ∈ ramPlaces T μ := by rw [← hS]; exact hv
    exact ⟨e.symm ⟨v, hv'⟩, Finset.mem_univ _, by simp⟩
  · rw [he x, indexFormula, indexValue_eq_parIdx]

theorem factor_iff_myTied {T : ThetaTied D X} {Z : DivX D} (hP : PlacesTied T Z) : MeasFactor T ↔ ThetaDivisorCompatibility X Z := by
  refine forall_congr' fun μ => ?_
  obtain ⟨e, he⟩ := hP μ
  constructor
  · rintro ⟨S, hS, hm⟩ j hj
    rw [hm j hj, prod_localIndex e he S hS]
  · intro h
    have hfin : (ramPlaces T μ).Finite := Set.finite_coe_iff.1 (Finite.of_equiv _ e)
    refine ⟨hfin.toFinset, hfin.coe_toFinset, fun j hj => ?_⟩
    rw [h j hj, prod_localIndex e he _ hfin.coe_toFinset]

theorem measTupleTied_iff (T : ThetaTied D X) (Z : DivX D) :
    MeasTupleTied T Z ↔ (∀ μ, ∀ v ∈ ramPlaces T μ, IsSplit D v) ∧ PlacesTied T Z ∧ ThetaDivisorCompatibility X Z :=
  ⟨fun h => ⟨h.split, h.places, (factor_iff_myTied h.places).1 h.factor⟩,
    fun h => ⟨h.1, h.2.1, (factor_iff_myTied h.2.1).2 h.2.2⟩⟩

theorem myTied_of_measTupleTied {T : ThetaTied D X} {Z : DivX D} (h : MeasTupleTied T Z) : ThetaDivisorCompatibility X Z :=
  ((measTupleTied_iff T Z).1 h).2.2

theorem mY_ne_one {T : ThetaTied D X} (h : MeasFactor T) {μ : D.what₂.Tup} (hμ : (ramPlaces T μ).Nonempty) :
    X.mY μ 1 ≠ 1 := by
  obtain ⟨S, hS, hm⟩ := h μ
  obtain ⟨v, hv⟩ := hμ
  have h2 := D.R.two_le_m
  have hr : 0 < D.R.r := by unfold Ranks.r; omega
  have ht : 0 < 1 * D.R.t := by have := D.R.rank_add_five_le; omega
  rw [hm 1 (by omega), ← Nat.cast_prod, Ne, Nat.cast_eq_one, Finset.prod_eq_one_iff]
  intro hall
  exact localIndex_ne_one v hr ht (hall v (Finset.mem_coe.1 (hS.symm.subset hv)))

theorem myTied_not_measTupleTied (T : ThetaTied D X) (Z : DivX D) {μ : D.what₂.Tup} (hμ : (ramPlaces T μ).Nonempty) :
    ∃ (X' : ThetaX D) (T' : ThetaTied D X') (Z' : DivX D), Z'.Qp = Z.Qp ∧ (∀ ν, ramPlaces T' ν = ramPlaces T ν) ∧
      (∀ ν j, X'.mY ν j = 1) ∧ ThetaDivisorCompatibility X' Z' ∧ ¬ PlacesTied T' Z' ∧ ¬ MeasFactor T' ∧
      ¬ MeasTupleTied T' Z' := by
  have hn : ¬ PlacesTied (GlobalTheory.MeasTuple.thetaDivisorRestriction T (GlobalTheory.MeasTuple.rep Z 0)) (GlobalTheory.MeasTuple.rep Z 0) := fun h => by
    obtain ⟨e, -⟩ := h μ
    obtain ⟨v, hv⟩ := hμ
    exact (e.symm ⟨v, hv⟩).1.elim0
  exact ⟨_, GlobalTheory.MeasTuple.thetaDivisorRestriction T (GlobalTheory.MeasTuple.rep Z 0), GlobalTheory.MeasTuple.rep Z 0, rfl, fun _ => rfl,
    (GlobalTheory.MeasTuple.trivial_factor X Z).2.2, GlobalTheory.MeasTuple.myTied_setMY _ _, hn,
    fun h => mY_ne_one h (μ := μ) hμ ((GlobalTheory.MeasTuple.trivial_factor X Z).2.2 μ 1), fun h => hn h.places⟩

end GlobalTheory.MeasTupleEq

end
