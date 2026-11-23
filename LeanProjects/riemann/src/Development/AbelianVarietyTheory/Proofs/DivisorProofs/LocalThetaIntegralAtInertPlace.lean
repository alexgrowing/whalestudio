import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusOfNormEqAbs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntSmulMemOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTerSide
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.IntegralDetModule

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def bas (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) :
    Module.Basis (Σ _ : Fin n, Fin (Module.finrank F E)) (AF F) (Fin n → AE F E) :=
  Pi.basis fun _ => (Module.finBasis F E).baseChange (AF F)

def big {n : ℕ} (t : Matrix (Fin n) (Fin n) (AE F E)) :
    Matrix (Σ _ : Fin n, Fin (Module.finrank F E)) (Σ _ : Fin n, Fin (Module.finrank F E)) (AF F) :=
  LinearMap.toMatrix (bas F E n) (bas F E n) ((Matrix.toLin' t).restrictScalars (AF F))

theorem big_apply {n : ℕ} (t : Matrix (Fin n) (Fin n) (AE F E)) (x y) :
    big t x y = (bas F E n).repr (t *ᵥ bas F E n y) x := by
  rw [big, LinearMap.toMatrix_apply]
  rfl

theorem det_big {n : ℕ} (t : Matrix (Fin n) (Fin n) (AE F E)) :
    (big t).det = Algebra.norm (AF F) t.det := by
  rw [big, LinearMap.det_toMatrix, LinearMap.det_restrictScalars, LinearMap.det_toLin']

theorem bas_eq {n : ℕ} (x) :
    bas F E n x = fun i => inclR (F := F) (AF F) ((Pi.single x.1 (Module.finBasis F E x.2) : Fin n → E) i) := by
  rw [bas, Pi.basis_apply]
  funext i
  by_cases h : i = x.1
  · subst h
    rw [Pi.single_eq_same, Pi.single_eq_same, Module.Basis.baseChange_apply]
    rfl
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]

theorem map_norm_det {n : ℕ} {K : Type} [CommRing K] (φ : AF F →+* K) (t : Matrix (Fin n) (Fin n) (AE F E))
    (u : AF F) (hu : φ u = 1) (ht : u • (t - 1) = 0) : φ (Algebra.norm (AF F) t.det) = 1 := by
  rw [← det_big, RingHom.map_det]
  have : φ.mapMatrix (big t) = 1 := by
    ext x y
    have h1 : u • (t *ᵥ bas F E n y) = u • bas F E n y := by
      have h2 : (u • (t - 1)) *ᵥ bas F E n y = 0 := by rw [ht, Matrix.zero_mulVec]
      rwa [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, smul_sub, sub_eq_zero] at h2
    have h3 := congrArg (fun z => φ ((bas F E n).repr z x)) h1
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, hu, one_mul, Module.Basis.repr_self] at h3
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, big_apply, h3, Matrix.one_apply, Finsupp.single_apply]
    by_cases h : x = y
    · simp [h]
    · simp [h, Ne.symm h]
  rw [this, Matrix.det_one]

theorem exists_bound {n : ℕ} (W : Spc F E n) (hL : W.L.FG) (v : Pl F) :
    ∃ C : ℝ, ∀ z ∈ GlobalTheory.InertSph.latAt W v, ∀ x, ‖evFin F v ((bas F E n).repr z x)‖ ≤ C := by
  first
  | exact @_root_.GlobalTheory.CoordinateEmbeddingMaps.main
  | exact _root_.GlobalTheory.CoordinateEmbeddingMaps.main
  | (apply _root_.GlobalTheory.CoordinateEmbeddingMaps.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoordinateEmbeddingMaps.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoordinateEmbeddingMaps.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoordinateEmbeddingMaps.main ..)

theorem exists_mul_mem {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsLattice E) (y : Fin n → E) :
    ∃ D : ℤ, D ≠ 0 ∧ D • y ∈ L := by
  first
  | exact @_root_.GlobalTheory.LatticeIntegerMultipleMembership.exists_int_smul_mem_of_isLattice
  | exact _root_.GlobalTheory.LatticeIntegerMultipleMembership.exists_int_smul_mem_of_isLattice
  | (apply _root_.GlobalTheory.LatticeIntegerMultipleMembership.exists_int_smul_mem_of_isLattice <;> assumption)
  | (intros; apply _root_.GlobalTheory.LatticeIntegerMultipleMembership.exists_int_smul_mem_of_isLattice <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LatticeIntegerMultipleMembership.exists_int_smul_mem_of_isLattice <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LatticeIntegerMultipleMembership.exists_int_smul_mem_of_isLattice ..)

theorem exists_entry_bound {n : ℕ} (W : Spc F E n) (hL : W.L.IsLattice E) (v : Pl F) :
    ∃ C : ℝ, ∀ t : Matrix (Fin n) (Fin n) (AE F E),
      (∀ z ∈ GlobalTheory.InertSph.latAt W v, t *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) → ∀ x y, ‖evFin F v (big t x y)‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound W hL.fg v
  choose D hD0 hD using fun x : (Σ _ : Fin n, Fin (Module.finrank F E)) =>
    exists_mul_mem W.L hL (Pi.single x.1 (Module.finBasis F E x.2))
  haveI : CharZero (Fv F v) := algebraRat.charZero _
  refine ⟨∑ y, |C| / ‖(D y : Fv F v)‖, fun t ht x y => ?_⟩
  set e := GlobalTheory.EmbChart.atPlace v (1 : Fv F v) with he
  have he1 : evFin F v e = 1 := GlobalTheory.EmbChart.evFin_atPlace v 1
  have hmem : e • (D y • bas F E n y) ∈ GlobalTheory.InertSph.latAt W v := by
    refine AddSubgroup.subset_closure ⟨e, ?_, ?_, _, hD y, ?_⟩
    · intro u hu
      rw [smul_eq_mul, mul_comm, he, GlobalTheory.EmbChart.atPlace_mul_right, hu, mul_zero, map_zero]
    · rw [he1]; exact one_mem _
    · rw [bas_eq]
      congr 1
      funext i
      simp only [Pi.smul_apply, map_zsmul]
  have h1 := hC _ (ht _ hmem) x
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, map_smul, map_zsmul, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul,
    map_mul, he1, one_mul, map_zsmul, zsmul_eq_mul, norm_mul, ← big_apply] at h1
  have hpos : 0 < ‖(D y : Fv F v)‖ := norm_pos_iff.2 (Int.cast_ne_zero.2 (hD0 y))
  calc ‖evFin F v (big t x y)‖ ≤ |C| / ‖(D y : Fv F v)‖ := by
        rw [le_div_iff₀ hpos, mul_comm]; exact h1.trans (le_abs_self C)
    _ ≤ _ := Finset.single_le_sum (f := fun y => |C| / ‖(D y : Fv F v)‖)
        (fun y _ => div_nonneg (abs_nonneg _) (norm_nonneg _)) (Finset.mem_univ y)

theorem norm_le_one {n : ℕ} (W : Spc F E n) (hL : W.L.IsLattice E) (v : Pl F) (t : Matrix (Fin n) (Fin n) (AE F E))
    (ht : ∀ z ∈ GlobalTheory.InertSph.latAt W v, t *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) :
    ‖evFin F v (Algebra.norm (AF F) t.det)‖ ≤ 1 := by
  obtain ⟨C, hC⟩ := exists_entry_bound W hL v
  have hk : ∀ k : ℕ, ∀ z ∈ GlobalTheory.InertSph.latAt W v, (t ^ k) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
    intro k
    induction k with
    | zero => intro z hz; simpa using hz
    | succ k ih => intro z hz; rw [pow_succ, ← Matrix.mulVec_mulVec]; exact ih _ (ht z hz)
  have hb : ∃ B : ℝ, ∀ k : ℕ, ‖evFin F v (Algebra.norm (AF F) t.det)‖ ^ k ≤ B := by
    refine ⟨(Fintype.card (Σ _ : Fin n, Fin (Module.finrank F E))).factorial •
      C ^ Fintype.card (Σ _ : Fin n, Fin (Module.finrank F E)), fun k => ?_⟩
    rw [← norm_pow, ← map_pow, ← map_pow, ← Matrix.det_pow, ← det_big]
    have := Matrix.det_le (abv := (NormedField.toAbsoluteValue (Fv F v))) (A := (big (t ^ k)).map (evFin F v)) (x := C)
      (fun x y => hC _ (hk k) x y)
    have e : evFin F v (big (t ^ k)).det = ((big (t ^ k)).map (evFin F v)).det :=
      RingHom.map_det (evFin F v).toRingHom _
    rw [e]
    exact this
  obtain ⟨B, hB⟩ := hb
  by_contra h
  obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_atTop_of_one_lt (not_le.1 h)).eventually_gt_atTop B).exists
  exact absurd (hB k) (not_le.2 hk)

theorem modu_eq_one (a : (AF F)ˣ) (h1 : (a : AF F).1 = 1) (h2 : ∀ v, ‖evFin F v a‖ = 1) :
    (adeleClass F).modu a = 1 := by
  apply NNReal.eq
  change (MeasureTheory.distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ) = _
  rw [GlobalTheory.ModuAdele.distribHaarChar_adeleRing, GroundTheory.Global.IdeleGroup.ideleModule_eq]
  have h3 : ∀ v : HeightOneSpectrum (𝓞 F), ‖(a : AF F).2 v‖ = 1 := h2
  have h4 : ∀ w : InfinitePlace F, ‖(a : AF F).1 w‖ = 1 := fun w => by
    rw [h1]; exact norm_one
  simp only [h3, h4, one_pow, Finset.prod_const_one, finprod_one, mul_one, NNReal.coe_one]

theorem modu_norm_det {n : ℕ} (W : Spc F E n) (hL : W.L.IsLattice E) (v : Pl F) (t : GL (Fin n) (AE F E))
    (h1 : At (evFin F v) ((t : Matrix (Fin n) (Fin n) (AE F E)) - 1))
    (h2 : ∀ z ∈ GlobalTheory.InertSph.latAt W v, (t : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v ∧
      ((t⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) :
    (adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t)) = 1 := by
  have h0 := h1 (1 - GlobalTheory.EmbChart.atPlace v 1) (by rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self])
  apply modu_eq_one
  · refine map_norm_det (fstA F).toRingHom _ _ ?_ h0
    rw [map_sub, map_one, sub_eq_self]
    rfl
  · intro u
    by_cases hu : u = v
    · subst hu
      have a1 := norm_le_one W hL u _ fun z hz => (h2 z hz).1
      have a2 := norm_le_one W hL u _ fun z hz => (h2 z hz).2
      have a3 : ‖evFin F u (Algebra.norm (AF F) (t : Matrix (Fin n) (Fin n) (AE F E)).det)‖ *
          ‖evFin F u (Algebra.norm (AF F) ((t⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)).det)‖ = 1 := by
        rw [← norm_mul, ← map_mul, ← map_mul, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, map_one, map_one, norm_one]
      refine le_antisymm a1 ?_
      rw [← a3]
      exact mul_le_of_le_one_right (norm_nonneg _) a2
    · have := map_norm_det (evFin F u).toRingHom _ _ (by
        rw [map_sub, map_one, sub_eq_self]
        exact evalV_singleFin_ne hu 1) h0
      exact (congrArg norm this).trans norm_one

end GlobalTheory.IntegralDetModule

theorem GlobalTheory.IntegralDetModule.modu_norm_det_triple : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ t : GL (Fin (a + a')) (AE F E), (At (evFin F v) ((t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) - 1) ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v ∧
        ((t⁻¹ : GL (Fin (a + a')) (AE F E)) : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
      (adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t)) = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v _ _ _ t ht
  exact GlobalTheory.IntegralDetModule.modu_norm_det G.W hT.geo.hW.lat v t ht.1 ht.2

end
