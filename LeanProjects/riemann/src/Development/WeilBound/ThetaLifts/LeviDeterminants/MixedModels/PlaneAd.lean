import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.PlaneGen

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.Mix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n k : ℕ}

theorem det_ne_of_sig {M : Matrix (Fin n) (Fin n) ℂ} {r s : ℕ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hr, A, hA⟩ := h
  let e : Fin n ≃ Fin r ⊕ Fin s := (finCongr hr.symm).trans finSumFinEquiv.symm
  have h1 : (A.submatrix id e)ᵀ * M * (A.submatrix id e).map star = (Aᵀ * M * A.map star).submatrix e e := by
    ext i j
    simp [Matrix.mul_apply]
  intro h0
  have h2 := congrArg Matrix.det h1
  rw [hA, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_mul, Matrix.det_mul, h0, Matrix.det_neg] at h2
  simp at h2
  exact pow_ne_zero s (neg_ne_zero.2 one_ne_zero) h2.symm

theorem conj_conj {B : Base F E} (h : B.IsGood σ) (x : E) : σ (σ x) = x := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact φ.injective (by rw [h.cm.2.2.2, h.cm.2.2.2, star_star])

theorem cA_inc (a : E) : cA σ (inclR (F := F) (AF F) a) = inclR (F := F) (AF F) (σ a) := rfl

theorem bf_inc (J : Matrix (Fin n) (Fin n) E) (u v : Fin n → E) :
    bf (cA σ).toRingHom (incM F J) (incV F u) (incV F v) = inclR (F := F) (AF F) (form σ J u v) := by
  simp only [bf, form, dotProduct, Matrix.mulVec, map_sum, map_mul]
  rfl

theorem inc_mulVec {m : ℕ} (A : Matrix (Fin n) (Fin m) E) (u : Fin m → E) : incM F A *ᵥ incV F u = incV F (A *ᵥ u) :=
  funext fun i => (RingHom.map_mulVec (inclR (F := F) (AF F)) A u i).symm

theorem vec_eq {m : ℕ} (z : Fin m → AE F E) : z = ∑ j, z j • incV F (Pi.single j 1) := by
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, incV, Pi.single_apply, apply_ite, map_one, map_zero, smul_eq_mul, mul_one, mul_zero]
  simp

theorem bf_sum_l {R : Type} [CommRing R] {c : R →+* R} {J : Matrix (Fin n) (Fin n) R} {m : ℕ} (u : Fin m → Fin n → R) (v) :
    bf c J (∑ j, u j) v = ∑ j, bf c J (u j) v := sum_dotProduct _ _ _

theorem planeOK {B : Base F E} (hB : B.IsGood σ) {Y : Spc F E n} {Y₁ : Spc F E k} {H : Plane E n k} {i₀ i₁ : ℕ}
    (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) (ε : ℤˣ) (hJ : ∀ i j, σ (Y.J j i) = ((ε : ℤ) : E) * Y.J i j) (hd : Y.J.det ≠ 0)
    (hL : Y.L.IsLattice E) :
    PlaneOK (cA σ).toRingHom (incM F Y.J) ((ε : ℤ) : AE F E) (incV F H.x) (incV F H.y) (incM F H.ι) := by
  have cc : ∀ a : AE F E, cA σ (cA σ a) = a := fun a => by
    induction a using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a e =>
      change a ⊗ₜ σ (σ e) = _
      rw [conj_conj hB]
  have orth : ∀ w : Fin n → E, (∀ u, form σ Y.J (H.ι *ᵥ u) w = 0) → ∀ z,
      bf (cA σ).toRingHom (incM F Y.J) (incM F H.ι *ᵥ z) (incV F w) = 0 := fun w hw z => by
    rw [vec_eq z, Matrix.mulVec_sum, bf_sum_l]
    exact Finset.sum_eq_zero fun j _ => by rw [Matrix.mulVec_smul, bf_smul_l, inc_mulVec, bf_inc, hw, map_zero, mul_zero]
  have sp : ∀ v : Fin n → E, ∃ (s t : E) (u : Fin k → E), v = s • H.x + H.ι *ᵥ u + t • H.y := fun v => by
    have hv : v ∈ Submodule.span E (Y.L : Set (Fin n → E)) := hL.span_eq_top ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨s, t, u, -, -, -, e⟩ := hH.split z hz
      exact ⟨s, t, u, e⟩
    | zero => exact ⟨0, 0, 0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨s, t, u, rfl⟩ := ha
      obtain ⟨s', t', u', rfl⟩ := hb
      exact ⟨s + s', t + t', u + u', by rw [Matrix.mulVec_add]; module⟩
    | smul a b _ hb =>
      obtain ⟨s, t, u, rfl⟩ := hb
      exact ⟨a * s, a * t, a • u, by rw [Matrix.mulVec_smul]; module⟩
  refine ⟨cc, by rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp, map_intCast _ _, fun i j => ?_,
    by rw [bf_inc, hH.xx, map_zero], by rw [bf_inc, hH.yy, map_zero], by rw [bf_inc, hH.xy, map_one],
    orth _ fun u => (hH.orth u).1, orth _ fun u => (hH.orth u).2, fun v => ?_, fun v hv => ?_⟩
  · change inclR (F := F) (AF F) (σ (Y.J j i)) = _ * inclR (F := F) (AF F) (Y.J i j)
    rw [hJ, map_mul, map_intCast]
  · choose s t u e using fun j : Fin n => sp (Pi.single j 1)
    refine ⟨∑ j, v j * inclR (F := F) (AF F) (s j), ∑ j, v j * inclR (F := F) (AF F) (t j), ∑ j, v j • incV F (u j), ?_⟩
    conv_lhs => rw [vec_eq v]
    rw [Finset.sum_smul, Finset.sum_smul, Matrix.mulVec_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec_smul, inc_mulVec, e j]
    funext i
    simp only [incV, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
    ring
  · have hu : IsUnit (incM F Y.J).det := by
      have := (isUnit_iff_ne_zero.2 hd).map (inclR (F := F) (E := E) (AF F))
      rwa [RingHom.map_det] at this
    have h0 : v ᵥ* incM F Y.J = 0 := funext fun j => by
      have := hv (Pi.single j 1)
      have e : (fun l => (cA σ).toRingHom ((Pi.single j 1 : Fin n → AE F E) l)) = Pi.single j 1 := funext fun l => by
        by_cases h : l = j <;> simp [Pi.single_apply, h]
      rw [bf, e, Matrix.dotProduct_mulVec] at this
      simpa using this
    have := congrArg (· ᵥ* (incM F Y.J)⁻¹) h0
    simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu] using this

theorem planeOK_herm {B : Base F E} (hB : B.IsGood σ) {Y : Spc F E n} {Y₁ : Spc F E k} {H : Plane E n k} {i₀ i₁ r s : ℕ}
    (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) (hY : Y.IsHerm σ B r s) :
    ∃ ε, PlaneOK (cA σ).toRingHom (incM F Y.J) ε (incV F H.x) (incV F H.y) (incM F H.ι) := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  refine ⟨_, planeOK hB hH 1 (fun i j => by simp [hY.herm]) (fun h0 => det_ne_of_sig (hY.sig w) ?_) hY.lat⟩
  have := RingHom.map_det (B.emb w).1 Y.J
  rw [h0, map_zero] at this
  exact this.symm

theorem planeOK_skew {B : Base F E} (hB : B.IsGood σ) {Y : Spc F E n} {Y₁ : Spc F E k} {H : Plane E n k} {i₀ i₁ r s : ℕ}
    (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) (hY : Y.IsSkew σ B r s) :
    ∃ ε, PlaneOK (cA σ).toRingHom (incM F Y.J) ε (incV F H.x) (incV F H.y) (incM F H.ι) := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  refine ⟨_, planeOK hB hH (-1) (fun i j => by simp [hY.skew]) (fun h0 => det_ne_of_sig (hY.sig w) ?_) hY.lat⟩
  have := RingHom.map_det (B.emb w).1 Y.J
  rw [h0, map_zero] at this
  rw [Matrix.det_smul]
  exact mul_eq_zero_of_right _ this.symm

def matH (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) : UA σ J →* Matrix (Fin n) (Fin n) (AE F E) :=
  (Units.coeHom _).comp (Subgroup.subtype _)

theorem matH_inj (J : Matrix (Fin n) (Fin n) E) : Function.Injective (matH σ J) := fun _ _ h => Subtype.ext (Units.ext h)

variable {Y : Spc F E n} {H : Plane E n k} {ε : AE F E}

theorem exists_scale (h : PlaneOK (cA σ).toRingHom (incM F Y.J) ε (incV F H.x) (incV F H.y) (incM F H.ι)) (t : ℕ) (ht : t ≠ 0) :
    ∃ m : UA σ Y.J, mat m *ᵥ incV F H.x = (t : AE F E) • incV F H.x ∧
      (t : AE F E) • (mat m *ᵥ incV F H.y) = incV F H.y ∧ ∀ z : Fin k → AE F E, mat m *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z := by
  have hu : IsUnit (t : AE F E) := by
    have := (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 ht : (t : E) ≠ 0)).map (inclR (F := F) (E := E) (AF F))
    rwa [map_natCast] at this
  obtain ⟨u, hu⟩ := hu
  obtain ⟨m, h0, h1, h2, h3⟩ := h.exists_lev u
  refine ⟨⟨m, h0⟩, hu ▸ h1, ?_, h3⟩
  change (t : AE F E) • (m.1 *ᵥ _) = _
  rw [h2, smul_smul, ← map_natCast (cA σ).toRingHom t, ← map_mul, ← hu, u.mul_inv, map_one, one_smul]

end PositivityTheory.Mix
