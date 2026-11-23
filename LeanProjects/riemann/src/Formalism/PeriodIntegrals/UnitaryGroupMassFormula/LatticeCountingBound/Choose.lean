import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.SepDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeSizeContinuity.LatticeIsometry

noncomputable section

open NumberField Matrix

namespace PI.UnitaryGroupMassFormula.LCG

namespace ChooseW

section Gen

variable {K : Type*} [Field K] {n : ℕ}

lemma ann_range (δ : Matrix (Fin n) (Fin n) K) (a : Fin n → K)
    (ha : ∀ z, δ *ᵥ z = 0 → a ⬝ᵥ z = 0) : ∃ t, a = t ᵥ* δ := by
  let ℓ : Module.Dual K (Fin n → K) :=
    { toFun := fun z => a ⬝ᵥ z
      map_add' := fun x y => dotProduct_add a x y
      map_smul' := fun c x => by simp [dotProduct_smul] }
  have hmem : ℓ ∈ (LinearMap.ker δ.mulVecLin).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro z hz
    exact ha z (by simpa using hz)
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hmem
  obtain ⟨φ, hφ⟩ := hmem
  refine ⟨fun j => φ (fun r => if j = r then 1 else 0), ?_⟩
  funext i
  have h1 := LinearMap.congr_fun hφ (fun r => if i = r then 1 else 0)
  rw [LinearMap.dualMap_apply] at h1
  have h2 : ℓ (fun r => if i = r then 1 else 0) = a i := by
    simp [ℓ, dotProduct]
  rw [h2, LinearMap.pi_apply_eq_sum_univ φ] at h1
  rw [← h1]
  simp [Matrix.vecMul, dotProduct, Matrix.mulVec, mul_comm]

lemma scaled_li {ι : Type*} {V : Type*} [AddCommGroup V] [Module K V] (d : ι → V)
    (hli : LinearIndependent K d) (m : ι → K) (hm : ∀ c, m c ≠ 0) :
    LinearIndependent K (fun c => m c • d c) := by
  have := hli.units_smul (fun c => Units.mk0 (m c) (hm c))
  convert this using 1
  funext c
  simp [Units.smul_def]

lemma scaled_span {ι : Type*} {V : Type*} [AddCommGroup V] [Module K V] (d : ι → V) (m : ι → K)
    (hm : ∀ c, m c ≠ 0) :
    Submodule.span K (Set.range d) ≤ Submodule.span K (Set.range fun c => m c • d c) := by
  rw [Submodule.span_le]
  rintro _ ⟨c, rfl⟩
  have : d c = (m c)⁻¹ • (m c • d c) := by rw [smul_smul, inv_mul_cancel₀ (hm c), one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

lemma basis_range (A : Matrix (Fin n) (Fin n) K) (k : ℕ) (hk : A.rank = k) :
    ∃ z : Fin k → Fin n → K, LinearIndependent K (fun c => A *ᵥ z c) ∧
      ∀ w, A *ᵥ w ∈ Submodule.span K (Set.range fun c => A *ᵥ z c) := by
  let R := LinearMap.range A.mulVecLin
  let bas := Module.finBasisOfFinrankEq K R hk
  have hz : ∀ c, ∃ z, A *ᵥ z = (bas c : Fin n → K) := fun c => by
    obtain ⟨z, hz⟩ := LinearMap.mem_range.mp (bas c).2
    exact ⟨z, by simpa using hz⟩
  choose z hz using hz
  have hspan : Submodule.span K (Set.range fun c => (bas c : Fin n → K)) = R := by
    rw [show (fun c => (bas c : Fin n → K)) = R.subtype ∘ bas from rfl, Set.range_comp,
      ← Submodule.map_span, bas.span_eq, Submodule.map_top, Submodule.range_subtype]
  refine ⟨z, ?_, ?_⟩
  · simp only [hz]
    exact bas.linearIndependent.map' R.subtype (Submodule.ker_subtype R)
  · intro w
    simp only [hz]
    rw [hspan]
    exact LinearMap.mem_range.mpr ⟨w, by simp⟩

lemma rank_pos (δ : Matrix (Fin n) (Fin n) K) (hδ : δ ≠ 0) : 1 ≤ δ.rank := by
  by_contra h
  have h0 : δ.rank = 0 := by omega
  have hbot : LinearMap.range δ.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h0
  have hz : Matrix.toLin' δ = 0 := by
    rw [Matrix.toLin'_apply']
    exact LinearMap.range_eq_bot.mp hbot
  exact hδ (Matrix.toLin'.injective (by rw [hz, map_zero]))

end Gen

section Star

variable {E : Type*} [Field E] [StarRing E] {n : ℕ}

def sv (w : Fin n → E) : Fin n → E := fun i => starRingEnd E (w i)

lemma sv_sv (w : Fin n → E) : sv (sv w) = w := by
  funext i; simp [sv]

lemma star_li {k : ℕ} (v : Fin k → Fin n → E) (h : LinearIndependent E v) :
    LinearIndependent E (fun a => sv (v a)) := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg i
  have h0 : ∑ a, starRingEnd E (g a) • v a = 0 := by
    funext j
    have := congrArg (starRingEnd E) (congrFun hg j)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sv, map_sum, map_mul,
      starRingEnd_self_apply, map_zero, Pi.zero_apply] at this ⊢
    rw [← this]
  have := h _ h0 i
  simpa using this

lemma star_span {k : ℕ} (v : Fin k → Fin n → E) (w : Fin n → E)
    (hw : sv w ∈ Submodule.span E (Set.range v)) :
    w ∈ Submodule.span E (Set.range fun a => sv (v a)) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp hw
  refine (Submodule.mem_span_range_iff_exists_fun E).mpr ⟨fun a => starRingEnd E (c a), ?_⟩
  rw [← sv_sv w, ← hc]
  funext j
  simp [sv, Finset.sum_apply, map_sum, map_mul]

end Star

lemma scale {E : Type} [Field E] [NumberField E] {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (hΛ : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) (w : Fin n → E) :
    ∃ m : ℤ, m ≠ 0 ∧ (m : E) • w ∈ Λ := by
  classical
  have hw : w ∈ Submodule.span E (Λ : Set (Fin n → E)) := hΛ ▸ Submodule.mem_top
  obtain ⟨N, f, g, hfg⟩ := Submodule.mem_span_set'.mp hw
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (L := E) (Finset.univ.image f)
  refine ⟨y, hy, ?_⟩
  rw [← hfg, Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hi : IsIntegral ℤ ((y : E) * f i) := by
    have := hint (f i) (Finset.mem_image_of_mem f (Finset.mem_univ i))
    simpa [zsmul_eq_mul] using this
  rw [smul_smul]
  have := Λ.smul_mem (⟨(y : E) * f i, hi⟩ : 𝓞 E) (g i).2
  convert this using 1
  exact (algebraMap_smul E _ _).symm

lemma hf_eq (I : Formalism.MainNotions.S.AutInst) (w z : Fin I.n → I.E) : hf I w z = (sv w ᵥ* I.J) ⬝ᵥ z := by
  simp only [hf, Formalism.UG.hform, dotProduct, vecMul, Finset.sum_mul, sv]
  rw [Finset.sum_comm]

end ChooseW

open ChooseW in
theorem choice_of_generators : Choose := by
  intro I y δ hδ
  obtain ⟨Λ, _, hΛs, hΛ0⟩ := PI.UnitaryGroupMassFormula.LSC.lattice_isometry I y
  have hΛ : PI.LatCountG.latSet I y = (Λ : Set (Fin I.n → I.E)) := hΛ0
  have hJ : IsUnit I.J.det := isUnit_iff_ne_zero.mpr I.J_det
  set k := δ.rank with hk
  have hk1 : 1 ≤ k := rank_pos δ hδ

  obtain ⟨z, hzli, hzsp⟩ := basis_range δ k hk.symm
  have hsc : ∀ c, ∃ m : ℤ, m ≠ 0 ∧ ((m : I.E) • z c) ∈ Λ := fun c => scale Λ hΛs (z c)
  choose mu hmu0 hmuΛ using hsc

  set B : Matrix (Fin I.n) (Fin I.n) I.E := (δ * I.J⁻¹)ᵀ with hB
  have hBr : B.rank = k := by
    rw [hB, Matrix.rank_transpose, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnit_nonsing_inv_det I.J hJ)]
  obtain ⟨t, htli, htsp⟩ := basis_range B k hBr
  have hsc' : ∀ a, ∃ m : ℤ, m ≠ 0 ∧ ((m : I.E) • sv (B *ᵥ t a)) ∈ Λ := fun a => scale Λ hΛs _
  choose mb hmb0 hmbΛ using hsc'
  have hmu0' : ∀ c, ((mu c : ℤ) : I.E) ≠ 0 := fun c => Int.cast_ne_zero.mpr (hmu0 c)
  have hmb0' : ∀ a, ((mb a : ℤ) : I.E) ≠ 0 := fun a => Int.cast_ne_zero.mpr (hmb0 a)

  have hperpB : ∀ s w, δ *ᵥ w = 0 → ((B *ᵥ s) ᵥ* I.J) ⬝ᵥ w = 0 := by
    intro s w hw
    rw [hB, Matrix.mulVec_transpose, Matrix.vecMul_vecMul, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hJ, Matrix.mul_one, ← Matrix.dotProduct_mulVec, hw, dotProduct_zero]
  refine ⟨k, fun c => ((mu c : ℤ) : I.E) • z c, fun a => ((mb a : ℤ) : I.E) • sv (B *ᵥ t a), hk1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c; rw [hΛ]; exact hmuΛ c
  · simp only [Matrix.mulVec_smul]
    exact scaled_li (fun c => δ *ᵥ z c) hzli (fun c => ((mu c : ℤ) : I.E)) hmu0'
  · intro w
    simp only [Matrix.mulVec_smul]
    exact scaled_span (fun c => δ *ᵥ z c) (fun c => ((mu c : ℤ) : I.E)) hmu0' (hzsp w)
  · intro a; rw [hΛ]; exact hmbΛ a
  · exact scaled_li (fun a => sv (B *ᵥ t a)) (star_li (fun a => B *ᵥ t a) htli)
      (fun a => ((mb a : ℤ) : I.E)) hmb0'
  · intro a w hw
    rw [hf_eq]
    have hs : sv (((mb a : ℤ) : I.E) • sv (B *ᵥ t a)) = ((mb a : ℤ) : I.E) • (B *ᵥ t a) := by
      funext i; simp [sv]
    rw [hs, Matrix.smul_vecMul, smul_dotProduct, hperpB _ _ hw, smul_zero]
  · intro w hw
    have hann : ∀ z', δ *ᵥ z' = 0 → (sv w ᵥ* I.J) ⬝ᵥ z' = 0 := fun z' hz' => by
      rw [← hf_eq]; exact hw z' hz'
    obtain ⟨s, hs⟩ := ann_range δ _ hann
    have hsv : sv w = B *ᵥ s := by
      have : sv w = (sv w ᵥ* I.J) ᵥ* I.J⁻¹ := by
        rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hJ, Matrix.vecMul_one]
      rw [this, hs, Matrix.vecMul_vecMul, hB, Matrix.mulVec_transpose]
    have h1 : sv w ∈ Submodule.span I.E (Set.range fun a => B *ᵥ t a) := hsv ▸ htsp s
    exact scaled_span (fun a => sv (B *ᵥ t a)) (fun a => ((mb a : ℤ) : I.E)) hmb0'
      (star_span (fun a => B *ᵥ t a) w h1)

end PI.UnitaryGroupMassFormula.LCG
