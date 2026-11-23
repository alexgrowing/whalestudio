import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BesselFormsTrivialNeBot
import Formalism.PeriodIntegrals.BesselMapUniq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.UnitaryOfBlockWMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupSecondKindCoordinatesNearOne
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothInExponentialCoordsIffFirstSecondKind
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ContDiffOnIffLocalExtension

noncomputable section

open Matrix Topology Filter
open scoped ContDiff

namespace GlobalTheory.BesselMapOne

theorem contDiff_list_prod_ofFn {F E : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedRing E]
    [NormedAlgebra ℝ E] {N : ℕ} (g : Fin N → F → E) (hg : ∀ i, ContDiff ℝ ∞ (g i)) :
    ContDiff ℝ ∞ fun t => (List.ofFn fun i => g i t).prod := by
  induction N with
  | zero => simpa using contDiff_const
  | succ N ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    exact (hg 0).mul (ih _ fun i => hg i.succ)

theorem exists_chart {E : Type} [NormedRing E] [NormedAlgebra ℝ E] [FiniteDimensional ℝ E] (σ : E →ₗ[ℝ] E)
    (hσ : ∀ a, σ (σ a) = a) (hm : ∀ a b, σ (a * b) = σ b * σ a) (h1 : σ 1 = 1) :
    ∃ (N : ℕ) (Y : Fin N → E) (Ψ : E → Fin N → ℝ), (∀ i, σ (Y i) = -Y i) ∧ ContDiffAt ℝ ∞ Ψ 1 ∧
      ∀ᶠ a in 𝓝 (1 : E), σ a * a = 1 → (List.ofFn fun i => NormedSpace.exp (Ψ a i • Y i)).prod = a := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : NormedAlgebra ℚ E := NormedAlgebra.restrictScalars ℚ ℝ E
  let S : Submodule ℝ E := LinearMap.ker (σ + LinearMap.id)
  have hS : ∀ X, X ∈ S ↔ σ X = -X := fun X => by simp [S, add_eq_zero_iff_eq_neg]
  let b := Module.finBasis ℝ S
  let e : Fin (Module.finrank ℝ S) → E := fun i => b i
  have hli : LinearIndependent ℝ e := b.linearIndependent.map' S.subtype S.ker_subtype
  have he : ∀ i, σ (e i) = -e i := fun i => (hS _).1 (b i).2
  have hsp : ∀ X, σ X = -X → X ∈ Submodule.span ℝ (Set.range e) := fun X hX => by
    have h := congrArg S.subtype (b.sum_repr ⟨X, (hS X).2 hX⟩)
    rw [map_sum] at h
    simp only [map_smul, Submodule.subtype_apply] at h
    rw [← h]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hexp : ∀ a, σ (NormedSpace.exp a) = NormedSpace.exp (σ a) := fun a => by
    have hp : ∀ n : ℕ, σ (a ^ n) = σ a ^ n := fun n => by
      induction n with
      | zero => simpa using h1
      | succ n ih => rw [pow_succ, hm, ih, pow_succ']
    have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) a).map σ.toAddMonoidHom σ.continuous_of_finiteDimensional
    refine h2.unique ?_
    convert NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (σ a) using 1
    funext n
    simp [hp]
  set Θ : (Fin _ → ℝ) → E := fun t => (List.ofFn fun i => NormedSpace.exp (t i • e i)).prod with hΘ
  have hU : ∀ t, σ (Θ t) * Θ t = 1 ∧ Θ t * σ (Θ t) = 1 := fun t =>
    GlobalTheory.UnitaryChart.unitary_list_prod σ hm h1 _ (fun u hu => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
      rw [hexp, map_smul, he, smul_neg, ← NormedSpace.exp_add_of_commute (Commute.refl _).neg_left,
        ← NormedSpace.exp_add_of_commute (Commute.refl _).neg_right]
      simp)
  have hC : ContDiff ℝ ∞ Θ := by
    refine contDiff_list_prod_ofFn (fun i (t : Fin _ → ℝ) => NormedSpace.exp (t i • e i)) fun i => ?_
    exact GlobalTheory.SmoothForms.SecondKind.contDiff_exp.comp ((contDiff_apply ℝ ℝ i).smul contDiff_const)
  let T : (Fin _ → ℝ) →L[ℝ] E :=
    ∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (e i)).comp (ContinuousLinearMap.proj i)
  have hT : ∀ t, T t = ∑ i, t i • e i := fun t => by simp [T]
  obtain ⟨h0, hD⟩ : Θ 0 = 1 ∧ HasStrictFDerivAt Θ T 0 :=
    GlobalTheory.UnitaryChart.hasStrictFDerivAt_ofFn_prod _ (fun i (t : Fin _ → ℝ) => NormedSpace.exp (t i • e i)) _ (fun i =>
      ⟨by simp, HasStrictFDerivAt.comp (0 : Fin _ → ℝ) (g := fun s : ℝ => NormedSpace.exp (s • e i))
        (by simpa using (hasStrictDerivAt_exp_smul_const (𝕂 := ℝ) (e i) 0).hasStrictFDerivAt)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin _ => ℝ) i).hasStrictFDerivAt⟩)
  obtain ⟨P, hP1, hP2, hP3⟩ := GlobalTheory.UnitaryChart.exists_skew_coord σ e hσ hli he hsp
  have hΦ : ContDiffAt ℝ ∞ (fun t => P (Θ t)) 0 := (P.contDiff.comp hC).contDiffAt
  have hΦ' : HasFDerivAt (fun t => P (Θ t))
      ((ContinuousLinearEquiv.refl ℝ (Fin (Module.finrank ℝ S) → ℝ) : (Fin (Module.finrank ℝ S) → ℝ) →L[ℝ] (Fin (Module.finrank ℝ S) → ℝ))) 0 := by
    refine (P.hasStrictFDerivAt.comp 0 hD).hasFDerivAt.congr_fderiv ?_
    ext1 t
    simp [hT, hP1]
  have hP0 : P 1 = 0 := hP2 _ h1
  have hΦ0 : P (Θ 0) = 0 := by rw [h0, hP0]
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have p1 := hΦ.to_localInverse hΦ' hn
  have p2 := hΦ.localInverse_apply_image hΦ' hn
  have p3 : ∀ᶠ y in 𝓝 (P (Θ 0)), P (Θ (hΦ.localInverse hΦ' hn y)) = y :=
    HasStrictFDerivAt.eventually_right_inverse (hΦ.hasStrictFDerivAt' hΦ' hn)
  simp only [hΦ0] at p1 p2 p3
  set Ψ := hΦ.localInverse hΦ' hn
  have hσc : Continuous σ := σ.continuous_of_finiteDimensional
  have hnear : ∀ᶠ m in 𝓝 (1 : E), ‖1 - σ m‖ ≤ 1 / 2 := by
    have : ContinuousAt (fun m => ‖1 - σ m‖) 1 := by fun_prop
    exact this.eventually_le_const (by simp [h1])
  have hPt : Tendsto P (𝓝 1) (𝓝 0) := hP0 ▸ P.continuous.tendsto 1
  have ht : Tendsto (fun a => Θ (Ψ (P a))) (𝓝 1) (𝓝 1) := by
    have := (hC.continuous.tendsto (Ψ 0)).comp p1.continuousAt
    rw [p2, h0] at this
    exact this.comp hPt
  refine ⟨_, e, fun a => Ψ (P a), he, ContDiffAt.comp (g := Ψ) 1 (by rwa [hP0]) P.contDiff.contDiffAt, ?_⟩
  filter_upwards [hPt.eventually p3, hnear, ht.eventually hnear] with a q1 q2 q3 ha
  haveI : IsArtinianRing E := IsArtinianRing.of_finite ℝ E
  exact GlobalTheory.UnitaryChart.eq_of_skew_eq (hU _).1 (mul_eq_one_comm.1 ha) (hP3 _ _ q1) q3 q2

section Smooth

open Formalism.MainNotions.S Formalism.L2.Theta Formalism.QuantumDeterminants GlobalTheory.SmVec

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {J : Matrix (Fin n) (Fin n) ℂ}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem exists_ext_at (hH : Jᴴ = J) (h2 : J * J = 1) (hσ : IsURepOn (UH J) σ) {v : H} (hv : v ∈ smSub J σ)
    {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ UH J) :
    ∃ F : (Fin n → Fin n → ℂ) → H, ContDiffAt ℝ ∞ F (Matrix.of.symm u) ∧
      ∀ᶠ g in 𝓝 u, g ∈ UH J → σ g v = F (Matrix.of.symm g) := by
  have hJ : IsUnit J := IsUnit.of_mul_eq_one _ h2
  let s : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun x => J * xᴴ * J
      map_add' := fun x y => by rw [conjTranspose_add, mul_add, add_mul]
      map_smul' := fun c x => by simp [conjTranspose_smul] }
  have hs : ∀ x, s x = J * xᴴ * J := fun _ => rfl
  have hJJ : ∀ x : Matrix (Fin n) (Fin n) ℂ, J * (J * x) = x := fun x => by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  obtain ⟨N, Y, Ψ, hY, hΨ, hE⟩ := exists_chart s
    (fun a => by simp only [hs, conjTranspose_mul, conjTranspose_conjTranspose, hH, Matrix.mul_assoc, hJJ, h2,
      Matrix.mul_one])
    (fun a b => by simp only [hs, conjTranspose_mul, Matrix.mul_assoc, hJJ]) (by simp [hs, h2])
  have hYl : ∀ i, Y i ∈ lieG J := fun i => by
    have := congrArg (J * ·) (hY i)
    simp only [hs, Matrix.mul_assoc, hJJ, Matrix.mul_neg] at this
    show _ + _ = 0
    rw [this, neg_add_cancel]
  have hun : ∀ g ∈ UH J, s g * g = 1 := fun g hg => by
    have hg' : gᴴ * J * g = J := hg
    rw [hs, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', h2]
  let A : (Fin n → Fin n → ℂ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun p => u⁻¹ * Matrix.of p
      map_add' := fun _ _ => Matrix.mul_add _ _ _
      map_smul' := fun c p => Matrix.mul_smul _ c (Matrix.of p) }
  have hd := (Matrix.isUnit_iff_isUnit_det u).1 (isUnit_of_mem_UH hJ hu)
  have hA : A (Matrix.of.symm u) = 1 := nonsing_inv_mul _ hd
  have h0 := ((σ u).restrictScalars ℝ).contDiff.comp (hv N Y hYl)
  refine ⟨fun p => σ u (σ (List.ofFn fun i => NormedSpace.exp (Ψ (A p) i • Y i)).prod v), ?_, ?_⟩
  · exact h0.contDiffAt.comp _ (ContDiffAt.comp (g := Ψ) _ (by rwa [hA])
      (LinearMap.toContinuousLinearMap A).contDiff.contDiffAt)
  · have ht : Tendsto (fun g => u⁻¹ * g) (𝓝 u) (𝓝 1) := by
      have := (continuous_const (y := u⁻¹).matrix_mul continuous_id).tendsto u
      rwa [id, nonsing_inv_mul _ hd] at this
    filter_upwards [ht.eventually hE] with g q hg
    have hm : u⁻¹ * g ∈ UH J := by
      have := GlobalTheory.GardingVec.list_prod_mem (G := J) [u⁻¹, g] (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨inv_mem_UH hJ hu, hg⟩)
      rwa [List.prod_cons, List.prod_singleton] at this
    have q' := q (hun _ hm)
    show _ = σ u (σ (List.ofFn fun i => NormedSpace.exp (Ψ (u⁻¹ * g) i • Y i)).prod v)
    refine Eq.trans ?_ (congrArg (fun m => σ u (σ m v)) q').symm
    show _ = σ u (σ (u⁻¹ * g) v)
    rw [← rep_mul hσ hu hm, mul_nonsing_inv_cancel_left _ _ hd]

theorem contDiff_entries {k : ℕ} (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ∞ fun t : Fin k → ℝ =>
      (Matrix.of.symm (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod : Fin n → Fin n → ℂ) := by
  let B : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Fin n → Fin n → ℂ) :=
    { toFun := fun m => Matrix.of.symm m
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact (LinearMap.toContinuousLinearMap B).contDiff.comp (GlobalTheory.GardingVec.contDiff_expProd Xs)

end

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem smoothOnH_iff_mem (hH : Jᴴ = J) (h2 : J * J = 1) (hσ : IsURepOn (UH J) σ) (v : H) :
    PI.UpqRep.SmoothOnH J (fun g => σ g v) ↔ v ∈ smSub J σ := by
  have hJ : IsUnit J := IsUnit.of_mul_eq_one _ h2
  refine (GlobalTheory.UnitaryRetraction.contDiffOn_iff_local_extension hH h2 (fun g => σ g v)).symm.trans ⟨fun h k Xs hX => ?_,
    fun hv u hu => ?_⟩
  · exact h.comp_contDiff (contDiff_entries Xs) fun t => expProd_mem_UH hJ hX t
  · obtain ⟨F, hF, hE⟩ := exists_ext_at hH h2 hσ hv hu
    refine hF.contDiffWithinAt.congr_of_eventuallyEq ?_ (hE.self_of_nhds hu)
    filter_upwards [nhdsWithin_le_nhds hE, self_mem_nhdsWithin] with g q hg using q hg

end Smooth

section Frame

open PI.UpqRep PI.HwUniqW GlobalTheory.RealBessel

variable {k r : ℕ}

def colW (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin k) ℂ := fun i a => if i = bl k r a then 1 else 0

def colE (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin r) ℂ := fun i a => if i = eI k r a then 1 else 0

theorem eI_inj {a b : Fin r} : eI k r a = eI k r b ↔ a = b := by simp [eI, Fin.ext_iff]

theorem colW_mulVec (x : Fin (2 * r + k + 1) → ℂ) (a : Fin k) :
    (((colW k r)ᴴ * Hpk k r) *ᵥ x) a = x (bl k r a) := by
  rw [← mulVec_mulVec, mulVec, dotProduct]
  simp [colW, apply_ite, Hpk_mulVec_apply, piI_in (inB_bl a), epsI_in (inB_bl a)]

theorem colE_mulVec (x : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    (((colE k r)ᴴ * Hpk k r) *ᵥ x) a = x (esI k r a) := by
  have h1 : piI k r (eI k r a) = esI k r a := Fin.ext (by rw [piI_val, if_neg (by simp only [eI]; omega)]; rfl)
  have h2 : epsI k r (eI k r a) = 1 := if_neg (by simp only [eI]; omega)
  rw [← mulVec_mulVec, mulVec, dotProduct]
  simp [colE, apply_ite, Hpk_mulVec_apply, h1, h2]

theorem colE_apply (a : Fin r → ℂ) (j : Fin r) : (colE k r *ᵥ a) (eI k r j) = a j := by
  simp [colE, mulVec, dotProduct, eI_inj]

theorem colE_apply_ge (a : Fin r → ℂ) {i : Fin (2 * r + k + 1)} (hi : r ≤ i.val) : (colE k r *ᵥ a) i = 0 := by
  rw [mulVec, dotProduct]
  refine Finset.sum_eq_zero fun j _ => ?_
  have : i ≠ eI k r j := fun h => by have := congrArg Fin.val h; simp only [eI] at this; omega
  simp [colE, this]

theorem colE_col (j : Fin r) : (fun i => colE k r i j) = bvec (eI k r j) := funext fun i => (bvec_apply _ _).symm

variable {z : Fin (2 * r + k + 1) → ℂ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}

theorem frame_perp (hg : g ∈ UH (Hpk k r)) (x : Fin (2 * r + k + 1) → ℂ) (a : Fin k) :
    (((g * colW k r)ᴴ * Hpk k r) *ᵥ (g *ᵥ x)) a = x (bl k r a) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  rw [mulVec_mulVec, conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', colW_mulVec]

theorem frame_perp_bvec (hg : g ∈ UH (Hpk k r)) {j : Fin (2 * r + k + 1)} (hj : ¬ InB k r j) :
    ((g * colW k r)ᴴ * Hpk k r) *ᵥ (g *ᵥ bvec j) = 0 := funext fun a => by
  rw [frame_perp hg, bvec_apply, if_neg (ne_of_inB (inB_bl a) hj)]; rfl

theorem not_inB_eI (a : Fin r) : ¬ InB k r (eI k r a) := by simp only [InB, eI]; omega

theorem not_inB_esI (a : Fin r) : ¬ InB k r (esI k r a) := by simp only [InB, esI]; omega

theorem not_inB_last : ¬ InB k r (wI k r (Fin.last k)) := by simp [InB, wI]

theorem besselFrame_translated_perp_of_isFrame (hg : IsFrameW k r z g) : ((g * colW k r)ᴴ * Hpk k r) *ᵥ z = 0 := by
  rw [← hg.2.2, mulVec_smul, mulVec_smul, frame_perp_bvec hg.1 not_inB_last, smul_zero]

theorem isFrame (hg : IsFrameW k r z g) (hz : inWb k r z) (hT : 0 < Tz k r z) :
    IsFrame (Hpk k r) 1 (g * colW k r) (colE k r) z where
  herm := Hpk_conjTranspose
  unit := IsUnit.of_mul_eq_one _ Hpk_mul_self
  unit₀ := isUnit_one
  codim := by omega
  gram := by
    ext a b
    have := frame_perp hg.1 (fun i => colW k r i b) a
    rw [show colW k r (bl k r a) b = (1 : Matrix (Fin k) (Fin k) ℂ) a b by simp [colW, one_apply, blockIndex_injective.eq_iff]]
      at this
    exact this
  e_indep := Matrix.mulVec_injective_iff.1 fun a b h => funext fun j => by
    rw [← colE_apply (k := k) a, h, colE_apply]
  e_iso := by
    ext a b
    have := colE_mulVec (fun i => colE k r i b) a
    rw [show colE k r (esI k r a) b = 0 from if_neg (by simp only [esI, eI, Fin.ext_iff]; omega)] at this
    exact this
  e_perp := by
    ext a b
    have := congrFun (frame_perp_bvec hg.1 (not_inB_eI b)) a
    rw [(hg.2.1 b).1, ← colE_col] at this
    exact this
  z_perpF := besselFrame_translated_perp_of_isFrame hg
  z_perpE := funext fun a => (colE_mulVec z a).trans (hz _ (Or.inr (by simp only [esI]; omega)))
  z_ne := fun h => by
    have h' : herm (Hpk k r) z z = 0 := h
    simp [Tz, h'] at hT

theorem mem_Nset {u : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hu : u ∈ unipRad (Hpk k r) (colE k r)) :
    u ∈ Formalism.QuantumDeterminants.Nset k r := by
  refine ⟨hu.1, fun a i hi => ?_, fun i j h1 h2 h3 => ?_⟩
  · obtain ⟨c, hc, h⟩ := hu.2.1 a
    have h' := congrFun h i
    rw [colE_col, mulVec_bvec_apply, Matrix.sub_apply, Matrix.one_apply, sub_eq_iff_eq_add] at h'
    have h0 : (colE k r *ᵥ c) i = 0 := by
      by_cases hr : i.val < r
      · exact (colE_apply c ⟨i.val, hr⟩).trans (hc _ hi)
      · exact colE_apply_ge c (by omega)
    rw [h0, zero_add] at h'
    exact h'
  · obtain ⟨c, h⟩ := hu.2.2 (bvec j) (funext fun a => by
      rw [colE_mulVec, bvec_apply, if_neg (by simp only [esI, Fin.ext_iff]; omega)]; rfl)
    have h' := congrFun h i
    rwa [mulVec_bvec_apply, Matrix.sub_apply, Matrix.one_apply, sub_eq_iff_eq_add, colE_apply_ge c h3, zero_add] at h'

theorem isCharWith (hz : inWb k r z) (c : Fin r → ℂ) :
    IsCharWith (Hpk k r) (colE k r) z c (PI.BesselMapUniq.psiGen k r z c) := by
  intro u _ a ha
  have key : ∀ j, PI.BesselMapUniq.ellA k r z u j = a j j := fun j => by
    have h := congrFun (ha j) (eI k r j)
    rw [colE_apply] at h
    rw [← h]
    unfold PI.BesselMapUniq.ellA
    split_ifs with hj
    · rw [show j.succ = Fin.castSucc ⟨j.val + 1, hj⟩ from rfl, flagVec, Fin.snoc_castSucc, colE_col, mulVec_bvec_apply,
        Matrix.sub_apply, Matrix.one_apply_ne (by simp [eI, Fin.ext_iff]), sub_zero]
      rfl
    · rw [show j.succ = Fin.last r from Fin.ext (by simp; omega), flagVec, Fin.snoc_last, sub_mulVec, one_mulVec,
        Pi.sub_apply, hz _ (Or.inl j.isLt), sub_zero]
      rfl
  simp only [PI.BesselMapUniq.psiGen, key]

theorem emb_eq (hg : IsFrameW k r z g) {x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {h : Matrix (Fin k) (Fin k) ℂ} (hx : x ∈ UH (Hpk k r)) (hE : IsEmb (Hpk k r) (g * colW k r) x h) :
    x ∈ Formalism.QuantumDeterminants.UWset k r z ∧ x = g * blockW k r h * g⁻¹ := by
  have fix : ∀ j, ¬ InB k r j → x *ᵥ (g *ᵥ bvec j) = g *ᵥ bvec j := fun j hj => hE.2 _ (frame_perp_bvec hg.1 hj)
  have fix' : ∀ j, ¬ InB k r j → (g⁻¹ * x * g) *ᵥ bvec j = bvec j := fun j hj => by
    rw [← mulVec_mulVec, ← mulVec_mulVec, fix j hj, mulVec_mulVec, inv_mul_UH' hg.1, one_mulVec]
  refine ⟨⟨hx, fun a => ⟨?_, ?_⟩, hE.2 _ (besselFrame_translated_perp_of_isFrame hg)⟩, ?_⟩
  · have := fix _ (not_inB_eI a)
    rwa [(hg.2.1 a).1] at this
  · have := fix _ (not_inB_esI a)
    rwa [(hg.2.1 a).2] at this
  · have hb := (fix_block (mul_mem_UH (mul_mem_UH (inv_mem_UH hg.1) hx) hg.1)
      ⟨fun a => ⟨fix' _ (not_inB_eI a), fix' _ (not_inB_esI a)⟩, fix' _ not_inB_last⟩).2
    have h1 : g⁻¹ * x * g * colW k r = colW k r * h := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, hE.1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, inv_mul_UH' hg.1,
        Matrix.one_mul]
    have h2 : PI.HwUniqW.sub k r (g⁻¹ * x * g) = h := by
      ext a b
      have := congrFun (congrFun h1 (bl k r a)) b
      rw [Matrix.mul_apply, Matrix.mul_apply] at this
      simpa [colW, blockIndex_injective.eq_iff, PI.HwUniqW.sub] using this
    rw [← h2, ← hb]
    simp only [← Matrix.mul_assoc, mul_inv_UH hg.1, Matrix.one_mul]
    rw [Matrix.mul_assoc, mul_inv_UH hg.1, Matrix.mul_one]

end Frame

section Dual

open PI.UpqRep PI.HwUniqW GlobalTheory.RealBessel

variable {k : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

def contra (ρ : Matrix (Fin k) (Fin k) ℂ → (W →L[ℂ] W)) (h : Matrix (Fin k) (Fin k) ℂ) :
    Module.End ℂ (Module.Dual ℂ W) := (ρ hᴴ : W →ₗ[ℂ] W).dualMap

theorem mem_UH_one {h : Matrix (Fin k) (Fin k) ℂ} : h ∈ Formalism.QuantumDeterminants.UH (1 : Matrix (Fin k) (Fin k) ℂ) ↔ hᴴ * h = 1 := by
  show hᴴ * 1 * h = 1 ↔ _
  rw [Matrix.mul_one]

theorem adj_mem {h : Matrix (Fin k) (Fin k) ℂ} (hh : hᴴ * h = 1) : hᴴ ∈ UJset (allPos k) := by
  rw [mem_UJset_allPos, conjTranspose_conjTranspose]
  exact mul_eq_one_comm.1 hh

theorem isContIrred_contra {u : Fin k → ℝ} {ρ : Matrix (Fin k) (Fin k) ℂ → (W →L[ℂ] W)} (hρ : IsHCTypeU k u ρ) :
    IsContIrred (Formalism.QuantumDeterminants.UH 1) (contra ρ) := by
  obtain ⟨-, hf, ⟨⟨h1, hm⟩, -, hc⟩, -, -, hi, -⟩ := hρ
  refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun w l => ?_, fun U hU => ?_⟩
  · ext l x
    simp [contra, h1]
  · ext l x
    simp [contra, hm _ (adj_mem (mem_UH_one.1 hb)) _ (adj_mem (mem_UH_one.1 ha))]
  · obtain ⟨x, rfl⟩ := (Module.evalEquiv ℂ W).surjective l
    have := w.continuous_of_finiteDimensional.comp_continuousOn ((hc x).comp
      (continuous_id.matrix_conjTranspose).continuousOn fun h hh => adj_mem (mem_UH_one.1 hh))
    exact this
  · have hs : IsKStableOn (allPos k) ρ U.dualCoannihilator := fun g hg v hv => by
      rw [Submodule.mem_dualCoannihilator] at hv ⊢
      intro l hl
      have hg' : g * gᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hg.1
      have := hv _ (hU gᴴ (mem_UH_one.2 (by rwa [conjTranspose_conjTranspose])) l hl)
      simpa [contra] using this
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := U)]
    rcases hi _ le_top hs with h | h
    · rw [h]; exact Or.inr Submodule.dualAnnihilator_bot
    · rw [h]; exact Or.inl Submodule.dualAnnihilator_top

end Dual

section Main

open PI.UpqRep PI.HwUniqW GlobalTheory.RealBessel PI.BesselMapUniq GlobalTheory.SmVec

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}

theorem dsigW_eq (l : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (v : H) :
    dsigW (k := k) (r := r) σ l v = l.foldr (Formalism.L2.Theta.dRep σ) v := by
  induction l with
  | nil => rfl
  | cons X l ih => rw [dsigW, ih]; rfl

theorem rep_of_isDSHpk {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} (h : IsDSHpk k r ε lam σ) :
    CompleteSpace H ∧ Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (Hpk k r)) σ ∧ Formalism.MainNotions.S.IsIrredOn (Formalism.QuantumDeterminants.UH (Hpk k r)) σ := by
  obtain ⟨P, ⟨⟨hP, hG⟩, -⟩, hc, -, hU, hI, -⟩ := h
  have hd := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have e : trRep (fun g => σ (P⁻¹ * g * P)) P = σ := funext fun g => by
    unfold trRep
    congr 1
    simp only [← Matrix.mul_assoc, nonsing_inv_mul _ hd, Matrix.one_mul]
    rw [Matrix.mul_assoc, nonsing_inv_mul _ hd, Matrix.mul_one]
  exact ⟨hc, e ▸ isURepOn_trRep (ε := ε) hP hG hU, e ▸ isIrredOn_trRep (ε := ε) hP hG hI⟩

theorem exists_form (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (Hpk k r)) σ) {z : Fin (2 * r + k + 1) → ℂ}
    {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : IsFrameW k r z g)
    {ψ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ} (hψ : ψ 1 = 1) {u : Fin k → ℝ}
    {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (W →L[ℂ] W)}
    (hπ : IsHCTypeU k u fun h => π (g * blockW k r h * g⁻¹)) {B : H → W}
    (hB : IsBesselMapSm (k := k) (r := r) z ψ σ π B) :
    ∃ β ∈ besselForms (Hpk k r) 1 (g * colW k r) (colE k r) ψ σ (contra fun h => π (g * blockW k r h * g⁻¹))
      (smSub (Hpk k r) σ), ∀ l x, β l x = l (B x) := by
  have hs : ∀ v, v ∈ smoothVecs (k := k) (r := r) σ ↔ v ∈ smSub (Hpk k r) σ :=
    smoothOnH_iff_mem Hpk_conjTranspose Hpk_mul_self hσ
  obtain ⟨-, hf, ⟨⟨h1, hm⟩, -, -⟩, -⟩ := hπ
  obtain ⟨ha, hc, he, C, S, hS, hC⟩ := hB
  have hπ1 : π 1 = 1 := by simpa only [blockW_one, Matrix.mul_one, mul_inv_UH hg.1] using h1
  let L : smSub (Hpk k r) σ →ₗ[ℂ] W :=
    { toFun := fun x => B x
      map_add' := fun x y => ha _ ((hs _).2 x.2) _ ((hs _).2 y.2)
      map_smul' := fun c x => hc c _ ((hs _).2 x.2) }
  refine ⟨L.dualMap, ⟨fun w => ?_, fun h hh x hx hE w v y hy => ?_, fun m hm w v y hy => ?_⟩, fun _ _ => rfl⟩
  · obtain ⟨l, hl⟩ := LinearMap.exists_extend (L.dualMap w)
    have hl' : ∀ x : smSub (Hpk k r) σ, l x = w (B x) := fun x => LinearMap.congr_fun hl x
    refine ⟨l, ⟨S, ‖LinearMap.toContinuousLinearMap w‖ * C, hS, fun v hv => ?_⟩, hl'⟩
    rw [hl' ⟨v, hv⟩, mul_assoc]
    refine ((LinearMap.toContinuousLinearMap w).le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    simpa only [dsigW_eq] using hC v ((hs v).2 hv)
  · obtain ⟨hW, rfl⟩ := emb_eq hg hx hE
    have e := he _ hW 1 (mem_Nset (k := k) (r := r) ⟨one_mem_UH, fun _ => ⟨0, fun _ _ => rfl, by simp⟩,
      fun _ _ => ⟨0, by simp⟩⟩) v ((hs _).2 v.2)
    rw [Matrix.mul_one, hψ, one_smul, ← hy] at e
    have hh' := mem_UH_one.1 hh
    have e2 := hm _ (adj_mem hh') _ (mem_UJset_allPos.2 hh')
    rw [hh'] at e2
    have e3 := congrArg (fun T : W →L[ℂ] W => T (B v)) (h1.symm.trans e2)
    show w (π (g * blockW k r hᴴ * g⁻¹) (B y)) = w (B v)
    rw [e]
    exact congrArg w e3.symm
  · have e := he 1 ⟨one_mem_UH, fun _ => ⟨one_mulVec _, one_mulVec _⟩, one_mulVec _⟩ m (mem_Nset hm) v ((hs _).2 v.2)
    rw [Matrix.one_mul, hπ1, ← hy] at e
    show w (B y) = ψ m * w (B v)
    rw [e, map_smul]
    rfl

theorem exists_gen {V : Type} [AddCommGroup V] [Module ℂ V] {S : Submodule ℂ V} (h : Module.rank ℂ S ≤ 1) :
    ∃ β : V, ∀ x ∈ S, ∃ s : ℂ, s • β = x := by
  obtain ⟨β, hβ⟩ := rank_le_one_iff.1 h
  exact ⟨β, fun x hx => (hβ ⟨x, hx⟩).imp fun _ q => congrArg Subtype.val q⟩

theorem besselMapUniq_of_besselUniqueness :
    GlobalTheory.Published.BesselUniquenessReal → PI.BesselMapUniq.BesselMapUniq := by
  intro hJ k r ε lam H _ _ σ z c u W _ _ π _ hσ hz hT hc hπ B₁ B₂ h₁ h₂
  obtain ⟨hH, hU, hI⟩ := rep_of_isDSHpk hσ
  obtain ⟨g, hg, hπ⟩ := hπ
  have := hπ.2.1
  have hχ := isCharWith hz c
  have hψ : psiGen k r z c 1 = 1 := by
    rw [hχ 1 ⟨one_mem_UH, fun _ => ⟨0, fun _ _ => rfl, by simp⟩, fun _ _ => ⟨0, by simp⟩⟩ 0 (fun _ => by simp)]
    simp
  have hr := hJ _ _ _ _ _ _ _ _ (isFrame hg hz hT) _ ⟨c, hc, hχ⟩ H σ hU hI _ _ (isContIrred_contra hπ)
  obtain ⟨β₁, m₁, e₁⟩ := exists_form hU hg hψ hπ h₁
  obtain ⟨β₂, m₂, e₂⟩ := exists_form hU hg hψ hπ h₂
  obtain ⟨β, hβ⟩ := exists_gen hr
  obtain ⟨s₁, r₁⟩ := hβ β₁ m₁
  obtain ⟨s₂, r₂⟩ := hβ β₂ m₂
  have key : ∀ a b : ℂ, a * s₁ + b * s₂ = 0 → ∀ v ∈ smoothVecs (k := k) (r := r) σ, a • B₁ v + b • B₂ v = 0 := by
    intro a b hab v hv
    have hv' := (smoothOnH_iff_mem Hpk_conjTranspose Hpk_mul_self hU v).1 hv
    refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun l => ?_
    rw [map_add, map_smul, map_smul, ← e₁ l ⟨v, hv'⟩, ← e₂ l ⟨v, hv'⟩, ← r₁, ← r₂]
    simp only [LinearMap.smul_apply, smul_eq_mul]
    rw [← mul_assoc, ← mul_assoc, ← add_mul, hab, zero_mul]
  by_cases h : s₁ = 0
  · exact ⟨1, 0, Or.inl one_ne_zero, key _ _ (by simp [h])⟩
  · exact ⟨s₂, -s₁, Or.inr (neg_ne_zero.2 h), key _ _ (by ring)⟩

end Main

end GlobalTheory.BesselMapOne

end
