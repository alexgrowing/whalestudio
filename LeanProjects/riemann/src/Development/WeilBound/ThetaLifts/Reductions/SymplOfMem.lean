import Mathlib
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLieG
import Development.WeilBound.ThetaLifts.Reductions.RealSmulL2Coe

noncomputable section

namespace PositivityTheory.ThKR

section Mid

open Complex Matrix Filter Topology GlobalTheory.RealWeil PositivityTheory.RL PositivityTheory.RL.Up

variable {l : Type} [Fintype l] [DecidableEq l]

def HG {G : Type} [Group G] (s : G →* Matrix (l ⊕ l) (l ⊕ l) ℝ) : Subgroup G where
  carrier := {g | ∃ U : (Sch l →L[ℂ] Sch l)ˣ, Im (s g) U.1}
  one_mem' := ⟨1, by rw [map_one]; exact Im.one⟩
  mul_mem' := fun ⟨U, hU⟩ ⟨U', hU'⟩ => ⟨U * U', by rw [map_mul]; exact hU.mul hU'⟩
  inv_mem' := fun ⟨U, hU⟩ => ⟨U⁻¹, hU.inv (by rw [← map_mul, mul_inv_cancel, map_one])⟩

theorem sympl_of_mem {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} (h : A ∈ Matrix.symplecticGroup l ℝ) (w w' : l ⊕ l → ℝ) :
    sympl (A *ᵥ w) (A *ᵥ w') = sympl w w' := by
  rw [sympl_eq, sympl_eq, neg_inj, mulVec_mulVec, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec,
    ← Matrix.mul_assoc, SymplecticGroup.mem_iff'.1 h]

theorem scalar_lie {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
    (hL : LocalLift) (𝔤 : Submodule ℝ 𝔸) (hAd : ∀ Z ∈ 𝔤, ∀ Y ∈ 𝔤, NormedSpace.exp Z * Y * NormedSpace.exp (-Z) ∈ 𝔤)
    (ρ : 𝔸 →ₐ[ℝ] Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (hexp : ∀ (Z : 𝔸) (t : ℝ), ρ (NormedSpace.exp (t • Z)) = NormedSpace.exp (t • ρ Z))
    (S : Subgroup 𝔸ˣ) (hS : ∀ Z ∈ 𝔤, expU Z ∈ S) (hρ : ∀ g : S, ρ g.1.1 ∈ Matrix.symplecticGroup l ℝ)
    (A : S →* (Sch l →L[ℂ] Sch l)) (hU : ∀ g : S, ∃ U : (Sch l →L[ℂ] Sch l)ˣ, Im (ρ g.1.1) U.1)
    (hA : ∀ (g : S) (U : (Sch l →L[ℂ] Sch l)ˣ), Im (ρ g.1.1) U.1 → ∃ c : ℂ, A g = c • U.1)
    (hw : ∀ (T : Sch l →L[ℂ] ℂ) f, Continuous fun g => T (A g f)) :
    ∃ ζ : 𝔸 →ₗ[ℝ] ℂ, (∀ Z (h : Z ∈ 𝔤) (T : Sch l →L[ℂ] ℂ) f,
        HasDerivAt (fun t : ℝ => T (A ⟨expU (t • Z), hS _ (𝔤.smul_mem t h)⟩ f)) (T (quad (ρ Z) f + ζ Z • f)) 0) ∧
      ∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, ζ (X * Y - Y * X) = 0 := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  let ex : 𝔤 → S := fun Z => ⟨expU Z.1, hS _ Z.2⟩
  have ex0 : ∀ Z : 𝔤, ex ((0 : ℝ) • Z) = 1 := fun Z => Subtype.ext (by rw [zero_smul]; exact expU_zero)
  have exm : ∀ (Z : 𝔤) (a b : ℝ), ex ((a + b) • Z) = ex (a • Z) * ex (b • Z) := fun Z a b => Subtype.ext (expU_add Z.1 a b)
  have exc : ∀ Z : 𝔤, Continuous fun t : ℝ => ex (t • Z) := fun Z => (continuous_expU Z.1).subtype_mk _
  have conf : ∀ g, Conf (A g) := fun g => by
    obtain ⟨U, h⟩ := hU g
    obtain ⟨c, hc⟩ := hA g U h
    exact ⟨‖c‖, fun f => by rw [hc, ContinuousLinearMap.smul_apply, map_smul, norm_smul, h.1]⟩
  have A0 : ∀ Z : 𝔤, A (ex ((0 : ℝ) • Z)) = 1 := fun Z => by rw [ex0, map_one]
  have Am : ∀ (Z : 𝔤) (a b : ℝ), A (ex ((a + b) • Z)) = A (ex (a • Z)) * A (ex (b • Z)) := fun Z a b => by
    rw [exm, map_mul]
  have key : ∀ Z : 𝔤, ∃ z : ℂ, ∀ (T : Sch l →L[ℂ] ℂ) f,
      HasDerivAt (fun t : ℝ => T (A (ex (t • Z)) f)) (T (quad (ρ Z) f + z • f)) 0 := fun Z =>
    line hL (mem_lie_of _ fun t => by
        rw [← hexp]
        exact hρ (ex (t • Z))) (fun t => A (ex (t • Z))) (fun t => conf _) (A0 Z) (Am Z)
      (fun T f => (hw T f).comp (exc Z)) fun t U h => hA _ U (by rw [← hexp] at h; exact h)
  choose z hz using key
  obtain ⟨f0, hf0⟩ := exists_ne (l := l)
  let T0 : Sch l →L[ℂ] ℂ := innerSL ℂ (schwartzToL2 l f0) ∘L schwartzToL2 l
  have hT0 : T0 f0 ≠ 0 := fun h => j_ne hf0 (inner_self_eq_zero.1 h)
  have uniq : ∀ (Z : 𝔤) (c : ℂ),
      HasDerivAt (fun t : ℝ => T0 (A (ex (t • Z)) f0)) (T0 (quad (ρ Z) f0 + c • f0)) 0 → z Z = c := fun Z c h => by
    have := (hz Z T0 f0).unique h
    simp only [map_add, map_smul, add_right_inj, smul_eq_mul] at this
    exact mul_right_cancel₀ hT0 this
  have hsm : ∀ (r : ℝ) (Z : 𝔤), z (r • Z) = r • z Z := fun r Z => uniq _ _ (by
    have h1 := hz Z T0 f0
    rw [← zero_mul r] at h1
    have h2 := h1.scomp (0 : ℝ) (hasDerivAt_mul_const r)
    refine (h2.congr_deriv ?_).congr_of_eventuallyEq (.of_forall fun t => by simp only [smul_smul]; rfl)
    rw [Submodule.coe_smul, map_smul ρ, quad_smul]
    simp [mul_add, mul_assoc])
  have hst : ∀ (Z : 𝔤) f, HasDerivAt (fun t : ℝ => schwartzToL2 l (A (ex (t • Z)) f))
      (schwartzToL2 l ((quad (ρ Z) + z Z • 1 : Sch l →L[ℂ] Sch l) f)) 0 := fun Z =>
    strong (fun t => A (ex (t • Z))) _ (A0 Z) (Am Z) (hz Z)
  have hbd : ∀ Z : 𝔤, ∃ C : ℝ, ∀ t ∈ Set.Icc (-1 : ℝ) 1, ∀ f, ‖schwartzToL2 l (A (ex (t • Z)) f)‖ ≤ C * ‖schwartzToL2 l f‖ :=
    fun Z => bd_of_conf _ (fun t => conf _) fun T f => (hw T f).comp (exc Z)
  have h3 : ∀ X Y : 𝔤, cexp (z X + (z Y + z (-(X + Y)))) = 1 := fun X Y => by
    refine delta_zero A hw conf (fun t => ex (t • X) * (ex (t • Y) * ex (t • -(X + Y)))) (by simp only [ex0, mul_one]) ?_ _
      fun f => ?_
    · rw [Topology.IsInducing.subtypeVal.tendsto_nhds_iff, Units.isOpenEmbedding_val.isInducing.tendsto_nhds_iff]
      have h1 := (hasDerivAt_exp_smul_const (𝕂 := ℝ) X.1 0).mul
        ((hasDerivAt_exp_smul_const (𝕂 := ℝ) Y.1 0).mul (hasDerivAt_exp_smul_const (𝕂 := ℝ) (-(X.1 + Y.1)) 0))
      exact pow_lim _ (by simp) (h1.congr_deriv (by simp))
    · obtain ⟨C, hC⟩ := hbd X
      obtain ⟨C', hC'⟩ := hbd Y
      have := dif_mul (U' := fun t => A (ex (t • Y)) * A (ex (t • -(X + Y)))) (A0 X) (by rw [A0, A0, mul_one]) hC (hst X)
        (dif_mul (A0 Y) (A0 (-(X + Y))) hC' (hst Y) (hst _)) f
      simp only [map_mul]
      refine this.congr_deriv ?_
      have e : quad (ρ (-(X + Y) : 𝔤)) = -(quad (ρ X) + quad (ρ Y)) := by
        rw [Submodule.coe_neg, Submodule.coe_add, map_neg, map_add, ← neg_one_smul ℝ, quad_smul, quad_add]
        simp [add_comm]
      rw [← map_smul, e]
      congr 1
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply]
      module
  let ζ0 : 𝔤 →ₗ[ℝ] ℂ :=
    { toFun := z
      map_smul' := hsm
      map_add' := fun X Y => by
        have h4 : z X + (z Y + z (-(X + Y))) = 0 := exp_mul_inj fun t => by
          have := h3 (t • X) (t • Y)
          rw [← smul_add, ← smul_neg, hsm, hsm, hsm] at this
          rw [zero_mul, Complex.exp_zero, ← this]
          congr 1
          simp only [real_smul]
          ring
        rw [← neg_one_smul ℝ, hsm] at h4
        simp only [neg_smul, one_smul] at h4
        linear_combination -h4 }
  obtain ⟨ζ, hζ⟩ := ζ0.exists_extend
  have hζ' : ∀ Z (h : Z ∈ 𝔤), ζ Z = z ⟨Z, h⟩ := fun Z h => LinearMap.congr_fun hζ ⟨Z, h⟩
  refine ⟨ζ, fun Z h T f => by rw [hζ' Z h]; exact hz ⟨Z, h⟩ T f, fun X hX Y hY => ?_⟩
  have hAd' : ∀ s : ℝ, ζ (NormedSpace.exp (s • X) * Y * NormedSpace.exp (s • -X)) = ζ Y := fun s => by
    have hm := hAd _ (𝔤.smul_mem s hX) Y hY
    rw [smul_neg, hζ' _ hm, hζ' _ hY]
    let g : S := ex (s • ⟨X, hX⟩)
    have e : ∀ t : ℝ, ex (t • ⟨_, hm⟩) = g * ex (t • ⟨Y, hY⟩) * g⁻¹ := fun t => by
      refine Subtype.ext (Units.ext ?_)
      have := NormedSpace.exp_units_conj (expU (s • X)) (t • Y)
      rw [mul_smul_comm, smul_mul_assoc] at this
      exact this
    refine uniq _ _ ?_
    have h1 := hz ⟨Y, hY⟩ (T0 ∘L A g) (A g⁻¹ f0)
    have i1 : A g (A g⁻¹ f0) = f0 := by rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
    obtain ⟨U, h⟩ := hU g
    obtain ⟨c, hc⟩ := hA g U h
    have h2 := h.quad (sympl_of_mem (hρ g)) (s' := ρ g⁻¹.1.1) (by
      rw [← map_mul]
      exact (congrArg ρ (Units.mul_inv g.1)).trans (map_one ρ)) (ρ Y)
    have h4 : A g * quad (ρ Y) = quad (ρ (g.1.1 * Y * g⁻¹.1.1)) * A g := by
      rw [hc, smul_mul_assoc, mul_smul_comm, h2, map_mul, map_mul]
    have h5 : A g (quad (ρ Y) (A g⁻¹ f0)) = quad (ρ (g.1.1 * Y * g⁻¹.1.1)) f0 := by
      rw [← ContinuousLinearMap.mul_apply, h4, ContinuousLinearMap.mul_apply, i1]
    simp only [e, map_mul A]
    refine h1.congr_deriv ?_
    rw [ContinuousLinearMap.comp_apply, map_add (A g), map_smul (A g), h5, i1]
    rfl
  have h1 := ((hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0).mul_const Y).mul (hasDerivAt_exp_smul_const (𝕂 := ℝ) (-X) 0)
  have h2 := ζ.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have h3 : HasDerivAt (fun s : ℝ => ζ (NormedSpace.exp (s • X) * Y * NormedSpace.exp (s • -X))) 0 0 := by
    simp only [hAd']
    exact hasDerivAt_const _ _
  have := h2.unique h3
  simpa [sub_eq_add_neg] using this

variable {W β : Type} [Fintype W] [DecidableEq W] [Fintype β] [DecidableEq β]

def HS (K : W → Matrix β β ℂ) (ρ : (W → Matrix β β ℂ) →ₐ[ℝ] Matrix (l ⊕ l) (l ⊕ l) ℝ) : Subgroup (W → Matrix β β ℂ)ˣ :=
  SG K ⊓ HG (ρ.toRingHom.toMonoidHom.comp (Units.coeHom _))

theorem mid2 (hL : LocalLift) (K : W → Matrix β β ℂ) (hK : ∀ w, (K w)ᴴ = K w) (hu : ∀ w, IsUnit (K w).det)
    (ρ : (W → Matrix β β ℂ) →ₐ[ℝ] Matrix (l ⊕ l) (l ⊕ l) ℝ) (hρ : ∀ g : SG K, ρ g.1.1 ∈ Matrix.symplecticGroup l ℝ)
    (A : HS K ρ →* (Sch l →L[ℂ] Sch l))
    (hA : ∀ (g : HS K ρ) (U : (Sch l →L[ℂ] Sch l)ˣ), Im (ρ g.1.1) U.1 → ∃ c : ℂ, A g = c • U.1)
    (hw : ∀ (T : Sch l →L[ℂ] ℂ) f, Continuous fun g => T (A g f)) :
    ∃ c : W → ℂ, ∀ (Z : W → Matrix β β ℂ) (γ : ℝ → SG K), (∀ t w, (γ t).1.1 w = NormedSpace.exp (t • Z w)) →
      ∃ h : ∀ t, (γ t).1 ∈ HS K ρ, ∀ (T : Sch l →L[ℂ] ℂ) f, HasDerivAt (fun t => T (A ⟨(γ t).1, h t⟩ f))
        (T (quad (ρ Z) f + (∑ w, c w * (Z w).trace) • f)) 0 := by
  have hρc : Continuous ρ := ρ.toLinearMap.continuous_of_finiteDimensional
  letI : NormedRing (Matrix β β ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix β β ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedRing (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix β β ℂ) := FiniteDimensional.complete ℝ _
  letI : NormedAlgebra ℚ (Matrix β β ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _
  letI : NormedAlgebra ℚ (Matrix (l ⊕ l) (l ⊕ l) ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
  have hpi : ∀ (Z : W → Matrix β β ℂ) w, NormedSpace.exp Z w = NormedSpace.exp (Z w) := fun Z w => Pi.coe_exp Z w
  have hS : ∀ Z ∈ LG K, expU Z ∈ SG K := fun Z hZ => funext fun w => by
    have := exp_preserves (Y := Z w) (J := K w) (congrFun hZ w)
    rw [← hpi] at this
    exact this
  have hexp : ∀ (Z : W → Matrix β β ℂ) (t : ℝ), ρ (NormedSpace.exp (t • Z)) = NormedSpace.exp (t • ρ Z) := fun Z t => by
    rw [← map_smul]
    exact NormedSpace.map_exp ρ hρc _
  have hS' : ∀ Z ∈ LG K, expU Z ∈ HS K ρ := fun Z hZ => ⟨hS Z hZ, by
    have := exists_im hL (X := ρ Z) (mem_lie_of _ fun t => by
      rw [← hexp]
      exact hρ ⟨expU (t • Z), hS _ ((LG K).smul_mem t hZ)⟩) 1
    rw [← hexp, one_smul] at this
    exact this⟩
  obtain ⟨ζ, hζ, hbr⟩ := scalar_lie hL (LG K) (fun Z hZ Y hY => by
    have h1 : star (expU Z)⁻¹.1 * K * (expU Z)⁻¹.1 = K := (SG K).inv_mem (hS Z hZ)
    have h2 : star Y * K + K * Y = 0 := hY
    show star ((expU Z).1 * Y * (expU Z)⁻¹.1) * K + K * ((expU Z).1 * Y * (expU Z)⁻¹.1) = 0
    generalize expU Z = g at h1
    calc _ = star (g.1 * Y * g⁻¹.1) * (star g⁻¹.1 * K * g⁻¹.1) + (star g⁻¹.1 * K * g⁻¹.1) * (g.1 * Y * g⁻¹.1) := by
          rw [h1]
      _ = star g⁻¹.1 * (star Y * star (g⁻¹.1 * g.1) * K + K * (g⁻¹.1 * g.1) * Y) * g⁻¹.1 := by
          simp only [star_mul, mul_assoc, mul_add, add_mul]
      _ = 0 := by rw [Units.inv_mul, star_one, mul_one, mul_one, h2, mul_zero, zero_mul]) ρ hexp
    (HS K ρ) hS' (fun g => hρ ⟨g.1, g.2.1⟩) A (fun g => g.2.2) hA hw
  have tr : ∀ w, ∃ c : ℂ, ∀ Z : Matrix β β ℂ, Zᴴ * K w + K w * Z = 0 → ζ (Pi.single w Z) = c * Z.trace := fun w => by
    let τ : Matrix β β ℂ →ₗ[ℝ] Matrix β β ℂ :=
      { toFun := fun A => -((K w)⁻¹ * Aᴴ * K w)
        map_add' := fun A B => by simp [Matrix.mul_add, Matrix.add_mul, add_comm]
        map_smul' := fun r A => by simp }
    have h1 : (K w)⁻¹ * K w = 1 := Matrix.nonsing_inv_mul _ (hu w)
    have h2 : K w * (K w)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (hu w)
    have hτ : ∀ Z, τ Z = Z ↔ Zᴴ * K w + K w * Z = 0 := fun Z => by
      show -((K w)⁻¹ * Zᴴ * K w) = Z ↔ _
      constructor
      · intro h
        conv_lhs => rw [← congrArg (K w * ·) h]
        simp [← Matrix.mul_assoc, h2]
      · intro h
        rw [Matrix.mul_assoc, eq_neg_of_add_eq_zero_left h]
        simp [← Matrix.mul_assoc, h1]
    have hm : ∀ Z, τ Z = Z → Pi.single w Z ∈ LG K := fun Z hZ => funext fun v => by
      by_cases h : v = w
      · subst h
        simpa [star_eq_conjTranspose] using (hτ Z).1 hZ
      · simp [h]
    obtain ⟨c, hc⟩ := real_form_trace τ (fun A => by simp [τ]) (fun A => by
      show -((K w)⁻¹ * (-((K w)⁻¹ * Aᴴ * K w))ᴴ * K w) = A
      simp only [conjTranspose_neg, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hK,
        Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc, h1, Matrix.mul_one]
      rw [← Matrix.mul_assoc, h1, Matrix.one_mul]) (ζ ∘ₗ LinearMap.single ℝ (fun _ : W => Matrix β β ℂ) w) fun X Y hX hY => by
      refine ⟨(hτ _).2 ?_, ?_⟩
      · have a1 := eq_neg_of_add_eq_zero_left ((hτ _).1 hX)
        have a2 := eq_neg_of_add_eq_zero_left ((hτ _).1 hY)
        simp only [conjTranspose_sub, conjTranspose_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, a1, a2,
          Matrix.mul_neg]
        simp only [← Matrix.mul_assoc, a1, a2, Matrix.neg_mul]
        abel
      · have := hbr _ (hm X hX) _ (hm Y hY)
        rw [← Pi.single_mul, ← Pi.single_mul, ← Pi.single_sub] at this
        exact this
    exact ⟨c, fun Z hZ => hc Z ((hτ Z).2 hZ)⟩
  choose c hc using tr
  refine ⟨c, fun Z γ hγ => ?_⟩
  have hZw : ∀ w, (Z w)ᴴ * K w + K w * Z w = 0 := fun w => lie_of_exp _ _ fun t => by
    rw [← hγ]
    exact congrFun (show star (γ t).1.1 * K * (γ t).1.1 = K from (γ t).2) w
  have hZ : Z ∈ LG K := funext hZw
  have e : ∀ t, (γ t).1 = expU (t • Z) := fun t => Units.ext (funext fun w => (hγ t w).trans (hpi (t • Z) w).symm)
  have b : ζ Z = ∑ w, c w * (Z w).trace := by
    conv_lhs => rw [← Finset.univ_sum_single Z, map_sum]
    exact Finset.sum_congr rfl fun w _ => hc w _ (hZw w)
  refine ⟨fun t => e t ▸ hS' _ ((LG K).smul_mem t hZ), ?_⟩
  simp only [e, ← b]
  exact hζ Z hZ

end Mid

section Main

open scoped TensorProduct Matrix Classical RealInnerProductSpace Real SchwartzMap
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealWeil Complex
open PositivityTheory.RL PositivityTheory.RL.Up

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
variable {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)} {d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ}

theorem main2 (hLL : LocalLift) (h : IsCMExt F E σ) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (K : InfinitePlace F → Matrix β β ℂ) (hK : ∀ w, (K w)ᴴ = K w)
    (hu : ∀ w, IsUnit (K w).det)
    (hKJ : ∀ w (g : Matrix β β ℂ), gᴴ * K w * g = K w ↔ gᵀ * JB.map (piInf (τ w)) * g.map star = JB.map (piInf (τ w)))
    {om : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)} (hom : IsUSplitting (adeleClass F) ψ d (actB (cA σ)) om)
    {D} (hD : IsD d D) :
    ∃ c : InfinitePlace F → ℂ, ∀ γ ∈ RLines σ JB, ∀ Z : InfinitePlace F → Matrix β β ℂ,
      (∀ (t : ℝ) w, ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf (τ w)) = NormedSpace.exp (t • Z w)) →
      ∀ (ι : Type) [Fintype ι] (u v : ι → Matrix α β (AE F E)), (∀ j, At (evI F) (u j)) → (∀ j, At (evI F) (v j)) →
        (∀ x, At (evI F) x → ∀ w, x.map (piInf (τ w)) * (Z w)ᵀ = ∑ j, sB σ JA JB (v j) x • (u j).map (piInf (τ w))) →
        ∀ f, SD (fun t => om (γ (Multiplicative.ofAdd t))) f
          ((8 * π * I : ℂ)⁻¹ • ∑ j, (D (u j) (D (v j) f) + D (v j) (D (u j) f)) + (∑ w, c w * (Z w).trace) • f) := by
  obtain ⟨n, ⟨c⟩⟩ := exists_co F κ
  obtain ⟨ι, hιc, hι, hι'⟩ := exists_iota h τ JB K fun w g => (hKJ w g).1
  obtain ⟨L, -, hL, hL'⟩ := exists_lf h τ α β
  have hLu : ∀ u, At (evI F) u → L (fun w => u.map (piInf (τ w))) = u := fun u hu =>
    ext_at h τ (At.sub' (hL _) hu) (hL' _)
  let E0 : (InfinitePlace F → Matrix α β ℂ) →ₗ[ℝ] (Fin n ⊕ Fin n → ℝ) :=
    { toFun := fun z => c.vec (d.e (L z))
      map_add' := fun z z' => by
        rw [← c.vec_add, ← map_add]
        congr 2
        refine ext_at h τ (At.sub' (hL _) fun a ha => by rw [smul_add, hL _ a ha, hL _ a ha, add_zero]) fun w => ?_
        rw [Matrix.map_add _ (map_add _), hL', hL', hL']
        rfl
      map_smul' := fun t z => by
        rw [RingHom.id_apply, ← c.vec_smul, ← map_smul]
        congr 2
        refine ext_at h τ (At.sub' (hL _) fun a ha => by rw [smul_comm, hL _ a ha, smul_zero]) fun w => ?_
        rw [hL']
        ext i j
        refine Eq.trans ?_ (Fock.piInf_realAd h.1 (τ w) t _).symm
        rw [show piInf (τ w) (L z i j) = z w i j from congrFun (congrFun (hL' z w) i) j]
        rfl }
  have hE0 : ∀ u, At (evI F) u → E0 (fun w => u.map (piInf (τ w))) = c.vec (d.e u) := fun u hu =>
    congrArg (fun x => c.vec (d.e x)) (hLu u hu)
  have hsurj : ∀ w, ∃ u, At (evI F) u ∧ c.vec (d.e u) = w := fun w => by
    obtain ⟨p, hp, rfl⟩ := c.exists_vec w
    exact ⟨d.e.symm p, at_symm hp, by rw [LinearEquiv.apply_symm_apply]⟩
  let Ee := LinearEquiv.ofBijective E0 ⟨(injective_iff_map_eq_zero _).2 fun z hz => by
    have h1 : L z = 0 := d.e.map_eq_zero_iff.1 (c.eq_zero_of_vec (at_e (hL z)) hz)
    funext w
    rw [← hL' z, h1, Matrix.map_zero _ (map_zero _)]
    rfl, fun w => by
    obtain ⟨u, hu, rfl⟩ := hsurj w
    exact ⟨_, hE0 u hu⟩⟩
  let Rm : (InfinitePlace F → Matrix β β ℂ) →ₐ[ℝ] Module.End ℝ (InfinitePlace F → Matrix α β ℂ) :=
    AlgHom.ofLinearMap (LinearMap.mk₂ ℝ (fun a z w => z w * (a w)ᵀ)
      (fun _ _ _ => by funext w; simp [Matrix.mul_add]) (fun _ _ _ => by funext w; simp)
      (fun _ _ _ => by funext w; simp [Matrix.add_mul]) (fun _ _ _ => by funext w; simp))
      (LinearMap.ext fun z => by funext w; simp)
      (fun a b => LinearMap.ext fun z => by funext w; simp [Matrix.mul_assoc])
  let ρ : (InfinitePlace F → Matrix β β ℂ) →ₐ[ℝ] Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
    (LinearMap.toMatrixAlgEquiv' : _ ≃ₐ[ℝ] _).toAlgHom.comp ((Ee.conjAlgEquiv ℝ).toAlgHom.comp Rm)
  have hρ : ∀ a z, ρ a *ᵥ E0 z = E0 fun w => z w * (a w)ᵀ := fun a z => by
    have : ρ a *ᵥ Ee z = Ee (Rm a (Ee.symm (Ee z))) :=
      LinearMap.toMatrix'_mulVec (Ee.conjAlgEquiv ℝ (Rm a)) (Ee z)
    rw [Ee.symm_apply_apply] at this
    exact this
  have hat : ∀ (g : UG (cA σ) JB) (u : Matrix α β (AE F E)), At (evI F) u → At (evI F) (actB (cA σ) g u) := fun g u hu a ha => by
    rw [actB, ← Matrix.smul_mul, hu a ha, Matrix.zero_mul]
  have hact : ∀ (g : SG K) (u : Matrix α β (AE F E)), At (evI F) u → ρ g.1.1 *ᵥ c.vec (d.e u) = c.vec (d.e (actB (cA σ) (ι g) u)) :=
    fun g u hu => by
      rw [← hE0 u hu, ← hE0 _ (hat _ u hu), hρ]
      congr 1
      funext w
      rw [actB, Matrix.map_mul, Matrix.transpose_map, hι']
  have hsp : ∀ g : SG K, ρ g.1.1 ∈ Matrix.symplecticGroup (Fin n) ℝ := fun g => mem_sp_of _ fun w w' => by
    obtain ⟨u, hu, rfl⟩ := hsurj w
    obtain ⟨u', hu', rfl⟩ := hsurj w'
    rw [hact g u hu, hact g u' hu', sympl_e, sympl_e, sB, sB, symp, symp, hTens_actB]
  have step : ∀ (g : SG K) (U : (Sch (Fin n) →L[ℂ] Sch (Fin n))ˣ), Im (ρ g.1.1) U.1 → ∃ z : ℂ,
      ∀ f, ∀ gf ∈ SB (κ → Af F), om (ι g) (pureA F (c.P f) gf) = pureA F (c.P ((z • U.1) f)) gf := fun g U hg => by
    obtain ⟨z, hz⟩ := c.schur2 hψ (om (ι g)) (hom.adm _) U⁻¹.1 (fun w hw Φ hΦ => by
      have := hom.impl (ι g) (d.e.symm w) Φ hΦ
      have e : actB (cA σ) (ι g) (d.e.symm w) = d.e.symm w := by
        have e1 : pairA F 0 1 • d.e.symm w = d.e.symm w := by rw [← map_smul, hw]
        have e2 := hι g (pairA F 0 1) (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))
        rw [actB, ← sub_eq_zero]
        conv_lhs => rw [← Matrix.mul_one (d.e.symm w), Matrix.mul_assoc, Matrix.one_mul, ← Matrix.mul_sub, ← e1,
          Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.transpose_one, ← Matrix.transpose_sub, ← Matrix.transpose_smul, e2]
        simp
      rw [e, Darboux.rho, LinearEquiv.apply_symm_apply] at this
      exact this) fun w hw f gf hgf => by
      have h1 : Im (ρ (g⁻¹).1.1) U⁻¹.1 := hg.inv (by
        rw [← map_mul]
        exact (congrArg ρ (Units.mul_inv g.1)).trans (map_one ρ))
      have hu := at_symm (d := d) hw
      have h2 := hact g⁻¹ _ hu
      rw [LinearEquiv.apply_symm_apply] at h2
      rw [h1.2, h2, ← c.schr_P hψ (at_e (hat _ _ hu))]
      have := hom.impl (ι g) (actB (cA σ) (ι g⁻¹) (d.e.symm w)) _ (pure_mem (c.P (U⁻¹.1 f)) hgf)
      rw [show actB (cA σ) (ι g) (actB (cA σ) (ι g⁻¹) (d.e.symm w)) = d.e.symm w by
        rw [actB, actB, Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, ← Subgroup.coe_mul, ← map_mul,
          mul_inv_cancel, map_one]
        simp] at this
      conv_rhs at this => rw [Darboux.rho, LinearEquiv.apply_symm_apply]
      exact this
    refine ⟨z, fun f gf hgf => ?_⟩
    have := hz (U.1 f) gf hgf
    rw [← ContinuousLinearMap.mul_apply, Units.inv_mul, ContinuousLinearMap.one_apply] at this
    rw [this, ContinuousLinearMap.smul_apply, map_smul]
    funext x
    simp [pureA, mul_assoc]
  let inc : HS K ρ →* SG K := Subgroup.inclusion inf_le_left
  have incc : Continuous inc := continuous_subtype_val.subtype_mk _
  have ex : ∀ g : HS K ρ, ∃ A : Sch (Fin n) →L[ℂ] Sch (Fin n),
      ∀ f, ∀ gf ∈ SB (κ → Af F), om (ι (inc g)) (pureA F (c.P f) gf) = pureA F (c.P (A f)) gf := fun g => by
    obtain ⟨U, hU⟩ := g.2.2
    obtain ⟨z, hz⟩ := step (inc g) U hU
    exact ⟨_, hz⟩
  choose A0 hA0 using ex
  have uniq : ∀ (g : HS K ρ) (B : Sch (Fin n) →L[ℂ] Sch (Fin n)),
      (∀ f, ∀ gf ∈ SB (κ → Af F), om (ι (inc g)) (pureA F (c.P f) gf) = pureA F (c.P (B f)) gf) → A0 g = B := fun g B hB => by
    ext1 f
    rw [← c.P'_P (A0 g f), ← c.P'_P (B f)]
    congr 1
    exact SeminormBoundRestriction.eq_of_pureA fun gf hgf x => by rw [← hA0 g f gf hgf, hB f gf hgf]
  let A : HS K ρ →* (Sch (Fin n) →L[ℂ] Sch (Fin n)) :=
    { toFun := A0
      map_one' := uniq _ _ fun f gf _ => by rw [map_one, map_one, map_one]; rfl
      map_mul' := fun a b => uniq _ _ fun f gf hgf => by
        rw [map_mul, map_mul, map_mul, Module.End.mul_apply, hA0 b f gf hgf, hA0 a _ gf hgf]
        rfl }
  obtain ⟨cc, hcc⟩ := mid2 hLL K hK hu ρ hsp A (fun g U hg => (step (inc g) U hg).imp fun z hz => uniq _ _ hz) fun T f => by
    obtain ⟨l, hl, gf, hgf, hT⟩ := exists_adm (T ∘L c.P')
    refine ((hom.cont l hl _ (pure_mem (c.P f) hgf)).comp (hιc.comp incc)).congr fun g => ?_
    show l (om (ι (inc g)) _) = T (A0 g f)
    rw [hA0 g f gf hgf, hT, ContinuousLinearMap.comp_apply, c.P'_P]
  refine ⟨cc, fun γ hγ Z hZ J _ u v hu hv huv f gf hgf l hl => ?_⟩
  obtain ⟨T, hT⟩ := hl gf hgf
  let mp : Matrix β β (AE F E) →* (InfinitePlace F → Matrix β β ℂ) :=
    MonoidHom.pi fun w => (piInf (τ w)).mapMatrix.toMonoidHom
  let γ0 : ℝ → SG K := fun t => ⟨Units.map mp (γ (Multiplicative.ofAdd t)).1, funext fun w => (hKJ w _).2 (by
    have := congrArg (fun X : Matrix β β (AE F E) => X.map (piInf (τ w))) (γ (Multiplicative.ofAdd t)).2
    simp only [map_form h] at this
    exact this)⟩
  have e0 : ∀ t, γ (Multiplicative.ofAdd t) = ι (γ0 t) := fun t => Subtype.ext (Units.ext (ext_at h τ (by
    have := At.sub' (hγ.2 (Multiplicative.ofAdd t)) (hι (γ0 t))
    rwa [sub_sub_sub_cancel_right] at this) fun w => (hι' (γ0 t) w).symm))
  have hq := quad_eq (ρ Z) (fun j => c.vec (d.e (u j))) (fun j => c.vec (d.e (v j))) fun w => by
    obtain ⟨x, hx, rfl⟩ := hsurj w
    simp only [sympl_e]
    rw [← hE0 x hx, hρ]
    simp only [huv x hx, ← hE0 _ (hu _), ← map_smul, ← map_sum]
    congr 1
    funext w
    simp [Finset.sum_apply]
  obtain ⟨hγ0, hcc⟩ := hcc Z γ0 hZ
  have := hcc (T ∘L c.P) (c.P' f)
  rw [hT]
  refine (this.congr_deriv ?_).congr_of_eventuallyEq (.of_forall fun t => ?_)
  · rw [ContinuousLinearMap.comp_apply, hq]
    congr 1
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.mul_apply, map_add, map_smul, map_sum, hD.P c (hu _), hD.P c (hv _), c.P_P']
  · show l (om (γ (Multiplicative.ofAdd t)) _) = T (c.P (A0 ⟨(γ0 t).1, hγ0 t⟩ (c.P' f)))
    rw [← hT, ← hA0 _ _ gf hgf, c.P_P', e0]
    rfl

end Main

end PositivityTheory.ThKR

end
