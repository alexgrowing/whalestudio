import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalConditionsIndependentOfPlaceOver
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem eps_eq_algebraMap (s : G ℚ Ω) :
    eps l s = algebraMap ℤ_[l] (Qbar l) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) := by
  simp [eps, cycBar]
  rfl

theorem eps_mem (c : Coef l) (s : G ℚ Ω) : eps l s ∈ c.O := by
  rw [eps_eq_algebraMap]; exact c.O.algebraMap_mem _

theorem continuous_eps : Continuous (fun s : G ℚ Ω => eps l s) := by
  have h : Continuous fun s : G ℚ Ω => ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) :=
    Units.continuous_val.comp (continuous_cycZ ℚ Ω l)
  have e : ∀ s : G ℚ Ω, eps l s = algebraMap ℚ_[l] (Qbar l) (((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) :=
    fun s => rfl
  simp only [e]
  have hc : Continuous (fun x : ℤ_[l] => (x : ℚ_[l])) := continuous_subtype_val
  exact (continuous_algebraMap ℚ_[l] (Qbar l)).comp (hc.comp h)

theorem eps_eq_one_of_mem_Ine [IsAlgClosure ℚ Ω] {A : ValuationSubring Ω} {v : Pl}
    (hl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) (h : IsPlaceOver A v) {σ : G ℚ Ω} (hσ : σ ∈ Ine (F := ℚ) A) :
    eps l σ = 1 := by
  have e : cycBar ℚ Ω l σ = cyc ℚ Ω l σ := (cyc_eq_map_cycZ ℚ Ω l σ).symm
  simp only [eps, e, cyc_eq_one_of_mem_Ine hl h hσ, Units.val_one]

theorem val_dt (W : R2 Ω l) (s : G ℚ Ω) : ((dt W s : (Qbar l)ˣ) : Qbar l) = (mat W s).det := by
  simp [dt, mat]

theorem dt_inv_eq (W : R2 Ω l) (h : dt W ^ 2 = 1) : (dt W)⁻¹ = dt W := by
  rw [pow_two] at h; exact inv_eq_of_mul_eq_one_right h

theorem mat_dual1_eq (W : R2 Ω l) (s : G ℚ Ω) :
    mat (dual1 W) s = (eps l s * (((dt W)⁻¹ s : (Qbar l)ˣ) : Qbar l)) • mat W s := by
  simp [mat, dual1, tw_val, eps]

theorem mat_dual1_eq' (W : R2 Ω l) (h : dt W ^ 2 = 1) (s : G ℚ Ω) :
    mat (dual1 W) s = (eps l s * (mat W s).det) • mat W s := by
  rw [mat_dual1_eq, dt_inv_eq W h, val_dt]

theorem continuous_mat (W : R2 Ω l) (hW : Continuous W) : Continuous fun s => mat W s :=
  Units.continuous_val.comp hW

theorem continuous_mat_dual1 (W : R2 Ω l) (hW : Continuous W) (h : dt W ^ 2 = 1) :
    Continuous fun s => mat (dual1 W) s := by
  simp only [mat_dual1_eq' W h]
  exact (continuous_eps.mul (continuous_mat W hW).matrix_det).smul (continuous_mat W hW)

theorem om_add_left (x x' y : Fin 2 → Qbar l) : om (x + x') y = om x y + om x' y := by
  simp only [om, Pi.add_apply]; ring

theorem om_add_right (x y y' : Fin 2 → Qbar l) : om x (y + y') = om x y + om x y' := by
  simp only [om, Pi.add_apply]; ring

theorem om_mulVec_smul (M : Matrix (Fin 2) (Fin 2) (Qbar l)) (c : Qbar l) (x y : Fin 2 → Qbar l) :
    om (M *ᵥ x) ((c • M) *ᵥ y) = c * M.det * om x y := by
  simp only [om, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.smul_apply, smul_eq_mul]
  ring

theorem om_pair (W : R2 Ω l) (s : G ℚ Ω) (x y : Fin 2 → Qbar l) :
    om (mat W s *ᵥ x) (mat (dual1 W) s *ᵥ y) = eps l s * om x y := by
  rw [mat_dual1_eq, om_mulVec_smul, mul_assoc (eps l s), ← val_dt, ← Units.val_mul,
    show (dt W)⁻¹ s * dt W s = 1 by simp, Units.val_one, mul_one]

theorem cup_cocycle (W : R2 Ω l) {a b : G ℚ Ω → Fin 2 → Qbar l} (ha : a ∈ Z1 (Loc.colRep W))
    (hb : b ∈ Z1 (Loc.colRep (dual1 W))) (r s t : G ℚ Ω) :
    eps l r * cup W a b s t + cup W a b r (s * t) = cup W a b (r * s) t + cup W a b r s := by
  simp only [cup]
  rw [cocycle_mulVec hb s t, cocycle_mulVec ha r s, mat_mul' (dual1 W) r s, ← Matrix.mulVec_mulVec,
    Matrix.mulVec_add, om_add_right, om_add_left, om_pair]
  ring

theorem cg_refl (n : ℕ) (x : Qbar l) : Cg n x x := by
  simp [Cg]

theorem vanish_NS [IsAlgClosure ℚ Ω] {S : Finset Pl} (hS : ContainsAbove S l) (V : R2 Ω l)
    (hV : Continuous fun s => mat V s) {z : G ℚ Ω → Fin 2 → Qbar l} (hz : z ∈ Z1 (Loc.colRep V))
    (hu : Unr V z) (hI : ∀ w, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ V.ker) :
    ∀ α ∈ NS Ω (S : Set Pl), mat V α = 1 ∧ z α = 0 := by
  have z1 : z 1 = 0 := by
    have := cocycle_mulVec hz 1 1
    rw [mul_one, mat_one', Matrix.one_mulVec] at this
    simpa using this
  let K : Subgroup (G ℚ Ω) :=
    { carrier := {g | mat V g = 1 ∧ z g = 0}
      one_mem' := ⟨mat_one' V, z1⟩
      mul_mem' := by
        rintro g h ⟨h1, h2⟩ ⟨h3, h4⟩
        exact ⟨by rw [mat_mul', h1, h3, mul_one], by rw [cocycle_mulVec hz, h2, h4, Matrix.mulVec_zero, add_zero]⟩
      inv_mem' := by
        rintro g ⟨h1, h2⟩
        have hm : mat V g⁻¹ * mat V g = 1 := by rw [← mat_mul', inv_mul_cancel, mat_one']
        rw [h1, mul_one] at hm
        refine ⟨hm, ?_⟩
        have := cocycle_mulVec hz g⁻¹ g
        rw [inv_mul_cancel, z1, h2, Matrix.mulVec_zero, add_zero] at this
        exact this.symm }
  have hK : K.Normal := ⟨fun g ⟨h1, h2⟩ x => by
    have hm : mat V (x * g * x⁻¹) = 1 := by
      rw [mat_mul', mat_mul', h1, mul_one, ← mat_mul', mul_inv_cancel, mat_one']
    refine ⟨hm, ?_⟩
    rw [cob_conj hz x g 0 (by rw [h2, Matrix.mulVec_zero, sub_zero]), hm, Matrix.one_mulVec, sub_self]⟩
  have hcl : IsClosed (K : Set (G ℚ Ω)) :=
    (isClosed_eq hV continuous_const).inter (isClosed_eq hz.1 continuous_const)
  intro α hα
  have hle : NS Ω (S : Set Pl) ≤ K := by
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) hcl
    intro τ hτ
    simp only [Set.mem_iUnion] at hτ
    obtain ⟨v, hv, A, hA, hτ⟩ := hτ
    have hv' : v ∉ S := by simpa using hv
    have hτ' : τ ∈ Ine (F := ℚ) A := hτ
    have hm : mat V τ = 1 := by
      have h1 : V τ = 1 := hI v hv' A hA hτ'
      simp [mat, h1]
    refine ⟨hm, ?_⟩
    have hl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := fun h => hv' (hS v h)
    obtain ⟨B0, hB0, x, hx⟩ := hu v hl
    obtain ⟨x', hx'⟩ := (place_indep l Ω V z hz v B0 A hB0 hA).1 ⟨x, hx⟩
    rw [hx' τ hτ', hm, Matrix.one_mulVec, sub_self]
  exact hle hα

theorem cupProductDualTwist_isTwoCocycle_unramified_alt : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ)
    (S : Finset Pl) (W : R2 Ω l) (a b : G ℚ Ω → Fin 2 → Qbar l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) →
    dt W ^ 2 = 1 → ContainsAbove S l →
    (∀ w, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ W.ker) →
    a ∈ Z1 (Loc.colRep W) → b ∈ Z1 (Loc.colRep (dual1 W)) → (∀ s i, a s i ∈ c.O) → (∀ s i, b s i ∈ c.O) →
    Unr W a → Unr (dual1 W) b → Coc2 c n S (cup W a b) := by
  intro l _ Ω _ _ _ c n S W a b hW hWi hdt hS hI ha hb hai hbi hua hub
  have hWc := continuous_mat W hW
  have hDc := continuous_mat_dual1 W hW hdt
  have hDI : ∀ w, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ (dual1 W).ker := by
    intro w hw B hB σ hσ
    have h1 : W σ = 1 := hI w hw B hB hσ
    have hm : mat W σ = 1 := by simp [mat, h1]
    have he : eps l σ = 1 := eps_eq_one_of_mem_Ine (fun h => hw (hS w h)) hB hσ
    show dual1 W σ = 1
    apply Units.ext
    show mat (dual1 W) σ = 1
    rw [mat_dual1_eq' W hdt, hm, he, Matrix.det_one, mul_one, one_smul]
  have vW := vanish_NS hS W hWc ha hua hI
  have vD := vanish_NS hS (dual1 W) hDc hb hub hDI
  have hker : (toGS Ω (S : Set Pl)).ker = NS Ω (S : Set Pl) := QuotientGroup.ker_mk' _
  have hD : ∀ s i j, mat (dual1 W) s i j ∈ c.O := by
    intro s i j
    rw [mat_dual1_eq' W hdt, Matrix.smul_apply, smul_eq_mul, Matrix.det_fin_two]
    exact c.O.mul_mem (c.O.mul_mem (eps_mem c s)
      (c.O.sub_mem (c.O.mul_mem (hWi s 0 0) (hWi s 1 1)) (c.O.mul_mem (hWi s 0 1) (hWi s 1 0)))) (hWi s i j)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have ha' : Continuous a := ha.1
    have hb' : Continuous b := hb.1
    have hA : ∀ i, Continuous fun p : G ℚ Ω × G ℚ Ω => a p.1 i :=
      fun i => (continuous_apply i).comp (ha'.comp continuous_fst)
    have hB : ∀ i, Continuous fun p : G ℚ Ω × G ℚ Ω => b p.2 i :=
      fun i => (continuous_apply i).comp (hb'.comp continuous_snd)
    have hM : ∀ i j, Continuous fun p : G ℚ Ω × G ℚ Ω => mat (dual1 W) p.1 i j :=
      fun i j => (continuous_apply j).comp ((continuous_apply i).comp (hDc.comp continuous_fst))
    simp only [cup, om, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    exact ((hA 0).mul (((hM 1 0).mul (hB 0)).add ((hM 1 1).mul (hB 1)))).sub
      ((hA 1).mul (((hM 0 0).mul (hB 0)).add ((hM 0 1).mul (hB 1))))
  · intro s t
    simp only [cup, om, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    exact c.O.sub_mem
      (c.O.mul_mem (hai s 0) (c.O.add_mem (c.O.mul_mem (hD s 1 0) (hbi t 0)) (c.O.mul_mem (hD s 1 1) (hbi t 1))))
      (c.O.mul_mem (hai s 1) (c.O.add_mem (c.O.mul_mem (hD s 0 0) (hbi t 0)) (c.O.mul_mem (hD s 0 1) (hbi t 1))))
  · intro r s t
    rw [cup_cocycle W ha hb r s t]
    exact cg_refl n _
  · intro s t α hα β hβ
    rw [hker] at hα hβ
    have e : cup W a b (s * α) (t * β) = cup W a b s t := by
      simp only [cup]
      rw [cocycle_mulVec ha s α, (vW α hα).2, Matrix.mulVec_zero, add_zero, cocycle_mulVec hb t β, (vD β hβ).2,
        Matrix.mulVec_zero, add_zero, mat_mul', (vD α hα).1, mul_one]
    rw [e]
    exact cg_refl n _

end GlobalTheory.Ord2
