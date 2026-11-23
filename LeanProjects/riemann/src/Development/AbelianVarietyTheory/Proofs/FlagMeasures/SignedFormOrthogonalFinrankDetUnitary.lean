import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagLeviMaxCompactClosedSubgroups

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.PerpModulus

open GlobalTheory.FlagLeviGroup
open scoped ComplexOrder

variable {n : ℕ} {ε : Fin n → Bool}

def basisMat (V : Submodule ℂ (Fin n → ℂ)) : Matrix (Fin n) (Fin (Module.finrank ℂ V)) ℂ :=
  Matrix.of fun j i => (Module.finBasis ℂ V i : Fin n → ℂ) j

variable (ε) in

def pairMap (V : Submodule ℂ (Fin n → ℂ)) : (Fin n → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) :=
  ((basisMat V)ᴴ * Formalism.REAL.Jm ε).mulVecLin

theorem pairMap_apply (V : Submodule ℂ (Fin n → ℂ)) (y : Fin n → ℂ) (i) :
    pairMap ε V y i = star (Module.finBasis ℂ V i : Fin n → ℂ) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) := by
  simp only [pairMap, Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec]
  simp only [Matrix.mulVec, dotProduct, basisMat, Matrix.conjTranspose_apply, Matrix.of_apply,
    Pi.star_apply]

private theorem basisMat_mulVec (V : Submodule ℂ (Fin n → ℂ))
    (c : Fin (Module.finrank ℂ V) → ℂ) :
    basisMat V *ᵥ c = (((Module.finBasis ℂ V).equivFun.symm c : V) : Fin n → ℂ) := by
  funext j
  simp [basisMat, Matrix.mulVec, dotProduct, Module.Basis.equivFun_symm_apply, Finset.sum_apply, mul_comm]

theorem rank_basisMat (V : Submodule ℂ (Fin n → ℂ)) : (basisMat V).rank = Module.finrank ℂ V := by
  have hr : LinearMap.range (basisMat V).mulVecLin = V := by
    apply le_antisymm
    · rintro _ ⟨c, rfl⟩
      rw [Matrix.mulVecLin_apply, basisMat_mulVec]
      exact Submodule.coe_mem _
    · intro x hx
      refine ⟨(Module.finBasis ℂ V).equivFun ⟨x, hx⟩, ?_⟩
      rw [Matrix.mulVecLin_apply, basisMat_mulVec, LinearEquiv.symm_apply_apply]
  rw [Matrix.rank, hr]

theorem pairMap_surj (V : Submodule ℂ (Fin n → ℂ)) : Function.Surjective (pairMap ε V) := by
  have hJ : IsUnit (Formalism.REAL.Jm ε).det :=
    Matrix.isUnit_det_of_right_inverse (Formalism.REAL.Jm_mul_self ε)
  have hrk : ((basisMat V)ᴴ * Formalism.REAL.Jm ε).rank = Module.finrank ℂ V := by
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hJ, Matrix.rank_conjTranspose, rank_basisMat]
  unfold Matrix.rank at hrk
  have htop : LinearMap.range (pairMap ε V) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]
    exact hrk
  exact LinearMap.range_eq_top.mp htop

theorem pair_sum (V : Submodule ℂ (Fin n → ℂ)) (x : V) (y : Fin n → ℂ) :
    star (x : Fin n → ℂ) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) =
      ∑ i, star ((Module.finBasis ℂ V).repr x i) * pairMap ε V y i := by
  have hx : (x : Fin n → ℂ) =
      ∑ i, (Module.finBasis ℂ V).repr x i • ((Module.finBasis ℂ V i : V) : Fin n → ℂ) := by
    have hs := congrArg V.subtype ((Module.finBasis ℂ V).sum_repr x)
    rw [map_sum] at hs
    simp only [map_smul, Submodule.subtype_apply] at hs
    exact hs.symm
  rw [hx, star_sum, sum_dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_smul, smul_dotProduct, pairMap_apply, smul_eq_mul]

private theorem pairMap_eq_zero_iff (V : Submodule ℂ (Fin n → ℂ)) (y : Fin n → ℂ) :
    pairMap ε V y = 0 ↔ ∀ x ∈ V, star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0 := by
  constructor
  · intro h0 x hx
    have hs := pair_sum (ε := ε) V ⟨x, hx⟩ y
    simp only [h0, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hs
    exact hs
  · intro h0
    funext i
    rw [pairMap_apply, Pi.zero_apply]
    exact h0 _ (Module.finBasis ℂ V i).2

theorem ker_pairMap {V V' : Submodule ℂ (Fin n → ℂ)}
    (h : ∀ y, y ∈ V' ↔ ∀ x ∈ V, star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0) :
    LinearMap.ker (pairMap ε V) = V' := by
  ext y
  rw [LinearMap.mem_ker, pairMap_eq_zero_iff, h]

theorem finrank_perp {V V' : Submodule ℂ (Fin n → ℂ)}
    (h : ∀ y, y ∈ V' ↔ ∀ x ∈ V, star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0) :
    Module.finrank ℂ V' + Module.finrank ℂ V = n := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (pairMap ε V)
  rw [LinearMap.range_eq_top.mpr (pairMap_surj (ε := ε) V), finrank_top, Module.finrank_fin_fun,
    Module.finrank_fin_fun, ker_pairMap h] at hrn
  omega

theorem star_form (x y : Fin n → ℂ) :
    star (star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y)) = star y ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) := by
  conv_lhs => rw [Matrix.star_dotProduct, star_star, Matrix.star_mulVec, Formalism.REAL.Jm_conjTranspose,
    ← Matrix.dotProduct_mulVec]

theorem mem_ker_pairMap (V : Submodule ℂ (Fin n → ℂ)) (y : Fin n → ℂ) :
    y ∈ LinearMap.ker (pairMap ε V) ↔ ∀ x ∈ V, star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0 := by
  rw [LinearMap.mem_ker]
  exact pairMap_eq_zero_iff V y

theorem perp_perp {V V' : Submodule ℂ (Fin n → ℂ)}
    (h : ∀ y, y ∈ V' ↔ ∀ x ∈ V, star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0) (x : Fin n → ℂ)
    (hx : ∀ y ∈ V', star y ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) = 0) : x ∈ V := by
  have hK : ∀ y, y ∈ LinearMap.ker (pairMap ε V') ↔
      ∀ z ∈ V', star z ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0 := fun y => mem_ker_pairMap V' y
  have h1 := finrank_perp hK
  have h2 := finrank_perp h
  have hle : V ≤ LinearMap.ker (pairMap ε V') := by
    intro v hv
    rw [mem_ker_pairMap]
    intro y hy
    rw [← star_form, (h y).1 hy v hv, star_zero]
  have heq := Submodule.eq_of_le_of_finrank_eq hle (by omega)
  rw [heq, mem_ker_pairMap]
  exact hx

theorem norm_det (m : Formalism.REAL.UJ ε) : ‖(uMat m).det‖ = 1 := by
  have hm : (uMat m)ᴴ * Formalism.REAL.Jm ε * uMat m = Formalism.REAL.Jm ε := m.2
  have hJ : (Formalism.REAL.Jm ε).det ≠ 0 :=
    (Matrix.isUnit_det_of_right_inverse (Formalism.REAL.Jm_mul_self ε)).ne_zero
  have hd := congrArg Matrix.det hm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at hd
  have h1 : star (uMat m).det * (uMat m).det = 1 := by
    have h0 : (star (uMat m).det * (uMat m).det - 1) * (Formalism.REAL.Jm ε).det = 0 := by
      linear_combination hd
    rcases mul_eq_zero.mp h0 with h | h
    · linear_combination h
    · exact absurd h hJ
  have h2 : ‖(uMat m).det‖ * ‖(uMat m).det‖ = 1 := by
    calc ‖(uMat m).det‖ * ‖(uMat m).det‖ = ‖star (uMat m).det * (uMat m).det‖ := by
          rw [norm_mul, norm_star]
      _ = 1 := by rw [h1, norm_one]
  rcases mul_self_eq_one_iff.mp h2 with h | h
  · exact h
  · linarith [norm_nonneg (uMat m).det]

theorem det_restrict_mul (m : Formalism.REAL.UJ ε) (V : Submodule ℂ (Fin n → ℂ))
    (h1 : ∀ y ∈ V, toLin' (uMat m) y ∈ V) (h2 : ∀ y ∈ V, toLin' (uMat m⁻¹) y ∈ V) :
    LinearMap.det ((toLin' (uMat m)).restrict h1) *
      LinearMap.det ((toLin' (uMat m⁻¹)).restrict h2) = 1 := by
  rw [← LinearMap.det_comp]
  have hid : ((toLin' (uMat m)).restrict h1).comp ((toLin' (uMat m⁻¹)).restrict h2) =
      LinearMap.id := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    simp only [LinearMap.comp_apply, LinearMap.coe_restrict_apply, Matrix.toLin'_apply,
      Matrix.mulVec_mulVec, uMat_mul_inv, Matrix.one_mulVec, LinearMap.id_apply]
  rw [hid, LinearMap.det_id]

theorem det_of_intertwine {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [FiniteDimensional ℂ X] (π : X →ₗ[ℂ] Y) (hπ : Function.Surjective π) (e : X →ₗ[ℂ] X)
    (f : Y →ₗ[ℂ] Y) (hef : ∀ x, π (e x) = f (π x)) (W : Submodule ℂ X) (hW : LinearMap.ker π = W)
    (he : ∀ x ∈ W, e x ∈ W) :
    LinearMap.det e = LinearMap.det (e.restrict he) * LinearMap.det f := by
  classical
  have : FiniteDimensional ℂ Y := Module.Finite.of_surjective π hπ
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl W
  have hπW : ∀ x ∈ W, π x = 0 := fun x hx => by
    rw [← LinearMap.mem_ker, hW]
    exact hx
  have hπp : ∀ x, π x = π (((Submodule.prodEquivOfIsCompl W C hC).symm x).2 : X) := by
    intro x
    conv_lhs => rw [← (Submodule.prodEquivOfIsCompl W C hC).apply_symm_apply x,
      Submodule.coe_prodEquivOfIsCompl']
    rw [map_add, hπW _ ((Submodule.prodEquivOfIsCompl W C hC).symm x).1.2, zero_add]
  have hinj : Function.Injective (π ∘ₗ C.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have hcW : (c : X) ∈ W := by
      rw [← hW, LinearMap.mem_ker]
      exact hc
    exact Subtype.ext ((Submodule.disjoint_def.mp hC.disjoint) _ hcW c.2)
  have hsurj : Function.Surjective (π ∘ₗ C.subtype) := by
    intro y
    obtain ⟨x, rfl⟩ := hπ y
    exact ⟨((Submodule.prodEquivOfIsCompl W C hC).symm x).2, (hπp x).symm⟩
  let ψ : C ≃ₗ[ℂ] Y := LinearEquiv.ofBijective (π ∘ₗ C.subtype) ⟨hinj, hsurj⟩
  let D : C →ₗ[ℂ] C := LinearMap.snd ℂ W C ∘ₗ
    ((Submodule.prodEquivOfIsCompl W C hC).symm : X →ₗ[ℂ] W × C) ∘ₗ e ∘ₗ C.subtype
  have hDf : D = (ψ.symm : Y →ₗ[ℂ] C) ∘ₗ f ∘ₗ (ψ : C →ₗ[ℂ] Y) := by
    apply LinearMap.ext
    intro c
    apply ψ.injective
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    show π (((Submodule.prodEquivOfIsCompl W C hC).symm (e c)).2 : X) = f (π c)
    rw [← hπp, hef]
  have hdetD : LinearMap.det D = LinearMap.det f := by
    rw [hDf]
    exact LinearMap.det_conj f ψ.symm
  let e' : (W × C) →ₗ[ℂ] (W × C) := ((Submodule.prodEquivOfIsCompl W C hC).symm : X →ₗ[ℂ] W × C) ∘ₗ
    e ∘ₗ ((Submodule.prodEquivOfIsCompl W C hC) : W × C →ₗ[ℂ] X)
  have hdet' : LinearMap.det e' = LinearMap.det e := by
    have := LinearMap.det_conj e (Submodule.prodEquivOfIsCompl W C hC).symm
    rwa [LinearEquiv.symm_symm] at this
  have hinl : ∀ j, e' ((Module.finBasis ℂ W).prod (Module.finBasis ℂ C) (Sum.inl j)) =
      (e.restrict he (Module.finBasis ℂ W j), 0) := by
    intro j
    simp only [e', Module.Basis.prod_apply_inl_fst, Module.Basis.prod_apply_inl_snd,
      LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.coe_prodEquivOfIsCompl',
      ZeroMemClass.coe_zero, add_zero]
    exact Submodule.prodEquivOfIsCompl_symm_apply_left W C hC (e.restrict he (Module.finBasis ℂ W j))
  have hinr : ∀ j, (e' ((Module.finBasis ℂ W).prod (Module.finBasis ℂ C) (Sum.inr j))).2 =
      D (Module.finBasis ℂ C j) := by
    intro j
    simp only [e', D, Module.Basis.prod_apply_inr_fst, Module.Basis.prod_apply_inr_snd,
      LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.coe_prodEquivOfIsCompl',
      ZeroMemClass.coe_zero, zero_add, LinearMap.snd_apply, Submodule.subtype_apply]
  have hM : LinearMap.toMatrix ((Module.finBasis ℂ W).prod (Module.finBasis ℂ C))
      ((Module.finBasis ℂ W).prod (Module.finBasis ℂ C)) e' =
      Matrix.fromBlocks (LinearMap.toMatrix (Module.finBasis ℂ W) (Module.finBasis ℂ W) (e.restrict he))
        (LinearMap.toMatrix ((Module.finBasis ℂ W).prod (Module.finBasis ℂ C))
          ((Module.finBasis ℂ W).prod (Module.finBasis ℂ C)) e').toBlocks₁₂ 0
        (LinearMap.toMatrix (Module.finBasis ℂ C) (Module.finBasis ℂ C) D) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rw [Matrix.fromBlocks_apply₁₁, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, hinl,
        Module.Basis.prod_repr_inl]
    · rfl
    · rw [Matrix.fromBlocks_apply₂₁, LinearMap.toMatrix_apply, hinl, Module.Basis.prod_repr_inr]
      simp
    · rw [Matrix.fromBlocks_apply₂₂, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
        Module.Basis.prod_repr_inr, hinr]
  rw [← hdet', ← LinearMap.det_toMatrix ((Module.finBasis ℂ W).prod (Module.finBasis ℂ C)), hM,
    Matrix.det_fromBlocks_zero₂₁, LinearMap.det_toMatrix, LinearMap.det_toMatrix, hdetD]

theorem norm_det_perp {V V' : Submodule ℂ (Fin n → ℂ)}
    (h : ∀ y, y ∈ V' ↔ ∀ x ∈ V, star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0) (m : Formalism.REAL.UJ ε)
    (h1 : ∀ y ∈ V, toLin' (uMat m) y ∈ V) (h2 : ∀ y ∈ V', toLin' (uMat m⁻¹) y ∈ V') :
    ‖LinearMap.det ((toLin' (uMat m⁻¹)).restrict h2)‖ *
      ‖LinearMap.det ((toLin' (uMat m)).restrict h1)‖ = 1 := by
  classical
  have hef : ∀ y, pairMap ε V (toLin' (uMat m⁻¹) y) =
      toLin' (LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V)
        ((toLin' (uMat m)).restrict h1))ᴴ (pairMap ε V y) := by
    intro y
    funext i
    rw [pairMap_apply]
    simp only [Matrix.toLin'_apply]
    rw [form_inv]
    have hx : uMat m *ᵥ ((Module.finBasis ℂ V i : V) : Fin n → ℂ) =
        (((toLin' (uMat m)).restrict h1 (Module.finBasis ℂ V i) : V) : Fin n → ℂ) := rfl
    rw [hx, pair_sum]
    simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, LinearMap.toMatrix_apply]
  have hdet := det_of_intertwine (pairMap ε V) (pairMap_surj V) (toLin' (uMat m⁻¹)) _ hef V'
    (ker_pairMap h) h2
  rw [LinearMap.det_toLin', LinearMap.det_toLin', Matrix.det_conjTranspose,
    LinearMap.det_toMatrix] at hdet
  have hn := congrArg norm hdet
  rw [norm_mul, norm_star, norm_det] at hn
  exact hn.symm

theorem perp_modulus : ∀ (n : ℕ) (ε : Fin n → Bool) (V V' : Submodule ℂ (Fin n → ℂ)), (∀ y, y ∈ V' ↔ ∀ x ∈ V, star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0) → Module.finrank ℂ V' + Module.finrank ℂ V = n ∧ (∀ x, (∀ y ∈ V', star y ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) = 0) → x ∈ V) ∧ ∀ m : Formalism.REAL.UJ ε, ‖(uMat m).det‖ = 1 ∧ ((∀ y ∈ V, uMat m *ᵥ y ∈ V) → (∀ y ∈ V', uMat m *ᵥ y ∈ V') ∧ detOn (uMat m) V' = detOn (uMat m) V ∧ 0 < detOn (uMat m) V) := by
  intro n ε V V' h
  refine ⟨finrank_perp h, fun x hx => perp_perp h x hx, fun m => ⟨norm_det m, fun hV => ?_⟩⟩
  have hVinv : ∀ y ∈ V, uMat m⁻¹ *ᵥ y ∈ V := inv_keeps (uMat_inv_mul m) V hV
  have hV' : ∀ y ∈ V', uMat m *ᵥ y ∈ V' := by
    intro y hy
    rw [h]
    intro x hx
    have hf := form_inv m⁻¹ x y
    rw [inv_inv] at hf
    rw [hf]
    exact (h y).1 hy _ (hVinv x hx)
  have hV'inv : ∀ y ∈ V', uMat m⁻¹ *ᵥ y ∈ V' := inv_keeps (uMat_inv_mul m) V' hV'
  have k1 : ∀ y ∈ V, toLin' (uMat m) y ∈ V := fun y hy => by
    rw [Matrix.toLin'_apply]; exact hV y hy
  have k1' : ∀ y ∈ V', toLin' (uMat m) y ∈ V' := fun y hy => by
    rw [Matrix.toLin'_apply]; exact hV' y hy
  have k2 : ∀ y ∈ V, toLin' (uMat m⁻¹) y ∈ V := fun y hy => by
    rw [Matrix.toLin'_apply]; exact hVinv y hy
  have k2' : ∀ y ∈ V', toLin' (uMat m⁻¹) y ∈ V' := fun y hy => by
    rw [Matrix.toLin'_apply]; exact hV'inv y hy
  have e1 := norm_det_perp h m k1 k2'
  have e2 := congrArg norm (det_restrict_mul m V' k1' k2')
  rw [norm_mul, norm_one] at e2
  have e3 := congrArg norm (det_restrict_mul m V k1 k2)
  rw [norm_mul, norm_one] at e3
  refine ⟨hV', ?_, ?_⟩
  · unfold detOn
    rw [dif_pos k1', dif_pos k1]
    linear_combination ‖LinearMap.det ((toLin' (uMat m)).restrict k1)‖ * e2 -
      ‖LinearMap.det ((toLin' (uMat m)).restrict k1')‖ * e1
  · unfold detOn
    rw [dif_pos k1]
    refine lt_of_le_of_ne (norm_nonneg _) fun h0 => ?_
    rw [← h0, zero_mul] at e3
    exact zero_ne_one e3

end GlobalTheory.PerpModulus
