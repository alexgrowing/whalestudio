import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar

set_option autoImplicit false

noncomputable section

open scoped TensorProduct Matrix

namespace GlobalTheory.HalfGeo

theorem linSt_norm_sum_lt_one {K α : Type} [NormedField K] [IsUltrametricDist K] (S : Finset α) (g : α → K)
    (h : ∀ i ∈ S, ‖g i‖ < 1) : ‖∑ i ∈ S, g i‖ < 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _)
      (max_lt (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem linSt_norm_sub_le_max {K : Type} [NormedField K] [IsUltrametricDist K] (x y : K) :
    ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]; exact IsUltrametricDist.norm_add_le_max _ _

theorem linSt : LinSt := by
  intro p _ _ hf T _ _ _ _ N hN e s u B J hBJ hdiv b b' hbb β β' hβ hβ' hγ hγ'
  classical
  set f := algebraMap ℤ_[p] ℂ_[p] with hfdef
  have hp : ‖(p : ℂ_[p])‖ < 1 := by
    have h := PadicComplex.norm_extends' p (p : ℚ_[p])
    have h2 : ‖(p : ℚ_[p])‖ < 1 := Padic.norm_p_lt_one
    rw [← h] at h2
    simpa using h2
  set G : Matrix (Fin N) (Fin N) ℤ_[p] := Matrix.of fun m m' => e (s m) (s m') with hG
  set φ : ℤ_[p] →+* ZMod p := PadicInt.toZMod with hφ
  set Bp : Matrix (Fin N) (Fin N) (ZMod p) := B.map (Int.castRingHom (ZMod p)) with hBp
  set Jp : Matrix (Fin N) (Fin N) (ZMod p) := J.map (Int.castRingHom (ZMod p)) with hJp
  have hφp : φ (p : ℤ_[p]) = 0 := by rw [map_natCast]; exact ZMod.natCast_self p
  have hGφ : G.map φ = φ u • Bp := by
    ext m m'
    obtain ⟨c, hc⟩ := hdiv m m'
    have h1 : e (s m) (s m') = u * (B m m' : ℤ_[p]) + p * c := by rw [← hc]; ring
    simp [G, Bp, h1, hφp]
  have hJB : J * B.transpose = 1 := mul_eq_one_comm.mp hBJ
  have hdetB : IsUnit B.det := by
    have h := congrArg Matrix.det hBJ
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
    exact ⟨⟨_, _, h, by rw [mul_comm]; exact h⟩, rfl⟩
  have hdetG : IsUnit G.det := by
    by_contra hn
    have hmem : G.det ∈ IsLocalRing.maximalIdeal ℤ_[p] := (IsLocalRing.mem_maximalIdeal _).2 hn
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker] at hmem
    have h2 : φ G.det = (φ u) ^ N * ((B.det : ℤ) : ZMod p) := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hGφ, Matrix.det_smul, Fintype.card_fin, hBp,
        ← RingHom.mapMatrix_apply, ← RingHom.map_det, eq_intCast]
    have h3 : IsUnit ((φ u) ^ N * ((B.det : ℤ) : ZMod p)) :=
      ((u.isUnit.map φ).pow N).mul (hdetB.map (Int.castRingHom (ZMod p)))
    rw [← h2, hmem] at h3
    exact not_isUnit_zero h3
  set H := G⁻¹ with hH
  have hGH : G * H = 1 := Matrix.mul_nonsing_inv G hdetG
  set Gc := G.map f with hGc
  set Hc := H.map f with hHc
  have hGHc : Gc * Hc = 1 := by
    rw [hGc, hHc, ← Matrix.map_mul, hGH, Matrix.map_one _ (map_zero f) (map_one f)]
  set eC := e.baseChange ℂ_[p] with heC
  let v : Fin N → ℂ_[p] ⊗[ℤ_[p]] T := fun m => (1 : ℂ_[p]) ⊗ₜ s m
  have hv : ∀ k l, eC (v k) (v l) = Gc k l := by
    intro k l
    show e.baseChange ℂ_[p] ((1 : ℂ_[p]) ⊗ₜ s k) ((1 : ℂ_[p]) ⊗ₜ s l) = f (e (s k) (s l))
    rw [LinearMap.BilinForm.baseChange_tmul, mul_one, Algebra.smul_def, mul_one]
  have hexp : ∀ c c' : Fin N → ℂ_[p], eC (∑ k, c k • v k) (∑ l, c' l • v l) =
      ∑ k, ∑ l, c k * c' l * Gc k l := by
    intro c c'
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hv]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have hexp1 : ∀ (c : Fin N → ℂ_[p]) (m : Fin N), eC (∑ k, c k • v k) (v m) = (Matrix.vecMul c Gc) m := by
    intro c m
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hv]
    rfl
  have hli : LinearIndependent ℂ_[p] v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 : Matrix.vecMul g Gc = 0 := by
      funext m
      rw [← hexp1, hg]
      simp
    have h1 : g = Matrix.vecMul g (Gc * Hc) := by rw [hGHc, Matrix.vecMul_one]
    intro i
    rw [h1, ← Matrix.vecMul_vecMul, h0, Matrix.zero_vecMul]
    rfl
  have hcard : Fintype.card (Fin N) = Module.finrank ℂ_[p] (ℂ_[p] ⊗[ℤ_[p]] T) := by
    rw [Fintype.card_fin, Module.finrank_baseChange, hN]
  let bb := basisOfLinearIndependentOfCardEqFinrank' v hli hcard
  have hbbv : ∀ k, bb k = v k := fun k => by simp [bb]
  have hsum : ∀ w, w = ∑ k, bb.repr w k • v k := fun w => by
    conv_lhs => rw [← bb.sum_repr w]
    simp only [hbbv]
  set x := bb.repr b with hx
  set x' := bb.repr b' with hx'
  have hb : b = ∑ k, x k • v k := hsum b
  have hb' : b' = ∑ k, x' k • v k := hsum b'
  have hx0 : ∑ k, ∑ l, x k * x' l * Gc k l = 0 := by rw [← hexp, ← hb, ← hb']; exact hbb
  obtain ⟨γ, hγdef⟩ : ∃ γ : Fin N → ℂ_[p], γ = Matrix.vecMul x Gc := ⟨_, rfl⟩
  obtain ⟨γ', hγdef'⟩ : ∃ γ : Fin N → ℂ_[p], γ = Matrix.vecMul x' Gc := ⟨_, rfl⟩
  have hγm : ∀ m, eC b (v m) = γ m := by intro m; rw [hγdef, hb]; exact hexp1 x m
  have hγm' : ∀ m, eC b' (v m) = γ' m := by intro m; rw [hγdef', hb']; exact hexp1 x' m
  have hγn : ∀ m, ‖γ m‖ ≤ 1 := by
    intro m
    have h2 : γ m = β m - (β m - eC b (v m)) := by rw [hγm]; ring
    rw [h2]; exact (linSt_norm_sub_le_max _ _).trans (max_le (hβ m) (hγ m).le)
  have hγn' : ∀ m, ‖γ' m‖ ≤ 1 := by
    intro m
    have h2 : γ' m = β' m - (β' m - eC b' (v m)) := by rw [hγm']; ring
    rw [h2]; exact (linSt_norm_sub_le_max _ _).trans (max_le (hβ' m) (hγ' m).le)
  have hHn : ∀ i j, ‖Hc i j‖ ≤ 1 := fun i j => by rw [hHc, Matrix.map_apply]; exact hf _
  have hxn : ∀ k, ‖x k‖ ≤ 1 := by
    have hxγ : x = Matrix.vecMul γ Hc := by rw [hγdef, Matrix.vecMul_vecMul, hGHc, Matrix.vecMul_one]
    intro k; rw [hxγ]
    simp only [Matrix.vecMul, dotProduct]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun m _ => ?_
    rw [norm_mul]; exact mul_le_one₀ (hγn m) (norm_nonneg _) (hHn _ _)
  have hxn' : ∀ k, ‖x' k‖ ≤ 1 := by
    have hxγ : x' = Matrix.vecMul γ' Hc := by rw [hγdef', Matrix.vecMul_vecMul, hGHc, Matrix.vecMul_one]
    intro k; rw [hxγ]
    simp only [Matrix.vecMul, dotProduct]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun m _ => ?_
    rw [norm_mul]; exact mul_le_one₀ (hγn' m) (norm_nonneg _) (hHn _ _)
  set Jz : Matrix (Fin N) (Fin N) ℤ_[p] := J.map (Int.castRingHom ℤ_[p]) with hJz
  set D : Matrix (Fin N) (Fin N) ℤ_[p] := G * Jz * G.transpose - (u : ℤ_[p]) • G with hD
  have hDφ : D.map φ = 0 := by
    have hJzφ : Jz.map φ = Jp := by ext; simp [Jz, Jp]
    have hJBp : Jp * Bp.transpose = 1 := by
      rw [hJp, hBp, ← Matrix.transpose_map, ← Matrix.map_mul, hJB, Matrix.map_one _ (map_zero _) (map_one _)]
    have hsm : ((u : ℤ_[p]) • G).map φ = φ u • G.map φ := by ext; simp
    rw [hD, Matrix.map_sub _ (map_sub φ), Matrix.map_mul, Matrix.map_mul, hsm, Matrix.transpose_map, hGφ, hJzφ]
    simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, hJBp,
      Matrix.mul_one, sub_self]
  have hDn : ∀ k l, ‖f (D k l)‖ ≤ ‖(p : ℂ_[p])‖ := by
    intro k l
    have h0 : φ (D k l) = 0 := by
      have := congrFun (congrFun hDφ k) l
      simpa using this
    have hmem : D k l ∈ IsLocalRing.maximalIdeal ℤ_[p] := by rw [← PadicInt.ker_toZMod]; exact h0
    have hlt : ‖D k l‖ < 1 := PadicInt.mem_nonunits.1 ((IsLocalRing.mem_maximalIdeal _).1 hmem)
    obtain ⟨c, hc⟩ := (PadicInt.norm_lt_one_iff_dvd _).1 hlt
    rw [hc, map_mul, map_natCast, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hf c)
  have hJc : ∀ m m', ((J m m' : ℤ) : ℂ_[p]) = (Jz.map f) m m' := by intro m m'; rw [Matrix.map_apply, hJz, Matrix.map_apply, eq_intCast, map_intCast]
  have hM : Gc * Jz.map f * Gc.transpose = D.map f + f u • Gc := by
    have hsm : ((u : ℤ_[p]) • G).map f = f u • G.map f := by ext; simp
    rw [hGc, hD, Matrix.map_sub _ (map_sub f), Matrix.map_mul, Matrix.map_mul, hsm, Matrix.transpose_map]
    abel
  have hsumγ : ∑ m, ∑ m', ((J m m' : ℤ) : ℂ_[p]) * (γ m * γ' m') = γ ⬝ᵥ ((Jz.map f) *ᵥ γ') := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, hJc]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_
    ring
  have hre : γ ⬝ᵥ ((Jz.map f) *ᵥ γ') = x ⬝ᵥ ((Gc * Jz.map f * Gc.transpose) *ᵥ x') := by
    rw [hγdef, hγdef', ← Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec]
  have hGx : x ⬝ᵥ (Gc *ᵥ x') = 0 := by
    rw [← hx0]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hT : ‖∑ m, ∑ m', ((J m m' : ℤ) : ℂ_[p]) * (γ m * γ' m')‖ ≤ ‖(p : ℂ_[p])‖ := by
    rw [hsumγ, hre, hM, Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul, hGx,
      smul_zero, add_zero]
    simp only [dotProduct, Matrix.mulVec]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun k _ => ?_
    rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) (hxn k)).trans ?_
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun l _ => ?_
    rw [norm_mul, Matrix.map_apply]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hxn' l)).trans (hDn k l)
  have hdiff : ‖∑ m, ∑ m', ((J m m' : ℤ) : ℂ_[p]) * (β m * β' m') -
      ∑ m, ∑ m', ((J m m' : ℤ) : ℂ_[p]) * (γ m * γ' m')‖ < 1 := by
    rw [← Finset.sum_sub_distrib]
    refine linSt_norm_sum_lt_one _ _ fun m _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine linSt_norm_sum_lt_one _ _ fun m' _ => ?_
    rw [← mul_sub, norm_mul]
    have hJn : ‖((J m m' : ℤ) : ℂ_[p])‖ ≤ 1 := by rw [← map_intCast f]; exact hf _
    have h1 : ‖β m * β' m' - γ m * γ' m'‖ < 1 := by
      have h3 : β m * β' m' - γ m * γ' m' = (β m - γ m) * β' m' + γ m * (β' m' - γ' m') := by ring
      rw [h3]
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
      · rw [norm_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (hβ' m')) (by rw [← hγm]; exact hγ m)
      · rw [norm_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (hγn m)) (by rw [← hγm']; exact hγ' m')
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hJn) h1
  have hfin := lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hdiff (hT.trans_lt hp))
  rw [sub_add_cancel] at hfin
  exact hfin

end GlobalTheory.HalfGeo
