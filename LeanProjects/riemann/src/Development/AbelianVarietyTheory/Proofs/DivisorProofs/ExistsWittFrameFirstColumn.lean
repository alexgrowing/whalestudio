import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.PlaneWitt

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open Formalism.UG (cT)

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨rfl, A, hA⟩ := h
  intro h0
  let A' : Matrix (Fin (r + s)) (Fin (r + s)) ℂ := A.submatrix id finSumFinEquiv.symm
  have h1 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hA]; ext i j; simp [A', Matrix.mul_apply]
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_mul, h0, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, Matrix.det_neg, Matrix.det_one] at h2
  simp at h2
  exact absurd h2.symm (by simp)

theorem exists_cons_front {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {s : K →+* K}
    (B : V →ₛₗ[s] V →ₗ[K] K) (hs : ∀ u v, B u v = s (B v u)) {r : ℕ} {x y : Fin r → V}
    (hx : ∀ i j, B (x i) (x j) = 0) (hy : ∀ i j, B (y i) (y j) = 0)
    (hxy : ∀ i j, B (x i) (y j) = if i = j then 1 else 0) {z w₀ : V}
    (hxz : ∀ i, B (x i) z = 0) (hyz : ∀ i, B (y i) z = 0) (hzz : B z z = 0) (hw₀ : B z w₀ = 1) :
    ∃ w : V, (∀ i j, B ((Fin.cons z x : Fin (r + 1) → V) i) ((Fin.cons z x : Fin (r + 1) → V) j) = 0) ∧
      (∀ i j, B ((Fin.cons w y : Fin (r + 1) → V) i) ((Fin.cons w y : Fin (r + 1) → V) j) = 0) ∧
      ∀ i j, B ((Fin.cons z x : Fin (r + 1) → V) i) ((Fin.cons w y : Fin (r + 1) → V) j) = if i = j then 1 else 0 := by
  have hzx : ∀ i, B z (x i) = 0 := fun i => by rw [hs, hxz, map_zero]
  have hzy : ∀ i, B z (y i) = 0 := fun i => by rw [hs, hyz, map_zero]
  have hyx : ∀ i j, B (y i) (x j) = if i = j then 1 else 0 := fun i j => by
    rw [hs, hxy]; simp [apply_ite s, eq_comm]
  obtain ⟨w₁, a1, a2, a3⟩ : ∃ w, (∀ i, B (x i) w = 0) ∧ (∀ i, B (y i) w = 0) ∧ B z w = 1 :=
    ⟨w₀ - ∑ j, B (y j) w₀ • x j - ∑ j, B (x j) w₀ • y j, fun i => by simp [hx, hxy], fun i => by simp [hy, hyx],
      by simp [hzx, hzy, hw₀]⟩
  obtain ⟨w, b1, b2, b3, b4⟩ : ∃ w, (∀ i, B (x i) w = 0) ∧ (∀ i, B (y i) w = 0) ∧ B z w = 1 ∧ B w w = 0 := by
    refine ⟨w₁ - (B w₁ w₁ / 2) • z, fun i => by simp [a1, hxz], fun i => by simp [a2, hyz], by simp [a3, hzz], ?_⟩
    have c1 : B w₁ z = 1 := by rw [hs, a3, map_one]
    have c2 : s (B w₁ w₁) = B w₁ w₁ := (hs _ _).symm
    simp only [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, c1, a3,
      hzz, map_div₀, c2, map_ofNat]
    ring
  have hwy : ∀ i, B w (y i) = 0 := fun i => by rw [hs, b2, map_zero]
  refine ⟨w, ?_, ?_, ?_⟩ <;> intro i j <;> refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [hzz, hzx, hxz, hx, b4, hwy, b2, hy, b3, hzy, b1, hxy, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

theorem exists_isWittFrame_col0 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n n₁ : ℕ) (V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (V₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n₁)
    (r s i₀ i₁ : ℕ) (H : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Plane E n n₁), B.IsGood σ → V.IsHerm σ B r s → H.IsAdapted σ B V V₁ i₀ i₁ →
    ∃ (m : ℕ) (X Y : Matrix (Fin n) (Fin (m + 1)) E), IsWittFrame σ V.Jᵀ X Y ∧
      col0 X = Matrix.of (fun i (_ : Fin 1) => H.x i) := by
  intro F E _ _ _ _ _ σ B n n₁ V V₁ r s i₀ i₁ H hB hV hH
  classical
  have hσ : IsCMExt F E σ := hB.cm
  have hJ : IsHermND σ V.Jᵀ := by
    refine ⟨fun i j => by simpa [Matrix.transpose_apply] using hV.herm j i, ?_⟩
    rw [Matrix.det_transpose]
    intro h0
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    apply det_ne_zero_of_hasSig (hV.sig w)
    have e := RingHom.map_det ((B.emb w).1) V.J
    rw [h0, map_zero] at e
    exact e.symm
  let Bf := toLinearMapₛₗ₂' E (σ : E →+* E) (RingHom.id E) V.Jᵀ
  have hB' : ∀ u v, Bf u v = ∑ i, ∑ j, σ (u i) * V.Jᵀ i j * v j := fun u v => by
    simp only [Bf, toLinearMapₛₗ₂'_apply, smul_eq_mul, RingHom.id_apply, RingHom.coe_coe]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hs : ∀ u v, Bf u v = (σ : E →+* E) (Bf v u) := fun u v => by
    simp only [hB', map_sum, map_mul, RingHom.coe_coe, sigma_sigma hσ, hJ.1]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hform : ∀ u v, Bf u v = form σ V.J v u := fun u v => by
    rw [hB']
    simp only [form, dotProduct, mulVec, Finset.mul_sum, Matrix.transpose_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have h0xx : Bf H.x H.x = 0 := (hform _ _).trans hH.xx
  have h0yy : Bf H.y H.y = 0 := (hform _ _).trans hH.yy
  have h0xy : Bf H.x H.y = 1 := by rw [hs, hform, hH.xy, map_one]
  let P : ℕ → Prop := fun r => ∃ x y : Fin (r + 1) → Fin n → E, x 0 = H.x ∧ (∀ i j, Bf (x i) (x j) = 0) ∧
    (∀ i j, Bf (y i) (y j) = 0) ∧ ∀ i j, Bf (x i) (y j) = if i = j then 1 else 0
  have hle : ∀ r, P r → r ≤ n := by
    rintro r ⟨x, y, -, -, -, e⟩
    have e1 : cT (σ : E →+* E) (of x)ᵀ * V.Jᵀ * (of y)ᵀ = 1 :=
      Matrix.ext fun i j => (gram_apply _ _ i j).trans (e i j)
    have e2 := congrArg Matrix.rank e1
    rw [Matrix.rank_one, Fintype.card_fin] at e2
    have e3 := e2.symm.le.trans ((Matrix.rank_mul_le_right _ _).trans (Matrix.rank_le_height _))
    omega
  have base : P 0 := ⟨fun _ => H.x, fun _ => H.y, rfl, fun _ _ => h0xx, fun _ _ => h0yy,
    fun i j => by
      show Bf H.x H.y = _
      rw [if_pos (Subsingleton.elim (α := Fin 1) i j)]; exact h0xy⟩
  obtain ⟨m, ⟨x, y, hx0, hx, hy, hxy⟩, hm⟩ : ∃ m, P m ∧ ¬ P (m + 1) := ⟨Nat.findGreatest P n,
    Nat.findGreatest_spec (Nat.zero_le n) base,
    fun hP => Nat.findGreatest_is_greatest (Nat.lt_succ_self _) (hle _ hP) hP⟩
  refine ⟨m, (of x)ᵀ, (of y)ᵀ, ⟨Matrix.ext fun i j => (gram_apply _ _ i j).trans (hx i j),
    Matrix.ext fun i j => (gram_apply _ _ i j).trans (hy i j),
    Matrix.ext fun i j => (gram_apply _ _ i j).trans (hxy i j), fun z h1 h2 h3 => ?_⟩, ?_⟩
  · by_contra hz
    obtain ⟨w₀, hw₀⟩ : ∃ w, Bf z w = 1 := by
      have h4 : (fun i => σ (z i)) ᵥ* V.Jᵀ ≠ 0 := fun e => hz (funext fun i => (σ : E →+* E).injective
        ((congrFun (Matrix.eq_zero_of_vecMul_eq_zero hJ.2 e) i).trans (map_zero σ).symm))
      obtain ⟨b, hb⟩ := Function.ne_iff.1 h4
      have h5 : Bf z (Pi.single b 1) = ((fun i => σ (z i)) ᵥ* V.Jᵀ) b := by
        simp [hB', Pi.single_apply, vecMul, dotProduct]
      exact ⟨(((fun i => σ (z i)) ᵥ* V.Jᵀ) b)⁻¹ • Pi.single b 1, by rw [map_smul, h5, smul_eq_mul, inv_mul_cancel₀ hb]⟩
    obtain ⟨w, e1, e2, e3⟩ := exists_cons_front Bf hs hx hy hxy
      (fun i => (gram_mulVec (of x)ᵀ z i).symm.trans (congrFun h1 i))
      (fun i => (gram_mulVec (of y)ᵀ z i).symm.trans (congrFun h2 i)) ((hB' z z).trans h3) hw₀
    let π := Equiv.swap (0 : Fin (m + 2)) 1
    refine hm ⟨fun i => (Fin.cons z x : Fin (m + 2) → Fin n → E) (π i),
      fun i => (Fin.cons w y : Fin (m + 2) → Fin n → E) (π i), ?_, fun i j => e1 _ _, fun i j => e2 _ _,
      fun i j => by rw [e3]; exact if_congr π.injective.eq_iff rfl rfl⟩
    show (Fin.cons z x : Fin (m + 2) → Fin n → E) (Equiv.swap 0 1 0) = H.x
    rw [Equiv.swap_apply_left]
    exact hx0
  · ext i j
    simp [col0, hx0]

end GlobalTheory.PlaneWitt
