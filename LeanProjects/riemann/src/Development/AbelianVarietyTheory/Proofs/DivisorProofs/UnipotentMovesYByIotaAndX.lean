import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralEqZeroOfMulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFixingVectorPreserves

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IsoMove

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem span_E {n n₁ : ℕ} {B : Base F E} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁} {j₀ j₁ : ℕ}
    (hH : H.IsAdapted σ B X X₁ j₀ j₁) (hlat : X.L.IsLattice E) (w : Fin n → E) :
    ∃ (a b : E) (v : Fin n₁ → E), w = a • H.x + H.ι *ᵥ v + b • H.y := by
  have hL : Submodule.span E (X.L : Set (Fin n → E)) ≤ GlobalTheory.UnipLine.spanSet H.x H.y H.ι := by
    rw [Submodule.span_le]
    intro z hz
    obtain ⟨a, b, v, -, -, -, h⟩ := hH.split z hz
    exact ⟨a, b, v, h⟩
  rw [hlat.span_eq_top] at hL
  exact hL (Submodule.mem_top (x := w))

theorem span_A {n n₁ : ℕ} {B : Base F E} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁} {j₀ j₁ : ℕ}
    (hH : H.IsAdapted σ B X X₁ j₀ j₁) (hlat : X.L.IsLattice E) (w : Fin n → AE F E) :
    ∃ (a b : AE F E) (z : Fin n₁ → AE F E), w = a • incV F H.x + incM F H.ι *ᵥ z + b • incV F H.y := by
  suffices h : w ∈ GlobalTheory.UnipLine.spanSet (incV F H.x) (incV F H.y) (incM F H.ι) from h
  rw [pi_eq_sum_univ w]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  obtain ⟨a, b, v, h⟩ := span_E hH hlat (fun j => if i = j then 1 else 0)
  refine ⟨inclR (AF F) a, inclR (AF F) b, incV F v, funext fun j => ?_⟩
  have hj := congrArg (inclR (F := F) (AF F)) (congrFun h j)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, RingHom.map_mulVec] at hj
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  convert hj using 1
  · split_ifs <;> simp
  · rfl

theorem form_y_x {n n₁ : ℕ} {B : Base F E} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁} {j₀ j₁ : ℕ}
    (hσ : ∀ e, σ (σ e) = e) (hs : ∀ i j, σ (X.J j i) = -X.J i j) (hH : H.IsAdapted σ B X X₁ j₀ j₁) :
    form σ X.J H.y H.x = -1 := by
  have h := congrArg σ hH.xy
  have hs' : ∀ i j, σ (X.J i j) = -X.J j i := fun i j => hs j i
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, map_one, hs', Finset.mul_sum] at h
  simp only [form, dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [← h, Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mulVec_y {n n₁ : ℕ} {B : Base F E} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁} {j₀ j₁ : ℕ}
    (hH : H.IsAdapted σ B X X₁ j₀ j₁) (hlat : X.L.IsLattice E) (hyx : form σ X.J H.y H.x ≠ 0) (u : UA σ X.J)
    (hux : mat u *ᵥ incV F H.x = incV F H.x) :
    ∃ (c : AE F E) (z₀ : Fin n₁ → AE F E), mat u *ᵥ incV F H.y = incV F H.y + c • incV F H.x + incM F H.ι *ᵥ z₀ := by
  set q := X.J *ᵥ fun i => σ (H.x i) with hq
  set g := incV F q
  have hunit : (mat u)ᵀ * incM F X.J * (mat u).map (cA σ) = incM F X.J := u.2
  have hg : g = incM F X.J *ᵥ fun i => cA σ (incV F H.x i) := by
    simp only [g, hq, ← GlobalTheory.UnipLine.incM_mulVec_incV]
    congr 1
  have hcx : (mat u).map (cA σ) *ᵥ (fun i => cA σ (incV F H.x i)) = fun i => cA σ (incV F H.x i) := by
    funext i
    have := ((cA σ).toRingHom.map_mulVec (mat u) (incV F H.x) i).symm
    rw [hux] at this
    exact this
  have hinv : ∀ w, (mat u *ᵥ w) ⬝ᵥ g = w ⬝ᵥ g := by
    intro w
    have hT : (mat u)ᵀ *ᵥ g = g := by
      rw [hg, ← hcx, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hunit, hcx]
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT, dotProduct_comm]
  have gx : incV F H.x ⬝ᵥ g = 0 := by
    rw [GlobalTheory.UnipLine.incV_dot]; exact (congrArg _ hH.xx).trans (map_zero _)
  have gy : incV F H.y ⬝ᵥ g = inclR (AF F) (form σ X.J H.y H.x) := GlobalTheory.UnipLine.incV_dot _ _
  have hιq : H.ιᵀ *ᵥ q = 0 := by
    funext j
    have := (hH.orth (Pi.single j 1)).1
    simp only [form, Matrix.mulVec_single_one] at this
    rw [Matrix.mulVec_transpose, Pi.zero_apply, ← this, ← hq, dotProduct_comm]
    rfl
  have gi : ∀ z, (incM F H.ι *ᵥ z) ⬝ᵥ g = 0 := by
    intro z
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    have : (incM F H.ι)ᵀ *ᵥ g = 0 := by
      rw [show (incM F H.ι)ᵀ = incM F H.ιᵀ from Matrix.transpose_map.symm, GlobalTheory.UnipLine.incM_mulVec_incV, hιq]
      funext i; simp [incV]
    rw [this, zero_dotProduct]
  obtain ⟨a, b, z, h⟩ := span_A hH hlat (mat u *ᵥ incV F H.y)
  have hb : b = 1 := by
    have e1 := hinv (incV F H.y)
    rw [h, add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, gx, gi, gy, smul_zero, zero_add,
      smul_eq_mul] at e1
    simp only [zero_add] at e1
    have hu : IsUnit (inclR (F := F) (AF F) (form σ X.J H.y H.x)) := (isUnit_iff_ne_zero.2 hyx).map _
    exact hu.mul_left_cancel (a := _) (b := b) (c := 1) (by rw [mul_one, mul_comm]; exact e1)
  refine ⟨a, z, ?_⟩
  rw [h, hb, one_smul]
  abel

end GlobalTheory.IsoMove

namespace GlobalTheory.IsoMove

theorem unip_mulVec_y : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r' s' : ℕ), IsCMExt F E σ → W.IsSkew σ B r' s' →
    H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ u ∈ unip σ W H', ∃ (z : Fin d₁ → AE F E) (β : AE F E),
      mat u *ᵥ incV F H'.y = incV F H'.y + incM F H'.ι *ᵥ z + β • incV F H'.x := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H' i₀ i₁ r' s' hcm hW hH u hu
  have hσ : ∀ e, σ (σ e) = e := by
    intro e
    obtain ⟨_, _, _, hτ⟩ := hcm
    let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
    apply τ.injective
    rw [hτ, hτ, star_star]
  rw [GlobalTheory.UnipCT.unip_eq] at hu
  have hyx : form σ W.J H'.y H'.x ≠ 0 := by
    rw [form_y_x hσ hW.skew hH]; exact neg_ne_zero.2 one_ne_zero
  obtain ⟨c, z₀, h⟩ := mulVec_y hH hW.lat hyx u hu.1
  exact ⟨z₀, c, by rw [h]; abel⟩

end GlobalTheory.IsoMove
