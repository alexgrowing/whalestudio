import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom

noncomputable section

namespace GlobalTheory.ThK.UnipDom.CoSkew

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_inclR (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (AF F) (σ e) := by
  simp [cA, inclR, Algebra.TensorProduct.map_tmul]

theorem cA_cA {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e) (a : AE F E) : cA σ (cA σ a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [cA, Algebra.TensorProduct.map_tmul, hσ]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem conj_conj {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hcm.2.2.2, hcm.2.2.2, star_star]

section Form

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem fA_add_left (v v' w : Fin n → AE F E) : fA σ J (v + v') w = fA σ J v w + fA σ J v' w := by
  simp [fA, add_dotProduct]

theorem fA_sub_left (v v' w : Fin n → AE F E) : fA σ J (v - v') w = fA σ J v w - fA σ J v' w := by
  simp [fA, sub_dotProduct]

theorem fA_smul_left (a : AE F E) (v w : Fin n → AE F E) : fA σ J (a • v) w = a * fA σ J v w := by
  simp [fA, smul_dotProduct]

theorem fA_add_right (v w w' : Fin n → AE F E) : fA σ J v (w + w') = fA σ J v w + fA σ J v w' := by
  simp only [fA, dotProduct, Matrix.mulVec, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem fA_sub_right (v w w' : Fin n → AE F E) : fA σ J v (w - w') = fA σ J v w - fA σ J v w' := by
  simp only [fA, dotProduct, Matrix.mulVec, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]

theorem fA_smul_right (a : AE F E) (v w : Fin n → AE F E) : fA σ J v (a • w) = cA σ a * fA σ J v w := by
  simp only [fA, dotProduct, Matrix.mulVec, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem fA_sum_left {ι : Type} (s : Finset ι) (f : ι → Fin n → AE F E) (w : Fin n → AE F E) :
    fA σ J (∑ j ∈ s, f j) w = ∑ j ∈ s, fA σ J (f j) w := by
  simp only [fA, dotProduct, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem fA_incV (a b : Fin n → E) : fA σ J (incV F a) (incV F b) = inclR (AF F) (form σ J a b) := by
  simp [fA, form, incV, incM, dotProduct, Matrix.mulVec, cA_inclR, map_sum, map_mul]

theorem fA_mat (g : UA σ J) (v w : Fin n → AE F E) : fA σ J (mat g *ᵥ v) (mat g *ᵥ w) = fA σ J v w := by
  have hg : (mat g)ᵀ * incM F J * (mat g).map (cA σ) = incM F J := g.2
  have h1 : (fun i => cA σ ((mat g *ᵥ w) i)) = (mat g).map (cA σ) *ᵥ fun i => cA σ (w i) := by
    funext i; simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  unfold fA
  rw [h1, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul,
    ← Matrix.mul_assoc, hg, ← Matrix.dotProduct_mulVec]

theorem fA_skew (hσ : ∀ e, σ (σ e) = e) (hJ : ∀ i j, σ (J i j) = -J j i) (v w : Fin n → AE F E) :
    cA σ (fA σ J v w) = -fA σ J w v := by
  simp only [fA, dotProduct, Matrix.mulVec, map_sum, map_mul, cA_cA hσ, incM, Matrix.map_apply, cA_inclR, hJ, map_neg]
  rw [← Finset.sum_neg_distrib]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem vecMul_incM (w : Fin n → AE F E) (i : Fin n) :
    (w ᵥ* incM F J) i = fA σ J w (incV F (Pi.single i 1)) := by
  have h : (fun k => cA σ (incV F (Pi.single i (1 : E)) k)) = Pi.single i 1 := by
    funext k
    by_cases h : k = i
    · subst h; simp [incV, cA_inclR]
    · simp [incV, h]
  unfold fA
  rw [h, Matrix.mulVec_single_one]
  simp [Matrix.vecMul, dotProduct, Matrix.col]

end Form

variable {n : ℕ}

theorem incV_add (a b : Fin n → E) : incV F (a + b) = incV F a + incV F b := by
  funext i; simp [incV]

theorem incV_smul (s : E) (a : Fin n → E) : incV F (s • a) = inclR (F := F) (AF F) s • incV F a := by
  funext i; simp [incV, Pi.smul_apply, smul_eq_mul]

theorem incV_mulVec {m : ℕ} (M : Matrix (Fin n) (Fin m) E) (z : Fin m → E) :
    incV F (M *ᵥ z) = incM F M *ᵥ incV F z := by
  funext i; simp [incV, incM, Matrix.mulVec, dotProduct, map_sum, map_mul]

end GlobalTheory.ThK.UnipDom.CoSkew

namespace GlobalTheory.ThK.UnipDom.CoSkew

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem det_ne_zero {σ : E →ₐ[F] E} {B : Base F E} {d : ℕ} {W : Spc F E d} {r s : ℕ} (h : W.IsSkew σ B r s) :
    W.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨hrs, A, hA⟩ := h.sig w
  set M := Complex.I • W.J.map (B.emb w).1 with hM
  let e : Fin r ⊕ Fin s ≃ Fin d := finSumFinEquiv.trans (finCongr hrs)
  have key : (A.submatrix id e.symm)ᵀ * M * (A.submatrix id e.symm).map star =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA]
    ext i j
    simp [Matrix.mul_apply]
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_mul, Matrix.det_mul] at hdet
  intro h0
  have h1 : (W.J.map (B.emb w).1).det = 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  have h2 : M.det = 0 := by rw [hM, Matrix.det_smul, h1, mul_zero]
  rw [h2] at hdet
  simp [Matrix.det_neg] at hdet
  exact pow_ne_zero s (neg_ne_zero.mpr one_ne_zero) hdet.symm

theorem spans {σ : E →ₐ[F] E} {B : Base F E} {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁}
    {r s i₀ i₁ : ℕ} (hsk : W.IsSkew σ B r s) (had : H'.IsAdapted σ B W W₁ i₀ i₁) (v : Fin d → E) :
    ∃ (z : Fin d₁ → E) (a b : E), v = a • H'.x + H'.ι *ᵥ z + b • H'.y := by
  have hv : v ∈ Submodule.span E (W.L : Set (Fin d → E)) := by
    rw [hsk.lat.span_eq_top]; trivial
  induction hv using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, b, u, -, -, -, h⟩ := had.split z hz
    exact ⟨u, a, b, h⟩
  | zero => exact ⟨0, 0, 0, by simp⟩
  | add p q _ _ hp hq =>
    obtain ⟨z, a, b, rfl⟩ := hp
    obtain ⟨z', a', b', rfl⟩ := hq
    refine ⟨z + z', a + a', b + b', ?_⟩
    rw [Matrix.mulVec_add, add_smul, add_smul]
    abel
  | smul c p _ hp =>
    obtain ⟨z, a, b, rfl⟩ := hp
    refine ⟨c • z, c * a, c * b, ?_⟩
    rw [Matrix.mulVec_smul, smul_add, smul_add, mul_smul, mul_smul]

theorem mem_gen {σ : E →ₐ[F] E} {d d₁ : ℕ} {W : Spc F E d} {H' : Plane E d d₁} {u : UA σ W.J}
    (hu : u ∈ unip σ W H') : mat u *ᵥ incV F H'.x = incV F H'.x ∧
      ∀ z, ∃ a : AE F E, mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x := by
  let S : Subgroup (UA σ W.J) :=
    { carrier := {u | mat u *ᵥ incV F H'.x = incV F H'.x ∧
        ∀ z, ∃ a : AE F E, mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x}
      one_mem' := ⟨by simp [mat], fun z => ⟨0, by simp [mat]⟩⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        have hm : mat (a * b) = mat a * mat b := rfl
        refine ⟨by rw [hm, ← Matrix.mulVec_mulVec, hb, ha], fun z => ?_⟩
        obtain ⟨p, hp⟩ := hb' z
        obtain ⟨q, hq⟩ := ha' z
        refine ⟨q + p, ?_⟩
        rw [hm, ← Matrix.mulVec_mulVec, hp, Matrix.mulVec_add, Matrix.mulVec_smul, hq, ha, add_smul]
        abel
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        have hi : mat a⁻¹ * mat a = 1 := by simp [mat]
        have hx : mat a⁻¹ *ᵥ incV F H'.x = incV F H'.x := by
          conv_lhs => rw [← ha]
          rw [Matrix.mulVec_mulVec, hi, Matrix.one_mulVec]
        refine ⟨hx, fun z => ?_⟩
        obtain ⟨p, hp⟩ := ha' z
        refine ⟨-p, ?_⟩
        have hz : incM F H'.ι *ᵥ z = mat a *ᵥ (incM F H'.ι *ᵥ z) - p • incV F H'.x := by rw [hp]; abel
        conv_lhs => rw [hz]
        rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hi, Matrix.one_mulVec, Matrix.mulVec_smul, hx, neg_smul,
          sub_eq_add_neg] }
  exact (Subgroup.closure_le S).mpr (fun _ h => h) hu

end GlobalTheory.ThK.UnipDom.CoSkew

namespace GlobalTheory.ThK.UnipDom.CoSkew

theorem coC_sub_conj_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (r s i₀ i₁ : ℕ), IsCMExt F E σ →
    W.IsSkew σ B r s → H'.IsAdapted σ B W W₁ i₀ i₁ → ∃ g : (Fin d₁ → AE F E) → AE F E, Continuous g ∧
      ∀ u ∈ unip σ W H', coC σ W.J H' u - cA σ (coC σ W.J H' u) = g (coA σ W.J H' u) := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H' r s i₀ i₁ hcm hsk had
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hσ := conj_conj hcm
  have hJ : ∀ i j, σ (W.J i j) = -W.J j i := fun i j => hsk.skew j i
  have hdet := det_ne_zero hsk
  choose zc sc tc hzc using fun i : Fin d => spans hsk had (Pi.single i 1)
  let Pv : (Fin d₁ → AE F E) → Fin d → AE F E := fun a i =>
    ∑ j, inclR (F := F) (AF F) (σ (zc i j)) * cA σ (a j)
  let Wv : (Fin d₁ → AE F E) → Fin d → AE F E := fun a => Pv a ᵥ* incM F W.J⁻¹
  refine ⟨fun a => -fA σ W.J (Wv a) (Wv a), ?_, ?_⟩
  · have hc : Continuous (cA σ : AE F E → AE F E) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
    simp only [fA, Wv, Pv, dotProduct, Matrix.mulVec, Matrix.vecMul]
    fun_prop
  · intro u hu
    obtain ⟨hx, hι⟩ := mem_gen hu
    set X := incV F H'.x with hX
    set Y := incV F H'.y with hY
    set U := mat u with hU
    set α := coA σ W.J H' u with hα
    set c := coC σ W.J H' u with hc
    have hcdef : fA σ W.J (U *ᵥ Y) Y = c := rfl
    have hxx : fA σ W.J X X = 0 := by rw [fA_incV, had.xx, map_zero]
    have hyy : fA σ W.J Y Y = 0 := by rw [fA_incV, had.yy, map_zero]
    have hxy : fA σ W.J X Y = 1 := by rw [fA_incV, had.xy, map_one]
    have hyx : fA σ W.J Y X = -1 := by
      have := fA_skew σ W.J hσ hJ X Y
      rw [hxy, map_one] at this
      linear_combination this
    have hιy : ∀ z, fA σ W.J (incV F (H'.ι *ᵥ z)) Y = 0 := fun z => by rw [fA_incV, (had.orth z).2, map_zero]
    have hιx : ∀ z, fA σ W.J (incV F (H'.ι *ᵥ z)) X = 0 := fun z => by rw [fA_incV, (had.orth z).1, map_zero]
    have hyι : ∀ z, fA σ W.J Y (incV F (H'.ι *ᵥ z)) = 0 := fun z => by
      have := fA_skew σ W.J hσ hJ (incV F (H'.ι *ᵥ z)) Y
      rw [hιy, map_zero] at this
      linear_combination this
    have hxι : ∀ z, fA σ W.J X (incV F (H'.ι *ᵥ z)) = 0 := fun z => by
      have := fA_skew σ W.J hσ hJ (incV F (H'.ι *ᵥ z)) X
      rw [hιx, map_zero] at this
      linear_combination this
    have hUyx : fA σ W.J (U *ᵥ Y) X = -1 := by
      have := fA_mat σ W.J u Y X
      rw [← hU, hx] at this
      rw [this, hyx]
    have hxUy : fA σ W.J X (U *ᵥ Y) = 1 := by
      have := fA_mat σ W.J u X Y
      rw [← hU, hx] at this
      rw [this, hxy]
    have hUyUy : fA σ W.J (U *ᵥ Y) (U *ᵥ Y) = 0 := by rw [hU, fA_mat, hyy]
    have hyUy : fA σ W.J Y (U *ᵥ Y) = -cA σ c := by
      rw [← hcdef, fA_skew σ W.J hσ hJ, neg_neg]

    have hβ : ∀ z : Fin d₁ → E, U *ᵥ incV F (H'.ι *ᵥ z) =
        incV F (H'.ι *ᵥ z) + (∑ j, inclR (F := F) (AF F) (z j) * α j) • X := by
      intro z
      obtain ⟨a, ha⟩ := hι (incV F z)
      rw [← incV_mulVec] at ha
      rw [ha]
      congr 2
      have h1 : fA σ W.J (U *ᵥ incV F (H'.ι *ᵥ z)) Y = a := by
        rw [ha, fA_add_left, fA_smul_left, hιy, hxy]; ring
      have h2 : incV F z = ∑ j, inclR (F := F) (AF F) (z j) • Pi.single j (1 : AE F E) := by
        funext k; simp [incV, Finset.sum_apply, Pi.single_apply]
      rw [← h1, incV_mulVec, h2, Matrix.mulVec_sum, Matrix.mulVec_sum, fA_sum_left]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, fA_smul_left]
      rfl
    set w := U *ᵥ Y - Y - c • X with hw
    have hwX : fA σ W.J w X = 0 := by
      rw [hw, fA_sub_left, fA_sub_left, fA_smul_left, hUyx, hyx, hxx]; ring
    have hwY : fA σ W.J w Y = 0 := by
      rw [hw, fA_sub_left, fA_sub_left, fA_smul_left, hcdef, hyy, hxy]; ring
    have hwι : ∀ z : Fin d₁ → E, fA σ W.J w (incV F (H'.ι *ᵥ z)) = cA σ (∑ j, inclR (F := F) (AF F) (z j) * α j) := by
      intro z
      set β := ∑ j, inclR (F := F) (AF F) (z j) * α j
      have hpre : incV F (H'.ι *ᵥ z) = U *ᵥ (incV F (H'.ι *ᵥ z) - β • X) := by
        rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hβ, hx]; abel
      have hUι : fA σ W.J (U *ᵥ Y) (incV F (H'.ι *ᵥ z)) = cA σ β := by
        rw [hpre, hU, fA_mat, fA_sub_right, fA_smul_right, hyι, hyx]; ring
      rw [hw, fA_sub_left, fA_sub_left, fA_smul_left, hUι, hyι, hxι]; ring
    have hww : c - cA σ c = -fA σ W.J w w := by
      rw [hw]
      simp only [fA_sub_left, fA_sub_right, fA_smul_left, fA_smul_right]
      rw [hUyUy, hcdef, hUyx, hyUy, hyy, hyx, hxUy, hxy, hxx]
      ring
    have hpair : w = Wv α := by
      have hinv : incM F W.J * incM F W.J⁻¹ = 1 := by
        unfold incM
        rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)]
        exact Matrix.map_one _ (map_zero _) (map_one _)
      have hv : w ᵥ* incM F W.J = Pv α := by
        funext i
        rw [vecMul_incM, hzc i, incV_add, incV_add, incV_smul, incV_smul, fA_add_right, fA_add_right,
          fA_smul_right, fA_smul_right, hwX, hwY, hwι]
        simp only [Pv, map_sum, map_mul, cA_inclR]
        ring
      calc w = w ᵥ* (incM F W.J * incM F W.J⁻¹) := by rw [hinv, Matrix.vecMul_one]
        _ = Wv α := by rw [← Matrix.vecMul_vecMul, hv]
    rw [hww, hpair]

end GlobalTheory.ThK.UnipDom.CoSkew
