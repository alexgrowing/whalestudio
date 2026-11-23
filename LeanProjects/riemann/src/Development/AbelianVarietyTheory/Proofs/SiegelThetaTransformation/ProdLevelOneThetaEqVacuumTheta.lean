import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSymplOfSelfDual
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PeriodCoordinateThetaOfSignedHeisenbergVacuumStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelOneThetaEqSmulOfSelfDualLatticeStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.VacProd

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} {X : Data E r}

theorem thetaSignExpEF_add_selfDual_lattice {L : Lt E r} (hL : SelfD X L) {w : E} (hw : IsIntegral ℤ w) (hw1 : w + cc w = 1)
    {u v : Fin r → E} (hu : u ∈ L) (hv : v ∈ L) :
    eps1 X w (u + v) = eps1 X w u * eps1 X w v * cexp (-(Real.pi * I * ((EF X u v : ℚ) : ℂ))) := by
  have hwv : w • v ∈ L := GlobalTheory.SW.TensLat.int_smul_mem hw hv
  obtain ⟨k, hk⟩ := (hL.2 u).1 hu (w • v) hwv
  have hcc : cc w = 1 - w := by rw [← hw1]; ring
  have hB : ∀ a b c d : Fin r → E,
      EF X (a + b) (c + d) = EF X a c + EF X a d + EF X b c + EF X b d := by
    intro a b c d
    simp only [GlobalTheory.SW.TensLat.EF_eq_bilin, map_add, LinearMap.add_apply]
    ring
  have hvu : EF X v (w • u) = EF X u (w • v) - EF X u v := by
    rw [GlobalTheory.SW.TensLat.EF_swap X (w • u) v, GlobalTheory.SW.TensLat.EF_smul, hcc, sub_smul, one_smul]
    simp only [GlobalTheory.SW.TensLat.EF_eq_bilin, map_sub]
    ring
  have key : EF X (u + v) (w • (u + v)) =
      EF X u (w • u) + EF X v (w • v) - EF X u v + 2 * (k : ℚ) := by
    rw [smul_add, hB, hvu, hk]; ring
  unfold GlobalTheory.Dict.eps1
  rw [key, ← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
  exact ⟨k, by push_cast; ring⟩

private theorem bilinForm_sum_smul_eq_neg_omegaStd {V : Type} [AddCommGroup V] [Module ℚ V] (B : LinearMap.BilinForm ℚ V)
    {b : Fin g ⊕ Fin g → V}
    (hb : ∀ i j, B (b i) (b j) = -(omegaStd (Pi.single i 1) (Pi.single j 1) : ℤ))
    (m m' : Fin g ⊕ Fin g → ℤ) :
    B (∑ j, m j • b j) (∑ j, m' j • b j) = -(omegaStd m m' : ℤ) := by
  have hsum : ∀ (c : Fin g ⊕ Fin g → ℤ) (y : Fin g ⊕ Fin g),
      ∑ k, c k * (Pi.single k (1 : ℤ) : Fin g ⊕ Fin g → ℤ) y = c y := by
    intro c y
    simp [Pi.single_apply]
  have h2 : ∀ j, ∑ k, m' k * omegaStd (Pi.single j (1 : ℤ)) (Pi.single k 1) =
      omegaStd (Pi.single j (1 : ℤ)) m' := by
    intro j
    unfold omegaStd
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← hsum m' (Sum.inr i), ← hsum m' (Sum.inl i), Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have h1 : ∑ j, m j * omegaStd (Pi.single j (1 : ℤ)) m' = omegaStd m m' := by
    unfold omegaStd
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← hsum m (Sum.inr i), ← hsum m (Sum.inl i), Finset.sum_mul, Finset.sum_mul,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have hZ : ∑ j, m j * ∑ k, m' k * omegaStd (Pi.single j (1 : ℤ)) (Pi.single k 1) = omegaStd m m' := by
    simp only [h2, h1]
  simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply, hb, zsmul_eq_mul]
  rw [← hZ]
  push_cast
  simp only [mul_neg, Finset.sum_neg_distrib, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

theorem EF_sum {b : Fin g ⊕ Fin g → (Fin r → E)}
    (hb : ∀ i j, EF X (b i) (b j) = -(omegaStd (Pi.single i 1) (Pi.single j 1) : ℤ))
    (m m' : Fin g ⊕ Fin g → ℤ) :
    EF X (∑ j, m j • b j) (∑ j, m' j • b j) = -(omegaStd m m' : ℤ) := by
  rw [GlobalTheory.SW.TensLat.EF_eq_bilin]
  exact bilinForm_sum_smul_eq_neg_omegaStd _ (fun i j => by rw [← GlobalTheory.SW.TensLat.EF_eq_bilin]; exact hb i j) m m'

private theorem canMult_add_add (a b : Fin g → ℝ) (m n m' n' : Fin g → ℤ) :
    GlobalTheory.CanTh.canMult a b (m + m') (n + n') = GlobalTheory.CanTh.canMult a b m n * GlobalTheory.CanTh.canMult a b m' n' *
      cexp (Real.pi * I * ((m ⬝ᵥ n' + m' ⬝ᵥ n : ℤ) : ℂ)) := by
  unfold GlobalTheory.CanTh.canMult
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [dotProduct, Pi.add_apply, Int.cast_add, mul_add, add_mul, Finset.sum_add_distrib]
  push_cast
  ring

theorem thetaSign_mul_canonicalTheta_multiplier {L : Lt E r} (hL : SelfD X L) {w : E} (hw : IsIntegral ℤ w) (hw1 : w + cc w = 1)
    {b : Fin g ⊕ Fin g → (Fin r → E)} (hbL : ∀ m : Fin g ⊕ Fin g → ℤ, ∑ j, m j • b j ∈ L)
    (hb : ∀ i j, EF X (b i) (b j) = -(omegaStd (Pi.single i 1) (Pi.single j 1) : ℤ))
    {a₁ a₂ : Fin g → ℝ} (h₁ : ∀ k, (a₁ k : ℂ) = 0 ∨ (a₁ k : ℂ) = 1 / 2)
    (he : ∀ i, eps1 X w (b (Sum.inl i)) = cexp (2 * Real.pi * I * a₁ i) ∧
      eps1 X w (b (Sum.inr i)) = cexp (2 * Real.pi * I * a₂ i)) (m : Fin g ⊕ Fin g → ℤ) :
    eps1 X w (∑ j, m j • b j) * CanTh.canMult a₁ a₂ (fun i => m (Sum.inl i)) (fun i => m (Sum.inr i)) = 1 := by
  have hbL' : ∀ m : Fin g ⊕ Fin g → ℤ, ∑ j, m j • b j ∈ L := hbL
  let P : (Fin g ⊕ Fin g → ℤ) → ℂ := fun m => eps1 X w (∑ j, m j • b j) *
    GlobalTheory.CanTh.canMult a₁ a₂ (fun i => m (Sum.inl i)) (fun i => m (Sum.inr i))
  have hP0 : P 0 = 1 := by
    simp only [P, Pi.zero_apply, zero_smul, Finset.sum_const_zero]
    unfold GlobalTheory.Dict.eps1 GlobalTheory.CanTh.canMult
    simp [GlobalTheory.SW.TensLat.EF_eq_bilin, dotProduct]
  have hadd : ∀ m m', P (m + m') = P m * P m' := by
    intro m m'
    have hE : cexp (-(Real.pi * I * ((EF X (∑ j, m j • b j) (∑ j, m' j • b j) : ℚ) : ℂ))) *
        cexp (Real.pi * I * (((fun i => m (Sum.inl i)) ⬝ᵥ (fun i => m' (Sum.inr i)) +
          (fun i => m' (Sum.inl i)) ⬝ᵥ (fun i => m (Sum.inr i)) : ℤ) : ℂ)) = 1 := by
      rw [EF_sum hb, ← Complex.exp_add, ← Complex.exp_zero, Complex.exp_eq_exp_iff_exists_int]
      refine ⟨(fun i => m (Sum.inl i)) ⬝ᵥ (fun i => m' (Sum.inr i)), ?_⟩
      have hc : ∑ i, (m (Sum.inr i) : ℂ) * (m' (Sum.inl i) : ℂ) =
          ∑ i, (m' (Sum.inl i) : ℂ) * (m (Sum.inr i) : ℂ) :=
        Finset.sum_congr rfl (fun i _ => mul_comm _ _)
      simp only [omegaStd, dotProduct]
      push_cast
      rw [Finset.sum_sub_distrib, hc]
      ring
    have h1 : eps1 X w (∑ j, (m + m') j • b j) = eps1 X w (∑ j, m j • b j) * eps1 X w (∑ j, m' j • b j) *
        cexp (-(Real.pi * I * ((EF X (∑ j, m j • b j) (∑ j, m' j • b j) : ℚ) : ℂ))) := by
      have hs : ∑ j, (m + m') j • b j = ∑ j, m j • b j + ∑ j, m' j • b j := by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      rw [hs]
      exact thetaSignExpEF_add_selfDual_lattice hL hw hw1 (hbL' m) (hbL' m')
    have h2 : GlobalTheory.CanTh.canMult a₁ a₂ (fun i => (m + m') (Sum.inl i)) (fun i => (m + m') (Sum.inr i)) =
        GlobalTheory.CanTh.canMult a₁ a₂ (fun i => m (Sum.inl i)) (fun i => m (Sum.inr i)) *
        GlobalTheory.CanTh.canMult a₁ a₂ (fun i => m' (Sum.inl i)) (fun i => m' (Sum.inr i)) *
        cexp (Real.pi * I * (((fun i => m (Sum.inl i)) ⬝ᵥ (fun i => m' (Sum.inr i)) +
          (fun i => m' (Sum.inl i)) ⬝ᵥ (fun i => m (Sum.inr i)) : ℤ) : ℂ)) :=
      canMult_add_add a₁ a₂ _ _ _ _
    show eps1 X w (∑ j, (m + m') j • b j) *
        GlobalTheory.CanTh.canMult a₁ a₂ (fun i => (m + m') (Sum.inl i)) (fun i => (m + m') (Sum.inr i)) =
      (eps1 X w (∑ j, m j • b j) * GlobalTheory.CanTh.canMult a₁ a₂ (fun i => m (Sum.inl i)) (fun i => m (Sum.inr i))) *
      (eps1 X w (∑ j, m' j • b j) * GlobalTheory.CanTh.canMult a₁ a₂ (fun i => m' (Sum.inl i)) (fun i => m' (Sum.inr i)))
    rw [h1, h2]
    linear_combination (eps1 X w (∑ j, m j • b j) * eps1 X w (∑ j, m' j • b j) *
      GlobalTheory.CanTh.canMult a₁ a₂ (fun i => m (Sum.inl i)) (fun i => m (Sum.inr i)) *
      GlobalTheory.CanTh.canMult a₁ a₂ (fun i => m' (Sum.inl i)) (fun i => m' (Sum.inr i))) * hE
  have hbase : ∀ j, P (Pi.single j 1) = 1 := by
    intro j
    have hB : ∑ k, (Pi.single j (1 : ℤ) : Fin g ⊕ Fin g → ℤ) k • b k = b j := by
      simp [Pi.single_apply]
    show eps1 X w (∑ k, (Pi.single j (1 : ℤ) : Fin g ⊕ Fin g → ℤ) k • b k) * _ = 1
    rw [hB]
    rcases j with i | i
    · have hc : GlobalTheory.CanTh.canMult a₁ a₂
          (fun i' => (Pi.single (Sum.inl i) (1 : ℤ) : Fin g ⊕ Fin g → ℤ) (Sum.inl i'))
          (fun i' => (Pi.single (Sum.inl i) (1 : ℤ) : Fin g ⊕ Fin g → ℤ) (Sum.inr i')) =
          cexp (2 * Real.pi * I * a₁ i) := by
        unfold GlobalTheory.CanTh.canMult
        congr 1
        simp [dotProduct, Pi.single_apply]
      rw [hc, (he i).1, ← Complex.exp_add]
      rcases h₁ i with h | h
      · rw [h]; simp
      · rw [h, Complex.exp_eq_one_iff]; exact ⟨1, by push_cast; ring⟩
    · have hc : GlobalTheory.CanTh.canMult a₁ a₂
          (fun i' => (Pi.single (Sum.inr i) (1 : ℤ) : Fin g ⊕ Fin g → ℤ) (Sum.inl i'))
          (fun i' => (Pi.single (Sum.inr i) (1 : ℤ) : Fin g ⊕ Fin g → ℤ) (Sum.inr i')) =
          cexp (-(2 * Real.pi * I * a₂ i)) := by
        unfold GlobalTheory.CanTh.canMult
        congr 1
        simp [dotProduct, Pi.single_apply]
      rw [hc, (he i).2, ← Complex.exp_add, Complex.exp_eq_one_iff]
      exact ⟨0, by push_cast; ring⟩
  have hsingle : ∀ j (k : ℤ), P (Pi.single j k) = 1 := by
    intro j k
    induction k using Int.induction_on with
    | zero => simpa using hP0
    | succ k ih =>
      rw [show (Pi.single j ((k : ℤ) + 1) : Fin g ⊕ Fin g → ℤ) = Pi.single j (k : ℤ) + Pi.single j 1 from
        Pi.single_add _ _ _, hadd, ih, hbase j, _root_.one_mul]
    | pred k ih =>
      have hk := hadd (Pi.single j (-(k : ℤ) - 1)) (Pi.single j 1)
      rw [← Pi.single_add, sub_add_cancel, ih, hbase j, _root_.mul_one] at hk
      exact hk.symm
  have hfin : ∀ s : Finset (Fin g ⊕ Fin g), P (∑ j ∈ s, Pi.single j (m j)) = 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hP0
    | @insert j s hj ih => rw [Finset.sum_insert hj, hadd, hsingle, ih, _root_.one_mul]
  have hm := hfin Finset.univ
  rwa [Finset.univ_sum_single] at hm

theorem prod_eq_mul_thA : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ v : TF n g, IsVac X bas w (tens (stdL E n) L) v → ∀ x ∈ X.dom, ∀ θ : (Fin g → ℂ) → ℂ, IsTheta1 X bas idx w x L θ → ∃ κ : ℂ, ∀ z : Fin n → Fin g → ℂ, ∏ b, θ (z b) = κ * thA X bas idx v x z := by
  intro E _ _ _ r X g bas idx n hs hn w hw hw1 L hL v hv x hxd θ hθ
  obtain ⟨b, hbL, hb⟩ := GlobalTheory.Dict.VacNorm.exists_sympl_of_selfD hs hL
  obtain ⟨c₁, c₂, C, hC, hc₁, hc₂, H⟩ :=
    GlobalTheory.T.periodCoordinateTheta_of_signedHeisenbergVacuum E r X g bas idx n hs hn w hw hw1 L hL v hv b hbL hb
  obtain ⟨hdet, hτ, hhx, heps, hthA⟩ := H x hxd _ _ rfl rfl
  clear H
  set M₁ : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i k => pv X idx x (b (Sum.inl k)) i with hM₁
  set M₂ : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i k => pv X idx x (b (Sum.inr k)) i with hM₂
  set h : Matrix (Fin g) (Fin g) ℂ := M₁⁻¹ with hh
  set τ : Matrix (Fin g) (Fin g) ℂ := h * M₂ with hτdef
  have hτ' : τ.IsSymm ∧ (τ.map Complex.im).PosDef := hτ
  have hM₁u : IsUnit M₁.det := (Matrix.isUnit_nonsing_inv_det_iff).1 hdet

  obtain ⟨a₁, ha₁, h₁⟩ : ∃ a : Fin g → ℝ, (fun i => (a i : ℂ)) = c₁ ∧
      ∀ k, (a k : ℂ) = 0 ∨ (a k : ℂ) = 1 / 2 := by
    refine ⟨fun k => if c₁ k = 0 then 0 else 1 / 2, ?_, ?_⟩
    · funext k; rcases hc₁ k with hk | hk <;> simp [hk]
    · intro k; rcases hc₁ k with hk | hk <;> simp [hk]
  obtain ⟨a₂, ha₂⟩ : ∃ a : Fin g → ℝ, (fun i => (a i : ℂ)) = c₂ := by
    refine ⟨fun k => if c₂ k = 0 then 0 else 1 / 2, ?_⟩
    funext k; rcases hc₂ k with hk | hk <;> simp [hk]
  subst ha₁ ha₂

  have hl : ∀ m : Fin g ⊕ Fin g → ℤ, h *ᵥ pv X idx x (∑ j, m j • b j) =
      (fun i => (m (Sum.inl i) : ℂ)) + τ *ᵥ fun i => (m (Sum.inr i) : ℂ) := by
    intro m
    have hpv : pv X idx x (∑ j, m j • b j) =
        M₁ *ᵥ (fun i => (m (Sum.inl i) : ℂ)) + M₂ *ᵥ (fun i => (m (Sum.inr i) : ℂ)) := by
      funext i
      simp only [pv, Function.comp_apply, GlobalTheory.ThFr.per_sum, GlobalTheory.ThFr.per_zsmul]
      simp only [Finset.sum_apply, Pi.smul_apply, Fintype.sum_sum_type, Pi.add_apply,
        Matrix.mulVec, dotProduct, hM₁, hM₂, Matrix.of_apply, pv, Function.comp_apply]
      simp only [zsmul_eq_mul]
      congr 1 <;> exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [hpv, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hh,
      Matrix.nonsing_inv_mul _ hM₁u, Matrix.one_mulVec]
  have hbL' : ∀ m : Fin g ⊕ Fin g → ℤ, ∑ j, m j • b j ∈ L := fun m => (hbL _).2 ⟨m, rfl⟩

  set F : (Fin g → ℂ) → ℂ := fun z => GlobalTheory.CanTh.canTh τ a₁ a₂ (h *ᵥ z) with hFdef
  have hlin : Differentiable ℂ (fun z : Fin g → ℂ => h *ᵥ z) := by
    have hd := (LinearMap.toContinuousLinearMap (Matrix.mulVecLin h)).differentiable
    simp only [LinearMap.coe_toContinuousLinearMap'] at hd
    exact hd
  have hF : IsTheta1 X bas idx w x L F := by
    refine ⟨(GlobalTheory.CanTh.differentiable_canTh hτ'.2 a₁ a₂).comp hlin, ?_⟩
    intro u hu
    obtain ⟨m, rfl⟩ := (hbL u).1 hu
    funext z
    have hxl : hx X bas idx x (z + (1 / 2 : ℂ) • pv X idx x (∑ j, m j • b j)) (pv X idx x (∑ j, m j • b j)) =
        hermForm (GlobalTheory.CanTh.imInv τ) (h *ᵥ z)
            ((fun i => (m (Sum.inl i) : ℂ)) + τ *ᵥ fun i => (m (Sum.inr i) : ℂ)) +
          1 / 2 * hermForm (GlobalTheory.CanTh.imInv τ)
            ((fun i => (m (Sum.inl i) : ℂ)) + τ *ᵥ fun i => (m (Sum.inr i) : ℂ))
            ((fun i => (m (Sum.inl i) : ℂ)) + τ *ᵥ fun i => (m (Sum.inr i) : ℂ)) := by
      rw [hhx, Matrix.mulVec_add, Matrix.mulVec_smul, hl]
      simp only [hermForm, GlobalTheory.CanTh.imInv, add_dotProduct, smul_dotProduct, smul_eq_mul]
    have hper := GlobalTheory.CanTh.canTh_add_period hτ'.1 hτ'.2 a₁ a₂ (fun i => m (Sum.inl i))
      (fun i => m (Sum.inr i))
      (l := (fun i => (m (Sum.inl i) : ℂ)) + τ *ᵥ fun i => (m (Sum.inr i) : ℂ)) rfl (h *ᵥ z)
    have key := thetaSign_mul_canonicalTheta_multiplier hL hw hw1 hbL' hb h₁ heps m
    simp only [Pi.smul_apply, smul_eq_mul, fock, hFdef]
    rw [hxl, Matrix.mulVec_add, hl, hper]
    generalize hermForm (GlobalTheory.CanTh.imInv τ) (h *ᵥ z)
      ((fun i => (m (Sum.inl i) : ℂ)) + τ *ᵥ fun i => (m (Sum.inr i) : ℂ)) = A
    generalize hermForm (GlobalTheory.CanTh.imInv τ)
      ((fun i => (m (Sum.inl i) : ℂ)) + τ *ᵥ fun i => (m (Sum.inr i) : ℂ))
      ((fun i => (m (Sum.inl i) : ℂ)) + τ *ᵥ fun i => (m (Sum.inr i) : ℂ)) = B
    have hE : cexp (-(((1 : ℕ) : ℂ) * Real.pi * (A + 1 / 2 * B))) *
        cexp (Real.pi * A + Real.pi / 2 * B) = 1 := by
      rw [← Complex.exp_add, Complex.exp_eq_one_iff]; exact ⟨0, by push_cast; ring⟩
    linear_combination (cexp (-(((1 : ℕ) : ℂ) * Real.pi * (A + 1 / 2 * B))) *
        cexp (Real.pi * A + Real.pi / 2 * B) * GlobalTheory.CanTh.canTh τ a₁ a₂ (h *ᵥ z)) * key +
      GlobalTheory.CanTh.canTh τ a₁ a₂ (h *ᵥ z) * hE
  have hF0 : F ≠ 0 := by
    intro hF0
    apply GlobalTheory.CanTh.canTh_ne_zero hτ'.1 hτ'.2 a₁ a₂
    funext ζ
    have hz := congr_fun hF0 (M₁ *ᵥ ζ)
    simp only [hFdef, Pi.zero_apply, Matrix.mulVec_mulVec, hh, Matrix.nonsing_inv_mul _ hM₁u,
      Matrix.one_mulVec] at hz
    simpa using hz
  obtain ⟨a, rfl⟩ := GlobalTheory.T.levelOne_theta_eq_smul_of_selfDual_lattice E r X g bas idx n hs hn w hw hw1 L hL x hxd θ F hθ hF hF0
  have hCd : C * h.det ^ (n / 2) ≠ 0 := mul_ne_zero hC (pow_ne_zero _ hdet.ne_zero)
  refine ⟨a ^ n * (C * h.det ^ (n / 2))⁻¹, fun z => ?_⟩
  rw [hthA z, _root_.mul_assoc (a ^ n), inv_mul_cancel_left₀ hCd]
  rw [show (∏ b, (a • F) (z b)) = a ^ n * ∏ b, F (z b) by
    simp [Finset.prod_mul_distrib, Finset.prod_const]]
  rfl

end GlobalTheory.Dict.VacProd
