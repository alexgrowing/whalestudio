import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.UmgOps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL

noncomputable section

open NumberField GlobalTheory.CuspRep GroundTheory.Automorphic UpperTheory.V.Cm

namespace UpperTheory.ConvolutionTheory.BW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}

private theorem lie_right_translate_comm (X : Lie E n) (y : GL (Fin n) (Cinf E)) (k : GL (Fin n) (Af E)) :
    ∃ X' : Lie E n, lie E n X * rt E n (infGL E n y * finGL E n k) =
      rt E n (infGL E n y * finGL E n k) * lie E n X' := by
  refine ⟨toL ((y⁻¹).val * Matrix.of X * y.val), ?_⟩
  have h := GlobalTheory.CapAdInv.rt_lie y ((y⁻¹).val * Matrix.of X * y.val)
  have e : y.val * ((y⁻¹).val * Matrix.of X * y.val) * (y⁻¹).val = Matrix.of X := by
    simp [mul_assoc]
  rw [e] at h
  have h' : lie E n (toL (Matrix.of X)) = lie E n X := rfl
  rw [h'] at h
  rw [map_mul, ← mul_assoc, ← h, mul_assoc, mul_assoc, lie_rt_fin, mul_assoc]

private theorem lie_comm (X : Lie E n) (g : GA E n) :
    ∃ X' : Lie E n, lie E n X * rt E n g = rt E n g * lie E n X' := by
  have h := lie_right_translate_comm X (Matrix.GeneralLinearGroup.map (pInf E) g) (Matrix.GeneralLinearGroup.map (pFin E) g)
  rwa [infGL_mul_finGL] at h

private def itw (g : GA E n) : Subalgebra ℂ (UC E n) where
  carrier := {u | ∃ u', uC E n u * rt E n g = rt E n g * uC E n u'}
  mul_mem' := by
    rintro a b ⟨a', ha⟩ ⟨b', hb⟩
    exact ⟨a' * b', by rw [map_mul, mul_assoc, hb, ← mul_assoc, ha, map_mul, mul_assoc]⟩
  add_mem' := by
    rintro a b ⟨a', ha⟩ ⟨b', hb⟩
    exact ⟨a' + b', by rw [map_add, add_mul, ha, hb, map_add, mul_add]⟩
  algebraMap_mem' r := ⟨algebraMap _ _ r, by rw [AlgHom.commutes]; exact Algebra.commutes _ _⟩

private theorem ιC_mem (g : GA E n) (X : Lie E n) : ιC E n X ∈ itw g := by
  obtain ⟨X', h⟩ := lie_comm X g
  exact ⟨ιC E n X', by rw [uC_ιC, uC_ιC]; exact h⟩

private theorem genC_mem (g : GA E n) (τ : E →+* ℂ) (i j : Fin n) : genC τ i j ∈ itw g := by
  rw [genC, UpperTheory.V.AlgRepEndIrreducible.eL]
  exact (itw g).smul_mem ((itw g).sub_mem (ιC_mem g _) ((itw g).smul_mem (ιC_mem g _) _)) _

private theorem exists_comm (g : GA E n) (u : UC E n) :
    ∃ u', uC E n u * rt E n g = rt E n g * uC E n u' := by
  have h : Algebra.adjoin ℂ {x : UC E n | ∃ τ i j, x = genC τ i j} ≤ itw g :=
    Algebra.adjoin_le (by rintro _ ⟨τ, i, j, rfl⟩; exact genC_mem g τ i j)
  exact h (adjoin_genC (E := E) (a := n) ▸ Algebra.mem_top)

private theorem zop_comm_rt (P : MvPolynomial ((E →+* ℂ) × Fin n) ℂ) (g : GA E n) :
    Commute (zop P) (rt E n g) := by
  refine GlobalTheory.CompanionTheory.CTFin.Slice1.commute_rt_of_mem_Zalg ?_ g
  rw [Zalg_eq_map]
  exact ⟨_, (evZ E n P).2, rfl⟩

private theorem zop_comm_uC (P : MvPolynomial ((E →+* ℂ) × Fin n) ℂ) (v : UC E n) :
    zop P * uC E n v = uC E n v * zop P := by
  have h := Subalgebra.mem_center_iff.1 (evZ E n P).2 v
  unfold zop
  rw [← map_mul, ← map_mul, h]

private theorem bnd_mono {C : ℝ} (hC : 0 ≤ C) (B : ℝ) (d : ℕ) (g : GA E n) {N M : ℕ} (h : N ≤ M) :
    B * C ^ d * AutomorphicForm.height g ^ N ≤ |B| * C ^ d * AutomorphicForm.height g ^ M := by
  have h1 := AutomorphicForm.one_le_height g
  have h2 : AutomorphicForm.height g ^ N ≤ AutomorphicForm.height g ^ M := pow_le_pow_right₀ h1 h
  have h3 : 0 ≤ C ^ d := pow_nonneg hC d
  have h4 : 0 ≤ AutomorphicForm.height g ^ N := pow_nonneg (zero_le_one.trans h1) N
  exact mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self B) h3) h2 h4 (mul_nonneg (abs_nonneg B) h3)

private theorem band_zero (C : ℝ) : Band C (0 : Sm E n) :=
  { toUmg := ((umgOps E) n).1
    band := ⟨0, fun u => ⟨0, fun α g => by simp⟩⟩ }

private theorem band_add {C : ℝ} (hC : 0 ≤ C) {φ ψ : Sm E n} (h₁ : Band C φ) (h₂ : Band C ψ) : Band C (φ + ψ) := by
  refine { toUmg := (((umgOps E) n).2 φ h₁.toUmg).2.1 ψ h₂.toUmg, band := ?_ }
  obtain ⟨N, hN⟩ := h₁.band
  obtain ⟨M, hM⟩ := h₂.band
  refine ⟨max N M, fun u => ?_⟩
  obtain ⟨B, hB⟩ := hN u
  obtain ⟨D, hD⟩ := hM u
  refine ⟨|B| + |D|, fun α g => ?_⟩
  rw [map_add, map_add]
  refine (norm_add_le _ _).trans ?_
  have := (hB α g).trans (bnd_mono hC B α.degree g (le_max_left N M))
  have := (hD α g).trans (bnd_mono hC D α.degree g (le_max_right N M))
  rw [add_mul, add_mul]
  exact add_le_add ‹_› ‹_›

private theorem band_smul {C : ℝ} {φ : Sm E n} (h : Band C φ) (c : ℂ) : Band C (c • φ) := by
  refine { toUmg := (((umgOps E) n).2 φ h.toUmg).2.2.1 c, band := ?_ }
  obtain ⟨N, hN⟩ := h.band
  refine ⟨N, fun u => ?_⟩
  obtain ⟨B, hB⟩ := hN u
  refine ⟨‖c‖ * B, fun α g => ?_⟩
  rw [map_smul, map_smul]
  show ‖c • (uC E n u (zop (MvPolynomial.monomial α 1) φ)).1 g‖ ≤ _
  rw [norm_smul, mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg c)
  rw [← mul_assoc]
  exact hB α g

private theorem band_uC {C : ℝ} {φ : Sm E n} (h : Band C φ) (v : UC E n) : Band C (uC E n v φ) := by
  refine { toUmg := (((umgOps E) n).2 φ h.toUmg).2.2.2.1 v, band := ?_ }
  obtain ⟨N, hN⟩ := h.band
  refine ⟨N, fun u => ?_⟩
  obtain ⟨B, hB⟩ := hN (u * v)
  refine ⟨B, fun α g => ?_⟩
  have e : uC E n u (zop (MvPolynomial.monomial α 1) (uC E n v φ)) =
      uC E n (u * v) (zop (MvPolynomial.monomial α 1) φ) := by
    rw [← Module.End.mul_apply (zop _), zop_comm_uC, map_mul]
    rfl
  rw [e]
  exact hB α g

private theorem band_rt {C : ℝ} (hC : 0 ≤ C) {φ : Sm E n} (h : Band C φ) (g : GA E n) : Band C (rt E n g φ) := by
  refine { toUmg := (((umgOps E) n).2 φ h.toUmg).2.2.2.2.1 g, band := ?_ }
  obtain ⟨N, hN⟩ := h.band
  refine ⟨N, fun u => ?_⟩
  obtain ⟨u', hu⟩ := exists_comm g u
  obtain ⟨B, hB⟩ := hN u'
  have hc : 0 ≤ AutomorphicForm.heightConst E n * AutomorphicForm.height g :=
    mul_nonneg (zero_le_one.trans AutomorphicForm.one_le_heightConst) (AutomorphicForm.height_pos g).le
  refine ⟨|B| * (AutomorphicForm.heightConst E n * AutomorphicForm.height g) ^ N, fun α x => ?_⟩
  have e : uC E n u (zop (MvPolynomial.monomial α 1) (rt E n g φ)) =
      rt E n g (uC E n u' (zop (MvPolynomial.monomial α 1) φ)) := by
    rw [← Module.End.mul_apply (zop _), (zop_comm_rt _ g).eq, Module.End.mul_apply,
      ← Module.End.mul_apply (uC E n u), hu]
    rfl
  rw [e]
  show ‖(uC E n u' (zop (MvPolynomial.monomial α 1) φ)).1 (x * g)‖ ≤ _
  refine (hB α (x * g)).trans ((bnd_mono hC B α.degree (x * g) le_rfl).trans ?_)
  have h3 : 0 ≤ |B| * C ^ α.degree := mul_nonneg (abs_nonneg B) (pow_nonneg hC _)
  have h4 : AutomorphicForm.height (x * g) ≤
      AutomorphicForm.heightConst E n * AutomorphicForm.height g * AutomorphicForm.height x := by
    have := AutomorphicForm.height_mul_le x g
    nlinarith [this]
  calc |B| * C ^ α.degree * AutomorphicForm.height (x * g) ^ N
      ≤ |B| * C ^ α.degree * (AutomorphicForm.heightConst E n * AutomorphicForm.height g * AutomorphicForm.height x) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (AutomorphicForm.height_pos _).le h4 N) h3
    _ = _ := by rw [mul_pow]; ring

private theorem band_finsum {C : ℝ} (hC : 0 ≤ C) {Q : Type*} (f : Q → Module.End ℂ (Sm E n)) {φ : Sm E n}
    (hf : ∀ c, Band C (f c φ)) : Band C ((∑ᶠ c, f c) φ) := by
  classical
  by_cases h : (Function.support f).Finite
  · rw [finsum_eq_sum_of_support_subset (s := h.toFinset) _ (by simp), LinearMap.sum_apply]
    exact Finset.sum_induction _ (Band C) (fun _ _ => band_add hC) (band_zero C) fun c _ => hf c
  · rw [finsum_of_infinite_support h]
    exact band_zero C

private theorem band_hk {C : ℝ} (hC : 0 ≤ C) {φ : Sm E n} (h : Band C φ) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 E)) (j : ℕ) :
    Band C (hk n w j φ) := by
  unfold hk
  rw [LinearMap.smul_apply]
  refine band_smul (band_finsum hC _ fun c => ?_) _
  rw [LinearMap.smul_apply]
  exact band_smul (band_rt hC h _) _

end UpperTheory.ConvolutionTheory.BW

theorem UpperTheory.ConvolutionTheory.BW.bandOps :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.BandOps E := by
  intro E _ _ _ n C hC
  exact ⟨UpperTheory.ConvolutionTheory.BW.band_zero C, fun φ h => ⟨fun ψ h₂ => UpperTheory.ConvolutionTheory.BW.band_add hC h h₂, UpperTheory.ConvolutionTheory.BW.band_smul h,
    UpperTheory.ConvolutionTheory.BW.band_uC h, UpperTheory.ConvolutionTheory.BW.band_rt hC h, fun w j => UpperTheory.ConvolutionTheory.BW.band_hk hC h w j⟩⟩
