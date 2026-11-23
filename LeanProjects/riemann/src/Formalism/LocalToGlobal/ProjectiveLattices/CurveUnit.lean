import Formalism.LocalToGlobal.ProjectiveLattices.CurveComp
import Formalism.LocalToGlobal.ProjectiveLattices.LocalUnitReduction.IsUnitMkOfForallPrime

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor TensorProduct

section Gen

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)
  (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

theorem curveUnit_isUnit_emb (Ω : Type) [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω)
    (F : X.Forms) (hF : gF F ≠ 0) :
    IsUnit (lwZ X la N Ω gF w (algebraMap (Rp X la N) (Lw X la w) (emb X la N F))) := by
  rw [lwZ_alg, rzMap_emb]
  have h1 : IsUnit ((1 : X.Kl la) ⊗ₜ[B.KO] gF F) := by
    simpa using (IsUnit.mk0 _ hF).map
      (Algebra.TensorProduct.includeRight : Ω →ₐ[B.KO] X.Kl la ⊗[B.KO] Ω)
  have h2 : IsUnit ((1 : Kp X la N) ⊗ₜ[X.Kl la] ((1 : X.Kl la) ⊗ₜ[B.KO] gF F)) := by
    simpa using h1.map (Algebra.TensorProduct.includeRight :
      X.Kl la ⊗[B.KO] Ω →ₐ[X.Kl la] Kp X la N ⊗[X.Kl la] (X.Kl la ⊗[B.KO] Ω))
  exact h2.map _

theorem curveUnit_isUnit_w0inv (Ω : Type) [CommRing Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω) :
    IsUnit (lwZ X la N Ω gF w (w0inv X la w)) := by
  refine IsUnit.of_mul_eq_one (lwZ X la N Ω gF w (algebraMap (Rp X la N) (Lw X la w) (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0))) ?_
  rw [← map_mul, mul_comm, section_mul_inverse_eq_one, map_one]

variable {ι : Type} (Ω : ι → Type) [∀ Z, Field (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)]
  (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z)

theorem nonzero_divisor_cusp_form
    (hInj : ∀ f : ↥(Frac0 X la w), (∀ Z, phiZ X la N (Ω Z) (gF Z) w f = 0) → f = 0)
    (F : X.Forms) (hF : ∀ Z, gF Z F ≠ 0) (b : ↥(Frac0 X la w))
    (hb : (b : Lw X la w) * algebraMap (Rp X la N) (Lw X la w) (emb X la N F) = 0) : b = 0 := by
  refine hInj b fun Z => ?_
  rw [phiZ_apply]
  have h1 := congrArg (lwZ X la N (Ω Z) (gF Z) w) hb
  rw [map_mul, map_zero] at h1
  exact (curveUnit_isUnit_emb X la N w (Ω Z) (gF Z) F (hF Z)).mul_left_eq_zero.mp h1

theorem curveUnit_unit_gen [Fintype ι]
    (hInj : ∀ f : ↥(Frac0 X la w), (∀ Z, phiZ X la N (Ω Z) (gF Z) w f = 0) → f = 0)
    (hone : ∀ Q : Ideal ↥(Frac0 X la w), Q.IsPrime → Jid X la w ≤ Q → ∀ Z Z',
      RingHom.ker (phiZ X la N (Ω Z) (gF Z) w) ≤ Q → RingHom.ker (phiZ X la N (Ω Z') (gF Z') w) ≤ Q → Z = Z')
    (hloc : ∀ Z (r : RZs X la N (Ω Z) (gF Z) w), ∃ a p : ↥(Frac0 X la w),
      (∀ Q : Ideal ↥(Frac0 X la w), Q.IsPrime → Jid X la w ≤ Q →
        RingHom.ker (phiZ X la N (Ω Z) (gF Z) w) ≤ Q → p ∉ Q) ∧
      phiZ X la N (Ω Z) (gF Z) w p * r = phiZ X la N (Ω Z) (gF Z) w a)
    (hfd : FiniteDimensional (Kp X la N) (OsK X la w))
    (u : ↥(Frac0 X la w)) (hu : ∀ Z, IsUnit (phiZ X la N (Ω Z) (gF Z) w u)) :
    IsUnit (toOsK X la w u) := by
  classical
  have hmem : ∀ b : ↥(Frac0 X la w), b * u ∈ Jid X la w → b ∈ Jid X la w := by
    intro b hb
    refine LocalUnitReduction.mem_of_forall_sup_ker (Jid X la w) (R := fun Z => RZs X la N (Ω Z) (gF Z) w)
      (fun Z => phiZ X la N (Ω Z) (gF Z) w) hInj hone fun Z => ?_
    refine LocalUnitReduction.mem_sup_ker (Jid X la w) (R := fun Z => RZs X la N (Ω Z) (gF Z) w)
      (fun Z => phiZ X la N (Ω Z) (gF Z) w) (hloc Z) ?_
    obtain ⟨v, hv⟩ := hu Z
    have h1 : phiZ X la N (Ω Z) (gF Z) w (b * u) ∈
        Ideal.map (phiZ X la N (Ω Z) (gF Z) w) (Jid X la w) := Ideal.mem_map_of_mem _ hb
    rw [map_mul, ← hv] at h1
    have h2 := Ideal.mul_mem_right (↑v⁻¹ : RZs X la N (Ω Z) (gF Z) w) _ h1
    rwa [mul_assoc, Units.mul_inv, mul_one] at h2
  have hinj : Function.Injective (LinearMap.mulRight (Kp X la N) (toOsK X la w u)) := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨b, rfl⟩ := toOsK_surjective X la w y
    rw [LinearMap.mulRight_apply, ← map_mul, toOsK_eq_zero_iff] at hy
    rw [toOsK_eq_zero_iff]
    exact hmem b hy
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp hinj) 1
  rw [LinearMap.mulRight_apply] at hy
  exact IsUnit.of_mul_eq_one y (by rw [mul_comm]; exact hy)

end Gen

section U0

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X}
  {hM : IntAtExt X E} {ka wL wF : WeightFamilies.Wt D j}

theorem phi_unit_product_cusp_forms (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO))
    (g0 : B.Cusp j wF) {e : ℕ} {w' : WeightFamilies.Wt D j} (θ : B.Cusp j w') (hw : wadd wF w' = wsmul e wL)
    (Ω : Type) [Field Ω] [Algebra B.KO Ω] (gF : (xplus X E hM).Forms →ₐ[B.KO] Ω)
    (hg : gF (X.inc wF g0) ≠ 0) (hθ : gF (X.inc w' θ) ≠ 0) :
    IsUnit (phiZ (xplus X E hM) la G.N Ω gF G.w (u0 G la g0 θ hw)) := by
  rw [phiZ_apply]
  show IsUnit (lwZ (xplus X E hM) la G.N Ω gF G.w (frac (xplus X E hM) la G.w e
    (emb (xplus X E hM) la G.N (X.inc wF g0) * emb (xplus X E hM) la G.N (X.inc w' θ))))
  simp only [frac_apply, map_mul, map_pow]
  exact ((curveUnit_isUnit_emb _ la G.N G.w Ω gF _ hg).mul
    (curveUnit_isUnit_emb _ la G.N G.w Ω gF _ hθ)).mul ((curveUnit_isUnit_w0inv _ la G.N G.w Ω gF).pow e)

end U0

section Inst

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j)
  (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)

theorem curveUnit_gF_inc (Z : Comp (T.Q.Xo j) T.Q.c) (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u) :
    formsEvR j hG hT Z ((recPJ h j hj).inc u F) = evC hG Z (F : T.R j) :=
  formsEvR_single j hG hT Z _ _

variable {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
  (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) (g0 : (recB h.toLawsCore).Cusp j wF)

theorem nonzero_divisor_cusp_form_record
    (hInj : ∀ f : ↥(Frac0 (recPlus h j hj) la G.w),
      (∀ Z : Comp (T.Q.Xo j) T.Q.c, phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w f = 0) →
        f = 0)
    (hg0 : ∀ Z : Comp (T.Q.Xo j) T.Q.c, evC hG Z ((g0 : (recB h.toLawsCore).Cusp j wF) : T.R j) ≠ 0) :
    ∀ b : ↥(Frac0 (recPlus h j hj) la G.w),
      (b : Lw (recPlus h j hj) la G.w) *
        algebraMap (Rp (recPlus h j hj) la G.N) (Lw (recPlus h j hj) la G.w)
          (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc wF g0)) = 0 →
        b = 0 :=
  fun b hb => nonzero_divisor_cusp_form (recPlus h j hj) la G.N G.w (fun Z => Om Z) (fun Z => formsEvR j hG hT Z)
    hInj _ (fun Z h0 => hg0 Z ((curveUnit_gF_inc h j hj hG hT Z wF g0).symm.trans h0)) b hb

theorem unit_ideal_cusp_form_record [Fintype (Comp (T.Q.Xo j) T.Q.c)]
    {e : ℕ} {w' : WeightFamilies.Wt D j} (θ : (recB h.toLawsCore).Cusp j w') (hw : wadd wF w' = wsmul e wL)
    (hInj : ∀ f : ↥(Frac0 (recPlus h j hj) la G.w),
      (∀ Z : Comp (T.Q.Xo j) T.Q.c, phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w f = 0) →
        f = 0)
    (hone : ∀ Q : Ideal ↥(Frac0 (recPlus h j hj) la G.w), Q.IsPrime → Jid (recPlus h j hj) la G.w ≤ Q →
      ∀ Z Z' : Comp (T.Q.Xo j) T.Q.c,
        RingHom.ker (phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w) ≤ Q →
        RingHom.ker (phiZ (recPlus h j hj) la G.N (Om Z') (formsEvR j hG hT Z') G.w) ≤ Q → Z = Z')
    (hloc : ∀ (Z : Comp (T.Q.Xo j) T.Q.c)
      (r : RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w),
      ∃ a p : ↥(Frac0 (recPlus h j hj) la G.w),
        (∀ Q : Ideal ↥(Frac0 (recPlus h j hj) la G.w), Q.IsPrime → Jid (recPlus h j hj) la G.w ≤ Q →
          RingHom.ker (phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w) ≤ Q → p ∉ Q) ∧
        phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w p * r =
          phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w a)
    (hfd : FiniteDimensional (Kp (recPlus h j hj) la G.N) (OsK (recPlus h j hj) la G.w))
    (hg0 : ∀ Z : Comp (T.Q.Xo j) T.Q.c, evC hG Z ((g0 : (recB h.toLawsCore).Cusp j wF) : T.R j) ≠ 0)
    (hθ : ∀ Z : Comp (T.Q.Xo j) T.Q.c, evC hG Z ((θ : (recB h.toLawsCore).Cusp j w') : T.R j) ≠ 0) :
    IsUnit (toOsK (recPlus h j hj) la G.w (u0 G la g0 θ hw)) :=
  curveUnit_unit_gen (recPlus h j hj) la G.N G.w (fun Z => Om Z) (fun Z => formsEvR j hG hT Z)
    hInj hone hloc hfd _ fun Z => phi_unit_product_cusp_forms G la g0 θ hw (Om Z) (formsEvR j hG hT Z)
      (fun h0 => hg0 Z ((curveUnit_gF_inc h j hj hG hT Z wF g0).symm.trans h0))
      (fun h0 => hθ Z ((curveUnit_gF_inc h j hj hG hT Z w' θ).symm.trans h0))

end Inst

end Formalism.L2.Pj
