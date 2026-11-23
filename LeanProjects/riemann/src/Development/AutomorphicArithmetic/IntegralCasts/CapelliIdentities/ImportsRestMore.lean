import Mathlib

namespace ZbYha7

open scoped ComplexOrder in
private lemma pos {I : Type} [Fintype I] (A : Matrix I I ℂ) (hA : A.PosDef) (x : I → ℂ) (hx : x ≠ 0) :
    0 < RCLike.re (star x ⬝ᵥ A.mulVec x) :=
  (RCLike.pos_iff.mp (hA.dotProduct_mulVec_pos hx)).1

private lemma scale {I : Type} [Fintype I] (A : Matrix I I ℂ) (x : I → ℂ) (r : ℝ) :
    RCLike.re (star ((r : ℂ) • x) ⬝ᵥ A.mulVec ((r : ℂ) • x)) = r ^ 2 * RCLike.re (star x ⬝ᵥ A.mulVec x) := by
  rw [Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct]
  simp only [smul_eq_mul, RCLike.star_def, Complex.conj_ofReal]
  rw [← mul_assoc, ← Complex.ofReal_mul]
  simp [Complex.re_ofReal_mul, sq]

private lemma cont {I : Type} [Fintype I] (A : Matrix I I ℂ) :
    Continuous fun x : I → ℂ => RCLike.re (star x ⬝ᵥ A.mulVec x) := by
  simp only [dotProduct, Matrix.mulVec]
  fun_prop

end ZbYha7

theorem UpperTheory.Reformulated.B.Yha7.main :
    ∀ {I : Type} [inst : Fintype I] [DecidableEq I] (A : Matrix I I Complex),
      @Matrix.PosDef I Complex Complex.instRing Complex.partialOrder Complex.instStarRing A →
        ∃ (l : Real),
          And (@LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) l)
            (∀ (x : I → Complex),
              @LE.le Real Real.instLE
                (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) l
                  (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))
                    (@Norm.norm (I → Complex)
                      (@NormedRing.toNorm (I → Complex)
                        (@Pi.normedRing I (fun (a : I) ↦ Complex) inst fun (i : I) ↦
                          @CStarAlgebra.toNormedRing Complex
                            (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))
                      x)
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@DFunLike.coe
                  (@AddMonoidHom Complex Real
                    (@AddZero.mk Complex
                      (@AddMonoid.toZero Complex
                        (@AddCommMonoid.toAddMonoid Complex
                          (@Semiring.toAddCommMonoid Complex
                            (@Ring.toSemiring Complex
                              (@CommRing.toRing Complex
                                (@Field.toCommRing Complex
                                  (@NormedField.toField Complex
                                    (@DenselyNormedField.toNormedField Complex
                                      (@RCLike.toDenselyNormedField Complex Complex.instRCLike)))))))))
                      (@AddSemigroup.toAdd Complex
                        (@AddMonoid.toAddSemigroup Complex
                          (@AddCommMonoid.toAddMonoid Complex
                            (@Semiring.toAddCommMonoid Complex
                              (@Ring.toSemiring Complex
                                (@CommRing.toRing Complex
                                  (@Field.toCommRing Complex
                                    (@NormedField.toField Complex
                                      (@DenselyNormedField.toNormedField Complex
                                        (@RCLike.toDenselyNormedField Complex Complex.instRCLike)))))))))))
                    (@AddZeroClass.toAddZero Real (@AddMonoid.toAddZeroClass Real Real.instAddMonoid)))
                  Complex (fun (x : Complex) ↦ Real)
                  (@AddMonoidHom.instFunLike Complex Real
                    (@AddZero.mk Complex
                      (@AddMonoid.toZero Complex
                        (@AddCommMonoid.toAddMonoid Complex
                          (@Semiring.toAddCommMonoid Complex
                            (@Ring.toSemiring Complex
                              (@CommRing.toRing Complex
                                (@Field.toCommRing Complex
                                  (@NormedField.toField Complex
                                    (@DenselyNormedField.toNormedField Complex
                                      (@RCLike.toDenselyNormedField Complex Complex.instRCLike)))))))))
                      (@AddSemigroup.toAdd Complex
                        (@AddMonoid.toAddSemigroup Complex
                          (@AddCommMonoid.toAddMonoid Complex
                            (@Semiring.toAddCommMonoid Complex
                              (@Ring.toSemiring Complex
                                (@CommRing.toRing Complex
                                  (@Field.toCommRing Complex
                                    (@NormedField.toField Complex
                                      (@DenselyNormedField.toNormedField Complex
                                        (@RCLike.toDenselyNormedField Complex Complex.instRCLike)))))))))))
                    (@AddZeroClass.toAddZero Real (@AddMonoid.toAddZeroClass Real Real.instAddMonoid)))
                  (@RCLike.re Complex Complex.instRCLike)
                  (@dotProduct I Complex inst Complex.instMul Complex.instAddCommMonoid
                    (@Star.star (I → Complex)
                      (@Pi.instStarForall I (fun (a : I) ↦ Complex) fun (i : I) ↦
                        @InvolutiveStar.toStar Complex
                          (@StarAddMonoid.toInvolutiveStar Complex
                            (@AddCommMonoid.toAddMonoid Complex
                              (@NonUnitalNonAssocSemiring.toAddCommMonoid Complex
                                (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                                  (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                                    (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex
                                      Complex.instNonUnitalCommRing)))))
                            (@StarRing.toStarAddMonoid Complex
                              (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))
                              Complex.instStarRing)))
                      x)
                    (@Matrix.mulVec I I Complex
                      (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))
                      inst A x)))) := by
  intro I inst _ A hA
  set f : (I → ℂ) → ℝ := fun x => RCLike.re (star x ⬝ᵥ A.mulVec x) with hf
  have hpos : ∀ x : I → ℂ, x ≠ 0 → 0 < f x := fun x hx => by
    exact ZbYha7.pos A hA x hx
  have hS : ∃ l : ℝ, 0 < l ∧ ∀ y ∈ Metric.sphere (0 : I → ℂ) 1, l ≤ f y := by
    by_cases hne : (Metric.sphere (0 : I → ℂ) 1).Nonempty
    · obtain ⟨y0, hy0, hmin⟩ := (isCompact_sphere (0 : I → ℂ) 1).exists_isMinOn hne
        (ZbYha7.cont A).continuousOn
      refine ⟨f y0, hpos y0 ?_, fun y hy => hmin hy⟩
      intro h; rw [h] at hy0; simp at hy0
    · exact ⟨1, one_pos, fun y hy => (hne ⟨y, hy⟩).elim⟩
  obtain ⟨l, hl, hlS⟩ := hS
  refine ⟨l, hl, fun x => ?_⟩
  by_cases hx : x = 0
  · subst hx; simp
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set y : I → ℂ := ((‖x‖⁻¹ : ℝ) : ℂ) • x with hy
  have hyS : y ∈ Metric.sphere (0 : I → ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, hy, norm_smul]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
    field_simp
  have h1 := hlS y hyS
  have hxy : x = ((‖x‖ : ℝ) : ℂ) • y := by
    rw [hy, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne', Complex.ofReal_one, one_smul]
  have h2 : f x = ‖x‖ ^ 2 * f y := by
    conv_lhs => rw [hxy]
    exact ZbYha7.scale A y ‖x‖
  change l * ‖x‖ ^ 2 ≤ f x
  rw [h2, mul_comm l]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)
