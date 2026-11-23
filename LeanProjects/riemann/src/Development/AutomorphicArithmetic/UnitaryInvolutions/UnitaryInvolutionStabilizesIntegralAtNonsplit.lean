import Development.AutomorphicArithmetic.Foundations.Convolution.OrbitNormCounting.NormCount
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties
import Development.AutomorphicArithmetic.UnitaryInvolutions.ExistsLocalQuadraticGaloisDataAtNonsplitPlace
import Development.AutomorphicArithmetic.UnitaryInvolutions.TwistedConjOfCharpolyMulGalConjEqOfSeparable
import Development.AutomorphicArithmetic.UnitaryInvolutions.NormInOfFreeAlgebraOfCompleteQuadratic
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

private theorem UpperTheory.G3.InertCase.th_mul {k R : Type} [CommRing k] [CommRing R] [Algebra k R] {n : ℕ}
    (c : R ≃ₐ[k] R) (a b : GL (Fin n) R) :
    UpperTheory.ConvolutionTheory.D.th c (a * b) = UpperTheory.ConvolutionTheory.D.th c a * UpperTheory.ConvolutionTheory.D.th c b := by
  refine Units.ext ?_
  change UpperTheory.ConvolutionTheory.D.ct c ((a * b)⁻¹ : GL (Fin n) R).val =
    UpperTheory.ConvolutionTheory.D.ct c (a⁻¹ : GL (Fin n) R).val * UpperTheory.ConvolutionTheory.D.ct c (b⁻¹ : GL (Fin n) R).val
  rw [_root_.mul_inv_rev, Units.val_mul, UpperTheory.ConvolutionTheory.D.ct, UpperTheory.ConvolutionTheory.D.ct, UpperTheory.ConvolutionTheory.D.ct, Matrix.map_mul,
    Matrix.transpose_mul]

theorem UpperTheory.unitary_involution_stabilizes_integral_at_nonsplit :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (u δ : GL (Fin n) E),
        (∀ g, thE E n g = u * UpperTheory.ConvolutionTheory.D.th (IsCMField.complexConj E) g * u⁻¹) →
        u * UpperTheory.ConvolutionTheory.D.th (IsCMField.complexConj E) u = 1 → ∀ w : Pl E, ¬ IsSplitAt w →
        (∀ g : GLw n w, (thL n w g).val = u.val.map (algebraMap E _) * ((g⁻¹ : GLw n w).val.map (cj w))ᵀ * (u⁻¹ : GL (Fin n) E).val.map (algebraMap E _)) →
        GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) u ∈ GlobalTheory.LFun.KGL w n →
        GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ ∈ GlobalTheory.LFun.KGL w n →
        (∀ Q : (Ov E w)[X], Q.map (Ov E w).subtype = atPl w (UpperTheory.ConvolutionTheory.G3.gpol δ) → Q.Separable) →
        ∀ y ∈ GlobalTheory.LFun.KGL w n, UpperTheory.ConvolutionTheory.G3.lpol w y = atPl w (UpperTheory.ConvolutionTheory.G3.gpol δ) →
          ∃ k ∈ GlobalTheory.LFun.KGL w n, y = k⁻¹ * locEl n w δ * thL n w k := by
  intro E _ _ _ hU n u δ hT hu w hw hL huK hδK hQ y hyK hy
  obtain ⟨k, _, _, _, c, ϖ, ω, hG, hc, hcϖ, hϖ, hcomp, hsep, hfin, hω⟩ := UpperTheory.exists_local_quadratic_galois_data_at_nonsplit_place E hU w hw
  have core := UpperTheory.twistedConj_of_charpoly_mul_galConj_eq_of_separable k (Ov E w) c hG
    (UpperTheory.normIn_of_free_algebra_of_complete_quadratic k (Ov E w) c ϖ ω hG hcϖ hϖ hcomp hsep hfin hω) n
  have hconj := ((GlobalTheory.T.placeConjugation_properties_cmField E hU w).2.2.2.1 hw).1
  obtain ⟨ι, hιdef⟩ : ∃ ι : GL (Fin n) (Ov E w) →* GLw n w, ι = Formalism.UG.bc (Ov E w).subtype := ⟨_, rfl⟩
  have hιv : ∀ a, (ι a).val = a.val.map (Ov E w).subtype := fun a => by rw [hιdef]; rfl
  have hinj : Function.Injective ι := fun a b e =>
    Units.ext (Matrix.map_injective (Ov E w).subtype_injective
      (by
        show a.val.map (Ov E w).subtype = b.val.map (Ov E w).subtype
        rw [← hιv, ← hιv, e]))
  have hK : ∀ x ∈ GlobalTheory.LFun.KGL w n, ∃ a, ι a = x := by
    intro x hx
    rw [hιdef]
    exact hx
  obtain ⟨u₀, hu₀⟩ := hK _ huK
  obtain ⟨δ₀, hδ₀⟩ := hK _ hδK
  obtain ⟨y₀, rfl⟩ := hK _ hyK
  have hcompat : ∀ a : GL (Fin n) (Ov E w),
      (ι (UpperTheory.ConvolutionTheory.D.th c a)).val = (((ι a)⁻¹ : GLw n w).val.map (cj w))ᵀ := by
    intro a
    rw [← map_inv, hιv, hιv]
    refine Matrix.ext fun i j => ?_
    exact hc _
  have hthL : ∀ a : GL (Fin n) (Ov E w),
      thL n w (ι a) = ι u₀ * ι (UpperTheory.ConvolutionTheory.D.th c a) * (ι u₀)⁻¹ := by
    intro a
    refine Units.ext ?_
    rw [hL, Units.val_mul, Units.val_mul, hcompat, hu₀, ← map_inv]
    rfl
  have hmapth : ι (UpperTheory.ConvolutionTheory.D.th c u₀) = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E))
      (UpperTheory.ConvolutionTheory.D.th (IsCMField.complexConj E) u) := by
    refine Units.ext ?_
    rw [hcompat, hu₀, ← map_inv]
    refine Matrix.ext fun i j => ?_
    exact hconj _
  have hu1 : UpperTheory.ConvolutionTheory.D.th c u₀ = u₀⁻¹ := by
    refine eq_inv_of_mul_eq_one_right (hinj ?_)
    rw [map_mul, map_one, hmapth, hu₀, ← map_mul, hu, map_one]
  have hnrm : ∀ a : GL (Fin n) (Ov E w),
      nrmL n w (ι a) = ι (a * u₀ * UpperTheory.ConvolutionTheory.D.th c (a * u₀)) := by
    intro a
    have e : nrmL n w (ι a) = ι a * thL n w (ι a) := by
      unfold nrmL thL
      rw [if_neg hw, if_neg hw]
    rw [e, hthL, UpperTheory.G3.InertCase.th_mul, hu1]
    simp only [map_mul, map_inv, mul_assoc]
  have hloc : locEl n w δ = ι δ₀ := by
    rw [hδ₀]
    unfold locEl
    rw [if_neg hw]
  have hcpmap : ∀ a : GL (Fin n) (Ov E w),
      (UpperTheory.ConvolutionTheory.D.cp (a * u₀ * UpperTheory.ConvolutionTheory.D.th c (a * u₀))).map (Ov E w).subtype =
        (nrmL n w (ι a)).val.charpoly := by
    intro a
    rw [hnrm, hιv]
    exact (Matrix.charpoly_map _ _).symm
  have hδpol : (UpperTheory.ConvolutionTheory.D.cp (δ₀ * u₀ * UpperTheory.ConvolutionTheory.D.th c (δ₀ * u₀))).map (Ov E w).subtype =
      atPl w (UpperTheory.ConvolutionTheory.G3.gpol δ) := by
    rw [hcpmap, ← hloc]
    exact GlobalTheory.BCT.ThBasic.charpoly_nrmL hU n w δ
  have hypol : (UpperTheory.ConvolutionTheory.D.cp (y₀ * u₀ * UpperTheory.ConvolutionTheory.D.th c (y₀ * u₀))).map (Ov E w).subtype =
      atPl w (UpperTheory.ConvolutionTheory.G3.gpol δ) := (hcpmap y₀).trans hy
  obtain ⟨t, ht⟩ := core (δ₀ * u₀) (y₀ * u₀) (hQ _ hδpol)
    (Polynomial.map_injective _ (Ov E w).subtype_injective (hypol.trans hδpol.symm))
  refine ⟨ι t, ⟨t, by rw [hιdef]⟩, ?_⟩
  have h1 := congrArg ι ht
  rw [UpperTheory.ConvolutionTheory.D.thConj] at h1
  simp only [map_mul, map_inv] at h1
  rw [hloc, hthL]
  have h2 : ι y₀ = (ι y₀ * ι u₀) * (ι u₀)⁻¹ := by group
  rw [h2, h1]
  simp only [mul_assoc]
