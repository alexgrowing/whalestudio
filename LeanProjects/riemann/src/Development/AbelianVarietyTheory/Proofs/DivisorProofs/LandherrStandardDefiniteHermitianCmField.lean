import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HeightOneSpectrumPlacesOverFiniteSet
import GroundTheory.GlobalFields.SemilocalAlgebras.Finite
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LandherrStd

open GroundTheory.Global.SemiLocal
open scoped GroundTheory.Global.SemiLocal

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem finrank_pos (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (u : HeightOneSpectrum (𝓞 E))
    [u.asIdeal.LiesOver v.asIdeal] :
    0 < Module.finrank (v.adicCompletion (maximalRealSubfield E)) (u.adicCompletion E) := by
  rw [finrank_eq_ramificationIdx_mul_inertiaDeg E v u]
  exact Nat.mul_pos (Ideal.ramificationIdx_pos u.asIdeal _) (Ideal.inertiaDeg_pos _ _)

theorem det_map' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) : (M.map f).det = f M.det :=
  (RingHom.map_det f M).symm

theorem exists_sq_sub_mul_sq (hU : Unr E) (θ : E) (hθ0 : θ ≠ 0) (hθ : IsCMField.complexConj E θ = -θ)
    (d : maximalRealSubfield E) (hd : (d : E) = θ * θ) (a : maximalRealSubfield E)
    (hloc : ∀ w : Pl E, ¬ IsSplitAt w → ∃ z : w.adicCompletion E,
      algebraMap E (w.adicCompletion E) (a : E) = cj w z * z)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) :
    ∃ x y : v.adicCompletion (maximalRealSubfield E),
      algebraMap _ (v.adicCompletion (maximalRealSubfield E)) a =
        x ^ 2 - algebraMap _ (v.adicCompletion (maximalRealSubfield E)) d * y ^ 2 := by
  set Fv := v.adicCompletion (maximalRealSubfield E)
  haveI : CharZero Fv :=
    charZero_of_injective_algebraMap (algebraMap (maximalRealSubfield E) Fv).injective
  have hd0 : d ≠ 0 := fun h => mul_ne_zero hθ0 hθ0 (hd.symm.trans (by rw [h]; rfl))
  by_cases hsq : IsSquare (algebraMap _ Fv d)
  · exact GlobalTheory.Published.HasseNormSt.of_isSquare ((_root_.map_ne_zero _).2 hd0) hsq _
  obtain ⟨w, hw⟩ := (GlobalTheory.QNorm.places_over (maximalRealSubfield E) E).2.1 v
  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw, HeightOneSpectrum.under_asIdeal]⟩
  set ι := completionMap v w with hιdef
  have hι : ∀ x : maximalRealSubfield E,
      ι (algebraMap _ Fv x) = algebraMap E (w.adicCompletion E) (x : E) := by
    intro x
    rw [hιdef, completionMap_algebraMap, IsScalarTower.algebraMap_apply (maximalRealSubfield E) E]
    rfl
  set t := algebraMap E (w.adicCompletion E) θ with htdef
  have ht2 : t * t = ι (algebraMap _ Fv d) := by rw [hι, hd, map_mul]
  have hnot : ∀ s : Fv, t ≠ ι s := by
    intro s hs
    apply hsq
    refine ⟨s, ι.injective ?_⟩
    rw [← ht2, map_mul, hs]
  have hsm : ∀ (s : Fv) (y : w.adicCompletion E), s • y = ι s * y := fun s y => Algebra.smul_def s y
  have hli : LinearIndependent Fv ![(1 : w.adicCompletion E), t] := by
    rw [LinearIndependent.pair_iff]
    intro s r h
    rw [hsm, hsm, mul_one] at h
    by_cases hr : r = 0
    · subst hr
      rw [map_zero, zero_mul, add_zero] at h
      exact ⟨ι.injective (by rw [h, map_zero]), rfl⟩
    · exfalso
      apply hnot (-s / r)
      have hr' : ι r ≠ 0 := (_root_.map_ne_zero ι).2 hr
      rw [map_div₀, map_neg]
      field_simp
      linear_combination h
  have hsum := sum_finrank_eq E v
  rw [Algebra.IsQuadraticExtension.finrank_eq_two] at hsum
  have hle : Module.finrank Fv (w.adicCompletion E) ≤ 2 := by
    rw [← hsum]
    exact Finset.single_le_sum (f := fun u : PlacesOver E v =>
      Module.finrank Fv (u.1.adicCompletion E)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ ⟨w, inferInstance⟩)
  haveI : Module.Finite Fv (w.adicCompletion E) := Module.finite_of_finrank_pos (finrank_pos v w)
  have hge : 2 ≤ Module.finrank Fv (w.adicCompletion E) := by
    simpa using hli.fintype_card_le_finrank
  have h2 : Module.finrank Fv (w.adicCompletion E) = 2 := le_antisymm hle hge
  have hns : ¬ IsSplitAt w := by
    rintro ⟨u, hne, hu⟩
    haveI : u.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw, ← hu, HeightOneSpectrum.under_asIdeal]⟩
    have hpos := finrank_pos v u
    have hne' : (⟨u, inferInstance⟩ : PlacesOver E v) ≠ ⟨w, inferInstance⟩ :=
      fun h => hne (congrArg Subtype.val h)
    have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun u : PlacesOver E v =>
      Module.finrank Fv (u.1.adicCompletion E))
      (Finset.subset_univ {(⟨u, inferInstance⟩ : PlacesOver E v), ⟨w, inferInstance⟩})
      (fun _ _ _ => Nat.zero_le _)
    rw [Finset.sum_pair hne', hsum] at this
    have key : Module.finrank Fv (u.adicCompletion E) + Module.finrank Fv (w.adicCompletion E) ≤ 2 := this
    rw [h2] at key
    have hpos' : 0 < Module.finrank Fv (u.adicCompletion E) := hpos
    omega
  obtain ⟨z, hz⟩ := hloc w hns
  have hcc := ((GlobalTheory.ConjAtPlace.main E hU w).2.2.2.1 hns).1
  have hcj : ∀ s : Fv, cj w (ι s) = ι s := by
    have h := (HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield E) v).equalizer
      ((GlobalTheory.ConjAtPlace.main E hU w).1.comp (continuous_completionMap v w))
      (continuous_completionMap v w) (funext fun x => ?_)
    · exact fun s => congrFun h s
    · simp only [Function.comp_apply]
      rw [← hιdef, hι, hcc]
      congr 1
      exact (IsCMField.complexConj E).commutes x
  have hct : cj w t = -t := by rw [htdef, hcc, hθ, map_neg]
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  have hzb : z = ι (b.repr z 0) + ι (b.repr z 1) * t := by
    conv_lhs => rw [← b.sum_repr z, Fin.sum_univ_two]
    simp [b, hsm]
  obtain ⟨A, C, hAC⟩ : ∃ A C : Fv, z = ι A + ι C * t := ⟨_, _, hzb⟩
  refine ⟨A, C, ι.injective ?_⟩
  rw [hι, hz, hAC, map_add, map_mul, hcj, hcj, hct, map_sub, map_mul, map_pow, map_pow, ← ht2]
  ring

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ)
    (H : Matrix (Fin n) (Fin n) E), IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H →
    (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H.map τ = cT (starRingEnd ℂ) Q * Q) →
    (∀ w : Pl E, ¬ IsSplitAt w → ∃ g : Matrix (Fin n) (Fin n) (w.adicCompletion E),
      H.map (algebraMap E (w.adicCompletion E)) = cT (cj w) g * g) →
    ∃ h : GL (Fin n) E, H = cT (IsCMField.complexConj E).toRingEquiv.toRingHom h.val * h.val := by
  intro E _ _ _ hU n H hH hτ hw
  have hG' : ∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc (H a b) = H b a := fun a b => by
    have := congrFun (congrFun hH b) a
    simpa [cT, ReciprocityTheory.ChartRestriction.G.FD.cc] using this
  have hG : ∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc ((1 : Matrix (Fin n) (Fin n) E) a b) =
      (1 : Matrix (Fin n) (Fin n) E) b a := by
    intro a b
    by_cases h : a = b
    · subst h
      simp [ReciprocityTheory.ChartRestriction.G.FD.cc]
    · simp [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h), ReciprocityTheory.ChartRestriction.G.FD.cc]
  have hs : ∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧
      H.map τ = Qᵀ * (1 : Matrix (Fin n) (Fin n) E).map τ * Q.map (starRingEnd ℂ) := by
    intro τ
    obtain ⟨Q, hQ, hQe⟩ := hτ τ
    refine ⟨Q.map (starRingEnd ℂ), ?_, ?_⟩
    · rw [det_map']
      exact (_root_.map_ne_zero _).2 hQ
    · have h1 : (Q.map (starRingEnd ℂ)).map (starRingEnd ℂ) = Q := by
        ext i j
        simp
      rw [hQe, Matrix.map_one _ (map_zero τ) (map_one τ), Matrix.mul_one, h1]
      rfl
  have hd : H.det ≠ 0 := by
    obtain ⟨Q, hQ, hQe⟩ := hτ (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
    intro h0
    have h1 := congrArg Matrix.det hQe
    rw [det_map', h0, map_zero, Matrix.det_mul] at h1
    have h2 : (cT (starRingEnd ℂ) Q).det = starRingEnd ℂ Q.det := by
      unfold cT
      rw [Matrix.det_transpose, det_map']
    rw [h2] at h1
    exact mul_ne_zero ((_root_.map_ne_zero _).2 hQ) hQ h1.symm
  have hd1 : (1 : Matrix (Fin n) (Fin n) E).det ≠ 0 := by simp
  obtain ⟨P, hP, hPe⟩ : ∃ P : Matrix (Fin n) (Fin n) E, P.det ≠ 0 ∧
      H = Pᵀ * 1 * P.map ReciprocityTheory.ChartRestriction.G.FD.cc := by
    refine GlobalTheory.LocalQuad.landherr_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt E n 1 H hG hG' hd1 hd hs ?_
    have hm : (1 : Matrix (Fin n) (Fin n) E).det / H.det ∈ maximalRealSubfield E := by
      rw [← IsCMField.complexConj_eq_self_iff, map_div₀]
      exact congrArg₂ (· / ·) (GlobalTheory.Published.cc_det_of_herm hG) (GlobalTheory.Published.cc_det_of_herm hG')
    let a : maximalRealSubfield E := ⟨_, hm⟩
    obtain ⟨θ, h0, hθ⟩ := GlobalTheory.Published.exists_cc_eq_neg E
    obtain ⟨d, hdθ⟩ := GlobalTheory.Published.exists_sq_real hθ
    have hd0 : d ≠ 0 := fun h => mul_ne_zero h0 h0 (hdθ.symm.trans (congrArg Subtype.val h))
    have ha0 : a ≠ 0 := fun h => div_ne_zero hd1 hd (congrArg Subtype.val h)
    have hloc : ∀ w : Pl E, ¬ IsSplitAt w → ∃ z : w.adicCompletion E,
        algebraMap E (w.adicCompletion E) (a : E) = cj w z * z := by
      intro w hns
      obtain ⟨g, hg⟩ := hw w hns
      have h1 := congrArg Matrix.det hg
      rw [det_map', Matrix.det_mul] at h1
      have h2 : (cT (cj w) g).det = cj w g.det := by
        unfold cT
        rw [Matrix.det_transpose, det_map']
      rw [h2] at h1
      refine ⟨g.det⁻¹, ?_⟩
      change algebraMap E (w.adicCompletion E) ((1 : Matrix (Fin n) (Fin n) E).det / H.det) = _
      rw [Matrix.det_one, one_div, map_inv₀, h1, map_inv₀, mul_inv]
    obtain ⟨x, y, hxy⟩ := GlobalTheory.QNorm.hasseNormSt (maximalRealSubfield E) d a hd0 ha0
      (fun ρ => by
        let τ := ComplexEmbedding.lift E (Complex.ofRealHom.comp ρ)
        have h1 : τ (a : E) = (Complex.ofRealHom.comp ρ) a :=
          ComplexEmbedding.lift_algebraMap_apply E _ a
        have h2 : 0 < (τ (a : E)).re := GlobalTheory.Published.Landherr.re_det_div_pos hd1 τ (hs τ)
        rw [h1] at h2
        exact ⟨√(ρ a), 0, by rw [Real.sq_sqrt (le_of_lt (by simpa using h2))]; ring⟩)
      (fun v => exists_sq_sub_mul_sq hU θ h0 hθ d hdθ a hloc v)
    refine ⟨x + y * θ, ?_⟩
    have h1 := congrArg (Subtype.val : maximalRealSubfield E → E) hxy
    have h2 : IsCMField.complexConj E θ = -θ := hθ
    simp [a, hdθ] at h1
    simp only [Matrix.det_one, one_div, ReciprocityTheory.ChartRestriction.G.FD.cc, map_add, map_mul,
      IsCMField.complexConj_apply_eq_self, h2]
    linear_combination h1
  have hPc : (P.map ReciprocityTheory.ChartRestriction.G.FD.cc).det ≠ 0 := by
    rw [show (P.map ReciprocityTheory.ChartRestriction.G.FD.cc) = P.map (IsCMField.complexConj E).toRingEquiv.toRingHom from rfl,
      det_map']
    exact (_root_.map_ne_zero _).2 hP
  let u : GL (Fin n) E := ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hPc)).unit
  refine ⟨u, ?_⟩
  have hu : (u : Matrix (Fin n) (Fin n) E) = P.map ReciprocityTheory.ChartRestriction.G.FD.cc := rfl
  rw [hu, hPe, Matrix.mul_one]
  congr 1
  ext i j
  simp [cT, ReciprocityTheory.ChartRestriction.G.FD.cc]

end GlobalTheory.LandherrStd
