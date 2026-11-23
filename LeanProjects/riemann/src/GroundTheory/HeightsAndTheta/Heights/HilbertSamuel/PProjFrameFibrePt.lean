import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameFibrePt
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.POneBlockPointDeg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.LemCone
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.StepTStB
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace ProjFrameFibrePt

theorem aeval_mul_of_isHomogeneous {R J : Type*} [CommRing R] (c : J → R) (s : R) {f : MvPolynomial J ℤ}
    {n : ℕ} (hf : f.IsHomogeneous n) : aeval (fun i => c i * s) f = aeval c f * s ^ n := by
  have h := congrArg ((Polynomial.aeval s).restrictScalars ℤ) (coneMap_of_isHomogeneous ℤ c hf)
  rw [coneMap, comp_aeval_apply] at h
  simp only [AlgHom.restrictScalars_apply, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
    Algebra.algebraMap_self, RingHom.id_apply] at h
  exact h

set_option linter.unusedSectionVars false

variable {κ : Type} [Fintype κ] {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {x : Ix κ → Ω}
  {e : Fin (D + 1) → Ix κ}

abbrev graphP (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ) : Ideal (MRing (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1))))) :=
  graphIdeal (coordIdeal ℤ x) (linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))

abbrev aV (D : ℕ) (i : κ) : Σ k, Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1))) k := ⟨Sum.inl (), i⟩

abbrev bV (κ : Type) (k : Fin (D + 1)) : Σ k, Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1))) k := ⟨Sum.inr (), k⟩

theorem graphMap_inl (P : Ideal (MRing (GlobalTheory κ))) (g : (Σ k, GlobalTheory (Fin (D + 1)) k) → MRing (GlobalTheory κ)) (p : Ix κ) :
    graphMap P g (X (aV D p.2)) = C (Ideal.Quotient.mk P (X p)) := by
  rw [graphMap, eval₂Hom_X']

theorem graphMap_inr (P : Ideal (MRing (GlobalTheory κ))) (g : (Σ k, GlobalTheory (Fin (D + 1)) k) → MRing (GlobalTheory κ))
    (k : Fin (D + 1)) : graphMap P g (X (bV κ k)) = C (Ideal.Quotient.mk P (g ⟨(), k⟩)) * X () := by
  rw [graphMap, eval₂Hom_X']

theorem graphMap_rename_inl (P : Ideal (MRing (GlobalTheory κ))) (g : (Σ k, GlobalTheory (Fin (D + 1)) k) → MRing (GlobalTheory κ))
    (f : MRing (GlobalTheory κ)) : graphMap P g (rename (fun p : Ix κ => aV D p.2) f) = C (Ideal.Quotient.mk P f) := by
  have : (graphMap P g).comp (rename (fun p : Ix κ => aV D p.2)).toRingHom = C.comp (Ideal.Quotient.mk P) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
    · simp
    · simp [graphMap_inl]
  exact DFunLike.congr_fun this f

variable (G : GenFibre (inrV (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1)))) (graphP x e))

theorem aeval_inl_eq_zero {f : MRing (GlobalTheory κ)} (hf : f ∈ coordIdeal ℤ x) :
    aeval (fun p : Ix κ => G.x' (aV D p.2)) f = 0 := by
  have h : rename (fun p : Ix κ => aV D p.2) f ∈ graphP x e := by
    rw [graphP, graphIdeal, RingHom.mem_ker, graphMap_rename_inl, Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero]
  rw [← G.genericFibre_ker_target, RingHom.mem_ker, aeval_rename] at h
  exact h

theorem aeval_inl_mul_eq_zero {f : MRing (GlobalTheory κ)} (hf : f ∈ coordIdeal ℤ x) {R : Type*} [CommRing R]
    (φ : G.Φ' →+* R) (s : R) : aeval (fun p : Ix κ => φ (G.x' (aV D p.2)) * s) f = 0 := by
  rw [← sum_homogeneousComponent f, map_sum]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [aeval_mul_of_isHomogeneous _ _ (homogeneousComponent_isHomogeneous d f)]
  have h0 := aeval_inl_eq_zero G (coordIdeal_isHomogIdeal ℤ x f hf d)
  have h1 := comp_aeval_apply (R := ℤ) (f := fun p : Ix κ => G.x' (aV D p.2)) φ.toIntAlgHom (homogeneousComponent d f)
  simp only [RingHom.toIntAlgHom_apply] at h1
  rw [← h1, h0, map_zero, zero_mul]

theorem eval₂_inl_mul_eq_zero {f : MRing (GlobalTheory κ)} (hf : f ∈ coordIdeal ℤ x) {R : Type*} [CommRing R]
    (φ : G.Φ' →+* R) (s : R) : eval₂ (Int.castRingHom R) (fun p : Ix κ => φ (G.x' (aV D p.2)) * s) f = 0 := by
  have h := aeval_inl_mul_eq_zero G hf φ s
  rwa [aeval_def, show algebraMap ℤ R = Int.castRingHom R from Subsingleton.elim _ _] at h

theorem x'_frame_mul (k : Fin (D + 1)) :
    G.x' (aV D (e k).2) * G.x' (bV κ 0) = G.x' (aV D (e 0).2) * G.x' (bV κ k) := by
  have h : X (aV D (e k).2) * X (bV κ 0) - X (aV D (e 0).2) * X (bV κ k) ∈ graphP x e := by
    rw [graphP, graphIdeal, RingHom.mem_ker]
    simp only [map_sub, map_mul, graphMap_inl, graphMap_inr, ProjFrameGraph.linForm_projMat]
    ring
  rw [← G.genericFibre_ker_target, RingHom.mem_ker] at h
  simpa [sub_eq_zero] using h

theorem x'_inr_ne_zero (hF : IsProjFrame x e) (k : Fin (D + 1)) : G.x' (bV κ k) ≠ 0 := by
  intro h
  have h1 : (X (bV κ k) : MRing (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1))))) ∈ graphP x e := by
    rw [← G.genericFibre_ker_target, RingHom.mem_ker, aeval_X]; exact h
  rw [graphP, graphIdeal, RingHom.mem_ker, graphMap_inr, ProjFrameGraph.linForm_projMat, C_mul_X_eq_monomial,
    monomial_eq_zero, Ideal.Quotient.eq_zero_iff_mem, X_mem_coordIdeal_iff] at h1
  exact ProjFrameGraph.frame_ne_zero hF k h1

theorem x'_frame_ne_zero (hF : IsProjFrame x e) : G.x' (aV D (e 0).2) ≠ 0 :=
  ProjFrameGraph.genFibre_x'_ne_zero G (e 0).2 (ProjFrameGraph.frame_ne_zero hF 0)

theorem frame_ratio (hF : IsProjFrame x e) (k : Fin (D + 1)) :
    G.x' (aV D (e k).2) / G.x' (aV D (e 0).2) = algebraMap G.Φ G.Φ' (G.x ⟨(), k⟩ / G.x ⟨(), 0⟩) := by
  rw [map_div₀, ← G.compat ⟨(), k⟩, ← G.compat ⟨(), 0⟩]
  change _ = G.x' (bV κ k) / G.x' (bV κ 0)
  rw [div_eq_div_iff (x'_frame_ne_zero G hF) (x'_inr_ne_zero G hF 0), x'_frame_mul G k]
  ring

theorem ratio_isIntegral (hF : IsProjFrame x e) (i : κ) :
    IsIntegral G.Φ (G.x' (aV D i) / G.x' (aV D (e 0).2)) := by
  obtain ⟨p, hmon, hp⟩ := isIntegralElem_coneMap x e hF (X ⟨(), i⟩)
  set F : MRing (GlobalTheory κ) :=
    p.eval₂ (rename e : MvPolynomial (Fin (D + 1)) ℤ →ₐ[ℤ] MRing (GlobalTheory κ)).toRingHom (X ⟨(), i⟩) with hFdef
  have hF0 : F ∈ coordIdeal ℤ x := by
    rw [coordIdeal, RingHom.mem_ker]
    have e1 : (coneMap ℤ x : MRing (GlobalTheory κ) →ₐ[ℤ] Polynomial Ω).toRingHom.comp
        (rename e : MvPolynomial (Fin (D + 1)) ℤ →ₐ[ℤ] MRing (GlobalTheory κ)).toRingHom =
        (coneMap ℤ (x ∘ e) : MvPolynomial (Fin (D + 1)) ℤ →+* Polynomial Ω) :=
      RingHom.ext fun q => coneMap_rename x e q
    change (coneMap ℤ x : MRing (GlobalTheory κ) →ₐ[ℤ] Polynomial Ω).toRingHom F = 0
    rw [hFdef, Polynomial.hom_eval₂, e1]
    exact hp
  have h0 := aeval_inl_mul_eq_zero G hF0 (RingHom.id G.Φ') (G.x' (aV D (e 0).2))⁻¹
  set t : Ix κ → G.Φ' := fun p => RingHom.id G.Φ' (G.x' (aV D p.2)) * (G.x' (aV D (e 0).2))⁻¹ with ht
  set cc : Fin (D + 1) → G.Φ := fun k => G.x ⟨(), k⟩ / G.x ⟨(), 0⟩ with hcc
  have e2 : (aeval t : MRing (GlobalTheory κ) →ₐ[ℤ] G.Φ').toRingHom.comp
      (rename e : MvPolynomial (Fin (D + 1)) ℤ →ₐ[ℤ] MRing (GlobalTheory κ)).toRingHom =
      (algebraMap G.Φ G.Φ').comp (aeval cc : MvPolynomial (Fin (D + 1)) ℤ →ₐ[ℤ] G.Φ).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => by simp) (fun k => ?_)
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X, aeval_X]
    rw [hcc, ← frame_ratio G hF k, ht]
    simp [div_eq_mul_inv]
  have e3 : G.x' (aV D i) / G.x' (aV D (e 0).2) =
      (aeval t : MRing (GlobalTheory κ) →ₐ[ℤ] G.Φ').toRingHom (X ⟨(), i⟩) := by
    simp [ht, div_eq_mul_inv]
  refine ⟨p.map (aeval cc : MvPolynomial (Fin (D + 1)) ℤ →ₐ[ℤ] G.Φ).toRingHom, hmon.map _, ?_⟩
  rw [Polynomial.eval₂_map, ← e2, e3, ← Polynomial.hom_eval₂, ← hFdef]
  exact h0

theorem aeval_scaled_eq_zero (hF : IsProjFrame x e) {F : MRing (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1))))}
    (hF' : F ∈ graphP x e) :
    aeval (fun v : Σ k, Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1))) k =>
      algebraMap G.Φ' (RatFunc G.Φ') (G.x' v) *
        Sum.elim (fun _ => (algebraMap G.Φ' (RatFunc G.Φ') (G.x' (aV D (e 0).2)))⁻¹ * RatFunc.X)
          (fun _ => 1) v.1) F = 0 := by
  set ℓ := algebraMap G.Φ' (RatFunc G.Φ') with hℓ
  have hu : ℓ (G.x' (aV D (e 0).2)) ≠ 0 := (map_ne_zero ℓ).2 (x'_frame_ne_zero G hF)
  have hW : (RatFunc.X : RatFunc G.Φ') ≠ 0 := RatFunc.X_ne_zero
  set s := (ℓ (G.x' (aV D (e 0).2)))⁻¹ * RatFunc.X with hs
  let lam0 : MRing (GlobalTheory κ) ⧸ coordIdeal ℤ x →+* RatFunc G.Φ' :=
    Ideal.Quotient.lift _
      (eval₂Hom (Int.castRingHom (RatFunc G.Φ')) (fun p : Ix κ => ℓ (G.x' (aV D p.2)) * s))
      (fun f hf => eval₂_inl_mul_eq_zero G hf ℓ s)
  let lam : MvPolynomial Unit (MRing (GlobalTheory κ) ⧸ coordIdeal ℤ x) →+* RatFunc G.Φ' :=
    eval₂Hom lam0 fun _ => ℓ (G.x' (bV κ 0)) / RatFunc.X
  have hcomp : lam.comp (graphMap (coordIdeal ℤ x) (linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))) =
      (aeval (fun v : Σ k, Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1))) k =>
        ℓ (G.x' v) * Sum.elim (fun _ => s) (fun _ => 1) v.1)).toRingHom := by
    have hinl : ∀ i : κ, lam (graphMap (coordIdeal ℤ x) (linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1)))
        (projMat e)) (X (aV D (⟨(), i⟩ : Ix κ).2))) = ℓ (G.x' (aV D i)) * s := by
      intro i
      rw [graphMap_inl]
      simp only [lam, lam0, coe_eval₂Hom, eval₂_C]
      erw [Ideal.Quotient.lift_mk]
      simp
    have hinr : ∀ j : Fin (D + 1), lam (graphMap (coordIdeal ℤ x) (linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1)))
        (projMat e)) (X (bV κ j))) = ℓ (G.x' (bV κ j)) := by
      intro j
      have hj := congrArg ℓ (x'_frame_mul G (e := e) j)
      rw [map_mul, map_mul] at hj
      rw [graphMap_inr, ProjFrameGraph.linForm_projMat]
      simp [lam, lam0, hs]
      field_simp
      linear_combination hj
    refine MvPolynomial.ringHom_ext (fun r => by simp) ?_
    rintro ⟨(w | w), j⟩
    · cases w
      simpa using hinl j
    · cases w
      simpa using hinr j
  have h1 := DFunLike.congr_fun hcomp F
  rw [graphP, graphIdeal, RingHom.mem_ker] at hF'
  rw [RingHom.comp_apply, hF', map_zero] at h1
  exact h1.symm

theorem exists_clear_poly (Q : Polynomial G.Φ) : ∃ b : MRing (GlobalTheory (Fin (D + 1))), aeval G.x b ≠ 0 ∧
    ∃ F : Polynomial (MRing (GlobalTheory (Fin (D + 1)))),
      Polynomial.C (aeval G.x b) * Q = F.map (aeval G.x : MRing (GlobalTheory (Fin (D + 1))) →ₐ[ℤ] G.Φ).toRingHom := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨b₁, hb₁, F₁, e₁⟩ := hp
    obtain ⟨b₂, hb₂, F₂, e₂⟩ := hq
    refine ⟨b₁ * b₂, by rw [map_mul]; exact mul_ne_zero hb₁ hb₂, Polynomial.C b₂ * F₁ + Polynomial.C b₁ * F₂, ?_⟩
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C, ← e₁, ← e₂]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul]
    ring
  | monomial n c =>
    obtain ⟨a, b, hb, rfl⟩ := G.gen c
    refine ⟨b, hb, Polynomial.monomial n a, ?_⟩
    rw [Polynomial.map_monomial, Polynomial.C_mul_monomial]
    congr 1
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    field_simp

theorem transcendental_frame (hF : IsProjFrame x e) : Transcendental G.Φ (G.x' (aV D (e 0).2)) := by
  rw [transcendental_iff]
  intro Q hQ
  obtain ⟨b, hb, F, hbF⟩ := exists_clear_poly G Q
  set evx := (aeval G.x : MRing (GlobalTheory (Fin (D + 1))) →ₐ[ℤ] G.Φ).toRingHom with hevx
  set ren := (rename (inrV (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1)))) :
    MRing (GlobalTheory (Fin (D + 1))) →ₐ[ℤ] MRing (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1))))).toRingHom with hren
  set Fz : MRing (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1)))) := F.eval₂ ren (X (aV D (e 0).2)) with hFz
  have hcx : (aeval G.x' : MRing (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1)))) →ₐ[ℤ] G.Φ').toRingHom.comp ren =
      (algebraMap G.Φ G.Φ').comp evx := by
    refine MvPolynomial.ringHom_ext (fun r => by simp) (fun q => ?_)
    simp [hren, hevx, G.compat]
  have hFz0 : Fz ∈ graphP x e := by
    rw [← G.genericFibre_ker_target, RingHom.mem_ker]
    change (aeval G.x' : MRing (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1)))) →ₐ[ℤ] G.Φ').toRingHom Fz = 0
    rw [hFz, Polynomial.hom_eval₂, hcx, ← Polynomial.eval₂_map, ← hbF, Polynomial.eval₂_mul, Polynomial.eval₂_C]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
    rw [← Polynomial.aeval_def, hQ, mul_zero]
  have hz := aeval_scaled_eq_zero G hF hFz0
  set ℓ := algebraMap G.Φ' (RatFunc G.Φ') with hℓ
  have hu : ℓ (G.x' (aV D (e 0).2)) ≠ 0 := (map_ne_zero ℓ).2 (x'_frame_ne_zero G hF)
  set z := fun v : Σ k, Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1))) k =>
      ℓ (G.x' v) * Sum.elim (fun _ => (ℓ (G.x' (aV D (e 0).2)))⁻¹ * RatFunc.X) (fun _ => 1) v.1 with hz_def
  have hcz : (aeval z : MRing (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1)))) →ₐ[ℤ] RatFunc G.Φ').toRingHom.comp ren =
      (ℓ.comp (algebraMap G.Φ G.Φ')).comp evx := by
    refine MvPolynomial.ringHom_ext (fun r => by simp) (fun q => ?_)
    simp [hren, hevx, hz_def, inrV]
    rw [← G.compat q]
    rfl
  have hzu : (aeval z : MRing (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1)))) →ₐ[ℤ] RatFunc G.Φ').toRingHom
      (X (aV D (e 0).2)) = RatFunc.X := by
    simp [hz_def]
    rw [← mul_assoc, mul_inv_cancel₀ hu, one_mul]
  have h2 : (aeval z : MRing (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1)))) →ₐ[ℤ] RatFunc G.Φ').toRingHom Fz = 0 := hz
  rw [hFz, Polynomial.hom_eval₂, hcz, hzu, ← Polynomial.eval₂_map, ← hbF] at h2

  have h3 : algebraMap (Polynomial G.Φ') (RatFunc G.Φ')
      ((Polynomial.C (aeval G.x b) * Q).map (algebraMap G.Φ G.Φ')) = 0 := by
    rw [← h2, ← Polynomial.eval₂_C_X (p := (Polynomial.C (aeval G.x b) * Q).map (algebraMap G.Φ G.Φ')),
      Polynomial.hom_eval₂, Polynomial.eval₂_map, RatFunc.algebraMap_X]
    congr 1
  rw [map_eq_zero_iff _ (RatFunc.algebraMap_injective G.Φ'),
    Polynomial.map_eq_zero_iff (algebraMap G.Φ G.Φ').injective, mul_eq_zero, Polynomial.C_eq_zero] at h3
  exact h3.resolve_left hb

end ProjFrameFibrePt

open ProjFrameFibrePt in

theorem ProjFrameFibrePt.proof : ProjFrameFibrePt.Statement := by
  intro D Ω _ _ κ _ x e _ hF G
  classical
  have hk₀ : (Sum.inl () : Unit ⊕ Unit) ∉ Set.range (Sum.inr : Unit → Unit ⊕ Unit) := by
    rintro ⟨_, h⟩; exact Sum.inr_ne_inl h
  let k₀ : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit) := ⟨Sum.inl (), hk₀⟩
  have hK : ∀ k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit), k = k₀ := by
    rintro ⟨(w' | w'), h⟩
    · cases w'; rfl
    · exact absurd ⟨w', rfl⟩ h
  let w : (Σ k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit),
      fibreIdx (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1)))) Sum.inr k) → G.Φ' := fun q => G.x' ⟨q.1.1, q.2⟩
  let c := ProjFrameGraph.fibreChart (κ := κ) (ι₂ := GlobalTheory (Fin (D + 1))) (e 0).2
  have hrat : ∀ q, IsIntegral G.Φ (w q / w ⟨k₀, c k₀⟩) := by
    rintro ⟨⟨(w' | w'), h⟩, j⟩
    · cases w'; exact ratio_isIntegral G hF j
    · exact absurd ⟨w', rfl⟩ h
  have hfin : Module.Finite G.Φ (Algebra.adjoin G.Φ (Set.range fun p => w p / w ⟨k₀, c k₀⟩)) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range _) (by rintro _ ⟨q, rfl⟩; exact hrat q)
  have htr : Transcendental (Algebra.adjoin G.Φ (Set.range fun p => w p / w ⟨k₀, c k₀⟩)) (w ⟨k₀, c k₀⟩) := by
    have : Algebra.IsAlgebraic G.Φ (Algebra.adjoin G.Φ (Set.range fun p => w p / w ⟨k₀, c k₀⟩)) :=
      Algebra.IsAlgebraic.of_finite _ _
    exact (transcendental_frame G hF).extendScalars _
  exact (OneBlockPointDeg.proof G.Φ G.Φ' (FibreBlock (Sum.inr : Unit → Unit ⊕ Unit)) _ k₀ hK w c
    (x'_frame_ne_zero G hF) hfin htr).1

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
