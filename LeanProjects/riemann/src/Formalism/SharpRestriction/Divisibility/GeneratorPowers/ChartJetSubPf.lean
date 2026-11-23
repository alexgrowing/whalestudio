import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetSubSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

theorem tan_coef {V K : Type} [CommRing V] [CommRing K] [Algebra V K] {d : ℕ} (j : Fin d) :
    (jetTan ((0 : Fin 1), j) : Jet K (Fin 1 × Fin d) (0 + 1) →ₐ[K] DualNumber K).toRingHom.comp
      (jetCoef (algebraMap V K) (Fin 1 × Fin d) 1) = (dualMap (algebraMap V K)).comp
      (jetTan ((0 : Fin 1), j) : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] DualNumber V).toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    show MvPolynomial.aeval _ (MvPolynomial.map _ (MvPolynomial.C r)) = dualMap _ (MvPolynomial.aeval _ (MvPolynomial.C r))
    rw [MvPolynomial.map_C, MvPolynomial.aeval_C, MvPolynomial.aeval_C]
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · intro s
    show MvPolynomial.aeval _ (MvPolynomial.map _ (MvPolynomial.X s)) = dualMap _ (MvPolynomial.aeval _ (MvPolynomial.X s))
    rw [MvPolynomial.map_X, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    split_ifs <;> ext <;> simp [dualMap]

set_option maxHeartbeats 1000000 in
theorem chartJetTan_holds : ChartJetTanSt Xo c := by
  intro T io y I d FT actT tgT uvecT xT hb hc hu
  letI := io.toAlgebra
  have hid : IsGrpPullback I.G.G I.G.G (𝟙 _) (𝟙 _) := ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy =>
    (mul_left_congr (Category.comp_id _) x₀ y₀ x y (hx.trans (Category.comp_id _)) (hy.trans (Category.comp_id _))).trans
      (Category.comp_id _).symm⟩
  let D : Fin d → (epsR T.V ⟶ I.G.G) := fun j => Over.homMk (Formalism.L2.Pj.homAt (𝟙 (Sp T.V))
    (jetTan ((0 : Fin 1), j) : Jet T.V (Fin 1 × Fin d) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫ xT 1).left
    ((Over.w _).trans (Category.comp_id _))
  let D' : Fin d → (epsR T.Fr ⟶ I.t'.G) := fun j => Over.homMk (spMap ((jetTan ((0 : Fin 1), j) :
    Jet T.Fr (Fin 1 × Fin d) (0 + 1) →ₐ[T.Fr] DualNumber T.Fr) : _ →+* _) ≫ JetTr.xL I xT 1) (by
      rw [Category.assoc, JetTr.xL_snd]; exact spMap_comp_alg _)
  have hD : ∀ j, (D' j).left ≫ I.m2.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (D j).left := fun j => by
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (JetTr.xL_fst I xT 1)).trans ((Category.assoc _ _ _).symm.trans
      (Eq.trans (congrArg (· ≫ (xT 1).left) ?_) (Category.assoc _ _ _))))
    exact (JetTr.spMap_comp' _ _).trans ((congrArg spMap (tan_coef j)).trans (JetTr.spMap_comp' _ _).symm)
  choose u' h₁ h₂ using I.lift
  have ho : ∀ τ i, u' τ i ≫ I.t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := fun τ i => by
    have : Mono (spMap (algebraMap T.V T.Fr)) := by
      have := IsPreimmersion.of_isLocalization (S := T.Fr) (nonZeroDivisors T.V)
      exact inferInstanceAs (Mono (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))))
    rw [← cancel_mono (spMap (algebraMap T.V T.Fr)), Category.assoc, ← I.m2.cart.1.w, ← Category.assoc, h₂, Category.assoc,
      Over.w]
    exact (JetTr.spMap_comp' _ _).trans ((congrArg spMap (RingHom.ext fun r => by
      ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])).trans (JetTr.spMap_comp' _ _).symm)
  let U' : Lt1 Dw → (epsR T.Fr ⟶ I.t'.G) := fun ℓ => Over.homMk (u' ℓ.1 ℓ.2) (ho _ _)
  have cb : ∀ ℓ, IsLieComb (fun i => algebraMap T.V T.Fr (uvecT ℓ i)) D' (U' ℓ) := fun ℓ =>
    Chart.comb_baseChange _ I.m2.cart (w := Over.homMk (I.ub ℓ.1 ℓ.2).left (Over.w (I.ub ℓ.1 ℓ.2)))
      ((Chart.comb_push hid _ D _).2 (by simp only [Category.comp_id]; exact hu ℓ)) hD (h₂ _ _)
  intro ℓ
  obtain ⟨u, a₁, a₂⟩ := (Chart.comb_push I.m1.cart _ _ _).1 (cb ℓ)
  exact ⟨u, fun i => (a₁ i).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _)), a₂.trans (h₁ _ _)⟩

set_option maxHeartbeats 1000000 in
theorem chartJetBasis_holds (hF : FrTanBasisSt Xo c) : ChartJetBasisSt Xo c := by
  intro T io y I d FT actT tgT uvecT xT hb hc hu
  letI := io.toAlgebra
  have hid : IsGrpPullback I.G.G I.G.G (𝟙 _) (𝟙 _) := ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy =>
    (mul_left_congr (Category.comp_id _) x₀ y₀ x y (hx.trans (Category.comp_id _)) (hy.trans (Category.comp_id _))).trans
      (Category.comp_id _).symm⟩
  let D : Fin d → (epsR T.V ⟶ I.G.G) := fun j => Over.homMk (Formalism.L2.Pj.homAt (𝟙 (Sp T.V))
    (jetTan ((0 : Fin 1), j) : Jet T.V (Fin 1 × Fin d) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫ xT 1).left
    ((Over.w _).trans (Category.comp_id _))
  let D' : Fin d → (epsR T.Fr ⟶ I.t'.G) := fun j => Over.homMk (spMap ((jetTan ((0 : Fin 1), j) :
    Jet T.Fr (Fin 1 × Fin d) (0 + 1) →ₐ[T.Fr] DualNumber T.Fr) : _ →+* _) ≫ JetTr.xL I xT 1) (by
      rw [Category.assoc, JetTr.xL_snd]; exact spMap_comp_alg _)
  have hD : ∀ j, (D' j).left ≫ I.m2.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (D j).left := fun j => by
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (JetTr.xL_fst I xT 1)).trans ((Category.assoc _ _ _).symm.trans
      (Eq.trans (congrArg (· ≫ (xT 1).left) ?_) (Category.assoc _ _ _))))
    exact (JetTr.spMap_comp' _ _).trans ((congrArg spMap (tan_coef j)).trans (JetTr.spMap_comp' _ _).symm)
  choose u' h₁ h₂ using I.lift
  have ho : ∀ τ i, u' τ i ≫ I.t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := fun τ i => by
    have : Mono (spMap (algebraMap T.V T.Fr)) := by
      have := IsPreimmersion.of_isLocalization (S := T.Fr) (nonZeroDivisors T.V)
      exact inferInstanceAs (Mono (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))))
    rw [← cancel_mono (spMap (algebraMap T.V T.Fr)), Category.assoc, ← I.m2.cart.1.w, ← Category.assoc, h₂, Category.assoc,
      Over.w]
    exact (JetTr.spMap_comp' _ _).trans ((congrArg spMap (RingHom.ext fun r => by
      ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])).trans (JetTr.spMap_comp' _ _).symm)
  let U' : Lt1 Dw → (epsR T.Fr ⟶ I.t'.G) := fun ℓ => Over.homMk (u' ℓ.1 ℓ.2) (ho _ _)
  have cb : ∀ ℓ, IsLieComb (fun i => algebraMap T.V T.Fr (uvecT ℓ i)) D' (U' ℓ) := fun ℓ =>
    Chart.comb_baseChange _ I.m2.cart (w := Over.homMk (I.ub ℓ.1 ℓ.2).left (Over.w (I.ub ℓ.1 ℓ.2)))
      ((Chart.comb_push hid _ D _).2 (by simp only [Category.comp_id]; exact hu ℓ)) hD (h₂ _ _)
  have := I.G.semi.smooth
  have := I.t'.semi.smooth
  let tg : Fin d → (epsR T.V ⟶ I.G.G) := fun j => Over.homMk (tgT j) ((hb.1 j).1.trans (Category.comp_id _))
  have ttg : ∀ j, IsTangent (tg j) := fun j => (Chart.tan_push hid _).2 (by simp only [Category.comp_id]; exact (hb.1 j).2)
  have tD : ∀ j, IsTangent (D j) := fun j => (Chart.tan_push hid _).2 (by
    have e := congrArg (fun q => q.left) (hc.zero 1)
    refine Eq.trans ?_ (e.trans ?_)
    · rw [Category.comp_id]
      refine (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (xT 1).left) ((JetTr.spMap_comp' _ _).trans (congrArg spMap ?_)))
      apply Ideal.Quotient.ringHom_ext
      apply MvPolynomial.ringHom_ext
      · intro r
        show (MvPolynomial.aeval _ (MvPolynomial.C r) : DualNumber T.V).fst = MvPolynomial.aeval _ (MvPolynomial.C r)
        rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C]; rfl
      · intro s
        show (MvPolynomial.aeval _ (MvPolynomial.X s) : DualNumber T.V).fst = MvPolynomial.aeval _ (MvPolynomial.X s)
        rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
        split_ifs <;> rfl
    · exact congrArg (· ≫ _) (show Spec.map (CommRingCat.ofHom (RingHom.id T.V)) ≫ 𝟙 _ = 𝟙 _ by simp))
  have eD : tg = D := funext fun j => Chart.eq_of_comb_single tD (ttg j) j
    ((Chart.comb_push hid _ D _).2 (by simp only [Category.comp_id]; exact hc.tan j))
  have bD : IsLieBasis D := eD ▸ ⟨ttg, fun w hw => by
    have := hb.2 w.left ⟨(Over.w w).trans (Category.comp_id _).symm, by
      simpa only [Category.comp_id] using (Chart.tan_push hid w).1 hw⟩
    simp only [Chart.comb_push hid, Category.comp_id]
    exact this⟩
  have bD' : IsLieBasis D' := Chart.isLieBasis_baseChange _ I.m2.cart bD hD
  let e := Fintype.equivFin (Lt1 Dw)
  have bU : IsLieBasis fun i => U' (e.symm i) := ⟨fun i => (Chart.tan_push I.m1.cart _).2
    ((congrArg (_ ≫ ·) (h₁ _ _)).trans (y.1.tan _ _).2), fun w hw => by
      obtain ⟨a, ha, hq⟩ := hF T.Fr y.1 (w.left ≫ I.m1.φ) ⟨Over.w (pushPt I.m1.cart.1.w w), (Chart.tan_push I.m1.cart w).1 hw⟩
      have k : ∀ b, IsLieComb b (fun i => U' (e.symm i)) w ↔ IsCombAt y.1.x (fun i => y.1.u (e.symm i).1 (e.symm i).2) b
          (w.left ≫ I.m1.φ) := fun b => (Chart.comb_push I.m1.cart _ _ _).trans (exists_congr fun u => and_congr_left'
        (forall_congr' fun i => Eq.congr_right (congrArg (_ ≫ ·) (h₁ _ _))))
      refine ⟨fun i => a (e.symm i), (k _).2 ha, fun b hb' => ?_⟩
      have := hq (fun ℓ => b (e ℓ)) (by simpa only [e, Equiv.apply_symm_apply] using (k b).1 hb')
      funext i; rw [← this]; simp⟩
  intro v
  obtain ⟨a, ha, hq⟩ := Chart.coords_basis bD' bU _ (fun i => cb (e.symm i)) v
  refine ⟨fun ℓ => a (e ℓ), fun j => (Fintype.sum_equiv e _ _ fun ℓ => by simp).trans (ha j), fun b hb' => ?_⟩
  have := hq (fun i => b (e.symm i)) fun j => (Fintype.sum_equiv e.symm _ _ fun i => rfl).trans (hb' j)
  funext ℓ; rw [← this]; simp

end Formalism.MainNotions.ModuliIntegralCharts.H1
