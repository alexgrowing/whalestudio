import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.NuExtA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenInj

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing QForm
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem app_fst_eq_zero_of_snd {X T S : Scheme.{0}} (p : X ⟶ S) (t : T ⟶ S) (W : X.Opens) (d : Γ(X, W))
    (h : ((pullback.snd t p).app W).hom d = 0) : ((pullback.fst p t).app W).hom d = 0 := by
  rw [← CategoryTheory.Limits.pullbackSymmetry_hom_comp_snd, AlgebraicGeometry.Scheme.Hom.comp_app]
  erw [CommRingCat.hom_comp, RingHom.comp_apply, h, map_zero]

theorem snd_app_eq_zero {X T S : Scheme.{0}} (p : X ⟶ S) (t : T ⟶ S) (W : X.Opens) (d : Γ(X, W))
    (h : ∀ y : ↥(CategoryTheory.Limits.pullback t p : Scheme.{0}), CategoryTheory.Limits.pullback.snd t p y ∈ W → gs (CategoryTheory.Limits.pullback.snd t p) y W d = 0) :
    ((CategoryTheory.Limits.pullback.snd t p).app W).hom d = 0 := by
  refine TopCat.Presheaf.section_ext (CategoryTheory.Limits.pullback t p).sheaf _ _ _ fun y hy => ?_
  have hy' : CategoryTheory.Limits.pullback.snd t p y ∈ W := hy
  have := h y hy'
  simp only [gs, dif_pos hy'] at this
  erw [this]
  exact (map_zero _).symm

theorem secB_dvd_of_vge {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) {D : Out.DegData V (IsLocalRing.maximalIdeal V)}
    {vK : AddValuation (FractionRing V) (WithTop ℚ)} (hv : ValOver ϖ (FractionRing V) vK) {k : ℕ}
    {α : D.toPre.X}
    {E : LB.Sec (LB.LinComb D.toPre.P.L (Out.DegPre.famφ D.toPre (FractionRing V) α) (Out.DegPre.famε k))}
    (hE : VGe D (FractionRing V) vK k α E 0) {r : V} (hr : r ≠ 0) (f : D.toPre.SecB k α)
    (hf : Out.GeneratorPullback.SecScal D.toPre.P.L (Out.DegPre.famφ D.toPre (FractionRing V) α) (Out.DegPre.famε k) E
      (D.toPre.famφB α) (Out.DegPre.famε k) f (Out.DegPre.prB D.toPre (FractionRing V)).left
      (Out.scal (Out.DegPre.BF D.toPre (FractionRing V)).hom r)) :
    ∀ j, ∃ g : Γ(D.toPre.P.A.left, LB.wchart D.toPre.P.L (D.toPre.famφB α) j),
      f.f j = Geo.Tor.constFn D.toPre.P.A.hom _ r * g := by
  obtain ⟨n, a, σ, σF, hscal, hva, hsum⟩ := hE
  have hb : ∀ i, ∃ b : V, algebraMap V (FractionRing V) b = a i := fun i => by
    obtain ⟨b, hb⟩ := mem_range_of_val_nonneg hϖ hv (a i) (by simpa using hva i)
    exact ⟨b, hb⟩
  choose b hb using hb
  have hflat : Flat D.toPre.P.A.hom := by
    have := D.toPre.P.smoothDim
    have := SmoothOfRelativeDimension.smooth D.toPre.P.g D.toPre.P.A.hom
    infer_instance
  have hjK : IsOpenImmersion (jK V) := by
    obtain ⟨ϖ₀, h₀⟩ := IsDiscreteValuationRing.exists_irreducible V
    have := away_fractionRing h₀
    exact IsOpenImmersion.of_isLocalization ϖ₀
  have hjFK : IsIso (jFK (R := V) (FractionRing V)) := by
    show IsIso (Spec.map (CommRingCat.ofHom (RingHom.id (FractionRing V))))
    rw [CommRingCat.ofHom_id, Spec.map_id]
    infer_instance
  have ht : IsOpenImmersion (TF (R := V) (FractionRing V)).hom := by
    show IsOpenImmersion (jFK (R := V) (FractionRing V) ≫ jK V)
    infer_instance
  have : Nonempty (TF (R := V) (FractionRing V)).left := ⟨IsLocalRing.closedPoint (FractionRing V)⟩

  have hBF : (Out.DegPre.BF D.toPre (FractionRing V)).hom =
      pullback.snd (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom ≫ D.toPre.P.A.hom := pullback.condition
  have hnat : ∀ {R S : CommRingCat.{0}} (g : R ⟶ S) (x : R),
      (Spec.map g).appTop.hom ((Scheme.ΓSpecIso R).inv.hom x) = (Scheme.ΓSpecIso S).inv.hom (g.hom x) := by
    intro R S g x
    exact (congrArg (fun q => q.hom x) (Scheme.ΓSpecIso_inv_naturality g)).symm
  have hTF : ∀ c : V, (TF (R := V) (FractionRing V)).hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom c) =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom (algebraMap V (FractionRing V) c) := by
    intro c
    show (jFK (R := V) (FractionRing V) ≫ jK V).appTop.hom _ = _
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, hnat, hnat]
    rfl

  have H : ∀ j : (LB.LinComb D.toPre.P.L (D.toPre.famφB α) (Out.DegPre.famε k)).ι,
      f.f j - constFn D.toPre.P.A.hom _ r * ∑ i, constFn D.toPre.P.A.hom _ (b i) * (σ i).f j = 0 := by
    intro j
    refine eq_zero_of_app_fst_open D.toPre.P.A.hom (TF (R := V) (FractionRing V)).hom _ _
      (app_fst_eq_zero_of_snd _ _ _ _ (snd_app_eq_zero _ _ _ _ fun y hy => ?_))
    choose J hJ using fun ψ : (Out.DegPre.BF D.toPre (FractionRing V)).left ⟶ D.toPre.P.A.left =>
      exists_chart D.toPre.P.isLB (ψ y)
    have hG : Good D.toPre.P.L y J := hJ
    set π := pullback.snd (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom
    set U := (LB.LinComb D.toPre.P.L (D.toPre.famφB α) (Out.DegPre.famε k)).U j
    obtain ⟨tj, htj⟩ : ∃ tj, (trF (L := D.toPre.P.L) (D.toPre.famφB α) (Out.DegPre.famε k) π y j
        (fun k => J (π ≫ D.toPre.famφB α k))).val = tj := ⟨_, rfl⟩
    have e_f : gs π y U (f.f j) = tj * sval f π y J :=
      (sec_trans f π y hy (hG.mem _ π)).trans (congrArg (· * sval f π y J) htj)
    have e_σ : ∀ i, gs π y U ((σ i).f j) = tj * sval (σ i) π y J := fun i =>
      (sec_trans (σ i) π y hy (hG.mem _ π)).trans (congrArg (· * sval (σ i) π y J) htj)
    have hf' : sval f (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom) ≫ π) y J = gs (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y ⊤ (Out.scal (Out.DegPre.BF D.toPre (FractionRing V)).hom r) *
        sval E (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y J := secScal_sval_c hf (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y hG
    have hσ' : ∀ i, sval (σ i) (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom) ≫ π) y J = sval (σF i) (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y J := fun i =>
      SectionScalarValuation.secScal_sval (hscal i) (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y hG
    rw [Category.id_comp] at hf'
    simp only [Category.id_comp] at hσ'
    let bg : Fin n → Γ((pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom), ⊤) := fun i =>
      (pullback.fst (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom (a i))
    have hE' : sval E (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y J = ∑ i, gs (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y ⊤ (bg i) * sval (σF i) (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y J :=
      SectionScalarValuation.sval_lin bg σF hsum (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y hG
    have c1 : gs (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y ⊤ (Out.scal (Out.DegPre.BF D.toPre (FractionRing V)).hom r) = cst (π ≫ D.toPre.P.A.hom) y r :=
      (gs_pull (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) _ y ⊤ trivial _).trans (by rw [Category.id_comp, hBF]; rfl)
    have c2 : ∀ i, gs (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y ⊤ (bg i) = cst (π ≫ D.toPre.P.A.hom) y (b i) := by
      intro i
      refine (gs_pull (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) _ y ⊤ trivial _).trans ?_
      rw [Category.id_comp, cst, ← pullback.condition, ← gs_pull _ _ y ⊤ trivial]
      exact (congrArg (fun z => gs (pullback.fst (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom) y ⊤
          ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom z)) (hb i).symm).trans
        (congrArg (gs (pullback.fst (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom) y ⊤) (hTF (b i)).symm)
    have e_sub : gs π y U (f.f j - constFn D.toPre.P.A.hom U r * ∑ i, constFn D.toPre.P.A.hom U (b i) * (σ i).f j) =
        gs π y U (f.f j) - gs π y U (constFn D.toPre.P.A.hom U r) *
          ∑ i, gs π y U (constFn D.toPre.P.A.hom U (b i)) * gs π y U ((σ i).f j) := by
      simp only [gs_eq π y U hy, map_sub, map_mul, map_sum]
    rw [e_sub, e_f, hf', hE', gs_constFn _ _ _ _ hy]
    simp only [e_σ, hσ', c1, c2, gs_constFn _ _ _ _ hy]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_eq_zero fun i _ => by ring
  intro j
  exact ⟨_, sub_eq_zero.1 (H j)⟩

end ReciprocityTheory.ChartRestriction.G.DVR
