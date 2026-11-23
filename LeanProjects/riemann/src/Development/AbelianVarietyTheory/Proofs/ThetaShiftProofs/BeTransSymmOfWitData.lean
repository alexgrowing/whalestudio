import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective

noncomputable section

namespace GlobalTheory.ThetaShiftProofs

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem exists_unit_gm_spMap {A F : Type} [CommRing A] [Field F] {X : Scheme.{0}} (f : A →+* F) (x : Sp A ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)ˣ) (z : Sp F) :
    ∃ u : Aˣ, (gm (spMap f ≫ x) z U a).val = toStk z (f u) := by
  let g : Γ(X, U) →+* A := (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp (x.appLE U ⊤ h).hom
  refine ⟨Units.map g.toMonoidHom a, ?_⟩
  have hz : (spMap f ≫ x) z ∈ U := h (show spMap f z ∈ (⊤ : (Sp A).Opens) from trivial)
  rw [← toStk_valF _ U z hz]
  congr 1
  have ht := (top_le_iff_mem (spMap f ≫ x) U z).2 hz
  rw [valF, dif_pos ht]
  have e1 : (spMap f ≫ x).appLE U ⊤ ht = x.appLE U ⊤ h ≫ (spMap f).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have e2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f)
  have e3 := congrArg (fun q => q.hom ((x.appLE U ⊤ h).hom a.val)) e2
  rw [e1]
  exact e3

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} {k : Type} [Field k] {b : O →+* k}

theorem psi_value_of_witData (a : ArcIn D l β k b)
    (P : Out.DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) [Module (𝓞 E) P.toPre.X]
    (oP : letI := H.starRing; P.toPre.OAct (𝓞 E)) (φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)) (e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X) (hW : WitData a P oP φ he w e)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing (PowerSeries k)) F] [Algebra (FractionRing k) F]
    (hF : ∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) =
        algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C x)))
    (z : Sp F) (y : a.D₀.X) (χ : P.toPre.X) (hχ : e y = χ) (j : P.toPre.P.L.ι)
    (hj : (P.toPre.c χ).left (cpt (PowerSeries k)) ∈ P.toPre.P.L.U j) :
    ∃ u : (PowerSeries k)ˣ,
      (gm (Out.jFK (R := PowerSeries k) F) z
        (LB.wchart P.toPre.P.L (K := PUnit) (fun _ => Out.ptK (P.toPre.c χ)) (fun _ => j))
        ((P.toPre.psi χ).s (fun _ => j))).val =
      toStk z ((algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ PowerSeries.X)) ^ (a.be y y / 2) *
        algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ u.val)) := by
  subst hχ
  obtain ⟨-, -, -, -, -, hG⟩ := hW
  have hG' := (genRel_iff w _ _ _ z).1 (hG F _ hF rfl y)
  obtain ⟨hp, hv⟩ := hG'
  let f : PowerSeries k →+* F :=
    (algebraMap (FractionRing (PowerSeries k)) F).comp (algebraMap (PowerSeries k) _)
  let x : Sp (PowerSeries k) ⟶ P.toPre.P.A.left := (P.toPre.c (e y)).left
  have hx : Out.jFK (R := PowerSeries k) F ≫ Out.ptK (P.toPre.c (e y)) = spMap f ≫ x := by
    have : spMap f = Out.jFK (R := PowerSeries k) F ≫ Out.jK (PowerSeries k) := by
      simp only [f, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [this, Category.assoc]
    rfl
  obtain ⟨j₀, hj₀⟩ := exists_chart a.D₀.P.isLB (φ (x (cpt (PowerSeries k))))
  have ht : ⊤ ≤ x ⁻¹ᵁ ((a.D₀.P.L.pull φ).U (fun _ => j₀) ⊓ P.toPre.P.L.U j) :=
    (top_le_iff_cpt _ _).2 ⟨mem_pull.2 hj₀, hj⟩
  have hz : (Out.jFK (R := PowerSeries k) F ≫ Out.ptK (P.toPre.c (e y))) z ∈
      (a.D₀.P.L.pull φ).U (fun _ => j₀) ⊓ P.toPre.P.L.U j := by
    rw [hx]
    exact ht (show spMap f z ∈ (⊤ : (Sp (PowerSeries k)).Opens) from trivial)
  have hz₀ := mem_pull.1 hz.1
  have H1 := hv (fun _ => j) (fun _ => j₀) (fun _ => hz₀) (fun _ => hz.2)
  rw [gm_pullGen', gm_pullGen', Category.id_comp, Category.id_comp, Fintype.prod_unique, zpow_neg_one,
    Units.val_mul, Units.inv_mul_eq_iff_eq_mul] at H1
  obtain ⟨u₁, hu₁⟩ := exists_unit_gm_spMap f x _ ht (w.s (fun _ => j₀, j)) z
  have hz₁ : (Out.jFK (R := k) F ≫ Out.ptK (a.D₀.c y)) z ∈ a.D₀.P.L.U j₀ := by
    rw [← hp PUnit.unit]; exact hz₀
  have ht₀ : ⊤ ≤ (𝟙 (Sp (FractionRing k))) ⁻¹ᵁ
      (LB.wchart a.D₀.P.L (K := PUnit) (fun _ => Out.ptK (a.D₀.c y)) (fun _ => j₀)) :=
    (top_le_iff_mem _ _ (Out.jFK (R := k) F z)).2 (Set.mem_iInter.2 fun _ => hz₁)
  obtain ⟨u₀, hu₀⟩ := exists_unit_gm_spMap (algebraMap (FractionRing k) F) (𝟙 _) _ ht₀ ((a.D₀.psi y).s (fun _ => j₀)) z
  obtain ⟨r, hr⟩ := (FractionRing.algEquiv k k).symm.surjective u₀.val
  have hr' : algebraMap k (FractionRing k) r = u₀.val := by
    rw [← hr]; exact ((FractionRing.algEquiv k k).symm.commutes r).symm
  have hr0 : r ≠ 0 := fun h0 => u₀.ne_zero (by rw [← hr', h0, map_zero])
  rw [← hr', hF, Category.comp_id] at hu₀
  rw [← hx] at hu₁
  refine ⟨u₁ * Units.map (PowerSeries.C (R := k)).toMonoidHom (Units.mk0 r hr0), H1.trans ?_⟩
  refine (congrArg₂ (· * ·) hu₁ (congrArg _ hu₀)).trans ?_
  simp only [Units.val_mul, map_mul]
  rw [mul_left_comm]
  rfl

theorem be_self_nonneg (a : ArcIn D l β k b) (y : a.D₀.X) : 0 ≤ a.be y y := by
  by_cases hy : y = 0
  · subst hy; simp
  · exact (a.be_pos y hy).le

theorem be_self_eq_of_witData (a : ArcIn D l β k b)
    (P : Out.DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) [Module (𝓞 E) P.toPre.X]
    (oP : letI := H.starRing; P.toPre.OAct (𝓞 E)) (φ₁ φ₂ : P.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he₁ : eSec P.toPre.P.A ≫ φ₁ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (he₂ : eSec P.toPre.P.A ≫ φ₂ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w₁ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₂))
    (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X)
    (h₁ : WitData a P oP φ₁ he₁ w₁ e₁) (h₂ : WitData a P oP φ₂ he₂ w₂ e₂) (y y' : a.D₀.X) (hy : e₁ y = e₂ y') :
    a.be y y = a.be y' y' := by
  let F := AlgebraicClosure (FractionRing (PowerSeries k))
  let f : PowerSeries k →+* F :=
    (algebraMap (FractionRing (PowerSeries k)) F).comp (algebraMap (PowerSeries k) _)
  have hf : Function.Injective f :=
    (algebraMap (FractionRing (PowerSeries k)) F).injective.comp (IsFractionRing.injective _ _)
  let g : k →+* F := f.comp (PowerSeries.C (R := k))
  let alg : Algebra (FractionRing k) F := (IsFractionRing.lift (K := FractionRing k) g.injective).toAlgebra
  have hF : ∀ x, @algebraMap (FractionRing k) F _ _ alg (algebraMap k _ x) =
      algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C x)) := fun x =>
    IsFractionRing.lift_algebraMap g.injective x
  have z : Sp F := (default : PrimeSpectrum F)
  obtain ⟨j, hj⟩ := exists_chart P.toPre.P.isLB ((P.toPre.c (e₁ y)).left (cpt (PowerSeries k)))
  obtain ⟨u, hu⟩ := @psi_value_of_witData E _ _ _ H D l c O _ β k _ b a P _ oP φ₁ he₁ w₁ e₁ h₁ F _ _ _ alg hF z y _ rfl j hj
  obtain ⟨u', hu'⟩ := @psi_value_of_witData E _ _ _ H D l c O _ β k _ b a P _ oP φ₂ he₂ w₂ e₂ h₂ F _ _ _ alg hF z y' _
    hy.symm j hj
  have e := (toStk z).injective (hu.symm.trans hu')
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (Int.ediv_nonneg (be_self_nonneg a y) (by norm_num : (0 : ℤ) ≤ 2))
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (Int.ediv_nonneg (be_self_nonneg a y') (by norm_num : (0 : ℤ) ≤ 2))
  rw [hm, hn, zpow_natCast, zpow_natCast] at e
  have e' : u.val * PowerSeries.X ^ m = u'.val * PowerSeries.X ^ n := by
    apply hf
    rw [map_mul, map_mul, map_pow, map_pow, mul_comm, mul_comm (f u')]
    exact e
  have hmn : m = n := IsDiscreteValuationRing.unit_mul_pow_congr_pow PowerSeries.X_irreducible PowerSeries.X_irreducible
    u u' m n e'
  have d : (2 : ℤ) ∣ a.be y y := (Dvd.intro _ rfl).trans (a.be_dvd y y)
  have d' : (2 : ℤ) ∣ a.be y' y' := (Dvd.intro _ rfl).trans (a.be_dvd y' y')
  omega

theorem be_trans_symm_of_witData (a : ArcIn D l β k b)
    (P : Out.DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) [Module (𝓞 E) P.toPre.X]
    (oP : letI := H.starRing; P.toPre.OAct (𝓞 E)) (φ₁ φ₂ : P.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he₁ : eSec P.toPre.P.A ≫ φ₁ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (he₂ : eSec P.toPre.P.A ≫ φ₂ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w₁ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₂))
    (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X)
    (h₁ : WitData a P oP φ₁ he₁ w₁ e₁) (h₂ : WitData a P oP φ₂ he₂ w₂ e₂) (y z : a.D₀.X) :
    a.be (e₁.trans e₂.symm y) (e₁.trans e₂.symm z) = a.be y z := by
  have key : ∀ v, a.be v v = a.be (e₁.trans e₂.symm v) (e₁.trans e₂.symm v) := fun v =>
    be_self_eq_of_witData a P oP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ h₁ h₂ v _ (by simp)
  have k₁ := key y
  have k₂ := key z
  have k₃ := key (y + z)
  have s₁ := a.be_symm z y
  have s₂ := a.be_symm (e₁.trans e₂.symm z) (e₁.trans e₂.symm y)
  simp only [map_add, LinearMap.add_apply] at k₃
  omega

theorem be_isometry_of_witData
    (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l)
    (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF)
    (P : Out.DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) [Module (𝓞 E) P.toPre.X]
    (oP : letI := H.starRing; P.toPre.OAct (𝓞 E)) (φ₁ φ₂ : P.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he₁ : eSec P.toPre.P.A ≫ φ₁ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (he₂ : eSec P.toPre.P.A ≫ φ₂ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w₁ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₂))
    (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X)
    (h₁ : WitData a P oP φ₁ he₁ w₁ e₁) (h₂ : WitData a P oP φ₂ he₂ w₂ e₂) :
    (∀ y y', e₁ y = e₂ y' → a.be y y = a.be y' y') ∧
      ∀ y z, a.be (e₁.trans e₂.symm y) (e₁.trans e₂.symm z) = a.be y z :=
  ⟨be_self_eq_of_witData a P oP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ h₁ h₂,
    be_trans_symm_of_witData a P oP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ h₁ h₂⟩

end GlobalTheory.ThetaShiftProofs
