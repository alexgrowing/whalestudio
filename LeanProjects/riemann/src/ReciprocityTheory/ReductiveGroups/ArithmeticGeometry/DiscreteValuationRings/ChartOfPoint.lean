import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LiftOUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.UUA

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor TWO TWM SectionScalarValuation IsLocalRing

theorem chart_of_point {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) {n : ℕ} (b : Fin n → Γ(Y, ⊤)) (t : Fin n → LB.Sec (LB.LinComb L φ ε))
    (h : ∀ y I, Good L y I → sval s (𝟙 Y) y I = ∑ i, gs (𝟙 Y) y ⊤ (b i) * sval (t i) (𝟙 Y) y I) :
    ∀ j, s.f j = ∑ i, resTop _ (b i) * (t i).f j := by
  intro j
  refine fn_ext fun y hy0 => ?_
  have hy : y ∈ LB.wchart L φ j := hy0
  choose I hI using fun ψ : Y ⟶ X => exists_chart hL (ψ y)
  have hIy : Good L y I := hI
  have mm := hIy.mem φ (𝟙 _)
  have T0 := sec_trans s (𝟙 _) y hy mm
  set τ := (trF φ ε (𝟙 _) y j (fun k => I (𝟙 _ ≫ φ k))).val with hτ
  have RHS : gs (𝟙 _) y (LB.wchart L φ j) (∑ i, resTop (LB.wchart L φ j) (b i) *
      (show Γ(Y, LB.wchart L φ j) from (t i).f j)) =
      τ * ∑ i, gs (𝟙 _) y ⊤ (b i) * sval (t i) (𝟙 _) y I := by
    rw [gs_sum _ y _ hy, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gs_mul _ y _ hy, gs_res _ y le_top hy, sec_trans (t i) (𝟙 _) y hy mm, hτ]
    exact mul_left_comm _ _ _
  exact T0.trans ((congrArg (fun x => τ * x) (h y I hIy)).trans RHS.symm)

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]

theorem hformF (k : ℕ) (ρ : D.toPre.X) :
    FormEq (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB ρ i) (DegPre.famε k)
      (DegPre.famφ D.toPre F ρ) (DegPre.famε k) := by
  have e : (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB ρ i) = DegPre.famφ D.toPre F ρ := by
    funext i
    fin_cases i
    · simp [DegPre.famφ, DegPre.famφB]
    · show (DegPre.prB D.toPre F).left ≫ (padd D.toPre.P.A (𝟙 D.toPre.P.A) (toUnit D.toPre.P.A ≫ D.toPre.c ρ)).left =
        (padd D.toPre.P.A (DegPre.prB D.toPre F) (toUnit _ ≫ D.toPre.c ρ)).left
      rw [← Over.comp_left]
      congr 1
      simp only [padd]
      rw [← Category.assoc, CartesianMonoidalCategory.comp_lift, Category.comp_id, ← Category.assoc,
        CartesianMonoidalCategory.toUnit_unique (DegPre.prB D.toPre F ≫ toUnit _) (toUnit _)]
    · show (DegPre.prB D.toPre F).left ≫ (toUnit D.toPre.P.A ≫ D.toPre.c ρ).left = (toUnit _ ≫ D.toPre.c ρ).left
      rw [← Over.comp_left, ← Category.assoc,
        CartesianMonoidalCategory.toUnit_unique (DegPre.prB D.toPre F ≫ toUnit _) (toUnit _)]
    · show (DegPre.prB D.toPre F).left ≫ (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]).left =
        (toUnit _ ≫ η[D.toPre.P.A]).left
      rw [← Over.comp_left, ← Category.assoc,
        CartesianMonoidalCategory.toUnit_unique (DegPre.prB D.toPre F ≫ toUnit _) (toUnit _)]
  intro U _ h
  rw [e]

theorem hformF' (k : ℕ) (ρ : D.toPre.X) :
    FormEq (DegPre.famφ D.toPre F ρ) (DegPre.famε k)
      (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB ρ i) (DegPre.famε k) := by
  have e : (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB ρ i) = DegPre.famφ D.toPre F ρ := by
    funext i
    fin_cases i
    · simp [DegPre.famφ, DegPre.famφB]
    · show (DegPre.prB D.toPre F).left ≫ (padd D.toPre.P.A (𝟙 D.toPre.P.A) (toUnit D.toPre.P.A ≫ D.toPre.c ρ)).left =
        (padd D.toPre.P.A (DegPre.prB D.toPre F) (toUnit _ ≫ D.toPre.c ρ)).left
      rw [← Over.comp_left]
      congr 1
      simp only [padd]
      rw [← Category.assoc, CartesianMonoidalCategory.comp_lift, Category.comp_id, ← Category.assoc,
        CartesianMonoidalCategory.toUnit_unique (DegPre.prB D.toPre F ≫ toUnit _) (toUnit _)]
    · show (DegPre.prB D.toPre F).left ≫ (toUnit D.toPre.P.A ≫ D.toPre.c ρ).left = (toUnit _ ≫ D.toPre.c ρ).left
      rw [← Over.comp_left, ← Category.assoc,
        CartesianMonoidalCategory.toUnit_unique (DegPre.prB D.toPre F ≫ toUnit _) (toUnit _)]
    · show (DegPre.prB D.toPre F).left ≫ (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]).left =
        (toUnit _ ≫ η[D.toPre.P.A]).left
      rw [← Over.comp_left, ← Category.assoc,
        CartesianMonoidalCategory.toUnit_unique (DegPre.prB D.toPre F ≫ toUnit _) (toUnit _)]
  intro U _ h
  rw [e]

theorem gF_gs (c : F) (y : (DegPre.BF D.toPre F).left) :
    gs (𝟙 _) y ⊤ (gF D.toPre F c) = gs (fst (TF (R := V) F) D.toPre.P.A).left y ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) := by
  first
  | rfl
  | exact (gs_appLE_top _ _ _ le_top _).symm
  | (unfold gF; exact (gs_appLE_top _ _ _ le_top _).symm)
  | simp [gF, gs_appLE_top]

theorem coordsF {k : ℕ} {ρ : D.toPre.X} {m : ℕ} (b : Fin m → D.toPre.SecB k ρ)
    (hb : ∀ (R' : Type) [CommRing R'] (f : V →+* R'),
      ∀ b' : Fin m → LB.Sec (LB.LinComb D.toPre.P.L
          (fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.toPre.P.A).left ≫ DegPre.famφB D.toPre ρ i)
          (DegPre.famε k)),
        (∀ i, IsPullSecLC D.toPre.P.L (DegPre.famφB D.toPre ρ) (DegPre.famε k)
          (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.toPre.P.A).left (b i) (b' i)) →
        IsSecBasis (T := Over.mk (Spec.map (CommRingCat.ofHom f))) (A := D.toPre.P.A) _ b')
    (bF : Fin m → LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k)))
    (hbF : ∀ i (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
      sval (bF i) (𝟙 _) y J = sval (b i) (DegPre.prB D.toPre F).left y J) :
    (∀ t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k)), ∃ c : Fin m → F,
      ∀ (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
        sval t (𝟙 _) y J = ∑ i, gs (𝟙 _) y ⊤ (gF D.toPre F (c i)) * sval (bF i) (𝟙 _) y J) ∧
    (∀ c : Fin m → F, (∀ (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
        ∑ i, gs (𝟙 _) y ⊤ (gF D.toPre F (c i)) * sval (bF i) (𝟙 _) y J = 0) → c = 0) := by
  have hL := D.toPre.P.isLB
  have eT : Over.mk (Spec.map (CommRingCat.ofHom (algVF (F := F) (V := V)))) = TF (R := V) F := by
    rw [← TF_hom]; rfl
  have hbF' := hb F (algVF (F := F) (V := V))
  rw [eT] at hbF'
  let b' := fun i => pullSec D.toPre.P.L (DegPre.famφB D.toPre ρ) (DegPre.famε k) (b i)
    (snd (TF (R := V) F) D.toPre.P.A).left
  have hB := hbF' b' (fun i j => rfl)
  have hb' : ∀ i (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
      sval (b' i) (𝟙 _) y J = sval (bF i) (𝟙 _) y J := fun i y J hJ => by
    rw [hbF i y J hJ]
    exact (sval_pullSec _ _ _ _ _ y hJ).trans (by rw [Category.id_comp])
  refine ⟨fun t => ?_, fun c hc => ?_⟩
  · obtain ⟨t', ht'⟩ := exists_sec hL (hformF' k ρ) t
    obtain ⟨r, hr, -⟩ := hB t'
    choose c hc using fun i => (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 (r i)
    refine ⟨c, fun y J hJ => ?_⟩
    rw [← ht' _ (𝟙 _) y J hJ, sval_lin (fun i => (fst (TF (R := V) F) D.toPre.P.A).left.appTop.hom (r i)) b' hr (𝟙 _) y hJ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb' i y J hJ, gF, RingHom.comp_apply, ← hc i]
  · let z0 : LB.Sec (LB.LinComb D.toPre.P.L (fun i => (snd (TF (R := V) F) D.toPre.P.A).left ≫ DegPre.famφB D.toPre ρ i)
      (DegPre.famε k)) := SecOps.secZero
    have r1 := chart_of_point hL z0 (fun i => (fst (TF (R := V) F) D.toPre.P.A).left.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i))) b' (fun y I hI => by
        rw [sval_zero_of (fun j => rfl) _ y I (hI.mem _ _), ← hc y I hI]
        exact Finset.sum_congr rfl fun i _ => by rw [hb' i y I hI]; rfl)
    have r0 : ∀ j, z0.f j = ∑ i, resTop _ ((fst (TF (R := V) F) D.toPre.P.A).left.appTop.hom 0) * (b' i).f j := fun j => by
      simp only [map_zero, MulZeroClass.zero_mul, Finset.sum_const_zero]; rfl
    obtain ⟨r, -, hu⟩ := hB z0
    have e := (hu _ r1).trans (hu _ r0).symm
    funext i
    have hi : (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i) = 0 := congrFun e i
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom hi
    simpa using this

end ReciprocityTheory.ChartRestriction.G.DVR.UUA
