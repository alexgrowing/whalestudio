import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecScalScale
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValueAtUnitSection

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenericUnitValue

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem sval_of_secScal {X Y Y' Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
    {φ₁ : K → (Y' ⟶ X)} {ε₁ : K → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {φ₂ : K' → (Y ⟶ X)} {ε₂ : K' → ℤ}
    {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)} (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c)
    (r : Z ⟶ Y') (z : Z) {J} (hJ : Good L z J) :
    sval s₂ (r ≫ h) z J = gs r z ⊤ c * sval s₁ r z J := by
  have hj : ∀ q : K ⊕ K', Sum.elim (fun k => J (r ≫ φ₁ k)) (fun k => J ((r ≫ h) ≫ φ₂ k)) q =
      J (r ≫ Sum.elim φ₁ (fun k => h ≫ φ₂ k) q) := by
    intro q
    cases q with
    | inl q => rfl
    | inr q => exact congrArg J (Category.assoc _ _ _)
  have key := H (fun k => J (r ≫ φ₁ k)) (fun k => J ((r ≫ h) ≫ φ₂ k))
    (fun q₁ q₂ hq => by rw [hj, hj, hq])
  have m₂ := hJ.mem φ₂ (r ≫ h)
  have m : r z ∈ L.wchart φ₁ (fun k => J (r ≫ φ₁ k)) ⊓
      L.wchart (fun k => h ≫ φ₂ k) (fun k => J ((r ≫ h) ≫ φ₂ k)) := by
    refine ⟨hJ.mem φ₁ r, ?_⟩
    have e₃ : (fun k => J ((r ≫ h) ≫ φ₂ k)) = (fun k => J (r ≫ (fun k => h ≫ φ₂ k) k)) :=
      funext fun k => congrArg J (Category.assoc _ _ _)
    rw [e₃]
    exact hJ.mem (fun k => h ≫ φ₂ k) r
  have e := congrArg (gs r z _) key
  rw [gs_mul r z _ m] at e
  unfold resTop at e
  rw [gs_res r z _ m, gs_res r z _ m] at e
  have p := gs_pull r h z _ m₂ (s₂.f fun k => J ((r ≫ h) ≫ φ₂ k))
  exact p.symm.trans (e.trans (congrArg (gs r z ⊤ c * ·) (gs_res r z _ m _)))

theorem isUnit_cst_generic {V : Type} [CommRing V] [IsDomain V] (y : Spec (CommRingCat.of (FractionRing V)))
    {c : V} (hc : c ≠ 0) : IsUnit (cst (jK V) y c) := by
  have hK : IsUnit (algebraMap V (FractionRing V) c) :=
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hc)).isUnit
  obtain ⟨w, hw⟩ := hK
  rw [show cst (jK V) y c = cst (𝟙 _) y (algebraMap V (FractionRing V) c) from H1.gs_spec _ y c, ← hw]
  exact ⟨⟨cst (𝟙 _) y (w : FractionRing V), cst (𝟙 _) y (↑w⁻¹ : FractionRing V),
    by rw [← H1.cst_mul, Units.mul_inv, H1.cst_one], by rw [← H1.cst_mul, Units.inv_mul, H1.cst_one]⟩, rfl⟩

section

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]

lemma unitK_fst : (unitK (G := G)) ≫ pullback.fst G.hom (jK V) = jK V ≫ eSec G := by
  simp only [unitK, pullback.lift_fst]

lemma gs_unitK_scal (y : Spec (CommRingCat.of (FractionRing V))) (c : V) :
    gs (unitK (G := G)) y ⊤ (scal (pullback.snd G.hom (jK V) ≫ jK V) c) = cst (jK V) y c := by
  have hsec : (unitK (G := G)) ≫ pullback.snd G.hom (jK V) = 𝟙 _ := by
    simp only [unitK, pullback.lift_snd]
  unfold scal cst
  refine (gs_pull (unitK (G := G)) (pullback.snd G.hom (jK V) ≫ jK V) y ⊤ trivial _).trans ?_
  rw [← Category.assoc, hsec, Category.id_comp]

end

theorem value_at_generic_unit : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ (k : ℕ) (s : P.U.SecK k) (F : Fam P.D.toPre (FractionRing V) k) (u : P.U.SecK (k * N)) (F' : Fam P.D.toPre (FractionRing V) (k * N)), P.U.Expands k s F → P.U.Expands (k * N) u F' → PullAl P.D (FractionRing V) P.oD a k N F F' → ∀ (y : Spec (CommRingCat.of (FractionRing V))) (J), Geo.Tor.Good P.U.LG.L y J → Geo.Tor.sval u unitK y J = (Geo.Tor.val (L := P.U.LG.L) P.U.LG.rig (jK V) y J ^ (k * (N - 1))).val * Geo.Tor.sval s unitK y J := by
  intro hL V _ _ _ E _ _ _ H t P a N hN hN0
  intro k s F u F' hs hu hpull y J hJ
  let _ := H.starRing
  obtain ⟨uΨ, huΨ, -, -⟩ := P.w0
  obtain ⟨X, hX, hXc⟩ := exists_XB P.D P.D.toPre.P.isLB P.oD H.w0 uΨ huΨ a N hN hN0 1
  obtain ⟨c, σ'', τ, hc, hsτ, huσ, hth⟩ :=
    GlobalTheory.PullExpInt.main hL.globalFns V E H t P a N hN hN0 X hX hXc k s F u F' hs hu hpull
  have hv := GlobalTheory.UnitValue.value_at_unit_section V E H t P a N hN hN0 X hX hXc k σ'' τ hth _ (jK V) y J hJ
  have e₁ := sval_of_secScal huσ unitK y hJ
  have e₂ := sval_of_secScal hsτ unitK y hJ
  rw [unitK_fst, gs_unitK_scal] at e₁ e₂
  rw [e₁, e₂] at hv
  apply (isUnit_cst_generic y hc).mul_left_cancel
  rw [hv]
  ring

end GlobalTheory.GenericUnitValue
