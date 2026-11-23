import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsAbLift
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LiftConnectedOfTrivialUnique
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMemCommonChart
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GtPtsVal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.HtPt.Ppic
open GlobalTheory.UU ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht

theorem unit_prod_eq_one {K : Type} [Field K] [IsAlgClosed K] {A B : Over (Sp K)} [GeometricallyIntegral (A ⊗ B).hom]
    (a : 𝟙_ (Over (Sp K)) ⟶ A) (b : 𝟙_ (Over (Sp K)) ⟶ B) (v : Γ((A ⊗ B).left, ⊤)) (hv : IsUnit v)
    (h₁ : (lift (𝟙 A) (toUnit A ≫ b)).left.appTop.hom v = 1)
    (h₂ : (lift (toUnit B ≫ a) (𝟙 B)).left.appTop.hom v = 1) : v = 1 := by
  let Y := A ⊗ B
  let e : 𝟙_ (Over (Sp K)) ⟶ Y := lift a b
  let m : Y ⊗ Y ⟶ Y := lift (fst Y Y ≫ fst A B) (snd Y Y ≫ snd A B)
  have h1 : (toUnit Y ≫ e).left = Y.hom ≫ e.left := by rw [Over.comp_left, toUnit_left]
  have e₁ : lift (𝟙 Y) (toUnit Y ≫ e) ≫ m = fst A B ≫ lift (𝟙 A) (toUnit A ≫ b) := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · simp [m]
    · simp only [m, e, Category.assoc, lift_snd, lift_snd_assoc]
      rw [← Category.assoc, toUnit_unique (fst A B ≫ toUnit A) (toUnit _)]
  have e₂ : lift (toUnit Y ≫ e) (𝟙 Y) ≫ m = snd A B ≫ lift (toUnit B ≫ a) (𝟙 B) := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · simp only [m, e, Category.assoc, lift_fst, lift_fst_assoc]
      rw [← Category.assoc, toUnit_unique (snd A B ≫ toUnit B) (toUnit _)]
    · simp [m]
  have e₃ : lift (𝟙 Y) (𝟙 Y) ≫ m = 𝟙 Y := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_ <;> simp [m, Y]
  have key : m.left.appTop.hom v = 1 := by
    refine GlobalTheory.UnitRigidity.unit_eq_one_of_axes Y.hom e.left (Over.w _) (lift (𝟙 Y) (toUnit Y ≫ e)).left
      (lift (toUnit Y ≫ e) (𝟙 Y)).left ?_ ?_ ?_ ?_ _ (hv.map _) ?_ ?_
    · exact congrArg (·.left) (lift_fst (𝟙 Y) (toUnit Y ≫ e))
    · exact (congrArg (·.left) (lift_snd (𝟙 Y) (toUnit Y ≫ e))).trans h1
    · exact (congrArg (·.left) (lift_fst (toUnit Y ≫ e) (𝟙 Y))).trans h1
    · exact congrArg (·.left) (lift_snd (toUnit Y ≫ e) (𝟙 Y))
    · refine (over_appTop_comp _ m v).trans ?_
      rw [e₁, ← over_appTop_comp, h₁, map_one]
    · refine (over_appTop_comp _ m v).trans ?_
      rw [e₂, ← over_appTop_comp, h₂, map_one]
  have := over_appTop_comp (lift (𝟙 Y) (𝟙 Y)) m v
  rw [key, map_one, e₃, Over.id_left, Scheme.Hom.id_appTop] at this
  exact this.symm

theorem appTop_chV {S : Scheme.{0}} {X : Type} [AddCommGroup X] {W Z : Over S} (p : W ⟶ Z) (t : Z ⟶ splitTorus S X)
    (χ : X) : p.left.appTop.hom (chV t χ).val = (chV (p ≫ t) χ).val := by
  rw [chV_val, chV_val, over_appTop_comp]

theorem chV_one {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Z : Over S} (χ : X) :
    chV (1 : Z ⟶ splitTorus S X) χ = 1 := by rw [chV, map_one]; rfl

theorem unit_eq_char {K : Type} [Field K] [IsAlgClosed K] {X : Type} [AddCommGroup X] [TwoUniqueSums X]
    {G : Over (Sp K)} [GeometricallyIntegral (splitTorus (Sp K) X ⊗ G).hom] (b : 𝟙_ (Over (Sp K)) ⟶ G)
    (ρ : Γ((splitTorus (Sp K) X ⊗ G).left, ⊤)ˣ)
    (h : (lift (1 : G ⟶ splitTorus (Sp K) X) (𝟙 G)).left.appTop.hom ρ.val = 1) :
    ∃ χ : X, ρ = chV (fst (splitTorus (Sp K) X) G) χ := by
  let T := splitTorus (Sp K) X
  obtain ⟨c, χ, -, hc⟩ := torus_units K X (ρ.isUnit.map (lift (𝟙 T) (toUnit T ≫ b)).left.appTop.hom)
  have hχ : chi (S := Sp K) X χ = (chV (𝟙 T) χ).val := by
    rw [chV_val, Over.id_left, Scheme.Hom.id_appTop, GlobalTheory.SplitTorus.charUnit_val]
    rfl
  rw [hχ] at hc
  have c1 : T.hom.appTop.hom c = 1 := by
    have e := congrArg (1 : T ⟶ T).left.appTop.hom hc
    have q : (1 : T ⟶ T) ≫ lift (𝟙 T) (toUnit T ≫ b) = (toUnit T ≫ b) ≫ lift (1 : G ⟶ T) (𝟙 G) := by
      rw [comp_lift, comp_lift, Category.comp_id, Category.comp_id, MonObj.comp_one, ← Category.assoc,
        toUnit_unique (_ ≫ toUnit T) (toUnit T)]
    rw [over_appTop_comp, q, ← over_appTop_comp, h, map_one, map_mul, appTop_chV, Category.comp_id, chV_one,
      Units.val_one, _root_.mul_one, ← appTop_comp_apply, Over.w] at e
    exact e.symm
  rw [c1, _root_.one_mul] at hc
  refine ⟨χ, mul_inv_eq_one.1 (Units.ext ?_)⟩
  have inv : ∀ {W : Over (Sp K)} (p : W ⟶ T ⊗ G), p.left.appTop.hom ρ.val = (chV (p ≫ fst T G) χ).val →
      p.left.appTop.hom (ρ * (chV (fst T G) χ)⁻¹).val = 1 := fun p hp => by
    rw [Units.val_mul, map_mul, hp, ← appTop_chV, ← map_mul, Units.mul_inv, map_one]
  refine unit_prod_eq_one η[T] b _ (Units.isUnit _) (inv _ ?_) (inv _ ?_)
  · rw [lift_fst]
    exact hc
  · rw [lift_fst, ← Hom.one_def, chV_one]
    exact h

theorem weight : ∀ (k : Type) [Field k] [IsAlgClosed k] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] (T : GlobalTheory.UU.TQ G X) (N : LB T.B.left), N.IsLB → ∀ t : LB.Gen (N.pull T.q.left), t.IsGen → ∃ (χ : X) (t' : LB.Gen (N.pull T.q.left)), T.GenWt N t' χ := by
  intro k _ _ X _ _ _ G _ _ T N hN t ht
  have := T.q_hom
  have := T.i_hom
  let H := splitTorus (Sp k) X
  obtain ⟨_, _⟩ := GlobalTheory.TrivDescentCompare.smooth_conn T
  obtain ⟨_, _⟩ := GlobalTheory.TrivDescentCompare.smooth_conn (TQ.torus (Sp k) X)
  have : TwoUniqueSums X := inferInstance
  have : Smooth (H ⊗ G).hom := inferInstanceAs (Smooth (pullback.fst H.hom G.hom ≫ H.hom))
  have : GeometricallyConnected (pullback.fst H.hom G.hom) :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) (IsPullback.of_hasPullback H.hom G.hom).flip ‹_›
  have : GeometricallyConnected (H ⊗ G).hom := GeometricallyConnected.comp (pullback.fst H.hom G.hom) H.hom
  have : GeometricallyIntegral (H ⊗ G).hom := GlobalTheory.geometricallyIntegral_of_smooth _
  have hq : ∀ (Z : Over (Sp k)) (s : Z ⟶ H) (g : Z ⟶ G), ((s ≫ T.i) * g).left ≫ T.q.left = g.left ≫ T.q.left :=
    fun Z s g => GlobalTheory.TrivDescentCompare.act_q T s g
  let a : H ⊗ G ⟶ G := (fst H G ≫ T.i) * snd H G
  obtain ⟨ρ, hρ⟩ := exists_ratio hN (φ := fun _ : PUnit => a.left ≫ T.q.left)
    (φ' := fun _ : PUnit => (snd H G).left ≫ T.q.left) (ε := fun _ => 1) (funext fun _ => hq _ _ _)
    (LB.pullGen N (fun _ : PUnit => T.q.left) (fun _ => 1) t a.left)
    (LB.pullGen N (fun _ : PUnit => T.q.left) (fun _ => 1) t (snd H G).left)
    (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.pullGen_isGen _ _ _ _ ht _)
  have hv : ∀ (Z : Over (Sp k)) (s : Z ⟶ H) (g : Z ⟶ G) (z : Z.left) (J), Good N z J →
      val (L := N) (φ := fun _ : PUnit => T.q.left) (ε := fun _ => 1) t ((s ≫ T.i) * g).left z J =
        gm (lift s g).left z ⊤ ρ * val (L := N) (φ := fun _ : PUnit => T.q.left) (ε := fun _ => 1) t g.left z J := by
    intro Z s g z J hJ
    have e := hρ _ (lift s g).left z J hJ
    rw [val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, lift_snd, MonObj.comp_mul, lift_fst_assoc,
      lift_snd] at e
    exact e
  obtain ⟨χ, hχ⟩ := unit_eq_char η[G] ρ (by
    have e : Units.map (lift (1 : G ⟶ H) (𝟙 G)).left.appTop.hom.toMonoidHom ρ = 1 := unit_ext fun z _ => by
      obtain ⟨J, hJ⟩ := exists_good_pt hN z
      have e := hv G 1 (𝟙 G) z J hJ
      rw [MonObj.one_comp, _root_.one_mul] at e
      rw [← gm_top, map_one]
      exact (right_eq_mul.1 e)
    exact congrArg Units.val e)
  refine ⟨χ, t, ht, fun j => isWt_of_gm _ χ fun Z s g z hz => ?_⟩
  obtain ⟨J, hJ, hj⟩ := exists_good N hN z (fun _ : PUnit => g.left ≫ T.q.left) j (fun _ _ _ => rfl)
    (fun _ => (mem_pull (L := N) (F := T.q.left)).1 hz)
  have e := hv Z s g z J hJ
  rw [val_of _ _ _ _ j (fun u => (congrArg J (hq Z s g)).trans (hj u)), val_of _ _ _ _ j hj] at e
  refine e.trans (congrArg (· * _) ?_)
  rw [gm_charUnit, gm_top, hχ]
  refine congrArg _ (Units.ext ?_)
  exact (appTop_chV _ _ _).trans (by rw [lift_fst])

end PositivityTheory.HtPt.Ppic
