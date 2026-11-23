import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfShearAutomorphismLiftNilpotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfFlatPullbackReductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperGeometricallyConnectedSmoothNilpotentLifStatement
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftGroupLaw

theorem exists_grpObj_isAbelianScheme : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (A₀ : Over (Sp R₀)) [GrpObj A₀], IsAbelianScheme A₀ →
    ∀ (X : Over (Sp R)) (i : A₀.left ⟶ X.left), IsPullback i A₀.hom X.hom (spMap π) → Smooth X.hom →
    ∀ (e : Sp R ⟶ X.left), e ≫ X.hom = 𝟙 _ → (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left ≫ i = spMap π ≫ e →
    ∀ (l : (A₀ ⊗ A₀).left ⟶ (X ⊗ X).left), l ≫ (fst X X).left = (fst A₀ A₀).left ≫ i → l ≫ (snd X X).left = (snd A₀ A₀).left ≫ i →
    ∀ (m : X ⊗ X ⟶ X), l ≫ m.left = (μ[A₀]).left ≫ i →
    ∃ _ : GrpObj X, IsGrpPullback A₀ X (spMap π) i ∧ IsAbelianScheme X := by
  intro R R₀ _ _ π hπ hN A₀ _ hA X i hi hsm e he he1 l hl1 hl2 m hm
  haveI : Smooth X.hom := hsm
  haveI : IsCommMonObj A₀ := hA.comm
  obtain ⟨hpX, hgX⟩ := GlobalTheory.T.isProper_geometricallyConnected_smooth_nilpotent_lift R R₀ π hπ hN X A₀ i hi hsm hA.proper hA.geomConnected
  haveI := hpX
  haveI := hgX
  have s2 : Smooth (X ⊗ X).hom := by rw [Over.tensorObj_hom]; infer_instance
  have p2 : IsProper (X ⊗ X).hom := by rw [Over.tensorObj_hom]; infer_instance
  have g2 : GeometricallyConnected (X ⊗ X).hom := by
    rw [Over.tensorObj_hom]; exact GeometricallyConnected.comp _ _
  haveI := s2
  haveI := p2
  haveI := g2
  have s3 : Smooth ((X ⊗ X) ⊗ X).hom := by rw [Over.tensorObj_hom]; infer_instance
  have p3 : IsProper ((X ⊗ X) ⊗ X).hom := by rw [Over.tensorObj_hom]; infer_instance
  have g3 : GeometricallyConnected ((X ⊗ X) ⊗ X).hom := by
    rw [Over.tensorObj_hom]; exact GeometricallyConnected.comp _ _

  obtain ⟨jA, hjl⟩ : ∃ jA : (Over.map (spMap π)).obj A₀ ⟶ X, jA.left = i := ⟨Over.homMk i hi.w, rfl⟩
  obtain ⟨E, hEl⟩ : ∃ E : 𝟙_ (Over (Sp R)) ⟶ X, E.left = e := ⟨Over.homMk e he, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ L : (Over.map (spMap π)).obj (A₀ ⊗ A₀) ⟶ X ⊗ X,
      L = lift ((Over.map (spMap π)).map (fst A₀ A₀) ≫ jA) ((Over.map (spMap π)).map (snd A₀ A₀) ≫ jA) := ⟨_, rfl⟩
  have hL : L.left = l := by
    have p : IsPullback (fst X X).left (snd X X).left X.hom X.hom := IsPullback.of_hasPullback _ _
    refine p.hom_ext ?_ ?_
    · rw [← Over.comp_left, hLd, lift_fst, hl1, Over.comp_left, Over.map_map_left, hjl]
    · rw [← Over.comp_left, hLd, lift_snd, hl2, Over.comp_left, Over.map_map_left, hjl]
  have pt : ∀ (T : Over (Sp R₀)) (x y : T ⟶ A₀),
      lift ((Over.map (spMap π)).map x ≫ jA) ((Over.map (spMap π)).map y ≫ jA) = (Over.map (spMap π)).map (lift x y) ≫ L := by
    intro T x y
    rw [hLd, comp_lift, ← CategoryTheory.Functor.map_comp_assoc, ← CategoryTheory.Functor.map_comp_assoc, lift_fst, lift_snd]
  have hLm : L ≫ m = (Over.map (spMap π)).map μ[A₀] ≫ jA := by
    ext1; rw [Over.comp_left, hL, hm, Over.comp_left, Over.map_map_left, hjl]
  have ptm : ∀ (T : Over (Sp R₀)) (x y : T ⟶ A₀),
      lift ((Over.map (spMap π)).map x ≫ jA) ((Over.map (spMap π)).map y ≫ jA) ≫ m = (Over.map (spMap π)).map (x * y) ≫ jA := by
    intro T x y
    rw [pt, Category.assoc, hLm, ← CategoryTheory.Functor.map_comp_assoc, Hom.mul_def]
  have hE : ∀ T : Over (Sp R₀), (Over.map (spMap π)).map (1 : T ⟶ A₀) ≫ jA = toUnit _ ≫ E := by
    intro T
    have h1 : (1 : T ⟶ A₀) = (Over.homMk T.hom (Category.comp_id T.hom) : T ⟶ Over.mk (𝟙 (Sp R₀))) ≫ 1 := (comp_one _).symm
    ext1
    rw [Over.comp_left, Over.comp_left, Over.map_map_left, h1, Over.comp_left, Category.assoc, hjl, he1,
      Over.toUnit_left, Over.map_obj_hom, hEl]
    rfl
  have hj : (Over.map (spMap π)).map (𝟙 A₀) ≫ jA = jA := by rw [CategoryTheory.Functor.map_id, Category.id_comp]
  have hjE : jA ≫ toUnit X ≫ E = (Over.map (spMap π)).map (1 : A₀ ⟶ A₀) ≫ jA := by
    rw [hE, comp_toUnit_assoc]

  obtain ⟨τ, hτd⟩ : ∃ τ : X ⟶ X, τ = lift (toUnit X ≫ E) (𝟙 X) ≫ m := ⟨_, rfl⟩
  have hτ : jA ≫ τ = jA := by
    rw [hτd, comp_lift_assoc, Category.comp_id, hjE]
    have h := ptm A₀ 1 (𝟙 A₀)
    rw [hj, _root_.one_mul, hj] at h
    exact h
  have τiso : IsIso τ := by
    refine GlobalTheory.T.isIso_of_flat_pullback_reduction R R₀ π hπ hN X X A₀ A₀ i i hi hi inferInstance τ (𝟙 A₀) ?_ inferInstance
    have h := congrArg (fun g => g.left) hτ
    simp only [Over.comp_left, hjl] at h
    rw [h, Over.id_left, Category.id_comp]
  obtain ⟨m₁, hm₁d⟩ : ∃ m₁ : X ⊗ X ⟶ X, m₁ = m ≫ inv τ := ⟨_, rfl⟩
  have hjτ : jA ≫ inv τ = jA := by
    conv_lhs => rw [← hτ]
    rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have ptm₁ : ∀ (T : Over (Sp R₀)) (x y : T ⟶ A₀),
      lift ((Over.map (spMap π)).map x ≫ jA) ((Over.map (spMap π)).map y ≫ jA) ≫ m₁ = (Over.map (spMap π)).map (x * y) ≫ jA := by
    intro T x y
    rw [hm₁d, ← Category.assoc, ptm, Category.assoc, hjτ]
  have hLm₁ : L ≫ m₁ = (Over.map (spMap π)).map μ[A₀] ≫ jA := by
    rw [hm₁d, ← Category.assoc, hLm, Category.assoc, hjτ]
  have hm₁ : l ≫ m₁.left = (μ[A₀]).left ≫ i := by
    have h := congrArg (fun g => g.left) hLm₁
    simp only [Over.comp_left, Over.map_map_left, hL, hjl] at h
    exact h
  have one_mul₁ : lift (toUnit X ≫ E) (𝟙 X) ≫ m₁ = 𝟙 X := by
    rw [hm₁d, ← Category.assoc, ← hτd, IsIso.hom_inv_id]
  have hEE : lift E E ≫ m₁ = E := by
    have h := congrArg (fun g => E ≫ g) one_mul₁
    simp only [comp_lift_assoc, Category.comp_id] at h
    rwa [← Category.assoc, toUnit_unique (E ≫ toUnit X) (𝟙 _), Category.id_comp] at h

  have hμ : μ[A₀] = fst A₀ A₀ * snd A₀ A₀ := by rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  have σ₀iso : IsIso (lift (fst A₀ A₀) μ[A₀]) := by
    refine ⟨⟨lift (fst A₀ A₀) ((fst A₀ A₀)⁻¹ * snd A₀ A₀), ?_, ?_⟩⟩
    · apply CartesianMonoidalCategory.hom_ext
      · simp
      · rw [Category.assoc, lift_snd, comp_mul, GrpObj.comp_inv, lift_fst, lift_snd, hμ, inv_mul_cancel_left,
          Category.id_comp]
    · apply CartesianMonoidalCategory.hom_ext
      · simp
      · rw [Category.assoc, lift_snd, hμ, comp_mul, lift_fst, lift_snd, mul_inv_cancel_left, Category.id_comp]
  have hl₂ : IsPullback l (A₀ ⊗ A₀).hom (X ⊗ X).hom (spMap π) := GlobalTheory.AbDual.isPullback_prod hi hi hl1 hl2
  have hLfst : L ≫ fst X X = (Over.map (spMap π)).map (fst A₀ A₀) ≫ jA := by rw [hLd, lift_fst]
  have hLσ : L ≫ lift (fst X X) m₁ = (Over.map (spMap π)).map (lift (fst A₀ A₀) μ[A₀]) ≫ L := by
    rw [comp_lift, hLm₁, hLfst, ← pt]
  have σiso : IsIso (lift (fst X X) m₁) := by
    refine GlobalTheory.T.isIso_of_flat_pullback_reduction R R₀ π hπ hN (X ⊗ X) (X ⊗ X) (A₀ ⊗ A₀) (A₀ ⊗ A₀) l l hl₂ hl₂ inferInstance _ _ ?_ σ₀iso
    have h := congrArg (fun g => g.left) hLσ
    simp only [Over.comp_left, Over.map_map_left, hL] at h
    exact h
  have toLeft : ∀ {P Q : Over (Sp R)} (a : Q ⟶ P) (f f' : P ⟶ X), a ≫ f = a ≫ f' → a.left ≫ f.left = a.left ≫ f'.left :=
    fun a f f' h => by simpa only [Over.comp_left] using congrArg (fun g => g.left) h
  have EXT := GlobalTheory.T.eq_of_shear_automorphism_lift_nilpotent R R₀ π hπ hN A₀ X i hi l hl1 hl2 m₁ hm₁ σiso
  have hEu : toUnit (𝟙_ (Over (Sp R))) = 𝟙 _ := toUnit_unique _ _

  have mul_one₁ : lift (𝟙 X) (toUnit X ≫ E) ≫ m₁ = 𝟙 X := by
    refine EXT X A₀ i hi hsm hpX hgX e he _ _ ?_ ?_
    · rw [← hjl]
      apply toLeft
      rw [comp_lift_assoc, Category.comp_id, hjE]
      have h := ptm₁ A₀ (𝟙 A₀) 1
      rw [hj, _root_.mul_one, hj] at h
      exact h
    · rw [← hEl]
      apply toLeft
      simp only [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc, hEu, Category.id_comp, hEE]

  have comm₁ : (β_ X X).hom ≫ m₁ = m₁ := by
    refine EXT (X ⊗ X) (A₀ ⊗ A₀) l hl₂ s2 p2 g2 (lift E E).left (by simpa using Over.w (lift E E)) _ _ ?_ ?_
    · rw [← hL]
      apply toLeft
      rw [hLd, lift_braiding_hom_assoc, ptm₁, ptm₁, _root_.mul_comm]
    · apply toLeft
      rw [lift_braiding_hom_assoc]

  obtain ⟨L₃, hL₃d⟩ : ∃ L₃ : (Over.map (spMap π)).obj ((A₀ ⊗ A₀) ⊗ A₀) ⟶ (X ⊗ X) ⊗ X,
      L₃ = lift (lift ((Over.map (spMap π)).map (fst (A₀ ⊗ A₀) A₀ ≫ fst A₀ A₀) ≫ jA)
        ((Over.map (spMap π)).map (fst (A₀ ⊗ A₀) A₀ ≫ snd A₀ A₀) ≫ jA)) ((Over.map (spMap π)).map (snd (A₀ ⊗ A₀) A₀) ≫ jA) :=
    ⟨_, rfl⟩
  have hL₃1 : L₃ ≫ fst (X ⊗ X) X = (Over.map (spMap π)).map (fst (A₀ ⊗ A₀) A₀) ≫ L := by
    rw [hL₃d, lift_fst, pt, ← comp_lift, lift_fst_snd, Category.comp_id]
  have hL₃2 : L₃ ≫ snd (X ⊗ X) X = (Over.map (spMap π)).map (snd (A₀ ⊗ A₀) A₀) ≫ jA := by
    rw [hL₃d, lift_snd]
  have hk3 : IsPullback L₃.left ((A₀ ⊗ A₀) ⊗ A₀).hom ((X ⊗ X) ⊗ X).hom (spMap π) := by
    refine GlobalTheory.AbDual.isPullback_prod hl₂ hi (h := L₃.left) ?_ ?_
    · rw [← Over.comp_left, hL₃1, Over.comp_left, Over.map_map_left, hL]
    · rw [← Over.comp_left, hL₃2, Over.comp_left, Over.map_map_left, hjl]
  have assoc₁ : (m₁ ▷ X) ≫ m₁ = (α_ X X X).hom ≫ (X ◁ m₁) ≫ m₁ := by
    refine EXT ((X ⊗ X) ⊗ X) ((A₀ ⊗ A₀) ⊗ A₀) L₃.left hk3 s3 p3 g3 (lift (lift E E) E).left
      (by simpa using Over.w (lift (lift E E) E)) _ _ ?_ ?_
    · apply toLeft
      rw [hL₃d]
      simp only [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc, ptm₁]
      rw [_root_.mul_assoc]
    · apply toLeft
      simp only [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc, hEE]

  obtain ⟨iX, hiXd⟩ : ∃ iX : X ⟶ X, iX = lift (𝟙 X) (toUnit X ≫ E) ≫ inv (lift (fst X X) m₁) ≫ snd X X := ⟨_, rfl⟩
  have right_inv₁ : lift (𝟙 X) iX ≫ m₁ = toUnit X ≫ E := by
    have hp : (lift (𝟙 X) (toUnit X ≫ E) ≫ inv (lift (fst X X) m₁)) ≫ lift (fst X X) m₁ = lift (𝟙 X) (toUnit X ≫ E) := by
      rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    have h1 : (lift (𝟙 X) (toUnit X ≫ E) ≫ inv (lift (fst X X) m₁)) ≫ fst X X = 𝟙 X := by
      have h := congrArg (· ≫ fst X X) hp
      simp only [Category.assoc, lift_fst] at h
      simpa only [Category.assoc] using h
    have h2 : (lift (𝟙 X) (toUnit X ≫ E) ≫ inv (lift (fst X X) m₁)) ≫ m₁ = toUnit X ≫ E := by
      have h := congrArg (· ≫ snd X X) hp
      simp only [Category.assoc, lift_snd] at h
      simpa only [Category.assoc] using h
    have h3 : lift (𝟙 X) iX = lift (𝟙 X) (toUnit X ≫ E) ≫ inv (lift (fst X X) m₁) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [lift_fst, h1]
      · rw [lift_snd, hiXd, Category.assoc]
    rw [h3, h2]
  have left_inv₁ : lift iX (𝟙 X) ≫ m₁ = toUnit X ≫ E := by
    rw [← comm₁, lift_braiding_hom_assoc, right_inv₁]
  letI G : GrpObj X :=
    { one := E
      mul := m₁
      inv := iX
      one_mul := by
        rw [← cancel_epi (λ_ X).inv, Iso.inv_hom_id, ← one_mul₁, ← Category.assoc]
        congr 1
        ext1 <;> simp
      mul_one := by
        rw [← cancel_epi (ρ_ X).inv, Iso.inv_hom_id, ← mul_one₁, ← Category.assoc]
        congr 1
        ext1 <;> simp
      mul_assoc := assoc₁
      left_inv := left_inv₁
      right_inv := right_inv₁ }
  refine ⟨G, ⟨hi, fun T x y x₀ y₀ hx hy => ?_⟩, ⟨⟨comm₁⟩, hsm, hpX, hgX⟩⟩
  have ex : ∀ (z : T ⟶ A₀) (z₀ : Over.mk (T.hom ≫ spMap π) ⟶ X), z₀.left = z.left ≫ i →
      z₀ = (Over.map (spMap π)).map z ≫ jA := fun z z₀ h => by
    ext1
    rw [h, Over.comp_left, Over.map_map_left, hjl]
  rw [ex x x₀ hx, ex y y₀ hy, Hom.mul_def]
  change (lift ((Over.map (spMap π)).map x ≫ jA) ((Over.map (spMap π)).map y ≫ jA) ≫ m₁).left = _
  rw [ptm₁, Over.comp_left, Over.map_map_left, hjl]

end GlobalTheory.LiftGroupLaw
