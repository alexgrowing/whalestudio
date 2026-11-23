import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassTorsionPointLocalSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointClassMulEqAddStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointClassAtStalkSmulActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfTorsionPointClassAtStalkEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointClassImageEqLevelActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelSectionOfIdealTorsionAtGeometricPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSectionInjectiveAtGeometricPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSectionAddAtGeometricPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSectionSmulAtGeometricPointStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
set_option autoImplicit false
noncomputable section
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.TorsSpec

theorem one_left {X' : Scheme.{0}} {G : Over X'} [GrpObj G] {Y : Scheme.{0}} (t : Y ⟶ X') :
    (1 : Over.mk t ⟶ G).left = t ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

end GlobalTheory.TorsSpec

namespace GlobalTheory.EqvAct

open GlobalTheory.TorsSpec in

theorem torsLevel_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ (I : Ideal (𝓞 E)) (g : ℕ), NeatPrime I g (Dw.p + Dw.q) → l.Mb ≤ I → ∀ (Γ : Type) [Group Γ] [Finite Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), ActsBy ι ρ → ∀ (X' : Scheme.{0}) [IsIntegral X'] (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (ρ' : Γ →* Aut X'), GlobalTheory.IsNormalScheme X' → IsProjOver (φ ≫ s₀ TF.Y Z) → IsOpenImmersion ℓ → ℓ ≫ φ = j₀ TF.Y Z → (∀ γ, (ρ γ).hom ≫ ℓ = ℓ ≫ (ρ' γ).hom) → ∀ m : Γ → ((GlobalTheory.EqvAct.pullG TF Z φ).left ⟶ (GlobalTheory.EqvAct.pullG TF Z φ).left), GlobalTheory.EqvAct.IsEqvAct ρ' (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullAct TF Z φ) m → GlobalTheory.EqvAct.MovesEta TF Z ι ρ ℓ (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullψ TF Z φ) m → GlobalTheory.EqvAct.TorsLevel I ι ρ' (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullAct TF Z φ) m := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ I g _ hMb Γ _ _ ι ρ _ X' _ φ ℓ ρ' hX _ hℓo hℓ hρ m hm hmv
  haveI := hX
  haveI := hℓo
  have hsemi : IsSemiAbelian (pullG TF Z φ) := IsSemiAbelian.pullback _ _ TF.Y.t.semi
  haveI := hsemi.smooth
  haveI := hsemi.separated
  haveI := hsemi.comm
  haveI : Nonempty (V₀ TF.Y Z) := by
    obtain ⟨z, hz⟩ := Z.2.1.nonempty
    exact ⟨⟨z, (j_mem_barComp Z z).2 hz⟩⟩
  have hn : IsUnit ((l.M : ℕ) : Γ(X', ⊤)) := by
    have h0 : IsUnit ((l.M : ℕ) : c.F) := isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (by have := l.three_le; omega))
    have := h0.map (((φ ≫ s₀ TF.Y Z).appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom)
    simpa using this
  have hnI : ((l.M : ℕ) : 𝓞 E) ∈ I := by
    have h0 : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]
      exact Ideal.mem_span_singleton_self _
    exact hMb ((Ideal.mul_le_inf.trans inf_le_left) h0)
  have hmv' : ∀ γ x, etaSecL TF Z φ ℓ hℓ x ≫ m γ = (ρ γ).hom ≫ etaSecL TF Z φ ℓ hℓ (ι γ x) := by
    intro γ x
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (ι γ (Submodule.Quotient.mk b))
    rw [← ha]
    refine hmv γ a b ?_ _ _ (etaSecL_w TF Z φ ℓ hℓ _) (etaSecL_w TF Z φ ℓ hℓ _) (etaSecL_ψ TF Z φ ℓ hℓ b)
      (etaSecL_ψ TF Z φ ℓ hℓ a)
    rw [ha]
    exact ((ι γ).symm_apply_apply _).symm
  intro K _ _ t
  classical
  have hlift : ∀ P : Over.mk t ⟶ pullG TF Z φ, IsTorsI I (pullAct TF Z φ) P →
      ∃ PT : Sp K ⟶ (torsion (pullG TF Z φ) l.M).left, PT ≫ (torsion.ι (pullG TF Z φ) l.M).left = P.left ∧
        ∃ x, ValAt (pullG TF Z φ) l.M ℓ (etaSecL TF Z φ ℓ hℓ) (PT (IsLocalRing.closedPoint K)) x := by
    intro P hP
    have h1 : P ≫ mulN (pullG TF Z φ) l.M = 1 := by rw [← act_natCast (pullAct TF Z φ)]; exact hP _ hnI
    obtain ⟨PT, hPT⟩ := exists_lift_torsion l.M P h1
    have hPT' : PT.left ≫ (torsion.ι (pullG TF Z φ) l.M).left = P.left := by rw [← Over.comp_left, hPT]
    refine ⟨PT.left, hPT', GlobalTheory.T.exists_class_torsionPoint_localScheme (pullG TF Z φ) l.M hn ℓ (etaSecL TF Z φ ℓ hℓ) (etaSecL_w TF Z φ ℓ hℓ)
      (pullAct TF Z φ) I (GlobalTheory.T.exists_levelSection_of_ideal_torsion_at_geometricPoint TF Z φ ℓ hℓ I hMb) K PT.left (fun a ha => ?_) _⟩
    have e1 := congrArg Over.Hom.left (hP a ha)
    rw [Over.comp_left, one_left] at e1
    rw [reassoc_of% hPT', e1, ← Category.assoc, Over.w PT]
    rfl
  let PT : ∀ P, IsTorsI I (pullAct TF Z φ) P → (Sp K ⟶ (torsion (pullG TF Z φ) l.M).left) :=
    fun P h => Classical.choose (hlift P h)
  have hPT : ∀ P h, PT P h ≫ (torsion.ι (pullG TF Z φ) l.M).left = P.left :=
    fun P h => (Classical.choose_spec (hlift P h)).1
  let cl : ∀ P, IsTorsI I (pullAct TF Z φ) P → LevelMod Dw l :=
    fun P h => Classical.choose (Classical.choose_spec (hlift P h)).2
  have hcl : ∀ P h, ValAt (pullG TF Z φ) l.M ℓ (etaSecL TF Z φ ℓ hℓ) (PT P h (IsLocalRing.closedPoint K)) (cl P h) :=
    fun P h => Classical.choose_spec (Classical.choose_spec (hlift P h)).2
  have hun := GlobalTheory.T.levelSection_injective_at_geometricPoint TF Z φ ℓ hℓ
  refine ⟨fun P => if h : IsTorsI I (pullAct TF Z φ) P then cl P h else 0, ?_, ?_, ?_, ?_⟩
  · intro P Q hP hQ
    have hPQ : IsTorsI I (pullAct TF Z φ) (P * Q) := fun a ha => by
      haveI := (pullAct TF Z φ).hom a
      rw [MonObj.mul_comp, hP a ha, hQ a ha, _root_.mul_one]
    simp only [dif_pos hP, dif_pos hQ, dif_pos hPQ]
    exact GlobalTheory.T.torsionPoint_class_mul_eq_add (pullG TF Z φ) l.M hn ℓ (etaSecL TF Z φ ℓ hℓ) (etaSecL_w TF Z φ ℓ hℓ) hun
      (GlobalTheory.T.levelSection_add_at_geometricPoint TF Z φ ℓ hℓ) K t P Q _ _ _ (hPT P hP) (hPT Q hQ) (hPT _ hPQ) _ _ _ _ (hcl P hP) (hcl Q hQ)
      (hcl _ hPQ)
  · intro P a hP
    have hPa : IsTorsI I (pullAct TF Z φ) (P ≫ (pullAct TF Z φ).act a) := fun r hr => by
      rw [Category.assoc, ← (pullAct TF Z φ).mul]
      exact hP _ (I.mul_mem_left a hr)
    simp only [dif_pos hP, dif_pos hPa]
    exact GlobalTheory.T.torsionPointClassAtStalk_smul_action (pullG TF Z φ) l.M hn ℓ (etaSecL TF Z φ ℓ hℓ) (etaSecL_w TF Z φ ℓ hℓ) hun (pullAct TF Z φ)
      (GlobalTheory.T.levelSection_smul_at_geometricPoint TF Z φ ℓ hℓ) K t P a _ _ (hPT P hP) (hPT _ hPa) _ _ _ (hcl P hP) (hcl _ hPa)
  · intro P Q hP hQ he
    simp only [dif_pos hP, dif_pos hQ] at he
    exact GlobalTheory.T.eq_of_torsionPointClassAtStalk_eq (pullG TF Z φ) l.M hn ℓ (etaSecL TF Z φ ℓ hℓ) (etaSecL_w TF Z φ ℓ hℓ) K t P Q _ _
      (hPT P hP) (hPT Q hQ) _ _ (hcl P hP) (he ▸ hcl Q hQ)
  · intro γ ht P Q hP hQP
    have hQ : IsTorsI I (pullAct TF Z φ) Q := fun a ha => by
      refine Over.OverMorphism.ext ?_
      have e1 := congrArg Over.Hom.left (hP a ha)
      rw [one_left] at e1
      rw [Over.comp_left, one_left, hQP, Category.assoc, ← hm.2.1 γ a, ← Category.assoc, ← Over.comp_left, e1,
        Category.assoc, eta_comp_of_isGrpPullback (hm.1 γ), ← Category.assoc, ht]
    simp only [dif_pos hP, dif_pos hQ]
    exact GlobalTheory.T.torsionPoint_class_image_eq_level_action (pullG TF Z φ) l.M hn ℓ (etaSecL TF Z φ ℓ hℓ) (etaSecL_w TF Z φ ℓ hℓ) hun (pullAct TF Z φ)
      ρ' ρ hρ ι m hm hmv' K t γ P Q _ _ (hPT P hP) (hPT Q hQ) hQP _ _ _ (hcl P hP) (hcl Q hQ)

end GlobalTheory.EqvAct
