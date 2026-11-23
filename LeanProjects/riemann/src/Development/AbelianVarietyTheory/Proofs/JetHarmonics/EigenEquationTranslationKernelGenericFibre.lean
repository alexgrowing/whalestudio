import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ColValMonomial
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TranslatePullbackEigensection
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThreePointSeriesExponentialOfDefect
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.EigenEquationOfForallGeometricPoint
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecLinIffComb
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGenMoveBack

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FieldBaseChange (constVal isoVal)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Jets

theorem units_mul_pow_mul_inv_cancel {R : Type} [CommRing R] (x y m : Rˣ) (s : R) :
    x.val * s * (y * x⁻¹ * m).val = y.val * (m.val * s) := by
  rw [Units.val_mul, Units.val_mul]
  linear_combination (s * y.val * m.val) * x.mul_inv

theorem ring_relation_transfer_identity {R : Type} [CommRing R] {t t' m m' e : R} (E : t' * m = e * (t * m')) (x y y' : R) :
    y' * t' * (y * x * m) = e * (y * t * (y' * x * m')) := by
  linear_combination (x * y * y') * E

theorem sval_of_isoRelM {Y Y' X₁ X₂ Z₁ Z : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    {w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)} {m : Y' ⟶ Y} {k : ℕ} {g₁ : Z₁ ⟶ X₁} {h₁ : Y' ⟶ Z₁}
    {a : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => g₁) (fun _ => (k : ℤ)))}
    {b : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => m ≫ f₂) (fun _ => (k : ℤ)))}
    (H : GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ a (m ≫ f₂) (𝟙 _) b) (r : Z ⟶ Y') (z : Z) {J₂} {J₁}
    (hJ₂ : Good L₂ z J₂) (hJ₁ : Good L₁ z J₁) :
    sval b r z J₂ = (isoVal w (r ≫ m) z (J₂ ((r ≫ m) ≫ f₂)) (J₁ ((r ≫ m) ≫ f₁)) ^ (k : ℤ)).val *
      sval a (r ≫ h₁) z J₁ := by
  have := (GlobalTheory.FieldBaseChange.isoRelM_iff w m k h₁ H.1 _ H.2.1 a b).1 H Z r z _ _
    (hJ₂ ((r ≫ m) ≫ f₂)) (hJ₁ ((r ≫ m) ≫ f₁))
  rw [Category.comp_id] at this
  rw [GlobalTheory.FieldBaseChange.sval_eq_powVal, GlobalTheory.FieldBaseChange.sval_eq_powVal, Category.assoc r h₁, H.1,
    ← Category.assoc r m f₁, ← Category.assoc r m f₂]
  exact this

theorem eigen_transfer {S X : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] (e : B ≅ A)
    [IsMonHom e.hom] {L₁ : LB A.left} {L₂ : LB X} (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) (f : B.left ⟶ X)
    {K : Type} [Field K] (p : Spec (CommRingCat.of K) ⟶ S) (φ : X ⟶ X) (b : B ⟶ B) (hφ : b.left ≫ f = f ≫ φ)
    (a : A ⟶ A) (ha : IsMonHom a) (hb : b ≫ e.hom = e.hom ≫ a) (N k : ℕ)
    (mu : LB.Gen (LB.LinComb L₂ (K := Fin 2) ![𝟙 X, φ] ![(N : ℤ), -1])) (hmu : mu.IsGen)
    (w : LB.Iso (L₁.pull e.hom.left) (L₂.pull f)) (hw : w.IsGen)
    (σ₀ : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => (snd (Over.mk p) B).left ≫ f) (fun _ => (k : ℤ))))
    (σ' τ : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => (snd (Over.mk p) B).left ≫ f)
      (fun _ => ((k * N : ℕ) : ℤ))))
    (t' t : LB.Sec (LPow A L₁ ((k * N : ℕ) : ℤ) (Over.mk p)))
    (h₀ : ∀ (y : (Over.mk p ⊗ B).left) (J), Good L₂ y J → sval σ' (𝟙 _) y J =
      sval σ₀ (Over.mk p ◁ b).left y J * (val mu ((snd (Over.mk p) B).left ≫ f) y J).val ^ k)
    (h₁ : GeneratorPullback.IsoRelM L₁ L₂ e.hom.left f w (snd (Over.mk p) B).left (k * N) (snd (Over.mk p) A).left
      (lift (fst (Over.mk p) B) (snd (Over.mk p) B ≫ e.hom)).left t' ((snd (Over.mk p) B).left ≫ f) (𝟙 _) σ')
    (h₂ : GeneratorPullback.IsoRelM L₁ L₂ e.hom.left f w (snd (Over.mk p) B).left (k * N) (snd (Over.mk p) A).left
      (lift (fst (Over.mk p) B) (snd (Over.mk p) B ≫ e.hom)).left t ((snd (Over.mk p) B).left ≫ f) (𝟙 _) τ)
    (θ : ThetaGrp A L₁ ((k * N : ℕ) : ℤ) (Over.mk p)) (hθ : IsActOf A L₁ ((k * N : ℕ) : ℤ) θ t' t)
    (c : Over.mk p ⟶ A) (u : Γ((Over.mk p).left, ⊤)ˣ) (hc : c ≫ a = 1)
    (hW : WeilIs A L₁ ((k * N : ℕ) : ℤ) c θ.pt u)
    (Z : Scheme.{0}) (ρ : Z ⟶ (Over.mk p ⊗ B).left) (z : Z) (J) (hJ : Good L₂ z J) :
    sval τ (ρ ≫ (translT B (c ≫ e.inv)).left) z J * (val mu (ρ ≫ (snd (Over.mk p) B).left ≫ f) z J).val ^ k =
      gs (ρ ≫ (fst (Over.mk p) B).left) z ⊤ u.val * (sval τ ρ z J *
        (val mu ((ρ ≫ (translT B (c ≫ e.inv)).left) ≫ (snd (Over.mk p) B).left ≫ f) z J).val ^ k) := by
  obtain ⟨g, hg⟩ : ∃ g, g = lift (fst (Over.mk p) B) (snd (Over.mk p) B ≫ e.hom) := ⟨_, rfl⟩
  rw [← hg] at h₁ h₂
  have g₁ : g ≫ fst _ _ = fst _ _ := by rw [hg, lift_fst]
  have g₂ : g ≫ snd _ _ = snd _ _ ≫ e.hom := by rw [hg, lift_snd]
  let n : Over.mk p ⊗ A ⟶ Over.mk p ⊗ B := lift (fst _ _) (snd _ _ ≫ e.inv)
  have hn : n ≫ g = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n, g₁, g₂]
  have hn' : g ≫ n = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n, g₁, reassoc_of% g₂]
  have hb' : a ≫ e.inv = e.inv ≫ b := by
    rw [Iso.comp_inv_eq, Category.assoc, hb, e.inv_hom_id_assoc]
  have gb : Over.mk p ◁ b ≫ g = g ≫ Over.mk p ◁ a := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [g₁, g₂, reassoc_of% g₂, hb]
  have gt : translT B (c ≫ e.inv) ≫ g = g ≫ translT A c := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [translT, g₁]
    · rw [Category.assoc, Category.assoc, g₂, translT, translT, lift_snd_assoc, lift_snd]
      show ((fst _ B ≫ c ≫ e.inv) * snd _ B) ≫ e.hom = g ≫ ((fst _ A ≫ c) * snd _ A)
      rw [MonObj.mul_comp, MonObj.comp_mul, g₂, reassoc_of% g₁]
      simp
  have tb : translT B (c ≫ e.inv) ≫ snd _ _ ≫ b = snd _ _ ≫ b := by
    rw [← cancel_mono e.hom]
    simp only [Category.assoc]
    rw [hb, ← reassoc_of% g₂, reassoc_of% gt, GlobalTheory.KernelEigen.translT_snd_comp a hc]
  obtain ⟨s, hs⟩ := ((GlobalTheory.FieldBaseChange.isoRelM_bijective (k := k) (m := (snd (Over.mk p) B).left)
    (g₁ := (snd (Over.mk p) A).left) (h₁ := g.left) hL₁ hL₂ hw (congrArg (fun q => q.left) g₂) n.left
    (congrArg (fun q => q.left) hn) (congrArg (fun q => q.left) hn')).2 σ₀).exists
  obtain ⟨ν, hν, vν⟩ := exists_gen hL₂ (K' := Fin 2) (φ' := ![𝟙 X, φ]) (ε' := ![((k * N : ℕ) : ℤ), -(k : ℤ)])
    (fun U _ h => by simp [Fin.prod_univ_two]) (GeneratorPullback.powGen L₂ _ _ mu k) (GlobalTheory.FrameGeo.powGen_isGen _ _ _ _ hmu k)
  obtain ⟨mA, hmA, vmA⟩ := exists_gen_move_back _ _ _ _ _ L₁ L₂ hL₁ hL₂ _ _ w hw (Fin 2)
    ![(snd (Over.mk p) A ≫ e.inv).left, (snd (Over.mk p) A ≫ a ≫ e.inv).left] _
    ![(snd (Over.mk p) A).left, (snd (Over.mk p) A ≫ a).left]
    (fun i => by
      fin_cases i
      · show (snd (Over.mk p) A).left = (snd (Over.mk p) A ≫ e.inv).left ≫ e.hom.left
        rw [← Over.comp_left, Category.assoc, e.inv_hom_id, Category.comp_id]
      · show (snd (Over.mk p) A ≫ a).left = (snd (Over.mk p) A ≫ a ≫ e.inv).left ≫ e.hom.left
        rw [← Over.comp_left, Category.assoc, Category.assoc, e.inv_hom_id, Category.comp_id])
    _ ((snd (Over.mk p) A ≫ e.inv).left ≫ f)
    (fun i => by
      fin_cases i
      · exact Category.comp_id _
      · show ((snd (Over.mk p) A ≫ e.inv).left ≫ f) ≫ φ = (snd (Over.mk p) A ≫ a ≫ e.inv).left ≫ f
        rw [Category.assoc, ← hφ, ← Category.assoc, ← Over.comp_left, Category.assoc, hb'])
    ν hν
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (Over.mk p ⊗ B).left) (z : Z) (J₂) (J₁), Good L₂ z J₂ → Good L₁ z J₁ →
      val mu (r ≫ (snd (Over.mk p) B).left ≫ f) z J₂ ^ k =
        isoVal w (r ≫ (snd (Over.mk p) B).left) z (J₂ ((r ≫ (snd (Over.mk p) B).left) ≫ f))
          (J₁ ((r ≫ (snd (Over.mk p) B).left) ≫ e.hom.left)) ^ ((k * N : ℕ) : ℤ) *
        (isoVal w (r ≫ (snd (Over.mk p) B ≫ b).left) z (J₂ ((r ≫ (snd (Over.mk p) B ≫ b).left) ≫ f))
          (J₁ ((r ≫ (snd (Over.mk p) B ≫ b).left) ≫ e.hom.left)) ^ (k : ℤ))⁻¹ * val mA (r ≫ g.left) z J₁ := by
    intro Z r z J₂ J₁ hJ₂ hJ₁
    have e₀ : (r ≫ g.left) ≫ (snd (Over.mk p) A ≫ e.inv).left = r ≫ (snd (Over.mk p) B).left := by
      rw [Category.assoc, ← Over.comp_left, reassoc_of% g₂, e.hom_inv_id, Category.comp_id]
    have e₁ : (r ≫ g.left) ≫ (snd (Over.mk p) A ≫ a ≫ e.inv).left = r ≫ (snd (Over.mk p) B ≫ b).left := by
      rw [Category.assoc, ← Over.comp_left, reassoc_of% g₂, hb', e.hom_inv_id_assoc]
    have := vmA Z (r ≫ g.left) z J₂ J₁ hJ₂ hJ₁
    rw [vν _ _ z J₂ hJ₂, GlobalTheory.FrameGeo.val_powGen, Fin.prod_univ_two, ← Category.assoc, e₀, Category.assoc] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e₀, e₁, zpow_neg] at this
    exact this
  have hσ := secRel_iff hL₂ _ _ σ' _ _ σ₀ (Over.mk p ◁ b).left _ _
    (LB.pullGen L₂ _ _ (GeneratorPullback.powGen L₂ _ _ mu k) ((snd (Over.mk p) B).left ≫ f))
  have h₀' := hσ.1 (hσ.2 fun y J hJ => by
    rw [h₀ y J hJ, val_pull hJ, GlobalTheory.FrameGeo.val_powGen, Category.id_comp, Category.id_comp,
      Units.val_pow_eq_pow_val])
  choose J₁ hJ₁ using fun χ : Z ⟶ A.left => exists_chart hL₁ (χ z)
  have E := GlobalTheory.translate_pullback_eigensection S A L₁ hL₁ K p a ha N k mA hmA s t' t (fun y I₁ hI₁ => by
    choose I₂ hI₂ using fun χ : (Over.mk p ⊗ A).left ⟶ X => exists_chart hL₂ (χ y)
    have ng : n.left ≫ g.left = 𝟙 _ := congrArg (fun q => q.left) hn
    have e₁ : (n.left ≫ (Over.mk p ◁ b).left) ≫ g.left = (Over.mk p ◁ a).left := by
      rw [← Over.comp_left, ← Over.comp_left, Category.assoc, gb, reassoc_of% hn]
    have e₂ : (n.left ≫ (Over.mk p ◁ b).left) ≫ (snd (Over.mk p) B).left =
        n.left ≫ (snd (Over.mk p) B ≫ b).left := by
      rw [Category.assoc, ← Over.comp_left, whiskerLeft_snd]
    have := h₀' _ n.left y I₂ hI₂
    rw [val_pull hI₂, GlobalTheory.FrameGeo.val_powGen, hv _ _ y I₂ I₁ hI₂ hI₁, sval_of_isoRelM h₁ _ y hI₂ hI₁,
      sval_of_isoRelM hs _ y hI₂ hI₁, ng, e₁, e₂] at this
    refine (Units.mul_right_inj _).1 (this.trans ?_)
    exact units_mul_pow_mul_inv_cancel _ _ _ _) θ hθ c u hc hW Z (ρ ≫ g.left) z J₁ hJ₁
  have e₁ : (ρ ≫ (translT B (c ≫ e.inv)).left) ≫ g.left = (ρ ≫ g.left) ≫ (translT A c).left := by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, gt]
  have e₂ : (ρ ≫ (translT B (c ≫ e.inv)).left) ≫ (snd (Over.mk p) B ≫ b).left =
      ρ ≫ (snd (Over.mk p) B ≫ b).left := by
    rw [Category.assoc, ← Over.comp_left, tb]
  have e₃ : (ρ ≫ g.left) ≫ (fst (Over.mk p) A).left = ρ ≫ (fst (Over.mk p) B).left := by
    rw [Category.assoc, ← Over.comp_left, g₁]
  rw [e₃] at E
  rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, hv _ _ z J J₁ hJ hJ₁, hv _ _ z J J₁ hJ hJ₁,
    sval_of_isoRelM h₂ _ z hJ hJ₁, sval_of_isoRelM h₂ _ z hJ hJ₁, e₁, e₂]
  simp only [Units.val_mul]
  exact ring_relation_transfer_identity E _ _ _

theorem eigen_equation_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (φ : G ⟶ G) (a : A.A ⟶ A.A), IsMonHom a → (Over.pullback (jK R)).map φ ≫ U.gen.hom = U.gen.hom ≫ a → ∀ (N k : ℕ) (mu : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 G.left, φ.left] ![(N : ℤ), -1])), mu.IsGen → ∀ (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))), w.IsGen → ∀ (σ₀ : U.SecGF F k) (σ' τ : U.SecGF F (k * N)) (t' t : LB.Sec (LPow A.A A.L ((k * N : ℕ) : ℤ) (TFK (R := R) F))), (∀ (y : (UnifPre.GF (G := G) F).left) (J), Good U.LG.L y J → sval σ' (𝟙 _) y J = sval σ₀ (TFK (R := R) F ◁ (Over.pullback (jK R)).map φ).left y J * (val mu (UnifPre.gFK (G := G) F) y J).val ^ k) → GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (k * N) (snd (TFK (R := R) F) A.A).left (U.genF F).left t' (UnifPre.gFK (G := G) F) (𝟙 _) σ' → GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (k * N) (snd (TFK (R := R) F) A.A).left (U.genF F).left t (UnifPre.gFK (G := G) F) (𝟙 _) τ → ∀ θ : ThetaGrp A.A A.L ((k * N : ℕ) : ℤ) (TFK (R := R) F), IsActOf A.A A.L ((k * N : ℕ) : ℤ) θ t' t → ∀ (z₀ : TFK (R := R) F ⟶ A.A) (ε : Fˣ), z₀ ≫ a = 1 → WeilIs A.A A.L ((k * N : ℕ) : ℤ) z₀ θ.pt (unitOn ε) → ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (UnifPre.GF (G := G) F).left) (z : Z) (J), Good U.LG.L z J → sval τ (ρ ≫ (translT ((Over.pullback (jK R)).obj G) (z₀ ≫ U.gen.inv)).left) z J * (val mu (ρ ≫ UnifPre.gFK (G := G) F) z J).val ^ k = constVal (ρ ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) z (ε : F) * (sval τ ρ z J * (val mu ((ρ ≫ (translT ((Over.pullback (jK R)).obj G) (z₀ ≫ U.gen.inv)).left) ≫ UnifPre.gFK (G := G) F) z J).val ^ k) := by
  intro R _ _ I D A G _ _ U F _ _ φ a ha hφ N k mu hmu w hw σ₀ σ' τ t' t h₀ h₁ h₂ θ hθ z₀ ε hz hW Z ρ z J hJ
  haveI := U.gen_hom
  exact eigen_transfer U.gen A.isLB U.LG.isLB (pullback.fst G.hom (jK R)) (jFK (R := R) F) φ.left
    ((Over.pullback (jK R)).map φ) (pullback.lift_fst _ _ _) a ha hφ N k mu hmu w hw σ₀ σ' τ t' t h₀ h₁ h₂ θ hθ
    z₀ (unitOn ε) hz hW Z ρ z J hJ

end GlobalTheory.Jets
