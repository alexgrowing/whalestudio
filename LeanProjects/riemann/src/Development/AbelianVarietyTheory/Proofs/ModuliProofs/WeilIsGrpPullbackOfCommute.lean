import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ThetaMove
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilPull

open GlobalTheory.CommPairing

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left} {k : ℤ}

theorem exists_psi_inv [IsIso τ] : ∃ χ : (T₀ ⊗ G).left ⟶ (T ⊗ A).left,
    (psiO hp τ hτ).left ≫ χ = 𝟙 (T ⊗ A).left ∧ χ ≫ (psiO hp τ hτ).left = 𝟙 _ := by
  have w₁ : (snd T₀ G).left ≫ G.hom = ((fst T₀ G).left ≫ inv τ ≫ T.hom) ≫ f := by
    rw [Over.w, Category.assoc, Category.assoc, ← hτ, IsIso.inv_hom_id_assoc, Over.w]
  let a : (T₀ ⊗ G).left ⟶ A.left := hp.1.lift _ _ w₁
  have a₁ : a ≫ φ = (snd T₀ G).left := hp.1.lift_fst _ _ _
  have a₂ : a ≫ A.hom = (fst T₀ G).left ≫ inv τ ≫ T.hom := hp.1.lift_snd _ _ _
  let χ : (T₀ ⊗ G).left ⟶ (T ⊗ A).left :=
    pullback.lift ((fst T₀ G).left ≫ inv τ) a (by rw [a₂, Category.assoc])
  have c₁ : χ ≫ (fst T A).left = (fst T₀ G).left ≫ inv τ := pullback.lift_fst _ _ _
  have c₂ : χ ≫ (snd T A).left = a := pullback.lift_snd _ _ _
  have p₁ := psi_fst hp τ hτ
  have p₂ := psi_snd hp τ hτ
  refine ⟨χ, ?_, ?_⟩
  · refine pullback.hom_ext (f := T.hom) (g := A.hom) ?_ ?_
    · show (_ ≫ χ) ≫ (fst T A).left = 𝟙 _ ≫ (fst T A).left
      rw [Category.assoc, c₁, ← Category.assoc, p₁, Category.assoc, IsIso.hom_inv_id, Category.id_comp,
        Category.comp_id]
    · show (_ ≫ χ) ≫ (snd T A).left = 𝟙 _ ≫ (snd T A).left
      rw [Category.assoc, c₂, Category.id_comp]
      refine hp.1.hom_ext ?_ ?_
      · rw [Category.assoc, a₁, p₂]
      · rw [Category.assoc, a₂, ← Category.assoc, p₁, Category.assoc, IsIso.hom_inv_id_assoc, Over.w, Over.w]
  · refine pullback.hom_ext (f := T₀.hom) (g := G.hom) ?_ ?_
    · show (χ ≫ _) ≫ (fst T₀ G).left = 𝟙 _ ≫ (fst T₀ G).left
      rw [Category.assoc, p₁, ← Category.assoc, c₁, Category.assoc, IsIso.inv_hom_id, Category.id_comp,
        Category.comp_id]
    · show (χ ≫ _) ≫ (snd T₀ G).left = 𝟙 _ ≫ (snd T₀ G).left
      rw [Category.assoc, p₂, ← Category.assoc, c₂, a₁, Category.id_comp]

def Rel (w : LB.Iso L₁ (L₀.pull φ)) (θ : ThetaGrp A L₁ k T) (θ₀ : ThetaGrp G L₀ k T₀) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J₀) (J), Good L₀ z J₀ → Good L₁ z J →
    tval θ₀ (r ≫ (psiO hp τ hτ).left) z J₀ =
      (gw w (r ≫ (snd T A).left) z (J₀ ((r ≫ (snd T A).left) ≫ φ)) (J (r ≫ (snd T A).left)) ^ k *
        gw w (r ≫ (translPt A θ.pt).left) z (J₀ ((r ≫ (translPt A θ.pt).left) ≫ φ))
          (J (r ≫ (translPt A θ.pt).left)) ^ (-k)) * tval θ r z J

theorem exists_rel_down (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) (hw : w.IsGen)
    (x : T ⟶ A) (θ₀ : ThetaGrp G L₀ k T₀) (hx : τ ≫ θ₀.pt.left = x.left ≫ φ) :
    ∃ θ : ThetaGrp A L₁ k T, θ.pt = x ∧ Rel hp τ hτ w θ θ₀ := by
  obtain ⟨θ, rfl, m⟩ := exists_theta_move hp τ hτ hL₀ hL₁ w hw k x θ₀ hx
  refine ⟨θ, rfl, fun Z r z J₀ J hG hJ => ?_⟩
  have e₀ : (r ≫ (psiO hp τ hτ).left) ≫ (snd T₀ G).left = (r ≫ (snd T A).left) ≫ φ := by
    rw [Category.assoc, Category.assoc, psi_snd]
  have e₁ : (r ≫ (psiO hp τ hτ).left) ≫ (translPt G θ₀.pt).left = (r ≫ (translPt A θ.pt).left) ≫ φ := by
    rw [Category.assoc, Category.assoc, psi_tr hp τ hτ _ _ hx]
  have e : ∀ i, (r ≫ (psiO hp τ hτ).left) ≫ ![(snd T₀ G).left, (translPt G θ₀.pt).left] i =
      (r ≫ ![(snd T A).left, (translPt A θ.pt).left] i) ≫ φ := fun i => by
    fin_cases i
    · exact e₀
    · exact e₁
  calc tval θ₀ (r ≫ (psiO hp τ hτ).left) z J₀ = _ :=
        m _ r z _ (fun i => J (r ≫ ![(snd T A).left, (translPt A θ.pt).left] i)) (fun i => by
          show _ ∈ L₀.U (J₀ ((r ≫ (psiO hp τ hτ).left) ≫ _))
          rw [e i]; exact hG _) (fun i => hJ _)
    _ = _ := by
      congr 1
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [e₀, e₁]

theorem exists_rel_up [IsIso τ] (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) (hw : w.IsGen)
    (x₀ : T₀ ⟶ G) (θ : ThetaGrp A L₁ k T) (hx : τ ≫ x₀.left = θ.pt.left ≫ φ) :
    ∃ θ₀ : ThetaGrp G L₀ k T₀, θ₀.pt = x₀ ∧ Rel hp τ hτ w θ θ₀ := by
  obtain ⟨χ, h₁, h₂⟩ := exists_psi_inv hp τ hτ
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff w).1 hw) hL₀ hL₁
    (φ' := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ θ.isGen
  have e₀ : χ ≫ (snd T A).left ≫ φ = (snd T₀ G).left := by
    rw [← psi_snd hp τ hτ, ← Category.assoc, h₂, Category.id_comp]
  have e₁ : χ ≫ (translPt A θ.pt).left ≫ φ = (translPt G x₀).left := by
    rw [← psi_tr hp τ hτ _ _ hx, ← Category.assoc, h₂, Category.id_comp]
  obtain ⟨u, hu, hu'⟩ := exists_gen hL₀ (φ' := ![(snd T₀ G).left, (translPt G x₀).left]) (ε' := ![k, -k])
    (fun U _ g => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => g q ^ k) e₀
      · exact congrArg (fun q => g q ^ (-k)) e₁)
    (LB.pullGen L₀ _ _ t χ) (DVR.pullGen_isGen _ _ _ _ ht _)
  refine ⟨⟨x₀, u, hu⟩, rfl, fun Z r z J₀ J hG hJ => ?_⟩
  have e : (r ≫ (psiO hp τ hτ).left) ≫ χ = r := by
    rw [Category.assoc]; exact (congrArg (r ≫ ·) h₁).trans (Category.comp_id _)
  refine ((hu' Z _ z J₀ hG).trans ((val_pull hG _ _ _).trans (congrArg (fun q => val t q z J₀) e))).trans ?_
  refine (hv Z r z _ _ (hG.mem _ r) (hJ.mem _ r)).trans ?_
  congr 1
  simp only [pw, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Category.assoc]

theorem transl_commute {x y : T ⟶ A} (h : x * y = y * x) :
    (translT A x).left ≫ (translPt A y).left = (translT A y).left ≫ (translPt A x).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  show translT A x ≫ ((fst T A ≫ y) * snd T A) = translT A y ≫ ((fst T A ≫ x) * snd T A)
  rw [MonObj.comp_mul, MonObj.comp_mul, translT, translT, lift_snd, lift_snd, ← Category.assoc, ← Category.assoc,
    lift_fst, lift_fst]
  show (fst T A ≫ y) * ((fst T A ≫ x) * snd T A) = (fst T A ≫ x) * ((fst T A ≫ y) * snd T A)
  rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← MonObj.comp_mul, ← MonObj.comp_mul, h]

theorem cancel_iff {M : Type*} [CommGroup M] (P X Y Z a b c d C : M) :
    (P * X⁻¹ * a) * (X * Z⁻¹ * b) = (P * Y⁻¹ * c) * (Y * Z⁻¹ * d) * C ↔ a * b = c * d * C := by
  have e₁ : (P * X⁻¹ * a) * (X * Z⁻¹ * b) = (P * Z⁻¹) * (a * b) := by
    apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel
  have e₂ : (P * Y⁻¹ * c) * (Y * Z⁻¹ * d) * C = (P * Z⁻¹) * (c * d * C) := by
    apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel
  rw [e₁, e₂, mul_right_inj]

theorem commIsOf_iff_of_rel [IsIso τ] (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ))
    {θx θy : ThetaGrp A L₁ k T} {θx₀ θy₀ : ThetaGrp G L₀ k T₀} (hc : θx.pt * θy.pt = θy.pt * θx.pt)
    (hx : τ ≫ θx₀.pt.left = θx.pt.left ≫ φ) (hy : τ ≫ θy₀.pt.left = θy.pt.left ≫ φ)
    (mx : Rel hp τ hτ w θx θx₀) (my : Rel hp τ hτ w θy θy₀) (c₀ : Γ(T₀.left, ⊤)ˣ) (c : Γ(T.left, ⊤)ˣ)
    (hcc : ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z), gm (r ≫ τ) z ⊤ c₀ = gm r z ⊤ c) :
    CommIsOf A L₁ k θx θy c ↔ CommIsOf G L₀ k θx₀ θy₀ c₀ := by
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J₀) (J), Good L₀ z J₀ → Good L₁ z J →
      (tval θx₀ (r ≫ (psiO hp τ hτ).left) z J₀ *
          tval θy₀ ((r ≫ (psiO hp τ hτ).left) ≫ (translT G θx₀.pt).left) z J₀ =
        tval θy₀ (r ≫ (psiO hp τ hτ).left) z J₀ *
          tval θx₀ ((r ≫ (psiO hp τ hτ).left) ≫ (translT G θy₀.pt).left) z J₀ *
          gm ((r ≫ (psiO hp τ hτ).left) ≫ (fst T₀ G).left) z ⊤ c₀ ↔
      tval θx r z J * tval θy (r ≫ (translT A θx.pt).left) z J =
        tval θy r z J * tval θx (r ≫ (translT A θy.pt).left) z J * gm (r ≫ (fst T A).left) z ⊤ c) := by
    intro Z r z J₀ J hG hJ
    have t : ∀ (x : T ⟶ A) (x₀ : T₀ ⟶ G), τ ≫ x₀.left = x.left ≫ φ →
        (r ≫ (psiO hp τ hτ).left) ≫ (translT G x₀).left = (r ≫ (translT A x).left) ≫ (psiO hp τ hτ).left :=
      fun x x₀ h => by rw [Category.assoc, Category.assoc, psi_transl hp τ hτ _ _ h]
    have g : gm ((r ≫ (psiO hp τ hτ).left) ≫ (fst T₀ G).left) z ⊤ c₀ = gm (r ≫ (fst T A).left) z ⊤ c := by
      rw [Category.assoc, psi_fst, ← Category.assoc, hcc]
    have s : ∀ x : T ⟶ A, (r ≫ (translT A x).left) ≫ (snd T A).left = r ≫ (translPt A x).left := fun x => by
      rw [Category.assoc, ← Over.comp_left, translT, lift_snd]
    have q : (r ≫ (translT A θx.pt).left) ≫ (translPt A θy.pt).left =
        (r ≫ (translT A θy.pt).left) ≫ (translPt A θx.pt).left := by
      rw [Category.assoc, Category.assoc, transl_commute hc]
    rw [t _ _ hx, t _ _ hy, g, mx Z _ z J₀ J hG hJ, mx Z _ z J₀ J hG hJ, my Z _ z J₀ J hG hJ, my Z _ z J₀ J hG hJ,
      s, s, q]
    simp only [zpow_neg]
    exact cancel_iff _ _ _ _ _ _ _ _ _
  rw [commIsOf_iff hL₀, commIsOf_iff hL₁]
  constructor
  · intro H Z r₀ z J₀ hG
    obtain ⟨χ, -, h₂⟩ := exists_psi_inv hp τ hτ
    choose J hJ using fun ψ : Z ⟶ A.left => exists_chart hL₁ (ψ z)
    have e : (r₀ ≫ χ) ≫ (psiO hp τ hτ).left = r₀ := by rw [Category.assoc, h₂, Category.comp_id]
    have := (key Z (r₀ ≫ χ) z J₀ J hG hJ).2 (H Z _ z J hJ)
    rwa [e] at this
  · intro H Z r z J hJ
    choose J₀ hG using fun ψ : Z ⟶ G.left => exists_chart hL₀ (ψ z)
    exact (key Z r z J₀ J hG hJ).1 (H Z _ z J₀ hG)

end GlobalTheory.WeilPull

namespace GlobalTheory

open WeilPull

theorem weilIs_grpPullback_of_commute : ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G']
    (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB →
    IsGrpPullback G' G f φ → LBIso L' (L.pull φ) → ∀ (T : Over S') (k : ℤ) (x y : T ⟶ G')
    (x₀ y₀ : Over.mk (T.hom ≫ f) ⟶ G) (c : Γ(T.left, ⊤)ˣ), x * y = y * x → x₀.left = x.left ≫ φ →
    y₀.left = y.left ≫ φ → (Out.WeilIs G' L' k x y c ↔ Out.WeilIs G L k x₀ y₀ c) := by
  intro S S' G G' _ _ f φ L L' hL hL' hp ⟨w, hw⟩ T k x y x₀ y₀ c hc ex ey
  refine forall_congr' fun p => exists_congr fun V => and_congr_right fun _ => ?_
  let V₀ : (Over.mk (T.hom ≫ f)).left.Opens := V
  let τ : (overRes V).left ⟶ (overRes V₀).left := 𝟙 V.toScheme
  haveI : IsIso τ := inferInstanceAs (IsIso (𝟙 V.toScheme))
  have hτ : τ ≫ (overRes V₀).hom = (overRes V).hom ≫ f := (Category.id_comp _).trans (Category.assoc _ _ _).symm
  have mv : ∀ {a : T ⟶ G'} {a₀ : Over.mk (T.hom ≫ f) ⟶ G}, a₀.left = a.left ≫ φ →
      τ ≫ (overResι V₀ ≫ a₀).left = (overResι V ≫ a).left ≫ φ := fun {a a₀} e =>
    (Category.id_comp _).trans ((congrArg (V.ι ≫ ·) e).trans (Category.assoc _ _ _).symm)
  have cm : ∀ {θx θy : ThetaGrp G' L' k (overRes V)} {θx₀ θy₀ : ThetaGrp G L k (overRes V₀)},
      θx.pt = overResι V ≫ x → θy.pt = overResι V ≫ y → θx₀.pt = overResι V₀ ≫ x₀ → θy₀.pt = overResι V₀ ≫ y₀ →
      Rel hp τ hτ w θx θx₀ → Rel hp τ hτ w θy θy₀ →
      (CommIsOf G' L' k θx θy (unitRes V c) ↔ CommIsOf G L k θx₀ θy₀ (unitRes V₀ c)) :=
    fun h₁ h₂ h₃ h₄ mx my => commIsOf_iff_of_rel hp τ hτ hL hL' w
      (by rw [h₁, h₂, ← MonObj.comp_mul, ← MonObj.comp_mul, hc]) (by rw [h₁, h₃]; exact mv ex)
      (by rw [h₂, h₄]; exact mv ey) mx my _ _ (fun Z r z => congrArg (fun q => gm q z ⊤ (unitRes V c))
        (Category.comp_id r))
  have up : ∀ {a : T ⟶ G'} {a₀ : Over.mk (T.hom ≫ f) ⟶ G}, a₀.left = a.left ≫ φ →
      ∀ θ : ThetaGrp G' L' k (overRes V), θ.pt = overResι V ≫ a →
        ∃ θ₀ : ThetaGrp G L k (overRes V₀), θ₀.pt = overResι V₀ ≫ a₀ ∧ Rel hp τ hτ w θ θ₀ :=
    fun e θ h => exists_rel_up hp τ hτ hL hL' w hw _ θ (by rw [h]; exact mv e)
  have down : ∀ {a : T ⟶ G'} {a₀ : Over.mk (T.hom ≫ f) ⟶ G}, a₀.left = a.left ≫ φ →
      ∀ θ₀ : ThetaGrp G L k (overRes V₀), θ₀.pt = overResι V₀ ≫ a₀ →
        ∃ θ : ThetaGrp G' L' k (overRes V), θ.pt = overResι V ≫ a ∧ Rel hp τ hτ w θ θ₀ :=
    fun e θ₀ h => exists_rel_down hp τ hτ hL hL' w hw _ θ₀ (by rw [h]; exact mv e)
  constructor
  · rintro ⟨⟨θx, θy, h₁, h₂⟩, H⟩
    obtain ⟨a, ha, -⟩ := up ex θx h₁
    obtain ⟨b, hb, -⟩ := up ey θy h₂
    refine ⟨⟨a, b, ha, hb⟩, fun a b ha hb => ?_⟩
    obtain ⟨a', ha', mx⟩ := down ex a ha
    obtain ⟨b', hb', my⟩ := down ey b hb
    exact (cm ha' hb' ha hb mx my).1 (H a' b' ha' hb')
  · rintro ⟨⟨θx, θy, h₁, h₂⟩, H⟩
    obtain ⟨a, ha, -⟩ := down ex θx h₁
    obtain ⟨b, hb, -⟩ := down ey θy h₂
    refine ⟨⟨a, b, ha, hb⟩, fun a b ha hb => ?_⟩
    obtain ⟨a', ha', mx⟩ := up ex a ha
    obtain ⟨b', hb', my⟩ := up ey b hb
    exact (cm ha hb ha' hb' mx my).2 (H a' b' ha' hb')

theorem weilIs_grpPullback_of_comm' : ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G']
    [IsCommMonObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB →
    IsGrpPullback G' G f φ → LBIso L' (L.pull φ) → ∀ (T : Over S') (k : ℤ) (x y : T ⟶ G')
    (x₀ y₀ : Over.mk (T.hom ≫ f) ⟶ G) (c : Γ(T.left, ⊤)ˣ), x₀.left = x.left ≫ φ →
    y₀.left = y.left ≫ φ → (Out.WeilIs G' L' k x y c ↔ Out.WeilIs G L k x₀ y₀ c) :=
  fun S S' G G' _ _ _ f φ L L' hL hL' hp hw T k x y x₀ y₀ c ex ey =>
    weilIs_grpPullback_of_commute S S' G G' f φ L L' hL hL' hp hw T k x y x₀ y₀ c (mul_comm x y) ex ey

theorem weilIs_grpPullback_of_comm : ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G']
    [IsCommMonObj G] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB →
    IsGrpPullback G' G f φ → LBIso L' (L.pull φ) → ∀ (T : Over S') (k : ℤ) (x y : T ⟶ G')
    (x₀ y₀ : Over.mk (T.hom ≫ f) ⟶ G) (c : Γ(T.left, ⊤)ˣ), x₀.left = x.left ≫ φ →
    y₀.left = y.left ≫ φ → (Out.WeilIs G' L' k x y c ↔ Out.WeilIs G L k x₀ y₀ c) := by
  intro S S' G G' _ _ _ f φ L L' hL hL' hp hw T k x y x₀ y₀ c ex ey
  refine weilIs_grpPullback_of_commute S S' G G' f φ L L' hL hL' hp hw T k x y x₀ y₀ c ?_ ex ey
  apply Over.OverMorphism.ext
  apply hp.1.hom_ext
  · rw [← hp.2 T x y x₀ y₀ ex ey, ← hp.2 T y x y₀ x₀ ey ex, mul_comm x₀ y₀]
  · rw [Over.w, Over.w]

end GlobalTheory
