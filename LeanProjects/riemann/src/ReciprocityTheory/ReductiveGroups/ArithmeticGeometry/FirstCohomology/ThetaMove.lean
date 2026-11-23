import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Move

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)

def psiO : Over.mk ((T ⊗ A).hom ≫ f) ⟶ T₀ ⊗ G :=
  lift (Over.homMk ((fst T A).left ≫ τ) (by
      show ((fst T A).left ≫ τ) ≫ T₀.hom = (T ⊗ A).hom ≫ f
      rw [Category.assoc, hτ, ← Category.assoc, Over.w (fst T A)]))
    (pushPt hp.1.w (snd T A))

theorem psi_fst : (psiO hp τ hτ).left ≫ (fst T₀ G).left = (fst T A).left ≫ τ := by
  rw [← Over.comp_left, psiO, lift_fst]; rfl

theorem psi_snd : (psiO hp τ hτ).left ≫ (snd T₀ G).left = (snd T A).left ≫ φ := by
  rw [← Over.comp_left, psiO, lift_snd]; rfl

theorem psi_tr (x : T ⟶ A) (x₀ : T₀ ⟶ G) (hx : τ ≫ x₀.left = x.left ≫ φ) :
    (psiO hp τ hτ).left ≫ (translPt G x₀).left = (translPt A x).left ≫ φ := by
  have e₁ : translPt G x₀ = (fst T₀ G ≫ x₀) * snd T₀ G := rfl
  have e₂ : translPt A x = (fst T A ≫ x) * snd T A := rfl
  rw [← Over.comp_left, e₁, MonObj.comp_mul, e₂]
  refine hp.2 _ _ _ _ _ ?_ ?_
  · rw [Over.comp_left, Over.comp_left, ← Category.assoc, psi_fst, Category.assoc, hx, Over.comp_left, Category.assoc]
  · rw [Over.comp_left, psi_snd]

theorem psi_transl (x : T ⟶ A) (x₀ : T₀ ⟶ G) (hx : τ ≫ x₀.left = x.left ≫ φ) :
    (translT A x).left ≫ (psiO hp τ hτ).left = (psiO hp τ hτ).left ≫ (translT G x₀).left := by
  let m : Over.mk ((T ⊗ A).hom ≫ f) ⟶ Over.mk ((T ⊗ A).hom ≫ f) :=
    Over.homMk (translT A x).left (by
      show (translT A x).left ≫ (T ⊗ A).hom ≫ f = (T ⊗ A).hom ≫ f
      rw [← Category.assoc, Over.w (translT A x)])
  have key : m ≫ psiO hp τ hτ = psiO hp τ hτ ≫ translT G x₀ := by
    apply CartesianMonoidalCategory.hom_ext
    · apply Over.OverMorphism.ext
      have e1 : (m ≫ psiO hp τ hτ ≫ fst T₀ G).left = (fst T A).left ≫ τ := by
        rw [psiO, lift_fst]
        show (translT A x).left ≫ (fst T A).left ≫ τ = _
        rw [← Category.assoc, ← Over.comp_left, translT, lift_fst]
      have e2 : (psiO hp τ hτ ≫ translT G x₀ ≫ fst T₀ G).left = (fst T A).left ≫ τ := by
        rw [translT, lift_fst, Over.comp_left, psi_fst]
      simpa only [Category.assoc] using e1.trans e2.symm
    · apply Over.OverMorphism.ext
      have e1 : (m ≫ psiO hp τ hτ ≫ snd T₀ G).left = (translPt A x).left ≫ φ := by
        rw [psiO, lift_snd]
        show (translT A x).left ≫ (snd T A).left ≫ φ = _
        rw [← Category.assoc, ← Over.comp_left, translT, lift_snd]
      have e2 : (psiO hp τ hτ ≫ translT G x₀ ≫ snd T₀ G).left = (translPt A x).left ≫ φ := by
        rw [translT, lift_snd, Over.comp_left, psi_tr hp τ hτ x x₀ hx]
      simpa only [Category.assoc] using e1.trans e2.symm
  exact congrArg CommaMorphism.left key

variable {L₀ : LB G.left} {L₁ : LB A.left}

theorem exists_theta_move (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) (hw : w.IsGen) (k : ℤ)
    (x : T ⟶ A) (θ₀ : ThetaGrp G L₀ k T₀) (hx : τ ≫ θ₀.pt.left = x.left ≫ φ) :
    ∃ θ : ThetaGrp A L₁ k T, θ.pt = x ∧
      PMaps w ![(snd T A).left, (translPt A θ.pt).left] ![(snd T₀ G).left, (translPt G θ₀.pt).left] ![k, -k]
        θ.φ θ₀.φ (psiO hp τ hτ).left := by
  obtain ⟨a, ha, hm⟩ := exists_gen_move hL₀ hL₁ w ((isGen_iff w).1 hw)
    ![(snd T₀ G).left, (translPt G θ₀.pt).left] ![(snd T A).left, (translPt A x).left] ![k, -k]
    (psiO hp τ hτ).left (fun i => by
      fin_cases i
      · exact (psi_snd hp τ hτ).symm
      · exact (psi_tr hp τ hτ x θ₀.pt hx).symm) θ₀.φ θ₀.isGen
  exact ⟨⟨x, a, ha⟩, rfl, hm⟩

end Move

theorem cancel_cg {M : Type*} [CommGroup M] (P X Y Z a b c d C : M)
    (h : (P * X⁻¹ * a) * (X * Z⁻¹ * b) = (P * Y⁻¹ * c) * (Y * Z⁻¹ * d) * C) : a * b = c * d * C := by
  have e₁ : a * b = (P * X⁻¹ * a) * (X * Z⁻¹ * b) * (P * Z⁻¹)⁻¹ := by
    apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel
  have e₂ : (P * Y⁻¹ * c) * (Y * Z⁻¹ * d) * C * (P * Z⁻¹)⁻¹ = c * d * C := by
    apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel
  rw [e₁, h, e₂]

theorem val_constGen {S : Scheme.{0}} {A : Over S} [GrpObj A] (L : LB A.left) {T : Over S} (c : Γ(T.left, ⊤)ˣ)
    {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι) :
    val (constGen A L c) r z J = gm (r ≫ (fst T A).left) z ⊤ c := by
  show gm r z _ (res le_top (pullU (fst T A).left ⊤ c)) = _
  exact (gm_res r z _ (Set.mem_iInter.2 fun k => k.elim) _).trans (gm_pull r _ z ⊤ trivial c)

section Comm

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A] [IsCommMonObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left}

theorem transl_snd (x : T ⟶ A) : (translT A x).left ≫ (snd T A).left = (translPt A x).left := by
  rw [← Over.comp_left, translT, lift_snd]

theorem transl_comm (x y : T ⟶ A) :
    (translT A x).left ≫ (translPt A y).left = (translT A y).left ≫ (translPt A x).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  show translT A x ≫ ((fst T A ≫ y) * snd T A) = translT A y ≫ ((fst T A ≫ x) * snd T A)
  rw [MonObj.comp_mul, MonObj.comp_mul, translT, translT, lift_snd, lift_snd, ← Category.assoc, ← Category.assoc,
    lift_fst, lift_fst]
  exact mul_left_comm _ _ _

theorem commIsOf_move (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) (k : ℤ)
    (θx₀ θy₀ : ThetaGrp G L₀ k T₀) (θx θy : ThetaGrp A L₁ k T)
    (hx : τ ≫ θx₀.pt.left = θx.pt.left ≫ φ) (hy : τ ≫ θy₀.pt.left = θy.pt.left ≫ φ)
    (mx : PMaps w ![(snd T A).left, (translPt A θx.pt).left] ![(snd T₀ G).left, (translPt G θx₀.pt).left] ![k, -k]
      θx.φ θx₀.φ (psiO hp τ hτ).left)
    (my : PMaps w ![(snd T A).left, (translPt A θy.pt).left] ![(snd T₀ G).left, (translPt G θy₀.pt).left] ![k, -k]
      θy.φ θy₀.φ (psiO hp τ hτ).left)
    (c₀ : Γ(T₀.left, ⊤)ˣ) (c : Γ(T.left, ⊤)ˣ)
    (hc : ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z), gm (r ≫ τ) z ⊤ c₀ = gm r z ⊤ c)
    (H : CommIsOf G L₀ k θx₀ θy₀ c₀) : CommIsOf A L₁ k θx θy c := by
  refine corr_of_val hL₁ fun y J hJ => ?_
  choose J₀ hJ₀ using fun χ : (T ⊗ A).left ⟶ G.left => exists_chart hL₀ (χ y)
  have hG : Good L₀ y J₀ := hJ₀
  let W : ((T ⊗ A).left ⟶ A.left) → ((T ⊗ A).left.presheaf.stalk y)ˣ := fun ψ => gw w ψ y (J₀ (ψ ≫ φ)) (J ψ)
  have rel : ∀ (θ₀ : ThetaGrp G L₀ k T₀) (θ : ThetaGrp A L₁ k T), τ ≫ θ₀.pt.left = θ.pt.left ≫ φ →
      PMaps w ![(snd T A).left, (translPt A θ.pt).left] ![(snd T₀ G).left, (translPt G θ₀.pt).left] ![k, -k]
        θ.φ θ₀.φ (psiO hp τ hτ).left →
      ∀ r : (T ⊗ A).left ⟶ (T ⊗ A).left, val θ₀.φ (r ≫ (psiO hp τ hτ).left) y J₀ =
        (W (r ≫ (snd T A).left) ^ k * W (r ≫ (translPt A θ.pt).left) ^ (-k)) * val θ.φ r y J := by
    intro θ₀ θ hθ m r
    have e₀ : (r ≫ (psiO hp τ hτ).left) ≫ (snd T₀ G).left = (r ≫ (snd T A).left) ≫ φ := by
      rw [Category.assoc, Category.assoc, psi_snd]
    have e₁ : (r ≫ (psiO hp τ hτ).left) ≫ (translPt G θ₀.pt).left = (r ≫ (translPt A θ.pt).left) ≫ φ := by
      rw [Category.assoc, Category.assoc, psi_tr hp τ hτ _ _ hθ]
    have e : ∀ i, (r ≫ (psiO hp τ hτ).left) ≫ ![(snd T₀ G).left, (translPt G θ₀.pt).left] i =
        (r ≫ ![(snd T A).left, (translPt A θ.pt).left] i) ≫ φ := fun i => by
      fin_cases i
      · exact e₀
      · exact e₁
    calc val θ₀.φ (r ≫ (psiO hp τ hτ).left) y J₀ = _ :=
          m _ r y _ (fun i => J (r ≫ ![(snd T A).left, (translPt A θ.pt).left] i)) (fun i => by
            show _ ∈ L₀.U (J₀ ((r ≫ (psiO hp τ hτ).left) ≫ _))
            rw [e i]; exact hG _) (fun i => hJ _)
      _ = _ := by
        congr 1
        simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [e₀, e₁]
  have a₁ := rel θx₀ θx hx mx (𝟙 _)
  have a₂ := rel θy₀ θy hy my (translT A θx.pt).left
  have a₃ := rel θy₀ θy hy my (𝟙 _)
  have a₄ := rel θx₀ θx hx mx (translT A θy.pt).left
  rw [Category.id_comp, Category.id_comp, Category.id_comp] at a₁ a₃
  rw [transl_snd] at a₂ a₄
  have hL : val (Z := (T ⊗ A).left) θx₀.φ (psiO hp τ hτ).left y J₀ *
        val θy₀.φ ((translT A θx.pt).left ≫ (psiO hp τ hτ).left) y J₀ =
      val (Z := (T ⊗ A).left) θy₀.φ (psiO hp τ hτ).left y J₀ *
        val θx₀.φ ((translT A θy.pt).left ≫ (psiO hp τ hτ).left) y J₀ *
        val (Z := (T ⊗ A).left) (constGen G L₀ c₀) (psiO hp τ hτ).left y J₀ := by
    have h0 := val_corr hG H (psiO hp τ hτ).left
    rw [psi_transl hp τ hτ _ _ hx, psi_transl hp τ hτ _ _ hy]
    exact ((val_mul hG _ _ _).trans (congrArg (val (Z := (T ⊗ A).left) θx₀.φ (psiO hp τ hτ).left y J₀ * ·) (val_pull hG _ _ _))).symm.trans
      (h0.trans ((val_mul hG _ _ _).trans (congrArg (· * _) ((val_mul hG _ _ _).trans
        (congrArg (val (Z := (T ⊗ A).left) θy₀.φ (psiO hp τ hτ).left y J₀ * ·) (val_pull hG _ _ _))))))
  have hcst : val (Z := (T ⊗ A).left) (constGen G L₀ c₀) (psiO hp τ hτ).left y J₀ = val (constGen A L₁ c) (𝟙 _) y J := by
    rw [val_constGen, val_constGen, psi_fst, hc, Category.id_comp]
  rw [a₁, a₂, a₃, a₄, transl_comm θx.pt θy.pt, hcst] at hL
  simp only [zpow_neg] at hL
  refine ((val_mul hJ _ _ _).trans (congrArg (val θx.φ (𝟙 _) y J * ·) (val_pull hJ _ _ _))).trans
    (Eq.trans ?_ ((val_mul hJ _ _ _).trans (congrArg (· * _) ((val_mul hJ _ _ _).trans
      (congrArg (val θy.φ (𝟙 _) y J * ·) (val_pull hJ _ _ _))))).symm)
  rw [Category.id_comp, Category.id_comp]
  exact cancel_cg _ _ _ _ _ _ _ _ _ hL

end Comm

theorem commIsOf_unique {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {k : ℤ} {T : Over S}
    (θx θy : ThetaGrp A L k T) (c c' : Γ(T.left, ⊤)ˣ) (h : CommIsOf A L k θx θy c) (h' : CommIsOf A L k θx θy c') :
    c = c' := by
  let s : T.left ⟶ (T ⊗ A).left := (lift (𝟙 T) (toUnit T ≫ η[A])).left
  have hs : s ≫ (fst T A).left = 𝟙 _ := by rw [← Over.comp_left, lift_fst, Over.id_left]
  refine unit_ext fun z _ => ?_
  choose J hJ using fun χ : T.left ⟶ A.left => exists_chart hL (χ z)
  have hJ' : Good L z J := hJ
  have e := (val_mul hJ' _ _ s).symm.trans ((val_corr hJ' h s).symm.trans ((val_corr hJ' h' s).trans (val_mul hJ' _ _ s)))
  have e' := mul_left_cancel e
  rw [val_constGen, val_constGen, hs] at e'
  exact e'

end ReciprocityTheory.ChartRestriction.G.H1
