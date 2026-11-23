import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfSquareCechPicardTranslates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundlePullbackGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsDimAdditionGraphPrincipalPolarisation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfUnimodular
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.MumKeep

theorem spMap_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, ← Spec.map_comp]

theorem exists_fibre_point : ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] (Q : Data V) (ρ : V →+* V₁)
    (D : DegPre V₁) (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)),
    (∀ (T : Over (Sp V₁)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap ρ)).obj Q.B)), ∃! x : T ⟶ D.P.A, ∀ a, x ≫ pr a = y a) →
    ∀ (K : Type) [Field K] (ev : V₁ →+* K) (T : Over (Sp K)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap (ev.comp ρ))).obj Q.B)),
    ∃ x : T.left ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left, x ≫ pullback.snd D.P.A.hom (spMap ev) = T.hom ∧
      ∀ a, x ≫ pullback.fst D.P.A.hom (spMap ev) ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) =
        (y a).left ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) := by
  intro V V₁ _ _ _ _ Q ρ D pr hu K _ ev T y
  have cond : ∀ a, ((y a).left ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ))) ≫ Q.B.hom = (T.hom ≫ spMap ev) ≫ spMap ρ :=
    fun a => by
      have hw : (y a).left ≫ pullback.snd Q.B.hom (spMap (ev.comp ρ)) = T.hom := Over.w (y a)
      rw [Category.assoc, pullback.condition, ← Category.assoc, hw, spMap_comp', Category.assoc]
  let y' : Fin 8 → (Over.mk (T.hom ≫ spMap ev) ⟶ (Over.pullback (spMap ρ)).obj Q.B) := fun a =>
    Over.homMk (pullback.lift ((y a).left ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ))) (T.hom ≫ spMap ev) (cond a))
      (pullback.lift_snd _ _ _)
  obtain ⟨x', hx', -⟩ := hu _ y'
  refine ⟨pullback.lift x'.left T.hom (Over.w x'), pullback.lift_snd _ _ _, fun a => ?_⟩
  rw [pullback.lift_fst_assoc, ← Category.assoc, ← Over.comp_left, hx' a]
  exact pullback.lift_fst _ _ _

theorem lam_eq_zero_of_unimodular : ∀ {S : Scheme.{0}} [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (N : GlobalTheory.CechPic.Pic A.left) (W : Matrix (Fin 8) (Fin 8) ℤ), (W + W.transpose).det = 1 →
    (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∑ ab : Fin 8 × Fin 8, W ab.1 ab.2 • GlobalTheory.CechPic.lam N (y ab.1) (y ab.2) = 0) →
    GlobalTheory.CechPic.lam N (fst A A) (snd A A) = 0 := by
  intro S _ A _ _ hA N W hW h
  have hB1 : ∀ (T : Over S) (x x' y : T ⟶ A), GlobalTheory.CechPic.lam N (x * x') y =
      GlobalTheory.CechPic.lam N x y + GlobalTheory.CechPic.lam N x' y := fun T x x' y => GlobalTheory.SquareSym.lam_mul_left hA N x x' y
  have hB2 : ∀ (T : Over S) (x y : T ⟶ A), GlobalTheory.CechPic.lam N x y = GlobalTheory.CechPic.lam N y x :=
    fun T x y => GlobalTheory.CechPic.lam_comm N x y
  have hform : ∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), GlobalTheory.MatrixBundle.form (GlobalTheory.CechPic.lam N) W y y = 0 :=
    fun T y => h T y
  have hE : ∀ (T : Over S) (x y : Fin 8 → (T ⟶ A)),
      GlobalTheory.MatrixBundle.form (GlobalTheory.CechPic.lam N) (W + W.transpose) x y = 0 := by
    intro T x y
    have := GlobalTheory.MatrixBundle.form_mul_self (hB1 T) (hB2 T) W x y
    rw [hform, hform, hform, zero_add, zero_add] at this
    exact this.symm
  have key := GlobalTheory.MatrixBundle.form_single_right (hB1 _) (hB2 _) (W + W.transpose)
    (fun u => fst A A ^ ((W + W.transpose).adjugate 0 u)) 0 (snd A A)
  rw [hE] at key
  have hp : ∏ u, (fst A A ^ ((W + W.transpose).adjugate 0 u)) ^ ((W + W.transpose) u 0) = fst A A := by
    simp only [← zpow_mul]
    have zs : ∀ (s : Finset (Fin 8)) (e : Fin 8 → ℤ), ∏ u ∈ s, fst A A ^ e u = fst A A ^ ∑ u ∈ s, e u := by
      intro s e
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]
    rw [zs]
    have : ∑ u, (W + W.transpose).adjugate 0 u * (W + W.transpose) u 0 = 1 := by
      have e := congrFun (congrFun (Matrix.adjugate_mul (W + W.transpose)) 0) 0
      rw [Matrix.mul_apply, hW] at e
      simpa using e
    rw [this, zpow_one]
  rw [hp] at key
  exact key.symm

theorem sq_unique {S X : Scheme.{0}} {G : Over S} (ψ ψ' : X ⟶ (G ⊗ G).left)
    (h₁ : ψ ≫ (fst G G).left = ψ' ≫ (fst G G).left) (h₂ : ψ ≫ (snd G G).left = ψ' ≫ (snd G G).left) : ψ = ψ' := by
  let a : Over.mk (ψ ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk ψ rfl
  let a' : Over.mk (ψ ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk ψ' (by
    show ψ' ≫ (G ⊗ G).hom = ψ ≫ (G ⊗ G).hom
    rw [← Over.w (fst G G), ← Category.assoc, ← h₁, Category.assoc])
  have : a = a' := CartesianMonoidalCategory.hom_ext _ _
    (Over.OverMorphism.ext (by simpa [a, a'] using h₁)) (Over.OverMorphism.ext (by simpa [a, a'] using h₂))
  exact congrArg (fun z => z.left) this

theorem lbIso_lam_of_lam_sub : ∀ {S S' : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (hL : L.IsLB)
    (G₀ G₁ : Over S') [GrpObj G₀] [IsCommMonObj G₀] [GrpObj G₁] [IsCommMonObj G₁] (t₀ t₁ : S' ⟶ S)
    (p₀ : G₀.left ⟶ G.left) (p₁ : G₁.left ⟶ G.left), IsGrpPullback G₀ G t₀ p₀ → IsGrpPullback G₁ G t₁ p₁ →
    ∀ (f₁ : G₀.left ⟶ G₁.left), IsGrpPullback G₀ G₁ (𝟙 _) f₁ → ∀ (f₂ : (G2 G₀).left ⟶ (G2 G₁).left), IsSquare f₁ f₂ →
    ∀ (ψ₀ : (G2 G₀).left ⟶ (G2 G).left) (ψσ : (G2 G₁).left ⟶ (G2 G).left), IsSquare p₀ ψ₀ → IsSquare p₁ ψσ →
    GlobalTheory.CechPic.lam (GlobalTheory.CechPic.pull (f₁ ≫ p₁) (GlobalTheory.CechPic.cls L hL) - GlobalTheory.CechPic.pull p₀ (GlobalTheory.CechPic.cls L hL))
      (fst G₀ G₀) (snd G₀ G₀) = 0 →
    LBIso ((abelian₂ G L).pull ψ₀) ((abelian₂ G L).pull (f₂ ≫ ψσ)) := by
  intro S S' G _ _ L hL G₀ G₁ _ _ _ _ t₀ t₁ p₀ p₁ g₀ g₁ f₁ hf₁ f₂ hf₂ ψ₀ ψσ hψ₀ hψσ hN
  have hLam : (abelian₂ G L).IsLB := LB.isLB_linComb hL _ _
  have hid : LBIso (abelian₂ G L) ((abelian₂ G L).pull (𝟙 _)) :=
    (GlobalTheory.CechPic.cls_eq_iff hLam (pull_isLB hLam _)).1 (by rw [GlobalTheory.CechPic.cls_pull hLam, GlobalTheory.CechPic.pull_id])
  have refl : ∀ {X : Scheme.{0}} {A : LB X} (hA : A.IsLB), LBIso A A := fun hA => (GlobalTheory.CechPic.cls_eq_iff hA hA).1 rfl
  obtain ⟨β₀, hβ₀, H₀⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ t₀ G G₀ p₀ g₀
  obtain ⟨β₁, hβ₁, H₁⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ (𝟙 _ ≫ t₁) G G₀ (f₁ ≫ p₁) (hf₁.comp g₁)
  have i₀ := H₀ L (L.pull p₀) _ (abelian₂ G L) (𝟙 _) hL (pull_isLB hL _) hLam (refl (pull_isLB hL _)) hid
  have i₁ := H₁ L (L.pull (f₁ ≫ p₁)) _ (abelian₂ G L) (𝟙 _) hL (pull_isLB hL _) hLam (refl (pull_isLB hL _)) hid
  have e₀ : β₀ = ψ₀ := sq_unique _ _ (hβ₀.1.trans hψ₀.1.symm) (hβ₀.2.trans hψ₀.2.symm)
  have e₁ : β₁ = f₂ ≫ ψσ := sq_unique _ _ (hβ₁.1.trans (by rw [Category.assoc, hψσ.1, ← Category.assoc f₂, hf₂.1, Category.assoc]))
    (hβ₁.2.trans (by rw [Category.assoc, hψσ.2, ← Category.assoc f₂, hf₂.2, Category.assoc]))
  rw [Category.comp_id, e₀] at i₀
  rw [Category.comp_id, e₁] at i₁
  have hl₀ : (abelian₂ G₀ (L.pull p₀)).IsLB := LB.isLB_linComb (pull_isLB hL _) _ _
  have hl₁ : (abelian₂ G₀ (L.pull (f₁ ≫ p₁))).IsLB := LB.isLB_linComb (pull_isLB hL _) _ _
  have k₀ : GlobalTheory.CechPic.cls (abelian₂ G₀ (L.pull p₀)) hl₀ =
      GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls (L.pull p₀) (pull_isLB hL _)) (fst G₀ G₀) (snd G₀ G₀) :=
    GlobalTheory.CechPic.cls_cube_two _ _ _ _
  have k₁ : GlobalTheory.CechPic.cls (abelian₂ G₀ (L.pull (f₁ ≫ p₁))) hl₁ =
      GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls (L.pull (f₁ ≫ p₁)) (pull_isLB hL _)) (fst G₀ G₀) (snd G₀ G₀) :=
    GlobalTheory.CechPic.cls_cube_two _ _ _ _
  rw [GlobalTheory.CechPic.cls_pull hL] at k₀ k₁
  have hlam : GlobalTheory.CechPic.lam (GlobalTheory.CechPic.pull (f₁ ≫ p₁) (GlobalTheory.CechPic.cls L hL)) (fst G₀ G₀) (snd G₀ G₀) =
      GlobalTheory.CechPic.lam (GlobalTheory.CechPic.pull p₀ (GlobalTheory.CechPic.cls L hL)) (fst G₀ G₀) (snd G₀ G₀) := by
    have := GlobalTheory.AdditionGraph.lam_add (GlobalTheory.CechPic.pull (f₁ ≫ p₁) (GlobalTheory.CechPic.cls L hL) -
      GlobalTheory.CechPic.pull p₀ (GlobalTheory.CechPic.cls L hL)) (GlobalTheory.CechPic.pull p₀ (GlobalTheory.CechPic.cls L hL)) (fst G₀ G₀) (snd G₀ G₀)
    rw [sub_add_cancel, hN, zero_add] at this
    exact this
  refine (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hLam _) (pull_isLB hLam _)).1 ?_
  rw [(GlobalTheory.CechPic.cls_eq_iff (pull_isLB hLam _) hl₀).2 i₀.symm,
    (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hLam _) hl₁).2 i₁.symm, k₀, k₁, hlam]

theorem pushed_mul_one : ∀ {S₁ S₂ S X : Scheme.{0}} (G₁ : Over S₁) [GrpObj G₁] (G₂ : Over S₂) [GrpObj G₂] (G : Over S) [GrpObj G]
    (t₁ : S₁ ⟶ S) (t₂ : S₂ ⟶ S) (φ₁ : G₁.left ⟶ G.left) (φ₂ : G₂.left ⟶ G.left),
    IsGrpPullback G₁ G t₁ φ₁ → IsGrpPullback G₂ G t₂ φ₂ →
    ∀ (P₁ : Over S₁) (P₂ : Over S₂) (u v : P₁ ⟶ G₁) (u' v' : P₂ ⟶ G₂) (z₁ : X ⟶ P₁.left) (z₂ : X ⟶ P₂.left),
    z₁ ≫ P₁.hom ≫ t₁ = z₂ ≫ P₂.hom ≫ t₂ →
    z₁ ≫ u.left ≫ φ₁ = z₂ ≫ u'.left ≫ φ₂ → z₁ ≫ v.left ≫ φ₁ = z₂ ≫ v'.left ≫ φ₂ →
    z₁ ≫ (u * v).left ≫ φ₁ = z₂ ≫ (u' * v').left ≫ φ₂ ∧
      z₁ ≫ (1 : P₁ ⟶ G₁).left ≫ φ₁ = z₂ ≫ (1 : P₂ ⟶ G₂).left ≫ φ₂ := by
  intro S₁ S₂ S X G₁ _ G₂ _ G _ t₁ t₂ φ₁ φ₂ h₁ h₂ P₁ P₂ u v u' v' z₁ z₂ hb hu hv
  let j₁ : Over.mk (z₁ ≫ P₁.hom) ⟶ P₁ := Over.homMk z₁ rfl
  let j₂ : Over.mk (z₂ ≫ P₂.hom) ⟶ P₂ := Over.homMk z₂ rfl
  have hb' : (Over.mk (z₁ ≫ P₁.hom)).hom ≫ t₁ = (Over.mk (z₂ ≫ P₂.hom)).hom ≫ t₂ := by
    simpa only [Over.mk_hom, Category.assoc] using hb

  have m₁ : ∀ a b : P₁ ⟶ G₁, (pushPt h₁.1.w (j₁ ≫ a) * pushPt h₁.1.w (j₁ ≫ b)).left = z₁ ≫ (a * b).left ≫ φ₁ :=
    fun a b => by
      rw [h₁.2 _ (j₁ ≫ a) (j₁ ≫ b) _ _ rfl rfl, ← MonObj.comp_mul]
      simp [j₁]
  have m₂ : ∀ a b : P₂ ⟶ G₂, (pushPt h₂.1.w (j₂ ≫ a) * pushPt h₂.1.w (j₂ ≫ b)).left = z₂ ≫ (a * b).left ≫ φ₂ :=
    fun a b => by
      rw [h₂.2 _ (j₂ ≫ a) (j₂ ≫ b) _ _ rfl rfl, ← MonObj.comp_mul]
      simp [j₂]
  have l₁ : ∀ a : P₁ ⟶ G₁, (pushPt h₁.1.w (j₁ ≫ a)).left = z₁ ≫ a.left ≫ φ₁ := fun a => by
    simp [pushPt, j₁]
  have l₂ : ∀ a : P₂ ⟶ G₂, (pushPt h₂.1.w (j₂ ≫ a)).left = z₂ ≫ a.left ≫ φ₂ := fun a => by
    simp [pushPt, j₂]
  refine ⟨?_, ?_⟩
  · rw [← m₁, ← m₂]
    exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.mul_left_congr hb' _ _ _ _ ((l₁ u).trans (hu.trans (l₂ u').symm))
      ((l₁ v).trans (hv.trans (l₂ v').symm))
  ·
    have i₁ : pushPt h₁.1.w (j₁ ≫ (1 : P₁ ⟶ G₁)) = 1 := by
      have k : pushPt h₁.1.w (j₁ ≫ (1 : P₁ ⟶ G₁)) * pushPt h₁.1.w (j₁ ≫ (1 : P₁ ⟶ G₁)) =
          pushPt h₁.1.w (j₁ ≫ (1 : P₁ ⟶ G₁)) := Over.OverMorphism.ext (by rw [m₁, _root_.mul_one, l₁])
      exact mul_eq_left.mp k
    have i₂ : pushPt h₂.1.w (j₂ ≫ (1 : P₂ ⟶ G₂)) = 1 := by
      have k : pushPt h₂.1.w (j₂ ≫ (1 : P₂ ⟶ G₂)) * pushPt h₂.1.w (j₂ ≫ (1 : P₂ ⟶ G₂)) =
          pushPt h₂.1.w (j₂ ≫ (1 : P₂ ⟶ G₂)) := Over.OverMorphism.ext (by rw [m₂, _root_.mul_one, l₂])
      exact mul_eq_left.mp k
    have oc : ∀ {a b : X ⟶ S} (h : a = b), (1 : Over.mk a ⟶ G).left = (1 : Over.mk b ⟶ G).left := by
      intro a b h; subst h; rfl
    rw [← l₁, ← l₂, i₁, i₂]
    exact oc hb'

theorem fibre_iso_keeps_lam : ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] (Q : Data V) (ρ : V →+* V₁) (D : DegPre V₁), ∀ (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)) (w : LB.Iso D.P.L (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4) (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2)))), (∀ a, IsMonHom (pr a)) → (∀ (T : Over (Sp V₁)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap ρ)).obj Q.B)), ∃! x : T ⟶ D.P.A, ∀ a, x ≫ pr a = y a) → w.IsGen → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (σ : K ≃+* K), ∀ (f : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A).left), IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A) (𝟙 _) f → LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (D.P.L.pull (f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)))) → ∀ f₁ : ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B).left, IsGrpPullback ((Over.pullback (spMap (ev.comp ρ))).obj Q.B) ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B) (𝟙 _) f₁ → (∀ (a : Fin 8) (T : Scheme.{0}) (x : T ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left) (y : T ⟶ ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left), y ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) = x ≫ pullback.fst D.P.A.hom (spMap ev) ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) → y ≫ pullback.snd Q.B.hom (spMap (ev.comp ρ)) = x ≫ pullback.snd D.P.A.hom (spMap ev) → x ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) = y ≫ f₁ ≫ pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ)))) → ∀ (f₂ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B)).left), IsSquare f₁ f₂ → ∀ (ψ₀ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 Q.B).left) (ψσ : (G2 ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B)).left ⟶ (G2 Q.B).left), IsSquare (pullback.fst Q.B.hom (spMap (ev.comp ρ))) ψ₀ → IsSquare (pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ)))) ψσ → LBIso ((abelian₂ Q.B Q.M.L).pull ψ₀) ((abelian₂ Q.B Q.M.L).pull (f₂ ≫ ψσ)) := by
  intro W hW V V₁ _ _ _ _ Q ρ D pr w hpr hu hw K _ _ ev σ f hf hfL f₁ hf₁ hco f₂ hf₂ ψ₀ ψσ hψ₀ hψσ
  have gK := isGrpPullback_pullback Q.B (spMap (ev.comp ρ))
  have gσ := isGrpPullback_pullback Q.B (spMap (σ.toRingHom.comp (ev.comp ρ)))
  have gρ := isGrpPullback_pullback Q.B (spMap ρ)
  have g₁ := hf₁.comp gσ
  refine lbIso_lam_of_lam_sub Q.B Q.M.L Q.M.isLB _ _ _ _ _ _ gK gσ f₁ hf₁ f₂ hf₂ ψ₀ ψσ hψ₀ hψσ ?_
  refine lam_eq_zero_of_unimodular _ (GlobalTheory.isAbelianScheme_pullback_obj _ _ Q.isAb) _ W hW.2 ?_
  intro T y
  obtain ⟨x, hx1, hx2⟩ := exists_fibre_point V V₁ Q ρ D pr hu K ev T y

  have hLC := LB.isLB_linComb Q.M.isLB
    (fun k : (Fin 8 × Fin 8) × Fin 4 => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ))
    (fun k => -(W k.1.1 k.1.2 * negε k.2))
  have A2 : ∀ {X : Scheme.{0}} (z : X ⟶ D.P.A.left), GlobalTheory.CechPic.pull z (GlobalTheory.CechPic.cls D.P.L D.P.isLB) =
      ∑ k : (Fin 8 × Fin 8) × Fin 4, (-(W k.1.1 k.1.2 * negε k.2)) •
        GlobalTheory.CechPic.pull (z ≫ lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ))
          (GlobalTheory.CechPic.cls Q.M.L Q.M.isLB) := by
    intro X z
    rw [(GlobalTheory.CechPic.cls_eq_iff D.P.isLB hLC).2 ⟨w, hw⟩, GlobalTheory.CechPic.cls_linComb Q.M.isLB, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, ← GlobalTheory.CechPic.pull_comp]
  have e0 : GlobalTheory.CechPic.pull (pullback.fst D.P.A.hom (spMap ev)) (GlobalTheory.CechPic.cls D.P.L D.P.isLB) =
      GlobalTheory.CechPic.pull (f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev))) (GlobalTheory.CechPic.cls D.P.L D.P.isLB) := by
    have := (GlobalTheory.CechPic.cls_eq_iff (pull_isLB D.P.isLB _) (pull_isLB D.P.isLB _)).2 hfL
    rwa [GlobalTheory.CechPic.cls_pull D.P.isLB, GlobalTheory.CechPic.cls_pull D.P.isLB] at this
  have e1 := congrArg (GlobalTheory.CechPic.pull x) e0
  rw [← GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.pull_comp, A2, A2] at e1
  have h0 : ∀ a b i, (x ≫ pullback.fst D.P.A.hom (spMap ev)) ≫ lamPts (pr a) (pr b) i ≫ pullback.fst Q.B.hom (spMap ρ) =
      lamPts (y a) (y b) i ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) := by
    intro a b i
    have base : (x ≫ pullback.fst D.P.A.hom (spMap ev)) ≫ D.P.A.hom ≫ spMap ρ = 𝟙 T.left ≫ T.hom ≫ spMap (ev.comp ρ) := by
      rw [Category.assoc, pullback.condition_assoc, ← Category.assoc x, hx1, spMap_comp', Category.id_comp]
    have hc : ∀ a, (x ≫ pullback.fst D.P.A.hom (spMap ev)) ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) =
        𝟙 T.left ≫ (y a).left ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) := fun a => by
      rw [Category.id_comp, Category.assoc]; exact hx2 a
    obtain ⟨hm, h1⟩ := pushed_mul_one _ _ Q.B _ _ _ _ gρ gK D.P.A T (pr a) (pr b) (y a) (y b) _ _ base (hc a) (hc b)
    fin_cases i
    · simpa [lamPts] using hm
    · simpa [lamPts] using hc a
    · simpa [lamPts] using hc b
    · simpa [lamPts] using h1
  have h1 : ∀ a b i, (x ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev))) ≫ lamPts (pr a) (pr b) i ≫
      pullback.fst Q.B.hom (spMap ρ) =
      lamPts (y a) (y b) i ≫ f₁ ≫ pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ))) := by
    intro a b i
    have hfw : f ≫ pullback.snd D.P.A.hom (spMap (σ.toRingHom.comp ev)) = pullback.snd D.P.A.hom (spMap ev) := by
      exact (hf.1.w).trans (Category.comp_id _)
    have base : (x ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev))) ≫ D.P.A.hom ≫ spMap ρ =
        𝟙 T.left ≫ T.hom ≫ 𝟙 _ ≫ spMap (σ.toRingHom.comp (ev.comp ρ)) := by
      rw [Category.assoc, Category.assoc, pullback.condition_assoc, ← Category.assoc f, hfw, ← Category.assoc x, hx1,
        Category.id_comp, Category.id_comp]
      simp only [spMap_comp', Category.assoc]
    have hc : ∀ a, (x ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev))) ≫ (pr a).left ≫
        pullback.fst Q.B.hom (spMap ρ) =
        𝟙 T.left ≫ (y a).left ≫ f₁ ≫ pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ))) := fun a => by
      have hyS : (y a).left ≫ pullback.snd Q.B.hom (spMap (ev.comp ρ)) = x ≫ pullback.snd D.P.A.hom (spMap ev) := by
        rw [hx1]; exact Over.w (y a)
      have := hco a T.left x (y a).left (hx2 a).symm hyS
      simpa only [Category.id_comp, Category.assoc] using this
    obtain ⟨hm, h1⟩ := pushed_mul_one _ _ Q.B _ _ _ _ gρ g₁ D.P.A T (pr a) (pr b) (y a) (y b) _ _ base (hc a) (hc b)
    fin_cases i
    · simpa [lamPts] using hm
    · simpa [lamPts] using hc a
    · simpa [lamPts] using hc b
    · simpa [lamPts] using h1
  simp_rw [h0, h1] at e1

  set c₀ : GlobalTheory.CechPic.Pic ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left :=
    GlobalTheory.CechPic.pull (pullback.fst Q.B.hom (spMap (ev.comp ρ))) (GlobalTheory.CechPic.cls Q.M.L Q.M.isLB) with hc₀
  set c₁ : GlobalTheory.CechPic.Pic ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left :=
    GlobalTheory.CechPic.pull (f₁ ≫ pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ)))) (GlobalTheory.CechPic.cls Q.M.L Q.M.isLB) with hc₁
  have L : ∀ a b, GlobalTheory.CechPic.lam (c₁ - c₀) (y a) (y b) =
      ∑ i : Fin 4, (-negε i) • (GlobalTheory.CechPic.pull (lamPts (y a) (y b) i ≫ f₁ ≫
        pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ)))) (GlobalTheory.CechPic.cls Q.M.L Q.M.isLB) -
        GlobalTheory.CechPic.pull (lamPts (y a) (y b) i ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)))
          (GlobalTheory.CechPic.cls Q.M.L Q.M.isLB)) := by
    intro a b
    simp only [hc₀, hc₁, GlobalTheory.CechPic.lam, Fin.sum_univ_four, negε, lamPts, map_sub, GlobalTheory.CechPic.pull_comp]
    simp
    abel
  have e2 : ∑ ab : Fin 8 × Fin 8, W ab.1 ab.2 • GlobalTheory.CechPic.lam (c₁ - c₀) (y ab.1) (y ab.2) =
      ∑ k : (Fin 8 × Fin 8) × Fin 4, (-(W k.1.1 k.1.2 * negε k.2)) • GlobalTheory.CechPic.pull (lamPts (y k.1.1) (y k.1.2) k.2 ≫
        f₁ ≫ pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ)))) (GlobalTheory.CechPic.cls Q.M.L Q.M.isLB) -
      ∑ k : (Fin 8 × Fin 8) × Fin 4, (-(W k.1.1 k.1.2 * negε k.2)) • GlobalTheory.CechPic.pull (lamPts (y k.1.1) (y k.1.2) k.2 ≫
        pullback.fst Q.B.hom (spMap (ev.comp ρ))) (GlobalTheory.CechPic.cls Q.M.L Q.M.isLB) := by
    rw [← Finset.sum_sub_distrib]
    conv_rhs => rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun ab _ => ?_
    rw [L, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, smul_sub, show W ab.1 ab.2 * -negε i = -(W ab.1 ab.2 * negε i) by ring]
  refine e2.trans ?_
  rw [← e1, sub_self]

end GlobalTheory.Poinc.Sep.MumKeep
