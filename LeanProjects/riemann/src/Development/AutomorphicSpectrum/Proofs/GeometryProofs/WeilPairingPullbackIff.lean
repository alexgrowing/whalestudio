import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ThetaMove

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.WeilPull

theorem cg_cancel {M : Type*} [CommGroup M] (P Q A : M) : Q⁻¹ * P * (Q * A) = P * A := by
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel

theorem cg_move {M : Type*} [CommGroup M] (P X Y Z a b c d C : M) (h : a * b = c * d * C) :
    (P * X⁻¹ * a) * (X * Z⁻¹ * b) = (P * Y⁻¹ * c) * (Y * Z⁻¹ * d) * C := by
  have e₁ : (P * X⁻¹ * a) * (X * Z⁻¹ * b) = (P * Z⁻¹) * (a * b) := by
    apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel
  have e₂ : (P * Y⁻¹ * c) * (Y * Z⁻¹ * d) * C = (P * Z⁻¹) * (c * d * C) := by
    apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel
  rw [e₁, e₂, h]

section Gen

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

theorem exists_gen_back₀ (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (hw : PGen w)
    {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (φ' : K → (Y ⟶ X')) (ε : K → ℤ)
    (hc : ∀ k, φ' k ≫ F = φ k) (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen ∧ PMaps w φ' φ ε a t (𝟙 Y) := by
  classical
  let O : (K → L.ι) → (K → L'.ι) → Y.Opens := fun p q => LB.wchart L φ p ⊓ LB.wchart L' φ' q
  have pF : ∀ k (y : Y), F (φ' k y) = φ k y := fun k y => by
    rw [← hc k]; rfl
  have memF : ∀ (p : K → L.ι) (y : Y), y ∈ LB.wchart L φ p → ∀ k, F (φ' k y) ∈ L.U (p k) := fun p y hy k => by
    rw [pF]; exact Set.mem_iInter.1 hy k
  have le1 : ∀ p q k, O p q ≤ φ' k ⁻¹ᵁ ((L.pull F).U (fun _ => p k) ⊓ L'.U (q k)) := fun p q k y hy =>
    ⟨mem_pull.2 (memF p y hy.1 k), Set.mem_iInter.1 hy.2 k⟩
  let v : ∀ p q, Γ(Y, O p q)ˣ := fun p q =>
    (∏ k, res (le1 p q k) (pullU (φ' k) _ (w.s (fun _ => p k, q k))) ^ ε k) * res inf_le_right (a.s q)
  have germ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) p q, r z ∈ O p q →
      gm r z (O p q) (v p q) =
        (∏ k, gw w (r ≫ φ' k) z (p k) (q k) ^ ε k) * gm r z (LB.wchart L' φ' q) (a.s q) := by
    intro Z r z p q hz
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => ?_))
      (gm_res r z (inf_le_right : O p q ≤ _) hz _))
    have m := le1 p q k hz
    exact (map_zpow _ _ _).trans (congrArg (· ^ ε k) ((gm_res r z (le1 p q k) hz _).trans (gm_pull r (φ' k) z _ m _)))
  have memO : ∀ p (y : Y), y ∈ LB.wchart L φ p → ∃ q, y ∈ O p q := fun p y hy => by
    choose q hq using fun k => exists_chart hL' (φ' k y)
    exact ⟨q, hy, Set.mem_iInter.2 hq⟩
  have glue : ∀ p, ∃ s : Γ(Y, LB.wchart L φ p)ˣ, ∀ q, res (inf_le_left : O p q ≤ _) s = v p q := by
    intro p
    refine glue_unit _ (O p) (fun q => inf_le_left) (fun y hy => ?_) (v p) fun q q' y hy => ?_
    · obtain ⟨q, hq⟩ := memO p y hy
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨q, hq⟩
    · rw [germ _ _ y p q hy.1, germ _ _ y p q' hy.2]
      have hp : ∀ k, F (φ' k y) ∈ L.U (p k) := memF p y hy.1.1
      have hq : ∀ k, φ' k y ∈ L'.U (q k) := fun k => Set.mem_iInter.1 hy.1.2 k
      have hq' : ∀ k, φ' k y ∈ L'.U (q' k) := fun k => Set.mem_iInter.1 hy.2.2 k
      have e3 : ∀ k, gw w (𝟙 Y ≫ φ' k) y (p k) (q k) =
          (gm (𝟙 Y ≫ φ' k) y _ (L'.g (q k) (q' k)))⁻¹ * gw w (𝟙 Y ≫ φ' k) y (p k) (q' k) := fun k => by
        rw [Category.id_comp, hw _ (φ' k) y (p k) (p k) (q k) (q' k) (hp k) (hp k) (hq k) (hq' k),
          gm_self hL _ y (hp k), _root_.one_mul]
      rw [gen_trans ha (𝟙 Y) y hy.1.2 hy.2.2]
      simp only [trF, e3, mul_zpow, inv_zpow, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
      exact cg_cancel _ _ _
  choose s hs using glue
  have vals : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) p q, r z ∈ O p q →
      gm r z (LB.wchart L φ p) (s p) =
        (∏ k, gw w (r ≫ φ' k) z (p k) (q k) ^ ε k) * gm r z (LB.wchart L' φ' q) (a.s q) := by
    intro Z r z p q hz
    rw [← gm_res r z (inf_le_left : O p q ≤ _) hz, hs p q, germ Z r z p q hz]
  refine ⟨⟨s⟩, fun p p' => unit_ext fun y hy => ?_, fun Z r z p q hp hq => ?_⟩
  · have hp := memF p y hy.1
    have hp' := memF p' y hy.2
    choose q hq using fun k => exists_chart hL' (φ' k y)
    have m : y ∈ O p q := ⟨hy.1, Set.mem_iInter.2 hq⟩
    have m' : y ∈ O p' q := ⟨hy.2, Set.mem_iInter.2 hq⟩
    rw [gm_res _ y _ hy, map_mul, gm_res _ y _ hy]
    show gm (𝟙 Y) y (LB.wchart L φ p) (s p) = gm (𝟙 Y) y (LB.wchart L φ p ⊓ LB.wchart L φ p')
      ((LB.LinComb L φ ε).g p p') * gm (𝟙 Y) y (LB.wchart L φ p') (s p')
    rw [gm_linComb L φ ε (𝟙 Y) y p p' hy.1 hy.2, vals _ _ y p q m, vals _ _ y p' q m']
    have e1 : ∀ k, gw w (𝟙 Y ≫ φ' k) y (p k) (q k) =
        gm (𝟙 Y ≫ φ k) y _ (L.g (p k) (p' k)) * gw w (𝟙 Y ≫ φ' k) y (p' k) (q k) := fun k => by
      rw [Category.id_comp, Category.id_comp, hw _ (φ' k) y (p k) (p' k) (q k) (q k) (hp k) (hp' k) (hq k) (hq k),
        gm_self hL' _ y (hq k), inv_one, _root_.mul_one, hc]
    simp only [e1, mul_zpow, Finset.prod_mul_distrib]
    exact mul_assoc _ _ _
  · have m : r z ∈ O p q := ⟨Set.mem_iInter.2 fun k => by
      have := hp k
      rw [pF] at this
      exact this, Set.mem_iInter.2 hq⟩
    show gm (r ≫ 𝟙 Y) z _ (s p) = _ * gm r z _ (a.s q)
    rw [Category.comp_id]
    exact vals Z r z p q m

theorem exists_gen_back (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (hw : PGen w)
    {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (φ' : K → (Y' ⟶ X')) (ε : K → ℤ) (h : Y' ⟶ Y) (ρ : Y ⟶ Y')
    (hρ : h ≫ ρ = 𝟙 Y') (hc : ∀ k, ρ ≫ φ' k ≫ F = φ k) (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen ∧ PMaps w φ' φ ε a t h := by
  obtain ⟨t, ht, m⟩ := exists_gen_back₀ hL hL' w hw φ (fun k => ρ ≫ φ' k) ε
    (fun k => by rw [Category.assoc]; exact hc k) (LB.pullGen L' φ' ε a ρ) (pullGen_isGen _ _ _ _ ha _)
  refine ⟨t, ht, fun Z r z p q hp hq => ?_⟩
  have e₀ : (r ≫ h) ≫ ρ = r := by rw [Category.assoc, hρ, Category.comp_id]
  have e₂ : ∀ k, (r ≫ h) ≫ ρ ≫ φ' k = r ≫ φ' k := fun k => by rw [← Category.assoc, e₀]
  have eρ : ρ ((r ≫ h) z) = r z := by
    show ((r ≫ h) ≫ ρ) z = r z
    rw [e₀]
  have pe : ∀ k, (ρ ≫ φ' k) ((r ≫ h) z) = φ' k (r z) := fun k => by
    show φ' k (ρ ((r ≫ h) z)) = _
    rw [eρ]
  have e := m Z (r ≫ h) z p q (fun k => by
    show F ((ρ ≫ φ' k) ((r ≫ h) z)) ∈ L.U (p k)
    rw [pe]; exact hp k) (fun k => by
    show (ρ ≫ φ' k) ((r ≫ h) z) ∈ L'.U (q k)
    rw [pe]; exact hq k)
  rw [Category.comp_id] at e
  refine e.trans ?_
  simp only [e₂]
  congr 1
  have hm : (r ≫ h) z ∈ ρ ⁻¹ᵁ LB.wchart L' φ' q := by
    show ρ ((r ≫ h) z) ∈ LB.wchart L' φ' q
    rw [eρ]; exact Set.mem_iInter.2 hq
  refine (gm_res (r ≫ h) z _ (Set.mem_iInter.2 fun k => by
      show (ρ ≫ φ' k) ((r ≫ h) z) ∈ L'.U (q k)
      rw [pe]; exact hq k) _).trans
    ((gm_pull (r ≫ h) ρ z _ hm _).trans ?_)
  rw [e₀]
  rfl

end Gen

section Move

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)

omit [GrpObj G] [GrpObj A] in

theorem left_ext {B C : Over S} {Z : Scheme.{0}} {u v : Z ⟶ (B ⊗ C).left}
    (h₁ : u ≫ (fst B C).left = v ≫ (fst B C).left) (h₂ : u ≫ (snd B C).left = v ≫ (snd B C).left) : u = v := by
  have hw : v ≫ (B ⊗ C).hom = u ≫ (B ⊗ C).hom := by
    rw [← Over.w (fst B C), ← Category.assoc, ← Category.assoc, h₁]
  let u' : Over.mk (u ≫ (B ⊗ C).hom) ⟶ B ⊗ C := Over.homMk u rfl
  let v' : Over.mk (u ≫ (B ⊗ C).hom) ⟶ B ⊗ C := Over.homMk v hw
  have e : u' = v' := CartesianMonoidalCategory.hom_ext _ _ (Over.OverMorphism.ext h₁) (Over.OverMorphism.ext h₂)
  exact congrArg CommaMorphism.left e

theorem exists_psi_inv (σ : T₀.left ⟶ T.left) (h₁ : σ ≫ τ = 𝟙 _) (h₂ : τ ≫ σ = 𝟙 _) :
    ∃ ρ : (T₀ ⊗ G).left ⟶ (T ⊗ A).left, ρ ≫ (psiO hp τ hτ).left = 𝟙 _ ∧ (psiO hp τ hτ).left ≫ ρ = 𝟙 _ := by
  have hl : (snd T₀ G).left ≫ G.hom = ((fst T₀ G).left ≫ σ ≫ T.hom) ≫ f := by
    rw [Over.w (snd T₀ G), Category.assoc, Category.assoc, ← hτ, ← Category.assoc σ, h₁, Category.id_comp,
      Over.w (fst T₀ G)]
  let a : (T₀ ⊗ G).left ⟶ A.left := hp.1.lift _ _ hl
  have ha₁ : a ≫ φ = (snd T₀ G).left := hp.1.lift_fst _ _ hl
  have ha₂ : a ≫ A.hom = (fst T₀ G).left ≫ σ ≫ T.hom := hp.1.lift_snd _ _ hl
  let U : Over S' := Over.mk ((fst T₀ G).left ≫ σ ≫ T.hom)
  let p₁ : U ⟶ T := Over.homMk ((fst T₀ G).left ≫ σ) (by simp [U])
  let p₂ : U ⟶ A := Over.homMk a ha₂
  let ρ : (T₀ ⊗ G).left ⟶ (T ⊗ A).left := (lift p₁ p₂).left
  have ρ₁ : ρ ≫ (fst T A).left = (fst T₀ G).left ≫ σ := by
    rw [← Over.comp_left, lift_fst]; rfl
  have ρ₂ : ρ ≫ (snd T A).left = a := by
    rw [← Over.comp_left, lift_snd]; rfl
  refine ⟨ρ, left_ext ?_ ?_, left_ext ?_ ?_⟩
  · rw [Category.assoc, psi_fst, ← Category.assoc, ρ₁, Category.assoc, h₁, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, psi_snd, ← Category.assoc, ρ₂, ha₁, Category.id_comp]
  · rw [Category.assoc, ρ₁, ← Category.assoc, psi_fst, Category.assoc, h₂, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, ρ₂, Category.id_comp]
    apply hp.1.hom_ext
    · rw [Category.assoc, ha₁, psi_snd]
    · rw [Category.assoc, ha₂, ← Category.assoc, psi_fst, Category.assoc, ← Category.assoc τ, h₂, Category.id_comp,
        Over.w (fst T A), Over.w (snd T A)]

variable {L₀ : LB G.left} {L₁ : LB A.left}

theorem exists_theta_back (σ : T₀.left ⟶ T.left) (h₁ : σ ≫ τ = 𝟙 _) (h₂ : τ ≫ σ = 𝟙 _)
    (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) (hw : w.IsGen) (k : ℤ)
    (x₀ : T₀ ⟶ G) (θ : ThetaGrp A L₁ k T) (hx : τ ≫ x₀.left = θ.pt.left ≫ φ) :
    ∃ θ₀ : ThetaGrp G L₀ k T₀, θ₀.pt = x₀ ∧
      PMaps w ![(snd T A).left, (translPt A θ.pt).left] ![(snd T₀ G).left, (translPt G θ₀.pt).left] ![k, -k]
        θ.φ θ₀.φ (psiO hp τ hτ).left := by
  obtain ⟨ρ, e₁, e₂⟩ := exists_psi_inv hp τ hτ σ h₁ h₂
  obtain ⟨t, ht, hm⟩ := exists_gen_back hL₀ hL₁ w ((isGen_iff w).1 hw)
    ![(snd T₀ G).left, (translPt G x₀).left] ![(snd T A).left, (translPt A θ.pt).left] ![k, -k]
    (psiO hp τ hτ).left ρ e₂ (fun i => by
      fin_cases i
      · show ρ ≫ (snd T A).left ≫ φ = (snd T₀ G).left
        rw [← psi_snd hp τ hτ, ← Category.assoc, e₁, Category.id_comp]
      · show ρ ≫ (translPt A θ.pt).left ≫ φ = (translPt G x₀).left
        rw [← psi_tr hp τ hτ θ.pt x₀ hx, ← Category.assoc, e₁, Category.id_comp]) θ.φ θ.isGen
  exact ⟨⟨x₀, t, ht⟩, rfl, hm⟩

end Move

section Comm

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A] [IsCommMonObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left}

theorem commIsOf_back (ρ : (T₀ ⊗ G).left ⟶ (T ⊗ A).left) (hρ : ρ ≫ (psiO hp τ hτ).left = 𝟙 _)
    (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) (k : ℤ)
    (θx₀ θy₀ : ThetaGrp G L₀ k T₀) (θx θy : ThetaGrp A L₁ k T)
    (hx : τ ≫ θx₀.pt.left = θx.pt.left ≫ φ) (hy : τ ≫ θy₀.pt.left = θy.pt.left ≫ φ)
    (mx : PMaps w ![(snd T A).left, (translPt A θx.pt).left] ![(snd T₀ G).left, (translPt G θx₀.pt).left] ![k, -k]
      θx.φ θx₀.φ (psiO hp τ hτ).left)
    (my : PMaps w ![(snd T A).left, (translPt A θy.pt).left] ![(snd T₀ G).left, (translPt G θy₀.pt).left] ![k, -k]
      θy.φ θy₀.φ (psiO hp τ hτ).left)
    (c₀ : Γ(T₀.left, ⊤)ˣ) (c : Γ(T.left, ⊤)ˣ)
    (hc : ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z), gm (r ≫ τ) z ⊤ c₀ = gm r z ⊤ c)
    (H : CommIsOf A L₁ k θx θy c) : CommIsOf G L₀ k θx₀ θy₀ c₀ := by
  refine corr_of_val hL₀ fun y J₀ hJ₀ => ?_
  choose J hJ using fun χ : (T₀ ⊗ G).left ⟶ A.left => exists_chart hL₁ (χ y)
  have hA : Good L₁ y J := hJ
  let W : ((T₀ ⊗ G).left ⟶ A.left) → ((T₀ ⊗ G).left.presheaf.stalk y)ˣ := fun ψ => gw w ψ y (J₀ (ψ ≫ φ)) (J ψ)
  have rel : ∀ (θ₀ : ThetaGrp G L₀ k T₀) (θ : ThetaGrp A L₁ k T), τ ≫ θ₀.pt.left = θ.pt.left ≫ φ →
      PMaps w ![(snd T A).left, (translPt A θ.pt).left] ![(snd T₀ G).left, (translPt G θ₀.pt).left] ![k, -k]
        θ.φ θ₀.φ (psiO hp τ hτ).left →
      ∀ r : (T₀ ⊗ G).left ⟶ (T ⊗ A).left, val θ₀.φ (r ≫ (psiO hp τ hτ).left) y J₀ =
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
            rw [e i]; exact hJ₀ _) (fun i => hJ _)
      _ = _ := by
        congr 1
        simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [e₀, e₁]
  have t₁ : (ρ ≫ (translT A θx.pt).left) ≫ (psiO hp τ hτ).left = (translT G θx₀.pt).left := by
    rw [Category.assoc, psi_transl hp τ hτ _ _ hx, ← Category.assoc, hρ, Category.id_comp]
  have t₂ : (ρ ≫ (translT A θy.pt).left) ≫ (psiO hp τ hτ).left = (translT G θy₀.pt).left := by
    rw [Category.assoc, psi_transl hp τ hτ _ _ hy, ← Category.assoc, hρ, Category.id_comp]
  have a₁ := rel θx₀ θx hx mx ρ
  have a₂ := rel θy₀ θy hy my (ρ ≫ (translT A θx.pt).left)
  have a₃ := rel θy₀ θy hy my ρ
  have a₄ := rel θx₀ θx hx mx (ρ ≫ (translT A θy.pt).left)
  rw [hρ] at a₁ a₃
  rw [t₁, Category.assoc, Category.assoc, transl_snd] at a₂
  rw [t₂, Category.assoc, Category.assoc, transl_snd] at a₄
  have hE : val (Z := (T₀ ⊗ G).left) θx.φ ρ y J * val θy.φ (ρ ≫ (translT A θx.pt).left) y J =
      val (Z := (T₀ ⊗ G).left) θy.φ ρ y J * val θx.φ (ρ ≫ (translT A θy.pt).left) y J *
        val (Z := (T₀ ⊗ G).left) (constGen A L₁ c) ρ y J := by
    have h0 := val_corr hA H ρ
    exact ((val_mul hA _ _ _).trans (congrArg (val (Z := (T₀ ⊗ G).left) θx.φ ρ y J * ·) (val_pull hA _ _ _))).symm.trans
      (h0.trans ((val_mul hA _ _ _).trans (congrArg (· * _) ((val_mul hA _ _ _).trans
        (congrArg (val (Z := (T₀ ⊗ G).left) θy.φ ρ y J * ·) (val_pull hA _ _ _))))))
  have hcst : val (constGen G L₀ c₀) (𝟙 _) y J₀ = val (Z := (T₀ ⊗ G).left) (constGen A L₁ c) ρ y J := by
    rw [val_constGen, val_constGen, Category.id_comp, ← hc, Category.assoc, ← psi_fst hp τ hτ, ← Category.assoc, hρ,
      Category.id_comp]
  refine ((val_mul hJ₀ _ _ _).trans (congrArg (val θx₀.φ (𝟙 _) y J₀ * ·) (val_pull hJ₀ _ _ _))).trans
    (Eq.trans ?_ ((val_mul hJ₀ _ _ _).trans (congrArg (· * _) ((val_mul hJ₀ _ _ _).trans
      (congrArg (val θy₀.φ (𝟙 _) y J₀ * ·) (val_pull hJ₀ _ _ _))))).symm)
  rw [Category.id_comp, Category.id_comp, a₁, a₂, a₃, a₄, transl_comm θx.pt θy.pt, hcst]
  simp only [zpow_neg]
  exact cg_move _ _ _ _ _ _ _ _ _ hE

theorem comm_clause_iff (hp : IsGrpPullback A G f φ) (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
    (σ : T₀.left ⟶ T.left) (h₁ : σ ≫ τ = 𝟙 _) (h₂ : τ ≫ σ = 𝟙 _)
    (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) (hw : w.IsGen) (k : ℤ)
    (x y : T ⟶ A) (x₀ y₀ : T₀ ⟶ G) (hx : τ ≫ x₀.left = x.left ≫ φ) (hy : τ ≫ y₀.left = y.left ≫ φ)
    (c₀ : Γ(T₀.left, ⊤)ˣ) (c : Γ(T.left, ⊤)ˣ)
    (hc : ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z), gm (r ≫ τ) z ⊤ c₀ = gm r z ⊤ c) :
    ((∃ θx θy : ThetaGrp A L₁ k T, θx.pt = x ∧ θy.pt = y) ∧
      ∀ θx θy : ThetaGrp A L₁ k T, θx.pt = x → θy.pt = y → CommIsOf A L₁ k θx θy c) ↔
    ((∃ θx θy : ThetaGrp G L₀ k T₀, θx.pt = x₀ ∧ θy.pt = y₀) ∧
      ∀ θx θy : ThetaGrp G L₀ k T₀, θx.pt = x₀ → θy.pt = y₀ → CommIsOf G L₀ k θx θy c₀) := by
  constructor
  · rintro ⟨⟨θx, θy, e₁, e₂⟩, hall⟩
    obtain ⟨ρ, r₁, -⟩ := exists_psi_inv hp τ hτ σ h₁ h₂
    obtain ⟨θx₀, f₁, -⟩ := exists_theta_back hp τ hτ σ h₁ h₂ hL₀ hL₁ w hw k x₀ θx (by rw [e₁]; exact hx)
    obtain ⟨θy₀, f₂, -⟩ := exists_theta_back hp τ hτ σ h₁ h₂ hL₀ hL₁ w hw k y₀ θy (by rw [e₂]; exact hy)
    refine ⟨⟨θx₀, θy₀, f₁, f₂⟩, fun ξ ζ g₁ g₂ => ?_⟩
    obtain ⟨ξ', i₁, m₁⟩ := exists_theta_move hp τ hτ hL₀ hL₁ w hw k x ξ (by rw [g₁]; exact hx)
    obtain ⟨ζ', i₂, m₂⟩ := exists_theta_move hp τ hτ hL₀ hL₁ w hw k y ζ (by rw [g₂]; exact hy)
    exact commIsOf_back hp τ hτ ρ r₁ hL₀ hL₁ w k ξ ζ ξ' ζ' (by rw [i₁, g₁]; exact hx) (by rw [i₂, g₂]; exact hy)
      m₁ m₂ c₀ c hc (hall ξ' ζ' i₁ i₂)
  · rintro ⟨⟨θx₀, θy₀, e₁, e₂⟩, hall⟩
    obtain ⟨θx, f₁, -⟩ := exists_theta_move hp τ hτ hL₀ hL₁ w hw k x θx₀ (by rw [e₁]; exact hx)
    obtain ⟨θy, f₂, -⟩ := exists_theta_move hp τ hτ hL₀ hL₁ w hw k y θy₀ (by rw [e₂]; exact hy)
    refine ⟨⟨θx, θy, f₁, f₂⟩, fun ξ ζ g₁ g₂ => ?_⟩
    obtain ⟨ξ₀, i₁, m₁⟩ := exists_theta_back hp τ hτ σ h₁ h₂ hL₀ hL₁ w hw k x₀ ξ (by rw [g₁]; exact hx)
    obtain ⟨ζ₀, i₂, m₂⟩ := exists_theta_back hp τ hτ σ h₁ h₂ hL₀ hL₁ w hw k y₀ ζ (by rw [g₂]; exact hy)
    exact commIsOf_move hp τ hτ hL₀ hL₁ w k ξ₀ ζ₀ ξ ζ (by rw [i₁, g₁]; exact hx) (by rw [i₂, g₂]; exact hy)
      m₁ m₂ c₀ c hc (hall ξ₀ ζ₀ i₁ i₂)

theorem weilIs_iff_pull (hp : IsGrpPullback A G f φ) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ))
    (hw : w.IsGen) {X : Scheme.{0}} (g : X ⟶ S') (k : ℤ) (x y : Over.mk g ⟶ A) (x₀ y₀ : Over.mk (g ≫ f) ⟶ G)
    (hx : x.left ≫ φ = x₀.left) (hy : y.left ≫ φ = y₀.left) (c : Γ(X, ⊤)ˣ) :
    WeilIs A L₁ k x y c ↔ WeilIs G L₀ k x₀ y₀ c := by
  have mv : ∀ (V : X.Opens) (q : Over.mk g ⟶ A) (q₀ : Over.mk (g ≫ f) ⟶ G), q.left ≫ φ = q₀.left →
      𝟙 _ ≫ (overResι (T := Over.mk (g ≫ f)) V ≫ q₀).left = (overResι (T := Over.mk g) V ≫ q).left ≫ φ :=
    fun V q q₀ h => by
      rw [Category.id_comp, Over.comp_left, Over.comp_left, Category.assoc, h]; rfl
  have key := fun V : X.Opens => comm_clause_iff (T := overRes (T := Over.mk g) V)
    (T₀ := overRes (T := Over.mk (g ≫ f)) V) hp (𝟙 _)
    (by
      rw [Category.id_comp]
      show V.ι ≫ g ≫ f = (V.ι ≫ g) ≫ f
      rw [Category.assoc]) (𝟙 _) (Category.id_comp _) (Category.id_comp _) hL₀ hL₁ w hw k
    (overResι (T := Over.mk g) V ≫ x) (overResι (T := Over.mk g) V ≫ y)
    (overResι (T := Over.mk (g ≫ f)) V ≫ x₀) (overResι (T := Over.mk (g ≫ f)) V ≫ y₀)
    (mv V x x₀ hx) (mv V y y₀ hy) (unitRes (T := Over.mk (g ≫ f)) V c) (unitRes (T := Over.mk g) V c)
    (fun Z r z => by rw [Category.comp_id]; rfl)
  constructor
  · intro H p
    obtain ⟨V, hV, h⟩ := H p
    exact ⟨V, hV, (key V).1 h⟩
  · intro H p
    obtain ⟨V, hV, h⟩ := H p
    exact ⟨V, hV, (key V).2 h⟩

end Comm

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f) (k : Type) [Field k] (z : Sp k ⟶ S') (a' b' : Over.mk z ⟶ t'.G) (a b : Over.mk (z ≫ f) ⟶ t.G) (n : ℕ) (c : kˣ), a'.left ≫ m.φ = a.left → b'.left ≫ m.φ = b.left → (Out.WeilIs t'.G t'.PP.L n a' b' (unitOn c) ↔ Out.WeilIs t.G t.PP.L n a b (unitOn c)) := by
  intro E _ _ _ H S S' t t' f m k _ z a' b' a b n c ha hb
  obtain ⟨w, hw, -, -⟩ := m.lin
  exact weilIs_iff_pull m.cart t.PP.isLB t'.PP.isLB w hw z n a' b' a b ha hb (unitOn c)

end GlobalTheory.CompanionTheory.Ar.WeilPull
