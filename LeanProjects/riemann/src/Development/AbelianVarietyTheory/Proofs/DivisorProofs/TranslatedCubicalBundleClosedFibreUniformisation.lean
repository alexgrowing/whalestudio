import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveCubeBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreUniformisationDataIsEvenCubicalOnClosedFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.TranslateLevel
open GlobalTheory.UU

section Iso
variable {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {τ : X ⟶ X} {τ' : X' ⟶ X'}

theorem exists_translate (h : τ' ≫ F = F ≫ τ) (w₁ : LB.Iso L' (L.pull F)) (hw₁ : w₁.IsGen) :
    ∃ w : LB.Iso (L'.pull τ') ((L.pull τ).pull F), w.IsGen ∧
      ∀ (Y : Scheme.{0}) (r : Y ⟶ X') (y : Y) (j : L.ι) (k : L'.ι), τ (F (r y)) ∈ L.U j → τ' (r y) ∈ L'.U k →
        gw w r y (fun _ => j) (fun _ => k) = gw w₁ (r ≫ τ') y j k := by
  have e : ∀ x : X', F (τ' x) = τ (F x) := fun x => congrArg (fun g => g x) h
  have le : ∀ (j : L.ι) (k : L'.ι), ((L.pull τ).pull F).U (fun _ _ => j) ⊓ (L'.pull τ').U (fun _ => k) ≤
      τ' ⁻¹ᵁ ((L.pull F).U (fun _ => j) ⊓ L'.U k) := fun j k x hx =>
    ⟨mem_pull.2 (by rw [e]; exact mem_pull.1 (mem_pull.1 hx.1)), mem_pull.1 hx.2⟩
  let w : LB.Iso (L'.pull τ') ((L.pull τ).pull F) :=
    ⟨fun p => res (le (p.1 PUnit.unit PUnit.unit) (p.2 PUnit.unit))
      (pullU τ' _ (w₁.s (fun _ => p.1 PUnit.unit PUnit.unit, p.2 PUnit.unit)))⟩
  have key : ∀ (Y : Scheme.{0}) (r : Y ⟶ X') (y : Y) (j : L.ι) (k : L'.ι), τ (F (r y)) ∈ L.U j → τ' (r y) ∈ L'.U k →
      gw w r y (fun _ => j) (fun _ => k) = gw w₁ (r ≫ τ') y j k := fun Y r y j k hj hk => by
    have hm : r y ∈ ((L.pull τ).pull F).U (fun _ _ => j) ⊓ (L'.pull τ').U (fun _ => k) :=
      ⟨mem_pull.2 (mem_pull.2 hj), mem_pull.2 hk⟩
    exact (gm_res r y (le j k) hm _).trans (gm_pull r τ' y _ (@le j k (r y) hm) _)
  refine ⟨w, (isGen_iff w).2 fun Y r y j j' k k' hj hj' hk hk' => ?_, key⟩
  have a := (isGen_iff w₁).1 hw₁ Y (r ≫ τ') y (j PUnit.unit) (j' PUnit.unit) (k PUnit.unit) (k' PUnit.unit)
    (by show F (τ' (r y)) ∈ _; rw [e]; exact mem_pull.1 hj) (by show F (τ' (r y)) ∈ _; rw [e]; exact mem_pull.1 hj')
    ((mem_pull (F := τ')).1 hk) ((mem_pull (F := τ')).1 hk')
  rw [Category.assoc, h, ← Category.assoc] at a
  refine (key Y r y _ _ (mem_pull.1 hj) (mem_pull.1 hk)).trans (a.trans ?_)
  exact congrArg₂ (· * ·) (congrArg₂ (· * ·) (gm_pull_g L τ (r ≫ F) y j j' hj hj').symm
    (congrArg (·⁻¹) (gm_pull_g L' τ' r y k k' hk hk').symm))
    (key Y r y _ _ (mem_pull.1 hj') (mem_pull.1 hk')).symm

end Iso

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

omit [IsCommMonObj G] in

theorem left_translate (a : 𝟙_ (Over S) ⟶ G) {T : Over S} (x : T ⟶ G) :
    x.left ≫ ((toUnit G ≫ a) * 𝟙 G).left = ((toUnit T ≫ a) * x).left := by
  rw [← Over.comp_left, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]

set_option maxHeartbeats 1000000 in

theorem exists_translate_pull {f : S' ⟶ S} {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}
    (Q P : CP G) (P₁ : CP G') (a : 𝟙_ (Over S) ⟶ G) (a' : 𝟙_ (Over S') ⟶ G') (ha : a'.left ≫ F = f ≫ a.left)
    (h2 : a' ^ 2 = 1) (hP : P.L.L = Q.L.L.pull ((toUnit G ≫ a) * 𝟙 G).left)
    (hs : ∀ (T : Over S) (x : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → Q.L.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good Q.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        val P.sym x.left z J' =
          val Q.sym ((toUnit T ≫ a) * x).left z J * (val Q.sym (toUnit T ≫ a).left z J)⁻¹)
    (hc : ∀ (T : Over S) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → Q.L.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good Q.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        cubV P.c z J' x y u = cubV Q.c z J x y ((toUnit T ≫ a) * u) * (cubV Q.c z J x y (toUnit T ≫ a))⁻¹)
    {w₁ : LB.Iso P₁.L.L (Q.L.L.pull F)} (h₁ : IsCPMap P₁ Q f F hw w₁) :
    ∃ P₀ : CP G', (∃ w, IsCPMap P₀ P f F hw w) ∧ P₀.L.L = P₁.L.L.pull ((toUnit G' ≫ a') * 𝟙 G').left ∧
      (∀ (T : Over S') (x : T ⟶ G') (z : T.left) (J : (T.left ⟶ G'.left) → P₁.L.L.ι)
        (J' : (T.left ⟶ G'.left) → P₀.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G' ≫ a') * 𝟙 G').left))) →
        val P₀.sym x.left z J' =
          val P₁.sym ((toUnit T ≫ a') * x).left z J * (val P₁.sym (toUnit T ≫ a').left z J)⁻¹) ∧
      (∀ (T : Over S') (x y u : T ⟶ G') (z : T.left) (J : (T.left ⟶ G'.left) → P₁.L.L.ι)
        (J' : (T.left ⟶ G'.left) → P₀.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G' ≫ a') * 𝟙 G').left))) →
        cubV P₀.c z J' x y u = cubV P₁.c z J x y ((toUnit T ≫ a') * u) * (cubV P₁.c z J x y (toUnit T ≫ a'))⁻¹) := by
  obtain ⟨⟨L, rg, hL, hrg⟩, c, sy, g₁, g₂, g₃⟩ := P
  dsimp only at hP hs hc
  subst hP
  have hβ : ∀ T : Over S', toBase hw (toUnit T ≫ a') = toUnit (Over.mk (T.hom ≫ f)) ≫ a := fun T =>
    Over.OverMorphism.ext (by
      show ((toUnit T).left ≫ a'.left) ≫ F = (toUnit (Over.mk (T.hom ≫ f))).left ≫ a.left
      rw [Rosenlicht.toUnit_left, Rosenlicht.toUnit_left, Category.assoc, ha, ← Category.assoc]; rfl)
  have hpt : ∀ {T : Over S'} (x : T ⟶ G'), (x.left ≫ F) ≫ ((toUnit G ≫ a) * 𝟙 G).left =
      ((toUnit T ≫ a') * x).left ≫ F := fun {T} x => by
    refine (left_translate a (toBase hw x)).trans ?_
    rw [← hβ, ← h₁.mul]; rfl
  have hτ : ((toUnit G' ≫ a') * 𝟙 G').left ≫ F = F ≫ ((toUnit G ≫ a) * 𝟙 G).left :=
    (hpt (𝟙 G')).symm.trans (congrArg (· ≫ _) (Category.id_comp F))
  obtain ⟨w, hg, hv⟩ := exists_translate hτ w₁ h₁.gen
  obtain ⟨rig, hr, c₀, s₀, k₁, k₂, k₃, H⟩ := exists_isCPMap (hw := hw) ⟨⟨_, rg, hL, hrg⟩, c, sy, g₁, g₂, g₃⟩ h₁.mul _
    (pull_isLB P₁.L.isLB _) w hg
  have main : ∀ (T : Over S') (z : T.left) (J : (T.left ⟶ G'.left) → P₁.L.L.ι), Good P₁.L.L z J →
      (∀ x : T ⟶ G', val s₀ x.left z (fun r _ => J (r ≫ ((toUnit G' ≫ a') * 𝟙 G').left)) =
          val P₁.sym ((toUnit T ≫ a') * x).left z J * (val P₁.sym (toUnit T ≫ a').left z J)⁻¹) ∧
      ∀ x y u : T ⟶ G', cubV c₀ z (fun r _ => J (r ≫ ((toUnit G' ≫ a') * 𝟙 G').left)) x y u =
        cubV P₁.c z J x y ((toUnit T ≫ a') * u) * (cubV P₁.c z J x y (toUnit T ≫ a'))⁻¹ := by
    intro T z J hJ
    obtain ⟨I, hI⟩ := exists_good_pt Q.L.isLB z
    obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G') → (T.left.presheaf.stalk z)ˣ,
      ∀ x, W x = gw w₁ x.left z (I (x.left ≫ F)) (J x.left) := ⟨_, fun _ => rfl⟩
    obtain ⟨-, a₂, a₃⟩ := h₁.vals T z J I hJ hI W hW
    obtain ⟨b, hb⟩ : ∃ b, b = toUnit T ≫ a' := ⟨_, rfl⟩
    have hbb : b⁻¹ = b := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← sq, hb, ← MonObj.comp_pow, h2, MonObj.comp_one]
    obtain ⟨-, b₂, b₃⟩ := H.vals T z (fun r _ => J (r ≫ ((toUnit G' ≫ a') * 𝟙 G').left))
      (fun r _ => I (r ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (fun r => mem_pull.2 (hJ (r ≫ _)))
      (fun r => mem_pull.2 (hI (r ≫ _))) (fun x => W (b * x)) (fun x => by
        refine Eq.trans ?_ (hv _ x.left z _ _ (hI ((x.left ≫ F) ≫ _)) (hJ (x.left ≫ _))).symm
        rw [hW, hpt, left_translate, hb])
    rw [← hb]
    refine ⟨fun x => ?_, fun x y u => ?_⟩
    · have e₀ := hs (Over.mk (T.hom ≫ f)) (toBase hw x) z I _ hI (fun _ => HEq.rfl)
      rw [← hβ, ← h₁.mul, ← hb] at e₀
      have e₁ : val Q.sym ((b * x).left ≫ F) z I * (val Q.sym (b.left ≫ F) z I)⁻¹ * W (b * x) =
          W (b * x⁻¹) * val s₀ x.left z (fun r _ => J (r ≫ ((toUnit G' ≫ a') * 𝟙 G').left)) :=
        (congrArg (· * W (b * x)) e₀).symm.trans (b₂ x)
      have e₂ := a₂ (b * x)
      have e₃ := a₂ b
      rw [mul_inv, hbb] at e₂
      rw [hbb] at e₃
      apply Additive.ofMul.injective
      have f₁ := congrArg Additive.ofMul e₁
      have f₂ := congrArg Additive.ofMul e₂
      have f₃ := congrArg Additive.ofMul e₃
      simp only [ofMul_mul, ofMul_inv] at f₁ f₂ f₃ ⊢
      linear_combination (norm := abel) f₂ - f₁ - f₃
    · have e₀ := hc (Over.mk (T.hom ≫ f)) (toBase hw x) (toBase hw y) (toBase hw u) z I _ hI (fun _ => HEq.rfl)
      rw [← hβ, ← h₁.mul, ← hb] at e₀
      obtain ⟨C, hC⟩ : ∃ C : (T ⟶ G') → (T.left.presheaf.stalk z)ˣ, ∀ v, C v =
        cubV Q.c (T := Over.mk (T.hom ≫ f)) z I (toBase hw x) (toBase hw y) (toBase hw v) := ⟨_, fun _ => rfl⟩
      have e₁ : C (b * u) * (C b)⁻¹ * W (b * (x * y)) * W (b * (x * u)) * W (b * (y * u)) * W (b * 1) =
          W (b * (x * y * u)) * W (b * x) * W (b * y) * W (b * u) *
            cubV c₀ z (fun r _ => J (r ≫ ((toUnit G' ≫ a') * 𝟙 G').left)) x y u := by
        rw [hC, hC]
        exact (congrArg (· * W (b * (x * y)) * W (b * (x * u)) * W (b * (y * u)) * W (b * 1)) e₀).symm.trans (b₃ x y u)
      have e₂ : ∀ v, C v * W (x * y) * W (x * v) * W (y * v) * W 1 =
          W (x * y * v) * W x * W y * W v * cubV P₁.c z J x y v := fun v => by rw [hC]; exact a₃ x y v
      have e₃ := e₂ (b * u)
      have e₄ := e₂ b
      rw [mul_left_comm x b, mul_left_comm y b, mul_left_comm (x * y) b] at e₃
      rw [mul_comm x b, mul_comm y b, mul_comm (x * y) b] at e₄
      rw [_root_.mul_one] at e₁
      apply Additive.ofMul.injective
      have f₁ := congrArg Additive.ofMul e₁
      have f₂ := congrArg Additive.ofMul e₃
      have f₃ := congrArg Additive.ofMul e₄
      simp only [ofMul_mul, ofMul_inv] at f₁ f₂ f₃ ⊢
      linear_combination (norm := abel) f₂ - f₁ - f₃
  refine ⟨⟨⟨_, rig, _, hr⟩, c₀, s₀, k₁, k₂, k₃⟩, ⟨w, H⟩, rfl, fun T x z J J' hJ h => ?_, fun T x y u z J J' hJ h => ?_⟩
  · obtain rfl : J' = fun r _ => J (r ≫ ((toUnit G' ≫ a') * 𝟙 G').left) := funext fun r => eq_of_heq (h r)
    exact (main T z J hJ).1 x
  · obtain rfl : J' = fun r _ => J (r ≫ ((toUnit G' ≫ a') * 𝟙 G').left) := funext fun r => eq_of_heq (h r)
    exact (main T z J hJ).2 x y u

theorem exists_section_pullback (f : S' ⟶ S) (a : 𝟙_ (Over S) ⟶ G) (h2 : a ^ 2 = 1) :
    ∃ a' : 𝟙_ (Over S') ⟶ (Over.pullback f).obj G, a'.left ≫ pullback.fst G.hom f = f ≫ a.left ∧ a' ^ 2 = 1 := by
  have h0 : (f ≫ a.left) ≫ G.hom = 𝟙 S' ≫ f := by
    rw [Category.assoc, Over.w a]; simp
  let a' : 𝟙_ (Over S') ⟶ (Over.pullback f).obj G :=
    Over.homMk (pullback.lift (f ≫ a.left) (𝟙 S') h0) (pullback.lift_snd _ _ _)
  have ha : a'.left ≫ pullback.fst G.hom f = f ≫ a.left := pullback.lift_fst _ _ _
  refine ⟨a', ha, ?_⟩
  let β := toBaseHom (toBase_mul_pullback G f) (𝟙_ (Over S'))
  have e : β a' = toUnit _ ≫ a := Over.OverMorphism.ext (by
    refine ha.trans ?_
    rw [Over.comp_left, Rosenlicht.toUnit_left]
    exact congrArg (· ≫ a.left) (Category.id_comp f).symm)
  have e' : β (a' ^ 2) = β 1 := by rw [map_pow, map_one, e, ← MonObj.comp_pow, h2, MonObj.comp_one]
  exact Over.OverMorphism.ext (pullback.hom_ext (congrArg (fun q => q.left) e')
    ((Over.w (a' ^ 2)).trans (Over.w (1 : 𝟙_ (Over S') ⟶ (Over.pullback f).obj G)).symm))

theorem exists_level_translate : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal R) D A G) (a : 𝟙_ (Over (Sp R)) ⟶ G), a ^ 2 = 1 →
    ∀ P : GlobalTheory.UU.CP G, P.L.L = U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left →
      (∀ (T : Over (Sp R)) (x : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → U.LG.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good U.LG.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        val P.sym x.left z J' =
          val U.symG ((toUnit T ≫ a) * x).left z J * (val U.symG (toUnit T ≫ a).left z J)⁻¹) →
      (∀ (T : Over (Sp R)) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → U.LG.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good U.LG.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        cubV P.c z J' x y u = cubV U.cubG z J x y ((toUnit T ≫ a) * u) * (cubV U.cubG z J x y (toUnit T ≫ a))⁻¹) →
    ∀ P₁ : GlobalTheory.UU.CP (thickObj R (maximalIdeal R) 0 G),
      GlobalTheory.UU.IsLevelCP (maximalIdeal R) 0 P₁ (GlobalTheory.ValueForm.modelCP U.toUnifPre GlobalTheory.firstFiveLaws.1.globalFns) →
    ∃ (a₀ : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1))))) ⟶ thickObj R (maximalIdeal R) 0 G)
      (P₀ : GlobalTheory.UU.CP (thickObj R (maximalIdeal R) 0 G)),
      a₀.left ≫ pullback.fst G.hom (thick R (maximalIdeal R) 0) = thick R (maximalIdeal R) 0 ≫ a.left ∧ a₀ ^ 2 = 1 ∧
      GlobalTheory.UU.IsLevelCP (maximalIdeal R) 0 P₀ P ∧
      P₀.L.L = P₁.L.L.pull ((toUnit (thickObj R (maximalIdeal R) 0 G) ≫ a₀) * 𝟙 (thickObj R (maximalIdeal R) 0 G)).left ∧
      (∀ (T : Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1))))) (x : T ⟶ thickObj R (maximalIdeal R) 0 G) (z : T.left)
        (J : (T.left ⟶ (thickObj R (maximalIdeal R) 0 G).left) → P₁.L.L.ι)
        (J' : (T.left ⟶ (thickObj R (maximalIdeal R) 0 G).left) → P₀.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit (thickObj R (maximalIdeal R) 0 G) ≫ a₀) * 𝟙 (thickObj R (maximalIdeal R) 0 G)).left))) →
        val P₀.sym x.left z J' =
          val P₁.sym ((toUnit T ≫ a₀) * x).left z J * (val P₁.sym (toUnit T ≫ a₀).left z J)⁻¹) ∧
      (∀ (T : Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1))))) (x y u : T ⟶ thickObj R (maximalIdeal R) 0 G) (z : T.left)
        (J : (T.left ⟶ (thickObj R (maximalIdeal R) 0 G).left) → P₁.L.L.ι)
        (J' : (T.left ⟶ (thickObj R (maximalIdeal R) 0 G).left) → P₀.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit (thickObj R (maximalIdeal R) 0 G) ≫ a₀) * 𝟙 (thickObj R (maximalIdeal R) 0 G)).left))) →
        cubV P₀.c z J' x y u = cubV P₁.c z J x y ((toUnit T ≫ a₀) * u) * (cubV P₁.c z J x y (toUnit T ≫ a₀))⁻¹) := by
  intro R _ _ _ D A G _ _ U a h2 P hP hs hc P₁ h₁
  obtain ⟨w₁, h₁⟩ := h₁
  obtain ⟨a₀, ha, h₀⟩ := exists_section_pullback (thick R (maximalIdeal R) 0) a h2
  obtain ⟨P₀, k⟩ := exists_translate_pull _ P P₁ a a₀ ha h₀ hP hs hc h₁
  exact ⟨a₀, P₀, ha, h₀, k⟩

end GlobalTheory.Mum.TranslateLevel
