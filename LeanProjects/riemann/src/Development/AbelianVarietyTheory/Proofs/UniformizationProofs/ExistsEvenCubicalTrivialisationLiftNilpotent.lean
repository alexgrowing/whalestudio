import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsNilpotentOfRd
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EvSurjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenLiftOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.CubeLift

open SplitTorus (bcMap)

theorem exists_pmaps_lift {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
    {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (h : Y' ⟶ Y) [IsClosedImmersion h] [Surjective h] [IsAffine Y] (hc : ∀ k, φ' k ≫ F = h ≫ φ k)
    (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen ∧ PMaps w φ' φ ε a t h := by
  obtain ⟨t₁, ht₁, hv⟩ := exists_up hw hL hL' a ha
  have le : ∀ j : PUnit → K → L.ι, ((LB.LinComb L φ ε).pull h).U j ≤
      LB.wchart L (fun k => φ' k ≫ F) (j PUnit.unit) := fun j y hy => Set.mem_iInter.2 fun k => by
    have : φ k (h y) ∈ L.U (j PUnit.unit k) := Set.mem_iInter.1 (mem_pull.1 hy) k
    rw [pt_eq hc] at this
    exact this
  let t₀ : LB.Gen ((LB.LinComb L φ ε).pull h) := ⟨fun j => res (le j) (t₁.s (j PUnit.unit))⟩
  have ht₀ : t₀.IsGen := isGen_of_gm _ fun y j j' hj hj' => by
    refine (gm_res (𝟙 Y') y (le j) hj _).trans ((gen_trans ht₁ (𝟙 Y') y (le j hj) (le j' hj')).trans
      (congrArg₂ (· * ·) ?_ (gm_res (𝟙 Y') y (le j') hj' _).symm))
    unfold trF
    symm
    rw [Fintype.prod_unique, zpow_one]
    refine (gm_linComb L φ ε (𝟙 Y' ≫ h) y _ _ (mem_pull.1 hj) (mem_pull.1 hj')).trans ?_
    simp only [hc, Category.assoc]
  obtain ⟨t, ht, e⟩ := GenLift.exists_genPull_eq h (LB.isLB_linComb hL φ ε) t₀ ht₀
  refine ⟨t, ht, fun Z r z p q hp hq => ?_⟩
  have m : h (r z) ∈ LB.wchart L φ p := Set.mem_iInter.2 fun k => by
    show φ k (h (r z)) ∈ L.U (p k)
    rw [pt_eq hc]; exact hp k
  have m' : r z ∈ ((LB.LinComb L φ ε).pull h).U fun _ => p := mem_pull.2 m
  refine Eq.trans ?_ (hv Z r z p q (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hq))
  refine Eq.trans ?_ (gm_res r z (le fun _ => p) m' _)
  refine Eq.trans ?_ (congrArg (fun s : LB.Gen ((LB.LinComb L φ ε).pull h) => gm r z _ (s.s fun _ => p)) e)
  exact ((gm_res r z _ m' _).trans (gm_pull r h z _ m _)).symm

section Defect

variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] {i : H ⟶ G}

theorem prod_triv {T : Over S} (x : T ⟶ H) {U : Type} [CommGroup U] (h : (T.left ⟶ G.left) → U) :
    ∏ k : Fin 2, h (x.left ≫ ![i.left, (1 : H ⟶ G).left] k) ^ (![1, -1] : Fin 2 → ℤ) k =
      h (x ≫ i).left * (h (1 : T ⟶ G).left)⁻¹ := by
  rw [Fin.prod_univ_two, ← MonObj.comp_one x]
  show h (x ≫ i).left ^ (1 : ℤ) * h (x ≫ 1).left ^ (-1 : ℤ) = _
  rw [zpow_one, zpow_neg, zpow_one]

variable [IsCommMonObj G] [GrpObj H] [IsMonHom i]

theorem exists_defect {L : RigLB G} (c : CubicalStr G L)
    (t : LB.Gen (LB.LinComb L.L (K := Fin 2) ![i.left, (1 : H ⟶ G).left] ![1, -1])) (ht : t.IsGen)
    {V : Over S} (a b d : V ⟶ H) : ∃ D : Γ(V.left, ⊤)ˣ, ∀ (T : Over S) (ρ : T ⟶ V) (z : T.left) (J), Good L.L z J →
      val t ((ρ ≫ a) * (ρ ≫ b) * (ρ ≫ d)).left z J * val t (ρ ≫ a).left z J * val t (ρ ≫ b).left z J *
        val t (ρ ≫ d).left z J = gm ρ.left z ⊤ D * (cubV c z J ((ρ ≫ a) ≫ i) ((ρ ≫ b) ≫ i) ((ρ ≫ d) ≫ i) *
          val t ((ρ ≫ a) * (ρ ≫ b)).left z J * val t ((ρ ≫ a) * (ρ ≫ d)).left z J *
          val t ((ρ ≫ b) * (ρ ≫ d)).left z J) := by
  let sy := fun p : V ⟶ H => LB.pullGen L.L _ _ t p.left
  have gs : ∀ p, (sy p).IsGen := fun p => DVR.pullGen_isGen _ _ _ _ ht _
  let cu := LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift (a ≫ i) (lift (b ≫ i) (d ≫ i))).left
  have gc : cu.IsGen := DVR.pullGen_isGen _ _ _ _ c.isGen _
  obtain ⟨D, hD⟩ := TorusCoord.exists_ratio L.isLB (fun U _ k => by
      refine (DVR.prod_sum₂ (K := (Fin 2 ⊕ Fin 2) ⊕ Fin 2) (K' := Fin 2) (U := U) _
        (DVR.prod_sum₂ (K := Fin 2 ⊕ Fin 2) (K' := Fin 2) (U := U) _
          (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := U) _ (prod_triv (a * b * d) k) (prod_triv a k))
          (prod_triv b k)) (prod_triv d k)).trans (Eq.trans ?_
        (DVR.prod_sum₂ (K := (thK ⊕ Fin 2) ⊕ Fin 2) (K' := Fin 2) (U := U) _
          (DVR.prod_sum₂ (K := thK ⊕ Fin 2) (K' := Fin 2) (U := U) _
            (DVR.prod_sum₂ (K := thK) (K' := Fin 2) (U := U) _ (prod_cub (a ≫ i) (b ≫ i) (d ≫ i) k)
              (prod_triv (a * b) k)) (prod_triv (a * d) k)) (prod_triv (b * d) k)).symm)
      simp only [MonObj.mul_comp]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (sy (a * b * d)) (sy a)) (sy b)) (sy d))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (gs _) (gs _))
      (gs _)) (gs _))
    (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ cu (sy (a * b))) (sy (a * d))) (sy (b * d)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ gc (gs _))
      (gs _)) (gs _))
  refine ⟨D, fun T ρ z J hJ => ?_⟩
  have vs : ∀ p, val (sy p) ρ.left z J = val t (ρ ≫ p).left z J := fun p => val_pull hJ _ _ _
  simp only [← MonObj.comp_mul, Category.assoc]
  refine Eq.trans ?_ ((hD _ ρ.left z J hJ).trans (congrArg (gm ρ.left z ⊤ D * ·) ?_))
  · exact ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vs _) (vs _))) (vs _))) (vs _))).symm
  · exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub c ρ hJ _ _ _) (vs _))) (vs _))) (vs _))

theorem exists_odd (P : CP G)
    (t : LB.Gen (LB.LinComb P.L.L (K := Fin 2) ![i.left, (1 : H ⟶ G).left] ![1, -1])) (ht : t.IsGen) :
    ∃ E : Γ(H.left, ⊤)ˣ, ∀ (T : Over S) (x : T ⟶ H) (z : T.left) (J), Good P.L.L z J →
      val t (x⁻¹).left z J = gm x.left z ⊤ E * (val P.sym (x ≫ i).left z J * val t x.left z J) := by
  obtain ⟨E, hE⟩ := TorusCoord.exists_ratio P.L.isLB (fun U _ k => by
      refine (prod_triv (𝟙 H)⁻¹ k).trans (Eq.trans ?_
        (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := U) _ (prod_sym i k) (prod_triv (𝟙 H) k)).symm)
      rw [GrpObj.inv_comp, Category.id_comp, ← _root_.mul_assoc, inv_mul_cancel_right])
    (LB.pullGen P.L.L _ _ t ((𝟙 H)⁻¹ : H ⟶ H).left) (DVR.pullGen_isGen _ _ _ _ ht _)
    (LB.mulGen P.L.L _ _ _ _ (LB.pullGen P.L.L _ _ P.sym i.left) (LB.pullGen P.L.L _ _ t (𝟙 H : H ⟶ H).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ P.sym_gen _) (DVR.pullGen_isGen _ _ _ _ ht _))
  refine ⟨E, fun T x z J hJ => ?_⟩
  have e := hE _ x.left z J hJ
  rw [val_mul hJ, val_pull hJ, val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left,
    GrpObj.comp_inv, Category.comp_id] at e
  exact e

end Defect

section Alg

variable {B C U : Type} [CommGroup B] [CommGroup C] [CommGroup U]

theorem defect_alg {θ : C → C → C → U} (hθ : IsCub θ) (ι' : B →* C) (σ : B → U) (D : B → B → B → U)
    (h : ∀ x y u, σ (x * y * u) * σ x * σ y * σ u =
      D x y u * (θ (ι' x) (ι' y) (ι' u) * σ (x * y) * σ (x * u) * σ (y * u))) :
    (∀ x y u, D x y u = D y x u) ∧ (∀ x y u, D x y u = D x u y) ∧
      ∀ x y u v, D (x * y) u v * D x y v = D x (y * u) v * D y u v := by
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  refine ⟨fun x y u => ?_, fun x y u => ?_, fun x y u v => ?_⟩
  · have a := E (h x y u)
    have b := E (h y x u)
    rw [mul_comm y x, hθ.s01] at b
    apply Additive.ofMul.injective
    simp only [ofMul_mul] at a b ⊢
    linear_combination (norm := abel) b - a
  · have a := E (h x y u)
    have b := E (h x u y)
    rw [mul_comm u y, mul_right_comm x u y, hθ.s12] at b
    apply Additive.ofMul.injective
    simp only [ofMul_mul] at a b ⊢
    linear_combination (norm := abel) b - a
  · have a₁ := E (h (x * y) u v)
    have a₂ := E (h x y v)
    have a₃ := E (h x (y * u) v)
    have a₄ := E (h y u v)
    have c := E (hθ.coc (ι' x) (ι' y) (ι' u) (ι' v))
    apply Additive.ofMul.injective
    simp only [ofMul_mul, map_mul, ← _root_.mul_assoc] at a₁ a₂ a₃ a₄ c ⊢
    linear_combination (norm := abel) a₃ + a₄ - a₁ - a₂ - c

theorem odd_alg {σ s E : B → U} {c c' : U} {x y u : B} (hE : ∀ a, σ a⁻¹ = E a * (s a * σ a))
    (h : σ (x * y * u) * σ x * σ y * σ u = c * σ (x * y) * σ (x * u) * σ (y * u))
    (h' : σ (x⁻¹ * y⁻¹ * u⁻¹) * σ x⁻¹ * σ y⁻¹ * σ u⁻¹ = c' * σ (x⁻¹ * y⁻¹) * σ (x⁻¹ * u⁻¹) * σ (y⁻¹ * u⁻¹))
    (hs : c' * s (x * y) * s (x * u) * s (y * u) = c * s (x * y * u) * s x * s y * s u) :
    E (x * y * u) * E x * E y * E u / E (x * y) / E (x * u) / E (y * u) = 1 := by
  simp only [← mul_inv, hE] at h'
  have a := congrArg Additive.ofMul h
  have b := congrArg Additive.ofMul h'
  have d := congrArg Additive.ofMul hs
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_one] at a b d ⊢
  linear_combination (norm := abel) b - a + d

theorem cub_red_alg {a₁ a₂ a₃ a₄ a₅ a₆ a₇ w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₀ c c₀ D v₁ v₂ v₃ v₄ v₅ v₆ v₇ : U}
    (h₀ : a₁ * a₂ * a₃ * a₄ = c₀ * a₅ * a₆ * a₇) (hc : c * w₅ * w₆ * w₇ * w₀ = w₁ * w₂ * w₃ * w₄ * c₀)
    (r₁ : v₁ = w₁ * w₀⁻¹ * a₁) (r₂ : v₂ = w₂ * w₀⁻¹ * a₂) (r₃ : v₃ = w₃ * w₀⁻¹ * a₃) (r₄ : v₄ = w₄ * w₀⁻¹ * a₄)
    (r₅ : v₅ = w₅ * w₀⁻¹ * a₅) (r₆ : v₆ = w₆ * w₀⁻¹ * a₆) (r₇ : v₇ = w₇ * w₀⁻¹ * a₇)
    (h : v₁ * v₂ * v₃ * v₄ = D * (c * v₅ * v₆ * v₇)) : D = 1 := by
  subst r₁ r₂ r₃ r₄ r₅ r₆ r₇
  have a := congrArg Additive.ofMul h₀
  have b := congrArg Additive.ofMul hc
  have d := congrArg Additive.ofMul h
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at a b d ⊢
  linear_combination (norm := abel) a - b - d

theorem odd_red_alg {a a' w w' w₀ s s₀ E : U} (h₀ : a' = s₀ * a) (hs : s * w = w' * s₀)
    (h : w' * w₀⁻¹ * a' = E * (s * (w * w₀⁻¹ * a))) : E = 1 := by
  have a := congrArg Additive.ofMul h₀
  have b := congrArg Additive.ofMul hs
  have d := congrArg Additive.ofMul h
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at a b d ⊢
  linear_combination (norm := abel) a - b - d

theorem scale_alg {a₁ a₂ a₃ a₄ a₅ a₆ a₇ g₁ g₂ g₃ g₄ g₅ g₆ g₇ c : U}
    (h : a₁ * a₂ * a₃ * a₄ = g₁ * g₂ * g₃ * g₄ / g₅ / g₆ / g₇ * (c * a₅ * a₆ * a₇)) :
    g₁⁻¹ * a₁ * (g₂⁻¹ * a₂) * (g₃⁻¹ * a₃) * (g₄⁻¹ * a₄) = c * (g₅⁻¹ * a₅) * (g₆⁻¹ * a₆) * (g₇⁻¹ * a₇) := by
  have a := congrArg Additive.ofMul h
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_div] at a ⊢
  linear_combination (norm := abel) a

end Alg

section Lift

variable {A : Type} [CommRing A] {J : Ideal A} {X : Type} [AddCommGroup X]
  {G : Over (Spec (CommRingCat.of A))} [GrpObj G] [IsCommMonObj G]
  {G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))} [GrpObj G₀] [IsCommMonObj G₀]
  {F : G₀.left ⟶ G.left} {hw : F ≫ G.hom = G₀.hom ≫ red J} {P : CP G} {P₀ : CP G₀}
  {w : LB.Iso P₀.L.L (P.L.L.pull F)} {i : splitTorus _ X ⟶ G} {i₀ : splitTorus _ X ⟶ G₀}

variable (w) in

def Reduces (t : LB.Gen (LB.LinComb P.L.L (K := Fin 2) ![i.left, (1 : splitTorus _ X ⟶ G).left] ![1, -1]))
    (σ₀ : CubTriv P₀.c i₀) : Prop :=
  ∀ (T : Over (Spec (CommRingCat.of (A ⧸ J)))) (z : T.left) (C₀) (C), Good P₀.L.L z C₀ → Good P.L.L z C →
    ∀ W : (T ⟶ G₀) → (T.left.presheaf.stalk z)ˣ, (∀ x, W x = gw w x.left z (C (x.left ≫ F)) (C₀ x.left)) →
      ∀ x : T ⟶ splitTorus _ X, val t (x.left ≫ bcMap (red J) X) z C = W (x ≫ i₀) * (W 1)⁻¹ * val σ₀.s x.left z C₀

theorem exists_reduces (hJ : IsNilpotent J) (h : IsCPMap P₀ P (red J) F hw w)
    (hi : bcMap (red J) X ≫ i.left = i₀.left ≫ F) (σ₀ : CubTriv P₀.c i₀) :
    ∃ t : LB.Gen (LB.LinComb P.L.L (K := Fin 2) ![i.left, (1 : splitTorus _ X ⟶ G).left] ![1, -1]),
      t.IsGen ∧ Reduces w t σ₀ := by
  have := surjective_red hJ
  have hp := (SplitTorus.isPullback_bcMap (red J) X).flip
  have : IsClosedImmersion (bcMap (red J) X) := MorphismProperty.of_isPullback hp inferInstance
  have : Surjective (bcMap (red J) X) := MorphismProperty.of_isPullback hp inferInstance
  have : IsAffine (splitTorus (Spec (CommRingCat.of A)) X).left :=
    isAffine_of_isAffineHom (splitTorus (Spec (CommRingCat.of A)) X).hom
  have hc : ∀ k : Fin 2, ![i₀.left, (1 : splitTorus _ X ⟶ G₀).left] k ≫ F =
      bcMap (red J) X ≫ ![i.left, (1 : splitTorus _ X ⟶ G).left] k := fun k => by
    fin_cases k
    · exact hi.symm
    · refine (one_left_comp h.mul _).trans (Eq.trans ?_ (congrArg (bcMap (red J) X ≫ ·) (one_left G _)).symm)
      rw [← SplitTorus.bcMap_hom, Category.assoc]
  obtain ⟨t, ht, H⟩ := exists_pmaps_lift ((isGen_iff w).1 h.gen) P.L.isLB P₀.L.isLB (bcMap (red J) X) hc σ₀.s σ₀.gen
  refine ⟨t, ht, fun T z C₀ C hC₀ hC W hW x => ?_⟩
  simp only [hW]
  exact (CubTransport.val_pmaps hc H x.left hC hC₀).trans
    (congrArg₂ (· * ·) (prod_triv x (fun q => gw w q z (C (q ≫ F)) (C₀ q))) rfl)

def up (T : Over (Spec (CommRingCat.of (A ⧸ J)))) :
    (T ⟶ splitTorus _ X) →* (Over.mk (T.hom ≫ red J) ⟶ splitTorus _ X) :=
  toBaseHom (hw := SplitTorus.bcMap_hom (red J) X) (fun T x y => Over.OverMorphism.ext
    (SplitTorus.mul_left_bcMap (red J) X T x y _ _ rfl rfl).symm) T

theorem up_comp (hi : bcMap (red J) X ≫ i.left = i₀.left ≫ F) {T : Over (Spec (CommRingCat.of (A ⧸ J)))}
    (x : T ⟶ splitTorus _ X) : up T x ≫ i = toBase hw (x ≫ i₀) := Over.OverMorphism.ext <| by
  show (x.left ≫ bcMap (red J) X) ≫ i.left = (x.left ≫ i₀.left) ≫ F
  rw [Category.assoc, hi, Category.assoc]

theorem Reduces.scale {t : LB.Gen (LB.LinComb P.L.L (K := Fin 2) ![i.left, (1 : splitTorus _ X ⟶ G).left] ![1, -1])}
    {σ₀ : CubTriv P₀.c i₀} (h : Reduces w t σ₀) {g : Γ((splitTorus (Spec (CommRingCat.of A)) X).left, ⊤)ˣ}
    (hg : app (bcMap (red J) X) g = 1) : Reduces w (scaleGen g t) σ₀ := fun T z C₀ C hC₀ hC W hW x => by
  have e : gm (x.left ≫ bcMap (red J) X) z ⊤ g = 1 := by
    rw [gm_top]
    exact (congrArg _ ((app_app _ _ g).symm.trans (by rw [hg, map_one]))).trans (map_one _)
  rw [val_scaleGen _ _ _ hC, e, _root_.one_mul]
  exact h T z C₀ C hC₀ hC W hW x

theorem exists_cubTriv_reduces [IsMonHom i] [IsMonHom i₀] (hJ : IsNilpotent J) (h : IsCPMap P₀ P (red J) F hw w)
    (hi : bcMap (red J) X ≫ i.left = i₀.left ≫ F) (σ₀ : CubTriv P₀.c i₀) :
    ∃ σ : CubTriv P.c i, Reduces w σ.s σ₀ := by
  obtain ⟨t, ht, hr⟩ := exists_reduces hJ h hi σ₀
  obtain ⟨D, hD⟩ := exists_defect P.c t ht (SplitTorus.torusMap _ (p₁ (X := X))) (SplitTorus.torusMap _ p₂)
    (SplitTorus.torusMap _ p₃)
  have hD' : ∀ (T : Over (Spec (CommRingCat.of A))) (z : T.left) (C), Good P.L.L z C →
      ∀ x y u : T ⟶ splitTorus _ X, val t (x * y * u).left z C * val t x.left z C * val t y.left z C *
        val t u.left z C = gm (𝟙 T.left) z ⊤ (app (pt x y u).left D) * (cubV P.c z C (x ≫ i) (y ≫ i) (u ≫ i) *
          val t (x * y).left z C * val t (x * u).left z C * val t (y * u).left z C) := fun T z C hC x y u => by
    have e := hD T (pt x y u) z C hC
    rwa [pt_p₁, pt_p₂, pt_p₃, gm_top] at e
  have alg := fun (T : Over (Spec (CommRingCat.of A))) (z : T.left) =>
    defect_alg (isCub_cubV P.c (exists_good_pt P.L.isLB z).choose_spec)
      (MonoidHom.mk' (fun x : T ⟶ splitTorus _ X => x ≫ i) fun x y => MonObj.mul_comp x y i)
      (fun x => val t x.left z _) (fun x y u => gm (𝟙 T.left) z ⊤ (app (pt x y u).left D))
      (hD' T z _ (exists_good_pt P.L.isLB z).choose_spec)
  have h₀ : app (bcMap (red J) (X × X × X)) D = 1 := unit_ext fun z _ => by
    obtain ⟨C, hC⟩ := exists_good_pt P.L.isLB z
    obtain ⟨C₀, hC₀⟩ := exists_good_pt P₀.L.isLB z
    let T := splitTorus (Spec (CommRingCat.of (A ⧸ J))) (X × X × X)
    have k : ∀ p : X →+ X × X × X, up T (𝟙 T) ≫ SplitTorus.torusMap _ p = up T (SplitTorus.torusMap _ p) :=
      fun p => Over.OverMorphism.ext (((congrArg (· ≫ _) (Category.id_comp _)).trans
        (SplitTorus.torusMap_bcMap (red J) p).symm))
    have e := hD _ (up T (𝟙 T)) z C hC
    rw [k, k, k, up_comp (hw := hw) hi, up_comp (hw := hw) hi, up_comp (hw := hw) hi] at e
    simp only [← map_mul] at e
    obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G₀) → (T.left.presheaf.stalk z)ˣ,
      ∀ x, W x = gw w x.left z (C (x.left ≫ F)) (C₀ x.left) := ⟨_, fun _ => rfl⟩
    have r : ∀ x, val t (up T x).left z C = _ := hr T z C₀ C hC₀ hC W hW
    have c := (h.vals T z C₀ C hC₀ hC W hW).2.2 (SplitTorus.torusMap _ p₁ ≫ i₀) (SplitTorus.torusMap _ p₂ ≫ i₀)
      (SplitTorus.torusMap _ p₃ ≫ i₀)
    simp only [← MonObj.mul_comp] at c
    have e' := cub_red_alg (σ₀.cub T _ _ _ z C₀ hC₀) c (r _) (r _) (r _) (r _) (r _) (r _) (r _) e
    rw [map_one, ← gm_top, ← Category.id_comp (bcMap _ _)]
    exact e'
  obtain ⟨g, hg, hg'⟩ := exists_dif hJ D (fun T x y u => unit_ext fun z _ => (alg T z).1 x y u)
    (fun T x y u => unit_ext fun z _ => (alg T z).2.1 x y u)
    (fun T x y u v => unit_ext fun z _ => by rw [map_mul, map_mul]; exact (alg T z).2.2 x y u v) h₀
  refine ⟨⟨scaleGen g⁻¹ t, scaleGen_isGen _ ht, fun T x y u z C hC => ?_⟩, hr.scale (by rw [map_inv, hg, inv_one])⟩
  have e := hD' T z C hC x y u
  rw [hg', dif] at e
  simp only [map_mul, map_div, ← gm_top] at e
  simp only [val_scaleGen _ _ _ hC, map_inv]
  exact scale_alg e

theorem Reduces.even [IsMonHom i] [IsMonHom i₀] (hJ : IsNilpotent J) (h : IsCPMap P₀ P (red J) F hw w)
    (hi : bcMap (red J) X ≫ i.left = i₀.left ≫ F) {σ₀ : CubTriv P₀.c i₀} (h₀ : σ₀.Even) {σ : CubTriv P.c i}
    (hr : Reduces w σ.s σ₀) : σ.Even := by
  obtain ⟨E, hE⟩ := exists_odd P σ.s σ.gen
  have e : E = 1 := by
    refine eq_one_of_dif hJ E (unit_ext fun z _ => ?_) fun T x y u => unit_ext fun z _ => ?_
    · obtain ⟨C, hC⟩ := exists_good_pt P.L.isLB z
      obtain ⟨C₀, hC₀⟩ := exists_good_pt P₀.L.isLB z
      let T := splitTorus (Spec (CommRingCat.of (A ⧸ J))) X
      have e := hE _ (up T (𝟙 T)) z C hC
      rw [up_comp (hw := hw) hi, ← map_inv] at e
      obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G₀) → (T.left.presheaf.stalk z)ˣ,
        ∀ x, W x = gw w x.left z (C (x.left ≫ F)) (C₀ x.left) := ⟨_, fun _ => rfl⟩
      have r : ∀ x, val σ.s (up T x).left z C = _ := hr T z C₀ C hC₀ hC W hW
      have c := (h.vals T z C₀ C hC₀ hC W hW).2.1 (𝟙 T ≫ i₀)
      rw [← GrpObj.inv_comp] at c
      have e' := odd_red_alg (h₀ T (𝟙 T) z C₀ hC₀) c ((r _).symm.trans (e.trans
        (congrArg (_ * ·) (congrArg₂ (· * ·) rfl (r _)))))
      rw [map_one, ← gm_top, ← Category.id_comp (bcMap _ _)]
      exact e'
    · obtain ⟨C, hC⟩ := exists_good_pt P.L.isLB z
      have a := σ.cub T x⁻¹ y⁻¹ u⁻¹ z C hC
      have b := P.sym_cub T (x ≫ i) (y ≫ i) (u ≫ i) z C hC
      simp only [← MonObj.mul_comp, ← GrpObj.inv_comp] at b
      rw [dif]
      simp only [map_mul, map_div, ← gm_top, map_one]
      exact odd_alg (σ := fun a : T ⟶ splitTorus _ X => val σ.s a.left z C)
        (s := fun a => val P.sym (a ≫ i).left z C) (E := fun a => gm a.left z ⊤ E) (fun a => hE T a z C hC)
        (σ.cub T x y u z C hC) a b
  intro T x z C hC
  rw [hE T x z C hC, e, map_one, _root_.one_mul]

end Lift

theorem exists_even_cubTriv : (∀ (A : Type) [CommRing A] [IsLocalRing A] (J : Ideal A), IsNilpotent J → J ≠ ⊤ → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] (G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G₀] [IsCommMonObj G₀] (F : G₀.left ⟶ G.left) (hw), IsGrpPullback G₀ G (red J) F → ∀ (P : CP G) (P₀ : CP G₀) (w), IsCPMap P₀ P (red J) F hw w → ∀ (i : splitTorus _ X ⟶ G) (i₀ : splitTorus _ X ⟶ G₀), IsMonHom i → IsMonHom i₀ → TorusCompat (red J) F i₀ i → Nonempty (BiTriv P.c i) → (∃ σ₀ : CubTriv P₀.c i₀, σ₀.Even) → ∃ σ : CubTriv P.c i, σ.Even) := by
  intro A _ _ J hJ _ X _ _ G _ _ G₀ _ _ F hw _ P P₀ w h i i₀ hi hi₀ hc _ ⟨σ₀, h₀⟩
  obtain ⟨σ, hσ⟩ := exists_cubTriv_reduces hJ h (torusCompat_iff.1 hc) σ₀
  exact ⟨σ, hσ.even hJ h (torusCompat_iff.1 hc) h₀⟩

end GlobalTheory.CubeLift
