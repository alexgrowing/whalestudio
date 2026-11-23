import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueCharacterOfMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceOfSection
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.CubTrivTorus

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

private lemma global_units_ext_of_gm_id_eq {Z : Scheme.{0}} {u v : Γ(Z, ⊤)ˣ}
    (h : ∀ z : Z, gm (𝟙 Z) z ⊤ u = gm (𝟙 Z) z ⊤ v) : u = v := by
  ext
  apply fn_ext
  intro x _
  rw [gs_unit (𝟙 Z) x ⊤ (by simp) u, gs_unit (𝟙 Z) x ⊤ (by simp) v, h x]

private lemma scheme_appTop_comp_apply {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (a : Γ(C, ⊤)) :
    f.appTop.hom (g.appTop.hom a) = (f ≫ g).appTop.hom a := by
  rw [Scheme.Hom.comp_appTop]
  rfl

private lemma global_val_eq_of_gm_eq {A B : Scheme.{0}} (r : A ⟶ B) (ρ : Γ(B, ⊤)ˣ) (c : Γ(A, ⊤)ˣ)
    (h : ∀ z, gm r z ⊤ ρ = gm (𝟙 A) z ⊤ c) : r.appTop.hom ρ.val = c.val := by
  have e : Units.map (r.appTop.hom : Γ(B, ⊤) →* Γ(A, ⊤)) ρ = c :=
    global_units_ext_of_gm_id_eq fun z => by rw [← h z, gm_top r]; rfl
  rw [← e]
  rfl

private lemma global_val_eq_mul_of_gm_eq_mul {A B : Scheme.{0}} (r r₁ r₂ : A ⟶ B) (ρ : Γ(B, ⊤)ˣ)
    (h : ∀ z, gm r z ⊤ ρ = gm r₁ z ⊤ ρ * gm r₂ z ⊤ ρ) :
    r.appTop.hom ρ.val = r₁.appTop.hom ρ.val * r₂.appTop.hom ρ.val := by
  have e := global_val_eq_of_gm_eq r ρ (Units.map (r₁.appTop.hom : Γ(B, ⊤) →* Γ(A, ⊤)) ρ *
    Units.map (r₂.appTop.hom : Γ(B, ⊤) →* Γ(A, ⊤)) ρ) (fun z => by rw [map_mul, h z, gm_top r₁, gm_top r₂]; rfl)
  rw [e]
  rfl

theorem existsUnique_char {Y : Over S} [ConnectedSpace Y.left] (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ)
    (hρ : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y) (z : Z.left),
      gm (lift (t * t') y).left z ⊤ ρ = gm (lift t y).left z ⊤ ρ * gm (lift t' y).left z ⊤ ρ) :
    ∃! χ : X, ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ Y) (z : Z.left),
      gm (lift t y).left z ⊤ ρ = gm (𝟙 Z.left) z ⊤ (chV t χ) := by
  have hm : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y),
      (lift (t * t') y).left.appTop.hom ρ.val =
        (lift t y).left.appTop.hom ρ.val * (lift t' y).left.appTop.hom ρ.val :=
    fun Z t t' y => global_val_eq_mul_of_gm_eq_mul _ _ _ ρ (hρ Z t t' y)
  obtain ⟨χ, hχ, huniq⟩ := GlobalTheory.existsUnique_character_of_mul S X Y ρ hm
  refine ⟨χ, fun Z t y z => ?_, fun χ' hχ' => huniq χ' ?_⟩
  · rw [gm_top]
    congr 1
    ext
    simp only [Units.coe_map, hχ, chV_val]
    show (lift t y).left.appTop.hom ((fst (splitTorus S X) Y).left.appTop.hom _) = _
    rw [scheme_appTop_comp_apply, ← Over.comp_left, lift_fst]
  · have e := global_val_eq_of_gm_eq (𝟙 _) ρ (chV (fst (splitTorus S X) Y) χ') (fun z => by
      have := hχ' (splitTorus S X ⊗ Y) (fst _ _) (snd _ _) z
      rwa [lift_fst_snd, Over.id_left] at this)
    rw [chV_val] at e
    simpa using e

theorem eq_one_of_mul {Y : Over S} [GrpObj Y] [ConnectedSpace Y.left] (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ)
    (hρ : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y) (z : Z.left),
      gm (lift (t * t') y).left z ⊤ ρ = gm (lift t y).left z ⊤ ρ * gm (lift t' y).left z ⊤ ρ)
    (h₁ : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (z : Z.left), gm (lift t (1 : Z ⟶ Y)).left z ⊤ ρ = 1)
    (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ Y) (z : Z.left) : gm (lift t y).left z ⊤ ρ = 1 := by
  obtain ⟨χ, hχ, -⟩ := existsUnique_char ρ hρ
  rw [hχ Z t y z, ← hχ Z t 1 z]
  exact h₁ Z t z

theorem connectedSpace_torus [ConnectedSpace S] [Module.Free ℤ X] : ConnectedSpace (splitTorus S X).left := by
  have hS : ConnectedSpace (𝟙_ (Over S)).left := ‹ConnectedSpace S›
  haveI : Smooth (𝟙_ (Over S)).hom := by show Smooth (𝟙 S); infer_instance
  haveI : GeometricallyConnected (𝟙_ (Over S)).hom := by show GeometricallyConnected (𝟙 S); infer_instance
  obtain ⟨h, -⟩ := (GlobalTheory.GroupConn.connectedSpace_group S (𝟙_ (Over S))).2 X (𝟙_ (Over S)) hS
  haveI : ConnectedSpace ((Over.forget S).obj (splitTorus S X ⊗ 𝟙_ (Over S))) := h
  let e := (Over.forget S).mapIso (ρ_ (splitTorus S X))
  exact (Scheme.homeoOfIso e).surjective.connectedSpace (Scheme.homeoOfIso e).continuous

private lemma gm_units_map_global_eq_gm_comp {A B C : Scheme.{0}} (r : A ⟶ B) (g : B ⟶ C) (v : Γ(C, ⊤)ˣ) (z : A) :
    gm r z ⊤ (Units.map (g.appTop.hom : Γ(C, ⊤) →* Γ(B, ⊤)) v) = gm (r ≫ g) z ⊤ v := by
  rw [gm_top, gm_top (r ≫ g)]
  congr 1

theorem eq_one_of_even [ConnectedSpace S] [Module.Free ℤ X] (u : Γ((splitTorus S X).left, ⊤)ˣ)
    (h₃ : ∀ (Z : Over S) (x y w : Z ⟶ splitTorus S X) (z : Z.left),
      gm (x * y * w).left z ⊤ u * gm x.left z ⊤ u * gm y.left z ⊤ u * gm w.left z ⊤ u =
        gm (x * y).left z ⊤ u * gm (x * w).left z ⊤ u * gm (y * w).left z ⊤ u)
    (h₁ : ∀ (Z : Over S) (z : Z.left), gm (1 : Z ⟶ splitTorus S X).left z ⊤ u = 1)
    (he : ∀ (Z : Over S) (x : Z ⟶ splitTorus S X) (z : Z.left), gm (x⁻¹).left z ⊤ u = gm x.left z ⊤ u) : u = 1 := by
  haveI : ConnectedSpace (splitTorus S X).left := connectedSpace_torus
  haveI hS : ConnectedSpace (𝟙_ (Over S)).left := ‹ConnectedSpace S›

  obtain ⟨ρ, hρ⟩ : ∃ ρ : Γ((splitTorus S X ⊗ splitTorus S X).left, ⊤)ˣ, ∀ (Z : Over S) (x y : Z ⟶ splitTorus S X)
      (z : Z.left), gm (lift x y).left z ⊤ ρ = gm (x * y).left z ⊤ u * (gm x.left z ⊤ u)⁻¹ * (gm y.left z ⊤ u)⁻¹ := by
    refine ⟨Units.map ((fst (splitTorus S X) (splitTorus S X) * snd _ _).left.appTop.hom :
        Γ((splitTorus S X).left, ⊤) →* Γ((splitTorus S X ⊗ splitTorus S X).left, ⊤)) u *
      (Units.map ((fst (splitTorus S X) (splitTorus S X)).left.appTop.hom :
        Γ((splitTorus S X).left, ⊤) →* Γ((splitTorus S X ⊗ splitTorus S X).left, ⊤)) u)⁻¹ *
      (Units.map ((snd (splitTorus S X) (splitTorus S X)).left.appTop.hom :
        Γ((splitTorus S X).left, ⊤) →* Γ((splitTorus S X ⊗ splitTorus S X).left, ⊤)) u)⁻¹, fun Z x y z => ?_⟩
    rw [map_mul, map_mul, map_inv, map_inv, gm_units_map_global_eq_gm_comp, gm_units_map_global_eq_gm_comp, gm_units_map_global_eq_gm_comp, ← Over.comp_left,
      ← Over.comp_left, ← Over.comp_left, MonObj.comp_mul, lift_fst, lift_snd]
  have hmulρ : ∀ (Z : Over S) (t t' y : Z ⟶ splitTorus S X) (z : Z.left),
      gm (lift (t * t') y).left z ⊤ ρ = gm (lift t y).left z ⊤ ρ * gm (lift t' y).left z ⊤ ρ := by
    intro Z t t' y z
    rw [hρ, hρ, hρ]
    have alg : ∀ a b c d e f g : (Z.left.presheaf.stalk z)ˣ, a * b * c * d = e * f * g →
        a * e⁻¹ * d⁻¹ = f * b⁻¹ * d⁻¹ * (g * c⁻¹ * d⁻¹) := by
      intro a b c d e f g h
      have ha : a = e * f * g * b⁻¹ * c⁻¹ * d⁻¹ := by
        calc a = a * (b * b⁻¹) * (c * c⁻¹) * (d * d⁻¹) := by simp
          _ = a * b * c * d * b⁻¹ * c⁻¹ * d⁻¹ := by ac_rfl
          _ = e * f * g * b⁻¹ * c⁻¹ * d⁻¹ := by rw [h]
      rw [ha]
      calc e * f * g * b⁻¹ * c⁻¹ * d⁻¹ * e⁻¹ * d⁻¹ = f * b⁻¹ * d⁻¹ * (g * c⁻¹ * d⁻¹) * (e * e⁻¹) := by ac_rfl
        _ = f * b⁻¹ * d⁻¹ * (g * c⁻¹ * d⁻¹) := by simp
    exact alg _ _ _ _ _ _ _ (h₃ Z t t' y z)
  have honeρ : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (z : Z.left),
      gm (lift t (1 : Z ⟶ splitTorus S X)).left z ⊤ ρ = 1 := by
    intro Z t z
    rw [hρ, _root_.mul_one, h₁ Z z, inv_one, _root_.mul_one, _root_.mul_inv_cancel]

  have hmul : ∀ (Z : Over S) (x y : Z ⟶ splitTorus S X) (z : Z.left),
      gm (x * y).left z ⊤ u = gm x.left z ⊤ u * gm y.left z ⊤ u := by
    intro Z x y z
    have e := eq_one_of_mul ρ hmulρ honeρ Z x y z
    rw [hρ] at e
    calc gm (x * y).left z ⊤ u
        = gm (x * y).left z ⊤ u * (gm x.left z ⊤ u)⁻¹ * (gm y.left z ⊤ u)⁻¹ * (gm y.left z ⊤ u * gm x.left z ⊤ u) := by
          group
      _ = gm x.left z ⊤ u * gm y.left z ⊤ u := by rw [e, _root_.one_mul, _root_.mul_comm]

  have germ : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ 𝟙_ (Over S)) (z : Z.left),
      gm (lift t y).left z ⊤ (Units.map ((fst (splitTorus S X) (𝟙_ (Over S))).left.appTop.hom :
        Γ((splitTorus S X).left, ⊤) →* Γ((splitTorus S X ⊗ 𝟙_ (Over S)).left, ⊤)) u) = gm t.left z ⊤ u := by
    intro Z t y z
    rw [gm_units_map_global_eq_gm_comp, ← Over.comp_left, lift_fst]
  obtain ⟨ψ, hψ, -⟩ := existsUnique_char (Y := 𝟙_ (Over S)) (Units.map ((fst (splitTorus S X) (𝟙_ (Over S))).left.appTop.hom :
        Γ((splitTorus S X).left, ⊤) →* Γ((splitTorus S X ⊗ 𝟙_ (Over S)).left, ⊤)) u)
    (fun Z t t' y z => by rw [germ, germ, germ]; exact hmul Z t t' z)
  have hψ' : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (z : Z.left), gm t.left z ⊤ u = gm (𝟙 Z.left) z ⊤ (chV t ψ) :=
    fun Z t z => by rw [← germ Z t (toUnit Z) z]; exact hψ Z t (toUnit Z) z

  have two : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X), chV t (ψ + ψ) = 1 := by
    intro Z t
    apply global_units_ext_of_gm_id_eq
    intro z
    have e1 : gm (t⁻¹).left z ⊤ u = (gm t.left z ⊤ u)⁻¹ := by rw [hψ' Z t⁻¹ z, hψ' Z t z, chV_inv, map_inv]
    rw [chV_add, map_mul, map_one, ← hψ' Z t z]
    nth_rewrite 1 [← he Z t z]
    rw [e1, _root_.inv_mul_cancel]
  obtain ⟨χ₀, -, h₀⟩ := existsUnique_char (Y := 𝟙_ (Over S)) (1 : Γ((splitTorus S X ⊗ 𝟙_ (Over S)).left, ⊤)ˣ)
    (fun Z t t' y z => by simp)
  have e0 := h₀ 0 (fun Z t y z => by rw [chV_zero, map_one, map_one])
  have e2 := h₀ (ψ + ψ) (fun Z t y z => by rw [two Z t, map_one, map_one])
  have h2 : (2 : ℤ) • ψ = 0 := by rw [two_smul]; exact e2.trans e0.symm
  have hψ0 : ψ = 0 := (smul_eq_zero.mp h2).resolve_left two_ne_zero
  apply global_units_ext_of_gm_id_eq
  intro z
  have e := hψ' (splitTorus S X) (𝟙 _) z
  rw [Over.id_left, hψ0, chV_zero] at e
  exact e

section
variable {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] (i : H ⟶ G)

theorem prod_cubTriv {T : Over S} (x : T ⟶ H) {U : Type} [CommGroup U] (h : (T.left ⟶ G.left) → U) :
    ∏ k : Fin 2, h (x.left ≫ ![i.left, (1 : H ⟶ G).left] k) ^ (![1, -1] : Fin 2 → ℤ) k =
      h (x ≫ i).left * (h (1 : T ⟶ G).left)⁻¹ := by
  rw [Fin.prod_univ_two]
  simp [← Over.comp_left]

theorem prod_biTriv {T : Over S} (t : T ⟶ H) (x : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ G.left) → U) :
    ∏ k : Fin 4, h ((lift t x).left ≫ lamφ i k) ^ Oε k =
      h ((t ≫ i) * x).left * (h (t ≫ i).left)⁻¹ * (h x.left)⁻¹ * h (1 : T ⟶ G).left := by
  have e1 : (lift t x).left ≫ ((fst H G ≫ i) * snd H G).left = ((t ≫ i) * x).left := by
    rw [← Over.comp_left, MonObj.comp_mul, lift_fst_assoc, lift_snd]
  have e2 : (lift t x).left ≫ (fst H G ≫ i).left = (t ≫ i).left := by
    rw [← Over.comp_left, lift_fst_assoc]
  have e3 : (lift t x).left ≫ (snd H G).left = x.left := by
    rw [← Over.comp_left, lift_snd]
  have e4 : (lift t x).left ≫ (1 : H ⊗ G ⟶ G).left = (1 : T ⟶ G).left := by
    rw [← Over.comp_left, MonObj.comp_one]
  rw [Fin.prod_univ_four]
  change h ((lift t x).left ≫ ((fst H G ≫ i) * snd H G).left) ^ (1 : ℤ) *
      h ((lift t x).left ≫ (fst H G ≫ i).left) ^ (-1 : ℤ) * h ((lift t x).left ≫ (snd H G).left) ^ (-1 : ℤ) *
      h ((lift t x).left ≫ (1 : H ⊗ G ⟶ G).left) ^ (1 : ℤ) = _
  rw [e1, e2, e3, e4]
  simp only [zpow_one, zpow_neg]

variable {i} [IsMonHom i] {L : RigLB G} {c : CubicalStr G L}

theorem exists_unit_delta (s : BiTriv c i) (σ : CubTriv c i) : ∃ a : Γ((H ⊗ H).left, ⊤)ˣ,
    ∀ (T : Over S) (t t' : T ⟶ H) (z : T.left) (J), Good L.L z J → val σ.s (t * t').left z J =
      gm (lift t t').left z ⊤ a * (val s.s (lift t (t' ≫ i)).left z J * val σ.s t.left z J * val σ.s t'.left z J) := by
  classical
  have hu := ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen L.L _ _ σ.s σ.gen (fst H H * snd H H).left
  have hu' := ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen L.L _ _ _ _ _ _
    (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen L.L _ _ _ _ _ _
      (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen L.L _ _ s.s s.gen (lift (fst H H) (snd H H ≫ i)).left)
      (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen L.L _ _ σ.s σ.gen (fst H H).left))
    (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen L.L _ _ σ.s σ.gen (snd H H).left)
  obtain ⟨a, ha⟩ := GlobalTheory.TorusCoord.exists_ratio L.isLB (fun U _ h => by
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
    rw [prod_cubTriv i (fst H H * snd H H) h, prod_biTriv i (fst H H) (snd H H ≫ i) h,
      prod_cubTriv i (fst H H) h, prod_cubTriv i (snd H H) h, MonObj.mul_comp]
    have key : ∀ A F N O : U, A * O⁻¹ = A * F⁻¹ * N⁻¹ * O * (F * O⁻¹) * (N * O⁻¹) := fun A F N O => by
      calc A * O⁻¹ = A * O⁻¹ * (F * F⁻¹) * (N * N⁻¹) * (O * O⁻¹) := by simp
        _ = A * F⁻¹ * N⁻¹ * O * (F * O⁻¹) * (N * O⁻¹) := by ac_rfl
    exact key _ _ _ _) _ hu _ hu'
  refine ⟨a, fun T t t' z J hJ => ?_⟩
  have key := ha T.left (lift t t').left z J hJ
  rw [val_pull hJ, val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, val_pull hJ] at key
  have e1 : (lift t t').left ≫ (fst H H * snd H H).left = (t * t').left := by
    rw [← Over.comp_left, MonObj.comp_mul, lift_fst, lift_snd]
  have e2 : (lift t t').left ≫ (lift (fst H H) (snd H H ≫ i)).left = (lift t (t' ≫ i)).left := by
    rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc]
  have e3 : (lift t t').left ≫ (fst H H).left = t.left := by rw [← Over.comp_left, lift_fst]
  have e4 : (lift t t').left ≫ (snd H H).left = t'.left := by rw [← Over.comp_left, lift_snd]
  rw [e1, e2, e3, e4] at key
  exact key

end

variable [ConnectedSpace S] [Module.Free ℤ X] {G : Over S} [GrpObj G] [IsCommMonObj G] {i : splitTorus S X ⟶ G}
  [IsMonHom i]

theorem val_mul_eq {L : RigLB G} {c : CubicalStr G L} (s : BiTriv c i) (σ : CubTriv c i) (T : Over S)
    (t t' : T ⟶ splitTorus S X) (z : T.left) (J) (hJ : Good L.L z J) : val σ.s (t * t').left z J =
      val s.s (lift t (t' ≫ i)).left z J * val σ.s t.left z J * val σ.s t'.left z J := by
  haveI : ConnectedSpace (splitTorus S X).left := connectedSpace_torus
  obtain ⟨a, ha⟩ := exists_unit_delta s σ
  have hmul : ∀ (Z : Over S) (t₁ t₂ y : Z ⟶ splitTorus S X) (z : Z.left),
      gm (lift (t₁ * t₂) y).left z ⊤ a = gm (lift t₁ y).left z ⊤ a * gm (lift t₂ y).left z ⊤ a := by
    intro Z t₁ t₂ y z
    obtain ⟨J, hJ⟩ := exists_good_pt L.isLB z
    have h1 := ha Z (t₁ * t₂) y z J hJ
    have h2 := ha Z t₁ y z J hJ
    have h3 := ha Z t₂ y z J hJ
    have hc := σ.cub Z t₁ t₂ y z J hJ
    have hl := s.law1 Z t₁ t₂ (y ≫ i) z J hJ
    have alg : ∀ A A₁ A₂ C s₁ s₂ P Q R Y : (Z.left.presheaf.stalk z)ˣ,
        A * (C * s₁ * s₂ * P * Y) * Q * R * Y = C * P * (A₁ * (s₁ * Q * Y)) * (A₂ * (s₂ * R * Y)) → A = A₁ * A₂ := by
      intro A A₁ A₂ C s₁ s₂ P Q R Y h
      apply mul_right_cancel (b := C * s₁ * s₂ * P * Y * Q * R * Y)
      calc A * (C * s₁ * s₂ * P * Y * Q * R * Y) = A * (C * s₁ * s₂ * P * Y) * Q * R * Y := by ac_rfl
        _ = C * P * (A₁ * (s₁ * Q * Y)) * (A₂ * (s₂ * R * Y)) := h
        _ = A₁ * A₂ * (C * s₁ * s₂ * P * Y * Q * R * Y) := by ac_rfl
    rw [h1, h2, h3, hl] at hc
    exact alg _ _ _ _ _ _ _ _ _ _ hc
  have hone : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (z : Z.left),
      gm (lift t (1 : Z ⟶ splitTorus S X)).left z ⊤ a = 1 := by
    intro Z t z
    obtain ⟨J, hJ⟩ := exists_good_pt L.isLB z
    have h1 := ha Z t 1 z J hJ
    rw [_root_.mul_one, MonObj.one_comp, BiTriv.val_one_right s hJ, CubTriv.val_one σ hJ, _root_.one_mul,
      _root_.mul_one] at h1
    calc _ = gm (lift t (1 : Z ⟶ splitTorus S X)).left z ⊤ a * val σ.s t.left z J * (val σ.s t.left z J)⁻¹ := by group
      _ = 1 := by rw [← h1, _root_.mul_inv_cancel]
  rw [ha T t t' z J hJ, eq_one_of_mul a hmul hone T t t' z, _root_.one_mul]

theorem eq_of_even {P : CP G} {σ σ' : CubTriv P.c i} (h : σ.Even) (h' : σ'.Even) : σ = σ' := by
  classical
  obtain ⟨u, hu⟩ := GlobalTheory.TorusCoord.exists_ratio P.L.isLB (fun U _ h => rfl) σ.s σ.gen σ'.s σ'.gen
  have h3 : ∀ (Z : Over S) (x y w : Z ⟶ splitTorus S X) (z : Z.left),
      gm (x * y * w).left z ⊤ u * gm x.left z ⊤ u * gm y.left z ⊤ u * gm w.left z ⊤ u =
        gm (x * y).left z ⊤ u * gm (x * w).left z ⊤ u * gm (y * w).left z ⊤ u := by
    intro Z x y w z
    obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB z
    have hc := σ.cub Z x y w z J hJ
    have hc' := σ'.cub Z x y w z J hJ
    simp only [hu Z.left _ z J hJ] at hc
    have alg : ∀ a b c d e f g S₁ S₂ S₃ S₄ C S₅ S₆ S₇ : (Z.left.presheaf.stalk z)ˣ,
        a * S₁ * (b * S₂) * (c * S₃) * (d * S₄) = C * (e * S₅) * (f * S₆) * (g * S₇) →
        S₁ * S₂ * S₃ * S₄ = C * S₅ * S₆ * S₇ → a * b * c * d = e * f * g := by
      intro a b c d e f g S₁ S₂ S₃ S₄ C S₅ S₆ S₇ h h'
      apply mul_right_cancel (b := S₁ * S₂ * S₃ * S₄)
      calc a * b * c * d * (S₁ * S₂ * S₃ * S₄) = a * S₁ * (b * S₂) * (c * S₃) * (d * S₄) := by ac_rfl
        _ = C * (e * S₅) * (f * S₆) * (g * S₇) := h
        _ = e * f * g * (C * S₅ * S₆ * S₇) := by ac_rfl
        _ = e * f * g * (S₁ * S₂ * S₃ * S₄) := by rw [h']
    exact alg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hc'
  have h1 : ∀ (Z : Over S) (z : Z.left), gm (1 : Z ⟶ splitTorus S X).left z ⊤ u = 1 := by
    intro Z z
    obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB z
    have e := hu Z.left (1 : Z ⟶ splitTorus S X).left z J hJ
    rw [CubTriv.val_one σ hJ, CubTriv.val_one σ' hJ, _root_.mul_one] at e
    exact e.symm
  have he : ∀ (Z : Over S) (x : Z ⟶ splitTorus S X) (z : Z.left), gm (x⁻¹).left z ⊤ u = gm x.left z ⊤ u := by
    intro Z x z
    obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB z
    have e := h Z x z J hJ
    have e' := h' Z x z J hJ
    rw [hu Z.left _ z J hJ, hu Z.left _ z J hJ, e'] at e
    apply mul_right_cancel (b := val P.sym (x ≫ i).left z J * val σ'.s x.left z J)
    exact e.trans (by ac_rfl)
  have hu1 := eq_one_of_even u h3 h1 he
  have hs : σ.s = σ'.s := GlobalTheory.TorusCoord.gen_eq_of_corr P.L.isLB σ.gen σ'.gen (corr_of_val P.L.isLB fun y J hJ => by
    rw [hu _ _ y J hJ, hu1, map_one, _root_.one_mul])
  obtain ⟨s₁, g₁, c₁⟩ := σ
  obtain ⟨s₂, g₂, c₂⟩ := σ'
  cases hs
  rfl

theorem cubTriv_delta_and_even_unique : (∀ (S : Scheme.{0}) [ConnectedSpace S] (X : Type) [AddCommGroup X] [Module.Free ℤ X] (G : Over S) [GrpObj G] [IsCommMonObj G] (P : CP G) (i : splitTorus S X ⟶ G), IsMonHom i → (∀ (s : BiTriv P.c i) (σ : CubTriv P.c i) (T : Over S) (t t' : T ⟶ splitTorus S X) (z : T.left) (J), Good P.L.L z J → val σ.s (t * t').left z J = val s.s (lift t (t' ≫ i)).left z J * val σ.s t.left z J * val σ.s t'.left z J) ∧ ∀ σ σ' : CubTriv P.c i, σ.Even → σ'.Even → σ = σ') := by
  intro S _ X _ _ G _ _ P i hi
  exact ⟨fun s σ T t t' z J hJ => val_mul_eq s σ T t t' z J hJ, fun σ σ' h h' => eq_of_even h h'⟩

end GlobalTheory.CubTrivTorus
