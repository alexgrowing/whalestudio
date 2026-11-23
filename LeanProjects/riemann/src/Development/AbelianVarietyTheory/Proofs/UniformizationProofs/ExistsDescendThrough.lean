import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitRatio
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubeDescendsAlongEtaleIsogeny
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubTrivDeltaAndEvenUnique
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsStalkHom

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.PackageDescent

section Descent

variable {X X' Y Y' Z : Scheme.{0}} {K : Type} [Fintype K]

theorem exists_gen_descend_val {L : LB X} (hL : L.IsLB) (π : Y' ⟶ Y) [Flat π] [Surjective π]
    [QuasiCompact π] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (u : LB.Gen (LB.LinComb L (fun k => π ≫ φ k) ε)) (hu : u.IsGen)
    (h : ∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ Y') (z : Z) (J), Good L z J → g₁ ≫ π = g₂ ≫ π →
      val u g₁ z J = val u g₂ z J) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J → val t (r ≫ π) z J = val u r z J := by
  have le : ∀ j : K → L.ι, π ⁻¹ᵁ LB.wchart L φ j ≤ LB.wchart L (fun k => π ≫ φ k) j :=
    fun j y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have desc : ∀ j : K → L.ι, ∃ a : Γ(Y, LB.wchart L φ j),
      (π.app _).hom a = (res (le j) (u.s j)).val := by
    intro j
    refine FunDescent.exists_app_eq π _ _ fun Z g₁ g₂ h₁ h₂ e => fn_ext fun z _ => ?_
    rw [CubeDescent.gs_appLE, CubeDescent.gs_appLE, gs_unit _ _ _ (h₁ (x := z) trivial),
      gs_unit _ _ _ (h₂ (x := z) trivial)]
    choose I hI using fun χ : Z ⟶ X => exists_chart hL (χ z)
    have c₁ := gen_trans hu g₁ z (le j (h₁ (x := z) trivial)) (Good.mem hI _ g₁)
    have c₂ := gen_trans hu g₂ z (le j (h₂ (x := z) trivial)) (Good.mem hI _ g₂)
    have c₃ : trF (fun k => π ≫ φ k) ε g₁ z j (fun k => I (g₁ ≫ π ≫ φ k)) =
        trF (fun k => π ≫ φ k) ε g₂ z j (fun k => I (g₂ ≫ π ≫ φ k)) := by
      refine Finset.prod_congr rfl fun k _ => ?_
      have : g₁ ≫ π ≫ φ k = g₂ ≫ π ≫ φ k := by rw [reassoc_of% e]
      show gm (g₁ ≫ π ≫ φ k) z (L.U (j k) ⊓ L.U (I (g₁ ≫ π ≫ φ k))) (L.g (j k) (I (g₁ ≫ π ≫ φ k))) ^ _ =
        gm (g₂ ≫ π ≫ φ k) z (L.U (j k) ⊓ L.U (I (g₂ ≫ π ≫ φ k))) (L.g (j k) (I (g₂ ≫ π ≫ φ k))) ^ _
      rw [this]
    exact congrArg Units.val ((gm_res g₁ z (le j) (h₁ (x := z) trivial) _).trans
      ((c₁.trans ((congrArg₂ (· * ·) c₃ (h Z g₁ g₂ z I hI e)).trans c₂.symm)).trans
        (gm_res g₂ z (le j) (h₂ (x := z) trivial) _).symm))
  choose a ha using desc
  have hun : ∀ j, IsUnit (a j) := fun j =>
    FunDescent.isUnit_of_isUnit_app π _ _ (ha j ▸ Units.isUnit _)
  have hv : ∀ j (Z : Scheme.{0}) (r : Z ⟶ Y') (y : Z), π (r y) ∈ LB.wchart L φ j →
      gm (r ≫ π) y (LB.wchart L φ j) (hun j).unit =
      gm r y (LB.wchart L (fun k => π ≫ φ k) j) (u.s j) := by
    intro j Z r y hy
    have e : pullU π _ (hun j).unit = res (le j) (u.s j) := Units.ext (ha j)
    exact (gm_pull r π y _ hy _).symm.trans ((congrArg (gm r y _) e).trans (gm_res r y (le j) hy _))
  refine ⟨⟨fun j => (hun j).unit⟩, fun j j' => Units.ext
    (FunDescent.app_injective π (LB.wchart L φ j ⊓ LB.wchart L φ j') ?_), fun Z r z J hJ => ?_⟩
  · refine congrArg Units.val (unit_ext (a := pullU π _ _) (b := pullU π _ _) fun y hy => ?_)
    have hy' : π y ∈ LB.wchart L φ j ⊓ LB.wchart L φ j' := hy
    refine (gm_pull (𝟙 Y') π y _ hy' _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') π y _ hy' _).symm)
    refine ((gm_res (𝟙 Y' ≫ π) y _ hy' _).trans ((hv j _ _ y hy'.1).trans
      (gen_trans hu (𝟙 Y') y (le j hy'.1) (le j' hy'.2)))).trans (Eq.symm ?_)
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_linComb L φ ε (𝟙 Y' ≫ π) y j j' hy'.1 hy'.2).trans ?_)
      ((gm_res (𝟙 Y' ≫ π) y _ hy' _).trans (hv j' _ _ y hy'.2)))
    simp only [trF, Category.id_comp]
  · rw [val_of _ (r ≫ π) z J (fun k => J (r ≫ π ≫ φ k)) (fun k => by rw [Category.assoc])]
    exact hv _ Z r z (Set.mem_iInter.2 fun k => hJ (r ≫ π ≫ φ k))

theorem exists_descend_through {M : LB X} {L : LB X'} {F : X' ⟶ X} {w : LB.Iso L (M.pull F)} (hw : PGen w)
    (hM : M.IsLB) (hL : L.IsLB) (π : Y' ⟶ Y) [Flat π] [Surjective π] [QuasiCompact π]
    {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} (hc : ∀ k, φ' k ≫ F = π ≫ φ k) {ε : K → ℤ}
    (a : LB.Gen (LB.LinComb L φ' ε)) (ha : a.IsGen)
    (h : ∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ Y') (z : Z) (I J), Good M z I → Good L z J → g₁ ≫ π = g₂ ≫ π →
      (∏ k, gw w (g₁ ≫ φ' k) z (I ((g₁ ≫ φ' k) ≫ F)) (J (g₁ ≫ φ' k)) ^ ε k) * val a g₁ z J =
      (∏ k, gw w (g₂ ≫ φ' k) z (I ((g₂ ≫ φ' k) ≫ F)) (J (g₂ ≫ φ' k)) ^ ε k) * val a g₂ z J) :
    ∃ t : LB.Gen (LB.LinComb M φ ε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (I J), Good M z I → Good L z J → val t (r ≫ π) z I =
        (∏ k, gw w (r ≫ φ' k) z (I ((r ≫ φ' k) ≫ F)) (J (r ≫ φ' k)) ^ ε k) * val a r z J := by
  obtain ⟨t₁, ht₁, v₁⟩ := exists_up hw hM hL a ha
  obtain ⟨u, hu, vu⟩ := exists_gen hM (φ' := fun k => π ≫ φ k) (ε' := ε)
    (fun U _ h => Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ ε k) (hc k)) t₁ ht₁
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (I J), Good M z I → Good L z J → val u r z I =
      (∏ k, gw w (r ≫ φ' k) z (I ((r ≫ φ' k) ≫ F)) (J (r ≫ φ' k)) ^ ε k) * val a r z J := by
    intro Z r z I J hI hJ
    rw [vu Z r z I hI, val_of t₁ r z I (fun k => I ((r ≫ φ' k) ≫ F)) (fun k => by rw [Category.assoc])]
    exact v₁ Z r z _ _ (Set.mem_iInter.2 fun k => hI ((r ≫ φ' k) ≫ F)) (hJ.mem φ' r)
  obtain ⟨t, ht, vt⟩ := exists_gen_descend_val hM π φ ε u hu fun Z g₁ g₂ z I hI e => by
    obtain ⟨J, hJ⟩ := exists_good_pt hL z
    rw [key Z g₁ z I J hI hJ, key Z g₂ z I J hI hJ, h Z g₁ g₂ z I J hI hJ e]
  exact ⟨t, ht, fun Z r z I J hI hJ => (vt Z r z I hI).trans (key Z r z I J hI hJ)⟩

theorem gm_comp (κ : Z ⟶ Y) (f : Y ⟶ X) (z : Z) (U : X.Opens) (h : f (κ z) ∈ U) (a : Γ(X, U)ˣ) :
    gm (κ ≫ f) z U a = Units.map (κ.stalkMap z).hom.toMonoidHom (gm f (κ z) U a) := by
  apply Units.ext
  rw [gm_val (κ ≫ f) z U h]
  show _ = (κ.stalkMap z).hom (gm f (κ z) U a).val
  rw [gm_val f (κ z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply κ (f ⁻¹ᵁ U) z h _).symm

theorem stalkMap_injective (r : Z ⟶ Y) [Flat r] (z : Z) : Function.Injective (r.stalkMap z).hom := by
  let _ := (r.stalkMap z).hom.toAlgebra
  have : Module.Flat (Y.presheaf.stalk (r z)) (Z.presheaf.stalk z) := Flat.stalkMap r z
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (r z)) (Z.presheaf.stalk z)) :=
    inferInstanceAs (IsLocalHom (r.stalkMap z).hom)
  have : Module.FaithfullyFlat (Y.presheaf.stalk (r z)) (Z.presheaf.stalk z) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (r z)) (Z.presheaf.stalk z)

theorem exists_val_cover {M : LB X} (hM : M.IsLB) (ρ : Z ⟶ Y) [Flat ρ] [Surjective ρ] (y : Y) (I) (hI : Good M y I) :
    ∃ (z : Z) (I' : _) (e : (Y.presheaf.stalk y)ˣ →* (Z.presheaf.stalk z)ˣ), Good M z I' ∧ Function.Injective e ∧
      ∀ {W : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (W ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb M φ ε))
        (r : Y ⟶ W), val t (ρ ≫ r) z I' = e (val t r y I) := by
  obtain ⟨z, rfl⟩ := ρ.surjective y
  have : Epi ρ := Flat.epi_of_flat_of_surjective ρ
  obtain ⟨I', hI', e⟩ := exists_good M hM z (fun ψ : Y ⟶ X => ρ ≫ ψ) I
    (fun a b h => congrArg I ((cancel_epi ρ).1 h)) (fun ψ => hI ψ)
  refine ⟨z, I', Units.map (ρ.stalkMap z).hom.toMonoidHom, hI',
    Units.map_injective (stalkMap_injective ρ z), fun {W K} _ {φ ε} t r => ?_⟩
  rw [val_of t (ρ ≫ r) z I' (fun k => I (r ≫ φ k)) (fun k => by rw [Category.assoc]; exact e _)]
  exact gm_comp ρ r z _ (hI.mem φ r) _

end Descent

section Action

variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] {i : H ⟶ G}

theorem exists_action {L : RigLB G} {c : CubicalStr G L} (s : BiTriv c i) (σ : CubTriv c i) :
    ∃ a : LB.Gen (LB.LinComb L.L (K := Fin 2) ![((fst H G ≫ i) * snd H G).left, (snd H G).left] ![1, -1]), a.IsGen ∧
      ∀ (T : Over S) (t : T ⟶ H) (x : T ⟶ G) (z : T.left) (J), Good L.L z J →
        val a (lift t x).left z J = val s.s (lift t x).left z J * val σ.s t.left z J := by
  obtain ⟨a, ha, va⟩ := exists_gen L.isLB (φ' := ![((fst H G ≫ i) * snd H G).left, (snd H G).left]) (ε' := ![1, -1])
    (fun U _ h => by
      have e : (fst H G).left ≫ (1 : H ⟶ G).left = (1 : H ⊗ G ⟶ G).left := by
        rw [← Over.comp_left, MonObj.comp_one]
      rw [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_two, Fin.prod_univ_two]
      show h ((fst H G ≫ i) * snd H G).left ^ (1 : ℤ) * h (fst H G ≫ i).left ^ (-1 : ℤ) * h (snd H G).left ^ (-1 : ℤ) *
        h (1 : H ⊗ G ⟶ G).left ^ (1 : ℤ) * (h (fst H G ≫ i).left ^ (1 : ℤ) *
          h ((fst H G).left ≫ (1 : H ⟶ G).left) ^ (-1 : ℤ)) =
        h ((fst H G ≫ i) * snd H G).left ^ (1 : ℤ) * h (snd H G).left ^ (-1 : ℤ)
      rw [e]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L.L _ _ _ _ s.s (LB.pullGen L.L _ _ σ.s (fst H G).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ s.gen (DVR.pullGen_isGen _ _ _ _ σ.gen _))
  refine ⟨a, ha, fun T t x z J hJ => ?_⟩
  rw [va _ _ z J hJ, val_mul hJ, val_pull hJ, ← Over.comp_left, lift_fst]

omit [GrpObj H] in

theorem prod_lam {T : Over S} (t : T ⟶ H) (x : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ G.left) → U) :
    ∏ k : Fin 4, h ((lift t x).left ≫ lamφ i k) ^ Oε k =
      h ((t ≫ i) * x).left * (h (t ≫ i).left)⁻¹ * (h x.left)⁻¹ * h (1 : T ⟶ G).left := by
  rw [Fin.prod_univ_four]
  show h (lift t x ≫ ((fst H G ≫ i) * snd H G)).left ^ (1 : ℤ) * h (lift t x ≫ fst H G ≫ i).left ^ (-1 : ℤ) *
    h (lift t x ≫ snd H G).left ^ (-1 : ℤ) * h (lift t x ≫ (1 : H ⊗ G ⟶ G)).left ^ (1 : ℤ) = _
  rw [MonObj.comp_mul, MonObj.comp_one, lift_fst_assoc, lift_snd, zpow_one, zpow_one, zpow_neg_one, zpow_neg_one]

theorem exists_biTriv_inv [IsCommMonObj H] [IsMonHom i] {P : CP G} (s : BiTriv P.c i) :
    ∃ s' : BiTriv P.c i, ∀ (T : Over S) (t : T ⟶ H) (x : T ⟶ G) (z : T.left) (J), Good P.L.L z J →
      val s'.s (lift t x).left z J = val s.s (lift t⁻¹ x⁻¹).left z J * val P.sym (t ≫ i).left z J *
        val P.sym x.left z J * (val P.sym ((t ≫ i) * x).left z J)⁻¹ := by
  let sy := fun p : H ⊗ G ⟶ G => LB.pullGen P.L.L _ _ P.sym p.left
  have gs : ∀ p, (sy p).IsGen := fun p => DVR.pullGen_isGen _ _ _ _ P.sym_gen _
  obtain ⟨a, ha, va⟩ := exists_gen P.L.isLB (φ' := lamφ i) (ε' := Oε)
    (fun U _ h => by
      refine (DVR.prod_sum₂ (K := (Fin 4 ⊕ Fin 2) ⊕ Fin 2) (K' := Fin 2) (U := U) _
        (DVR.prod_sum₂ (K := Fin 4 ⊕ Fin 2) (K' := Fin 2) (U := U) _
          (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 2) (U := U) _ (prod_lam (fst H G)⁻¹ (snd H G)⁻¹ h)
            (prod_sym (fst H G ≫ i) h)) (prod_sym (snd H G) h))
          (c' := (h (((fst H G ≫ i) * snd H G)⁻¹).left * (h ((fst H G ≫ i) * snd H G).left)⁻¹)⁻¹) ?_).trans ?_
      · rw [← prod_sym, ← Finset.prod_inv_distrib]
        exact Finset.prod_congr rfl fun k _ => zpow_neg _ _
      · have e := prod_lam (i := i) (fst H G) (snd H G) h
        rw [lift_fst_snd, Over.id_left] at e
        simp only [Category.id_comp] at e
        rw [e, GrpObj.inv_comp, ← mul_inv]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel)
    (LB.mulGen P.L.L _ _ _ _ (LB.mulGen P.L.L _ _ _ _ (LB.mulGen P.L.L _ _ _ _
      (LB.pullGen P.L.L _ _ s.s (lift (fst H G)⁻¹ (snd H G)⁻¹).left) (sy (fst H G ≫ i))) (sy (snd H G)))
      (LB.invGen P.L.L _ _ (sy ((fst H G ≫ i) * snd H G))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.pullGen_isGen _ _ _ _ s.gen _) (gs _)) (gs _)) (DVR.invGen_isGen _ _ _ _ (gs _)))
  have v : ∀ (T : Over S) (t : T ⟶ H) (x : T ⟶ G) (z : T.left) (J), Good P.L.L z J →
      val a (lift t x).left z J = val s.s (lift t⁻¹ x⁻¹).left z J * val P.sym (t ≫ i).left z J *
        val P.sym x.left z J * (val P.sym ((t ≫ i) * x).left z J)⁻¹ := by
    intro T t x z J hJ
    rw [va _ _ z J hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, val_pull hJ, val_pull hJ]
    simp only [← Over.comp_left, comp_lift, GrpObj.comp_inv, MonObj.comp_mul, lift_fst, lift_snd, lift_fst_assoc]
  refine ⟨⟨a, ha, fun T t t' x z J hJ => ?_, fun T t x x' z J hJ => ?_⟩, v⟩
  · have e := P.sym_cub T (t ≫ i) (t' ≫ i) x z J hJ
    rw [v _ _ _ z J hJ, v _ _ _ z J hJ, v _ _ _ z J hJ, mul_inv, s.law1 _ _ _ _ z J hJ, GrpObj.inv_comp,
      GrpObj.inv_comp, MonObj.mul_comp]
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'
  · have e := P.sym_cub T (t ≫ i) x x' z J hJ
    rw [v _ _ _ z J hJ, v _ _ _ z J hJ, v _ _ _ z J hJ, mul_inv, s.law2 _ _ _ _ z J hJ, GrpObj.inv_comp,
      ← _root_.mul_assoc (t ≫ i)]
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'

end Action

section Package

variable {S : Scheme.{0}} {G B : Over S} (q : G ⟶ B) [Flat q.left] [Surjective q.left]

theorem exists_lift_cover {T : Over S} (x : T ⟶ B) :
    ∃ (T' : Over S) (ρ : T' ⟶ T) (x' : T' ⟶ G), Flat ρ.left ∧ Surjective ρ.left ∧ x' ≫ q = ρ ≫ x := by
  refine ⟨Over.mk (pullback.fst x.left q.left ≫ T.hom), Over.homMk (pullback.fst x.left q.left) rfl,
    Over.homMk (pullback.snd x.left q.left) ?_, ?_, ?_, Over.OverMorphism.ext pullback.condition.symm⟩
  · show _ = pullback.fst x.left q.left ≫ T.hom
    rw [← Over.w q, ← Over.w x, pullback.condition_assoc]
  · show Flat (pullback.fst x.left q.left); infer_instance
  · show Surjective (pullback.fst x.left q.left); infer_instance

theorem exists_lift_cover₄ {T : Over S} (x y u v : T ⟶ B) :
    ∃ (T' : Over S) (ρ : T' ⟶ T) (x' y' u' v' : T' ⟶ G), Flat ρ.left ∧ Surjective ρ.left ∧ x' ≫ q = ρ ≫ x ∧
      y' ≫ q = ρ ≫ y ∧ u' ≫ q = ρ ≫ u ∧ v' ≫ q = ρ ≫ v := by
  obtain ⟨T₁, ρ₁, x', _, _, e₁⟩ := exists_lift_cover q x
  obtain ⟨T₂, ρ₂, y', _, _, e₂⟩ := exists_lift_cover q (ρ₁ ≫ y)
  obtain ⟨T₃, ρ₃, u', _, _, e₃⟩ := exists_lift_cover q (ρ₂ ≫ ρ₁ ≫ u)
  obtain ⟨T₄, ρ₄, v', _, _, e₄⟩ := exists_lift_cover q (ρ₃ ≫ ρ₂ ≫ ρ₁ ≫ v)
  refine ⟨T₄, ρ₄ ≫ ρ₃ ≫ ρ₂ ≫ ρ₁, ρ₄ ≫ ρ₃ ≫ ρ₂ ≫ x', ρ₄ ≫ ρ₃ ≫ y', ρ₄ ≫ u', v', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Over.comp_left]; infer_instance
  · simp only [Over.comp_left]; infer_instance
  all_goals simp only [Category.assoc, e₁, e₂, e₃, e₄]

variable [GrpObj G] [IsCommMonObj G] [GrpObj B] [IsCommMonObj B] [IsMonHom q] [QuasiCompact q.left]

def isoV {L : LB G.left} {M : LB B.left} (w : LB.Iso L (M.pull q.left)) {T : Over S} (z : T.left)
    (I : (T.left ⟶ B.left) → M.ι) (J : (T.left ⟶ G.left) → L.ι) (x : T ⟶ G) : (T.left.presheaf.stalk z)ˣ :=
  gw w x.left z (I (x.left ≫ q.left)) (J x.left)

def diff₃ {A U : Type} [CommGroup A] [CommGroup U] (W : A → U) (a b d : A) : U :=
  W (a * b * d) * (W (a * b))⁻¹ * (W (a * d))⁻¹ * (W (b * d))⁻¹ * W a * W b * W d * (W 1)⁻¹

theorem diff₃_swap₁ {A U : Type} [CommGroup A] [CommGroup U] (W : A → U) (a b d : A) :
    diff₃ W a b d = diff₃ W b a d := by
  rw [diff₃, diff₃, mul_comm b a]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem diff₃_swap₂ {A U : Type} [CommGroup A] [CommGroup U] (W : A → U) (a b d : A) :
    diff₃ W a b d = diff₃ W a d b := by
  rw [diff₃, diff₃, mul_comm d b, mul_right_comm a d b]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_descent (P : CP G) {M : LB B.left} (hM : M.IsLB) (w : LB.Iso P.L.L (M.pull q.left)) (hw : w.IsGen)
    (hcub : ∀ (T : Over S) (z : T.left) (I J), Good M z I → Good P.L.L z J → ∀ x x' y u : T ⟶ G, x ≫ q = x' ≫ q →
      diff₃ (isoV q w z I J) x y u * cubV P.c z J x y u = diff₃ (isoV q w z I J) x' y u * cubV P.c z J x' y u)
    (hsym : ∀ (T : Over S) (z : T.left) (I J), Good M z I → Good P.L.L z J → ∀ x x' : T ⟶ G, x ≫ q = x' ≫ q →
      isoV q w z I J x⁻¹ * (isoV q w z I J x)⁻¹ * val P.sym x.left z J =
        isoV q w z I J x'⁻¹ * (isoV q w z I J x')⁻¹ * val P.sym x'.left z J)
    (hq : q.left ≫ B.hom = G.hom ≫ 𝟙 S) :
    ∃ (N : CP B) (w' : _), IsCPMap P N (𝟙 S) q.left hq w' := by
  have hp := (isGen_iff w).1 hw
  have hL := P.L.isLB
  let β : ∀ T : Over S, (T ⟶ G) →* (T ⟶ B) := fun T => MonoidHom.mk' (· ≫ q) fun a b => MonObj.mul_comp a b q

  have he : eSec G ≫ q.left = 𝟙 _ ≫ eSec B := by
    rw [Category.id_comp, eSec, eSec, ← Over.comp_left, IsMonHom.one_hom]
  obtain ⟨rig, hr, vr⟩ := exists_descend_through hp hM hL (𝟙 _) (K := PUnit) (φ' := fun _ => eSec G)
    (φ := fun _ => eSec B) (ε := fun _ => 1) (fun _ => he) P.L.rig P.L.rigGen fun Z g₁ g₂ z I J _ _ e => by
      rw [Category.comp_id, Category.comp_id] at e
      rw [e]

  have hc₂ : ∀ k : Fin 2, ![(ι[G]).left, 𝟙 G.left] k ≫ q.left = q.left ≫ ![(ι[B]).left, 𝟙 B.left] k := fun k => by
    fin_cases k
    · exact congrArg (fun q => q.left) (GrpObj.inv_hom q)
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  have ps : ∀ (T : Over S) (z : T.left) (I J) (x : T ⟶ G),
      (∏ k : Fin 2, gw w (x.left ≫ ![(ι[G]).left, 𝟙 G.left] k) z (I ((x.left ≫ ![(ι[G]).left, 𝟙 G.left] k) ≫ q.left))
        (J (x.left ≫ ![(ι[G]).left, 𝟙 G.left] k)) ^ (![1, -1] : Fin 2 → ℤ) k) * val P.sym x.left z J =
      isoV q w z I J x⁻¹ * (isoV q w z I J x)⁻¹ * val P.sym x.left z J := fun T z I J x =>
    congrArg₂ (· * ·) (prod_sym x (fun r => gw w r z (I (r ≫ q.left)) (J r))) rfl
  obtain ⟨s, hs, vs₀⟩ := exists_descend_through hp hM hL q.left hc₂ P.sym P.sym_gen fun Z g₁ g₂ z I J hI hJ e => by
    let T : Over S := Over.mk (g₂ ≫ G.hom)
    let k₂ : T ⟶ G := Over.homMk g₂ rfl
    let k₁ : T ⟶ G := Over.homMk g₁ (by
      change g₁ ≫ G.hom = g₂ ≫ G.hom
      rw [← Over.w q, reassoc_of% e])
    exact (ps T z I J k₁).trans ((hsym T z I J hI hJ k₁ k₂ (Over.OverMorphism.ext e)).trans (ps T z I J k₂).symm)
  have vs : ∀ (T : Over S) (z : T.left) (I J), Good M z I → Good P.L.L z J → ∀ x : T ⟶ G,
      val s (x ≫ q).left z I = isoV q w z I J x⁻¹ * (isoV q w z I J x)⁻¹ * val P.sym x.left z J :=
    fun T z I J hI hJ x => (vs₀ _ x.left z I J hI hJ).trans (ps T z I J x)

  have := AbelianQuotient.flat_tensorHom q q
  have := AbelianQuotient.surjective_tensorHom q q
  have := AbelianQuotient.quasiCompact_tensorHom q q
  have := AbelianQuotient.flat_tensorHom q (q ⊗ₘ q)
  have := AbelianQuotient.surjective_tensorHom q (q ⊗ₘ q)
  have := AbelianQuotient.quasiCompact_tensorHom q (q ⊗ₘ q)
  let π : G3 G ⟶ G3 B := q ⊗ₘ q ⊗ₘ q
  have hπ : ∀ {T : Over S} (x y u : T ⟶ G),
      lift x (lift y u) ≫ π = lift (x ≫ q) (lift (y ≫ q) (u ≫ q)) := fun x y w => by
    simp [π, lift_map]
  have hφ : ∀ I, thφ G (x3 G) I ≫ q.left = π.left ≫ thφ B (x3 B) I := fun I =>
    congrArg (fun q => q.left) ((psum_hom (β (G3 G)) (x3 G) I.down).trans
      ((congrArg (fun q => psum B q I.down) (funext fun i => by
        fin_cases i <;> simp [β, π, preHom, x3])).trans (psum_hom (preHom π) (x3 B) I.down).symm))
  have pc : ∀ (T : Over S) (z : T.left) (I J) (x y u : T ⟶ G),
      (∏ k, gw w ((lift x (lift y u)).left ≫ thφ G (x3 G) k) z
        (I (((lift x (lift y u)).left ≫ thφ G (x3 G) k) ≫ q.left)) (J ((lift x (lift y u)).left ≫ thφ G (x3 G) k)) ^
          thε k) * val (L := P.L.L) (φ := thφ G (x3 G)) (ε := thε) P.c.t (lift x (lift y u)).left z J =
      diff₃ (isoV q w z I J) x y u * cubV P.c z J x y u := fun T z I J x y u =>
    congrArg₂ (· * ·) (prod_cub x y u (fun r => gw w r z (I (r ≫ q.left)) (J r))) rfl
  obtain ⟨t, ht, vt₀⟩ := exists_descend_through hp hM hL π.left hφ (ε := thε) P.c.t P.c.isGen
    fun Z g₁ g₂ z I J hI hJ e => by
      let T : Over S := Over.mk (g₂ ≫ (G3 G).hom)
      let k₂ : T ⟶ G3 G := Over.homMk g₂ rfl
      let k₁ : T ⟶ G3 G := Over.homMk g₁ (by
        change g₁ ≫ (G3 G).hom = g₂ ≫ (G3 G).hom
        rw [← Over.w π, reassoc_of% e])
      have e' : k₁ ≫ π = k₂ ≫ π := Over.OverMorphism.ext e
      obtain ⟨x, y, u, h₁⟩ : ∃ x y u, k₁ = lift x (lift y u) :=
        ⟨k₁ ≫ fst _ _, k₁ ≫ snd _ _ ≫ fst _ _, k₁ ≫ snd _ _ ≫ snd _ _, by ext <;> simp⟩
      obtain ⟨x', y', u', h₂⟩ : ∃ x y u, k₂ = lift x (lift y u) :=
        ⟨k₂ ≫ fst _ _, k₂ ≫ snd _ _ ≫ fst _ _, k₂ ≫ snd _ _ ≫ snd _ _, by ext <;> simp⟩
      rw [h₁, h₂, hπ, hπ] at e'
      have ex : x ≫ q = x' ≫ q := by simpa using e' =≫ fst _ _
      have ey : y ≫ q = y' ≫ q := by simpa using e' =≫ snd _ _ ≫ fst _ _
      have eu : u ≫ q = u' ≫ q := by simpa using e' =≫ snd _ _ ≫ snd _ _
      have a₁ : g₁ = (lift x (lift y u)).left := congrArg (fun q => q.left) h₁
      have a₂ : g₂ = (lift x' (lift y' u')).left := congrArg (fun q => q.left) h₂
      have C := isCub_cubV P.c (T := T) hJ
      have s01 : ∀ a b d : T ⟶ G, diff₃ (isoV q w z I J) a b d * cubV P.c z J a b d =
          diff₃ (isoV q w z I J) b a d * cubV P.c z J b a d := fun a b d => by
        rw [C.s01 a, diff₃_swap₁ _ a]
      have s12 : ∀ a b d : T ⟶ G, diff₃ (isoV q w z I J) a b d * cubV P.c z J a b d =
          diff₃ (isoV q w z I J) a d b * cubV P.c z J a d b := fun a b d => by
        rw [C.s12 a, diff₃_swap₂ _ a]
      have key : diff₃ (isoV q w z I J) x y u * cubV P.c z J x y u =
          diff₃ (isoV q w z I J) x' y' u' * cubV P.c z J x' y' u' := by
        rw [hcub T z I J hI hJ x x' y u ex, s01, hcub T z I J hI hJ y y' x' u ey, s12, s01,
          hcub T z I J hI hJ u u' y' x' eu, s01, s12, s01]
      clear_value k₁ k₂
      have f := (pc T z I J x y u).trans (key.trans (pc T z I J x' y' u').symm)
      rw [← a₁, ← a₂] at f
      exact f
  let M₁ : RigLB B := ⟨M, rig, hM, hr⟩
  have vt : ∀ (T : Over S) (z : T.left) (I J), Good M z I → Good P.L.L z J → ∀ x y u : T ⟶ G,
      CubTransport.thV (L := M₁) t z I (x ≫ q) (y ≫ q) (u ≫ q) =
        diff₃ (isoV q w z I J) x y u * cubV P.c z J x y u := fun T z I J hI hJ x y u => by
    have e := (vt₀ _ (lift x (lift y u)).left z I J hI hJ).trans (pc T z I J x y u)
    rw [← Over.comp_left, hπ] at e
    exact e
  have vt' : ∀ (T : Over S) (z : T.left) (I J), Good M z I → Good P.L.L z J → ∀ x y u : T ⟶ G,
      cubV P.c z J x y u = diff₃ (fun a => (isoV q w z I J a)⁻¹) x y u *
        CubTransport.thV (L := M₁) t z I (x ≫ q) (y ≫ q) (u ≫ q) := fun T z I J hI hJ x y u => by
    rw [vt T z I J hI hJ, diff₃, diff₃]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have cover : ∀ (T : Over S) (z : T.left) (I), Good M z I → ∀ x y u v : T ⟶ B,
      ∃ (T' : Over S) (z' : T'.left) (I' : _) (J : _) (ρ : (T ⟶ B) →* (T' ⟶ B))
        (e : (T.left.presheaf.stalk z)ˣ →* (T'.left.presheaf.stalk z')ˣ) (x' y' u' v' : T' ⟶ G),
        Good M z' I' ∧ Good P.L.L z' J ∧ Function.Injective e ∧ ρ x = β _ x' ∧ ρ y = β _ y' ∧ ρ u = β _ u' ∧
        ρ v = β _ v' ∧ (∀ a b d, e (CubTransport.thV (L := M₁) t z I a b d) =
          CubTransport.thV (L := M₁) t z' I' (ρ a) (ρ b) (ρ d)) ∧
        ∀ a, e (val s a.left z I) = val s (ρ a).left z' I' := by
    intro T z I hI x y u v
    obtain ⟨T', ρ, x', y', u', v', _, _, e₁, e₂, e₃, e₄⟩ := exists_lift_cover₄ q x y u v
    obtain ⟨z', I', e, hI', ei, ev⟩ := exists_val_cover hM ρ.left z I hI
    obtain ⟨J, hJ⟩ := exists_good_pt hL z'
    refine ⟨T', z', I', J, preHom ρ, e, x', y', u', v', hI', hJ, ei, e₁.symm, e₂.symm, e₃.symm, e₄.symm,
      fun a b d => ?_, fun a => (ev s a.left).symm⟩
    refine (ev (φ := thφ B (x3 B)) (ε := thε) t (lift a (lift b d)).left).symm.trans ?_
    rw [← Over.comp_left, comp_lift, comp_lift]; rfl
  have up : ∀ (T : Over S) (z : T.left) (I J), Good M z I → Good P.L.L z J →
      IsCub (fun a b d : T ⟶ G => CubTransport.thV (L := M₁) t z I (β _ a) (β _ b) (β _ d)) :=
    fun T z I J hI hJ => CubTransport.isCub_of_twist (isCub_cubV P.c hJ) (MonoidHom.id _)
      (fun a => (isoV q w z I J a)⁻¹) (vt' T z I J hI hJ)
  let c : CubicalStr B M₁ := CubTransport.cubicalOfVal t ht fun T z I hI => by
    refine ⟨fun x y => ?_, fun x y u => ?_, fun x y u => ?_, fun x y u v => ?_⟩
    · obtain ⟨T', z', I', J, ρ, e, x', y', -, -, hI', hJ, ei, e₁, e₂, -, -, ec, -⟩ := cover T z I hI x y x x
      apply ei
      rw [ec, map_one, map_one, e₁, e₂, ← map_one (β T')]
      exact (up T' z' I' J hI' hJ).face x' y'
    · obtain ⟨T', z', I', J, ρ, e, x', y', u', -, hI', hJ, ei, e₁, e₂, e₃, -, ec, -⟩ := cover T z I hI x y u x
      apply ei
      rw [ec, ec, e₁, e₂, e₃]
      exact (up T' z' I' J hI' hJ).s01 x' y' u'
    · obtain ⟨T', z', I', J, ρ, e, x', y', u', -, hI', hJ, ei, e₁, e₂, e₃, -, ec, -⟩ := cover T z I hI x y u x
      apply ei
      rw [ec, ec, e₁, e₂, e₃]
      exact (up T' z' I' J hI' hJ).s12 x' y' u'
    · obtain ⟨T', z', I', J, ρ, e, x', y', u', v', hI', hJ, ei, e₁, e₂, e₃, e₄, ec, -⟩ := cover T z I hI x y u v
      apply ei
      rw [map_mul, map_mul, ec, ec, ec, ec, map_mul, map_mul, e₁, e₂, e₃, e₄, ← map_mul (β T'), ← map_mul (β T')]
      exact (up T' z' I' J hI' hJ).coc x' y' u' v'
  refine ⟨⟨M₁, c, s, hs, corr_of_val hM fun y I hI => ?_, fun T x y u z I hI => ?_⟩, w,
    toBase_mul_of_isMonHom q hq, hw, fun T z J I hJ hI W hW => ?_⟩
  · obtain ⟨J, hJ⟩ := exists_good_pt hL y
    have e := vs (𝟙_ _) y I J hI hJ 1
    rw [inv_one, mul_inv_cancel, _root_.one_mul, P.val_sym_one hJ, MonObj.one_comp, one_left] at e
    exact (val_pull hI _ _ _).trans (e.trans (val_one _).symm)
  · obtain ⟨T', z', I', J, ρ, e, x', y', u', -, hI', hJ, ei, e₁, e₂, e₃, -, ec, es⟩ := cover T z I hI x y u x
    apply ei
    have ec' : ∀ a b d, e (cubV c z I a b d) = CubTransport.thV (L := M₁) t z' I' (ρ a) (ρ b) (ρ d) := ec
    simp only [map_mul, ec', es, map_inv, e₁, e₂, e₃]
    simp only [← map_mul, ← map_inv]
    exact sym_cub_alg (MonoidHom.id _) (fun a => (isoV q w z' I' J a)⁻¹) (θ := cubV P.c z' J)
      (θ' := fun a b d => CubTransport.thV (L := M₁) t z' I' (β _ a) (β _ b) (β _ d))
      (σ := fun a => val P.sym a.left z' J) (σ' := fun a => val s (β _ a).left z' I') (vt' T' z' I' J hI' hJ)
      (fun a => by
        refine Eq.trans ?_ (congrArg (_ * ·) (vs T' z' I' J hI' hJ a)).symm
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, MonoidHom.id_apply]
        abel) (P.sym_cub T' x' y' u' z' J hJ)
  · obtain rfl : W = isoV q w z I J := funext hW
    refine ⟨?_, fun x => ?_, fun x y u => ?_⟩
    · have e := vr _ T.hom z I J hI hJ
      rw [Fintype.prod_unique, zpow_one, ← one_left] at e
      exact e
    · refine (congrArg (· * _) (vs T z I J hI hJ x)).trans ?_
      rw [mul_right_comm, inv_mul_cancel_right]
    · let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
      have e : ∀ a : T ⟶ G, toBase hq a = ρ ≫ a ≫ q := fun a => Over.OverMorphism.ext (Category.id_comp _).symm
      have e' : (lift (toBase hq x) (lift (toBase hq y) (toBase hq u))).left =
          (lift (x ≫ q) (lift (y ≫ q) (u ≫ q))).left := by
        rw [e, e, e, ← comp_lift, ← comp_lift]; exact Category.id_comp _
      exact cub_alg ((congrArg (fun r => val (L := M) (φ := thφ B (x3 B)) (ε := thε) t r z I) e').trans
        (vt T z I J hI hJ x y u))

end Package

end GlobalTheory.UU.PackageDescent

namespace GlobalTheory.UU
open PackageDescent

theorem nonempty_desc : ∀ (S : Scheme.{0}) [ConnectedSpace S] (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (G : Over S) [GrpObj G] [IsCommMonObj G] [ConnectedSpace G.left] (Q : TQ G X) (P : CP G),
    Nonempty (BiTriv P.c Q.i) → (∃ σ : CubTriv P.c Q.i, σ.Even) → Nonempty (Q.Desc P) := by
  intro S _ X _ _ _ G _ _ _ Q P ⟨s⟩ ⟨σ, hσ⟩
  have := Q.q_hom
  have := Q.i_hom
  have := Q.q_flat
  have := Q.q_surj
  have := Q.q_affine
  obtain ⟨a, ha, va⟩ := exists_action s σ
  obtain ⟨M, w, hM, hw, hv⟩ := GlobalTheory.EquivDesc.main S X G Q P.L.L P.L.isLB a ha fun T t t' x z J hJ => by
    rw [va _ _ _ z J hJ, va _ _ _ z J hJ, va _ _ _ z J hJ, (GlobalTheory.CubTrivTorus.cubTriv_delta_and_even_unique S X G P Q.i Q.i_hom).1 s σ T t t' z J hJ,
      s.law1 _ _ _ _ z J hJ, s.law2 _ _ _ _ z J hJ]
    ac_rfl
  have ker : ∀ {T : Over S} (x x' : T ⟶ G), x ≫ Q.q = x' ≫ Q.q → ∃ t : T ⟶ splitTorus S X, x = (t ≫ Q.i) * x' := by
    intro T x x' e
    have h : (x * x'⁻¹) ≫ Q.q = toUnit T ≫ η[Q.B] := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, e, mul_inv_cancel]
      rfl
    exact ⟨Q.isKernel.lift _ _ h, by rw [Q.isKernel.lift_fst, inv_mul_cancel_right]⟩
  have tr : ∀ (T : Over S) (z : T.left) (I J), Good M z I → Good P.L.L z J → ∀ (t : T ⟶ splitTorus S X) (x : T ⟶ G),
      isoV Q.q w z I J ((t ≫ Q.i) * x) * (val s.s (lift t x).left z J * val σ.s t.left z J) = isoV Q.q w z I J x := by
    intro T z I J hI hJ t x
    have e : ((t ≫ Q.i) * x).left ≫ Q.q.left = x.left ≫ Q.q.left := by
      rw [← Over.comp_left, ← Over.comp_left, MonObj.mul_comp, Category.assoc, Q.isKernel.w, ← Category.assoc,
        toUnit_unique (t ≫ toUnit _) (toUnit T), ← Hom.one_def, _root_.one_mul]
    rw [isoV, isoV, e, ← va T t x z J hJ]
    exact hv T t x z J _ hJ (hI (x.left ≫ Q.q.left))
  obtain ⟨s', vs'⟩ := exists_biTriv_inv s
  obtain rfl : s = s' := biTriv_unique S X G P.L P.c Q.i Q.i_hom s s'
  obtain ⟨N, w', h⟩ := exists_descent Q.q P hM w hw (fun T z I J hI hJ x x' y u e => by
      obtain ⟨t, rfl⟩ := ker x x' e
      have a₁ := tr T z I J hI hJ t (x' * y * u)
      have a₂ := tr T z I J hI hJ t (x' * y)
      have a₃ := tr T z I J hI hJ t (x' * u)
      have a₄ := tr T z I J hI hJ t x'
      have b₁ := s.law2 T t (x' * y) u z J hJ
      have b₂ := s.law2 T t x' u z J hJ
      have C := isCub_cubV P.c hJ
      have b₃ := C.coc (t ≫ Q.i) x' y u
      simp only [diff₃, _root_.mul_assoc (t ≫ Q.i)]
      apply Additive.ofMul.injective
      have E := fun {p q : (T.left.presheaf.stalk z)ˣ} (e : p = q) => congrArg Additive.ofMul e
      replace a₁ := E a₁; replace a₂ := E a₂; replace a₃ := E a₃; replace a₄ := E a₄
      replace b₁ := E b₁; replace b₂ := E b₂; replace b₃ := E b₃
      simp only [ofMul_mul, ofMul_inv] at a₁ a₂ a₃ a₄ b₁ b₂ b₃ ⊢
      linear_combination (norm := abel) a₁ - a₂ - a₃ + a₄ - b₁ + b₂ + b₃)
    (fun T z I J hI hJ x x' e => by
      obtain ⟨t, rfl⟩ := ker x x' e
      have a₁ := tr T z I J hI hJ t⁻¹ x'⁻¹
      have a₂ := tr T z I J hI hJ t x'
      have b₁ := vs' T t x' z J hJ
      have b₂ := hσ T t z J hJ
      rw [GrpObj.inv_comp, ← mul_inv] at a₁
      apply Additive.ofMul.injective
      have E := fun {p q : (T.left.presheaf.stalk z)ˣ} (e : p = q) => congrArg Additive.ofMul e
      replace a₁ := E a₁; replace a₂ := E a₂; replace b₁ := E b₁; replace b₂ := E b₂
      simp only [ofMul_mul, ofMul_inv] at a₁ a₂ b₁ b₂ ⊢
      linear_combination (norm := abel) a₁ - a₂ + b₁ - b₂)
    (by simp)
  exact ⟨⟨N, w', h⟩⟩

end GlobalTheory.UU
end
