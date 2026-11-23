import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisInvariantFunctionsFlatBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveCubeBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCubicalSymmetricExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubeDescendsAlongEtaleIsogeny
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.SymDesc

open GlobalTheory.CechPic

theorem exists_gen_of_invariant {X Y Y' : Scheme.{0}} {K : Type} [Fintype K] {L : LB X} (hL : L.IsLB) (π : Y' ⟶ Y)
    {Γ₀ : Type} (act : Γ₀ → (Y' ⟶ Y')) (hact : ∀ σ, act σ ≫ π = π)
    (H : ∀ V : Y.Opens, Function.Injective (π.app V).hom ∧ ∀ u : Γ(Y', π ⁻¹ᵁ V),
      (∀ σ (h : π ⁻¹ᵁ V ≤ act σ ⁻¹ᵁ (π ⁻¹ᵁ V)), ((act σ).appLE _ _ h).hom u = u) → u ∈ Set.range (π.app V).hom)
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (u : LB.Gen (LB.LinComb L (fun k => π ≫ φ k) ε)) (hu : u.IsGen)
    (h : ∀ σ (z : Y') (J), Good L z J → val u (act σ) z J = val u (𝟙 Y') z J) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen := by
  have le : ∀ j : K → L.ι, π ⁻¹ᵁ LB.wchart L φ j ≤ LB.wchart L (fun k => π ≫ φ k) j :=
    fun j y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have inv : ∀ (j : K → L.ι) σ (h₁ : π ⁻¹ᵁ LB.wchart L φ j ≤ act σ ⁻¹ᵁ (π ⁻¹ᵁ LB.wchart L φ j)),
      ((act σ).appLE _ _ h₁).hom (res (le j) (u.s j)).val = (res (le j) (u.s j)).val := by
    intro j σ h₁
    refine fn_ext fun z hz => ?_
    have hz' : act σ z ∈ π ⁻¹ᵁ LB.wchart L φ j := h₁ hz
    have e₀ : gs (𝟙 Y') z _ (((act σ).appLE _ _ h₁).hom (res (le j) (u.s j)).val) =
        gs (act σ) z _ (res (le j) (u.s j)).val := by
      have := (gs_res (𝟙 Y') z h₁ hz (((act σ).app _).hom (res (le j) (u.s j)).val)).trans
        (gs_pull (𝟙 Y') (act σ) z _ hz' _)
      rw [Category.id_comp] at this
      exact this
    rw [e₀, gs_unit (act σ) z _ hz', gs_unit (𝟙 Y') _ _ hz]
    choose I hI using fun χ : Y' ⟶ X => exists_chart hL (χ z)
    have c₁ := gen_trans hu (act σ) z (le j hz') (Good.mem hI _ (act σ))
    have c₂ := gen_trans hu (𝟙 Y') z (le j hz) (Good.mem hI _ (𝟙 Y'))
    have c₃ : trF (fun k => π ≫ φ k) ε (act σ) z j (fun k => I (act σ ≫ π ≫ φ k)) =
        trF (fun k => π ≫ φ k) ε (𝟙 Y') z j (fun k => I (𝟙 Y' ≫ π ≫ φ k)) := by
      refine Finset.prod_congr rfl fun k _ => ?_
      have : act σ ≫ π ≫ φ k = 𝟙 Y' ≫ π ≫ φ k := by rw [reassoc_of% hact σ, Category.id_comp]
      show gm (act σ ≫ π ≫ φ k) z (L.U (j k) ⊓ L.U (I (act σ ≫ π ≫ φ k))) (L.g (j k) (I (act σ ≫ π ≫ φ k))) ^ _ =
        gm (𝟙 Y' ≫ π ≫ φ k) z (L.U (j k) ⊓ L.U (I (𝟙 Y' ≫ π ≫ φ k))) (L.g (j k) (I (𝟙 Y' ≫ π ≫ φ k))) ^ _
      rw [this]
    exact congrArg Units.val ((gm_res (act σ) z (le j) hz' _).trans
      ((c₁.trans ((congrArg₂ (· * ·) c₃ (h σ z I hI)).trans c₂.symm)).trans
        (gm_res (𝟙 Y') z (le j) hz _).symm))
  have desc : ∀ j : K → L.ι, ∃ a : Γ(Y, LB.wchart L φ j)ˣ, pullU π _ a = res (le j) (u.s j) := by
    intro j
    obtain ⟨a, ha⟩ := (H _).2 _ (inv j)
    obtain ⟨b, hb⟩ := (H _).2 (res (le j) (u.s j))⁻¹.val (fun σ h₁ => by
      refine (Units.mul_left_inj (res (le j) (u.s j))).1 ?_
      rw [Units.inv_mul]
      conv_lhs => rw [← inv j σ h₁]
      rw [← map_mul, Units.inv_mul, map_one])
    have ab : a * b = 1 := (H _).1 (by rw [map_mul, ha, hb, Units.mul_inv, map_one])
    exact ⟨⟨a, b, ab, (mul_comm b a).trans ab⟩, Units.ext ha⟩
  choose a ha using desc
  have hv : ∀ j (Z : Scheme.{0}) (r : Z ⟶ Y') (y : Z), π (r y) ∈ LB.wchart L φ j →
      gm (r ≫ π) y (LB.wchart L φ j) (a j) = gm r y (LB.wchart L (fun k => π ≫ φ k) j) (u.s j) := by
    intro j Z r y hy
    exact (gm_pull r π y _ hy _).symm.trans ((congrArg (gm r y _) (ha j)).trans (gm_res r y (le j) hy _))
  refine ⟨⟨a⟩, fun j j' => Units.ext ((H (LB.wchart L φ j ⊓ LB.wchart L φ j')).1 ?_)⟩
  refine congrArg Units.val (unit_ext (a := pullU π _ _) (b := pullU π _ _) fun y hy => ?_)
  have hy' : π y ∈ LB.wchart L φ j ⊓ LB.wchart L φ j' := hy
  refine (gm_pull (𝟙 Y') π y _ hy' _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') π y _ hy' _).symm)
  refine ((gm_res (𝟙 Y' ≫ π) y _ hy' _).trans ((hv j _ _ y hy'.1).trans
    (gen_trans hu (𝟙 Y') y (le j hy'.1) (le j' hy'.2)))).trans (Eq.symm ?_)
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_linComb L φ ε (𝟙 Y' ≫ π) y j j' hy'.1 hy'.2).trans ?_)
    ((gm_res (𝟙 Y' ≫ π) y _ hy' _).trans (hv j' _ _ y hy'.2)))
  simp only [trF, Category.id_comp]

theorem isSymmetric_of_exists_gen {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G)
    (t : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) (ht : t.IsGen) :
    L.IsSymmetric := by
  have e₂ : eSec G ≫ (ι[G]).left = eSec G := by
    rw [eSec, ← Over.comp_left, GrpObj.one_inv]
  have z := (cls_eq_zero_iff (LB.isLB_linComb L.isLB _ _)).2 ⟨t, ht⟩
  rw [cls_linComb L.isLB, Fin.sum_univ_two] at z
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, pull_id, ← sub_eq_add_neg,
    sub_eq_zero] at z
  have he : eSec G ≫ (ι[G]).left = 𝟙 _ ≫ eSec G := e₂.trans (Category.id_comp _).symm
  exact ⟨he, Unif.RigidifyIso.exists_rigidified_iso S S (𝟙 S) G G _ he L L
    ((cls_eq_iff L.isLB (pull_isLB L.isLB _)).1 z.symm)⟩

theorem exists_sym_pull {S S' : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {G' : Over S'} [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {β : G'.left ⟶ G.left} (gp : IsGrpPullback G' G f β) {L : LB G.left} (hL : L.IsLB)
    {L' : LB G'.left} (hL' : L'.IsLB) (hiso : LBIso L' (L.pull β))
    (s : LB.Gen (LB.LinComb L' (K := Fin 2) ![(ι[G']).left, 𝟙 G'.left] ![1, -1])) (hs : s.IsGen)
    (hr : LB.Gen.Corr L' _ _ _ _ (LB.pullGen L' _ _ s (eSec G')) (LB.oneGen L')) :
    ∃ u : LB.Gen (LB.LinComb L (fun k : Fin 2 => β ≫ ![(ι[G]).left, 𝟙 G.left] k) ![1, -1]), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over S')).left) (z : Z) (I), Good L z I → val u (r ≫ eSec G') z I = 1 := by
  obtain ⟨w, hw⟩ := hiso
  have hp := (isGen_iff w).1 hw
  have hι : (ι[G']).left ≫ β = β ≫ (ι[G]).left := by
    have e := congrArg (fun q => q.left) (map_inv (pushHom gp G') (𝟙 G'))
    simp only [Hom.inv_def, Category.id_comp] at e
    refine e.trans ?_
    show (𝟙 _ ≫ β) ≫ _ = _
    rw [Category.id_comp]
  have e₁ : eSec G' ≫ (ι[G']).left = eSec G' := by
    rw [eSec, ← Over.comp_left, GrpObj.one_inv]
  have hc : ∀ k : Fin 2, ![(ι[G']).left, 𝟙 G'.left] k ≫ β = β ≫ ![(ι[G]).left, 𝟙 G.left] k := fun k => by
    fin_cases k
    · exact hι
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨t₁, ht₁, v₁⟩ := exists_up hp hL hL' s hs
  obtain ⟨u, hu, vu⟩ := exists_gen hL (φ' := fun k : Fin 2 => β ≫ ![(ι[G]).left, 𝟙 G.left] k) (ε' := ![1, -1])
    (fun U _ h => Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ (![1, -1] : Fin 2 → ℤ) k) (hc k)) t₁ ht₁
  refine ⟨u, hu, fun Z r z I hI => ?_⟩
  choose J hJ using fun χ : Z ⟶ G'.left => exists_chart hL' (χ z)
  rw [vu Z _ z I hI, val_of t₁ _ z I (fun k => I (((r ≫ eSec G') ≫ ![(ι[G']).left, 𝟙 G'.left] k) ≫ β))
    (fun k => congrArg I (Category.assoc _ _ _).symm)]
  refine (v₁ Z (r ≫ eSec G') z _ _ (Set.mem_iInter.2 fun k => hI (((r ≫ eSec G') ≫ ![(ι[G']).left, 𝟙 G'.left] k) ≫ β))
    (Good.mem hJ _ _)).trans ?_
  have h1 : val s (r ≫ eSec G') z J = 1 :=
    (val_pull hJ s (eSec G') r).symm.trans ((val_corr hJ hr r).trans (val_one _))
  refine (congrArg₂ (· * ·) ?_ h1).trans (_root_.mul_one 1)
  have k : ∀ (V : Type) [CommGroup V] (q : (Z ⟶ G'.left) → V),
      ∏ k : Fin 2, q ((r ≫ eSec G') ≫ ![(ι[G']).left, 𝟙 G'.left] k) ^ (![1, -1] : Fin 2 → ℤ) k = 1 := by
    intro V _ q
    simp [Fin.prod_univ_two, e₁]
  exact k _ (fun q => gw w q z (I (q ≫ β)) (J q))

end GlobalTheory.Mum.SymDesc

namespace GlobalTheory.Mum

open SymDesc

theorem isSymmetric_of_pull_iso_unif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∀ (L : LB G.left) (hL : L.IsLB), LBIso U'.LG.L (L.pull β) → ∀ (rig : LB.Gen (L.pull (eSec G))) (hr : rig.IsGen), RigLB.IsSymmetric (⟨L, rig, hL, hr⟩ : RigLB G) := by
  intro R _ _ _ _ R' _ _ _ ρ hρ hg D D' hD A' G' _ _ _ U' a G _ _ β hG gp hβ L hL hiso rig hr
  obtain ⟨u, hu, h1⟩ := exists_sym_pull gp hL U'.LG.isLB hiso U'.symG U'.symG_gen U'.symG_rig
  have := U'.smooth
  have := hG.smooth
  have hsurj : Function.Surjective (pullback.snd G'.hom (jK R')).appTop.hom := by
    have hw : U'.gen.hom.left ≫ A'.A.hom = pullback.snd G'.hom (jK R') := Over.w U'.gen.hom
    have : IsIso U'.gen.hom.left := ((Over.forget _).mapIso U'.gen).isIso_hom
    have : IsIso U'.gen.hom.left.appTop := inferInstanceAs (IsIso (U'.gen.hom.left.app ⊤))
    rw [← hw]
    exact surj_comp (ConcreteCategory.bijective_of_isIso U'.gen.hom.left.appTop).2
      (GlobalTheory.SemiRigid.globalFns _ _ A'.isAb).2
  have he : eSec G' ≫ G'.hom = 𝟙 _ := Over.w η[G']
  obtain ⟨t, ht⟩ := exists_gen_of_invariant hL β a.act hβ
    (GlobalTheory.T.galois_invariant_functions_flat_baseChange R R' ρ hρ hg _ _ G.hom G'.hom β inferInstance gp.1 a.act hβ fun σ => (a.cart σ).1.w)
    _ _ u hu fun σ z J hJ => by
      have key := GlobalTheory.ValueForm.gen_unique_of_injective hL (φ := fun k : Fin 2 => a.act σ ≫ β ≫ ![(ι[G]).left, 𝟙 G.left] k)
        (fun V _ q => Finset.prod_congr rfl fun k _ => by
          dsimp only
          rw [reassoc_of% hβ σ])
        (pullback.fst G'.hom (jK R')) (GlobalTheory.ValueForm.app_generic_injective _) (pullback.snd _ _)
        (pullback.lift (jK R' ≫ eSec G') (𝟙 _) (by
          rw [Category.id_comp]
          exact (Category.assoc _ _ _).trans ((congrArg (jK R' ≫ ·) he).trans (Category.comp_id _))))
        (pullback.lift_snd _ _ _) hsurj (DVR.pullGen_isGen _ _ _ _ hu (a.act σ)) hu (fun y I hI => by
          rw [pullback.lift_fst]
          refine (val_pull hI _ _ _).trans (Eq.trans ?_ (h1 _ (jK R') y I hI).symm)
          have e : (jK R' ≫ eSec G') ≫ a.act σ = (jK R' ≫ (cubeMapOf (a.cart σ)).e) ≫ eSec G' :=
            (Category.assoc _ _ _).trans ((congrArg (jK R' ≫ ·) (cubeMapOf (a.cart σ)).e_comm).trans
              (Category.assoc _ _ _).symm)
          exact (congrArg (fun q => val u q y I) e).trans (h1 _ _ y I hI)) _ (𝟙 _) z J hJ
      have k₂ := (val_pull hJ u (a.act σ) (𝟙 _)).symm.trans key
      rwa [Category.id_comp] at k₂
  exact isSymmetric_of_exists_gen _ t ht

end GlobalTheory.Mum
