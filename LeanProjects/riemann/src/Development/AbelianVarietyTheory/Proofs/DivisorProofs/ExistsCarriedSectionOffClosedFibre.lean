import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecCarriedOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupPullbackTripleProductMapLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorOffClosedFibreDescended
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarriedSectionNonzeroNearClosedFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open CubeCarried

theorem exists_secOver_of_gen {X : Scheme.{0}} (L : LB X) (W : X.Opens) (g : W.toScheme ⟶ X) (hg : g = W.ι)
    (t : LB.Gen (L.pull g)) (ht : t.IsGen) :
    ∃ s : ∀ k, Γ(X, W ⊓ L.U k), IsSecOver L W s ∧
      (∀ (z : X) (k : L.ι), z ∈ W → z ∈ L.U k → IsUnit (gs (𝟙 X) z (W ⊓ L.U k) (s k))) ∧
      ∀ (f : X ⟶ X) (w : LB.Iso L (L.pull f)), W ≤ f ⁻¹ᵁ W →
        (∀ (Z : Scheme.{0}) (r r' : Z ⟶ W) (z : Z) (j k : L.ι), r' ≫ W.ι = (r ≫ W.ι) ≫ f →
          g (r' z) ∈ L.U j → g (r z) ∈ L.U k →
          gm r' z ((L.pull g).U (fun _ => j)) (t.s (fun _ => j)) =
            gw w (r ≫ g) z j k * gm r z ((L.pull g).U (fun _ => k)) (t.s (fun _ => k))) →
        SecCarriedOver L W s f w := by
  subst hg
  obtain ⟨s, hs⟩ := exists_sec_of_gen L W t
  have inj : ∀ z : W.toScheme, Function.Injective (W.ι.stalkMap z).hom := fun z =>
    (ConcreteCategory.bijective_of_isIso (W.ι.stalkMap z)).1
  have v : ∀ (z : W.toScheme) (k : L.ι), W.ι z ∈ L.U k →
      (W.ι.stalkMap z).hom (gs (𝟙 X) (W.ι z) (W ⊓ L.U k) (s k)) =
        (gm (𝟙 _) z ((L.pull W.ι).U (fun _ => k)) (t.s (fun _ => k))).val := fun z k hk => by
    rw [← gs_eq_map_gs W.ι z _ (show W.ι z ∈ W ⊓ L.U k from ⟨z.2, hk⟩), ← hs _ (𝟙 _) z k hk, Category.id_comp]
  refine ⟨s, fun z k k' hz hk hk' => ?_, fun z k hz hk => ?_, fun f w hf H z j k hz hfz hk hj => ?_⟩
  · obtain ⟨z, rfl⟩ : ∃ z' : W.toScheme, W.ι z' = z := ⟨⟨z, hz⟩, rfl⟩
    apply inj z
    rw [map_mul, v z k hk, v z k' hk', ← gm_val_map W.ι z (L.U k ⊓ L.U k') ⟨hk, hk'⟩, ← Units.val_mul]
    congr 1
    refine (gen_trans ht (𝟙 _) z (j := fun _ => k) (j' := fun _ => k') (mem_pull.2 hk) (mem_pull.2 hk')).trans ?_
    rw [trF, Fintype.prod_unique, zpow_one, Category.id_comp]
    rfl
  · obtain ⟨z, rfl⟩ : ∃ z' : W.toScheme, W.ι z' = z := ⟨⟨z, hz⟩, rfl⟩
    refine (isUnit_map_iff (W.ι.stalkMap z).hom _).1 ?_
    rw [v z k hk]
    exact Units.isUnit _
  · obtain ⟨z, rfl⟩ : ∃ z' : W.toScheme, W.ι z' = z := ⟨⟨z, hz⟩, rfl⟩
    apply inj z
    have hr : f.resLE W W hf ≫ W.ι = (𝟙 _ ≫ W.ι) ≫ f := by simp
    have hj' : W.ι (f.resLE W W hf z) ∈ L.U j := by
      rw [← Scheme.Hom.comp_apply, hr]; exact hj
    have e := congrArg Units.val (H _ (𝟙 _) (f.resLE W W hf) z j k hr hj' hk)
    rw [← hs _ _ z j hj', hr, Category.id_comp, Units.val_mul] at e
    rw [map_mul, v z k hk, ← CubeCarried.gs_comp W.ι f z (W ⊓ L.U j) ⟨hfz, hj⟩, e]
    exact congrArg₂ (· * ·) (gm_val_map W.ι z ((L.pull f).U (fun _ => j) ⊓ L.U k) ⟨mem_pull.2 hj, hk⟩ _) rfl

set_option maxHeartbeats 1000000 in

theorem exists_carried_sec_off_closed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β), ∀ y : G.left, G.hom y ≠ closedPoint R → ∃ V : G.left.Opens, y ∈ V ∧ ∃ s : ∀ k : U'.LG.L.ι, Γ(G'.left, β ⁻¹ᵁ V ⊓ U'.LG.L.U k), IsSecOver U'.LG.L (β ⁻¹ᵁ V) s ∧ (∀ (z : G'.left) (k : U'.LG.L.ι), β z = y → z ∈ U'.LG.L.U k → IsUnit (gs (𝟙 G'.left) z (β ⁻¹ᵁ V ⊓ U'.LG.L.U k) (s k))) ∧ ∀ σ : Gal ρ, ∃ (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ ∧ ∃ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h ∧ SecCarriedOver U'.LG.L (β ⁻¹ᵁ V) s _ (Classical.choose hP.lg) := by
  intro R _ _ _ hB R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hact y hy
  obtain ⟨θ, hθ, O, hO, hnz⟩ := GlobalTheory.T.exists_carried_section_nonzero_near_closedFibre R hB R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hact
  have := hB.1.1
  have hfin : IsFinite (spMap ρ) := (IsFinite.SpecMap_iff _).2 hF.2.2
  have hβf : IsFinite β := MorphismProperty.of_isPullback (P := @IsFinite) hβ.1.flip hfin
  let O' : G.left.Opens := ⟨farSet β θ, isOpen_farSet β β.isClosedMap θ⟩
  have hO' : ∃ g ∈ O', G.hom g = closedPoint R := by
    obtain ⟨g, hg, hgc⟩ := hO
    refine ⟨g, fun g' hg' => ?_, hgc⟩
    subst hg'
    exact hnz g' hg hgc
  obtain ⟨p, q, c, h⟩ := OffClosed.exists_ten R hB.1.2.2.2 G hS O' hO' y hy
  let V : G.left.Opens := ⟨⋂ f ∈ {f | f ∈ cubeTen (𝟙 G) p q c}, ((f.left ⁻¹ᵁ O' : G.left.Opens) : Set G.left),
    (List.finite_toSet _).isOpen_biInter fun f _ => (f.left ⁻¹ᵁ O').isOpen⟩
  have hyV : y ∈ V := Set.mem_iInter₂.2 h
  refine ⟨V, hyV, ?_⟩
  obtain ⟨hl, hm⟩ := grpPullback_points_lift_mul_inv _ _ (spMap ρ) G G' β hβ G' G β hβ.1.w
  obtain ⟨a', ha⟩ := hl p
  obtain ⟨b', hb⟩ := hl q
  obtain ⟨c', hc⟩ := hl c
  have h1 : (𝟙 G' : G' ⟶ G').left ≫ β = β ≫ (𝟙 G : G ⟶ G).left := by simp
  have mul := fun u v u' v' hu hv => (hm u v u' v' hu hv).1
  have inv := fun u u' hu => (hm u u u' u' hu hu).2
  have hten : ∀ f' ∈ cubeTen (𝟙 G') a' b' c', ∃ f ∈ cubeTen (𝟙 G) p q c, f'.left ≫ β = β ≫ f.left := by
    intro f' hf
    simp only [cubeTen, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 ha⟩
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 (inv _ _ ha)⟩
    · exact ⟨_, by simp [cubeTen], ha⟩
    · exact ⟨_, by simp [cubeTen], inv _ _ ha⟩
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 hb⟩
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 hc⟩
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 (inv _ _ (mul _ _ _ _ hb hc))⟩
    · exact ⟨_, by simp [cubeTen], hb⟩
    · exact ⟨_, by simp [cubeTen], hc⟩
    · exact ⟨_, by simp [cubeTen], inv _ _ (mul _ _ _ _ hb hc)⟩
  choose hd bc hbc hP hov using a.unif
  let F : Gal ρ → (G'.left ⟶ G'.left) := fun σ => (bc σ).hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))
  have hFa : ∀ σ, F σ = a.act σ := hbc
  have hFc : ∀ σ, IsGrpPullback G' G' (spMap (Gal.hom σ)) (F σ) := fun σ => (hFa σ).symm ▸ a.cart σ
  have hFβ : ∀ σ, F σ ≫ β = β := fun σ => by rw [hFa, hact]
  let w : ∀ σ, LB.Iso U'.LG.L (U'.LG.L.pull (F σ)) := fun σ => Classical.choose (hP σ).lg
  have hw : ∀ σ, (w σ).IsGen := fun σ => (Classical.choose_spec (hP σ).lg).1
  have hrig : ∀ σ, PMaps (w σ) (K := PUnit) (fun _ => eSec G') (fun _ => eSec G') (fun _ => 1) U'.LG.rig U'.LG.rig
      (spMap (Gal.hom σ)) := fun σ => by
    obtain ⟨he, hr, -⟩ := (Classical.choose_spec (hP σ).lg).2
    exact (maps_iff (w σ) _ (fun _ => eSec G') _ U'.LG.rig U'.LG.rig (spMap (Gal.hom σ)) _
      (rigPull_le (F σ) (spMap (Gal.hom σ)) he U'.LG.L) (fun _ => rfl)).1 hr
  have comm : ∀ (u : G ⟶ G) (u' : G' ⟶ G'), u'.left ≫ β = β ≫ u.left → ∀ σ, u'.left ≫ F σ = F σ ≫ u'.left := by
    intro u u' hu σ
    have e₁ := hFβ σ
    have e₂ := (hFc σ).1.w
    generalize F σ = f at e₁ e₂ ⊢
    apply hβ.1.hom_ext
    · rw [Category.assoc, e₁, Category.assoc, hu, ← Category.assoc, e₁]
    · rw [Category.assoc, Category.assoc, Over.w, e₂, ← Category.assoc, Over.w]
  obtain ⟨t, ht, hcar⟩ := exists_gen_carried U'.cubG hFc w hrig
    (fun σ => pmaps_cub R' _ D' A' G' U'.toUnifPre (hFc σ) (w σ) (hw σ)) θ
    (fun σ => hθ σ (hd σ) (bc σ) (hbc σ) (hP σ) (hov σ)) G' F (fun σ => (hFc σ).1.w) (𝟙 G') a' b' c'
    (comm _ _ h1) (comm _ _ ha) (comm _ _ hb) (comm _ _ hc) (β ⁻¹ᵁ V) (by
      intro f' hf' g hg
      obtain ⟨f, hf, e⟩ := hten f' hf'
      have h2 : f.left (β g) ∈ farSet β θ := Set.mem_iInter₂.1 hg f hf
      refine h2 (f'.left g) ?_
      rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply])
  obtain ⟨s, hs, hu, hcs⟩ := exists_secOver_of_gen U'.LG.L (β ⁻¹ᵁ V) _ (by simp) t ht
  refine ⟨s, hs, fun z k hz hk => hu z k (show β z ∈ V from hz ▸ hyV) hk, fun σ =>
    ⟨hd σ, bc σ, hbc σ, hP σ, hov σ, hcs (F σ) (w σ) (fun z hz => ?_) (hcar σ)⟩⟩
  show (F σ ≫ β) z ∈ V
  rw [hFβ]
  exact hz

end GlobalTheory.Mum
