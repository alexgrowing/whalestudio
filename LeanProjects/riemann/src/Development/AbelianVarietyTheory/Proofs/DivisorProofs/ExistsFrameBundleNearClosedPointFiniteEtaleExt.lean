import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCarriedAlong
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleSectionOfSmoothClosedFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackPointsLiftMulInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorDescendedBundleNearClosedPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarriedFrameTheoremOfCubeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedGaloisLinearisationCarriesRigidificatiStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

set_option maxHeartbeats 1000000 in

theorem exists_carried_frame_upstairs : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β) (θ : U'.LG.L.Sec), (∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → SecCarried U'.LG.L θ _ (Classical.choose hP.lg)) → ∀ O : G.left.Opens, (∃ g ∈ O, G.hom g = closedPoint R) → (∀ g' : G'.left, β g' ∈ O → G.hom (β g') = closedPoint R → g' ∈ secNz θ) → ∀ y : G.left, IsClosed ({y} : Set G.left) → G.hom y = closedPoint R → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ₁ : R →+* R₁), FinExt ρ₁ ∧ ρ₁.Etale ∧ ∃ V₀ : G.left.Opens, y ∈ V₀ ∧ ∃ τ : ∀ k : U'.LG.L.ι, Γ(pullback (G'.hom ≫ spMap ρ) (spMap ρ₁), (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀) ⊓ (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ U'.LG.L.U k)ˣ, FrameAlong U'.LG.L (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ((pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀)) τ ∧ (∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → ∀ f' : (pullback (G'.hom ≫ spMap ρ) (spMap ρ₁) : Scheme.{0}) ⟶ pullback (G'.hom ≫ spMap ρ) (spMap ρ₁), f' ≫ (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) = (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ≫ a.act σ → f' ≫ (pullback.snd (G'.hom ≫ spMap ρ) (spMap ρ₁)) = (pullback.snd (G'.hom ≫ spMap ρ) (spMap ρ₁)) → FrameCarriedAlong U'.LG.L (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ((pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀)) τ _ (Classical.choose hP.lg) f') := by
  intro R _ _ _ hB R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hact θ hθ O hO hOθ y hyc hy
  have hR : AdmBase R (maximalIdeal R) := hB.1
  have hN : IsNoetherianRing R := hR.1
  have hI : IsIntegrallyClosed R := hR.2.2.1
  have := hS.smooth
  have hρf : IsFinite (spMap ρ) := (IsFinite.SpecMap_iff (CommRingCat.ofHom ρ)).2 hF.2.2
  have hβf : IsFinite β := MorphismProperty.of_isPullback hβ.1.flip hρf
  have hgi : GeometricallyIrreducible G.hom :=
    ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun Ω _ s => GlobalTheory.T.irreducibleSpace_fibre_semiAbelian_fieldPoint _ G hS Ω s⟩
  have s₂ : Smooth (G ⊗ G).hom := inferInstanceAs (Smooth (pullback.fst G.hom G.hom ≫ G.hom))
  have i₂ : GeometricallyIrreducible (G ⊗ G).hom := GeometricallyIrreducible.comp (pullback.fst G.hom G.hom) G.hom
  have s₃ : Smooth (G ⊗ G ⊗ G).hom := inferInstanceAs (Smooth (pullback.fst G.hom (G ⊗ G).hom ≫ G.hom))
  have i₃ : GeometricallyIrreducible (G ⊗ G ⊗ G).hom :=
    GeometricallyIrreducible.comp (pullback.fst G.hom (G ⊗ G).hom) G.hom
  let O' : G.left.Opens := ⟨farSet β θ, isOpen_farSet β β.isClosedMap θ⟩
  obtain ⟨g, hgO, hg⟩ := hO
  have hgO' : g ∈ O' := fun g' e => by
    subst e
    exact hOθ g' hgO hg
  have hfin : IsFinite (G.left.fromSpecResidueField y ≫ G.hom) :=
    ClosedPt.isFinite_fromSpec G.hom y hyc (by rw [hy]; exact isClosed_singleton_closedPoint R)
  obtain ⟨N, hN₁, hN₂⟩ := ClosedPt.exists_open_good G.hom (G ⊗ G ⊗ G).hom y (ClosedPt.ten G)
    (fun f => f.left ⁻¹ᵁ O') fun f hf => by
      obtain ⟨q, h₁, h₂⟩ := ClosedPt.ten_meets G y g (hy.trans hg.symm) f hf
      exact ⟨q, show f.left q ∈ O' from h₁ ▸ hgO', h₂⟩
  rw [hy] at hN₁
  obtain ⟨R₁, _, _, _, ρ₁, t, hρ₁, het, ht, htN⟩ := GlobalTheory.T.exists_finiteEtale_section_of_smooth_closedFibre R hR (G ⊗ G ⊗ G) s₃ N hN₁
  have hρ₁f : IsFinite (spMap ρ₁) := (IsFinite.SpecMap_iff (CommRingCat.ofHom ρ₁)).2 hρ₁.2.2
  let m : pullback G.hom (spMap ρ₁) ⟶ pullback G.hom (G ⊗ G ⊗ G).hom :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ t) (by rw [Category.assoc, ht]; exact pullback.condition)
  have m₁ : m ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have m₂ : m ≫ pullback.snd _ _ = pullback.snd _ _ ≫ t := pullback.lift_snd _ _ _
  have hU : IsOpen {p | ∀ f ∈ ClosedPt.ten G, f.left (m p) ∈ O'} := by
    have : {p | ∀ f ∈ ClosedPt.ten G, f.left (m p) ∈ O'} =
        ⋂ f ∈ {f | f ∈ ClosedPt.ten G}, m ⁻¹' (f.left ⁻¹' O') := by ext; simp
    rw [this]
    exact (List.finite_toSet _).isOpen_biInter fun f _ => (O'.isOpen.preimage f.left.continuous).preimage m.continuous
  let V : G.left.Opens := ⟨_, ((pullback.fst G.hom (spMap ρ₁)).isClosedMap _ hU.isClosed_compl).isOpen_compl⟩
  have hyV : y ∈ V := by
    rintro ⟨p, hp, hpy⟩
    refine hp (hN₂ (m p) ?_ ?_)
    · rw [← Scheme.Hom.comp_apply, m₁, hpy]
    · rw [← Scheme.Hom.comp_apply, m₂, Scheme.Hom.comp_apply]
      exact htN ⟨_, rfl⟩
  have hgood : ∀ p : (pullback G.hom (spMap ρ₁) : Scheme.{0}), pullback.fst G.hom (spMap ρ₁) p ∈ V →
      ∀ f ∈ ClosedPt.ten G, f.left (m p) ∈ O' := fun p hp => by
    by_contra h
    exact hp ⟨p, h, rfl⟩
  let q := pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)
  let s := pullback.snd (G'.hom ≫ spMap ρ) (spMap ρ₁)
  have hqs : (q ≫ β) ≫ G.hom = s ≫ spMap ρ₁ := by
    rw [Category.assoc, hβ.1.w]; exact pullback.condition
  let n' : (pullback (G'.hom ≫ spMap ρ) (spMap ρ₁) : Scheme.{0}) ⟶ pullback G.hom (spMap ρ₁) := pullback.lift (q ≫ β) s hqs
  have n₁ : n' ≫ pullback.fst _ _ = q ≫ β := pullback.lift_fst _ _ _
  have n₂ : n' ≫ pullback.snd _ _ = s := pullback.lift_snd _ _ _
  let ζ : (pullback (G'.hom ≫ spMap ρ) (spMap ρ₁) : Scheme.{0}) ⟶ (G ⊗ G ⊗ G ⊗ G).left := n' ≫ m
  let T : Over (Sp R') := Over.mk (q ≫ G'.hom)
  have hζ : ζ ≫ (fst G (G ⊗ G ⊗ G)).left = q ≫ β := by
    change (n' ≫ m) ≫ pullback.fst G.hom (G ⊗ G ⊗ G).hom = _
    rw [Category.assoc, m₁, n₁]
  have hw : ζ ≫ (G ⊗ G ⊗ G ⊗ G).hom = T.hom ≫ spMap ρ := by
    rw [← Over.w (fst G (G ⊗ G ⊗ G)), ← Category.assoc, hζ, Category.assoc, hβ.1.w]
    exact (Category.assoc _ _ _).symm
  obtain ⟨hl, hm⟩ := GlobalTheory.T.grpPullback_points_lift_and_compat_mul_inv (Sp R) (Sp R') (spMap ρ) G G' β hβ T (G ⊗ G ⊗ G ⊗ G) ζ hw
  obtain ⟨a₁, ha⟩ := hl (snd _ _ ≫ fst _ _)
  obtain ⟨b₁, hb⟩ := hl (snd _ _ ≫ snd _ _ ≫ fst _ _)
  obtain ⟨c₁, hc₁⟩ := hl (snd _ _ ≫ snd _ _ ≫ snd _ _)
  let x : T ⟶ G' := Over.homMk q rfl
  have hx : x.left ≫ β = ζ ≫ (fst G _).left := hζ.symm
  have mu := fun u v u' v' h₁ h₂ => (hm u v u' v' h₁ h₂).1
  have iv := fun u u' h₁ => (hm u u u' u' h₁ h₁).2
  have key : ∀ f' ∈ cubeTen x a₁ b₁ c₁, ∃ f ∈ ClosedPt.ten G, f'.left ≫ β = ζ ≫ f.left := by
    intro f hf
    simp only [cubeTen, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], mu _ _ _ _ hx ha⟩
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], mu _ _ _ _ hx (iv _ _ ha)⟩
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], ha⟩
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], iv _ _ ha⟩
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], mu _ _ _ _ hx hb⟩
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], mu _ _ _ _ hx hc₁⟩
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], mu _ _ _ _ hx (iv _ _ (mu _ _ _ _ hb hc₁))⟩
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], hb⟩
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], hc₁⟩
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], iv _ _ (mu _ _ _ _ hb hc₁)⟩
  have hten : ∀ g ∈ cubeTen x a₁ b₁ c₁, q ⁻¹ᵁ (β ⁻¹ᵁ V) ≤ g.left ⁻¹ᵁ secNz θ := by
    intro g' hg' z hz
    obtain ⟨f, hf, e⟩ := key g' hg'
    have hzV : pullback.fst G.hom (spMap ρ₁) (n' z) ∈ V := by
      rw [← Scheme.Hom.comp_apply, n₁, Scheme.Hom.comp_apply]; exact hz
    have h1 := hgood (n' z) hzV f hf
    refine h1 (g'.left z) ?_
    have e' := congrArg (fun φ => φ z) e
    simp only [Scheme.Hom.comp_apply] at e'
    exact e'
  obtain ⟨τ, hτ, hcar⟩ := GlobalTheory.T.exists_carriedFrame_theoremOfCube G' U'.LG U'.cubG θ T x a₁ b₁ c₁ (q ⁻¹ᵁ (β ⁻¹ᵁ V)) hten
  refine ⟨R₁, inferInstance, inferInstance, inferInstance, ρ₁, hρ₁, het, V, hyV, τ, hτ, ?_⟩
  intro σ h bc hbc hP hPO f' hf'q hf's
  have hc : IsGrpPullback G' G' (specOf (Gal.hom σ)) (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) :=
    hbc ▸ a.cart σ
  have hrc := GlobalTheory.T.rigidifiedGaloisLinearisation_carries_rigidification_cube R hB R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hact σ h bc hbc hP
  have hTw : f' ≫ T.hom = T.hom ≫ spMap (Gal.hom σ) := by
    change f' ≫ q ≫ G'.hom = (q ≫ G'.hom) ≫ _
    rw [← Category.assoc, hf'q, Category.assoc, (a.cart σ).1.w, Category.assoc]
  have hfn : f' ≫ n' = n' := by
    apply pullback.hom_ext
    · rw [Category.assoc, n₁, ← Category.assoc, hf'q, Category.assoc, hact]
    · rw [Category.assoc, n₂, hf's]
  have hfζ : f' ≫ ζ = ζ := by
    change f' ≫ n' ≫ m = n' ≫ m
    rw [← Category.assoc, hfn]
  have lift_eq : ∀ (u₁ : T ⟶ G') (u : G ⊗ G ⊗ G ⊗ G ⟶ G), u₁.left ≫ β = ζ ≫ u.left →
      u₁.left ≫ (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) = f' ≫ u₁.left := by
    intro u₁ u hu
    rw [hbc]
    apply hβ.1.hom_ext
    · rw [Category.assoc, hact, hu, Category.assoc f', hu, ← Category.assoc, hfζ]
    · have e₁ : u₁.left ≫ G'.hom = T.hom := Over.w u₁
      rw [Category.assoc, (a.cart σ).1.w, ← Category.assoc, e₁, Category.assoc, e₁, hTw]
  exact hcar (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) (specOf (Gal.hom σ)) hc
    (Classical.choose hP.lg) (Classical.choose_spec hP.lg).1 hrc.1 (hrc.2 hc) (hθ σ h bc hbc hP hPO) f' hTw
    (by rw [hbc]; exact hf'q.symm) (lift_eq a₁ _ ha) (lift_eq b₁ _ hb) (lift_eq c₁ _ hc₁)

end GlobalTheory.Mum
