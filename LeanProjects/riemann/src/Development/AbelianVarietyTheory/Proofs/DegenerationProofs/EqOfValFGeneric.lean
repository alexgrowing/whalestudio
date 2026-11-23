import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH
open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem RatModel.exists_eq_spMap_pt (M : RatModel o Ω) {K : Type} [Field K] (y : Sp K ⟶ M.Z)
    (hy : ∀ w, y w = genericPoint M.Z) : ∃ β : Ω →+* K, y = spMap β ≫ M.pt := by
  have hs : ∀ w, y w ⤳ genericPoint M.Z := fun w => (hy w) ▸ specializes_rfl
  have hm : ∀ x : Ω, x ∈ M.O (genericPoint M.Z) := fun x => by rw [RatModel.O_genericPoint]; trivial
  let β : Ω →+* K := (RatModel.valHomOf y _ hs).comp
    ((RingHom.id Ω).codRestrict (M.O (genericPoint M.Z)).toSubring hm)
  obtain ⟨U, hU, hz, -⟩ := exists_isAffineOpen_mem_and_subset (X := M.Z) (x := genericPoint M.Z) (U := ⊤) trivial
  have h1 : ⊤ ≤ y ⁻¹ᵁ U := fun w _ => by
    change y w ∈ U
    rw [hy]; exact hz
  have h2 : ⊤ ≤ M.pt ⁻¹ᵁ U := M.top_le_preimage_pt ⟨_, hz⟩
  refine ⟨β, ext_of_valR hU h1 (le_preimage_comp _ _ h2 (le_preimage_top _)) fun f => ?_⟩
  rw [valR_spMap_comp β M.pt U h2]
  exact (RatModel.val_valF ((top_le_preimage_iff _ _).1 h1) f).symm

variable {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} (Q : ZHPre ρ M U₀)

instance ZHPre.isIntegral : IsIntegral Q.G.left :=
  have := Q.semi
  isIntegral_left_of_isSemiAbelian Q.G

theorem ZHPre.hom_genericPoint : Q.G.hom (genericPoint Q.G.left) = genericPoint M.Z := by
  have hw : η[Q.G].left ≫ Q.G.hom = 𝟙 _ := Over.w η[Q.G]
  have h1 : Q.G.hom (η[Q.G].left (genericPoint M.Z)) = genericPoint M.Z :=
    (Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg (fun f : M.Z ⟶ M.Z => f (genericPoint M.Z)) hw)
  have h2 := (genericPoint_specializes (η[Q.G].left (genericPoint M.Z))).map Q.G.hom.continuous
  rw [h1] at h2
  exact (h2.antisymm (genericPoint_specializes _)).eq

theorem ZHPre.exists_generic (hU : (U₀ : Set M.Z).Nonempty) :
    ∃ (K : Type) (_ : Field K) (β : Ω →+* K) (g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀)
      (r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left) (jP : ρ.P.L.ι),
      g ≫ pullback.snd _ _ ≫ U₀.ι = spMap β ≫ M.pt ∧
      r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = g ≫ pullback.fst _ _ ∧
      Set.range (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⊆ ρ.P.L.U jP ∧
      ∀ w, (g ≫ Q.φ) w = genericPoint Q.G.left := by
  let K : Type := Q.G.left.residueField (genericPoint Q.G.left)
  let x : Sp K ⟶ Q.G.left := Q.G.left.fromSpecResidueField (genericPoint Q.G.left)
  have hx : ∀ w, x w = genericPoint Q.G.left := fun w => Scheme.fromSpecResidueField_apply _ _
  have hx' : ∀ w, (x ≫ Q.G.hom) w = genericPoint M.Z := fun w => by
    rw [Scheme.Hom.comp_apply, hx, Q.hom_genericPoint]
  obtain ⟨β, hβ⟩ := M.exists_eq_spMap_pt (x ≫ Q.G.hom) hx'
  have hg : genericPoint M.Z ∈ U₀ := (genericPoint_specializes hU.some).mem_open U₀.isOpen hU.some_mem
  have hr : Set.range (x ≫ Q.G.hom) ⊆ Set.range U₀.ι := by
    rintro _ ⟨w, rfl⟩
    rw [hx', Scheme.Opens.range_ι]
    exact hg
  let y : Sp K ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι (x ≫ Q.G.hom) hr
  have hy : y ≫ U₀.ι = x ≫ Q.G.hom := IsOpenImmersion.lift_fac _ _ _
  let g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀ := Q.cart.1.lift x y hy.symm
  have hg1 : g ≫ Q.φ = x := Q.cart.1.lift_fst x y hy.symm
  have hg2 : g ≫ pullback.snd _ _ = y := Q.cart.1.lift_snd x y hy.symm
  obtain ⟨jP, hj⟩ := exists_le_preimage_of_iSup_eq_top (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ρ.P.isLB.cover
  refine ⟨K, inferInstance, β, g, pullback.lift ((g ≫ pullback.fst _ _) ≫ ρ.P.A.hom) (g ≫ pullback.fst _ _)
    (Category.comp_id _), jP, ?_, pullback.lift_snd _ _ _, (top_le_preimage_iff _ _).1 hj, fun w => hg1 ▸ hx w⟩
  rw [← Category.assoc, hg2, hy, hβ]

theorem eq_of_valF_generic {X : Scheme.{0}} [IsIntegral X] {K : Type} [Field K] (x : Sp K ⟶ X)
    (hx : ∀ w, x w = genericPoint X) {U : X.Opens} {f f' : Γ(X, U)}
    (h : ⊤ ≤ x ⁻¹ᵁ U → valF x U f = valF x U f') : f = f' := by
  by_contra h0
  have hne : ((X.basicOpen (f - f') : X.Opens) : Set X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun h => h0 (sub_eq_zero.1 ((basicOpen_eq_bot_iff _).1 (SetLike.coe_injective h)))
  have h1 : ⊤ ≤ x ⁻¹ᵁ X.basicOpen (f - f') := fun w _ => by
    change x w ∈ X.basicOpen (f - f')
    rw [hx]
    exact (genericPoint_specializes hne.some).mem_open (X.basicOpen _).isOpen hne.some_mem
  have h2 : ⊤ ≤ x ⁻¹ᵁ U := le_preimage_mono x (X.basicOpen_le _) h1
  have hu := (le_preimage_basicOpen_iff x h2 _).1 h1
  have h3 := h h2
  rw [valF_eq_valR, valF_eq_valR, valR_eq x U h2, valR_eq x U h2] at h3
  rw [valR_eq x U h2, map_sub, h3, sub_self] at hu
  exact not_isUnit_zero hu

theorem ZHPre.eq_of_genVal (hU : (U₀ : Set M.Z).Nonempty) (k : ℤ) {I : Type} [Fintype I]
    (t : I → LB.Sec (LPow ρ.P.A ρ.P.L k (baseOver (Sp S.R)))) (c : I → Ω) (V : Q.G.left.Opens)
    (σ σ' : ∀ j, Γ(Q.G.left, V ⊓ (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => k)).U j))
    (h : GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w k t c V σ) (h' : GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w k t c V σ') :
    σ = σ' := by
  obtain ⟨K, _, β, g, r, jP, h1, h2, h3, h4⟩ := Q.exists_generic hU
  funext j
  obtain ⟨jL, rfl⟩ : ∃ jL, j = fun _ => jL := ⟨j 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  refine eq_of_valF_generic (g ≫ Q.φ) h4 fun hm => ?_
  have hm' := (top_le_preimage_iff _ _).1 hm
  have hV : Set.range (g ≫ Q.φ) ⊆ V := fun y hy => (hm' hy).1
  have hL : Set.range (g ≫ Q.φ) ⊆ Q.L.L.U jL := fun y hy => Set.mem_iInter.1 (hm' hy).2 0
  have e := (h K β g r jP jL h1 h2 h3 hL hV).symm.trans (h' K β g r jP jL h1 h2 h3 hL hV)
  refine mul_left_cancel₀ (zpow_ne_zero _ ?_) e
  refine IsUnit.ne_zero ?_
  have hw : ⊤ ≤ g ⁻¹ᵁ (LB.div (ρ.P.L.pull (pullback.fst ρ.P.A.hom Q.u₀)) (Q.L.L.pull Q.φ)).U
      (fun _ => jP, fun _ => jL) := fun w _ =>
    ⟨Set.mem_iInter.2 fun _ => h3 ⟨w, Scheme.Hom.comp_apply _ _ _⟩,
      Set.mem_iInter.2 fun _ => hL ⟨w, Scheme.Hom.comp_apply _ _ _⟩⟩
  rw [valF_eq_valR, valR_eq g _ hw]
  exact (Units.isUnit _).map _

end GlobalTheory.ZH
