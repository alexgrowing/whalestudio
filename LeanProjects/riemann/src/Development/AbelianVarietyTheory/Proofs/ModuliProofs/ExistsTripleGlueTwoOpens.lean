import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfAppLESectionEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGeometricallyIntegralAbLocusTensorObj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenOfRigid
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalStructureAndSymmetricOfCubeGen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfLbIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueTwo
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MemOfMemImage

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.TripleGlue

open GlobalTheory.CechPic

section Cube

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

def cub {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (c : Pic G.left) : Pic T.left :=
  ∑ I : ULift.{0} (Finset (Fin n)), ((-1 : ℤ) ^ (n - I.down.card)) • pull (psum G x I.down).left c

theorem cls_cubeLB {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) {L : LB G.left} (hL : L.IsLB)
    (h : (cubeLB G x L).IsLB) : cls (cubeLB G x L) h = cub x (cls L hL) :=
  cls_linComb hL _ _ h

theorem isLB_cubeLB {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) {L : LB G.left} (hL : L.IsLB) :
    (cubeLB G x L).IsLB := LB.isLB_linComb hL _ _

theorem pull_cub {T T' : Over S} {n : ℕ} (U : T' ⟶ T) (x : Fin n → (T ⟶ G)) (c : Pic G.left) :
    pull U.left (cub x c) = cub (fun i => U ≫ x i) c := by
  unfold cub
  rw [map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_zsmul, ← pull_comp, ← Over.comp_left]
  exact congrArg (fun z : T' ⟶ G => _ • pull z.left c) (psum_hom (preHom U) x I.down)

theorem pull_cub_push (h : IsGrpPullback G' G f φ) {T' : Over S'} {T : Over S} {n : ℕ} (x' : Fin n → (T' ⟶ G'))
    (x : Fin n → (T ⟶ G)) (U : Over.mk (T'.hom ≫ f) ⟶ T) (hx : ∀ i, pushPt h.1.w (x' i) = U ≫ x i)
    (c : Pic G.left) : pull U.left (cub x c) = cub x' (pull φ c) := by
  unfold cub
  rw [map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_zsmul, ← pull_comp, ← psum_push h x' x U hx, pull_comp]

theorem pull_one {T : Over S} {c : Pic G.left} (hc : pull (eSec G) c = 0) : pull (1 : T ⟶ G).left c = 0 := by
  have : (1 : T ⟶ G).left = (toUnit T).left ≫ eSec G := rfl
  rw [this, pull_comp, hc, map_zero]

theorem cub_one {T : Over S} {n : ℕ} {x : Fin n → (T ⟶ G)} (hx : ∀ i, x i = 1) {c : Pic G.left}
    (hc : pull (eSec G) c = 0) : cub x c = 0 := by
  refine Finset.sum_eq_zero fun I _ => ?_
  have e : psum G x I.down = 1 := by
    have := psum_hom (1 : (T ⟶ G) →* (T ⟶ G)) x I.down
    rw [MonoidHom.one_apply] at this
    exact (congrArg (fun z => psum G z I.down) (funext hx)).trans this.symm
  rw [e, pull_one hc, smul_zero]

end Cube

theorem eq_zero_of_cover {X : Scheme.{0}} (P : Over X) (e : 𝟙_ (Over X) ⟶ P) (hs : Smooth P.hom)
    (hg : GeometricallyIntegral P.hom) (hr : IsReduced X) (hab : genericPoints X ⊆ abLocus P) {U V : X.Opens}
    (hUV : U ⊔ V = ⊤) (c : Pic P.left) (h₀ : pull e.left c = 0) (hU : pull (P.hom ⁻¹ᵁ U).ι c = 0)
    (hV : pull (P.hom ⁻¹ᵁ V).ι c = 0) : c = 0 := by
  obtain ⟨N, hN, rfl⟩ := cls_surj c
  have he : e.left ≫ P.hom = 𝟙 X := Over.w e
  refine (cls_eq_zero_iff hN).2 (GlobalTheory.RigidTriv.exists_gen_of_rigid X P e.left N he
    (GlobalTheory.eq_one_of_appLE_section_eq_one X P e.left he hs hg ⟨hr, hab⟩) hN
    ((cls_eq_zero_iff (pull_isLB hN _)).1 h₀) fun x => ?_)
  have hx : x ∈ U ⊔ V := hUV ▸ trivial
  rcases hx with hx | hx
  · exact ⟨U, hx, (cls_eq_zero_iff (pull_isLB hN _)).1 hU⟩
  · exact ⟨V, hx, (cls_eq_zero_iff (pull_isLB hN _)).1 hV⟩

abbrev part {X : Scheme.{0}} (P : Over X) (W : X.Opens) : Over W.toScheme := Over.mk (P.hom ∣_ W)

def partι {X : Scheme.{0}} (P : Over X) (W : X.Opens) : Over.mk ((part P W).hom ≫ W.ι) ⟶ P :=
  Over.homMk (P.hom ⁻¹ᵁ W).ι (morphismRestrict_ι P.hom W).symm

theorem exists_lift {X : Scheme.{0}} {W : X.Opens} {G : Over X} {G' : Over W.toScheme} {ψ : G'.left ⟶ G.left}
    (h : IsPullback ψ G'.hom G.hom W.ι) {P : Over X} (x : P ⟶ G) :
    ∃ x' : part P W ⟶ G', pushPt h.w x' = partι P W ≫ x :=
  ⟨Over.homMk (h.lift (partι P W ≫ x).left (part P W).hom (Over.w _)) (h.lift_snd _ _ _),
    Over.OverMorphism.ext (h.lift_fst _ _ _)⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem local_identities {X : Scheme.{0}} {W : X.Opens} {G : Over X} [GrpObj G] [IsCommMonObj G]
    (a : OAct (𝓞 E) G) (c : Pic G.left) (t : SAB H W.toScheme) {ψ : t.G.left ⟶ G.left}
    (gp : IsGrpPullback t.G G W.ι ψ) (ha : ∀ x, (t.act.act x).left ≫ ψ = ψ ≫ (a.act x).left)
    (hc : pull ψ c = cls t.PP.L t.PP.isLB) :
    pull ((G3 G).hom ⁻¹ᵁ W).ι (cub (x3 G) c) = 0 ∧
    pull (G.hom ⁻¹ᵁ W).ι (c - pull (GrpObj.inv (X := G)).left c) = 0 ∧
    (∀ b, pull ((G ⊗ G).hom ⁻¹ᵁ W).ι
      (cub ![fst G G ≫ a.act b, snd G G] c - cub ![fst G G, snd G G ≫ a.act (H.bar b)] c) = 0) ∧
    pull (G.hom ⁻¹ᵁ W).ι (c - cub ![𝟙 G, a.act H.w0] c) = 0 := by
  have pa : ∀ {T : Over W.toScheme} (x : T ⟶ t.G) b,
      pushPt gp.1.w (x ≫ t.act.act b) = pushPt gp.1.w x ≫ a.act b := fun x b =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, ha, Category.assoc])
  obtain ⟨u, hu⟩ := exists_lift gp.1 (𝟙 G)
  have hu' : u.left ≫ ψ = (G.hom ⁻¹ᵁ W).ι := (congrArg (fun z => z.left) hu).trans (Category.comp_id _)
  have hp : pull (G.hom ⁻¹ᵁ W).ι c = pull u.left (cls t.PP.L t.PP.isLB) := by rw [← hu', pull_comp, hc]
  refine ⟨?_, ?_, fun b => ?_, ?_⟩
  · choose x' hx' using fun i => exists_lift gp.1 (x3 G i)
    have e₁ := pull_cub_push gp x' _ _ hx' c
    have e₂ := pull_cub (lift (x' 0) (lift (x' 1) (x' 2))) (x3 t.G) (cls t.PP.L t.PP.isLB)
    have e₃ : cub (x3 t.G) (cls t.PP.L t.PP.isLB) = 0 :=
      (cls_cubeLB _ _ (isLB_cubeLB _ t.PP.isLB)).symm.trans ((cls_eq_zero_iff _).2 ⟨t.cub.t, t.cub.isGen⟩)
    have e₄ : (fun i => lift (x' 0) (lift (x' 1) (x' 2)) ≫ x3 t.G i) = x' := by
      funext i
      fin_cases i <;> simp [x3]
    rw [e₃, map_zero, e₄, ← hc] at e₂
    exact e₁.trans e₂.symm
  · obtain ⟨_, w, hw, -⟩ := t.sym
    have e₁ : cls t.PP.L t.PP.isLB = pull (GrpObj.inv (X := t.G)).left (cls t.PP.L t.PP.isLB) :=
      (cls_eq_iff _ (pull_isLB t.PP.isLB _)).2 ⟨w, hw⟩
    have e₂ : (GrpObj.inv (X := t.G)).left ≫ ψ = ψ ≫ (GrpObj.inv (X := G)).left := by
      have e := congrArg (fun z => z.left) (map_inv (pushHom gp t.G) (𝟙 t.G))
      simpa [pushHom, pushPt, Hom.inv_def] using e
    rw [map_sub, ← pull_comp, ← hu', Category.assoc, ← e₂, pull_comp, pull_comp, pull_comp, hc, ← e₁, sub_self]
  · obtain ⟨x, hx⟩ := exists_lift gp.1 (fst G G)
    obtain ⟨y, hy⟩ := exists_lift gp.1 (snd G G)
    have e₁ := pull_cub_push gp ![x ≫ t.act.act b, y] ![fst G G ≫ a.act b, snd G G] (partι _ W) (fun i => by
      fin_cases i
      · exact (pa _ _).trans (by rw [hx]; exact Category.assoc _ _ _)
      · exact hy) c
    have e₂ := pull_cub_push gp ![x, y ≫ t.act.act (H.bar b)] ![fst G G, snd G G ≫ a.act (H.bar b)] (partι _ W)
      (fun i => by
        fin_cases i
        · exact hx
        · exact (pa _ _).trans (by rw [hy]; exact Category.assoc _ _ _)) c
    have e₃ := congrArg (pull (lift x y).left) ((cls_cubeLB _ t.PP.isLB _).symm.trans
      (((cls_eq_iff (isLB_cubeLB _ t.PP.isLB) (isLB_cubeLB _ t.PP.isLB)).2 (t.adj b)).trans
        (cls_cubeLB _ t.PP.isLB _)))
    have f₁ : (fun i => lift x y ≫ ![fst t.G t.G ≫ t.act.act b, snd t.G t.G] i) = ![x ≫ t.act.act b, y] := by
      funext i
      fin_cases i <;> simp
    have f₂ : (fun i => lift x y ≫ ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar b)] i) =
        ![x, y ≫ t.act.act (H.bar b)] := by
      funext i
      fin_cases i <;> simp
    rw [pull_cub, pull_cub, f₁, f₂, ← hc] at e₃
    rw [map_sub, sub_eq_zero]
    exact e₁.trans (e₃.trans e₂.symm)
  · have e₁ := pull_cub_push gp ![u, u ≫ t.act.act H.w0] ![𝟙 G, a.act H.w0] (partι _ W) (fun i => by
      fin_cases i
      · exact hu
      · exact (pa _ _).trans (by rw [hu]; simp)) c
    have e₃ := congrArg (pull u.left)
      (((cls_eq_iff t.PP.isLB (isLB_cubeLB _ t.PP.isLB)).2 t.prim).trans (cls_cubeLB _ t.PP.isLB _))
    have f₁ : (fun i => u ≫ ![𝟙 t.G, t.act.act H.w0] i) = ![u, u ≫ t.act.act H.w0] := by
      funext i
      fin_cases i <;> simp
    rw [pull_cub, f₁] at e₃
    rw [hc] at e₁
    rw [map_sub, sub_eq_zero, hp]
    exact e₃.trans e₁.symm

theorem isReduced_of_cover {X : Scheme.{0}} {U V : X.Opens} (hUV : U ⊔ V = ⊤) [IsReduced U.toScheme]
    [IsReduced V.toScheme] : IsReduced X := by
  have key : ∀ (W : X.Opens) [IsReduced W.toScheme] (x : X), x ∈ W → _root_.IsReduced (X.presheaf.stalk x) := by
    intro W _ x hx
    obtain ⟨y, rfl⟩ : ∃ y : W.toScheme, W.ι y = x := ⟨⟨x, hx⟩, rfl⟩
    exact isReduced_of_injective (W.ι.stalkMap y).hom (ConcreteCategory.bijective_of_isIso (W.ι.stalkMap y)).1
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have hx : x ∈ U ⊔ V := hUV ▸ trivial
    rcases hx with hx | hx
    · exact key U x hx
    · exact key V x hx
  exact isReduced_of_isReduced_stalk X

theorem mem_genericPoints_open {X : Scheme.{0}} (W : X.Opens) (x : W.toScheme) (hx : W.ι x ∈ genericPoints X) :
    x ∈ genericPoints W.toScheme := by
  have h := preimage_mem_irreducibleComponents (t := closure {W.ι x}) hx W.ι.isOpenEmbedding
    ⟨W.ι x, subset_closure rfl, x, rfl⟩
  change closure _ ∈ irreducibleComponents W.toScheme
  rw [W.ι.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image, Set.image_singleton]
  exact h

theorem pull_eSec {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G) :
    pull (eSec G) (cls L.L L.isLB) = 0 :=
  (cls_eq_zero_iff (pull_isLB L.isLB _)).2 ⟨L.rig, L.rigGen⟩

theorem pull_rigidify {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {ψ : G'.left ⟶ G.left} (gp : IsGrpPullback G' G f ψ) (c : Pic G.left)
    (L : RigLB G') (h : cls L.L L.isLB = pull ψ c) :
    pull ψ (c - pull ((toUnit G).left ≫ eSec G) c) = cls L.L L.isLB := by
  have e : ψ ≫ (toUnit G).left ≫ eSec G = (toUnit G').left ≫ eSec G' ≫ ψ := by
    have e₁ : eSec G' ≫ ψ = f ≫ eSec G := (cubeMapOf gp).e_comm
    have e₂ : ψ ≫ G.hom = G'.hom ≫ f := gp.1.w
    rw [e₁, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ eSec G) e₂
  rw [map_sub, ← pull_comp, e, pull_comp, pull_comp, ← h, pull_eSec, map_zero, sub_zero]

theorem exists_sab_glue : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (U V : X.Opens) (t₁ : SAB H U.toScheme) (t₂ : SAB H V.toScheme) (t₀ : SAB H (U ⊓ V).toScheme) (m₁ : SABMap t₀ t₁ (X.homOfLE inf_le_left)) (m₂ : SABMap t₀ t₂ (X.homOfLE inf_le_right)), U ⊔ V = ⊤ → (IsReduced U.toScheme ∧ genericPoints U.toScheme ⊆ abLocus t₁.G) → (IsReduced V.toScheme ∧ genericPoints V.toScheme ⊆ abLocus t₂.G) → ∃ (t : SAB H X) (n₁ : SABMap t₁ t U.ι) (n₂ : SABMap t₂ t V.ι), m₁.φ ≫ n₁.φ = m₂.φ ≫ n₂.φ := by
  intro E _ _ _ H X U V t₁ t₂ t₀ m₁ m₂ hUV h₁ h₂
  obtain ⟨G, _, a, ψ₁, ψ₂, hG, gp₁, gp₂, hφ, ha⟩ := GlobalTheory.GroupGlue.exists_glue_two (𝓞 E) X U V t₁.G t₂.G t₀.G t₁.act t₂.act t₀.act
    m₁.φ m₂.φ hUV t₁.semi t₂.semi m₁.cart m₂.cart fun x => ⟨m₁.act x, m₂.act x⟩
  have := hG.comm
  have o₁ : IsOpenImmersion ψ₁ := MorphismProperty.of_isPullback gp₁.1.flip inferInstance
  have o₂ : IsOpenImmersion ψ₂ := MorphismProperty.of_isPullback gp₂.1.flip inferInstance
  have sq : IsPullback m₁.φ m₂.φ ψ₁ ψ₂ := by
    have big := m₁.cart.1.paste_vert (isPullback_opens_inf U V)
    rw [← m₂.cart.1.w, ← gp₁.1.w] at big
    exact big.of_bot hφ gp₂.1
  have cov : Set.range ψ₁ ∪ Set.range ψ₂ = Set.univ := by
    refine Set.eq_univ_of_forall fun g => ?_
    have hx : G.hom g ∈ U ⊔ V := hUV ▸ trivial
    rcases hx with hx | hx
    · obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback gp₁.1 g ⟨_, hx⟩ rfl
      exact .inl ⟨z, hz⟩
    · obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback gp₂.1 g ⟨_, hx⟩ rfl
      exact .inr ⟨z, hz⟩
  obtain ⟨w₁, hw₁, -⟩ := m₁.lin
  obtain ⟨w₂, hw₂, -⟩ := m₂.lin
  obtain ⟨L, hL, i₁, i₂⟩ := GlobalTheory.GlueTwoLB.glue G.left t₀.G.left t₁.G.left t₂.G.left ψ₁ ψ₂ m₁.φ m₂.φ t₁.PP.L t₂.PP.L o₁ o₂
    sq cov t₁.PP.isLB t₂.PP.isLB (LBIso.trans (pull_isLB t₁.PP.isLB _) t₀.PP.isLB (pull_isLB t₂.PP.isLB _)
      (LBIso.symm ⟨w₁, hw₁⟩) ⟨w₂, hw₂⟩)
  obtain ⟨M, hM, hc⟩ := cls_surj (cls L hL - pull ((toUnit G).left ≫ eSec G) (cls L hL))
  have c₁ : pull ψ₁ (cls M hM) = cls t₁.PP.L t₁.PP.isLB :=
    hc ▸ pull_rigidify gp₁ _ t₁.PP ((cls_eq_iff _ (pull_isLB hL _)).2 i₁)
  have c₂ : pull ψ₂ (cls M hM) = cls t₂.PP.L t₂.PP.isLB :=
    hc ▸ pull_rigidify gp₂ _ t₂.PP ((cls_eq_iff _ (pull_isLB hL _)).2 i₂)
  have c₀ : pull (eSec G) (cls M hM) = 0 := by
    have e : eSec G ≫ (toUnit G).left = 𝟙 _ := Over.w η[G]
    rw [hc, map_sub, ← pull_comp, ← Category.assoc, e, Category.id_comp, sub_self]
  obtain ⟨ρ, hρ⟩ := (cls_eq_zero_iff (pull_isLB hM _)).1 c₀
  let PP : RigLB G := ⟨M, ρ, hM, hρ⟩
  have hr : IsReduced X := by
    have := h₁.1
    have := h₂.1
    exact isReduced_of_cover hUV
  have hab : genericPoints X ⊆ abLocus G := fun x hx => by
    have hx' : x ∈ U ⊔ V := hUV ▸ trivial
    rcases hx' with hx' | hx'
    · exact (abLocus_pullback abLocusOne hG gp₁.1 ⟨x, hx'⟩).2 (h₁.2 (mem_genericPoints_open U ⟨x, hx'⟩ hx))
    · exact (abLocus_pullback abLocusOne hG gp₂.1 ⟨x, hx'⟩).2 (h₂.2 (mem_genericPoints_open V ⟨x, hx'⟩ hx))
  have a₁ := hG.smooth
  have := hG.geomConnected
  have b₁ := GlobalTheory.grpObj_geometricallyIntegral_of_smooth X G
  obtain ⟨a₂, b₂, d₂⟩ := GlobalTheory.smooth_geometricallyIntegral_abLocus_tensorObj X G G a₁ a₁ b₁ b₁
  have g₂ := (Set.subset_inter hab hab).trans d₂
  obtain ⟨a₃, b₃, d₃⟩ := GlobalTheory.smooth_geometricallyIntegral_abLocus_tensorObj X G _ a₁ a₂ b₁ b₂
  have g₃ := (Set.subset_inter hab g₂).trans d₃
  obtain ⟨p₁, q₁, r₁, s₁⟩ := local_identities a (cls M hM) t₁ gp₁ (fun x => (ha x).1) c₁
  obtain ⟨p₂, q₂, r₂, s₂⟩ := local_identities a (cls M hM) t₂ gp₂ (fun x => (ha x).2) c₂
  have one_act : ∀ b, (1 : 𝟙_ (Over X) ⟶ G) ≫ a.act b = 1 := fun b => by
    have := a.hom b
    exact MonObj.one_comp _
  have z₀ : pull (1 : 𝟙_ (Over X) ⟶ G).left (cls M hM) = 0 := pull_one c₀
  have p := eq_zero_of_cover (G3 G) (lift 1 (lift 1 1)) a₃ b₃ hr g₃ hUV _
    ((pull_cub _ _ _).trans (cub_one (fun i => by fin_cases i <;> simp [x3]) c₀)) p₁ p₂
  have q := eq_zero_of_cover G 1 a₁ b₁ hr hab hUV _ (by
    have e : (1 : 𝟙_ (Over X) ⟶ G) ≫ GrpObj.inv (X := G) = 1 := (Hom.inv_def _).symm.trans inv_one
    rw [map_sub, ← pull_comp, ← Over.comp_left, e, sub_self]) q₁ q₂
  have r := fun b => eq_zero_of_cover (G ⊗ G) (lift 1 1) a₂ b₂ hr g₂ hUV _ (by
    rw [map_sub, pull_cub, pull_cub, cub_one (fun i => by fin_cases i <;> simp [one_act]) c₀,
      cub_one (fun i => by fin_cases i <;> simp [one_act]) c₀, sub_self]) (r₁ b) (r₂ b)
  have s := eq_zero_of_cover G 1 a₁ b₁ hr hab hUV _ (by
    rw [map_sub, pull_cub, cub_one (fun i => by fin_cases i <;> simp [one_act]) c₀, z₀, sub_self]) s₁ s₂
  obtain ⟨k₁, k₂⟩ := GlobalTheory.CubeGen.cubical_and_symmetric X G PP hG ⟨hr, hab⟩
  obtain ⟨cb⟩ := k₁ ((cls_eq_zero_iff (isLB_cubeLB _ hM)).1 ((cls_cubeLB _ hM _).trans p))
  let t : SAB H X :=
    { G := G, semi := hG, act := a, PP := PP, cub := cb
      sym := k₂ ((cls_eq_iff hM (pull_isLB hM _)).1 (sub_eq_zero.1 q))
      adj := fun b => (cls_eq_iff (isLB_cubeLB _ hM) (isLB_cubeLB _ hM)).1
        ((cls_cubeLB _ hM _).trans ((sub_eq_zero.1 (r b)).trans (cls_cubeLB _ hM _).symm))
      prim := (cls_eq_iff hM (isLB_cubeLB _ hM)).1 ((sub_eq_zero.1 s).trans (cls_cubeLB _ hM _).symm) }
  obtain ⟨n₁, hn₁⟩ := GlobalTheory.exists_sabMap_of_lbIso E H X U t t₁ U.ι ψ₁ h₁ gp₁ (fun x => (ha x).1)
    ((cls_eq_iff t₁.PP.isLB (pull_isLB hM _)).1 c₁.symm)
  obtain ⟨n₂, hn₂⟩ := GlobalTheory.exists_sabMap_of_lbIso E H X V t t₂ V.ι ψ₂ h₂ gp₂ (fun x => (ha x).2)
    ((cls_eq_iff t₂.PP.isLB (pull_isLB hM _)).1 c₂.symm)
  exact ⟨t, n₁, n₂, by rw [hn₁, hn₂]; exact hφ⟩

end GlobalTheory.TripleGlue
