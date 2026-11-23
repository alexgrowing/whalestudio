import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulApplyEqOfEqOnInvariants
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfAppLESectionEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGeometricallyIntegralAbLocusTensorObj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenOfQuotientOfRigid
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalStructureAndSymmetricOfCubeGen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfLbIso

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.QuotTriple

open GlobalTheory.CechPic

theorem isPullback_lift {X X' : Scheme.{0}} {π : X ⟶ X'} {P Q : Over X} {P' Q' : Over X'} {a : P.left ⟶ P'.left}
    {b : Q.left ⟶ Q'.left} (ha : IsPullback a P.hom P'.hom π) (hb : IsPullback b Q.hom Q'.hom π) :
    IsPullback (lift (pushPt ha.w (fst P Q)) (pushPt hb.w (snd P Q))).left (P ⊗ Q).hom (P' ⊗ Q').hom π := by
  have big : IsPullback ((snd P Q).left ≫ b) (fst P Q).left Q'.hom (P.hom ≫ π) :=
    (IsPullback.of_hasPullback P.hom Q.hom).flip.paste_horiz hb
  have e₁ : (lift (pushPt ha.w (fst P Q)) (pushPt hb.w (snd P Q))).left ≫ (fst P' Q').left = (fst P Q).left ≫ a :=
    congrArg (fun z => z.left) (lift_fst (pushPt ha.w (fst P Q)) (pushPt hb.w (snd P Q)))
  have e₂ : (lift (pushPt ha.w (fst P Q)) (pushPt hb.w (snd P Q))).left ≫ (snd P' Q').left = (snd P Q).left ≫ b :=
    congrArg (fun z => z.left) (lift_snd (pushPt ha.w (fst P Q)) (pushPt hb.w (snd P Q)))
  have h₁ : IsPullback (lift (pushPt ha.w (fst P Q)) (pushPt hb.w (snd P Q))).left (fst P Q).left
      (fst P' Q').left a := by
    refine IsPullback.of_right (h₁₂ := (snd P' Q').left) (v₁₃ := Q'.hom) (h₂₂ := P'.hom) ?_ e₁
      (IsPullback.of_hasPullback P'.hom Q'.hom).flip
    rw [e₂, ha.w]
    exact big
  exact h₁.paste_vert ha

section Cube

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem pull_cls_cube (h : IsGrpPullback G' G f φ) {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (hc : pull φ (cls L hL) = cls L' hL') {T' : Over S'} {T : Over S} {n : ℕ} (x' : Fin n → (T' ⟶ G'))
    (x : Fin n → (T ⟶ G)) (U : Over.mk (T'.hom ≫ f) ⟶ T) (hx : ∀ i, pushPt h.1.w (x' i) = U ≫ x i) :
    pull U.left (cls (cubeLB G x L) (LB.isLB_linComb hL _ _)) = cls (cubeLB G' x' L') (LB.isLB_linComb hL' _ _) := by
  refine (congrArg (pull U.left) (cls_linComb hL _ _ _)).trans (Eq.trans ?_ (cls_linComb hL' _ _ _).symm)
  rw [map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_zsmul, ← pull_comp, ← hc, ← pull_comp]
  exact congrArg (fun q => _ • pull q (cls L hL)) (psum_push h x' x U hx I.down).symm

theorem psum_one {T : Over S} {n : ℕ} (I : Finset (Fin n)) : psum G (fun _ => (1 : T ⟶ G)) I = 1 := by
  unfold psum
  induction (List.finRange n).filter (· ∈ I) with
  | nil => rfl
  | cons k l ih => exact (congrArg ((1 : T ⟶ G) * ·) ih).trans (_root_.mul_one _)

theorem one_left : (1 : 𝟙_ (Over S) ⟶ G).left = eSec G := by
  rw [Hom.one_def]; simp [eSec]

theorem pull_cls_cube_origin {L : LB G.left} (hL : L.IsLB) (h0 : pull (eSec G) (cls L hL) = 0) {T : Over S} {n : ℕ}
    (x : Fin n → (T ⟶ G)) (o : 𝟙_ (Over S) ⟶ T) (ho : ∀ i, o ≫ x i = 1) :
    pull o.left (cls (cubeLB G x L) (LB.isLB_linComb hL _ _)) = 0 := by
  refine (congrArg (pull o.left) (cls_linComb hL _ _ _)).trans ?_
  rw [map_sum]
  refine Finset.sum_eq_zero fun I _ => ?_
  have e : o ≫ psum G x I.down = 1 :=
    (psum_hom (preHom o) x I.down).trans ((congrArg (fun z => psum G z I.down) (funext ho)).trans (psum_one _))
  rw [map_zsmul, ← pull_comp, ← Over.comp_left, e, one_left, h0, smul_zero]

end Cube

section Quot

variable {Γ : Type} [Group Γ] [Finite Γ] {X X' : Scheme.{0}} {ρ : Γ →* Aut X} {π : X ⟶ X'}

theorem eq_zero_of_pull (hq : IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens,
      Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)),
        ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom)
    {P : Over X} {P' : Over X'} {Φ : P.left ⟶ P'.left} (hΦ : IsPullback Φ P.hom P'.hom π) (hs' : Smooth P'.hom)
    (hs : Smooth P.hom) (hg : GeometricallyIntegral P.hom) (hr : IsReduced X) (hab : genericPoints X ⊆ abLocus P)
    (o : 𝟙_ (Over X) ⟶ P) (o' : 𝟙_ (Over X') ⟶ P') (ho : o.left ≫ Φ = π ≫ o'.left) (c : Pic P'.left)
    (h₀ : pull o'.left c = 0) (h₁ : pull Φ c = 0) : c = 0 := by
  obtain ⟨N, hN, rfl⟩ := cls_surj c
  exact (cls_eq_zero_iff hN).2 (exists_gen_of_quotient_of_rigid Γ X X' ρ π P P' Φ o.left o'.left N hq hΦ
    inferInstance (Over.w o) (Over.w o') ho
    (eq_one_of_appLE_section_eq_one X P o.left (Over.w o) hs hg ⟨hr, hab⟩) hN
    ((cls_eq_zero_iff (pull_isLB hN _)).1 h₀) ((cls_eq_zero_iff (pull_isLB hN _)).1 h₁))

theorem genericPoints_subset_image [Surjective π] : genericPoints X' ⊆ π '' genericPoints X := by
  intro y hy
  obtain ⟨x, rfl⟩ := π.surjective y
  let C : irreducibleComponents X := ⟨_, irreducibleComponent_mem_irreducibleComponents x⟩
  have hs : (genericPoints.ofComponent C).1 ⤳ x :=
    (genericPoints.isGenericPoint_ofComponent C).specializes mem_irreducibleComponent
  exact ⟨_, (genericPoints.ofComponent C).2, eq_of_specializes_of_mem_genericPoints hy (hs.map π.continuous)⟩

end Quot

theorem exists_sab_of_quotient : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X') (t : SAB H X) (G' : Over X') [GrpObj G'] [IsCommMonObj G'] (a' : OAct (𝓞 E) G') (φ : t.G.left ⟶ G'.left) (L' : LB G'.left), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → (IsReduced X ∧ genericPoints X ⊆ abLocus t.G) → IsSemiAbelian G' → IsGrpPullback t.G G' π φ → (∀ x, (t.act.act x).left ≫ φ = φ ≫ (a'.act x).left) → L'.IsLB → LBIso t.PP.L (L'.pull φ) → ∃ (t' : SAB H X') (ν : SABMap t t' π) (e : t'.G ≅ G'), ν.φ ≫ e.hom.left = φ := by
  intro E _ _ _ H Γ _ _ X X' ρ π t G' _ _ a' φ L' hq ⟨hr, hab⟩ hG' gp hact hL' hiso
  obtain ⟨-, hsurj, -⟩ := quotient_isIntegral_surjective_orbits Γ X X' ρ π hq
  have hr' : IsReduced X' := ⟨fun V => isReduced_of_injective _ (hq.2.2 V).1⟩
  have hab' : genericPoints X' ⊆ abLocus G' := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := genericPoints_subset_image (π := π) hy
    exact (abLocus_pullback abLocusOne hG' gp.1 x).2 (hab hx)
  have he : eSec t.G ≫ φ = π ≫ eSec G' := (cubeMapOf gp).e_comm
  have hp : eSec G' ≫ G'.hom = 𝟙 X' := Over.w _
  have c₀ : pull (eSec t.G) (cls t.PP.L t.PP.isLB) = 0 :=
    (cls_eq_zero_iff (pull_isLB t.PP.isLB _)).2 ⟨_, t.PP.rigGen⟩
  have cl : cls t.PP.L t.PP.isLB = pull φ (cls L' hL') := (cls_eq_iff _ (pull_isLB hL' φ)).2 hiso
  obtain ⟨M, hM, cM⟩ := cls_surj (cls L' hL' - pull (G'.hom ≫ eSec G') (cls L' hL'))
  have m₀ : pull (eSec G') (cls M hM) = 0 := by
    have e : eSec G' ≫ G'.hom ≫ eSec G' = eSec G' :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ eSec G') hp).trans (Category.id_comp _))
    rw [cM, map_sub, ← pull_comp, e, sub_self]
  have m₁ : pull φ (cls M hM) = cls t.PP.L t.PP.isLB := by
    have e : φ ≫ G'.hom ≫ eSec G' = t.G.hom ≫ eSec t.G ≫ φ := by
      rw [he, ← Category.assoc, gp.1.w, Category.assoc]
    rw [cM, map_sub, ← pull_comp, e, pull_comp, pull_comp, ← cl, c₀, map_zero, sub_zero]
  obtain ⟨r, hrig⟩ := (cls_eq_zero_iff (pull_isLB hM (eSec G'))).1 m₀
  let PP : RigLB G' := ⟨M, r, hM, hrig⟩
  have a₁ := t.semi.smooth
  have := t.semi.geomConnected
  have b₁ := grpObj_geometricallyIntegral_of_smooth X t.G
  obtain ⟨a₂, b₂, c₂⟩ := smooth_geometricallyIntegral_abLocus_tensorObj X t.G t.G a₁ a₁ b₁ b₁
  have d₂ := (Set.subset_inter hab hab).trans c₂
  obtain ⟨a₃, b₃, c₃⟩ := smooth_geometricallyIntegral_abLocus_tensorObj X t.G _ a₁ a₂ b₁ b₂
  have d₃ := (Set.subset_inter hab d₂).trans c₃
  have a₁' := hG'.smooth
  have a₂' : Smooth (G' ⊗ G').hom := smooth_tensorObj_hom _ _
  have a₃' : Smooth (G' ⊗ G' ⊗ G').hom := smooth_tensorObj_hom _ _
  have p₂ := isPullback_lift gp.1 gp.1
  have p₃ := isPullback_lift gp.1 p₂
  have o₁ : (1 : 𝟙_ (Over X) ⟶ t.G).left ≫ φ = π ≫ (1 : 𝟙_ (Over X') ⟶ G').left := by
    rw [one_left, one_left]; exact he
  have pa : ∀ {T : Over X} (x : T ⟶ t.G) a, pushPt gp.1.w (x ≫ t.act.act a) = pushPt gp.1.w x ≫ a'.act a :=
    fun x a => Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc])
  have ol : ∀ {P Q : Over X} {P' Q' : Over X'} {a : P.left ⟶ P'.left} {b : Q.left ⟶ Q'.left}
      (wa : a ≫ P'.hom = P.hom ≫ π) (wb : b ≫ Q'.hom = Q.hom ≫ π) (u : 𝟙_ _ ⟶ P) (v : 𝟙_ _ ⟶ Q) (u' : 𝟙_ _ ⟶ P')
      (v' : 𝟙_ _ ⟶ Q'), u.left ≫ a = π ≫ u'.left → v.left ≫ b = π ≫ v'.left →
      (lift u v).left ≫ (lift (pushPt wa (fst P Q)) (pushPt wb (snd P Q))).left = π ≫ (lift u' v').left := by
    intro P Q P' Q' a b wa wb u v u' v' hu hv
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst P' Q').left = (_ ≫ _) ≫ (fst P' Q').left
      rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst, ← hu]
      show _ ≫ (fst P Q).left ≫ a = _
      rw [← Category.assoc, ← Over.comp_left, lift_fst]
    · show (_ ≫ _) ≫ (snd P' Q').left = (_ ≫ _) ≫ (snd P' Q').left
      rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd, ← hv]
      show _ ≫ (snd P Q).left ≫ b = _
      rw [← Category.assoc, ← Over.comp_left, lift_snd]
  have o₂ := ol gp.1.w gp.1.w 1 1 1 1 o₁ o₁
  have o₃ := ol gp.1.w p₂.w 1 _ 1 _ o₁ o₂
  have aone : ∀ a, (1 : 𝟙_ (Over X') ⟶ G') ≫ a'.act a = 1 := fun a => by
    have := a'.hom a
    exact MonObj.one_comp _
  have hΘ : ∃ s : (Theta G' M).Gen, s.IsGen := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hM _ _)).1 (eq_zero_of_pull hq p₃ a₃' a₃ b₃ hr d₃ _ _ o₃ _
      (pull_cls_cube_origin hM m₀ (x3 G') _ fun i => by fin_cases i <;> simp [x3])
      ((pull_cls_cube gp hM t.PP.isLB m₁ (x3 t.G) (x3 G') _ fun i => ?_).trans
        ((cls_eq_zero_iff _).2 ⟨_, t.cub.isGen⟩)))
    fin_cases i
    · simp [x3]
    · refine Eq.trans ?_ (congrArg (· ≫ fst G' G') (lift_snd _ _).symm |>.trans (Category.assoc _ _ _))
      refine Over.OverMorphism.ext ?_
      exact (Category.assoc _ _ _).trans ((congrArg (fun z => (snd t.G (t.G ⊗ t.G)).left ≫ z.left)
        (lift_fst (pushPt gp.1.w (fst t.G t.G)) (pushPt gp.1.w (snd t.G t.G)))).symm.trans (Category.assoc _ _ _).symm)
    · refine Eq.trans ?_ (congrArg (· ≫ snd G' G') (lift_snd _ _).symm |>.trans (Category.assoc _ _ _))
      refine Over.OverMorphism.ext ?_
      exact (Category.assoc _ _ _).trans ((congrArg (fun z => (snd t.G (t.G ⊗ t.G)).left ≫ z.left)
        (lift_snd (pushPt gp.1.w (fst t.G t.G)) (pushPt gp.1.w (snd t.G t.G)))).symm.trans (Category.assoc _ _ _).symm)
  have hsym : LBIso M (M.pull (GrpObj.inv (X := G')).left) := by
    have e₁ : φ ≫ (GrpObj.inv (X := G')).left = (GrpObj.inv (X := t.G)).left ≫ φ := by
      have e := congrArg (fun z => z.left) (map_inv (pushHom gp t.G) (𝟙 t.G))
      exact (congrArg (· ≫ (GrpObj.inv (X := G')).left) (Category.id_comp φ).symm).trans
        (e.symm.trans (congrArg (· ≫ φ) (Category.id_comp _)))
    have e₂ : (1 : 𝟙_ (Over X') ⟶ G') ≫ GrpObj.inv (X := G') = 1 := inv_one (G := 𝟙_ (Over X') ⟶ G')
    obtain ⟨-, w, hw, -⟩ := t.sym
    have e₃ : cls t.PP.L t.PP.isLB = pull (GrpObj.inv (X := t.G)).left (cls t.PP.L t.PP.isLB) :=
      (cls_eq_iff _ (pull_isLB t.PP.isLB _)).2 ⟨w, hw⟩
    refine (cls_eq_iff hM (pull_isLB hM _)).1 (sub_eq_zero.1 (eq_zero_of_pull hq gp.1 a₁' a₁ b₁ hr hab 1 1 o₁ _ ?_ ?_))
    · rw [map_sub, cls_pull hM, ← pull_comp, ← Over.comp_left, e₂, sub_self]
    · rw [map_sub, cls_pull hM, ← pull_comp, e₁, pull_comp, m₁, ← e₃, sub_self]
  have hadj : ∀ a, LBIso (cubeLB G' ![fst G' G' ≫ a'.act a, snd G' G'] M)
      (cubeLB G' ![fst G' G', snd G' G' ≫ a'.act (H.bar a)] M) := fun a => by
    refine (cls_eq_iff (LB.isLB_linComb hM _ _) (LB.isLB_linComb hM _ _)).1
      (sub_eq_zero.1 (eq_zero_of_pull hq p₂ a₂' a₂ b₂ hr d₂ _ _ o₂ _ ?_ ?_))
    · rw [map_sub, sub_eq_zero]
      exact (pull_cls_cube_origin hM m₀ _ _ fun i => by fin_cases i <;> simp [aone]).trans
        (pull_cls_cube_origin hM m₀ _ _ fun i => by fin_cases i <;> simp [aone]).symm
    · rw [map_sub, sub_eq_zero]
      refine (pull_cls_cube gp hM t.PP.isLB m₁ _ _ _ fun i => ?_).trans
        (((cls_eq_iff _ _).2 (t.adj a)).trans (pull_cls_cube gp hM t.PP.isLB m₁ _ _ _ fun i => ?_).symm)
      · fin_cases i
        · exact (pa _ a).trans (by simp)
        · simp
      · fin_cases i
        · simp
        · exact (pa _ _).trans (by simp)
  have hprim : LBIso M (cubeLB G' ![𝟙 G', a'.act H.w0] M) := by
    refine (cls_eq_iff hM (LB.isLB_linComb hM _ _)).1
      (sub_eq_zero.1 (eq_zero_of_pull hq gp.1 a₁' a₁ b₁ hr hab 1 1 o₁ _ ?_ ?_))
    · rw [map_sub, sub_eq_zero]
      exact (one_left (G := G') ▸ m₀).trans
        (pull_cls_cube_origin hM m₀ _ _ fun i => by fin_cases i <;> simp [aone]).symm
    · rw [map_sub, sub_eq_zero, m₁]
      refine ((cls_eq_iff _ (LB.isLB_linComb t.PP.isLB _ _)).2 t.prim).trans (Eq.trans
        (pull_cls_cube gp hM t.PP.isLB m₁ _ ![𝟙 G', a'.act H.w0] (pushPt gp.1.w (𝟙 t.G)) fun i => ?_).symm ?_)
      · fin_cases i
        · simp
        · exact (congrArg (pushPt gp.1.w) (Category.id_comp _).symm).trans (pa _ _)
      · exact congrArg (fun q => pull q _) (Category.id_comp φ)
  obtain ⟨k₁, k₂⟩ := CubeGen.cubical_and_symmetric X' G' PP hG' ⟨hr', hab'⟩
  obtain ⟨cub⟩ := k₁ hΘ
  let t' : SAB H X' := ⟨G', hG', a', PP, cub, k₂ hsym, hadj, hprim⟩
  obtain ⟨ν, hν⟩ := exists_sabMap_of_lbIso E H X' X t' t π φ ⟨hr, hab⟩ gp hact
    ((cls_eq_iff _ (pull_isLB hM φ)).1 m₁.symm)
  exact ⟨t', ν, Iso.refl _, (Category.comp_id _).trans hν⟩

end GlobalTheory.QuotTriple
