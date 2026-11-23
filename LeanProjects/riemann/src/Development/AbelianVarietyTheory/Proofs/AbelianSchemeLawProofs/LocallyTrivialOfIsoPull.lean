import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.RigidityTranslation

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CubeLawCompare

section General

variable {Y T : Scheme.{0}}

def IsGenOn (M : LB Y) (W : Y.Opens) (d : ∀ j, Γ(Y, W ⊓ M.U j)ˣ) : Prop :=
  ∀ j j' (y : Y), y ∈ W → y ∈ M.U j → y ∈ M.U j' →
    gm (𝟙 Y) y (W ⊓ M.U j) (d j) =
      gm (𝟙 Y) y (M.U j ⊓ M.U j') (M.g j j') * gm (𝟙 Y) y (W ⊓ M.U j') (d j')

theorem gen_restrict_iff (M : LB Y) (W : Y.Opens) :
    (∃ c : LB.Gen (M.pull W.ι), c.IsGen) ↔ ∃ d, IsGenOn M W d := by
  constructor
  · rintro ⟨c, hc⟩
    choose b hb using fun j : M.ι =>
      exists_ext_unit W.ι ((M.pull W.ι).U fun _ => j) (c.s fun _ => j)
    have le : ∀ j, W ⊓ M.U j ≤ W.ι ''ᵁ ((M.pull W.ι).U fun _ => j) :=
      fun j y hy => ⟨⟨y, hy.1⟩, mem_pull.2 hy.2, rfl⟩
    refine ⟨fun j => res (le j) (b j), fun j j' y hW hj hj' => ?_⟩
    let z : W.toScheme := ⟨y, hW⟩
    have hz : W.ι z ∈ W ⊓ M.U j ⊓ M.U j' := ⟨⟨hW, hj⟩, hj'⟩
    have l₁ : W ⊓ M.U j ⊓ M.U j' ≤ W ⊓ M.U j := inf_le_left
    have l₂ : W ⊓ M.U j ⊓ M.U j' ≤ M.U j ⊓ M.U j' := fun _ h => ⟨h.1.2, h.2⟩
    have l₃ : W ⊓ M.U j ⊓ M.U j' ≤ W ⊓ M.U j' := fun _ h => ⟨h.1.1, h.2⟩
    have v : ∀ i (hi : y ∈ M.U i), gm W.ι z (W ⊓ M.U i) (res (le i) (b i)) =
        gm (𝟙 _) z ((M.pull W.ι).U fun _ => i) (c.s fun _ => i) := fun i hi => by
      have h := hb i _ (𝟙 _) z (mem_pull.2 hi)
      rw [Category.id_comp] at h
      exact (gm_res W.ι z (le i) ⟨hW, hi⟩ _).trans h
    have m : (𝟙 W.toScheme : _ ⟶ _) z ∈ ((M.pull W.ι).U fun _ => j) ⊓ ((M.pull W.ι).U fun _ => j') :=
      ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
    have e := (gm_res (𝟙 _) z _ m _).symm.trans ((congrArg (gm (𝟙 _) z _) (hc (fun _ => j) (fun _ => j'))).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_pull_g M W.ι (𝟙 _) z _ _ m.1 m.2) (gm_res (𝟙 _) z _ m _))))
    rw [Category.id_comp] at e
    have key := gm_inj W.ι z hz hz (a := res l₁ (res (le j) (b j)))
      (b := res l₂ (M.g j j') * res l₃ (res (le j') (b j'))) (by
        rw [map_mul, gm_res W.ι z l₁ hz, gm_res W.ι z l₂ hz, gm_res W.ι z l₃ hz, v j hj, v j' hj']
        exact e)
    rw [map_mul, gm_res (𝟙 Y) (W.ι z) l₁ hz, gm_res (𝟙 Y) (W.ι z) l₂ hz, gm_res (𝟙 Y) (W.ι z) l₃ hz] at key
    exact key
  · rintro ⟨d, hd⟩
    have le : ∀ J : PUnit → M.ι, (M.pull W.ι).U J ≤ W.ι ⁻¹ᵁ (W ⊓ M.U (J PUnit.unit)) :=
      fun J z hz => ⟨z.2, mem_pull.1 hz⟩
    refine ⟨⟨fun J => res (le J) (pullU W.ι _ (d (J PUnit.unit)))⟩, fun J J' => ?_⟩
    have e : res (inf_le_left : W ⊓ M.U (J PUnit.unit) ⊓ M.U (J' PUnit.unit) ≤ _) (d (J PUnit.unit)) =
        res (show W ⊓ M.U (J PUnit.unit) ⊓ M.U (J' PUnit.unit) ≤
            M.U (J PUnit.unit) ⊓ M.U (J' PUnit.unit) from fun _ h => ⟨h.1.2, h.2⟩)
          (M.g (J PUnit.unit) (J' PUnit.unit)) *
        res (show W ⊓ M.U (J PUnit.unit) ⊓ M.U (J' PUnit.unit) ≤
            W ⊓ M.U (J' PUnit.unit) from fun _ h => ⟨h.1.1, h.2⟩)
          (d (J' PUnit.unit)) := unit_ext fun y hy => by
      rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy, gm_res _ y _ hy]
      exact hd _ _ y hy.1.1 hy.1.2 hy.2
    refine unit_ext fun z hz => ?_
    have hz' : W.ι z ∈ W ⊓ M.U (J PUnit.unit) ⊓ M.U (J' PUnit.unit) :=
      ⟨⟨z.2, mem_pull.1 hz.1⟩, mem_pull.1 hz.2⟩
    have e' := congrArg (gm W.ι z _) e
    rw [map_mul, gm_res _ z _ hz', gm_res _ z _ hz', gm_res _ z _ hz'] at e'
    have v : ∀ I : PUnit → M.ι, z ∈ (M.pull W.ι).U I →
        gm (𝟙 _) z ((M.pull W.ι).U I) (res (le I) (pullU W.ι _ (d (I PUnit.unit)))) =
          gm W.ι z (W ⊓ M.U (I PUnit.unit)) (d (I PUnit.unit)) := fun I hI =>
      (gm_res (𝟙 _) z (le I) hI _).trans ((gm_pull (𝟙 _) W.ι z _ (le I hI) _).trans
        (by rw [Category.id_comp]))
    refine ((gm_res (𝟙 _) z _ hz _).trans (v J hz.1)).trans (e'.trans (Eq.symm ?_))
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_pull_g M W.ι (𝟙 _) z J J' hz.1 hz.2).trans ?_)
      ((gm_res (𝟙 _) z _ hz _).trans (v J' hz.2)))
    rw [Category.id_comp]

theorem locally_trivial_of_iso_pull (p : Y ⟶ T) (M : LB Y) {N : LB T} (hN : N.IsLB)
    (u : LB.Iso (N.pull p) M) (hu : u.IsGen) (t : T) :
    ∃ V : T.Opens, t ∈ V ∧ ∃ c : LB.Gen (M.pull (p ⁻¹ᵁ V).ι), c.IsGen := by
  obtain ⟨i, hi⟩ := exists_chart hN t
  refine ⟨N.U i, hi, (gen_restrict_iff M _).2 ?_⟩
  have le : ∀ j, p ⁻¹ᵁ N.U i ⊓ M.U j ≤ M.U j ⊓ (N.pull p).U fun _ => i :=
    fun j y hy => ⟨hy.2, mem_pull.2 hy.1⟩
  refine ⟨fun j => res (le j) (u.s (j, fun _ => i)), fun j j' y hW hj hj' => ?_⟩
  have hI : (𝟙 Y : Y ⟶ Y) y ∈ (N.pull p).U fun _ => i := mem_pull.2 hW
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ M.U j ⊓ (N.pull p).U (fun _ => i) ⊓ (M.U j' ⊓ (N.pull p).U fun _ => i) :=
    ⟨⟨hj, hI⟩, hj', hI⟩
  have e := (gm_res (𝟙 Y) y _ hm _).symm.trans ((congrArg (gm (𝟙 Y) y _)
    (hu (j, fun _ => i) (j', fun _ => i))).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_div (N.pull p) M (𝟙 Y) y (j, fun _ => i) (j', fun _ => i) hm) (gm_res (𝟙 Y) y _ hm _))))
  rw [gm_self (LB.isLB_pull hN p) (𝟙 Y) y hI, inv_one, _root_.mul_one] at e
  exact (gm_res (𝟙 Y) y (le j) ⟨hW, hj⟩ _).trans
    (e.trans (congrArg _ (gm_res (𝟙 Y) y (le j') ⟨hW, hj'⟩ _).symm))

theorem iso_pull_of_locally_trivial (p : Y ⟶ T) (hp : ∀ V : T.Opens, Function.Bijective (p.app V).hom)
    {M : LB Y} (hM : M.IsLB)
    (h : ∀ t : T, ∃ V : T.Opens, t ∈ V ∧ ∃ c : LB.Gen (M.pull (p ⁻¹ᵁ V).ι), c.IsGen) :
    ∃ N : LB T, N.IsLB ∧ ∃ u : LB.Iso (N.pull p) M, u.IsGen := by
  choose V hV hc using h
  choose d hd using fun t => (gen_restrict_iff M _).1 (hc t)
  have inj : ∀ (O : T.Opens) (a b : Γ(T, O)ˣ),
      (∀ y : Y, p y ∈ O → gm p y O a = gm p y O b) → a = b := fun O a b hab => by
    have e : pullU p O a = pullU p O b := unit_ext fun y hy => by
      rw [gm_pull (𝟙 Y) p y O hy, gm_pull (𝟙 Y) p y O hy, Category.id_comp]
      exact hab y hy
    exact Units.ext ((hp O).1 (congrArg Units.val e))
  have ratio : ∀ t t' : T, ∃ g : Γ(T, V t ⊓ V t')ˣ, ∀ j (y : Y), p y ∈ V t → p y ∈ V t' → y ∈ M.U j →
      gm p y _ g = gm (𝟙 Y) y (p ⁻¹ᵁ V t' ⊓ M.U j) (d t' j) * (gm (𝟙 Y) y (p ⁻¹ᵁ V t ⊓ M.U j) (d t j))⁻¹ := by
    intro t t'
    have l₁ : ∀ j, p ⁻¹ᵁ (V t ⊓ V t') ⊓ M.U j ≤ p ⁻¹ᵁ V t ⊓ M.U j := fun j y hy => ⟨hy.1.1, hy.2⟩
    have l₂ : ∀ j, p ⁻¹ᵁ (V t ⊓ V t') ⊓ M.U j ≤ p ⁻¹ᵁ V t' ⊓ M.U j := fun j y hy => ⟨hy.1.2, hy.2⟩
    have v : ∀ j (y : Y) (hy : y ∈ p ⁻¹ᵁ (V t ⊓ V t') ⊓ M.U j),
        gm (𝟙 Y) y _ (res (l₂ j) (d t' j) * (res (l₁ j) (d t j))⁻¹) =
          gm (𝟙 Y) y (p ⁻¹ᵁ V t' ⊓ M.U j) (d t' j) * (gm (𝟙 Y) y (p ⁻¹ᵁ V t ⊓ M.U j) (d t j))⁻¹ :=
      fun j y hy => by rw [map_mul, map_inv, gm_res _ y _ hy, gm_res _ y _ hy]
    obtain ⟨a, ha⟩ := glue_unit (p ⁻¹ᵁ (V t ⊓ V t')) (fun j => p ⁻¹ᵁ (V t ⊓ V t') ⊓ M.U j)
      (fun _ => inf_le_left) (fun y hy => by
        obtain ⟨j, hj⟩ := exists_chart hM y
        exact Opens.mem_iSup.2 ⟨j, hy, hj⟩)
      (fun j => res (l₂ j) (d t' j) * (res (l₁ j) (d t j))⁻¹) (fun j j' y hy => by
        rw [v j y hy.1, v j' y hy.2, hd t j j' y hy.1.1.1 hy.1.2 hy.2.2,
          hd t' j j' y hy.1.1.2 hy.1.2 hy.2.2, mul_inv, _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul])
    let E := RingEquiv.ofBijective _ (hp (V t ⊓ V t'))
    let g : Γ(T, V t ⊓ V t')ˣ := Units.map E.symm.toRingHom.toMonoidHom a
    have hg : pullU p _ g = a := Units.ext (E.apply_symm_apply a.val)
    refine ⟨g, fun j y h₁ h₂ hj => ?_⟩
    have hy : (𝟙 Y : Y ⟶ Y) y ∈ p ⁻¹ᵁ (V t ⊓ V t') ⊓ M.U j := ⟨⟨h₁, h₂⟩, hj⟩
    have e := gm_pull (𝟙 Y) p y (V t ⊓ V t') hy.1 g
    rw [Category.id_comp, hg] at e
    rw [← e, ← v j y hy, ← ha j, gm_res _ y _ hy]
  choose g hg using ratio
  let N : LB T := ⟨T, V, g⟩
  have hN : N.IsLB := by
    refine ⟨eq_top_iff.2 fun t _ => Opens.mem_iSup.2 ⟨t, hV t⟩, fun t => inj _ _ _ fun y hy => ?_,
      fun t t' t'' => inj _ _ _ fun y hy => ?_⟩
    · obtain ⟨j, hj⟩ := exists_chart hM y
      exact (gm_res p y _ hy _).trans ((hg t t j y hy hy hj).trans
        ((mul_inv_cancel _).trans (map_one _).symm))
    · obtain ⟨j, hj⟩ := exists_chart hM y
      rw [map_mul, gm_res p y _ hy, gm_res p y _ hy, gm_res p y _ hy]
      refine (congrArg₂ (· * ·) (hg t t' j y hy.1.1 hy.1.2 hj) (hg t' t'' j y hy.1.2 hy.2 hj)).trans
        (Eq.trans ?_ (hg t t'' j y hy.1.1 hy.2 hj).symm)
      rw [mul_comm, _root_.mul_assoc, inv_mul_cancel_left]
  have le : ∀ q : M.ι × (PUnit → T), M.U q.1 ⊓ (N.pull p).U q.2 ≤ p ⁻¹ᵁ V (q.2 PUnit.unit) ⊓ M.U q.1 :=
    fun q y hy => ⟨mem_pull (L := N).1 hy.2, hy.1⟩
  refine ⟨N, hN, ⟨fun q => res (le q) (d (q.2 PUnit.unit) q.1)⟩, fun q q' => unit_ext fun y hy => ?_⟩
  have h₁ : p y ∈ V (q.2 PUnit.unit) := mem_pull (L := N).1 hy.1.2
  have h₂ : p y ∈ V (q'.2 PUnit.unit) := mem_pull (L := N).1 hy.2.2
  have eN := gm_pull_g N p (𝟙 Y) y q.2 q'.2 hy.1.2 hy.2.2
  rw [Category.id_comp] at eN
  refine ((gm_res (𝟙 Y) y _ hy _).trans (gm_res (𝟙 Y) y (le q) hy.1 _)).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_div (N.pull p) M (𝟙 Y) y q q' hy).trans
    (congrArg (fun w => _ * w⁻¹) (eN.trans (hg _ _ q'.1 y h₁ h₂ hy.2.1))))
    ((gm_res (𝟙 Y) y _ hy _).trans (gm_res (𝟙 Y) y (le q') hy.2 _)))).trans ?_
  rw [hd _ q.1 q'.1 y h₁ hy.1.1 hy.2.1, mul_inv_rev, inv_inv, _root_.mul_assoc, inv_mul_cancel_right]

end General

theorem bijective_app_of_restrict {Y T : Scheme.{0}} (p : Y ⟶ T) (V : T.Opens)
    (h : Function.Bijective (p ∣_ V).appTop.hom) : Function.Bijective (p.app V).hom := by
  have h₁ : IsIso (p ∣_ V).appTop := (ConcreteCategory.isIso_iff_bijective _).2 h
  have h₂ : IsIso (p.app (V.ι ''ᵁ ⊤)) :=
    @IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _
      (by rw [eqToHom_op]; exact Y.presheaf.map_isIso (eqToHom _)) h₁ (morphismRestrict_appTop p V).symm
  have e : V.ι ''ᵁ ⊤ = V := V.ι_image_top
  rw [e] at h₂
  exact ConcreteCategory.bijective_of_isIso (p.app V)

open scoped CategoryTheory.Obj in

theorem bijective_app_fst (hG : GlobalFnsSt) {S : Scheme.{0}} {A : Over S} [GrpObj A]
    (hA : IsAbelianScheme A) (T : Over S) (V : T.left.Opens) :
    Function.Bijective ((fst T A).left.app V).hom := by
  have hB : IsAbelianScheme ((Over.pullback (V.ι ≫ T.hom)).obj A) :=
    { comm := by have := hA.comm; infer_instance
      smooth := by have := hA.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by have := hA.proper; show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := hA.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }
  have h₁ : Function.Bijective (pullback.snd A.hom (V.ι ≫ T.hom)).appTop.hom := hG _ _ hB
  have sq : IsPullback ((pullback.fst T.hom A.hom ⁻¹ᵁ V).ι ≫ pullback.snd T.hom A.hom)
      (pullback.fst T.hom A.hom ∣_ V) A.hom (V.ι ≫ T.hom) :=
    (isPullback_morphismRestrict (pullback.fst T.hom A.hom) V).flip.paste_horiz
      (IsPullback.of_hasPullback T.hom A.hom).flip
  have h₂ : Function.Bijective (pullback.fst T.hom A.hom ∣_ V).appTop.hom := by
    rw [← sq.isoPullback_hom_snd, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso (sq.isoPullback.hom.app ⊤)).comp h₁
  exact bijective_app_of_restrict _ V h₂

end GlobalTheory.CubeLawCompare
