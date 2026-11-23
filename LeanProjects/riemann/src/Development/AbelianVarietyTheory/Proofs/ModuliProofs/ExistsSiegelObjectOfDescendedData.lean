import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAlgClosedJoinOfTwoFieldExtensions
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsMonHomIffOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeDescentSmoothDimensionStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleTrivialIsoDescendFieldStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilPairingFieldExtensionIffStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SiegelDescent

section Points

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem isPullback_square (hA : IsPullback φ G'.hom G.hom f) (φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left)
    (h : IsSquare φ φ₂) : IsPullback φ₂ (G' ⊗ G').hom (G ⊗ G).hom f := by
  have w₁ : (fst G G).left ≫ G.hom = (G ⊗ G).hom := Over.w _
  have w₂ : (snd G G).left ≫ G.hom = (G ⊗ G).hom := Over.w _
  have v₁ : (fst G' G').left ≫ G'.hom = (G' ⊗ G').hom := Over.w _
  have v₂ : (snd G' G').left ≫ G'.hom = (G' ⊗ G').hom := Over.w _
  have h₁ := h.1
  have h₂ := h.2
  refine ⟨⟨by rw [← w₁, reassoc_of% h₁, hA.w, reassoc_of% v₁]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => pullback.lift
      (hA.lift (s.fst ≫ (fst G G).left) s.snd (by rw [Category.assoc, w₁, s.condition]))
      (hA.lift (s.fst ≫ (snd G G).left) s.snd (by rw [Category.assoc, w₂, s.condition]))
      (by rw [IsPullback.lift_snd, IsPullback.lift_snd])) (fun s => ?_) (fun s => ?_)
    (fun s m h1 h2 => ?_)⟩⟩
  · apply pullback.hom_ext
    · change _ ≫ (fst G G).left = _ ≫ (fst G G).left
      rw [Category.assoc, h₁, ← Category.assoc]
      exact (congrArg (· ≫ φ) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
    · change _ ≫ (snd G G).left = _ ≫ (snd G G).left
      rw [Category.assoc, h₂, ← Category.assoc]
      exact (congrArg (· ≫ φ) (pullback.lift_snd _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
  · rw [← v₁, ← Category.assoc]
    exact (congrArg (· ≫ G'.hom) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_snd _ _ _ _)
  · apply pullback.hom_ext
    · refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
      change _ ≫ (fst G' G').left = _
      refine hA.hom_ext ?_ ?_
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₁]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₁]
    · refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      change _ ≫ (snd G' G').left = _
      refine hA.hom_ext ?_ ?_
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₂]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₂]

theorem lift_square {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} (h : IsSquare φ φ₂) {T : Over S'} {T₀ : Over S}
    {τ : T.left ⟶ T₀.left} {a b : T ⟶ G'} {a₀ b₀ : T₀ ⟶ G} (ha : a.left ≫ φ = τ ≫ a₀.left)
    (hb : b.left ≫ φ = τ ≫ b₀.left) : (lift a b).left ≫ φ₂ = τ ≫ (lift a₀ b₀).left := by
  apply pullback.hom_ext
  · change (_ ≫ _) ≫ (fst G G).left = (_ ≫ _) ≫ (fst G G).left
    rw [Category.assoc, h.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
      lift_fst, ha]
  · change (_ ≫ _) ≫ (snd G G).left = (_ ≫ _) ≫ (snd G G).left
    rw [Category.assoc, h.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
      lift_snd, hb]

variable [GrpObj G] [GrpObj G']

theorem exists_liftHom (h : IsGrpPullback G' G f φ) (T : Over S') (T₀ : Over S) (τ : T.left ⟶ T₀.left)
    (hτ : τ ≫ T₀.hom = T.hom ≫ f) :
    ∃ ρ : (T₀ ⟶ G) →* (T ⟶ G'), ∀ x₀ x, ρ x₀ = x ↔ x.left ≫ φ = τ ≫ x₀.left := by
  let r : (T₀ ⟶ G) → (T ⟶ G') := fun x₀ => Over.homMk
    (h.1.lift (τ ≫ x₀.left) T.hom (by rw [Category.assoc, Over.w, hτ])) (h.1.lift_snd _ _ _)
  have hr : ∀ x₀, (r x₀).left ≫ φ = τ ≫ x₀.left := fun x₀ => h.1.lift_fst _ _ _
  have key : ∀ x₀ x, r x₀ = x ↔ x.left ≫ φ = τ ≫ x₀.left := fun x₀ x =>
    ⟨fun e => e ▸ hr x₀, fun e => Over.OverMorphism.ext
      (h.1.hom_ext ((hr x₀).trans e.symm) (by rw [Over.w, Over.w]))⟩
  let U : Over.mk (T.hom ≫ f) ⟶ T₀ := Over.homMk τ hτ
  refine ⟨MonoidHom.mk' r fun a b => (key _ _).2 ?_, key⟩
  rw [← h.2 T (r a) (r b) (U ≫ a) (U ≫ b) (hr a).symm (hr b).symm, ← MonObj.comp_mul]
  rfl

theorem one_comp (h : IsGrpPullback G' G f φ) (T : Over S') (T₀ : Over S) (τ : T.left ⟶ T₀.left)
    (hτ : τ ≫ T₀.hom = T.hom ≫ f) : (1 : T ⟶ G').left ≫ φ = τ ≫ (1 : T₀ ⟶ G).left := by
  obtain ⟨ρ, hρ⟩ := exists_liftHom h T T₀ τ hτ
  exact (hρ _ _).1 (map_one ρ)

omit [GrpObj G'] in

theorem weilIs_congr {X : Scheme.{0}} {a b : X ⟶ S} (e : a = b) (L : LB G.left) (k : ℤ)
    (x y : Over.mk a ⟶ G) (x' y' : Over.mk b ⟶ G) (hx : x.left = x'.left) (hy : y.left = y'.left)
    (c : Γ(X, ⊤)ˣ) (H : Out.WeilIs G L k x y c) : Out.WeilIs G L k x' y' c := by
  subst e
  rw [← Over.OverMorphism.ext hx, ← Over.OverMorphism.ext hy]
  exact H

end Points

section Bundles

variable {X X₀ Y Y₀ : Scheme.{0}}

theorem lbIso_square {P : LB X} {P₀ : LB X₀} (hP : P.IsLB) (hP₀ : P₀.IsLB) {F : X ⟶ X₀} (hw : LBIso P (P₀.pull F))
    {a : Y ⟶ X} {a₀ : Y₀ ⟶ X₀} {ψ : Y ⟶ Y₀} (e : a ≫ F = ψ ≫ a₀) : LBIso (P.pull a) ((P₀.pull a₀).pull ψ) :=
  LBIso.trans (pull_isLB hP _) (pull_isLB hP₀ (ψ ≫ a₀)) (pull_isLB (pull_isLB hP₀ _) _)
    (LBIso.chartPull (chartPullPull P a a rfl) (chartPullSame P₀ _ _ _ a fun _ => e.symm) hw)
    (LBIso.chartPull (chartPullSame P₀ _ _ _ ψ fun _ => rfl) (chartPullPull _ ψ ψ rfl)
      (PolBaseChange.lbIso_refl (pull_isLB hP₀ a₀)))

theorem exists_gen_of_lbIso {L N : LB X} (hL : L.IsLB) (hN : N.IsLB) (H : LBIso L N)
    (h : ∃ t : L.Gen, t.IsGen) : ∃ t : N.Gen, t.IsGen :=
  (CechPic.iso_triv_iff N).1 (LBIso.trans (LB.isLB_triv X) hL hN ((CechPic.iso_triv_iff L).2 h) H)

end Bundles

theorem prod_zpow_single {I H : Type} [Fintype I] [DecidableEq I] [CommGroup H] (l : (I → ℤ) → H)
    (hl : ∀ a b, l (a + b) = l a * l b) (a : I → ℤ) : ∏ u, l (Pi.single u 1) ^ a u = l a := by
  let F : (I → ℤ) →+ Additive H := AddMonoidHom.mk' (fun a => Additive.ofMul (l a)) fun a b => by
    rw [hl, ofMul_mul]
  have e : a = ∑ u, a u • (Pi.single u 1 : I → ℤ) := by
    ext v
    simp [Finset.sum_apply, Pi.single_apply]
  have : F a = ∑ u, a u • F (Pi.single u 1) := by
    conv_lhs => rw [e]
    simp only [map_sum, map_zsmul]
  apply Additive.ofMul.injective
  rw [ofMul_prod]
  simp only [ofMul_zpow]
  exact this.symm

end GlobalTheory.SiegelDescent

namespace GlobalTheory

open SiegelDescent

theorem exists_siegPre_of_descended_data : ∀ (h M : ℕ) (o : Type) [CommRing o] (ζ : o) (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (s₀ : Sp K₀ ⟶ Sp o) (s : Sp K ⟶ Sp o) (c : SiegPre h M ζ s) (A₀ : Over (Sp K₀)) [GrpObj A₀] (φ : c.A.left ⟶ A₀.left) (φ₂ : (G2 c.A).left ⟶ (G2 A₀).left) (P₀ : LB (G2 A₀).left) (lev₀ : Fin h ⊕ Fin h → (𝟙_ (Over (Sp K₀)) ⟶ A₀)), s = spMap i ≫ s₀ → IsGrpPullback c.A A₀ (spMap i) φ → IsSquare φ φ₂ → P₀.IsLB → LBIso c.P (P₀.pull φ₂) → (∀ u, (c.lev (Pi.single u 1)).left ≫ φ = spMap i ≫ (lev₀ u).left) → ∃ c₀ : SiegPre h M ζ s₀, SiegPB c c₀ (spMap i) := by
  intro h M o _ ζ K₀ K _ _ i s₀ s c A₀ _ φ φ₂ P₀ lev₀ hs hp sq hP₀ hw hlev
  have ab : IsAbelianScheme A₀ := (T.abelian_scheme_descent_smooth_dimension K₀ K i A₀ c.A φ hp c.ab).1
  haveI := ab.comm
  haveI := ab.smooth
  haveI := ab.proper
  haveI := ab.geomConnected
  have epi : ∀ (F F' : Type) [Field F] [Field F'] (j : F →+* F'), Epi (spMap j) := fun F F' _ _ j =>
    ((_root_.GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff F F' j).1 _ _ (𝟙 _) (𝟙 _) (spMap j) (IsPullback.of_vert_isIso ⟨by simp⟩)).1
  have hφ : φ ≫ A₀.hom = c.A.hom ≫ spMap i := hp.1.w
  have one := one_comp hp c.A A₀ φ hφ
  have idφ : (𝟙 c.A : c.A ⟶ c.A).left ≫ φ = φ ≫ (𝟙 A₀ : A₀ ⟶ A₀).left := by simp
  have gen := (T.lineBundle_trivial_iso_descend_field K₀ K i _ _ A₀.hom c.A.hom φ inferInstance inferInstance inferInstance hp.1).1
  have rig : ∀ (a : c.A ⟶ c.A ⊗ c.A) (a₀ : A₀ ⟶ A₀ ⊗ A₀), a.left ≫ φ₂ = φ ≫ a₀.left →
      (∃ t : (c.P.pull a.left).Gen, t.IsGen) → ∃ t : (P₀.pull a₀.left).Gen, t.IsGen := fun a a₀ e ht =>
    gen _ (pull_isLB hP₀ _) (exists_gen_of_lbIso (pull_isLB c.isLB _) (pull_isLB (pull_isLB hP₀ _) _)
      (lbIso_square c.isLB hP₀ hw e) ht)
  have symm : LBIso P₀ (P₀.pull (lift (snd A₀ A₀) (fst A₀ A₀)).left) := by
    have h₁ : Smooth (A₀ ⊗ A₀).hom := by rw [Over.tensorObj_hom]; infer_instance
    have h₂ : IsProper (A₀ ⊗ A₀).hom := by rw [Over.tensorObj_hom]; infer_instance
    have h₃ : GeometricallyConnected (A₀ ⊗ A₀).hom := by
      rw [Over.tensorObj_hom]; exact GeometricallyConnected.comp _ _
    refine (T.lineBundle_trivial_iso_descend_field K₀ K i _ _ (A₀ ⊗ A₀).hom (c.A ⊗ c.A).hom φ₂ h₁ h₂ h₃ (isPullback_square hp.1 φ₂ sq)).2 _ _ hP₀
      (pull_isLB hP₀ _) ?_
    exact LBIso.trans (pull_isLB hP₀ _) c.isLB (pull_isLB (pull_isLB hP₀ _) _) hw.symm
      (LBIso.trans c.isLB (pull_isLB c.isLB _) (pull_isLB (pull_isLB hP₀ _) _) c.symm
        (lbIso_square c.isLB hP₀ hw (lift_square sq sq.2.symm sq.1.symm)))
  have diag : LBIso (c.P.pull (lift (𝟙 c.A) (𝟙 c.A)).left) ((P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left).pull φ) :=
    lbIso_square c.isLB hP₀ hw (lift_square sq idφ idφ)

  obtain ⟨ρ, hρ⟩ := exists_liftHom hp (𝟙_ _) (𝟙_ _) (spMap i)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  let lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp K₀)) ⟶ A₀) := fun a => ∏ u, lev₀ u ^ a u
  have ρlev : ∀ a, ρ (lev a) = c.lev a := fun a => by
    rw [← prod_zpow_single c.lev c.lev_add a]
    refine (map_prod ρ _ _).trans (Finset.prod_congr rfl fun u _ => ?_)
    rw [map_zpow, (hρ _ _).2 (hlev u)]
  have hlev' : ∀ a, (c.lev a).left ≫ φ = spMap i ≫ (lev a).left := fun a => (hρ _ _).1 (ρlev a)
  have ρinj : Function.Injective ρ := fun x y e => by
    haveI := epi _ _ i
    exact Over.OverMorphism.ext ((cancel_epi (spMap i)).1
      (((hρ x _).1 rfl).symm.trans ((hρ y _).1 e.symm)))
  refine ⟨{ A := A₀, ab := ab, P := P₀, isLB := hP₀
            rig₁ := rig _ _ (lift_square sq one idφ) c.rig₁
            rig₂ := rig _ _ (lift_square sq idφ one) c.rig₂
            symm := symm, lev := lev
            lev_add := fun a b => ρinj (by rw [map_mul, ρlev, ρlev, ρlev, c.lev_add])
            lev_tors := fun a => ρinj (by rw [map_pow, ρlev, c.lev_tors, map_one])
            geom := ?_ }, φ, φ₂, hp, sq, hw, hlev'⟩
  intro k _ _ x β z hx hz
  obtain ⟨i', rfl⟩ : ∃ i' : K₀ →+* k, x = spMap i' := ⟨(Spec.preimage x).hom, (Spec.map_preimage x).symm⟩
  obtain ⟨Ω, _, _, j, j', hj⟩ := exists_algClosed_join_of_two_field_extensions K₀ K k i i'
  have e : spMap j' ≫ spMap i' = spMap j ≫ spMap i := by rw [← spMap_comp, ← spMap_comp, hj]
  obtain ⟨g₁, g₂, g₃⟩ := c.geom Ω (spMap j) (j'.comp β) (Units.map j'.toMonoidHom z)
    (by rw [hs, ← Category.assoc, ← e, Category.assoc, hx, spMap_comp]) (congrArg j' hz)
  obtain ⟨σ, hσ⟩ := exists_liftHom hp (Over.mk (spMap j)) (Over.mk (spMap i')) (spMap j') e
  have σinj : Function.Injective σ := fun x y e => by
    haveI := epi _ _ j'
    exact Over.OverMorphism.ext ((cancel_epi (spMap j')).1
      (((hσ x _).1 rfl).symm.trans ((hσ y _).1 e.symm)))
  have pt : ∀ a, (toUnit (Over.mk (spMap j)) ≫ c.lev a).left ≫ φ =
      spMap j' ≫ (toUnit (Over.mk (spMap i')) ≫ lev a).left := fun a => by
    change (spMap j ≫ (c.lev a).left) ≫ φ = spMap j' ≫ spMap i' ≫ (lev a).left
    rw [Category.assoc, hlev', reassoc_of% e]
  have σlev : ∀ a, σ (toUnit _ ≫ lev a) = toUnit _ ≫ c.lev a := fun a => (hσ _ _).2 (pt a)
  refine ⟨fun a => ?_, fun g hg => ?_, fun a b => ?_⟩
  · rw [← g₁ a, ← σlev, map_eq_one_iff σ σinj]
  · obtain ⟨a, ha⟩ := g₂ (σ g) (by rw [← map_pow, hg, map_one])
    exact ⟨a, σinj ((σlev a).trans ha)⟩
  · have hD := pull_isLB hP₀ (lift (𝟙 A₀) (𝟙 A₀)).left
    refine (T.weilPairing_fieldExtension_iff _ A₀ k Ω j' (spMap i') _ _ _ _ _ ab hD).1 ?_
    have H := (weilIs_grpPullback_of_comm _ _ A₀ c.A (spMap i) φ _ _ hD (pull_isLB c.isLB _) hp diag _ _ _ _
      (pushPt hφ _) (pushPt hφ _) _ rfl rfl).1 (g₃ a b)
    rw [map_zpow]
    exact weilIs_congr e.symm _ _ _ _ _ _ (pt a) (pt b) _ H

end GlobalTheory
