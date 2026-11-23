import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsHomFamilyComplex
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace Spread

section Bundles

variable {W X X' Y Z : Scheme.{0}}

theorem lbIso_pull_comp {L : LB X} {M : LB Z} {a : Y ⟶ X} {b : Y ⟶ Z} (j : W ⟶ Y) {a' : W ⟶ X} {b' : W ⟶ Z}
    (ha : a' = j ≫ a) (hb : b' = j ≫ b) (h : LBIso (L.pull a) (M.pull b)) : LBIso (L.pull a') (M.pull b') :=
  LBIso.chartPull (chartPullSame L _ _ _ j fun _ => ha) (chartPullSame M _ _ _ j fun _ => hb) h

theorem lbIso_pull_pull {L : LB X} (hL : L.IsLB) {a : Y ⟶ X} (j : W ⟶ Y) {a' : W ⟶ X} (ha : a' = j ≫ a) :
    LBIso (L.pull a') ((L.pull a).pull j) :=
  LBIso.chartPull (chartPullSame L _ _ _ j fun _ => ha) (chartPullPull _ j) (lbIso_refl (pull_isLB hL a))

theorem lbIso_pow_pull_comp {L : LB X} {L' : LB X'} (hL : L.IsLB) (hL' : L'.IsLB) {F : X' ⟶ X}
    (h : LBIso L' (L.pull F)) (g : Y ⟶ X') {a : Y ⟶ X} (ha : a = g ≫ F) (N : ℕ) :
    LBIso (lbPow (L'.pull g) N) ((lbPow L N).pull a) :=
  LBIso.trans (isLB_lbPow (pull_isLB hL' _) _) (isLB_lbPow (pull_isLB hL _) _) (pull_isLB (isLB_lbPow hL _) _)
    (lbIso_lbPow (LBIso.chartPull (chartPullPull L' g) (chartPullSame L _ _ _ g fun _ => ha) h) N)
    (lbIso_lbPow_pull hL a N)

end Bundles

variable {k A : Type} [Field k] [CommRing A] [Algebra k A] {B Z S : Scheme.{0}} (pB : B ⟶ Sp k) [QuasiCompact pB]
  [QuasiSeparated pB] (q : Z ⟶ S) [LocallyOfFinitePresentation q]

theorem exists_fg_over_lbIso {R₁ : Subalgebra k A} (h₁ : R₁.FG) (y : Sp R₁ ⟶ S)
    (Φ : pullback pB (spMap (algebraMap k A)) ⟶ Z) (hΦ : Φ ≫ q = pullback.snd _ _ ≫ spMap R₁.val.toRingHom ≫ y)
    {L : LB Z} {M : LB B} (hL : L.IsLB) (hM : M.IsLB) (H : LBIso (L.pull Φ) (M.pull (pullback.fst _ _))) :
    ∃ (R : Subalgebra k A) (h : R₁ ≤ R) (ψ : pullback pB (spMap (algebraMap k R)) ⟶ Z), R.FG ∧
      ψ ≫ q = pullback.snd _ _ ≫ spMap (Subalgebra.inclusion h).toRingHom ≫ y ∧ bcMap pB R.val ≫ ψ = Φ ∧
      LBIso (L.pull ψ) (M.pull (pullback.fst _ _)) := by
  have : Algebra.FiniteType k R₁ := (Subalgebra.fg_iff_finiteType _).1 h₁
  have : LocallyOfFinitePresentation (spMap (algebraMap k R₁)) :=
    HasRingHomProperty.Spec_iff.2 (RingHom.finitePresentation_algebraMap.2
      (Algebra.FinitePresentation.of_finiteType.1 this))
  let Φ₁ : pullback pB (spMap (algebraMap k A)) ⟶ pullback q y :=
    pullback.lift Φ (pullback.snd _ _ ≫ spMap R₁.val.toRingHom) (by rw [hΦ, Category.assoc])
  obtain ⟨R₂, ψ, h₂, le, hψ⟩ := exists_fg_forall_comp_eq pB (pullback.snd q y ≫ spMap (algebraMap k R₁))
    (fun _ : Unit => Φ₁) (fun _ => by
      rw [pullback.lift_snd_assoc, Category.assoc, spMap_algHom_comp, pullback.condition]) R₁ h₁
  obtain ⟨e₁, e₂⟩ := hψ ()
  have e₃ : ψ () ≫ pullback.snd q y = pullback.snd _ _ ≫ spMap (Subalgebra.inclusion le).toRingHom := by
    refine hom_ext_bcMap pB R₂.val Subtype.val_injective (spMap (algebraMap k R₁)) ?_ ?_
    · rw [Category.assoc, e₁, Category.assoc, spMap_algHom_comp, pullback.condition]
    · rw [← Category.assoc, e₂, pullback.lift_snd, bcMap_snd_assoc, spMap_comp_ring]
      rfl
  have e₄ : Φ = bcMap pB R₂.val ≫ ψ () ≫ pullback.fst q y := by rw [← Category.assoc, e₂, pullback.lift_fst]
  obtain ⟨R, le', hR, hI⟩ := exists_fg_lbIso pB h₂ (L.pull (ψ () ≫ pullback.fst q y)) (M.pull (pullback.fst _ _))
    (pull_isLB hL _) (pull_isLB hM _)
    (LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) (pull_isLB (pull_isLB hM _) _)
      (lbIso_pull_pull hL _ e₄).symm (LBIso.trans (pull_isLB hL _) (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _) H
        (lbIso_pull_pull hM _ (bcMap_fst pB R₂.val).symm)))
  refine ⟨R, le.trans le', bcMap pB (Subalgebra.inclusion le') ≫ ψ () ≫ pullback.fst q y, hR, ?_, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% e₃, bcMap_snd_assoc, ← Category.assoc (spMap _),
      spMap_comp_ring]
    rfl
  · rw [e₄, bcMap_comp_of_eq_assoc pB _ _ R₂.val fun _ => rfl]
  · exact LBIso.trans (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) (pull_isLB hM _) (lbIso_pull_pull hL _ rfl)
      (LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hM _) hI
        (lbIso_pull_pull hM _ (bcMap_fst pB (Subalgebra.inclusion le')).symm).symm)

theorem exists_fg_forall_over_lbIso {R₁ : Subalgebra k A} (h₁ : R₁.FG) (y : Sp R₁ ⟶ S) {J : Type} [Finite J]
    (Φ : J → (pullback pB (spMap (algebraMap k A)) ⟶ Z))
    (hΦ : ∀ i, Φ i ≫ q = pullback.snd _ _ ≫ spMap R₁.val.toRingHom ≫ y)
    {L : J → LB Z} {M : J → LB B} (hL : ∀ i, (L i).IsLB) (hM : ∀ i, (M i).IsLB)
    (H : ∀ i, LBIso ((L i).pull (Φ i)) ((M i).pull (pullback.fst _ _))) :
    ∃ (R : Subalgebra k A) (h : R₁ ≤ R), R.FG ∧ ∀ i, ∃ ψ : pullback pB (spMap (algebraMap k R)) ⟶ Z,
      ψ ≫ q = pullback.snd _ _ ≫ spMap (Subalgebra.inclusion h).toRingHom ≫ y ∧ bcMap pB R.val ≫ ψ = Φ i ∧
      LBIso ((L i).pull ψ) ((M i).pull (pullback.fst _ _)) := by
  choose R h ψ hR e₁ e₂ e₃ using fun i => exists_fg_over_lbIso pB q h₁ y (Φ i) (hΦ i) (hL i) (hM i) (H i)
  have hle (i) : R i ≤ R₁ ⊔ ⨆ i, R i := le_sup_of_le_right (le_iSup R i)
  refine ⟨R₁ ⊔ ⨆ i, R i, le_sup_left, h₁.sup (fg_iSup hR), fun i =>
    ⟨bcMap pB (Subalgebra.inclusion (hle i)) ≫ ψ i, ?_, ?_,
      lbIso_pull_comp _ rfl (bcMap_fst pB _).symm (e₃ i)⟩⟩
  · rw [Category.assoc, e₁, bcMap_snd_assoc, ← Category.assoc (spMap _), spMap_comp_ring]
    rfl
  · rw [bcMap_comp_of_eq_assoc pB _ _ (R i).val fun _ => rfl, e₂]

end Spread

namespace PureType

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem dualMapR_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    (Chart.dualMapR g).comp (Chart.dualMapR f) = Chart.dualMapR (g.comp f) := by
  refine RingHom.ext fun a => ?_
  ext <;> simp [Chart.dualMapR]

theorem IsHomFamily.descend {D : Datum H} {R R' : Type} [CommRing R] [CommRing R'] {f : R →+* R'}
    (hf : Function.Injective f) {t : SAB H (Sp R)} {t' : SAB H (Sp R')} {n : t'.G.left ⟶ t.G.left}
    (hn : IsGrpPullback t'.G t.G (spMap f) n) (hact : ∀ a, (t'.act.act a).left ≫ n = n ≫ (t.act.act a).left)
    {B : Over (Sp R)} {B' : Over (Sp R')} [GrpObj B] [GrpObj B'] [Flat B.hom] {β : B'.left ⟶ B.left}
    (hβ : IsGrpPullback B' B (spMap f) β) {M : LB B.left} {M' : LB B'.left} {v : epsR R ⟶ B} {v' : epsR R' ⟶ B'}
    (hv : v'.left ≫ β = spMap (Chart.dualMapR f) ≫ v.left) {L : Submodule (𝓞 E) D.La} {ρ : R} {S S' T : Set L}
    {φ' : L → (B' ⟶ t'.G)} (h : IsHomFamily t' B' M' v' L (f ρ) S' φ') (hT : AddSubgroup.closure T = ⊤) (hS : S ⊆ T)
    (hd : ∀ a ∈ T, ∃ ψ : B ⟶ t.G, (φ' a).left ≫ n = β ≫ ψ.left ∧ ∃ N : ℕ, 1 ≤ N ∧
      LBIso (lbPow (t.PP.L.pull ψ.left) N) (lbPow M (N * (D.EF (H.w0 • (a : D.La)) a).natAbs))) :
    ∃ φ : L → (B ⟶ t.G), (∀ a, (φ' a).left ≫ n = β ≫ (φ a).left) ∧ IsHomFamily t B M v L ρ S φ := by
  obtain ⟨h₁, h₂, h₃, h₄, -⟩ := h
  have := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom f) hf
  have := t.semi.separated
  let U : Over.mk (B'.hom ≫ spMap f) ⟶ B := Over.homMk β hβ.1.w
  let π := pushHom hn B'
  let α : (B ⟶ t.G) →* (Over.mk (B'.hom ≫ spMap f) ⟶ t.G) := preHom U
  have key : ∀ {x : B' ⟶ t'.G} {y : B ⟶ t.G}, α y = π x ↔ x.left ≫ n = β ≫ y.left :=
    ⟨fun e => (congrArg (fun z => z.left) e).symm, fun e => Over.OverMorphism.ext e.symm⟩
  have inj : Function.Injective α := fun x y e =>
    ExtUnique.over_hom_ext_of_isPullback hβ.1 (congrArg (fun z => z.left) e)
  have h0 : φ' 0 = 1 := mul_eq_left.1 ((h₂ 0 0).symm.trans (by rw [add_zero]))
  have all : ∀ a, π (φ' a) ∈ α.range := fun a => by
    induction (hT.ge trivial : a ∈ AddSubgroup.closure T) using AddSubgroup.closure_induction with
    | mem a ha => obtain ⟨ψ, e, -⟩ := hd a ha; exact ⟨ψ, key.2 e⟩
    | zero => rw [h0, map_one]; exact one_mem _
    | add a b _ _ ha hb => rw [h₂, map_mul]; exact mul_mem ha hb
    | neg a _ ha =>
      rw [eq_inv_of_mul_eq_one_left ((h₂ (-a) a).symm.trans (by rw [neg_add_cancel, h0])), map_inv]
      exact inv_mem ha
  choose φ hφ using all
  have hφ' := fun a => key.1 (hφ a)
  refine ⟨φ, hφ', fun a => ?_, fun a b => inj ?_, fun s a => inj ?_, fun a => ?_, fun a ha => ?_⟩
  · have := h₁ a
    exact ExtUnique.isMonHom_of_isGrpPullback hβ hn (φ' a) (φ a) (hφ' a)
  · rw [map_mul, hφ, hφ, hφ, h₂, map_mul]
  · rw [hφ]
    refine (key.2 ?_).symm
    rw [h₃, Over.comp_left, Over.comp_left, Category.assoc, hact, reassoc_of% hφ' a]
  · obtain ⟨u, hu, hw⟩ := h₄ a
    have e : (v' ≫ φ' a ≫ t'.act.act H.rt).left = spMap (epsScaleR (f ρ)) ≫ (v' ≫ φ' a).left := by
      rw [hw]; simpa using hu 0
    refine ⟨![CMCurveTest.scaleVec ρ (v ≫ φ a)], fun j => by fin_cases j; rfl, ?_⟩
    have e' : v ≫ φ a ≫ t.act.act H.rt = CMCurveTest.scaleVec ρ (v ≫ φ a) := by
      refine Over.OverMorphism.ext (Spread.tangent_ext f hf t.G.hom ((Over.w _).trans (Over.w _).symm) ?_)
      change _ ≫ v.left ≫ (φ a).left ≫ (t.act.act H.rt).left = _ ≫ spMap (epsScaleR ρ) ≫ v.left ≫ (φ a).left
      have e₂ : v'.left ≫ (φ' a).left ≫ (t'.act.act H.rt).left = spMap (epsScaleR (f ρ)) ≫ v'.left ≫ (φ' a).left := e
      rw [reassoc_of% LieCombBaseChange.dualMap_epsScale f ρ, ← reassoc_of% hv, ← reassoc_of% hv, ← hφ',
        ← reassoc_of% hφ' a, ← hact, reassoc_of% e₂]
    simpa using e'
  · obtain ⟨ψ, e, hN⟩ := hd a (hS ha)
    rwa [inj ((hφ a).trans (key.2 e).symm)]

end PureType

open PureType in

theorem cmPoint (hT : ThetaUnifAV) (hW : Out.WeilSt) : CMPoint := by
  intro E _ _ _ H D l Xo g ty FU i Pe hP k hk _ P₀ v₀ _ hv₀ PC ψ u₀ c hg hψ hL hu hc hΛ S hS R₀ hR₀
  obtain ⟨y', t', m', v', φ', hy', hyu, -, hv', hφ'⟩ :=
    cmPoint_complex hT hW E H D l Xo g ty FU i Pe hP k hk P₀ v₀ hv₀ PC ψ u₀ c hg hψ hL hu hc hΛ
  have hid : spMap (AlgHom.id k ℂ).toRingHom = 𝟙 _ := Spec.map_id _
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim _
  have := Xo.univ.t.semi.smooth
  have := P₀.isAb.proper
  have := P₀.isAb.smooth

  obtain ⟨R₁, y₁, h₁, le₁, hy₁⟩ := Spread.exists_fg_points
    (pullback.snd Xo.s (spMap (IntermediateField.inclusion hk).toRingHom))
    (fun _ : Unit => pullback.lift y' (spMap (algebraMap k ℂ)) (hy'.trans (spMap_comp_ring _ _).symm))
    (fun _ => pullback.lift_snd _ _ _) R₀ hR₀
  have e₁ : spMap R₁.val.toRingHom ≫ y₁ () ≫ pullback.fst _ _ = y' := by
    rw [← Category.assoc, (hy₁ ()).2, pullback.lift_fst]

  have gen : ∀ ε : ℤˣ, ∃ T : Set (lat hP (((ε : ℤ) : ℂ) * H.rt0)), AddSubgroup.closure T = ⊤ ∧ T.Finite := fun ε => by
    have := (FU.Di i).fin
    have : Module.Finite ℤ (lat hP (((ε : ℤ) : ℂ) * H.rt0)) := Module.Finite.trans (𝓞 E) _
    exact AddGroup.fg_iff.1 (Module.Finite.iff_addGroup_fg.1 this)
  choose T hT hTf using gen
  have : ∀ ε, Finite ↥(S ε ∪ T ε) := fun ε => ((hS ε).union (hTf ε)).to_subtype
  choose N hN hI using fun ε a => (hφ' ε).1.2.2.2.2 a trivial
  have hL' : LBIso t'.PP.L (Xo.univ.t.PP.L.pull m'.φ) := m'.lin.imp fun _ h => h.1
  have hP := Xo.univ.t.PP.isLB
  obtain ⟨R, le, hR, hψ⟩ := Spread.exists_fg_forall_over_lbIso P₀.A.hom Xo.univ.t.G.hom h₁ (y₁ () ≫ pullback.fst _ _)
    (J := Σ ε : ℤˣ, ↥(S ε ∪ T ε)) (fun a => (φ' a.1 a.2).left ≫ m'.φ)
    (fun a => by rw [e₁, Category.assoc, m'.cart.1.w, ← Category.assoc, Over.w]; rfl)
    (fun a => isLB_lbPow hP (N a.1 a.2)) (fun a => isLB_lbPow P₀.isLB _)
    (fun a => LBIso.trans (pull_isLB (isLB_lbPow hP _) _) (isLB_lbPow (pull_isLB t'.PP.isLB _) _)
      (pull_isLB (isLB_lbPow P₀.isLB _) _) (Spread.lbIso_pow_pull_comp hP t'.PP.isLB hL' _ rfl _).symm
      (LBIso.trans (isLB_lbPow (pull_isLB t'.PP.isLB _) _) (isLB_lbPow (pull_isLB P₀.isLB _) _)
        (pull_isLB (isLB_lbPow P₀.isLB _) _) (hI a.1 a.2) (lbIso_lbPow_pull P₀.isLB _ _)))
  set y : Sp R ⟶ Xo.X := spMap (Subalgebra.inclusion le).toRingHom ≫ y₁ () ≫ pullback.fst _ _ with hy
  have e₂ : spMap R.val.toRingHom ≫ y = y' := by
    rw [hy, ← Category.assoc, spMap_comp_ring]
    exact e₁
  obtain ⟨t, m, -⟩ : ∃ (t : SAB H (Sp R)) (m : SABMap t Xo.univ.t y), True := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull y Xo.univ.t
    exact ⟨_, m, trivial⟩
  subst e₂
  obtain ⟨n, hn⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m m'
  have hn' : m'.φ = n.φ ≫ m.φ := hn
  have hB := isGrpPullback_pullback P₀.A (spMap (algebraMap k R))
  have hβ : IsGrpPullback ((Over.pullback (spMap (algebraMap k ℂ))).obj P₀.A)
      ((Over.pullback (spMap (algebraMap k R))).obj P₀.A) (spMap R.val.toRingHom) (Spread.bcMap P₀.A.hom R.val) :=
    hB.cancel ((isGrpPullback_pullback P₀.A (spMap (algebraMap k ℂ))).congr (Spread.spMap_algHom_comp R.val).symm
      (Spread.bcMap_fst _ _).symm) (Spread.bcMap_snd _ _)
  obtain ⟨v, hv, hvv⟩ := exists_tangent_over _ hB hv₀
  have hvβ : v'.left ≫ Spread.bcMap P₀.A.hom R.val = spMap (Chart.dualMapR R.val.toRingHom) ≫ v.left := by
    apply pullback.hom_ext
    · rw [Category.assoc, Spread.bcMap_fst, hv', Category.assoc]
      erw [hvv]
      rw [← Category.assoc, spMap_comp_ring]
      congr 2
      exact (dualMapR_comp (algebraMap k R) R.val.toRingHom).symm
    · rw [Category.assoc, Spread.bcMap_snd, Category.assoc]
      exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (Over.w v'))).trans
        ((LieCombBaseChange.dualMap_over _).symm.trans (congrArg (_ ≫ ·) (Over.w v).symm))
  have : Flat ((Over.pullback (spMap (algebraMap k R))).obj P₀.A).hom :=
    inferInstanceAs (Flat (pullback.snd P₀.A.hom _))
  have hLm : LBIso t.PP.L (Xo.univ.t.PP.L.pull m.φ) := m.lin.imp fun _ h => h.1
  choose φ hφ hφ₁ using fun ε : ℤˣ => IsHomFamily.descend (f := R.val.toRingHom) Subtype.val_injective n.cart n.act hβ
    (M := P₀.L.pull (pullback.fst P₀.A.hom (spMap (algebraMap k R)))) hvβ
    (ρ := ((ε : ℤ) : R) * algebraMap k R (IntermediateField.inclusion hk (baseKA l).ρ)) (T := S ε ∪ T ε)
    (by rw [map_mul, map_intCast]; exact (hφ' ε).1)
    (top_le_iff.1 ((hT ε).ge.trans (AddSubgroup.closure_mono Set.subset_union_right))) Set.subset_union_left
    (fun a ha => by
      obtain ⟨χ, c₁, c₂, c₃⟩ := hψ ⟨ε, a, ha⟩
      have d₁ := m.cart.1.lift_fst χ _ c₁
      have d₂ := m.cart.1.lift_snd χ _ c₁
      refine ⟨Over.homMk (m.cart.1.lift χ _ c₁) d₂, m.cart.1.hom_ext ?_ ?_, N ε a, hN ε a, ?_⟩
      · exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hn'.symm)).trans (c₂.symm.trans
          ((congrArg (_ ≫ ·) d₁.symm).trans (Category.assoc _ _ _).symm))
      · rw [Category.assoc, Category.assoc, n.cart.1.w, Over.w, ← Category.assoc, Over.w]
        exact (Spread.bcMap_snd _ _).symm
      · exact LBIso.trans (isLB_lbPow (pull_isLB t.PP.isLB _) _) (pull_isLB (isLB_lbPow hP _) _)
          (isLB_lbPow (pull_isLB P₀.isLB _) _) (Spread.lbIso_pow_pull_comp hP t.PP.isLB hLm _ d₁.symm _)
          (LBIso.trans (pull_isLB (isLB_lbPow hP _) _) (pull_isLB (isLB_lbPow P₀.isLB _) _)
            (isLB_lbPow (pull_isLB P₀.isLB _) _) c₃ (lbIso_lbPow_pull P₀.isLB _ _).symm))
  refine ⟨R, hR, le₁.trans le, y, t, m, v, φ, ?_, (Category.id_comp _).symm.trans (hid ▸ hyu), hv, hvv,
    fun ε => ⟨hφ₁ ε, fun a z x hx hx' => ?_⟩⟩
  · rw [hy, Category.assoc, Category.assoc, pullback.condition, reassoc_of% (hy₁ ()).1, spMap_comp_ring,
      spMap_comp_ring]
    rfl
  · let x' : Sp ℂ ⟶ pullback P₀.A.hom (spMap (algebraMap k ℂ)) := pullback.lift (x ≫ pullback.fst _ _) (𝟙 _) (by
      rw [Category.assoc, pullback.condition, reassoc_of% hx', Spread.spMap_algHom_comp, Category.id_comp])
    have e : x' ≫ Spread.bcMap P₀.A.hom R.val = x := by
      apply pullback.hom_ext
      · rw [Category.assoc, Spread.bcMap_fst, pullback.lift_fst]
      · rw [Category.assoc, Spread.bcMap_snd, pullback.lift_snd_assoc, Category.id_comp, hx']
    rw [← (hφ' ε).2 a z x' ((pullback.lift_fst _ _ _).trans hx) ((pullback.lift_snd _ _ _).trans hid.symm), ← e, hn',
      Category.assoc]
    exact congrArg (x' ≫ ·) ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ m.φ) (hφ ε a).symm).trans
      (Category.assoc _ _ _)))

end GlobalTheory
