import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.TorRef GlobalTheory.FlagMod GlobalTheory.Reg GlobalTheory.PolFin
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem)
open MonoidalCategory CartesianMonoidalCategory MonObj Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GlueLie

section Lift

variable {X A : Scheme.{0}} (f : X ⟶ A) [IsOpenImmersion f] {S S' : Type} [CommRing S] [CommRing S']

theorem range_subset (U : X.Opens) (z : Sp S ⟶ A) (h : ⊤ ≤ z ⁻¹ᵁ (f ''ᵁ U)) : Set.range z ⊆ Set.range f := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, -, hy⟩ := h (Set.mem_univ x)
  exact ⟨y, hy⟩

def liftPt (U : X.Opens) (z : Sp S ⟶ A) (h : ⊤ ≤ z ⁻¹ᵁ (f ''ᵁ U)) : Sp S ⟶ X :=
  IsOpenImmersion.lift f z (range_subset f U z h)

@[reassoc (attr := simp)]
theorem liftPt_fac (U : X.Opens) (z : Sp S ⟶ A) (h : ⊤ ≤ z ⁻¹ᵁ (f ''ᵁ U)) : liftPt f U z h ≫ f = z :=
  IsOpenImmersion.lift_fac _ _ _

theorem liftPt_le (U : X.Opens) (z : Sp S ⟶ A) (h : ⊤ ≤ z ⁻¹ᵁ (f ''ᵁ U)) : ⊤ ≤ liftPt f U z h ⁻¹ᵁ U := by
  intro x _
  obtain ⟨y, hy, e⟩ := h (Set.mem_univ x)
  have e2 : f (liftPt f U z h x) = z x := by
    rw [← Scheme.Hom.comp_apply, liftPt_fac]
  have : y = liftPt f U z h x := f.isOpenEmbedding.injective (e.trans e2.symm)
  show liftPt f U z h x ∈ U
  exact this ▸ hy

theorem liftPt_comp (U : X.Opens) (x : Sp S ⟶ X) (h : ⊤ ≤ (x ≫ f) ⁻¹ᵁ (f ''ᵁ U)) : liftPt f U (x ≫ f) h = x := by
  rw [← cancel_mono f, liftPt_fac]

theorem spMap_liftPt (φ : S →+* S') (U : X.Opens) (z : Sp S ⟶ A) (h : ⊤ ≤ z ⁻¹ᵁ (f ''ᵁ U))
    (h' : ⊤ ≤ (spMap φ ≫ z) ⁻¹ᵁ (f ''ᵁ U)) : spMap φ ≫ liftPt f U z h = liftPt f U (spMap φ ≫ z) h' := by
  rw [← cancel_mono f, Category.assoc, liftPt_fac, liftPt_fac]

end Lift

section Cast

variable {X0 : Scheme.{0}} {G : Over X0} [GrpObj G] [IsCommMonObj G] {S : Type} [CommRing S]

def tanCast {x x' : Sp S ⟶ X0} (e : x = x') : TanM x G ≃ₗ[S] TanM x' G := by
  subst e; exact LinearEquiv.refl _ _

theorem tanCast_left {x x' : Sp S ⟶ X0} (e : x = x') (v : TanM x G) : (tv (tanCast e v)).left = (tv v).left := by
  subst e; rfl

end Cast

end GlobalTheory.GlueLie

namespace GlobalTheory.GlueLie

section Basis

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {A : Scheme.{0}} {G : Over A} [GrpObj G] [IsCommMonObj G] {f : Y.X ⟶ A} [IsOpenImmersion f]
  {F : Y.t.G.left ⟶ G.left} (hF : IsGrpPullback Y.t.G G f F) {S S' : Type} [CommRing S] [CommRing S']

def gBasis (M : MChart Y) (z : Sp S ⟶ A) (h : ⊤ ≤ z ⁻¹ᵁ (f ''ᵁ M.U)) : Module.Basis (Fin M.n) S (TanM z G) :=
  ((lieBasis M (liftPt f M.U z h) (liftPt_le f M.U z h)).map (tanEquiv hF _)).map (tanCast (liftPt_fac f M.U z h))

theorem gBasis_left (M : MChart Y) (z : Sp S ⟶ A) (h : ⊤ ≤ z ⁻¹ᵁ (f ''ᵁ M.U)) (j : Fin M.n) :
    (tv (gBasis hF M z h j)).left =
      spMap (dualMap (ev (liftPt f M.U z h) M.U (liftPt_le f M.U z h))) ≫ M.v₀ j ≫ F := by
  simp only [gBasis, Module.Basis.map_apply]
  rw [tanCast_left]
  show (tv (lieBasis M _ _ j)).left ≫ F = _
  rw [lieBasis_left, Category.assoc]

theorem gBasis_comp (M : MChart Y) (x : Sp S ⟶ Y.X) (h : ⊤ ≤ (x ≫ f) ⁻¹ᵁ (f ''ᵁ M.U)) (h₀ : ⊤ ≤ x ⁻¹ᵁ M.U)
    (j : Fin M.n) : gBasis hF M (x ≫ f) h j = tanEquiv hF x (lieBasis M x h₀ j) := by
  apply tan_ext_left
  rw [gBasis_left]
  show _ = (tv (lieBasis M x h₀ j)).left ≫ F
  rw [lieBasis_left, ev_congr (liftPt_comp f M.U x h), Category.assoc]

theorem gBasis_toMatrix (M M' : MChart Y) (x : Sp S ⟶ Y.X) (h : ⊤ ≤ (x ≫ f) ⁻¹ᵁ (f ''ᵁ M.U))
    (h' : ⊤ ≤ (x ≫ f) ⁻¹ᵁ (f ''ᵁ M'.U)) (h₀ : ⊤ ≤ x ⁻¹ᵁ M.U) (h₀' : ⊤ ≤ x ⁻¹ᵁ M'.U) :
    (gBasis hF M (x ≫ f) h).toMatrix (gBasis hF M' (x ≫ f) h') = (lieBasis M x h₀).toMatrix (lieBasis M' x h₀') := by
  have e1 : gBasis hF M (x ≫ f) h = (lieBasis M x h₀).map (tanEquiv hF x) :=
    Module.Basis.eq_of_apply_eq fun j => by rw [gBasis_comp hF M x h h₀, Module.Basis.map_apply]
  have e2 : gBasis hF M' (x ≫ f) h' = (lieBasis M' x h₀').map (tanEquiv hF x) :=
    Module.Basis.eq_of_apply_eq fun j => by rw [gBasis_comp hF M' x h' h₀', Module.Basis.map_apply]
  rw [e1, e2]
  ext i j
  simp [Module.Basis.toMatrix_apply]

theorem tanPull_gBasis (M : MChart Y) (φ : S →+* S') {z : Sp S ⟶ A} {z' : Sp S' ⟶ A} (e : spMap φ ≫ z = z')
    (h : ⊤ ≤ z ⁻¹ᵁ (f ''ᵁ M.U)) (h' : ⊤ ≤ z' ⁻¹ᵁ (f ''ᵁ M.U)) (j : Fin M.n) :
    tanPull φ e (gBasis hF M z h j) = gBasis hF M z' h' j := by
  subst e
  apply tan_ext_left
  rw [tanPull_left, gBasis_left, gBasis_left]
  have e1 := spMap_liftPt f φ M.U z h h'
  rw [← ev_congr e1 M.U (le_preimage_comp _ (liftPt_le f M.U z h)) (liftPt_le f M.U _ h'),
    ev_spMap φ _ M.U (liftPt_le f M.U z h), FlagMod.dualMap_comp, ← spMap_comp', Category.assoc]

end Basis

end GlobalTheory.GlueLie

namespace GlobalTheory.GlueLie

section Glue

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {I : Type} {R : I → Type} [∀ i, CommRing (R i)] {ω : ∀ i, R i →+* c.F}
  (C : ∀ i, Model Xo c (ω i)) {A : Scheme.{0}} {G : Over A} [GrpObj G] [IsCommMonObj G] (ψ : ∀ i, (C i).X ⟶ A)
  [∀ i, IsOpenImmersion (ψ i)] {F : ∀ i, (C i).t.G.left ⟶ G.left} (hF : ∀ i, IsGrpPullback (C i).t.G G (ψ i) (F i))
  {S : Type} [CommRing S]

def gU (a : Σ i, MChart (C i)) : A.Opens := ψ a.1 ''ᵁ a.2.U

theorem isAffineOpen_gU_inf [A.IsSeparated] (a b : Σ i, MChart (C i)) : IsAffineOpen (gU C ψ a ⊓ gU C ψ b) :=
  (a.2.hU.image_of_isOpenImmersion (ψ a.1)).inf (b.2.hU.image_of_isOpenImmersion (ψ b.1))

def gDet [A.IsSeparated] (a b : Σ i, MChart (C i)) : Γ(A, gU C ψ a ⊓ gU C ψ b)ˣ :=
  (isUnit_rdet_toMatrix (gBasis (hF a.1) a.2 (tau (isAffineOpen_gU_inf C ψ a b)) (tau_le _ inf_le_left))
    (gBasis (hF b.1) b.2 (tau (isAffineOpen_gU_inf C ψ a b)) (tau_le _ inf_le_right))).unit

def gLie [A.IsSeparated] : LB A := ⟨Σ i, MChart (C i), gU C ψ, gDet C ψ hF⟩

theorem ev_gDet [A.IsSeparated] (a b : Σ i, MChart (C i)) (z : Sp S ⟶ A) (h : ⊤ ≤ z ⁻¹ᵁ gU C ψ a)
    (h' : ⊤ ≤ z ⁻¹ᵁ gU C ψ b) (hh : ⊤ ≤ z ⁻¹ᵁ (gU C ψ a ⊓ gU C ψ b)) :
    ev z _ hh (gDet C ψ hF a b).val = rdet ((gBasis (hF a.1) a.2 z h).toMatrix (gBasis (hF b.1) b.2 z h')) := by
  have e : spMap (ev z _ hh) ≫ tau (isAffineOpen_gU_inf C ψ a b) = z := spMap_ev z _ hh
  refine (map_rdet _ _).trans (congrArg rdet ?_)
  ext i j
  have h1 := (gBasis (hF a.1) a.2 (tau (isAffineOpen_gU_inf C ψ a b)) (tau_le _ inf_le_left)).sum_toMatrix_smul_self
    (gBasis (hF b.1) b.2 (tau (isAffineOpen_gU_inf C ψ a b)) (tau_le _ inf_le_right)) j
  have h2 := congrArg (tanPull (G := G) _ e) h1
  rw [map_sum, tanPull_gBasis (hF b.1) b.2 _ e _ h'] at h2
  simp only [map_smulₛₗ, tanPull_gBasis (hF a.1) a.2 _ e _ h] at h2
  rw [Module.Basis.toMatrix_apply, ← h2, Module.Basis.repr_sum_self]
  rfl

theorem isLB_gLie [A.IsSeparated] (hc : ∀ i, (detLie (C i)).IsLB) (hcov : ∀ x : A, ∃ i, x ∈ Set.range (ψ i)) :
    (gLie C ψ hF).IsLB := by
  refine isLB_of_ev _ (eq_top_iff.2 fun x _ => ?_) fun a b d S _ z hab hbd had => ?_
  · obtain ⟨i, y, rfl⟩ := hcov x
    obtain ⟨M, hM⟩ := Opens.mem_iSup.1 ((hc i).cover.ge (Set.mem_univ y))
    exact Opens.mem_iSup.2 ⟨⟨i, M⟩, ⟨y, hM, rfl⟩⟩
  · have ha := le_preimage_mono inf_le_left hab
    have hb := le_preimage_mono inf_le_right hab
    have hd := le_preimage_mono inf_le_right hbd
    exact (congrArg₂ (· * ·) (ev_gDet C ψ hF a b z ha hb hab) (ev_gDet C ψ hF b d z hb hd hbd)).trans
      ((rdet_toMatrix_mul _ _ _).trans (ev_gDet C ψ hF a d z ha hd had).symm)

theorem lbIso_gLie_pull [A.IsSeparated] (i : I) : LBIso ((gLie C ψ hF).pull (ψ i)) (detLie (C i)) := by
  have le : ∀ (M : MChart (C i)) (J : ((gLie C ψ hF).pull (ψ i)).ι),
      M.U ⊓ ((gLie C ψ hF).pull (ψ i)).U J ≤ ψ i ⁻¹ᵁ (gU C ψ ⟨i, M⟩ ⊓ gU C ψ (J PUnit.unit)) := fun M J =>
    fun y hy => ⟨⟨y, hy.1, rfl⟩, LB.wchart_le (gLie C ψ hF) (fun _ : PUnit => ψ i) J PUnit.unit hy.2⟩
  refine ⟨⟨fun p => res (le p.1 p.2) (pullU (ψ i) _ (gDet C ψ hF ⟨i, p.1⟩ (p.2 PUnit.unit)))⟩, fun p q => ?_⟩
  refine Eq.trans ?_ (mul_right_comm _ _ _)
  refine eq_mul_inv_of_mul_eq (Units.ext (ext_ev fun S _ z hz => ?_))
  have hp := le_preimage_mono inf_le_left hz
  have hq := le_preimage_mono inf_le_right hz
  have hp1 : ⊤ ≤ z ⁻¹ᵁ (p.1 : MChart (C i)).U := le_preimage_mono inf_le_left hp
  have hq1 : ⊤ ≤ z ⁻¹ᵁ (q.1 : MChart (C i)).U := le_preimage_mono inf_le_left hq
  have hp2 : ⊤ ≤ z ⁻¹ᵁ ((gLie C ψ hF).pull (ψ i)).U p.2 := le_preimage_mono inf_le_right hp
  have hq2 : ⊤ ≤ z ⁻¹ᵁ ((gLie C ψ hF).pull (ψ i)).U q.2 := le_preimage_mono inf_le_right hq
  have hp3 := le_preimage_map (ψ i) (le p.1 p.2) hp
  have hq3 := le_preimage_map (ψ i) (le q.1 q.2) hq
  have a1 : ⊤ ≤ (z ≫ ψ i) ⁻¹ᵁ gU C ψ ⟨i, p.1⟩ := le_preimage_mono inf_le_left hp3
  have b1 : ⊤ ≤ (z ≫ ψ i) ⁻¹ᵁ gU C ψ (p.2 PUnit.unit) := le_preimage_mono inf_le_right hp3
  have a2 : ⊤ ≤ (z ≫ ψ i) ⁻¹ᵁ gU C ψ ⟨i, q.1⟩ := le_preimage_mono inf_le_left hq3
  have b2 : ⊤ ≤ (z ≫ ψ i) ⁻¹ᵁ gU C ψ (q.2 PUnit.unit) := le_preimage_mono inf_le_right hq3
  have g := ev_pull_g (gLie C ψ hF) (ψ i) z p.2 q.2 (le_preimage_inf hp2 hq2) (le_preimage_inf b1 b2)
  have sp : ev z _ hp (res (le p.1 p.2) (pullU (ψ i) _ (gDet C ψ hF ⟨i, p.1⟩ (p.2 PUnit.unit)))).val =
      ev (z ≫ ψ i) _ hp3 (gDet C ψ hF ⟨i, p.1⟩ (p.2 PUnit.unit)).val := by
    rw [← ev_appLE z (ψ i) (le p.1 p.2) hp hp3]; rfl
  have sq : ev z _ hq (res (le q.1 q.2) (pullU (ψ i) _ (gDet C ψ hF ⟨i, q.1⟩ (q.2 PUnit.unit)))).val =
      ev (z ≫ ψ i) _ hq3 (gDet C ψ hF ⟨i, q.1⟩ (q.2 PUnit.unit)).val := by
    rw [← ev_appLE z (ψ i) (le q.1 q.2) hq hq3]; rfl
  refine (map_mul (ev z _ hz) _ _).trans (Eq.trans ?_ (map_mul (ev z _ hz) _ _).symm)
  refine (congrArg₂ (· * ·) ((ev_res z _ hz hp _).trans (sp.trans (ev_gDet C ψ hF _ _ _ a1 b1 hp3)))
    ((ev_res z _ hz _ _).trans (g.trans (ev_gDet C ψ hF _ _ _ b1 b2 _)))).trans (Eq.trans ?_
    (congrArg₂ (· * ·) ((ev_res z _ hz (le_preimage_inf hp1 hq1) _).trans (ev_detChg _ _ z hp1 hq1 _))
      ((ev_res z _ hz hq _).trans (sq.trans (ev_gDet C ψ hF _ _ _ a2 b2 hq3)))).symm)
  exact (rdet_toMatrix_mul _ _ _).trans ((congrArg (rdet · * _)
    (gBasis_toMatrix (hF i) p.1 q.1 z a1 a2 hp1 hq1).symm).trans (rdet_toMatrix_mul _ _ _)).symm

end Glue

end GlobalTheory.GlueLie
