import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeG
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFiniteMchartCover
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NonemptyLift
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

noncomputable section

namespace GlobalTheory.FlagMod

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)

attribute [local instance] Over.cartesianMonoidalCategory

section Ev

variable {Z Z' : Scheme.{0}} {S S' : Type} [CommRing S] [CommRing S']

def ev (z : Sp S ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ z ⁻¹ᵁ U) : Γ(Z, U) →+* S :=
  (z.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom).hom

theorem ev_congr {z z' : Sp S ⟶ Z} (e : z = z') (U : Z.Opens) (h : ⊤ ≤ z ⁻¹ᵁ U) (h' : ⊤ ≤ z' ⁻¹ᵁ U) :
    ev z U h = ev z' U h' := by
  subst e; rfl

theorem ev_appLE (z : Sp S ⟶ Z') (π : Z' ⟶ Z) {U : Z.Opens} {V : Z'.Opens} (e : V ≤ π ⁻¹ᵁ U)
    (h : ⊤ ≤ z ⁻¹ᵁ V) (h' : ⊤ ≤ (z ≫ π) ⁻¹ᵁ U) (a : Γ(Z, U)) :
    ev z V h ((π.appLE U V e).hom a) = ev (z ≫ π) U h' a := by
  unfold ev
  rw [← Scheme.Hom.appLE_comp_appLE z π U V ⊤ e h]
  rfl

theorem ev_res (z : Sp S ⟶ Z) {U V : Z.Opens} (e : V ≤ U) (h : ⊤ ≤ z ⁻¹ᵁ V) (h' : ⊤ ≤ z ⁻¹ᵁ U) (a : Γ(Z, U)) :
    ev z V h (resG Z e a) = ev z U h' a := by
  unfold ev
  rw [← Scheme.Hom.map_appLE z h (homOfLE e).op]
  rfl

theorem ev_spMap (φ : S →+* S') (z : Sp S ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ z ⁻¹ᵁ U) (h' : ⊤ ≤ (spMap φ ≫ z) ⁻¹ᵁ U) :
    ev (spMap φ ≫ z) U h' = φ.comp (ev z U h) := by
  unfold ev
  rw [← Scheme.Hom.appLE_comp_appLE (spMap φ) z U ⊤ ⊤ h le_rfl, Category.assoc]
  have : (spMap φ).appLE ⊤ ⊤ le_rfl = (spMap φ).appTop := Scheme.Hom.appLE_eq_app _
  rw [this, Scheme.ΓSpecIso_naturality]
  rfl

theorem le_preimage_comp {T : Scheme.{0}} (g : T ⟶ Z') {z : Z' ⟶ Z} {U : Z.Opens} (h : ⊤ ≤ z ⁻¹ᵁ U) :
    ⊤ ≤ (g ≫ z) ⁻¹ᵁ U := fun x _ => h (Set.mem_univ (g x))

theorem le_preimage_map {T : Scheme.{0}} {z : T ⟶ Z'} (π : Z' ⟶ Z) {U : Z.Opens} {V : Z'.Opens} (e : V ≤ π ⁻¹ᵁ U)
    (h : ⊤ ≤ z ⁻¹ᵁ V) : ⊤ ≤ (z ≫ π) ⁻¹ᵁ U := fun x hx => e (h hx)

theorem le_preimage_mono {T : Scheme.{0}} {z : T ⟶ Z} {U V : Z.Opens} (e : V ≤ U)
    (h : ⊤ ≤ z ⁻¹ᵁ V) : ⊤ ≤ z ⁻¹ᵁ U := fun _ hx => e (h hx)

theorem le_preimage_inf {T : Scheme.{0}} {z : T ⟶ Z} {U V : Z.Opens} (h : ⊤ ≤ z ⁻¹ᵁ U)
    (h' : ⊤ ≤ z ⁻¹ᵁ V) : ⊤ ≤ z ⁻¹ᵁ (U ⊓ V) := fun _ hx => ⟨h hx, h' hx⟩

theorem spMap_ev (z : Sp S ⟶ Z) {U : Z.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ z ⁻¹ᵁ U) :
    spMap (ev z U h) ≫ hU.fromSpec = z := by
  have h1 := IsAffineOpen.SpecMap_appLE_fromSpec z hU (isAffineOpen_top (Sp S)) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h1
  show Spec.map (z.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom) ≫ hU.fromSpec = z
  rw [Spec.map_comp, Category.assoc, h1, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp]

def tau {U : Z.Opens} (hU : IsAffineOpen U) : Sp Γ(Z, U) ⟶ Z := hU.fromSpec

theorem tau_le {U V : Z.Opens} (hU : IsAffineOpen U) (e : U ≤ V) : ⊤ ≤ tau hU ⁻¹ᵁ V :=
  fun x _ => e (hU.range_fromSpec.le ⟨x, rfl⟩)

theorem ev_tau_self {U : Z.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ tau hU ⁻¹ᵁ U) : ev (tau hU) U h = RingHom.id _ := by
  have h1 := spMap_ev (tau hU) hU h
  have h2 : spMap (ev (tau hU) U h) = spMap (RingHom.id _) := by
    rw [← cancel_mono hU.fromSpec, h1]
    exact ((Category.id_comp _).symm.trans (congrArg (· ≫ hU.fromSpec) (Spec.map_id _).symm))
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h2)

theorem ev_tau {U V : Z.Opens} (hU : IsAffineOpen U) (e : U ≤ V) (h : ⊤ ≤ tau hU ⁻¹ᵁ V) (a : Γ(Z, V)) :
    ev (tau hU) V h a = resG Z e a := by
  rw [← ev_res (tau hU) e (tau_le hU le_rfl) h, ev_tau_self]
  rfl

theorem ev_spMap_tau {U : Z.Opens} (hU : IsAffineOpen U) (f : Γ(Z, U) →+* S) (h : ⊤ ≤ (spMap f ≫ tau hU) ⁻¹ᵁ U) :
    ev (spMap f ≫ tau hU) U h = f := by
  rw [ev_spMap f (tau hU) U (tau_le hU le_rfl), ev_tau_self]
  rfl

theorem ext_ev_loc {V : Z.Opens} {a b : Γ(Z, V)}
    (h : ∀ p ∈ V, ∃ N : Z.Opens, p ∈ N ∧ ∀ (S : Type) [CommRing S] (z : Sp S ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ V),
      ⊤ ≤ z ⁻¹ᵁ N → ev z V hz a = ev z V hz b) : a = b := by
  apply TopCat.Presheaf.section_ext Z.sheaf V
  intro p hp
  obtain ⟨N, hN, e⟩ := h p hp
  obtain ⟨_, ⟨W, hW, rfl⟩, hpW, hle⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (show p ∈ ((V ⊓ N : Z.Opens) : Set Z) from ⟨hp, hN⟩) (V ⊓ N).isOpen
  have hWV : W ≤ V := fun q hq => (hle hq).1
  have e0 := e _ (tau hW) (tau_le hW hWV) (tau_le hW fun q hq => (hle hq).2)
  rw [ev_tau hW hWV, ev_tau hW hWV] at e0
  have e1 := Z.presheaf.germ_res_apply (homOfLE hWV) p hpW a
  have e2 := Z.presheaf.germ_res_apply (homOfLE hWV) p hpW b
  exact e1.symm.trans ((congrArg _ e0).trans e2)

theorem ext_ev {V : Z.Opens} {a b : Γ(Z, V)}
    (h : ∀ (S : Type) [CommRing S] (z : Sp S ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ V), ev z V hz a = ev z V hz b) : a = b :=
  ext_ev_loc fun _ hp => ⟨V, hp, fun S _ z hz _ => h S z hz⟩

theorem isLB_of_ev (L : LB Z) (hc : ⨆ i, L.U i = ⊤)
    (h : ∀ (i j k : L.ι) (S : Type) [CommRing S] (z : Sp S ⟶ Z) (hij : ⊤ ≤ z ⁻¹ᵁ (L.U i ⊓ L.U j))
      (hjk : ⊤ ≤ z ⁻¹ᵁ (L.U j ⊓ L.U k)) (hik : ⊤ ≤ z ⁻¹ᵁ (L.U i ⊓ L.U k)),
      ev z _ hij (L.g i j).val * ev z _ hjk (L.g j k).val = ev z _ hik (L.g i k).val) : L.IsLB := by
  refine ⟨hc, fun i => Units.ext (ext_ev fun S _ z hz => ?_), fun i j k => Units.ext (ext_ev fun S _ z hz => ?_)⟩
  · have hii := le_preimage_inf hz hz
    have e := h i i i S z hii hii hii
    have hu : IsUnit (ev z _ hii (L.g i i).val) := (L.g i i).isUnit.map _
    have e1 : ev z _ hii (L.g i i).val = 1 := hu.mul_left_cancel (e.trans (_root_.mul_one _).symm)
    refine (ev_res z _ hz hii _).trans (e1.trans (map_one _).symm)
  · rw [Units.val_mul, map_mul]
    exact ((congrArg₂ (· * ·) (ev_res z _ hz _ _) (ev_res z _ hz _ _)).trans
      (h i j k S z (le_preimage_mono inf_le_left hz)
        (le_preimage_mono (le_inf (inf_le_left.trans inf_le_right) inf_le_right) hz)
        (le_preimage_mono (le_inf (inf_le_left.trans inf_le_left) inf_le_right) hz))).trans (ev_res z _ hz _ _).symm

theorem exists_chart_of_isLocalRing [IsLocalRing S] {J : Type} {U : J → Z.Opens} (hc : ⨆ i, U i = ⊤)
    (z : Sp S ⟶ Z) : ∃ i, ⊤ ≤ z ⁻¹ᵁ U i := by
  have : z (IsLocalRing.closedPoint S) ∈ ⨆ i, U i := by rw [hc]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
  exact ⟨i, ((IsLocalRing.closed_point_mem_iff (U := z ⁻¹ᵁ U i)).1 hi).ge⟩

end Ev

section Pull

variable {X0 : Scheme.{0}} {G : Over X0} [GrpObj G] [IsCommMonObj G] {S S' : Type} [CommRing S] [CommRing S']

def epsHom (φ : S →+* S') {x : Sp S ⟶ X0} {x' : Sp S' ⟶ X0} (h : spMap φ ≫ x = x') :
    overAt x' (DualNumber S') ⟶ overAt x (DualNumber S) :=
  Over.homMk (spMap (dualMap φ)) (by
    show spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x = spMap (algebraMap S' (DualNumber S')) ≫ x'
    rw [← h, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', dualMap_comp_alg])

omit [IsCommMonObj G] in
theorem smT_epsHom (φ : S →+* S') {x : Sp S ⟶ X0} {x' : Sp S' ⟶ X0} (h : spMap φ ≫ x = x') (a : S)
    (v : overAt x (DualNumber S) ⟶ G) : smT x' (φ a) (epsHom φ h ≫ v) = epsHom φ h ≫ smT x a v := by
  apply Over.OverMorphism.ext
  show spMap (epsMul (φ a)) ≫ spMap (dualMap φ) ≫ v.left = spMap (dualMap φ) ≫ spMap (epsMul a) ≫ v.left
  rw [← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', dualMap_comp_epsMul]

def tanPull (φ : S →+* S') {x : Sp S ⟶ X0} {x' : Sp S' ⟶ X0} (h : spMap φ ≫ x = x') :
    TanM x G →ₛₗ[φ] TanM x' G where
  toFun v := mkT (epsHom φ h ≫ tv v) (by
    rw [← map_zero φ, smT_epsHom, tv_mem, MonObj.comp_one])
  map_add' u v := tanM_ext (MonObj.comp_mul _ _ _)
  map_smul' a v := tanM_ext (smT_epsHom φ h a (tv v)).symm

theorem tanPull_left (φ : S →+* S') {x : Sp S ⟶ X0} {x' : Sp S' ⟶ X0} (h : spMap φ ≫ x = x') (v : TanM x G) :
    (tv (tanPull φ h v)).left = spMap (dualMap φ) ≫ (tv v).left := rfl

theorem tan_ext_left {x : Sp S ⟶ X0} {u v : TanM x G} (h : (tv u).left = (tv v).left) : u = v :=
  tanM_ext (Over.OverMorphism.ext h)

theorem tanPull_actR {O : Type} [CommRing O] (A : OAct O G) (φ : S →+* S') {x : Sp S ⟶ X0} {x' : Sp S' ⟶ X0}
    (h : spMap φ ≫ x = x') (a : O) (v : TanM x G) : tanPull φ h (actR A a v) = actR A a (tanPull φ h v) :=
  tanM_ext (Category.assoc _ _ _).symm

theorem tv_sum' {x : Sp S ⟶ X0} {κ : Type} (s : Finset κ) (f : κ → TanM x G) :
    tv (∑ i ∈ s, f i) = ∏ i ∈ s, tv (f i) := by
  simp only [tv, toMul_sum, Subgroup.val_finsetProd]

theorem dualMap_comp {S'' : Type} [CommRing S''] (φ : S →+* S') (ψ : S' →+* S'') :
    dualMap (ψ.comp φ) = (dualMap ψ).comp (dualMap φ) := by
  apply RingHom.ext
  intro r
  ext <;> simp [dualMap]

end Pull

section Basis

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

variable {S S' : Type} [CommRing S] [CommRing S']

theorem exists_lieBasis (M : MChart Y) (x : Sp S ⟶ Y.X) (h : ⊤ ≤ x ⁻¹ᵁ M.U) :
    ∃ b : Module.Basis (Fin M.n) S (TanM x Y.t.G),
      (∀ j, (tv (b j)).left = spMap (dualMap (ev x M.U h)) ≫ M.v₀ j) ∧
      ∀ a j, actR Y.t.act a (b j) = ∑ i, ev x M.U h (M.ρ a i j) • b i := by
  have key : ∀ (f : Γ(Y.X, M.U) →+* S) (x : Sp S ⟶ Y.X), spMap f ≫ M.hU.fromSpec = x →
      ∃ b : Module.Basis (Fin M.n) S (TanM x Y.t.G), (∀ j, (tv (b j)).left = spMap (dualMap f) ≫ M.v₀ j) ∧
      ∀ a j, actR Y.t.act a (b j) = ∑ i, f (M.ρ a i j) • b i := by
    rintro f _ rfl
    have hp : ∃ t' : SAB H (Sp S), Nonempty (SABMap t' Y.t (spMap f ≫ M.hU.fromSpec)) := by
      obtain ⟨PP', cub, sym, adj, prim, m, -⟩ :=
        sabPull ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull (spMap f ≫ M.hU.fromSpec) Y.t
      exact ⟨_, ⟨m⟩⟩
    obtain ⟨t', ⟨m⟩⟩ := hp
    obtain ⟨v', hv', hb, hact⟩ := M.lie S f _ m
    let u : Fin M.n → TanM (spMap f ≫ M.hU.fromSpec) Y.t.G := fun j =>
      mkT (pushHom m.cart (epsR S) (v' j)) ((PullbackSections.isTangent_iff m.cart _).1 (hb.1 j))
    have hcomb : ∀ (a : Fin M.n → S) (w : epsR S ⟶ t'.G), IsLieComb a v' w ↔
        pushHom m.cart (epsR S) w = tv (∑ i, a i • u i) := fun a w => by
      rw [PullbackSections.isLieComb_iff m.cart, tv_sum']
      rfl
    have hbij : Function.Bijective (Fintype.linearCombination S u) := by
      rw [Function.bijective_iff_existsUnique]
      intro W
      obtain ⟨p, hp⟩ := PullbackSections.push_surj m.cart (tv W)
      have ht : IsTangent p := (PullbackSections.isTangent_iff m.cart p).2 (by rw [hp]; exact tv_mem W)
      refine (existsUnique_congr fun a => ?_).1 (hb.2 p ht)
      rw [hcomb, hp, Fintype.linearCombination_apply]
      exact ⟨fun e => (tanM_ext e).symm, fun e => by rw [e]⟩
    let e := LinearEquiv.ofBijective _ hbij
    have he : ∀ j, (Pi.basisFun S (Fin M.n)).map e j = u j := fun j => by
      simp [e, Fintype.linearCombination_apply_single]
    refine ⟨(Pi.basisFun S (Fin M.n)).map e, fun j => by rw [he]; exact hv' j, fun a j => ?_⟩
    simp only [he]
    apply tanM_ext
    rw [← (hcomb _ _).1 (hact a j)]
    apply Over.OverMorphism.ext
    show ((v' j).left ≫ m.φ) ≫ (Y.t.act.act a).left = ((v' j).left ≫ _) ≫ m.φ
    rw [Category.assoc, Category.assoc, m.act]
  exact key _ x (spMap_ev x M.hU h)

def lieBasis (M : MChart Y) (x : Sp S ⟶ Y.X) (h : ⊤ ≤ x ⁻¹ᵁ M.U) : Module.Basis (Fin M.n) S (TanM x Y.t.G) :=
  (exists_lieBasis M x h).choose

theorem lieBasis_left (M : MChart Y) (x : Sp S ⟶ Y.X) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (j : Fin M.n) :
    (tv (lieBasis M x h j)).left = spMap (dualMap (ev x M.U h)) ≫ M.v₀ j :=
  (exists_lieBasis M x h).choose_spec.1 j

theorem actR_lieBasis (M : MChart Y) (x : Sp S ⟶ Y.X) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (a : 𝓞 E) (j : Fin M.n) :
    actR Y.t.act a (lieBasis M x h j) = ∑ i, ev x M.U h (M.ρ a i j) • lieBasis M x h i :=
  (exists_lieBasis M x h).choose_spec.2 a j

theorem tanPull_lieBasis (M : MChart Y) (φ : S →+* S') {x : Sp S ⟶ Y.X} {x' : Sp S' ⟶ Y.X} (e : spMap φ ≫ x = x')
    (h : ⊤ ≤ x ⁻¹ᵁ M.U) (h' : ⊤ ≤ x' ⁻¹ᵁ M.U) (j : Fin M.n) :
    tanPull φ e (lieBasis M x h j) = lieBasis M x' h' j := by
  subst e
  apply tan_ext_left
  rw [tanPull_left, lieBasis_left, lieBasis_left, ev_spMap φ x M.U h, dualMap_comp, ← spMap_comp', Category.assoc]

def vec (M : MChart Y) (x : Sp S ⟶ Y.X) (h : ⊤ ≤ x ⁻¹ᵁ M.U) : (Fin M.n → S) ≃ₗ[S] TanM x Y.t.G :=
  (lieBasis M x h).equivFun.symm

theorem vec_apply (M : MChart Y) (x : Sp S ⟶ Y.X) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (cv : Fin M.n → S) :
    vec M x h cv = ∑ j, cv j • lieBasis M x h j := Module.Basis.equivFun_symm_apply _ _

theorem tanPull_vec (M : MChart Y) (φ : S →+* S') {x : Sp S ⟶ Y.X} {x' : Sp S' ⟶ Y.X} (e : spMap φ ≫ x = x')
    (h : ⊤ ≤ x ⁻¹ᵁ M.U) (h' : ⊤ ≤ x' ⁻¹ᵁ M.U) (cv : Fin M.n → S) :
    tanPull φ e (vec M x h cv) = vec M x' h' (fun j => φ (cv j)) := by
  rw [vec_apply, vec_apply, map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smulₛₗ, tanPull_lieBasis M φ e h h']

theorem actR_vec (M : MChart Y) (x : Sp S ⟶ Y.X) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (a : 𝓞 E) (cv : Fin M.n → S) :
    actR Y.t.act a (vec M x h cv) = vec M x h (((M.ρ a).map (ev x M.U h)).mulVec cv) := by
  rw [vec_apply, vec_apply, map_sum]
  simp only [map_smul, actR_lieBasis, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Matrix.map_apply,
    Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [_root_.mul_comm]

theorem isAffineOpen_inf (M M' : MChart Y) : IsAffineOpen (M.U ⊓ M'.U) := by
  have := projProper _ _ _ Y.proj
  have : Y.X.IsSeparated := ⟨by
    rw [← terminal.comp_from Y.s]
    infer_instance⟩
  exact M.hU.inf M'.hU

def chg (M M' : MChart Y) : Matrix (Fin M.n) (Fin M'.n) Γ(Y.X, M.U ⊓ M'.U) :=
  (lieBasis M (tau (isAffineOpen_inf M M')) (tau_le _ inf_le_left)).toMatrix
    (lieBasis M' (tau (isAffineOpen_inf M M')) (tau_le _ inf_le_right))

theorem chg_map (M M' : MChart Y) (x : Sp S ⟶ Y.X) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (h' : ⊤ ≤ x ⁻¹ᵁ M'.U)
    (hh : ⊤ ≤ x ⁻¹ᵁ (M.U ⊓ M'.U)) :
    (chg M M').map (ev x _ hh) = (lieBasis M x h).toMatrix (lieBasis M' x h') := by
  have e : spMap (ev x _ hh) ≫ tau (isAffineOpen_inf M M') = x := spMap_ev x _ hh
  ext i j
  have h1 := (lieBasis M (tau (isAffineOpen_inf M M')) (tau_le _ inf_le_left)).sum_toMatrix_smul_self
    (lieBasis M' (tau (isAffineOpen_inf M M')) (tau_le _ inf_le_right)) j
  have h2 := congrArg (tanPull (G := Y.t.G) _ e) h1
  rw [map_sum, tanPull_lieBasis M' _ e _ h'] at h2
  simp only [map_smulₛₗ, tanPull_lieBasis M _ e _ h] at h2
  rw [Module.Basis.toMatrix_apply, ← h2, Module.Basis.repr_sum_self]
  rfl

theorem vec_chg (M M' : MChart Y) (x : Sp S ⟶ Y.X) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (h' : ⊤ ≤ x ⁻¹ᵁ M'.U)
    (hh : ⊤ ≤ x ⁻¹ᵁ (M.U ⊓ M'.U)) (cv : Fin M'.n → S) :
    vec M x h (((chg M M').map (ev x _ hh)).mulVec cv) = vec M' x h' cv := by
  rw [chg_map M M' x h h' hh]
  apply (lieBasis M x h).equivFun.injective
  rw [vec, LinearEquiv.apply_symm_apply, vec_apply, map_sum]
  funext i
  simp [Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, Finset.sum_apply, _root_.mul_comm]

end Basis

section Det

variable {R R' : Type} [CommRing R] [CommRing R']

def rdet {n n' : ℕ} (A : Matrix (Fin n) (Fin n') R) : R :=
  if h : n = n' then (A.submatrix id (Fin.cast h)).det else 1

theorem rdet_self {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : rdet A = A.det := by
  rw [rdet, dif_pos rfl]; rfl

theorem map_rdet (φ : R →+* R') {n n' : ℕ} (A : Matrix (Fin n) (Fin n') R) : φ (rdet A) = rdet (A.map φ) := by
  by_cases h : n = n'
  · subst h
    rw [rdet_self, rdet_self, RingHom.map_det]; rfl
  · rw [rdet, rdet, dif_neg h, dif_neg h, map_one]

variable {N : Type} [AddCommGroup N] [Module R N]

theorem rdet_toMatrix_mul {n₁ n₂ n₃ : ℕ} (b₁ : Module.Basis (Fin n₁) R N) (b₂ : Module.Basis (Fin n₂) R N)
    (b₃ : Module.Basis (Fin n₃) R N) :
    rdet (b₁.toMatrix b₂) * rdet (b₂.toMatrix b₃) = rdet (b₁.toMatrix b₃) := by
  nontriviality R
  obtain rfl : n₁ = n₂ := by simpa using Fintype.card_congr (b₁.indexEquiv b₂)
  obtain rfl : n₁ = n₃ := by simpa using Fintype.card_congr (b₁.indexEquiv b₃)
  rw [rdet_self, rdet_self, rdet_self, ← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix]

theorem isUnit_rdet_toMatrix {n₁ n₂ : ℕ} (b₁ : Module.Basis (Fin n₁) R N) (b₂ : Module.Basis (Fin n₂) R N) :
    IsUnit (rdet (b₁.toMatrix b₂)) := by
  have h := rdet_toMatrix_mul b₁ b₂ b₁
  rw [Module.Basis.toMatrix_self, rdet_self, Matrix.det_one] at h
  exact IsUnit.of_mul_eq_one _ h

end Det

section Lines

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

variable {S : Type} [CommRing S]

def detChg (M M' : MChart Y) : Γ(Y.X, M.U ⊓ M'.U)ˣ := (isUnit_rdet_toMatrix
  (lieBasis M (tau (isAffineOpen_inf M M')) (tau_le _ inf_le_left))
  (lieBasis M' (tau (isAffineOpen_inf M M')) (tau_le _ inf_le_right))).unit

theorem detChg_val (M M' : MChart Y) : (detChg M M').val = rdet (chg M M') := rfl

theorem ev_detChg (M M' : MChart Y) (x : Sp S ⟶ Y.X) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (h' : ⊤ ≤ x ⁻¹ᵁ M'.U)
    (hh : ⊤ ≤ x ⁻¹ᵁ (M.U ⊓ M'.U)) :
    ev x _ hh (detChg M M').val = rdet ((lieBasis M x h).toMatrix (lieBasis M' x h')) := by
  rw [detChg_val, map_rdet, chg_map M M' x h h']

theorem ev_detChg_mul (M M' M'' : MChart Y) (x : Sp S ⟶ Y.X) (h₁ : ⊤ ≤ x ⁻¹ᵁ (M.U ⊓ M'.U))
    (h₂ : ⊤ ≤ x ⁻¹ᵁ (M'.U ⊓ M''.U)) (h₃ : ⊤ ≤ x ⁻¹ᵁ (M.U ⊓ M''.U)) :
    ev x _ h₁ (detChg M M').val * ev x _ h₂ (detChg M' M'').val = ev x _ h₃ (detChg M M'').val := by
  rw [ev_detChg M M' x (le_preimage_mono inf_le_left h₁) (le_preimage_mono inf_le_right h₁),
    ev_detChg M' M'' x (le_preimage_mono inf_le_right h₁) (le_preimage_mono inf_le_right h₂),
    ev_detChg M M'' x (le_preimage_mono inf_le_left h₁) (le_preimage_mono inf_le_right h₂), rdet_toMatrix_mul]

structure GChart (Y : Model Xo c β) extends MChart Y where
  gen : ∀ (W : Y.X.Opens) (hW : W ≤ U), ∀ s ∈ secOn Y.t.PP.L (Y.t.G.hom ⁻¹ᵁ W), ∃! a : Γ(Y.X, W), ∀ i,
    s i = (Y.t.G.hom.appLE W (Y.t.G.hom ⁻¹ᵁ W ⊓ Y.t.PP.L.U i) inf_le_left).hom a *
      resG Y.t.G.left (inf_le_inf_right _ (Y.t.G.hom.preimage_mono hW)) (θ i)

theorem resG_resG {Z : Scheme.{0}} {U V W : Z.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(Z, U)) :
    resG Z h' (resG Z h a) = resG Z (h'.trans h) a :=
  ext_ev fun _ _ z hz => by
    rw [ev_res z h' hz (le_preimage_mono h' hz), ev_res z h _ (le_preimage_mono (h'.trans h) hz), ev_res z _ hz]

theorem exists_gChart [IsNoetherianRing O] (hP : PushInvertible Y.t.G Y.t.PP.L) (x : Y.X) :
    ∃ M : GChart Y, x ∈ M.U := by
  obtain ⟨J, -, MM, hM⟩ := exists_finite_mchart_cover E H Dw l Xo c O β Y hP
  obtain ⟨j, hx⟩ := hM x
  generalize MM j = M at hx
  have := projProper _ _ _ Y.proj
  have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  have : GlobalTheory.IsNormalScheme Y.X := GlobalTheory.IsNormalScheme.of_pred Y.normal
  obtain ⟨W, hxW, hW⟩ := GlobalTheory.ModelChart.exists_open_isDomain Y.X x
  obtain ⟨V, hxV, θ, hθ, hg, nz⟩ := hP x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hle⟩ := Y.X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ ((M.U ⊓ (W ⊓ V) : Y.X.Opens) : Set Y.X) from ⟨hx, hxW, hxV⟩) (M.U ⊓ (W ⊓ V)).isOpen
  have hUM : U ≤ M.U := fun q hq => (hle hq).1
  have hUV : U ≤ V := fun q hq => (hle hq).2.2
  let r : Γ(Y.X, M.U) →+* Γ(Y.X, U) := ev (tau hU) M.U (tau_le hU hUM)
  have hr : spMap r ≫ M.hU.fromSpec = hU.fromSpec := spMap_ev (tau hU) M.hU _
  refine ⟨⟨⟨U, hU, hW U hxU fun q hq => (hle hq).2.1, _,
    GlobalTheory.ModelChart.res_mem_secOn _ (Y.t.G.hom.preimage_mono hUV) hθ, fun y hy => ?_, M.n,
    fun j => spMap (dualMap r) ≫ M.v₀ j, fun a => (M.ρ a).map r, fun R' _ f t' m => ?_⟩, fun W' hW' s hs => ?_⟩, hxU⟩
  · obtain ⟨g, i, rfl, hg⟩ := nz y (hUV hy)
    refine ⟨g, i, rfl, ?_⟩
    show g ∈ Y.t.G.left.basicOpen (Y.t.G.left.presheaf.map (homOfLE _).op (θ i))
    rw [Scheme.basicOpen_res]
    exact ⟨⟨hy, (Y.t.G.left.basicOpen_le _ hg).2⟩, hg⟩
  · have cast : ∀ (p q : Sp R' ⟶ Y.X) (_ : p = q) (n : SABMap t' Y.t p), ∃ n' : SABMap t' Y.t q, n'.φ = n.φ := by
      rintro p q rfl n
      exact ⟨n, rfl⟩
    obtain ⟨m', hm'⟩ := cast _ (spMap (f.comp r) ≫ M.hU.fromSpec)
      (by rw [← spMap_comp', Category.assoc, hr]) m
    obtain ⟨v', hv', hb, ha⟩ := M.lie R' (f.comp r) t' m'
    refine ⟨v', fun j => ?_, hb, ha⟩
    rw [← hm', hv']
    show spMap (dualMap (f.comp r)) ≫ _ = spMap (dualMap f) ≫ _
    rw [dualMap_comp, ← spMap_comp', Category.assoc]
  · simp only [resG_resG]
    exact hg W' (hW'.trans hUV) s hs

def thRat (M M' : GChart Y) : Γ(Y.X, M.U ⊓ M'.U) :=
  (M.gen _ inf_le_left _
    (GlobalTheory.ModelChart.res_mem_secOn _ (Y.t.G.hom.preimage_mono inf_le_right) M'.θ_mem)).exists.choose

theorem ev_thRat (M M' : GChart Y) (g : Sp S ⟶ Y.t.G.left) (i : Y.t.PP.L.ι)
    (h : ⊤ ≤ g ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U i)) (h' : ⊤ ≤ g ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ M'.U ⊓ Y.t.PP.L.U i))
    (hh : ⊤ ≤ (g ≫ Y.t.G.hom) ⁻¹ᵁ (M.U ⊓ M'.U)) :
    ev g _ h' (M'.θ i) = ev (g ≫ Y.t.G.hom) _ hh (thRat M M') * ev g _ h (M.θ i) := by
  have hg : ⊤ ≤ g ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ (M.U ⊓ M'.U) ⊓ Y.t.PP.L.U i) := fun p hp => ⟨⟨(h hp).1, (h' hp).1⟩, (h hp).2⟩
  have e := congrArg (ev g _ hg) ((M.gen _ inf_le_left _
    (GlobalTheory.ModelChart.res_mem_secOn _ (Y.t.G.hom.preimage_mono inf_le_right) M'.θ_mem)).exists.choose_spec i)
  rw [map_mul, ev_res g _ hg h', ev_res g _ hg h, ev_appLE g _ _ hg hh] at e
  exact e

theorem thRat_unique (M M' : GChart Y) {W : Y.X.Opens} (hW : W ≤ M.U) (hW' : W ≤ M'.U) {a b : Γ(Y.X, W)}
    (H : ∀ e ∈ ({a, b} : Set Γ(Y.X, W)), ∀ (S : Type) [CommRing S] (g : Sp S ⟶ Y.t.G.left) (i : Y.t.PP.L.ι)
      (h : ⊤ ≤ g ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U i)) (h' : ⊤ ≤ g ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ M'.U ⊓ Y.t.PP.L.U i))
      (hh : ⊤ ≤ (g ≫ Y.t.G.hom) ⁻¹ᵁ W), ev g _ h' (M'.θ i) = ev (g ≫ Y.t.G.hom) _ hh e * ev g _ h (M.θ i)) :
    a = b := by
  have key : ∀ e ∈ ({a, b} : Set Γ(Y.X, W)), ∀ i,
      resG Y.t.G.left (inf_le_inf_right _ (Y.t.G.hom.preimage_mono hW')) (M'.θ i) =
      (Y.t.G.hom.appLE W (Y.t.G.hom ⁻¹ᵁ W ⊓ Y.t.PP.L.U i) inf_le_left).hom e *
        resG Y.t.G.left (inf_le_inf_right _ (Y.t.G.hom.preimage_mono hW)) (M.θ i) := fun e he i =>
    ext_ev fun S _ g hg => by
      have h := le_preimage_mono (inf_le_inf_right _ (Y.t.G.hom.preimage_mono hW)) hg
      have h' := le_preimage_mono (inf_le_inf_right _ (Y.t.G.hom.preimage_mono hW')) hg
      have hh := le_preimage_map Y.t.G.hom inf_le_left hg
      rw [map_mul, ev_res g _ hg h', ev_res g _ hg h, ev_appLE g _ _ hg hh]
      exact H e he S g i h h' hh
  exact (M.gen W hW _ (GlobalTheory.ModelChart.res_mem_secOn _ (Y.t.G.hom.preimage_mono hW') M'.θ_mem)).unique
    (key a (by simp)) (key b (by simp))

theorem thRat_mul (M M' M'' : GChart Y) {W : Y.X.Opens} (h₁ : W ≤ M.U ⊓ M'.U) (h₂ : W ≤ M'.U ⊓ M''.U)
    (h₃ : W ≤ M.U ⊓ M''.U) :
    resG _ h₁ (thRat M M') * resG _ h₂ (thRat M' M'') = resG _ h₃ (thRat M M'') := by
  refine thRat_unique M M'' (h₁.trans inf_le_left) (h₂.trans inf_le_right) ?_
  intro e he S _ g i h h'' hh
  have h' : ⊤ ≤ g ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ M'.U ⊓ Y.t.PP.L.U i) := fun p hp => ⟨(h₁ (hh hp)).2, (h hp).2⟩
  rcases he with rfl | rfl
  · rw [map_mul, ev_res _ h₁ hh (le_preimage_mono h₁ hh), ev_res _ h₂ hh (le_preimage_mono h₂ hh),
      ev_thRat M' M'' g i h' h'' (le_preimage_mono h₂ hh), ev_thRat M M' g i h h' (le_preimage_mono h₁ hh)]
    ring
  · rw [ev_res _ h₃ hh (le_preimage_mono h₃ hh), ev_thRat M M'' g i h h'' (le_preimage_mono h₃ hh)]

theorem thRat_self (M : GChart Y) : thRat M M = 1 := by
  refine thRat_unique M M inf_le_left inf_le_left ?_
  intro e he S _ g i h h' hh
  rcases he with rfl | rfl
  · exact ev_thRat M M g i h h' hh
  · rw [map_one, _root_.one_mul]

theorem isUnit_thRat (M M' : GChart Y) : IsUnit (thRat M M') := by
  have h := thRat_mul M M' M (W := M.U ⊓ M'.U) le_rfl (le_inf inf_le_right inf_le_left) (le_inf inf_le_left inf_le_left)
  rw [thRat_self, map_one] at h
  have e : resG Y.X (le_rfl : M.U ⊓ M'.U ≤ M.U ⊓ M'.U) (thRat M M') = thRat M M' :=
    ext_ev fun _ _ z hz => ev_res z _ hz hz _
  rw [e] at h
  exact IsUnit.of_mul_eq_one _ h

def thUnit (M M' : GChart Y) : Γ(Y.X, M.U ⊓ M'.U)ˣ := (isUnit_thRat M M').unit

theorem thUnit_val (M M' : GChart Y) : (thUnit M M').val = thRat M M' := rfl

theorem ev_thRat_mul (M M' M'' : GChart Y) (x : Sp S ⟶ Y.X) (h₁ : ⊤ ≤ x ⁻¹ᵁ (M.U ⊓ M'.U))
    (h₂ : ⊤ ≤ x ⁻¹ᵁ (M'.U ⊓ M''.U)) (h₃ : ⊤ ≤ x ⁻¹ᵁ (M.U ⊓ M''.U)) :
    ev x _ h₁ (thRat M M') * ev x _ h₂ (thRat M' M'') = ev x _ h₃ (thRat M M'') := by
  have hW : ⊤ ≤ x ⁻¹ᵁ (M.U ⊓ M'.U ⊓ M''.U) := le_preimage_inf h₁ (le_preimage_mono inf_le_right h₂)
  have e := congrArg (ev x _ hW) (thRat_mul M M' M'' (W := M.U ⊓ M'.U ⊓ M''.U) inf_le_left
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (le_inf (inf_le_left.trans inf_le_left) inf_le_right))
  rwa [map_mul, ev_res x _ hW h₁, ev_res x _ hW h₂, ev_res x _ hW h₃] at e

theorem ev_unit_inv {Z : Scheme.{0}} (z : Sp S ⟶ Z) {U : Z.Opens} (h : ⊤ ≤ z ⁻¹ᵁ U) (u : Γ(Z, U)ˣ) :
    ev z U h (u⁻¹).val = ((Units.map (ev z U h).toMonoidHom u)⁻¹).val := rfl

variable (Y)

def detLie : LB Y.X := ⟨MChart Y, fun M => M.U, detChg⟩

def detOm : LB Y.X := GlobalTheory.CechPic.dual (detLie Y)

def pushPP : LB Y.X := ⟨GChart Y, fun M => M.U, thUnit⟩

def de : LB Y.X := GlobalTheory.CechPic.dual (pushPP Y)

variable {Y}

theorem isLB_detLie [IsNoetherianRing O] (hP : PushInvertible Y.t.G Y.t.PP.L) : (detLie Y).IsLB :=
  isLB_of_ev _ (eq_top_iff.2 fun x _ => (exists_gChart hP x).elim fun M hM =>
      TopologicalSpace.Opens.mem_iSup.2 ⟨M.toMChart, hM⟩)
    fun i j k _ _ z => ev_detChg_mul i j k z

theorem isLB_detOm [IsNoetherianRing O] (hP : PushInvertible Y.t.G Y.t.PP.L) : (detOm Y).IsLB :=
  GlobalTheory.CechPic.isLB_dual (isLB_detLie hP)

theorem isLB_pushPP [IsNoetherianRing O] (hP : PushInvertible Y.t.G Y.t.PP.L) : (pushPP Y).IsLB :=
  isLB_of_ev _ (eq_top_iff.2 fun x _ => (exists_gChart hP x).elim fun M hM =>
      TopologicalSpace.Opens.mem_iSup.2 ⟨M, hM⟩)
    fun i j k _ _ z => ev_thRat_mul i j k z

theorem isLB_de [IsNoetherianRing O] (hP : PushInvertible Y.t.G Y.t.PP.L) : (de Y).IsLB :=
  GlobalTheory.CechPic.isLB_dual (isLB_pushPP hP)

end Lines

end GlobalTheory.FlagMod
