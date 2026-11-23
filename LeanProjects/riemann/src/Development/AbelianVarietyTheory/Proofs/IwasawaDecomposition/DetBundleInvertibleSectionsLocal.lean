import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmpStOfSabExtNormalSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SabExtNormalStOfHomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericFiberNormalReduced
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAffineLieBasisBaseChange

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.GenFrame

open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.FlagMod GlobalTheory.Reg
open GlobalTheory.PolFin (tanEquiv tanPull_tanEquiv)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem)

attribute [local instance] Over.cartesianMonoidalCategory

theorem toMatrix_map_of_semilinear {R R' N N' : Type} [CommRing R] [CommRing R'] [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R' N'] {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] (φ : R →+* R')
    (T : N →ₛₗ[φ] N') (b : Module.Basis κ R N) (b' : Module.Basis κ' R N) (c : Module.Basis κ R' N')
    (c' : Module.Basis κ' R' N') (hb : ∀ i, T (b i) = c i) (hb' : ∀ j, T (b' j) = c' j) :
    (b.toMatrix b').map φ = c.toMatrix c' := by
  ext i j
  have h := congrArg T (b.sum_repr (b' j))
  simp only [map_sum, map_smulₛₗ, hb, hb'] at h
  rw [Matrix.map_apply, Module.Basis.toMatrix_apply, Module.Basis.toMatrix_apply, ← h, Module.Basis.repr_sum_self]

section VecBasis

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
  {U : X0.Opens} (hU : IsAffineOpen U) {n : ℕ} (v₀ : Fin n → (Sp (DualNumber Γ(X0, U)) ⟶ t.G.left))
  (hv : ∀ (R' : Type) [CommRing R'] (f : Γ(X0, U) →+* R') (G' : Over (Sp R')) [GrpObj G'] (φ : G'.left ⟶ t.G.left),
    IsGrpPullback G' t.G (spMap f ≫ hU.fromSpec) φ → ∃ v' : Fin n → (epsR R' ⟶ G'),
      (∀ j, (v' j).left ≫ φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ v₀ j) ∧ IsLieBasis v')
  {S S' : Type} [CommRing S] [CommRing S']

include hv in

theorem exists_vecBasis (x : Sp S ⟶ X0) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    ∃ b : Module.Basis (Fin n) S (TanM x t.G), ∀ j, (tv (b j)).left = spMap (dualMap (ev x U h)) ≫ v₀ j := by
  have key : ∀ (f : Γ(X0, U) →+* S) (x : Sp S ⟶ X0), spMap f ≫ hU.fromSpec = x →
      ∃ b : Module.Basis (Fin n) S (TanM x t.G), ∀ j, (tv (b j)).left = spMap (dualMap f) ≫ v₀ j := by
    rintro f _ rfl
    have hp : ∃ t' : SAB H (Sp S), Nonempty (SABMap t' t (spMap f ≫ hU.fromSpec)) := by
      obtain ⟨PP', cub, sym, adj, prim, m, -⟩ :=
        sabPull ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull (spMap f ≫ hU.fromSpec) t
      exact ⟨_, ⟨m⟩⟩
    obtain ⟨t', ⟨m⟩⟩ := hp
    obtain ⟨v', hv', hb⟩ := hv S f t'.G m.φ m.cart
    let u : Fin n → TanM (spMap f ≫ hU.fromSpec) t.G := fun j =>
      mkT (pushHom m.cart (epsR S) (v' j)) ((PullbackSections.isTangent_iff m.cart _).1 (hb.1 j))
    have hcomb : ∀ (a : Fin n → S) (w : epsR S ⟶ t'.G), IsLieComb a v' w ↔
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
    have he : ∀ j, (Pi.basisFun S (Fin n)).map e j = u j := fun j => by
      simp [e, Fintype.linearCombination_apply_single]
    exact ⟨(Pi.basisFun S (Fin n)).map e, fun j => by rw [he]; exact hv' j⟩
  exact key _ x (spMap_ev x hU h)

def vecBasis (x : Sp S ⟶ X0) (h : ⊤ ≤ x ⁻¹ᵁ U) : Module.Basis (Fin n) S (TanM x t.G) :=
  (exists_vecBasis t hU v₀ hv x h).choose

theorem vecBasis_left (x : Sp S ⟶ X0) (h : ⊤ ≤ x ⁻¹ᵁ U) (j : Fin n) :
    (tv (vecBasis t hU v₀ hv x h j)).left = spMap (dualMap (ev x U h)) ≫ v₀ j :=
  (exists_vecBasis t hU v₀ hv x h).choose_spec j

theorem tanPull_vecBasis (φ : S →+* S') {x : Sp S ⟶ X0} {x' : Sp S' ⟶ X0} (e : spMap φ ≫ x = x')
    (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ x' ⁻¹ᵁ U) (j : Fin n) :
    tanPull φ e (vecBasis t hU v₀ hv x h j) = vecBasis t hU v₀ hv x' h' j := by
  subst e
  apply tan_ext_left
  rw [tanPull_left, vecBasis_left, vecBasis_left, ev_spMap φ x U h, GlobalTheory.FlagMod.dualMap_comp, ← spMap_comp', Category.assoc]

end VecBasis

section Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {Zs : Scheme.{0}} {p : Zs ⟶ Y.X} {V : Zs.Opens} {n : ℕ}
  (B : ∀ (S : Type) [CommRing S] (z : Sp S ⟶ Zs), ⊤ ≤ z ⁻¹ᵁ V → Module.Basis (Fin n) S (TanM (z ≫ p) Y.t.G))
  (hB : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S') (z : Sp S ⟶ Zs) (z' : Sp S' ⟶ Zs)
    (h : ⊤ ≤ z ⁻¹ᵁ V) (h' : ⊤ ≤ z' ⁻¹ᵁ V), spMap φ ≫ z = z' → ∀ (e : spMap φ ≫ z ≫ p = z' ≫ p) (j : Fin n),
      tanPull φ e (B S z h j) = B S' z' h' j)
  (hA : ∀ M : MChart Y, IsAffineOpen (p ⁻¹ᵁ M.U ⊓ V))

def frameFn (M : MChart Y) : Γ(Zs, p ⁻¹ᵁ M.U ⊓ V) :=
  rdet ((B _ (tau (hA M)) (tau_le _ inf_le_right)).toMatrix
    (lieBasis M (tau (hA M) ≫ p) (le_preimage_map p inf_le_left (tau_le _ le_rfl))))

include hB in
theorem ev_frameFn (M : MChart Y) {S : Type} [CommRing S] (z : Sp S ⟶ Zs) (hz : ⊤ ≤ z ⁻¹ᵁ (p ⁻¹ᵁ M.U ⊓ V))
    (h : ⊤ ≤ z ⁻¹ᵁ V) (hM : ⊤ ≤ (z ≫ p) ⁻¹ᵁ M.U) :
    ev z _ hz (frameFn B hA M) = rdet ((B S z h).toMatrix (lieBasis M (z ≫ p) hM)) := by
  have e0 : spMap (ev z _ hz) ≫ tau (hA M) = z := spMap_ev z (hA M) hz
  have e1 : spMap (ev z _ hz) ≫ tau (hA M) ≫ p = z ≫ p := by rw [← Category.assoc, e0]
  rw [frameFn, map_rdet, toMatrix_map_of_semilinear _ (tanPull (G := Y.t.G) _ e1) _ _ _ _
    (hB _ _ _ _ _ _ _ e0 e1) (tanPull_lieBasis M _ e1 _ hM)]

def frame (J : ((detOm Y).pull p).ι) : Γ(Zs, V ⊓ ((detOm Y).pull p).U J) :=
  resG Zs (show V ⊓ ((detOm Y).pull p).U J ≤ p ⁻¹ᵁ (J PUnit.unit).U ⊓ V from
    le_inf (inf_le_right.trans (LB.wchart_le (detOm Y) (fun _ : PUnit => p) J PUnit.unit)) inf_le_left)
    (frameFn B hA (J PUnit.unit))

theorem isUnit_frameFn (M : MChart Y) : IsUnit (frameFn B hA M) := isUnit_rdet_toMatrix _ _

theorem isUnit_frame (J : ((detOm Y).pull p).ι) : IsUnit (frame B hA J) :=
  (isUnit_frameFn B hA _).map _

include hB in
theorem frame_mem : frame B hA ∈ secOn ((detOm Y).pull p) V := by
  intro J J'
  apply ext_ev
  intro S _ z hz
  have hV : ⊤ ≤ z ⁻¹ᵁ V := le_preimage_mono (inf_le_left.trans inf_le_left) hz
  have hJ : ⊤ ≤ z ⁻¹ᵁ ((detOm Y).pull p).U J := le_preimage_mono (inf_le_left.trans inf_le_right) hz
  have hJ' : ⊤ ≤ z ⁻¹ᵁ ((detOm Y).pull p).U J' := le_preimage_mono inf_le_right hz
  have hM0 : ⊤ ≤ (z ≫ p) ⁻¹ᵁ (detOm Y).U (J PUnit.unit) :=
    le_preimage_map p (LB.wchart_le (detOm Y) (fun _ : PUnit => p) J PUnit.unit) hJ
  have hM : ⊤ ≤ (z ≫ p) ⁻¹ᵁ (J PUnit.unit).U := hM0
  have hM0' : ⊤ ≤ (z ≫ p) ⁻¹ᵁ (detOm Y).U (J' PUnit.unit) :=
    le_preimage_map p (LB.wchart_le (detOm Y) (fun _ : PUnit => p) J' PUnit.unit) hJ'
  have hM' : ⊤ ≤ (z ≫ p) ⁻¹ᵁ (J' PUnit.unit).U := hM0'
  have hpre : ∀ W : Y.X.Opens, ⊤ ≤ (z ≫ p) ⁻¹ᵁ W → ⊤ ≤ z ⁻¹ᵁ (p ⁻¹ᵁ W) := by
    intro W h
    rwa [← Scheme.Hom.comp_preimage]
  have hW : ⊤ ≤ z ⁻¹ᵁ (p ⁻¹ᵁ (J PUnit.unit).U ⊓ V) := le_preimage_inf (hpre _ hM) hV
  have hW' : ⊤ ≤ z ⁻¹ᵁ (p ⁻¹ᵁ (J' PUnit.unit).U ⊓ V) := le_preimage_inf (hpre _ hM') hV
  have hMM : ⊤ ≤ (z ≫ p) ⁻¹ᵁ ((J PUnit.unit).U ⊓ (J' PUnit.unit).U) := le_preimage_inf hM hM'
  rw [map_mul, ev_res z _ hz (le_preimage_inf hV hJ), ev_res z _ hz (le_preimage_inf hV hJ'),
    ev_res z _ hz (le_preimage_inf hJ hJ')]
  rw [frame, frame, ev_res z _ _ hW, ev_res z _ _ hW']
  rw [ev_frameFn B hB hA _ z hW hV hM, ev_frameFn B hB hA _ z hW' hV hM']
  rw [GlobalTheory.FlagMod.ev_pull_g (detOm Y) p J J' z (le_preimage_inf hJ hJ') hMM]
  change _ = ev (z ≫ p) _ hMM ((detChg (J PUnit.unit) (J' PUnit.unit))⁻¹).val * _
  rw [ev_unit_inv]
  have hu : ((Units.map (ev (z ≫ p) _ hMM).toMonoidHom (detChg (J PUnit.unit) (J' PUnit.unit)) : Sˣ) : S) =
      rdet ((lieBasis (J PUnit.unit) (z ≫ p) hM).toMatrix (lieBasis (J' PUnit.unit) (z ≫ p) hM')) :=
    ev_detChg _ _ (z ≫ p) hM hM' hMM
  rw [← rdet_toMatrix_mul (B S z hV) (lieBasis (J PUnit.unit) (z ≫ p) hM) (lieBasis (J' PUnit.unit) (z ≫ p) hM'),
    ← hu, mul_left_comm, Units.inv_mul, _root_.mul_one]

end Frame

section Transport

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Zs Y0 X0 : Scheme.{0}} {t₀ : SAB H Zs}
  {tY : SAB H Y0} {tX : SAB H X0} {p : Zs ⟶ Y0} {q : Zs ⟶ X0} (n₁ : SABMap t₀ tY p) (n₂ : SABMap t₀ tX q)
  {U' : X0.Opens} (hU' : IsAffineOpen U') {n : ℕ} (v₀ : Fin n → (Sp (DualNumber Γ(X0, U')) ⟶ tX.G.left))
  (hv : ∀ (R' : Type) [CommRing R'] (f : Γ(X0, U') →+* R') (G' : Over (Sp R')) [GrpObj G'] (φ : G'.left ⟶ tX.G.left),
    IsGrpPullback G' tX.G (spMap f ≫ hU'.fromSpec) φ → ∃ v' : Fin n → (epsR R' ⟶ G'),
      (∀ j, (v' j).left ≫ φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ v₀ j) ∧ IsLieBasis v')
  {V : Zs.Opens} (hVU : V ≤ q ⁻¹ᵁ U')

def genB (S : Type) [CommRing S] (z : Sp S ⟶ Zs) (h : ⊤ ≤ z ⁻¹ᵁ V) : Module.Basis (Fin n) S (TanM (z ≫ p) tY.G) :=
  (vecBasis tX hU' v₀ hv (z ≫ q) (le_preimage_map q hVU h)).map
    ((tanEquiv n₂.cart z).symm.trans (tanEquiv n₁.cart z))

theorem tanPull_genB (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S') (z : Sp S ⟶ Zs) (z' : Sp S' ⟶ Zs)
    (h : ⊤ ≤ z ⁻¹ᵁ V) (h' : ⊤ ≤ z' ⁻¹ᵁ V) (e0 : spMap φ ≫ z = z') (e : spMap φ ≫ z ≫ p = z' ≫ p) (j : Fin n) :
    tanPull φ e (genB n₁ n₂ hU' v₀ hv hVU S z h j) = genB n₁ n₂ hU' v₀ hv hVU S' z' h' j := by
  have e2 : spMap φ ≫ z ≫ q = z' ≫ q := by rw [← e0, Category.assoc]
  simp only [genB, Module.Basis.map_apply, LinearEquiv.trans_apply]
  rw [tanPull_tanEquiv n₁.cart φ e0 e]
  congr 1
  apply (tanEquiv n₂.cart z').injective
  rw [LinearEquiv.apply_symm_apply, ← tanPull_tanEquiv n₂.cart φ e0 e2, LinearEquiv.apply_symm_apply,
    tanPull_vecBasis tX hU' v₀ hv φ e2]

end Transport

theorem detOm_frame_gen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (X : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (ρ : gen Y ⟶ gen X),
    Y.jQ ≫ ρ = X.jQ → (GlobalTheory.FlagMod.detOm Y).IsLB → ∀ y : gen Y, ∃ U : (gen X).affineOpens, ρ y ∈ U.1 ∧
      ∃ e ∈ secOn ((GlobalTheory.FlagMod.detOm Y).pull (genι Y)) (ρ ⁻¹ᵁ U.1), ∀ i, IsUnit (e i) := by
  intro E _ _ _ H D l Xo c X Y ρ hρ _ y
  have hN := (GlobalTheory.GenFibre.gen_normal_reduced_noetherian E H D l Xo c Y).1
  obtain ⟨t₀, n₁, n₂, -⟩ := cmpSt_of_sabExtNormalSt (sabExtNormalSt_of_homExtNormalSt GlobalTheory.homExtNormal)
    E H D l Xo c _ _ _ _ X Y ρ hρ hN
  haveI : Smooth X.t.G.hom := X.t.semi.smooth
  obtain ⟨U', hU', hyU', -, n, v₀, hv⟩ :=
    GlobalTheory.exists_affine_lieBasis_baseChange X.X X.t.G (genι X (ρ y)) ⊤ trivial
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUU'⟩ := (gen X).isBasis_affineOpens.exists_subset_of_mem_open
    (show ρ y ∈ ((genι X ⁻¹ᵁ U' : (gen X).Opens) : Set (gen X)) from hyU') (genι X ⁻¹ᵁ U').isOpen
  have hVU : ρ ⁻¹ᵁ U ≤ (ρ ≫ genι X) ⁻¹ᵁ U' := fun r hr => hUU' hr
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver X.proj
  have hA : ∀ M : MChart Y, IsAffineOpen (genι Y ⁻¹ᵁ M.U ⊓ ρ ⁻¹ᵁ U) := fun M =>
    GlobalTheory.PolFin.isAffineOpen_inf_preimage (genStr X) ρ hU (M.hU.preimage (genι Y))
  exact ⟨⟨U, hU⟩, hyU, frame (genB n₁ n₂ hU' v₀ hv hVU) hA, frame_mem _ (tanPull_genB n₁ n₂ hU' v₀ hv hVU) hA,
    isUnit_frame _ hA⟩

end GlobalTheory.GenFrame
