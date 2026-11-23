import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LbIsoDetAffDetOm

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic
open Formalism.L2.Pj
open GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.GrCl GlobalTheory.Reg GlobalTheory.FlagMod
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.Twist (resM resM_resM)

namespace GlobalTheory.ChartLieFrame

theorem eq_of_loc {Z : Scheme.{0}} {W : Z.Opens} {a b : Γ(Z, W)}
    (h : ∀ p ∈ W, ∃ (N : Z.Opens) (e : N ≤ W), p ∈ N ∧ resG Z e a = resG Z e b) : a = b :=
  ext_ev_loc fun p hp => by
    obtain ⟨N, e, hpN, hab⟩ := h p hp
    exact ⟨N, hpN, fun S _ z hz hN => by rw [← ev_res z e hN hz a, ← ev_res z e hN hz b, hab]⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β}

def Rep (M : MChart Y) (j : Fin M.n) {U : Y.X.Opens} (hU : U ≤ M.U) (s : Γ(GlobalTheory.LieVB.Lie Y.t.G, U)) : Prop :=
  ∀ (W : Y.X.Opens) (hW : IsAffineOpen W) (h : W ≤ U) (w : Γ(GlobalTheory.LieVB.omega Y.t.G, W)),
    VB.dualApp s h w = tanEv Y.t (isTan_tv (lieBasis M (tau hW) (tau_le hW (h.trans hU)) j)) (tau_le hW le_rfl) w

theorem tanLin_res (M : MChart Y) {W W₀ V : Y.X.Opens} (hW : IsAffineOpen W) (hW₀ : IsAffineOpen W₀) (e : W ≤ W₀)
    (hM : W₀ ≤ M.U) (hV : W₀ ≤ V) {n : ℕ} (s : Fin n → Γ(GlobalTheory.LieVB.omega Y.t.G, V)) (j : Fin M.n) :
    tanLin Y.t (tau_le hW (e.trans hV)) s (lieBasis M (tau hW) (tau_le hW (e.trans hM)) j) =
      fun i => resG Y.X e (tanLin Y.t (tau_le hW₀ hV) s (lieBasis M (tau hW₀) (tau_le hW₀ hM) j) i) := by
  have φe : spMap (ev (tau hW) W₀ (tau_le hW e)) ≫ tau hW₀ = tau hW := spMap_ev (tau hW) hW₀ (tau_le hW e)
  rw [← tanPull_lieBasis M _ φe (tau_le hW₀ hM) (tau_le hW (e.trans hM)) j,
    tanLin_tanPull Y.t _ φe (tau_le hW₀ hV) (tau_le hW (e.trans hV))]
  funext i
  exact ev_tau hW e (tau_le hW e) _

theorem tanEv_res (M : MChart Y) {W W₀ : Y.X.Opens} (hW : IsAffineOpen W) (hW₀ : IsAffineOpen W₀) (e : W ≤ W₀)
    (hM : W₀ ≤ M.U) (w : Γ(GlobalTheory.LieVB.omega Y.t.G, W₀)) (j : Fin M.n) :
    tanEv Y.t (isTan_tv (lieBasis M (tau hW) (tau_le hW (e.trans hM)) j)) (tau_le hW le_rfl) (resM _ e w) =
      resG Y.X e (tanEv Y.t (isTan_tv (lieBasis M (tau hW₀) (tau_le hW₀ hM) j)) (tau_le hW₀ le_rfl) w) := by
  rw [tanEv_resM]
  exact congrFun (tanLin_res M hW hW₀ e hM le_rfl ![w] j) 0

theorem Rep.res {M : MChart Y} {j : Fin M.n} {U : Y.X.Opens} {hU : U ≤ M.U} {s : Γ(GlobalTheory.LieVB.Lie Y.t.G, U)}
    (hs : Rep M j hU s) {U' : Y.X.Opens} (e : U' ≤ U) : Rep M j (e.trans hU) (resM _ e s) := fun W hW h w => by
  rw [VB.dualApp_res]
  exact hs W hW (h.trans e) w

theorem rep_unique (M : MChart Y) (j : Fin M.n) {U : Y.X.Opens} (hU : U ≤ M.U) {s s' : Γ(GlobalTheory.LieVB.Lie Y.t.G, U)}
    (hs : Rep M j hU s) (hs' : Rep M j hU s') : s = s' :=
  VB.dual_ext fun W h w => eq_of_loc fun p hp => by
    obtain ⟨N, hN, hpN, hNW'⟩ := exists_isAffineOpen_mem_and_subset (x := p) (U := W) hp
    have hNW : N ≤ W := hNW'
    refine ⟨N, hNW, hpN, ?_⟩
    rw [← VB.dualApp_resM, ← VB.dualApp_resM, hs N hN, hs' N hN]

theorem rep_of_cover (M : MChart Y) (j : Fin M.n) {U : Y.X.Opens} (hU : U ≤ M.U) {ι : Type} (V : ι → Y.X.Opens)
    (hV : ∀ k, V k ≤ U) (hc : U ≤ iSup V) (s : Γ(GlobalTheory.LieVB.Lie Y.t.G, U))
    (H : ∀ k, Rep M j ((hV k).trans hU) (resM _ (hV k) s)) : Rep M j hU s := fun W hW h w =>
  eq_of_loc fun p hp => by
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc (h hp))
    obtain ⟨N, hN, hpN, hNW⟩ := exists_isAffineOpen_mem_and_subset (x := p) (U := W ⊓ V k) ⟨hp, hk⟩
    have eW : N ≤ W := fun q hq => (hNW hq).1
    have eV : N ≤ V k := fun q hq => (hNW hq).2
    refine ⟨N, eW, hpN, ?_⟩
    rw [← VB.dualApp_resM, ← tanEv_res M hN hW eW (h.trans hU) w j]
    have := H k N hN eV (resM _ eW w)
    rw [VB.dualApp_res] at this
    exact this

def locSec (M : MChart Y) (j : Fin M.n) {n : ℕ} (C : VB.Chart (GlobalTheory.LieVB.omega Y.t.G) n) (hC : IsAffineOpen C.U)
    (hM : C.U ≤ M.U) : Γ(GlobalTheory.LieVB.Lie Y.t.G, C.U) :=
  ∑ i : Fin n, (tanLin Y.t (tau_le hC le_rfl) C.e (lieBasis M (tau hC) (tau_le hC hM) j) i : Γ(Y.X, C.U)) •
    (C.isFrame.coord i : Γ(GlobalTheory.LieVB.Lie Y.t.G, C.U))

theorem rep_locSec (M : MChart Y) (j : Fin M.n) {n : ℕ} (C : VB.Chart (GlobalTheory.LieVB.omega Y.t.G) n)
    (hC : IsAffineOpen C.U) (hM : C.U ≤ M.U) : Rep M j hM (locSec M j C hC hM) := fun W hW h w => by
  rw [locSec, VB.dualApp_sum]
  simp only [VB.dualApp_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    VB.IsFrame.dualApp_coord, smul_eq_mul]
  conv_rhs => rw [← (C.isFrame.basis h).sum_repr w]
  rw [tanEv_sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [VB.IsFrame.basis_apply, tanEv_resM, ev_tau_self, RingHom.id_apply, _root_.mul_comm]
  exact congrArg (((C.isFrame.basis h).repr w i) * ·) (congrFun (tanLin_res M hW hC h hM le_rfl C.e j) i).symm

theorem exists_rep (M : MChart Y) (j : Fin M.n) : ∃ s : Γ(GlobalTheory.LieVB.Lie Y.t.G, M.U), Rep M j le_rfl s := by
  haveI := Y.t.semi
  haveI := Y.t.semi.smooth
  let V : (Σ n : ℕ, {C : VB.Chart (GlobalTheory.LieVB.omega Y.t.G) n // IsAffineOpen C.U ∧ C.U ≤ M.U}) → Y.X.Opens :=
    fun k => k.2.1.U
  have hV : ∀ k, V k ≤ M.U := fun k => k.2.2.2
  have hc : M.U ≤ iSup V := fun p hp => by
    obtain ⟨U₀, n, e, hp₀, he⟩ := GlobalTheory.LieVB.exists_isFrame_omega Y.t.G p
    obtain ⟨N, hN, hpN, hNU⟩ := exists_isAffineOpen_mem_and_subset (x := p) (U := M.U ⊓ U₀) ⟨hp, hp₀⟩
    have e₁ : N ≤ M.U := fun q hq => (hNU hq).1
    have e₂ : N ≤ U₀ := fun q hq => (hNU hq).2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨n, ⟨⟨N, fun i => resM _ e₂ (e i), he.res e₂⟩, hN, e₁⟩⟩, hpN⟩
  have hrep : ∀ k, Rep M j (hV k) (locSec M j k.2.1 k.2.2.1 k.2.2.2) := fun k => rep_locSec M j _ _ _
  obtain ⟨t, ht⟩ := Twist.exists_sec_of_cover V hV hc (fun k => locSec M j k.2.1 k.2.2.1 k.2.2.2) fun k k' =>
    rep_unique M j (inf_le_left.trans (hV k)) ((hrep k).res inf_le_left) ((hrep k').res inf_le_right)
  exact ⟨t, rep_of_cover M j le_rfl V hV hc t fun k => by rw [ht k]; exact hrep k⟩

theorem isFrame_of_rep (M : MChart Y) (f : Fin M.n → Γ(GlobalTheory.LieVB.Lie Y.t.G, M.U)) (hf : ∀ j, Rep M j le_rfl (f j)) :
    VB.IsFrame f := by
  haveI := Y.t.semi
  haveI := Y.t.semi.smooth
  refine VB.isFrame_of_forall_exists fun V h p hp => ?_
  obtain ⟨U₀, n, e, hp₀, he⟩ := GlobalTheory.LieVB.exists_isFrame_omega Y.t.G p
  obtain ⟨W, hW, hpW, hWU⟩ := exists_isAffineOpen_mem_and_subset (x := p) (U := V ⊓ U₀) ⟨hp, hp₀⟩
  have e₁ : W ≤ V := fun q hq => (hWU hq).1
  have e₂ : W ≤ U₀ := fun q hq => (hWU hq).2
  let C : VB.Chart (GlobalTheory.LieVB.omega Y.t.G) n := ⟨W, fun i => resM _ e₂ (e i), he.res e₂⟩
  refine ⟨W, e₁, hpW, ?_⟩
  let R := (C.isFrame.dual.basis (le_rfl : C.U ≤ C.U)).equivFun
  let T : (Fin M.n → Γ(Y.X, W)) → (Fin n → Γ(Y.X, W)) :=
    (tanLin Y.t (tau_le hW (le_rfl : W ≤ C.U)) C.e) ∘ (lieBasis M (tau hW) (tau_le hW (e₁.trans h))).equivFun.symm
  have hT : Function.Bijective T :=
    (HodgeCech.tanLin_bijective Y.t C (tau hW) (tau_le hW le_rfl)).comp (LinearEquiv.bijective _)
  have key : ∀ a, R (Fintype.linearCombination Γ(Y.X, W) (fun j => resM _ (e₁.trans h) (f j)) a) = T a := by
    intro a
    funext i
    simp only [R, T, Function.comp_apply, Module.Basis.equivFun_apply, VB.IsFrame.dual_basis_repr,
      Fintype.linearCombination_apply, VB.dualApp_sum, LinearMap.sum_apply, VB.dualApp_smul, LinearMap.smul_apply,
      VB.dualApp_res, Module.Basis.equivFun_symm_apply, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, GlobalTheory.LB.resG_self]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hf k W hW _ _, GlobalTheory.Twist.resM_self]
    rfl
  have hc : R ∘ (Fintype.linearCombination Γ(Y.X, W) (fun j => resM _ (e₁.trans h) (f j))) = T := funext key
  exact (Function.Bijective.of_comp_iff' R.bijective _).1 (hc ▸ hT)

theorem rep_chg (M M' : MChart Y) (f : Fin M.n → Γ(GlobalTheory.LieVB.Lie Y.t.G, M.U)) (hf : ∀ i, Rep M i le_rfl (f i))
    (j : Fin M'.n) :
    Rep M' j inf_le_right (∑ i, chg M M' i j • resM _ (inf_le_left : M.U ⊓ M'.U ≤ M.U) (f i)) := fun W hW h w => by
  have ev' : ∀ v, tanEv Y.t (isTan_tv v) (tau_le hW le_rfl) w = tanLin Y.t (tau_le hW le_rfl) ![w] v 0 := fun v => rfl
  rw [VB.dualApp_sum]
  simp only [VB.dualApp_smul, LinearMap.sum_apply, LinearMap.smul_apply, VB.dualApp_res, smul_eq_mul]
  rw [ev', ← (lieBasis M (tau hW) (tau_le hW (h.trans inf_le_left))).sum_toMatrix_smul_self
    (lieBasis M' (tau hW) (tau_le hW (h.trans inf_le_right))) j, map_sum]
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, hf i W hW (h.trans inf_le_left) w, ev']
  refine congrArg₂ (· * ·) ?_ rfl
  rw [← chg_map M M' (tau hW) (tau_le hW (h.trans inf_le_left)) (tau_le hW (h.trans inf_le_right)) (tau_le hW h),
    Matrix.map_apply, ev_tau hW h]

theorem exists_lieFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), ∃ f : ∀ M : GlobalTheory.Reg.MChart Y, Fin M.n → Γ(GlobalTheory.LieVB.Lie Y.t.G, M.U), (∀ M, GlobalTheory.VB.IsFrame (f M)) ∧ ∀ (M M' : GlobalTheory.Reg.MChart Y) (j : Fin M'.n), GlobalTheory.Twist.resM _ (inf_le_right : M.U ⊓ M'.U ≤ M'.U) (f M' j) = ∑ i, GlobalTheory.FlagMod.chg M M' i j • GlobalTheory.Twist.resM _ (inf_le_left : M.U ⊓ M'.U ≤ M.U) (f M i) := by
  intro E _ _ _ H Dw l Xo c O _ β Y
  choose f hf using fun (M : MChart Y) (j : Fin M.n) => exists_rep M j
  exact ⟨f, fun M => isFrame_of_rep M (f M) (hf M), fun M M' j =>
    rep_unique M' j inf_le_right ((hf M' j).res inf_le_right) (rep_chg M M' (f M) (hf M) j)⟩

end GlobalTheory.ChartLieFrame
