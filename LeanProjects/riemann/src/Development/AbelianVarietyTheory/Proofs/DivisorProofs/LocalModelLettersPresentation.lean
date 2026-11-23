import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatHalfSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualPullback

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison GlobalTheory.ChainPts
open GlobalTheory
open GlobalTheory.Twist (resM resM_self resM_resM app_resM resM_smul)

namespace GlobalTheory.ChainPts.DualPres

section Frames

open GlobalTheory.VB

variable {X : Scheme.{0}} {F G : X.Modules} {r : ℕ} {V V' : X.Opens}

theorem repr_perm {e : Fin r → Γ(F, V)} (he : IsFrame e) (σ : Equiv.Perm (Fin r)) (he' : IsFrame fun i => e (σ i))
    (h : V' ≤ V) (v : Γ(F, V')) (i : Fin r) : (he'.basis h).repr v i = (he.basis h).repr v (σ i) := by
  have : he'.basis h = (he.basis h).reindex σ.symm := DFunLike.ext _ _ fun k => by simp
  rw [this]
  simp

theorem coef_dual {e : Fin r → Γ(F, V)} {s : Fin r → Γ(F, V')} (he : IsFrame e) (hs : IsFrame s) (l i : Fin r) :
    coef false he.dual hs.dual l i = coef true he hs l i :=
  he.dual_basis_repr inf_le_left _ l

theorem exists_predual (hF : IsVB F r) {e : Fin r → Γ(VB.dual F, V)} (he : IsFrame e) :
    ∃ (e' : Fin r → Γ(F, V)) (he' : IsFrame e'), e = he'.coord := by
  haveI := hF.isIso_toBidual_of_local_frames
  have he' := he.dual.map_iso (inv (cartierDualToBidual F))
  refine ⟨_, he', funext fun i => he'.dual_ext le_rfl fun j => ?_⟩
  rw [he'.dualApp_coord_frame, ← dualSheafSectionApply_toBidual]
  have : (cartierDualToBidual F).app V ((inv (cartierDualToBidual F)).app V (he.coord j)) = he.coord j := by
    change (inv (cartierDualToBidual F) ≫ cartierDualToBidual F).app V (he.coord j) = _
    rw [IsIso.inv_hom_id]; rfl
  rw [this]
  have := he.dualApp_coord_frame j i le_rfl
  rw [resM_self] at this
  rw [this]
  simp only [eq_comm]

theorem dualMap_coord (φ : F ⟶ G) {s : Fin r → Γ(F, V)} (hs : IsFrame s) (hs' : IsFrame fun i => φ.app V (s i))
    (i : Fin r) : (VB.dualMap φ).app V (hs'.coord i) = hs.coord i :=
  hs.dual_ext le_rfl fun j => by
    rw [dualApp_dualMap, app_resM, hs'.dualApp_coord_frame, hs.dualApp_coord_frame]

theorem dualMap_coord_eig (φ : F ⟶ F) {s : Fin r → Γ(F, V)} (hs : IsFrame s) (c : Fin r → Γ(X, V))
    (hc : ∀ i, φ.app V (s i) = c i • s i) (i : Fin r) : (VB.dualMap φ).app V (hs.coord i) = c i • hs.coord i :=
  hs.dual_ext le_rfl fun j => by
    rw [dualApp_dualMap, app_resM, hc, resM_smul, map_smul, dualApp_smul, LinearMap.smul_apply,
      hs.dualApp_coord_frame]
    split_ifs with h
    · rw [h]
    · simp

theorem isIso_pullback_dualMap {Y : Scheme.{0}} (f : Y ⟶ X) (φ : F ⟶ G) (hF : IsVB F r) (hG : IsVB G r)
    [IsIso ((Scheme.Modules.pullback f).map φ)] : IsIso ((Scheme.Modules.pullback f).map (VB.dualMap φ)) := by
  haveI := DualPull.isIso_theta f hF
  haveI := DualPull.isIso_theta f hG
  haveI : IsIso (VB.dualMap ((Scheme.Modules.pullback f).map φ)) :=
    (dualIso (asIso ((Scheme.Modules.pullback f).map φ))).isIso_hom
  haveI : IsIso ((Scheme.Modules.pullback f).map (VB.dualMap φ) ≫ DualPull.theta f F) := by
    rw [DualPull.theta_naturality]; infer_instance
  exact IsIso.of_isIso_comp_right _ (DualPull.theta f F)

end Frames

section Act

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O} {Λ : Type} [CommRing Λ]
  (τ : Λ ≃+* Λ)

def dualA (M : AM B Λ) : AM B Λ where
  V := VB.dual M.V
  ρ :=
    { toFun c := VB.dualMap (M.ρ (τ c) : M.V ⟶ M.V)
      map_one' := by rw [map_one, map_one]; rfl
      map_mul' a b := by rw [mul_comm a b, map_mul, map_mul]; rfl }

def dualHomA {M N : AM B Λ} (φ : M ⟶ N) : dualA τ N ⟶ dualA τ M where
  hom := VB.dualMap φ.hom
  comm c := by
    have e : (M.ρ (τ c) : M.V ⟶ M.V) ≫ φ.hom = φ.hom ≫ (N.ρ (τ c) : N.V ⟶ N.V) := φ.comm _
    change VB.dualMap (N.ρ (τ c) : N.V ⟶ N.V) ≫ VB.dualMap φ.hom = VB.dualMap φ.hom ≫ VB.dualMap (M.ρ (τ c) : M.V ⟶ M.V)
    rw [← VB.dualMap_comp, ← VB.dualMap_comp, e]

theorem isAdd_dualA {M : AM B Λ} (h : IsAdd M) : IsAdd (dualA τ M) := fun a b => by
  change VB.dualMap (M.ρ (τ (a + b)) : M.V ⟶ M.V) = VB.dualMap (M.ρ (τ a) : M.V ⟶ M.V) + VB.dualMap (M.ρ (τ b) : M.V ⟶ M.V)
  rw [map_add, h, VB.dualMap_add]

def dualP (P : EPres B Λ) : EPres B Λ where
  r := P.r
  E := dualA τ P.E'
  E' := dualA τ P.E
  add := isAdd_dualA τ P.add'
  add' := isAdd_dualA τ P.add
  vb := P.vb'.dual
  vb' := P.vb.dual
  ψ := dualHomA τ P.ψ
  iso := haveI := P.iso; isIso_pullback_dualMap _ P.ψ.hom P.vb' P.vb

end Act

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory in
open MonObj in

theorem comb_perm {X0 : Scheme.{0}} (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) {m : ℕ}
    (p : Equiv.Perm (Fin m)) (v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)) (cf : Fin m → S)
    (w : Sp (DualNumber S) ⟶ t.G.left) (h : IsCombAtG t x0 v cf w) :
    IsCombAtG t x0 (fun j => v (p j)) (fun j => cf (p j)) w := by
  obtain ⟨u, hu, hp⟩ := h
  refine ⟨fun j => u (p j), fun j => hu (p j), ?_⟩
  rw [← hp]
  letI : CommMonoid (tEpsG x0 ⟶ t.G) := Hom.commMonoid
  exact congrArg Over.Hom.left ((List.prod_ofFn (f := fun j => u (p j))).trans
    ((Equiv.prod_comp p u).trans (List.prod_ofFn (f := u)).symm))

theorem comb_perm' {X0 : Scheme.{0}} (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) {m : ℕ}
    (p : Equiv.Perm (Fin m)) (v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)) (cf : Fin m → S)
    (w : Sp (DualNumber S) ⟶ t.G.left) (h : IsCombAtG t x0 (fun j => v (p j)) cf w) :
    IsCombAtG t x0 v (fun j => cf (p.symm j)) w := by
  simpa only [Equiv.apply_symm_apply] using comb_perm t x0 p.symm _ _ _ h

theorem bar_bar (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  show ((H.bar (H.bar a) : 𝓞 E) : E) = (a : E)
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

variable {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}
  {i₀ : Idx H p} {Z : LocM.Mdl Y i₀} {X : Scheme.{0}} {h : X ⟶ Z.X} {r : ℕ} {b : Bool} {F : X.Modules}

theorem isLat_perm {x : Fin r → Letter Dw} {s : ∀ a : Fin Z.m, Fin r → Γ(F, h ⁻¹ᵁ (Z.U a).1)}
    (k : IsLat Z h x true b F s) (σ : Equiv.Perm (Fin r)) :
    IsLat Z h (fun i => x (σ i)) true b F fun a i => s a (σ i) where
  frame a := (k.frame a).comp_equiv σ
  glue K _ w a a' φ φ' hφ hφ' j := by
    have := comb_perm _ _ σ _ _ _ (k.glue K w a a' φ φ' hφ hφ' (σ j))
    convert this using 3
    exact repr_perm (k.frame a') σ _ _ _ _
  norm y w hw a φ hφ V e he hV cf v hv := by
    have h1 := comb_perm' _ _ σ (fun i => (Z.fr a).bc φ (x i).1 (x i).2) _ _ hv
    rw [k.norm y w hw a φ hφ V e he hV _ v h1]
    refine forall_congr' fun l => ?_
    rw [← Equiv.sum_comp σ]
    simp only [Equiv.symm_apply_apply]
    refine Iff.of_eq (congrArg (fun z => ‖z‖ ≤ 1) (Finset.sum_congr rfl fun i _ => ?_))
    exact congrArg (fun z => cf i * valF _ _ z) (repr_perm (k.frame a) σ _ _ _ _).symm

theorem isLat_dual {x : Fin r → Letter Dw} {s : ∀ a : Fin Z.m, Fin r → Γ(F, h ⁻¹ᵁ (Z.U a).1)}
    (k : IsLat Z h x true b F s) (hF : VB.IsVB F r) :
    IsLat Z h x false b (VB.dual F) fun a => (k.frame a).coord where
  frame a := (k.frame a).dual
  glue K _ w a a' φ φ' hφ hφ' j := by
    simp only [coef_dual]
    exact k.glue K w a a' φ φ' hφ hφ' j
  norm y w hw a φ hφ V e he hV cf v hv := by
    obtain ⟨e', he', rfl⟩ := exists_predual hF he
    simp only [coef_dual]
    exact k.norm y w hw a φ hφ V e' he' hV cf v hv

theorem exists_dual_pres : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  (Z : LocM.Mdl Y i₀) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O}
  (h : B.X ⟶ Z.X) {r : ℕ} (x : Fin r → Letter Dw) (oo : EPres B (𝓞 E)) (π : Γ(B.X, ⊤)) (u : oo.E ⟶ oo.E'),
  u ≫ oo.ψ = smulA _ π → IsEqLatPres Z h (fun k => x k.rev) true oo →
    ∃ (lw : EPres B (𝓞 E)) (wl : lw.E ⟶ lw.E'), lw.ψ ≫ wl = smulA _ π ∧ IsEqLatPres Z h x false lw := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z O _ _ _ B h r x oo π u hu ⟨hr, s, k1, k2, k3⟩
  subst hr
  have hx : (fun i => x (Fin.rev (Fin.revPerm i))) = x := funext fun i => by simp
  have l1 := isLat_perm k1 Fin.revPerm
  have l2 := isLat_perm k2 Fin.revPerm
  rw [hx] at l1 l2
  refine ⟨dualP H.bar oo, dualHomA H.bar u, ?_, rfl, fun a => (l2.frame a).coord, isLat_dual l2 oo.vb, ?_, ?_⟩
  · apply Action.Hom.ext
    change VB.dualMap (u ≫ oo.ψ).hom = smulHom (VB.dual oo.E.V) π
    rw [hu]
    exact VB.dualMap_smulHom π
  · have e : (fun a i => (VB.dualMap oo.ψ.hom).app _ ((l2.frame a).coord i)) = fun a => (l1.frame a).coord :=
      funext fun a => funext fun i => dualMap_coord oo.ψ.hom (l1.frame a) (l2.frame a) i
    have := isLat_dual l1 oo.vb'
    rw [← e] at this
    exact this
  · intro a i c
    refine dualMap_coord_eig (oo.E.ρ (H.bar c) : oo.E.V ⟶ oo.E.V) (l2.frame a)
      (fun i => (h.app (Z.U a).1).hom (Z.alg a (embK Z.i.c (x i).1 c))) (fun j => ?_) i
    have e1 := k3 a j.rev (H.bar c)
    simp only [if_true, bar_bar, Fin.rev_rev] at e1
    have e2 : (oo.E'.ρ (H.bar c) : oo.E'.V ⟶ oo.E'.V) ≫ oo.ψ.hom = oo.ψ.hom ≫ (oo.E.ρ (H.bar c) : oo.E.V ⟶ oo.E.V) :=
      oo.ψ.comm _
    change (oo.ψ.hom ≫ (oo.E.ρ (H.bar c) : oo.E.V ⟶ oo.E.V)).app _ (s a j.rev) = _
    rw [← e2]
    change oo.ψ.hom.app _ ((oo.E'.ρ (H.bar c) : oo.E'.V ⟶ oo.E'.V).app _ (s a j.rev)) = _
    rw [e1]
    exact Scheme.Modules.Hom.app_smul _ _ _

end GlobalTheory.ChainPts.DualPres

end
