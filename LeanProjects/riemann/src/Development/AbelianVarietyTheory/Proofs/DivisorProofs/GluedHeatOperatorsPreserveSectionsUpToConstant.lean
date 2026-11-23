import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeatOperatorGluedPullbackBundlePower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedLineBundleSectionCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleSectionExtendBasicOpenStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatVExt
open GlobalTheory.KS

theorem cst_resV {Y : Scheme.{0}} {R : Type} [CommRing R] (π : Y ⟶ Sp R) (c : R) {O : Y.Opens}
    (h : O ≤ π ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1) (r : R) :
    GlobalTheory.HeatV.cst π _ h (GlobalTheory.HeatV.resV R c r) = rsT (π.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) O := by
  rw [rsT_of_le le_top]
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
    (Scheme.Hom.map_appLE π (U := (GlobalTheory.HeatV.bo R c).1) (U' := ⊤) (V := O) h (homOfLE le_top).op)

theorem rsT_cst {Y X : Scheme.{0}} (π : Y ⟶ X) (V : X.Opens) {O O' : Y.Opens} (h : O ≤ π ⁻¹ᵁ V) (h' : O' ≤ O)
    (a : Γ(X, V)) : rsT (GlobalTheory.HeatV.cst π V h a) O' = GlobalTheory.HeatV.cst π V (h'.trans h) a := by
  rw [rsT_of_le h']
  exact congrArg (fun φ => φ.hom a) (Scheme.Hom.appLE_map π h (homOfLE h').op)

theorem rsT_natCast {Y : Scheme.{0}} {O₀ O : Y.Opens} (h : O ≤ O₀) (m : ℕ) : rsT (m : Γ(Y, O₀)) O = m := by
  rw [rsT_of_le h, map_natCast]

theorem rsT_two {Y : Scheme.{0}} {O₀ O : Y.Opens} (h : O ≤ O₀) : rsT (2 : Γ(Y, O₀)) O = 2 := by
  rw [rsT_of_le h, map_ofNat]

theorem opV_rsT : ∀ {Y X : Scheme.{0}} (π : Y ⟶ X) (V : X.Opens) {n : ℕ} (dd : Fin n → GlobalTheory.Heat.Fld Y), (∀ a, IsField ⊤ (dd a)) → ∀ (Θ : Matrix (Fin n) (Fin n) Γ(X, V)) (u : Fin n → Γ(X, V)) (d : GlobalTheory.Heat.Fld Y) {W : Y.Opens}, IsField W d → ∀ (p p' : Γ(Y, W)) (k : ℕ) {O O' : Y.Opens} (hOW : O ≤ W) (h : O ≤ π ⁻¹ᵁ V) (h' : O' ≤ O) (f : Γ(Y, O)), rsT (GlobalTheory.HeatV.opV π V dd Θ u d p p' k O h f) O' = GlobalTheory.HeatV.opV π V dd Θ u d p p' k O' (h'.trans h) (rsT f O') := by
  intro Y X π V n dd hdd Θ u d W hd p p' k O O' hOW h h' f
  have hd' : ∀ g, resG Y h' (d O g) = d O' (resG Y h' g) :=
    fun g => ((hd.2.2 O O' h' hOW g)).symm
  have hdd' : ∀ a g, resG Y h' (dd a O g) = dd a O' (resG Y h' g) :=
    fun a g => ((hdd a).2.2 O O' h' le_top g).symm
  have hc : ∀ r, resG Y h' (GlobalTheory.HeatV.cst π V h r) = GlobalTheory.HeatV.cst π V (h'.trans h) r :=
    fun r => (rsT_of_le h' _).symm.trans (rsT_cst π V h h' r)
  have hp : ∀ q : Γ(Y, W), resG Y h' (rsT q O) = rsT q O' := fun q => by
    rw [← rsT_of_le h', rsT_rsT hOW h']
  rw [rsT_of_le h', rsT_of_le h']
  simp only [GlobalTheory.HeatV.opV, map_add, map_sub, map_mul, map_sum, map_pow, map_natCast, map_ofNat, hd', hdd', hc, hp]

theorem heat_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (c : R), c ≠ 0 → ∀ (n : ℕ) (dd' : Fin n → Fld t.G.left), (∀ a, IsField ⊤ (dd' a)) → ∀ (D : Derivation ℤ R R) (Θ₁ : Matrix (Fin n) (Fin n) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (DV : Derivation ℤ Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), (∀ r, DV (GlobalTheory.HeatV.resV R c r) = GlobalTheory.HeatV.resV R c (D r)) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (d : J → Fld t.G.left) (u : Fin n → Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (pf pf' : ∀ i, Γ(t.G.left, W i)) (hW : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1), ⨆ i, W i = t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 → (∀ i, W i ≤ t.PP.L.U (j i)) → (∀ i, IsField (W i) (d i)) → (∀ i O (h : O ≤ W i) (a : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), d i O (GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) a) = GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) (DV a)) → (∀ (k : ℕ) i i' O (h : O ≤ W i ⊓ W i') (f : Γ(t.G.left, O)), GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i) (pf i) (pf' i) k O (h.trans (inf_le_left.trans (hW i))) (pbT (𝟙 t.G.left) (t.PP.L.g (j i) (j i')).val O ^ k * f) = pbT (𝟙 t.G.left) (t.PP.L.g (j i) (j i')).val O ^ k * GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i') (pf i') (pf' i') k O (h.trans (inf_le_right.trans (hW i'))) f) → ∀ (k : ℕ) (σ : SecM (𝟙 t.G.left) t.PP.L k) (a : R), ∃ (r : R) (σ' : SecM (𝟙 t.G.left) t.PP.L k), r ≠ 0 ∧ ∀ i, rsT (σ'.f fun _ => j i) (W i) = GlobalTheory.HeatV.cst t.G.hom _ (hW i) (GlobalTheory.HeatV.resV R c r) * (GlobalTheory.HeatV.cst t.G.hom _ (hW i) (GlobalTheory.HeatV.resV R c a) * GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i) (pf i) (pf' i) k (W i) (hW i) (rsT (σ.f fun _ => j i) (W i)) - 2 * (k : Γ(t.G.left, W i)) * GlobalTheory.HeatV.cst t.G.hom _ (hW i) (GlobalTheory.HeatV.resV R c (D a)) * rsT (σ.f fun _ => j i) (W i)) := by
  intro E _ _ _ H R _ _ _ _ _ _ t c hc n dd' hdd' D Θ₁ DV hDV J W j d u pf pf' hW hcov hWL hd hdc hglue k σ a
  set π := t.G.hom
  set M := LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => (k : ℤ)) with hMdef
  have hM : M.IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ t.PP.isLB _ _
  set f : Γ(t.G.left, ⊤) := π.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) with hfdef
  have hb : π ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 = t.G.left.basicOpen f := Scheme.preimage_basicOpen_top π _
  have hWc : ∀ i, W i ≤ M.U (fun _ => j i) := fun i => GlobalTheory.Heat.Glue.le_wchart _ (hWL i)
  let F : ∀ i, Γ(t.G.left, W i) := fun i =>
    GlobalTheory.HeatV.cst π _ (hW i) (GlobalTheory.HeatV.resV R c a) *
                 GlobalTheory.HeatV.opV π _ dd' Θ₁ u (d i) (pf i) (pf' i) k (W i) (hW i) (rsT (σ.f fun _ => j i) (W i)) -
      2 * (k : Γ(t.G.left, W i)) * GlobalTheory.HeatV.cst π _ (hW i) (GlobalTheory.HeatV.resV R c (D a)) *
        rsT (σ.f fun _ => j i) (W i)
  have hF : ∀ i i', rsT (F i) (W i ⊓ W i') =
      rsT (M.g (fun _ => j i) (fun _ => j i')).val (W i ⊓ W i') * rsT (F i') (W i ⊓ W i') := by
    intro i i'
    have hII : W i ⊓ W i' ≤ M.U (fun _ => j i) ⊓ M.U (fun _ => j i') := inf_le_inf (hWc i) (hWc i')
    have hs := GlobalTheory.Heat.Glue.sec_rel (𝟙 t.G.left) k σ (fun _ => j i) (fun _ => j i') hII
    have hgl := hglue k i i' (W i ⊓ W i') le_rfl (rsT (σ.f fun _ => j i') (W i ⊓ W i'))
    rw [GlobalTheory.Heat.Glue.linComb_g (𝟙 t.G.left) k _ _ hII]
    simp only [F, rsT_sub, rsT_mul, rsT_cst _ _ _ inf_le_left, rsT_cst _ _ _ inf_le_right,
      rsT_natCast inf_le_left, rsT_natCast inf_le_right, rsT_two inf_le_left, rsT_two inf_le_right]
    rw [opV_rsT π _ dd' hdd' Θ₁ u (d i) (hd i) (pf i) (pf' i) k le_rfl (hW i) inf_le_left,
      opV_rsT π _ dd' hdd' Θ₁ u (d i') (hd i') (pf i') (pf' i') k le_rfl (hW i') inf_le_right,
      rsT_rsT (hWc i) inf_le_left, rsT_rsT (hWc i') inf_le_right, hs, hgl]
    ring
  haveI := t.semi.quasiCompact
  haveI := t.semi.separated
  haveI : CompactSpace t.G.left := QuasiCompact.compactSpace_of_compactSpace t.G.hom
  haveI : QuasiSeparatedSpace t.G.left := quasiSeparatedSpace_of_quasiSeparated t.G.hom
  obtain ⟨tt, htt, htF⟩ := GlobalTheory.T.exists_glued_lineBundleSection_cover M hM (t.G.left.basicOpen f) W (fun i _ => j i) F (by rw [hcov, hb]) hWc hF
  obtain ⟨N, s, hs⟩ := GlobalTheory.T.exists_lineBundleSection_extend_basicOpen t.G.left M hM f tt htt
  refine ⟨c ^ N, s, pow_ne_zero N hc, fun i => ?_⟩
  have hWi : W i ≤ M.U (fun _ => j i) ⊓ t.G.left.basicOpen f := le_inf (hWc i) (hb ▸ hW i)
  refine (rsT_rsT inf_le_left hWi _).symm.trans ?_
  refine (congrArg (fun x => rsT x (W i)) (hs (fun _ => j i))).trans ?_
  rw [rsT_mul, GlobalTheory.Heat.Glue.rsT_pow' hWi, rsT_rsT le_top hWi,
    htF i, map_pow, map_pow, cst_resV]

end GlobalTheory.HeatVExt
