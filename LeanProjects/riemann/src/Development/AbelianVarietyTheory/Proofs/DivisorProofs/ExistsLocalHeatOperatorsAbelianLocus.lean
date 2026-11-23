import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantLiftAddInvariantCombination
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKSSymmAbLocus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapDualMapCompEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDlogAddCoboundaryAbLocus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeatV
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatV
open GlobalTheory.KS

theorem cst_resV {R : Type} [CommRing R] {Y : Scheme.{0}} (π : Y ⟶ Sp R) (c : R) {O : Y.Opens}
    (h : O ≤ π ⁻¹ᵁ (bo R c).1) (a : R) : cst π (bo R c).1 h (resV R c a) = constFn π O a :=
  congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.map_appLE π h (homOfLE ((Sp R).basicOpen_le (U := ⊤)
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c))).op)

theorem field_cst_eq_zero {R : Type} [CommRing R] {Y : Scheme.{0}} (π : Y ⟶ Sp R) (c : R) (dd : Fld Y)
    (hd : IsField ⊤ dd) (h0 : ∀ O a, dd O (constFn π O a) = 0) (O : Y.Opens) (h : O ≤ π ⁻¹ᵁ (bo R c).1)
    (r : Γ(Sp R, (bo R c).1)) : dd O (cst π (bo R c).1 h r) = 0 := by
  let s : Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c
  have hu : IsUnit (resV R c c) := IsLocalization.Away.algebraMap_isUnit (S := Γ(Sp R, (Sp R).basicOpen s)) s
  obtain ⟨k, y, hy⟩ := IsLocalization.Away.surj (S := Γ(Sp R, (Sp R).basicOpen s)) s r
  have hy' : r * resV R c (c ^ k) = resV R c ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom y) := by
    rw [map_pow]
    refine hy.trans ?_
    show _ = algebraMap Γ(Sp R, ⊤) Γ(Sp R, (Sp R).basicOpen s) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom y))
    simp
  have e := congrArg (fun z => dd O (cst π (bo R c).1 h z)) hy'
  simp only [map_mul] at e
  have hu' : IsUnit (cst π (bo R c).1 h (resV R c (c ^ k))) := by
    rw [map_pow]
    exact (hu.pow k).map _
  rw [hd.2.1 O le_top, cst_resV π c h (c ^ k), cst_resV, h0, h0, ← cst_resV π c h (c ^ k)] at e
  exact hu'.mul_right_eq_zero.1 (by linear_combination e)

theorem exists_heat_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (c : R), c = ∏ i, tt i → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R) (dd' : Fin n → Fld t.G.left), (∀ a, IsInv t.G (v' a) (dd' a)) → ∀ (Θ₁ : Matrix (Fin n) (Fin n) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (DV : Derivation ℤ Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), (∀ r, DV (GlobalTheory.HeatV.resV R c r) = GlobalTheory.HeatV.resV R c (D r)) → IsKS t (GlobalTheory.HeatV.bo R c).1 (GlobalTheory.HeatV.bo R c) (fun a => spMap (dualMap (GlobalTheory.HeatV.resV R c)) ≫ (tv (v' a)).left) ⇑DV Θ₁ → ∃ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (d : J → Fld t.G.left) (u : Fin n → Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (pf pf' : ∀ i, Γ(t.G.left, W i)) (hW : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1), ⨆ i, W i = t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 ∧ (∀ i, W i ≤ t.PP.L.U (j i)) ∧ (∀ i, IsField (W i) (d i)) ∧ (∀ i O (h : O ≤ W i) (a : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), d i O (GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) a) = GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) (DV a)) ∧ (∀ (k : ℕ) i i' O (h : O ≤ W i ⊓ W i') (f : Γ(t.G.left, O)), GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i) (pf i) (pf' i) k O (h.trans (inf_le_left.trans (hW i))) (pbT (𝟙 t.G.left) (t.PP.L.g (j i) (j i')).val O ^ k * f) = pbT (𝟙 t.G.left) (t.PP.L.g (j i) (j i')).val O ^ k * GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i') (pf i') (pf' i') k O (h.trans (inf_le_right.trans (hW i'))) f) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam _ htt hab c hc n v' D dd' hdd Θ₁ DV _ hKS
  obtain ⟨J, W, j, d, hW, hcov, hWj, hfld, hlift, hdiff⟩ :=
    ksRel_operators E H R t P m tt htt hab c hc n v' dd' hdd DV Θ₁ hKS
  have hsym := isKS_symm_abLocus E H R t P m tt htt hab c hc n v' dd' hdd DV Θ₁ hKS
  have hkill : ∀ a O (h : O ≤ t.G.hom ⁻¹ᵁ (bo R c).1) (r : Γ(Sp R, (bo R c).1)),
      dd' a O (cst t.G.hom (bo R c).1 h r) = 0 := fun a O h r =>
    field_cst_eq_zero t.G.hom c (dd' a) (hdd a).1
      (fun O' b => GlobalTheory.Heat.Adjust.inv_constFn t.G (v' a) (dd' a) (hdd a) O' b) O h r
  have h2 : IsUnit (2 : Γ(Sp R, (bo R c).1)) := by
    have : IsUnit ((2 : ℚ)) := by norm_num
    have h' := (this.map (algebraMap ℚ R)).map (resV R c)
    rwa [map_ofNat, map_ofNat] at h'
  obtain ⟨e, u, pf, pf', hglue⟩ := GlobalTheory.HeatVAlg.exists_heatV t.G.left (Sp R) t.G.hom (bo R c).1 t.PP.L t.PP.isLB h2 n
    dd' (fun a => (hdd a).1) hkill Θ₁ hsym J W j d hW hWj hfld hdiff
    (GlobalTheory.CechH1Local.exists_dlog_add_coboundary_abLocus E H R t P m tt htt hab c hc n v' dd' hdd J W j hW hcov hWj)
  refine ⟨J, W, j, fun i O' f' => d i O' f' + ∑ a, pbT t.G.hom (e a) O' * dd' a O' f', u, pf, pf', hW, hcov, hWj,
    fun i => ?_, fun i O h a => ?_, hglue⟩
  · have hF := GlobalTheory.Heat.Adjust.isField_add_comb (d i) dd' (fun a => pbT t.G.hom (e a) (W i)) (hfld i)
      fun a => (hdd a).1
    have r : ∀ O, O ≤ W i → ∀ a, rsT (pbT t.G.hom (e a) (W i)) O = pbT t.G.hom (e a) O :=
      fun O h a => rsT_pbT t.G.hom (hW i) h _
    refine ⟨fun O h f f' => ?_, fun O h f f' => ?_, fun O O' hh h f => ?_⟩
    · simpa only [r O h] using hF.1 O h f f'
    · simpa only [r O h] using hF.2.1 O h f f'
    · simpa only [r O h, r O' (hh.trans h)] using hF.2.2 O O' hh h f
  · simp only [hlift i O h a, hkill, mul_zero, Finset.sum_const_zero, add_zero]

end GlobalTheory.HeatV
