import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelA
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelASt

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Matrix
open scoped TensorProduct Matrix

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D}

theorem lamAf_eq_hatL (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
    (lamAf (F := D.host.F) Λ : Set (Fin V.rank → D.host.E ⊗[D.host.F] Formalism.MainNotions.S.Af D.host.F)) =
      (Formalism.L2.Herm.hatL (F := D.host.F) Λ : Set (Fin V.rank → D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F)) := by
  unfold lamAf Formalism.L2.Herm.hatL Formalism.UG.latS
  rw [Set.image_eq_range]
  rfl

theorem dual_of_dualL {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (h : Formalism.L2.Herm.dualL D.sp.cm V Λ = Λ) (x : Fin V.rank → D.host.E) : x ∈ Λ ↔
      ∀ y ∈ Λ, Formalism.UG.hform (starRingEnd D.host.E) V.gram y x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  have hsub : ∀ z ∈ Submodule.span (𝓞 D.host.E)
      (Formalism.BasicNotions.dualSet (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram Λ),
      z ∈ Formalism.BasicNotions.dualSet (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram Λ := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz => exact hz
    | zero =>
      intro y _
      refine ⟨0, ?_⟩
      simp [Formalism.UG.hform]
    | add a b _ _ ha hb =>
      intro y hy
      obtain ⟨u, hu⟩ := ha y hy
      obtain ⟨w, hw⟩ := hb y hy
      refine ⟨u + w, ?_⟩
      simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib] at hu hw ⊢
      rw [map_add, hu, hw]
    | smul c a _ ha =>
      intro y hy
      obtain ⟨u, hu⟩ := ha y hy
      refine ⟨c * u, ?_⟩
      have e : Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram y (c • a) =
          algebraMap (𝓞 D.host.E) D.host.E c * Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram y a := by
        simp only [Formalism.UG.hform, Pi.smul_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [Algebra.smul_def]
        ring
      rw [e, map_mul, hu]
  constructor
  · intro hx y hy
    rw [← h] at hx
    exact hsub x hx y hy
  · intro hx
    rw [← h]
    exact Submodule.subset_span hx

def framesB {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}
    (hB : Lev.IsBaseFrame V β Λ N) : UI.Frames D V :=
  UI.framesL D V Λ
    (by
      obtain ⟨-, -, hN, -, hΛ⟩ := hB
      let φ : (Fin V.rank → D.host.E) →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) := (N : 𝓞 D.host.E) • LinearMap.id
      have hinj : Function.Injective φ := by
        intro x y hxy
        have hN' : ((N : 𝓞 D.host.E) : D.host.E) ≠ 0 := by simpa using hN.ne'
        funext i
        have := congrFun hxy i
        simp only [φ, LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply] at this
        rw [Algebra.smul_def, Algebra.smul_def] at this
        exact mul_left_cancel₀ hN' this
      apply Submodule.fg_of_fg_map_injective φ hinj
      have hle : Λ.map φ ≤ UI.Lv D V := by
        rintro _ ⟨x, hx, rfl⟩
        have := hΛ x hx
        simp only [φ, LinearMap.smul_apply, LinearMap.id_apply]
        rw [show ((N : 𝓞 D.host.E) • x) = (N : D.host.E) • x by
          funext i; simp [Algebra.smul_def]]
        exact (UI.mem_Lv D V _).mpr this
      haveI : IsNoetherian (𝓞 D.host.E) (UI.Lv D V) := isNoetherian_of_fg_of_noetherian _ (UI.L_fg D V)
      have hfg := IsNoetherian.noetherian ((Λ.map φ).comap (UI.Lv D V).subtype)
      have e : ((Λ.map φ).comap (UI.Lv D V).subtype).map (UI.Lv D V).subtype = Λ.map φ := by
        rw [Submodule.map_comap_eq, Submodule.range_subtype]
        exact inf_eq_right.mpr hle
      rw [← e]
      exact hfg.map _)
    (by
      obtain ⟨-, -, hN, h0, -⟩ := hB
      rw [eq_top_iff, ← UI.L_span D V]
      apply Submodule.span_le.mpr
      intro x hx
      have hxN := h0 x ((UI.mem_Lv D V x).mp hx)
      have hN' : (N : D.host.E) ≠ 0 := by exact_mod_cast hN.ne'
      have : x = (N : D.host.E)⁻¹ • ((N : D.host.E) • x) := by rw [smul_smul, inv_mul_cancel₀ hN', one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hxN))
    (dual_of_dualL hB.2.1)

section Core

variable {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}

theorem frame_mem (hF : Formalism.L2.DIV.IsFrame β Λ) (v : Fin V.rank → Lev.EAf D) :
    v ∈ (lamAf (F := D.host.F) Λ : Set (Fin V.rank → Lev.EAf D)) ↔
      ∀ i, ((β⁻¹).val *ᵥ v) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  rw [lamAf_eq_hatL]
  exact hF v

theorem col_mem (hF : Formalism.L2.DIV.IsFrame β Λ) (j : Fin V.rank) :
    (fun i => β.val i j) ∈ (lamAf (F := D.host.F) Λ : Set (Fin V.rank → Lev.EAf D)) := by
  rw [frame_mem hF]
  intro i
  have e : ((β⁻¹).val *ᵥ (fun i => β.val i j)) i = ((β⁻¹).val * β.val) i j := rfl
  rw [e, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

theorem conj_int (hF : Formalism.L2.DIV.IsFrame β Λ) (x : GL (Fin V.rank) (Lev.EAf D))
    (hx : ∀ v, v ∈ (lamAf (F := D.host.F) Λ : Set (Fin V.rank → Lev.EAf D)) →
      x.val *ᵥ v ∈ (lamAf (F := D.host.F) Λ : Set (Fin V.rank → Lev.EAf D))) (i j : Fin V.rank) :
    ((β⁻¹).val * x.val * β.val) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have h := (frame_mem hF _).mp (hx _ (col_mem hF j)) i
  have e : ((β⁻¹).val * x.val * β.val) i j = ((β⁻¹).val *ᵥ (x.val *ᵥ (fun i => β.val i j))) i := by
    rw [Matrix.mulVec_mulVec]; rfl
  rw [e]
  exact h

end Core

section Main

variable {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}

def Stabs (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (g : GL (Fin V.rank) (Lev.EAf D)) : Prop :=
  ∀ v, v ∈ (lamAf (F := D.host.F) Λ : Set (Fin V.rank → Lev.EAf D)) →
    g.val *ᵥ v ∈ (lamAf (F := D.host.F) Λ : Set (Fin V.rank → Lev.EAf D))

theorem conj_mul (β g : GL (Fin V.rank) (Lev.EAf D)) :
    ((β⁻¹).val * g.val * β.val) * ((β⁻¹).val * (g⁻¹).val * β.val) = 1 := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc β.val (β⁻¹).val, Units.mul_inv, Matrix.one_mul, ← Matrix.mul_assoc g.val (g⁻¹).val,
    Units.mul_inv, Matrix.one_mul, Units.inv_mul]

def yMat (hF : Formalism.L2.DIV.IsFrame β Λ) (g : GL (Fin V.rank) (Lev.EAf D)) (hg : Stabs Λ g) :
    Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E) :=
  Matrix.of fun i j => ⟨((β⁻¹).val * g.val * β.val) i j, conj_int hF g hg i j⟩

theorem yMat_map (hF : Formalism.L2.DIV.IsFrame β Λ) (g : GL (Fin V.rank) (Lev.EAf D)) (hg : Stabs Λ g) :
    (yMat hF g hg).map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype = (β⁻¹).val * g.val * β.val := by
  ext i j; rfl

theorem yMat_mul (hF : Formalism.L2.DIV.IsFrame β Λ) (g : GL (Fin V.rank) (Lev.EAf D)) (hg : Stabs Λ g)
    (hgi : Stabs Λ g⁻¹) : yMat hF g hg * yMat hF g⁻¹ hgi = 1 := by
  have hinj : Function.Injective fun M : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E) =>
      M.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype := Matrix.map_injective Subtype.val_injective
  apply hinj
  have e : (yMat hF g hg * yMat hF g⁻¹ hgi).map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)).map
        (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype := by
    rw [Matrix.map_mul, yMat_map, yMat_map, conj_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  exact e

theorem yMat_congr (hF : Formalism.L2.DIV.IsFrame β Λ) {g g' : GL (Fin V.rank) (Lev.EAf D)} (h : g = g') (hg : Stabs Λ g)
    (hg' : Stabs Λ g') : yMat hF g hg = yMat hF g' hg' := by
  subst h; rfl

def yOf (hF : Formalism.L2.DIV.IsFrame β Λ) (g : GL (Fin V.rank) (Lev.EAf D)) (hg : Stabs Λ g) (hgi : Stabs Λ g⁻¹) :
    GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E) :=
  ⟨yMat hF g hg, yMat hF g⁻¹ hgi, yMat_mul hF g hg hgi,
    by
      have hgi' : Stabs Λ g⁻¹⁻¹ := by rw [inv_inv]; exact hg
      have h := yMat_mul hF g⁻¹ hgi hgi'
      have e : yMat hF g⁻¹⁻¹ hgi' = yMat hF g hg := yMat_congr hF (inv_inv g) hgi' hg
      rw [e] at h
      exact h⟩

theorem frGL_yOf (hF : Formalism.L2.DIV.IsFrame β Λ) (g : GL (Fin V.rank) (Lev.EAf D)) (hg : Stabs Λ g) (hgi : Stabs Λ g⁻¹) :
    Formalism.L2.DIV.frGL β (yOf hF g hg hgi) = g := by
  apply Units.ext
  show β.val * ((yMat hF g hg).map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) * (β⁻¹).val = g.val
  rw [yMat_map]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc β.val (β⁻¹).val, Units.mul_inv, Matrix.one_mul]
  simp

theorem conj_entry (hF : Formalism.L2.DIV.IsFrame β Λ) (g : GL (Fin V.rank) (Lev.EAf D)) (M : ℕ) (j : Fin V.rank)
    (z : Fin V.rank → Lev.EAf D) (hgz : (g.val - 1) *ᵥ (fun i => β.val i j) = (M : Lev.EAf D) • z) (i : Fin V.rank) :
    ((β⁻¹).val * g.val * β.val) i j =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) i j + (M : Lev.EAf D) * ((β⁻¹).val *ᵥ z) i := by
  have e1 : ((β⁻¹).val * g.val * β.val) i j = ((β⁻¹).val *ᵥ (g.val *ᵥ (fun i => β.val i j))) i := by
    rw [Matrix.mulVec_mulVec]; rfl
  have e2 : g.val *ᵥ (fun i => β.val i j) = (fun i => β.val i j) + (M : Lev.EAf D) • z := by
    rw [← hgz, Matrix.sub_mulVec, Matrix.one_mulVec, add_sub_cancel]
  have e3 : ((β⁻¹).val *ᵥ (fun i => β.val i j)) i = (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) i j := by
    show ((β⁻¹).val * β.val) i j = _
    rw [Units.inv_mul]
  rw [e1, e2, Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, e3, smul_eq_mul]

theorem ent_eq (hF : Formalism.L2.DIV.IsFrame β Λ) (g : GL (Fin V.rank) (Lev.EAf D)) (hg : Stabs Λ g) (hgi : Stabs Λ g⁻¹)
    (M : ℕ) (j : Fin V.rank) (z : Fin V.rank → Lev.EAf D)
    (hgz : (g.val - 1) *ᵥ (fun i => β.val i j) = (M : Lev.EAf D) • z) (i : Fin V.rank)
    (hs : ((β⁻¹).val *ᵥ z) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    (yOf hF g hg hgi).val i j = (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)) i j +
      (M : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨_, hs⟩ := by
  apply Subtype.ext
  have ht := conj_entry hF g M j z hgz i
  refine ht.trans ?_
  rw [Subring.coe_add, Subring.coe_mul, Subring.coe_natCast]
  congr 1
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · rfl
  · rfl

theorem natCast_kP_eq_zero_of_mem (PP : Formalism.L2.DIV.Pl D.host.E) (M : ℕ) (hP : ((M : 𝓞 D.host.E)) ∈ PP.asIdeal) :
    (M : Formalism.L2.DIV.kP PP) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal) M]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hP

theorem map_res_one (PP : Formalism.L2.DIV.Pl D.host.E) (M : ℕ) (hP : ((M : 𝓞 D.host.E)) ∈ PP.asIdeal)
    (S : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)) :
    (RingHom.mapMatrix (Formalism.L2.DIV.resS D.host.F PP)) (1 + M • S) = 1 := by
  rw [map_add, map_one, map_nsmul, ← Nat.cast_smul_eq_nsmul (Formalism.L2.DIV.kP PP), natCast_kP_eq_zero_of_mem PP M hP, zero_smul,
    add_zero]

theorem redFn_yOf (hF : Formalism.L2.DIV.IsFrame β Λ) (g : GL (Fin V.rank) (Lev.EAf D)) (hg : Stabs Λ g) (hgi : Stabs Λ g⁻¹)
    (M : ℕ) (hM : ∀ j, ∃ z ∈ (lamAf (F := D.host.F) Λ : Set (Fin V.rank → Lev.EAf D)),
      (g.val - 1) *ᵥ (fun i => β.val i j) = (M : Lev.EAf D) • z) (PP : Formalism.L2.DIV.Pl D.host.E)
    (hP : ((M : 𝓞 D.host.E)) ∈ PP.asIdeal) : Formalism.L2.DIV.redFn β PP g = 1 := by
  choose z hz hgz using hM
  have hs : ∀ i j, ((β⁻¹).val *ᵥ z j) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun i j => (frame_mem hF (z j)).mp (hz j) i
  let S : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E) := Matrix.of fun i j => ⟨_, hs i j⟩
  have hY : (yOf hF g hg hgi).val = 1 + M • S := by
    refine Matrix.ext fun i j => ?_
    rw [Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul]
    exact ent_eq hF g hg hgi M j (z j) (hgz j) i (hs i j)
  have e1 : Formalism.L2.DIV.redFn β PP g = Formalism.UG.bc (Formalism.L2.DIV.resS D.host.F PP) (yOf hF g hg hgi) := by
    conv_lhs => rw [← frGL_yOf hF g hg hgi]
    exact Formalism.L2.DIV.redFn_frGL β PP _
  rw [e1]
  apply Units.ext
  have e2 : ((Formalism.UG.bc (Formalism.L2.DIV.resS D.host.F PP) (yOf hF g hg hgi) : GL (Fin V.rank) (Formalism.L2.DIV.kP PP)) :
      Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.DIV.kP PP)) =
      (RingHom.mapMatrix (Formalism.L2.DIV.resS D.host.F PP)) (yOf hF g hg hgi).val := rfl
  rw [e2, hY, map_res_one PP M hP S, Units.val_one]

end Main

end Formalism.IndefR.Eqv

end
