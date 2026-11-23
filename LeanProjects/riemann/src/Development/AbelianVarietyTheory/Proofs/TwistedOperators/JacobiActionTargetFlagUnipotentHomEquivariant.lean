import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MixPer.JacHom

variable {D : D7}

theorem mul_strictUp_eq_zero {ρ m : ℕ} {y : Mx D m ρ} (hy : ∀ u ∈ UX D ρ, y ⬝ u.1 = y) {T : Mx D ρ ρ}
    (hT : GlobalTheory.BesselChar.StrictUp T) : y ⬝ T = 0 := by
  have hbt : (1 + T).BlockTriangular id := fun i j h => by
    have h' : j < i := h
    rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt h'), hT i j (le_of_lt h'), add_zero]
  have hdiag : ∀ i, (1 + T) i i = 1 := fun i => by
    rw [Matrix.add_apply, Matrix.one_apply_eq, hT i i le_rfl, add_zero]
  have hdet : (1 + T).det = 1 := by
    rw [Matrix.det_of_upperTriangular hbt]
    simp only [hdiag, Finset.prod_const_one]
  have hu : IsUnit (1 + T) := (Matrix.isUnit_iff_isUnit_det _).2 (by rw [hdet]; exact isUnit_one)
  have hmem : hu.unit ∈ UX D ρ := mem_UX.2 fun i j =>
    ⟨fun h => by rw [IsUnit.unit_spec]; exact hbt h, by rw [IsUnit.unit_spec]; exact hdiag i⟩
  have h := hy _ hmem
  rw [IsUnit.unit_spec, Matrix.mul_add, Matrix.mul_one] at h
  exact add_left_cancel (h.trans (add_zero y).symm)

section Sympl

variable {S T : HSp D}

theorem symplOH_skew (x y : WO S T) : symplOH S T y x = -symplOH S T x y := by
  unfold symplOH
  rw [GlobalTheory.OrientedHeis.symplO_skew, mul_neg]

theorem symplOH_neg_right (x y : WO S T) : symplOH S T x (-y) = -symplOH S T x y := by
  have h := GlobalTheory.OrientedHeis.symplOH_add_right x y (-y)
  rw [add_neg_cancel, symplOH_zero_right] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem hO_mt (g : GA D T) (x v : WO S T) : hO S T (mt T g ⬝ x) (mt T g ⬝ v) = hO S T x v := by
  rw [hO_eq_trace, hO_eq_trace, adj_mul]
  have h := mt_unitary T g
  congr 1
  rw [Matrix.mul_assoc (adj v), ← Matrix.mul_assoc (gA T), ← Matrix.mul_assoc (adj (mt T g)), h]

theorem symplOH_mt (g : GA D T) (x v : WO S T) : symplOH S T (mt T g ⬝ x) (mt T g ⬝ v) = symplOH S T x v := by
  rw [symplOH_eq, symplOH_eq, hO_mt]

theorem symplOH_mt_right (g : GA D T) (x v : WO S T) : symplOH S T x (mt T g ⬝ v) = symplOH S T (mt T g⁻¹ ⬝ x) v := by
  rw [← symplOH_mt g⁻¹ x (mt T g ⬝ v), ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]

theorem eq_zero_of_eq_neg {x : AF D.host.F} (h : x = -x) : x = 0 := by
  have h2 : x + x = 0 := by
    calc x + x = -x + x := by rw [← h]
      _ = 0 := neg_add_cancel x
  calc x = algebraMap D.host.F (AF D.host.F) (1 / 2) * (x + x) := by
        rw [mul_add, ← add_mul, ← map_add, add_halves, map_one, one_mul]
    _ = 0 := by rw [h2, mul_zero]

end Sympl

section Main

variable (ψ : AddChar (AF D.host.F) ℂ) {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (y : Mx D S.rank ρ)

theorem pY_incAdj : d.pY ⬝ d.incAdj S y = incA D (-D.host.xi0⁻¹) • (adj y ⬝ gA S) := by
  rw [d.incAdj_apply, d.incY_apply, ← Matrix.mul_assoc, d.pY_jY, Matrix.one_mul]

theorem jY_pY_incAdj : d.jY ⬝ (d.pY ⬝ d.incAdj S y) = d.incAdj S y := by
  rw [pY_incAdj, d.incAdj_apply, d.incY_apply]

theorem hom_space_symplectic_adjoint_inclusion_anisotropic_zero (p : WO S T₀) : symplOH S T (d.incAdj S y) (d.inc0 S p) = 0 :=
  d.wittDecomp_sympl_inclDual_inclAnisotropic S _ p

theorem hom_space_symplectic_anisotropic_isotropic_inclusion_zero (p : WO S T₀) (ξ : Mx D ρ S.rank) : symplOH S T (d.inc0 S p) (d.incX S ξ) = 0 := by
  rw [symplOH_skew, d.wittDecomp_sympl_inclIsotropic_inclAnisotropic, neg_zero]

theorem ptT_one : ptT d S y 1 = 0 := by
  rw [ptT, inv_one, mt_one, Matrix.one_mul, d.incAdj_apply, d.incY_apply, ← Matrix.mul_assoc, d.p0_jY, Matrix.zero_mul]

theorem cenT_one : cenT d S y 1 = 0 := by
  rw [cenT, inv_one, mt_one, Matrix.one_mul, GlobalTheory.OrientedHeis.symplOH_self]

theorem pY_mt_inv {n : GA D T} {U : Mx D ρ ρ} (h1 : mt T n ⬝ d.jX = d.jX + d.jX ⬝ U) :
    d.pY ⬝ mt T n⁻¹ = d.pY + adj U ⬝ d.pY := by
  rw [mt_inv, d.pY_eq, Matrix.mul_assoc, gA_giA_cancel, ← Matrix.mul_assoc, ← adj_mul, h1, adj_add, adj_mul,
    Matrix.add_mul]
  simp only [Matrix.mul_assoc]

theorem pY_inv_incAdj (hy : ∀ u ∈ UX D ρ, y ⬝ u.1 = y) {n : GA D T} (hn : n ∈ flagN d) :
    d.pY ⬝ (mt T n⁻¹ ⬝ d.incAdj S y) = d.pY ⬝ d.incAdj S y := by
  obtain ⟨U, b, hU, h1, -⟩ := exists_blocks d hn
  have hyU := mul_strictUp_eq_zero hy hU
  have e := pY_mt_inv d h1
  have e2 : d.pY ⬝ (mt T n⁻¹ ⬝ d.incAdj S y) = d.pY ⬝ d.incAdj S y + adj U ⬝ (d.pY ⬝ d.incAdj S y) := by
    rw [← Matrix.mul_assoc, e, Matrix.add_mul, Matrix.mul_assoc]
  have e3 : adj U ⬝ (d.pY ⬝ d.incAdj S y) = 0 := by
    rw [pY_incAdj, Matrix.mul_smul, ← Matrix.mul_assoc (adj U), ← adj_mul y U, hyU, adj_zero, Matrix.zero_mul, smul_zero]
  rw [e2, e3, add_zero]

theorem inv_incAdj (hy : ∀ u ∈ UX D ρ, y ⬝ u.1 = y) {n : GA D T} (hn : n ∈ flagN d) :
    mt T n⁻¹ ⬝ d.incAdj S y = d.incAdj S y + d.incX S (d.pX ⬝ (mt T n⁻¹ ⬝ d.incAdj S y)) +
      d.inc0 S (ptT d S y n) := by
  conv_lhs => rw [← Matrix.one_mul (mt T n⁻¹ ⬝ d.incAdj S y), ← d.sum_eq_one]
  rw [d.incX_apply, d.wittDecomp_inclAnisotropicHom_apply, ptT]
  simp only [Matrix.add_mul, Matrix.mul_assoc]
  rw [pY_inv_incAdj d S y hy hn, jY_pY_incAdj]
  abel

theorem witt_anisotropic_projection_flag_unipotent_isotropic_zero {g : GA D T} (hg : g ∈ flagN d) (ξ : Mx D ρ S.rank) : d.p0 ⬝ (mt T g ⬝ d.incX S ξ) = 0 := by
  obtain ⟨U, b, -, h1, -⟩ := exists_blocks d hg
  rw [d.incX_apply, ← Matrix.mul_assoc (mt T g), h1]
  simp only [Matrix.add_mul, Matrix.mul_add, ← Matrix.mul_assoc, d.p0_jX, Matrix.zero_mul, add_zero]

theorem witt_anisotropic_projection_flag_unipotent_anisotropic {g : GA D T} (hg : g ∈ flagN d) (p : WO S T₀) : d.p0 ⬝ (mt T g ⬝ d.inc0 S p) = p := by
  obtain ⟨U, b, -, -, h2⟩ := exists_blocks d hg
  rw [d.wittDecomp_inclAnisotropicHom_apply, ← Matrix.mul_assoc (mt T g), h2]
  simp only [Matrix.add_mul, Matrix.mul_add, ← Matrix.mul_assoc, d.p0_jX, d.p0_j0, Matrix.zero_mul, Matrix.one_mul,
    add_zero]

theorem ptT_mul (hy : ∀ u ∈ UX D ρ, y ⬝ u.1 = y) {n n' : GA D T} (hn : n ∈ flagN d) (hn' : n' ∈ flagN d) :
    ptT d S y (n * n') = ptT d S y n + ptT d S y n' := by
  have e : ptT d S y (n * n') = d.p0 ⬝ (mt T n'⁻¹ ⬝ (mt T n⁻¹ ⬝ d.incAdj S y)) := by
    rw [ptT, _root_.mul_inv_rev, mt_mul, Matrix.mul_assoc]
  have e2 : d.p0 ⬝ (mt T n'⁻¹ ⬝ d.incAdj S y) = ptT d S y n' := rfl
  have hi := (flagN d).inv_mem hn'
  rw [e, inv_incAdj d S y hy hn, Matrix.mul_add, Matrix.mul_add, Matrix.mul_add, Matrix.mul_add, witt_anisotropic_projection_flag_unipotent_isotropic_zero d S hi,
    witt_anisotropic_projection_flag_unipotent_anisotropic d S hi, add_zero, e2, add_comm]

theorem ptT_inv (hy : ∀ u ∈ UX D ρ, y ⬝ u.1 = y) {n : GA D T} (hn : n ∈ flagN d) :
    ptT d S y n⁻¹ = -ptT d S y n := by
  have h := ptT_mul d S y hy ((flagN d).inv_mem hn) hn
  rw [inv_mul_cancel, ptT_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem cenT_eq (hy : ∀ u ∈ UX D ρ, y ⬝ u.1 = y) {n : GA D T} (hn : n ∈ flagN d) :
    cenT d S y n = symplOH S T (d.incAdj S y) (d.incX S (d.pX ⬝ (mt T n⁻¹ ⬝ d.incAdj S y))) := by
  have h := inv_incAdj d S y hy hn
  rw [cenT]
  conv_lhs => rw [h]
  rw [GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right,
    GlobalTheory.OrientedHeis.symplOH_self, hom_space_symplectic_adjoint_inclusion_anisotropic_zero, zero_add, add_zero]

theorem cenT_mul (hy : ∀ u ∈ UX D ρ, y ⬝ u.1 = y) {n n' : GA D T} (hn : n ∈ flagN d) (hn' : n' ∈ flagN d) :
    cenT d S y (n * n') = cenT d S y n + cenT d S y n' + symplOH S T₀ (ptT d S y n) (ptT d S y n') := by
  have e : cenT d S y (n * n') =
      symplOH S T (d.incAdj S y) (mt T n'⁻¹ ⬝ (mt T n⁻¹ ⬝ d.incAdj S y)) := by
    rw [cenT, _root_.mul_inv_rev, mt_mul, Matrix.mul_assoc]
  have hi := (flagN d).inv_mem hn'
  have e' : mt T n' ⬝ d.incAdj S y = d.incAdj S y + d.incX S (d.pX ⬝ (mt T n' ⬝ d.incAdj S y)) +
      d.inc0 S (ptT d S y n'⁻¹) := by
    have h := inv_incAdj d S y hy hi
    rwa [inv_inv] at h
  have hc' : symplOH S T (d.incAdj S y) (mt T n'⁻¹ ⬝ d.incAdj S y) = cenT d S y n' := rfl
  rw [e, inv_incAdj d S y hy hn, Matrix.mul_add, Matrix.mul_add, GlobalTheory.OrientedHeis.symplOH_add_right,
    GlobalTheory.OrientedHeis.symplOH_add_right, symplOH_mt_right n'⁻¹ (d.incAdj S y) (d.incX S _),
    symplOH_mt_right n'⁻¹ (d.incAdj S y) (d.inc0 S _), inv_inv, e']
  simp only [GlobalTheory.OrientedHeis.symplOH_add_left, d.symplOH_incX_incX, d.wittDecomp_sympl_inclIsotropic_inclAnisotropic, hom_space_symplectic_adjoint_inclusion_anisotropic_zero,
    hom_space_symplectic_anisotropic_isotropic_inclusion_zero, d.wittDecomp_sympl_inclAnisotropic_inclAnisotropic, add_zero, zero_add]
  rw [hc', ← cenT_eq d S y hy hn, ptT_inv d S y hy hn', symplOH_skew, symplOH_neg_right, neg_neg]
  ring

theorem jacT_mul (hy : ∀ u ∈ UX D ρ, y ⬝ u.1 = y) {n n' : GA D T} (hn : n ∈ flagN d) (hn' : n' ∈ flagN d)
    (f : WO S T₀ → ℂ) : jacT ψ d S y (n * n') f = jacT ψ d S y n (jacT ψ d S y n' f) := by
  have hs : ∀ (c : ℂ) (p : WO S T₀) (g : WO S T₀ → ℂ), heisO ψ S T₀ p (c • g) = c • heisO ψ S T₀ p g := by
    intro c p g
    funext w
    simp only [heisO, Pi.smul_apply, smul_eq_mul]
    ring
  rw [jacT, jacT, jacT, cenT_mul d S y hy hn hn', ptT_mul d S y hy hn hn', hs, GlobalTheory.OrientedHeis.heisO_heisO,
    smul_smul, smul_smul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]

theorem cenT_inv (hy : ∀ u ∈ UX D ρ, y ⬝ u.1 = y) {n : GA D T} (hn : n ∈ flagN d) :
    cenT d S y n⁻¹ = -cenT d S y n := by
  have h := cenT_mul d S y hy hn ((flagN d).inv_mem hn)
  rw [mul_inv_cancel, cenT_one, ptT_inv d S y hy hn, symplOH_neg_right, GlobalTheory.OrientedHeis.symplOH_self, neg_zero,
    add_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem inv_nB_incAdj (b : Mx D ρ T₀.rank) :
    mt T (d.nB b)⁻¹ ⬝ d.incAdj S y = d.incAdj S y +
      d.incX S (-((half D • (b ⬝ plus T₀ b)) ⬝ (d.pY ⬝ d.incAdj S y))) +
      d.inc0 S (plus T₀ b ⬝ (d.pY ⬝ d.incAdj S y)) := by
  set η := d.pY ⬝ d.incAdj S y with hη
  have hw : d.incAdj S y = d.jY ⬝ η := (jY_pY_incAdj d S y).symm
  rw [hw, d.nB_inv, ← Matrix.mul_assoc, d.nB_jY, plus_neg, d.incX_apply, d.wittDecomp_inclAnisotropicHom_apply]
  simp only [Matrix.sub_mul, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  abel

theorem cenT_nB_eq (b : Mx D ρ T₀.rank) :
    cenT d S y (d.nB b) = symplOH S T (d.incAdj S y)
      (d.incX S (-((half D • (b ⬝ plus T₀ b)) ⬝ (d.pY ⬝ d.incAdj S y)))) := by
  rw [cenT, inv_nB_incAdj, GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right,
    GlobalTheory.OrientedHeis.symplOH_self, hom_space_symplectic_adjoint_inclusion_anisotropic_zero, zero_add, add_zero]

theorem cenT_nB (hy : ∀ u ∈ UX D ρ, y ⬝ u.1 = y) (b : Mx D ρ T₀.rank) : cenT d S y (d.nB b) = 0 := by
  have h1 : cenT d S y (d.nB (-b)) = cenT d S y (d.nB b) := by
    rw [cenT_nB_eq, cenT_nB_eq, plus_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  have h2 := cenT_inv d S y hy (d.nB_mem_NFlag b)
  rw [d.nB_inv, h1] at h2
  exact eq_zero_of_eq_neg h2

theorem ptT_nC (c : skewA D ρ) : ptT d S y (d.nC c) = 0 := by
  have h := ptT_nB_mul_nC d S y 0 c
  rwa [d.nB_zero, one_mul, plus_zero, Matrix.zero_mul] at h

theorem cenT_nB_mul_nC (hy : ∀ u ∈ UX D ρ, y ⬝ u.1 = y) (b : Mx D ρ T₀.rank) (c : skewA D ρ) :
    cenT d S y (d.nB b * d.nC c) = d.qT S c y := by
  rw [cenT_mul d S y hy (d.nB_mem_NFlag b) (d.nC_mem_NFlag c), cenT_nB d S y hy, cenT_nC, ptT_nC,
    symplOH_zero_right, zero_add, add_zero]

theorem incAdj_levi (hy : ∀ u ∈ UX D ρ, y ⬝ u.1 = y) {u : GL (Fin ρ) (AE D)} (hu : u ∈ UX D ρ) :
    mt T (d.levi u) ⬝ d.incAdj S y = d.incAdj S y := by
  have h := levi_inv_incAdj d S y u⁻¹
  rwa [map_inv, inv_inv, hy _ ((UX D ρ).inv_mem hu)] at h

theorem jacT_mul_levi (hy : ∀ u ∈ UX D ρ, y ⬝ u.1 = y) (n : GA D T) {u : GL (Fin ρ) (AE D)} (hu : u ∈ UX D ρ) :
    jacT ψ d S y (n * d.levi u) = jacT ψ d S y n := by
  have hp : ptT d S y (n * d.levi u) = ptT d S y n := by
    rw [ptT, ptT, _root_.mul_inv_rev, mt_mul, Matrix.mul_assoc, ← Matrix.mul_assoc d.p0, ← map_inv, d.wittDecomp_projAnisotropic_levi]
  have hc : cenT d S y (n * d.levi u) = cenT d S y n := by
    rw [cenT, cenT, _root_.mul_inv_rev, mt_mul, Matrix.mul_assoc, symplOH_mt_right, inv_inv, incAdj_levi d S y hy hu]
  funext f
  rw [jacT, jacT, hp, hc]

theorem witt_embedded_anisotropic_fixes_adjoint_inclusion (g : GA D T₀) : mt T (d.emb0 g) ⬝ d.incAdj S y = d.incAdj S y := by
  rw [d.incAdj_apply, d.incY_apply, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclY]

theorem heisenberg_target_point_central_conj_embedded_anisotropic (n : GA D T) (g : GA D T₀) :
    ptT d S y (d.emb0 g * n * (d.emb0 g)⁻¹) = actO S T₀ 1 g (ptT d S y n) ∧
      cenT d S y (d.emb0 g * n * (d.emb0 g)⁻¹) = cenT d S y n := by
  have hinv : (d.emb0 g * n * (d.emb0 g)⁻¹)⁻¹ = d.emb0 g * n⁻¹ * (d.emb0 g)⁻¹ := by group
  have he : mt T (d.emb0 g)⁻¹ ⬝ d.incAdj S y = d.incAdj S y := by rw [← map_inv]; exact witt_embedded_anisotropic_fixes_adjoint_inclusion d S y _
  have hm : mt T (d.emb0 g * n * (d.emb0 g)⁻¹)⁻¹ ⬝ d.incAdj S y = mt T (d.emb0 g) ⬝ (mt T n⁻¹ ⬝ d.incAdj S y) := by
    rw [hinv, mt_mul, mt_mul, Matrix.mul_assoc, he, Matrix.mul_assoc]
  constructor
  · rw [ptT, hm, ← Matrix.mul_assoc d.p0, d.wittDecomp_projAnisotropic_anisotropicEmbedding, actO_eq, inv_one, mt_one, Matrix.mul_one, ptT, Matrix.mul_assoc]
  · rw [cenT, hm, symplOH_mt_right, ← map_inv, witt_embedded_anisotropic_fixes_adjoint_inclusion, cenT]

end Main

end GlobalTheory.MixPer.JacHom

open GlobalTheory.MixPer.JacHom in

theorem GlobalTheory.MixPer.jacT_hom : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (T T₀ S : HSp D) (ρ : ℕ) (d : HypDec T T₀ ρ)
    (y : Mx D S.rank ρ), (∀ u ∈ UX D ρ, y ⬝ u.1 = y) → (∀ b c, cenT d S y (d.nB b * d.nC c) = d.qT S c y) ∧
    (∀ n ∈ flagN d, ∀ n' ∈ flagN d, ptT d S y (n * n') = ptT d S y n + ptT d S y n' ∧
      cenT d S y (n * n') = cenT d S y n + cenT d S y n' + symplOH S T₀ (ptT d S y n) (ptT d S y n') ∧
      ∀ f, jacT ψ d S y (n * n') f = jacT ψ d S y n (jacT ψ d S y n' f)) ∧
    (∀ n ∈ flagN d, ∀ u ∈ UX D ρ, jacT ψ d S y (n * d.levi u) = jacT ψ d S y n) ∧
    ∀ n g, ptT d S y (d.emb0 g * n * (d.emb0 g)⁻¹) = actO S T₀ 1 g (ptT d S y n) ∧
      cenT d S y (d.emb0 g * n * (d.emb0 g)⁻¹) = cenT d S y n := by
  intro D ψ T T₀ S ρ d y hy
  exact ⟨fun b c => cenT_nB_mul_nC d S y hy b c,
    fun n hn n' hn' => ⟨ptT_mul d S y hy hn hn', cenT_mul d S y hy hn hn', jacT_mul ψ d S y hy hn hn'⟩,
    fun n _ u hu => jacT_mul_levi ψ d S y hy n hu, fun n g => heisenberg_target_point_central_conj_embedded_anisotropic d S y n g⟩

end
