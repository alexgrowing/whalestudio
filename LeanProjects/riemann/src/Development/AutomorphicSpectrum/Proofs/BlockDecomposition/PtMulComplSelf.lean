import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.CellDefs
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PtMMapOfZero

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Cell

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.CellDecomp

section Weyl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem matHom_proj_weyl (σ : E →ₐ[F] E) (J : Matrix (Fin (n + n)) (Fin (n + n)) E)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (g : GAd σ J)
    (hg : (matHom _ σ J g).1 = blk4 0 1 (-1) 0) :
    (matHom _ σ J (proj σ J v g)).1 = blk4 (0 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) 1 (-1) 0 := by
  rw [matHom_proj, bc_val, hg]
  exact weyl_map _

theorem stab_of_weyl (σ : E →ₐ[F] E) (J : Matrix (Fin (n + n)) (Fin (n + n)) E)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (k : GLoc σ J v)
    (hk : (matHom _ σ J k).1 = blk4 (0 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) 1 (-1) 0) :
    k ∈ stabLoc σ J (stdLattice E (n + n)) v := by
  rw [stabLoc, Subgroup.mem_comap]
  change ∀ x, x ∈ latLoc F (stdLattice E (n + n)) v ↔ (↑(matHom _ σ J k) : Matrix _ _ _).mulVec x ∈ latLoc F (stdLattice E (n + n)) v
  rw [hk]
  have hmap : ∀ y ∈ latLoc F (stdLattice E (n + n)) v,
      (blk4 (0 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) 1 (-1) 0).mulVec y ∈ latLoc F (stdLattice E (n + n)) v := by
    intro y hy
    change y ∈ AddSubgroup.closure _ at hy
    change _ ∈ AddSubgroup.closure _
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      apply AddSubgroup.subset_closure
      refine ⟨a, ha, (blk4 (0 : Matrix (Fin n) (Fin n) E) 1 (-1) 0).mulVec x, ?_, ?_⟩
      · change _ ∈ Submodule.pi _ _ at hx ⊢
        rw [Submodule.mem_pi] at hx ⊢
        intro j _
        obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
        rcases s with i | i
        · rw [(weyl_mulVec x i).1]
          exact hx _ (Set.mem_univ _)
        · rw [(weyl_mulVec x i).2]
          exact neg_mem (hx _ (Set.mem_univ _))
      · funext j
        obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
        rcases s with i | i
        · rw [(weyl_mulVec _ i).1, (weyl_mulVec x i).1]
        · rw [(weyl_mulVec _ i).2, (weyl_mulVec x i).2, TensorProduct.tmul_neg]
    | zero =>
      rw [Matrix.mulVec_zero]
      exact zero_mem _
    | add y z _ _ hy hz =>
      rw [Matrix.mulVec_add]
      exact add_mem hy hz
    | neg y _ hy =>
      rw [Matrix.mulVec_neg]
      exact neg_mem hy
  have hWW : ∀ y : Fin (n + n) → Fv F v ⊗[F] E,
      (blk4 (0 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) 1 (-1) 0).mulVec
        ((blk4 (0 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) 1 (-1) 0).mulVec y) = -y := by
    intro y
    funext j
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
    rcases s with i | i
    · rw [(weyl_mulVec _ i).1, (weyl_mulVec y i).2, Pi.neg_apply]
    · rw [(weyl_mulVec _ i).2, (weyl_mulVec y i).1, Pi.neg_apply]
  intro x
  constructor
  · exact hmap x
  · intro hx
    have h2 := neg_mem (hmap _ hx)
    rwa [hWW, neg_neg] at h2

end Weyl

section Main

variable {D : D7} {n : ℕ}

theorem pt_comm {e : AE D} (he : e * e = e) (hc : cA D e = e) (he' : (1 - e) * (1 - e) = 1 - e)
    (hc' : cA D (1 - e) = 1 - e) (x y : G D n) :
    pt e he hc x * pt (1 - e) he' hc' y = pt (1 - e) he' hc' y * pt e he hc x := by
  apply mat_inj
  rw [mat_mul', mat_mul', mat_pt, mat_pt, (ptM_mul_compl he he' _ _).1, (ptM_mul_compl he he' _ _).2]

theorem pt_mul_compl_self {e : AE D} (he : e * e = e) (hc : cA D e = e) (he' : (1 - e) * (1 - e) = 1 - e)
    (hc' : cA D (1 - e) = 1 - e) (x : G D n) : pt e he hc x * pt (1 - e) he' hc' x = x := by
  apply mat_inj
  rw [mat_mul', mat_pt, mat_pt, (ptM_mul_compl he he' _ _).1, ← add_smul, add_sub_cancel, one_smul]

theorem pt_nb {e : AE D} (he : e * e = e) (hc : cA D e = e) {nb : hermA D n → G D n} (hnb : IsNMap nb)
    (x : hermS D n e) : pt e he hc (nb x.1) = nb x.1 := by
  apply mat_inj
  rw [mat_pt, hnb, ptM_unip he x.2]

theorem proj_weyl {w : G D n} (hw : IsW w) (v : Pl D) :
    proj D.sp.cm.sig (Jst D n) v w ∈ stabLoc D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) v := by
  exact stab_of_weyl _ _ v _ (matHom_proj_weyl _ _ v w hw)

theorem proj_pt_zero {f : AE D} (hf : f * f = f) (hc : cA D f = f) (x : G D n) {v : Pl D} (h : cv D v f = 0) :
    proj D.sp.cm.sig (Jst D n) v (pt f hf hc x) = 1 := by
  refine matHom_injective _ _ _ (Units.ext ?_)
  rw [matHom_proj, map_one, bc_val]
  exact ptM_map_of_zero (cv D v) hf h (mat x)

theorem proj_pt_one {f : AE D} (hf : f * f = f) (hc : cA D f = f) (x : G D n) {v : Pl D} (h : cv D v f = 1) :
    proj D.sp.cm.sig (Jst D n) v (pt f hf hc x) = proj D.sp.cm.sig (Jst D n) v x := by
  refine matHom_injective _ _ _ (Units.ext ?_)
  rw [matHom_proj, matHom_proj, bc_val, bc_val]
  exact ptM_map_of_one (cv D v) hf h (mat x)

theorem projArch_pt_zero {f : AE D} (hf : f * f = f) (hc : cA D f = f) (x : G D n) {w : NumberField.InfinitePlace D.host.F}
    (h : compInf D.host.F D.host.E w f = 0) : projArch D.sp.cm.sig (Jst D n) w (pt f hf hc x) = 1 := by
  refine matHom_injective _ _ _ (Units.ext ?_)
  rw [matHom_projArch, map_one, bc_val]
  exact ptM_map_of_zero (compInf D.host.F D.host.E w) hf h (mat x)

theorem cv_of_mem {S : Finset (Pl D)} {e : AE D} (hS : IsIdem S e) {v : Pl D} (hv : v ∈ S) : cv D v e = 1 := by
  rw [hS.2 v, if_pos hv]

theorem cv_of_not_mem {S : Finset (Pl D)} {e : AE D} (hS : IsIdem S e) {v : Pl D} (hv : v ∉ S) : cv D v e = 0 := by
  rw [hS.2 v, if_neg hv]

theorem pt_mem_KOff {S : Finset (Pl D)} {e : AE D} (hS : IsIdem S e) (he' : (1 - e) * (1 - e) = 1 - e)
    (hc' : cA D (1 - e) = 1 - e) {x : G D n}
    (hx : ∀ v, proj D.sp.cm.sig (Jst D n) v x ∈ stabLoc D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) v) :
    pt (1 - e) he' hc' x ∈ KOff D n S := by
  refine mem_levelOff.2 ⟨mem_finPts_iff_forall.2 fun w => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · exact projArch_pt_zero he' hc' x (map_compl_zero _ (hS.1 w))
  · exact proj_pt_zero he' hc' x (map_compl_zero _ (cv_of_mem hS hv))
  · rw [proj_pt_one he' hc' x (map_compl_one _ (cv_of_not_mem hS hv))]
    exact hx v

theorem mat_inv_wn {w : G D n} (hw : IsW w) {nb : hermA D n → G D n} (hnb : IsNMap nb) (y : hermA D n) :
    mat (w * nb y)⁻¹ = blk4 (-y.1) (-1) 1 0 := by
  have hw' : mat w = blk4 0 1 (-1) 0 := hw
  have h1 : mat (w * nb y) * blk4 (-y.1) (-1) 1 0 = 1 := by
    rw [mat_mul', hw', hnb, weyl_inv]
  have h2 : mat (w * nb y)⁻¹ * mat (w * nb y) = 1 := by
    rw [← mat_mul', inv_mul_cancel, mat_one']
  calc mat (w * nb y)⁻¹ = mat (w * nb y)⁻¹ * (mat (w * nb y) * blk4 (-y.1) (-1) 1 0) := by
        rw [h1, mul_one]
    _ = blk4 (-y.1) (-1) 1 0 := by rw [← mul_assoc, h2, one_mul]

theorem cB_quot {e : AE D} (he : e * e = e) (hc : cA D e = e) {w : G D n} (hw : IsW w) {nb : hermA D n → G D n}
    (hnb : IsNMap nb) (g : G D n) (y : hermA D n) (hy : mm (e • cB g) y.1 = e • dB g) :
    cB (pt e he hc (g * (w * nb y)⁻¹)) = 0 := by
  rw [cB_pt, cB_mul, blkA_of (mat_inv_wn hw hnb y), cB_of (mat_inv_wn hw hnb y)]
  exact cell_alg hy

theorem cB_off {f : AE D} (hf : f * f = f) (hc : cA D f = f) {q : G D n} (hq : q ∈ P D n) :
    cB (pt f hf hc q) = 0 := by
  rw [cB_pt, cB_of_mem_P hq, smul_zero]

theorem decomp (hI : IdemEx) : Decomp := by
  intro D p nb hnb w hw S e hS g _ y hy
  obtain ⟨he, hc⟩ := (hI D S).2 e hS
  have he' := idem_compl he
  have hc' : cA D (1 - e) = 1 - e := by rw [map_sub, map_one, hc]
  obtain ⟨q₀, hq₀, k₀, hk₀, hgk⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D p g
  have hA : pt e he hc (nb y.1) = nb y.1 := pt_nb he hc hnb y
  have key := assemble (pt e he hc) (pt (1 - e) he' hc') (pt_comm he hc he' hc')
    (pt_mul_compl_self he hc he' hc') (w := w) hA hgk
  refine ⟨pt e he hc (g * (w * nb y.1)⁻¹) * pt (1 - e) he' hc' q₀, ?_, pt (1 - e) he' hc' (w⁻¹ * k₀), ?_, key, ?_⟩
  · exact mul_mem (mem_siegelParabolic_of_lowerLeft_eq_zero (cB_quot he hc hw hnb g y.1 hy)) (mem_siegelParabolic_of_lowerLeft_eq_zero (cB_off he' hc' hq₀))
  · apply pt_mem_KOff hS he' hc'
    intro v
    have hk : proj D.sp.cm.sig (Jst D p) v k₀ ∈
        stabLoc D.sp.cm.sig (Jst D p) (stdLattice D.host.E (p + p)) v :=
      Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hk₀).1 v
    rw [map_mul, map_inv]
    exact mul_mem (inv_mem (proj_weyl hw v)) hk
  · intro x
    rw [← pt_nb he hc hnb x]
    exact pt_comm he hc he' hc' _ _

end Main

end GlobalTheory.CompanionTheory.CellDecomp

end
