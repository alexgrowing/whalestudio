import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactLevelOffFinEmpty

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LCutLow

variable {D : D7} {n : ℕ}

theorem matHom_proj_val (v : Pl D) (g : G D n) :
    (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig (Jst D n) (proj D.sp.cm.sig (Jst D n) v g)).1 = (mat g).map (cv D v) := by
  rw [GlobalTheory.AdelicU.matHom_proj]; rfl

theorem matHom_projArch_val (w : InfinitePlace D.host.F) (g : G D n) :
    (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig (Jst D n) (projArch D.sp.cm.sig (Jst D n) w g)).1 =
      (mat g).map (compInf D.host.F D.host.E w) := by
  rw [GlobalTheory.AdelicU.matHom_projArch]; rfl

theorem block_matrix_diagonal_one_eq_one {R : Type} [CommRing R] : blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 := by
  unfold blk4
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem block_matrix_entry_property {R : Type} [CommRing R] (S : Subring R) {a b c d : Matrix (Fin n) (Fin n) R}
    (ha : ∀ i j, a i j ∈ S) (hb : ∀ i j, b i j ∈ S) (hc : ∀ i j, c i j ∈ S) (hd : ∀ i j, d i j ∈ S) (i j : Fin (n + n)) :
    blk4 a b c d i j ∈ S := by
  unfold blk4
  simp only [Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i' | i' <;> rcases finSumFinEquiv.symm j with j' | j' <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  exacts [ha _ _, hb _ _, hc _ _, hd _ _]

theorem map_mat_nb {nb : hermA D n → G D n} (hnb : IsNMap nb) {S : Type} [CommRing S] (f : AE D →+* S) (x : hermA D n) :
    (mat (nb x)).map f = blk4 1 (x.1.map f) 0 1 := by
  rw [hnb x, GlobalTheory.CompanionTheory.FourierN.blk4_map_alt, Matrix.map_one _ (map_zero f) (map_one f), Matrix.map_zero _ (map_zero f)]

theorem proj_nb_eq_one {nb : hermA D n → G D n} (hnb : IsNMap nb) (v : Pl D) {x : hermA D n}
    (hx : ∀ i j, cv D v (x.1 i j) = 0) : proj D.sp.cm.sig (Jst D n) v (nb x) = 1 := by
  refine GlobalTheory.AdelicU.matHom_injective _ _ _ (Units.ext ?_)
  rw [map_one, Units.val_one, matHom_proj_val, map_mat_nb hnb]
  have : x.1.map (cv D v) = 0 := Matrix.ext fun i j => hx i j
  rw [this, block_matrix_diagonal_one_eq_one]

theorem projArch_nb_eq_one {nb : hermA D n → G D n} (hnb : IsNMap nb) (w : InfinitePlace D.host.F) {x : hermA D n}
    (hx : ∀ i j, compInf D.host.F D.host.E w (x.1 i j) = 0) : projArch D.sp.cm.sig (Jst D n) w (nb x) = 1 := by
  refine GlobalTheory.AdelicU.matHom_injective _ _ _ (Units.ext ?_)
  rw [map_one, Units.val_one, matHom_projArch_val, map_mat_nb hnb]
  have : x.1.map (compInf D.host.F D.host.E w) = 0 := Matrix.ext fun i j => hx i j
  rw [this, block_matrix_diagonal_one_eq_one]

theorem nb_mem_atPts {nb : hermA D n → G D n} (hnb : IsNMap nb) (v : Pl D) {x : hermA D n}
    (hinf : ∀ w i j, compInf D.host.F D.host.E w (x.1 i j) = 0) (hoff : ∀ v' ≠ v, ∀ i j, cv D v' (x.1 i j) = 0) :
    nb x ∈ atPts D.sp.cm.sig (Jst D n) {v} :=
  GlobalTheory.AdelicU.mem_atPts.2 ⟨GlobalTheory.AdelicU.mem_finPts_iff_forall.2 fun w => projArch_nb_eq_one hnb w (hinf w),
    fun v' hv' => proj_nb_eq_one hnb v' (hoff v' (by simpa using hv'))⟩

theorem nb_neg {nb : hermA D n → G D n} (hnb : IsNMap nb) (x : hermA D n) : nb (-x) = (nb x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← GlobalTheory.CompanionTheory.FourierN.nb_add hnb, neg_add_cancel, GlobalTheory.CompanionTheory.FourierN.nb_zero hnb])

theorem proj_nb_entry {nb : hermA D n → G D n} (hnb : IsNMap nb) (v : Pl D) {y : hermA D n}
    (hy : ∀ i j, cv D v (y.1 i j) ∈ intLoc D.host.F D.host.E v) (i j : Fin (n + n)) :
    (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig (Jst D n) (proj D.sp.cm.sig (Jst D n) v (nb y))).1 i j ∈ intLoc D.host.F D.host.E v := by
  rw [matHom_proj_val, map_mat_nb hnb]
  refine block_matrix_entry_property _ (fun a b => ?_) (fun a b => hy a b) (fun a b => ?_) (fun a b => ?_) i j
  · rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  · exact zero_mem _
  · rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem proj_nb_mem_stabLoc {nb : hermA D n → G D n} (hnb : IsNMap nb) (v : Pl D) {x : hermA D n}
    (hx : ∀ i j, cv D v (x.1 i j) ∈ intLoc D.host.F D.host.E v) :
    proj D.sp.cm.sig (Jst D n) v (nb x) ∈ stabLoc D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) v := by
  refine GlobalTheory.AdelicU.mem_stabLoc_stdLattice_iff.2 ⟨proj_nb_entry hnb v hx, ?_⟩
  have e : (proj D.sp.cm.sig (Jst D n) v (nb x))⁻¹ = proj D.sp.cm.sig (Jst D n) v (nb (-x)) := by
    rw [nb_neg hnb, map_inv]
  rw [e]
  refine proj_nb_entry hnb v fun i j => ?_
  have h1 : cv D v ((-x).1 i j) = -cv D v (x.1 i j) := RingHom.map_neg (cv D v) (x.1 i j)
  rw [h1]
  exact neg_mem (hx i j)

theorem mem_KAt_of {v : Pl D} {y : G D n}
    (h1 : y ∈ levelOpen D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n))) (h2 : y ∈ atPts D.sp.cm.sig (Jst D n) {v}) :
    y ∈ KAt D n v := by
  refine Subgroup.mem_inf.2 ⟨?_, h2⟩
  show y ∈ levelAll D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) 1
  refine GlobalTheory.AdelicU.mem_levelAll.2 ⟨GlobalTheory.AdelicU.mem_levelOpen.1 h1, fun w => ?_⟩
  rw [GlobalTheory.AdelicU.mem_finPts_iff_forall.1 (GlobalTheory.AdelicU.mem_atPts.1 h2).1 w]
  exact one_mem _

theorem nb_mem_KAt {nb : hermA D n → G D n} (hnb : IsNMap nb) (v : Pl D) {x : hermA D n} (hx : IntAt v x) :
    nb x ∈ KAt D n v := by
  refine mem_KAt_of (GlobalTheory.AdelicU.mem_levelOpen.2 fun v' => ?_) (nb_mem_atPts hnb v hx.1 hx.2.1)
  by_cases h : v' = v
  · subst h; exact proj_nb_mem_stabLoc hnb _ hx.2.2
  · rw [proj_nb_eq_one hnb v' (hx.2.1 v' h)]; exact one_mem _

theorem commute_of_atPts {v : Pl D} {x g : G D n} (hx : x ∈ atPts D.sp.cm.sig (Jst D n) {v})
    (hg : proj D.sp.cm.sig (Jst D n) v g = 1) : x * g = g * x :=
  (GlobalTheory.AdelicU.commute_atPts_awayPts _ _ hx (GlobalTheory.AdelicU.mem_awayPts.2 fun u hu => by
    rw [Finset.mem_singleton.1 hu]; exact hg)).eq

def lev (nb : hermA D n → G D n) (s : Finset (hermA D n)) : Subgroup (G D n) :=
  ⨅ x : s, (levelOpen D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n))).comap (MulAut.conj (nb x.1)⁻¹).toMonoidHom

theorem isOpen_lev (nb : hermA D n → G D n) (s : Finset (hermA D n)) : IsOpen (lev nb s : Set (G D n)) := by
  have : Submodule.IsLattice D.host.E (stdLattice D.host.E (n + n)) := GlobalTheory.AdelicU.isLattice_stdLattice
  rw [lev, Subgroup.coe_iInf]
  refine isOpen_iInter_of_finite fun x => ?_
  rw [Subgroup.coe_comap]
  exact (GlobalTheory.AdelicU.isOpen_levelOpen _ _ _).preimage ((continuous_mul_const _).comp (continuous_const_mul _))

theorem conj_mem_KAt {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D} (C : Cut D n v) {k : G D n}
    (hk : k ∈ lev nb C.s) (hkv : k ∈ atPts D.sp.cm.sig (Jst D n) {v}) {x : hermA D n} (hx : x ∈ C.s) :
    (nb x)⁻¹ * k * nb x ∈ KAt D n v := by
  have h1 := Subgroup.mem_iInf.1 hk ⟨x, hx⟩
  rw [Subgroup.mem_comap] at h1
  have hat := nb_mem_atPts hnb v (C.inf x hx) (C.off x hx)
  refine mem_KAt_of ?_ (mul_mem (mul_mem (inv_mem hat) hkv) hat)
  simpa [MulAut.conj_apply] using h1

end PositivityTheory.Rg.Rsw.L.LCutLow

end
