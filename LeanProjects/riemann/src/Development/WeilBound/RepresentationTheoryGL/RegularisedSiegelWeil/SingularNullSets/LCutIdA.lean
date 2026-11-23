import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierBesselBasePointIsUnfoldingBasePointSpec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LCutId

open GlobalTheory.StdUnn.Model

variable {D : D7} {n : ℕ}

theorem repr_map' {F E R R' ι : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing R']
    [Algebra F R'] (φ : R →ₐ[F] R') (b : Module.Basis ι F E) (z : R ⊗[F] E) (k : ι) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) z) k =
      φ ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul a e => simp [Algebra.TensorProduct.basis_repr_tmul]

theorem ae_ext (z z' : AE D) (hi : ∀ w, compInf D.host.F D.host.E w z = compInf D.host.F D.host.E w z')
    (hf : ∀ v, cv D v z = cv D v z') : z = z' := by
  let b := Module.Basis.ofVectorSpace D.host.F D.host.E
  apply (Algebra.TensorProduct.basis (AF D.host.F) b).repr.injective
  refine Finsupp.ext fun k => Prod.ext ?_ ?_
  · funext w
    have h1 := repr_map' (evInf D.host.F w) b z k
    have h2 := repr_map' (evInf D.host.F w) b z' k
    have h : Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) z =
        Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) z' := hi w
    rw [h, h2] at h1
    exact h1.symm
  · refine FiniteAdeleRing.ext _ fun v => ?_
    have h1 := repr_map' (evFin D.host.F v) b z k
    have h2 := repr_map' (evFin D.host.F v) b z' k
    have h : Algebra.TensorProduct.map (evFin D.host.F v) (AlgHom.id D.host.F D.host.E) z =
        Algebra.TensorProduct.map (evFin D.host.F v) (AlgHom.id D.host.F D.host.E) z' := hf v
    rw [h, h2] at h1
    exact h1.symm

theorem fst_zero (z : AE D) (h : ∀ w, compInf D.host.F D.host.E w z = 0) :
    Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) z = 0 := by
  let b := Module.Basis.ofVectorSpace D.host.F D.host.E
  have hk : ∀ k, ((Algebra.TensorProduct.basis (AF D.host.F) b).repr z k).1 = 0 := fun k => by
    funext w
    have h1 := repr_map' (evInf D.host.F w) b z k
    have h2 : Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) z = 0 := h w
    rw [h2, LinearEquiv.map_zero, Finsupp.zero_apply] at h1
    exact h1.symm
  apply (Algebra.TensorProduct.basis (Ainf D.host.F) b).repr.injective
  refine Finsupp.ext fun k => ?_
  rw [repr_map', LinearEquiv.map_zero, Finsupp.zero_apply]
  exact hk k

theorem block_matrix_map_ringHom {R S : Type} [Semiring R] [Semiring S] (φ : R →+* S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d).map φ = blk4 (a.map φ) (b.map φ) (c.map φ) (d.map φ) := by
  ext i j
  simp only [blk4, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> rfl

theorem unipotent_block_mem_subring {S : Type} [Ring S] (T : Subring S) (Y : Matrix (Fin n) (Fin n) S) (hY : ∀ i j, Y i j ∈ T) (i j : Fin (n + n)) :
    blk4 1 Y 0 1 i j ∈ T := by
  simp only [blk4, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j
  · rw [Matrix.fromBlocks_apply₁₁, Matrix.one_apply]; split_ifs; exacts [T.one_mem, T.zero_mem]
  · rw [Matrix.fromBlocks_apply₁₂]; exact hY i j
  · rw [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]; exact T.zero_mem
  · rw [Matrix.fromBlocks_apply₂₂, Matrix.one_apply]; split_ifs; exacts [T.one_mem, T.zero_mem]

theorem mat_nb_map {nb : hermA D n → G D n} (hnb : IsNMap nb) {S : Type} [CommRing S] (φ : AE D →+* S) (y : hermA D n) :
    (mat (nb y)).map φ = blk4 1 (y.1.map φ) 0 1 := by
  rw [hnb y, block_matrix_map_ringHom, Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.map_zero _ (map_zero φ)]

theorem mat_nb_map_one {nb : hermA D n → G D n} (hnb : IsNMap nb) {S : Type} [CommRing S] (φ : AE D →+* S) (y : hermA D n)
    (h : ∀ i j, φ (y.1 i j) = 0) : (mat (nb y)).map φ = 1 := by
  rw [mat_nb_map hnb, show y.1.map φ = 0 from Matrix.ext fun i j => h i j, block_matrix_one]

theorem map_comm {m : ℕ} {S : Type} [CommRing S] (φ : AE D →+* S) (A B : Mx D m m) (h : A.map φ = 1 ∨ B.map φ = 1) :
    (A * B).map φ = (B * A).map φ := by
  rw [Matrix.map_mul, Matrix.map_mul]
  rcases h with h | h <;> rw [h, one_mul, mul_one]

theorem nb_comm {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D} {y : hermA D n}
    (hi : ∀ w i j, compInf D.host.F D.host.E w (y.1 i j) = 0) (ho : ∀ v' ≠ v, ∀ i j, cv D v' (y.1 i j) = 0)
    {g : G D n} (hg : proj D.sp.cm.sig (Jst D n) v g = 1) : nb y * g = g * nb y := by
  apply GlobalTheory.CompanionTheory.FourierN.mat_injective
  show mat (nb y) * mat g = mat g * mat (nb y)
  have hgv : (mat g).map (cv D v) = 1 := by
    have e := congrArg (fun k => (GlobalTheory.AdelicU.matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n) k).1) hg
    simp only [map_one, Units.val_one] at e
    exact e
  have key : ∀ {S : Type} [CommRing S] (φ : AE D →+* S), (mat (nb y)).map φ = 1 ∨ (mat g).map φ = 1 →
      ∀ i j, φ ((mat (nb y) * mat g) i j) = φ ((mat g * mat (nb y)) i j) := by
    intro S _ φ h i j
    have e := map_comm φ (mat (nb y)) (mat g) h
    exact congrFun (congrFun e i) j
  ext i j
  refine ae_ext _ _ (fun w => key _ (Or.inl (mat_nb_map_one hnb _ y fun a b => hi w a b)) i j) (fun v' => ?_)
  by_cases hv : v' = v
  · subst hv
    exact key _ (Or.inr hgv) i j
  · exact key _ (Or.inl (mat_nb_map_one hnb _ y fun a b => ho v' hv a b)) i j

theorem stab_of_int (v : Pl D) (k : GLoc D.sp.cm.sig (Jst D n) v)
    (hM : ∀ i j, (GlobalTheory.AdelicU.matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n) k).1 i j ∈ intLoc D.host.F D.host.E v)
    (hM' : ∀ i j, ((GlobalTheory.AdelicU.matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n) k)⁻¹).1 i j ∈ intLoc D.host.F D.host.E v) :
    k ∈ stabLoc D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) v := by
  set M := GlobalTheory.AdelicU.matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n) k
  have hint : ∀ (N : Matrix (Fin (n + n)) (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)),
      (∀ i j, N i j ∈ intLoc D.host.F D.host.E v) → ∀ z : Fin (n + n) → Fv D.host.F v ⊗[D.host.F] D.host.E,
      (∀ i, z i ∈ intLoc D.host.F D.host.E v) → ∀ i, (N *ᵥ z) i ∈ intLoc D.host.F D.host.E v :=
    fun N hN z hz i => by
      simp only [Matrix.mulVec, dotProduct]
      exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hN i j) (hz j)
  refine GlobalTheory.AdelicU.mem_stabLoc.2 fun z => ?_
  simp only [GlobalTheory.AdelicU.mem_latLoc_stdLattice]
  refine ⟨fun hz => hint _ hM z hz, fun hz => ?_⟩
  have e : (M⁻¹).1 *ᵥ (M.1 *ᵥ z) = z := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rw [← e]
  exact hint _ hM' _ hz

set_option maxHeartbeats 800000 in

theorem nb_mem_KAt {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D} {y : hermA D n} (hy : IntAt v y) :
    nb y ∈ KAt D n v := by
  obtain ⟨hi, ho, hint⟩ := hy
  have hcv : ∀ (v' : Pl D) i j, cv D v' (y.1 i j) ∈ intLoc D.host.F D.host.E v' := by
    intro v' i j
    by_cases hv : v' = v
    · subst hv; exact hint i j
    · rw [ho v' hv i j]; exact zero_mem _
  have hinv : (nb y)⁻¹ = nb (-y) := by
    rw [inv_eq_iff_mul_eq_one, ← GlobalTheory.CompanionTheory.FourierN.nb_add hnb, add_neg_cancel, GlobalTheory.CompanionTheory.FourierN.nb_zero hnb]
  have hstab : ∀ v' : Pl D, proj D.sp.cm.sig (Jst D n) v' (nb y) ∈
      stabLoc D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) v' := by
    intro v'
    refine stab_of_int v' _ (fun i j => ?_) (fun i j => ?_)
    · change ((mat (nb y)).map (cv D v')) i j ∈ _
      rw [mat_nb_map hnb]
      exact unipotent_block_mem_subring _ _ (fun a b => hcv v' a b) i j
    · rw [← map_inv, ← map_inv, hinv]
      change ((mat (nb (-y))).map (cv D v')) i j ∈ _
      rw [mat_nb_map hnb]
      refine unipotent_block_mem_subring _ _ (fun a b => ?_) i j
      show cv D v' ((-y).1 a b) ∈ _
      rw [show (-y).1 a b = -(y.1 a b) from rfl, RingHom.map_neg]
      exact neg_mem (hcv v' a b)
  have harch : ∀ w, projArch D.sp.cm.sig (Jst D n) w (nb y) = 1 := fun w =>
    Subtype.ext (Units.ext (mat_nb_map_one hnb _ y fun a b => hi w a b))
  have hoff : ∀ v' ≠ v, proj D.sp.cm.sig (Jst D n) v' (nb y) = 1 := fun v' hv =>
    Subtype.ext (Units.ext (mat_nb_map_one hnb _ y fun a b => ho v' hv a b))
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · show nb y ∈ levelAll D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) 1
    refine Subgroup.mem_inf.2 ⟨mem_levelOpen.2 hstab, Subgroup.mem_iInf.2 fun w => ?_⟩
    rw [Subgroup.mem_comap, harch w]
    exact one_mem _
  · refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · show nb y ∈ MonoidHom.ker _
      rw [MonoidHom.mem_ker]
      have e := mat_nb_map_one hnb (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom y
        fun a b => fst_zero _ fun w => hi w a b
      apply Units.ext
      rw [MonoidHom.comp_apply, Formalism.UG.bc, Units.coe_map, Units.val_one]
      exact e
    · refine Subgroup.mem_iInf.2 fun v' => Subgroup.mem_iInf.2 fun hv' => ?_
      rw [MonoidHom.mem_ker]
      exact hoff v' fun h => hv' (Finset.mem_singleton.2 h)

end PositivityTheory.Rg.Rsw.L.LCutId

end
