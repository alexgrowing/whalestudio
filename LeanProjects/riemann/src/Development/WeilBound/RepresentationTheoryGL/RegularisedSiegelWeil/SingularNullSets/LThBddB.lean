import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactLevelOffFinEmpty

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LThBdd

variable {D : D7} {n : ℕ}

theorem map_upper_unipotent_block {R : Type} [CommRing R] (f : AE D →+* R) (b : Mx D n n) :
    (blk4 (1 : Mx D n n) b 0 1).map f = blk4 1 (b.map f) 0 1 := by
  simp only [blk4, ← Matrix.submatrix_map, Matrix.fromBlocks_map, Matrix.map_one _ f.map_zero f.map_one,
    Matrix.map_zero _ f.map_zero]

theorem val_bc_matHom {R : Type} [CommRing R] (f : AE D →+* R) (g : G D n) :
    ((Formalism.UG.bc f (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig (Jst D n) g) : GL (Fin (n + n)) R) : Matrix (Fin (n + n)) (Fin (n + n)) R) =
      (mat g).map f := rfl

theorem proj_eq_one_iff {v : Pl D} {g : G D n} :
    GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g = 1 ↔ (mat g).map (cv D v) = 1 := by
  rw [← (matHom_injective _ D.sp.cm.sig (Jst D n)).eq_iff, matHom_proj, map_one]
  constructor
  · intro h
    have := congrArg Units.val h
    rwa [val_bc_matHom, Units.val_one] at this
  · intro h
    apply Units.ext
    rw [val_bc_matHom, Units.val_one]
    exact h

theorem projArch_eq_one_iff {w : InfinitePlace D.host.F} {g : G D n} :
    projArch D.sp.cm.sig (Jst D n) w g = 1 ↔ (mat g).map (compInf D.host.F D.host.E w) = 1 := by
  rw [← (matHom_injective _ D.sp.cm.sig (Jst D n)).eq_iff, matHom_projArch, map_one]
  constructor
  · intro h
    have := congrArg Units.val h
    rwa [val_bc_matHom, Units.val_one] at this
  · intro h
    apply Units.ext
    rw [val_bc_matHom, Units.val_one]
    exact h

theorem nb_mem_atPts {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D} (x : hermA D n)
    (hinf : ∀ w i j, compInf D.host.F D.host.E w (x.1 i j) = 0) (hoff : ∀ v' ≠ v, ∀ i j, cv D v' (x.1 i j) = 0) :
    nb x ∈ atPts D.sp.cm.sig (Jst D n) {v} := by
  rw [mem_atPts, mem_finPts_iff_forall]
  refine ⟨fun w => ?_, fun u hu => ?_⟩
  · rw [projArch_eq_one_iff, hnb x, map_upper_unipotent_block]
    have : x.1.map (compInf D.host.F D.host.E w) = 0 := by
      ext i j; exact hinf w i j
    rw [this]; exact GlobalTheory.StdUnn.Model.block_matrix_one
  · rw [proj_eq_one_iff, hnb x, map_upper_unipotent_block]
    have : x.1.map (cv D u) = 0 := by
      ext i j; exact hoff u (by simpa using hu) i j
    rw [this]; exact GlobalTheory.StdUnn.Model.block_matrix_one

theorem commute_of_atPts {v : Pl D} {a g : G D n} (ha : a ∈ atPts D.sp.cm.sig (Jst D n) {v})
    (hg : GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g = 1) : a * g = g * a := by
  rw [mem_atPts, mem_finPts_iff_forall] at ha
  apply GAd_ext
  · intro w; simp [map_mul, ha.1 w]
  · intro u
    by_cases h : u = v
    · subst h; simp [hg]
    · simp [ha.2 u (by simpa using h)]

theorem mulVec_mem_iff {A : Type} [CommRing A] {ι : Type} [Fintype ι] [DecidableEq ι] (R : Subring A)
    {M M' : Matrix ι ι A} (hM : ∀ i j, M i j ∈ R) (hM' : ∀ i j, M' i j ∈ R) (h : M' * M = 1) (y : ι → A) :
    (∀ i, y i ∈ R) ↔ ∀ i, (M *ᵥ y) i ∈ R := by
  have key : ∀ N : Matrix ι ι A, (∀ i j, N i j ∈ R) → ∀ z : ι → A, (∀ i, z i ∈ R) → ∀ i, (N *ᵥ z) i ∈ R :=
    fun N hN z hz i => by
      simp only [Matrix.mulVec, dotProduct]
      exact Subring.sum_mem _ fun j _ => R.mul_mem (hN i j) (hz j)
  refine ⟨key M hM y, fun hy => ?_⟩
  have : y = M' *ᵥ (M *ᵥ y) := by rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
  rw [this]; exact key M' hM' _ hy

theorem block_matrix_entry_property {A : Type} (p : A → Prop) {a b c d : Matrix (Fin n) (Fin n) A}
    (ha : ∀ i j, p (a i j)) (hb : ∀ i j, p (b i j)) (hc : ∀ i j, p (c i j)) (hd : ∀ i j, p (d i j)) :
    ∀ i j, p (blk4 a b c d i j) := by
  intro i j
  simp only [blk4, Matrix.submatrix_apply]
  generalize finSumFinEquiv.symm i = x
  generalize finSumFinEquiv.symm j = y
  rcases x with x | x <;> rcases y with y | y
  · exact ha x y
  · exact hb x y
  · exact hc x y
  · exact hd x y

theorem mem_K_of_atPts {v : Pl D} {g : G D n} (hg : g ∈ atPts D.sp.cm.sig (Jst D n) {v})
    (hv : GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g ∈ stabLoc D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) v) :
    g ∈ K D n := by
  rw [mem_atPts, mem_finPts_iff_forall] at hg
  unfold GlobalTheory.StdUnn.K levelAll
  refine Subgroup.mem_inf.2 ⟨mem_levelOpen.2 fun u => ?_, Subgroup.mem_iInf.2 fun w => ?_⟩
  · by_cases h : u = v
    · subst h; exact hv
    · rw [hg.2 u (by simpa using h)]; exact one_mem _
  · rw [Subgroup.mem_comap, hg.1 w]; exact one_mem _

theorem stab_of_entries {v : Pl D} (g : G D n) (hM : ∀ i j, cv D v (mat g i j) ∈ intLoc D.host.F D.host.E v)
    (hM' : ∀ i j, cv D v (mat g⁻¹ i j) ∈ intLoc D.host.F D.host.E v) :
    GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g ∈ stabLoc D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) v := by
  have e : ∀ (h : G D n) i j, (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig (Jst D n) (GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v h)).1 i j =
      cv D v (mat h i j) := fun h i j => by rw [matHom_proj]; rfl
  rw [mem_stabLoc]
  intro y
  rw [mem_latLoc_stdLattice, mem_latLoc_stdLattice]
  refine mulVec_mem_iff _
    (M' := (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig (Jst D n) (GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g⁻¹)).1)
    (fun i j => by rw [e]; exact hM i j) (fun i j => by rw [e]; exact hM' i j) ?_ y
  rw [← Units.val_mul, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, Units.val_one]

theorem mat_inj {g h : G D n} (e : mat g = mat h) : g = h := Subtype.ext (Units.ext e)

theorem nb_neg_mul {nb : hermA D n → G D n} (hnb : IsNMap nb) (o : hermA D n) : nb (-o) * nb o = 1 := by
  apply mat_inj
  show mat (nb (-o)) * mat (nb o) = mat 1
  rw [hnb, hnb, GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul]
  simp only [AddSubgroup.coe_neg, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    neg_add_cancel, add_neg_cancel]
  rw [GlobalTheory.StdUnn.Model.block_matrix_one]
  rfl

theorem nb_mem_KAt {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D} (o : hermA D n) (ho : IntAt v o) :
    nb o ∈ KAt D n v := by
  have ha := nb_mem_atPts hnb o ho.1 ho.2.1
  have h1 : ∀ i j, cv D v ((1 : Mx D n n) i j) ∈ intLoc D.host.F D.host.E v := fun i j => by
    rw [Matrix.one_apply]
    split_ifs
    · rw [map_one]; exact one_mem _
    · rw [map_zero]; exact zero_mem _
  have h0 : ∀ i j, cv D v ((0 : Mx D n n) i j) ∈ intLoc D.host.F D.host.E v := fun i j => by
    rw [Matrix.zero_apply, map_zero]; exact zero_mem _
  have hinv : (nb o)⁻¹ = nb (-o) := (eq_inv_of_mul_eq_one_left (nb_neg_mul hnb o)).symm
  have hst := stab_of_entries (v := v) (nb o)
    (by rw [hnb o]; exact block_matrix_entry_property (fun a => cv D v a ∈ intLoc D.host.F D.host.E v) h1 ho.2.2 h0 h1)
    (by
      rw [hinv, hnb (-o)]
      exact block_matrix_entry_property (fun a => cv D v a ∈ intLoc D.host.F D.host.E v) h1
        (fun i j => by rw [AddSubgroup.coe_neg, Matrix.neg_apply, map_neg]; exact neg_mem (ho.2.2 i j)) h0 h1)
  exact Subgroup.mem_inf.2 ⟨mem_K_of_atPts ha hst, ha⟩

def cjv (nb : hermA D n → G D n) (v : Pl D) (x : hermA D n) : G D n →* GLoc D.sp.cm.sig (Jst D n) v :=
  (GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v).comp (MulAut.conj (nb x)⁻¹).toMonoidHom

theorem cjv_apply (nb : hermA D n → G D n) (v : Pl D) (x : hermA D n) (k : G D n) :
    cjv nb v x k = GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v ((nb x)⁻¹ * k * nb x) := by
  simp [cjv, MulAut.conj_apply]

def Ucut (nb : hermA D n → G D n) (v : Pl D) (s : Finset (hermA D n)) : Subgroup (G D n) where
  carrier := {k | ∀ x ∈ s, cjv nb v x k ∈ stabLoc D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) v}
  one_mem' := fun x _ => by rw [map_one]; exact one_mem _
  mul_mem' := fun ha hb x hx => by rw [map_mul]; exact mul_mem (ha x hx) (hb x hx)
  inv_mem' := fun ha x hx => by rw [map_inv]; exact inv_mem (ha x hx)

theorem mem_Ucut {nb : hermA D n → G D n} {v : Pl D} {s : Finset (hermA D n)} {k : G D n} :
    k ∈ Ucut nb v s ↔ ∀ x ∈ s, GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v ((nb x)⁻¹ * k * nb x) ∈
      stabLoc D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) v := by
  show (∀ x ∈ s, _) ↔ _
  simp only [cjv_apply]

theorem isOpen_Ucut (nb : hermA D n → G D n) (v : Pl D) (s : Finset (hermA D n)) :
    IsOpen (Ucut nb v s : Set (G D n)) := by
  have : (Ucut nb v s : Set (G D n)) = ⋂ x ∈ s, (fun k => GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v ((nb x)⁻¹ * k * nb x)) ⁻¹'
      (stabLoc D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) v : Set _) := by
    ext k
    simp only [SetLike.mem_coe, mem_Ucut, Set.mem_iInter, Set.mem_preimage]
  rw [this]
  haveI : Submodule.IsLattice D.host.E (stdLattice D.host.E (n + n)) := isLattice_stdLattice
  exact isOpen_biInter_finset fun x _ => (isOpen_stabLoc _ _ _ v).preimage
    ((continuous_proj _ _ v).comp ((continuous_const.mul continuous_id).mul continuous_const))

theorem mem_Ucut_of_proj {nb : hermA D n → G D n} {v : Pl D} {s : Finset (hermA D n)} {k k' : G D n}
    (h : GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v k = GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v k')
    (hk : k ∈ Ucut nb v s) : k' ∈ Ucut nb v s := by
  rw [mem_Ucut] at hk ⊢
  intro x hx
  have := hk x hx
  rwa [map_mul, map_mul, h, ← map_mul, ← map_mul] at this

theorem conj_mem_KAt {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D} (C : Cut D n v) {k : G D n}
    (hk : k ∈ Ucut nb v C.s) (hkv : k ∈ atPts D.sp.cm.sig (Jst D n) {v}) {x : hermA D n} (hx : x ∈ C.s) :
    (nb x)⁻¹ * k * nb x ∈ KAt D n v := by
  have ha := nb_mem_atPts hnb x (C.inf x hx) (C.off x hx)
  have hm : (nb x)⁻¹ * k * nb x ∈ atPts D.sp.cm.sig (Jst D n) {v} := mul_mem (mul_mem (inv_mem ha) hkv) ha
  exact Subgroup.mem_inf.2 ⟨mem_K_of_atPts hm ((mem_Ucut.1 hk) x hx), hm⟩

def locPart (v : Pl D) (g : G D n) : G D n :=
  emb D.sp.cm.sig (Jst D n) v (GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g)

theorem locPart_mem_atPts (v : Pl D) (g : G D n) : locPart v g ∈ atPts D.sp.cm.sig (Jst D n) {v} := by
  rw [mem_atPts, mem_finPts]
  exact ⟨by simp [locPart], fun u hu => proj_emb_ne _ _ (by simpa using hu) _⟩

theorem proj_locPart (v : Pl D) (g : G D n) :
    GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v (locPart v g) = GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g :=
  proj_emb_self _ _ _ _

theorem continuous_locPart (v : Pl D) : Continuous (locPart (n := n) v) :=
  (continuous_emb _ _ v).comp (continuous_proj _ _ v)

end PositivityTheory.Rg.Rsw.L.LThBdd

end
