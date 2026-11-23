import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.OrdinaryIdealSaturatorsConjInvariantStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.NilpotentTwistStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.IsUnitCharacterDiffAtChosenInertiaStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ExistsGLConjEqDiagonalOfCharpolyEqProdStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.GaloisSubgroupLBasicPropertiesStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.TripleProductStableFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.UpperTriRepMulApplyZeroOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IqBasic

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc

theorem conjBy_right_eq {G C : Type} [Group G] [CommRing C] (h : GL (Fin 3) C) (r : G →* GG 3 C) (g : G) :
    (conjBy h r g).right = (r g).right := by
  simp [conjBy, MulAut.conj_apply]

theorem conjBy_left_eq {G C : Type} [Group G] [CommRing C] (h : GL (Fin 3) C) (r : G →* GG 3 C) (g : G)
    (hg : (r g).right = 1) : (conjBy h r g).left = h * (r g).left * h⁻¹ := by
  simp [conjBy, GG.ofGL, SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.inv_left, SemidirectProduct.inv_right, hg]

end GlobalTheory.OrdLoc

private theorem fin_eq_eI_or_wI_or_esI {C : Type} [CommRing C] (p q : Fin 3 → C)
    (hp : ∀ a b, a ≠ b → IsUnit (p a - p b)) (N : Matrix (Fin 3) (Fin 3) C)
    (h0 : (N - Matrix.scalar (Fin 3) (q 0)) * (Matrix.diagonal p - Matrix.scalar (Fin 3) (p 1)) *
      (Matrix.diagonal p - Matrix.scalar (Fin 3) (p 2)) = 0)
    (h1 : (Matrix.diagonal p - Matrix.scalar (Fin 3) (p 0)) * (N - Matrix.scalar (Fin 3) (q 1)) *
      (Matrix.diagonal p - Matrix.scalar (Fin 3) (p 2)) = 0)
    (h2 : (Matrix.diagonal p - Matrix.scalar (Fin 3) (p 0)) * (Matrix.diagonal p - Matrix.scalar (Fin 3) (p 1)) *
      (N - Matrix.scalar (Fin 3) (q 2)) = 0) :
    N 1 0 = 0 ∧ N 2 0 = 0 ∧ N 2 1 = 0 ∧ N 0 0 = q 0 ∧ N 1 1 = q 1 ∧ N 2 2 = q 2 := by
  have e : ∀ c, Matrix.diagonal p - Matrix.scalar (Fin 3) c = Matrix.diagonal (fun i => p i - c) := by
    intro c
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.diagonal_apply_ne _ hij]
  simp only [e] at h0 h1 h2
  have u01 := hp 0 1 (by decide)
  have u02 := hp 0 2 (by decide)
  have u10 := hp 1 0 (by decide)
  have u12 := hp 1 2 (by decide)
  have u20 := hp 2 0 (by decide)
  have u21 := hp 2 1 (by decide)
  have a10 := congrFun (congrFun h0 1) 0
  have a20 := congrFun (congrFun h0 2) 0
  have a00 := congrFun (congrFun h0 0) 0
  have b21 := congrFun (congrFun h1 2) 1
  have b11 := congrFun (congrFun h1 1) 1
  have c22 := congrFun (congrFun h2 2) 2
  simp [Matrix.mul_diagonal, Matrix.diagonal_mul] at a10 a20 a00 b21 b11 c22
  have k : ∀ {x a b : C}, IsUnit a → IsUnit b → x * a * b = 0 → x = 0 := by
    intro x a b ha hb h
    rw [mul_assoc] at h
    exact (ha.mul hb).mul_left_eq_zero.mp h
  rw [mul_comm (p 2 - p 0)] at b21
  rw [mul_comm (p 1 - p 0)] at b11
  rw [mul_comm] at c22
  refine ⟨k u01 u02 a10, k u01 u02 a20, k u20 u12 b21, sub_eq_zero.mp (k u01 u02 a00),
    sub_eq_zero.mp (k u10 u12 b11), sub_eq_zero.mp ((u20.mul u21).mul_left_eq_zero.mp c22)⟩

private theorem exists_isUnit_det_apply_eq_sum_of_mem_Nof {C : Type} [CommRing C] (p : Fin 3 → C)
    (hp : ∀ a b, a ≠ b → IsUnit (p a - p b)) (M T : Matrix (Fin 3) (Fin 3) C)
    (hT : T 1 0 = 0 ∧ T 2 0 = 0 ∧ T 2 1 = 0 ∧ T 0 0 = p 0 ∧ T 1 1 = p 1 ∧ T 2 2 = p 2)
    (h : T * M = M * Matrix.diagonal p) : M 1 0 = 0 ∧ M 2 0 = 0 ∧ M 2 1 = 0 := by
  obtain ⟨t10, t20, t21, t00, t11, t22⟩ := hT
  have e20 := congrFun (congrFun h 2) 0
  have e10 := congrFun (congrFun h 1) 0
  have e21 := congrFun (congrFun h 2) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mul_diagonal, t10, t20, t21, t00, t11, t22] at e20 e10 e21
  have m20 : M 2 0 = 0 := by
    have : (p 2 - p 0) * M 2 0 = 0 := by linear_combination e20
    exact (hp 2 0 (by decide)).mul_right_eq_zero.mp this
  have m10 : M 1 0 = 0 := by
    have : (p 1 - p 0) * M 1 0 = 0 := by linear_combination e10 - T 1 2 * m20
    exact (hp 1 0 (by decide)).mul_right_eq_zero.mp this
  have m21 : M 2 1 = 0 := by
    have : (p 2 - p 1) * M 2 1 = 0 := by linear_combination e21
    exact (hp 2 1 (by decide)).mul_right_eq_zero.mp this
  exact ⟨m10, m20, m21⟩

private theorem upperTriangular_fin_three_mul_entries {C : Type} [CommRing C] (A B : Matrix (Fin 3) (Fin 3) C)
    (hA : A 1 0 = 0 ∧ A 2 0 = 0 ∧ A 2 1 = 0) (hB : B 1 0 = 0 ∧ B 2 0 = 0 ∧ B 2 1 = 0) :
    (∀ i, (A * B) i i = A i i * B i i) ∧ (A * B) 0 1 = A 0 0 * B 0 1 + A 0 1 * B 1 1 ∧
      (A * B) 1 2 = A 1 1 * B 1 2 + A 1 2 * B 2 2 ∧
      (A * B) 0 2 = A 0 0 * B 0 2 + A 0 1 * B 1 2 + A 0 2 * B 2 2 := by
  obtain ⟨a10, a20, a21⟩ := hA
  obtain ⟨b10, b20, b21⟩ := hB
  refine ⟨fun i => ?_, ?_, ?_, ?_⟩
  · fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_three, a10, a20, a21, b10, b20, b21]
  · simp [Matrix.mul_apply, Fin.sum_univ_three, a10, a20, a21, b10, b20, b21]
  · simp [Matrix.mul_apply, Fin.sum_univ_three, a10, a20, a21, b10, b20, b21]
  · simp [Matrix.mul_apply, Fin.sum_univ_three, a10, a20, a21, b10, b20, b21]

open GlobalTheory.OrdLoc in

theorem GlobalTheory.OrdLoc.triangular_of_ordIdeal_eq_bot : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [IsLocalRing B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] (r : GQ l →* GG 3 B), HasMult D.η r → (∀ a b, QCont l fun g => (r g).mat a b) → GlobalTheory.OrdLoc.ordIdeal D r = ⊥ → ∃ (h : GL (Fin 3) B) (ρ : ↥D.HL →* GL (Fin 3) B) (κ : Fin 3 → ↥D.HL →* Bˣ) (x y z : ↥D.HL → B), (∀ g, ρ g = (conjBy h r g).left) ∧ (∀ i, Continuous fun g => (κ i g : B)) ∧ (∀ g : ↥D.HL, (g : GQ l) ∈ Iq l → ∀ i, κ i g = cycA l l B (g : GQ l) ^ ((D.e : ℤ) * wt1 i)) ∧ Continuous z ∧ (∀ g, (ρ g : Matrix (Fin 3) (Fin 3) B) = triM (fun i => κ i g) (x g) (y g) (z g)) ∧ x ∈ Z1 (chRep (κ 0 / κ 1)) ∧ y ∈ Z1 (chRep (κ 1 / κ 2)) ∧ ∀ hσ : GlobalTheory.OrdLoc.fr D ∈ D.HL, (∃ v : Bˣ, GlobalTheory.OrdLoc.dd D r 0 = v * (((κ 0 / κ 1) ⟨_, hσ⟩ : Bˣ) - (cycA l l B (GlobalTheory.OrdLoc.fr D) : B))) ∧ ∃ v : Bˣ, GlobalTheory.OrdLoc.dd D r 1 = v * (((κ 1 / κ 2) ⟨_, hσ⟩ : Bˣ) - (cycA l l B (GlobalTheory.OrdLoc.fr D) : B)) := by
  intro l _ O _ _ _ _ _ _ _ D B _ _ _ _ _ _ _ _ _ _ _ r hmult hcont hbot
  obtain ⟨hHLn, -, -, hPsi, hS0⟩ := GlobalTheory.T.galoisSubgroupL_basic_properties D
  obtain ⟨hsHL, hsIq, -⟩ := hS0
  obtain ⟨hpu, hcc⟩ := GlobalTheory.T.isUnit_characterDiff_at_chosenInertia D B
  set p : Fin 3 → B := fun a => algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a D.s0) with hp_def
  have hchar : (r D.s0).mat.charpoly = ∏ a : Fin 3, (X - Polynomial.C (p a)) := by
    rw [← sub_eq_zero]
    ext i
    have hm : ((r D.s0).mat.charpoly - ∏ a : Fin 3, (X - Polynomial.C (p a))).coeff i ∈
        GlobalTheory.OrdLoc.ordIdeal D r :=
      Ideal.subset_span (Set.mem_union_left _ ⟨D.s0, ⟨hsHL, hsIq⟩, i, rfl⟩)
    rw [hbot, Ideal.mem_bot] at hm
    simpa using hm
  obtain ⟨h, hh⟩ := GlobalTheory.T.diagonalize_of_distinct_eigenvalues (r D.s0).mat p hpu hchar
  have hright : ∀ g ∈ D.HL, (r g).right = 1 := by
    intro g hg
    rw [hmult g]
    have := (Subgroup.mem_inf.mp hg).1
    simpa using this
  set r' := conjBy h r with hr'_def
  have hright' : ∀ g ∈ D.HL, (r' g).right = 1 := by
    intro g hg
    rw [hr'_def, GlobalTheory.OrdLoc.conjBy_right_eq]
    exact hright g hg
  have hmat : ∀ g ∈ D.HL, (r' g).mat = (h : Matrix (Fin 3) (Fin 3) B) * (r g).mat * ((h⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B) :=
    fun g hg => GlobalTheory.OrdLoc.conjBy_mat h r g (hright g hg)
  have hs0' : (r' D.s0).mat = Matrix.diagonal p := by rw [hmat _ hsHL, hh]
  have hbot' : GlobalTheory.OrdLoc.ordIdeal D r' = ⊥ := by rw [(GlobalTheory.T.ordinaryIdeal_saturators_conj_invariant D r h hmult).1, hbot]
  have hsh : ∀ s : Fin 3 → GQ l, (∀ a, s a ∈ D.HL ⊓ Iq l) →
      D.sh r' 0 (s 0) * D.sh r' 1 (s 1) * D.sh r' 2 (s 2) = 0 := by
    intro s hs
    ext i j
    have hm : (D.sh r' 0 (s 0) * D.sh r' 1 (s 1) * D.sh r' 2 (s 2)) i j ∈ GlobalTheory.OrdLoc.ordIdeal D r' :=
      Ideal.subset_span (Set.mem_union_right _ ⟨s, hs, i, j, rfl⟩)
    rw [hbot', Ideal.mem_bot] at hm
    simpa using hm
  have hs0I : D.s0 ∈ D.HL ⊓ Iq l := ⟨hsHL, hsIq⟩
  have htriI : ∀ t ∈ D.HL ⊓ Iq l, (r' t).mat 1 0 = 0 ∧ (r' t).mat 2 0 = 0 ∧ (r' t).mat 2 1 = 0 ∧
      (r' t).mat 0 0 = algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ 0 t) ∧
      (r' t).mat 1 1 = algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ 1 t) ∧
      (r' t).mat 2 2 = algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ 2 t) := by
    intro t ht
    apply fin_eq_eI_or_wI_or_esI p (fun a => algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a t)) hpu
    · have := hsh ![t, D.s0, D.s0] (by intro a; fin_cases a <;> simpa)
      simpa [UpperTheory.V.Loc.Dat3.sh, hs0'] using this
    · have := hsh ![D.s0, t, D.s0] (by intro a; fin_cases a <;> simpa)
      simpa [UpperTheory.V.Loc.Dat3.sh, hs0'] using this
    · have := hsh ![D.s0, D.s0, t] (by intro a; fin_cases a <;> simpa)
      simpa [UpperTheory.V.Loc.Dat3.sh, hs0'] using this
  have hmm : ∀ x y : GG 3 B, x.right = 1 → (x * y).mat = x.mat * y.mat := by
    intro x y hx
    simp [UpperTheory.V.U3.GG.mat, SemidirectProduct.mul_left, hx]
  have hpsiconj : ∀ g a, UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a (g * D.s0 * g⁻¹) = UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a D.s0 := by
    intro g a
    simp [UpperTheory.V.UnitaryThreeInertia.psi, mul_inv_cancel_comm]
  have htri : ∀ g ∈ D.HL, (r' g).mat 1 0 = 0 ∧ (r' g).mat 2 0 = 0 ∧ (r' g).mat 2 1 = 0 := by
    intro g hg
    have ht : g * D.s0 * g⁻¹ ∈ D.HL ⊓ Iq l :=
      ⟨hHLn.conj_mem _ hsHL g, (UpperTheory.V.Loc.iqBasic l).1.conj_mem _ hsIq g⟩
    obtain ⟨a, b, c, d, e, f⟩ := htriI _ ht
    apply exists_isUnit_det_apply_eq_sum_of_mem_Nof p hpu (r' g).mat (r' (g * D.s0 * g⁻¹)).mat
    · refine ⟨a, b, c, ?_, ?_, ?_⟩
      · rw [d, hpsiconj]
      · rw [e, hpsiconj]
      · rw [f, hpsiconj]
    · rw [← hs0', ← hmm _ _ (hright' _ ht.1), ← hmm _ _ (hright' _ hg), ← map_mul, ← map_mul]
      rw [show g * D.s0 * g⁻¹ * g = g * D.s0 by group]
  have hc : ∀ a b, Continuous fun g : GQ l => (r g).mat a b := by
    intro a b
    have := hcont a b
    unfold UpperTheory.V.Loc.QCont at this
    rwa [← eq_moduleTopology ℚ_[l] B] at this
  have hMc : ∀ i j, Continuous fun g : ↥D.HL => (r' (g : GQ l)).mat i j := by
    intro i j
    have e : (fun g : ↥D.HL => (r' (g : GQ l)).mat i j) = fun g : ↥D.HL =>
        ((h : Matrix (Fin 3) (Fin 3) B) * (r (g : GQ l)).mat *
          ((h⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B)) i j := by
      funext g
      rw [hmat g g.2]
    rw [e]
    have hr : Continuous fun g : GQ l => (r g).mat := continuous_matrix fun a b => hc a b
    exact ((continuous_const.matrix_mul (hr.comp continuous_subtype_val)).matrix_mul
      continuous_const).matrix_elem i j
  have hmulHL : ∀ a b : ↥D.HL, (r' ((a * b : ↥D.HL) : GQ l)).mat = (r' a).mat * (r' b).mat := by
    intro a b
    rw [Subgroup.coe_mul, map_mul, hmm _ _ (hright' _ a.2)]
  have hinv1 : ∀ a : ↥D.HL, (r' a).mat * (r' ((a⁻¹ : ↥D.HL) : GQ l)).mat = 1 := by
    intro a
    rw [← hmulHL, mul_inv_cancel]
    simp [UpperTheory.V.U3.GG.mat]
  have hdiag : ∀ (a b : ↥D.HL) i,
      (r' ((a * b : ↥D.HL) : GQ l)).mat i i = (r' a).mat i i * (r' b).mat i i := by
    intro a b i
    rw [hmulHL]
    exact (upperTriangular_fin_three_mul_entries _ _ (htri _ a.2) (htri _ b.2)).1 i
  have hunit : ∀ (a : ↥D.HL) i, (r' a).mat i i * (r' ((a⁻¹ : ↥D.HL) : GQ l)).mat i i = 1 := by
    intro a i
    rw [← (upperTriangular_fin_three_mul_entries _ _ (htri _ a.2) (htri _ (a⁻¹).2)).1 i, hinv1]
    simp
  have hunit' : ∀ (a : ↥D.HL) i, (r' ((a⁻¹ : ↥D.HL) : GQ l)).mat i i * (r' a).mat i i = 1 := by
    intro a i
    rw [mul_comm]
    exact hunit a i
  let κ : Fin 3 → ↥D.HL →* Bˣ := fun i => MonoidHom.mk'
    (fun g => ⟨(r' g).mat i i, (r' ((g⁻¹ : ↥D.HL) : GQ l)).mat i i, hunit g i, hunit' g i⟩)
    (fun a b => by
      ext
      simp only [Units.val_mul]
      exact hdiag a b i)
  let ρ : ↥D.HL →* GL (Fin 3) B := MonoidHom.mk' (fun g => (r' g).left) (fun a b => by
    rw [Subgroup.coe_mul, map_mul, SemidirectProduct.mul_left, hright' _ a.2, map_one]
    rfl)
  have hκ : ∀ i (g : ↥D.HL), ((κ i g : Bˣ) : B) = (r' g).mat i i := fun i g => rfl
  have hq : ∀ (i j : Fin 3) (a : ↥D.HL), (((κ i / κ j) a : Bˣ) : B) =
      (r' a).mat i i * (r' ((a⁻¹ : ↥D.HL) : GQ l)).mat j j := by
    intro i j a
    rw [MonoidHom.div_apply, div_eq_mul_inv, Units.val_mul]
    rfl
  have hcyc : ∀ s, Units.map (algebraMap O B : O →* B) (cycA l l O s) = cycA l l B s := by
    intro s
    ext
    simp [UpperTheory.V.Loc.cycA, ← IsScalarTower.algebraMap_apply]
  refine ⟨h, ρ, κ, fun g => (r' g).mat 0 1 * (r' ((g⁻¹ : ↥D.HL) : GQ l)).mat 1 1,
    fun g => (r' g).mat 1 2 * (r' ((g⁻¹ : ↥D.HL) : GQ l)).mat 2 2,
    fun g => (r' g).mat 0 2 * (r' ((g⁻¹ : ↥D.HL) : GQ l)).mat 2 2,
    fun g => rfl, fun i => hMc i i, ?_, (hMc 0 2).mul ((hMc 2 2).comp continuous_inv), ?_, ?_, ?_, ?_⟩
  · intro g hgI i
    obtain ⟨-, -, -, d0, d1, d2⟩ := htriI _ ⟨g.2, hgI⟩
    have key : ∀ i, algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ i g) =
        ((cycA l l B (g : GQ l) ^ ((D.e : ℤ) * wt1 i) : Bˣ) : B) := by
      intro i
      rw [UpperTheory.V.UnitaryThreeInertia.psi, hPsi _ g.2 hgI, ← hcyc, ← map_zpow, Units.coe_map, zpow_mul, zpow_natCast]
      rfl
    ext
    fin_cases i
    · exact d0.trans (key 0)
    · exact d1.trans (key 1)
    · exact d2.trans (key 2)
  · intro g
    obtain ⟨t10, t20, t21⟩ := htri _ g.2
    have u1 := hunit g 1
    have u2 := hunit g 2
    change (r' (g : GQ l)).mat = _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [UpperTheory.V.Loc.triM, hκ, t10, t20, t21] at u1 u2 ⊢
    all_goals first
      | linear_combination -(r' (g : GQ l)).mat 0 1 * u1
      | linear_combination -(r' (g : GQ l)).mat 0 2 * u2
      | linear_combination -(r' (g : GQ l)).mat 1 2 * u2
  · refine ⟨(hMc 0 1).mul ((hMc 1 1).comp continuous_inv), fun a b => ?_⟩
    dsimp only
    rw [UpperTheory.V.Loc.chRep_apply, hq, mul_inv_rev, hmulHL, hmulHL]
    obtain ⟨-, e01, -, -⟩ := upperTriangular_fin_three_mul_entries _ _ (htri _ a.2) (htri _ b.2)
    obtain ⟨dB, -, -, -⟩ := upperTriangular_fin_three_mul_entries _ _ (htri _ (b⁻¹).2) (htri _ (a⁻¹).2)
    rw [e01, dB 1]
    linear_combination ((r' a).mat 0 1 * (r' ((a⁻¹ : ↥D.HL) : GQ l)).mat 1 1) * hunit b 1
  · refine ⟨(hMc 1 2).mul ((hMc 2 2).comp continuous_inv), fun a b => ?_⟩
    dsimp only
    rw [UpperTheory.V.Loc.chRep_apply, hq, mul_inv_rev, hmulHL, hmulHL]
    obtain ⟨-, -, e12, -⟩ := upperTriangular_fin_three_mul_entries _ _ (htri _ a.2) (htri _ b.2)
    obtain ⟨dB, -, -, -⟩ := upperTriangular_fin_three_mul_entries _ _ (htri _ (b⁻¹).2) (htri _ (a⁻¹).2)
    rw [e12, dB 2]
    linear_combination ((r' a).mat 1 2 * (r' ((a⁻¹ : ↥D.HL) : GQ l)).mat 2 2) * hunit b 2
  · intro hσ
    have hdd : ∀ a, D.dd r a = D.dd r' a := fun a => ((GlobalTheory.T.ordinaryIdeal_saturators_conj_invariant D r h hmult).2.1 a).symm
    have hdiag' := GlobalTheory.T.ordinary_derivative_entry_formula D r' hs0'
    have hc' : algebraMap O B ((cycA l l O (GlobalTheory.OrdLoc.fr D) : Oˣ) : O) =
        ((cycA l l B (GlobalTheory.OrdLoc.fr D) : Bˣ) : B) := by
      rw [← hcyc]
      rfl
    have u1 := hunit ⟨_, hσ⟩ 1
    have u2 := hunit ⟨_, hσ⟩ 2
    refine ⟨⟨(hcc 0).unit * (hcc 1).unit * κ 1 ⟨_, hσ⟩, ?_⟩, ⟨(hcc 1).unit * (hcc 2).unit * κ 2 ⟨_, hσ⟩, ?_⟩⟩
    · rw [hdd, hdiag' 0, hq, Units.val_mul, Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec, hκ, ← hc']
      simp only [map_mul]
      have e01 : (0 : Fin 3) + 1 = 1 := rfl
      rw [e01]
      linear_combination (-(algebraMap O B (D.cc 0) * algebraMap O B (D.cc 1) *
        (r' (GlobalTheory.OrdLoc.fr D)).mat 0 0)) * u1
    · rw [hdd, hdiag' 1, hq, Units.val_mul, Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec, hκ, ← hc']
      simp only [map_mul]
      have e12 : (1 : Fin 3) + 1 = 2 := rfl
      rw [e12]
      linear_combination (-(algebraMap O B (D.cc 1) * algebraMap O B (D.cc 2) *
        (r' (GlobalTheory.OrdLoc.fr D)).mat 1 1)) * u2
