import Mathlib
import GroundTheory.AutomorphicForms.FourierWhittaker.IsAddFundamentalDomainImageOfMapVecLattice
import GroundTheory.AutomorphicForms.FourierWhittaker.Series
import GroundTheory.AutomorphicForms.FourierWhittaker.AlgebraMapIntegerMemIntegralFiniteAdeles
import GroundTheory.AutomorphicForms.FourierWhittaker.AdelicCharPairTorusPtSingle
import GroundTheory.AutomorphicForms.FourierWhittaker.UMatColXEqFromBlocks
import GroundTheory.AutomorphicForms.FourierWhittaker.PartialCoeffDiagonalBlockGLEqVecCoeff
import GroundTheory.AutomorphicForms.FourierWhittaker.Smooth
import GroundTheory.AutomorphicForms.FourierWhittaker.PartialCoeffBlockGLEqOfVecMulEq
import GroundTheory.AutomorphicForms.FourierWhittaker.Single
import GroundTheory.AutomorphicForms.FourierWhittaker.IsAddFundamentalDomainShearSymm

open NumberField NumberField.mixedEmbedding MeasureTheory Topology Set Filter IsDedekindDomain Matrix
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace FourierWhittaker

open AutomorphicForm

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def whittaker (ϕ : AdelicGLn.AdelicGL K n → ℂ) (g : AdelicGLn.AdelicGL K n) : ℂ :=
  ∫ X in vecDomain K (Pos n), ϕ (uGL X * g) * (GroundTheory.Global.adelicChar K (-supSum 0 X) : ℂ)
    ∂vecMeasure K (Pos n)

def gePosZeroEquiv : GePos n 0 ≃ Pos n := Equiv.subtypeUnivEquiv fun _ => Nat.zero_le _

theorem whittaker_eq_partialCoeff_zero {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : Continuous ϕ)
    (g : AdelicGLn.AdelicGL K n) : whittaker ϕ g = partialCoeff ϕ 0 g := by
  rw [partialCoeff_eq_setIntegral hϕ _ 0 rfl (Nat.zero_le n), whittaker]
  let E := MeasurableEquiv.piCongrLeft (fun _ : Pos n => 𝔸[K]) (gePosZeroEquiv (n := n))
  have hE : MeasurePreserving E (vecMeasure K (GePos n 0)) (vecMeasure K (Pos n)) :=
    measurePreserving_piCongrLeft (fun _ : Pos n => GroundTheory.Global.adeleMeasure K) gePosZeroEquiv
  have hext : ∀ Z : GePos n 0 → 𝔸[K], extGe Z = E Z := by
    intro Z
    funext p
    rw [extGe, dif_pos (Nat.zero_le _)]
    simp [E, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, gePosZeroEquiv]
  have hpre : E ⁻¹' vecDomain K (Pos n) = vecDomain K (GePos n 0) := by
    ext Z
    simp only [Set.mem_preimage, vecDomain, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h q
      have := h (gePosZeroEquiv q)
      simpa [E, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, gePosZeroEquiv] using this
    · intro h p
      have := h (gePosZeroEquiv.symm p)
      simpa [E, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, gePosZeroEquiv] using this
  rw [← hE.setIntegral_preimage_emb E.measurableEmbedding, hpre]
  refine setIntegral_congr_fun measurableSet_vecDomain fun Z _ => ?_
  simp only [wInt, hext]

theorem stepCoeff_zero (F : AdelicGLn.AdelicGL K n → ℂ) (g : AdelicGLn.AdelicGL K n) :
    stepCoeff 0 F g = F g := by
  have hx : ∀ x : Fin 0 → 𝔸[K], x = 0 := fun x => funext fun i => i.elim0
  have hc : ∀ x : Fin 0 → 𝔸[K], F (colGL 0 x * g) *
      (GroundTheory.Global.adelicChar K (-pair (lastVec 0) x) : ℂ) = F g := by
    intro x
    rw [hx x, colGL_zero, one_mul, pair_zero, neg_zero, AddChar.map_zero_eq_one, Circle.coe_one,
      mul_one]
  rw [stepCoeff, vecCoeff]
  simp_rw [hc]
  rw [setIntegral_const, measureReal_def, vecMeasure_vecDomain, ENNReal.toReal_one, one_smul]

theorem partialCoeff_zero_eq_one (ϕ : AdelicGLn.AdelicGL K n → ℂ) (hn : 0 < n) :
    partialCoeff ϕ 0 = partialCoeff ϕ 1 := by
  funext g
  rw [partialCoeff_of_lt ϕ hn, stepCoeff_zero]

theorem whittaker_eq_partialCoeff {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : Continuous ϕ) (hn : 0 < n)
    (g : AdelicGLn.AdelicGL K n) : whittaker ϕ g = partialCoeff ϕ 1 g := by
  rw [whittaker_eq_partialCoeff_zero hϕ, partialCoeff_zero_eq_one ϕ hn]

theorem isUSmooth_of_isAutomorphicForm {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : IsAutomorphicForm ϕ) :
    IsUSmooth ϕ where
  arch := hϕ.isSmooth.1
  fin := by
    obtain ⟨U, -, hU⟩ := exists_openSubgroup_rightInvariant hϕ.isSmooth hϕ.isKFinite
    exact ⟨U, hU⟩
  left := hϕ.isLeftInvariant

theorem hasSum_partialCoeff_cusp {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : ϕ ∈ cuspForms K n) {k : ℕ}
    (hk0 : 0 < k) (hk : k < n) (g : AdelicGLn.AdelicGL K n) :
    HasSum (fun ξ : {ξ : Fin k → K // ξ ≠ 0} =>
        partialCoeff ϕ k (AdelicGLn.diagonal K n (blockGL hk.le (rowCompletion ξ.1)) * g))
      (partialCoeff ϕ (k + 1) g) :=
  hasSum_partialCoeff_of_vecCoeff_zero (isUSmooth_of_isAutomorphicForm hϕ.1) hk
    (fun g => vecCoeff_zero_of_isCuspidal hϕ.1.continuous hϕ.1.isLeftInvariant hϕ.2 hk0 hk g) g

variable (K) in

def mirabolic (k : ℕ) : Subgroup (GL (Fin k) K) where
  carrier := {h | IsLastRowUnit ((h : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)}
  one_mem' := by
    show Matrix.vecMul (lastVec k) (1 : Matrix (Fin k) (Fin k) K) = lastVec k
    rw [Matrix.vecMul_one]
  mul_mem' {a b} ha hb := by
    show Matrix.vecMul (lastVec k) ((a * b : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) = lastVec k
    rw [Units.val_mul, ← Matrix.vecMul_vecMul, ha, hb]
  inv_mem' {a} ha := IsLastRowUnit.inv ha

def lastRow {k : ℕ} (γ : GL (Fin k) K) : Fin k → K :=
  Matrix.vecMul (lastVec k) (γ : Matrix (Fin k) (Fin k) K)

theorem lastRow_ne_zero {k : ℕ} (hk : 0 < k) (γ : GL (Fin k) K) : lastRow γ ≠ 0 := by
  intro h
  have hlv : lastVec (K := K) k ≠ 0 := fun h0 => by
    have := congrFun h0 ⟨k - 1, by omega⟩
    simp [lastVec] at this; omega
  apply hlv
  have := congrArg (fun v => Matrix.vecMul v ((γ⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)) h
  simp only [lastRow, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.vecMul_one, Matrix.zero_vecMul] at this
  exact this

theorem lastRow_eq_iff {k : ℕ} (γ γ' : GL (Fin k) K) :
    lastRow γ = lastRow γ' ↔ γ' * γ⁻¹ ∈ mirabolic K k := by
  constructor
  · intro h
    show Matrix.vecMul (lastVec k) ((γ' * γ⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) = lastVec k
    rw [Units.val_mul, ← Matrix.vecMul_vecMul]
    change Matrix.vecMul (lastRow γ') _ = _
    rw [← h, lastRow, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.vecMul_one]
  · intro h
    have h' : Matrix.vecMul (lastVec k) ((γ' * γ⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) =
        lastVec k := h
    symm
    calc lastRow γ' = lastRow ((γ' * γ⁻¹) * γ) := by rw [inv_mul_cancel_right]
      _ = Matrix.vecMul (Matrix.vecMul (lastVec k) ((γ' * γ⁻¹ : GL (Fin k) K) :
            Matrix (Fin k) (Fin k) K)) (γ : Matrix (Fin k) (Fin k) K) := by
          rw [lastRow, Units.val_mul, ← Matrix.vecMul_vecMul]
      _ = lastRow γ := by rw [h']; rfl

def cosetEquiv {k : ℕ} (hk : 0 < k) :
    Quotient (QuotientGroup.rightRel (mirabolic K k)) ≃ {ξ : Fin k → K // ξ ≠ 0} where
  toFun := Quotient.lift (fun γ => ⟨lastRow γ, lastRow_ne_zero hk γ⟩) fun a b hab =>
    Subtype.ext ((lastRow_eq_iff a b).2 (QuotientGroup.rightRel_apply.1 hab))
  invFun ξ := Quotient.mk _ (rowCompletion ξ.1)
  left_inv := by
    refine Quotient.ind fun γ => Quotient.sound ?_
    show (QuotientGroup.rightRel (mirabolic K k)) (rowCompletion (lastRow γ)) γ
    rw [QuotientGroup.rightRel_apply, ← lastRow_eq_iff]
    exact vecMul_rowCompletion (lastRow_ne_zero hk γ)
  right_inv ξ := Subtype.ext (vecMul_rowCompletion ξ.2)

theorem hasSum_partialCoeff_cusp_cosets {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : ϕ ∈ cuspForms K n)
    {k : ℕ} (hk0 : 0 < k) (hk : k < n) (g : AdelicGLn.AdelicGL K n) :
    HasSum (fun c : Quotient (QuotientGroup.rightRel (mirabolic K k)) =>
        partialCoeff ϕ k (AdelicGLn.diagonal K n (blockGL hk.le c.out) * g))
      (partialCoeff ϕ (k + 1) g) := by
  rw [← (cosetEquiv (K := K) hk0).symm.hasSum_iff]
  refine (hasSum_partialCoeff_cusp hϕ hk0 hk g).congr_fun fun ξ => ?_
  simp only [Function.comp_apply]
  refine partialCoeff_blockGL_eq_of_vecMul_eq hϕ.1.isLeftInvariant hk.le ?_ g
  have hc : ((cosetEquiv (K := K) hk0).symm ξ) = Quotient.mk _ (rowCompletion ξ.1) := rfl
  have hrel := Quotient.mk_out (s := QuotientGroup.rightRel (mirabolic K k)) (rowCompletion ξ.1)
  rw [hc]
  have := (lastRow_eq_iff _ _).2 (QuotientGroup.rightRel_apply.1 hrel)
  exact this.symm

def nestedWhittaker (ϕ : AdelicGLn.AdelicGL K n → ℂ) : ℕ → AdelicGLn.AdelicGL K n → ℂ
  | 0 => whittaker ϕ
  | 1 => whittaker ϕ
  | k + 2 => fun g => if h : k + 1 < n then
      ∑' c : Quotient (QuotientGroup.rightRel (mirabolic K (k + 1))),
        nestedWhittaker ϕ (k + 1) (AdelicGLn.diagonal K n (blockGL h.le c.out) * g)
    else 0

theorem partialCoeff_eq_nestedWhittaker {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : ϕ ∈ cuspForms K n) :
    ∀ k, 0 < k → k ≤ n → partialCoeff ϕ k = nestedWhittaker ϕ k := by
  intro k
  induction k with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | succ k ih =>
    intro _ hkn
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · funext g
      exact (whittaker_eq_partialCoeff hϕ.1.continuous hkn g).symm
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      funext g
      have hlt : m + 1 < n := by omega
      rw [nestedWhittaker]
      dsimp only
      rw [dif_pos hlt, ← (hasSum_partialCoeff_cusp_cosets hϕ hk0 hlt g).tsum_eq, ih hk0 hlt.le]

theorem eq_nestedWhittaker {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : ϕ ∈ cuspForms K n) (hn : 0 < n)
    (g : AdelicGLn.AdelicGL K n) : ϕ g = nestedWhittaker ϕ n g := by
  rw [← partialCoeff_eq_nestedWhittaker hϕ n hn le_rfl, partialCoeff_self]

end FourierWhittaker

end

end GroundTheory.Automorphic
