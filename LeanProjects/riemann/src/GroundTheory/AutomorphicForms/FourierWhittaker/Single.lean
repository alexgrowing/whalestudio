import Mathlib
import GroundTheory.AutomorphicForms.FourierWhittaker.PartialCoeffBlockGLEqOfVecMulEq

open NumberField NumberField.mixedEmbedding MeasureTheory Topology Set Filter IsDedekindDomain Matrix
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace FourierWhittaker

open AutomorphicForm

variable {K : Type*} [Field K] [NumberField K]

theorem setIntegral_vecDomain_sum {ι ι₁ ι₂ : Type*} [Fintype ι] [Fintype ι₁] [Fintype ι₂]
    (e : ι ≃ ι₁ ⊕ ι₂) {h : (ι → 𝔸[K]) → ℂ} (hc : Continuous h) :
    ∫ z in vecDomain K ι, h z ∂vecMeasure K ι =
      ∫ x in vecDomain K ι₁, ∫ y in vecDomain K ι₂, h (fun i => Sum.elim x y (e i))
        ∂vecMeasure K ι₂ ∂vecMeasure K ι₁ := by
  let E : (ι → 𝔸[K]) ≃ᵐ (ι₁ → 𝔸[K]) × (ι₂ → 𝔸[K]) :=
    (MeasurableEquiv.piCongrLeft (fun _ : ι₁ ⊕ ι₂ => 𝔸[K]) e).trans
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : ι₁ ⊕ ι₂ => 𝔸[K]))
  have hE : MeasurePreserving E (vecMeasure K ι) ((vecMeasure K ι₁).prod (vecMeasure K ι₂)) :=
    (measurePreserving_piCongrLeft (fun _ : ι₁ ⊕ ι₂ => GroundTheory.Global.adeleMeasure K) e).trans
      (measurePreserving_sumPiEquivProdPi (fun _ : ι₁ ⊕ ι₂ => GroundTheory.Global.adeleMeasure K))
  have hEsymm : ∀ p, E.symm p = fun i => Sum.elim p.1 p.2 (e i) := by
    intro p
    funext i
    simp [E, MeasurableEquiv.piCongrLeft, MeasurableEquiv.sumPiEquivProdPi, Equiv.piCongrLeft,
      Equiv.sumPiEquivProdPi]
    generalize e i = j
    cases j <;> rfl
  have hpre : E ⁻¹' (vecDomain K ι₁ ×ˢ vecDomain K ι₂) = vecDomain K ι := by
    ext z
    simp only [Set.mem_preimage, Set.mem_prod, vecDomain, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · rintro ⟨h1, h2⟩ i
      have hz : z = E.symm (E z) := (E.symm_apply_apply z).symm
      rw [hz, hEsymm]
      show ((E z).1 ⊕ᵥ (E z).2) (e i) ∈ _
      rcases e i with a | b
      · exact h1 a
      · exact h2 b
    · intro h
      refine ⟨fun a => ?_, fun b => ?_⟩
      · have := h (e.symm (Sum.inl a)); simpa [E, MeasurableEquiv.piCongrLeft,
          MeasurableEquiv.sumPiEquivProdPi, Equiv.piCongrLeft, Equiv.sumPiEquivProdPi] using this
      · have := h (e.symm (Sum.inr b)); simpa [E, MeasurableEquiv.piCongrLeft,
          MeasurableEquiv.sumPiEquivProdPi, Equiv.piCongrLeft, Equiv.sumPiEquivProdPi] using this
  rw [← hpre]
  have h1 := hE.setIntegral_preimage_emb E.measurableEmbedding (fun p => h (E.symm p))
    (vecDomain K ι₁ ×ˢ vecDomain K ι₂)
  simp only [E.symm_apply_apply] at h1
  rw [h1, setIntegral_prod]
  · simp only [hEsymm]
  · have hcont : Continuous fun p : (ι₁ → 𝔸[K]) × (ι₂ → 𝔸[K]) => h (E.symm p) := by
      simp_rw [hEsymm]
      refine hc.comp (continuous_pi fun i => ?_)
      rcases e i with a | b
      · exact (continuous_apply a).comp continuous_fst
      · exact (continuous_apply b).comp continuous_snd
    exact (hcont.continuousOn.integrableOn_compact ((isCompact_closure_vecDomain (K := K)
      (ι := ι₁)).prod (isCompact_closure_vecDomain (K := K) (ι := ι₂)))).mono_set
      (Set.prod_mono subset_closure subset_closure)

variable {n : ℕ}

abbrev GePos (n k : ℕ) : Type := {p : Pos n // k ≤ p.1.2.val}

def extGe {R : Type*} [Zero R] {k : ℕ} (Z : GePos n k → R) : Pos n → R :=
  fun p => if h : k ≤ p.1.2.val then Z ⟨p, h⟩ else 0

def supSum (m : ℕ) (X : Pos n → 𝔸[K]) : 𝔸[K] :=
  ∑ p ∈ Finset.univ.filter (fun p : Pos n => p.1.2.val = p.1.1.val + 1 ∧ m ≤ p.1.2.val), X p

theorem supSum_add (m : ℕ) (X Y : Pos n → 𝔸[K]) : supSum m (X + Y) = supSum m X + supSum m Y := by
  simp [supSum, Finset.sum_add_distrib]

theorem supSum_zero (m : ℕ) : supSum m (0 : Pos n → 𝔸[K]) = 0 := by simp [supSum]

theorem supSum_colX_succ (k : ℕ) (x : Fin k → 𝔸[K]) : supSum (k + 1) (colX (n := n) k x) = 0 := by
  refine Finset.sum_eq_zero fun p hp => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  rw [colX_apply, dif_neg (by omega)]

theorem supSum_colX (k : ℕ) (hk : k < n) (x : Fin k → 𝔸[K]) :
    supSum k (colX (n := n) k x) = pair (lastVec k) x := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [supSum]
    simp only [pair, Finset.univ_eq_empty, Finset.sum_empty]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [colX_apply, dif_neg]
    have := p.2
    rw [Fin.lt_def] at this
    omega
  · have hmem : ∀ p : Pos n, (p.1.2.val = p.1.1.val + 1 ∧ k ≤ p.1.2.val) → p.1.2.val = k →
        p = ⟨(⟨k - 1, by omega⟩, ⟨k, hk⟩), by rw [Fin.lt_def]; simp; omega⟩ := by
      intro p h1 h2
      apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext <;> simp <;> omega
    rw [supSum, Finset.sum_eq_single ⟨(⟨k - 1, by omega⟩, ⟨k, hk⟩), by rw [Fin.lt_def]; simp; omega⟩]
    · rw [colX_apply, dif_pos rfl, pair, Finset.sum_eq_single ⟨k - 1, by omega⟩]
      · simp [lastVec]; congr 1; omega
      · intro i _ hi
        rw [lastVec, if_neg (fun h => hi (Fin.ext (by show i.val = k - 1; omega))), map_zero, zero_mul]
      · simp
    · intro p hp hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      rw [colX_apply, dif_neg (fun h => hne (hmem p hp h))]
    · intro h
      exfalso
      apply h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor <;> (try simp) <;> omega

theorem extGe_eq_zero {R : Type*} [Zero R] {k : ℕ} (Z : GePos n (k + 1) → R) (p : Pos n)
    (hp : p.1.2.val ≤ k) : extGe Z p = 0 := by
  rw [extGe, dif_neg (by omega)]

def colSplit (k : ℕ) (hk : k < n) : GePos n k ≃ Fin k ⊕ GePos n (k + 1) where
  toFun p := if h : p.1.1.2.val = k then
      Sum.inl ⟨p.1.1.1.val, by have := p.1.2; rw [Fin.lt_def] at this; omega⟩
    else Sum.inr ⟨p.1, by have := p.2; omega⟩
  invFun := Sum.elim (fun a => ⟨⟨(⟨a.val, by omega⟩, ⟨k, hk⟩), by rw [Fin.lt_def]; exact a.2⟩,
    le_refl k⟩) (fun q => ⟨q.1, by have := q.2; omega⟩)
  left_inv p := by
    by_cases h : p.1.1.2.val = k
    · simp only [dif_pos h, Sum.elim_inl]
      apply Subtype.ext; apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext <;> simp [h]
    · simp only [dif_neg h, Sum.elim_inr]
  right_inv q := by
    rcases q with a | q
    · simp
    · have := q.2
      show (if h : q.1.1.2.val = k then _ else _) = _
      rw [dif_neg (show ¬ q.1.1.2.val = k by omega)]
      rfl

theorem extGe_colSplit {R : Type*} [CommRing R] (k : ℕ) (hk : k < n) (x : Fin k → R)
    (y : GePos n (k + 1) → R) :
    extGe (fun i => Sum.elim x y (colSplit k hk i)) = extGe y + colX k x := by
  funext p
  simp only [extGe, colX_apply, Pi.add_apply]
  by_cases h1 : k ≤ p.1.2.val
  · rw [dif_pos h1]
    by_cases h2 : p.1.2.val = k
    · rw [dif_neg (by omega), dif_pos h2, zero_add]
      show Sum.elim x y (colSplit k hk ⟨p, h1⟩) = _
      simp only [colSplit, Equiv.coe_fn_mk, dif_pos h2, Sum.elim_inl]
    · rw [dif_pos (by omega), dif_neg h2, add_zero]
      show Sum.elim x y (colSplit k hk ⟨p, h1⟩) = _
      simp only [colSplit, Equiv.coe_fn_mk, dif_neg h2, Sum.elim_inr]
  · rw [dif_neg h1, dif_neg (by omega), dif_neg (by omega), add_zero]

theorem continuous_extGe {k : ℕ} : Continuous (extGe (n := n) (k := k) (R := 𝔸[K])) := by
  refine continuous_pi fun p => ?_
  simp only [extGe]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

theorem continuous_supSum (m : ℕ) : Continuous (supSum (K := K) (n := n) m) :=
  continuous_finsetSum _ fun p _ => continuous_apply p

theorem coe_uGL_inv (X : Pos n → 𝔸[K]) :
    (((uGL X)⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K]) = (uMat X).adjugate := by
  rw [Matrix.coe_units_inv, coe_uGL, Matrix.inv_def, det_uMat, Ring.inverse_one, one_smul]

theorem continuous_uGL : Continuous fun X : Pos n → 𝔸[K] => (uGL X : GL (Fin n) 𝔸[K]) := by
  have hc : Continuous fun X : Pos n → 𝔸[K] => uMat X := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [uMat_apply]
    split_ifs
    · exact continuous_const
    · exact continuous_apply _
    · exact continuous_const
  refine Units.continuous_iff.2 ⟨hc, ?_⟩
  simp only [coe_uGL_inv]
  exact hc.matrix_adjugate

def wInt (m : ℕ) (ϕ : AdelicGLn.AdelicGL K n → ℂ) (g : AdelicGLn.AdelicGL K n) (X : Pos n → 𝔸[K]) : ℂ :=
  ϕ (uGL X * g) * (GroundTheory.Global.adelicChar K (-supSum m X) : ℂ)

theorem continuous_wInt (m : ℕ) {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : Continuous ϕ)
    (g : AdelicGLn.AdelicGL K n) : Continuous (wInt m ϕ g) :=
  (hϕ.comp (continuous_uGL.mul continuous_const)).mul
    (continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp (continuous_supSum m).neg))

theorem setIntegral_geCols (k : ℕ) (hk : k < n) {H : (Pos n → 𝔸[K]) → ℂ} (hH : Continuous H) :
    ∫ Z in vecDomain K (GePos n k), H (extGe Z) ∂vecMeasure K (GePos n k) =
      ∫ x in vecDomain K (Fin k), ∫ Y in vecDomain K (GePos n (k + 1)),
        H (extGe Y + colX k x) ∂vecMeasure K (GePos n (k + 1)) ∂vecMeasure K (Fin k) := by
  have := setIntegral_vecDomain_sum (colSplit k hk) (hH.comp continuous_extGe)
  simp only [Function.comp_apply, extGe_colSplit] at this
  exact this

theorem partialCoeff_eq_setIntegral {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : Continuous ϕ) :
    ∀ (m k : ℕ), n - k = m → k ≤ n → ∀ g, partialCoeff ϕ k g =
      ∫ Z in vecDomain K (GePos n k), wInt k ϕ g (extGe Z) ∂vecMeasure K (GePos n k) := by
  intro m
  induction m with
  | zero =>
    intro k hkm hk g
    obtain rfl : k = n := by omega
    rw [partialCoeff_self]
    have hz : ∀ Z : GePos k k → 𝔸[K], extGe Z = 0 := fun Z => by
      funext p; rw [extGe, dif_neg (by have := p.1.2.2; omega)]; rfl
    simp only [hz, wInt, uGL_zero, one_mul, supSum_zero, neg_zero, AddChar.map_zero_eq_one,
      Circle.coe_one, mul_one]
    rw [setIntegral_const, measureReal_def, vecMeasure_vecDomain, ENNReal.toReal_one, one_smul]
  | succ m ih =>
    intro k hkm hk g
    have hkn : k < n := by omega
    rw [setIntegral_geCols k hkn (continuous_wInt k hϕ g), partialCoeff_of_lt ϕ hkn, stepCoeff,
      vecCoeff]
    refine setIntegral_congr_fun measurableSet_vecDomain fun x _ => ?_
    rw [ih (k + 1) (by omega) hkn, ← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun Y => ?_)
    simp only [wInt]
    have hY : ∀ p : Pos n, p.1.2.val ≤ k → extGe Y p = 0 := fun p hp => extGe_eq_zero Y p hp
    have hsup : supSum k (extGe Y) = supSum (k + 1) (extGe Y) := by
      unfold supSum
      refine (Finset.sum_subset (fun p hp => ?_) fun p hp hp' => ?_).symm
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; omega
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
        exact hY p (by omega)
    have hmul : uGL (extGe Y) * colGL k x = uGL (extGe Y + colX k x) := Units.ext (by
      rw [Units.val_mul, colGL, coe_uGL, coe_uGL, coe_uGL]; exact uMat_mul_uMat_colX hY x)
    rw [← mul_assoc (uGL _), hmul, supSum_add, hsup, supSum_colX k hkn x, neg_add,
      AddChar.map_add_eq_mul, Circle.coe_mul, mul_assoc]

theorem vecCoeff_zero_eq_setIntegral {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : Continuous ϕ) {k : ℕ}
    (hk : k < n) (g : AdelicGLn.AdelicGL K n) :
    vecCoeff (fun x => partialCoeff ϕ (k + 1) (colGL k x * g)) 0 =
      ∫ Z in vecDomain K (GePos n k), wInt (k + 1) ϕ g (extGe Z) ∂vecMeasure K (GePos n k) := by
  rw [setIntegral_geCols k hk (continuous_wInt (k + 1) hϕ g), vecCoeff]
  refine setIntegral_congr_fun measurableSet_vecDomain fun x _ => ?_
  simp only [pair, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero, neg_zero,
    AddChar.map_zero_eq_one, Circle.coe_one, mul_one]
  rw [partialCoeff_eq_setIntegral hϕ _ (k + 1) rfl hk]
  refine integral_congr_ae (ae_of_all _ fun Y => ?_)
  simp only [wInt]
  have hY : ∀ p : Pos n, p.1.2.val ≤ k → extGe Y p = 0 := fun p hp => extGe_eq_zero Y p hp
  have hmul : uGL (extGe Y) * colGL k x = uGL (extGe Y + colX k x) := Units.ext (by
    rw [Units.val_mul, colGL, coe_uGL, coe_uGL, coe_uGL]; exact uMat_mul_uMat_colX hY x)
  rw [← mul_assoc (uGL _), hmul, supSum_add, supSum_colX_succ, add_zero]

abbrev LowPos (n k : ℕ) : Type := {p : Pos n // k ≤ p.1.1.val}

def lowSplit (k : ℕ) : GePos n k ≃ LowPos n k ⊕ AutomorphicForm.UPos n k where
  toFun p := if h : k ≤ p.1.1.1.val then Sum.inl ⟨p.1, h⟩
    else Sum.inr ⟨p.1.1, by have := p.2; omega, p.2⟩
  invFun := Sum.elim (fun q => ⟨q.1, by have := q.1.2; have := q.2; rw [Fin.lt_def] at *; omega⟩)
    (fun u => ⟨⟨u.1, by have := u.2; rw [Fin.lt_def]; omega⟩, u.2.2⟩)
  left_inv p := by
    by_cases h : k ≤ p.1.1.1.val
    · simp only [dif_pos h, Sum.elim_inl]
    · simp only [dif_neg h, Sum.elim_inr]
  right_inv q := by
    rcases q with q | u
    · show (if h : k ≤ q.1.1.1.val then _ else _) = _
      rw [dif_pos q.2]
      rfl
    · show (if h : k ≤ u.1.1.val then _ else _) = _
      rw [dif_neg (by have := u.2; omega)]
      rfl

def extLow {R : Type*} [Zero R] {k : ℕ} (B : LowPos n k → R) : Pos n → R :=
  fun p => if h : k ≤ p.1.1.val then B ⟨p, h⟩ else 0

def extU {R : Type*} [Zero R] {k : ℕ} (A : AutomorphicForm.UPos n k → R) : Pos n → R :=
  fun p => if h : p.1.1.val < k ∧ k ≤ p.1.2.val then A ⟨p.1, h⟩ else 0

theorem extGe_lowSplit {R : Type*} [AddCommGroup R] (k : ℕ) (B : LowPos n k → R)
    (A : AutomorphicForm.UPos n k → R) :
    extGe (fun i => Sum.elim B A (lowSplit k i)) = extLow B + extU A := by
  funext p
  simp only [extGe, extLow, extU, Pi.add_apply]
  by_cases h1 : k ≤ p.1.2.val
  · rw [dif_pos h1]
    by_cases h2 : k ≤ p.1.1.val
    · rw [dif_pos h2, dif_neg (by omega), add_zero]
      show Sum.elim B A (lowSplit k ⟨p, h1⟩) = _
      simp only [lowSplit, Equiv.coe_fn_mk, dif_pos h2, Sum.elim_inl]
    · rw [dif_neg h2, dif_pos ⟨by omega, h1⟩, zero_add]
      show Sum.elim B A (lowSplit k ⟨p, h1⟩) = _
      simp only [lowSplit, Equiv.coe_fn_mk, dif_neg h2, Sum.elim_inr]
  · have hp := p.2
    rw [Fin.lt_def] at hp
    rw [dif_neg h1, dif_neg (by omega), dif_neg (by omega), add_zero]

theorem supSum_extU (k : ℕ) (A : AutomorphicForm.UPos n k → 𝔸[K]) :
    supSum (k + 1) (extU A) = 0 := by
  refine Finset.sum_eq_zero fun p hp => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  rw [extU, dif_neg (by omega)]

theorem vecCoeff_zero_eq_setIntegral_low {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : Continuous ϕ)
    {k : ℕ} (hk : k < n) (g : AdelicGLn.AdelicGL K n) :
    vecCoeff (fun x => partialCoeff ϕ (k + 1) (colGL k x * g)) 0 =
      ∫ B in vecDomain K (LowPos n k), (GroundTheory.Global.adelicChar K (-supSum (k + 1) (extLow B)) : ℂ) *
        ∫ A in vecDomain K (AutomorphicForm.UPos n k), ϕ (uGL (extLow B + extU A) * g)
          ∂vecMeasure K (AutomorphicForm.UPos n k) ∂vecMeasure K (LowPos n k) := by
  rw [vecCoeff_zero_eq_setIntegral hϕ hk g]
  have := setIntegral_vecDomain_sum (lowSplit k) ((continuous_wInt (k + 1) hϕ g).comp
    (continuous_extGe (K := K) (n := n) (k := k)))
  simp only [Function.comp_apply, extGe_lowSplit] at this
  rw [this]
  refine setIntegral_congr_fun measurableSet_vecDomain fun B _ => ?_
  simp only [wInt, supSum_add, supSum_extU, add_zero]
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun A => ?_)
  ring

end FourierWhittaker

end

end GroundTheory.Automorphic
