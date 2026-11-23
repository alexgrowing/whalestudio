import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.PsiDatumStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.WhittakerZeroStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.TransferA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.TopContDiffOn

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.CapelliClosureMembership

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Grp

def jAdj (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Jm ε * gᴴ * Jm ε

lemma jAdj_mul {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : jAdj ε g * g = 1 := by
  unfold jAdj
  unfold inUJ at hg
  rw [show Jm ε * gᴴ * Jm ε * g = Jm ε * (gᴴ * Jm ε * g) by simp only [Matrix.mul_assoc], hg,
    SmDerA.Jm_mul_Jm]

lemma mul_jAdj {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : g * jAdj ε g = 1 :=
  mul_eq_one_comm.mp (jAdj_mul hg)

lemma inUJ_jAdj {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    inUJ ε (jAdj ε g) := by
  have h1 := mul_jAdj hg
  unfold jAdj at h1 ⊢
  unfold inUJ
  have h2 : g * (Jm ε * (gᴴ * Jm ε)) = 1 := by simpa only [Matrix.mul_assoc] using h1
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, SmDerA.Jm_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc, LemK.ta_Jm_Jm]
  rw [h2, Matrix.mul_one]

lemma inUJ_one (ε : Fin n → Bool) : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by
  unfold inUJ
  simp

lemma inUJ_exp (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (t : ℝ) :
    inUJ ε (NormedSpace.exp ((t : ℂ) • X)) := by
  have := LemK.ta_inUJ_mul_exp ε (inUJ_one ε) hX t
  simpa using this

end Grp

section Unit

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

lemma inner_sig_sig (hσ : IsURepOn (UJset ε) σ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g)
    (x y : H) : ⟪σ g x, σ g y⟫_ℂ = ⟪x, y⟫_ℂ := by
  let T : H →ₗᵢ[ℂ] H := { toLinearMap := (σ g : H →ₗ[ℂ] H), norm_map' := fun v => hσ.2.1 g hg v }
  exact T.inner_map_map x y

lemma sig_sig_jAdj (hσ : IsURepOn (UJset ε) σ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (y : H) :
    σ g (σ (jAdj ε g) y) = y := by
  rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 g hg _ (inUJ_jAdj hg), mul_jAdj hg, hσ.1.1]
  rfl

lemma inner_sig_left (hσ : IsURepOn (UJset ε) σ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g)
    (x y : H) : ⟪σ g x, y⟫_ℂ = ⟪x, σ (jAdj ε g) y⟫_ℂ := by
  conv_lhs => rw [← sig_sig_jAdj hσ hg y]
  exact inner_sig_sig hσ hg _ _

lemma hasDerivAt_coef (hσ : IsURepOn (UJset ε) σ) {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} (hD : IsDerivedOn ε σ D E) {g X : Matrix (Fin n) (Fin n) ℂ}
    (hg : inUJ ε g) (hX : inG ε X) (y : H) (x : D) :
    HasDerivAt (fun t : ℝ => ⟪y, σ (g * NormedSpace.exp ((t : ℂ) • X)) (x : H)⟫_ℂ)
      ⟪y, σ g ((actM E X x : D) : H)⟫_ℂ 0 := by
  have e : (fun t : ℝ => ⟪y, σ (g * NormedSpace.exp ((t : ℂ) • X)) (x : H)⟫_ℂ) =
      fun t : ℝ => (((innerSL ℂ y).comp (σ g)).restrictScalars ℝ)
        (σ (NormedSpace.exp ((t : ℂ) • X)) (x : H)) := by
    funext t
    rw [hσ.1.2 g hg _ (inUJ_exp ε hX t)]
    rfl
  rw [e]
  exact (((innerSL ℂ y).comp (σ g)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (hD.deriv X hX x)

end Unit

section Op

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {D : Submodule ℂ H} {V : Submodule ℂ D}

abbrev ob (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] :
    OrthonormalBasis (Fin (Module.finrank ℂ W)) ℂ W := stdOrthonormalBasis ℂ W

def opC (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (ι : V ≃ₗ[ℂ] W)
    (h : Matrix (Fin n) (Fin n) ℂ) (B : Module.End ℂ D) : W →L[ℂ] W :=
  ∑ i, ∑ j, ⟪(((ι.symm (ob W i) : V) : D) : H), σ h ((B ((ι.symm (ob W j) : V) : D) : D) : H)⟫_ℂ •
    (innerSL ℂ (ob W j)).smulRight (ob W i)

variable (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (ι : V ≃ₗ[ℂ] W)

lemma opC_add (h : Matrix (Fin n) (Fin n) ℂ) (B₁ B₂ : Module.End ℂ D) :
    opC σ ι h (B₁ + B₂) = opC σ ι h B₁ + opC σ ι h B₂ := by
  simp only [opC, LinearMap.add_apply, Submodule.coe_add, map_add, inner_add_right, add_smul,
    Finset.sum_add_distrib]

lemma opC_smul (h : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (B : Module.End ℂ D) :
    opC σ ι h (c • B) = c • opC σ ι h B := by
  simp only [opC, LinearMap.smul_apply, Submodule.coe_smul, map_smul, inner_smul_right, smul_smul,
    Finset.smul_sum]

lemma opC_zero (h : Matrix (Fin n) (Fin n) ℂ) : opC σ ι h (0 : Module.End ℂ D) = 0 := by
  simpa using opC_smul σ ι h (0 : ℂ) 0

def opL (h : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ D →ₗ[ℂ] (W →L[ℂ] W) where
  toFun := opC σ ι h
  map_add' := opC_add σ ι h
  map_smul' := opC_smul σ ι h

lemma vec_expand (v : V) :
    ((v : D) : H) = ∑ j, ⟪ob W j, ι v⟫_ℂ • (((ι.symm (ob W j) : V) : D) : H) := by
  conv_lhs => rw [← ι.symm_apply_apply v, ← (ob W).sum_repr' (ι v)]
  simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul]

lemma vec_expandD (v : V) :
    (v : D) = ∑ j, ⟪ob W j, ι v⟫_ℂ • ((ι.symm (ob W j) : V) : D) := by
  conv_lhs => rw [← ι.symm_apply_apply v, ← (ob W).sum_repr' (ι v)]
  simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul]

lemma opC_coef (h : Matrix (Fin n) (Fin n) ℂ) (B : Module.End ℂ D) (v v' : V) :
    ⟪ι v', opC σ ι h B (ι v)⟫_ℂ = ⟪((v' : D) : H), σ h ((B v : D) : H)⟫_ℂ := by
  rw [vec_expandD ι v, vec_expand ι v']
  simp only [opC, map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_sum, sum_inner, inner_smul_left,
    inner_smul_right, inner_conj_symm]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Op

section Deriv

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {D : Submodule ℂ H} {V : Submodule ℂ D} {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {E : Fin n → Fin n → Module.End ℂ D}
  (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (ι : V ≃ₗ[ℂ] W)

include hσ hD

lemma hasDerivAt_opC {g X : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hX : inG ε X)
    (B : Module.End ℂ D) :
    HasDerivAt (fun t : ℝ => opC σ ι (g * NormedSpace.exp ((t : ℂ) • X)) B)
      (opC σ ι g (actM E X * B)) 0 := by
  unfold opC
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.fun_sum
  intro j _
  exact (hasDerivAt_coef hσ hD hg hX _ _).smul_const _

lemma rdV_opC {F : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {B : Module.End ℂ D}
    (hF : ∀ h, inUJ ε h → F h = opC σ ι h B) {g X : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g)
    (hX : inG ε X) : Formalism.REAL.RdV X F g = opC σ ι g (actM E X * B) := by
  have e : (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) =
      fun t : ℝ => opC σ ι (g * NormedSpace.exp ((t : ℂ) • X)) B :=
    funext fun t => hF _ (LemK.ta_inUJ_mul_exp ε hg hX t)
  show deriv (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) 0 = _
  rw [e]
  exact (hasDerivAt_opC hσ hD ι hg hX B).deriv

lemma eabV_opC {F : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {B : Module.End ℂ D}
    (hF : ∀ h, inUJ ε h → F h = opC σ ι h B) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g)
    (a b : Fin n) : Formalism.REAL.EabV ε a b F g = opC σ ι g (E a b * B) := by
  have h1 : inG ε (Formalism.REAL.cpart1 ε (Matrix.single a b 1)) := LemK.ta_inG_cpart1 ε _
  have h2 : inG ε (Formalism.REAL.cpart2 ε (Matrix.single a b 1)) := LemK.ta_inG_cpart2 ε _
  have hs : Formalism.REAL.cpart1 ε (Matrix.single a b 1) + Complex.I • Formalism.REAL.cpart2 ε (Matrix.single a b 1) =
      Matrix.single a b 1 := LemK.ta_cpart_sum ε _
  show Formalism.REAL.RdV (Formalism.REAL.cpart1 ε (Matrix.single a b 1)) F g +
    Complex.I • Formalism.REAL.RdV (Formalism.REAL.cpart2 ε (Matrix.single a b 1)) F g = _
  rw [rdV_opC hσ hD ι hF hg h1, rdV_opC hσ hD ι hF hg h2, ← opC_smul, ← opC_add, ← smul_mul_assoc,
    ← add_mul, ← SmDerA.actM_smul, ← SmDerA.actM_add, hs, SmDerA.actM_single]

lemma top_opC {F : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {B : Module.End ℂ D}
    (hF : ∀ h, inUJ ε h → F h = opC σ ι h B) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g)
    (u : ℂ) (a b : Fin n) :
    Formalism.QuantumDeterminants.Top (Formalism.REAL.EabV ε) u a b F g = opC σ ι g (Capelli.capEntry E u a b * B) := by
  unfold Formalism.QuantumDeterminants.Top Capelli.capEntry
  rw [eabV_opC hσ hD ι hF hg, hF g hg, add_mul, opC_add]
  split_ifs
  · rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, opC_smul, add_comm]
  · rw [zero_mul, opC_zero, zero_add, add_zero]

lemma foldr_opC (l : List (ℂ × Fin n × Fin n)) :
    ∀ (F : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (B : Module.End ℂ D),
      (∀ h, inUJ ε h → F h = opC σ ι h B) → ∀ g, inUJ ε g →
      (l.map fun p => Formalism.QuantumDeterminants.Top (Formalism.REAL.EabV ε) p.1 p.2.1 p.2.2).foldr (fun T f => T f) F g =
        opC σ ι g ((l.map fun p => Capelli.capEntry E p.1 p.2.1 p.2.2).prod * B) := by
  induction l with
  | nil =>
    intro F B hF g hg
    simp [hF g hg]
  | cons p l ih =>
    intro F B hF g hg
    simp only [List.map_cons, List.foldr_cons, List.prod_cons]
    rw [top_opC hσ hD ι (B := (l.map fun p => Capelli.capEntry E p.1 p.2.1 p.2.2).prod * B)
      (fun h hh => ih F B hF h hh) hg, mul_assoc]

lemma qdet_opC {F : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {B : Module.End ℂ D}
    (hF : ∀ h, inUJ ε h → F h = opC σ ι h B) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (u : ℂ) :
    Formalism.QuantumDeterminants.qdetOp (Formalism.REAL.EabV ε) u F g = opC σ ι g (Capelli.capelliC E u * B) := by
  unfold Formalism.QuantumDeterminants.qdetOp Formalism.QuantumDeterminants.qminorOp Capelli.capelliC Capelli.cminor
  rw [Finset.sum_apply, Finset.sum_mul]
  change _ = opL σ ι g _
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Pi.smul_apply, smul_mul_assoc, ← Int.cast_smul_eq_zsmul ℂ, map_smul]
  congr 1
  have e1 : (List.ofFn fun k : Fin n => Formalism.QuantumDeterminants.Top (Formalism.REAL.EabV (E := W →L[ℂ] W) ε) (u - ((k : ℕ) : ℂ)) (id (s k)) (id k)) =
      (List.ofFn fun k : Fin n => (u - ((k : ℕ) : ℂ), s k, k)).map
        fun p => Formalism.QuantumDeterminants.Top (Formalism.REAL.EabV (E := W →L[ℂ] W) ε) p.1 p.2.1 p.2.2 := by
    rw [List.map_ofFn]; rfl
  have e2 : (List.ofFn fun j : Fin n => Capelli.capEntry E (u - ((j : ℕ) : ℂ)) (id (s j)) (id j)) =
      (List.ofFn fun k : Fin n => (u - ((k : ℕ) : ℂ), s k, k)).map
        fun p => Capelli.capEntry E p.1 p.2.1 p.2.2 := by
    rw [List.map_ofFn]; rfl
  rw [e1, e2]
  exact foldr_opC hσ hD ι _ F B hF g hg

end Deriv

end ReciprocityTheory.ChartRestriction.DS.Lap.CapelliClosureMembership
