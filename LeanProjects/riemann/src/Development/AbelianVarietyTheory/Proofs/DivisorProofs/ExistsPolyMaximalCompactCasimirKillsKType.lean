import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasKOp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot GlobalTheory.HCAlpha MeasureTheory
open scoped ContDiff

noncomputable section
open Filter Topology
open scoped Matrix

namespace GlobalTheory.HCKTypes

theorem slope_mem {K : Type} (V : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ V] (F : ℝ → K → ℂ)
    (hF : ∀ t, F t ∈ V) (D : K → ℂ) (hD : ∀ x, HasDerivAt (fun t => F t x) (D x) 0) : D ∈ V := by
  have hsV : ∀ t : ℝ, ((t : ℂ)⁻¹ • (F t - F 0)) ∈ V := fun t => V.smul_mem _ (V.sub_mem (hF t) (hF 0))
  have hlim : Tendsto (fun t : ℝ => (t : ℂ)⁻¹ • (F t - F 0)) (𝓝[≠] 0) (𝓝 D) := by
    refine tendsto_pi_nhds.2 fun x => ?_
    refine (hasDerivAt_iff_tendsto_slope_zero.1 (hD x)).congr fun t => ?_
    simp [Complex.real_smul, zero_add]
  exact (Submodule.closed_of_finiteDimensional V).mem_of_tendsto hlim (Eventually.of_forall hsV)

theorem slope_deriv {K : Type} (V : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ V] (F : ℝ → K → ℂ)
    (hF : ∀ t, F t ∈ V) (D : K → ℂ) (hD : ∀ x, HasDerivAt (fun t => F t x) (D x) 0) (hDV : D ∈ V)
    (β : V →ₗ[ℂ] ℂ) : HasDerivAt (fun t => β ⟨F t, hF t⟩) (β ⟨D, hDV⟩) 0 := by
  have hsV : ∀ t : ℝ, ((t : ℂ)⁻¹ • (F t - F 0)) ∈ V := fun t => V.smul_mem _ (V.sub_mem (hF t) (hF 0))
  have hlim : Tendsto (fun t : ℝ => (t : ℂ)⁻¹ • (F t - F 0)) (𝓝[≠] 0) (𝓝 D) := by
    refine tendsto_pi_nhds.2 fun x => ?_
    refine (hasDerivAt_iff_tendsto_slope_zero.1 (hD x)).congr fun t => ?_
    simp [Complex.real_smul, zero_add]
  have hlim' : Tendsto (fun t : ℝ => (⟨_, hsV t⟩ : V)) (𝓝[≠] 0) (𝓝 ⟨D, hDV⟩) := tendsto_subtype_rng.2 hlim
  have hβ := ((LinearMap.continuous_of_finiteDimensional β).tendsto _).comp hlim'
  refine hasDerivAt_iff_tendsto_slope_zero.2 (hβ.congr fun t => ?_)
  have e : (⟨_, hsV t⟩ : V) = (t : ℂ)⁻¹ • ((⟨F t, hF t⟩ : V) - ⟨F 0, hF 0⟩) := rfl
  simp only [Function.comp_apply, e, map_smul, map_sub, zero_add, Complex.real_smul, smul_eq_mul, Complex.ofReal_inv]

section Curve
open scoped Matrix
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem exists_curve (X : Lie E a) (hX : (Matrix.of X)ᴴ = -Matrix.of X) :
    ∃ c : ℝ → Kinf E a, c 0 = 1 ∧ HasDerivAt (fun t => toL (c t : Matrix (Fin a) (Fin a) (Cinf E))) X 0 := by
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  set A : Matrix (Fin a) (Fin a) (Cinf E) := Matrix.of X with hA
  have hmem : ∀ t : ℝ, NormedSpace.exp (t • A) ∈ Matrix.unitaryGroup (Fin a) (Cinf E) := by
    intro t
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose,
      Matrix.conjTranspose_smul, hX, star_trivial]
    have hc : Commute (t • A) (t • -A) := by
      rw [smul_neg]; exact (((Commute.refl A).smul_left t).smul_right t).neg_right
    refine (NormedSpace.exp_add_of_commute hc).symm.trans ?_
    rw [smul_neg, add_neg_cancel, NormedSpace.exp_zero]
  refine ⟨fun t => ⟨_, hmem t⟩, ?_, ?_⟩
  · ext1
    simp
  · have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) A 0
    simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
    let L : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a :=
      LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap
    exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

end Curve

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def wf (φ : Sm E a) (g : GA E a) : Kinf E a → ℂ := fun k => (cptRep E a k φ).1 g

theorem wf_apply (φ : Sm E a) (g : GA E a) (k : Kinf E a) :
    wf φ g k = φ.1 (g * infGL E a (Unitary.toUnits k)) := rfl

theorem wf_mul (φ : Sm E a) (g : GA E a) (k : Kinf E a) :
    wf φ (g * infGL E a (Unitary.toUnits k)) = fun x => wf φ g (k * x) := by
  funext x
  simp only [wf_apply, map_mul, mul_assoc]

theorem wf_one (φ : Sm E a) (g : GA E a) : wf φ g 1 = φ.1 g := by
  simp [wf_apply]

variable (W : Submodule ℂ (Kinf E a → ℂ))

def Vsp : Submodule ℂ (Kinf E a → ℂ) :=
  Submodule.span ℂ {f | ∃ φ : Sm E a, (∀ g, wf φ g ∈ W) ∧ ∃ g, wf φ g = f}

theorem Vsp_le : Vsp W ≤ W := Submodule.span_le.2 fun _ ⟨_, hφ, g, e⟩ => e ▸ hφ g

theorem wf_mem_Vsp {φ : Sm E a} (hφ : ∀ g, wf φ g ∈ W) (g : GA E a) : wf φ g ∈ Vsp W :=
  Submodule.subset_span ⟨φ, hφ, g, rfl⟩

theorem Vsp_stable (k : Kinf E a) (v : Kinf E a → ℂ) (hv : v ∈ Vsp W) : (fun x => v (k * x)) ∈ Vsp W := by
  induction hv using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨φ, hφ, g, rfl⟩ := hf
    have h := wf_mem_Vsp W hφ (g * infGL E a (Unitary.toUnits k))
    rwa [wf_mul] at h
  | zero => exact (Vsp W).zero_mem
  | add u w _ _ hu hw => exact (Vsp W).add_mem hu hw
  | smul c u _ hu => exact (Vsp W).smul_mem c hu

variable {W}

def Rel (o : Module.End ℂ (Sm E a)) (O : Module.End ℂ (Vsp W)) : Prop :=
  ∀ (φ : Sm E a) (hφ : ∀ g, wf φ g ∈ W) (β : Vsp W →ₗ[ℂ] ℂ) (ψ : Sm E a),
    (∀ g, ψ.1 g = β ⟨wf φ g, wf_mem_Vsp W hφ g⟩) → ∀ g, (o ψ).1 g = β (O ⟨wf φ g, wf_mem_Vsp W hφ g⟩)

theorem Rel.mul {o₁ o₂ : Module.End ℂ (Sm E a)} {O₁ O₂ : Module.End ℂ (Vsp W)} (h₁ : Rel o₁ O₁) (h₂ : Rel o₂ O₂) :
    Rel (o₁ * o₂) (O₂ * O₁) := fun φ hφ β ψ hψ g =>
  h₁ φ hφ (β ∘ₗ O₂) (o₂ ψ) (h₂ φ hφ β ψ hψ) g

theorem Rel.add {o₁ o₂ : Module.End ℂ (Sm E a)} {O₁ O₂ : Module.End ℂ (Vsp W)} (h₁ : Rel o₁ O₁) (h₂ : Rel o₂ O₂) :
    Rel (o₁ + o₂) (O₁ + O₂) := fun φ hφ β ψ hψ g => by
  simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, map_add, h₁ φ hφ β ψ hψ g, h₂ φ hφ β ψ hψ g]

theorem Rel.smul {o : Module.End ℂ (Sm E a)} {O : Module.End ℂ (Vsp W)} (h : Rel o O) (c : ℂ) :
    Rel (c • o) (c • O) := fun φ hφ β ψ hψ g => by
  simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, map_smul, h φ hφ β ψ hψ g, smul_eq_mul]

theorem Rel.algebraMap (c : ℂ) : Rel (W := W) (algebraMap ℂ (Module.End ℂ (Sm E a)) c) (algebraMap ℂ _ c) :=
  fun φ hφ β ψ hψ g => by
    simp only [Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply, map_smul, hψ g, smul_eq_mul]

theorem Rel.sum {ι : Type} (s : Finset ι) {o : ι → Module.End ℂ (Sm E a)} {O : ι → Module.End ℂ (Vsp W)}
    (h : ∀ i ∈ s, Rel (o i) (O i)) : Rel (∑ i ∈ s, o i) (∑ i ∈ s, O i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using Rel.algebraMap (W := W) (E := E) (a := a) 0
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem Rel.aeval {o : Module.End ℂ (Sm E a)} {O : Module.End ℂ (Vsp W)} (h : Rel o O) (p : Polynomial ℂ) :
    Rel (Polynomial.aeval o p) (Polynomial.aeval O p) := by
  induction p using Polynomial.induction_on with
  | C c => simpa using Rel.algebraMap (W := W) c
  | add p q hp hq => simpa using hp.add hq
  | monomial n c hp =>
    have e1 : Polynomial.aeval o (Polynomial.C c * Polynomial.X ^ (n + 1)) =
        Polynomial.aeval o (Polynomial.C c * Polynomial.X ^ n) * o := by
      rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X]
    have e2 : Polynomial.aeval O (Polynomial.C c * Polynomial.X ^ (n + 1)) =
        O * Polynomial.aeval O (Polynomial.C c * Polynomial.X ^ n) := by
      rw [pow_succ', mul_left_comm, map_mul, Polynomial.aeval_X]
    rw [e1, e2]
    exact hp.mul h

section Lie
variable {X : Lie E a} {c : ℝ → Kinf E a}

theorem differentiableAt_wf (φ : Sm E a) (g : GA E a) (hc0 : c 0 = 1)
    (hc : HasDerivAt (fun t => toL (c t : Matrix (Fin a) (Fin a) (Cinf E))) X 0) (x : Kinf E a) :
    DifferentiableAt ℝ (fun t => wf φ g (c t * x)) 0 := by
  have e : (fun t => wf φ g (c t * x)) =
      chart φ.1 g ∘ rmul (toL (x : Matrix (Fin a) (Fin a) (Cinf E))) ∘
        (fun t => toL (c t : Matrix (Fin a) (Fin a) (Cinf E))) := by
    funext t
    rw [wf_apply, Function.comp_apply, Function.comp_apply, ← chart_val φ.1 g (Unitary.toUnits (c t * x))]
    rfl
  rw [e]
  refine DifferentiableAt.comp (0 : ℝ) ?_ ((rmul _).differentiableAt.comp (0 : ℝ) hc.differentiableAt)
  have e2 : rmul (toL (x : Matrix (Fin a) (Fin a) (Cinf E))) (toL (c 0 : Matrix (Fin a) (Fin a) (Cinf E))) =
      toL (Unitary.toUnits x).val := by
    rw [hc0]
    change (1 : Matrix (Fin a) (Fin a) (Cinf E)) * (x : Matrix (Fin a) (Fin a) (Cinf E)) = _
    rw [one_mul]; rfl
  rw [Function.comp_apply, e2]
  exact (contDiffAt_chart φ.2 g (val_mem_invSet _)).differentiableAt (by simp)

theorem differentiableAt_Vsp (hc0 : c 0 = 1)
    (hc : HasDerivAt (fun t => toL (c t : Matrix (Fin a) (Fin a) (Cinf E))) X 0) (v : Kinf E a → ℂ)
    (hv : v ∈ Vsp W) (x : Kinf E a) : DifferentiableAt ℝ (fun t => v (c t * x)) 0 := by
  induction hv using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨φ, -, g, rfl⟩ := hf
    exact differentiableAt_wf φ g hc0 hc x
  | zero => exact differentiableAt_const _
  | add u w _ _ hu hw => exact hu.add hw
  | smul r u _ hu => exact hu.const_smul r

variable [FiniteDimensional ℂ (Vsp W)]

def leftDer (hc0 : c 0 = 1) (hc : HasDerivAt (fun t => toL (c t : Matrix (Fin a) (Fin a) (Cinf E))) X 0) :
    Module.End ℂ (Vsp W) where
  toFun v := ⟨fun x => deriv (fun t => v.1 (c t * x)) 0, slope_mem (Vsp W) (fun t x => v.1 (c t * x))
    (fun t => Vsp_stable W (c t) v.1 v.2) _ fun x => (differentiableAt_Vsp hc0 hc v.1 v.2 x).hasDerivAt⟩
  map_add' u v := Subtype.ext <| funext fun x =>
    deriv_add (differentiableAt_Vsp hc0 hc u.1 u.2 x) (differentiableAt_Vsp hc0 hc v.1 v.2 x)
  map_smul' r v := Subtype.ext <| funext fun x =>
    deriv_const_smul r (differentiableAt_Vsp hc0 hc v.1 v.2 x)

theorem rel_lie (hc0 : c 0 = 1) (hc : HasDerivAt (fun t => toL (c t : Matrix (Fin a) (Fin a) (Cinf E))) X 0) :
    Rel (W := W) (lie E a X) (leftDer hc0 hc) := by
  intro φ hφ β ψ hψ g
  have h1 := hasDerivAt_curve ψ g (fun t => Unitary.toUnits (c t)) X (by rw [hc0, map_one]) hc
  have hF : ∀ t, (fun x => wf φ g (c t * x)) ∈ Vsp W := fun t => Vsp_stable W (c t) _ (wf_mem_Vsp W hφ g)
  have hD := fun x => (differentiableAt_Vsp hc0 hc (wf φ g) (wf_mem_Vsp W hφ g) x).hasDerivAt
  have h2 := slope_deriv (Vsp W) (fun t x => wf φ g (c t * x)) hF _ hD
    (slope_mem (Vsp W) (fun t x => wf φ g (c t * x)) hF _ hD) β
  have e : (fun t => ψ.1 (g * infGL E a (Unitary.toUnits (c t)))) = fun t => β ⟨_, hF t⟩ := by
    funext t
    rw [hψ]
    congr 2
    exact wf_mul φ g (c t)
  rw [e] at h1
  exact h1.unique h2

end Lie

section Skew
open scoped Matrix

omit [NumberField E] [IsTotallyComplex E] in
theorem star_atEmb (τ : E →+* ℂ) (z : ℂ) : star (atEmb τ z) = atEmb τ (star z) := by
  classical
  funext w
  unfold atEmb
  by_cases hw : w = InfinitePlace.mk τ
  · subst hw
    simp only [Pi.star_apply, Pi.single_eq_same]
    split_ifs <;> simp
  · simp [Pi.star_apply, Pi.single_eq_of_ne hw]

omit [NumberField E] [IsTotallyComplex E] in
theorem skew_sub {x : Cinf E} (hx : star x = x) (i j : Fin a) :
    (Matrix.single i j x - Matrix.single j i x)ᴴ = -(Matrix.single i j x - Matrix.single j i x) := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_single, Matrix.conjTranspose_single, hx, neg_sub]

omit [NumberField E] [IsTotallyComplex E] in
theorem skew_add {y : Cinf E} (hy : star y = -y) (i j : Fin a) :
    (Matrix.single i j y + Matrix.single j i y)ᴴ = -(Matrix.single i j y + Matrix.single j i y) := by
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_single, Matrix.conjTranspose_single, hy, neg_add, add_comm]
  ext k l
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.single_apply]
  split_ifs <;> simp

end Skew

theorem exists_casK_poly : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (W : Submodule ℂ (Kinf E a → ℂ)),
    FiniteDimensional ℂ W → ∃ q : Polynomial ℂ, q ≠ 0 ∧ ∀ φ : Sm E a,
      (∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k φ).1 g) ∈ W) → Polynomial.aeval (casKOp E a) q φ = 0 := by
  intro E _ _ _ a W hW
  haveI : FiniteDimensional ℂ (Vsp W) := Submodule.finiteDimensional_of_le (Vsp_le W)
  have hlie : ∀ X : Lie E a, (Matrix.of X)ᴴ = -Matrix.of X → ∃ O : Module.End ℂ (Vsp W), Rel (lie E a X) O := by
    intro X hX
    obtain ⟨c, hc0, hc⟩ := exists_curve X hX
    exact ⟨leftDer hc0 hc, rel_lie hc0 hc⟩
  have hA : ∀ (τ : E →+* ℂ) (i j : Fin a), ∃ O : Module.End ℂ (Vsp W),
      Rel (lieS E a i j (atEmb τ 1) - lieS E a j i (atEmb τ 1)) O := by
    intro τ i j
    rw [lieS_apply, lieS_apply, ← map_sub]
    exact hlie _ (skew_sub (by rw [star_atEmb, star_one]) i j)
  have hB : ∀ (τ : E →+* ℂ) (i j : Fin a), ∃ O : Module.End ℂ (Vsp W),
      Rel (lieS E a i j (atEmb τ Complex.I) + lieS E a j i (atEmb τ Complex.I)) O := by
    intro τ i j
    rw [lieS_apply, lieS_apply, ← map_add]
    refine hlie _ (skew_add ?_ i j)
    rw [star_atEmb, Complex.star_def, Complex.conj_I, atEmb_eq, atEmb_eq τ Complex.I]
    simp
  choose OA hOA using hA
  choose OB hOB using hB
  set C : Module.End ℂ (Vsp W) :=
    ∑ τ : E →+* ℂ, ∑ i : Fin a, ∑ j : Fin a, (1 / 4 : ℂ) • (OA τ i j ^ 2 + OB τ i j ^ 2) with hCdef
  have hC : Rel (casKOp E a) C := by
    unfold casKOp
    refine Rel.sum _ fun τ _ => Rel.sum _ fun i _ => Rel.sum _ fun j _ => Rel.smul ?_ _
    rw [sq, sq, sq, sq]
    exact ((hOA τ i j).mul (hOA τ i j)).add ((hOB τ i j).mul (hOB τ i j))
  refine ⟨C.charpoly, (LinearMap.charpoly_monic C).ne_zero, fun φ hφ => ?_⟩
  let α : Vsp W →ₗ[ℂ] ℂ := LinearMap.proj (R := ℂ) (φ := fun _ : Kinf E a => ℂ) 1 ∘ₗ (Vsp W).subtype
  have h := hC.aeval C.charpoly φ hφ α φ (fun g => (wf_one φ g).symm)
  refine Subtype.ext (funext fun g => ?_)
  rw [h g, LinearMap.aeval_self_charpoly]
  rfl

end GlobalTheory.HCKTypes
