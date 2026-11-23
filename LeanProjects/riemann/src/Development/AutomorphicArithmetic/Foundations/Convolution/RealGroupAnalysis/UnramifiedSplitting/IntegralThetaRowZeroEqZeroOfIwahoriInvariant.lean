import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.HatSt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.WWMulCube
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SlZero
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Imports
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.RightInv
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.JExExists
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SgLaws
import GroundTheory.HeightsAndTheta.Theta.Weil.PartialFourierAdelicPi
import GroundTheory.HeightsAndTheta.Theta.AdelicFourierCoord

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

noncomputable section

namespace UpperTheory.ConvolutionTheory.R2.H.T0

variable {F : Type} [Field F] [NumberField F]

private theorem comp_signed_mem {ι κ : Type} [Fintype ι] [Fintype κ] (e : κ ≃ ι) (ε : κ → F)
    (hε : ∀ k, ε k * ε k = 1) {G : (κ → A F) → ℂ} (hG : G ∈ schwartzBruhatPi F κ) :
    (fun x : ι → A F => G fun k => rt (ε k) * x (e k)) ∈ schwartzBruhatPi F ι := by
  have hD : Matrix.diagonal ε * Matrix.diagonal ε = (1 : Matrix κ κ F) := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    exact hε k
  let M : Matrix κ ι F := (Matrix.diagonal ε).submatrix id e.symm
  let N : Matrix ι κ F := (Matrix.diagonal ε).submatrix e.symm id
  have hNM : N * M = 1 := by
    have h := Matrix.submatrix_mul (Matrix.diagonal ε) (Matrix.diagonal ε) e.symm id e.symm
      Function.bijective_id
    rw [hD, Matrix.submatrix_one_equiv] at h
    exact h.symm
  have hMN : M * N = 1 := by
    have h := Matrix.submatrix_mul (Matrix.diagonal ε) (Matrix.diagonal ε) id e.symm id
      e.symm.bijective
    rw [hD, Matrix.submatrix_id_id] at h
    exact h.symm
  have h := GroundTheory.Heights₂.Theta.comp_mulVec_mem_schwartzBruhatPi M N hNM hMN hG
  have hx : ∀ x : ι → A F, (M.map (algebraMap F (A F)) *ᵥ x) = fun k => rt (ε k) * x (e k) := by
    intro x
    funext k
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, M, Matrix.submatrix_apply, id]
    rw [← e.sum_comp]
    simp only [Matrix.diagonal_apply]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  simpa only [hx] using h

private def eS : Fin 3 ⊕ Unit ≃ Fin 4 where
  toFun := Sum.elim ![0, 2, 3] fun _ => 1
  invFun := ![.inl 0, .inr (), .inl 1, .inl 2]
  left_inv := by
    rintro (i | ⟨⟩)
    · fin_cases i <;> rfl
    · rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

private def sn : Fin 3 ⊕ Unit → F := Sum.elim 1 fun _ => -1

private def FF (φ : V4 F → ℂ) (z : Fin 3 ⊕ Unit → A F) : ℂ := φ fun i => z (eS.symm i)

private theorem FF_mem {φ : V4 F → ℂ} (hφ : φ ∈ schwartzBruhatPi F (Fin 4)) :
    FF φ ∈ schwartzBruhatPi F (Fin 3 ⊕ Unit) := by
  have h := comp_signed_mem (F := F) eS.symm (fun _ => 1) (fun _ => by simp) hφ
  have he : FF φ = fun x => φ fun k => rt ((fun _ => 1 : Fin 4 → F) k) * x (eS.symm k) := by
    funext x
    simp [FF]
  rw [he]
  exact h

private theorem hat_eq (φ : V4 F → ℂ) (x : V4 F) :
    hat φ x = GroundTheory.Heights₂.Theta.partialFourierPi (FF φ) fun k => rt (sn k) * x (eS k) := by
  have hmp := measurePreserving_funUnique (adeleMeasure F) Unit
  have h := hmp.integral_comp' (g := fun s => φ (Function.update x 1 s) * ψ (-(s * x 1)))
  rw [hat, ← h, GroundTheory.Heights₂.Theta.partialFourierPi, adelicFourierPi, adeleMeasurePi]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have h1 : Function.update x 1 (MeasurableEquiv.funUnique Unit (A F) y) =
      fun i => (Sum.elim (fun i => rt (sn (Sum.inl i)) * x (eS (Sum.inl i))) y
        : Fin 3 ⊕ Unit → A F) (eS.symm i) := by
    funext i
    fin_cases i <;> simp [eS, sn]
  have h2 : ψ (-(MeasurableEquiv.funUnique Unit (A F) y * x 1)) =
      ((adelicChar F (∑ i, y i * (rt (sn (Sum.inr i)) * x (eS (Sum.inr i)))) : Circle) : ℂ) := by
    simp [ψ, eS, sn]
  simp only [FF]
  rw [h1, h2]

private theorem hat_add {a b : V4 F → ℂ} (ha : a ∈ schwartzBruhatPi F (Fin 4))
    (hb : b ∈ schwartzBruhatPi F (Fin 4)) (x : V4 F) : hat (a + b) x = hat a x + hat b x := by
  rw [hat_eq, hat_eq, hat_eq]
  have e : FF (a + b) = FF a + FF b := rfl
  rw [e]
  exact congrFun (adelicFourierPi_add
    (GroundTheory.Heights₂.Theta.integrable_partialFourierPi_slice (FF_mem ha) _)
    (GroundTheory.Heights₂.Theta.integrable_partialFourierPi_slice (FF_mem hb) _)) _

private theorem row_summable (χ : S4 F) :
    Summable fun ξ : Fin 2 → F => hat χ.1 ![0, 0, rt (ξ 0), rt (ξ 1)] := by
  have h := (poisson_of_mem_schwartzBruhatPi (UpperTheory.ConvolutionTheory.R2.D.hatMem F χ).1).1
  have hinj : Function.Injective (fun ξ : Fin 2 → F => (![0, 0, ξ 0, ξ 1] : Fin 4 → F)) := by
    intro a b hab
    funext i
    fin_cases i
    · exact congrFun hab 2
    · exact congrFun hab 3
  refine (h.of_norm.comp_injective hinj).congr fun ξ => ?_
  simp only [Function.comp]
  congr 1
  funext i
  fin_cases i <;> simp

private theorem thRow_add (a b : S4 F) :
    ThRow 0 0 (a + b : S4 F).1 = ThRow 0 0 a.1 + ThRow 0 0 b.1 := by
  unfold ThRow
  rw [← (row_summable a).tsum_add (row_summable b)]
  refine tsum_congr fun ξ => ?_
  exact hat_add a.2 b.2 _

private theorem thRow_zero : ThRow 0 0 (0 : S4 F).1 = 0 := by
  unfold ThRow hat
  simp

private theorem thRow_sum {ι : Type} (s : Finset ι) (c : ι → S4 F) :
    ThRow 0 0 (∑ k ∈ s, c k : S4 F).1 = ∑ k ∈ s, ThRow 0 0 (c k).1 := by
  induction s using Finset.induction_on with
  | empty => simpa using thRow_zero
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, thRow_add, ih]

private theorem int_add {v : P F} {x y : Kv v} (hx : IsInt x) (hy : IsInt y) : IsInt (x + y) :=
  (Valuation.map_add _ x y).trans (max_le hx hy)

private theorem int_mul {v : P F} {x y : Kv v} (hx : IsInt x) (hy : IsInt y) : IsInt (x * y) := by
  unfold IsInt at *
  rw [map_mul]
  exact mul_le_one' hx hy

private theorem int_neg {v : P F} {x : Kv v} (hx : IsInt x) : IsInt (-x) := by
  unfold IsInt at *
  rwa [Valuation.map_neg]

private theorem int_one {v : P F} : IsInt (1 : Kv v) := by
  unfold IsInt
  rw [map_one]

private theorem int_zero {v : P F} : IsInt (0 : Kv v) := by
  unfold IsInt
  rw [map_zero]
  exact zero_le'

private def KP (v : P F) (ϖ : (Kv v)ˣ) : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Kv v)) where
  carrier := {x | IsInt (x 0 0) ∧ IsInt (x 1 1) ∧ IsInt (((ϖ⁻¹ : (Kv v)ˣ) : Kv v) * x 0 1) ∧
    IsInt ((ϖ : Kv v) * x 1 0)}
  mul_mem' := by
    rintro x y ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩
    have hu : (((ϖ⁻¹ : (Kv v)ˣ) : Kv v)) * (ϖ : Kv v) = 1 := Units.inv_mul ϖ
    have e00 : (x * y) 0 0 = x 0 0 * y 0 0 +
        (((ϖ⁻¹ : (Kv v)ˣ) : Kv v) * x 0 1) * ((ϖ : Kv v) * y 1 0) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
        mul_mul_mul_comm _ (x 0 1), hu, one_mul]
    have e11 : (x * y) 1 1 = ((ϖ : Kv v) * x 1 0) * (((ϖ⁻¹ : (Kv v)ˣ) : Kv v) * y 0 1) +
        x 1 1 * y 1 1 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
        mul_mul_mul_comm _ (x 1 0), mul_comm (ϖ : Kv v), hu, one_mul]
    have e01 : ((ϖ⁻¹ : (Kv v)ˣ) : Kv v) * (x * y) 0 1 =
        x 0 0 * (((ϖ⁻¹ : (Kv v)ˣ) : Kv v) * y 0 1) + (((ϖ⁻¹ : (Kv v)ˣ) : Kv v) * x 0 1) * y 1 1 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    have e10 : (ϖ : Kv v) * (x * y) 1 0 =
        ((ϖ : Kv v) * x 1 0) * y 0 0 + x 1 1 * ((ϖ : Kv v) * y 1 0) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e00]; exact int_add (int_mul a a') (int_mul c d')
    · rw [e11]; exact int_add (int_mul d c') (int_mul b b')
    · rw [e01]; exact int_add (int_mul a c') (int_mul c b')
    · rw [e10]; exact int_add (int_mul d a') (int_mul b d')
  one_mem' := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [int_one, int_zero]
  inv_mem' := by
    rintro x ⟨a, b, c, d⟩
    have e : ((x⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (Kv v)) : Matrix (Fin 2) (Fin 2) (Kv v)) =
        !![x 1 1, -x 0 1; -x 1 0, x 0 0] := by
      rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e]; simpa using b
    · rw [e]; simpa using a
    · rw [e]; simpa using int_neg c
    · rw [e]; simpa using int_neg d

private theorem ball_compact (v : P F) (c : (Kv v)ˣ) : IsCompact {x : Kv v | IsInt ((c : Kv v) * x)} := by
  have hO : IsCompact (v.adicCompletionIntegers F : Set (Kv v)) :=
    isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace (v.adicCompletionIntegers F)))
  have e : {x : Kv v | IsInt ((c : Kv v) * x)} =
      (fun y => ((c⁻¹ : (Kv v)ˣ) : Kv v) * y) '' (v.adicCompletionIntegers F : Set (Kv v)) := by
    ext x
    constructor
    · intro hx
      exact ⟨(c : Kv v) * x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      have : IsInt y := hy
      simpa [Set.mem_setOf_eq] using this
  rw [e]
  exact hO.image (continuous_const.mul continuous_id)

private theorem kp_compact (v : P F) (ϖ : (Kv v)ˣ) : CompactSpace (KP v ϖ) := by
  let cc : Fin 2 → Fin 2 → (Kv v)ˣ := ![![1, ϖ⁻¹], ![ϖ, 1]]
  let C : Set (Matrix (Fin 2) (Fin 2) (Kv v)) :=
    Set.pi Set.univ fun i => Set.pi Set.univ fun k => {x : Kv v | IsInt ((cc i k : Kv v) * x)}
  have hC : IsCompact C := isCompact_univ_pi fun i => isCompact_univ_pi fun k => ball_compact v _
  have hcl : IsClosed {A : Matrix (Fin 2) (Fin 2) (Kv v) | A.det = 1} :=
    isClosed_eq (Continuous.matrix_det continuous_id) continuous_const
  have hemb : Topology.IsClosedEmbedding
      (Subtype.val : Matrix.SpecialLinearGroup (Fin 2) (Kv v) → Matrix (Fin 2) (Fin 2) (Kv v)) :=
    hcl.isClosedEmbedding_subtypeVal
  have hK : IsCompact ((KP v ϖ : Subgroup _) : Set (Matrix.SpecialLinearGroup (Fin 2) (Kv v))) := by
    have e : ((KP v ϖ : Subgroup _) : Set (Matrix.SpecialLinearGroup (Fin 2) (Kv v))) = Subtype.val ⁻¹' C := by
      ext x
      constructor
      · rintro ⟨a, b, c, d⟩ i - k -
        fin_cases i <;> fin_cases k
        · show IsInt (((1 : (Kv v)ˣ) : Kv v) * x.1 0 0)
          rw [Units.val_one, one_mul]; exact a
        · exact c
        · exact d
        · show IsInt (((1 : (Kv v)ˣ) : Kv v) * x.1 1 1)
          rw [Units.val_one, one_mul]; exact b
      · intro h
        have h00 : IsInt (((1 : (Kv v)ˣ) : Kv v) * x.1 0 0) := h 0 (Set.mem_univ _) 0 (Set.mem_univ _)
        have h11 : IsInt (((1 : (Kv v)ˣ) : Kv v) * x.1 1 1) := h 1 (Set.mem_univ _) 1 (Set.mem_univ _)
        rw [Units.val_one, one_mul] at h00 h11
        exact ⟨h00, h11, h 0 (Set.mem_univ _) 1 (Set.mem_univ _), h 1 (Set.mem_univ _) 0 (Set.mem_univ _)⟩
    rw [e]
    exact hemb.isCompact_preimage hC
  exact isCompact_iff_compactSpace.1 hK

private def nK {v : P F} (b : Kv v) : Matrix.SpecialLinearGroup (Fin 2) (Kv v) :=
  ⟨!![1, b; 0, 1], by simp [Matrix.det_fin_two]⟩

private def lK {v : P F} (c : Kv v) : Matrix.SpecialLinearGroup (Fin 2) (Kv v) :=
  ⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two]⟩

private def lU (c : A F) : G1 F := ⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two]⟩

private theorem sg_zero (v : P F) : sg v (0 : Kv v) = 0 := by
  have h := (sgLaws F v).1 0 0
  simpa using h

private theorem sg_neg (v : P F) (x : Kv v) : sg v (-x) = -sg v x := by
  have h := (sgLaws F v).1 x (-x)
  rw [add_neg_cancel, sg_zero] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

private theorem w_conj (t : A F) : wW F * nU t * (wW F)⁻¹ = lU (-t) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  show (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) (A F)) * !![1, t; 0, 1] = !![1, 0; -t, 1] * !![0, 1; -1, 0]
  simp [Matrix.mul_fin_two]

end UpperTheory.ConvolutionTheory.R2.H.T0

end

open UpperTheory.ConvolutionTheory.R2.H.T0 in
theorem UpperTheory.ConvolutionTheory.R2.H.integral_thetaRowZero_eq_zero_of_iwahori_invariant :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (v : P F) (ϖ : (Kv v)ˣ), IsU ϖ → Gd D.δ v → Aniso D.δ v → ∀ j, IsJ v j →
      ∀ (f : G1 F → ℂ) (φ : S4 F), (∀ γ g, f (ratS F γ * g) = f g) →
      (∀ g (x : Matrix.SpecialLinearGroup (Fin 2) (Kv v)), IsInt (x 0 0) → IsInt (x 1 1) → IsInt (((ϖ⁻¹ : (Kv v)ˣ) : Kv v) * x 0 1) → IsInt ((ϖ : Kv v) * x 1 0) →
        f (g * j x) = f g) →
      IntegrableOn (fun g => f g * ThRow 0 0 (W.Om g φ).1) M.D M.μ → ∫ g in M.D, f g * ThRow 0 0 (W.Om g φ).1 ∂M.μ = 0 := by
  intro F E _ _ _ _ _ _ _ D W M v ϖ hϖ hGd hAn j hj f φ hfL hfR hint
  have hH : St.Hat W := hatSt F E D W
  obtain ⟨hjc, hAt, -, hent⟩ := (jEx F v).2 j hj
  let ρ : KP v ϖ →* Module.End ℂ (S4 F) := W.Om.comp (j.comp (KP v ϖ).subtype)
  haveI : CompactSpace (KP v ϖ) := kp_compact v ϖ
  have hρ : ∀ (k : KP v ϖ) (χ : S4 F), ρ k χ = W.Om (j k.1) χ := fun _ _ => rfl
  have hev : ∀ᶠ h in 𝓝 (1 : KP v ϖ), ρ h φ = φ := by
    have ht : Tendsto (fun h : KP v ϖ => j h.1) (𝓝 1) (𝓝 1) := by
      have h1 := (hjc.comp continuous_subtype_val).tendsto (1 : KP v ϖ)
      simp only [OneMemClass.coe_one, map_one, Function.comp_apply] at h1
      exact h1
    filter_upwards [ht.eventually (W.level φ)] with h hh
    exact hh (hAt h.1).1
  obtain ⟨s, hs, hfix⟩ := avg (KP v ϖ) (S4 F) ρ φ hev
  set φ₂ : S4 F := ∑ k ∈ s, ρ k φ with hφ₂
  have hnj : ∀ b : Kv v, j (nK b) = nU (sg v b) := by
    intro b
    apply Matrix.SpecialLinearGroup.ext
    intro i k
    rw [hent]
    fin_cases i <;> fin_cases k <;> simp [nK, nU, sg_zero]
  have hlj : ∀ c : Kv v, j (lK c) = lU (sg v c) := by
    intro c
    apply Matrix.SpecialLinearGroup.ext
    intro i k
    rw [hent]
    fin_cases i <;> fin_cases k <;> simp [lK, lU, sg_zero]
  have hn : ∀ b, IsInt b → W.Om (nU (sg v ((ϖ : Kv v) * b))) φ₂ = φ₂ := by
    intro b hb
    have hm : nK ((ϖ : Kv v) * b) ∈ KP v ϖ := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [nK] using int_one
      · simpa [nK] using int_one
      · simpa [nK] using hb
      · simpa [nK] using int_zero
    have := hfix ⟨_, hm⟩
    rw [hρ] at this
    simpa only [hnj] using this
  have hw : ∀ c, IsInt c → W.Om (wW F * nU (sg v (((ϖ⁻¹ : (Kv v)ˣ) : Kv v) * c)) * (wW F)⁻¹) φ₂ = φ₂ := by
    intro c hc
    have hm : lK (-(((ϖ⁻¹ : (Kv v)ˣ) : Kv v) * c)) ∈ KP v ϖ := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [lK] using int_one
      · simpa [lK] using int_one
      · simpa [lK] using int_zero
      · simpa [lK] using int_neg hc
    have := hfix ⟨_, hm⟩
    rw [hρ] at this
    simp only [hlj, sg_neg] at this
    rw [w_conj]
    exact this
  have hker := slKer F E D W φ₂ (slZero F E D W v ϖ hϖ hGd hAn φ₂ hn hw)
  let u : G1 F → ℂ := fun g => f g * ThRow 0 0 (W.Om g φ).1
  have hu : ∀ γ g, u (ratS F γ * g) = u g := by
    intro γ g
    have h := hH.row γ 0 (W.Om g φ)
    simp only [Matrix.zero_vecMul, Pi.zero_apply, map_zero] at h
    show f (ratS F γ * g) * ThRow 0 0 (W.Om (ratS F γ * g) φ).1 = f g * ThRow 0 0 (W.Om g φ).1
    rw [hfL, map_mul, Module.End.mul_apply, h]
  have hk : ∀ (k : KP v ϖ) g, u (g * j k.1) = f g * ThRow 0 0 (W.Om g (ρ k φ)).1 := by
    intro k g
    obtain ⟨x, a, b, c, d⟩ := k
    show f (g * j x) * ThRow 0 0 (W.Om (g * j x) φ).1 = _
    rw [hfR g x a b c d, map_mul, Module.End.mul_apply]
    rfl
  have hz : ∀ g, ∑ k ∈ s, u (g * j k.1) = 0 := by
    intro g
    simp only [hk]
    rw [← Finset.mul_sum]
    have e : W.Om g φ₂ = ∑ k ∈ s, W.Om g (ρ k φ) := by rw [hφ₂, map_sum]
    have h := hker g
    rw [e, thRow_sum] at h
    rw [h, mul_zero]
  have hsum : ∑ k ∈ s, ∫ g in M.D, u (g * j k.1) ∂M.μ = 0 := by
    rw [← integral_finset_sum s fun k _ => (rightInv F M u hu hint (j k.1)).1]
    simp only [hz, integral_zero]
  have hcard : (s.card : ℂ) * ∫ g in M.D, u g ∂M.μ = 0 := by
    have e : ∀ k ∈ s, ∫ g in M.D, u (g * j k.1) ∂M.μ = ∫ g in M.D, u g ∂M.μ :=
      fun k _ => (rightInv F M u hu hint (j k.1)).2
    rw [Finset.sum_congr rfl e, Finset.sum_const, nsmul_eq_mul] at hsum
    exact hsum
  have hne : (s.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 hs)
  exact (mul_eq_zero.1 hcard).resolve_left hne
