import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ThickFrames

noncomputable section

open NumberField IsDedekindDomain ValuativeRel
open GroundTheory.Automorphic GroundTheory.Global GroundTheory.Global.SemiLocal PositivityTheory.Rg.Tf.Geo

namespace UpperTheory.ConvolutionTheory.L1

section Unif

variable (A : Type*) [Field A] [ValuativeRel A] [TopologicalSpace A] [IsNonarchimedeanLocalField A]

private theorem val_le_unif {x : A} (hx : valuation A x < 1) :
    valuation A x ≤ valuation A (GLnLocal.uniformizer A : A) := by
  let y : 𝒪[A] := ⟨x, (Valuation.mem_integer_iff _ _).2 hx.le⟩
  have hy : y ∈ IsLocalRing.maximalIdeal 𝒪[A] ^ 1 := by
    rw [pow_one, ← IsLocalRing.residue_eq_zero_iff]
    exact (GLnLocal.residue_eq_zero_iff_valuation_lt_one A y).2 hx
  simpa using (GLnLocal.mem_maximalIdeal_pow_iff A (m := 1)).1 hy

end Unif

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : Pl F) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]

private theorem ef_eq_one (hs : Function.Surjective (completionMap v w)) :
    w.asIdeal.ramificationIdx (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 F) = 1 := by
  rw [← finrank_eq_ramificationIdx_mul_inertiaDeg E v w]
  have hb : Function.Bijective (Algebra.linearMap (v.adicCompletion F) (w.adicCompletion E)) :=
    ⟨(completionMap v w).injective, hs⟩
  rw [← (LinearEquiv.ofBijective _ hb).finrank_eq, Module.finrank_self]

private theorem val_map (hs : Function.Surjective (completionMap v w)) (x : v.adicCompletion F) :
    Valued.v (completionMap v w x) = Valued.v x := by
  have h := ef_eq_one v w hs
  have he : w.asIdeal.ramificationIdx (𝓞 F) = 1 := Nat.eq_one_of_mul_eq_one_right h
  rw [valued_completionMap, he, pow_one]

private theorem le_iff (hs : Function.Surjective (completionMap v w)) (x : v.adicCompletion F) :
    valuation (w.adicCompletion E) (completionMap v w x) ≤ 1 ↔ valuation (v.adicCompletion F) x ≤ 1 := by
  rw [(ValuativeRel.isEquiv (valuation (w.adicCompletion E)) Valued.v).le_one_iff_le_one,
    (ValuativeRel.isEquiv (valuation (v.adicCompletion F)) Valued.v).le_one_iff_le_one, val_map v w hs]

private theorem lt_iff (hs : Function.Surjective (completionMap v w)) (x : v.adicCompletion F) :
    valuation (w.adicCompletion E) (completionMap v w x) < 1 ↔ valuation (v.adicCompletion F) x < 1 := by
  rw [(ValuativeRel.isEquiv (valuation (w.adicCompletion E)) Valued.v).lt_one_iff_lt_one,
    (ValuativeRel.isEquiv (valuation (v.adicCompletion F)) Valued.v).lt_one_iff_lt_one, val_map v w hs]

private theorem eq_iff (hs : Function.Surjective (completionMap v w)) (x : v.adicCompletion F) :
    valuation (w.adicCompletion E) (completionMap v w x) = 1 ↔ valuation (v.adicCompletion F) x = 1 := by
  rw [(ValuativeRel.isEquiv (valuation (w.adicCompletion E)) Valued.v).eq_one_iff_eq_one,
    (ValuativeRel.isEquiv (valuation (v.adicCompletion F)) Valued.v).eq_one_iff_eq_one, val_map v w hs]

private theorem val_unif (hs : Function.Surjective (completionMap v w)) :
    Valued.v (completionMap v w (GLnLocal.uniformizer (v.adicCompletion F) : v.adicCompletion F)) =
      Valued.v (GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E) := by
  obtain ⟨y, hy⟩ := hs (GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E)
  have hB := GLnLocal.valuation_uniformizer_lt_one (w.adicCompletion E)
  have hA := GLnLocal.valuation_uniformizer_lt_one (v.adicCompletion F)
  apply le_antisymm
  · have := val_le_unif (w.adicCompletion E) ((lt_iff v w hs _).2 hA)
    exact (ValuativeRel.isEquiv (valuation (w.adicCompletion E)) Valued.v).le_iff_le.1 this
  · rw [← hy, val_map v w hs, val_map v w hs]
    have hy1 : valuation (v.adicCompletion F) y < 1 := by
      rw [← lt_iff v w hs, hy]; exact hB
    have := val_le_unif (v.adicCompletion F) hy1
    exact (ValuativeRel.isEquiv (valuation (v.adicCompletion F)) Valued.v).le_iff_le.1 this

private theorem cont_symm (hs : Function.Surjective (completionMap v w))
    (φ : v.adicCompletion F ≃+* w.adicCompletion E) (hφ : ∀ x, φ x = completionMap v w x) :
    Continuous φ.symm := by
  refine continuous_of_continuousAt_zero φ.symm.toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  refine ((IsValuativeTopology.hasBasis_nhds_zero (w.adicCompletion E)).tendsto_iff
    (IsValuativeTopology.hasBasis_nhds_zero (v.adicCompletion F))).2 ?_
  intro γ _
  obtain ⟨c, hc⟩ : ∃ c, valuation (v.adicCompletion F) c = (γ : ValueGroupWithZero (v.adicCompletion F)) := by
    exact ValuativeRel.valuation_surjective (γ : ValueGroupWithZero (v.adicCompletion F))
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact γ.ne_zero hc.symm
  refine ⟨Units.mk0 (valuation (w.adicCompletion E) (φ c))
    ((Valuation.ne_zero_iff _).2 ((map_ne_zero φ).2 hc0)), trivial, fun x hx => ?_⟩
  have hx' : valuation (w.adicCompletion E) x < valuation (w.adicCompletion E) (φ c) := hx
  have h2 := (ValuativeRel.isEquiv (valuation (w.adicCompletion E)) Valued.v).lt_iff_lt.1 hx'
  have h1 : Valued.v (φ.symm x) = Valued.v x := by
    rw [← val_map v w hs, ← hφ, RingEquiv.apply_symm_apply]
  rw [hφ, val_map v w hs, ← h1] at h2
  change valuation (v.adicCompletion F) (φ.symm x) < γ
  rw [← hc]
  exact (ValuativeRel.isEquiv (valuation (v.adicCompletion F)) Valued.v).lt_iff_lt.2 h2

variable (n : ℕ)

private theorem map_inj : Function.Injective (mapGL n (completionMap v w)) := fun a b h =>
  Units.ext (Matrix.ext fun i j => (completionMap v w).injective
    (congrArg (fun g : GL (Fin n) (w.adicCompletion E) => g i j) h))

private theorem integral_iff (hs : Function.Surjective (completionMap v w)) (g : GL (Fin n) (v.adicCompletion F)) :
    mapGL n (completionMap v w) g ∈ GLnLocal.integralGL (w.adicCompletion E) n ↔
      g ∈ GLnLocal.integralGL (v.adicCompletion F) n := by
  rw [GLnLocal.mem_integralGL_iff, GLnLocal.mem_integralGL_iff, ← map_inv]
  simp only [Valuation.mem_integer_iff]
  exact and_congr (forall₂_congr fun i j => le_iff v w hs _) (forall₂_congr fun i j => le_iff v w hs _)

private theorem iw_iff (hs : Function.Surjective (completionMap v w)) (g : GL (Fin n) (v.adicCompletion F)) :
    mapGL n (completionMap v w) g ∈ GLnLocal.iwahori (w.adicCompletion E) n ↔
      g ∈ GLnLocal.iwahori (v.adicCompletion F) n := by
  rw [GLnLocal.mem_iwahori_iff, GLnLocal.mem_iwahori_iff]
  exact and_congr (forall₂_congr fun i j => le_iff v w hs _)
    (and_congr (forall₂_congr fun i j => forall_congr' fun _ => lt_iff v w hs _)
      (forall_congr' fun i => eq_iff v w hs _))

private theorem diag_fac (hs : Function.Surjective (completionMap v w)) (ν : Fin n → ℤ) :
    ∃ d ∈ GLnLocal.iwahori (w.adicCompletion E) n, Cartan.diagPow (w.adicCompletion E) n ν =
      mapGL n (completionMap v w) (Cartan.diagPow (v.adicCompletion F) n ν) * d := by
  set a : w.adicCompletion E :=
    completionMap v w (GLnLocal.uniformizer (v.adicCompletion F) : v.adicCompletion F) with ha
  set b : w.adicCompletion E := (GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E) with hb
  have ha0 : a ≠ 0 := (map_ne_zero _).2 (Cartan.uniformizer_ne_zero (v.adicCompletion F))
  have hb0 : b ≠ 0 := Cartan.uniformizer_ne_zero (w.adicCompletion E)
  have hu : valuation (w.adicCompletion E) (b / a) = 1 := by
    rw [(ValuativeRel.isEquiv (valuation (w.adicCompletion E)) Valued.v).eq_one_iff_eq_one, map_div₀, ha,
      val_unif v w hs, div_self ((Valuation.ne_zero_iff _).2 hb0)]
  have hz : ∀ k : ℤ, valuation (w.adicCompletion E) ((b / a) ^ k) = 1 := fun k => by
    rw [map_zpow₀, hu, one_zpow]
  obtain ⟨x, hx, hxm⟩ := GLnLocal.exists_mem_iwahori (w.adicCompletion E) n
    (Matrix.diagonal fun i => (b / a) ^ ν i)
    (fun i j => by
      by_cases h : i = j
      · subst h; rw [Matrix.diagonal_apply_eq]; exact (hz _).le
      · rw [Matrix.diagonal_apply_ne _ h, map_zero]; exact zero_le')
    (fun i j hij => by
      rw [Matrix.diagonal_apply_ne _ hij.ne', map_zero]; exact zero_lt_one)
    (fun i => by rw [Matrix.diagonal_apply_eq]; exact hz _)
  refine ⟨x, hx, Units.ext ?_⟩
  have hm : ((mapGL n (completionMap v w) (Cartan.diagPow (v.adicCompletion F) n ν) : GL (Fin n) (w.adicCompletion E)) :
      Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.diagonal fun i => a ^ ν i := by
    change (Cartan.diagPow (v.adicCompletion F) n ν : Matrix (Fin n) (Fin n) (v.adicCompletion F)).map (completionMap v w) = _
    rw [Cartan.coe_diagPow, Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    simp only [Function.comp_apply, map_zpow₀, ha]
  rw [Units.val_mul, hxm, hm, Cartan.coe_diagPow, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [← mul_zpow, mul_div_cancel₀ _ ha0]

private theorem coset_iff (hs : Function.Surjective (completionMap v w)) (ν : Fin n → ℤ)
    (hsurj : Function.Surjective (mapGL n (completionMap v w))) (g : GL (Fin n) (v.adicCompletion F)) :
    mapGL n (completionMap v w) g ∈ GM.iwCoset w ν ↔ g ∈ GM.iwCoset v ν := by
  obtain ⟨d, hd, hD⟩ := diag_fac v w n hs ν
  constructor
  · rintro ⟨a, ha, b, hb, h⟩
    obtain ⟨a', rfl⟩ := hsurj a
    obtain ⟨b', hb'⟩ := hsurj (d * b)
    refine ⟨a', (iw_iff v w n hs _).1 ha, b', (iw_iff v w n hs _).1 (hb' ▸ mul_mem hd hb), map_inj v w n ?_⟩
    rw [h, map_mul, map_mul, hb', hD]
    simp only [mul_assoc]
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨mapGL n (completionMap v w) a, (iw_iff v w n hs _).2 ha, d⁻¹ * mapGL n (completionMap v w) b,
      mul_mem (inv_mem hd) ((iw_iff v w n hs _).2 hb), ?_⟩
    rw [map_mul, map_mul, hD]
    simp only [mul_assoc, mul_inv_cancel_left]

private theorem norm_eq (hs : Function.Surjective (completionMap v w)) :
    Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal := by
  have hf : w.asIdeal.inertiaDeg (𝓞 F) = 1 := Nat.eq_one_of_mul_eq_one_left (ef_eq_one v w hs)
  have h := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal v.asIdeal v.isPrime v.ne_bot
  rw [h, Ideal.inertiaDeg'_eq_inertiaDeg, hf, pow_one]

private theorem main (hs : Function.Surjective (completionMap v w)) :
    (∃ e : GL (Fin n) (v.adicCompletion F) ≃ₜ* GL (Fin n) (w.adicCompletion E),
      ∀ g, e g = mapGL n (completionMap v w) g) ∧
    (∀ g, mapGL n (completionMap v w) g ∈ GLnLocal.integralGL (w.adicCompletion E) n ↔
      g ∈ GLnLocal.integralGL (v.adicCompletion F) n) ∧
    (∀ g, mapGL n (completionMap v w) g ∈ GLnLocal.iwahori (w.adicCompletion E) n ↔
      g ∈ GLnLocal.iwahori (v.adicCompletion F) n) ∧
    (∀ ν g, mapGL n (completionMap v w) g ∈ GM.iwCoset w ν ↔ g ∈ GM.iwCoset v ν) ∧
    Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal := by
  let φ : v.adicCompletion F ≃+* w.adicCompletion E :=
    RingEquiv.ofBijective (completionMap v w) ⟨(completionMap v w).injective, hs⟩
  have hφ : ∀ x, φ x = completionMap v w x := fun _ => rfl
  have hc : Continuous (completionMap v w) := continuous_completionMap v w
  have hc' : Continuous φ.symm := cont_symm v w hs φ hφ
  have hl : ∀ g, mapGL n (φ.symm : w.adicCompletion E →+* v.adicCompletion F) (mapGL n (completionMap v w) g) = g :=
    fun g => Units.ext (Matrix.ext fun i j => φ.symm_apply_apply _)
  have hr : ∀ g, mapGL n (completionMap v w) (mapGL n (φ.symm : w.adicCompletion E →+* v.adicCompletion F) g) = g :=
    fun g => Units.ext (Matrix.ext fun i j => φ.apply_symm_apply _)
  have hsurj : Function.Surjective (mapGL n (completionMap v w)) := fun y => ⟨_, hr y⟩
  refine ⟨⟨{ toFun := mapGL n (completionMap v w)
             invFun := mapGL n (φ.symm : w.adicCompletion E →+* v.adicCompletion F)
             left_inv := hl
             right_inv := hr
             map_mul' := map_mul _
             continuous_toFun := Units.continuous_iff.2
               ⟨Units.continuous_val.matrix_map hc, Units.continuous_coe_inv.matrix_map hc⟩
             continuous_invFun := Units.continuous_iff.2
               ⟨Units.continuous_val.matrix_map hc', Units.continuous_coe_inv.matrix_map hc'⟩ },
      fun _ => rfl⟩, integral_iff v w n hs, iw_iff v w n hs, fun ν => coset_iff v w n hs ν hsurj,
    norm_eq v w hs⟩

end Main

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.splitLoc :
    UpperTheory.ConvolutionTheory.L1.SplitLoc := by
  intro F E _ _ _ _ _ v w hs n
  exact UpperTheory.ConvolutionTheory.L1.main v w.1 n hs
