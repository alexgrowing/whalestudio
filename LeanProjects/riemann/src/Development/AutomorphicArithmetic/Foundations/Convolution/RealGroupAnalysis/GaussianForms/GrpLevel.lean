import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ImportsAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NbBasis
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.TorusEq
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Place

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private theorem dv_mul {F : Type} [Field F] [NumberField F] {m n : F} {x y : A F}
    (hx : Dv m x) (hy : Dv n y) : Dv (m * n) (x * y) := fun v => by
  have h : Valued.v ((x * y).2 v) = Valued.v (x.2 v) * Valued.v (y.2 v) := by
    change Valued.v (x.2 v * y.2 v) = _
    exact map_mul _ _ _
  rw [h, map_mul]
  exact mul_le_mul' (hx v) (hy v)

private theorem dv_add {F : Type} [Field F] [NumberField F] {m : F} {x y : A F}
    (hx : Dv m x) (hy : Dv m y) : Dv m (x + y) := fun v => by
  change Valued.v (x.2 v + y.2 v) ≤ _
  exact Valuation.map_add_le _ (hx v) (hy v)

private theorem dv_neg {F : Type} [Field F] [NumberField F] {m : F} {x : A F}
    (hx : Dv m x) : Dv m (-x) := fun v => by
  change Valued.v (-(x.2 v)) ≤ _
  rw [Valuation.map_neg]
  exact hx v

private theorem dv_zero {F : Type} [Field F] [NumberField F] (m : F) : Dv m (0 : A F) := fun v => by
  change Valued.v (0 : v.adicCompletion F) ≤ _
  rw [map_zero]
  exact zero_le'

private theorem dv_one {F : Type} [Field F] [NumberField F] : Dv 1 (1 : A F) := fun v => by
  change Valued.v (1 : v.adicCompletion F) ≤ _
  rw [map_one, map_one]

private theorem val_le_one {F : Type} [Field F] [NumberField F] {m : F} (hm : Dv 1 (rt m))
    (v : HeightOneSpectrum (𝓞 F)) : v.valuation F m ≤ 1 := by
  have h := hm v
  rw [map_one] at h
  have h2 : Valued.v ((rt m : A F).2 v) = v.valuation F m :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v m
  rwa [h2] at h

private theorem dv_weaken {F : Type} [Field F] [NumberField F] {m n : F} {x : A F}
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F m ≤ v.valuation F n) (hx : Dv m x) : Dv n x :=
  fun v => (hx v).trans (h v)

private theorem unit_alt {F : Type} [Field F] [NumberField F] (g : G1 F)
    (h00 : Dv 1 (g 0 0)) (h01 : Dv 1 (g 0 1)) (h10 : Dv 1 (g 1 0)) (h11 : Dv 1 (g 1 1))
    (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((g 1 0).2 v) = 1 ∨ Valued.v ((g 1 1).2 v) = 1 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hc, hd⟩ := hcon
  have le1 : ∀ {x : A F}, Dv 1 x → Valued.v (x.2 v) ≤ 1 := fun {x} hx => by
    have := hx v
    rwa [map_one] at this
  have hc' := lt_of_le_of_ne (le1 h10) hc
  have hd' := lt_of_le_of_ne (le1 h11) hd
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have h := g.det_coe
    rwa [Matrix.det_fin_two] at h
  have hloc : (g 0 0).2 v * (g 1 1).2 v - (g 0 1).2 v * (g 1 0).2 v = 1 := by
    have := congrArg (fun x : A F => x.2 v) hdet
    exact this
  have h1 : Valued.v ((g 0 0).2 v * (g 1 1).2 v) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (le1 h00)) hd'
  have h2 : Valued.v ((g 0 1).2 v * (g 1 0).2 v) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (le1 h01)) hc'
  have h3 := Valuation.map_sub_lt _ h1 h2
  rw [hloc, map_one] at h3
  exact lt_irrefl _ h3

theorem UpperTheory.ConvolutionTheory.R2.C.grpLevel :
    ∀ (F : Type) [Field F] [NumberField F] (H : Subgroup (G1 F)), (∀ᶠ b in 𝓝 (0 : A F), b.1 = 0 → nU b ∈ H ∧ wW F * nU b * (wW F)⁻¹ ∈ H) → ∀ᶠ g in 𝓝 (1 : G1 F), InfOne g → g ∈ H := by
  intro F _ _ H hH
  obtain ⟨hb1, hb2⟩ := nbBasis F
  obtain ⟨m, hm0, hm1, hmU⟩ := hb1 _ hH
  have hm := val_le_one hm1
  have hsq : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (m ^ 2) ≤ v.valuation F m := fun v => by
    rw [map_pow, pow_two]
    exact mul_le_of_le_one_left' (hm v)
  have hone : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F m ≤ v.valuation F 1 := fun v => by
    rw [map_one]
    exact hm v
  let R : Subring (A F) :=
    { carrier := {x | Dv 1 x}
      mul_mem' := fun {a b} ha hb => by
        have h := dv_mul ha hb
        rwa [one_mul] at h
      one_mem' := dv_one
      add_mem' := fun ha hb => dv_add ha hb
      zero_mem' := dv_zero 1
      neg_mem' := fun ha => dv_neg ha }
  let I : AddSubgroup (A F) :=
    { carrier := {x | x.1 = 0 ∧ Dv m x}
      add_mem' := fun {a b} ha hb => ⟨by
        change a.1 + b.1 = 0
        rw [ha.1, hb.1, add_zero], dv_add ha.2 hb.2⟩
      zero_mem' := ⟨rfl, dv_zero m⟩
      neg_mem' := fun {a} ha => ⟨by
        change -a.1 = 0
        rw [ha.1, neg_zero], dv_neg ha.2⟩ }
  have hRI : ∀ r ∈ R, ∀ x ∈ I, r * x ∈ I := fun r hr x hx => ⟨by
    change r.1 * x.1 = 0
    rw [hx.1, mul_zero], by
    have h := dv_mul hr hx.2
    rwa [one_mul] at h⟩
  have hI : ∀ b ∈ I, nU b ∈ H ∧ wW F * nU b * (wW F)⁻¹ ∈ H := fun b hb => hmU b hb.1 hb.2 hb.1
  have hev : ∀ i j, ∀ᶠ g in 𝓝 (1 : G1 F), Dv (m ^ 2) (g i j - (1 : Matrix (Fin 2) (Fin 2) (A F)) i j) := by
    intro i j
    have hc : Continuous fun g : G1 F => g i j - (1 : Matrix (Fin 2) (Fin 2) (A F)) i j :=
      (continuous_subtype_val.matrix_elem i j).sub continuous_const
    have ht : Tendsto (fun g : G1 F => g i j - (1 : Matrix (Fin 2) (Fin 2) (A F)) i j) (𝓝 1) (𝓝 0) := by
      have h := hc.tendsto 1
      simpa using h
    exact ht.eventually (hb2 _ (pow_ne_zero 2 hm0))
  filter_upwards [hev 0 0, hev 0 1, hev 1 0, hev 1 1] with g h00 h01 h10 h11 hinf
  have e00 : g 0 0 - 1 = g 0 0 - (1 : Matrix (Fin 2) (Fin 2) (A F)) 0 0 := by simp
  have e01 : g 0 1 = g 0 1 - (1 : Matrix (Fin 2) (Fin 2) (A F)) 0 1 := by simp
  have e10 : g 1 0 = g 1 0 - (1 : Matrix (Fin 2) (Fin 2) (A F)) 1 0 := by simp
  have e11 : g 1 1 - 1 = g 1 1 - (1 : Matrix (Fin 2) (Fin 2) (A F)) 1 1 := by simp
  rw [← e00] at h00
  rw [← e01] at h01
  rw [← e10] at h10
  rw [← e11] at h11
  have toOne : ∀ {x : A F}, Dv (m ^ 2) x → Dv 1 x := fun hx =>
    dv_weaken hone (dv_weaken hsq hx)
  have d00 : Dv 1 (g 0 0) := by
    have h := dv_add (toOne h00) dv_one
    rwa [sub_add_cancel] at h
  have d11 : Dv 1 (g 1 1) := by
    have h := dv_add (toOne h11) dv_one
    rwa [sub_add_cancel] at h
  have c0 : (g 1 0).1 = 0 := by simpa using hinf 1 0
  have c1 : (g 0 1).1 = 0 := by simpa using hinf 0 1
  have d1 : (g 1 1).1 = 1 := by
    have h : (g 1 1).1 = (1 : A F).1 := by simpa using hinf 1 1
    exact h
  obtain ⟨u, ε, x, y, hu, hui, hε, hx, hy, e1, e2⟩ :=
    lvEps F m hm0 hm1 (g 1 0) (g 1 1) c0 d1 (toOne h10) h11
      (unit_alt g d00 (toOne h01) (toOne h10) d11)
  exact lvAlg F H R I hRI hI g u d00 ⟨c1, dv_weaken hsq h01⟩ ⟨c0, dv_weaken hsq h10⟩ hu hui
    ε hε x hx y hy e1 e2
