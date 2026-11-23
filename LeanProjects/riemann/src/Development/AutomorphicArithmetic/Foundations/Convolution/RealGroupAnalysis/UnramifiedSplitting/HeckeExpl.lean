import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.SphDict
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.MemIffLocal
import GroundTheory.AutomorphicForms.MacdonaldHecke

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

section Cosets

open GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GLnLocal Iwasawa HeckeAlgebra
open scoped ValuativeRel

attribute [local instance] GroundTheory.Automorphic.Spherical.fintypeResidue

private theorem coset_sum {K : Type} [Field K] [NumberField K] (v : P K) (n : ℕ) {B : Multiset ℂˣ}
    {W : GL (Fin n) (Kv v) → ℂ} (hE : Eig v B W) {r : ℕ} (hr : r ≤ n) (g : GL (Fin n) (Kv v)) :
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∑ c : Pairs S → 𝓀[Kv v], W (g * gMat S c) =
      GlobalTheory.LFun.satEig (Formalism.UG.qV K v) n B r * W g := by
  obtain ⟨hK, hu, -, -⟩ := UpperTheory.V.Af.Smo.sphDict K n v
  borelize (GL (Fin n) (Kv v))
  let μ : Measure (GL (Fin n) (Kv v)) := Measure.haar
  have hf : ∀ g, ∀ k ∈ integralGL (Kv v) n, W (g * k) = W g := by
    rw [hK]
    exact hE.inv
  have hKp : (μ.real (integralGL (Kv v) n : Set (GL (Fin n) (Kv v))) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2
      (measureReal_compactOpen_pos μ (isCompact_integralGL _ n) (isOpen_integralGL _ n)).ne'
  have h1 := integral_minusculeHecke_mul (μ := μ) hf g r
  have hcs : HasCompactSupport fun x => (minusculeHecke μ r : HeckeAlgebra μ) x * W (g * x) := by
    refine HasCompactSupport.intro (isCompact_minusculeSet r) fun x hx => ?_
    simp only [minusculeHecke_apply, Set.indicator_of_notMem hx, zero_mul]
  have h2 := integral_eq_smul_finsum_coset μ (integralOpen (Kv v) n) (isCompact_integralGL _ n) hcs (fun x k hk => by
      rw [(HeckeAlgebraLevel.val_mem _ _ (minusculeHecke μ r) k hk x).2, ← mul_assoc, hf _ k hk])
  have h3 : ∑ᶠ c : GL (Fin n) (Kv v) ⧸ integralGL (Kv v) n,
      (minusculeSet (Kv v) n r).indicator (fun _ => (1 : ℂ)) c.out * W (g * c.out) =
        GlobalTheory.LFun.satEig (Formalism.UG.qV K v) n B r * W g := by
    rw [hK, ← UpperTheory.V.Af.Smo.tjSet UpperTheory.V.Af.Smo.sphDict K n v r hr]
    exact hE.eig _ hu r hr g
  rw [Complex.real_smul] at h2
  refine mul_left_cancel₀ hKp ?_
  rw [← h1, h2, ← h3]
  rfl

end Cosets

section Cosets2

open GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GLnLocal Iwasawa HeckeAlgebra
open scoped ValuativeRel

attribute [local instance] GroundTheory.Automorphic.Spherical.fintypeResidue

variable {K : Type} [Field K] [NumberField K]

private theorem dL_mul {v : P K} (a a' d d' : (Kv v)ˣ) : dL a d * dL a' d' = dL (a * a') (d * d') :=
  Units.ext (by ext i j; fin_cases i <;> fin_cases j <;> simp [dL])

private theorem dL_mem {v : P K} {a d : (Kv v)ˣ} (ha : Valued.v (a : Kv v) = 1) (hd : Valued.v (d : Kv v) = 1) :
    dL a d ∈ GlobalTheory.LFun.KGL v 2 := by
  obtain ⟨hK, -, -, -⟩ := UpperTheory.V.Af.Smo.sphDict K 2 v
  have e : ∀ x : Kv v, Valued.v x ≤ 1 → x ∈ (ValuativeRel.valuation (Kv v)).integer :=
    fun x hx => (GroundTheory.Global.mem_valuationInteger_iff v x).2 hx
  have ha' : Valued.v ((a⁻¹ : (Kv v)ˣ) : Kv v) = 1 := by simp [ha]
  have hd' : Valued.v ((d⁻¹ : (Kv v)ˣ) : Kv v) = 1 := by simp [hd]
  rw [← hK, mem_integralGL_iff]
  refine ⟨fun i j => e _ ?_, fun i j => e _ ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [dL, ha, hd]
  · change Valued.v ((!![((a⁻¹ : (Kv v)ˣ) : Kv v), 0; 0, ((d⁻¹ : (Kv v)ˣ) : Kv v)] : Matrix (Fin 2) (Fin 2) (Kv v)) i j) ≤ 1
    fin_cases i <;> fin_cases j <;> simp [ha, hd]

private noncomputable def pi0 (v : P K) : (Kv v)ˣ := Units.mk0 (GLnLocal.uniformizer (Kv v) : Kv v) (Cartan.uniformizer_ne_zero _)

private noncomputable def lf (v : P K) (a : 𝓀[Kv v]) : Kv v := ((residueLift (Kv v) a : 𝒪[Kv v]) : Kv v)

private theorem lf_inj (v : P K) : Function.Injective (lf v) := by
  intro a b h
  have : residueLift (Kv v) a = residueLift (Kv v) b := Subtype.ext h
  rw [← residue_residueLift (F := Kv v) a, this, residue_residueLift]

private def p0 : Pairs ({0} : Finset (Fin 2)) := ⟨(0, 1), by simp, by simp, by simp⟩

private instance : Unique (Pairs ({0} : Finset (Fin 2))) where
  default := p0
  uniq := by
    rintro ⟨⟨a, b⟩, ha, hb, hab⟩
    have key : ∀ b : Fin 2, b ≠ 0 → b = 1 := by decide
    obtain rfl : a = 0 := Finset.mem_singleton.1 ha
    obtain rfl : b = 1 := key b fun h => hb (Finset.mem_singleton.2 h)
    rfl

private instance : IsEmpty (Pairs ({1} : Finset (Fin 2))) where
  false := by
    rintro ⟨⟨a, b⟩, ha, hb, hab⟩
    fin_cases a <;> fin_cases b <;> simp_all

private instance : IsEmpty (Pairs (Finset.univ : Finset (Fin 2))) where
  false := by
    rintro ⟨⟨a, b⟩, ha, hb, hab⟩
    simp at hb

private theorem gMat_zero (v : P K) (c : Pairs ({0} : Finset (Fin 2)) → 𝓀[Kv v]) :
    gMat {0} c = nL (lf v (c default)) * dL (pi0 v) 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [gMat_apply]
  fin_cases i <;> fin_cases j <;> simp [cMat, lamS, nL, dL, pi0, lf]
  rfl

private theorem gMat_one (v : P K) (c : Pairs ({1} : Finset (Fin 2)) → 𝓀[Kv v]) :
    gMat {1} c = dL 1 (pi0 v) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [gMat_apply]
  fin_cases i <;> fin_cases j <;> simp [cMat, lamS, dL, pi0]

private theorem gMat_top (v : P K) (c : Pairs (Finset.univ : Finset (Fin 2)) → 𝓀[Kv v]) :
    gMat Finset.univ c = dL (pi0 v) (pi0 v) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [gMat_apply]
  fin_cases i <;> fin_cases j <;> simp [cMat, lamS, dL, pi0]

private theorem sum_one (v : P K) (f : GL (Fin 2) (Kv v) → ℂ) :
    ∑ S ∈ (Finset.univ : Finset (Fin 2)).powersetCard 1, ∑ c : Pairs S → 𝓀[Kv v], f (gMat S c) =
      ∑ a : 𝓀[Kv v], f (nL (lf v a) * dL (pi0 v) 1) + f (dL 1 (pi0 v)) := by
  rw [Finset.powersetCard_one, Finset.sum_map, Fin.sum_univ_two]
  simp only [Function.Embedding.coeFn_mk]
  congr 1
  · refine Fintype.sum_equiv (Equiv.funUnique (Pairs ({0} : Finset (Fin 2))) 𝓀[Kv v]) _ _ fun c => ?_
    rw [gMat_zero]
    rfl
  · rw [Fintype.sum_unique, gMat_one]

private theorem sum_two (v : P K) (f : GL (Fin 2) (Kv v) → ℂ) :
    ∑ S ∈ (Finset.univ : Finset (Fin 2)).powersetCard 2, ∑ c : Pairs S → 𝓀[Kv v], f (gMat S c) =
      f (dL (pi0 v) (pi0 v)) := by
  have hp : (Finset.univ : Finset (Fin 2)).powersetCard 2 = {Finset.univ} := by
    have := Finset.powersetCard_self (Finset.univ : Finset (Fin 2))
    rwa [Finset.card_univ, Fintype.card_fin] at this
  rw [hp, Finset.sum_singleton, Fintype.sum_unique, gMat_top]

private theorem sat_one (q : ℕ) (α β : ℂˣ) :
    GlobalTheory.LFun.satEig q 2 {α, β} 1 = (q : ℂ) ^ (1 / 2 : ℂ) * ((α : ℂ) + β) := by
  have : GlobalTheory.LFun.satEig q 2 {α, β} 1 = (q : ℂ) ^ ((((1 : ℕ) : ℂ) * (((2 : ℕ) : ℂ) - ((1 : ℕ) : ℂ))) / 2) * (Multiset.map (fun b : ℂˣ => (b : ℂ)) {α, β}).esymm 1 := rfl
  rw [this]
  norm_num [Multiset.esymm, Multiset.insert_eq_cons, Multiset.powersetCard_one]
  exact Or.inl (add_comm _ _)

private theorem sat_two (q : ℕ) (α β : ℂˣ) :
    GlobalTheory.LFun.satEig q 2 {α, β} 2 = (α : ℂ) * β := by
  have : GlobalTheory.LFun.satEig q 2 {α, β} 2 = (q : ℂ) ^ ((((2 : ℕ) : ℂ) * (((2 : ℕ) : ℂ) - ((2 : ℕ) : ℂ))) / 2) * (Multiset.map (fun b : ℂˣ => (b : ℂ)) {α, β}).esymm 2 := rfl
  rw [this]
  norm_num [Multiset.esymm, Multiset.insert_eq_cons, Multiset.powersetCard_cons, Multiset.powersetCard_one]

private theorem card_res (v : P K) : Fintype.card 𝓀[Kv v] = Ideal.absNorm v.asIdeal := by
  rw [← Nat.card_eq_fintype_card, GroundTheory.Global.natCard_residueField_integer, Ideal.absNorm_apply, Submodule.cardQuot_apply]

end Cosets2

section Main

attribute [local instance] GroundTheory.Automorphic.Spherical.fintypeResidue

theorem UpperTheory.ConvolutionTheory.R2.H.heckeExpl :
    ∀ (K : Type) [Field K] [NumberField K] (v : P K) (ϖ : (Kv v)ˣ), IsU ϖ → ∃ R : Finset (Kv v), R.card = Ideal.absNorm v.asIdeal ∧ (∀ b ∈ R, IsInt b) ∧
      ∀ (α β : ℂˣ) (W : GL (Fin 2) (Kv v) → ℂ), Eig v {α, β} W → ∀ g,
        q v ^ (1 / 2 : ℂ) * ((α : ℂ) + β) * W g = ∑ b ∈ R, W (g * nL b * dL ϖ 1) + W (g * dL 1 ϖ) ∧ W (g * dL ϖ ϖ) = (α : ℂ) * β * W g := by
  intro K _ _ v ϖ hϖ
  obtain ⟨-, hu, -, -⟩ := UpperTheory.V.Af.Smo.sphDict K 2 v
  have hv : Valued.v (((pi0 v)⁻¹ * ϖ : (Kv v)ˣ) : Kv v) = 1 := by
    have h0 : Valued.v ((pi0 v : (Kv v)ˣ) : Kv v) = Valued.v (ϖ : Kv v) := hu.trans hϖ.symm
    have hne : Valued.v ((pi0 v : (Kv v)ˣ) : Kv v) ≠ 0 := by simp
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, ← h0, inv_mul_cancel₀ hne]
  set u : (Kv v)ˣ := (pi0 v)⁻¹ * ϖ with hu_def
  have hϖu : ϖ = pi0 v * u := by rw [hu_def, mul_inv_cancel_left]
  have hone : Valued.v (((1 : (Kv v)ˣ)) : Kv v) = 1 := by simp
  refine ⟨Finset.univ.image (lf v), ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (lf_inj v), Finset.card_univ, card_res]
  · intro b hb
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hb
    exact (GroundTheory.Global.mem_valuationInteger_iff v _).1 (GroundTheory.Automorphic.Spherical.residueLift (Kv v) a).2
  · intro α β W hE g
    have inv := hE.inv
    have s1 := coset_sum v 2 hE (r := 1) (by norm_num) g
    have s2 := coset_sum v 2 hE (r := 2) le_rfl g
    rw [sum_one v fun x => W (g * x), sat_one] at s1
    rw [sum_two v fun x => W (g * x), sat_two] at s2
    have e1 : ∀ b, W (g * nL b * dL ϖ 1) = W (g * (nL b * dL (pi0 v) 1)) := by
      intro b
      have : dL ϖ (1 : (Kv v)ˣ) = dL (pi0 v) 1 * dL u 1 := by rw [dL_mul, ← hϖu, mul_one]
      rw [this, ← mul_assoc, ← mul_assoc, inv _ _ (dL_mem hv hone)]
    have e2 : W (g * dL 1 ϖ) = W (g * dL 1 (pi0 v)) := by
      have : dL (1 : (Kv v)ˣ) ϖ = dL 1 (pi0 v) * dL 1 u := by rw [dL_mul, ← hϖu, mul_one]
      rw [this, ← mul_assoc, inv _ _ (dL_mem hone hv)]
    have e3 : W (g * dL ϖ ϖ) = W (g * dL (pi0 v) (pi0 v)) := by
      have : dL ϖ ϖ = dL (pi0 v) (pi0 v) * dL u u := by rw [dL_mul, ← hϖu]
      rw [this, ← mul_assoc, inv _ _ (dL_mem hv hv)]
    refine ⟨?_, ?_⟩
    · rw [Finset.sum_image fun a _ b _ h => lf_inj v h, e2]
      simp only [e1]
      exact s1.symm
    · rw [e3]
      exact s2

end Main
