import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private theorem psi_eq_one {F : Type} [Field F] [NumberField F] (x : A F) (hx : x.1 = 0)
    (hU : x.2 ∈ finiteInvDifferent F) : ψ x = 1 := by
  have hxe : x = finiteAdeleInr x.2 := Prod.ext (by simpa using hx) (by simp)
  have h := finiteAdelicChar_eq_one_of_mem hU
  rw [finiteAdelicChar_apply, ← hxe] at h
  simp [ψ, h]

private theorem tensor_case {F : Type} [Field F] [NumberField F] (δ : F)
    (f : SchwartzMap (Fin 4 → mixedEmbedding.mixedSpace F) ℂ) {g : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ finiteSchwartzBruhatPi F) :
    ∀ᶠ b in 𝓝 (0 : A F), b.1 = 0 → ∀ v,
      ψ (b * q4 δ v) * schwartzBruhatTensorPi f g v = schwartzBruhatTensorPi f g v := by
  have hc : IsCompact (tsupport g) := ((mem_finiteSchwartzBruhatPi F).1 hg).2
  let qf : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → FiniteAdeleRing (𝓞 F) F :=
    fun w => w 2 ^ 2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) δ * w 3 ^ 2 - w 1 * w 0
  have hqf : Continuous qf := by
    have h (i : Fin 4) : Continuous fun w : Fin 4 → FiniteAdeleRing (𝓞 F) F => w i := continuous_apply i
    exact (((h 2).pow 2).sub (continuous_const.mul ((h 3).pow 2))).sub ((h 1).mul (h 0))
  have hU := isOpen_finiteInvDifferent F
  have h0 : ∀ᶠ a in 𝓝 (0 : FiniteAdeleRing (𝓞 F) F), ∀ y ∈ qf '' tsupport g,
      a * y ∈ (finiteInvDifferent F : Set (FiniteAdeleRing (𝓞 F) F)) := by
    refine (hc.image hqf).eventually_forall_of_forall_eventually (fun y _ => ?_)
    have hcont : Continuous fun z : FiniteAdeleRing (𝓞 F) F × FiniteAdeleRing (𝓞 F) F => z.1 * z.2 :=
      continuous_mul
    exact hcont.continuousAt.eventually (hU.mem_nhds (by simpa using zero_mem (finiteInvDifferent F)))
  have h1 : ∀ᶠ b in 𝓝 (0 : A F), ∀ y ∈ qf '' tsupport g,
      b.2 * y ∈ (finiteInvDifferent F : Set (FiniteAdeleRing (𝓞 F) F)) :=
    (continuous_snd.tendsto (0 : A F)).eventually h0
  filter_upwards [h1] with b hb hb1 v
  by_cases hv : g (finPartPi v) = 0
  · simp [schwartzBruhatTensorPi, hv]
  · have hmem : finPartPi v ∈ tsupport g := subset_tsupport g hv
    have hq : (b * q4 δ v).2 = b.2 * qf (finPartPi v) := by
      have hp (x : A F) : (x ^ 2).2 = x.2 ^ 2 := rfl
      simp [q4, qf, finPartPi, hp]
    have hone : ψ (b * q4 δ v) = 1 := by
      refine psi_eq_one _ (by simp [hb1]) ?_
      rw [hq]
      exact hb _ ⟨_, hmem, rfl⟩
    rw [hone, one_mul]

private theorem span_case {F : Type} [Field F] [NumberField F] (δ : F) {f : V4 F → ℂ}
    (hf : f ∈ schwartzBruhatPi F (Fin 4)) :
    ∀ᶠ b in 𝓝 (0 : A F), b.1 = 0 → ∀ v, ψ (b * q4 δ v) * f v = f v := by
  refine Submodule.span_induction (p := fun f _ =>
    ∀ᶠ b in 𝓝 (0 : A F), b.1 = 0 → ∀ v, ψ (b * q4 δ v) * f v = f v) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨p, g, hg, rfl⟩
    exact tensor_case δ p hg
  · exact Eventually.of_forall fun b _ v => by simp
  · intro x y _ _ hx hy
    filter_upwards [hx, hy] with b h1 h2 hb v
    rw [Pi.add_apply, mul_add, h1 hb v, h2 hb v]
  · intro c x _ hx
    filter_upwards [hx] with b h1 hb v
    rw [Pi.smul_apply, smul_eq_mul, mul_left_comm, h1 hb v]

theorem UpperTheory.ConvolutionTheory.R2.C.nLevel :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (φ : S4 F), ∀ᶠ b in 𝓝 (0 : A F), b.1 = 0 → ∀ v, ψ (b * q4 δ v) * φ.1 v = φ.1 v := by
  intro F _ _ δ φ
  exact span_case δ φ.2
