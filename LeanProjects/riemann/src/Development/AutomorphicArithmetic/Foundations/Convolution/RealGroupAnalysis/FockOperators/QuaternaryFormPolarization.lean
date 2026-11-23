import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private noncomputable def Bf {F : Type} [Field F] [NumberField F] (δ : F)
    (a y : Fin 4 → FiniteAdeleRing (𝓞 F) F) : FiniteAdeleRing (𝓞 F) F :=
  2 * (a 2 * y 2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) δ * (a 3 * y 3)) - a 1 * y 0 - a 0 * y 1

private theorem continuous_Bf {F : Type} [Field F] [NumberField F] (δ : F) :
    Continuous fun p : (Fin 4 → FiniteAdeleRing (𝓞 F) F) × (Fin 4 → FiniteAdeleRing (𝓞 F) F) =>
      Bf δ p.1 p.2 := by
  unfold Bf
  fun_prop

private theorem fin_level {F : Type} [Field F] [NumberField F] (δ : F)
    {g : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ finiteSchwartzBruhatPi F (ι := Fin 4)) :
    ∃ Λ : OpenAddSubgroup (FiniteAdeleRing (𝓞 F) F), ∀ a : Fin 4 → FiniteAdeleRing (𝓞 F) F,
      (∀ i, a i ∈ Λ) → ∀ y, g (y + a) = g y ∧ (finiteAdelicChar F (Bf δ a y) : ℂ) * g y = g y := by
  obtain ⟨hl, hc⟩ := hg
  have hev := IsLocallyConstant.iff_eventually_eq g |>.1 hl
  have hP1 : IsOpen {p : (Fin 4 → FiniteAdeleRing (𝓞 F) F) × (Fin 4 → FiniteAdeleRing (𝓞 F) F) |
      g (p.2 + p.1) = g p.2} := by
    rw [isOpen_iff_eventually]
    intro p hp
    have h1 : ∀ᶠ q : (Fin 4 → FiniteAdeleRing (𝓞 F) F) × (Fin 4 → FiniteAdeleRing (𝓞 F) F) in 𝓝 p,
        g (q.2 + q.1) = g (p.2 + p.1) :=
      ((continuous_snd.add continuous_fst).tendsto p).eventually (hev _)
    have h2 : ∀ᶠ q : (Fin 4 → FiniteAdeleRing (𝓞 F) F) × (Fin 4 → FiniteAdeleRing (𝓞 F) F) in 𝓝 p,
        g q.2 = g p.2 :=
      (continuous_snd.tendsto p).eventually (hev _)
    filter_upwards [h1, h2] with q e1 e2
    change g (q.2 + q.1) = g q.2
    rw [e1, e2]
    exact hp
  have hχ : IsLocallyConstant fun x : FiniteAdeleRing (𝓞 F) F => (finiteAdelicChar F x : ℂ) := by
    have := isLocallyConstant_finiteAdelicChar_mul (K := F) (1 : FiniteAdeleRing (𝓞 F) F)
    simpa using this
  have hP2 : IsOpen {p : (Fin 4 → FiniteAdeleRing (𝓞 F) F) × (Fin 4 → FiniteAdeleRing (𝓞 F) F) |
      (finiteAdelicChar F (Bf δ p.1 p.2) : ℂ) = 1} :=
    (hχ.isOpen_fiber 1).preimage (continuous_Bf δ)
  obtain ⟨u, w, hu, -, h0u, hSw, huw⟩ := generalized_tube_lemma (isCompact_singleton (x := (0 : Fin 4 → FiniteAdeleRing (𝓞 F) F)))
    (t := tsupport g) hc (hP1.inter hP2) (by
      rintro ⟨a, y⟩ ⟨ha, -⟩
      obtain rfl : a = 0 := ha
      refine ⟨by simp, ?_⟩
      change (finiteAdelicChar F (Bf δ 0 y) : ℂ) = 1
      have : Bf δ 0 y = 0 := by simp [Bf]
      rw [this, AddChar.map_zero_eq_one, Circle.coe_one])
  have hu0 : u ∈ 𝓝 (0 : Fin 4 → FiniteAdeleRing (𝓞 F) F) := hu.mem_nhds (h0u rfl)
  rw [nhds_pi, Filter.mem_pi] at hu0
  obtain ⟨I, -, t, ht, hIt⟩ := hu0
  have hN : (⋂ i, t i) ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := Filter.iInter_mem.mpr ht
  obtain ⟨J, hJ⟩ := exists_idealFiniteAdeles_subset hN
  refine ⟨⟨idealFiniteAdeles J, isOpen_idealFiniteAdeles J⟩, fun a ha y => ?_⟩
  have hmem : ∀ b : Fin 4 → FiniteAdeleRing (𝓞 F) F, (∀ i, b i ∈ idealFiniteAdeles J) → b ∈ u :=
    fun b hb => hIt fun i _ => Set.mem_iInter.1 (hJ (hb i)) i
  have ha' : ∀ i, a i ∈ idealFiniteAdeles J := ha
  have hau : a ∈ u := hmem a ha'
  have hnau : -a ∈ u := hmem (-a) fun i => neg_mem (ha' i)
  by_cases hy : y ∈ tsupport g
  · obtain ⟨e1, e2⟩ := huw (Set.mk_mem_prod hau (hSw hy))
    have e2' : (finiteAdelicChar F (Bf δ a y) : ℂ) = 1 := e2
    refine ⟨e1, ?_⟩
    rw [e2', one_mul]
  · have hy0 : g y = 0 := image_eq_zero_of_notMem_tsupport hy
    refine ⟨?_, by rw [hy0, mul_zero]⟩
    by_cases hy' : y + a ∈ tsupport g
    · have e1 : g (y + a + -a) = g (y + a) := (huw (Set.mk_mem_prod hnau (hSw hy'))).1
      rw [add_neg_cancel_right] at e1
      exact e1.symm
    · rw [hy0]
      exact image_eq_zero_of_notMem_tsupport hy'

private theorem quaternaryForm_polarization {F : Type} [Field F] [NumberField F] (δ : F) (a v : V4 F)
    (ha : ∀ i, (a i).1 = 0) :
    ψ (B4 δ a v) = (finiteAdelicChar F (Bf δ (finPartPi a) (finPartPi v)) : ℂ) := by
  have : B4 δ a v = finiteAdeleInr (Bf δ (finPartPi a) (finPartPi v)) := by
    refine Prod.ext ?_ ?_
    · simp [B4, ha, finiteAdeleInr_fst]
    · have h2 : (2 : A F).2 = (2 : FiniteAdeleRing (𝓞 F) F) := map_ofNat (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) 2
      simp [B4, Bf, finPartPi, finiteAdeleInr_snd, h2]
  rw [ψ, this, finiteAdelicChar_apply]

private theorem level_of_mem {F : Type} [Field F] [NumberField F] (δ : F) {f : V4 F → ℂ}
    (hf : f ∈ schwartzBruhatPi F (Fin 4)) :
    ∃ Λ : OpenAddSubgroup (FiniteAdeleRing (𝓞 F) F), ∀ a : V4 F, (∀ i, (a i).1 = 0 ∧ (a i).2 ∈ Λ) →
      ∀ v, f (v + a) = f v ∧ ψ (B4 δ a v) * f v = f v := by
  induction hf using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    obtain ⟨Λ, hΛ⟩ := fin_level δ hg
    refine ⟨Λ, fun a ha v => ?_⟩
    obtain ⟨e1, e2⟩ := hΛ (finPartPi a) (fun i => (ha i).2) (finPartPi v)
    have hinf : infPartPi (v + a) = infPartPi v := by
      funext i
      have : (v + a) i = ((v i).1, (v i).2 + (a i).2) := by
        refine Prod.ext ?_ rfl
        change (v i).1 + (a i).1 = (v i).1
        rw [(ha i).1, add_zero]
      simp only [infPartPi, this]
    have hfin : finPartPi (v + a) = finPartPi v + finPartPi a := rfl
    refine ⟨?_, ?_⟩
    · simp only [schwartzBruhatTensorPi, hinf, hfin, e1]
    · simp only [schwartzBruhatTensorPi]
      rw [quaternaryForm_polarization δ a v fun i => (ha i).1, mul_left_comm, e2]
  | zero =>
    exact ⟨⊤, fun _ _ _ => ⟨rfl, by simp⟩⟩
  | add G H _ _ hG hH =>
    obtain ⟨Λ, hΛ⟩ := hG
    obtain ⟨Λ', hΛ'⟩ := hH
    refine ⟨Λ ⊓ Λ', fun a ha v => ?_⟩
    obtain ⟨e1, e2⟩ := hΛ a (fun i => ⟨(ha i).1, (ha i).2.1⟩) v
    obtain ⟨e1', e2'⟩ := hΛ' a (fun i => ⟨(ha i).1, (ha i).2.2⟩) v
    refine ⟨?_, ?_⟩
    · simp only [Pi.add_apply, e1, e1']
    · simp only [Pi.add_apply, mul_add, e2, e2']
  | smul c G _ hG =>
    obtain ⟨Λ, hΛ⟩ := hG
    refine ⟨Λ, fun a ha v => ?_⟩
    obtain ⟨e1, e2⟩ := hΛ a ha v
    refine ⟨?_, ?_⟩
    · simp only [Pi.smul_apply, e1]
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [mul_left_comm, e2]

theorem UpperTheory.ConvolutionTheory.R2.Fo.fixEx :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F), (∀ φ : S4 F, ∃ Λ, φ ∈ Fix δ Λ) ∧ ∀ Λ Λ', Λ ≤ Λ' → Fix δ Λ' ≤ Fix δ Λ := by
  intro F _ _ δ
  refine ⟨fun φ => ?_, fun Λ Λ' h φ hφ a ha v => hφ a (fun i => ⟨(ha i).1, h (ha i).2⟩) v⟩
  obtain ⟨Λ, hΛ⟩ := level_of_mem δ φ.2
  exact ⟨Λ, fun a ha v => hΛ a ha v⟩
