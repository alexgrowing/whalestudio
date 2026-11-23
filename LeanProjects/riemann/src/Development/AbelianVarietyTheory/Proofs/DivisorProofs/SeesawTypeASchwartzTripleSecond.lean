import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DecayNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTensEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormBlockVanishing

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.FinFinite

open GlobalTheory.HeisSchA

theorem finite_image_of_isLocallyConstant {P Z Y : Type} [TopologicalSpace P] [TopologicalSpace Z] [Zero Y]
    (Φ : P → Z → Y) (hΦ : IsLocallyConstant fun q : P × Z => Φ q.1 q.2) {K : Set P} (hK : IsCompact K)
    {C : Set Z} (hC : IsCompact C) (h0 : ∀ p ∈ K, ∀ z ∉ C, Φ p z = 0) : (Φ '' K).Finite := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hl : IsLocallyConstant fun p : K => Φ p.1 := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro p₀
    have h1 : ∀ᶠ p in 𝓝 p₀.1, ∀ z ∈ C, Φ p z = Φ p₀.1 z := by
      refine hC.eventually_forall_of_forall_eventually fun z _ => ?_
      have h2 := hΦ.eventually_eq (p₀.1, z)
      have h3 : ∀ᶠ q : P × Z in 𝓝 (p₀.1, z), Φ p₀.1 q.2 = Φ p₀.1 z :=
        (hΦ.comp_continuous (f := fun q : P × Z => (p₀.1, q.2)) (by fun_prop)).eventually_eq (p₀.1, z)
      filter_upwards [h2, h3] with q e2 e3
      rw [e2, e3]
    filter_upwards [continuous_subtype_val.continuousAt.eventually h1] with p hp
    funext z
    by_cases hz : z ∈ C
    · exact hp z hz
    · rw [h0 _ p.2 z hz, h0 _ p₀.2 z hz]
  rw [Set.image_eq_range]
  exact hl.range_finite

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem finite_finS (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F))
    {P : Type} [TopologicalSpace P] {d s : P → κ → Af F} {d₀ : P → Af F} (hd : Continuous d) (hs : Continuous s)
    (hd₀ : Continuous d₀) {K : Set P} (hK : IsCompact K) :
    ((fun p => finS ψ g (d p) (s p) (d₀ p)) '' K).Finite := by
  refine finite_image_of_isLocallyConstant _ ?_ hK
    (C := (fun q : (κ → Af F) × P => q.1 - s q.2) '' (tsupport g ×ˢ K)) ((hg.2.isCompact.prod hK).image (by fun_prop)) ?_
  · have hlin : Continuous fun q : P × (κ → Af F) => q.2 ⬝ᵥ d q.1 + d₀ q.1 :=
      (continuous_snd.dotProduct (hd.comp continuous_fst)).add (hd₀.comp continuous_fst)
    exact ((finChar_isLocallyConstant ψ hψ).comp_continuous hlin).mul
      (hg.1.comp_continuous (continuous_snd.add (hs.comp continuous_fst)))
  · intro p hp z hz
    have : g (z + s p) = 0 := by
      by_contra h
      exact hz ⟨(z + s p, p), ⟨subset_tsupport _ h, hp⟩, by simp⟩
    simp only [finS, this, mul_zero]

theorem schr_pureA_fin [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (w : (κ → AF F) × (κ → AF F))
    (h1 : ∀ i, p1 (w.1 i) = 0) (h2 : ∀ i, p1 (w.2 i) = 0) (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → Af F) → ℂ) :
    schr ψ w (pureA F f g) = pureA F f (finS ψ g (fun i => p2 (w.2 i)) (fun i => p2 (w.1 i))
      (p2 (⅟(2 : AF F)) * ((fun i => p2 (w.1 i)) ⬝ᵥ fun i => p2 (w.2 i)))) := by
  funext x
  have e1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + w.1) i).1) =
      fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 := by
    funext i
    congr 1
    change p1 (x i + w.1 i) = p1 (x i)
    rw [map_add, h1, add_zero]
  have e2 : (fun i => ((x + w.1) i).2) = (fun i => (x i).2) + fun i => p2 (w.1 i) := rfl
  have e3 : ψ (x ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) = finChar ψ ((fun i => (x i).2) ⬝ᵥ (fun i => p2 (w.2 i)) +
      p2 (⅟(2 : AF F)) * ((fun i => p2 (w.1 i)) ⬝ᵥ fun i => p2 (w.2 i))) := by
    rw [map_eq_mul ψ]
    have : p1 (x ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) = 0 := by
      simp only [dotProduct, map_add, map_mul, map_sum, h2, mul_zero, Finset.sum_const_zero, add_zero]
    rw [this, show mk (F := F) 0 0 = 0 from rfl, AddChar.map_zero_eq_one, one_mul]
    congr 1
    simp only [dotProduct, map_add, map_mul, map_sum]
    rfl
  simp only [schr, pureA, finS]
  rw [e1, e2, e3]
  ring

theorem hTens_smul_vecMulVec {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
    {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A)
    (a a' : A) (u : α → A) (v : β → A) (h : ∑ i, ∑ k, u i * (JA i k * c (u k)) = 0) :
    hTens c JA JB (a • Matrix.vecMulVec u v) (a' • Matrix.vecMulVec u v) = 0 := by
  have : hTens c JA JB (a • Matrix.vecMulVec u v) (a' • Matrix.vecMulVec u v) =
      ∑ j, ∑ l, (a * v j * JB j l * c a' * c (v l)) * ∑ i, ∑ k, u i * (JA i k * c (u k)) := by
    unfold hTens
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm (s := (Finset.univ : Finset β))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, map_mul]
    ring
  rw [this]
  simp only [h, mul_zero, Finset.sum_const_zero]

theorem rho_shiftA_pureA_finite : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ g ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → FiniteAdeleRing (𝓞 F) F), ∀ m : ℕ, 0 < m →
      ∃ (r : ℕ) (gs : Fin r → (Fin (b + 2) × Fin (b + 2 + a') → FiniteAdeleRing (𝓞 F) F) → ℂ),
        (∀ j, gs j ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → FiniteAdeleRing (𝓞 F) F)) ∧
        ∀ l : (AE F E)ˣ, (∀ i v, evFin F v ((m : AF F) * GlobalTheory.IdeleDecay.coord F E l.1 i) ∈ v.adicCompletionIntegers F) →
          ∃ j, ∀ f : SInf F (Fin (b + 2) × Fin (b + 2 + a')),
            G.M.co.rho B.ψ (shiftA H H' l) (pureA F f g) =
              G.M.co.rho B.ψ (((pairA F 1 0 : AF F) • l.1) • Matrix.vecMulVec (incV F H.x) (incV F H'.y)) (pureA F f (gs j)) := by
  intro _ F E _ _ _ _ _ σ B b a' G G₁ H H' hC e _ X om om' om₁ om₁' hT _ g hg m hm
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  set bs := Algebra.TensorProduct.basis (AF F) (Module.finBasis F E) with hbs
  set M := Matrix.vecMulVec (incV F H.x) (incV F H'.y) with hM
  set c : Af F := algebraMap F (Af F) (m : F)⁻¹ with hc
  have hcm : c * (m : Af F) = 1 := by
    rw [hc, ← map_natCast (algebraMap F (Af F)), ← map_mul, inv_mul_cancel₀ (by exact_mod_cast hm.ne'), map_one]
  let u : Fin (Module.finrank F E) → (Fin (b + 2) × Fin (b + 2 + a') → AF F) × (Fin (b + 2) × Fin (b + 2 + a') → AF F) :=
    fun i => G.M.co.e (bs i • M)
  let s : (Fin (Module.finrank F E) → Af F) → Fin (b + 2) × Fin (b + 2 + a') → Af F :=
    fun t k => ∑ i, c * t i * p2 ((u i).1 k)
  let d : (Fin (Module.finrank F E) → Af F) → Fin (b + 2) × Fin (b + 2 + a') → Af F :=
    fun t k => ∑ i, c * t i * p2 ((u i).2 k)
  have hs : Continuous s := continuous_pi fun k => continuous_finsetSum _ fun i _ =>
    (continuous_const.mul (continuous_apply i)).mul continuous_const
  have hd : Continuous d := continuous_pi fun k => continuous_finsetSum _ fun i _ =>
    (continuous_const.mul (continuous_apply i)).mul continuous_const
  have hψ : Continuous B.ψ := hT.base.std.1
  have hK : IsCompact (Set.univ.pi fun _ : Fin (Module.finrank F E) =>
      {a : Af F | ∀ v : HeightOneSpectrum (𝓞 F), a.1 v ∈ v.adicCompletionIntegers F}) :=
    isCompact_univ_pi fun _ => GlobalTheory.LatHatClosed.isCompact_integralFinite F
  have hfin := finite_finS B.ψ hψ hg (d₀ := fun t => p2 (⅟(2 : AF F)) * (s t ⬝ᵥ d t)) hd hs
    (continuous_const.mul (hs.dotProduct hd)) hK
  obtain ⟨r, gs, -, hgs⟩ := hfin.fin_param
  refine ⟨r, gs, fun j => ?_, fun l hl => ?_⟩
  · obtain ⟨t, -, ht⟩ : gs j ∈ _ := hgs ▸ Set.mem_range_self j
    rw [← ht]
    exact finS_mem _ hψ hg _ _ _
  · let t : Fin (Module.finrank F E) → Af F := fun i => p2 ((m : AF F) * GlobalTheory.IdeleDecay.coord F E l.1 i)
    have ht : t ∈ Set.univ.pi fun _ : Fin (Module.finrank F E) =>
        {a : Af F | ∀ v : HeightOneSpectrum (𝓞 F), a.1 v ∈ v.adicCompletionIntegers F} := fun i _ v => hl i v
    have hmem := Set.mem_image_of_mem (fun p => finS B.ψ g (d p) (s p) (p2 (⅟(2 : AF F)) * (s p ⬝ᵥ d p))) ht
    rw [← hgs] at hmem
    obtain ⟨j, hj⟩ := hmem
    refine ⟨j, fun f => ?_⟩
    have hl' : l.1 = ∑ i, GlobalTheory.IdeleDecay.coord F E l.1 i • bs i := (bs.sum_equivFun l.1).symm
    have hw : G.M.co.e (((pairA F 0 1 : AF F) • l.1) • M) =
        ∑ i, (pairA F 0 1 * GlobalTheory.IdeleDecay.coord F E l.1 i) • u i := by
      conv_lhs => rw [hl']
      simp only [Finset.smul_sum, Finset.sum_smul, map_sum, smul_smul, u, ← map_smul, smul_assoc]
    have hp1 : p1 (pairA F 0 1) = 0 := rfl
    have hp2 : p2 (pairA F 0 1) = 1 := rfl
    have hct : ∀ i, c * t i = p2 (GlobalTheory.IdeleDecay.coord F E l.1 i) := fun i => by
      simp only [t, map_mul, map_natCast, ← mul_assoc, hcm, one_mul]
    have hsplit : shiftA H H' l = ((pairA F 1 0 : AF F) • l.1) • M + ((pairA F 0 1 : AF F) • l.1) • M := by
      rw [← add_smul, ← add_smul, show (pairA F 1 0 : AF F) + pairA F 0 1 = 1 from Prod.ext (add_zero _) (zero_add _),
        one_smul]
      rfl
    have hiso : symp (R := AF F) (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) (((pairA F 1 0 : AF F) • l.1) • M)
        (((pairA F 0 1 : AF F) • l.1) • M) = 0 := by
      unfold symp
      rw [hM, hTens_smul_vecMulVec, mul_zero, map_zero]
      have h0 := congrArg (inclR (F := F) (AF F)) hC.hH.xx
      have hcA : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun _ => rfl
      rw [map_zero] at h0
      rw [← h0]
      simp only [form, Matrix.mulVec, dotProduct, incM, incV, Matrix.map_apply, hcA, map_sum, map_mul, Finset.mul_sum]
    rw [hsplit, ← GlobalTheory.MixW.UnipHeis.rho_rho G.M.co B.ψ _ _ hiso]
    congr 1
    rw [Darboux.rho, schr_pureA_fin, hj]
    · have e1 : (fun k => p2 ((G.M.co.e (((pairA F 0 1 : AF F) • l.1) • M)).1 k)) = s t := by
        funext k
        simp only [hw, Prod.fst_sum, Finset.sum_apply, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, hp2,
          one_mul, s, hct]
      have e2 : (fun k => p2 ((G.M.co.e (((pairA F 0 1 : AF F) • l.1) • M)).2 k)) = d t := by
        funext k
        simp only [hw, Prod.snd_sum, Finset.sum_apply, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, hp2,
          one_mul, d, hct]
      rw [e1, e2]
    · intro k
      simp only [hw, Prod.fst_sum, Finset.sum_apply, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, hp1,
        zero_mul, Finset.sum_const_zero]
    · intro k
      simp only [hw, Prod.snd_sum, Finset.sum_apply, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, hp1,
        zero_mul, Finset.sum_const_zero]

end GlobalTheory.FinFinite
