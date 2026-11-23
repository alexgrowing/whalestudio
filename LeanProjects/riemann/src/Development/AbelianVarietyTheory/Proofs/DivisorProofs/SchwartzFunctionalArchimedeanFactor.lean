import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledLatticeTranslationInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledLatticeFourierInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleApproxScaledStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledIndicatorCosetSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSumIndicatorNonzeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledCosetIndicatorSchwartzStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

noncomputable section

namespace GlobalTheory.ThetaFunctionalUnique

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

variable (F κ) in

abbrev boxInd (a : F) : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  (GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator (fun _ => (1 : ℂ))

variable (F κ) in

abbrev cosInd (a : F) (r : κ → FiniteAdeleRing (𝓞 F) F) : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a}.indicator (fun _ => (1 : ℂ))

theorem inf_rat (q : F) :
    InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (AF F) q).1 = mixedEmbedding F q := by
  simp [InfiniteAdeleRing.ringEquiv_mixedSpace]
  rfl

theorem boxInd_mem_SB {a : F} (ha : a ≠ 0) : boxInd F κ a ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  have h := GlobalTheory.T.scaled_coset_indicator_schwartz F κ a ha 0
  convert h using 2
  ext y
  simp

theorem pure_mem (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) : pureA F f g ∈ schA F κ :=
  Submodule.subset_span ⟨f, g, hg, rfl⟩

theorem schr_trans (ψ : AddChar (AF F) ℂ) (ξ : κ → F) (Φ : (κ → AF F) → ℂ) :
    schr ψ ((fun i => algebraMap F (AF F) (ξ i)), (fun i => algebraMap F (AF F) ((0 : κ → F) i))) Φ =
      fun x => Φ (x + fun i => algebraMap F (AF F) (ξ i)) := by
  funext x
  simp [schr, dotProduct]

theorem pure_shift (f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (ξ : κ → F)
    (g g' : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (hf : ∀ x, f' x = f (x + fun i => mixedEmbedding F (ξ i)))
    (hg : ∀ y, g' y = g (y + fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i))) :
    (fun x => pureA F f g (x + fun i => algebraMap F (AF F) (ξ i))) = pureA F f' g' := by
  funext x
  simp only [pureA, hf, hg]
  congr 2
  funext i
  show InfiniteAdeleRing.ringEquiv_mixedSpace F ((x i + algebraMap F (AF F) (ξ i)).1) =
    InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 + mixedEmbedding F (ξ i)
  rw [← inf_rat]
  exact map_add _ _ _

theorem L_shift (ψ : AddChar (AF F) ℂ) (L : ((κ → AF F) → ℂ) → ℂ)
    (hinv : ∀ a b : κ → F, ∀ Φ ∈ schA F κ,
      L (schr ψ ((fun i => algebraMap F (AF F) (a i)), (fun i => algebraMap F (AF F) (b i))) Φ) = L Φ)
    (ξ : κ → F) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    L (fun x => Φ (x + fun i => algebraMap F (AF F) (ξ i))) = L Φ := by
  have h := hinv ξ 0 Φ hΦ
  rwa [schr_trans] at h

theorem theta_shift (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (ξ : κ → F) (Φ : (κ → AF F) → ℂ) :
    thetaSum F (fun x => Φ (x + fun i => algebraMap F (AF F) (ξ i))) = thetaSum F Φ := by
  have h := GlobalTheory.ThetaQuasiRat.thetaSum_schr_rat F ψ hψ.2.1 ξ 0 Φ
  rwa [schr_trans] at h

theorem box_eq (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (L : ((κ → AF F) → ℂ) → ℂ)
    (hinv : ∀ a b : κ → F, ∀ Φ ∈ schA F κ,
      L (schr ψ ((fun i => algebraMap F (AF F) (a i)), (fun i => algebraMap F (AF F) (b i))) Φ) = L Φ)
    {a : F} (ha : a ≠ 0) (T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ)
    (hT : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, L (pureA F f (boxInd F κ a)) = T f) :
    ∃ c : ℂ, ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, L (pureA F f (boxInd F κ a)) = c * thetaSum F (pureA F f (boxInd F κ a)) := by
  obtain ⟨c, hc⟩ := GlobalTheory.T.scaled_lattice_translation_invariant F κ a ha T (fun ξ hξ f f' hf => by
      rw [← hT, ← hT]
      have e := pure_shift f f' ξ (boxInd F κ a) (boxInd F κ a) hf (fun y => by
        simp only [Set.indicator_apply, SetLike.mem_coe, AddSubgroup.add_mem_cancel_right _ hξ])
      rw [← e]
      exact L_shift ψ L hinv ξ (pure_mem f (boxInd_mem_SB ha)))
    (fun b hb f f' hf => by
      rw [← hT, ← hT, ← GlobalTheory.T.scaled_lattice_fourier_invariant F ψ hψ κ a ha b hb f f' hf]
      have h := hinv 0 b _ (pure_mem f (boxInd_mem_SB ha))
      have e0 : (fun i => algebraMap F (AF F) ((0 : κ → F) i)) = 0 := by funext i; simp
      rw [e0] at h
      exact h)
  refine ⟨c, fun f => ?_⟩
  rw [hT, hc f]
  congr 1
  unfold thetaSum
  refine tsum_congr fun ξ => ?_
  have e1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) i).1) = fun i => mixedEmbedding F (ξ i) := by
    funext i; exact inf_rat (ξ i)
  have e2 : (fun i => ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) i).2) =
      fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i) := rfl
  simp only [pureA, e1, e2, Set.indicator_apply, SetLike.mem_coe, Set.mem_setOf_eq]
  split_ifs <;> simp

end GlobalTheory.ThetaFunctionalUnique

namespace GlobalTheory.ThetaFunctionalUnique

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem cosInd_mem_SB {a : F} (ha : a ≠ 0) (r : κ → FiniteAdeleRing (𝓞 F) F) :
    cosInd F κ a r ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) :=
  GlobalTheory.T.scaled_coset_indicator_schwartz F κ a ha r

theorem cos_eq (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (L : ((κ → AF F) → ℂ) → ℂ)
    (hinv : ∀ a b : κ → F, ∀ Φ ∈ schA F κ,
      L (schr ψ ((fun i => algebraMap F (AF F) (a i)), (fun i => algebraMap F (AF F) (b i))) Φ) = L Φ)
    {a : F} (ha : a ≠ 0) {c : ℂ}
    (hc : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      L (pureA F f (boxInd F κ a)) = c * thetaSum F (pureA F f (boxInd F κ a)))
    (r : κ → FiniteAdeleRing (𝓞 F) F) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) :
    L (pureA F f (cosInd F κ a r)) = c * thetaSum F (pureA F f (cosInd F κ a r)) := by
  obtain ⟨ξ, hξ⟩ := GlobalTheory.T.finite_adele_approx_scaled F κ a ha r
  have hs : {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a} =
      {y | y - (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a} := by
    ext y
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      have := add_mem h hξ
      rwa [sub_add_sub_cancel] at this
    · intro h
      have := sub_mem h hξ
      rwa [sub_sub_sub_cancel_right] at this
  have hr : cosInd F κ a r = cosInd F κ a (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) := by
    simp only [cosInd, hs]
  rw [hr]
  set f' := SchwartzMap.compSubConstCLM ℂ (-(fun i => mixedEmbedding F (ξ i))) f with hf'def
  have hf' : ∀ x, f' x = f (x + fun i => mixedEmbedding F (ξ i)) := by
    intro x
    simp [hf'def, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]
  have e := pure_shift f f' ξ (cosInd F κ a (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)))
    (boxInd F κ a) hf' (fun y => by simp only [Set.indicator_apply, SetLike.mem_coe, Set.mem_setOf_eq, add_sub_cancel_right])
  have hm := pure_mem f (cosInd_mem_SB ha (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)))
  rw [← L_shift ψ L hinv ξ hm, ← theta_shift ψ hψ ξ, e, hc f']

theorem L_sum (L : ((κ → AF F) → ℂ) → ℂ) (hadd : ∀ Φ ∈ schA F κ, ∀ Ψ ∈ schA F κ, L (Φ + Ψ) = L Φ + L Ψ)
    (hsmul : ∀ (c : ℂ), ∀ Φ ∈ schA F κ, L (c • Φ) = c * L Φ) {ι : Type} (s : Finset ι)
    (Φ : ι → (κ → AF F) → ℂ) (hΦ : ∀ j ∈ s, Φ j ∈ schA F κ) : L (∑ j ∈ s, Φ j) = ∑ j ∈ s, L (Φ j) := by
  have hL0 : L 0 = 0 := by
    have h := hsmul 0 0 (zero_mem _)
    simpa using h
  induction s using Finset.induction_on with
  | empty => simpa using hL0
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj,
      hadd _ (hΦ j (Finset.mem_insert_self _ _)) _ (Submodule.sum_mem _ fun k hk => hΦ k (Finset.mem_insert_of_mem hk)),
      ih fun k hk => hΦ k (Finset.mem_insert_of_mem hk)]

theorem theta_sum {ι : Type} (s : Finset ι) (Φ : ι → (κ → AF F) → ℂ) (hΦ : ∀ j ∈ s, Φ j ∈ schA F κ) :
    thetaSum F (∑ j ∈ s, Φ j) = ∑ j ∈ s, thetaSum F (Φ j) := by
  induction s using Finset.induction_on with
  | empty => simp [thetaSum]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj,
      GlobalTheory.WeilM.thetaSum_add F (hΦ j (Finset.mem_insert_self _ _))
        (Submodule.sum_mem _ fun k hk => hΦ k (Finset.mem_insert_of_mem hk)),
      ih fun k hk => hΦ k (Finset.mem_insert_of_mem hk)]

theorem pure_sum (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) {ι : Type} (s : Finset ι)
    (w : ι → ℂ) (g : ι → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    pureA F f (∑ j ∈ s, w j • g j) = ∑ j ∈ s, w j • pureA F f (g j) := by
  funext x
  simp only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem const_mul (L : ((κ → AF F) → ℂ) → ℂ) (hadd : ∀ Φ ∈ schA F κ, ∀ Ψ ∈ schA F κ, L (Φ + Ψ) = L Φ + L Ψ)
    (hsmul : ∀ (c : ℂ), ∀ Φ ∈ schA F κ, L (c • Φ) = c * L Φ) (c : F → ℂ)
    (hc : ∀ a : F, a ≠ 0 → ∀ (r : κ → FiniteAdeleRing (𝓞 F) F) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ),
      L (pureA F f (cosInd F κ a r)) = c a * thetaSum F (pureA F f (cosInd F κ a r)))
    {a : F} (ha : a ≠ 0) (m : 𝓞 F) (hm : m ≠ 0) : c a = c (a * m) := by
  obtain ⟨R, hR⟩ := GlobalTheory.T.scaled_indicator_coset_sum F κ a ha m hm
  obtain ⟨f, hf⟩ := GlobalTheory.T.theta_sum_indicator_nonzero F κ a ha
  have ham : a * (m : F) ≠ 0 := mul_ne_zero ha (by simpa using hm)
  have hb : boxInd F κ a = cosInd F κ a 0 := by
    unfold boxInd cosInd
    congr 1
    ext y
    simp
  have hsplit : pureA F f (boxInd F κ a) = ∑ ξ ∈ R, (1 : ℂ) •
      pureA F f (cosInd F κ (a * m) (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i))) := by
    rw [← pure_sum]
    congr 1
    rw [show boxInd F κ a = _ from hR]
    simp
  have hmem : ∀ ξ ∈ R, (1 : ℂ) •
      pureA F f (cosInd F κ (a * m) (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i))) ∈ schA F κ :=
    fun ξ _ => Submodule.smul_mem _ _ (pure_mem f (cosInd_mem_SB ham _))
  have h1 := hc a ha 0 f
  rw [← hb] at h1
  have h2 : L (pureA F f (boxInd F κ a)) = c (a * m) * thetaSum F (pureA F f (boxInd F κ a)) := by
    rw [hsplit, L_sum L hadd hsmul R _ hmem, theta_sum R _ hmem, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [one_smul, hc _ ham]
  exact mul_right_cancel₀ hf (h1.symm.trans h2)

end GlobalTheory.ThetaFunctionalUnique

namespace GlobalTheory.ThetaFunctionalUnique

theorem main : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (L : ((κ → AF F) → ℂ) → ℂ),
    (∀ Φ ∈ schA F κ, ∀ Ψ ∈ schA F κ, L (Φ + Ψ) = L Φ + L Ψ) →
    (∀ (c : ℂ), ∀ Φ ∈ schA F κ, L (c • Φ) = c * L Φ) →
    (∀ g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F), ∃ T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ,
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, L (pureA F f g) = T f) →
    (∀ a b : κ → F, ∀ Φ ∈ schA F κ,
      L (schr ψ ((fun i => algebraMap F (AF F) (a i)), (fun i => algebraMap F (AF F) (b i))) Φ) = L Φ) →
    ∃ c : ℂ, ∀ Φ ∈ schA F κ, L Φ = c * thetaSum F Φ := by
  intro F _ _ ψ hψ κ _ L hadd hsmul hadm hinv
  have hbox : ∀ a : F, ∃ c : ℂ, a ≠ 0 → ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      L (pureA F f (boxInd F κ a)) = c * thetaSum F (pureA F f (boxInd F κ a)) := by
    intro a
    by_cases ha : a = 0
    · exact ⟨0, fun h => absurd ha h⟩
    obtain ⟨T, hT⟩ := hadm _ (boxInd_mem_SB ha)
    obtain ⟨c, hc⟩ := box_eq ψ hψ L hinv ha T hT
    exact ⟨c, fun _ => hc⟩
  choose c hc using hbox
  have hcos : ∀ a : F, a ≠ 0 → ∀ (r : κ → FiniteAdeleRing (𝓞 F) F) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ),
      L (pureA F f (cosInd F κ a r)) = c a * thetaSum F (pureA F f (cosInd F κ a r)) :=
    fun a ha r f => cos_eq ψ hψ L hinv ha (hc a ha) r f
  have hall : ∀ a : F, a ≠ 0 → c a = c 1 := by
    intro a ha
    obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := 𝓞 F) a
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hqF : (algebraMap (𝓞 F) F q) ≠ 0 := by simpa using hq0
    have hp0 : p ≠ 0 := by
      rintro rfl
      apply ha
      rw [← hpq]
      simp
    have e : a * (q : F) = 1 * (p : F) := by
      rw [← hpq]
      have : (algebraMap (𝓞 F) F q) = (q : F) := rfl
      have : (algebraMap (𝓞 F) F p) = (p : F) := rfl
      field_simp
    calc c a = c (a * q) := const_mul L hadd hsmul c hcos ha q hq0
      _ = c (1 * p) := by rw [e]
      _ = c 1 := (const_mul L hadd hsmul c hcos one_ne_zero p hp0).symm
  refine ⟨c 1, fun Φ hΦ => ?_⟩
  have hΦ' : Φ ∈ Submodule.span ℂ {Φ | ∃ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
      (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) ∧ Φ = pureA F f g} := hΦ
  induction hΦ' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    obtain ⟨a, ha, R, hR⟩ := GlobalTheory.EvAdm.exists_sum_cosets hg
    have hsplit : pureA F f g = ∑ r ∈ R, g r • pureA F f (cosInd F κ a r) := by
      rw [← pure_sum]
      congr 1
    have hmem : ∀ r ∈ R, g r • pureA F f (cosInd F κ a r) ∈ schA F κ :=
      fun r _ => Submodule.smul_mem _ _ (pure_mem f (cosInd_mem_SB ha r))
    rw [hsplit, L_sum L hadd hsmul R _ hmem, theta_sum R _ hmem, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hsmul _ _ (pure_mem f (cosInd_mem_SB ha r)), GlobalTheory.WeilM.thetaSum_smul F, hcos a ha r f, hall a ha]
    ring
  | zero =>
    have h := hsmul 0 0 (zero_mem _)
    simp only [zero_smul, zero_mul] at h
    rw [h]
    simp [thetaSum]
  | add x y hx hy ihx ihy =>
    rw [hadd x hx y hy, GlobalTheory.WeilM.thetaSum_add F hx hy, ihx hx, ihy hy]
    ring
  | smul t x hx ih =>
    rw [hsmul t x hx, GlobalTheory.WeilM.thetaSum_smul F, ih hx]
    ring

end GlobalTheory.ThetaFunctionalUnique
