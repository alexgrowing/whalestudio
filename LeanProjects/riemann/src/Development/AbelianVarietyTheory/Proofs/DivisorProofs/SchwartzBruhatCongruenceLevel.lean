import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupsSchroedingerFixStandardChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.SchrUnifDen

theorem eq_nsmul_int {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (N : ℕ)
    (x : κ → FiniteAdeleRing (𝓞 F) F)
    (hx : ∀ k v, ∃ c ∈ v.adicCompletionIntegers F, x k v = (N : Fv F v) * c) :
    ∃ x' ∈ GlobalTheory.SchADecomp.intP F κ, x = N • x' := by
  choose c hc hxc using hx
  let X : κ → FiniteAdeleRing (𝓞 F) F := fun k =>
    RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite (fun v => ⟨c k v, hc k v⟩)
  have hX : ∀ k v, X k v = c k v := fun _ _ => rfl
  refine ⟨X, fun k _ v => hc k v, ?_⟩
  funext k
  apply RestrictedProduct.ext
  intro v
  show x k v = (N • X k) v
  rw [hxc k v, nsmul_eq_mul, ← hX k v]
  show _ = evalV F v ((N : FiniteAdeleRing (𝓞 F) F) * X k)
  rw [map_mul, map_natCast]
  rfl

theorem schr_fix_pure_uniform : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) {κ : Type} [Fintype κ]
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)),
    ∃ M₀ : ℕ, 1 ≤ M₀ ∧ ∀ (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (a b : κ → AF F),
      (∀ k, evI F (a k) = 0 ∧ evI F (b k) = 0 ∧
        (∀ v, ∃ c ∈ v.adicCompletionIntegers F, evFin F v (a k) = (M₀ : Fv F v) * c) ∧
        (∀ v, ∃ c ∈ v.adicCompletionIntegers F, evFin F v (b k) = (M₀ : Fv F v) * c)) →
      schr ψ (a, b) (pureA F f g) = pureA F f g := by
  intro F _ _ ψ hψ κ _ g hg
  haveI := GlobalTheory.HeisSchA.nonarch_finiteAdeleRing (F := F)
  haveI : NonarchimedeanAddGroup (κ → FiniteAdeleRing (𝓞 F) F) := GlobalTheory.HeisSchA.nonarch_pi
  obtain ⟨H, hH⟩ := GlobalTheory.SchrFixNbhd.exists_dot_ker (GlobalTheory.HeisSchA.finChar ψ)
    (GlobalTheory.HeisSchA.finChar_isLocallyConstant ψ hψ) κ (tsupport g) hg.2.isCompact
  let c : FiniteAdeleRing (𝓞 F) F := (⅟(2 : AdeleRing (𝓞 F) F)).2
  let L₁ : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) := GlobalTheory.SchrFixNbhd.fixTrans g ⊓
    (H : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)).comap
      (DistribSMul.toAddMonoidHom (κ → FiniteAdeleRing (𝓞 F) F) c)
  have o₁ : IsOpen (L₁ : Set (κ → FiniteAdeleRing (𝓞 F) F)) := by
    rw [AddSubgroup.coe_inf]
    exact (GlobalTheory.SchrFixNbhd.isOpen_fixTrans hg.1 hg.2).inter (H.isOpen.preimage (continuous_const_smul c))
  obtain ⟨N₁, hN₁, h₁⟩ := GlobalTheory.SchADecomp.exists_nsmul_mem κ L₁ o₁
  obtain ⟨N₂, hN₂, h₂⟩ := GlobalTheory.SchADecomp.exists_nsmul_mem κ (H : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)) H.isOpen
  refine ⟨N₁ * N₂, Nat.one_le_iff_ne_zero.2 (mul_ne_zero hN₁ hN₂), fun f a b hab => ?_⟩
  let x : κ → FiniteAdeleRing (𝓞 F) F := fun k => (a k).2
  let y : κ → FiniteAdeleRing (𝓞 F) F := fun k => (b k).2
  have ha : a = GlobalTheory.WeilCont.adeleJoin F 0 x := by
    funext k
    rw [GlobalTheory.SchrFixNbhd.adeleJoin_zero_apply]
    refine Prod.ext ?_ rfl
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact (hab k).1)
  have hb : b = GlobalTheory.WeilCont.adeleJoin F 0 y := by
    funext k
    rw [GlobalTheory.SchrFixNbhd.adeleJoin_zero_apply]
    refine Prod.ext ?_ rfl
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact (hab k).2.1)
  obtain ⟨x', hx', hxx⟩ := eq_nsmul_int (N₁ * N₂) x (fun k v => (hab k).2.2.1 v)
  obtain ⟨y', hy', hyy⟩ := eq_nsmul_int (N₁ * N₂) y (fun k v => (hab k).2.2.2 v)
  have hx : x ∈ L₁ := by
    rw [hxx, ← smul_smul]
    exact h₁ _ (nsmul_mem hx' _)
  have hy : y ∈ (H : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)) := by
    rw [hyy, mul_comm, ← smul_smul]
    exact h₂ _ (nsmul_mem hy' _)
  obtain ⟨hx1, hx2⟩ := hx
  rw [ha, hb]
  funext z
  have hf : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((z + GlobalTheory.WeilCont.adeleJoin F 0 x) i).1) =
      fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1 := by
    funext i
    rw [Pi.add_apply, GlobalTheory.SchrFixNbhd.adeleJoin_zero_apply]
    exact congrArg _ (add_zero (z i).1)
  have hgz : (fun i => ((z + GlobalTheory.WeilCont.adeleJoin F 0 x) i).2) = (fun i => (z i).2) + x := by
    funext i
    rw [Pi.add_apply, GlobalTheory.SchrFixNbhd.adeleJoin_zero_apply]
    rfl
  have hz : GlobalTheory.WeilM.pureA F f g (z + GlobalTheory.WeilCont.adeleJoin F 0 x) = GlobalTheory.WeilM.pureA F f g z := by
    simp only [GlobalTheory.WeilM.pureA]
    rw [hf, hgz, hx1]
  simp only [GlobalTheory.WeilM.schr]
  rw [hz]
  by_cases hg0 : g (fun i => (z i).2) = 0
  · simp only [GlobalTheory.WeilM.pureA, hg0, mul_zero]
  have hzc : (fun i => (z i).2) ∈ tsupport g := subset_tsupport _ hg0
  have harg : z ⬝ᵥ GlobalTheory.WeilCont.adeleJoin F 0 y + ⅟(2 : AdeleRing (𝓞 F) F) *
      (GlobalTheory.WeilCont.adeleJoin F 0 x ⬝ᵥ GlobalTheory.WeilCont.adeleJoin F 0 y) =
      ((0 : InfiniteAdeleRing F), (fun i => (z i).2) ⬝ᵥ y + (c • x) ⬝ᵥ y) := by
    rw [GlobalTheory.SchrFixNbhd.dotProduct_adeleJoin_zero, GlobalTheory.SchrFixNbhd.dotProduct_adeleJoin_zero, smul_dotProduct]
    refine Prod.ext ?_ ?_
    · show (0 : InfiniteAdeleRing F) + (⅟(2 : AdeleRing (𝓞 F) F)).1 * 0 = 0
      rw [mul_zero, add_zero]
    · show (fun i => (z i).2) ⬝ᵥ y + c * ((fun i => (GlobalTheory.WeilCont.adeleJoin F 0 x i).2) ⬝ᵥ y) = _
      rfl
  rw [harg]
  have h1 : ψ ((0 : InfiniteAdeleRing F), (fun i => (z i).2) ⬝ᵥ y + (c • x) ⬝ᵥ y) = 1 :=
    hH _ hzc (c • x) hx2 y hy
  rw [h1, one_mul]

end GlobalTheory.SchrUnifDen
