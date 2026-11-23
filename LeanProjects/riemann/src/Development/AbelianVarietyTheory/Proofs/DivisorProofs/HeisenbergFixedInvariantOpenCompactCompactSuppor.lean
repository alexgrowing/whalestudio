import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedSpaceVecPairAsAdeles
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompactAnnihilatorFiniteAdelesStdChar
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
import Formalism.LocalToGlobal.Columns.RecLevelTop
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.FundamentalContinuity.AdelicIsomorphismStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilAdm

open Filter Topology

theorem fixSupp_exists_box {κ X : Type} [Fintype κ] [TopologicalSpace X] {S : Set (κ → X)} {x0 : X}
    (hS : S ∈ 𝓝 (fun _ : κ => x0)) : ∃ O ∈ 𝓝 x0, ∀ u : κ → X, (∀ i, u i ∈ O) → u ∈ S := by
  rw [nhds_pi, Filter.mem_pi] at hS
  obtain ⟨I, -, t, ht, hsub⟩ := hS
  exact ⟨⋂ i, t i, Filter.iInter_mem.2 ht, fun u hu => hsub fun i _ => Set.mem_iInter.1 (hu i) i⟩

variable {F : Type} [Field F] [NumberField F]

theorem fixSupp_finE_zero {κ : Type} : finE F (0 : κ → FiniteAdeleRing (𝓞 F) F) = 0 := by
  funext i; rfl

theorem fixSupp_finE_single {κ : Type} [DecidableEq κ] (j : κ) (t : FiniteAdeleRing (𝓞 F) F) :
    finE F (Pi.single j t : κ → FiniteAdeleRing (𝓞 F) F) = Pi.single j (pairA F 0 t) := by
  funext i
  by_cases hij : i = j
  · subst hij
    show pairA F 0 ((Pi.single i t : κ → FiniteAdeleRing (𝓞 F) F) i) = (Pi.single i (pairA F 0 t) : κ → AdeleRing (𝓞 F) F) i
    rw [Pi.single_eq_same, Pi.single_eq_same]
  · simp only [finE, Pi.single_eq_of_ne hij]; rfl

theorem fixed_schroedinger_invariant_compactSupport_bounded_annihilator (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (hann : ∀ O ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F), ∃ K : Set (FiniteAdeleRing (𝓞 F) F), IsCompact K ∧
      ∀ x : FiniteAdeleRing (𝓞 F) F, (∀ t ∈ O, ψ (pairA F 0 (t * x)) = 1) → x ∈ K)
    (κ : Type) [Fintype κ]
    (M : AddSubgroup ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)))
    (hM : IsOpen (M : Set ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)))) :
    ∃ (U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)) (K : Set (κ → FiniteAdeleRing (𝓞 F) F)),
      IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧ IsCompact (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
      IsCompact K ∧ ∀ Φ : (κ → AdeleRing (𝓞 F) F) → ℂ, (∀ m ∈ M, GlobalTheory.WeilM.schr ψ (finE2 F m) Φ = Φ) →
        (∀ x, ∀ u ∈ U, Φ (x + finE F u) = Φ x) ∧ ∀ x, (fun i => (x i).2) ∉ K → Φ x = 0 := by
  classical
  have hc1 : Continuous fun u : κ → FiniteAdeleRing (𝓞 F) F => (u, (0 : κ → FiniteAdeleRing (𝓞 F) F)) :=
    continuous_id.prodMk continuous_const
  have hc2 : Continuous fun v : κ → FiniteAdeleRing (𝓞 F) F => ((0 : κ → FiniteAdeleRing (𝓞 F) F), v) :=
    continuous_const.prodMk continuous_id
  have hM1 : (fun u : κ → FiniteAdeleRing (𝓞 F) F => (u, (0 : κ → FiniteAdeleRing (𝓞 F) F))) ⁻¹'
      (M : Set _) ∈ 𝓝 (fun _ : κ => (0 : FiniteAdeleRing (𝓞 F) F)) :=
    (hM.preimage hc1).mem_nhds M.zero_mem
  have hM2 : (fun v : κ → FiniteAdeleRing (𝓞 F) F => ((0 : κ → FiniteAdeleRing (𝓞 F) F), v)) ⁻¹'
      (M : Set _) ∈ 𝓝 (fun _ : κ => (0 : FiniteAdeleRing (𝓞 F) F)) :=
    (hM.preimage hc2).mem_nhds M.zero_mem
  obtain ⟨O₁, hO₁, hbox₁⟩ := fixSupp_exists_box hM1
  obtain ⟨O₂, hO₂, hbox₂⟩ := fixSupp_exists_box hM2
  obtain ⟨N, hN, hNO⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F O₁ hO₁
  obtain ⟨K₀, hK₀, hK₀mem⟩ := hann O₂ hO₂
  let c : FiniteAdeleRing (𝓞 F) F := algebraMap F _ ((N : F)⁻¹)
  have hcN : (N : FiniteAdeleRing (𝓞 F) F) * c = 1 := by
    rw [← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) N, ← map_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), map_one]
  have hNc : c * (N : FiniteAdeleRing (𝓞 F) F) = 1 := by rw [mul_comm]; exact hcN
  let h : (κ → FiniteAdeleRing (𝓞 F) F) ≃ₜ (κ → FiniteAdeleRing (𝓞 F) F) :=
    { toFun := fun u i => c * u i
      invFun := fun u i => (N : FiniteAdeleRing (𝓞 F) F) * u i
      left_inv := fun u => funext fun i => by
        show (N : FiniteAdeleRing (𝓞 F) F) * (c * u i) = u i
        rw [← mul_assoc, hcN, one_mul]
      right_inv := fun u => funext fun i => by
        show c * ((N : FiniteAdeleRing (𝓞 F) F) * u i) = u i
        rw [← mul_assoc, hNc, one_mul]
      continuous_toFun := continuous_pi fun i => continuous_const.mul (continuous_apply i)
      continuous_invFun := continuous_pi fun i => continuous_const.mul (continuous_apply i) }
  let φ : (κ → FiniteAdeleRing (𝓞 F) F) →+ (κ → FiniteAdeleRing (𝓞 F) F) :=
    { toFun := fun u i => c * u i
      map_zero' := by funext i; exact mul_zero c
      map_add' := fun u w => by funext i; exact mul_add c (u i) (w i) }
  let U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) :=
    (AddSubgroup.pi Set.univ fun _ => (Formalism.UG.intAd F).toAddSubgroup).comap φ
  have hUset : (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) =
      h ⁻¹' Set.univ.pi fun _ => (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := rfl
  have hint_c : IsCompact (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := Formalism.L2.Col.rlt_isCompact_intAd
  have hint_o : IsOpen (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := Formalism.L2.SG.Pf.top_isOpen_intAd F
  refine ⟨U, Set.univ.pi fun _ => K₀, ?_, ?_, isCompact_univ_pi fun _ => hK₀, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · rw [hUset]; exact (isOpen_set_pi Set.finite_univ fun _ _ => hint_o).preimage h.continuous
  · rw [hUset]; exact h.isCompact_preimage.2 (isCompact_univ_pi fun _ => hint_c)
  · intro x u hu
    have hu1 : ∀ i, u i ∈ O₁ := by
      intro i
      have hi : c * u i ∈ Formalism.UG.intAd F := hu i (Set.mem_univ i)
      have := hNO (c * u i) hi
      rwa [nsmul_eq_mul, ← mul_assoc, hcN, one_mul] at this
    have hm : (u, (0 : κ → FiniteAdeleRing (𝓞 F) F)) ∈ M := hbox₁ u hu1
    have := congrFun (hΦ _ hm) x
    simp only [GlobalTheory.WeilM.schr, finE2, fixSupp_finE_zero, dotProduct_zero, mul_zero, add_zero,
      AddChar.map_zero_eq_one, one_mul] at this
    exact this
  · intro x hx
    by_contra hne
    apply hx
    intro j _
    apply hK₀mem
    intro t ht
    have hv : ∀ i, (Pi.single j t : κ → FiniteAdeleRing (𝓞 F) F) i ∈ O₂ := by
      intro i
      by_cases hij : i = j
      · subst hij; rw [Pi.single_eq_same]; exact ht
      · rw [Pi.single_eq_of_ne hij]; exact mem_of_mem_nhds hO₂
    have hm : ((0 : κ → FiniteAdeleRing (𝓞 F) F), (Pi.single j t : κ → FiniteAdeleRing (𝓞 F) F)) ∈ M :=
      hbox₂ _ hv
    have h1 := congrFun (hΦ _ hm) x
    simp only [GlobalTheory.WeilM.schr, finE2, fixSupp_finE_zero, zero_dotProduct, mul_zero, add_zero] at h1
    rw [fixSupp_finE_single, dotProduct_single] at h1
    have hdot : x j * pairA F 0 t = pairA F 0 (t * (x j).2) :=
      Prod.ext (by show (x j).1 * 0 = 0; exact mul_zero _) (by show (x j).2 * t = t * (x j).2; exact mul_comm _ _)
    rw [hdot] at h1
    exact mul_right_cancel₀ hne (h1.trans (one_mul _).symm)

theorem fixed_invariant_compactSupport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (κ : Type) [Fintype κ]
    (M : AddSubgroup ((κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F) × (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F))), IsOpen (M : Set ((κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F) × (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F))) →
      ∃ (U : AddSubgroup (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (K : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)), IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧
        IsCompact (U : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧ IsCompact K ∧
        ∀ Φ : (κ → AF D.host.F) → ℂ, (∀ m ∈ M, GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilAdm.finE2 D.host.F m) Φ = Φ) →
          (∀ x, ∀ u ∈ U, Φ (x + GlobalTheory.WeilAdm.finE D.host.F u) = Φ x) ∧ ∀ x, (fun i => (x i).2) ∉ K → Φ x = 0 := by
  intro D ψ hψ κ _ M hM
  exact fixed_schroedinger_invariant_compactSupport_bounded_annihilator ψ (GlobalTheory.ScalarAnnih.exists_compact_of_annih D ψ hψ) κ M hM

end GlobalTheory.WeilAdm

end
