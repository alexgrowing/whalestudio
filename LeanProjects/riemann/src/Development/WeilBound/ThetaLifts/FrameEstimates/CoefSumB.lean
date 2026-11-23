import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
import Development.WeilBound.ThetaLifts.FrameEstimates.CoefSumA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IndicatorMemSBOfIsClopen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSubgroupCountableAndExistsStrictFundamen
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsNhdsZeroPrincipalEqZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

def RatOfKer {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) : Prop :=
  {x : AF F | ∀ t ∈ (algebraMap F (AF F)).range, ψ (x * t) = 1} ⊆ (algebraMap F (AF F)).range

def Annih : Prop := ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → RatOfKer ψ

namespace CS

variable (F : Type) [Field F] [NumberField F] (κ : Type)

def ratH : (κ → F) →+ (κ → AF F) :=
  AddMonoidHom.mk' (fun ξ i => algebraMap F (AF F) (ξ i)) fun x y => by
    funext i
    simp only [Pi.add_apply, map_add]

variable {F κ}

theorem ratH_apply (ξ : κ → F) : ratH F κ ξ = fun i => algebraMap F (AF F) (ξ i) := rfl

variable [Fintype κ]

theorem ratH_dot (ξ η : κ → F) : ratH F κ ξ ⬝ᵥ ratH F κ η = algebraMap F (AF F) (ξ ⬝ᵥ η) := by
  simp [ratH_apply, dotProduct, map_sum, map_mul]

theorem dot_single (i : κ) [DecidableEq κ] (u : κ → AF F) (a : F) :
    u ⬝ᵥ ratH F κ (Pi.single i a) = algebraMap F (AF F) a * u i := by
  have : ratH F κ (Pi.single i a) = Pi.single i (algebraMap F (AF F) a) := by
    funext j
    by_cases h : j = i
    · subst h; simp [ratH_apply]
    · simp [ratH_apply, Pi.single_eq_of_ne h]
  rw [this, dotProduct_single, mul_comm]

theorem dual {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) (hann : RatOfKer ψ) :
    Dual (ratH F κ) fun ξ u => ψ (u ⬝ᵥ ratH F κ ξ) where
  inj := by
    have : Nontrivial (AF F) := by
      show Nontrivial (AdeleRing (𝓞 F) F)
      unfold AdeleRing
      infer_instance
    intro ξ η h
    funext l
    exact (algebraMap F (AF F)).injective (congrFun h l)
  cont ξ := by
    have h : Continuous fun u : κ → AF F => u ⬝ᵥ ratH F κ ξ :=
      continuous_finset_sum _ fun i _ => (continuous_apply i).mul continuous_const
    exact hψ.1.comp h
  norm ξ u := hψ.2.1 _
  addl ξ η u := by rw [map_add, dotProduct_add, AddChar.map_add_eq_mul]
  addr ξ u v := by rw [add_dotProduct, AddChar.map_add_eq_mul]
  triv ξ η := by rw [ratH_dot, hψ.2.2.1]
  sep u hu := by
    classical
    have key : ∀ i, ∃ c : F, algebraMap F (AF F) c = u i := fun i => hann (a := u i) (by
      rintro _ ⟨a, rfl⟩
      rw [mul_comm, ← dot_single]
      exact hu _)
    choose c hc using key
    exact ⟨c, funext hc⟩
  nondeg ξ hξ := by
    classical
    obtain ⟨x, hx⟩ := hψ.2.2.2
    obtain ⟨l, hl⟩ := Function.ne_iff.1 hξ
    refine ⟨Pi.single l (x * algebraMap F (AF F) (ξ l)⁻¹), ?_⟩
    rwa [single_dotProduct, ratH_apply, mul_assoc, ← map_mul, inv_mul_cancel₀ hl, map_one, mul_one]
  cpt := by
    obtain ⟨K, hK, hKc⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
    refine ⟨Set.univ.pi fun _ => K, isCompact_univ_pi fun _ => hK, fun u => ?_⟩
    choose ξ hξ using fun l => hKc (u l)
    exact ⟨ξ, fun l _ => hξ l⟩

theorem discrete : DiscreteTopology (ratH F κ).range := by
  obtain ⟨U, hU, hU0⟩ := GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F
  obtain ⟨V, hVU, hVo, h0V⟩ := mem_nhds_iff.1 hU
  rw [discreteTopology_iff_isOpen_singleton_zero]
  have : ({0} : Set (ratH F κ).range) = ((↑) : (ratH F κ).range → κ → AF F) ⁻¹' (Set.univ.pi fun _ => V) := by
    ext ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := hx
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · intro h i _
      have : ratH F κ y = 0 := congrArg Subtype.val h
      rw [this]; exact h0V
    · intro h
      have : y = 0 := funext fun i => hU0 (y i) (hVU (h i trivial))
      subst this
      exact Subtype.ext (map_zero _)
  rw [this]
  exact (isOpen_set_pi Set.finite_univ fun _ _ => hVo).preimage continuous_subtype_val

theorem exists_dom {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [hd : DiscreteTopology Γ]
    (m : Measure G) : ∃ D, IsAddFundamentalDomain Γ D m := by
  let : MeasurableSpace (Multiplicative G) := inferInstanceAs (MeasurableSpace G)
  have : BorelSpace (Multiplicative G) := inferInstanceAs (BorelSpace G)
  have : SecondCountableTopology (Multiplicative G) := inferInstanceAs (SecondCountableTopology G)
  have : DiscreteTopology (AddSubgroup.toSubgroup Γ) := hd
  obtain ⟨-, D, hDm, hD⟩ :=
    GlobalTheory.discreteSubgroup_countable_and_exists_strict_fundamentalDomain (AddSubgroup.toSubgroup Γ)
  have hDm' : MeasurableSet (Multiplicative.ofAdd ⁻¹' D : Set G) := hDm
  refine ⟨_, IsAddFundamentalDomain.mk' hDm'.nullMeasurableSet fun x => ?_⟩
  obtain ⟨γ, hγ, huniq⟩ := hD (Multiplicative.ofAdd x)
  refine ⟨⟨γ.1.toAdd, γ.2⟩, hγ, fun g hg => ?_⟩
  have := huniq ⟨Multiplicative.ofAdd g.1, g.2⟩ hg
  exact Subtype.ext (congrArg (fun s : AddSubgroup.toSubgroup Γ => Multiplicative.toAdd s.1) this)

end CS

open CS in

theorem coefSum_of_annih (hA : Annih) : CoefSum := by
  intro F _ _ κ _ ψ hstd μ hμ
  have hψ := GlobalTheory.StdCharFromIsStd.isCharAF hstd
  have : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have : BorelSpace (κ → AF F) := ⟨rfl⟩
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have := discrete (F := F) (κ := κ)
  have hd := dual (κ := κ) hψ (hA F ψ hstd)
  obtain ⟨D, hD⟩ := exists_dom (ratH F κ).range μ
  obtain ⟨c, hc, hP⟩ := hd.poisson_le hD
  refine ⟨c, hc, fun Φ₁ h₁ Φ₂ h₂ => ?_⟩
  obtain ⟨c₁, b₁⟩ := GlobalTheory.CompanionTheory.ThetaCoord.Cont.schA_bound h₁
  obtain ⟨c₂, b₂⟩ := GlobalTheory.CompanionTheory.ThetaCoord.Cont.schA_bound h₂
  have s₁ : Summable fun ξ => ‖Φ₁ (ratH F κ ξ)‖ := summable_norm_of_mem_schA F h₁
  have s₂ : Summable fun ξ => ‖(starRingEnd ℂ) (Φ₂ (ratH F κ ξ))‖ := by
    simp only [Complex.norm_conj]
    exact summable_norm_of_mem_schA F h₂
  have hx : ∀ x : κ → F, ‖∑' ξ, Φ₁ (ratH F κ ξ + ratH F κ x) * (starRingEnd ℂ) (Φ₂ (ratH F κ ξ))‖ₑ ≤
      ENNReal.ofReal c * ∑' y : κ → F, ‖coef F ψ μ Φ₁ Φ₂ (ratH F κ x, ratH F κ y)‖ₑ := by
    intro x
    refine (hP (fun u => Φ₁ (u + ratH F κ x) * (starRingEnd ℂ) (Φ₂ u))
      ((c₁.comp (continuous_id.add continuous_const)).mul (Complex.continuous_conj.comp c₂)) fun K hK => ?_).trans
      (le_of_eq ?_)
    · obtain ⟨u, hu, hub⟩ := b₁ K hK
      obtain ⟨v, hv, hvb⟩ := b₂ K hK
      obtain ⟨M, hM⟩ := hu.tendsto_cofinite_zero.bddAbove_range_of_cofinite
      refine ⟨fun ξ => M * v ξ, hv.mul_left M, fun ξ a ha => ?_⟩
      have h1 : ‖Φ₁ (ratH F κ ξ + a + ratH F κ x)‖ ≤ M := by
        rw [add_right_comm, ← map_add]
        exact (hub (ξ + x) a ha).trans (hM ⟨_, rfl⟩)
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul h1 (hvb ξ a ha) (norm_nonneg _) ((norm_nonneg _).trans h1)
    · congr 1
      refine tsum_congr fun y => ?_
      have h2 : ⅟(2 : AF F) * (ratH F κ x ⬝ᵥ ratH F κ y) = algebraMap F (AF F) (2⁻¹ * (x ⬝ᵥ y)) := by
        rw [ratH_dot, invOf_mul_eq_iff_eq_mul_left, ← map_ofNat (algebraMap F (AF F)) 2, ← map_mul,
          mul_inv_cancel_left₀ two_ne_zero]
      simp only [coef, schr, h2, AddChar.map_add_eq_mul, hψ.2.2.1, mul_one, mul_assoc]
  have hs := summable_mul_of_summable_norm s₁ s₂
  let e : (κ → F) × (κ → F) ≃ (κ → F) × (κ → F) :=
    { toFun := fun p => (p.2 + p.1, p.2)
      invFun := fun p => (p.1 - p.2, p.2)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  have hs' := e.summable_iff.2 hs
  have hmain : thetaSum F Φ₁ * (starRingEnd ℂ) (thetaSum F Φ₂) =
      ∑' x : κ → F, ∑' ξ, Φ₁ (ratH F κ ξ + ratH F κ x) * (starRingEnd ℂ) (Φ₂ (ratH F κ ξ)) := by
    have e2 : (starRingEnd ℂ) (thetaSum F Φ₂) = ∑' ξ, (starRingEnd ℂ) (Φ₂ (ratH F κ ξ)) := Complex.conj_tsum _
    have e1 : thetaSum F Φ₁ = ∑' ξ, Φ₁ (ratH F κ ξ) := rfl
    rw [e1, e2, tsum_mul_tsum_of_summable_norm s₁ s₂, ← e.tsum_eq]
    refine hs'.tsum_prod.trans ?_
    simp only [← map_add]
    rfl
  calc ‖thetaSum F Φ₁‖ₑ * ‖thetaSum F Φ₂‖ₑ = ‖thetaSum F Φ₁ * (starRingEnd ℂ) (thetaSum F Φ₂)‖ₑ := by
        rw [enorm_mul, ← ofReal_norm ((starRingEnd ℂ) _), Complex.norm_conj, ofReal_norm]
    _ ≤ ∑' x : κ → F, ENNReal.ofReal c * ∑' y : κ → F, ‖coef F ψ μ Φ₁ Φ₂ (ratH F κ x, ratH F κ y)‖ₑ := by
        rw [hmain]
        exact enorm_tsum_le_tsum_enorm.trans (ENNReal.tsum_le_tsum hx)
    _ = _ := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_prod']
        rfl

end PositivityTheory.ThKEst

end
