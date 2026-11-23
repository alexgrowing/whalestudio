import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodLiftOnto
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IntegralFundamentalDomainEqSumDoubleCoset
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ClassUnfold

theorem integral_eq_sum_of_surjective {G H : Type} [Group G] [Group H] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsMulLeftInvariant] (Γ : Subgroup G) [Countable Γ]
    (π : G →* H) (hπ : Function.Surjective π) (J : Subgroup H) (𝓖 : Set G) (h𝓖 : IsFundamentalDomain Γ 𝓖 ν)
    (ho : IsOpen (J.comap π : Set G)) (h1 : ν (J.comap π) = 1) (I : Type) [Fintype I] (y : I → H)
    (hy : Bridge.IsReps (π.comp Γ.subtype) J y) (hf : ∀ c, Finite (Bridge.stab (π.comp Γ.subtype) J (y c)))
    (Φ : H → ℂ) (hΦ : ∀ (γ : Γ) h (k : J), Φ (π.comp Γ.subtype γ * h * k) = Φ h) :
    ∫ h in 𝓖, Φ (π h) ∂ν = ∑ c, (Nat.card (Bridge.stab (π.comp Γ.subtype) J (y c)) : ℂ)⁻¹ * Φ (y c) := by
  choose h hh using fun c => hπ (y c)
  have hS : ∀ c, {γ : G | γ ∈ Γ ∧ (h c)⁻¹ * γ * h c ∈ J.comap π} =
      Subtype.val '' (Bridge.stab (π.comp Γ.subtype) J (y c) : Set Γ) := by
    intro c
    ext γ
    simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe, Bridge.mem_stab, Subgroup.mem_comap, map_mul,
      map_inv, hh]
    constructor
    · rintro ⟨a, b⟩
      exact ⟨⟨γ, a⟩, b, rfl⟩
    · rintro ⟨δ, b, rfl⟩
      exact ⟨δ.2, b⟩
  have hfin : ∀ c, (Bridge.stab (π.comp Γ.subtype) J (y c) : Set Γ).Finite := fun c => hf c
  have key := GlobalTheory.Ker.integral_fundamentalDomain_eq_sum_doubleCoset G ν Γ (J.comap π) 𝓖 h𝓖 ho
    (by rw [h1]; exact ENNReal.one_ne_top) I h ?_ (fun c => by rw [hS]; exact (hfin c).image _)
    (fun x => Φ (π x)) ?_ ?_
  · rw [key.2.2, h1]
    simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hS, Set.ncard_image_of_injective _ Subtype.val_injective, hh]
    rfl
  · intro x
    refine (existsUnique_congr fun i => ?_).1 (hy (π x))
    constructor
    · rintro ⟨γ, k, e⟩
      refine ⟨γ, γ.2, (γ * h i)⁻¹ * x, ?_, by group⟩
      rw [Subgroup.mem_comap, map_mul, map_inv, map_mul, hh, e]
      change (π γ * y i)⁻¹ * (π γ * y i * k) ∈ J
      rw [inv_mul_cancel_left]
      exact k.2
    · rintro ⟨γ, hγ, k, hk, rfl⟩
      exact ⟨⟨γ, hγ⟩, ⟨π k, hk⟩, by rw [map_mul, map_mul, hh]; rfl⟩
  · intro γ hγ x
    have := hΦ ⟨γ, hγ⟩ (π x) 1
    rw [OneMemClass.coe_one, mul_one] at this
    rw [map_mul]
    exact this
  · intro k hk x
    have := hΦ 1 (π x) ⟨π k, hk⟩
    rw [map_one, one_mul] at this
    rw [map_mul]
    exact this

theorem integral_eq_classSum : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), L.P.H = ⊥ → IsMeasDef V (lev D.sp.cm V.gram β L) μ 𝓕 → ∀ (I : Type) [Fintype I] (y : I → Bridge.Gf V), Bridge.IsReps (Bridge.ratF V) (levEnv V β L).J y → (∀ c, Finite (Bridge.stab (Bridge.ratF V) (levEnv V β L).J (y c))) → ∀ Φ : Bridge.Gf V → ℂ, (∀ (γ : GQ V) h (k : (levEnv V β L).J), Φ (Bridge.ratF V γ * h * k) = Φ h) → ∫ h in 𝓕, Φ (fin V h) ∂μ = ∑ c, (Nat.card (Bridge.stab (Bridge.ratF V) (levEnv V β L).J (y c)) : ℂ)⁻¹ * Φ (y c) := by
  intro D V β L μ 𝓕 hL hμ I _ y hy hf Φ hΦ
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  haveI := hμ.1.1
  have hK : (levEnv V β L).J.comap (finHom V).rangeRestrict = (lev D.sp.cm V.gram β L).comap (finE V) := by
    ext g
    change (finE V g ∈ parLev D.sp.cm V.gram β L ∧ rTup β L (finE V g) ∈ (⊥ : Subgroup _)) ↔
      (finE V g ∈ parLev D.sp.cm V.gram β L ∧ rTup β L (finE V g) ∈ L.P.H)
    rw [hL]
  refine integral_eq_sum_of_surjective μ (GQ V) (finHom V).rangeRestrict (finHom V).rangeRestrict_surjective
    (levEnv V β L).J 𝓕 hμ.2 ?_ ?_ I y hy hf Φ hΦ
  · refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    filter_upwards [GlobalTheory.ThetaIntegrand.eventually_level V β L] with κ hκ
    exact hκ.1
  · rw [hK]
    exact GlobalTheory.Mass.Levels.measure_comap_finE hμ.1

end GlobalTheory.ClassUnfold
