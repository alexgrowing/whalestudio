import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqOneAddOfSq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AnPer

theorem log_cocycle_cohomologous : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) (a lg : Λ → ∀ k, Hol (K.W k)) (β : Λ → Λ → Hol F.V), (∀ l k, IsUnit (a l k)) → (∀ l k c, dw c (a l k) = dw c (lg l k) * a l k) → (∀ l m k'' k' (h : K.le m k'' k'), a (l + m) k'' = Charts.sh h (a l k') * a m k'') → (∀ l m k'' k' (h : K.le m k'' k'), Charts.sh h (lg l k') = lg l k'' + K.cst k'' (β l m)) → (∀ l m k, lg (l + m) k = lg l k + lg m k) → ∀ (e : ∀ T : K.Obj, (T.C)ˣ) (uu : ∀ T T' : K.Obj, (T ⟶ T') → T'.C) (ℓ : ∀ T T' T'' : K.Obj, (T ⟶ T') → (T' ⟶ T'') → T''.C), (∀ (T T' : K.Obj) (φ : T ⟶ T'), uu T T' φ * φ.φ (e T : T.C) * T'.ρ (a φ.deg T'.k) - (e T' : T'.C) ∈ T'.J) → (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), ℓ T T' T'' φ ψ ∈ T''.J ∧ dpExp T''.δ (ℓ T T' T'' φ ψ) * uu T T'' (φ ≫ ψ) = ψ.φ (uu T T' φ) * uu T' T'' ψ) → ∃ c : GlobalTheory.CatCoh.C1 K.Oc, ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), ℓ T T' T'' φ ψ = (show T''.C from GlobalTheory.CatCoh.d1 K.Oc c T T' T'' φ ψ) + algebraMap (Hol F.V) T''.C (β φ.deg ψ.deg) := by

  intro I _ g Λ _ F K a lg β ha hdw hsh hlgsh hlgadd e uu ℓ huu hℓ
  have hnil : ∀ T : K.Obj, IsNilDP T.δ := fun T ↦ by letI := T.ratAlg; exact isPDNilpotent_of_rat _ T.nil
  have hdp : ∀ {T T' : K.Obj} (ψ : T ⟶ T'), DividedPowers.IsDPMorphism T.δ T'.δ (ψ.φ : T.C →+* T'.C) := fun {T T'} ψ ↦ by
    letI := T'.ratAlg; exact isDPMorphism_of_rat T.δ T'.δ (ψ.φ : T.C →+* T'.C) ψ.mem
  have hw : ∀ (T T' : K.Obj) (φ : T ⟶ T'), ∃ n ∈ T'.J, dpExp T'.δ n =
      uu T T' φ * φ.φ (e T : T.C) * T'.ρ (a φ.deg T'.k) * (((e T')⁻¹ : (T'.C)ˣ) : T'.C) := by
    intro T T' φ
    have hm : uu T T' φ * φ.φ (e T : T.C) * T'.ρ (a φ.deg T'.k) * (((e T')⁻¹ : (T'.C)ˣ) : T'.C) - 1 ∈ T'.J := by
      have := T'.J.mul_mem_right (((e T')⁻¹ : (T'.C)ˣ) : T'.C) (huu T T' φ)
      convert this using 1
      rw [sub_mul, Units.mul_inv]
    obtain ⟨x, hx, hx'⟩ := (GlobalTheory.Cris.ExpBij.dpExp_bijOn T'.C T'.J T'.δ (hnil T')).surjOn hm
    exact ⟨x, hx, hx'⟩
  choose n hnJ hn using hw
  refine ⟨fun T T' φ ↦ (n T T' φ - T'.ρ (lg φ.deg T'.k) : T'.C), ?_⟩
  intro T T' T'' φ ψ
  obtain ⟨hℓJ, hℓe⟩ := hℓ T T' T'' φ ψ
  have hce := close_exp T''.J T''.δ (hnil T'') _ _ (a φ.deg T'.k) (lg φ.deg T'.k) (hdw φ.deg T'.k) ψ.close
  have hxJ := ψ.close.sub_mem (lg φ.deg T'.k)
  simp only [RingHom.comp_apply, AlgHom.coe_toRingHom] at hce hxJ
  have hnat : ∀ c ∈ T'.J, ψ.φ (dpExp T'.δ c) = dpExp T''.δ (ψ.φ c) := fun c hc ↦
    (dpExp_add_and_natural _ _ _ _ T'.δ T''.δ (hnil T')).2 _ (hdp ψ) c hc
  have hadd := (dpExp_add_and_natural _ _ _ _ T''.δ T''.δ (hnil T'')).1
  have hQ : ψ.φ (((e T')⁻¹ : (T'.C)ˣ) : T'.C) * ψ.φ (e T' : T'.C) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have haa : T''.ρ (a (φ ≫ ψ).deg T''.k) = T''.ρ (Charts.sh (Charts.Hom.le ψ) (a φ.deg T'.k)) * T''.ρ (a ψ.deg T''.k) := by
    rw [Charts.comp_deg, hsh _ _ _ _ (Charts.Hom.le ψ), map_mul]
  have hn1 := hn T T'' (φ ≫ ψ)
  have hn2 := hn T T' φ
  have hn3 := hn T' T'' ψ
  rw [Charts.comp_φ, haa] at hn1
  set x := ψ.φ (T'.ρ (lg φ.deg T'.k)) - T''.ρ (Charts.sh (Charts.Hom.le ψ) (lg φ.deg T'.k)) with hx
  have key : dpExp T''.δ (ℓ T T' T'' φ ψ + n T T'' (φ ≫ ψ) + x) = dpExp T''.δ (ψ.φ (n T T' φ) + n T' T'' ψ) := by
    rw [hadd _ (T''.J.add_mem hℓJ (hnJ _ _ _)) _ hxJ, hadd _ hℓJ _ (hnJ _ _ _),
      hadd _ (ψ.mem _ (hnJ _ _ _)) _ (hnJ _ _ _), ← hnat _ (hnJ _ _ _), hn1, hn2, hn3]
    simp only [map_mul]
    linear_combination (ψ.φ (φ.φ (e T : T.C)) * T''.ρ (Charts.sh (Charts.Hom.le ψ) (a φ.deg T'.k)) * T''.ρ (a ψ.deg T''.k) *
        (((e T'')⁻¹ : (T''.C)ˣ) : T''.C) * dpExp T''.δ x) * hℓe
      - (ψ.φ (uu T T' φ) * ψ.φ (φ.φ (e T : T.C)) * ψ.φ (((e T')⁻¹ : (T'.C)ˣ) : T'.C) * uu T' T'' ψ * ψ.φ (e T' : T'.C) *
        T''.ρ (a ψ.deg T''.k) * (((e T'')⁻¹ : (T''.C)ˣ) : T''.C)) * hce
      - (ψ.φ (uu T T' φ) * uu T' T'' ψ * ψ.φ (φ.φ (e T : T.C)) * T''.ρ (Charts.sh (Charts.Hom.le ψ) (a φ.deg T'.k)) *
        T''.ρ (a ψ.deg T''.k) * (((e T'')⁻¹ : (T''.C)ˣ) : T''.C) * dpExp T''.δ x) * hQ
  have hinj := (GlobalTheory.Cris.ExpBij.dpExp_bijOn T''.C T''.J T''.δ (hnil T'')).injOn
    (T''.J.add_mem (T''.J.add_mem hℓJ (hnJ _ _ _)) hxJ) (T''.J.add_mem (ψ.mem _ (hnJ _ _ _)) (hnJ _ _ _)) key
  have hb : T''.ρ (Charts.sh (Charts.Hom.le ψ) (lg φ.deg T'.k)) = T''.ρ (lg φ.deg T''.k) + algebraMap (Hol F.V) T''.C (β φ.deg ψ.deg) := by
    rw [hlgsh _ _ _ _ (Charts.Hom.le ψ), map_add, T''.ρ_cst]
  show ℓ T T' T'' φ ψ = (ψ.φ (n T T' φ - T'.ρ (lg φ.deg T'.k)) - (n T T'' (φ ≫ ψ) - T''.ρ (lg (φ ≫ ψ).deg T''.k)) +
    (n T' T'' ψ - T''.ρ (lg ψ.deg T''.k))) + algebraMap (Hol F.V) T''.C (β φ.deg ψ.deg)
  rw [Charts.comp_deg, hlgadd, map_sub, map_add]
  rw [hx, hb] at hinj
  linear_combination hinj

end GlobalTheory.AnPer
