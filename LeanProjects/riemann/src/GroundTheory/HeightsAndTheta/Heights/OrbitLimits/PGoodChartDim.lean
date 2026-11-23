import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StGoodChartDim
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StConeVanishingHomog
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StConeSliceIdeal
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartDehomogPrime
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartDim
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGoodChartZeroSet
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartHomogenise
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartDehomog
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDim
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar mcPts segre)

namespace GoodChartDim

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def segreCone (P : Ideal (MRing ι)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) : Set (Fin m → ℂ) :=
  {x | ∃ z ∈ mcPts P, x = fun a => segre z (σ a)}

theorem segreCone_smul {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) :
    ∀ c ∈ segreCone P σ, ∀ a : ℂ, a ≠ 0 → a • c ∈ segreCone P σ := by
  rintro _ ⟨z, hz, rfl⟩ a ha
  obtain ⟨z', hz', hseg⟩ := GoodChartZeroSet.exists_segre_smul P hP.2.1.2.1 hz ha
    (fun h => absurd hP.1 (not_nonempty_iff.2 h))
  exact ⟨z', hz', funext fun b => by simp [hseg]⟩

open Classical in

def psiCoeffs {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    Fin m → ℂ :=
  fun a => Ψ (fun i' => if σ a = i' then (1 : ℂ) else 0) 0

theorem projChartSet_eq (P : Ideal (MRing ι)) {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    projChartSet P σ Ψ = {x | x ∈ segreCone P σ ∧ eval x (linForm (psiCoeffs σ Ψ)) = 1} := by
  have hl : ∀ z : (Σ k, ι k) → ℂ,
      eval (fun a => segre z (σ a)) (linForm (psiCoeffs σ Ψ)) = Ψ (segre z) 0 := fun z => by
    rw [show linForm (psiCoeffs σ Ψ) = GoodChartZeroSet.linForm σ Ψ from rfl, GoodChartZeroSet.eval_linForm]
    simp
  ext x
  constructor
  · rintro ⟨z, hz, h1, rfl⟩
    exact ⟨⟨z, hz, rfl⟩, (hl z).trans h1⟩
  · rintro ⟨⟨z, hz, rfl⟩, h1⟩
    exact ⟨z, hz, (hl z).symm.trans h1, rfl⟩

theorem linForm_single' {m : ℕ} (a : Fin m) : linForm (Pi.single a (1 : ℂ)) = X a := by
  classical
  simp [linForm, Pi.single_apply]

omit [∀ k, Fintype (ι k)] in

theorem segreChartSet_eq (P : Ideal (MRing ι)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (a : Fin m) :
    segreChartSet P σ (σ a) = {x | x ∈ segreCone P σ ∧ eval x (linForm (Pi.single a (1 : ℂ))) = 1} := by
  ext x
  simp only [segreChartSet, segreCone, Set.mem_ofPred_eq, linForm_single', eval_X]
  constructor
  · rintro ⟨z, hz, h1, rfl⟩
    exact ⟨⟨z, hz, rfl⟩, h1⟩
  · rintro ⟨⟨z, hz, rfl⟩, h1⟩
    exact ⟨z, hz, h1, rfl⟩

theorem linForm_sub_one_not_mem {m : ℕ} {V : Ideal (MvPolynomial (Fin m) ℂ)} (hV : IsHomogIdeal V) (hne : V ≠ ⊤)
    (t : Fin m → ℂ) : linForm t - 1 ∉ V := by
  intro h
  have h0 := hV _ h 0
  rw [homogeneousComponent_zero] at h0
  have hc : coeff 0 (linForm t - 1) = -1 := by
    simp [linForm, coeff_sum, coeff_C_mul, coeff_X]
  rw [hc] at h0
  exact hne (Ideal.eq_top_of_isUnit_mem _ h0 (by simp))

theorem exists_X_not_mem {m : ℕ} {W : Ideal (MvPolynomial (Fin m) ℂ)} {t : Fin m → ℂ} (h : linForm t ∉ W) :
    ∃ a, X a ∉ W := by
  by_contra hall
  push Not at hall
  exact h (Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ (hall a))

theorem le_of_homog_le_sup {m : ℕ} {V W : Ideal (MvPolynomial (Fin m) ℂ)} {t : Fin m → ℂ} (hV : IsHomogIdeal V)
    (hW : W.IsPrime) (hWh : IsHomogIdeal W) (ht : linForm t ∉ W) (hle : V ≤ W ⊔ Ideal.span {linForm t - 1}) :
    V ≤ W := by
  intro f hf
  rw [← sum_homogeneousComponent f]
  exact Ideal.sum_mem _ fun d _ => ChartDehomog.proof ℂ m W t _ d hW hWh ht
    (homogeneousComponent_isHomogeneous d f) (hle (hV f hf d))

theorem eq_of_add_one_eq {x : WithBot ℕ∞} {e : ℕ} (h : x + 1 = (e : WithBot ℕ∞) + 1) : x = e := by
  induction x using WithBot.recBotCoe with
  | bot =>
    rw [WithBot.bot_add, ← Nat.cast_succ] at h
    exact absurd h (WithBot.bot_ne_natCast _)
  | coe x =>
    induction x using ENat.recTopCoe with
    | top =>
      have h' : ((⊤ + 1 : ℕ∞) : WithBot ℕ∞) = ((e + 1 : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast h
      rw [WithBot.coe_inj, top_add] at h'
      exact absurd h' (by exact_mod_cast (ENat.top_ne_natCast (e + 1)))
    | coe x =>
      have h' : ((x + 1 : ℕ) : WithBot ℕ∞) = ((e + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast h
      have h'' : x + 1 = e + 1 := by exact_mod_cast h'
      exact_mod_cast (show x = e by omega)

end GoodChartDim

open GoodChartDim

theorem GoodChartDim.proof (h₁ : ConeVanishingHomog.Statement) (h₂ : ConeSliceIdeal.Statement)
    (h₃ : ChartDehomogPrime.Statement) : GoodChartDim.Statement := by
  classical
  intro K _ ι _ P e m σ Ψ hP J hJ
  have hC := segreCone_smul hP σ
  set t := psiCoeffs σ Ψ
  have hS : projChartSet P σ Ψ = {x | x ∈ segreCone P σ ∧ eval x (linForm t) = 1} := projChartSet_eq P σ Ψ
  have hJp : J.IsPrime := hJ.1.1
  have hIJ : projChartIdeal P σ Ψ ≤ J := hJ.1.2
  set H := vanishingIdeal ℂ (segreCone P σ)
  have hH : IsHomogIdeal H := h₁ m _ hC
  have hHI : H ≤ projChartIdeal P σ Ψ := by
    rw [projChartIdeal, hS]; exact vanishingIdeal_anti_mono fun x hx => hx.1
  have hℓ1 : linForm t - 1 ∈ projChartIdeal P σ Ψ := by
    rw [projChartIdeal, hS, mem_vanishingIdeal_iff]
    intro x hx
    simp [hx.2]

  obtain ⟨W, hW, hℓW, hWJ, hWcore⟩ := ChartHomogenise.proof ℂ m J t hJp (hIJ hℓ1)
  have hHW : H ≤ W := hWcore H hH (hHI.trans hIJ)
  obtain ⟨a, ha⟩ := exists_X_not_mem hℓW
  set u : Fin m → ℂ := Pi.single a 1
  have huW : linForm u ∉ W := by rw [linForm_single']; exact ha
  have hT : segreChartSet P σ (σ a) = {x | x ∈ segreCone P σ ∧ eval x (linForm u) = 1} :=
    segreChartSet_eq P σ a

  have := h₃ ℂ m W u hW huW
  have hTJ' : segreChartIdeal P σ (σ a) ≤ W ⊔ Ideal.span {linForm u - 1} := by
    rw [segreChartIdeal, hT]; exact h₂ m _ u W hC hHW
  obtain ⟨Q₀, hQ₀, hQ₀J'⟩ := Ideal.exists_minimalPrimes_le hTJ'
  have hdimQ₀ := SegreChartDim.proof K ι P e m σ (σ a) hP Q₀ (mem_segreChartComponents.2 hQ₀)
  have hu1 : linForm u - 1 ∈ segreChartIdeal P σ (σ a) := by
    rw [segreChartIdeal, hT, mem_vanishingIdeal_iff]
    intro x hx
    simp [hx.2]
  have hHT : H ≤ segreChartIdeal P σ (σ a) := by
    rw [segreChartIdeal, hT]; exact vanishingIdeal_anti_mono fun x hx => hx.1
  obtain ⟨V, hV, huV, hVQ₀, hVcore⟩ := ChartHomogenise.proof ℂ m Q₀ u hQ₀.1.1 (hQ₀.1.2 hu1)
  have hHV : H ≤ V := hVcore H hH (hHT.trans hQ₀.1.2)
  have hVW : V ≤ W := le_of_homog_le_sup hV.isHomog hW.isPrime hW.isHomog huW
    ((le_sup_left.trans hVQ₀.le).trans hQ₀J')

  have hIV : projChartIdeal P σ Ψ ≤ V ⊔ Ideal.span {linForm t - 1} := by
    rw [projChartIdeal, hS]; exact h₂ m _ t V hC hHV
  have hVJ : V ⊔ Ideal.span {linForm t - 1} ≤ J :=
    sup_le (hVW.trans (le_sup_left.trans hWJ.le)) ((Ideal.span_singleton_le_iff_mem _).2 (hIJ hℓ1))
  have hJmin : J ∈ (V ⊔ Ideal.span {linForm t - 1}).minimalPrimes :=
    ⟨⟨hJp, hVJ⟩, fun Z hZ hZJ => hJ.2 ⟨hZ.1, hIV.trans hZ.2⟩ hZJ⟩
  have hQ₀min : Q₀ ∈ (V ⊔ Ideal.span {linForm u - 1}).minimalPrimes := by
    have := hQ₀.1.1
    rw [hVQ₀, Ideal.minimalPrimes_eq_subsingleton_self]
    rfl

  have d₁ := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.dimPIT ℂ (Fin m) V J (linForm t - 1) hV.isPrime
    (linForm_sub_one_not_mem hV.isHomog hV.isPrime.ne_top t) hJmin
  have d₂ := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.dimPIT ℂ (Fin m) V Q₀ (linForm u - 1) hV.isPrime
    (linForm_sub_one_not_mem hV.isHomog hV.isPrime.ne_top u) hQ₀min
  rw [← d₂, hdimQ₀] at d₁
  exact eq_of_add_one_eq d₁

end GroundTheory.Heights₂.Heights
