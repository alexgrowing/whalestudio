import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTw
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulMemOfHatCosetIndNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralPeriodicCompactSupportEqFiniteSum

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.TwBridge.TopHat

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem hat_coset_box [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n]
    {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν) {ε : k}
    (hε : ε ∈ 𝒪[k]) (c : kˣ) (y₀ : n → k) {η : n → k} (hη : ∀ i, η i * (c : k) ∈ 𝒪[k]) :
    hat ψ ν ε (cosetInd (box n c) (Submodule.Quotient.mk y₀)) η =
      ((nabs k c ^ Fintype.card n : ℝ) : ℂ) * ψ (ε * (η ⬝ᵥ y₀)) := by
  have := hν.1
  have := secondCountable k
  unfold hat
  rw [← integral_add_left_eq_self _ y₀]
  have e : ∀ y : n → k, cosetInd (box n c) (Submodule.Quotient.mk y₀) (y₀ + y) * (ψ (ε * (η ⬝ᵥ (y₀ + y))) : ℂ) =
      (Set.pi Set.univ fun _ => cball c).indicator (fun _ => (ψ (ε * (η ⬝ᵥ y₀)) : ℂ)) y := fun y => by
    have hy : (y₀ + y ∈ {y' : n → k | Submodule.Quotient.mk (p := box n c) y' = Submodule.Quotient.mk y₀}) ↔
        y ∈ Set.pi Set.univ fun _ => cball c := by
      simp [Submodule.Quotient.eq, mem_box, cball]
    by_cases h : y ∈ Set.pi Set.univ fun _ => cball c
    · have hi : ε * (η ⬝ᵥ y) ∈ 𝒪[k] := by
        refine mul_mem hε (sum_mem fun i _ => ?_)
        have h1 : valuation k (y i) ≤ valuation k (c : k) := h i trivial
        have h2 := (Valuation.mem_integer_iff _ _).1 (hη i)
        rw [Valuation.mem_integer_iff, map_mul]
        rw [map_mul] at h2
        calc valuation k (η i) * valuation k (y i) ≤ valuation k (η i) * valuation k (c : k) := mul_le_mul' le_rfl h1
          _ ≤ 1 := h2
      rw [cosetInd, Set.indicator_of_mem (hy.2 h), Set.indicator_of_mem h, dotProduct_add, mul_add,
        AddChar.map_add_eq_mul, hψ.eq_one (show _ ∈ cball (1 : kˣ) from hi)]
      simp
    · rw [cosetInd, Set.indicator_of_notMem (mt hy.1 h), Set.indicator_of_notMem h, zero_mul]
  simp only [e]
  rw [integral_indicator_const _ (MeasurableSet.univ_pi fun _ => (isOpen_cball c).measurableSet), Measure.real,
    Measure.pi_pi]
  simp only [measure_cball ν c, hν.2, mul_one, Finset.prod_const, Finset.card_univ]
  simp [nabs, ENNReal.toReal_pow]

theorem hat_coset_eq_ftY : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → 2 * cst.M ≤ cst.D P →
  ∀ (e' : XIx (Fin R.k) (Fin R.t) (s + 1) ≃ Fin (R.N (s + 1))) (e : Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2) ⊕ Unit ≃ Fin (R.N R.m)),
    IsOrd xPos e' → IsOrd (Sum.elim zPos fun _ => R.N R.m - 1) e →
    ∀ (y : HomE X.E (R.N (s + 1)) (R.N R.m)) (y' : Sp X.E (R.N (s + 1))), (∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y' l)) →
      hat W.ψ ν (-1) (cosetInd (box _ (W.ϖ ^ cst.M)) (Submodule.Quotient.mk fun a => ι (y' (e' a)))) ((toLoc ι e e' y) (Sum.inr ())) =
        σ₀ (ftY sel mu cst P (atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ y) y') := by
  classical
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hν _ hA hD e' e _ he y y' hy'
  haveI := hν.1
  have hint : ∀ a : X.E, ι a ∈ 𝒪[k] ↔ IntAt P.1 a := hA.compl.int
  have hlast : (e (Sum.inr ())).val = R.N R.m - 1 := he (Sum.inr ())
  have hNpos : R.N R.m - 1 < R.N R.m := by have := (e (Sum.inr ())).isLt; omega
  set η' := atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ y with hη'
  have hη'v : ∀ v, η' v = y v (e (Sum.inr ())) := fun v => by
    simp only [hη', LinearMap.comp_apply, atNL, dif_pos hNpos, LinearMap.proj_apply]
    rw [show (⟨R.N R.m - 1, hNpos⟩ : Fin (R.N R.m)) = e (Sum.inr ()) from Fin.ext hlast.symm]
  have hrow : (toLoc ι e e' y) (Sum.inr ()) = fun a => ι (η' (Pi.single (e' a) 1)) := by
    funext a; simp [toLoc, hη'v]
  have hsum : η' y' = ∑ i, y' i * η' (Pi.single i 1) := by
    have : y' = ∑ i, y' i • Pi.single i (1 : X.E) := by ext j; simp [Pi.single_apply]
    conv_lhs => rw [this]
    simp [map_sum, map_smul]
  have hdot : (fun a => ι (η' (Pi.single (e' a) 1))) ⬝ᵥ (fun a => ι (y' (e' a))) = ι (η' y') := by
    rw [hsum, map_sum, dotProduct]
    exact Fintype.sum_equiv e' _ _ (fun a => by simp [mul_comm])
  have hϖ : (W.ϖ : k) = ι (qOf P.1 : X.E) := hA.compl.unif
  have hcM : ((W.ϖ ^ cst.M : kˣ) : k) = ι ((qOf P.1 : X.E) ^ cst.M) := by
    rw [Units.val_pow_eq_pow_val, hϖ, map_pow]
  rw [hrow, ftY, if_neg hA.nmem]
  by_cases hη : ∀ i : Fin (R.N (s + 1)), IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * η' (Pi.single i 1))
  · rw [if_pos hη, hat_coset_box W.cond hν (neg_mem (one_mem _)) _ _ (fun a => ?_), hdot]
    · have hres : resCard k = qOf P.1 := ComplRes.resCard_eq hA.compl W.unif
      obtain ⟨p, hp, hpϖ⟩ := GlobalTheory.PeriodicIntegral.exists_irreducible_of_isUnif W.unif
      have hnabs : nabs k W.ϖ = (resCard k : ℝ)⁻¹ := nabs_uniformiser hp hpϖ.symm
      have hnM : nabs k (W.ϖ ^ cst.M) = ((qOf P.1 : ℝ) ^ cst.M)⁻¹ := by
        rw [show nabs k (W.ϖ ^ cst.M) = nabs k W.ϖ ^ cst.M by simp [nabs], hnabs, hres, inv_pow]
      have hcard : Fintype.card (XIx (Fin R.k) (Fin R.t) (s + 1)) = R.N (s + 1) := by
        simpa using Fintype.card_congr e'
      have hqi : ∀ j, ι ((qOf P.1 : X.E) ^ j) ∈ 𝒪[k] := fun j => by
        rw [map_pow, map_natCast]; exact pow_mem (natCast_mem _ _) _
      have hi : IntAt P.1 ((qOf P.1 : X.E) ^ cst.D P * ((epsSg : X.E) * η' y')) := by
        rw [← hint, hsum]
        obtain ⟨d, hd⟩ : ∃ d, cst.D P = d + 2 * cst.M := ⟨_, (Nat.sub_add_cancel hD).symm⟩
        have : (qOf P.1 : X.E) ^ cst.D P * ((epsSg : X.E) * ∑ i, y' i * η' (Pi.single i 1)) =
            -((qOf P.1 : X.E) ^ d *
              ∑ i, ((qOf P.1 : X.E) ^ cst.M * y' i) * ((qOf P.1 : X.E) ^ cst.M * η' (Pi.single i 1))) := by
          rw [hd, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [epsSg, Int.cast_neg, Int.cast_one]
          ring
        rw [this, map_neg, map_mul, map_sum]
        exact neg_mem (mul_mem (hqi _) (sum_mem fun i _ => by
          rw [map_mul]; exact mul_mem ((hint _).2 (hy' i)) ((hint _).2 (hη i))))
      have h1 := hA.psi _ hi
      have h2 : ι ((epsSg : X.E) * η' y') = -1 * ι (η' y') := by simp [epsSg]
      rw [map_mul σ₀, ← h1, h2, map_inv₀, map_pow, map_natCast, hnM, hcard]
      push_cast
      rw [inv_pow, ← pow_mul]
    · rw [show (fun a => ι (η' (Pi.single (e' a) 1))) a * ((W.ϖ ^ cst.M : kˣ) : k) =
        ι ((qOf P.1 : X.E) ^ cst.M * η' (Pi.single (e' a) 1)) by rw [hcM, ← map_mul, mul_comm]]
      exact (hint _).2 (hη _)
  · rw [if_neg hη, map_zero]
    by_contra hne
    have hm := mul_mem_of_hat_cosetInd_ne_zero k W.ψ W.cond ν _ (W.ϖ ^ cst.M) (-1) _ _ hne
    refine hη fun i => (hint _).1 ?_
    have h' := neg_mem (hm (e'.symm i))
    convert h' using 1
    rw [map_mul, ← hcM]
    simp only [Equiv.apply_symm_apply]
    ring

end GlobalTheory.TwBridge.TopHat
