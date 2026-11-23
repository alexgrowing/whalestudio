import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HarrisTaylorCardKilledByIdealEqAbsNormPow
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.HermitianCharacters.SelfDualLatticeFiltrationCharacter
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalDensityOfSelfDualLatticeLemmas
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiV

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

def ball (v : HeightOneSpectrum (𝓞 F)) (m : ℤ) : AddSubgroup (Fv F v) where
  carrier := {x | Valued.v x ≤ WithZero.exp m}
  add_mem' := by
    intro a b ha hb
    change Valued.v (a + b) ≤ _
    exact (Valuation.map_add _ a b).trans (max_le ha hb)
  zero_mem' := by
    change Valued.v (0 : Fv F v) ≤ _
    simp
  neg_mem' := by
    intro a ha
    change Valued.v (-a) ≤ _
    rw [Valuation.map_neg]
    exact ha

theorem mem_ball (m : ℤ) (x : Fv F v) : x ∈ ball v m ↔ Valued.v x ≤ WithZero.exp m := Iff.rfl

theorem ball_isCompact (m : ℤ) : IsCompact (ball v m : Set (Fv F v)) :=
  (GlobalTheory.LatticeDensity.ball_compact_open v m).1

theorem ball_isOpen (m : ℤ) : IsOpen (ball v m : Set (Fv F v)) :=
  (GlobalTheory.LatticeDensity.ball_compact_open v m).2

theorem ball_le {a b : ℤ} (hab : a ≤ b) : (ball v a : Set (Fv F v)) ⊆ ball v b :=
  fun _ hx => le_trans ((mem_ball _ _).1 hx) (WithZero.exp_le_exp.2 hab)

theorem exists_mem_ball (x : Fv F v) : ∃ m, x ∈ ball v m := by
  by_cases hx : Valued.v x = 0
  · exact ⟨0, by rw [mem_ball, hx]; exact zero_le'⟩
  · exact ⟨WithZero.log (Valued.v x), by rw [mem_ball, WithZero.exp_log hx]⟩

theorem exists_ball_of_isCompact (K : Set (Fv F v)) (hK : IsCompact K) :
    ∃ m, K ⊆ ball v m := by
  refine hK.elim_directed_cover (fun m : ℤ => (ball v m : Set (Fv F v))) ball_isOpen ?_
    (Monotone.directed_le fun a b hab => ball_le hab)
  intro x _
  obtain ⟨m, hm⟩ := exists_mem_ball x
  exact Set.mem_iUnion.2 ⟨m, hm⟩

theorem exists_ball_subset (U : Set (Fv F v)) (hU : U ∈ 𝓝 (0 : Fv F v)) :
    ∃ m, (ball v m : Set (Fv F v)) ⊆ U := by
  obtain ⟨W, hWU, hWo, h0⟩ := mem_nhds_iff.1 hU
  have hcl : ∀ m : ℤ, IsClosed (ball v m : Set (Fv F v)) := fun m => (ball_isCompact m).isClosed
  obtain ⟨n, hn⟩ := (ball_isCompact (v := v) 0).elim_directed_cover
    (fun n : ℕ => W ∪ (ball v (-(n : ℤ)) : Set (Fv F v))ᶜ)
    (fun n => hWo.union (hcl _).isOpen_compl)
    (by
      intro x _
      by_cases hx : x = 0
      · exact Set.mem_iUnion.2 ⟨0, Or.inl (hx ▸ h0)⟩
      · have hv : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
        refine Set.mem_iUnion.2 ⟨(WithZero.log (Valued.v x)).natAbs + 1, Or.inr fun hm => ?_⟩
        have h1 := WithZero.exp_le_exp.1 ((WithZero.exp_log hv).le.trans ((mem_ball _ _).1 hm))
        omega)
    (Monotone.directed_le fun a b hab x hx => hx.imp id fun h hm =>
      h (ball_le (by omega) hm))
  refine ⟨min (-(n : ℤ)) 0, fun x hx => hWU ?_⟩
  rcases hn (ball_le (min_le_right _ _) hx) with h | h
  · exact h
  · exact absurd (ball_le (min_le_left _ _) hx) h

theorem psiV_add (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (x y : Fv F v) :
    psiV F ψ v (x + y) = psiV F ψ v x * psiV F ψ v y := by
  classical
  have h : pairA F 0 (singleV F v (x + y)) =
      pairA F 0 (singleV F v x) + pairA F 0 (singleV F v y) := by
    have : singleV F v (x + y) = singleV F v x + singleV F v y :=
      RestrictedProduct.single_add _ v x y
    rw [this]
    exact Prod.ext (add_zero (0 : Ainf F)).symm rfl
  rw [psiV, h, AddChar.map_add_eq_mul]
  rfl

theorem ann_isCompact {χ : Fv F v → ℂ} (hc : Continuous χ) (h0 : χ 0 = 1) {y : Fv F v} (hy : χ y ≠ 1)
    (L : AddSubgroup (Fv F v)) (hLo : IsOpen (L : Set (Fv F v))) :
    IsCompact {t | ∀ s ∈ L, χ (s * t) = 1} := by
  obtain ⟨m, hm⟩ := exists_ball_subset (L : Set (Fv F v)) (hLo.mem_nhds L.zero_mem)
  have hy0 : y ≠ 0 := fun h => hy (h ▸ h0)
  have hv : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy0
  have hcl : IsClosed {t | ∀ s ∈ L, χ (s * t) = 1} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun s => isClosed_iInter fun _ =>
      isClosed_eq (hc.comp (continuous_const.mul continuous_id)) continuous_const
  refine (ball_isCompact (v := v) (WithZero.log (Valued.v y) - m)).of_isClosed_subset hcl ?_
  intro t ht
  by_contra hne
  have hlt : WithZero.exp (WithZero.log (Valued.v y) - m) < Valued.v t :=
    not_le.1 fun h => hne h
  have hvt : Valued.v t ≠ 0 := (lt_of_le_of_lt zero_le' hlt).ne'
  have ht0 : t ≠ 0 := (Valuation.ne_zero_iff _).1 hvt
  have hmem : y / t ∈ ball v m := by
    rw [mem_ball, map_div₀, div_le_iff₀ (zero_lt_iff.2 hvt)]
    calc Valued.v y = WithZero.exp m * WithZero.exp (WithZero.log (Valued.v y) - m) := by
          rw [← WithZero.exp_add, add_sub_cancel, WithZero.exp_log hv]
      _ ≤ WithZero.exp m * Valued.v t := mul_le_mul_right hlt.le _
  have := ht _ (hm hmem)
  rw [div_mul_cancel₀ _ ht0] at this
  exact hy this

theorem selfDual_pi_v : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (v : HeightOneSpectrum (𝓞 F)) (k : Measure (Fv F v)), SelfDual k (fun s t => psiV F ψ v (s * t)) → ∀ (ι : Type) [Fintype ι], SelfDual (Measure.pi fun _ : ι => k) (fun x y => psiV F ψ v (x ⬝ᵥ y)) := by
  intro F _ _ ψ hψ v k hk ι _
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨hc, y, hy⟩ := (GlobalTheory.CompanionTheory.AdeleCharLocal.char_nontrivial_at_every_place F ψ hψ).1 v
  have ha := psiV_add ψ v
  have hn : ∀ x, ‖psiV F ψ v x‖ = 1 := fun x => hψ.2.1 _
  refine GlobalTheory.CompanionTheory.SW.FourierPi.selfDual_pi (Fv F v) (psiV F ψ v) hc ha hn k hk
    ⟨ball v 0, ball_isCompact 0, ball_isOpen 0⟩
    (fun L _ hLo => ann_isCompact hc (GlobalTheory.CompanionTheory.SW.FourierPi.psi_zero ha hn) hy L hLo)
    (fun K hK => ?_) (fun U hU => ?_) ι
  · obtain ⟨m, hm⟩ := exists_ball_of_isCompact K hK
    exact ⟨ball v m, ball_isCompact m, ball_isOpen m, hm⟩
  · obtain ⟨m, hm⟩ := exists_ball_subset U hU
    exact ⟨ball v m, ball_isCompact m, ball_isOpen m, hm⟩

end GlobalTheory.CompanionTheory.SW.PiV
