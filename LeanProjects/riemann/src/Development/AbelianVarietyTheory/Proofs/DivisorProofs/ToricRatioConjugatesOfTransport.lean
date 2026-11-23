import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LatticeNormTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartEqOneOfLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRingClassGroupOfConductorNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEntireLatticeSumOfHeckeLContinuation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricSumEqHeckeLValueMulAuxiliaryFactors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLNeZeroNat
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsHeckeLOfHasInf

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeGal
open GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols (IsTwistedSum IsSymbol conjChar classOf ToricRatioConjugates)
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (IsConjWt IsConjChar lamF upIdele)

namespace GlobalTheory.ToricTransport

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem exists_toricSum_ne_zero [IsCMField E] {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF E)} {χ : HChar E}
    (hU : UnramFin E) (hφ : IsCMType φ) (hs : 1 ≤ s) (hb : IsBaseCond 𝔣) (hχ : IsValChar φ s κ 𝔣 ∅ χ) :
    ∃ T₀ : ℂ, IsToricSum φ s κ (condQ 𝔣 ∅) χ T₀ ∧ T₀ ≠ 0 := by
  obtain ⟨i₀, -⟩ := hφ (Classical.arbitrary _)
  obtain ⟨Λ, hΛ⟩ := GlobalTheory.ToricDistribution.exists_isHeckeL_of_hasInf E I φ _ χ hφ hχ.1 hχ.2.2.1 ⟨i₀, by omega⟩
  obtain ⟨P₀⟩ : Nonempty (HeightOneSpectrum (𝓞 E)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 E)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField _)⟩⟩
  have t1 := GlobalTheory.ToricSumValue.toricSum_eq GlobalTheory.ToricDistribution.exists_isHeckeL_of_hasInf E I φ hφ s κ 𝔣 ∅ χ (fun _ => P₀) Λ hU hs hb
    (fun _ h => absurd h (Finset.notMem_empty _)) hχ (fun _ h => absurd h (Finset.notMem_empty _)) hΛ
  rw [Finset.filter_empty, Finset.prod_empty, mul_one] at t1
  exact ⟨Λ s, t1, hΛ.ne_zero_nat hχ.1 hs⟩

theorem condQ_ne_bot {𝔣 : Ideal (OF E)} (hb : IsBaseCond 𝔣) (Q : Finset (HeightOneSpectrum (OF E))) : condQ 𝔣 Q ≠ ⊥ :=
  mul_ne_zero hb.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)

theorem exists_twistedSum [IsCMField E] {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF E)} {χ : HChar E}
    (hU : UnramFin E) (hφ : IsCMType φ) (hs : 1 ≤ s) (hb : IsBaseCond 𝔣) (hχ : IsValChar φ s κ 𝔣 ∅ χ)
    (Q : Finset (HeightOneSpectrum (OF E))) (ψ : PicO (condQ 𝔣 Q) →* ℂˣ) : ∃ T, IsTwistedSum φ s κ (condQ 𝔣 Q) χ ψ T := by
  have h0 := OrderUnits.finPart_eq_one E I φ hφ s κ 𝔣 ∅ χ hU hb (fun _ h => absurd h (Finset.notMem_empty _)) hχ
  have hle : condQ 𝔣 Q ≤ condQ 𝔣 ∅ := by
    rw [show condQ 𝔣 ∅ = 𝔣 by simp [condQ]]
    exact Ideal.dvd_iff_le.1 (dvd_mul_right 𝔣 _)
  choose S hS using fun q : PicO (condQ 𝔣 Q) =>
    LatEnt.exists_isLatSum GlobalTheory.ToricDistribution.exists_isHeckeL_of_hasInf E I φ hφ s κ 𝔣 _ χ hU hs hb (dvd_mul_right _ _)
      (condQ_ne_bot hb Q) hχ.1 hχ.2.2.1 (fun y hy => h0 y (hatOUnits_mono hle hy)) q.out
  exact ⟨_, PicFin.finite_picO E _ (condQ_ne_bot hb Q), S, hS, rfl⟩

theorem isTwistedSum_one {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ} {c : Ideal (OF E)} {χ : HChar E} (T : ℂ) :
    IsTwistedSum φ s κ c χ 1 T ↔ IsToricSum φ s κ c χ T := by
  simp [IsTwistedSum, IsToricSum, GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.lamF]

theorem conjChar_one {c : Ideal (OF E)} (g : ℂ ≃+* ℂ) : conjChar g (1 : PicO c →* ℂˣ) = 1 :=
  MonoidHom.ext fun _ => Units.ext (map_one g)

theorem toricRatioConjugates_of_transport (hT : TwistedTransport) : ToricRatioConjugates := by
  intro E _ _ _ K _ _ _ d δ ι I _ φ s κ 𝔣 Q χ hU hK hd hδ hφ hι hs hκ hb hQ hχ
  obtain ⟨Ω₀, hΩ₀, halg, hconj⟩ := hT K d δ ι hK hd hδ
  obtain ⟨T₀, hT₀, h0⟩ := exists_toricSum_ne_zero hU hφ hs hb hχ
  choose T hTw using exists_twistedSum hU hφ hs hb hχ Q
  have hD : IsDatum ι φ s κ 𝔣 Q χ := ⟨hU, hφ, hι, hs, hκ, hb, hQ, hχ⟩
  have hD₀ : IsDatum ι φ s κ 𝔣 ∅ χ := ⟨hU, hφ, hι, hs, hκ, hb, fun _ h => absurd h (Finset.notMem_empty _), hχ⟩
  have hT₀' := (isTwistedSum_one T₀).2 hT₀
  have e : condQ 𝔣 ∅ = 𝔣 := by simp [condQ]
  refine ⟨T₀, T, e ▸ hT₀, h0, hTw, fun ψ => ?_, fun Ω _ _ _ j art hj ha g σ t hgE hgl hσ ht ψ => ⟨?_, ?_⟩⟩
  · rw [← coordIn_div E hd hs κ hΩ₀, div_eq_mul_inv]
    exact (halg E I φ s κ 𝔣 Q χ hD ψ _ (hTw ψ)).mul (halg E I φ s κ 𝔣 ∅ χ hD₀ 1 _ hT₀').inv
  · obtain ⟨Ω₁, hΩ₁, h⟩ := hconj Ω j art hj ha g σ t hσ ht
    have hw : IsConjWt φ g κ κ := fun i i' hi => by
      have : φ i = φ i' := RingHom.ext fun x => (hgE i x).symm.trans (hi x)
      rw [(hφ (φ i)).unique (Or.inl rfl) (Or.inl this)]
    have hc : IsConjChar φ s κ g χ χ := ⟨fun y => (hgl y).symm, hχ.2.2.1⟩
    have h1 := h E I φ s κ 𝔣 Q χ hD κ χ hw hc ψ _ _ (hTw ψ) (hTw _)
    have h2 := h E I φ s κ 𝔣 ∅ χ hD₀ κ χ hw hc 1 T₀ T₀ hT₀' (by rw [conjChar_one]; exact hT₀')
    have hl := GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.lamF_ne_zero s χ (upIdele K E t)
    have hm : ((modF t : ℝ) : ℂ) ≠ 0 := by
      have := GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.lamF_ne_zero 1 (1 : HChar K) t
      rw [lamF, pow_one] at this
      exact right_ne_zero_of_mul this
    rw [← coordIn_div E hd hs κ hΩ₀, map_div₀, h1, h2, coordIn_div E hd hs κ hΩ₁, conjChar_one]
    simp only [MonoidHom.one_apply, Units.val_one, mul_one]
    have := (conjChar g ψ (classOf K (condQ 𝔣 Q) t)).ne_zero
    field_simp
  · have := PicFin.finite_picO E _ (condQ_ne_bot hb Q)
    exact (conjChar g ψ).isOfFinOrder (isOfFinOrder_of_finite _)

end GlobalTheory.ToricTransport
