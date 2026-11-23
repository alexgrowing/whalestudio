import Mathlib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRat
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedNefGeneric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPerturb
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedRestrict
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedProductNonneg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

theorem GeneratedNefGeneric.eq_natCast_of_add_one_eq (d : ℕ) (x : WithBot ℕ∞)
    (hform : x + 1 = ((d : ℕ) : WithBot ℕ∞) + 1) : x = d := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd hform (by simp; rw [← Nat.cast_succ]; exact (WithBot.natCast_ne_bot _).symm)
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      exfalso
      have h1 : (((⊤ : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) = (((d + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        rw [WithBot.coe_add]; exact_mod_cast hform
      have h2 : ((⊤ : ℕ∞) + 1 : ℕ∞) = ((d + 1 : ℕ) : ℕ∞) := WithBot.coe_injective h1
      rw [top_add] at h2
      exact ENat.top_ne_natCast _ h2
    | coe y =>
      have h1 : ((y + 1 : ℕ) : WithBot ℕ∞) = ((d + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hform
      have : y = d := by exact_mod_cast (by exact_mod_cast h1 : y + 1 = d + 1) |> Nat.succ_injective
      subst this; rfl

theorem GeneratedNefGeneric.isProjVarF_map {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {W : Ideal (MRing ι)} {d : ℕ} (hW : IsArithVar W (d + 1)) :
    IsProjVarF (W.map (MvPolynomial.map (Int.castRingHom ℚ))) d := by
  obtain ⟨-, ⟨hWp, ⟨S, hS, hWS⟩, hrel⟩, hhor, hdim⟩ := hW
  have : W.IsPrime := hWp
  have hchar : ∀ m : ℤ, (C m : MvPolynomial (Σ k, ι k) ℤ) ∈ W → m = 0 := by
    intro m hm
    have h1 : m ∈ W.comap (C : ℤ →+* MRing ι) := hm
    rw [show W.comap (C : ℤ →+* MRing ι) = ⊥ from hhor, Ideal.mem_bot] at h1
    exact h1
  obtain ⟨hqp, hcomap, hform⟩ := ReciprocityTheory.AnForm.R.extQ_spec W hchar
  have hq : ReciprocityTheory.AnForm.R.extQ W = W.map (MvPolynomial.map (Int.castRingHom ℚ)) := rfl
  rw [← hq]
  refine ⟨⟨hqp, ?_, ?_⟩, ?_⟩
  · refine ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩
    · rintro _ ⟨f, hf, rfl⟩
      obtain ⟨b, hb⟩ := hS f hf
      exact ⟨b, fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k⟩
    · show W.map (MvPolynomial.map (Int.castRingHom ℚ)) = _
      rw [hWS, Ideal.map_span]
  · intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun hX => hi ?_⟩
    rw [← hcomap, Ideal.mem_comap, map_X]
    exact hX
  · refine GeneratedNefGeneric.eq_natCast_of_add_one_eq (d + Fintype.card K) _ ?_
    rw [hform, hdim, show d + 1 + Fintype.card K = (d + Fintype.card K) + 1 by omega]
    push_cast
    rfl

theorem GeneratedNefGeneric.proof (hG : GenOnFibres.Statement) (hR : GeneratedRestrict.Statement)
    (hN : GeneratedProductNonneg.Statement) : GeneratedNefGeneric.Statement := by
  intro K _ ι _ Ω _ _ y D a q w _ hw hgen W hW hPW
  classical
  let _ : LinearOrder K := LinearOrder.lift' (Fintype.equivFin K) (Fintype.equivFin K).injective
  let _ : ∀ k, LinearOrder (ι k) := fun k =>
    LinearOrder.lift' (Fintype.equivFin (ι k)) (Fintype.equivFin (ι k)).injective
  have hQ : KH.GeneratedV ℚ (KH.genIdeal y) a := (hG K ι Ω y a q w hw hgen).1
  have hWQ : KH.GeneratedV ℚ (W.map (MvPolynomial.map (Int.castRingHom ℚ))) a :=
    hR ℚ K ι _ _ a (Ideal.map_mono hPW) hQ
  have hV : IsProjVarF (W.map (MvPolynomial.map (Int.castRingHom ℚ))) 1 :=
    GeneratedNefGeneric.isProjVarF_map (d := 1) hW
  have h := hN ℚ K ι (fun V _ L => NumbersDVR.intNum ℚ V L) _ 1 (fun _ => a)
    (NumbersDVR.IntNumIsFieldIntersection.full ℚ K ι) hV (fun _ => hWQ)
  unfold genDeg
  convert h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
