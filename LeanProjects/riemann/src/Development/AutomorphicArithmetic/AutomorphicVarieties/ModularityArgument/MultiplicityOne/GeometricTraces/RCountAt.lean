import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.RCountAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SmallTendsto
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.RChoice

open UpperTheory.V.Z.Mult UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
open NumberField IsDedekindDomain Filter GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open UpperTheory.V.Af.Bc (cPl)

theorem UpperTheory.V.Z.Mult.rCountAt :
    UpperTheory.V.Z.Mult.RCountAt := by
  classical
  intro hC hEv hCp hP E _ _ _ hU n hn1 hn4 π hreg hd S hS lam Z hZ B τ hB hτ K' hK' hKZ ι _ σ hdec
  obtain ⟨t, Bi, hi, hev⟩ := hEv E hU n hn1 S hS lam Z hZ K' hK' hKZ ι σ hdec
  obtain ⟨-, hc, -, hSec⟩ := hP E
  have hF := UpperTheory.V.Af.formsFiniteGL
  have hsat : ∀ w, Off Z w → ∃ τ₀ : SmIrr (GLw n w), π.IsLocComp w τ₀ ∧ HasSatGL w τ₀.ρ (B w) := fun w hw => by
    obtain ⟨τ₀, h₀⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp hF E n π w
    exact ⟨τ₀, h₀.1, ((GlobalTheory.Cong.satake_locComp E n π w τ₀ h₀.1).1 _).1 (hB w hw)⟩
  have hAt : ∀ i, (∀ w, Off Z w → IsSplitAt w → Bi i w = B w) → At π (σ i) := fun i h => by
    filter_upwards [off_cofinite hP Z] with w hw hs
    obtain ⟨τ', h1, h2⟩ := (hi i).2.2 w hw hs
    exact ⟨τ', B w, h1, h w hw hs ▸ h2, hB w hw⟩
  have hCo : ∀ i, At π (σ i) → ∀ w, IsSplitAt w → ∀ τ₀, π.IsLocComp w τ₀ → Cp (σ i) w τ₀ := fun i h =>
    hC E hU n hn1 hn4 π hreg hd (σ i) (hdec.1 i).1 (hi i).1 h
  have hEq : ∀ i, At π (σ i) → ∀ w, Off Z w → IsSplitAt w → Bi i w = B w := fun i h w hw hs => by
    obtain ⟨τ', h1, h2⟩ := (hi i).2.2 w hw hs
    obtain ⟨τ₀, h₀, s₀⟩ := hsat w hw
    exact HasSatGL.unique h2 ((hCp E hU n hn1 (σ i) (hdec.1 i).1 w hs τ₀ τ' (hCo i h w hs τ₀ h₀) h1).1 _ s₀)
  refine ⟨{i // ¬ At π (σ i)}, inferInstance, fun j => Bi j.1, fun j => ?_, ?_⟩
  · by_contra hno
    refine j.2 (hAt j.1 fun w hw hs => ?_)
    by_contra hne
    obtain ⟨τ', -, h2⟩ := (hi j.1).2.2 w hw hs
    obtain ⟨τ₀, -, s₀⟩ := hsat w hw
    exact hno ⟨w, hw, hs, HasSatGL.card s₀, HasSatGL.card h2, hne⟩
  · intro f hf T hT hTZ e₁ e₂ h1 h0 k
    obtain ⟨htest, htr⟩ := hev f hf T hT hTZ e₁ e₂ k
    refine ⟨htest, fun hk => ?_⟩
    have hoffT : ∀ w ∈ T, Off Z w ∧ IsSplitAt w := fun w hw => by
      have hnZ : ∀ {u}, u ∈ T → u ∉ Z := fun hu hu' => Finset.disjoint_left.1 hTZ hu hu'
      refine ⟨⟨hnZ hw, fun h => ?_⟩, (hT w hw).2⟩
      exact ((hc w).2.1 (hT w hw).2) ((hSec S hS w).2 (hT w hw).1 (hZ _ h).1)
    have hval : ∀ i, At π (σ i) → val1 T e₁ e₂ (Bi i) = 1 := fun i h => by
      rw [← h1]
      refine Finset.prod_congr rfl fun w hw => ?_
      obtain ⟨⟨ha, hb⟩, hs⟩ := hoffT w hw
      have hcs : IsSplitAt (cPl w) := (hc (cPl w)).2.2 (by rw [(hc w).1]; exact ((hc w).2.1 hs).symm)
      have ho : Off Z (cPl w) := ⟨hb, by rwa [(hc w).1]⟩
      rw [hEq i h w ⟨ha, hb⟩ hs, hEq i h _ ho hcs]
    have hterm : ∀ i, (∏ w ∈ Z, trc (t i w).ρ (KGL w n) (f w)) * val1 T e₁ e₂ (Bi i) ^ k =
        (if At π (σ i) then 1 else 0) * ∏ w ∈ Z, trc (τ w).ρ (KGL w n) (f w) := fun i => by
      by_cases h : At π (σ i)
      · rw [if_pos h, hval i h, one_pow, mul_one, one_mul]
        refine Finset.prod_congr rfl fun w hw => ?_
        exact ((hCp E hU n hn1 (σ i) (hdec.1 i).1 w (hZ w hw).2 (τ w) (t i w)
          (hCo i h w (hZ w hw).2 _ (hτ w hw)) ((hi i).2.1 w hw)).2 (f w)).symm
      · rw [if_neg h, h0 ⟨i, h⟩, zero_pow (by omega), mul_zero, zero_mul]
    rw [htr, Finset.sum_congr rfl fun i _ => hterm i, ← Finset.sum_mul, Finset.sum_boole, Nat.card_eq_fintype_card,
      Fintype.card_subtype]
