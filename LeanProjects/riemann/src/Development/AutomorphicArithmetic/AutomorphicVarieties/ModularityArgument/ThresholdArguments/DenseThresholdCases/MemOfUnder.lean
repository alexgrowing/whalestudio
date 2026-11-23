import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.MemOfUnder
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WStmtxx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AdjointLiftTransferToUnitaryGroupTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TGoodW
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAboveW
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAwayW
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ResidualCharpolyRankFour
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TPlainAtW
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UfOfCharpoly

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Sym.W
private theorem val_iff {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] {A : ValuationSubring Ω} {w : Plc L}
    (h : IsPlaceOver A w) (M : ℕ) : A.valuation (M : Ω) < 1 ↔ (M : 𝓞 L) ∈ w.asIdeal := by
  have := h (M : 𝓞 L)
  simpa using this
private theorem mem_of_under {L : Type} [Field L] [NumberField L] [IsCMField L] {w w' : Plc L}
    (e : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) (M : ℕ) : (M : 𝓞 L) ∈ w'.asIdeal ↔ (M : 𝓞 L) ∈ w.asIdeal := by
  have hl : ∀ w : Plc L, (M : 𝓞 L) ∈ w.asIdeal ↔ (M : 𝓞 (Lp L)) ∈ (w.under (𝓞 (Lp L))).asIdeal := fun w => by
    rw [← map_natCast (algebraMap (𝓞 (Lp L)) (𝓞 L))]
    rfl
  rw [hl, hl, e]
private theorem core (P : _root_.UpperTheory.V.Z.Sym.W.PureWeightCompatibility) (hA : AdLiftW) (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (hl : l ≠ 2) (M m : ℕ) (hM : M ≠ 0) (h2 : 2 * l ∣ M) (hU : UnrSplit L M)
    (r : G L Ω →* GL (Fin 2) (Qbar l)) (hr : AdInW ι M m r) (w₀ : Plc L) (hw₀ : (M : 𝓞 L) ∈ w₀.asIdeal) :
    ∃ π : CuspSub L 3, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ AttC ι (tw (ad0 r) (cycBar L Ω l)⁻¹) π ∧
      (∀ w : Plc L, (M : 𝓞 L) ∉ w.asIdeal → ∃ B, (CG.mk π).HasSat w B) ∧ ∀ τ, π.IsLocComp w₀ τ → PT τ := by
  have hlM : l ∣ M := (Dvd.intro_left 2 rfl).trans h2
  have h2M : 2 ∣ M := (Dvd.intro l rfl).trans h2
  have hdv : ∀ {a : ℕ} {w : Plc L}, a ∣ M → (a : 𝓞 L) ∈ w.asIdeal → (M : 𝓞 L) ∈ w.asIdeal := by
    rintro a w ⟨b, rfl⟩ h
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ h
  obtain ⟨σ, HT, hσ, hg, hpt, hunr, hwt⟩ := _root_.UpperTheory.V.Z.Sym.W.aboveWeight P L Ω l ι hl M m hM hlM hU r hr
  obtain ⟨S, hS, h0S, hSi, hSm⟩ := selectW L {w | (M : 𝓞 L) ∈ w.asIdeal} w₀ hw₀
  obtain ⟨Q, hQ, hQi, hQm⟩ := Ga.select L {w | IsSplitAt w ∧ (M : 𝓞 L) ∉ w.asIdeal ∧ ∃ s, Ga.FrobAt w s ∧ s ∉ Ga.Bad r}
  have hfin : S.Finite := by
    have h0 : Ideal.span {(M : 𝓞 L)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast hM
    exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (hS hv)
  have key : ∀ w : Plc L, ∃ ψ : Fin 2 → (Kw w)ˣ →* ℂˣ, (w ∈ S ∪ Q → CompEq σ w ψ) ∧ (w ∈ S → NoLk (ψ 0 / ψ 1)) ∧
      (w ∈ Q → (∀ i, ∀ u ∈ Hi.Uo (Kw w), ψ i u = 1) ∧ Reg (ψ 0 / ψ 1)) := fun w => by
    by_cases hq : w ∈ Q
    · obtain ⟨h1, h3, h4⟩ := hQ hq
      obtain ⟨τ, hτ⟩ := hg.comp w h1
      obtain ⟨ψ, a1, a2, a3, a4⟩ := _root_.UpperTheory.V.Z.Sym.W.good_w_statement P.af L Ω l ι r w (mt (hdv hlM) h3)
        (fun A hA => hr.unr A (mt (val_iff hA M).1 h3)) h4 τ (hg.loc w h1 τ hτ) (hpt w h1 τ hτ).1
      exact ⟨ψ, fun _ => ⟨a1, τ, hτ, a2⟩, fun h => absurd (hS h) h3, fun _ => ⟨a3, a4⟩⟩
    by_cases hs : w ∈ S
    · have h1 := hU.split w (hS hs)
      obtain ⟨τ, hτ⟩ := hg.comp w h1
      by_cases hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal
      · obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
        obtain ⟨⟨ψ, a1, a2, a3⟩, -⟩ := _root_.UpperTheory.V.Z.Sym.W.above_w_statement P.af L Ω l ι hl r hr.cont m hr.gap w hw HT (hpt w h1 τ hτ).2 A hA
          (hr.above A ((val_iff hA l).2 hw)) τ (hg.loc w h1 τ hτ) (hpt w h1 τ hτ).1
        exact ⟨ψ, fun _ => ⟨a1, τ, hτ, a2⟩, fun _ => a3, fun h => absurd h hq⟩
      · obtain ⟨ψ, a1, a2, a3⟩ := _root_.UpperTheory.V.Z.Sym.W.away_w_statement P.af L Ω l ι r hr.cont hr.unl w hw τ (hg.loc w h1 τ hτ) (hpt w h1 τ hτ).1
        exact ⟨ψ, fun _ => ⟨a1, τ, hτ, a2⟩, fun _ => a3, fun h => absurd h hq⟩
    · exact ⟨1, fun h => (h.elim hs hq).elim, fun h => absurd h hs, fun h => absurd h hq⟩
  choose ψ hψ hnl hψ' using key
  have hgood : Ga.GoodSet ι M r σ Q ψ :=
    ⟨fun w hw => ⟨(hQ hw).1, mt (hdv hlM) (hQ hw).2.1, hψ w (Or.inr hw)⟩, fun w a b c => hQm w ⟨a, b, c⟩⟩
  have hgap := hr.gap
  have := hA L hU.unr hfin.toFinset Q ?_ ?_ ?_ σ hσ (m - 1) (by omega) hwt ?_ ψ ?_ hψ'
  · rcases this with ⟨σ₃, h1, hu, h4, h3⟩ | ⟨σ', h1, h3⟩
    · obtain ⟨π, a, b, c, d⟩ := _root_.UpperTheory.V.Z.Sym.W.branch1W_alt P L Ω l ι hl hU.unr M m hM r σ hr hg Q ψ hgood (fun w hw => (hψ' w hw).2) σ₃ h1 h3
      exact ⟨π, a, b, c, fun w hw => d.unr w (hu w fun w' hw' e => hw ((mem_of_under e M).1 (hS (hfin.mem_toFinset.1 hw')))),
        _root_.UpperTheory.V.Z.Sym.W.plain_at_w_statement P.af.litN L σ₃ π h1 d w₀ (hU.split w₀ hw₀) _ (hnl w₀ h0S) (h4 w₀ (hfin.mem_toFinset.2 h0S))⟩
    · exact (_root_.UpperTheory.V.Z.Sym.W.branch_two_w_statement P L Ω l ι hl hU.unr M m hM r σ hr hg Q ψ hgood (fun w hw => (hψ' w hw).2) σ' h1 h3).elim
  · rw [hfin.coe_toFinset, Set.disjoint_left]
    exact fun w a b => (hQ b).2.1 (hS a)
  · rw [hfin.coe_toFinset]
    refine ⟨fun w hw => hw.elim (fun h => hU.split w (hS h)) fun h => (hQ h).1, ?_⟩
    rintro a (ha | ha) b (hb | hb) e
    · exact hSi ha hb e
    · exact absurd ((mem_of_under e M).1 (hS ha)) (hQ hb).2.1
    · exact absurd ((mem_of_under e M).2 (hS hb)) (hQ ha).2.1
    · exact hQi ha hb e
  · intro w hw
    obtain ⟨w', a, b⟩ := hSm w (hdv h2M (by exact_mod_cast hw))
    exact ⟨w', hfin.mem_toFinset.2 a, b⟩
  · intro w hw
    refine hunr w fun h => ?_
    obtain ⟨w', a, b⟩ := hSm w h
    exact hw w' (hfin.mem_toFinset.2 a) b
  · rw [hfin.coe_toFinset]
    exact hψ
theorem adjoint_automorphy_w_of_pure_weight_adjoint_lift (P : _root_.UpperTheory.V.Z.Sym.W.PureWeightCompatibility) (hA : AdLiftW) : AdAutW := by
  intro L Ω _ _ _ _ _ _ l _ ι hl M m hM h2 hU r hr
  obtain ⟨w₁, hw₁⟩ : ∃ w : Plc L, (M : 𝓞 L) ∈ w.asIdeal := by
    have hl1 : ((l : ℕ) : 𝓞 L) ∈ (GlobalTheory.EvExtend.placeOf (IsAlgClosed.lift (R := ℚ) (M := Qbar l) (S := L)).toRingHom).asIdeal := by
      rw [GlobalTheory.EvExtend.mem_placeOf]
      simpa using GlobalTheory.EvExtend.norm_natCast_lt_one (l := l)
    obtain ⟨b, rfl⟩ := (Dvd.intro_left 2 rfl).trans h2
    exact ⟨_, by rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hl1⟩
  obtain ⟨π, a, b, c, d, -⟩ := core P hA L Ω l ι hl M m hM h2 hU r hr w₁ hw₁
  refine ⟨⟨π, a, b, c⟩, glueW L Ω l ι _ fun w => ?_⟩
  by_cases hw : (M : 𝓞 L) ∈ w.asIdeal
  · obtain ⟨π', -, -, c', -, e⟩ := core P hA L Ω l ι hl M m hM h2 hU r hr w hw
    exact ⟨π', c', Or.inr e⟩
  · exact ⟨π, c, Or.inl (d w hw)⟩
end UpperTheory.V.Z.Sym.W
end
end
