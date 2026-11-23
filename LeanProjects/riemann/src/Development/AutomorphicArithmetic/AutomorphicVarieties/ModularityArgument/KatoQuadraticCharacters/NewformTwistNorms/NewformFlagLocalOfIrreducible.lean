import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.FixedAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.SsCalcP
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LevelQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SatOfFixed
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.CycIne

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.UnramAtL

theorem dualTw_det {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin 2) k) :
    DualTw r (Matrix.GeneralLinearGroup.det.comp r) := by
  refine ⟨⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩, fun s => ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

theorem place_unique (l : ℕ) [hl : Fact l.Prime] {v w : Pl} (hv : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (hw : ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) : v = w := by
  have hpr : Prime (l : 𝓞 ℚ) := by
    have e : (l : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm (l : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr (Nat.prime_iff_prime_int.1 hl.out)
  have hm : (Ideal.span {(l : 𝓞 ℚ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hpr.ne_zero).2 hpr).isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpr.ne_zero)
  exact HeightOneSpectrum.ext
    ((hm.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hv)).symm.trans
      (hm.eq_of_le w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hw)))

end GlobalTheory.Ord2.UnramAtL

open GlobalTheory.Ord2.UnramAtL in

theorem GlobalTheory.Ord2.unram_at_l : Af.Hypotheses₂ → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (V : R2 Ω l) (A : ValuationSubring Ω) (κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ) (g : Newform (2 * e + 1)), l ≠ 2 → 1 ≤ e → Continuous V → IsIrr V → (∃ M : ℕ, 1 ≤ M ∧ LevelAway l M V) → (∃ M : ℕ, 1 ≤ M ∧ KillsMu M (dt V)) → OverL l A → IsFlagOn V (Dec (F := ℚ) A) κ → (∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A → κ 0 s = cycBar ℚ Ω l s ^ (e : ℤ) ∧ κ 1 s = cycBar ℚ Ω l s ^ (-(e : ℤ))) → g.Att ι (tw V (cycBar ℚ Ω l ^ (-(e : ℤ)))) → ∀ π : TR.CuspSub ℚ 2, π.IsRegAlg → AttR ι V π → ∀ w : Pl, ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal → ∃ Bs, π.HasSat w Bs := by
  intro P l _ Ω _ _ _ ι e V A κ g hl he hcont hirr hAway hKill hOver hfl hκ _ π hreg hatt w hw
  obtain ⟨M, hM, haway⟩ := hAway
  obtain ⟨M', hM', hkill⟩ := hKill
  obtain ⟨v, hAv, hlv⟩ := hOver
  obtain rfl : w = v := place_unique l hw hlv
  have hAl : A.valuation (l : Ω) < 1 := by simpa using (hAv _).2 hlv
  let m : Fin 2 → ℤ := ![(e : ℤ), -(e : ℤ)]
  have hκm : ∀ i (s : ↥(Dec (F := ℚ) A)), (s : G ℚ Ω) ∈ Ine (F := ℚ) A →
      κ i s = cycBar ℚ Ω l s ^ m i * (1 : G ℚ Ω →* (Qbar l)ˣ) s := by
    intro i s hs
    fin_cases i
    · simpa [m] using (hκ s hs).1
    · simpa [m] using (hκ s hs).2
  have hor : ∀ i j, κ i ≠ κ j * (cycBar ℚ Ω l).comp (Dec (F := ℚ) A).subtype := by
    intro i j hij
    obtain ⟨s, hs, hne⟩ := UpperTheory.V.Ws.Pt.cycIne ℚ Ω l A hAl (m i - m j - 1) (by
      fin_cases i <;> fin_cases j <;> simp [m] <;> omega)
    have h1 := congrArg (fun f => f ⟨s, Ine_le_Dec A hs⟩) hij
    simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Subgroup.coe_subtype] at h1
    rw [hκm i _ hs, hκm j _ hs] at h1
    apply hne
    simp only [MonoidHom.one_apply, mul_one] at h1
    rw [zpow_sub, zpow_sub, h1, zpow_one]
    group
  have hlev : Level l M m V := ⟨hcont, haway, fun w' hw' => by
    obtain rfl : w = w' := place_unique l hlv hw'
    exact ⟨A, hAv, fun _ => 1, κ, fun _ _ _ => rfl, hfl, hκm, Or.inl hor⟩⟩
  have hdual : ∃ θ, IsCycWt l 0 θ ∧ DualTw V θ :=
    ⟨dt V, ⟨M', dt V, hM', hkill, by simp⟩, dualTw_det V⟩
  have hanti : StrictAnti m := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [m] at hij ⊢ <;> omega
  have hL : GlobalTheory.Published.LocalLanglandsGL :=
    GlobalTheory.LocLanglandsBridge.localLanglandsGL_of_depthZero_zelevinsky_bernstein P.litN.loc.llc P.litN.loc.conv P.litN.loc.dzc P.litN.loc.dzi
      P.litN.loc.brauer P.litN.loc.chev P.litN.aut.art P.litN.loc.exh P.litN.loc.multi P.litN.loc.cos P.litN.loc.zel
      P.litN.loc.geo P.litN.loc.bz
  obtain ⟨rc, hrc, -⟩ := hL.1 ℚ Ω A w hAv
  obtain ⟨j, L0, hj, hB⟩ := GlobalTheory.PlaceBridge.exists_locBridge l ℚ Ω w A hw hAv
  obtain ⟨Bw, hBj, -⟩ := hB L0 le_rfl
  have hI : GlobalTheory.Pst.Induces Bw := fun x => by rw [hBj]; exact hj x
  obtain ⟨c1, c2⟩ := compatAtLQ P 2 le_rfl 0 l hl Ω ι V π hcont hirr M m hM hanti hlev hdual hreg hatt w A hAv _ Bw hI
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := locCompR P ℚ 2 π w
  obtain ⟨x, hx0, hx⟩ := Lev.fixedAll P ℚ Ω l ι 2 1 le_rfl m V hcont w A hAv _ Bw hI κ
    ⟨fun _ => 1, fun _ _ _ => rfl, hfl, hκm⟩ c1 rc hrc σ
    (fun ⟨μ, hμ⟩ => c2 σ hσ rc hrc (Or.inl ((Lev.ssCalc ℚ Ω A w hAv).1 2 _ μ hμ))) (Or.inr (Or.inl hor))
  have hK : HasFixed σ.ρ (GlobalTheory.LFun.KGL w 2) := ⟨x, hx0, fun u hu => hx u (locGL_mem_KLev 2 w (by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top) hu)⟩
  obtain ⟨B, hB⟩ := (satLoc P ℚ 2 w σ).1 hK
  exact ⟨B, ((satLoc P ℚ 2 w σ).2 _ π.finPart (hiso σ hσ) B).2 hB⟩

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newform_flag_local_of_irreducible : Af.Hypotheses₂ → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (V : R2 Ω l) (A : ValuationSubring Ω) (κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ) (g : Newform (2 * e + 1)), l ≠ 2 → 1 ≤ e → Continuous V → IsIrr V → (∃ M : ℕ, 1 ≤ M ∧ LevelAway l M V) → (∃ M : ℕ, 1 ≤ M ∧ KillsMu M (dt V)) → OverL l A → IsFlagOn V (Dec (F := ℚ) A) κ → (∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A → κ 0 s = cycBar ℚ Ω l s ^ (e : ℤ) ∧ κ 1 s = cycBar ℚ Ω l s ^ (-(e : ℤ))) → g.Att ι (tw V (cycBar ℚ Ω l ^ (-(e : ℤ)))) → ∀ π : TR.CuspSub ℚ 2, π.IsRegAlg → AttR ι V π → ∀ w : Pl, ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal → ∃ Bs, π.HasSat w Bs := by
  first | exact @GlobalTheory.Ord2.unram_at_l | exact GlobalTheory.Ord2.unram_at_l | (intros; apply GlobalTheory.Ord2.unram_at_l <;> assumption)

end
