import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.LocalConditionCharacters.LocalConditionOfFlagOfCharactersNotCyclotomicShi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLocCompC
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocCharDR
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.GaloisRepExistsTotallyRealGL2

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th
open UpperTheory.GalN.V UpperTheory.Zero.LLC UpperTheory.V.Z.Win
open scoped Pointwise
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open private ex_elt algPow_const flag_cont cyc_cont from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.PurityTempered.AlgPowConst
open private ratio_lt from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.PurLocSW
open private place_under pow_eq_one_of_kills charpoly_of_flag from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.WinFreePU
theorem UpperTheory.V.Z.Win.RR.purLocA_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)), Continuous r → ∀ (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∀ x : WD h, (∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : Induces Bw), IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) ∧ Lev.SsCmp (wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := F) A).subtype)) x) → (x.mono0 → RatioW x) → ∀ (ψ : Fin n → Dec (F := F) A →* (Qbar l)ˣ) (m : Fin n → ℤ) (k : ℕ), W.HasFlag (r.comp (Dec (F := F) A).subtype) ψ → StrictAnti m → 0 < k → (∀ i (g : Dec (F := F) A), (g : G F Ω) ∈ Ine (F := F) A → (ψ i g * cycBar F Ω l g ^ (-m i)) ^ k = 1) → ((∀ i j, ψ i ≠ ψ j * (cycBar F Ω l).comp (Dec (F := F) A).subtype) ∨ x.mono0) → ∃ g : Dec (F := F) A, cycZ F Ω l g = 1 ∧ Pr.FreeRatios fun i => ψ i g := by
  intro P F Ω _ _ _ _ _ l _ _ ι n r hr w A h hw x hx ht ψ m k hf hm hk hI hor
  have hN := P.litN
  have H := hN.aut.art
  obtain ⟨a, ha⟩ := Loc.laArtin H h
  obtain ⟨O, _, _, _, Bw, hj⟩ := Af.exists_bridge (l := l) h hw
  obtain ⟨hp, hcmp⟩ := hx O Bw hj
  have hc : Continuous (r.comp (Dec (F := F) A).subtype) := hr.comp continuous_subtype_val
  have hψc := flag_cont hc hf
  choose ω hω using fun i => (Loc.ordCharIff H h ι a ha (fun _ => -m i) (ψ i)).1.2
    ⟨hψc i, Loc.laArith H h hw (ψ i) (hψc i) (m i) k hk (hI i)⟩
  have hpol : ∀ s, (wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := F) A).subtype)).charPol s =
      ∏ i, (X - C (((ω i).comp a) s : ℂ)) := fun s => by
    obtain ⟨M, hM⟩ := hf
    obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
    have hc := fun i => (_root_.UpperTheory.V.Loc.hecke_char_de_rham_of_local_artin_above_l hN h hw ι a ha (ω i) _ (ψ i) (hω i)).1 O Bw hj
    obtain ⟨-, F₂⟩ := UpperTheory.V.Loc.PstExact.flag T ι Bw h hj _ (fun i => GlobalTheory.TripleGal.rk1 (ψ i)) M
      (fun g => (hM g).1) (fun g i => ((hM g).2 i).trans (by simp [GlobalTheory.TripleGal.rk1]))
    rw [(F₂ hp).2 s]
    exact Finset.prod_congr rfl fun i _ => (hc i).2.2 s
  have hxp := fun s => (hcmp (Or.inl ((Lev.ssCalc F Ω A w h).1 n _ _ hpol)) s).symm.trans (hpol s)
  let inc := Subgroup.inclusion (Weil_le_Dec h)
  let ε : ↥(Dec (F := F) A) →* (Qbar l)ˣ := (cycBar F Ω l).comp (Dec (F := F) A).subtype
  let χ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ := fun i => ψ i * ε ^ (-m i)
  have hχc : ∀ i, Continuous (χ i) := fun i => (hψc i).mul ((continuous_zpow (-m i)).comp cyc_cont)
  have hq : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot
  have hq' : ((normV w : ℕ) : Qbar l) ≠ 0 := Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot
  have hμ : ∀ i s, (((ω i).comp a) s : ℂ) = ((normV w : ℕ) : ℂ) ^ (m i * deg s) * ι (χ i (inc s) : Qbar l) := fun i s => by
    have h1 : (ψ i (inc s) : Qbar l) = ι.symm (ω i (a s)) * Hi.algPow w (-fun _ => -m i) (a s : w.adicCompletion F) :=
      (hω i).val s _ rfl (Set.mem_univ _)
    have h2 : (ε (inc s) : Qbar l) = _ := UpperTheory.V.Loc.epsArt H h hw a ha s
    have h3 : Hi.algPow (l := l) w (fun _ => 1) (a s : w.adicCompletion F) ≠ 0 := fun h0 =>
      (ε (inc s)).ne_zero (by rw [h2, h0, mul_zero])
    have h4 : (χ i (inc s) : Qbar l) = (ψ i (inc s) : Qbar l) * (ε (inc s) : Qbar l) ^ (-m i) := by simp [χ]
    have h5 : (χ i (inc s) : Qbar l) = ι.symm (ω i (a s)) * ((normV w : ℕ) : Qbar l) ^ (-(m i * deg s)) := by
      rw [h4, h1, h2, algPow_const, mul_zpow, ← zpow_mul, mul_mul_mul_comm, ← zpow_add₀ h3, add_neg_cancel, zpow_zero, mul_one,
        mul_neg, mul_comm (deg s)]
    rw [h5, map_mul, ι.apply_symm_apply, map_zpow₀, map_natCast, mul_left_comm, ← zpow_add₀ hq, add_neg_cancel, zpow_zero, mul_one]
    rfl
  obtain ⟨s, hs, hs1⟩ := ex_elt H hw ha
  refine ⟨inc s, hs1, fun i j hij N hN0 e => hij ?_⟩
  have hn := ratio_lt x _ (fun i => ha.smooth (hω i).smooth) hxp ht (hor.imp_left fun hne i j => by
    by_contra hij
    simp only [not_exists, not_not, hμ] at hij
    obtain ⟨ha, h1⟩ := UpperTheory.continuous_character_compact_unit_values F Ω l ι w A h hw (χ i * (χ j)⁻¹) (1 + m j - m i)
      (Units.continuous_val.comp ((hχc i).mul (hχc j).inv)) (fun σ => by
        have h2 := hij σ
        have h3 : ι (χ j (inc σ) : Qbar l) ≠ 0 := (map_ne_zero ι).mpr (Units.ne_zero _)
        have h4 : ((normV w : ℕ) : ℂ) ^ (m i * deg σ) ≠ 0 := zpow_ne_zero _ hq
        change ι ((χ i (inc σ) * (χ j (inc σ))⁻¹ : (Qbar l)ˣ) : Qbar l) = _
        rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, sub_mul, add_mul, one_mul, zpow_sub₀ hq,
          zpow_add₀ hq, mul_inv_eq_iff_eq_mul₀ h3, div_mul_eq_mul_div, eq_div_iff h4, mul_comm, mul_assoc]
        exact h2)
    refine hne i j ?_
    have h5 : χ i = χ j := mul_inv_eq_one.mp h1
    have h6 : -m j = 1 + -m i := by omega
    simp only [χ] at h5
    rw [h6, zpow_add, zpow_one, ← mul_assoc] at h5
    exact mul_right_cancel h5) i j
  have h7 : ε (inc s) = 1 := congrArg (Units.map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom) hs1 |>.trans
    (map_one _)
  have h8 : ∀ i, χ i (inc s) = ψ i (inc s) := fun i => by simp [χ, h7]
  have h9 : ‖ι (ψ i (inc s) : Qbar l)‖ = ‖ι (ψ j (inc s) : Qbar l)‖ := by
    refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hN0.ne').1 ?_
    rw [← norm_pow, ← norm_pow, ← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val]
    exact congrArg (fun u : (Qbar l)ˣ => ‖ι (u : Qbar l)‖) e
  have h0 : ‖ι (ψ j (inc s) : Qbar l)‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero ι).mpr (Units.ne_zero _))
  have hq1 : (1 : ℝ) < (normV w : ℕ) := by exact_mod_cast one_lt_normV w
  refine hm.injective (sub_eq_zero.1 (hn s hs (m i - m j) ?_))
  rw [hμ, hμ, h8, h8, norm_mul, norm_mul, h9, norm_zpow, norm_zpow, Complex.norm_natCast, ← mul_assoc,
    ← zpow_add₀ (zero_lt_one.trans hq1).ne']
  congr 2
  ring
namespace UpperTheory.V.Z.Win.RR
theorem free_core_alt (PH : _root_.UpperTheory.V.Af.HypothesesH') (F Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (ι : Qbar l ≃+* ℂ) (n : ℕ) (hn : 1 ≤ n) (r : G F Ω →* GL (Fin n) (Qbar l)) (hr : Continuous r)
    (π : CuspSub F n) (hreg : (CG.mk π).IsRegAlg) (hpol : ∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ) (hatt : AttC ι r π) (hW : WitA ι r)
    (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (hw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal)
    (ψ : Fin n → Dec (F := F) A →* (Qbar l)ˣ) (m : Fin n → ℤ) (k : ℕ)
    (hflag : W.HasFlag (r.comp (Dec (F := F) A).subtype) ψ) (hm : StrictAnti m) (hk : 0 < k)
    (hine : ∀ i (g : Dec (F := F) A), (g : G F Ω) ∈ Ine (F := F) A → (ψ i g * cycBar F Ω l g ^ (-m i)) ^ k = 1)
    (hgen : ∀ i j, ψ i ≠ ψ j * (cycBar F Ω l).comp (Dec (F := F) A).subtype) :
    ∃ g : Dec (F := F) A, cycZ F Ω l g = 1 ∧ Pr.FreeRatios fun i => ψ i g := by
  have P := PH.toClassicalTheorems
  have hU := local_condition_of_flag_of_characters_not_cyclotomic_shift h hflag hgen
  obtain ⟨⟨σ, hσ⟩, -⟩ := _root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P F n π w
  obtain ⟨rc, hrc⟩ := recTExists F Ω A w h
  obtain ⟨-, g1, g2⟩ := guard_of plainRec hreg hatt hW (Or.inr (Or.inl hU)) hrc hσ
  obtain ⟨HT, -, hloc⟩ := compatTOf (_root_.UpperTheory.Gal.SV.rowOf' P.litN.aut.gal) plainRec F Ω l ι n hn r π hr hreg hpol hatt
  obtain ⟨t, ht⟩ := hW.2 π hreg hatt
  have hc := ((hloc w σ hσ).1 A h rc hrc).2
  exact _root_.UpperTheory.V.Z.Win.RR.purLocA_alt P F Ω l hl ι n r hr w A h hw (rc (algNorm σ))
    (fun O _ _ _ Bw hj => ⟨(hc O Bw hj ⟨g1, g2⟩).1, Lev.SsCmp.of_eq (hc O Bw hj ⟨g1, g2⟩).2⟩)
    (fun _ => UpperTheory.Gal.SV.ratioT F Ω A w h rc hrc n π t (ht w (Or.inr (hW.1 w hw hU))) σ hσ) ψ m k hflag hm hk hine (Or.inl hgen)
theorem exists_cycZ_eq_one_freeRatios_of_ne_mul_cycBar :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (F Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
        ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ r : G F Ω →* GL (Fin n) (Qbar l), Continuous r → IsAutCsdA ι r →
        ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ (ψ : Fin n → Dec (F := F) A →* (Qbar l)ˣ) (m : Fin n → ℤ) (k : ℕ),
          W.HasFlag (r.comp (Dec (F := F) A).subtype) ψ → StrictAnti m → 0 < k →
          (∀ i (g : Dec (F := F) A), (g : G F Ω) ∈ Ine (F := F) A → (ψ i g * cycBar F Ω l g ^ (-m i)) ^ k = 1) →
          (∀ i j, ψ i ≠ ψ j * (cycBar F Ω l).comp (Dec (F := F) A).subtype) →
          ∃ g : Dec (F := F) A, cycZ F Ω l g = 1 ∧ Pr.FreeRatios fun i => ψ i g := by
  intro PH F Ω _ _ _ _ _ _ l _ hl ι n hn r hr haut A hA ψ m k hflag hm hk hine hgen
  obtain ⟨⟨π, hreg, hcsd, hatt⟩, hW⟩ := haut
  have hpol : GlobalTheory.ContraPair.PolarizedPair π (quadChar F ^ n) :=
    ⟨fun v => by
      have e : (quadChar F ^ n).locInf v (-1) = (quadChar F).locInf v (-1) ^ n := rfl
      rw [e, quadChar_locInf],
     by rw [map_pow, compNorm_quadChar, one_pow]; exact (GlobalTheory.ContraPair.dualIsConjBy_one π).2 hcsd⟩
  obtain ⟨w, h, hw⟩ := place_under (F := F) (Fact.out : l.Prime).ne_zero hA
  exact _root_.UpperTheory.V.Z.Win.RR.free_core_alt PH F Ω l hl ι n hn r hr π hreg ⟨_, hpol⟩ hatt (hW hr) w A h hw ψ m k hflag hm hk hine hgen
end UpperTheory.V.Z.Win.RR
open UpperTheory.V.Z.Win.RR in
theorem UpperTheory.V.Z.Win.RR.freeAt_of_autPA_of_unl_of_finrank_eq_two :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (K Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω], Module.finrank ℚ K = 2 → ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ), 2 ≤ n → ∀ (r : G K Ω →* GL (Fin n) (Qbar l)) (M : ℕ) (m : Fin n → ℤ), 1 ≤ M → StrictAnti m → Continuous r → AutPA ι r → Th.Unl l M m r → FreeAt l r := by
  intro PH K Ω _ _ _ _ _ _ hK l _ hl ι n hn r M m hM hm hr haut hU B hB
  have P : _root_.UpperTheory.V.Af.Hypotheses' := PH.toClassicalTheorems
  obtain ⟨w, hBw, hw⟩ := place_under (F := K) (Fact.out : l.Prime).ne_zero hB
  obtain ⟨⟨π, hreg, hpol, hatt⟩, hW⟩ := haut
  obtain ⟨A, hA, κ, hF, hunl⟩ := hU w hw
  obtain ⟨χ, hχ, hflag, hκ⟩ := id hF
  obtain ⟨k, hk, hpow⟩ := pow_eq_one_of_kills (F := K) (Ω := Ω) hM
  have hflag' : W.HasFlag (r.comp (Dec (F := K) A).subtype) κ := hflag
  obtain ⟨g, hg, hfree⟩ := _root_.UpperTheory.V.Z.Win.RR.free_core_alt PH K Ω l hl ι n (by omega) r hr π hreg hpol hatt (hW hr) w A hA hw κ m k hflag' hm hk
    (fun i s hs => by
      rw [hκ i s hs, zpow_neg, mul_inv_cancel_comm]
      exact hpow _ _ (hχ i) _) hunl
  obtain ⟨t, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := K) hA hBw
  refine ⟨t * g * t⁻¹, ?_, ?_, fun i => κ i g, hfree, ?_⟩
  · have h1 : (g : G K Ω) • A = A := g.2
    show (t * (g : G K Ω) * t⁻¹) • t • A = t • A
    rw [mul_smul, mul_smul, inv_smul_smul, h1]
  · rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm, hg]
  · have h1 := charpoly_of_flag hflag' g (r t)
    rw [← h1]
    show (r (t * g * t⁻¹)).val.charpoly = _
    rw [map_mul, map_mul, map_inv]
    rfl
end
