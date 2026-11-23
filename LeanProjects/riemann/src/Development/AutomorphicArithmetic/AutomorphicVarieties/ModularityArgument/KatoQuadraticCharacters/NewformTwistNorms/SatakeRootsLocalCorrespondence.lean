import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.FlagPol
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.SsCalcP
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.CompatAtLQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.WDAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompR
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.WeilDeligneFrobeniusEigenvalueOfFullFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.OrdinaryFlagInertiaWeights
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.ExistsCuspidalSatakeAtPrimeToLevelOfNewform
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.LocalMemPrincipalCongruence

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.CuspRep GlobalTheory.LocLanglands GlobalTheory.LocGL Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FrobHecke

theorem normV_rat {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 ℚ)) (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    normV w = p := by
  have h : normV w = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hN : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 ℚ)}) = p := by
    rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank]
    simp
  have hd : Ideal.absNorm w.asIdeal ∣ p :=
    hN ▸ Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hw)
  rw [h]
  refine ((Nat.dvd_prime hp).1 hd).resolve_left ?_
  rw [Ideal.absNorm_eq_one_iff]
  exact w.isPrime.ne_top

theorem dualTw_det {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin 2) k) :
    DualTw r (Matrix.GeneralLinearGroup.det.comp r) := by
  refine ⟨⟨!![0, 1; -1, 0], !![0, -1; 1, 0], ?_, ?_⟩, fun s => ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_fin_two]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_fin_two]
  · have e : (r s : Matrix (Fin 2) (Fin 2) k) = !![(r s : Matrix (Fin 2) (Fin 2) k) 0 0, (r s : Matrix (Fin 2) (Fin 2) k) 0 1;
        (r s : Matrix (Fin 2) (Fin 2) k) 1 0, (r s : Matrix (Fin 2) (Fin 2) k) 1 1] := Matrix.eta_fin_two _
    simp only [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.val_det_apply, Matrix.coe_units_inv]
    rw [e, Matrix.det_fin_two_of]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem frobValue_isRoot_heckePoly : Af.Hypotheses₂ → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (V : R2 Ω l) (A : ValuationSubring Ω) (κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ) (g : Newform (2 * e + 1)), l ≠ 2 → 1 ≤ e → Continuous V → IsIrr V → (∃ M : ℕ, 1 ≤ M ∧ LevelAway l M V) → (∃ M : ℕ, 1 ≤ M ∧ KillsMu M (dt V)) → OverL l A → IsFlagOn V (Dec (F := ℚ) A) κ → (∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A → κ 0 s = cycBar ℚ Ω l s ^ (e : ℤ) ∧ κ 1 s = cycBar ℚ Ω l s ^ (-(e : ℤ))) → g.Att ι (tw V (cycBar ℚ Ω l ^ (-(e : ℤ)))) → ¬ l ∣ g.M → ∀ σ : ↥(Dec (F := ℚ) A), IsFrob A l (σ : G ℚ Ω) → ∃ α : ℂ, (g.heckePoly l).IsRoot α ∧ (α = ι ((κ 0 σ * cycBar ℚ Ω l σ ^ (-(e : ℤ)) : (Qbar l)ˣ) : Qbar l) ∨ α⁻¹ = ι ((κ 0 σ * cycBar ℚ Ω l σ ^ (-(e : ℤ)) : (Qbar l)ˣ) : Qbar l)) := by
  intro P l _ Ω _ _ _ ι e V A κ g hl he hc hirr hway hdet hA hfl hI hatt hgM σ hσ
  obtain ⟨M, hM, haway⟩ := hway
  obtain ⟨M', hM', hdet⟩ := hdet
  obtain ⟨π, hreg, hattR, hsat⟩ := GlobalTheory.T.exists_cuspidal_satake_at_prime_to_level_of_newform P e g l Ω ι V he hatt hgM
  have hlev := GlobalTheory.T.ordinary_flag_inertia_weights l Ω e M V A κ he hM hc haway hA hfl hI
  obtain ⟨v, hv, hlv⟩ := hA
  have hnv : normV v = l := normV_rat (Fact.out) v hlv
  have hdual : ∃ θ, IsCycWt l 0 θ ∧ DualTw V θ :=
    ⟨dt V, ⟨M', dt V, hM', hdet, by rw [zpow_zero, one_mul]⟩, dualTw_det V⟩
  obtain ⟨j, L0, hj0, hL⟩ := GlobalTheory.PlaceBridge.exists_locBridge l ℚ Ω v A hlv hv
  obtain ⟨Bw, hB, -⟩ := hL L0 le_rfl
  have hj : Induces Bw := fun x => by rw [hB]; exact hj0 x
  have hm : StrictAnti ![(e : ℤ), -(e : ℤ)] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all <;> omega
  obtain ⟨hpst, hcomp⟩ := compatAtLQ P 2 le_rfl 0 l hl Ω ι V π hc hirr M ![(e : ℤ), -(e : ℤ)] hM hm hlev hdual hreg
    hattR v A hv _ Bw hj
  obtain ⟨B, hB, hpoly⟩ := hsat v hlv
  obtain ⟨⟨τ, hτ⟩, hiso⟩ := locCompR P ℚ 2 π v
  have hBτ := ((satLoc P ℚ 2 v τ).2 _ π.finPart (hiso τ hτ) B).1 hB
  have L := P.litN.loc
  obtain ⟨rc, hrc⟩ := L.llc ℚ Ω A v hv
  have hrec : IsRec hv rc := GlobalTheory.T.rec_of_rec_literal L.dzc L.dzi L.exh L.multi L.cos L.zel L.geo L.bz ℚ Ω A v hv rc hrc
  have heq := hcomp τ hτ rc hrec
  have hσ' : IsFrob A (normV v) (σ : G ℚ Ω) := by rw [hnv]; exact hσ
  let φ : ↥(Weil hv) := ⟨σ, mem_Weil_of_isFrob hv hσ'⟩
  have hd : deg φ = 1 := deg_eq_one_iff.2 hσ'
  have hfa : FlagAt M ![(e : ℤ), -(e : ℤ)] V A κ := by
    refine ⟨fun _ => 1, fun _ _ _ => rfl, hfl, fun i s hs => ?_⟩
    fin_cases i
    · simpa using (hI s hs).1
    · simpa using (hI s hs).2
  have h1 := GlobalTheory.T.weilDeligne_frobenius_eigenvalue_of_full_flag ℚ Ω l ι 2 M hM _ V hc v A hv _ Bw hj κ hfa hpst 0 φ hd
  obtain ⟨μ, hμ, -⟩ := Lev.flagPol ℚ Ω l ι 2 M hM _ V hc v A hv _ Bw hj κ hfa hpst
  rw [heq (Or.inl ((Lev.ssCalc ℚ Ω A v hv).1 2 _ μ hμ))] at h1
  obtain ⟨b, hb, hzb⟩ := GlobalTheory.T.satake_roots_local_correspondence ℚ Ω A v hv rc hrec 2 τ B hBτ φ hd _ h1
  rw [hnv] at hb
  have hinc : Subgroup.inclusion (Weil_le_Dec hv) φ = σ := rfl
  refine ⟨(l : ℂ) ^ e * b, ?_, Or.inr ?_⟩
  · rw [← hpoly, Polynomial.IsRoot, Polynomial.eval_multiset_prod]
    refine Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨_, Multiset.mem_map_of_mem _ hb, ?_⟩)
    simp
  · rw [hinc, hnv] at hzb
    simp only [Matrix.cons_val_zero] at hzb
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [zpow_natCast] at hzb
    linear_combination hzb

end GlobalTheory.FrobHecke

end

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newform_flag_local_of_level : Af.Hypotheses₂ → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (V : R2 Ω l) (A : ValuationSubring Ω) (κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ) (g : Newform (2 * e + 1)), l ≠ 2 → 1 ≤ e → Continuous V → IsIrr V → (∃ M : ℕ, 1 ≤ M ∧ LevelAway l M V) → (∃ M : ℕ, 1 ≤ M ∧ KillsMu M (dt V)) → OverL l A → IsFlagOn V (Dec (F := ℚ) A) κ → (∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A → κ 0 s = cycBar ℚ Ω l s ^ (e : ℤ) ∧ κ 1 s = cycBar ℚ Ω l s ^ (-(e : ℤ))) → g.Att ι (tw V (cycBar ℚ Ω l ^ (-(e : ℤ)))) → ¬ l ∣ g.M → ∀ σ : ↥(Dec (F := ℚ) A), IsFrob A l (σ : G ℚ Ω) → ∃ α : ℂ, (g.heckePoly l).IsRoot α ∧ (α = ι ((κ 0 σ * cycBar ℚ Ω l σ ^ (-(e : ℤ)) : (Qbar l)ˣ) : Qbar l) ∨ α⁻¹ = ι ((κ 0 σ * cycBar ℚ Ω l σ ^ (-(e : ℤ)) : (Qbar l)ˣ) : Qbar l)) := by
  first | exact @GlobalTheory.FrobHecke.frobValue_isRoot_heckePoly | exact GlobalTheory.FrobHecke.frobValue_isRoot_heckePoly | (intros; apply GlobalTheory.FrobHecke.frobValue_isRoot_heckePoly <;> assumption)

end
