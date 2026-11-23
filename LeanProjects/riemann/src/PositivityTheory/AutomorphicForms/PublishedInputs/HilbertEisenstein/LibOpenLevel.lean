import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SSmooth
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.KLevTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.GlobFixed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenIdeleSubgroupContainsCongruenceUnits

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published
open Matrix UpperTheory.V.Af.GlobalFixedVectors

namespace UpperTheory.HilbertEisensteinWeightOne.LibOpenLevel

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private theorem local_mem_principal_congruence {M : ℕ} (w : HeightOneSpectrum (𝓞 F)) (c : ℕ)
    (hM : (M : w.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c)
    {k : GL (Fin 2) (Af F)} (hk : k ∈ KLev F 2 M) : GeneralLinearGroup.map (pLoc F w) k ∈ K1 w c := by
  obtain ⟨g, hg, rfl⟩ := hk
  let p : Ohat F →+* w.adicCompletionIntegers F :=
    ((pLoc F w).comp (Ohat F).subtype).codRestrict (w.adicCompletionIntegers F) fun x => GlobalFixedVectors.mem_Ohat.1 x.2 w
  refine ⟨GeneralLinearGroup.map p g, ?_, Units.ext rfl⟩
  have key : GeneralLinearGroup.map (n := Fin 2)
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c)) (GeneralLinearGroup.map p g) = 1 := by
    let q := Ideal.quotientMap (I := Ideal.span {(M : ↥(Ohat F))}) (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c) p
      ((Ideal.span_singleton_le_iff_mem _).2 (by simpa using hM))
    have := congrArg (GeneralLinearGroup.map q) (MonoidHom.mem_ker.1 hg)
    rw [map_one] at this
    rw [← this]
    rfl
  exact Subgroup.mem_comap.2 (key ▸ one_mem _)

private theorem exists_level (c : HeightOneSpectrum (𝓞 F) → ℕ) (hc : {w | c w ≠ 0}.Finite) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ w : HeightOneSpectrum (𝓞 F),
      (M : w.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c w := by
  refine ⟨∏ w ∈ hc.toFinset, Ideal.absNorm w.asIdeal ^ c w, ?_, fun w => ?_⟩
  · refine Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ ?_)
    exact fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  · by_cases h : c w = 0
    · simp [h]
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun w : HeightOneSpectrum (𝓞 F) => Ideal.absNorm w.asIdeal ^ c w)
      (hc.mem_toFinset.2 h)
    rw [hm, Nat.cast_mul, Nat.cast_pow]
    refine Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ?_ _)
    have h1 := Ideal.absNorm_mem w.asIdeal
    rw [← map_natCast (algebraMap (𝓞 F) (w.adicCompletionIntegers F))]
    generalize (Ideal.absNorm w.asIdeal : 𝓞 F) = x at h1
    refine (Valuation.mem_maximalIdeal_iff _ (Valued.v : Valuation (w.adicCompletion F) _)).2 ?_
    have h2 : Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) x) < 1 := by
      rw [IsScalarTower.algebraMap_apply (𝓞 F) F (w.adicCompletion F)]
      exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).trans_lt ((w.valuation_lt_one_iff_mem x).2 h1)
    exact h2

theorem finite_support {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (hH : Hyp ω c) :
    {w | c w ≠ 0}.Finite := by
  obtain ⟨m, hm, hω⟩ := isOfFinOrder_iff_pow_eq_one.1 hH.fin
  have ho := GlobalTheory.HeckeGal.isOpen_ker_of_pow ω.1 ω.2.1 hm fun x => by
    have := congrArg (fun ξ : HChar F => ξ.1 x) hω
    simpa using this
  obtain ⟨S, M, hS, key⟩ := GlobalTheory.OpenIdeleCongr.localIdele_mem_of_isOpen ω.1.ker ho
  refine hS.subset fun w hw => ?_
  by_contra hwS
  exact hw (Nat.le_zero.1 ((hH.cond w).2 fun x hu _ => MonoidHom.mem_ker.1 (key w x hu fun h => absurd h hwS)))

variable (F) in

def Kc (c : HeightOneSpectrum (𝓞 F) → ℕ) : Subgroup (GL (Fin 2) (Af F)) :=
  ⨅ w, (K1 w (c w)).comap (GeneralLinearGroup.map (pLoc F w))

theorem mem_Kc {c : HeightOneSpectrum (𝓞 F) → ℕ} {k : GL (Fin 2) (Af F)} :
    k ∈ Kc F c ↔ ∀ w, GeneralLinearGroup.map (pLoc F w) k ∈ K1 w (c w) := by
  simp [Kc, Subgroup.mem_iInf]

theorem isOpen_Kc {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite) : IsOpen (Kc F c : Set (GL (Fin 2) (Af F))) := by
  obtain ⟨M, hM1, hM⟩ := exists_level c hc
  exact Subgroup.isOpen_mono (fun k hk => mem_Kc.2 fun w => local_mem_principal_congruence w _ (hM w) hk) (isOpen_KLev hM1)

def stab (φ : UpperTheory.V.TR.Sm F 2) : Subgroup (GL (Fin 2) (Af F)) where
  carrier := {k | UpperTheory.V.TR.finRep F 2 k φ = φ}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem isOpen_stab {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (hH : Hyp ω c) (φ : UpperTheory.V.TR.Sm F 2)
    (h : ∀ k ∈ Kc F c, UpperTheory.V.TR.finRep F 2 k φ = φ) : IsOpen {k | UpperTheory.V.TR.finRep F 2 k φ = φ} :=
  Subgroup.isOpen_mono (H₂ := stab φ) (fun k hk => h k hk) (isOpen_Kc (finite_support hH))

theorem isOpen_stab_of_glob {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (hH : Hyp ω c)
    (φ : UpperTheory.V.TR.Sm F 2)
    (h : ∀ k : GL (Fin 2) (Af F), (∀ w, GeneralLinearGroup.map (pLoc F w) k ∈ K1 w (c w)) →
      ∀ g, φ.1 (g * finGL F 2 k) = φ.1 g) :
    IsOpen {k | UpperTheory.V.TR.finRep F 2 k φ = φ} :=
  isOpen_stab hH φ fun k hk => Subtype.ext (funext fun g => h k (mem_Kc.1 hk) g)

end UpperTheory.HilbertEisensteinWeightOne.LibOpenLevel
