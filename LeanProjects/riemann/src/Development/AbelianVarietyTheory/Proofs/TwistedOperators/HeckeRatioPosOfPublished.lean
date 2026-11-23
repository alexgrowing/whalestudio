import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PartialLFunctionCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousInfiniteAdeleMap
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealPosAtOneOfRight
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OneSubRePosOfNormLeHalf
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CmConjugationOnPrimesProperties
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CmLocalCharacterValueBounded
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CmCharacterConjugateInverse
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CmCharacterConjugationSymmetry
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterInfinityExponentGroupLaws
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.InputsHecke

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.HeckeRatio

section Standard

open HeckeCharacterZeroLocus.ThmBIn GlobalTheory.LFun GlobalTheory.HeckeOne GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele GlobalTheory.UnitaryHeckeBaseChange
open Formalism.L2.Host (HChar)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_conj_prime (hσ : IsCMExt F E σ) (χ : (AE F E)ˣ →* Circle)
    (hF : ∀ a : (AF F)ˣ, χ (idF F E a) = 1) :
    ∃ c : HeightOneSpectrum (𝓞 E) ≃ HeightOneSpectrum (𝓞 E), (∀ P, normP (c P) = normP P) ∧
      (∀ P, (c P).under (𝓞 F) = P.under (𝓞 F)) ∧ ∀ P, chiAt σ χ (c P) = starRingEnd ℂ (chiAt σ χ P) := by
  obtain ⟨c, hcc, hN, hmem, hund, hinv, hint, hidem⟩ := GlobalTheory.cmConjugation_on_primes_adeles_idempotents F E σ hσ
  have hsd := GlobalTheory.ideleChar_conj_eq_inv_of_trivial_on_base F E σ hσ χ hF
  have hun := GlobalTheory.HeckeUnif.unifIdele_exists_chiAt F E σ hσ χ
  have hram : ∀ P, IsUnramAt σ χ P → IsUnramAt σ χ (c P) := by
    rintro P ⟨e, f, he, hz⟩
    refine ⟨cA σ e, f, hidem P e f he, fun z h1 h2 h3 => ?_⟩
    have h4 : χ (Units.map (cA σ).toMonoidHom z) = 1 := by
      apply hz
      · change cA σ (z : AE F E) = e * cA σ (z : AE F E) + (1 - e)
        have := congrArg (cA σ) h1
        rwa [map_add, map_mul, map_sub, map_one, hinv] at this
      · exact (hint _).2 h2
      · exact (hint _).2 h3
    rw [hsd z (Units.map (cA σ).toMonoidHom z) rfl] at h4
    exact inv_eq_one.1 h4
  have hunif : ∀ P x, IsUnifIdele σ P x → IsUnifIdele σ (c P) (Units.map (cA σ).toMonoidHom x) := by
    rintro P x ⟨e, f, ϖ, he, h1, h2, h3⟩
    have hy : ((RingOfIntegers.mapRingHom σ.toRingHom ϖ : 𝓞 E) : E) = σ ϖ := rfl
    refine ⟨cA σ e, f, RingOfIntegers.mapRingHom σ.toRingHom ϖ, hidem P e f he,
      ((hmem P _ _ hy).1).2 h1, fun h => h2 (((hmem P _ _ hy).2).1 h), ?_⟩
    change cA σ (x : AE F E) = _
    rw [h3, map_add, map_mul, map_sub, map_one, GlobalTheory.cA_incA_apply, hy]
  refine ⟨c, hN, fun P => ((hund P (c P)).2 (Or.inr rfl)).symm, fun P => ?_⟩
  by_cases hP : IsUnramAt σ χ P
  · obtain ⟨x, hx⟩ := (hun P).1
    rw [(hun P).2.1 hP x hx, (hun (c P)).2.1 (hram P hP) _ (hunif P x hx),
      hsd x (Units.map (cA σ).toMonoidHom x) rfl, Circle.coe_inv_eq_conj]
  · have hP' : ¬ IsUnramAt σ χ (c P) := fun h => hP (by simpa [hcc] using hram _ h)
    simp [chiAt, hP, hP']

def toH (χ : UnitaryHeckeChar E) : HChar E := toHChar χ.toHom ⟨χ.continuous_toHom, χ.map_principal⟩

theorem unrAt_toH (χ : UnitaryHeckeChar E) (P : HeightOneSpectrum (𝓞 E)) :
    (toH χ).UnrAt P ↔ χ.IsUnramifiedAt P :=
  forall₂_congr fun _ _ => ⟨fun h => Circle.ext (congrArg Units.val h),
    fun h => (congrArg Circle.toUnits h).trans (map_one _)⟩

theorem val_toH (χ : UnitaryHeckeChar E) {P : HeightOneSpectrum (𝓞 E)} (h : χ.IsUnramifiedAt P) :
    (((toH χ).val P : ℂˣ) : ℂ) = χ.valueAt P :=
  (χ.valueAt_eq h (Formalism.L2.Host.unif_spec P)).symm

theorem eulerFactor_toH (χ : UnitaryHeckeChar E) (s : ℂ) (P : HeightOneSpectrum (𝓞 E)) :
    GlobalTheory.CMVal.eulerFactor (toH χ) s P = χ.eulerFactor P s := by
  unfold GlobalTheory.CMVal.eulerFactor UnitaryHeckeChar.eulerFactor
  split_ifs with h
  · rw [val_toH χ ((unrAt_toH χ P).1 h)]
  · rw [χ.valueAt_of_ramified fun h' => h ((unrAt_toH χ P).2 h'), zero_mul, sub_zero, inv_one]

theorem eq_zero_of_npow (H : GlobalTheory.Published.HeckeLPartialContinuation) {z : ℂ} (hz : z.re = 0)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), npow P (-z) = 1) : z = 0 := by
  obtain ⟨Z, hZ, h1, h2⟩ := (H E ∅ Set.finite_empty).2
  have e : ∀ s : ℂ, zetaOff (K := E) ∅ (s + z) = zetaOff (K := E) ∅ s := fun s => by
    simp only [zetaOff, eulerProd, locL, neg_add, LFun.npow_add, h, mul_one]
  have k := GlobalTheory.IndefiniteRowSideFullHecke.PartialLFunctionCharacter.eq_of_eqOn_re (f := fun s => Z s * (s + z - 1)) (g := fun s => Z (s + z) * (s - 1))
    (hZ.mul (by fun_prop)) ((hZ.comp (by fun_prop)).mul (by fun_prop)) fun s hs => by
      rw [h1 s hs, h1 (s + z) (by simpa [hz] using hs), e]; ring
  have k1 := congrFun k 1
  simp only [sub_self, mul_zero, add_sub_cancel_left] at k1
  exact (mul_eq_zero.1 k1).resolve_left (h2 1 (by simp))

theorem exists_entire_pos (H : GlobalTheory.Published.HeckeLPartialContinuation) (hσ : IsCMExt F E σ)
    (χ : (AE F E)ˣ →* Circle) (hχ : IsHeckeChar F E χ) (hF : ∀ a : (AF F)ˣ, χ (idF F E a) = 1) (hne : χ ≠ 1)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (p : HeightOneSpectrum (𝓞 E) → Prop)
    (hp : ∀ P, p P ↔ P.under (𝓞 F) ∉ S) :
    ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
      (∀ s : ℂ, 1 < s.re → HasProd (fun P : {P // p P} => lfac σ χ P.1 s) (Λ s)) ∧
      ∀ n : ℕ, 1 ≤ n → (Λ n).im = 0 ∧ 0 < (Λ n).re := by
  obtain ⟨c, hN, hU, hc⟩ := exists_conj_prime hσ χ hF
  obtain ⟨χ, rfl, -⟩ := (GlobalTheory.UnitaryHeckeBaseChange.isHeckeChar_iff hσ χ).1 hχ
  have hu : (toH χ).IsUnitary := isUnitary_toHChar _ _
  have hnp : ¬ ∃ t : ℝ, IsNormPow (toH χ) t := by
    rintro ⟨t, ht⟩
    rw [isNormPow_iff] at ht
    have hv : ∀ P, chiAt σ (pull F χ) P = npow P (-((t : ℂ) * Complex.I)) := fun P => by
      rw [chiAt_eq hσ, ← val_toH χ ((unrAt_toH χ P).1 (ht ▸ unrAt_normChar t P)), ht, val_normChar]
      rfl
    have h0 : (t : ℂ) * Complex.I + (t : ℂ) * Complex.I = 0 := eq_zero_of_npow (E := E) H (by simp) fun P => by
      have e1 : npow (c P) (-((t : ℂ) * Complex.I)) = npow P (-((t : ℂ) * Complex.I)) :=
        congrArg (fun n : ℕ => (n : ℂ) ^ (-((t : ℂ) * Complex.I))) (hN P)
      have e2 := hc P
      rw [hv, hv, e1] at e2
      rw [neg_add, LFun.npow_add]
      nth_rewrite 2 [e2]
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_npow]
      simp
    have ht0 : t = 0 := by simpa using congrArg Complex.im h0
    rw [ht0, normChar_zero] at ht
    refine hne ((pull_eq_one_iff hσ χ).2 (UnitaryHeckeChar.ext (MonoidHom.ext fun x => Circle.ext ?_)))
    exact congrArg (fun ψ : HChar E => ((ψ.1 x : ℂˣ) : ℂ)) ht
  obtain rfl : p = fun P => P ∉ {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) ∈ S} :=
    funext fun P => propext (hp P)
  have hT : {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) ∈ S}.Finite := by
    have := Filter.mem_cofinite.1 (tendsto_under F E S.finite_toSet.compl_mem_cofinite)
    exact this.subset fun P hP h => h hP
  obtain ⟨Λ, hΛ, h1, h2⟩ := (H E _ hT).1 _ hu hnp
  have hprod : ∀ s : ℂ, 1 < s.re → HasProd (fun P : {P // P ∉ {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) ∈ S}} =>
      lfac σ (pull F χ) P.1 s) (Λ s) := fun s hs => by
    have k := (converges_heckeFam {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) ∈ S} hu hs).hasProd
    simp only [locL_heckeFam, eulerFactor_toH, ← lfac_eq hσ] at k
    rw [h1 s hs]
    exact k
  obtain ⟨k1, k2⟩ := eulerProduct_eq_exp_and_pos {P // P ∉ {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) ∈ S}}
    (fun P => normP P.1) (fun P => chiAt σ (pull F χ) P.1) (fun P => GlobalTheory.LFun.one_lt_absNorm P.1)
    (fun P => (GlobalTheory.HeckeUnif.unifIdele_exists_chiAt F E σ hσ _ P.1).2.2)
    (fun t ht => (UnitaryHeckeChar.summable_absNorm_rpow ht).subtype _)
  have hpos : ∀ s : ℂ, 1 < s.re → s.im = 0 → (Λ s).im = 0 ∧ 0 < (Λ s).re := fun s hs hs0 => by
    rw [(hprod s hs).unique (k1 s hs).2]
    exact k2 (c.subtypeEquiv fun P => by simp only [Set.mem_ofPred_eq, hU]) (fun P => hN P.1) (fun P => hc P.1) s hs hs0
  refine ⟨Λ, hΛ, hprod, fun n hn => ?_⟩
  rcases hn.eq_or_lt with rfl | hlt
  · simpa using real_pos_at_one_of_right Λ hΛ.continuous.continuousAt (h2 1 (by simp)) hpos
  · exact hpos n (by simpa using hlt) (by simp)

end Standard

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult GlobalTheory.IndefiniteRowSideFullHecke.PartialLFunctionCharacter

variable {D : D7}

theorem offS_iff (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    OffS D S w ↔ w.under (𝓞 D.host.F) ∉ S := by
  constructor
  · intro h hw
    obtain ⟨x, hx, hy⟩ := h _ hw
    exact hy (algebraMap _ _ x) rfl hx
  · intro h u hu
    have : ¬ u.asIdeal ≤ (w.under (𝓞 D.host.F)).asIdeal := fun hle =>
      h (HeightOneSpectrum.ext (u.isMaximal.eq_of_le (w.under _).isPrime.ne_top hle) ▸ hu)
    obtain ⟨x, hx, hx'⟩ := SetLike.not_le_iff_exists.1 this
    refine ⟨x, hx, fun y hy hw => hx' ?_⟩
    obtain rfl : y = algebraMap _ _ x := RingOfIntegers.ext hy
    exact hw

theorem isPrimeIdem_eq : IsPrimeIdem (D := D) = HeckeCharacterZeroLocus.ThmBIn.IsPrimeIdem D.sp.cm.sig := rfl

theorem isUnifIdele_eq : Mi.IsUnifIdele (D := D) = HeckeCharacterZeroLocus.ThmBIn.IsUnifIdele D.sp.cm.sig := by
  funext P x
  unfold Mi.IsUnifIdele HeckeCharacterZeroLocus.ThmBIn.IsUnifIdele
  rw [isPrimeIdem_eq]
  rfl

theorem isUnramAt_eq : Mi.IsUnramAt (D := D) = HeckeCharacterZeroLocus.ThmBIn.IsUnramAt D.sp.cm.sig := by
  funext χ P
  unfold Mi.IsUnramAt HeckeCharacterZeroLocus.ThmBIn.IsUnramAt
  rw [isPrimeIdem_eq]
  rfl

theorem lfac_eq (χ : (AE D)ˣ →* Circle) : Mi.lfac χ = HeckeCharacterZeroLocus.ThmBIn.lfac D.sp.cm.sig χ := by
  funext P s
  have key : ∀ (A A' : Prop) (U U' : (AE D)ˣ → Prop), A = A' → U = U' →
      (open Classical in if h : A ∧ ∃ x, U x then ((χ h.2.choose : Circle) : ℂ) else 0) =
      (open Classical in if h : A' ∧ ∃ x, U' x then ((χ h.2.choose : Circle) : ℂ) else 0) := by
    rintro _ _ _ _ rfl rfl
    rfl
  have e0 := key (Mi.IsUnramAt χ P) (HeckeCharacterZeroLocus.ThmBIn.IsUnramAt D.sp.cm.sig χ P) (Mi.IsUnifIdele P)
    (HeckeCharacterZeroLocus.ThmBIn.IsUnifIdele D.sp.cm.sig P) (by rw [isUnramAt_eq]) (by rw [isUnifIdele_eq])
  have e : Mi.chiAt χ P = HeckeCharacterZeroLocus.ThmBIn.chiAt D.sp.cm.sig χ P := by
    unfold Mi.chiAt HeckeCharacterZeroLocus.ThmBIn.chiAt
    exact e0
  unfold Mi.lfac HeckeCharacterZeroLocus.ThmBIn.lfac
  rw [e]
  rfl

theorem heckeRatioPos_of_partialContinuation (H : GlobalTheory.Published.HeckeLPartialContinuation) (D : D7) : HeckeRatioPos D := by
  rintro μ μ' hμ hμ' hF hF' ⟨τ, e, e', h1, h2, hne⟩ t
  have hχ : IsHeckeChar D (μ * μ'⁻¹) := ⟨hμ.1.mul hμ'.1.inv, fun x => by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hμ.2 x, hμ'.2 x, inv_one, mul_one]⟩
  have hχF : ∀ a, (μ * μ'⁻¹) (idF D a) = 1 := fun a => by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hF a, hF' a, inv_one, mul_one]
  have hχ1 : μ * μ'⁻¹ ≠ 1 := fun h => by
    obtain rfl := mul_inv_eq_one.1 h
    exact hne (neg_injective (GlobalTheory.Mem.HeckeExp.hasInfExp_unique h1 h2))
  have key := exists_entire_pos H (Formalism.IndefR.ThmB.InputsHecke.isCMExt D) (μ * μ'⁻¹) hχ hχF hχ1
  refine ⟨?_, fun S => ?_⟩
  · obtain ⟨Λ, a1, a2, a3⟩ := key ∅ (fun _ => True) fun P => by simp
    refine ⟨Λ, ⟨a1, fun s hs => ?_⟩, fun n hn _ => a3 n hn⟩
    rw [lfac_eq]
    exact (Equiv.subtypeUnivEquiv (p := fun _ => True) fun _ => trivial).hasProd_iff.1 (a2 s hs)
  · obtain ⟨Λ, a1, a2, a3⟩ := key S (OffS D S) (offS_iff S)
    refine ⟨Λ, ⟨a1, fun s hs => ?_⟩, fun n hn _ => a3 n hn⟩
    rw [lfac_eq]
    exact a2 s hs

theorem heckeRatioPos (D : D7) : HeckeRatioPos D :=
  heckeRatioPos_of_partialContinuation GlobalTheory.Published.HeckeLPartialContinuation_holds D

end GlobalTheory.HeckeRatio

end
