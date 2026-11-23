import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsClassSystem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChangeOfSplittingPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalAnticyclotomicCharacterLaws
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlNeOfSplit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArtinPullbackIsGoodTwistOfAnticyclotomicTame
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharUnramifiedOutsideSplitSetOfTameStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoprimeAbsNormOfNatCastNotMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwistPullTame

theorem coprime_absNorm {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {m : ℕ}
    (hm : ((m : ℕ) : 𝓞 E) ∉ P.asIdeal) : Nat.Coprime m (Ideal.absNorm P.asIdeal) := by
  first
  | exact @_root_.GlobalTheory.CoprimeAbsNorm.coprime_absNorm_of_natCast_notMem
  | exact _root_.GlobalTheory.CoprimeAbsNorm.coprime_absNorm_of_natCast_notMem
  | (apply _root_.GlobalTheory.CoprimeAbsNorm.coprime_absNorm_of_natCast_notMem <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoprimeAbsNorm.coprime_absNorm_of_natCast_notMem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoprimeAbsNorm.coprime_absNorm_of_natCast_notMem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoprimeAbsNorm.coprime_absNorm_of_natCast_notMem ..)

open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin) in

theorem tameAt_of_ine {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {art : Neutral.B1.Ideles E →* Gab E Ω}
    (ha : IsGlobalArtin art) {r : G E Ω →* ℂˣ} {χ : Formalism.L2.Host.HChar E} (h : GlobalTheory.ToricDistribution.Corr art r χ)
    {P : HeightOneSpectrum (𝓞 E)} {B : ValuationSubring Ω} (hB : IsPlaceOver B P) {m : ℕ}
    (hm : ((m : ℕ) : 𝓞 E) ∉ P.asIdeal) (hi : ∀ σ ∈ Ine (F := E) B, r σ ^ m = 1) : χ.TameAt P := by
  intro x hx hx1
  obtain ⟨a, ha'⟩ := GlobalTheory.Mem.UnrAe.exists_levelLe χ P
  have hmem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem P.asIdeal
  have hlt : Valued.v ((Ideal.absNorm P.asIdeal : ℕ) : P.adicCompletion E) < 1 := by
    rw [← map_natCast (algebraMap (𝓞 E) (P.adicCompletion E)), GlobalTheory.Mem.WildChar.valued_algebraMap_lt_one]
    exact hmem
  have h3 := ha' _ (GlobalTheory.Mem.UnrAe.isUnitAt_pow hx (Ideal.absNorm P.asIdeal ^ a)) (by
    rw [Units.val_pow_eq_pow_val]
    refine GlobalTheory.Mem.WildChar.val_pow_pow_sub_one_le _ (le_of_eq hx) (hx1.trans_lt ?_) hlt a
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num)
  rw [map_pow] at h3
  have h4 : χ.loc P x ^ m = 1 := by
    obtain ⟨σ, hσ, e⟩ := (ha.ine P B hB _).mp ⟨x, hx, rfl⟩
    have e2 : χ.loc P x = r σ := h _ σ e.symm
    rw [e2, hi σ hσ]
  have hc : Nat.Coprime m (Ideal.absNorm P.asIdeal ^ a) := (coprime_absNorm hm).pow_right a
  rw [← pow_one (χ.loc P x), ← hc.gcd_eq_one]
  exact pow_gcd_eq_one.2 ⟨h4, h3⟩

theorem ine_pow_of_conj {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N) {A : Type} [CommGroup A]
    {φ : G D.host.E N.Om →* A} (hanti : AntiHom X.cc φ) {P P' : Pl D.host.E} (hc : Formalism.BasicNotions.IsConjPl D.host P P') {m : ℕ}
    (h : ∀ B : ValuationSubring N.Om, IsPlaceOver B P → ∀ σ ∈ Ine (F := D.host.E) B, φ σ ^ m = 1)
    (B' : ValuationSubring N.Om) (hB' : IsPlaceOver B' P') (σ : G D.host.E N.Om) (hσ : σ ∈ Ine (F := D.host.E) B') :
    φ σ ^ m = 1 := by
  have h1 := GlobalTheory.TwistDet.cConj_mem_ine X hσ
  have h2 := GlobalTheory.TwistDet.isPlaceOver_moveVal_cc X (GlobalTheory.TwistDet.isConjPl_symm hc) hB'
  have h3 := h _ h2 _ h1
  rw [GlobalTheory.TwistDet.antiHom_cConj X hanti, inv_pow, inv_eq_one] at h3
  exact h3

theorem natCast_mem_conj {D : D7} {P P' : Pl D.host.E} (hc : Formalism.BasicNotions.IsConjPl D.host P P') (m : ℕ) :
    ((m : ℕ) : 𝓞 D.host.E) ∈ P'.asIdeal ↔ ((m : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
  rw [GlobalTheory.TwistDet.isConjPl_iff.1 hc, map_natCast]

end GlobalTheory.TwistPullTame

namespace GlobalTheory.TwistPullTame

open GlobalTheory.TwistPull

theorem good_pull_tame : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (a : Recip D N.Om), a.Good → ∀ (A : Type) [CommGroup A] (φ : G D.host.E N.Om →* A), IsOpen (φ.ker : Set (G D.host.E N.Om)) → AntiHom X.cc φ → ∀ Q : Finset (Pl D.host.E), SplitSet Q → (∀ P ∈ Q, ∃ m : ℕ, ((m : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ ∀ B : ValuationSubring N.Om, IsPlaceOver B P → ∀ σ ∈ Ine (F := D.host.E) B, φ σ ^ m = 1) → (∀ v : Pl D.host.E, v ∉ Q → (∀ P ∈ Q, ¬ Formalism.BasicNotions.IsConjPl D.host P v) → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ σ ∈ Ine (F := D.host.E) B, φ σ = 1) → (⟨Q, a.pull φ, resOf (a.pull φ)⟩ : Twist D A).Good := by
  intro D N X a ha A _ φ hφ hanti Q hQ hQm hunr
  haveI := finite_range (D := D) hφ
  set M := Nat.card φ.range with hMdef
  have hM : M ≠ 0 := Nat.card_pos.ne'
  have hr : ∀ f : φ.range →* ℂˣ, IsOpen ((f.comp φ.rangeRestrict).ker : Set (G D.host.E N.Om)) ∧
      ∀ σ, (f.comp φ.rangeRestrict) σ ^ M = 1 := fun f => by
    refine ⟨Subgroup.isOpen_mono (H₁ := φ.ker) (fun g hg => ?_) hφ, fun σ => ?_⟩
    · have : φ.rangeRestrict g = 1 := Subtype.ext (MonoidHom.mem_ker.1 hg)
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, this, map_one]
    · rw [MonoidHom.comp_apply, ← map_pow, pow_card_eq_one', map_one]
  have hanti' : ∀ f : φ.range →* ℂˣ, AntiHom X.cc (f.comp φ.rangeRestrict) := fun f g g' hg => by
    have e : φ.rangeRestrict g' = (φ.rangeRestrict g)⁻¹ := Subtype.ext (hanti g g' hg)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, e, map_inv]

  have hin : ∀ P ∈ Q, ∀ P' : Pl D.host.E, (P' = P ∨ Formalism.BasicNotions.IsConjPl D.host P P') → ∃ m : ℕ,
      ((m : ℕ) : 𝓞 D.host.E) ∉ P'.asIdeal ∧
        ∀ B : ValuationSubring N.Om, IsPlaceOver B P' → ∀ σ ∈ Ine (F := D.host.E) B, φ σ ^ m = 1 := by
    intro P hP P' hP'
    obtain ⟨m, hm, hB⟩ := hQm P hP
    rcases hP' with rfl | hc
    · exact ⟨m, hm, hB⟩
    · exact ⟨m, fun h => hm ((natCast_mem_conj hc m).1 h), ine_pow_of_conj X hanti hc hB⟩
  have htame : ∀ (f : φ.range →* ℂˣ) (χ : Formalism.L2.Host.HChar D.host.E),
      GlobalTheory.ToricDistribution.Corr a.art (f.comp φ.rangeRestrict) χ →
      ∀ P ∈ Q, ∀ P' : Pl D.host.E, (P' = P ∨ Formalism.BasicNotions.IsConjPl D.host P P') → χ.TameAt P' := by
    intro f χ hχ P hP P' hP'
    obtain ⟨m, hm, hB⟩ := hin P hP P' hP'
    obtain ⟨B, hB'⟩ := ReciprocityTheory.Gal.exists_isPlaceOver N.Om P'
    refine tameAt_of_ine ha.artin hχ hB' hm fun σ hσ => ?_
    have e : φ.rangeRestrict σ ^ m = 1 := Subtype.ext (by
      rw [SubmonoidClass.coe_pow, MonoidHom.coe_rangeRestrict, hB B hB' σ hσ]; rfl)
    rw [MonoidHom.comp_apply, ← map_pow, e, map_one]
  refine ⟨isOpen_ker_pull ha hφ, fun x => pull_rat ha φ x, fun y => ?_, hQ, ?_, fun PP hPP => isResAt_resOf ?_⟩
  ·
    refine (pull_eq_of_chars a hφ (y := 1) fun f => ?_).trans (map_one _)
    obtain ⟨h1, h2⟩ := hr f
    obtain ⟨c, χ, hc, hχ, hcr⟩ := exists_chrEq_pull ha h1 hM h2
    rw [map_one]
    refine Units.ext ((hcr _).symm.trans ?_)
    rw [real_C D N X a.art ha.artin _ _ hM h2 (hanti' f) c χ hc hχ y]
    simp
  ·
    intro x h1 h2 h3 h4
    refine (pull_eq_of_chars a hφ (y := 1) fun f => ?_).trans (map_one _)
    obtain ⟨o1, o2⟩ := hr f
    obtain ⟨c, χ, hc, hχ, hcr⟩ := exists_chrEq_pull ha o1 hM o2
    rw [map_one]
    refine Units.ext ((hcr _).symm.trans ?_)
    rw [GlobalTheory.T.heckeChar_unramified_outside_split_set_of_tame D N a.art ha.artin _ M hM o2 c χ hc hχ Q hQ (htame f χ hχ) (fun v hv hc' B hB σ hσ => by
      rw [MonoidHom.comp_apply, show φ.rangeRestrict σ = 1 from Subtype.ext (hunr v hv hc' B hB σ hσ), map_one]) x h1 h2 h3 h4]
    simp
  ·
    have hPP := hQ.isIdemAt hPP
    have same : ∀ (x x' : (AE D)ˣ) (u : (kP PP)ˣ), (1 - idemAt PP) * (x : AE D) = 1 - idemAt PP →
        (1 - idemAt PP) * (x' : AE D) = 1 - idemAt PP →
        ∀ (hi : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
          (hi' : toEAf D (x' : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E),
        resS D.host.F PP ⟨_, hi⟩ = u → resS D.host.F PP ⟨_, hi'⟩ = u → a.pull φ x = a.pull φ x' := by
      intro x x' u hx hx' hi hi' hu hu'
      refine pull_eq_of_chars a hφ fun f => ?_
      obtain ⟨o1, o2⟩ := hr f
      obtain ⟨c, χ, hc, hχ, hcr⟩ := exists_chrEq_pull ha o1 hM o2
      have ht : χ.TameAt PP := htame f χ hχ PP ‹_› PP (Or.inl rfl)
      obtain ⟨ρ, hρ⟩ := GlobalTheory.exists_isRes_of_tameAt D χ PP ht
      have e : ∀ z : (AE D)ˣ, (1 - idemAt PP) * (z : AE D) = 1 - idemAt PP →
          ∀ (hz : toEAf D (z : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E),
          resS D.host.F PP ⟨_, hz⟩ = u → a.pull (f.comp φ.rangeRestrict) z = ρ u := fun z hz hzi hzu =>
        Units.ext ((hcr z).symm.trans (GlobalTheory.ConjTwist.eq_res_of_chrEq hc hPP ht hρ z hz hzi u hzu))
      rw [e x hx hi hu, e x' hx' hi' hu']
    have hlift := fun u => GlobalTheory.ConjTwist.exists_isLocUnit hPP u
    choose xs hxs using hlift
    have hmul : ∀ u v, a.pull φ (xs (u * v)) = a.pull φ (xs u * xs v) := fun u v => by
      obtain ⟨hi, hu⟩ := (hxs (u * v)).res
      obtain ⟨hi1, hu1⟩ := (hxs u).res
      obtain ⟨hi2, hu2⟩ := (hxs v).res
      have hi3 : toEAf D ((xs u * xs v : (AE D)ˣ) : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
        rw [Units.val_mul, map_mul]
        exact mul_mem hi1 hi2
      refine same _ _ (u * v) (hxs (u * v)).off ?_ hi hi3 hu ?_
      · rw [Units.val_mul, ← mul_assoc, (hxs u).off, (hxs v).off]
      · have : (⟨_, hi3⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨_, hi1⟩ * ⟨_, hi2⟩ :=
          Subtype.ext (by
            change toEAf D ((xs u * xs v : (AE D)ˣ) : AE D) = toEAf D (xs u : AE D) * toEAf D (xs v : AE D)
            rw [Units.val_mul, map_mul])
        rw [this, map_mul, hu1, hu2, Units.val_mul]
    refine ⟨MonoidHom.mk' (fun u => a.pull φ (xs u)) (fun u v => ?_), ?_⟩
    · show a.pull φ (xs (u * v)) = a.pull φ (xs u) * a.pull φ (xs v)
      rw [hmul, map_mul]
    · intro x hx hi u hu
      show a.pull φ x = a.pull φ (xs u)
      obtain ⟨hi', hu'⟩ := (hxs u).res
      exact same x (xs u) u hx (hxs u).off hi hi' hu hu'

end GlobalTheory.TwistPullTame
