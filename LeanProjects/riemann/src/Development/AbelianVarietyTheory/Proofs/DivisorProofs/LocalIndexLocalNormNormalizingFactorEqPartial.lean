import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainTwistPlacesSplitUnramifiedQuotients
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistEulerFactorsRestoreNormalizingFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexBlockLevel

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

noncomputable section

namespace GlobalTheory.NormRatio

theorem conj_smul_le {D : D7} {I J : Ideal (𝓞 D.host.E)} (h : I ≤ J) : D.host.conj • I ≤ D.host.conj • J :=
  EigUnit.conj_smul_mono D h

theorem exists_conj_place {D : D7} (w : HeightOneSpectrum (𝓞 D.host.E)) :
    ∃ w' : HeightOneSpectrum (𝓞 D.host.E), w'.asIdeal = D.host.conj • w.asIdeal ∧
      w'.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) ∧
      ∀ w'' : HeightOneSpectrum (𝓞 D.host.E), w''.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) → w'' = w ∨ w'' = w' := by
  have hcc : ∀ x : D.host.E, GlobalTheory.Member.cF D x = D.host.conj x := fun x => Formalism.BasicNotions.bridge_star_holds D.R D.host x
  have hp := w.isPrime
  have hpr : (D.host.conj • w.asIdeal).IsPrime := inferInstance
  have hnb : D.host.conj • w.asIdeal ≠ ⊥ := by
    intro h0
    apply w.ne_bot
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using this
  let w' : HeightOneSpectrum (𝓞 D.host.E) := ⟨D.host.conj • w.asIdeal, hpr, hnb⟩
  have hc : GlobalTheory.Mem.Chr.ConjPl (GlobalTheory.Member.cF D).toRingEquiv w w' := by
    rw [GlobalTheory.Mem.Chr.conjPl_iff_mem]
    intro x y hxy
    have hy : y = D.host.conj • x := RingOfIntegers.ext (by rw [hxy]; exact hcc _)
    rw [hy]
    exact Ideal.smul_mem_pointwise_smul_iff.symm
  have hiff := GlobalTheory.Mem.Chr.under_eq_iff_conjPl (GlobalTheory.Member.cF D) D.sp.cm.deg2 (GlobalTheory.IdeleNinety.conj_ne_one D) w
  refine ⟨w', rfl, (hiff w').2 (Or.inr hc), fun w'' h => ?_⟩
  rcases (hiff w'').1 h with h1 | h1
  · exact Or.inl h1
  · exact Or.inr ((GlobalTheory.Mem.Chr.existsUnique_conjPl _ w).unique h1 hc)

theorem eq_top_of_eq_conj {D : D7} {𝔪 A B : Ideal (𝓞 D.host.E)} (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hA : 𝔪 ≤ A)
    (hB : 𝔪 ≤ B) (h : A = D.host.conj • B) : A = ⊤ :=
  top_le_iff.1 (hcop ▸ sup_le hA (h ▸ conj_smul_le hB))

theorem prod_Ioc_shift {M : Type} [CommMonoid M] (g : ℕ → M) (a a' : ℕ) :
    ∏ n ∈ Finset.Ioc a' (a + a'), g n = ∏ i ∈ Finset.Icc 1 a, g (a' + i) := by
  have e : Finset.Ioc a' (a + a') = (Finset.Icc 1 a).image (a' + ·) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_image, Finset.mem_Icc]
    constructor
    · intro h; exact ⟨n - a', by omega, by omega⟩
    · rintro ⟨x, ⟨h1, h2⟩, rfl⟩; omega
  rw [e, Finset.prod_image fun x _ y _ h => by simpa using h]

theorem locIdx_mul_locNorm_mul_dSfun : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (Sf : Finset (FinPl D)), GoodMod D 𝔪 Sf →
    ∀ a a' : ℕ, 1 ≤ a' →
    (locIdx D 𝔪 a a' : ℂ) * (locNorm D 𝔪 a a' : ℂ) * GlobalTheory.LFun.dSfun D.host.E (∅ : Set (FinPl D)) a (a + a') ((a' : ℂ) / 2) =
      GlobalTheory.LFun.dSfun D.host.E (Sf : Set (FinPl D)) a (a + a') ((a' : ℂ) / 2) := by
  intro D 𝔪 Sf hG a a' ha'
  classical
  obtain ⟨hne, hcop, -, hS⟩ := hG
  set s : ℂ := (a' : ℂ) / 2 with hs_def
  have hs : 0 < s.re := by
    have : (1 : ℝ) ≤ a' := by exact_mod_cast ha'
    simp only [hs_def, Complex.div_ofNat_re, Complex.natCast_re]
    linarith
  set f : HeightOneSpectrum (𝓞 D.host.F) → ℂ := fun v => GlobalTheory.LFun.dv D.host.E a (a + a') v s with hf
  have h0 := (hasProd_subtype_iff_mulIndicator (s := {v | v ∉ (∅ : Set (HeightOneSpectrum (𝓞 D.host.F)))}) (f := f)).1
    (GlobalTheory.LFun.hasProd_dv (∅ : Set (HeightOneSpectrum (𝓞 D.host.F))) a (a + a') hs).multipliable.hasProd
  have h1 := (hasProd_subtype_iff_mulIndicator (s := {v | v ∉ (Sf : Set (HeightOneSpectrum (𝓞 D.host.F)))}) (f := f)).1
    (GlobalTheory.LFun.hasProd_dv (Sf : Set (HeightOneSpectrum (𝓞 D.host.F))) a (a + a') hs).multipliable.hasProd
  have h2 := (hasProd_subtype_iff_mulIndicator (s := (Sf : Set (HeightOneSpectrum (𝓞 D.host.F)))) (f := f)).1
    (Finset.hasProd Sf f)
  have hsplitf : Set.mulIndicator {v | v ∉ (∅ : Set (HeightOneSpectrum (𝓞 D.host.F)))} f =
      Set.mulIndicator {v | v ∉ (Sf : Set (HeightOneSpectrum (𝓞 D.host.F)))} f * Set.mulIndicator (Sf : Set _) f := by
    funext v
    simp only [Pi.mul_apply, Set.mulIndicator_apply, Set.mem_setOf_eq, Finset.mem_coe, Set.mem_empty_iff_false]
    by_cases hv : v ∈ Sf <;> simp [hv]
  rw [hsplitf] at h0
  have key : GlobalTheory.LFun.dSfun D.host.E (∅ : Set (HeightOneSpectrum (𝓞 D.host.F))) a (a + a') s =
      GlobalTheory.LFun.dSfun D.host.E (Sf : Set (HeightOneSpectrum (𝓞 D.host.F))) a (a + a') s * ∏ v ∈ Sf, f v :=
    h0.unique (h1.mul h2)
  set P := (normalizedFactors 𝔪).toFinset with hP
  have hw : ∀ I ∈ P, I.IsPrime ∧ I ≠ ⊥ ∧ 𝔪 ≤ I := by
    intro I hI
    obtain ⟨hp, hle⟩ := (Ideal.mem_normalizedFactors_iff hne).1 (Multiset.mem_toFinset.1 hI)
    exact ⟨hp, fun h => hne (le_bot_iff.1 (h ▸ hle)), hle⟩
  let W : P → HeightOneSpectrum (𝓞 D.host.E) := fun x => ⟨x.1, (hw x.1 x.2).1, (hw x.1 x.2).2.1⟩
  have hbij : ∏ v ∈ Sf, f v = ∏ x ∈ P.attach, f ((W x).under (𝓞 D.host.F)) := by
    symm
    refine Finset.prod_bij (fun x _ => (W x).under (𝓞 D.host.F)) (fun x _ => (hS _).2 ⟨W x, (hw x.1 x.2).2.2, rfl⟩)
      (fun x _ y _ hxy => ?_) (fun v hv => ?_) (fun x _ => rfl)
    · obtain ⟨w', hw', -, hall⟩ := exists_conj_place (W x)
      rcases hall (W y) hxy.symm with h | h
      · exact Subtype.ext (congrArg HeightOneSpectrum.asIdeal h).symm
      · have h' : y.1 = D.host.conj • x.1 := (congrArg HeightOneSpectrum.asIdeal h).trans hw'
        exact absurd (eq_top_of_eq_conj hcop (hw y.1 y.2).2.2 (hw x.1 x.2).2.2 h') (hw y.1 y.2).1.ne_top
    · obtain ⟨w, hmw, rfl⟩ := (hS v).1 hv
      have hmem : w.asIdeal ∈ P := Multiset.mem_toFinset.2 ((Ideal.mem_normalizedFactors_iff hne).2 ⟨w.isPrime, hmw⟩)
      exact ⟨⟨w.asIdeal, hmem⟩, Finset.mem_attach _ _, rfl⟩
  have hloc : ∀ x : P, ((blockIdx (Ideal.absNorm x.1 : ℝ) ((normalizedFactors 𝔪).count x.1) a a' : ℝ) : ℂ) *
      ((((Ideal.absNorm x.1 : ℝ) ^ ((normalizedFactors 𝔪).count x.1 * a * a'))⁻¹ * glVol (Ideal.absNorm x.1 : ℝ) a : ℝ) : ℂ) *
      f ((W x).under (𝓞 D.host.F)) = 1 := by
    intro x
    obtain ⟨w', hw', hu, -⟩ := exists_conj_place (W x)
    have hne' : W x ≠ w' := by
      intro h
      have h' : x.1 = D.host.conj • x.1 := (congrArg HeightOneSpectrum.asIdeal h).trans hw'
      exact (hw x.1 x.2).1.ne_top (eq_top_of_eq_conj hcop (hw x.1 x.2).2.2 (hw x.1 x.2).2.2 h')
    have hsp : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) ((W x).under (𝓞 D.host.F)) :=
      ⟨W x, w', hne', rfl, congrArg HeightOneSpectrum.asIdeal hu⟩
    have hN : Ideal.absNorm ((W x).under (𝓞 D.host.F)).asIdeal = Ideal.absNorm x.1 :=
      GlobalTheory.ChainTw.TwPlaces.absNorm_under_of_ne hu.symm hne'
    have hq : (1 : ℝ) < (Ideal.absNorm x.1 : ℝ) := by
      have h1 : Ideal.absNorm x.1 ≠ 1 := fun h => (hw x.1 x.2).1.ne_top (Ideal.absNorm_eq_one_iff.1 h)
      have h2 : Ideal.absNorm x.1 ≠ 0 := fun h => (hw x.1 x.2).2.1 (Ideal.absNorm_eq_zero_iff.1 h)
      exact_mod_cast (by omega : 1 < Ideal.absNorm x.1)
    have hd := GlobalTheory.ChainTw.dv_center_of_isSplit D.sp.cm.deg2 hsp a a'
    have hst := congrArg (fun r : ℝ => (r : ℂ)) (GlobalTheory.StdLoc.stdLoc_product hq ((normalizedFactors 𝔪).count x.1) a a')
    simp only [hf, hs_def, hd, hN, prod_Ioc_shift (fun n => (1 - (((Ideal.absNorm x.1 : ℕ) : ℂ) ^ n)⁻¹)) a a']
    push_cast at hst ⊢
    linear_combination hst
  rw [key]
  have hmain : (locIdx D 𝔪 a a' : ℂ) * (locNorm D 𝔪 a a' : ℂ) * ∏ v ∈ Sf, f v = 1 := by
    rw [hbij, locIdx, locNorm, Complex.ofReal_prod, Complex.ofReal_prod, ← Finset.prod_attach P,
      ← Finset.prod_attach P, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun x _ => hloc x
  linear_combination (GlobalTheory.LFun.dSfun D.host.E (Sf : Set (HeightOneSpectrum (𝓞 D.host.F))) a (a + a') s) * hmain

end GlobalTheory.NormRatio
