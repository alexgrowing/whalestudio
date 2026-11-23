import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussGLZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdVal
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompletedLatticeIntegralityFacts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDecompChainSpaceDefiniteAddNormalFrame
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharacterValueAtConjugatePlacePowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixesUntwistedLiftDataConjugatePrimeValueSqrtNorStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.FlatConst

theorem one_add_sum_eq_prod {R ι : Type} [CommRing R] [DecidableEq ι] (s : Finset ι) (f a : ι → R)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i * f j = 0) :
    1 + ∑ i ∈ s, f i * (a i - 1) = ∏ i ∈ s, (1 + f i * (a i - 1)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj,
      ← ih fun k hk l hl hkl => h k (Finset.mem_insert_of_mem hk) l (Finset.mem_insert_of_mem hl) hkl]
    have h0 : f j * (a j - 1) * ∑ k ∈ s, f k * (a k - 1) = 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_eq_zero fun k hk => ?_
      have hne : j ≠ k := fun e => hj (e ▸ hk)
      have := h j (Finset.mem_insert_self j s) k (Finset.mem_insert_of_mem hk) hne
      calc f j * (a j - 1) * (f k * (a k - 1)) = (f j * f k) * ((a j - 1) * (a k - 1)) := by ring
        _ = 0 := by rw [this, zero_mul]
    linear_combination (-1 : R) * h0

theorem chr_inv_val {D : D7} (c : (AE D)ˣ →* Circle) (x : (AE D)ˣ) : ((c x⁻¹ : Circle) : ℂ) = ((c x : Circle) : ℂ)⁻¹ := by
  rw [map_inv, Circle.coe_inv]

theorem chrW_val {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t' : T0) (x : (AE D)ˣ) :
    (((Lift.chrTh (R.toLevCh.mu t') R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ) =
      ((R.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) * ((R.xi t' x : Circle) : ℂ) * ((R.eta x : Circle) : ℂ)⁻¹ := by
  unfold Lift.chrTh LevCh.mu Lift.tup
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Circle.coe_mul, Circle.coe_inv]

end GlobalTheory.FlatConst

open GlobalTheory.FlatConst in

theorem GlobalTheory.FlatConst.flat_const : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T0) (es : Pl D.host.E → AE D) (ϖ : Pl D.host.E → 𝓞 D.host.E) (n : ℕ) (x : (AE D)ˣ), (∀ PP ∈ R.Q t, Formalism.L2.NTheta.IsIdemAt (es PP) PP) → (∑ PP ∈ R.Q t, es PP) * cA D (∑ PP ∈ R.Q t, es PP) = 0 → (∀ PP ∈ R.Q t, ϖ PP ∈ PP.asIdeal ∧ ϖ PP ∉ PP.asIdeal ^ 2) → (x : AE D) = 1 + ∑ PP ∈ R.Q t, cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) ^ n - 1) → ∃ b : ℂ, (∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → τ (b * ∏ PP ∈ R.Q t, (((Real.sqrt (Ideal.absNorm PP.asIdeal : ℝ) : ℝ) : ℂ)⁻¹) ^ n) = b * ∏ PP ∈ R.Q t, (((Real.sqrt (Ideal.absNorm PP.asIdeal : ℝ) : ℝ) : ℂ)⁻¹) ^ n) ∧ (∀ t' : T0, (((Lift.chrTh (R.toLevCh.mu t') R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ)⁻¹ = b * ((R.xi t' x⁻¹ : Circle) : ℂ)) ∧ (∀ (t' : T0) (S : Finset (Pl D.host.E)), S ⊆ R.Q t' → ∀ u : ∀ PP : Pl D.host.E, (kP PP)ˣ, ∃ s : (AE D)ˣ, ∏ PP ∈ S, ((R.xiR t' PP (u PP) : ℂˣ) : ℂ) = ((R.xi t' s : Circle) : ℂ)) := by
  intro D G _ _ Pl0 T0 A T _ R F hC i t es ϖ n x hes hc hϖ hx
  set Q := R.Q t with hQ

  have hidem : ∀ PP ∈ Q, cA D (es PP) * cA D (es PP) = cA D (es PP) := fun PP hP =>
    Formalism.IndefR.Fin.LevelGroupLemmas.isIdem_cA (hes PP hP).1.1
  have hϖ0 : ∀ PP ∈ Q, star ((ϖ PP : 𝓞 D.host.E) : D.host.E) ≠ 0 := fun PP hP h0 => by
    have : (ϖ PP : D.host.E) = 0 := by rw [← star_star ((ϖ PP : 𝓞 D.host.E) : D.host.E), h0, star_zero]
    exact (hϖ PP hP).2 (by rw [show ϖ PP = 0 from RingOfIntegers.ext this]; exact zero_mem _)
  let y : Q → (AE D)ˣ := fun P =>
    Formalism.L2.JoinChr.locU (hidem P.1 P.2) ((Units.mk0 (star ((ϖ P.1 : 𝓞 D.host.E) : D.host.E)) (hϖ0 P.1 P.2)) ^ n)
  have hyv : ∀ P : Q, ((y P : (AE D)ˣ) : AE D) = 1 + cA D (es P.1) * (incA D (star ((ϖ P.1 : 𝓞 D.host.E) : D.host.E)) ^ n - 1) := by
    intro P
    show Formalism.L2.JoinChr.locE D _ _ = _
    unfold Formalism.L2.JoinChr.locE
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, map_pow]
  have horth : ∀ P ∈ Q.attach, ∀ P' ∈ Q.attach, P ≠ P' → cA D (es P.1) * cA D (es P'.1) = 0 := by
    intro P _ P' _ hne
    rw [← map_mul, Formalism.IndefR.Fin.LevelGroupLemmas.idemSum_orth hes rfl hc P.2 P'.2 (fun e => hne (Subtype.ext e)), map_zero]
  have hxy : x = ∏ P ∈ Q.attach, y P := by
    apply Units.ext
    rw [Units.coe_prod, hx]
    simp only [hyv]
    rw [← Finset.sum_attach Q (fun PP => cA D (es PP) * (incA D (star ((ϖ PP : 𝓞 D.host.E) : D.host.E)) ^ n - 1))]
    exact one_add_sum_eq_prod Q.attach (fun P => cA D (es P.1)) (fun P => incA D (star ((ϖ P.1 : 𝓞 D.host.E) : D.host.E)) ^ n) horth

  have hg : ∀ PP ∈ Q, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP hP =>
    GlobalTheory.StdFrames.g_not_mem (hC.lev.Q_pl t) hP
  have hgc : ∀ PP ∈ Q, ∀ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ (Formalism.L2.DIV.conjPl PP).asIdeal := by
    intro PP hP k hk
    have hk' : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
      have : Formalism.L2.DIV.starOHom ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := hk
      rwa [map_natCast] at this
    apply hg PP hP
    rw [Nat.cast_mul]
    fin_cases k
    · exact Ideal.mul_mem_right _ _ hk'
    · exact Ideal.mul_mem_left _ _ hk'
  have unrM : ∀ PP ∈ Q, (R.C.mu0 i).UnrAt (Formalism.L2.DIV.conjPl PP) := fun PP hP =>
    (R.C.isMu0 i).unr _ fun k => hgc PP hP k
  have unrE : ∀ PP ∈ Q, R.C.eta.UnrAt (Formalism.L2.DIV.conjPl PP) := fun PP _ => R.C.isEta.unr _

  have hvM : ((R.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = ∏ PP ∈ Q, (((R.C.mu0 i).val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) ^ n := by
    have := map_prod (Circle.coeHom.comp (R.mu0 ((i : ℕ) + 1))) y Q.attach
    rw [← hxy] at this
    show (Circle.coeHom.comp (R.mu0 ((i : ℕ) + 1))) x = _
    rw [this, ← Finset.prod_attach Q]
    refine Finset.prod_congr rfl fun P _ => ?_
    exact GlobalTheory.T.heckeCharacter_value_at_conjugatePlace_pow D P.1 (es P.1) (ϖ P.1) _ _ n (y P) (hes P.1 P.2) (hϖ P.1 P.2).1 (hϖ P.1 P.2).2 (hC.lev.mu0 i)
      (unrM P.1 P.2) (hyv P)
  have hvE : ((R.eta x : Circle) : ℂ) = ∏ PP ∈ Q, ((R.C.eta.val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) ^ n := by
    have := map_prod (Circle.coeHom.comp R.eta) y Q.attach
    rw [← hxy] at this
    show (Circle.coeHom.comp R.eta) x = _
    rw [this, ← Finset.prod_attach Q]
    refine Finset.prod_congr rfl fun P _ => ?_
    exact GlobalTheory.T.heckeCharacter_value_at_conjugatePlace_pow D P.1 (es P.1) (ϖ P.1) _ _ n (y P) (hes P.1 P.2) (hϖ P.1 P.2).1 (hϖ P.1 P.2).2 hC.lev.eta
      (unrE P.1 P.2) (hyv P)
  set sq : Pl D.host.E → ℂ := fun PP => ((Real.sqrt (Ideal.absNorm PP.asIdeal : ℝ) : ℝ) : ℂ) with hsq
  set v : Pl D.host.E → ℂ := fun PP => (((R.C.mu0 i * R.C.eta⁻¹).val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) with hv
  refine ⟨(((R.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) * ((R.eta x : Circle) : ℂ)⁻¹)⁻¹, ?_, ?_, ?_⟩
  · intro τ hτ
    have key : (((R.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) * ((R.eta x : Circle) : ℂ)⁻¹)⁻¹ * ∏ PP ∈ Q, (sq PP)⁻¹ ^ n =
        ∏ PP ∈ Q, ((v PP * sq PP)⁻¹) ^ n := by
      rw [hvM, hvE]
      simp only [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun PP _ => ?_
      simp only [hv, Formalism.L2.Host.HChar.val_mul, Formalism.L2.Host.HChar.val_inv, Units.val_mul, Units.val_inv_eq_inv_val]
      ring
    show τ (_ * ∏ PP ∈ Q, (sq PP)⁻¹ ^ n) = _ * ∏ PP ∈ Q, (sq PP)⁻¹ ^ n
    rw [key, map_prod]
    refine Finset.prod_congr rfl fun PP hP => ?_
    rw [map_pow, map_inv₀]
    congr 2
    exact GlobalTheory.T.fixesUntwistedLiftData_conjugatePrime_value_sqrtNorm T R i τ PP hτ (hg PP hP)
  · intro t'
    have h1 := chrW_val R i t' x
    have h2 := chr_inv_val (R.xi t') x
    simp only [h1, h2]
    ring
  · intro t' S hS u
    exact GlobalTheory.FlatConj.prod_val (R.xi t') S (fun PP => ((R.xiR t' PP (u PP) : ℂˣ) : ℂ))
      fun PP hP => GlobalTheory.FlatConj.xiR_val hC t' PP (hS hP) (u PP)
