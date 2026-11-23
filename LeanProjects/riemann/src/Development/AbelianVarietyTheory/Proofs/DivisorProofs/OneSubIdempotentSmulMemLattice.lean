import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne

namespace GlobalTheory.OffIdem

open NumberField in

theorem exists_common {O R ι : Type} [CommRing O] [IsDomain O] [CommRing R] (f : O →+* R) (I : ι → Ideal O) (ε : R)
    (hε : ε * ε = ε) (P : Finset ι) (h : ∀ i ∈ P, ∃ x ∈ I i, x ≠ 0 ∧ ∃ s, ε = s * f x) :
    ∃ x, x ≠ 0 ∧ (∀ i ∈ P, x ∈ I i) ∧ ∃ s, ε = s * f x := by
  classical
  induction P using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp, ε, by simp⟩
  | insert a P _ ih =>
    obtain ⟨x, hx0, hx, s, hs⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    obtain ⟨y, hy, hy0, t, ht⟩ := h a (Finset.mem_insert_self _ _)
    refine ⟨x * y, mul_ne_zero hx0 hy0, fun i hi => ?_, s * t, ?_⟩
    · rcases Finset.mem_insert.1 hi with rfl | hi
      · exact Ideal.mul_mem_left _ _ hy
      · exact Ideal.mul_mem_right _ _ (hx i hi)
    · rw [map_mul, mul_mul_mul_comm, ← hs, ← ht, hε]

end GlobalTheory.OffIdem

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OffIdem

theorem idemSum_mul_idemAt {D : D7} {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (h : IsIdemSum e P)
    {PP : Formalism.L2.DIV.Pl D.host.E} (hPP : PP ∈ P) : ∃ a : AE D, Formalism.L2.NTheta.IsIdemAt a PP ∧ a * e = a := by
  obtain ⟨⟨es, hes, rfl⟩, hc⟩ := h
  have h1 : ∀ i ∈ P, es i * es i = es i := fun i hi => (hes i hi).1.1
  have hcross : ∀ i ∈ P, ∀ j ∈ P, es i * cA D (es j) = 0 :=
    GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es P h1 hc
  refine ⟨es PP, hes PP hPP, ?_⟩
  rw [Finset.mul_sum, Finset.sum_eq_single PP (fun j hj hji =>
    GlobalTheory.PlaceDatum.idemAt_mul (hes PP hPP) (hes j hj) (hcross PP hPP j hj) (hcross j hj PP hPP) hji)
    (fun h => absurd hPP h), h1 PP hPP]

theorem exists_eq_mul_of_mul_eq_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : Finset (Formalism.L2.DIV.Pl E)) (ε : Formalism.L2.Herm.intAf F E) (hε : ε * ε = ε)
    (h : ∀ PP ∈ P, ∃ a : Formalism.L2.Herm.intAf F E, Formalism.L2.DIV.resS F PP a = 1 ∧ a * ε = 0) :
    ∃ x : 𝓞 E, x ≠ 0 ∧ (∀ PP ∈ P, x ∈ PP.asIdeal) ∧ ∃ s, ε = s * Formalism.L2.DIV.oToS F E x :=
  exists_common (Formalism.L2.DIV.oToS F E) (fun PP : Formalism.L2.DIV.Pl E => PP.asIdeal) _ hε P fun PP hPP => by
    refine GlobalTheory.IdemRes.exists_eq_mul_of_resS_ne_one PP _ hε fun hne => ?_
    have := PP.isPrime
    obtain ⟨a, ha1, h0⟩ := h PP hPP
    have h3 := congrArg (Formalism.L2.DIV.resS F PP) h0
    rw [RingHom.map_mul, ha1, hne, RingHom.map_zero, one_mul] at h3
    exact one_ne_zero h3

theorem one_sub_mul_self {R : Type} [CommRing R] {e : R} (h : e * e = e) : (1 - e) * (1 - e) = 1 - e := by
  linear_combination h

theorem mul_one_sub {R : Type} [CommRing R] {a e : R} (h : a * e = a) : a * (1 - e) = 0 := by
  linear_combination -h

theorem mul_ringHom_mul_ringHom_inv_cancel {K R : Type} [Field K] [CommRing R] (f : K →+* R) (s : R) {y : K} (hy : y ≠ 0) :
    s * f y * f y⁻¹ = s := by
  rw [mul_assoc, ← map_mul, mul_inv_cancel₀ hy, map_one, mul_one]

theorem exists_den {D : D7} {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P) :
    ∃ y : 𝓞 D.host.E, (y : D.host.E) ≠ 0 ∧ (∀ PP ∈ P, y ∈ PP.asIdeal) ∧
      finPart D ((1 - e) * incA D ((y : D.host.E)⁻¹)) ∈ intAE D := by
  have h1 : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have h2 : (1 - e) * (1 - e) = 1 - e := one_sub_mul_self (R := AE D) h1
  have hint : toEAf D (1 - e) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    GlobalTheory.IdemRes.toEAf_mem_of_finPart (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, h2]))
  obtain ⟨y, hy0, hy, s, hs⟩ := exists_eq_mul_of_mul_eq_zero P ⟨toEAf D (1 - e), hint⟩
    (Subtype.ext (by change toEAf D (1 - e) * toEAf D (1 - e) = toEAf D (1 - e); rw [← RingHom.map_mul, h2]))
    fun PP hPP => by
      obtain ⟨a, ha, hae⟩ := idemSum_mul_idemAt he hPP
      obtain ⟨hai, ha1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D a PP ha
      refine ⟨_, ha1, Subtype.ext ?_⟩
      change toEAf D a * toEAf D (1 - e) = 0
      rw [← RingHom.map_mul, mul_one_sub (R := AE D) hae, RingHom.map_zero]
  have hs' : toEAf D (1 - e) = (s : Formalism.IndefR.Datum.EAf D) * eToEAf D (y : D.host.E) := congrArg Subtype.val hs
  have hy0' : (y : D.host.E) ≠ 0 := fun h => hy0 (RingOfIntegers.coe_eq_zero_iff.1 h)
  have h4 : toEAf D (incA D ((y : D.host.E)⁻¹)) = eToEAf D ((y : D.host.E)⁻¹) := rfl
  refine ⟨y, hy0', hy, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_⟩
  rw [RingHom.map_mul, h4, hs', mul_ringHom_mul_ringHom_inv_cancel (eToEAf D) _ hy0']
  exact s.2

theorem one_sub_smul_mem_latO : ∀ (D : D7) (V W : HSp D) (LV : Set (Fin V.rank → D.host.E)) (LW : Set (Fin W.rank → D.host.E)) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → ∀ x : WO V W, (∀ s : 𝓞 D.host.E, (∀ PP ∈ P, s ∈ PP.asIdeal) → incA D (s : D.host.E) • x ∈ (latO V W LV LW fun _ => True)) → (1 - e) • x ∈ (latO V W LV LW fun _ => True) := by
  intro D V W LV LW e P he x hx
  obtain ⟨y, hy0, hy, hw⟩ := exists_den he
  have h5 := GlobalTheory.LatticeStable.smul_mem_latO D V W LV LW _ _ hw _ (hx y hy)
  rwa [smul_smul, mul_assoc, ← RingHom.map_mul, inv_mul_cancel₀ hy0, RingHom.map_one, mul_one] at h5

end GlobalTheory.OffIdem
