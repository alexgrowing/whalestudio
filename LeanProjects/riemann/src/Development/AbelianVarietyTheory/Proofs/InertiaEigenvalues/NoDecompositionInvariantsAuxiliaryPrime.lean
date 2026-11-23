import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameInertiaElementActsByScalar
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal.ScalarInvariants

theorem eq_zero_of_scalar {O : Type} [CommRing O] [IsDomain O] {n : ℕ} (d : O) (hd : d ≠ 1)
    (x : Fin n → FractionRing O)
    (h : ((d • (1 : Matrix (Fin n) (Fin n) O)).map (algebraMap O (FractionRing O))).mulVec x = x) : x = 0 := by
  have e : (d • (1 : Matrix (Fin n) (Fin n) O)).map (algebraMap O (FractionRing O)) =
      algebraMap O (FractionRing O) d • (1 : Matrix (Fin n) (Fin n) (FractionRing O)) := by
    ext a b
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  rw [e, Matrix.smul_mulVec, Matrix.one_mulVec] at h
  have h1 : algebraMap O (FractionRing O) d - 1 ≠ 0 := fun h0 =>
    hd (IsFractionRing.injective O (FractionRing O) (by rw [map_one]; exact sub_eq_zero.1 h0))
  have h2 : (algebraMap O (FractionRing O) d - 1) • x = 0 := by rw [sub_smul, h, one_smul, sub_self]
  exact (smul_eq_zero.1 h2).resolve_left h1

theorem inv_unit_smul_one {O : Type} [CommRing O] {n : ℕ} (d : Oˣ) :
    ((d : O) • (1 : Matrix (Fin n) (Fin n) O))⁻¹ = ((d⁻¹ : Oˣ) : O) • (1 : Matrix (Fin n) (Fin n) O) := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, Units.inv_mul, one_smul]

theorem noInv_pD : ∀ (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i), UnrRho i s → ∀ v ∈ D.ntw.pD i,
    NoInv i (Tmat i s) v ∧ NoInv i (Tdual i s) v := by
  intro D i s h v hv
  have hlp : (D.ntw.l i).Prime := (D.ntw.lPrime i).out
  have hv' : v ∈ placesOver D.host.E (if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde) := by
    rw [← D.ntw.pD_eq i]; exact hv
  have hp : (if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde).Prime := by
    split_ifs
    exacts [D.host.pde'_prime, D.host.pde_prime]
  have hl : v ∉ placesOver D.host.E (D.ntw.l i) := by
    refine GlobalTheory.TwSys.TameScalar.not_mem_placesOver hp hlp ?_ hv'
    split_ifs with hh
    · rw [hh]; exact D.host.pde_ne.symm
    · exact fun e => hh e.symm
  have hg : ∀ k, v ∉ placesOver D.host.E (D.host.g k) := fun k => by
    refine GlobalTheory.TwSys.TameScalar.not_mem_placesOver hp (D.host.g_prime k) ?_ hv'
    split_ifs
    exacts [(D.host.pde_ne_g k).2, (D.host.pde_ne_g k).1]
  have key : ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∃ z ∈ Dec (F := D.host.E) A,
      ∃ d : (D.ntw.O0 i)ˣ, d ≠ 1 ∧
        Tmat i s z = (d : D.ntw.O0 i) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)) ∧ eps0 D.ntw i z = 1 := by
    intro A hA
    have h15 := D.ntw.delta_15 i v hv A hA
    obtain ⟨z, hzA, hz⟩ : ∃ z ∈ Ine (F := D.host.E) A, D.ntw.delta i z ≠ 1 := by
      by_contra hc
      push Not at hc
      have hb : (Ine (F := D.host.E) A).map (D.ntw.delta i) = ⊥ :=
        (Subgroup.map_eq_bot_iff _).2 fun z hz => hc z hz
      rw [hb, Subgroup.card_bot] at h15
      exact absurd h15 (by norm_num)
    have h1 : D.ntw.rhoS i s z = 1 := h v hl hg A hA z hzA
    have h2 : chiS i s z = if D.ntw.side i s then D.ntw.delta i z else (D.ntw.delta i z)⁻¹ :=
      D.ntw.twistCharacterFamily_at_auxiliaryPlaces i _ _ v hv A hA z hzA
    refine ⟨z, Ine_le_Dec A hzA, (chiS i s z)⁻¹, ?_, ?_, ?_⟩
    · rw [h2]
      split_ifs
      · exact inv_ne_one.2 hz
      · rw [inv_inv]; exact hz
    · rw [Tmat, h1, Units.val_one]
    · have h4 : cycZ D.host.E D.nd.Om (D.ntw.l i) z = 1 := by
        refine Units.ext (PadicInt.ext_of_toZModPow.1 fun n => ?_)
        rw [ReciprocityTheory.Gal.cycZ_toZModPow_eq hl hA (q := 1) (fun x hx => by simpa using hzA.2 x hx) n]
        simp
      simp [eps0, h4]
  refine ⟨fun A hA x hx => ?_, fun A hA x hx => ?_⟩
  · obtain ⟨z, hz, d, hd, hT, -⟩ := key A hA
    have e := hx z hz
    rw [hT] at e
    exact eq_zero_of_scalar _ (fun h0 => hd (Units.ext h0)) x e
  · obtain ⟨z, hz, d, hd, hT, he⟩ := key A hA
    have e := hx z hz
    rw [Tdual, hT, he, inv_unit_smul_one, Units.val_one, one_smul, Matrix.transpose_smul, Matrix.transpose_one] at e
    exact eq_zero_of_scalar _ (fun h0 => inv_ne_one.2 hd (Units.ext h0)) x e

end GlobalTheory.TripleGal.ScalarInvariants
