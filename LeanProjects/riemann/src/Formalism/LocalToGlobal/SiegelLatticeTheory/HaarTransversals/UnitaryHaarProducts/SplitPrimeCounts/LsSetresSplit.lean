import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
import ReciprocityTheory.ReductiveGroups.PlaceCounting.RaySplA

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas

namespace Formalism.L2.SG.SplitPrimeNormLemmas.SplitG

theorem ef_one_of_split (E L : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L] (p : ℕ)
    (hall : ∀ W : HeightOneSpectrum (𝓞 L), ((p : ℕ) : 𝓞 L) ∈ W.asIdeal →
      W.asIdeal.ramificationIdx ℤ = 1 ∧ W.asIdeal.inertiaDeg ℤ = 1)
    (Q : Ideal (𝓞 E)) (hQp : Q.IsPrime) (hQb : Q ≠ ⊥) (hpQ' : ((p : ℕ) : 𝓞 E) ∈ Q) :
    Q.ramificationIdx ℤ = 1 ∧ Q.inertiaDeg ℤ = 1 := by
  have hinjEL : Function.Injective (algebraMap (𝓞 E) (𝓞 L)) :=
    FaithfulSMul.algebraMap_injective (𝓞 E) (𝓞 L)
  obtain ⟨W, -, hWp, hWQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 L) Q ⊥
    (by rw [Ideal.comap_bot_of_injective _ hinjEL]; exact bot_le)
  have hWb : W ≠ ⊥ := by
    intro h0; apply hQb; rw [← hWQ, h0, Ideal.comap_bot_of_injective _ hinjEL]
  have hpW : ((p : ℕ) : 𝓞 L) ∈ W := by
    have : algebraMap (𝓞 E) (𝓞 L) ((p : ℕ) : 𝓞 E) ∈ W := by
      rw [← Ideal.mem_comap, hWQ]; exact hpQ'
    simpa using this
  obtain ⟨h1, h2⟩ := hall ⟨W, hWp, hWb⟩ hpW
  have : W.LiesOver Q := ⟨hWQ.symm⟩
  have h1' : W.ramificationIdx ℤ = 1 := h1
  have h2' : W.inertiaDeg ℤ = 1 := h2
  rw [Ideal.ramificationIdx_tower (R := ℤ) Q W] at h1'
  rw [Ideal.inertiaDeg_tower (R := ℤ) Q W] at h2'
  exact ⟨(mul_eq_one.mp h1').1, (mul_eq_one.mp h2').1⟩

theorem card_over_of_split (F E L : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Field L]
    [NumberField L] [Algebra F E] [Algebra E L] (p : ℕ) (hp : p.Prime)
    (hall : ∀ W : HeightOneSpectrum (𝓞 L), ((p : ℕ) : 𝓞 L) ∈ W.asIdeal →
      W.asIdeal.ramificationIdx ℤ = 1 ∧ W.asIdeal.inertiaDeg ℤ = 1)
    (v : HeightOneSpectrum (𝓞 F)) (hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal) :
    Nat.card {w : HeightOneSpectrum (𝓞 E) // w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal} =
      Module.finrank F E := by
  classical
  set P : Ideal (𝓞 F) := v.asIdeal with hP
  have : P.IsPrime := v.isPrime
  have : Finite (P.primesOver (𝓞 E)) := (IsDedekindDomain.primesOver_finite P (𝓞 E)).to_subtype
  let _ : Fintype (P.primesOver (𝓞 E)) := Fintype.ofFinite _
  have hpQ : ∀ Q : P.primesOver (𝓞 E), ((p : ℕ) : 𝓞 E) ∈ Q.1 := by
    intro Q
    have h1 : ((p : ℕ) : 𝓞 F) ∈ Q.1.under (𝓞 F) := by rw [← Q.2.2.over]; exact hv
    rw [Ideal.under_def, Ideal.mem_comap] at h1
    simpa using h1
  have hne : ∀ Q : P.primesOver (𝓞 E), Q.1 ≠ ⊥ := by
    intro Q hb
    have := hpQ Q
    rw [hb, Ideal.mem_bot] at this
    exact hp.ne_zero (by exact_mod_cast this)
  let e : {w : HeightOneSpectrum (𝓞 E) // w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal}
      ≃ P.primesOver (𝓞 E) :=
    { toFun := fun w => ⟨w.1.asIdeal, w.1.isPrime, ⟨w.2.symm⟩⟩
      invFun := fun Q => ⟨⟨Q.1, Q.2.1, hne Q⟩, Q.2.2.over.symm⟩
      left_inv := fun w => rfl
      right_inv := fun Q => rfl }
  have hE := ef_one_of_split E L p hall
  have hterm : ∀ Q : P.primesOver (𝓞 E),
      Q.1.ramificationIdx (𝓞 F) * Q.1.inertiaDeg (𝓞 F) = 1 := by
    intro Q
    have := Q.2.1
    have := Q.2.2
    obtain ⟨h1, h2⟩ := hE Q.1 Q.2.1 (hne Q) (hpQ Q)
    have h1' : Q.1.ramificationIdx ℤ = 1 := h1
    have h2' : Q.1.inertiaDeg ℤ = 1 := h2
    rw [Ideal.ramificationIdx_tower (R := ℤ) P Q.1] at h1'
    rw [Ideal.inertiaDeg_tower (R := ℤ) P Q.1] at h2'
    rw [(mul_eq_one.mp h1').2, (mul_eq_one.mp h2').2, mul_one]
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  calc Fintype.card (P.primesOver (𝓞 E))
      = ∑ Q : P.primesOver (𝓞 E), Q.1.ramificationIdx (𝓞 F) * Q.1.inertiaDeg (𝓞 F) := by
        simp [hterm]
    _ = Module.finrank (𝓞 F) (𝓞 E) := Ideal.sum_ramification_inertia_eq_finrank P (𝓞 E)
    _ = Module.finrank F E := (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E).symm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem splitAtG_holds (D : D7) : ∀ (A : UnitaryGroupInstance D) (v : HeightOneSpectrum (𝓞 A.I.F)),
    ((gD D : ℕ) : 𝓞 A.I.F) ∈ v.asIdeal →
    Nat.card {w : HeightOneSpectrum (𝓞 A.I.E) //
      w.asIdeal.comap (algebraMap (𝓞 A.I.F) (𝓞 A.I.E)) = v.asIdeal} = 2 := by
  intro A v hv
  have hv' : ((D.host.g 0 : ℕ) : 𝓞 A.I.F) * ((D.host.g 1 : ℕ) : 𝓞 A.I.F) ∈ v.asIdeal := by
    rw [← Nat.cast_mul]; exact hv
  let _ : Algebra A.I.E D.host.E := A.ιE.toRingHom.toAlgebra
  have key : ∀ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 A.I.F) ∈ v.asIdeal →
      Nat.card {w : HeightOneSpectrum (𝓞 A.I.E) //
        w.asIdeal.comap (algebraMap (𝓞 A.I.F) (𝓞 A.I.E)) = v.asIdeal} = 2 := by
    intro i hi
    rw [card_over_of_split A.I.F A.I.E D.host.E (D.host.g i) (D.host.g_prime i)
      ((ReciprocityTheory.ChartRestriction.N2.ncard_places_eq_finrank_iff D.host.E _ (D.host.g_prime i)).mp (D.nd.g_split i)) v hi]
    exact A.I.cm.deg2
  rcases v.isPrime.mem_or_mem hv' with h0 | h1
  · exact key 0 h0
  · exact key 1 h1

end Formalism.L2.SG.SplitPrimeNormLemmas.SplitG
