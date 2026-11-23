import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAdmissibleIntegralBasisChangeOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

noncomputable section

namespace GlobalTheory.Mem.Col2.IdxFin

open GlobalTheory.Mem.LevFin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem exists_classes {N q : ℕ} (hq : (q : E) ≠ 0) (e : ℕ → ℤ) (j : ℕ) :
    ∃ (ι : Type) (_ : Finite ι) (f : (Sp E N ≃ₗ[E] Sp E N) → ι), ∀ h h' : Sp E N ≃ₗ[E] Sp E N,
      (∀ x ∈ LocE.sclLat P q N e, h⁻¹ x ∈ LocE.sclLat P q N e ∧ ((q : E) ^ j) • h x ∈ LocE.sclLat P q N e) →
      (∀ x ∈ LocE.sclLat P q N e, h'⁻¹ x ∈ LocE.sclLat P q N e ∧ ((q : E) ^ j) • h' x ∈ LocE.sclLat P q N e) →
      f h = f h' → ∀ x ∈ LocE.sclLat P q N e, (q : E)⁻¹ • ((h⁻¹ * h') x - x) ∈ LocE.sclLat P q N e := by
  classical
  have hc : ((q ^ (j + 1) : ℕ) : E) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hq
  have hq' : ((q ^ (j + 1) : ℕ) : 𝓞 E) ≠ 0 := fun h0 => hc (by simpa using congrArg (algebraMap (𝓞 E) E) h0)
  have hfin : Finite (𝓞 E ⧸ Ideal.span {((q ^ (j + 1) : ℕ) : 𝓞 E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa only [Ne, Ideal.span_singleton_eq_bot] using hq')
  have hz : ∀ l : ℕ, (q : E) ^ e l ≠ 0 := fun l => zpow_ne_zero _ hq
  have he : ∀ i : Fin N, (Pi.single i ((q : E) ^ e i.1) : Sp E N) ∈ LocE.sclLat P q N e := by
    intro i
    rw [GlobalTheory.CongLevel.mem_sclLat]
    intro l
    rw [Pi.single_apply]
    split_ifs with hl
    · rw [hl, inv_mul_cancel₀ (hz _)]
      exact GlobalTheory.GO.ChRoot.intAt_one'
    · rw [mul_zero]
      exact GlobalTheory.GO.ChRoot.intAt_zero'
  let m : (Sp E N ≃ₗ[E] Sp E N) → Fin N → Fin N → E :=
    fun h i l => ((q : E) ^ e l.1)⁻¹ * ((q : E) ^ j * h (Pi.single i ((q : E) ^ e i.1)) l)
  have hex : ∀ a : E, ∃ r : 𝓞 E, IntAt P a → IntAt P (((q ^ (j + 1) : ℕ) : E)⁻¹ * (a - algebraMap (𝓞 E) E r)) := by
    intro a
    by_cases ha : IntAt P a
    · obtain ⟨r, hr⟩ := exists_int_congr hc ha
      exact ⟨r, fun _ => hr⟩
    · exact ⟨0, fun h => (ha h).elim⟩
  choose r hr using hex
  refine ⟨Fin N → Fin N → 𝓞 E ⧸ Ideal.span {((q ^ (j + 1) : ℕ) : 𝓞 E)}, inferInstance,
    fun h i l => Ideal.Quotient.mk _ (r (m h i l)), fun a b ha hb hab x hx => ?_⟩
  have hma : ∀ i l, IntAt P (m a i l) := fun i l => (GlobalTheory.CongLevel.mem_sclLat P q N e _).1 (ha _ (he i)).2 l
  have hmb : ∀ i l, IntAt P (m b i l) := fun i l => (GlobalTheory.CongLevel.mem_sclLat P q N e _).1 (hb _ (he i)).2 l
  have h1 : ∀ i l, IntAt P (((q ^ (j + 1) : ℕ) : E)⁻¹ * (m b i l - m a i l)) := by
    intro i l
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 (congrFun (congrFun hab i) l))
    have ht' := congrArg (algebraMap (𝓞 E) E) ht
    simp only [map_mul, map_natCast, map_sub] at ht'
    have := ((hr _ (hmb i l)).add (intAt_neg (hr _ (hma i l)))).add (intAt_neg (IntAt.coe P t))
    convert this using 1
    generalize ((q ^ (j + 1) : ℕ) : E) = c at *
    field_simp
    linear_combination ht'
  have e1 : (q : E)⁻¹ • ((a⁻¹ * b) x - x) = a⁻¹ ((q : E)⁻¹ • (b x - a x)) := by
    rw [map_smul, map_sub, show a⁻¹ (a x) = x from LinearEquiv.symm_apply_apply _ x]
    rfl
  rw [e1]
  refine (ha _ ?_).1
  rw [GlobalTheory.CongLevel.mem_sclLat] at hx ⊢
  intro l
  have ex : x = ∑ i, (((q : E) ^ e i.1)⁻¹ * x i) • (Pi.single i ((q : E) ^ e i.1) : Sp E N) := by
    funext l
    have := hz l.1
    simp [Finset.sum_apply, Pi.single_apply]
    field_simp
  have e2 : ((q : E) ^ e l.1)⁻¹ * ((q : E)⁻¹ • (b x - a x)) l =
      ∑ i, (((q : E) ^ e i.1)⁻¹ * x i) * (((q ^ (j + 1) : ℕ) : E)⁻¹ * (m b i l - m a i l)) := by
    conv_lhs => rw [ex]
    simp only [map_sum, map_smul, Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, smul_eq_mul, ← Finset.sum_sub_distrib,
      Finset.mul_sum, m]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hz l.1
    have := hz i.1
    push_cast
    field_simp
    ring
  rw [e2]
  exact Finset.sum_induction _ (IntAt P) (fun _ _ => IntAt.add) GlobalTheory.GO.ChRoot.intAt_zero' fun i _ =>
    (hx i).mul (h1 i l)

theorem exists_finite_index_of_adm_cosets : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), ∃ (ι : Type) (_ : Finite ι) (f : AutY X R j → ι), ∀ h h' : AutY X R j, admitted Pr j P h → admitted Pr j P h' → f h = f h' → h⁻¹ * h' ∈ Jat (Pr := Pr) sharp j P := by
  intro X Pr R sharp j P
  classical
  have hq := qOf_ne P
  have hb : ∀ h : AutY X R j, admitted Pr j P h → ∀ x ∈ lamYat (Pr := Pr) (R := R) j P,
      h⁻¹ x ∈ lamYat (Pr := Pr) (R := R) j P ∧ ((qOf P : X.E) ^ j) • h x ∈ lamYat (Pr := Pr) (R := R) j P := by
    intro h hh
    by_cases hP : P ∈ Pr.vGs
    · have hs := hh.1 hP
      intro x hx
      refine ⟨((inv_mem hs) x).2 hx, ?_⟩
      rw [← Nat.cast_pow]
      exact natCast_smul_mem _ _ ((hs x).2 hx)
    · exact (between_iff hP h).2 (hh.2 hP)
  obtain ⟨ι, hι, f, hf⟩ := exists_classes (P := P) (N := R.N j + cOf R j) hq
    (LocE.scE (R.N j) (if P ∈ Pr.vGs then fun i => i + 1 else 0)) j
  refine ⟨ι, hι, f, fun h h' hh hh' e => ?_⟩
  have h1 := hf h h' (hb h hh) (hb h' hh') e
  have h2 := hf h' h (hb h' hh') (hb h hh) e.symm
  refine mem_Jat _ _ _ _ (stab_of_cong hq _ _ h1 ?_) h1
  rw [mul_inv_rev, inv_inv]
  exact h2

end GlobalTheory.Mem.Col2.IdxFin

end
