import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetCharEqOneOfHasWt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfTameLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitOpenAndCongrOpen
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsIdealsPrimeToEqSpan
import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitRealOfCongrOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdArgRealUnitEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAlgCharEqArgMulAbsStatement

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.AlgCharUnr

theorem phase_prod_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] {q : ℕ} (hq : q.Prime) (hq2 : 2 < q)
    (ht : ¬ q ∣ Nat.card (Units.torsion E)) (u : (𝓞 E)ˣ) (hu : (u : 𝓞 E) - 1 ∈ Ideal.span {((q : ℕ) : 𝓞 E)})
    (m : InfinitePlace E → ℤ) (w0 : ℤ) (hm : ∀ w, ∃ a, m w = 2 * a - w0) :
    ∏ w : InfinitePlace E, (w.embedding ((u : 𝓞 E) : E) / ((‖w.embedding ((u : 𝓞 E) : E)‖ : ℝ) : ℂ)) ^ m w = 1 := by
  have hr := GlobalTheory.T.unit_real_of_sub_one_mem_span_prime E q hq ht u hu
  have hs := GlobalTheory.T.prod_arg_real_unit_eq_one' E q hq hq2 u hu hr
  have hsq : ∀ w : InfinitePlace E,
      (w.embedding ((u : 𝓞 E) : E) / ((‖w.embedding ((u : 𝓞 E) : E)‖ : ℝ) : ℂ)) ^ m w =
      ((w.embedding ((u : 𝓞 E) : E) / ((‖w.embedding ((u : 𝓞 E) : E)‖ : ℝ) : ℂ)) ^ w0)⁻¹ := fun w => by
    set z := w.embedding ((u : 𝓞 E) : E) with hz
    have h0 : z ≠ 0 := by rw [hz, map_ne_zero]; exact Units.coe_ne_zero u
    have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h0
    have hzr : starRingEnd ℂ z = z := hr _
    have h2 : (z / ((‖z‖ : ℝ) : ℂ)) ^ (2 : ℤ) = 1 := by
      rw [zpow_two, div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero hn hn)]
      have e : ((‖z‖ : ℝ) : ℂ) * ((‖z‖ : ℝ) : ℂ) = z * starRingEnd ℂ z := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
      rw [e, hzr]
    obtain ⟨a, ha⟩ := hm w
    have hne : z / ((‖z‖ : ℝ) : ℂ) ≠ 0 := div_ne_zero h0 hn
    rw [ha, sub_eq_add_neg, zpow_add₀ hne, zpow_mul, h2, one_zpow, one_mul, zpow_neg]
  rw [Finset.prod_congr rfl fun w _ => hsq w, Finset.prod_inv_distrib, Finset.prod_zpow, hs, one_zpow, inv_one]

theorem exists_odd_prime_gt_two_bounds (l t : ℕ) : ∃ q : ℕ, q.Prime ∧ 2 < q ∧ l < q ∧ t < q := by
  obtain ⟨q, hq, hp⟩ := Nat.exists_infinite_primes (max (max 3 (l + 1)) (t + 1))
  exact ⟨q, hp, by omega, by omega, by omega⟩

theorem exists_algChar_unr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ), l.Prime → ∀ (n : (E →+* ℂ) → ℤ) (w0 : ℤ), (∀ φ, n φ + n (NumberField.ComplexEmbedding.conjugate φ) = w0) → ∃ χ : HChar E, IsAlgPos χ n ∧ ∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → χ.UnrAt w := by
  intro E _ _ _ l hl n w0 hn
  classical
  obtain ⟨q, hq, hq2, hlq, htq⟩ := exists_odd_prime_gt_two_bounds l (Nat.card (Units.torsion E))
  have ht : ¬ q ∣ Nat.card (Units.torsion E) := fun h =>
    absurd (Nat.le_of_dvd Nat.card_pos h) (by omega)
  set 𝔪 : Ideal (𝓞 E) := Ideal.span {((q : ℕ) : 𝓞 E)} with h𝔪
  have hq0 : ((q : ℕ) : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
  have hm : 𝔪 ≠ ⊥ := by rw [h𝔪, Ne, Ideal.span_singleton_eq_bot]; exact hq0
  let m : InfinitePlace E → ℤ := fun w => 2 * n w.embedding - w0
  have hbij : Function.Bijective fun w : InfinitePlace E => InfinitePlace.mk w.embedding := by
    simp only [InfinitePlace.mk_embedding]
    exact Function.bijective_id
  obtain ⟨ψ, hψ, hψu, hψi, -, hψS, hψd⟩ := GlobalTheory.ModelChar.exists_modelChar E (InfinitePlace E) (fun w => w.embedding)
    hbij m ∅ (fun _ => 1) (by simp)
  have hinf := (GlobalTheory.InfTypeLocal.infType_iff_local E (InfinitePlace E) (fun w => w.embedding) hbij ψ hψ _).2 hψi
  let U : Subgroup (Neutral.B1.Ideles E) := GlobalTheory.Mem.Chr.unitIdl E ⊓ GlobalTheory.RayChar.congrIdl 𝔪
  have hU : IsOpen (U : Set (Neutral.B1.Ideles E)) :=
    GlobalTheory.Mem.UnitOpen.isOpen_unitIdl.inter (GlobalTheory.RayChar.isOpen_congrIdl hm)
  have hmem : ∀ k : Eˣ, infDiag k ∈ U := fun k => by
    refine ⟨?_, (GlobalTheory.RayChar.mem_congrIdl hm).2 fun v _ => ?_⟩
    · unfold infDiag
      rw [MonoidHom.finsetProd_apply]
      exact Subgroup.prod_mem _ fun w _ => GlobalTheory.Mem.Chr.AntiExist.inf_mem w _
    · have h1 : GlobalTheory.RayChar.cmp (infDiag k) v = 1 :=
        congrArg Units.val (GlobalTheory.ModelChar.finEv_infDiag v k)
      rw [h1, sub_self, map_zero]
      exact zero_le'
  obtain ⟨χ1, hχc, -, hχU, hχd⟩ := GlobalTheory.exists_unitary_char_of_open_subgroup_and_hom (Neutral.B1.Ideles E) Eˣ U hU
    (Neutral.B1.diagUnits E) 1 ψ hψ hψu (fun _ => by simp) (fun k hk => by
      obtain ⟨u, hu⟩ := GlobalTheory.DefU.NonTriv.exists_unit k hk.1
      have hu1 : (u : 𝓞 E) - 1 ∈ 𝔪 := (GlobalTheory.RayChar.mem_iff_at hm _).2 fun v hv => by
        rw [GlobalTheory.RayChar.at'_sub_one]
        have h2 := (GlobalTheory.RayChar.mem_congrIdl hm).1 hk.2 v hv
        rw [GlobalTheory.RayChar.cmp_diag, ← hu] at h2
        exact h2
      show (1 : ℂˣ) = ψ (Neutral.B1.diagUnits E k)
      rw [hψd, Finset.prod_empty, mul_one]
      refine (Units.ext ?_).symm
      rw [hinf k, Units.val_one, ← hu]
      exact phase_prod_eq_one hq hq2 ht u hu1 m w0 fun w => ⟨n w.embedding, rfl⟩)
  let χ0 : HChar E := ⟨χ1, hχc, fun k => by rw [hχd]; rfl⟩
  let s : ℝ := (w0 : ℝ) / 2
  let ν : HChar E := GlobalTheory.Mem.Chr.CharModel.absChar E (s : ℂ)
  have hν : ν.IsAbsPow s := GlobalTheory.Mem.Chr.CharModel.absChar_isAbsPow s
  refine ⟨χ0 * ν, fun k _ => ?_, fun w hw x hx => ?_⟩
  · have h1 : ((χ0.inf k : ℂˣ) : ℂ) = ∏ w : InfinitePlace E, (w.embedding (k : E) / ((‖w.embedding (k : E)‖ : ℝ) : ℂ)) ^ m w := by
      show ((χ1 (infDiag k) : ℂˣ) : ℂ) = _
      rw [hχU _ (hmem k)]
      exact hinf k
    rw [HChar.inf_mul, Units.val_mul, h1, hν.2.2 k]
    exact GlobalTheory.T.cm_algChar_eq_arg_mul_abs E n w0 hn (k : E) k.ne_zero
  · have hwq : ¬ w.asIdeal ∣ 𝔪 := by
      rw [h𝔪, Ideal.dvd_span_singleton]
      intro hqw
      have hc : IsCoprime ((l : ℕ) : 𝓞 E) ((q : ℕ) : 𝓞 E) :=
        Nat.Coprime.cast ((Nat.coprime_primes hl hq).2 hlq.ne)
      obtain ⟨a, b, hab⟩ := hc
      apply w.isPrime.ne_top
      rw [Ideal.eq_top_iff_one, ← hab]
      exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hw) (w.asIdeal.mul_mem_left _ hqw)
    rw [HChar.loc_mul, hν.1 w x hx, mul_one]
    show χ1 (Neutral.B1.localIdele E w x) = 1
    rw [hχU _ ⟨GlobalTheory.RayChar.local_mem_unitIdl hx, GlobalTheory.RayChar.local_mem_congrIdl hwq x⟩]
    exact hψS w (Finset.notMem_empty w) x

end GlobalTheory.AlgCharUnr
