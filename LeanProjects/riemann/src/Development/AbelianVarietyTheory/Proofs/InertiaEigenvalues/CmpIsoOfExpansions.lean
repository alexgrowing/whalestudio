import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NBasisLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLevelExpansionAtRootOfUnity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineFrobeniusBijOnLettersDirectSumStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionBasisDivisibilityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeEqStdPowerSeriesAtZeroStatement
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.WachCrystallineComparison

noncomputable section

namespace GlobalTheory.NL.CmpCris

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Series

variable {LL M : Type} [Field LL] [AddCommGroup M] [Module LL M]

theorem conv_one (f : ℤ → M) : conv (1 : PowerSeries LL) f = f := by
  funext k
  unfold conv
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    simp [PowerSeries.coeff_one, hj]

theorem conv_zero_coeff (e : PowerSeries LL) (f : ℤ → M) (hf : ∀ k < (0 : ℤ), f k = 0) :
    conv e f 0 = PowerSeries.constantCoeff e • f 0 := by
  unfold conv
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    rw [hf _ (by omega), smul_zero]

theorem mem_latSpan {ι : Type} (ex : ι → ℤ → M) (x : ι) : ex x ∈ latSpan (LL := LL) ex :=
  Submodule.subset_span ⟨1, x, (conv_one _).symm⟩

theorem neg_eq_zero_of_std {ι : Type} {D : Submodule LL M} {ex : ι → ℤ → M}
    (h : Std D (latSpan (LL := LL) ex)) (x : ι) : ∀ k < (0 : ℤ), ex x k = 0 :=
  ((h _).1 (mem_latSpan ex x)).2

theorem full_of_std {D : Submodule LL M} {Λ : Submodule LL (ℤ → M)} (h : Std D Λ) : Full D Λ :=
  ⟨0, fun f h1 h2 => (h f).2 ⟨h1, by simpa using h2⟩⟩

theorem span_const_of_std {ι : Type} {D : Submodule LL M} {ex : ι → ℤ → M}
    (h : Std D (latSpan (LL := LL) ex)) :
    Submodule.span LL (Set.range fun x => ex x 0) = D := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ((h _).1 (mem_latSpan ex x)).1 0
  · intro d hd
    have h1 : (Pi.single (0 : ℤ) d : ℤ → M) ∈ latSpan (LL := LL) ex := by
      refine (h _).2 ⟨fun k => ?_, fun k hk => Pi.single_eq_of_ne hk.ne _⟩
      by_cases hk : k = 0
      · subst hk; simpa using hd
      · rw [Pi.single_eq_of_ne hk]; exact D.zero_mem
    have h2 : latSpan (LL := LL) ex ≤ (Submodule.span LL (Set.range fun x => ex x 0)).comap
        (LinearMap.proj (R := LL) (φ := fun _ : ℤ => M) 0) := by
      unfold latSpan
      rw [Submodule.span_le]
      rintro _ ⟨e, x, rfl⟩
      change conv e (ex x) 0 ∈ Submodule.span LL (Set.range fun x => ex x 0)
      rw [conv_zero_coeff e _ (neg_eq_zero_of_std h x)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
    simpa using h2 h1

theorem exists_shift_of_std {D : Submodule LL M} {Λ : Submodule LL (ℤ → M)} (h : Std D Λ)
    (g : ℤ → M) (hg : g ∈ Λ) (h0 : g 0 = 0) : ∃ f ∈ Λ, ∀ j : ℤ, g j = f (j - ((1 : ℕ) : ℤ)) := by
  obtain ⟨h1, h2⟩ := (h g).1 hg
  refine ⟨fun j => g (j + 1), (h _).2 ⟨fun k => h1 _, fun k hk => ?_⟩, fun j => by simp⟩
  rcases (show k + 1 < 0 ∨ k + 1 = 0 by omega) with h3 | h3
  · exact h2 _ h3
  · rw [h3, h0]

end Series

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem prim_one (p : ℕ) : ∃ j : ℕ, IsPrimitiveRoot (1 : LL) (p ^ j) :=
  ⟨0, by simpa using IsPrimitiveRoot.one⟩

theorem sum_letE [NeZero n] : ∑ i : ZMod n, (letE i : LetA O n) = 1 := by
  funext j
  simp [letE, Finset.sum_apply, Pi.single_apply]

theorem const_lev_π (i : ZMod n) : PowerSeries.constantCoeff (W.lev i 1 letπ) = 0 := by
  obtain ⟨E, hE0, -, hE⟩ := W.lev_π i 1 (prim_one _)
  have := congrArg PowerSeries.constantCoeff hE
  simpa [hE0] using this

theorem const_lev (i : ZMod n) (a : LetA O n) :
    PowerSeries.constantCoeff (W.lev i 1 a) = algebraMap O LL (PowerSeries.constantCoeff (a i)) := by
  obtain ⟨b, hb⟩ : (PowerSeries.X : PowerSeries O) ∣
      a i - PowerSeries.C (PowerSeries.constantCoeff (a i)) := by
    rw [PowerSeries.X_dvd_iff]; simp
  have h := W.lev_letter i 1
    (a - algebraMap O (LetA O n) (PowerSeries.constantCoeff (a i)) - letπ * fun _ => b) (by
      simp only [Pi.sub_apply, Pi.mul_apply, letπ, Pi.algebraMap_apply]
      rw [← hb]
      simp [PowerSeries.algebraMap_apply])
  rw [map_sub, map_sub, map_mul, AlgHom.commutes] at h
  have h2 := congrArg PowerSeries.constantCoeff h
  rw [map_sub, map_sub, map_mul, const_lev_π, zero_mul, sub_zero, map_zero, sub_eq_zero] at h2
  rw [h2]
  simp [PowerSeries.algebraMap_apply]

theorem const_lev_Q (i : ZMod n) : PowerSeries.constantCoeff (W.lev i 1 W.Q) = (PD.p : LL) := by
  rw [LevPt.Q_eq, map_sum, map_sum]
  simp [const_lev_π]

theorem π_dvd_of_van (hinj : Function.Injective (algebraMap O LL)) (a : LetA O n)
    (ha : ∀ i, a ∈ van W i 1 1) : (letπ : LetA O n) ∣ a := by
  have h : ∀ i, (PowerSeries.X : PowerSeries O) ∣ a i := by
    intro i
    have h1 := ha i
    rw [van, Ideal.mem_comap, Ideal.mem_span_singleton, pow_one, PowerSeries.X_dvd_iff,
      const_lev] at h1
    rw [PowerSeries.X_dvd_iff]
    exact hinj (by rw [h1, map_zero])
  choose b hb using h
  exact ⟨b, funext hb⟩

theorem cmp_eq_sum [NeZero n] (T : LocLat G Qp LL O) (x : ↥(W.N T)) :
    W.cmp T x = ∑ i : ZMod n, W.cmp T ((letE i : LetA O n) • x) := by
  rw [← map_sum, ← Finset.sum_smul, sum_letE, one_smul]

theorem cmp_iso_of_expansions [NeZero n] (hinj : Function.Injective (algebraMap O LL))
    (T : LocLat G Qp LL O) (ex : ZMod n → ↥(W.N T) → ℤ → T.V ⊗[Qp] B)
    (hcmp : ∀ i x, W.cmp T ((letE i : LetA O n) • x) = ex i x 0)
    (hstd : ∀ i, Std (DcrisL PD T.ρ (W.emb i)) (latSpan (LL := LL) (ex i)))
    (hsup : (⨆ i, DcrisL PD T.ρ (W.emb i)) = Dcris PD T.ρ)
    (hind : iSupIndep fun i => DcrisL PD T.ρ (W.emb i))
    {r : ℕ} (nb : Module.Basis (Fin r) (LetA O n) ↥(W.N T))
    (hvan : ∀ i (y : ↥(W.N T)), (∃ f ∈ latSpan (LL := LL) (ex i), ∀ j : ℤ,
      ex i y j = f (j - ((1 : ℕ) : ℤ))) → ∀ j, nb.repr y j ∈ van W i 1 1)
    (hφ : ∀ (i : ZMod n) (x : ↥(W.N T)) (m : ℕ) (hx : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T),
      ex i ⟨W.Q ^ m • W.φD T (x : W.DD T), hx⟩ 0 =
        ∑ᶠ j : ℕ, PowerSeries.coeff j (W.lev i 1 (W.Q ^ m)) •
          (((PD.p : LL) ^ ((0 : ℤ) - (j : ℤ))) •
            φVB PD (LL := LL) (V := T.V) (ex (i - 1) x (0 - (j : ℤ))))) :
    GlobalTheory.IndefiniteRowSideFullHecke.WachCrystallineComparison.CmpIso W PD.p T := by
  have hlet : ∀ i : ZMod n, Submodule.span LL
      (Set.range fun x : ↥(W.N T) => W.cmp T ((letE i : LetA O n) • x)) =
        DcrisL PD T.ρ (W.emb i) := by
    intro i
    simp only [hcmp]
    exact span_const_of_std (hstd i)
  refine ⟨fun x => ⟨fun hx => ?_, ?_⟩, ?_, hlet, ?_⟩
  · rw [cmp_eq_sum] at hx
    have h0 : ∀ i, ex i x 0 = 0 := by
      intro i
      rw [← hcmp]
      exact (iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero _).1 hind Finset.univ
        (fun i => W.cmp T ((letE i : LetA O n) • x)) (fun i _ => W.cmp_letter T i x) hx i
        (Finset.mem_univ _)
    have hv : ∀ j, (letπ : LetA O n) ∣ nb.repr x j := fun j =>
      π_dvd_of_van W hinj _ fun i =>
        hvan i x (exists_shift_of_std (hstd i) _ (mem_latSpan _ x) (h0 i)) j
    choose b hb using hv
    refine ⟨∑ j, b j • nb j, ?_⟩
    rw [Finset.smul_sum]
    conv_lhs => rw [← nb.sum_repr x]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hb j, mul_smul]
  · rintro ⟨y, rfl⟩
    exact W.cmp_π T y
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact W.cmp_mem T x
    · rw [← hsup, iSup_le_iff]
      intro i
      rw [← hlet i]
      apply Submodule.span_mono
      rintro _ ⟨x, rfl⟩
      exact ⟨_, rfl⟩
  · intro x m hx
    rw [cmp_eq_sum W T x, cmp_eq_sum, map_sum, Finset.smul_sum,
      ← Equiv.sum_comp (Equiv.subRight (1 : ZMod n))
        (fun i => (PD.p : LL) ^ m •
          φVB PD (LL := LL) (V := T.V) (W.cmp T ((letE i : LetA O n) • x)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcmp, hcmp, Equiv.subRight_apply, hφ, finsum_eq_single _ 0]
    · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, map_pow, const_lev_Q]
      simp only [Nat.cast_zero, sub_zero, zpow_zero, one_smul]
    · intro j hj
      rw [neg_eq_zero_of_std (hstd (i - 1)) x (0 - (j : ℤ)) (by omega), map_zero, smul_zero,
        smul_zero]

end Generic

set_option maxHeartbeats 1000000 in

theorem cmp_iso (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l)
    (h : Good K s LL) (T : Lt K LL) (hT : IsCrys ((D.loc l).PD K) T.ρ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WachCrystallineComparison.CmpIso ((HW l).W K s LL h) ((D.loc l).PD K).p T := by
  have := ((D.loc l).PD K).finK₀
  have : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hstd := GlobalTheory.T.wach_lattice_eq_std_powerSeries_at_zero D HW F Cm l K s LL h T hT
  have hD := GlobalTheory.T.crystallineFrobenius_bijOn_letters_directSum D HW l K s LL h T hT
  obtain ⟨nb⟩ := GlobalTheory.NL.N_basis D HW F l K s LL h T hT
  exact cmp_iso_of_expansions ((HW l).W K s LL h) Subtype.val_injective T
    (fun i => ex (Cm l) h T i 1) (fun i x => ((Cm l).C K s LL h).tie.cmp_eq T hT i x) hstd
    hD.2.1 hD.2.2.1 nb
    (fun i y => (((GlobalTheory.T.wachExpansion_basis_divisibility D HW F Cm l K s LL h T hT i 1 (prim_one l)
        (full_of_std (hstd i))).2 _ nb).2.2 y 1).1)
    (fun i x m hx => by
      have key := ((Cm l).C K s LL h).tie.levB_φ T hT i 1 (prim_one _) x m hx 0
      have h1 : (1 : ↥LL.1) ^ ((D.loc l).PD K).p = 1 := one_pow _
      simp only [h1] at key
      unfold ex
      exact key)

end GlobalTheory.NL.CmpCris
