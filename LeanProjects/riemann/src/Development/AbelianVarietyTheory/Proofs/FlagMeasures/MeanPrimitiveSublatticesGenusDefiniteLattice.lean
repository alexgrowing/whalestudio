import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Formalism.HermitianLattices.HermitianLatticesProofs.MassTelescope
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianGenusMassEqOrbitStabilizerMassStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBoundedBasis
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CyclicDiscriminantLatticesFormOneGenusStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassGenusCyclicDiscriminantSplitPrimeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveSublatticeMeanCountBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularHermitianMassMulLeMassStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsBisTail

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.PrimGenus

section
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]

theorem nondeg_of_pd (h : V →ₗ⋆[K] V →ₗ[K] K) (hp : GlobalTheory.Mass.PD h) : h.Nondegenerate := by
  unfold GlobalTheory.Mass.PD at hp
  have key : ∀ x, h x x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    have hlt := hp (Classical.arbitrary (K →+* ℂ)) x hne
    rw [hx, map_zero, Complex.zero_re] at hlt
    exact lt_irrefl _ hlt
  constructor
  · intro x hx
    exact key x (hx x)
  · intro y hy
    exact key y (hy y)

end

theorem gen_of_cyclic {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] {A B : Submodule R W} (hle : B ≤ A)
    (I : Ideal R) (e : (↥A ⧸ B.comap A.subtype) ≃ₗ[R] (R ⧸ I)) :
    ∃ t : Finset W, t.card ≤ 1 ∧ A = B ⊔ Submodule.span R (t : Set W) := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (e.symm (Ideal.Quotient.mk I 1))
  refine ⟨{(a : W)}, by simp, le_antisymm ?_ ?_⟩
  · intro x hx
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (e (Submodule.Quotient.mk ⟨x, hx⟩))
    have hmk : Ideal.Quotient.mk I r = r • Ideal.Quotient.mk I 1 := by
      rw [Algebra.smul_def, map_one, mul_one]
      rfl
    have h1 : Submodule.Quotient.mk (⟨x, hx⟩ : A) = Submodule.Quotient.mk (p := B.comap A.subtype) (r • a) := by
      rw [Submodule.Quotient.mk_smul, ha, ← LinearEquiv.map_smul, ← hmk, hr, LinearEquiv.symm_apply_apply]
    rw [Submodule.Quotient.eq] at h1
    have h2 : x - r • (a : W) ∈ B := by simpa using h1
    have h3 : x = (x - r • (a : W)) + r • (a : W) := by abel
    rw [h3]
    exact Submodule.add_mem_sup h2 (Submodule.smul_mem _ r (Submodule.subset_span (by simp)))
  · exact sup_le hle (Submodule.span_le.mpr (by simp [a.2]))

theorem exponents (n D k s l : ℝ) (hn : 1 ≤ n) (hD : 1 ≤ D) (hs : 0 ≤ s) :
    n ^ ((k - s) / 2) * (n * D) ^ ((9 * s + 8 + 4 * l) / 2) ≤
      D ^ ((k - 1) / 2) * ((n / D) ^ (k / 2) * (n * D) ^ (5 * s + 5 + 2 * (1 + l))) := by
  have hn0 : 0 < n := by linarith
  have hD0 : 0 < D := by linarith
  have ha : 0 ≤ Real.log n := Real.log_nonneg hn
  have hb : 0 ≤ Real.log D := Real.log_nonneg hD
  simp only [Real.rpow_def_of_pos hn0, Real.rpow_def_of_pos hD0, Real.rpow_def_of_pos (mul_pos hn0 hD0),
    Real.rpow_def_of_pos (div_pos hn0 hD0), Real.log_mul hn0.ne' hD0.ne', Real.log_div hn0.ne' hD0.ne',
    ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg ha hs, mul_nonneg hb hs]

private theorem finrank_eq_two_mul_fDeg (K : Type) [Field K] [NumberField K] [StarRing K] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) :
    Module.finrank ℚ K = 2 * Formalism.HermitianLatticesTheory.fDeg K := by
  haveI := hK.1
  rw [IsTotallyComplex.finrank]
  unfold Formalism.HermitianLatticesTheory.fDeg
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero,
    zero_add]

private theorem mass_bound_rpow_le (K : Type) [Field K] [NumberField K] [StarRing K] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hv : 1 ≤ Formalism.HermitianLatticesTheory.vInv K) :
    1 ≤ (20 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ 2) ^ (2 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) * (6 + cf K)) ∧
    (20 * (Formalism.HermitianLatticesTheory.fDeg K : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ 2) ^ (16 * Formalism.HermitianLatticesTheory.fDeg K) ≤
      (20 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ 2) ^ (2 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) * (6 + cf K)) := by
  have hd := finrank_eq_two_mul_fDeg K hK
  have hfpos : 0 < Formalism.HermitianLatticesTheory.fDeg K := by
    have : 0 < Module.finrank ℚ K := Module.finrank_pos
    omega
  have hf : (1 : ℝ) ≤ (Formalism.HermitianLatticesTheory.fDeg K : ℝ) := by exact_mod_cast hfpos
  have hB : 1 ≤ 20 * (Formalism.HermitianLatticesTheory.fDeg K : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ 2 := by nlinarith
  have hd2 : (2 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by
    rw [hd]
    push_cast
    linarith
  have hl : 1 ≤ Real.logb 2 (Module.finrank ℚ K : ℝ) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
    simpa using hd2
  have hcf : 2 ≤ cf K := by
    unfold cf
    linarith
  refine ⟨Real.one_le_rpow hB (by nlinarith), ?_⟩
  rw [← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le hB
  push_cast
  nlinarith

private theorem laurent_T_unit_zpow_eq_T (T : ℝ) (hT : 2 ≤ T) (k f : ℕ) (hk : 1 ≤ k) :
    (T ^ (2 * f)) ^ (((k : ℝ) - 1) / 2) ≤ ((T ^ k - 1) / (T - 1)) ^ f := by
  have hT0 : 0 ≤ T := by linarith
  have h1 : (T ^ (2 * f)) ^ (((k : ℝ) - 1) / 2) = (T ^ (k - 1)) ^ f := by
    rw [← Real.rpow_natCast T (2 * f), ← Real.rpow_mul hT0, ← pow_mul, ← Real.rpow_natCast]
    congr 1
    push_cast [Nat.cast_sub hk]
    ring
  rw [h1]
  apply pow_le_pow_left₀ (pow_nonneg hT0 _)
  rw [le_div_iff₀ (by linarith)]
  have h2 : (1 : ℝ) ≤ T ^ (k - 1) := one_le_pow₀ (by linarith)
  have h3 : T ^ k = T ^ (k - 1) * T := by
    rw [← pow_succ]
    congr 1
    omega
  rw [h3]
  nlinarith

private theorem le_dual_of_integral_form {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V)
    (hi : ∀ x ∈ L, ∀ y ∈ L, h x y ∈ (1 : Submodule (𝓞 K) K)) : L ≤ Formalism.HermitianLatticesTheory.dual h L := by
  intro x hx
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf]
  intro y hy
  first
  | exact hi x hx y hy
  | exact hi y hy x hx
  | simpa using hi x hx y hy
  | simpa using hi y hy x hx

private theorem norm_cofactor_le_of_factorization {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (h : V →ₗ⋆[K] V →ₗ[K] K)
    (L : Submodule (𝓞 K) V) (T : ℕ)
    (e : (↥(Formalism.HermitianLatticesTheory.dual h L) ⧸ L.comap (Formalism.HermitianLatticesTheory.dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)})) :
    GlobalTheory.Mass.discN h L = T ^ (2 * Formalism.HermitianLatticesTheory.fDeg K) := by
  have hc : GlobalTheory.Mass.discN h L = Nat.card (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)}) := by
    unfold GlobalTheory.Mass.discN GlobalTheory.Mass.idxN AddSubgroup.relIndex AddSubgroup.index
    exact Nat.card_congr e.toEquiv
  rw [hc, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton]
  have hT : ((T : 𝓞 K)) = algebraMap ℤ (𝓞 K) (T : ℤ) := by simp
  rw [hT, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, finrank_eq_two_mul_fDeg K hK]
  simp [Int.natAbs_pow]

private theorem mul_mul_mul_le_of_bounds (A Bm X Y C R Q1 Q2 G mk : ℝ) (h10 : Bm * A ≤ mk * C) (hexp : X * Y ≤ R * (Q1 * Q2))
    (htp : R ≤ G) (hXY : 0 ≤ X * Y) (hkC : 0 ≤ mk * C) (hQ : 0 ≤ Q1 * Q2) :
    A * Bm * X * Y ≤ mk * G * C * Q1 * Q2 := by
  calc A * Bm * X * Y = (Bm * A) * (X * Y) := by ring
    _ ≤ (mk * C) * (R * (Q1 * Q2)) := mul_le_mul h10 hexp hXY hkC
    _ ≤ (mk * C) * (G * (Q1 * Q2)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right htp hQ) hkC
    _ = mk * G * C * Q1 * Q2 := by ring

theorem main : GlobalTheory.Mass.MaxMass → Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → HasOrtho K → 1 ≤ Formalism.HermitianLatticesTheory.vInv K → GlobalTheory.Mass.PD H.B.flip → 3 ≤ (Module.finrank K V) → ∀ (T : ℕ) (L₀ : Submodule (𝓞 K) V) (Mb : ℝ), T.Prime → (∀ P : Ideal (𝓞 K), P.IsMaximal → (T : 𝓞 K) ∈ P → Ideal.absNorm P = T ∧ (T : 𝓞 K) ∉ P ^ 2) → GlobalTheory.Mass.IsIntLat H.B.flip L₀ → Nonempty ((↥(Formalism.HermitianLatticesTheory.dual H.B.flip L₀) ⧸ L₀.comap (Formalism.HermitianLatticesTheory.dual H.B.flip L₀).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)})) → Mb = (20 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ 2) ^ (2 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) * (6 + cf K)) → ∀ D₀ : ℝ, D₀ = (T : ℝ) ^ (2 * (Formalism.HermitianLatticesTheory.fDeg K)) → ∀ s n : ℕ, 1 ≤ s → s < (Module.finrank K V) → 1 ≤ n → GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom H.B.flip) (Formalism.HermitianLatticesTheory.genus H.B.flip L₀) (fun L => (((GlobalTheory.Mass.primSp H.B.flip L ((Module.finrank K V) - s) n).encard : ℕ∞) : ℝ≥0∞)) ≤ ENNReal.ofReal (Formalism.HermitianLatticesTheory.mass H.B.flip L₀ * (Mb * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (Formalism.HermitianLatticesTheory.fDeg K) * 16 ^ (s * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K))) * ((n : ℝ) / D₀) ^ (((Module.finrank K V) : ℝ) / 2) * ((n : ℝ) * D₀) ^ (5 * (s : ℝ) + 5 + 2 * cf K)) := by
  intro hMax hS K V _ _ _ _ _ _ _ _ H hK hO hv hPD hk T L₀ Mb hT hTP hL₀ hq hMb D₀ hD₀ s n hs hsk hn
  obtain ⟨ms, hms0, hms⟩ := GlobalTheory.OrthoMass.main K hK
  have hsymm : H.B.flip.IsSymm := GlobalTheory.HermLat.flip_isSymm H
  have hnd : H.B.flip.Nondegenerate := nondeg_of_pd H.B.flip hPD
  have hgen := GlobalTheory.T.cyclicDiscriminant_lattices_form_one_genus K V H.B.flip hK hsymm hnd T hT hTP
  obtain ⟨-, -, hstab, -⟩ := GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V H.B.flip hK hsymm hPD L₀ hL₀.1
  have hsk' : Module.finrank K V - s + s = Module.finrank K V := Nat.sub_add_cancel hsk.le
  have key := GlobalTheory.T.primitiveSublattice_mean_count_bound hMax K V H.B.flip hK hsymm hPD hO (Module.finrank K V - s) s (by omega) hs hsk'
    (Fin (Module.finrank K V - s) → K) (Formalism.HermitianLatticesTheory.massTelescope_form K _) (Formalism.HermitianLatticesTheory.massTelescope_lat K _)
    (Formalism.HermitianLatticesTheory.massTelescope_symm K _) (Formalism.HermitianLatticesTheory.massTelescope_ortho K _)
    (Fin s → K) (Formalism.HermitianLatticesTheory.massTelescope_form K s) (Formalism.HermitianLatticesTheory.massTelescope_lat K s)
    (Formalism.HermitianLatticesTheory.massTelescope_symm K s) (Formalism.HermitianLatticesTheory.massTelescope_ortho K s)
    n (T ^ (2 * Formalism.HermitianLatticesTheory.fDeg K)) hn (Nat.one_le_pow _ _ hT.pos)
    (Formalism.HermitianLatticesTheory.genus H.B.flip L₀) hstab (fun L hL => by
      obtain ⟨hLi, ⟨eL⟩⟩ := (hgen.2 L₀ L hL₀ hq).mp hL
      exact ⟨hLi, norm_cofactor_le_of_factorization hK H.B.flip L T eL, gen_of_cyclic (le_dual_of_integral_form H.B.flip L hLi.2) _ eL⟩)
  have hm : ∀ j, Formalism.HermitianLatticesTheory.mass (Formalism.HermitianLatticesTheory.massTelescope_form K j) (Formalism.HermitianLatticesTheory.massTelescope_lat K j) = ms j :=
    fun j => hms j _ _ _ (Formalism.HermitianLatticesTheory.massTelescope_symm K j) (Formalism.HermitianLatticesTheory.massTelescope_ortho K j)
  rw [hm, hm] at key
  have hmass := GlobalTheory.T.mass_genus_cyclicDiscriminant_splitPrime hMax K V H.B.flip hK hsymm hPD (by omega) (Fin (Module.finrank K V) → K)
    (Formalism.HermitianLatticesTheory.massTelescope_form K _) (Formalism.HermitianLatticesTheory.massTelescope_symm K _) (Formalism.HermitianLatticesTheory.massTelescope_lat K _)
    (Formalism.HermitianLatticesTheory.massTelescope_ortho K _) T hT hTP L₀ hL₀ hq
  rw [hm] at hmass
  obtain ⟨hMb1, hMbB⟩ := mass_bound_rpow_le K hK hv
  rw [← hMb] at hMb1 hMbB
  have hsmall : ∀ j, 1 ≤ j → j ≤ 2 → ms j ≤ Mb := fun j h1 h2 => by
    rw [← hm j]
    exact (GlobalTheory.SmallRankMass.mass_small hK hv h1 h2).trans hMbB
  have h10 := GlobalTheory.T.unimodularHermitianMass_mul_le_mass hS K hK hv (Module.finrank K V) s Mb ms hk hs hsk hms
    (hsmall 1 le_rfl (by norm_num)) (hsmall 2 (by norm_num) le_rfl) hMb1
  have hexp := exponents (n : ℝ) ((T : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K)) (Module.finrank K V : ℝ) (s : ℝ)
    (Real.logb 2 (Module.finrank ℚ K)) (by exact_mod_cast hn) (one_le_pow₀ (by exact_mod_cast hT.one_lt.le))
    (by positivity)
  have htp := laurent_T_unit_zpow_eq_T (T : ℝ) (by exact_mod_cast hT.two_le) (Module.finrank K V) (Formalism.HermitianLatticesTheory.fDeg K) (by omega)
  have hC : 0 ≤ Mb * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (Formalism.HermitianLatticesTheory.fDeg K) * 16 ^ (s * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K)) :=
    mul_nonneg (mul_nonneg (by linarith) (pow_nonneg (by linarith) _)) (by positivity)
  subst hD₀
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [hmass, Nat.cast_sub hsk.le, Nat.cast_pow]
  exact mul_mul_mul_le_of_bounds _ _ _ _ _ _ _ _ _ _ h10 hexp htp (by positivity) (mul_nonneg (hms0 _).le hC) (by positivity)

end GlobalTheory.DegCnt.PrimGenus
