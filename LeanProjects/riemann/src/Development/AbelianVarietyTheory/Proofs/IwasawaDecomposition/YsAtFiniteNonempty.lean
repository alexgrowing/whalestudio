import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

open Formalism.HermitianLatticesTheory (localization₂)

namespace GlobalTheory.Mem.CosetFin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

omit [StarRing E] in

theorem exists_reps (N : Submodule (𝓞 E) (Sp E n)) (hN : N.FG) (m : ℕ) (hm : m ≠ 0) :
    ∃ T : Set (Sp E n), T.Finite ∧ ∀ x ∈ N, ∃ t ∈ T, ∃ z ∈ N, x - t = (m : 𝓞 E) • z := by
  haveI : Module.Finite (𝓞 E) N := Module.Finite.iff_fg.2 hN
  haveI : Module.Finite ℤ N := Module.Finite.trans (𝓞 E) N
  let M : Submodule ℤ N := LinearMap.range (LinearMap.lsmul ℤ N (m : ℤ))
  haveI : Finite (N ⧸ M) := by
    refine Module.finite_of_fg_torsion _ fun x => ⟨⟨(m : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hm)⟩, ?_⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective M x
    show (m : ℤ) • (Submodule.Quotient.mk y : N ⧸ M) = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨y, rfl⟩
  refine ⟨Set.range fun q : N ⧸ M => ((Quotient.out q : N) : Sp E n), Set.finite_range _, fun x hx => ?_⟩
  refine ⟨_, ⟨Submodule.Quotient.mk ⟨x, hx⟩, rfl⟩, ?_⟩
  have h : (⟨x, hx⟩ : N) - Quotient.out (Submodule.Quotient.mk (p := M) ⟨x, hx⟩) ∈ M :=
    (Submodule.Quotient.eq M).1 (Quotient.out_eq _).symm
  obtain ⟨z, hz⟩ := h
  refine ⟨z, z.2, ?_⟩
  have h2 := congrArg Subtype.val hz
  simp only [LinearMap.lsmul_apply, AddSubgroupClass.coe_sub, natCast_zsmul] at h2
  rw [← h2, Nat.cast_smul_eq_nsmul]
  rfl

theorem exists_reps_loc (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) (hN : N.FG) (m : ℕ) (hm : m ≠ 0) :
    ∃ T : Set (Sp E n), T.Finite ∧
      ∀ x ∈ localization₂ P.asIdeal N, ∃ t ∈ T, ((m : E)⁻¹) • (x - t) ∈ localization₂ P.asIdeal N := by
  obtain ⟨T, hT, h⟩ := exists_reps N hN m hm
  refine ⟨T, hT, fun x hx => ?_⟩
  obtain ⟨s, hs, hsx⟩ := (mem_locP P N x).1 hx
  have hk : ∀ k : ℕ, s ^ (k + 1) • x ∈ N := fun k => by
    rw [pow_succ, mul_smul]; exact N.smul_mem _ hsx
  choose t ht z hz he using fun k => h _ (hk k)
  haveI := hT.to_subtype
  obtain ⟨i, j, hij, hEq⟩ : ∃ i j : ℕ, i < j ∧ t i = t j := by
    obtain ⟨a, b, hab, h1⟩ := Finite.exists_ne_map_eq_of_infinite (fun k => (⟨t k, ht k⟩ : T))
    have h1' : t a = t b := congrArg Subtype.val h1
    rcases lt_or_gt_of_ne hab with h2 | h2
    · exact ⟨a, b, h2, h1'⟩
    · exact ⟨b, a, h2, h1'.symm⟩
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_lt hij
  refine ⟨t p, ht p, (mem_locP P N _).2 ⟨s ^ (i + 1), fun hh => hs (P.isPrime.mem_of_pow_mem _ hh), ?_⟩⟩
  have hm' : (m : E) ≠ 0 := by exact_mod_cast hm
  have e1 : s ^ (i + 1) • (x - t p) = (m : 𝓞 E) • (z i - z (i + p + 1) + s ^ (i + 1) • z p) := by
    rw [smul_add, smul_sub (m : 𝓞 E), ← he i, ← he (i + p + 1), smul_comm (m : 𝓞 E), ← he p, hEq, smul_sub, smul_sub,
      ← mul_smul, ← pow_add, show i + 1 + (p + 1) = i + p + 1 + 1 by ring]
    abel
  rw [smul_comm, e1, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ hm']
  exact N.add_mem (N.sub_mem (hz _) (hz _)) (N.smul_mem _ (hz _))

theorem exists_reps_pow (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) (hN : N.FG) (a b : ℤ) :
    ∃ T : Set (Sp E n), T.Finite ∧ ∀ x : Sp E n, ((qOf P : E) ^ a)⁻¹ • x ∈ localization₂ P.asIdeal N →
      ∃ t ∈ T, ((qOf P : E) ^ b)⁻¹ • (x - t) ∈ localization₂ P.asIdeal N := by
  have hq : qOf P ≠ 0 := fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hq' : (qOf P : E) ≠ 0 := by exact_mod_cast hq
  obtain ⟨T, hT, h⟩ := exists_reps_loc P N hN (qOf P ^ (b - a).toNat) (pow_ne_zero _ hq)
  refine ⟨(fun t => (qOf P : E) ^ a • t) '' T, hT.image _, fun x hx => ?_⟩
  obtain ⟨t, ht, h1⟩ := h _ hx
  refine ⟨_, ⟨t, ht, rfl⟩, ?_⟩
  have h2 := (localization₂ P.asIdeal N).smul_mem ((qOf P ^ (a - b).toNat : ℕ) : 𝓞 E) h1
  rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E] at h2
  have e : ((qOf P ^ (a - b).toNat : ℕ) : E) * ((qOf P ^ (b - a).toNat : ℕ) : E)⁻¹ = ((qOf P : E) ^ b)⁻¹ * (qOf P : E) ^ a := by
    push_cast
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_neg, ← zpow_add₀ hq', ← zpow_add₀ hq']
    congr 1
    omega
  rw [smul_smul, e, mul_smul, smul_sub, smul_inv_smul₀ (zpow_ne_zero _ hq')] at h2
  exact h2

theorem finite_cosets (SB : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E n)) (hN : N.FG) (a b : SB → ℤ) :
    {Y : Set (Sp E n) | ∃ y ∈ locLat SB N a, Y = {z | z - y ∈ locLat SB N b}}.Finite := by
  choose T hT h using fun P : SB => exists_reps_pow P.1 N hN (a P) (b P)
  refine ((Set.Finite.pi' hT).image fun t : SB → Sp E n =>
    {z | ∀ P : SB, ((qOf P.1 : E) ^ b P)⁻¹ • (z - t P) ∈ localization₂ P.1.asIdeal N}).subset ?_
  rintro Y ⟨y, hy, rfl⟩
  choose t ht h1 using fun P => h P y ((mem_locLat SB N a y).1 hy P)
  refine ⟨t, ht, ?_⟩
  ext z
  simp only [Set.mem_setOf_eq, mem_locLat]
  refine forall_congr' fun P => ?_
  have e : z - t P = (z - y) + (y - t P) := by abel
  rw [e, smul_add]
  exact (localization₂ P.1.asIdeal N).add_mem_iff_left (h1 P)

theorem ysAt_finite_nonempty : ∀ {X : Fields} {Pr : Primes X} (R : Ranks)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (j : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E (R.N j))), Submodule.IsLattice X.E N →
      ((ysAt R sel mu cst j).ys N).Finite ∧ ((ysAt R sel mu cst j).ys N).Nonempty := by
  intro X Pr R sel S mu cst j N hN
  unfold ysAt
  split_ifs
  · exact ⟨finite_cosets _ N hN.fg _ _, _, 0, zero_mem _, rfl⟩
  · exact ⟨Set.finite_singleton _, Set.singleton_nonempty _⟩

end GlobalTheory.Mem.CosetFin
