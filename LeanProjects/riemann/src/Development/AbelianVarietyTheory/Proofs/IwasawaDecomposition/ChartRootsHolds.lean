import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankEqZeroIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFormEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModNOfDvdModulus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsObjTwistBySimilitude
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimTrivialOfMult
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLimitPointTateIsoSequence

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.LocM GlobalTheory.LocM.Cht

namespace GlobalTheory.LocM.RootsPrescribe

theorem exists_smul_of_mem_of_coprime {R L : Type*} [CommRing R] [AddCommGroup L] [Module R L] {I J : Ideal R} {r : R}
    (hc : I ⊔ J = ⊤) (hp : I * J = Ideal.span {r}) {x : L} (hI : x ∈ I • (⊤ : Submodule R L))
    (hJ : x ∈ J • (⊤ : Submodule R L)) : ∃ b, x = r • b := by
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (show (1 : R) ∈ I ⊔ J from hc ▸ Submodule.mem_top)
  have h1 : u • x ∈ (I * J) • (⊤ : Submodule R L) := by
    rw [mul_smul]; exact Submodule.smul_mem_smul hu hJ
  have h2 : v • x ∈ (I * J) • (⊤ : Submodule R L) := by
    rw [mul_comm, mul_smul]; exact Submodule.smul_mem_smul hv hI
  have h3 : x ∈ (I * J) • (⊤ : Submodule R L) := by
    have := Submodule.add_mem _ h1 h2
    rwa [← add_smul, huv, one_smul] at this
  rw [hp, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h3
  obtain ⟨b, -, hb⟩ := h3
  exact ⟨b, hb.symm⟩

theorem exists_one {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    (l : Level H) {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    (I : TateIso Dw k Q act e) (hpq : 1 ≤ Dw.p + Dw.q) {m : ℕ} (hm : 0 < m) {w : kˣ}
    (hw : IsPrimitiveRoot w (l.A * m)) (hA : w ^ m = I.ζ l.A) :
    ∃ I' : TateIso Dw k Q act e, I'.ζ (l.A * m) = w ∧ (∀ a, I'.ev l.A a = I.ev l.A a) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), I'.ev l.M a = I.ev l.M a := by
  have hN : 0 < l.A * m := Nat.mul_pos l.A_pos hm
  have hM : 0 < l.M := by have := l.three_le; omega
  have : NeZero (l.A * m) := ⟨hN.ne'⟩
  have hζ : IsPrimitiveRoot ((I.ζ (l.A * m) : kˣ) : k) (l.A * m) := IsPrimitiveRoot.coe_units_iff.2 (I.ζ_prim _ hN)
  obtain ⟨i, -, hi, hiz⟩ := (hζ.isPrimitiveRoot_iff).1 (IsPrimitiveRoot.coe_units_iff.2 hw)
  have hiz' : I.ζ (l.A * m) ^ i = w := Units.ext (by rw [Units.val_pow_eq_pow_val, hiz])
  have hi1 : (l.A : ℤ) ∣ (i : ℤ) - 1 := by
    rw [← (I.ζ_prim l.A l.A_pos).zpow_eq_one_iff_dvd, zpow_sub, zpow_one, zpow_natCast, mul_inv_eq_one]
    conv_lhs => rw [← I.ζ_pow l.A m l.A_pos hm, ← pow_mul, mul_comm m, pow_mul, hiz', hA]
  obtain ⟨g, hg, -, hgM, hgA⟩ := GlobalTheory.SimMult.exists_sim_trivial_of_mult GlobalTheory.SimAlg.sim_group GlobalTheory.exists_sim_lift E H Dw
    l (l.A * m) i hN (Nat.isCoprime_iff_coprime.2 hi) hi1
  refine ⟨GlobalTheory.LevelTwist.twist I g ((GlobalTheory.SimAlg.sim_group E H Dw hpq).1 g), ?_, fun a => ?_, fun a ha => ?_⟩
  · rw [GlobalTheory.LevelTwist.twist_ζ, GlobalTheory.LevelTwist.zeta_zpow_congr I hN hg, zpow_natCast, hiz']
  · exact GlobalTheory.LevelTwist.ev_congr I l.A_pos (hgA a)
  · refine GlobalTheory.LevelTwist.ev_congr I hM ?_
    obtain ⟨b, hb⟩ := exists_smul_of_mem_of_coprime l.coprime l.prod (hgM a)
      (Submodule.sub_mem _ (GlobalTheory.LevelTwist.map_mem_smul_top _ _ ha) ha)
    exact ⟨b, hb.trans (Nat.cast_smul_eq_nsmul _ _ _)⟩

theorem roots : GlobalTheory.LocM.Cht.RootsSt := by
  intro E _ _ _ H Dw l k _ Q _ act e I z hpq hz hzp hA
  have hM : 0 < l.M := by have := l.three_le; omega
  have key := fun j : ℕ => exists_one l I hpq j.factorial_pos (hz _ (Nat.mul_pos l.A_pos j.factorial_pos))
    ((hzp _ _ l.A_pos j.factorial_pos).trans hA)
  choose J hJ hJA hJM using key
  obtain ⟨I', hI'⟩ := GlobalTheory.Ex.TateLimit.exists_limit E H Dw k Q act e J
  refine ⟨I', fun n hn => ?_, fun a => ?_, fun a ha => ?_⟩
  · obtain ⟨j, hj, -, h⟩ := hI' n hn n
    obtain ⟨t, ht⟩ : n ∣ l.A * j.factorial := (Nat.dvd_factorial hn hj).mul_left _
    have ht0 : 0 < t := Nat.pos_of_mul_pos_left (ht ▸ Nat.mul_pos l.A_pos j.factorial_pos : 0 < n * t)
    rw [h, ← (J j).ζ_pow n t hn ht0, ← hzp n t hn ht0, ← ht, hJ]
  · obtain ⟨j, -, h, -⟩ := hI' l.A l.A_pos 0
    rw [h, hJA]
  · obtain ⟨j, -, h, -⟩ := hI' l.M hM 0
    rw [h, hJM j a ha]

end GlobalTheory.LocM.RootsPrescribe
