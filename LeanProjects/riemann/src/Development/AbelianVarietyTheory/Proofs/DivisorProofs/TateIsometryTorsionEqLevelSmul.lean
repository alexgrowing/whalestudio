import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory.LevDesc (move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.TateTorsion

open NumberField in

theorem _root_.GlobalTheory.TateTorsion.torsion_eq_level_smul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → kˣ → Prop) (T : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIso Dw k Q act e) (eta : Dw.La → Q) (I : Ideal (𝓞 E)) (g : ℕ), (∀ a b x, act (a + b) x = act a x * act b x) → (∀ x, act 1 x = x) → (∀ (n : ℕ) x, act (n : 𝓞 E) x = x ^ n) → (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), eta a = T.ev l.M a) → g.Prime → Ideal.absNorm I = g → (g : 𝓞 E) ∉ I ^ 2 → l.Mb ≤ I → ∃ t : 𝓞 E, (∀ c ∈ I • (⊤ : Submodule (𝓞 E) Dw.La), t • c ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) ∧ ∀ x : Q, (∀ a ∈ I, act a x = 1) → ∃ c : Dw.La, x = eta (t • c) := by
  intro E _ _ _ H Dw l k _ Q _ act e T eta I g hadd hone hnat heta hg hI hsq hle
  have hMb : (l.M : 𝓞 E) ∈ l.Mb := by
    have h : (l.M : 𝓞 E) ∈ Ideal.span {(l.M : 𝓞 E)} := Ideal.mem_span_singleton_self _
    rw [← l.prod] at h
    exact Ideal.mul_le_left h
  have hgI : (g : 𝓞 E) ∈ I := hI ▸ Ideal.absNorm_mem I
  have hprime : I.IsPrime := by
    apply Ideal.isPrime_of_irreducible_absNorm
    rw [hI]
    exact (Nat.prime_iff.mp hg).irreducible
  have hne : I ≠ ⊥ := by
    rintro rfl
    simp only [Ideal.absNorm_bot] at hI
    exact hg.ne_zero hI.symm
  have hmax : I.IsMaximal := hprime.isMaximal hne
  obtain ⟨B, hB⟩ : I ∣ Ideal.span {(g : 𝓞 E)} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hgI)
  have hIB : I ⊔ B = ⊤ := by
    by_contra h
    have hBI : B ≤ I := (hmax.eq_of_le h le_sup_left).symm ▸ le_sup_right
    apply hsq
    have hgB : (g : 𝓞 E) ∈ I * B := hB ▸ Ideal.mem_span_singleton_self _
    rw [pow_two]
    exact Ideal.mul_mono_right hBI hgB
  have hIbar : I ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ :=
    eq_top_iff.mpr (l.coprime ▸ sup_le_sup_right hle _)
  have hIK : I ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) * B = ⊤ := by
    rw [← Ideal.isCoprime_iff_sup_eq] at hIB hIbar ⊢
    exact hIbar.mul_right hIB
  obtain ⟨i, hi, u, hu, hiu⟩ :=
    Submodule.mem_sup.mp (hIK ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ I ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) * B)
  have huB : u ∈ B := Ideal.mul_le_right hu
  have huBar : u ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.mul_le_left hu
  have hgN : g ∣ l.M := by
    have h := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr (hle hMb))
    have h' : ((l.M : ℕ) : 𝓞 E) = algebraMap ℤ (𝓞 E) (l.M : ℤ) := by simp
    rw [hI, Ideal.absNorm_span_singleton, h', Algebra.norm_algebraMap, Int.natAbs_pow,
      Int.natAbs_natCast] at h
    exact hg.dvd_of_dvd_pow h
  obtain ⟨m, hm⟩ := hgN
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; have := l.three_le; omega)
  have key : ∀ j ∈ I, (m : 𝓞 E) * u * j ∈ l.Mb := by
    intro j hj
    have h : u * j ∈ Ideal.span {(g : 𝓞 E)} := hB ▸ (mul_comm j u ▸ Ideal.mul_mem_mul hj huB)
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp h
    have h2 : (m : 𝓞 E) * u * j = r * (l.M : 𝓞 E) := by
      rw [mul_assoc, ← hr, hm]; push_cast; ring
    rw [h2]
    exact Ideal.mul_mem_left _ r hMb
  refine ⟨(m : 𝓞 E) * u, ?_, ?_⟩
  · intro c hc
    refine Submodule.smul_induction_on hc (fun j hj y _ => ?_) (fun y z hy hz => ?_)
    · rw [smul_smul]
      exact Submodule.smul_mem_smul (key j hj) Submodule.mem_top
    · rw [smul_add]
      exact add_mem hy hz
  · intro x hx
    have hxg : x ^ g = 1 := by rw [← hnat]; exact hx _ hgI
    obtain ⟨b, hb⟩ := (T.onto g hg.pos x).mp hxg
    have hpow : ∀ (n j : ℕ) (a : Dw.La), T.ev n (j • a) = T.ev n a ^ j := by
      intro n j a
      induction j with
      | zero =>
        have h := T.add n 0 0
        rw [add_zero] at h
        simpa using h
      | succ j ih => rw [succ_nsmul, T.add, ih, pow_succ]
    have hux : act u x = x := by
      have h := hone x
      rwa [← hiu, hadd, hx i hi, one_mul] at h
    refine ⟨b, ?_⟩
    have hmem : ((m : 𝓞 E) * u) • b ∈
        l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La) :=
      Submodule.smul_mem_smul (Ideal.mul_mem_left _ _ huBar) Submodule.mem_top
    rw [heta _ hmem, mul_comm, mul_smul, T.lin, Nat.cast_smul_eq_nsmul, hpow, hm,
      T.tower g m hg.pos hm0, hb, hux]

end GlobalTheory.TateTorsion
