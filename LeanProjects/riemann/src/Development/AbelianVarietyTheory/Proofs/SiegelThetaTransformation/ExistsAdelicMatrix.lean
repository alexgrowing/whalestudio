import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevelStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsIsometryModPrimePow
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsEventuallyCongr
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionFractionalIdealDivisibleEqZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Real Classical nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.OntoLat

theorem exists_tower {R L M : Type} [CommRing R] [AddCommGroup L] [AddCommGroup M] [Module R L] [Module R M]
    [Module.Finite ℤ L] [Module.Finite ℤ M] (hc : ∀ r : ℕ, 0 < r → ∀ a c : L, r • a = r • c → a = c)
    (Q : ℕ → (L →ₗ[R] M) → Prop) (hQ : ∀ n m f, Q (n * m) f → Q n f)
    (hex : ∀ n : ℕ, 0 < n → ∃ f : L →ₗ[R] M,
      ((∀ a, (∃ e, f a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f a + n • e) ∧ Q n f) :
    ∃ f : ℕ → L →ₗ[R] M, (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧
      (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧
      ∀ n : ℕ, 0 < n → Q n (f n) := by
  choose g hg using fun j : ℕ => hex _ j.factorial_pos
  let U : Ultrafilter ℕ := Ultrafilter.of Filter.atTop
  have hU : ∀ n, 0 < n → ∀ᶠ j : ℕ in U, n ∣ j.factorial := fun n hn =>
    Ultrafilter.of_le _ ((Filter.eventually_ge_atTop n).mono fun j hj => Nat.dvd_factorial hn hj)
  have hs : ∀ n : ℕ, ∃ i : ℕ, 0 < n →
      (n ∣ i.factorial ∧ ∀ᶠ j in U, ∀ a, ∃ e, g j a = g i a + n • e) := fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, fun h => absurd h (lt_irrefl 0)⟩
    · obtain ⟨i, hi⟩ := IsoTower.exists_eventually_congr U (fun j => (g j).toAddMonoidHom) hn _ (hU n hn)
      exact ⟨i, fun _ => hi⟩
  choose s hs using hs
  refine ⟨fun n => g (s n), fun n m hn hm a => ?_, fun n hn => ?_, fun n hn => ?_⟩
  · obtain ⟨j, h1, h2⟩ := ((hs _ (Nat.mul_pos hn hm)).2.and (hs n hn).2).exists
    obtain ⟨e1, h1⟩ := h1 a
    obtain ⟨e2, h2⟩ := h2 a
    refine ⟨e2 - m • e1, ?_⟩
    show g (s (n * m)) a = g (s n) a + _
    rw [smul_sub, ← mul_smul, ← add_sub_assoc, ← h2, h1, add_sub_cancel_right]
  · obtain ⟨r, hr⟩ := (hs n hn).1
    have hr0 : 0 < r := Nat.pos_of_mul_pos_left (hr ▸ (s n).factorial_pos)
    obtain ⟨⟨h1, h2⟩, -⟩ := hg (s n)
    rw [hr] at h1 h2
    refine ⟨fun a => ⟨?_, ?_⟩, fun a' => ?_⟩
    · rintro ⟨e, he⟩
      have he' : g (s n) a = n • e := he
      obtain ⟨b, hb⟩ := (h1 (r • a)).1 ⟨e, by rw [map_nsmul, he', mul_comm, mul_smul]⟩
      exact ⟨b, hc r hr0 _ _ (by rw [hb, mul_comm, mul_smul])⟩
    · rintro ⟨e, rfl⟩
      exact ⟨_, map_nsmul _ _ _⟩
    · obtain ⟨a, e, h⟩ := h2 a'
      exact ⟨a, r • e, by rw [h, mul_smul]⟩
  · obtain ⟨r, hr⟩ := (hs n hn).1
    exact hQ n r _ (hr ▸ (hg (s n)).2)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_valueIdeal (X : Data E r) : ∃ J : FractionalIdeal (𝓞 E)⁰ E, J ≠ 0 ∧ (∀ z ∈ J, cc z ∈ J) ∧
    ∀ L : Lt E r, SelfD X L → ∀ x, x ∈ L ↔ ∀ y ∈ L, herm X.Gm x y ∈ J := by
  set ξ : E := X.κ0 / 2 with hξ
  have hξ' : ξ = X.ξ0 ∨ ξ = -X.ξ0 := X.κ0_xi.imp (fun h => by rw [hξ, h]; ring) fun h => by rw [hξ, h]; ring
  have hξ0 : ξ ≠ 0 := by
    rcases hξ' with h | h <;> rw [h]
    exacts [X.ξ0_ne, neg_ne_zero.2 X.ξ0_ne]
  have hξc : cc ξ = -ξ := by
    have := X.ξ0_im
    rcases hξ' with h | h <;> rw [h]
    · exact this
    · simp only [cc, map_neg] at this ⊢
      rw [this]
  have hI0 : FractionalIdeal.spanSingleton (𝓞 E)⁰ ξ ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.2 hξ0
  have hJ : ∀ z : E, z ∈ FractionalIdeal.dual ℤ ℚ (FractionalIdeal.spanSingleton (𝓞 E)⁰ ξ) ↔
      ∀ a : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E (-ξ * ((a : E) * z)) = k := by
    intro z
    rw [FractionalIdeal.mem_dual hI0]
    constructor
    · intro h a
      obtain ⟨k, hk⟩ := h ((-a) • ξ) ((FractionalIdeal.mem_spanSingleton _).2 ⟨-a, rfl⟩)
      refine ⟨k, ?_⟩
      rw [eq_intCast, Algebra.traceForm_apply, Algebra.smul_def, map_neg] at hk
      rw [hk]
      congr 1
      change _ = z * (-(a : E) * ξ)
      ring
    · intro h w hw
      obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hw
      obtain ⟨k, hk⟩ := h (-c)
      refine ⟨k, ?_⟩
      rw [eq_intCast, ← hk, Algebra.traceForm_apply, Algebra.smul_def]
      congr 1
      change -ξ * (((-c : 𝓞 E) : E) * z) = z * ((c : E) * ξ)
      push_cast
      ring
  have htr : ∀ z : E, Algebra.trace ℚ E (cc z) = Algebra.trace ℚ E z := fun z =>
    Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) z
  refine ⟨_, FractionalIdeal.dual_ne_zero ℤ ℚ hI0, fun z hz => ?_, fun L hL x => ?_⟩
  · rw [hJ] at hz ⊢
    intro a
    obtain ⟨k, hk⟩ := hz (-RingOfIntegers.mapRingEquiv (IsCMField.complexConj E : E ≃+* E) a)
    refine ⟨k, ?_⟩
    rw [← hk, ← htr]
    congr 1
    have e : ((-RingOfIntegers.mapRingEquiv (IsCMField.complexConj E : E ≃+* E) a : 𝓞 E) : E) = -cc (a : E) := rfl
    rw [e]
    simp only [cc, map_mul, map_neg, IsCMField.complexConj_apply_apply] at hξc ⊢
    rw [hξc]
    ring
  · have hE : ∀ (a : 𝓞 E) (u v : Fin r → E),
        EF X (a • u) v = Algebra.trace ℚ E (-ξ * ((a : E) * herm X.Gm u v)) := fun a u v => by
      rw [EF_def, ← algebraMap_smul E, HermitianTraceFormVanishing.herm_smul_left]
    constructor
    · intro hx y hy
      rw [hJ]
      intro a
      rw [← hE]
      exact (hL.2 _).1 (L.smul_mem a hx) y hy
    · intro h
      refine (hL.2 x).2 fun y hy => ?_
      have := (hJ _).1 (h y hy) 1
      rwa [← hE, one_smul] at this

theorem exists_adelic_matrix [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] (F : Type) [Field F]
    [NumberField F] [Algebra F E] (c : E ≃ₐ[F] E) (hcc : ∀ x, c x = cc x) (X : Data E r) {L L' : Lt E r}
    (hL : SelfD X L) (hL' : SelfD X L') :
    ∃ g : GL (Fin r) (AdLat.RA F E),
      (g : Matrix (Fin r) (Fin r) (AdLat.RA F E)).mulVec '' (AdLat.hat F (L : Set (Fin r → E))) =
        AdLat.hat F (L' : Set (Fin r → E)) ∧
      ∀ x y, AdLat.hermA c X.Gm ((g : Matrix (Fin r) (Fin r) (AdLat.RA F E)) *ᵥ x)
        ((g : Matrix (Fin r) (Fin r) (AdLat.RA F E)) *ᵥ y) = AdLat.hermA c X.Gm x y := by
  obtain ⟨J, hJ0, hJc, hJ⟩ := exists_valueIdeal X
  have h1 : ReciprocityTheory.MultiplicativeHeights.IsLattice L := ⟨hL.1, SW.TensLat.span_of_selfD X hL⟩
  have h2 : ReciprocityTheory.MultiplicativeHeights.IsLattice L' := ⟨hL'.1, SW.TensLat.span_of_selfD X hL'⟩
  have hγ := SelfDualGenus.exists_isLocalIsometry_of_modular hJ0 hJc X.Gm_herm X.Gm_herm X.Gm_det X.Gm_det h2 h1
    (hJ L' hL') (hJ L hL)
  haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL.1
  haveI : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  haveI : Module.Finite (𝓞 E) L' := Module.Finite.iff_fg.2 hL'.1
  haveI : Module.Finite ℤ L' := Module.Finite.trans (𝓞 E) L'
  obtain ⟨f, f1, f2, f3⟩ := exists_tower (R := 𝓞 E) (L := L) (M := L')
    (fun n hn a b h => by
      have hn' : (n : E) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
      have h' : (n : E) • (a : Fin r → E) = (n : E) • (b : Fin r → E) := by
        simpa only [Nat.cast_smul_eq_nsmul, Submodule.coe_smul_of_tower] using congrArg Subtype.val h
      exact Subtype.ext (smul_right_injective _ hn' h'))
    (fun n f => ∀ a a' : L, ∃ z ∈ J, herm X.Gm (f a) (f a') - herm X.Gm a a' = n • z)
    (fun n m f h a a' => by
      obtain ⟨z, hz, e⟩ := h a a'
      exact ⟨m • z, nsmul_mem (show z ∈ (J : Submodule (𝓞 E) E) from hz) m, by rw [e, mul_smul]⟩)
    (fun n hn => by
      obtain ⟨f, hf, hf'⟩ := IsomModN.exists_isometry_mod h1 h2 (IsomModN.isLattice_ideal hJ0)
        (fun x hx y hy i _ => (hJ L' hL' x).1 hx y hy) hγ hn
      refine ⟨f, hf, fun a a' => ?_⟩
      obtain ⟨m, hm, e⟩ := hf' a a'
      exact ⟨m 0, hm 0 trivial, e⟩)
  have hh : ∀ x y : Fin r → E, (∑ a, ∑ b, x a * X.Gm a b * c (y b)) = herm X.Gm x y := fun x y => by
    simp only [herm, hcc]
  obtain ⟨g, g1, -, g3⟩ := AdLat.exists_adelic_matrix_of_tower F E r L L' f h1.1 h1.2 h2.1 h2.2 f1 f2
  refine ⟨g, g1, g3 c X.Gm J (fun x hx y hy => ?_) fun n hn x y => ?_⟩
  · rw [hh]
    exact (hJ L' hL' x).1 hx y hy
  · obtain ⟨z, hz, e⟩ := f3 n hn x y
    exact ⟨z, hz, by rw [hh, hh, ← e, add_sub_cancel]⟩

theorem exists_mov_of_selfD {D : D7} {S T : HSp D} (C : Ctx S T) {L : Lt D.host.E T.rank} (hL : SelfD C.X L) :
    ∃ g ∈ GfC T, IsMov (fmt T g) C.X.Λ L := by
  haveI := (hostOfRecord D).unram
  obtain ⟨g, g1, g2⟩ := exists_adelic_matrix D.host.F (Member.cF D)
    (Member.latHat_eq_hat_and_gram D T).2.2.2.2.2.1 C.X (SW.Lev.selfD_of_sympl C.sympl) hL
  rw [C.m.gT] at g2
  obtain ⟨k, hk, rfl⟩ := (UnitarySplit.real_finite_split D T).2.2.2.1 g g2
  refine ⟨k, hk, fun u => ?_⟩
  have e : u ∈ hatV L ↔ u ∈ (AdLat.hat D.host.F (L : Set (Fin T.rank → D.host.E)) : Set _) := Iff.rfl
  rw [e, ← g1]
  exact ⟨fun ⟨u₀, h₀, h⟩ => ⟨u₀, h₀, h.symm⟩, fun ⟨u₀, h₀, h⟩ => ⟨u₀, h₀, h.symm⟩⟩

theorem exists_trivAt_mov : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ Lv : SW.Level C.X, ∀ L ∈ Lv.lats,
    ∃ g ∈ GfC T, TrivAt T (C.under Lv) g ∧ IsMov (fmt T g) C.X.Λ L := by
  intro D S T C Lv L hL
  obtain ⟨g, -, hg⟩ := exists_mov_of_selfD C hL.1
  exact ((GlobalTheory.T.self_dual_lattices_at_level D S T C).2 Lv g L hL.1.1 hg).2.2.2 hL

end GlobalTheory.Ker.OntoLat
