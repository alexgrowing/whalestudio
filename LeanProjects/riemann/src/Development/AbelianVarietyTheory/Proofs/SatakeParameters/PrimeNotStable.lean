import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtOne
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
open scoped WithZero

noncomputable section

namespace GlobalTheory.XcSplit

open Topology

theorem ball_mem_nhds {K : Type} [Field K] [Valued K ℤᵐ⁰] (x r : K) (hr : r ≠ 0) :
    {y | Valued.v (y - x) < Valued.v r} ∈ 𝓝 x := by
  rw [Valued.mem_nhds]
  have h' : (Valued.v : Valuation K ℤᵐ⁰).restrict r ≠ 0 := by simp [hr]
  exact ⟨Units.mk0 _ h', fun y hy => (Valuation.restrict_lt_iff _).1 hy⟩

theorem approx {F E K : Type} [Field F] [Field E] [Algebra F E] [Field K] [Algebra F K] [Valued K ℤᵐ⁰]
    (hd : DenseRange (algebraMap F K)) (s : E ⊗[F] K ≃+* K × K) (hs : ∀ c : K, s ((1 : E) ⊗ₜ[F] c) = (c, c))
    (t : E ⊗[F] K) (r : K) (hr : r ≠ 0) :
    ∃ x : E, Valued.v ((s (x ⊗ₜ[F] (1 : K))).1 - (s t).1) < Valued.v r ∧
      Valued.v ((s (x ⊗ₜ[F] (1 : K))).2 - (s t).2) < Valued.v r := by
  have hr0 : (0 : ℤᵐ⁰) < Valued.v r := by
    rw [pos_iff_ne_zero]; simpa using hr
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simpa using hr0, by simpa using hr0⟩
  | tmul e c =>
    classical
    set α := (s (e ⊗ₜ[F] (1 : K))).1 with hα
    set β := (s (e ⊗ₜ[F] (1 : K))).2 with hβ

    obtain ⟨u, hαu, hβu⟩ : ∃ u : K, Valued.v α ≤ Valued.v u ∧ Valued.v β ≤ Valued.v u := by
      rcases le_total (Valued.v α) (Valued.v β) with h | h
      · exact ⟨β, h, le_rfl⟩
      · exact ⟨α, le_rfl, h⟩

    have key : ∀ w z : K, Valued.v w ≤ Valued.v u → Valued.v z < Valued.v (if u = 0 then r else r * u⁻¹) →
        Valued.v (w * z) < Valued.v r := by
      intro w z hw hz
      rw [Valuation.map_mul]
      by_cases hu : u = 0
      · have : Valued.v w = 0 := by
          rw [hu, Valuation.map_zero] at hw; exact le_antisymm hw zero_le'
        rw [this, zero_mul]; exact hr0
      · rw [if_neg hu] at hz
        have hu0 : (0 : ℤᵐ⁰) < Valued.v u := by rw [pos_iff_ne_zero]; simpa using hu
        calc Valued.v w * Valued.v z ≤ Valued.v u * Valued.v z := by gcongr
          _ < Valued.v u * Valued.v (r * u⁻¹) := mul_lt_mul_of_pos_left hz hu0
          _ = Valued.v r := by
              rw [← Valuation.map_mul]; congr 1; field_simp
    have hne : (if u = 0 then r else r * u⁻¹) ≠ 0 := by
      split_ifs with hu
      · exact hr
      · exact mul_ne_zero hr (inv_ne_zero hu)
    obtain ⟨_, hy, f, rfl⟩ := mem_closure_iff_nhds.1 (hd c) _ (ball_mem_nhds c _ hne)
    have h1 : (f • e) ⊗ₜ[F] (1 : K) = (e ⊗ₜ[F] (1 : K)) * ((1 : E) ⊗ₜ[F] algebraMap F K f) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, TensorProduct.smul_tmul,
        Algebra.algebraMap_eq_smul_one]
    have h2 : e ⊗ₜ[F] c = (e ⊗ₜ[F] (1 : K)) * ((1 : E) ⊗ₜ[F] c) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    refine ⟨f • e, ?_, ?_⟩
    · rw [h1, h2, map_mul, map_mul, hs, hs, Prod.fst_mul, Prod.fst_mul, ← mul_sub]
      exact key _ _ hαu hy
    · rw [h1, h2, map_mul, map_mul, hs, hs, Prod.snd_mul, Prod.snd_mul, ← mul_sub]
      exact key _ _ hβu hy
  | add t1 t2 h1 h2 =>
    obtain ⟨x1, a1, b1⟩ := h1
    obtain ⟨x2, a2, b2⟩ := h2
    refine ⟨x1 + x2, ?_, ?_⟩
    · have : (s ((x1 + x2) ⊗ₜ[F] (1 : K))).1 - (s (t1 + t2)).1 =
          ((s (x1 ⊗ₜ[F] (1 : K))).1 - (s t1).1) + ((s (x2 ⊗ₜ[F] (1 : K))).1 - (s t2).1) := by
        rw [TensorProduct.add_tmul, map_add, map_add, Prod.fst_add, Prod.fst_add]; ring
      rw [this]; exact Valuation.map_add_lt _ a1 a2
    · have : (s ((x1 + x2) ⊗ₜ[F] (1 : K))).2 - (s (t1 + t2)).2 =
          ((s (x1 ⊗ₜ[F] (1 : K))).2 - (s t1).2) + ((s (x2 ⊗ₜ[F] (1 : K))).2 - (s t2).2) := by
        rw [TensorProduct.add_tmul, map_add, map_add, Prod.snd_add, Prod.snd_add]; ring
      rw [this]; exact Valuation.map_add_lt _ b1 b2

theorem exists_frac {S K : Type} [CommRing S] [IsDedekindDomain S] [Field K] [Algebra S K] [IsFractionRing S K]
    (ν : Valuation K ℤᵐ⁰) (P : Ideal S) [hp : P.IsPrime] (hP : P ≠ ⊥)
    (hle : ∀ x : S, ν (algebraMap S K x) ≤ 1) (hlt : ∀ x ∈ P, ν (algebraMap S K x) < 1) (z : K) (hz : ν z ≤ 1) :
    ∃ a s : S, s ∉ P ∧ z * algebraMap S K s = algebraMap S K a := by
  have hmax : P.IsMaximal := hp.isMaximal hP
  have hunit : ∀ s, s ∉ P → ν (algebraMap S K s) = 1 := by
    intro s hs
    obtain ⟨t, r, hr, htr⟩ := hmax.exists_inv hs
    have h1 : ν (algebraMap S K (t * s)) = 1 := by
      have h2 : t * s = 1 - r := by rw [← htr]; ring
      rw [h2, map_sub, map_one]
      exact Valuation.map_one_sub_of_lt _ (hlt r hr)
    rw [map_mul, map_mul] at h1
    refine le_antisymm (hle s) ?_
    calc (1 : ℤᵐ⁰) = ν (algebraMap S K t) * ν (algebraMap S K s) := h1.symm
      _ ≤ 1 * ν (algebraMap S K s) := by gcongr; exact hle t
      _ = _ := one_mul _
  let A := Localization.AtPrime P
  haveI : IsDiscreteValuationRing A := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S hP A
  have hinj : Function.Injective (algebraMap S A) :=
    IsLocalization.injective A P.primeCompl_le_nonZeroDivisors
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := S) z
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hyK : algebraMap S K y ≠ 0 := by
    simpa using (IsFractionRing.injective S K).ne hy0
  obtain ⟨c, hc⟩ := PreValuationRing.cond (algebraMap S A x) (algebraMap S A y)
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl c
  have hK1 : ∀ {a s : S}, x * a = y * s →
      algebraMap S K x / algebraMap S K y * algebraMap S K a = algebraMap S K s := by
    intro a s h
    have h' : algebraMap S K x * algebraMap S K a = algebraMap S K y * algebraMap S K s := by
      rw [← map_mul, ← map_mul, h]
    field_simp
    exact h'
  have hK2 : ∀ {a s : S}, y * a = x * s →
      algebraMap S K x / algebraMap S K y * algebraMap S K s = algebraMap S K a := by
    intro a s h
    have h' : algebraMap S K y * algebraMap S K a = algebraMap S K x * algebraMap S K s := by
      rw [← map_mul, ← map_mul, h]
    field_simp
    exact h'.symm
  rcases hc with hc | hc
  · have h1 : x * a = y * s := by
      apply hinj
      rw [map_mul, map_mul, ← hc, mul_assoc, IsLocalization.mk'_spec]
    by_cases ha : a ∈ P
    · exfalso
      have h3 := congrArg ν (hK1 h1)
      rw [map_mul, hunit _ s.2] at h3
      have h6 : ν (algebraMap S K x / algebraMap S K y) * ν (algebraMap S K a) < 1 :=
        lt_of_le_of_lt (mul_le_of_le_one_left' hz) (hlt a ha)
      exact h6.ne h3
    · exact ⟨s, a, ha, hK1 h1⟩
  · have h1 : y * a = x * s := by
      apply hinj
      rw [map_mul, map_mul, ← hc, mul_assoc, IsLocalization.mk'_spec]
    exact ⟨a, s, s.2, hK2 h1⟩

theorem prime_not_stable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n p : ℕ) (G : GAtP p) (A : LocAt F E n G) (J : Matrix (Fin n) (Fin n) E) [Fact p.Prime], LocGood σ J A → LocInt A → SplAlg A → ∀ v (P : HeightOneSpectrum (𝓞 E)), PrimeOf p (G.P.W v) (A.iw v) P → ∃ a b : 𝓞 E, (b : E) = σ (a : E) ∧ a ∈ P.asIdeal ∧ b ∉ P.asIdeal := by
  intro F E _ _ _ _ _ σ n p G A J _ hG hI hS v P hP
  classical
  haveI hfr := (G.P.setting v).frac_alt
  have hinjW : Function.Injective (algebraMap (G.P.W v) (G.P.Qq v)) := IsFractionRing.injective _ _
  let ν : Valuation E ℤᵐ⁰ := (Valued.v : Valuation ((A.pl v).1.adicCompletion F) ℤᵐ⁰).comap (A.phE v)
  have hν : ∀ x : E, ν x = Valued.v ((A.spl v (x ⊗ₜ[F] (1 : (A.pl v).1.adicCompletion F))).1) := by
    intro x; rfl
  have hνiw : ∀ x : E, ν x = Valued.v (A.eQ v (A.iw v x)) := by
    intro x; simp [ν, LocAt.iw]

  have hleW : ∀ y : G.P.W v, Valued.v (A.eQ v (algebraMap _ _ y)) ≤ 1 := fun y => (hI v _).1 ⟨y, rfl⟩
  have hunitW : ∀ y : G.P.W v, IsUnit y → Valued.v (A.eQ v (algebraMap _ _ y)) = 1 := by
    intro y hy
    obtain ⟨z, hz⟩ := hy.exists_right_inv
    have h1 : Valued.v (A.eQ v (algebraMap _ _ y)) * Valued.v (A.eQ v (algebraMap _ _ z)) = 1 := by
      rw [← Valuation.map_mul, ← map_mul, ← map_mul, hz, map_one, map_one, Valuation.map_one]
    refine le_antisymm (hleW y) ?_
    calc (1 : ℤᵐ⁰) = _ := h1.symm
      _ ≤ Valued.v (A.eQ v (algebraMap _ _ y)) * 1 := by gcongr; exact hleW z
      _ = _ := mul_one _
  have hnunitW : ∀ y : G.P.W v, ¬ IsUnit y → Valued.v (A.eQ v (algebraMap _ _ y)) < 1 := by
    intro y hy
    refine lt_of_le_of_ne (hleW y) (fun h1 => hy ?_)
    have hq0 : A.eQ v (algebraMap _ _ y) ≠ 0 := by
      intro h0; rw [h0, Valuation.map_zero] at h1; exact zero_ne_one h1
    obtain ⟨z, hz⟩ := (hI v ((A.eQ v).symm (A.eQ v (algebraMap _ _ y))⁻¹)).2 (by
      rw [RingEquiv.apply_symm_apply]
      show Valued.v (A.eQ v (algebraMap _ _ y))⁻¹ ≤ 1
      rw [map_inv₀, h1, inv_one])
    refine IsUnit.of_mul_eq_one z (hinjW ?_)
    rw [map_mul, map_one, hz]
    apply (A.eQ v).injective
    rw [map_mul, RingEquiv.apply_symm_apply, map_one]
    exact mul_inv_cancel₀ hq0
  have hdvdW : ∀ y : G.P.W v, (p : G.P.W v) ∣ y ↔ ¬ IsUnit y := by
    intro y
    have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 (G.P.setting v).p_unif
    rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, hmax, Ideal.mem_span_singleton]

  have hle : ∀ a : 𝓞 E, ν (algebraMap (𝓞 E) E a) ≤ 1 := by
    intro a
    obtain ⟨y, hy, -⟩ := hP a
    change ν (a : E) ≤ 1
    rw [hνiw, hy]; exact hleW y
  have hmem : ∀ a : 𝓞 E, a ∈ P.asIdeal ↔ ν (a : E) < 1 := by
    intro a
    obtain ⟨y, hy, hiff⟩ := hP a
    rw [hiff, hdvdW, hνiw, hy]
    exact ⟨hnunitW y, fun h hu => (ne_of_lt h) (hunitW y hu)⟩
  have hunit : ∀ s : 𝓞 E, s ∉ P.asIdeal → ν (s : E) = 1 :=
    fun s hs => le_antisymm (hle s) (not_lt.1 (fun h => hs ((hmem s).2 h)))

  have hσ : ∀ x : E, ν (σ x) = Valued.v ((A.spl v (x ⊗ₜ[F] (1 : (A.pl v).1.adicCompletion F))).2) := by
    intro x
    have h := hG.sig v (x ⊗ₜ[F] (1 : (A.pl v).1.adicCompletion F))
    have h2 : sigR σ ((A.pl v).1.adicCompletion F) (x ⊗ₜ[F] (1 : (A.pl v).1.adicCompletion F)) =
        (σ x) ⊗ₜ[F] (1 : (A.pl v).1.adicCompletion F) := by
      simp [sigR]
    rw [h2] at h
    rw [hν, h]
    simp [swapR]
  by_contra hcon
  push_neg at hcon
  let σO : 𝓞 E →+* 𝓞 E := NumberField.RingOfIntegers.mapRingHom (σ : E →+* E)
  have hσP : ∀ a : 𝓞 E, a ∈ P.asIdeal → σO a ∈ P.asIdeal := fun a ha => hcon a (σO a) rfl ha
  have hσs : ∀ s : 𝓞 E, s ∉ P.asIdeal → σO s ∉ P.asIdeal := by
    intro s hs hs'
    obtain ⟨t, i, hi, hti⟩ := P.isMaximal.exists_inv hs
    have h1 : σO t * σO s + σO i = 1 := by rw [← map_mul, ← map_add, hti, map_one]
    have h2 : (1 : 𝓞 E) ∈ P.asIdeal := h1 ▸ add_mem (Ideal.mul_mem_left _ _ hs') (hσP i hi)
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h2)

  obtain ⟨x, hx1, hx2⟩ := approx (HeightOneSpectrum.denseRange_algebraMap F (A.pl v).1) (A.spl v) (hS v)
    ((A.spl v).symm (0, 1)) 1 one_ne_zero
  rw [RingEquiv.apply_symm_apply, Valuation.map_one] at hx1 hx2
  have hνx : ν x < 1 := by rw [hν]; simpa using hx1
  have hν2 : Valued.v ((A.spl v (x ⊗ₜ[F] (1 : (A.pl v).1.adicCompletion F))).2) = 1 := by
    have := Valuation.map_eq_of_sub_lt (Valued.v : Valuation ((A.pl v).1.adicCompletion F) ℤᵐ⁰)
      (x := 1) (by simpa using hx2)
    simpa using this
  obtain ⟨a, s, hs, hxs⟩ := exists_frac (hp := P.isPrime) ν P.asIdeal P.ne_bot hle
    (fun a ha => (hmem a).1 ha) x hνx.le
  have hxs' : x * (s : E) = (a : E) := hxs
  have ha : a ∈ P.asIdeal := by
    rw [hmem, ← hxs', Valuation.map_mul, hunit s hs, mul_one]; exact hνx
  have h2a : Valued.v ((A.spl v ((a : E) ⊗ₜ[F] (1 : (A.pl v).1.adicCompletion F))).2) < 1 := by
    rw [← hσ]; exact (hmem (σO a)).1 (hσP a ha)
  have h2s : Valued.v ((A.spl v ((s : E) ⊗ₜ[F] (1 : (A.pl v).1.adicCompletion F))).2) = 1 := by
    rw [← hσ]; exact hunit (σO s) (hσs s hs)
  have hprod : (A.spl v (x ⊗ₜ[F] (1 : (A.pl v).1.adicCompletion F))).2 *
      (A.spl v ((s : E) ⊗ₜ[F] (1 : (A.pl v).1.adicCompletion F))).2 =
      (A.spl v ((a : E) ⊗ₜ[F] (1 : (A.pl v).1.adicCompletion F))).2 := by
    rw [← Prod.snd_mul, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hxs']
  have h3 := congrArg (Valued.v : Valuation ((A.pl v).1.adicCompletion F) ℤᵐ⁰) hprod
  rw [Valuation.map_mul, hν2, h2s, one_mul] at h3
  exact (ne_of_lt h2a) h3.symm

end GlobalTheory.XcSplit
