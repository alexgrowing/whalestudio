import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockValAe
import Development.DiscreteGroups.GlobalIrreducibility.DzIneEq

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
open scoped Pointwise

namespace DiscreteGroups.sglob.DzType

theorem isTotallyComplex_of_algebra {E L : Type} [Field E] [NumberField E] [IsTotallyComplex E] [Field L]
    [NumberField L] [Algebra E L] : IsTotallyComplex L :=
  NumberField.isTotallyComplex_of_algebra E L

set_option linter.deprecated false in

theorem unram_place {E L Ω : Type} [Field E] [NumberField E] [Field L] [NumberField L] [Field Ω] [Algebra E L]
    [Algebra E Ω] [Algebra L Ω] [IsScalarTower E L Ω] [IsAlgClosure E Ω] [IsAlgClosure L Ω] (g : ℕ) [Fact g.Prime]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (v : HeightOneSpectrum (𝓞 L))
    (hv : IsPlaceOver A v) (hL : IsLocalExt L h)
    (hI : ∀ σ ∈ Ine (F := E) A, ∀ x : L, (σ : G E Ω) (algebraMap L Ω x) = algebraMap L Ω x)
    (hgw : ((g : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2) (hN : normV w = g) :
    ((g : ℕ) : 𝓞 L) ∈ v.asIdeal ∧ ((g : ℕ) : 𝓞 L) ∉ v.asIdeal ^ 2 ∧ normV v = g ^ Module.finrank E L := by
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : w.asIdeal.IsMaximal := w.isMaximal

  have hvw : ∀ x : 𝓞 E, x ∈ w.asIdeal ↔ algebraMap (𝓞 E) (𝓞 L) x ∈ v.asIdeal := fun x => by
    rw [← h x, ← hv (algebraMap (𝓞 E) (𝓞 L) x)]
    have e1 : algebraMap L Ω ((algebraMap (𝓞 E) (𝓞 L) x : 𝓞 L) : L) = algebraMap E Ω (x : E) :=
      (IsScalarTower.algebraMap_apply E L Ω (x : E)).symm
    rw [e1]
  have : v.asIdeal.LiesOver w.asIdeal := ⟨Ideal.ext fun x => (hvw x).trans Iff.rfl⟩
  have hgmem : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal := natCast_mem_of_normV w g 1 Nat.one_pos (by rw [hN, pow_one])
  have hgv : ((g : ℕ) : 𝓞 L) ∈ v.asIdeal := by
    have := (hvw _).1 hgmem
    rwa [map_natCast] at this

  set f := w.asIdeal.inertiaDeg' v.asIdeal with hf_def
  have hnorm : normV v = normV w ^ f := by
    have hn : ∀ {K : Type} [Field K] [NumberField K] (u : HeightOneSpectrum (𝓞 K)), normV u = Ideal.absNorm u.asIdeal :=
      fun u => by rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
    rw [hn, hn]
    exact Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver v.asIdeal w.asIdeal w.isPrime w.ne_bot
  have hf0 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with hf | hf
    · have := one_lt_normV v
      rw [hnorm, hf, pow_zero] at this
      exact absurd this (lt_irrefl 1)
    · exact hf

  let S : Subgroup (Weil h) :=
    { carrier := {τ | ∀ x : L, (τ : G E Ω) (algebraMap L Ω x) = algebraMap L Ω x}
      mul_mem' := fun {a b} ha hb x => by
        show ((a * b : Weil h) : G E Ω) (algebraMap L Ω x) = _
        rw [Subgroup.coe_mul, AlgEquiv.mul_apply, hb x, ha x]
      one_mem' := fun x => rfl
      inv_mem' := fun {a} ha x => by
        show ((a⁻¹ : Weil h) : G E Ω) (algebraMap L Ω x) = _
        rw [Subgroup.coe_inv]
        conv_lhs => rw [← ha x]
        rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply] }
  have hS : ∀ τ : Weil h, τ ∈ S ↔ ∀ x : L, (τ : G E Ω) (algebraMap L Ω x) = algebraMap L Ω x := fun _ => Iff.rfl
  have hIS : ∀ τ : Weil h, deg τ = 0 → τ ∈ S := fun τ hτ x => hI _ (deg_eq_zero_iff.1 hτ) x

  obtain ⟨φ, hφ⟩ := ReciprocityTheory.Gal.exists_isFrob hv
  have hφA : ActsAs A (normV w) (AlgEquiv.restrictScalars E φ) f 0 := by
    refine ⟨?_, fun x hx => ?_⟩
    · show AlgEquiv.restrictScalars E φ • A = A
      have hd : φ • A = A := hφ.1
      ext y
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      conv_rhs => rw [← hd]
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      exact Iff.rfl
    · have := hφ.2 x hx
      rw [hnorm] at this
      simpa using this
  let φW : Weil h := ⟨_, ⟨f, 0, hφA⟩⟩
  have hφdeg : deg φW = f := by rw [deg_eq hφA]; simp
  have hφS : φW ∈ S := fun x => φ.commutes x

  let Φ : Weil h → (L →ₐ[E] Ω) := fun τ => ((τ : G E Ω) : Ω →ₐ[E] Ω).comp (IsScalarTower.toAlgHom E L Ω)
  have hΦS : ∀ τ s : Weil h, s ∈ S → Φ (τ * s) = Φ τ := fun τ s hs => AlgHom.ext fun x => by
    show ((τ * s : Weil h) : G E Ω) (algebraMap L Ω x) = (τ : G E Ω) (algebraMap L Ω x)
    rw [Subgroup.coe_mul, AlgEquiv.mul_apply, hs x]
  have hΦsurj : ∀ ψ : L →ₐ[E] Ω, ∃ τ : Weil h, Φ τ = ψ := fun ψ => by
    let σ : G E Ω := AlgEquiv.ofBijective (ψ.liftNormal Ω) (Algebra.IsAlgebraic.algHom_bijective _)
    obtain ⟨τ, hτ⟩ := hL σ
    refine ⟨τ, AlgHom.ext fun x => ?_⟩
    show (τ : G E Ω) (algebraMap L Ω x) = ψ x
    rw [hτ x]
    show ψ.liftNormal Ω (algebraMap L Ω x) = ψ x
    rw [AlgHom.liftNormal_commutes]
    rfl

  let φ₀ := frob h
  have hφ₀f : φ₀ ^ (f : ℤ) ∈ S := by
    have hk : deg (φW⁻¹ * φ₀ ^ (f : ℤ)) = 0 := by
      rw [deg_mul, deg_inv, deg_zpow, hφdeg, deg_frob]; ring
    have := S.mul_mem hφS (hIS _ hk)
    rwa [mul_inv_cancel_left] at this
  have hcover : ∀ ψ : L →ₐ[E] Ω, ∃ j : Fin f, Φ (φ₀ ^ (j : ℕ)) = ψ := fun ψ => by
    obtain ⟨τ, rfl⟩ := hΦsurj ψ
    obtain ⟨ι, hι⟩ := exists_eq_zpow_mul (deg_frob (h := h)) τ
    have hfz : (0 : ℤ) < f := by exact_mod_cast hf0
    set d := deg τ
    have hd : d = d % f + f * (d / f) := by have := Int.emod_def d f; linarith
    have hj0 : 0 ≤ d % f := Int.emod_nonneg d hfz.ne'
    have hjf : d % f < f := Int.emod_lt_of_pos d hfz
    refine ⟨⟨(d % f).toNat, by omega⟩, ?_⟩
    show Φ (φ₀ ^ (d % f).toNat) = Φ τ
    have hs : (φ₀ ^ (f : ℤ)) ^ (d / f) * ineIncl h ι ∈ S :=
      S.mul_mem (S.zpow_mem hφ₀f _) (hIS _ (deg_ineIncl ι))
    have e1 : φ₀ ^ d = φ₀ ^ ((d % f).toNat : ℕ) * (φ₀ ^ (f : ℤ)) ^ (d / f) := by
      conv_lhs => rw [hd]
      rw [zpow_add, zpow_mul, ← zpow_natCast, Int.toNat_of_nonneg hj0]
    have e : τ = φ₀ ^ ((d % f).toNat : ℕ) * ((φ₀ ^ (f : ℤ)) ^ (d / f) * ineIncl h ι) := by
      rw [← mul_assoc, ← e1]
      exact hι
    have key : Φ τ = Φ (φ₀ ^ ((d % f).toNat : ℕ)) := by
      rw [e]
      exact hΦS _ _ hs
    exact key.symm
  have hcard : Module.finrank E L ≤ f := by
    have h1 := Fintype.card_le_of_surjective (fun j : Fin f => Φ (φ₀ ^ (j : ℕ))) hcover
    rw [AlgHom.card] at h1
    simpa using h1

  have hw0 : w.asIdeal ≠ ⊥ := w.ne_bot
  have hmem : v.asIdeal ∈ IsDedekindDomain.primesOverFinset w.asIdeal (𝓞 L) :=
    (IsDedekindDomain.mem_primesOverFinset_iff hw0 _).2 ⟨v.isPrime, inferInstance⟩
  have hsum := Ideal.sum_ramification_inertia (𝓞 L) E L hw0
  have hle : Ideal.ramificationIdx' w.asIdeal v.asIdeal * f ≤ Module.finrank E L := by
    rw [← hsum]
    exact Finset.single_le_sum (f := fun P => Ideal.ramificationIdx' w.asIdeal P * Ideal.inertiaDeg' w.asIdeal P)
      (fun _ _ => Nat.zero_le _) hmem
  have he0 : Ideal.ramificationIdx' w.asIdeal v.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver v.asIdeal hw0
  have hfn : f = Module.finrank E L := by
    have : f ≤ Ideal.ramificationIdx' w.asIdeal v.asIdeal * f := Nat.le_mul_of_pos_left f (Nat.pos_of_ne_zero he0)
    omega
  have he1 : Ideal.ramificationIdx' w.asIdeal v.asIdeal = 1 := by
    rw [hfn] at hle
    have hn0 : 0 < Module.finrank E L := Module.finrank_pos
    have : Ideal.ramificationIdx' w.asIdeal v.asIdeal ≤ 1 := by
      by_contra hc
      rw [not_le] at hc
      have := Nat.mul_le_mul_right (Module.finrank E L) hc
      omega
    omega
  refine ⟨hgv, fun hg2 => ?_, by rw [hnorm, hN, hfn]⟩

  obtain ⟨J, hJ⟩ : w.asIdeal ∣ Ideal.span {((g : ℕ) : 𝓞 E)} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hgmem)
  have hJw : ¬ J ≤ w.asIdeal := fun hJle => hgw (by
    have : Ideal.span {((g : ℕ) : 𝓞 E)} ≤ w.asIdeal ^ 2 := by
      rw [hJ, pow_two]; exact Ideal.mul_mono_right hJle
    exact this (Ideal.mem_span_singleton_self _))
  have hmapJ : ¬ v.asIdeal ∣ Ideal.map (algebraMap (𝓞 E) (𝓞 L)) J := fun hd => hJw (by
    intro y hy
    have := Ideal.dvd_iff_le.1 hd (Ideal.mem_map_of_mem _ hy)
    exact (hvw y).2 this)
  have hdiv : v.asIdeal ^ 2 ∣ Ideal.map (algebraMap (𝓞 E) (𝓞 L)) w.asIdeal *
      Ideal.map (algebraMap (𝓞 E) (𝓞 L)) J := by
    rw [← Ideal.map_mul, ← hJ, Ideal.map_span, Set.image_singleton, map_natCast]
    exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hg2)
  have hprime : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.isPrime
  have hw2 := Ideal.dvd_iff_le.1 (hprime.pow_dvd_of_dvd_mul_right 2 hmapJ hdiv)

  by_cases hb : ∀ k : ℕ, Ideal.map (algebraMap (𝓞 E) (𝓞 L)) w.asIdeal ≤ v.asIdeal ^ k
  · have := Ideal.ramificationIdx'_eq_zero (p := w.asIdeal) (P := v.asIdeal) fun k => ⟨k + 1, hb (k + 1), by omega⟩
    omega
  · obtain ⟨k0, hk0⟩ := not_forall.1 hb
    have hbdd : BddAbove {k | Ideal.map (algebraMap (𝓞 E) (𝓞 L)) w.asIdeal ≤ v.asIdeal ^ k} := by
      refine ⟨k0, fun k hk => ?_⟩
      by_contra hlt
      rw [not_le] at hlt
      exact hk0 (hk.trans (Ideal.pow_le_pow_right hlt.le))
    have h2 : 2 ≤ Ideal.ramificationIdx' w.asIdeal v.asIdeal := le_csSup hbdd hw2
    omega

end DiscreteGroups.sglob.DzType
