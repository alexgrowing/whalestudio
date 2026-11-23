import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.EffCartierIffForallCartAt
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocPrincipalSpan
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

theorem LocPrincipal.exists_pow_mul_sq {A : Type} [CommRing A] {I : Ideal A} {t f : A}
    (h : ∀ g ∈ I, ∃ n : ℕ, t ^ n * g ∈ Ideal.span {f}) {x : A} (hx : x ∈ I ^ 2) :
    ∃ N : ℕ, ∃ c : A, t ^ N * x = c * (f * f) := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro g hg k hk
    obtain ⟨n, hn⟩ := h g hg
    obtain ⟨m, hm⟩ := h k hk
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hn
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hm
    refine ⟨n + m, a * b, ?_⟩
    calc t ^ (n + m) * (g * k) = (t ^ n * g) * (t ^ m * k) := by ring
      _ = a * b * (f * f) := by rw [← ha, ← hb]; ring
  · rintro x y ⟨N, c, hc⟩ ⟨M, d, hd⟩
    refine ⟨N + M, t ^ M * c + t ^ N * d, ?_⟩
    calc t ^ (N + M) * (x + y) = t ^ M * (t ^ N * x) + t ^ N * (t ^ M * y) := by ring
      _ = _ := by rw [hc, hd]; ring

theorem LocPrincipal.smul_toCotangent_ne_zero {A : Type} [CommRing A] [IsDomain A] {I p : Ideal A}
    [p.IsPrime] (hIp : I ≤ p) {t f : A} (ht : t ∉ p) (hf : f ∈ I) (hf0 : f ≠ 0)
    (h : ∀ g ∈ I, ∃ n : ℕ, t ^ n * g ∈ Ideal.span {f}) {s : A} (hs : s ∉ p) :
    s • I.toCotangent ⟨f, hf⟩ ≠ 0 := by
  intro h0
  rw [← map_smul I.toCotangent s ⟨f, hf⟩, Ideal.toCotangent_eq_zero] at h0
  have h0' : s * f ∈ I ^ 2 := by simpa [smul_eq_mul] using h0
  obtain ⟨N, c, hc⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.LocPrincipal.exists_pow_mul_sq h h0'
  have hcancel : t ^ N * s = c * f := by
    apply mul_right_cancel₀ hf0
    calc t ^ N * s * f = t ^ N * (s * f) := by ring
      _ = c * (f * f) := hc
      _ = c * f * f := by ring
  have hmem : t ^ N * s ∈ p := by
    rw [hcancel]
    exact hIp (I.mul_mem_left c hf)
  rcases Ideal.IsPrime.mem_or_mem ‹p.IsPrime› hmem with h1 | h1
  · exact ht (Ideal.IsPrime.mem_of_pow_mem ‹p.IsPrime› N h1)
  · exact hs h1

theorem LocPrincipal.exists_pow_smul_eq {A : Type} [CommRing A] {I : Ideal A} {t f : A}
    (hf : f ∈ I) (h : ∀ g ∈ I, ∃ n : ℕ, t ^ n * g ∈ Ideal.span {f}) (m : I.Cotangent) :
    ∃ (n : ℕ) (c : A), t ^ n • m = c • I.toCotangent ⟨f, hf⟩ := by
  obtain ⟨g, rfl⟩ := I.toCotangent_surjective m
  obtain ⟨n, hn⟩ := h g g.2
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hn
  refine ⟨n, c, ?_⟩
  rw [← map_smul I.toCotangent (t ^ n) g, ← map_smul I.toCotangent c ⟨f, hf⟩]
  congr 1
  ext
  simp [smul_eq_mul, hc]

theorem rankAtStalk_cotangent_eq_one {A : Type} [CommRing A] [IsDomain A] (I : Ideal A)
    [Module.Finite (A ⧸ I) I.Cotangent] [Module.Projective (A ⧸ I) I.Cotangent]
    (P : PrimeSpectrum (A ⧸ I))
    (hP : LocPrincipal I (P.asIdeal.comap (Ideal.Quotient.mk I))) :
    Module.rankAtStalk I.Cotangent P = 1 := by
  obtain ⟨t, f, ht, hf, hf0, h⟩ := hP
  have htP : Ideal.Quotient.mk I t ∉ P.asIdeal := fun H => ht (Ideal.mem_comap.mpr H)
  have hIq : I ≤ P.asIdeal.comap (Ideal.Quotient.mk I) := fun g hg => by
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hg]
    exact zero_mem _
  have hsmul : ∀ (a : A) (m : I.Cotangent), Ideal.Quotient.mk I a • m = a • m := fun a m => by
    rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
  have hspan : Submodule.span (Localization.AtPrime P.asIdeal)
      {LocalizedModule.mk (I.toCotangent ⟨f, hf⟩) (1 : P.asIdeal.primeCompl)} = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro y
    induction y using LocalizedModule.induction_on with
    | h m s =>
      obtain ⟨n, c, hc⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.LocPrincipal.exists_pow_smul_eq hf h m
      have htn : (Ideal.Quotient.mk I t) ^ n ∈ P.asIdeal.primeCompl :=
        Ideal.mem_primeCompl_iff.mpr fun H => htP (Ideal.IsPrime.mem_of_pow_mem P.isPrime n H)
      have key : Ideal.Quotient.mk I c • I.toCotangent ⟨f, hf⟩ =
          (⟨_, htn⟩ : P.asIdeal.primeCompl) • m := by
        rw [Submonoid.mk_smul, hsmul, ← map_pow, hsmul]
        exact hc.symm
      rw [Submodule.mem_span_singleton]
      refine ⟨Localization.mk (Ideal.Quotient.mk I c) (⟨_, htn⟩ * s), ?_⟩
      rw [LocalizedModule.mk_smul_mk, key, mul_one, LocalizedModule.mk_cancel_common_left]
  have hx : LocalizedModule.mk (I.toCotangent ⟨f, hf⟩) (1 : P.asIdeal.primeCompl) ≠ 0 := by
    intro H
    rw [← LocalizedModule.zero_mk (1 : P.asIdeal.primeCompl), LocalizedModule.mk_eq] at H
    obtain ⟨⟨u, hu⟩, hu0⟩ := H
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective u
    simp only [one_smul, smul_zero, Submonoid.mk_smul] at hu0
    rw [hsmul] at hu0
    exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.LocPrincipal.smul_toCotangent_ne_zero hIq ht hf hf0 h
      (fun hs => Ideal.mem_primeCompl_iff.mp hu (Ideal.mem_comap.mp hs)) hu0
  have hfree : Module.Free (Localization.AtPrime P.asIdeal)
      (LocalizedModule P.asIdeal.primeCompl I.Cotangent) := by
    haveI : Module.Flat (A ⧸ I) I.Cotangent := Module.Flat.of_projective
    have hmem : P ∈ Module.freeLocus (A ⧸ I) I.Cotangent := by
      rw [Module.freeLocus_eq_univ]
      trivial
    exact Module.mem_freeLocus.mp hmem
  haveI : Module.Finite (Localization.AtPrime P.asIdeal)
      (LocalizedModule P.asIdeal.primeCompl I.Cotangent) :=
    Module.Finite.of_fg_top ⟨{LocalizedModule.mk (I.toCotangent ⟨f, hf⟩) 1}, by
      rw [Finset.coe_singleton]
      exact hspan⟩
  haveI := nontrivial_of_ne _ _ hx
  have hle : Module.finrank (Localization.AtPrime P.asIdeal)
      (LocalizedModule P.asIdeal.primeCompl I.Cotangent) ≤ 1 := by
    have := finrank_le_of_span_eq_top (R := Localization.AtPrime P.asIdeal)
      (v := fun _ : Unit => LocalizedModule.mk (I.toCotangent ⟨f, hf⟩)
        (1 : P.asIdeal.primeCompl)) (by rw [Set.range_const]; exact hspan)
    simpa using this
  have hpos : 0 < Module.finrank (Localization.AtPrime P.asIdeal)
      (LocalizedModule P.asIdeal.primeCompl I.Cotangent) :=
    (Module.finrank_pos_iff_of_free _ _).mpr inferInstance
  show Module.finrank (Localization.AtPrime P.asIdeal)
    (LocalizedModule P.asIdeal.primeCompl I.Cotangent) = 1
  omega

end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
