import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.NormLeOneOfInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ResEqOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocFlat
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocDim

set_option linter.overlappingInstances false

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

private theorem int_of_norm {l : ℕ} [Fact l.Prime] (z : Qbar l) (hz : ‖z‖ ≤ 1) :
    ∃ f : Polynomial ℤ_[l], f.Monic ∧ Polynomial.aeval z f = 0 := by
  have hi : IsIntegral ℚ_[l] z := Algebra.IsIntegral.isIntegral z
  have hm : (minpoly ℚ_[l] z).Monic := minpoly.monic hi
  have h1 : spectralValue (minpoly ℚ_[l] z) ≤ 1 := by
    rw [← PadicAlgCl.spectralNorm_eq l z] at hz
    exact hz
  have h2 := (spectralValue_le_one_iff hm).1 h1
  have hl : minpoly ℚ_[l] z ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, h2 n⟩, rfl⟩
  obtain ⟨f, hf, -, hfm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hm
  refine ⟨f, hfm, ?_⟩
  rw [← Polynomial.aeval_map_algebraMap ℚ_[l], hf, minpoly.aeval]

private theorem int_pt {l : ℕ} [Fact l.Prime] {D : Type} [CommRing D] (ξ : D →+* Qbar l) (h : ∀ a, ‖ξ a‖ ≤ 1)
    (φ : ℤ_[l] →+* D) (hφ : ∀ t, ξ (φ t) = algebraMap ℤ_[l] (Qbar l) t) (a : D) :
    ∃ f : Polynomial ℤ_[l], f.Monic ∧ ξ (f.eval₂ φ a) = 0 := by
  obtain ⟨f, hf, h0⟩ := int_of_norm (ξ a) (h a)
  refine ⟨f, hf, ?_⟩
  rw [Polynomial.hom_eval₂, ← h0, Polynomial.aeval_def]
  congr 1
  exact RingHom.ext hφ

private def nx {l : ℕ} [Fact l.Prime] {D : Type} [CommRing D] (ξ : D →+* Qbar l) (h : ∀ a, ‖ξ a‖ ≤ 1) : Ideal D where
  carrier := {a | ‖ξ a‖ < 1}
  add_mem' {a b} ha hb := by
    show ‖ξ (a + b)‖ < 1
    rw [map_add]
    exact lt_of_le_of_lt (PadicAlgCl.isNonarchimedean l _ _) (max_lt ha hb)
  zero_mem' := by
    show ‖ξ 0‖ < 1
    simp
  smul_mem' c a ha := by
    show ‖ξ (c • a)‖ < 1
    rw [smul_eq_mul, map_mul, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (h c)) ha

private theorem nx_prime {l : ℕ} [Fact l.Prime] {D : Type} [CommRing D] (ξ : D →+* Qbar l) (h : ∀ a, ‖ξ a‖ ≤ 1) :
    (nx ξ h).IsPrime := by
  refine ⟨fun e => ?_, fun {a b} hab => ?_⟩
  · have h1 : ‖ξ 1‖ < 1 := (Ideal.eq_top_iff_one _).1 e
    simp at h1
  · by_contra hn
    rw [not_or] at hn
    have ha : ‖ξ a‖ = 1 := le_antisymm (h a) (not_lt.1 hn.1)
    have hb : ‖ξ b‖ = 1 := le_antisymm (h b) (not_lt.1 hn.2)
    have h1 : ‖ξ (a * b)‖ < 1 := hab
    rw [map_mul, norm_mul, ha, hb, one_mul] at h1
    exact lt_irrefl _ h1

private theorem norm_l_lt {l : ℕ} [Fact l.Prime] : ‖(l : Qbar l)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)) l, norm_algebraMap']
  exact Padic.norm_p_lt_one

private theorem nx_max {l : ℕ} [Fact l.Prime] {D : Type} [CommRing D] (ξ : D →+* Qbar l) (h : ∀ a, ‖ξ a‖ ≤ 1)
    (φ : ℤ_[l] →+* D) (hφ : ∀ t, ξ (φ t) = algebraMap ℤ_[l] (Qbar l) t) : (nx ξ h).IsMaximal := by
  haveI hpr := nx_prime ξ h
  haveI hnt : Nontrivial (D ⧸ nx ξ h) := Ideal.Quotient.nontrivial_iff.2 hpr.ne_top
  haveI hdom : IsDomain (D ⧸ nx ξ h) := Ideal.Quotient.isDomain _
  haveI hbp : (⊥ : Ideal (D ⧸ nx ξ h)).IsPrime := Ideal.bot_prime
  let f : ℤ_[l] →+* D ⧸ nx ξ h := (Ideal.Quotient.mk (nx ξ h)).comp φ
  have hf : f.IsIntegral := fun z => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨p, hp, h0⟩ := int_pt ξ h φ hφ a
    refine ⟨p, hp, ?_⟩
    have e : p.eval₂ f (Ideal.Quotient.mk (nx ξ h) a) = Ideal.Quotient.mk (nx ξ h) (p.eval₂ φ a) :=
      (Polynomial.hom_eval₂ p φ (Ideal.Quotient.mk (nx ξ h)) a).symm
    rw [e, Ideal.Quotient.eq_zero_iff_mem]
    show ‖ξ _‖ < 1
    rw [h0]
    simp
  have hk : (maximalIdeal ℤ_[l]) ≤ (⊥ : Ideal (D ⧸ nx ξ h)).comap f := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_le, Set.singleton_subset_iff]
    show f (l : ℤ_[l]) ∈ (⊥ : Ideal (D ⧸ nx ξ h))
    rw [Ideal.mem_bot, map_natCast, ← map_natCast (Ideal.Quotient.mk (nx ξ h)), Ideal.Quotient.eq_zero_iff_mem]
    show ‖ξ (l : D)‖ < 1
    rw [map_natCast]
    exact norm_l_lt
  have hm : ((⊥ : Ideal (D ⧸ nx ξ h)).comap f).IsMaximal := by
    rw [← (maximalIdeal.isMaximal ℤ_[l]).eq_of_le (Ideal.comap_ne_top _ hbp.ne_top) hk]
    exact maximalIdeal.isMaximal _
  haveI := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' f hf ⊥ hm
  have h2 := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk (nx ξ h)) (K := (⊥ : Ideal (D ⧸ nx ξ h)))
    Ideal.Quotient.mk_surjective
  rwa [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at h2

private theorem td_zero {l : ℕ} [Fact l.Prime] {B A : Type} [CommRing B] [CommRing A] [Algebra B A] (q : Ideal A)
    [q.IsPrime] (ψ : ℤ_[l] →+* B)
    (h : ∀ a, ∃ f : Polynomial ℤ_[l], f.Monic ∧ f.eval₂ ((algebraMap B A).comp ψ) a ∈ q) :
    Algebra.trdeg (B ⧸ q.comap (algebraMap B A)) (A ⧸ q) = 0 := by
  haveI hcp : (q.comap (algebraMap B A)).IsPrime := Ideal.IsPrime.comap _
  haveI hnt : Nontrivial (B ⧸ q.comap (algebraMap B A)) := Ideal.Quotient.nontrivial_iff.2 hcp.ne_top
  haveI : Algebra.IsIntegral (B ⧸ q.comap (algebraMap B A)) (A ⧸ q) := ⟨fun z => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨p, hp, h0⟩ := h a
    refine ⟨p.map ((Ideal.Quotient.mk _).comp ψ), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have e := Polynomial.hom_eval₂ p ((algebraMap B A).comp ψ) (Ideal.Quotient.mk q) a
    rw [Ideal.Quotient.eq_zero_iff_mem.2 h0] at e
    exact e.symm⟩
  haveI : Algebra.IsAlgebraic (B ⧸ q.comap (algebraMap B A)) (A ⧸ q) := Algebra.IsIntegral.isAlgebraic
  exact trdeg_eq_zero

private theorem down {A R : Type} [CommRing A] [CommRing R] [IsLocalRing R] (ι : A →+* R) (hf : ι.Flat)
    (x q : Ideal A) [x.IsPrime] [q.IsPrime] (hq : q ≤ x) (hl : (maximalIdeal R).comap ι = x) :
    ∃ Q : Ideal R, Q.IsPrime ∧ Q.comap ι = q ∧ Q ∈ (q.map ι).minimalPrimes := by
  letI := ι.toAlgebra
  haveI : Module.Flat A R := hf
  haveI : Algebra.HasGoingDown A R := Algebra.HasGoingDown.of_flat
  haveI : (maximalIdeal R).LiesOver x := ⟨hl.symm⟩
  obtain ⟨P, -, hp, hlo⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := q) (q := x) (maximalIdeal R) hq
  have hc : P.comap ι = q := hlo.over.symm
  have hne : q.map ι ≤ P := Ideal.map_le_iff_le_comap.2 hc.ge
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le hne
  exact ⟨Q, hQ.1.1, le_antisymm (hc ▸ Ideal.comap_mono hQP) (Ideal.map_le_iff_le_comap.1 hQ.1.2), hQ⟩

private theorem dim_ge {R : Type} [CommRing R] [IsLocalRing R] (Q : Ideal R) [Q.IsPrime] (z : R)
    (hz : z ∈ maximalIdeal R) (hn : z ∉ Q) : 1 ≤ ringKrullDim (R ⧸ Q) := by
  have hp : ((maximalIdeal R).map (Ideal.Quotient.mk Q)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
  haveI hnt : Nontrivial (R ⧸ Q) := Ideal.Quotient.nontrivial_iff.2 (Ideal.IsPrime.ne_top inferInstance)
  haveI hdom : IsDomain (R ⧸ Q) := Ideal.Quotient.isDomain _
  have h0 : (0 : WithBot ℕ∞) < ringKrullDim (R ⧸ Q) := by
    refine Order.krullDim_pos_iff.2 ⟨⟨⊥, Ideal.bot_prime⟩, ⟨_, hp⟩, ?_⟩
    refine (PrimeSpectrum.asIdeal_lt_asIdeal _ _).1 (bot_lt_iff_ne_bot.2 fun e => ?_)
    have h1 : Ideal.Quotient.mk Q z ∈ (maximalIdeal R).map (Ideal.Quotient.mk Q) := Ideal.mem_map_of_mem _ hz
    have e' : (maximalIdeal R).map (Ideal.Quotient.mk Q) = ⊥ := e
    rw [e', Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at h1
    exact hn h1
  generalize ringKrullDim (R ⧸ Q) = d at h0 ⊢
  induction d using WithBot.recBotCoe with
  | bot => simp at h0
  | coe d => exact_mod_cast Order.one_le_iff_pos (α := ℕ∞).2 (by exact_mod_cast h0)

private theorem dim_fin {O Y : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing Y] [Algebra O Y]
    [Module.Finite O Y] : ringKrullDim Y ≤ 1 := by
  have h1 : ringKrullDim O = 1 :=
    IsPrincipalIdealRing.ringKrullDim_eq_one O (IsDiscreteValuationRing.not_isField O)
  rw [← h1]
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap O Y)) fun a b hab => ?_
  exact (PrimeSpectrum.asIdeal_lt_asIdeal _ _).1
    (Ideal.IsIntegral.comap_lt_comap ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).2 hab))

private theorem dim_pt {l : ℕ} [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (R : Type) [CommRing R] [Algebra c.O R]
    [IsCO c.O R] (y : R →ₐ[c.O] Qbar l) : ringKrullDim (R ⧸ RingHom.ker y) ≤ 1 := by
  haveI : Module.Finite c.O y.range := (coPt l c R y).1
  have hker : RingHom.ker (y.rangeRestrict : R →+* y.range) = RingHom.ker y := by
    ext a
    rw [RingHom.mem_ker, RingHom.mem_ker]
    exact Subtype.ext_iff
  have e : R ⧸ RingHom.ker y ≃+* y.range := (Ideal.quotEquivOfEq hker.symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := (y.rangeRestrict : R →+* y.range)) y.rangeRestrict_surjective)
  rw [ringKrullDim_eq_of_ringEquiv e]
  exact dim_fin (O := c.O)

private noncomputable def zA {l : ℕ} [Fact l.Prime] (c : Coef l) (B : Type) [CommRing B] [Algebra c.O B] : ℤ_[l] →+* B :=
  (algebraMap c.O B).comp (algebraMap ℤ_[l] c.O)

private theorem td_pt {l : ℕ} [Fact l.Prime] (c : Coef l) {F : Fr.Frame l (ResidueField c.O)} {n : ℕ} (S : Fr.Space c.O F n)
    (ξ : S.A →ₐ[c.O] Qbar l) (h : ∀ a, ‖ξ a‖ ≤ 1) : S.td (RingHom.ker ξ) = 0 := by
  haveI hq : (RingHom.ker ξ).IsPrime := RingHom.ker_isPrime ξ
  have hφ : ∀ t, (ξ : S.A →+* Qbar l) (((algebraMap S.B S.A).comp (zA c S.B)) t) = algebraMap ℤ_[l] (Qbar l) t := fun t =>
    ((congrArg ξ (S.inc.commutes _)).trans (ξ.commutes _)).trans rfl
  have h2 : ∀ a, ∃ f : Polynomial ℤ_[l], f.Monic ∧ f.eval₂ ((algebraMap S.B S.A).comp (zA c S.B)) a ∈ RingHom.ker ξ := fun a => by
    obtain ⟨f, hf, h0⟩ := int_pt (ξ : S.A →+* Qbar l) h _ hφ a
    exact ⟨f, hf, RingHom.mem_ker.2 h0⟩
  exact td_zero (RingHom.ker ξ) (zA c S.B) h2

private theorem max_pt {l : ℕ} [Fact l.Prime] (c : Coef l) {F : Fr.Frame l (ResidueField c.O)} {n : ℕ} (S : Fr.Space c.O F n)
    (ξ : S.A →ₐ[c.O] Qbar l) (h : ∀ a, ‖(ξ : S.A →+* Qbar l) a‖ ≤ 1) : (nx (ξ : S.A →+* Qbar l) h).IsMaximal :=
  nx_max _ h (zA c S.A) fun t => (ξ.commutes _).trans rfl

private theorem dim_up {l : ℕ} [Fact l.Prime] {c : Coef l} [Fr.IsCoef l c.O] {F : Fr.Frame l (ResidueField c.O)} {C₀ n : ℕ}
    (hF : F.Ok C₀) (hn : n = 2 ∨ n = 3) (S : Fr.Space c.O F n) (ξ : S.A →ₐ[c.O] Qbar l) (h : ∀ a, ‖ξ a‖ ≤ 1)
    {x : Ideal S.A} (L : S.Loc x) (Q : Ideal L.R) (hQ : Q.IsPrime) (hc : L.im Q = RingHom.ker ξ) :
    ringKrullDim (L.R ⧸ Q) ≤ 1 := by
  have hup := (Fr.loc_dim hF hn S x L).1 Q hQ 0 (by rw [hc, td_pt c S ξ h]; simp)
  have hpi : L.π Q = RingHom.ker (ξ.comp S.inc) := by
    show S.π (L.im Q) = _
    rw [hc]
    ext b
    rfl
  obtain ⟨hco, -⟩ := Fr.co_B hF hn S
  haveI := hco
  have hd := dim_pt c S.B (ξ.comp S.inc)
  rw [hpi] at hup
  simpa using hup.trans (by simpa using hd)

private theorem l_mem {l : ℕ} {O R : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] [CommRing R] [Algebra O R]
    [IsCO O R] : ((l : ℕ) : R) ∈ maximalIdeal R := by
  rw [← res_eq_zero_iff O R, map_natCast]
  exact CharP.cast_eq_zero _ l

private theorem l_not {l : ℕ} [Fact l.Prime] {A R : Type} [CommRing A] [CommRing R] (ι : A →+* R) (ξ : A →+* Qbar l)
    (Q : Ideal R) (hc : ∀ a, ι a ∈ Q → ξ a = 0) : ((l : ℕ) : R) ∉ Q := fun h => by
  have h1 := hc (l : A) (by rw [map_natCast]; exact h)
  rw [map_natCast] at h1
  exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h1

theorem UpperTheory.V.J.locAt :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (F : Fr.Frame l (ResidueField c.O)) (C₀ n : ℕ), F.Ok C₀ → (n = 2 ∨ n = 3) →
        ∀ (S : Fr.Space c.O F n), ∀ ξ : S.A →ₐ[c.O] Qbar l, IntPt S ξ → ∃ (x : Ideal S.A) (L : S.Loc x) (Q : Ideal L.R), Over S L (RingHom.ker ξ) Q := by
  intro l _ c _ F C₀ n hF hn S ξ hξ
  haveI hxm := max_pt c S ξ hξ.1
  have hB : S.mB ≤ S.π (nx (ξ : S.A →+* Qbar l) hξ.1) := fun b hb => hξ.2 b hb
  obtain ⟨L⟩ := Fr.loc_ex hF hn S _ hxm hB
  have hfl := (Fr.loc_flat hF hn S _ L).1
  haveI hq : (RingHom.ker ξ).IsPrime := RingHom.ker_isPrime ξ
  have hqx : RingHom.ker ξ ≤ nx (ξ : S.A →+* Qbar l) hξ.1 := fun a ha => by
    show ‖ξ a‖ < 1
    rw [RingHom.mem_ker.1 ha, norm_zero]
    exact one_pos
  obtain ⟨Q, hQ, hQc, hQm⟩ := @down S.A L.R _ _ _ (L.ι : S.A →+* L.R) hfl _ _ hxm.isPrime hq hqx L.lies
  haveI := hQ
  have hn' := l_not (l := l) (L.ι : S.A →+* L.R) (ξ : S.A →+* Qbar l) Q fun a ha => RingHom.mem_ker.1 (hQc.le ha)
  have d1 := dim_up hF hn S ξ hξ.1 L Q hQ hQc
  have d2 := dim_ge Q _ (l_mem (l := l) (O := L.O') (R := L.R)) hn'
  exact ⟨_, L, Q, hQ, hQc, hQm, le_antisymm d1 d2⟩
