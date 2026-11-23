import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAct
import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
import ReciprocityTheory.Automorphisms.InstMainA
import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP

namespace Formalism.L2

variable {D : D7}

local notation "cO" => IsCMField.ringOfIntegersComplexConj D.host.E

theorem cO_cO (x : 𝓞 D.host.E) : cO (cO x) = x := by
  apply RingOfIntegers.ext
  rw [IsCMField.coe_ringOfIntegersComplexConj, IsCMField.coe_ringOfIntegersComplexConj]
  exact IsCMField.complexConj_apply_apply D.host.E (x : D.host.E)

theorem cO_algebraMap (a : 𝓞 (maximalRealSubfield D.host.E)) :
    cO (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) a) =
      algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) a :=
  (IsCMField.ringOfIntegersComplexConj_eq_self_iff D.host.E _).2 ⟨a, rfl⟩

def conjPlE (P : PlE D.host) : PlE D.host where
  asIdeal := P.asIdeal.comap (cO : 𝓞 D.host.E →+* 𝓞 D.host.E)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    refine (Submodule.ne_bot_iff _).2 ⟨cO y, ?_, ?_⟩
    · show (cO : 𝓞 D.host.E →+* 𝓞 D.host.E) (cO y) ∈ P.asIdeal
      rw [RingHom.coe_coe, cO_cO]; exact hy
    · intro h0
      apply hy0
      rw [← cO_cO y, h0, map_zero]

theorem mem_conjPlE (P : PlE D.host) (x : 𝓞 D.host.E) : x ∈ (conjPlE P).asIdeal ↔ cO x ∈ P.asIdeal := Iff.rfl

theorem eq_or_eq_conjPlE (P w : PlE D.host)
    (hw : w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) =
      P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E))) :
    w = P ∨ w = conjPlE P := by
  by_contra hne
  push Not at hne
  obtain ⟨h1, h2⟩ := hne
  have nle : ∀ Q : PlE D.host, w ≠ Q → ¬ w.asIdeal ≤ Q.asIdeal := fun Q h hle =>
    h (HeightOneSpectrum.ext (w.isMaximal.eq_of_le Q.isPrime.ne_top hle))
  obtain ⟨a, ha, haP⟩ := Set.not_subset.mp (nle P h1)
  obtain ⟨b, hb, hbQ⟩ := Set.not_subset.mp (nle _ h2)
  have key : ∃ x ∈ w.asIdeal, x ∉ P.asIdeal ∧ x ∉ (conjPlE P).asIdeal := by
    by_cases haQ : a ∈ (conjPlE P).asIdeal
    · by_cases hbP : b ∈ P.asIdeal
      · refine ⟨a + b, w.asIdeal.add_mem ha hb, fun h => haP ?_, fun h => hbQ ?_⟩
        · simpa using P.asIdeal.sub_mem h hbP
        · simpa using (conjPlE P).asIdeal.sub_mem h haQ
      · exact ⟨b, hb, hbP, hbQ⟩
    · exact ⟨a, ha, haP, haQ⟩
  obtain ⟨x, hx, hxP, hxQ⟩ := key
  rw [mem_conjPlE] at hxQ
  have hfix : cO (x * cO x) = x * cO x := by rw [map_mul, cO_cO, mul_comm]
  obtain ⟨y, hy⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff D.host.E _).1 hfix
  have hyw : y ∈ w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := by
    rw [Ideal.mem_comap, hy]; exact w.asIdeal.mul_mem_right _ hx
  rw [hw, Ideal.mem_comap, hy] at hyw
  rcases P.isPrime.mem_or_mem hyw with h | h
  · exact hxP h
  · exact hxQ h

def conjSplit (s : SplitPlace D.host.E) : SplitPlace D.host.E :=
  ⟨s.v, s.i.comp (IsCMField.complexConj D.host.E).toAlgHom⟩

theorem mem_conj_w (s : SplitPlace D.host.E) (x : 𝓞 D.host.E) : x ∈ (conjSplit s).w.asIdeal ↔ cO x ∈ s.w.asIdeal := by
  show Valued.v ((conjSplit s).i (x : D.host.E)) < 1 ↔ Valued.v (s.i ((cO x : 𝓞 D.host.E) : D.host.E)) < 1
  rw [IsCMField.coe_ringOfIntegersComplexConj]
  rfl

theorem splitEx_of (hstar : ∀ x : D.host.E, D.host.conj x = IsCMField.complexConj D.host.E x)
    (hsplit : ∀ v₀ : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)),
      (∃ w w' : PlE D.host, w ≠ w' ∧
        w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = v₀.asIdeal ∧
        w'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = v₀.asIdeal) →
      ∃ s : SplitPlace D.host.E, s.v = v₀) :
    SplitEx D := by
  intro v hv

  have hconj : ∀ w : PlE D.host, (∀ x, x ∈ v.asIdeal ↔ cO x ∈ w.asIdeal) → IsConjPl D.host v w := by
    intro w hw x y hxy
    have : y = cO x := by
      apply RingOfIntegers.ext
      rw [hxy, hstar, IsCMField.coe_ringOfIntegersComplexConj]
    rw [this]; exact hw x

  obtain ⟨x0, hx0, hx0'⟩ := hv
  have hc0 : cO x0 ∉ v.asIdeal := hx0' (cO x0) (by rw [hstar, IsCMField.coe_ringOfIntegersComplexConj])
  have hne : v ≠ conjPlE v := by
    intro h
    apply hc0
    have : x0 ∈ (conjPlE v).asIdeal := by rw [← h]; exact hx0
    exact this

  let v₀ : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) :=
    { asIdeal := v.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E))
      isPrime := Ideal.comap_isPrime _ _
      ne_bot := by
        obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
        exact Ideal.comap_ne_bot_of_integral_mem hy0 hy (Algebra.IsIntegral.isIntegral y) }
  have hover' : (conjPlE v).asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) =
      v₀.asIdeal := by
    ext a
    show cO (algebraMap _ _ a) ∈ v.asIdeal ↔ algebraMap _ _ a ∈ v.asIdeal
    rw [cO_algebraMap]
  obtain ⟨s, hs⟩ := hsplit v₀ ⟨v, conjPlE v, hne, rfl, hover'⟩
  have hsw : s.w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) =
      v.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := by
    rw [s.w_under, hs]

  obtain ⟨π, hπ⟩ := s.v.valuation_exists_uniformizer (maximalRealSubfield D.host.E)
  have hu : Formalism.AUTREP.IsUnif D.host.E s.v (algebraMap (maximalRealSubfield D.host.E) (s.v.adicCompletion _) π) := by
    unfold Formalism.AUTREP.IsUnif
    rw [adic_valued_algebraMap s.v π, hπ]
  rcases eq_or_eq_conjPlE v s.w hsw with h | h
  ·
    refine ⟨conjSplit s, algebraMap (maximalRealSubfield D.host.E) (s.v.adicCompletion _) π, ?_, hu⟩
    apply hconj
    intro x
    rw [mem_conj_w, cO_cO, h]
  · refine ⟨s, algebraMap (maximalRealSubfield D.host.E) (s.v.adicCompletion _) π, ?_, hu⟩
    apply hconj
    intro x
    rw [h, mem_conjPlE, cO_cO]

end Formalism.L2

namespace Formalism.L2

variable {D : D7}

local notation "cO" => IsCMField.ringOfIntegersComplexConj D.host.E
local notation "Fp" => maximalRealSubfield D.host.E

def belowE (v : PlE D.host) : HeightOneSpectrum (𝓞 Fp) where
  asIdeal := v.asIdeal.comap (algebraMap (𝓞 Fp) (𝓞 D.host.E))
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    exact Ideal.comap_ne_bot_of_integral_mem hy0 hy (Algebra.IsIntegral.isIntegral y)

theorem fixed_of_cO {x : 𝓞 D.host.E} (hx : cO x = x) : ∃ y : 𝓞 Fp, algebraMap (𝓞 Fp) (𝓞 D.host.E) y = x :=
  (IsCMField.ringOfIntegersComplexConj_eq_self_iff D.host.E _).1 hx

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem exists_splitPlace (v : PlE D.host) (x0 : 𝓞 D.host.E) (hx0 : x0 ∈ v.asIdeal) (hc0 : cO x0 ∉ v.asIdeal) :
    ∃ s : SplitPlace D.host.E, s.v = belowE v := by
  classical
  set v₀ := belowE v
  obtain ⟨a, ha⟩ := fixed_of_cO (x := x0 + cO x0) (by rw [map_add, cO_cO, add_comm])
  obtain ⟨b, hb⟩ := fixed_of_cO (x := x0 * cO x0) (by rw [map_mul, cO_cO, mul_comm])
  have hbv : b ∈ v₀.asIdeal := by
    show algebraMap _ _ b ∈ v.asIdeal
    rw [hb]; exact v.asIdeal.mul_mem_right _ hx0
  have hav : a ∉ v₀.asIdeal := by
    intro h
    have h' : algebraMap _ _ a ∈ v.asIdeal := h
    rw [ha] at h'
    exact hc0 (by simpa using v.asIdeal.sub_mem h' hx0)

  haveI : IsAdicComplete (IsLocalRing.maximalIdeal (v₀.adicCompletionIntegers Fp)) (v₀.adicCompletionIntegers Fp) := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v₀.adicCompletionIntegers Fp)
    have : IsPrecomplete (IsLocalRing.maximalIdeal (v₀.adicCompletionIntegers Fp)) (v₀.adicCompletionIntegers Fp) :=
      Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.completion_integers_precomplete v₀ hϖ
    exact {}
  set Rv := v₀.adicCompletionIntegers Fp
  let g : Polynomial Rv := Polynomial.X ^ 2 - Polynomial.C (algebraMap (𝓞 Fp) Rv a) * Polynomial.X +
    Polynomial.C (algebraMap (𝓞 Fp) Rv b)
  have hcoe : ∀ z : 𝓞 Fp, ((algebraMap (𝓞 Fp) Rv z : Rv) : v₀.adicCompletion Fp) =
      algebraMap Fp (v₀.adicCompletion Fp) (algebraMap (𝓞 Fp) Fp z) := fun z => rfl
  have hmem : ∀ z : 𝓞 Fp, algebraMap (𝓞 Fp) Rv z ∈ IsLocalRing.maximalIdeal Rv ↔ z ∈ v₀.asIdeal := by
    intro z
    rw [ReciprocityTheory.Aut.mem_maxIdeal_iff, hcoe, ReciprocityTheory.Aut.adic_valued_algebraMap]
    exact v₀.valuation_lt_one_iff_mem (K := Fp) z
  have h1 : g.eval 0 ∈ IsLocalRing.maximalIdeal Rv := by
    simp only [g, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_mul, Polynomial.eval_C]
    simpa using (hmem b).2 hbv
  have h2 : IsUnit (Ideal.Quotient.mk (IsLocalRing.maximalIdeal Rv) (g.derivative.eval 0)) := by
    have hd : g.derivative.eval 0 = -algebraMap (𝓞 Fp) Rv a := by
      simp [g]
    rw [hd, map_neg, IsUnit.neg_iff]
    exact (IsLocalRing.notMem_maximalIdeal.1 (fun h => hav ((hmem a).1 h))).map _
  obtain ⟨r, hr, -⟩ := HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal Rv) g (by simp only [g]; monicity!) 0 h1 h2
  have hr' : ((r : v₀.adicCompletion Fp)) ^ 2 - algebraMap Fp (v₀.adicCompletion Fp) (a : Fp) * r +
      algebraMap Fp (v₀.adicCompletion Fp) (b : Fp) = 0 := by
    have := congrArg (fun z : Rv => (z : v₀.adicCompletion Fp)) hr.eq_zero
    simp only [g, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_mul, Polynomial.eval_C] at this
    push_cast at this
    rw [hcoe, hcoe] at this
    exact this

  set x : D.host.E := (x0 : D.host.E)
  have hint : IsIntegral Fp x := Algebra.IsIntegral.isIntegral x
  let gF : Polynomial Fp := Polynomial.X ^ 2 - Polynomial.C (a : Fp) * Polynomial.X + Polynomial.C (b : Fp)
  have hgF_monic : gF.Monic := by simp only [gF]; monicity!
  have hgF_deg : gF.natDegree = 2 := by simp only [gF]; compute_degree!
  have hax : algebraMap Fp D.host.E (a : Fp) = x + IsCMField.complexConj D.host.E x := by
    have e := congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) ha
    rw [ReciprocityTheory.Aut.split_coe_algebraMap] at e
    rw [e, show ((x0 + cO x0 : 𝓞 D.host.E) : D.host.E) = (x0 : D.host.E) + ((cO x0 : 𝓞 D.host.E) : D.host.E) from rfl,
      IsCMField.coe_ringOfIntegersComplexConj]
  have hbx : algebraMap Fp D.host.E (b : Fp) = x * IsCMField.complexConj D.host.E x := by
    have e := congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) hb
    rw [ReciprocityTheory.Aut.split_coe_algebraMap] at e
    rw [e, show ((x0 * cO x0 : 𝓞 D.host.E) : D.host.E) = (x0 : D.host.E) * ((cO x0 : 𝓞 D.host.E) : D.host.E) from rfl,
      IsCMField.coe_ringOfIntegersComplexConj]
  have hgx : Polynomial.aeval x gF = 0 := by
    rw [Polynomial.aeval_def]
    simp only [gF, Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C, hax, hbx]
    ring
  have hnot : x ∉ (algebraMap Fp D.host.E).range := by
    rintro ⟨y, hy⟩
    have hc : IsCMField.complexConj D.host.E x = x := by
      rw [← hy]; exact IsCMField.complexConj_apply_eq_self D.host.E y
    apply hc0
    have : cO x0 = x0 := by
      apply RingOfIntegers.ext
      rw [IsCMField.coe_ringOfIntegersComplexConj]; exact hc
    rw [this]; exact hx0
  have hmin : gF = minpoly Fp x := by
    refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hgF_monic
      (minpoly.dvd Fp x hgx) ?_)
    rw [hgF_deg]
    have h0 := minpoly.natDegree_pos hint
    have h1' : (minpoly Fp x).natDegree ≠ 1 := fun h => hnot ((minpoly.natDegree_eq_one_iff).1 h)
    omega
  have hroot : Polynomial.aeval ((r : v₀.adicCompletion Fp)) (minpoly Fp x) = 0 := by
    rw [← hmin, Polynomial.aeval_def]
    simp only [gF, Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    exact hr'
  let pb := IntermediateField.adjoin.powerBasis hint
  have hpbroot : Polynomial.aeval ((r : v₀.adicCompletion Fp)) (minpoly Fp pb.gen) = 0 := by
    rw [show pb.gen = IntermediateField.AdjoinSimple.gen Fp x from rfl, IntermediateField.minpoly_gen]
    exact hroot
  have htop : IntermediateField.adjoin Fp {x} = ⊤ := by
    refine IntermediateField.eq_of_le_of_finrank_eq le_top ?_
    rw [IntermediateField.finrank_top', IntermediateField.adjoin.finrank hint, ← hmin, hgF_deg,
      Algebra.IsQuadraticExtension.finrank_eq_two]
  let φ : IntermediateField.adjoin Fp {x} →ₐ[Fp] v₀.adicCompletion Fp := pb.lift _ hpbroot
  let i : D.host.E →ₐ[Fp] v₀.adicCompletion Fp :=
    φ.comp ((IntermediateField.equivOfEq htop.symm).toAlgHom.comp IntermediateField.topEquiv.symm.toAlgHom)
  exact ⟨⟨v₀, i⟩, rfl⟩

theorem splitEx_of_star (hstar : ∀ x : D.host.E, D.host.conj x = IsCMField.complexConj D.host.E x) : SplitEx D := by
  refine splitEx_of hstar fun v₀ ⟨w, w', hne, hw, hw'⟩ => ?_

  have key : ∃ x0 ∈ w.asIdeal, cO x0 ∉ w.asIdeal := by
    rcases eq_or_eq_conjPlE w w' (hw'.trans hw.symm) with h | h
    · exact absurd h.symm hne
    · by_contra hall
      push Not at hall
      apply hne
      rw [h]
      ext1
      refine le_antisymm (fun x hx => hall x hx) ?_
      exact w.isMaximal.eq_of_le (conjPlE w).isPrime.ne_top (fun x hx => hall x hx) ▸ le_refl _
  obtain ⟨x0, hx0, hc0⟩ := key
  obtain ⟨s, hs⟩ := exists_splitPlace w x0 hx0 hc0
  refine ⟨s, hs.trans ?_⟩
  exact HeightOneSpectrum.ext hw

end Formalism.L2
