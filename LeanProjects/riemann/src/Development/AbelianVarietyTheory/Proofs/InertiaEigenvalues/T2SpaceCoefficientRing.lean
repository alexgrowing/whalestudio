import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BlockComplementLattice
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RepresentationOverSumChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyLinearEquivOfCharpolyEq

noncomputable section

namespace GlobalTheory.ComplementCompare

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N ReciprocityTheory.Gal
open GlobalTheory.IndefiniteRowSideFullHecke

section General

variable {k Γ : Type} [Field k] [Group Γ]

theorem semisimple_congr {V W : Type} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {ρ : Representation k Γ V} {σ : Representation k Γ W} (e : V ≃ₗ[k] W)
    (he : ∀ g v, e (ρ g v) = σ g (e v)) :
    ρ.IsSemisimpleRepresentation ↔ σ.IsSemisimpleRepresentation := by
  have he' : ∀ g w, e.symm (σ g w) = ρ g (e.symm w) := fun g w => by
    rw [LinearEquiv.symm_apply_eq, he, LinearEquiv.apply_symm_apply]
  let o : Subrepresentation ρ ≃o Subrepresentation σ :=
    { toFun := fun P => ⟨P.toSubmodule.comap e.symm.toLinearMap, fun g w hw => by
        change e.symm (σ g w) ∈ P.toSubmodule
        rw [he']
        exact P.apply_mem_toSubmodule g hw⟩
      invFun := fun Q => ⟨Q.toSubmodule.comap e.toLinearMap, fun g v hv => by
        change e (ρ g v) ∈ Q.toSubmodule
        rw [he]
        exact Q.apply_mem_toSubmodule g hv⟩
      left_inv := fun P => by ext v; simp
      right_inv := fun Q => by ext w; simp
      map_rel_iff' := by
        intro P Q
        constructor
        · intro h v hv
          have := @h (e v) (by
            change e.symm (e v) ∈ P.toSubmodule
            rw [e.symm_apply_apply]
            exact hv)
          change e.symm (e v) ∈ Q.toSubmodule at this
          rw [e.symm_apply_apply] at this
          exact this
        · intro h w hw
          exact @h (e.symm w) hw }
  exact OrderIso.complementedLattice_iff o

theorem isCompl_sub_iff {V : Type} [AddCommGroup V] [Module k V] {ρ : Representation k Γ V}
    (P Q : Subrepresentation ρ) : IsCompl P Q ↔ IsCompl P.toSubmodule Q.toSubmodule := by
  rw [isCompl_iff, isCompl_iff, disjoint_iff, disjoint_iff, codisjoint_iff, codisjoint_iff,
    ← Subrepresentation.toSubmodule_injective.eq_iff, ← Subrepresentation.toSubmodule_injective.eq_iff]
  rfl

theorem isSSRep_iff {a : ℕ} (ρ : Γ →* GL (Fin a) k) :
    IsSSRep ρ ↔ (glRep ρ).IsSemisimpleRepresentation := by
  constructor
  · intro h
    refine ⟨fun P => ?_⟩
    obtain ⟨W', h1, h2⟩ := h P.toSubmodule fun g v hv => P.apply_mem_toSubmodule g hv
    exact ⟨⟨W', fun g v hv => h1 g v hv⟩, (isCompl_sub_iff _ _).2 h2⟩
  · intro h W hW
    obtain ⟨Q, hQ⟩ := h.exists_isCompl ⟨W, fun g v hv => hW g v hv⟩
    exact ⟨Q.toSubmodule, fun g v hv => Q.apply_mem_toSubmodule g hv, (isCompl_sub_iff _ _).1 hQ⟩

variable {O : Type} [CommRing O] [IsDomain O]

theorem fracRep_eq {a : ℕ} (r : Γ →* GL (Fin a) O) :
    BlockRepresentationsSemisimple.fracRep r = RepresentationOverSumChar.repOver (FractionRing O) ((Units.coeHom _).comp r) := rfl

theorem sum_equivariant {a : ℕ} (ρ : Γ →* GL (Fin a) O) (χ : ℕ → (Γ →* Oˣ)) (t : ℕ) (g : Γ)
    (v : Fin a ⊕ Fin t → FractionRing O) :
    LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin t) (FractionRing O) (FractionRing O)
        (RepresentationOverSumChar.repOver (FractionRing O) (RepresentationOverSumChar.blockSum t ρ χ) g v) =
      BlockRepresentationsSemisimple.blockRep ρ χ t g
        (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin t) (FractionRing O) (FractionRing O) v) := by
  rw [BlockRepresentationsSemisimple.blockRep_apply]
  have key : ∀ s : Fin a ⊕ Fin t, RepresentationOverSumChar.repOver (FractionRing O) (RepresentationOverSumChar.blockSum t ρ χ) g v s =
      ∑ s' : Fin a ⊕ Fin t, algebraMap O (FractionRing O)
        (Matrix.fromBlocks ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O) 0 0
          (Matrix.diagonal fun c : Fin t => ((χ (c.1 + 1) g : Oˣ) : O)) s s') * v s' := fun s => rfl
  refine Prod.ext (funext fun j => ?_) (funext fun c => ?_)
  · refine (key (Sum.inl j)).trans ?_
    simp [Fintype.sum_sum_type, Matrix.mulVec, dotProduct]
  · refine (key (Sum.inr c)).trans ?_
    simp [Fintype.sum_sum_type, Matrix.diagonal_apply, apply_ite]

theorem trace_repOver {n : Type} [Fintype n] [DecidableEq n] (M : Γ →* Matrix n n O) (g : Γ) :
    LinearMap.trace _ _ (RepresentationOverSumChar.repOver (FractionRing O) M g) =
      algebraMap O (FractionRing O) (M g).trace := by
  change LinearMap.trace _ _ (Matrix.toLin' ((M g).map (algebraMap O (FractionRing O)))) = _
  rw [Matrix.trace_toLin'_eq, AddMonoidHom.map_trace]

omit [IsDomain O] in
theorem trace_eq_of_charpoly_eq [Nontrivial O] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (A : Matrix m m O) (B : Matrix n n O) (h : A.charpoly = B.charpoly) :
    A.trace = B.trace := by
  rw [Matrix.trace_eq_neg_charpoly_nextCoeff, Matrix.trace_eq_neg_charpoly_nextCoeff, h]

end General

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)

theorem ss_iff (i : N.Loc) (ρ : GE N →* GL (Fin R.r) (N.O i)) :
    BlockRepresentationsSemisimple.BlockSemisimple ρ (N.chi i) R.t ↔ RepresentationOverSumChar.IsSSSum N i ρ :=
  (semisimple_congr _ (sum_equivariant ρ (N.chi i) R.t)).symm

theorem isoBlock_iff (i : N.Loc) (r₀ : GE N →* GL (Fin R.nV) (N.O i)) (ρ : GE N →* GL (Fin R.r) (N.O i)) :
    BlockRepresentationsSemisimple.IsoBlock r₀ ρ (N.chi i) R.t ↔ RepresentationOverSumChar.SplitsAs N i r₀ ρ := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e.trans (LinearEquiv.sumArrowLequivProdArrow _ _ _ _).symm, fun g u => ?_⟩
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_eq]
    refine (he g u).trans ?_
    refine Eq.trans ?_ (sum_equivariant ρ (N.chi i) R.t g _).symm
    rw [LinearEquiv.apply_symm_apply]
  · rintro ⟨e, he⟩
    refine ⟨e.trans (LinearEquiv.sumArrowLequivProdArrow _ _ _ _), fun g u => ?_⟩
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, fracRep_eq, he g u]
    exact sum_equivariant ρ (N.chi i) R.t g _

theorem isHeckeGalois_iff (i : N.Loc) (x : N.X i) (r : GE N →* GL (Fin R.nV) (N.O i)) :
    IsHeckeGalois N i x r ↔ RepresentationOverSumChar.IsRx N i x ((Units.coeHom _).comp r) :=
  and_congr Iff.rfl (and_congr (isSSRep_iff _) Iff.rfl)

theorem second_of_first (i : N.Loc) (π : N.X i) (r₀ : GE N →* GL (Fin R.nV) (N.O i))
    (ρ : GE N →* GL (Fin R.r) (N.O i)) (hr : IsHeckeGalois N i π r₀)
    (h : BlockRepresentationsSemisimple.IsComplement N i r₀ ρ) : RepresentationOverSumChar.IsComplement N i π ρ :=
  ⟨RepresentationOverSumChar.isRhoAt_of_splitsAs N i π r₀ ρ hr.2.2 ((isoBlock_iff N i r₀ ρ).1 h.rho),
    (ss_iff N i ρ).1 h.ss, h.cont⟩

theorem exists_conj_ne (H : Host R) : ∃ x y : 𝓞 H.E, (y : H.E) = H.conj (x : H.E) ∧ y - x ≠ 0 := by
  by_contra hc
  push Not at hc
  have h1 : ∀ x : 𝓞 H.E, H.conj (x : H.E) = x := fun x => by
    have := hc x ⟨H.conj x, (RingOfIntegers.isIntegral_coe x).map (H.conj.toAlgHom.restrictScalars ℤ)⟩ rfl
    exact congrArg (fun z : 𝓞 H.E => (z : H.E)) (sub_eq_zero.1 this)
  have h2 : ∀ z : H.E, H.conj z = z := fun z => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 H.E) z
    rw [map_div₀]
    exact congrArg₂ (· / ·) (h1 a) (h1 b)
  have := H.isCMField_hostE
  refine IsTotallyComplex.complexEmbedding_not_isReal H.φ₀ (ComplexEmbedding.isReal_iff.2 ?_)
  ext z
  exact (H.conjE_apply H.φ₀ z).symm.trans (congrArg H.φ₀ (h2 z))

theorem exists_int_sub_mem {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E))
    (hv : v.asIdeal.inertiaDeg ℤ = 1) (x : 𝓞 E) : ∃ n : ℤ, x - n ∈ v.asIdeal := by
  have := v.isPrime
  have : NeZero v.asIdeal := ⟨v.ne_bot⟩
  have hp := Nat.absNorm_under_prime v.asIdeal
  have h := Ideal.absNorm_pow_inertiaDeg (v.asIdeal.under ℤ) v.asIdeal
  rw [hv, pow_one] at h
  rw [h] at hp
  have : Fact (Ideal.absNorm v.asIdeal).Prime := ⟨hp⟩
  have hc : Nat.card (𝓞 E ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := rfl
  have : Nontrivial (𝓞 E ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.2 v.isPrime.ne_top
  have hm := mem_zmultiples_of_prime_card hc (g := (1 : 𝓞 E ⧸ v.asIdeal)) (g' := Ideal.Quotient.mk _ x)
    one_ne_zero
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 hm
  refine ⟨n, Ideal.Quotient.eq.1 ?_⟩
  rw [← hn]
  simp

theorem eq_univ_of_frob (hC : GlobalTheory.TwSys.Cheb) (i : N.Loc) (s : Set (GE N)) (hs : IsClosed s)
    (h : ∀ w : PlE H, SplitOut N i w → ∀ (B : ValuationSubring N.Om) (σ : GE N),
      IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ → σ ∈ s) (g : GE N) : g ∈ s := by
  classical
  by_contra hg
  have : IsGalois H.E N.Om := {}
  have hn : (fun u : GE N => u * g) ⁻¹' sᶜ ∈ nhds (1 : GE N) :=
    (hs.isOpen_compl.preimage (continuous_mul_const g)).mem_nhds (by simpa using hg)
  obtain ⟨L, hfd, hN, hL⟩ := (krullTopology_mem_nhds_one_iff_of_normal H.E N.Om _).1 hn
  have hgal : IsGalois H.E L := {}
  obtain ⟨x, y, hxy, hne⟩ := exists_conj_ne H
  have f1 : {v : PlE H | v.asIdeal ∣ Ideal.span {y - x}}.Finite :=
    Ideal.finite_factors (by simpa using hne)
  have f2 : {v : PlE H | v.asIdeal ∣ Ideal.span {((N.l i : ℕ) : 𝓞 H.E)}}.Finite :=
    Ideal.finite_factors (by simpa using (N.lPrime i).out.ne_zero)
  obtain ⟨v, hv, hf, -, B, hB, -, σ, hσ, hU⟩ := hC H.E N.Om L.fixingSubgroup L.fixingSubgroup_isOpen
    ((InfiniteGalois.normal_iff_isGalois L).2 hgal) g (f1.toFinset ∪ f2.toFinset ∪ N.S i ∪ N.Q i)
  simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton,
    not_or] at hv
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hv
  obtain ⟨n, hx⟩ := exists_int_sub_mem v hf x
  have hsplit : IsSplitPl H v := by
    refine ⟨x - n, hx, fun z hz hzv => h1 ?_⟩
    have hz' : z = y - n := by
      apply RingOfIntegers.ext
      rw [hz]
      simp [hxy]
    have := v.asIdeal.sub_mem hzv hx
    rwa [hz', sub_sub_sub_cancel_right] at this
  have := hL hU
  simp only [Set.mem_preimage, inv_mul_cancel_right, Set.mem_compl_iff] at this
  exact this (h v ⟨hsplit, h2, h3, h4⟩ B σ hB hσ)

theorem t2Space_coefficientRing (i : N.Loc) : T2Space (N.O i) :=
  have := N.O_complete i
  (N.O_adic i).isHausdorff_iff.1 inferInstance

theorem isRx_unique (hC : GlobalTheory.TwSys.Cheb) (i : N.Loc) (x : N.X i) {m n : Type} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (M : GE N →* Matrix m m (N.O i)) (M' : GE N →* Matrix n n (N.O i))
    (h : RepresentationOverSumChar.IsRx N i x M) (h' : RepresentationOverSumChar.IsRx N i x M') :
    ∃ e : (m → KK N i) ≃ₗ[KK N i] (n → KK N i), ∀ g u,
      e (RepresentationOverSumChar.repOver (KK N i) M g u) = RepresentationOverSumChar.repOver (KK N i) M' g (e u) := by
  have := t2Space_coefficientRing N i
  have : CharZero what₂.LL := what₂.embLL.charZero
  have : CharZero (FractionRing (N.O i)) :=
    (N.embK i).charZero_iff (N.embK i).injective |>.1 inferInstance
  refine GlobalTheory.TraceIso.exists_equiv_of_trace_eq _ _ h.2.1 h'.2.1 fun g => ?_
  rw [trace_repOver, trace_repOver]
  congr 1
  refine eq_univ_of_frob N hC i {g | (M g).trace = (M' g).trace}
    (isClosed_eq h.1.matrix_trace h'.1.matrix_trace) (fun w hw B σ hB hσ => ?_) g
  exact trace_eq_of_charpoly_eq _ _ ((h.2.2 w hw B σ hB hσ).trans (h'.2.2 w hw B σ hB hσ).symm)

end GlobalTheory.ComplementCompare

end
