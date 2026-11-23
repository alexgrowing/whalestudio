import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRootSubMemOfEvalMem
open IsLocalRing Polynomial

namespace GlobalTheory.LocAcyc.Translate

theorem exists_X_sub_C_mem_of_isAlgClosed (k : Type) [Field k] [IsAlgClosed k]
    (Q : Ideal k[X]) [hQ : Q.IsPrime] :
    ∀ (n : ℕ) (g : k[X]), g ≠ 0 → g.natDegree = n → g ∈ Q → ∃ r : k, X - C r ∈ Q := by
  intro n
  induction n with
  | zero =>
    intro g hg hdeg hgQ
    exfalso
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg] at hgQ hg
    have h0 : g.coeff 0 ≠ 0 := fun h => hg (by rw [h, map_zero])
    exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hgQ (isUnit_C.2 (IsUnit.mk0 _ h0)))
  | succ n ih =>
    intro g hg hdeg hgQ
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_root g (by
      rw [Polynomial.degree_eq_natDegree hg, hdeg]; exact_mod_cast Nat.succ_ne_zero n)
    have hdiv := (mul_divByMonic_eq_iff_isRoot (p := g) (a := r)).2 hr
    rw [← hdiv] at hgQ hg
    rcases hQ.mem_or_mem hgQ with h | h
    · exact ⟨r, h⟩
    · refine ih _ (right_ne_zero_of_mul hg) ?_ h
      have := natDegree_divByMonic g (monic_X_sub_C r)
      rw [natDegree_X_sub_C] at this
      rw [this, hdeg]; omega

theorem exists_X_sub_C_mem (T : Type) [CommRing T] [IsLocalRing T] [IsAlgClosed (ResidueField T)]
    (P : Ideal T[X]) [hPp : P.IsPrime] (hP : P.comap (C : T →+* T[X]) = maximalIdeal T)
    (hne : P ≠ (maximalIdeal T).map (C : T →+* T[X])) : ∃ c : T, X - C c ∈ P := by
  set π : T[X] →+* (ResidueField T)[X] := mapRingHom (residue T) with hπ
  have hsurj : Function.Surjective π := map_surjective _ residue_surjective
  have hker : RingHom.ker π = (maximalIdeal T).map (C : T →+* T[X]) := by
    rw [hπ, ker_mapRingHom, ker_residue]
  have hle : RingHom.ker π ≤ P := by
    rw [hker, Ideal.map_le_iff_le_comap, hP]
  haveI hQ : (P.map π).IsPrime := Ideal.map_isPrime_of_surjective hsurj hle
  have hPQ : (P.map π).comap π = P := by
    rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot]
    exact sup_eq_left.2 hle
  have hQbot : P.map π ≠ ⊥ := by
    intro h
    apply hne
    rw [← hker, ← hPQ, h, RingHom.ker_eq_comap_bot]
  obtain ⟨g, hgQ, hg⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQbot
  obtain ⟨r, hr⟩ := exists_X_sub_C_mem_of_isAlgClosed _ _ _ g hg rfl hgQ
  obtain ⟨c, rfl⟩ := residue_surjective r
  refine ⟨c, ?_⟩
  rw [← hPQ, Ideal.mem_comap]
  simpa [hπ] using hr

end GlobalTheory.LocAcyc.Translate

namespace GlobalTheory.LocAcyc.Translate

theorem keyClosedPts_of_keyOrigin : GlobalTheory.LocAcyc.KeyOrigin → GlobalTheory.LocAcyc.KeyClosedPts := by
  intro hKO
  unfold GlobalTheory.LocAcyc.KeyOrigin GlobalTheory.LocAcyc.KeyLocalWith at hKO
  unfold GlobalTheory.LocAcyc.KeyClosedPts GlobalTheory.LocAcyc.KeyLocalWith
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hPm hne q hq hqu
  have hne' : P ≠ (maximalIdeal T).map (C : T →+* T[X]) := hne
  haveI hac : IsAlgClosed (ResidueField T) :=
    (GlobalTheory.AbsIntClosedLocal.henselian_isAlgClosed_pow_surj T ⟨inferInstance, hT⟩).2.1
  obtain ⟨c, hc⟩ := exists_X_sub_C_mem T P hPm hne'
  let τ : T[X] ≃ₐ[T] T[X] := algEquivAevalXAddC (-c)
  have hτX : τ X = X - C c := by simp [τ, sub_eq_add_neg]
  have hτC : ∀ a : T, τ (C a) = C a := fun a => τ.commutes a
  let P' : Ideal T[X] := P.comap (τ : T[X] →+* T[X])
  haveI hP'p : P'.IsPrime := Ideal.comap_isPrime _ _
  have hP'C : P'.comap (C : T →+* T[X]) = maximalIdeal T := by
    rw [← hPm]; ext a
    simp only [Ideal.mem_comap, P']
    rw [show ((τ : T[X] →+* T[X]) (C a)) = C a from hτC a]
  have hXP' : (X : T[X]) ∈ P' := by
    simp only [P', Ideal.mem_comap]
    rw [show ((τ : T[X] →+* T[X]) X) = X - C c from hτX]; exact hc
  have hP' : P' = (maximalIdeal T).map (C : T →+* T[X]) ⊔ Ideal.span {X} := by
    apply le_antisymm
    · intro p hp
      have hd : p - C (p.coeff 0) ∈ Ideal.span {(X : T[X])} := Ideal.mem_span_singleton.2 X_dvd_sub_C
      have hc0 : C (p.coeff 0) ∈ P' := by
        have h1 : p - C (p.coeff 0) ∈ P' := by
          obtain ⟨u, hu⟩ := (X_dvd_sub_C : X ∣ p - C (p.coeff 0))
          rw [hu]; exact P'.mul_mem_right _ hXP'
        have := P'.sub_mem hp h1
        simpa using this
      have hc0' : p.coeff 0 ∈ maximalIdeal T := by rw [← hP'C]; exact hc0
      have : p = C (p.coeff 0) + (p - C (p.coeff 0)) := by ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hc0')) (Ideal.mem_sup_right hd)
    · refine sup_le ?_ ?_
      · rw [Ideal.map_le_iff_le_comap, hP'C]
      · rw [Ideal.span_le, Set.singleton_subset_iff]; exact hXP'

  let f' : T[X] →+* O := (algebraMap T[X] O).comp (τ : T[X] →+* T[X])
  let alg' : Algebra T[X] O := f'.toAlgebra
  have tower' : @IsScalarTower T T[X] O _ alg'.toSMul _ := by
    refine @IsScalarTower.of_algebraMap_eq T T[X] O _ _ _ _ alg' _ ?_
    intro x
    change algebraMap T O x = f' (algebraMap T T[X] x)
    simp only [f', RingHom.comp_apply]
    rw [show (τ : T[X] →+* T[X]) (algebraMap T T[X] x) = algebraMap T T[X] x from τ.commutes x,
      ← IsScalarTower.algebraMap_apply]

  have hmap : P'.primeCompl.map (τ : T[X] ≃+* T[X]).toMonoidHom = P.primeCompl := by
    ext x
    rw [Submonoid.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      refine ⟨(τ : T[X] ≃+* T[X]).symm x, ?_, by simp⟩
      change (τ : T[X] →+* T[X]) ((τ : T[X] ≃+* T[X]).symm x) ∉ P
      have hx' : x ∉ P := hx
      convert hx' using 2
      exact (τ : T[X] ≃+* T[X]).apply_symm_apply x
  let Lq : Localization.AtPrime P' ≃+* Localization.AtPrime P :=
    IsLocalization.ringEquivOfRingEquiv _ _ (τ : T[X] ≃+* T[X]) hmap
  let φ' : Localization.AtPrime P' →+* O := φ.comp (Lq : Localization.AtPrime P' →+* Localization.AtPrime P)
  have hφ' : φ'.comp (algebraMap T[X] (Localization.AtPrime P')) = f' := by
    refine RingHom.ext fun x => ?_
    simp only [φ', f', RingHom.comp_apply]
    rw [show (Lq : Localization.AtPrime P' →+* Localization.AtPrime P) (algebraMap T[X] _ x)
        = algebraMap T[X] (Localization.AtPrime P) ((τ : T[X] ≃+* T[X]) x) from
      IsLocalization.ringEquivOfRingEquiv_eq _ x]
    rw [← RingHom.comp_apply φ, hφ]
    rfl
  have hsh' : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ' := by
    obtain ⟨h1, h2, h3, h4⟩ := hsh
    refine ⟨h1, h2, ?_, ?_⟩
    · haveI := h3
      haveI : IsLocalHom (Lq : Localization.AtPrime P' →+* Localization.AtPrime P) :=
        ⟨fun a ha => by simpa using ha.map (Lq.symm : Localization.AtPrime P →+* Localization.AtPrime P')⟩
      exact RingHom.isLocalHom_comp _ _
    · have : (RingHom.toMorphismProperty @RingHom.Etale).RespectsIso :=
        RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.Etale.respectsIso
      have h5 := CategoryTheory.MorphismProperty.RespectsIso.precomp
        (CategoryTheory.MorphismProperty.ind.{0} (RingHom.toMorphismProperty @RingHom.Etale))
        Lq.toCommRingCatIso.hom (CommRingCat.ofHom φ) h4
      unfold GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale
      convert h5 using 1
      rfl
  exact @hKO T O _ _ _ _ _ _ alg' tower' hT P' hP'p φ' hφ' hsh' hP'C hP' q hq hqu

end GlobalTheory.LocAcyc.Translate
