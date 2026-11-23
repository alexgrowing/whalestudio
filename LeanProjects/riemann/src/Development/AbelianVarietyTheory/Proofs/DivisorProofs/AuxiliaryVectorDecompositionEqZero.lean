import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolynomialModelCoefficientSpaceRealPoints
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeDvdAbsNormHalfDifferent
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefNodeIsV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacEqJets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiDiagonalEpsilonGramMulVec

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors Pointwise

namespace GlobalTheory.FunObj

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7}

theorem exists_unit_cpt (f g : ∀ Q : Pl D.host.E, Kw Q) (hfg : ∀ Q, f Q * g Q = 1)
    (hf : ∀ᶠ Q : Pl D.host.E in Filter.cofinite, f Q ∈ Q.adicCompletionIntegers D.host.E)
    (hg : ∀ᶠ Q : Pl D.host.E in Filter.cofinite, g Q ∈ Q.adicCompletionIntegers D.host.E) :
    ∃ y : (Lev.EAf D)ˣ, ∀ Q, cpt (D := D) Q y.1 = f Q := by
  obtain ⟨a, ha⟩ := GlobalTheory.AdeleBaseChange.map_surjective (toAd_spec D)
    (⟨f, hf⟩ : FiniteAdeleRing (𝓞 D.host.E) D.host.E)
  obtain ⟨b, hb⟩ := GlobalTheory.AdeleBaseChange.map_surjective (toAd_spec D)
    (⟨g, hg⟩ : FiniteAdeleRing (𝓞 D.host.E) D.host.E)
  have h1 : ∀ Q, cpt (D := D) Q a = f Q := fun Q => by
    change toAd D a Q = _
    rw [ha]
    rfl
  have h2 : ∀ Q, cpt (D := D) Q b = g Q := fun Q => by
    change toAd D b Q = _
    rw [hb]
    rfl
  have e : a * b = 1 := cpt_ext fun Q => by rw [map_mul, h1, h2, hfg, map_one]
  exact ⟨⟨a, b, e, by rw [mul_comm]; exact e⟩, h1⟩

theorem cpt_tmul_one (Q : Pl D.host.E) (u : D.host.E) :
    cpt (D := D) Q (u ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)) = algebraMap D.host.E (Kw Q) u :=
  congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z Q) (GlobalTheory.AdeleBaseChange.map_tmul_one (toAd_spec D) u)

theorem idele_inv_mul_mem_iff {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (hI : I ≠ 0) (y : (Lev.EAf D)ˣ)
    (hy : ∀ Q, Valued.v (cpt (D := D) Q y.1) = WithZero.exp (-FractionalIdeal.count D.host.E Q I)) (u : D.host.E) :
    (y⁻¹).1 * (u ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)) ∈ OA D ↔ u ∈ I := by
  rw [mem_OA_iff, GlobalTheory.Idele.mem_iff_valuation_le hI]
  refine forall_congr' fun Q => ?_
  have hne : Valued.v (cpt (D := D) Q y.1) ≠ 0 := by rw [hy]; exact WithZero.exp_ne_zero
  have e3 : Valued.v (cpt (D := D) Q (y⁻¹).1) = (Valued.v (cpt (D := D) Q y.1))⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one])
  rw [map_mul, cpt_tmul_one, HeightOneSpectrum.mem_adicCompletionIntegers, map_mul,
    show Valued.v (algebraMap D.host.E (Kw Q) u) = Q.valuation D.host.E u from
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q u, ← hy, e3, ← div_eq_inv_mul, div_le_one₀ (zero_lt_iff.2 hne)]

theorem auxiliaryVectorDecomposition_eq_zero {A B : HSp D} {c : ℕ} {ε : D.host.E} (hε : ε ≠ 0) (d : HermitianOrthogonalExtensionData A B c ε)
    (y : Fin A.rank → D.host.E) (u : Fin c → D.host.E)
    (h : frameMat B A d.ι *ᵥ y + d.a *ᵥ u = 0) : y = 0 ∧ u = 0 := by
  have h1 := congrArg (fun x => (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A d.ι) * B.gram) *ᵥ x) h
  simp only [mulVec_add, mulVec_mulVec, mulVec_zero] at h1
  rw [GlobalTheory.AutFunCounterexample.gram_pull B A d.ι d.isom, d.perp, zero_mulVec, add_zero] at h1
  have hy : y = 0 := eq_zero_of_mulVec_eq_zero (GlobalTheory.AutFunCounterexample.gram_det_ne A) h1
  subst hy
  rw [mulVec_zero, zero_add] at h
  have h2 := congrArg (fun x => (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) d.a * B.gram) *ᵥ x) h
  simp only [mulVec_mulVec, mulVec_zero] at h2
  rw [d.gram] at h2
  refine ⟨rfl, funext fun p => ?_⟩
  have h3 := congrFun h2 p.rev
  rw [GlobalTheory.ChiGrid.SumDual.antiDiagonalEpsilonGram_mulVec, Fin.rev_rev] at h3
  have h4 : (if p.rev = p then ε else 1) ≠ 0 := by split_ifs; exacts [hε, one_ne_zero]
  exact (mul_eq_zero.1 h3).resolve_left h4

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

theorem exists_sumFrame {A B : HSp D} {c : ℕ} {ε : D.host.E} (hε : ε ≠ 0) (d : HermitianOrthogonalExtensionData A B c ε)
    {Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)} (hΛ : Submodule.IsLattice D.host.E Λ)
    {β : GL (Fin A.rank) (Lev.EAf D)} (hβ : IsFrame β Λ) {𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E}
    (h𝔟 : ∀ p, 𝔟 p ≠ 0) (y : Fin c → (Lev.EAf D)ˣ)
    (hy : ∀ p Q, Valued.v (cpt (D := D) Q (y p).1) = WithZero.exp (-FractionalIdeal.count D.host.E Q (𝔟 p))) :
    ∃ β' : GL (Fin B.rank) (Lev.EAf D), IsFrame β' (d.lat Λ 𝔟) ∧
      ∀ w, IsSumFrame d w β β' fun p => cpt (D := D) w (y p).1 := by
  classical
  set σ := frame d.rank with hσ
  obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin B.rank) (Fin A.rank ⊕ Fin c) D.host.E, C = Matrix.fromCols (frameMat B A d.ι) d.a :=
    ⟨_, rfl⟩
  have hCv : ∀ v, C *ᵥ v = frameMat B A d.ι *ᵥ (v ∘ Sum.inl) + d.a *ᵥ (v ∘ Sum.inr) := fun v => by
    rw [hC, fromCols_mulVec]
  have hCinj : Function.Injective C.mulVec := fun v v' h => by
    have h0 : C *ᵥ (v - v') = 0 := by rw [mulVec_sub, h, sub_self]
    rw [hCv] at h0
    obtain ⟨h1, h2⟩ := auxiliaryVectorDecomposition_eq_zero hε d _ _ h0
    refine sub_eq_zero.1 (funext fun s => ?_)
    rcases s with k | p
    · exact congrFun h1 k
    · exact congrFun h2 p
  obtain ⟨Cr, hCrdef⟩ : ∃ Cr : Matrix (Fin B.rank) (Fin B.rank) D.host.E, Cr = C.submatrix id σ.symm := ⟨_, rfl⟩
  have hCrv : ∀ z, Cr *ᵥ z = C *ᵥ (z ∘ σ) := fun z => by
    rw [hCrdef, submatrix_mulVec_equiv]
    rfl
  have hCr : IsUnit Cr := by
    rw [← mulVec_injective_iff_isUnit]
    intro v v' h
    rw [hCrv, hCrv] at h
    have := hCinj h
    funext i
    simpa using congrFun this (σ.symm i)
  obtain ⟨U, hU⟩ := hCr
  let ι : D.host.E →+* Lev.EAf D := Formalism.UG.inclE (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  have hιc : ∀ w x, cpt (D := D) w (ι x) = algebraMap D.host.E (Kw w) x := fun w x => cpt_tmul_one w x
  let Ua : GL (Fin B.rank) (Lev.EAf D) := Units.map (RingHom.mapMatrix ι).toMonoidHom U
  have hUa : Ua.val = Cr.map ι := by rw [← hU]; rfl
  let Bl : GL (Fin A.rank ⊕ Fin c) (Lev.EAf D) :=
    ⟨fromBlocks β.1 0 0 (diagonal fun p => (y p).1), fromBlocks (β⁻¹).1 0 0 (diagonal fun p => ((y p)⁻¹).1),
      by rw [fromBlocks_multiply, diagonal_mul_diagonal]; simp, by rw [fromBlocks_multiply, diagonal_mul_diagonal]; simp⟩
  let Bl' : GL (Fin B.rank) (Lev.EAf D) :=
    ⟨Bl.val.submatrix σ.symm σ.symm, (Bl⁻¹).val.submatrix σ.symm σ.symm,
      by rw [Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv],
      by rw [Matrix.submatrix_mul_equiv, Units.inv_mul, Matrix.submatrix_one_equiv]⟩
  have hBl' : Bl'.val = Bl.val.submatrix σ.symm σ.symm := rfl
  have hBl'i : (Bl'⁻¹).val = (fromBlocks (β⁻¹).1 0 0 (diagonal fun p => ((y p)⁻¹).1)).submatrix σ.symm σ.symm := rfl
  refine ⟨Ua * Bl', ?_, fun w => ?_⟩
  · have hΛ' := eq_lat hβ hΛ
    have e3 : ∀ v : Fin B.rank → Lev.EAf D,
        (fromBlocks (β⁻¹).1 0 0 (diagonal fun p => ((y p)⁻¹).1)).submatrix σ.symm σ.symm *ᵥ v =
          (Sum.elim ((β⁻¹).1 *ᵥ (v ∘ σ ∘ Sum.inl)) (fun p => ((y p)⁻¹).1 * v (σ (Sum.inr p)))) ∘ σ.symm := fun v => by
      rw [submatrix_mulVec_equiv, fromBlocks_mulVec]
      funext i
      rcases h : σ.symm i with k | p <;> simp [h, mulVec_diagonal, Function.comp_def]
    have key : GlobalTheory.NormSum.AdLattice.lat (Ua * Bl') = d.lat Λ 𝔟 := by
      ext x
      obtain ⟨z, rfl⟩ : ∃ z, Cr *ᵥ z = x := ⟨((U⁻¹ : (Matrix _ _ D.host.E)ˣ) : Matrix _ _ D.host.E) *ᵥ x, by
        rw [mulVec_mulVec, ← hU, Units.mul_inv, one_mulVec]⟩
      have hL : Cr *ᵥ z ∈ GlobalTheory.NormSum.AdLattice.lat (Ua * Bl') ↔
          z ∘ σ ∘ Sum.inl ∈ Λ ∧ ∀ p, z (σ (Sum.inr p)) ∈ 𝔟 p := by
        rw [← GlobalTheory.NormSum.AdLattice.mem_lat_rat Ua Bl' Cr hUa z, GlobalTheory.NormSum.AdLattice.mem_lat, hBl'i, e3]
        constructor
        · intro h
          refine ⟨?_, fun p => ?_⟩
          · rw [hΛ', GlobalTheory.NormSum.AdLattice.mem_lat]
            intro k
            have := h (σ (Sum.inl k))
            simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl] at this
            exact this
          · have := h (σ (Sum.inr p))
            simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr] at this
            exact (idele_inv_mul_mem_iff (h𝔟 p) (y p) (hy p) _).1 this
        · rintro ⟨h1, h2⟩ i
          rw [hΛ', GlobalTheory.NormSum.AdLattice.mem_lat] at h1
          rcases h : σ.symm i with k | p
          · simp only [Function.comp_apply, h, Sum.elim_inl]
            exact h1 k
          · simp only [Function.comp_apply, h, Sum.elim_inr]
            exact (idele_inv_mul_mem_iff (h𝔟 p) (y p) (hy p) _).2 (h2 p)
      have hx : Cr *ᵥ z = frameMat B A d.ι *ᵥ (z ∘ σ ∘ Sum.inl) + d.a *ᵥ (z ∘ σ ∘ Sum.inr) := by
        rw [hCrv, hCv]
        rfl
      refine hL.trans ?_
      show _ ↔ ∃ y ∈ Λ, ∃ u : Fin c → D.host.E, (∀ p, u p ∈ 𝔟 p) ∧ Cr *ᵥ z = frameMat B A d.ι *ᵥ y + d.a *ᵥ u
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨_, h1, _, h2, hx⟩
      · rintro ⟨y0, hy0, u, hu, hxu⟩
        have e4 : z ∘ σ = Sum.elim y0 u := hCinj (by rw [← hCrv, hCv, hxu]; rfl)
        refine ⟨?_, fun p => ?_⟩
        · have : z ∘ σ ∘ Sum.inl = y0 := by rw [← Function.comp_assoc, e4]; rfl
          rw [this]
          exact hy0
        · have : z (σ (Sum.inr p)) = u p := congrFun e4 (Sum.inr p)
          rw [this]
          exact hu p
    rw [← key]
    exact isFrame_lat _
  · show ((Ua * Bl').val.map (cpt (D := D) w)).submatrix id (frame d.rank) = _
    rw [Units.val_mul, hUa, hBl', hCrdef, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv, ← Matrix.submatrix_map,
      Matrix.submatrix_submatrix]
    rw [← hσ]
    simp only [Function.comp_id, Equiv.symm_comp_self, Matrix.submatrix_id_id]
    have key : ∀ (M : Matrix (Fin B.rank) (Fin A.rank ⊕ Fin c) (Lev.EAf D)) (N : Matrix (Fin A.rank ⊕ Fin c) (Fin A.rank ⊕ Fin c) (Lev.EAf D)),
        (M * N).map (cpt (D := D) w) = M.map (cpt (D := D) w) * N.map (cpt (D := D) w) :=
      fun M N => Matrix.ext fun i j => by simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]
    have hm2 : (C.map ι).map (cpt (D := D) w) = C.map (algebraMap D.host.E (Kw w)) := Matrix.ext fun i j => hιc w (C i j)
    have e2 : Bl.val.map (cpt (D := D) w) = fromBlocks ((β.val).map (cpt (D := D) w)) 0 0
        (diagonal fun p => cpt (D := D) w (y p).1) := by
      show (fromBlocks β.1 0 0 (diagonal fun p => (y p).1)).map (cpt (D := D) w) = _
      rw [Matrix.fromBlocks_map, Matrix.diagonal_map (map_zero _)]
      simp
    have e1 : C.map (algebraMap D.host.E (Kw w)) = Matrix.fromCols ((frameMat B A d.ι).map (algebraMap D.host.E (Kw w)))
        (d.a.map (algebraMap D.host.E (Kw w))) := by
      rw [hC]
      exact Matrix.ext fun i s => by rcases s with k | p <;> rfl
    rw [key, hm2, e2, e1, fromCols_mul_fromBlocks]
    simp only [Matrix.mul_zero, add_zero, zero_add]
    rfl

theorem exists_gen {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (hI : I ≠ 0) {S : Set (Pl D.host.E)} (hS : S.Finite)
    (u : ∀ Q, Kw Q) (hu : ∀ Q ∈ S, Valued.v (u Q) = WithZero.exp (-FractionalIdeal.count D.host.E Q I)) :
    ∃ y : (Lev.EAf D)ˣ, (∀ Q, Valued.v (cpt (D := D) Q y.1) = WithZero.exp (-FractionalIdeal.count D.host.E Q I)) ∧
      ∀ Q ∈ S, cpt (D := D) Q y.1 = u Q := by
  classical
  obtain ⟨t, ht⟩ := GlobalTheory.Idele.exists_idealOf_eq hI
  have hvt : ∀ Q, Valued.v ((t : FiniteAdeleRing (𝓞 D.host.E) D.host.E) Q) =
      WithZero.exp (-FractionalIdeal.count D.host.E Q I) := fun Q => by
    rw [GlobalTheory.Idele.valued_idele, ← ht, GlobalTheory.Idele.count_idealOf]
  have hu0 : ∀ Q ∈ S, u Q ≠ 0 := fun Q hQ h => by
    have := hu Q hQ
    rw [h, map_zero] at this
    exact WithZero.exp_ne_zero this.symm
  obtain ⟨y, hy⟩ := exists_unit_cpt (D := D)
    (fun Q => if Q ∈ S then u Q else (t : FiniteAdeleRing (𝓞 D.host.E) D.host.E) Q)
    (fun Q => if Q ∈ S then (u Q)⁻¹ else
      ((t⁻¹ : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) : FiniteAdeleRing (𝓞 D.host.E) D.host.E) Q)
    (fun Q => by
      by_cases hQ : Q ∈ S
      · simp only [if_pos hQ]
        exact mul_inv_cancel₀ (hu0 Q hQ)
      · simp only [if_neg hQ]
        exact GlobalTheory.Idele.idele_apply_mul_inv t Q)
    (by
      filter_upwards [hS.compl_mem_cofinite, (t : FiniteAdeleRing (𝓞 D.host.E) D.host.E).2] with Q h1 h2
      rw [if_neg h1]
      exact h2)
    (by
      filter_upwards [hS.compl_mem_cofinite,
        ((t⁻¹ : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) : FiniteAdeleRing (𝓞 D.host.E) D.host.E).2] with Q h1 h2
      rw [if_neg h1]
      exact h2)
  refine ⟨y, fun Q => ?_, fun Q hQ => by rw [hy, if_pos hQ]⟩
  rw [hy]
  split_ifs with hQ
  · exact hu Q hQ
  · exact hvt Q

theorem count_stairId {𝔞 𝔞' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (h : 𝔞 ≠ 0) (h' : 𝔞' ≠ 0) (c : ℕ) (p : Fin c)
    (w : Pl D.host.E) : FractionalIdeal.count D.host.E w (stairId 𝔞 𝔞' c p) =
      ((c - p.1 : ℕ) : ℤ) * FractionalIdeal.count D.host.E w 𝔞 -
        ((p.1 + 1 : ℕ) : ℤ) * FractionalIdeal.count D.host.E w 𝔞' := by
  rw [stairId, FractionalIdeal.count_mul _ _ (pow_ne_zero _ h) (inv_ne_zero (pow_ne_zero _ h')),
    FractionalIdeal.count_inv, FractionalIdeal.count_pow, FractionalIdeal.count_pow]
  ring

theorem ne_zero_of_conj {I J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (hI : I ≠ 0) (h : ∀ x, x ∈ J ↔ star x ∈ I) :
    J ≠ 0 := by
  intro hJ
  obtain ⟨t, ht0, ht⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger hI
  have h1 : star (algebraMap (𝓞 D.host.E) D.host.E t) ∈ J := (h _).2 (by rwa [star_star])
  rw [hJ, FractionalIdeal.mem_zero_iff, star_eq_zero] at h1
  exact ht0 (by simpa using h1)

theorem conjPrime_ne_of_isIdempotentAt {w : Pl D.host.E} {e : AE D} (he : Formalism.L2.NTheta.IsIdemAt e w) :
    GlobalTheory.IdemSupport.cP w ≠ w := by
  intro h
  have h1 := GlobalTheory.IdemSupport.delta_of_isIdemAt (comp_toAd D) he
  have h2 := GlobalTheory.IdemSupport.delta_conj (comp_toAd D) h1
  rw [h] at h2
  have h3 : ((toAd D).comp (toEAf D) (e * cA D e)) w = 0 := by
    rw [he.1.2.1, map_zero]
    rfl
  rw [map_mul] at h3
  change ((toAd D).comp (toEAf D) e) w * ((toAd D).comp (toEAf D) (cA D e)) w = 0 at h3
  rw [h1.2.1, h2.2.1, one_mul] at h3
  exact one_ne_zero h3

theorem conjPl_eq_cP (w : Pl D.host.E) : Formalism.DivisionValues.conjPl w = GlobalTheory.IdemSupport.cP w := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  have hc : ∀ y : 𝓞 D.host.E, Formalism.DivisionValues.cO D.host.E (GlobalTheory.IdemSupport.cO D y) = y := fun y =>
    RingOfIntegers.ext (by rw [Formalism.DivisionValues.ValuationRepresentative.cO_apply, GlobalTheory.IdemSupport.cO_coe, star_star])
  have hc' : ∀ y : 𝓞 D.host.E, GlobalTheory.IdemSupport.cO D (Formalism.DivisionValues.cO D.host.E y) = y := fun y =>
    RingOfIntegers.ext (by rw [GlobalTheory.IdemSupport.cO_coe, Formalism.DivisionValues.ValuationRepresentative.cO_apply, star_star])
  change x ∈ Ideal.map (Formalism.DivisionValues.cO D.host.E) w.asIdeal ↔ x ∈ (GlobalTheory.IdemSupport.cP w).asIdeal
  rw [Ideal.mem_map_of_equiv, GlobalTheory.IdemSupport.mem_cP]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [hc']
  · intro hx
    exact ⟨_, hx, hc x⟩

variable {T : Type} {L : LevCh D T} {sc : Consts}

theorem count_modul (G : GridData L sc) (w : Pl D.host.E) :
    FractionalIdeal.count D.host.E w ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
      cosExp G w := by
  classical
  have hprod : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
      ∏ v ∈ G.pl.S0, ((G.pl.w v).asIdeal : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ G.pl.depth sc v := by
    rw [Places.modul, ← FractionalIdeal.coeIdealHom_apply, map_prod]
    simp only [map_pow, FractionalIdeal.coeIdealHom_apply]
  have hne : ∀ v, ((G.pl.w v).asIdeal : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := fun v => by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact (G.pl.w v).ne_bot
  rw [hprod, FractionalIdeal.count_prod _ _ _ _ fun v _ => pow_ne_zero _ (hne v)]
  have key : ∀ v, FractionalIdeal.count D.host.E w (((G.pl.w v).asIdeal : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^
      G.pl.depth sc v) = if G.pl.w v = w then (G.pl.depth sc v : ℤ) else 0 := fun v => by
    rw [FractionalIdeal.count_pow]
    split_ifs with h
    · rw [h, FractionalIdeal.count_self, mul_one]
    · rw [FractionalIdeal.count_maximal_coprime _ _ h, mul_zero]
  simp only [key]
  rw [cosExp]
  split_ifs with hw
  · obtain ⟨v, hv, rfl⟩ : ∃ v ∈ G.pl.S0, G.pl.w v = w := by simpa [Places.W0] using hw
    rw [Finset.sum_eq_single_of_mem v hv fun v' hv' hne' => if_neg fun h => hne' ?_, if_pos rfl, G.pl.under_w hv]
    rw [← G.pl.under_w hv, ← G.pl.under_w hv', h]
  · refine Finset.sum_eq_zero fun v hv => if_neg fun h => hw ?_
    rw [← h]
    simpa [Places.W0] using ⟨v, hv, rfl⟩

theorem count_modulBar (G : GridData L sc) {t : T} {w : Pl D.host.E} (hw : w ∈ locPl G t) :
    FractionalIdeal.count D.host.E w ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
      0 := by
  have hs : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  have e1 : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
      ((Ideal.map (Formalism.DivisionValues.cO D.host.E) (G.pl.modul sc) : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
    ext x
    constructor
    · intro hx
      have h1 := (GlobalTheory.ChiGrid.StairConj.mem_coe_iff D (G.pl.modul sc) (D.host.conj x)).2
        (by rwa [Formalism.L2.Pj.conj_conj])
      obtain ⟨z, hz, hzx⟩ := (FractionalIdeal.mem_coeIdeal _).1 h1
      refine (FractionalIdeal.mem_coeIdeal _).2 ⟨Formalism.DivisionValues.cO D.host.E z, (Ideal.mem_map_of_equiv _ _).2 ⟨z, hz, rfl⟩, ?_⟩
      show algebraMap (𝓞 D.host.E) D.host.E (Formalism.DivisionValues.cO D.host.E z) = x
      rw [← RingOfIntegers.coe_eq_algebraMap, Formalism.DivisionValues.ValuationRepresentative.cO_apply, RingOfIntegers.coe_eq_algebraMap, hzx, hs,
        Formalism.L2.Pj.conj_conj]
    · intro hx
      obtain ⟨y, hy, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
      obtain ⟨z, hz, rfl⟩ := (Ideal.mem_map_of_equiv _ _).1 hy
      have h1 : D.host.conj (algebraMap (𝓞 D.host.E) D.host.E (Formalism.DivisionValues.cO D.host.E z)) ∈
          ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
        rw [← hs, ← RingOfIntegers.coe_eq_algebraMap, Formalism.DivisionValues.ValuationRepresentative.cO_apply, star_star]
        exact (FractionalIdeal.mem_coeIdeal _).2 ⟨z, hz, rfl⟩
      have h2 := (GlobalTheory.ChiGrid.StairConj.mem_coe_iff D _ _).1 h1
      rwa [Formalism.L2.Pj.conj_conj] at h2
  have h2 := Formalism.DivisionValues.ValuationRepresentative.count_map (Formalism.DivisionValues.conjPl w) (G.pl.modul sc) (G.pl.modul_ne_bot sc)
  rw [Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl] at h2
  rw [e1, h2, count_modul, conjPl_eq_cP, cosExp, if_neg, Nat.cast_zero]
  intro hc
  obtain ⟨v, hv, hvw⟩ : ∃ v ∈ G.pl.S0, G.pl.w v = GlobalTheory.IdemSupport.cP w := by simpa [Places.W0] using hc
  have hu : v = w.under (𝓞 D.host.F) := by
    rw [← G.pl.under_w hv, hvw, GlobalTheory.IdemSupport.under_cP]
  rcases Good.locPl_cases hw with ⟨-, hw2⟩ | ⟨hw1, -, -⟩
  · obtain ⟨e, he⟩ := G.pl.w_split v hv
    apply conjPrime_ne_of_isIdempotentAt he
    have e : G.pl.w v = w := by rw [hu]; exact hw2.symm
    rw [e] at hvw ⊢
    exact hvw.symm
  · exact hw1 (hu ▸ hv)

def rowId (G : GridData L sc) : ∀ j, Fin (D.R.m - 1 - j) → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E
  | 0 => stairId (G.pl.stA sc) (G.pl.stAbar sc) (D.R.m - 1)
  | j + 1 => stairId D.host.AA D.host.AAbar (D.R.m - 1 - (j + 1))

theorem rowLat_eq (G : GridData L sc) : ∀ j (hj : j < D.R.m),
    (G.rowDec j hj).lat (G.Λ (.top j)) (rowId G j) = G.Λ (.grid D.R.m j)
  | 0, h => (G.sp.colLat D.R.m h le_rfl).symm
  | j + 1, h => (G.sp.rowLat j h).symm

theorem rowId_ne_zero (G : GridData L sc) : ∀ j p, rowId G j p ≠ 0 := by
  have h1 := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1
  have h2 := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L G.pl sc
  have key : ∀ {𝔞 𝔞' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E}, 𝔞 ≠ 0 → (∀ x, x ∈ 𝔞' ↔ star x ∈ 𝔞) → ∀ c p,
      stairId 𝔞 𝔞' c p ≠ 0 := fun h h' c p =>
    mul_ne_zero (pow_ne_zero _ h) (inv_ne_zero (pow_ne_zero _ (ne_zero_of_conj h h')))
  intro j p
  cases j with
  | zero => exact key h2.1 h2.2 _ p
  | succ j => exact key h1.1 h1.2 _ p

theorem count_rowId (G : GridData L sc) {t : T} {w : Pl D.host.E} (hw : w ∈ locPl G t)
    (hA : FractionalIdeal.count D.host.E w D.host.AA = 0 ∧ FractionalIdeal.count D.host.E w D.host.AAbar = 0) (j : ℕ)
    (p : Fin (D.R.m - 1 - j)) :
    FractionalIdeal.count D.host.E w (rowId G j p) = ((if j = 0 then cosExp G w * (p.1 + 1) else 0 : ℕ) : ℤ) := by
  have h1 := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1
  have h2 := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L G.pl sc
  have hmo : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact G.pl.modul_ne_bot sc
  have hmb : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    intro h
    have h4 := h2.1
    rw [Places.stA, h, _root_.inv_zero, mul_zero] at h4
    exact h4 rfl
  cases j with
  | zero =>
    rw [if_pos rfl]
    change FractionalIdeal.count D.host.E w (stairId (G.pl.stA sc) (G.pl.stAbar sc) (D.R.m - 1) p) = _
    rw [count_stairId h2.1 (ne_zero_of_conj h2.1 h2.2), Places.stA, Places.stAbar,
      FractionalIdeal.count_mul _ _ h1.1 (inv_ne_zero hmb), FractionalIdeal.count_mul _ _ (ne_zero_of_conj h1.1 h1.2)
        (inv_ne_zero hmo), FractionalIdeal.count_inv, FractionalIdeal.count_inv, count_modulBar G hw, count_modul, hA.1, hA.2]
    push_cast
    ring
  | succ j =>
    rw [if_neg (Nat.succ_ne_zero j)]
    change FractionalIdeal.count D.host.E w (stairId D.host.AA D.host.AAbar _ p) = _
    rw [count_stairId h1.1 (ne_zero_of_conj h1.1 h1.2), hA.1, hA.2]
    simp

theorem valued_frameSign (w : Pl D.host.E) (c : ℕ) (p : Fin c) (k : ℕ) :
    Valued.v (frameSign (Kw w) c p * (unifAt w : Kw w) ^ k) = WithZero.exp (-(k : ℤ)) := by
  have hu : Valued.v (unifAt w : Kw w) = WithZero.exp (-1 : ℤ) := unif_spec w
  have hs : Valued.v (frameSign (Kw w) c p) = 1 := by
    unfold frameSign
    split_ifs
    · rw [Valuation.map_neg, map_one]
    · exact map_one _
  rw [map_mul, hs, one_mul, map_pow, hu, ← WithZero.exp_nsmul]
  congr 1
  simp

variable {G : GridData L sc} (W : G.Weil)

set_option maxHeartbeats 4000000 in

theorem gridChoice_nonempty {U : Set T} (N : Std G U) (Z : Normal W N)
    (hfin : (⋃ t ∈ U, (locPl G t : Set (Pl D.host.E))).Finite)
    (hAA : ∀ t ∈ U, ∀ w ∈ locPl G t,
      FractionalIdeal.count D.host.E w D.host.AA = 0 ∧ FractionalIdeal.count D.host.E w D.host.AAbar = 0) :
    Nonempty (GridChoice W U) := by
  classical
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have hS : ∀ t ∈ U, ∀ w ∈ locPl G t, w ∈ ⋃ t ∈ U, (locPl G t : Set (Pl D.host.E)) := fun t ht w hw =>
    Set.mem_iUnion₂.2 ⟨t, ht, hw⟩
  have hlatTop : ∀ j, j ≤ D.R.m → Submodule.IsLattice D.host.E (G.Λ (.top j)) := fun j hj =>
    (G.isV (X := .top j) hj fun _ e => by cases e).sd.1
  have hb : ∀ j, ∃ β : GL (Fin (G.V (.top j)).rank) (Lev.EAf D), j ≤ D.R.m → IsFrame β (G.Λ (.top j)) := fun j => by
    by_cases hj : j ≤ D.R.m
    · obtain ⟨β, hβ⟩ := GlobalTheory.AdelicFrame.exists_isFrame D.host.F _ (hlatTop j hj).fg (hlatTop j hj).span_eq_top
      exact ⟨β, fun _ => hβ⟩
    · exact ⟨1, fun h => absurd h hj⟩
  choose b0 hb0 using hb
  have hrow : ∀ j (hj : j < D.R.m), ∃ β' : GL (Fin (G.V (.grid D.R.m j)).rank) (Lev.EAf D),
      IsFrame β' (G.Λ (.grid D.R.m j)) ∧ ∀ w ∈ ⋃ t ∈ U, (locPl G t : Set (Pl D.host.E)),
        IsSumFrame (G.rowDec j hj) w (b0 j) β' fun p =>
          frameSign _ _ p * (unifAt w : Kw w) ^ if j = 0 then cosExp G w * (p.1 + 1) else 0 := by
    intro j hj
    have hy : ∀ p : Fin (D.R.m - 1 - j), ∃ y : (Lev.EAf D)ˣ,
        (∀ Q, Valued.v (cpt (D := D) Q y.1) = WithZero.exp (-FractionalIdeal.count D.host.E Q (rowId G j p))) ∧
        ∀ Q ∈ ⋃ t ∈ U, (locPl G t : Set (Pl D.host.E)), cpt (D := D) Q y.1 =
          frameSign (Kw Q) (D.R.m - 1 - j) p * (unifAt Q : Kw Q) ^ if j = 0 then cosExp G Q * (p.1 + 1) else 0 :=
      fun p => exists_gen (rowId_ne_zero G j p) hfin _ fun Q hQ => by
        obtain ⟨t, ht, hQt⟩ := Set.mem_iUnion₂.1 hQ
        rw [valued_frameSign, count_rowId G hQt (hAA t ht Q hQt)]
    choose y hy1 hy2 using hy
    obtain ⟨β', h1, h2⟩ := exists_sumFrame (by norm_num : (-1 : D.host.E) ≠ 0) (G.rowDec j hj) (hlatTop j hj.le)
      (hb0 j hj.le) (rowId_ne_zero G j) y hy1
    refine ⟨β', rowLat_eq G j hj ▸ h1, fun w hw => ?_⟩
    have e : (fun p => cpt (D := D) w (y p).1) = fun p =>
        frameSign (Kw w) (D.R.m - 1 - j) p * (unifAt w : Kw w) ^ if j = 0 then cosExp G w * (p.1 + 1) else 0 :=
      funext fun p => hy2 p w hw
    have := h2 w
    rw [e] at this
    exact this
  have hF : ∀ i j, ∃ f : GL (Fin (G.V (.grid i j)).rank) (Lev.EAf D),
      (1 ≤ i → i ≤ D.R.m → j ≤ D.R.m → IsFrame f (G.Λ (.grid i j))) ∧
      ∀ (hi : i = D.R.m) (hj : j < D.R.m), ∀ w ∈ ⋃ t ∈ U, (locPl G t : Set (Pl D.host.E)),
        IsSumFrame (G.rowDec j hj) w (b0 j) (hi ▸ f) fun p =>
          frameSign _ _ p * (unifAt w : Kw w) ^ if j = 0 then cosExp G w * (p.1 + 1) else 0 := by
    intro i j
    by_cases hij : i = D.R.m ∧ j < D.R.m
    · obtain ⟨rfl, hj⟩ := hij
      obtain ⟨β', h1, h2⟩ := hrow j hj
      exact ⟨β', fun _ _ _ => h1, fun _ _ => h2⟩
    · by_cases hr : 1 ≤ i ∧ i ≤ D.R.m ∧ j ≤ D.R.m
      · have hl := (G.isV (X := .grid i j) ⟨hr.2.1, hr.2.2⟩ fun j' e => by
          cases e
          exact absurd hr.1 (by norm_num)).sd.1
        obtain ⟨β, hβ⟩ := GlobalTheory.AdelicFrame.exists_isFrame D.host.F _ hl.fg hl.span_eq_top
        exact ⟨β, fun _ _ _ => hβ, fun hi hj => absurd ⟨hi, hj⟩ hij⟩
      · exact ⟨1, fun a b c => absurd ⟨a, b, c⟩ hr, fun hi hj => absurd ⟨hi, hj⟩ hij⟩
  choose F hF1 hF2 using hF
  let B : Frames G := ⟨fun i j => match i with
      | 0 => 1
      | k + 1 => F (k + 1) j, fun i j h1 h2 h3 => by
      match i, h1 with
      | k + 1, _ => exact hF1 (k + 1) j (by omega) h2 h3⟩
  have hB : ∀ i j, 1 ≤ i → B.β i j = F i j := fun i j hi => by
    match i, hi with
    | k + 1, _ => rfl
  have hlatm : Submodule.IsLattice D.host.E (G.Λ (.grid D.R.m D.R.m)) :=
    (G.isV (X := .grid D.R.m D.R.m) ⟨le_rfl, le_rfl⟩ fun j' e => by
      injection e with e1 e2
      omega).sd.1
  obtain ⟨βl, hl1, hl2⟩ := exists_sumFrame (one_ne_zero : (1 : D.host.E) ≠ 0) G.sp.topDec hlatm
    (hF1 D.R.m D.R.m hm le_rfl le_rfl) (fun _ => one_ne_zero) (fun _ => 1)
    (fun _ Q => by rw [Units.val_one, map_one, map_one, FractionalIdeal.count_one, neg_zero, WithZero.exp_zero])
  have hl1' : IsFrame βl (G.Λ (.top D.R.m)) := by
    change IsFrame βl (xOf (G.sp.P D.R.m) G.sp.Xs D.R.m).lat
    rw [G.sp.topLat]
    exact hl1
  have hl2' : ∀ w, IsSumFrame G.sp.topDec w (F D.R.m D.R.m) βl 1 := fun w => by
    have := hl2 w
    have e : (fun _ : Fin 1 => cpt (D := D) w ((1 : (Lev.EAf D)ˣ) : Lev.EAf D)) = 1 := funext fun _ => by
      rw [Units.val_one, map_one]
      rfl
    rw [e] at this
    exact this

  obtain ⟨tA, htA⟩ := GlobalTheory.Idele.exists_idealOf_eq (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1.1
  have hfinA : {w : Pl D.host.E | FractionalIdeal.count D.host.E w D.host.AA ≠ 0}.Finite := by
    have := GlobalTheory.Idele.ord_vw_eventually_zero tA
    rw [Filter.eventually_cofinite] at this
    refine this.subset fun w hw => ?_
    simp only [Set.mem_setOf_eq] at hw ⊢
    rwa [← GlobalTheory.Idele.count_idealOf, htA]
  haveI : Nonempty (Pl D.host.E) := ⟨G.pl.w G.pl.v0⟩
  let rep : Pl D.host.F → Pl D.host.E := fun v =>
    Classical.epsilon fun w' => w' ∈ hfinA.toFinset ∧ w'.under (𝓞 D.host.F) = v
  refine ⟨⟨B, Function.update b0 D.R.m βl, fun j hj => ?_, fun t ht w hw j hj => ?_, fun t ht w hw => ?_, N, Z,
    hfinA.toFinset.filter fun w => w = rep (w.under (𝓞 D.host.F)), fun w hw => ?_, fun w hw => ?_⟩⟩
  · rcases eq_or_ne j D.R.m with rfl | hj'
    · rw [Function.update_self]
      exact hl1'
    · rw [Function.update_of_ne hj']
      exact hb0 j hj
  · rw [Function.update_of_ne hj.ne, hB D.R.m j hm]
    exact hF2 D.R.m j rfl hj w (hS t ht w hw)
  · rw [Function.update_self, hB D.R.m D.R.m hm]
    exact hl2' w
  · left
    have := (Finset.mem_filter.1 hw).1
    simpa using this
  · have hspec := Classical.epsilon_spec (p := fun w' => w' ∈ hfinA.toFinset ∧
      w'.under (𝓞 D.host.F) = w.under (𝓞 D.host.F)) ⟨w, by simpa using hw, rfl⟩
    refine ⟨rep (w.under (𝓞 D.host.F)), ⟨Finset.mem_filter.2 ⟨hspec.1, ?_⟩, hspec.2⟩, fun w'' h => ?_⟩
    · change _ = rep _
      rw [hspec.2]
    · obtain ⟨h1, h2⟩ := h
      rw [(Finset.mem_filter.1 h1).2, h2]

theorem coeIdeal_conj_smul (J : Ideal (𝓞 D.host.E)) :
    ((D.host.conj • J : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
      ((Ideal.map (Formalism.DivisionValues.cO D.host.E) J : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
  have hs : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  ext x
  constructor
  · intro hx
    have h1 := (GlobalTheory.ChiGrid.StairConj.mem_coe_iff D J (D.host.conj x)).2 (by rwa [Formalism.L2.Pj.conj_conj])
    obtain ⟨z, hz, hzx⟩ := (FractionalIdeal.mem_coeIdeal _).1 h1
    refine (FractionalIdeal.mem_coeIdeal _).2 ⟨Formalism.DivisionValues.cO D.host.E z, (Ideal.mem_map_of_equiv _ _).2 ⟨z, hz, rfl⟩, ?_⟩
    show algebraMap (𝓞 D.host.E) D.host.E (Formalism.DivisionValues.cO D.host.E z) = x
    rw [← RingOfIntegers.coe_eq_algebraMap, Formalism.DivisionValues.ValuationRepresentative.cO_apply, RingOfIntegers.coe_eq_algebraMap, hzx, hs,
      Formalism.L2.Pj.conj_conj]
  · intro hx
    obtain ⟨y, hy, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
    obtain ⟨z, hz, rfl⟩ := (Ideal.mem_map_of_equiv _ _).1 hy
    have h1 : D.host.conj (algebraMap (𝓞 D.host.E) D.host.E (Formalism.DivisionValues.cO D.host.E z)) ∈
        ((J : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
      rw [← hs, ← RingOfIntegers.coe_eq_algebraMap, Formalism.DivisionValues.ValuationRepresentative.cO_apply, star_star]
      exact (FractionalIdeal.mem_coeIdeal _).2 ⟨z, hz, rfl⟩
    have h2 := (GlobalTheory.ChiGrid.StairConj.mem_coe_iff D _ _).1 h1
    rwa [Formalism.L2.Pj.conj_conj] at h2

theorem count_conj_smul (J : Ideal (𝓞 D.host.E)) (hJ : J ≠ ⊥) (w : Pl D.host.E) :
    FractionalIdeal.count D.host.E w ((D.host.conj • J : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
      FractionalIdeal.count D.host.E (GlobalTheory.IdemSupport.cP w) ((J : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
  have h2 := Formalism.DivisionValues.ValuationRepresentative.count_map (Formalism.DivisionValues.conjPl w) J hJ
  rw [Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl] at h2
  rw [coeIdeal_conj_smul, h2, conjPl_eq_cP]

theorem count_AA_AAbar (w : Pl D.host.E) (hw : ((GlobalTheory.HalfCompare.badInt D : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) :
    FractionalIdeal.count D.host.E w D.host.AA = 0 ∧ FractionalIdeal.count D.host.E w D.host.AAbar = 0 := by
  have hc : D.host.ccE ≠ ⊥ := GlobalTheory.HalfCompare.ccE_ne_bot D
  have hb : D.host.𝔟 ≠ ⊥ := ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI.bb_ne_bot D
  have hne : ∀ J : Ideal (𝓞 D.host.E), J ≠ ⊥ →
      ((D.host.conj • J : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := fun J hJ => by
    rw [coeIdeal_conj_smul, Ne, FractionalIdeal.coeIdeal_eq_zero,
      Ideal.map_eq_bot_iff_of_injective (Formalism.DivisionValues.cO D.host.E).injective]
    exact hJ
  have hne' : ∀ J : Ideal (𝓞 D.host.E), J ≠ ⊥ → ((J : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 :=
    fun J hJ => by rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact hJ
  have hw' : ((GlobalTheory.HalfCompare.badInt D : ℕ) : 𝓞 D.host.E) ∉ (GlobalTheory.IdemSupport.cP w).asIdeal := by
    rwa [GlobalTheory.StdFrames.natCast_mem_cP]
  have h1 : FractionalIdeal.count D.host.E w D.host.AA = 0 := GlobalTheory.HalfCompare.primeToAA_of_not_mem hw
  have h2 : FractionalIdeal.count D.host.E (GlobalTheory.IdemSupport.cP w) D.host.AA = 0 :=
    GlobalTheory.HalfCompare.primeToAA_of_not_mem hw'
  refine ⟨h1, ?_⟩
  unfold Formalism.BasicNotions.Host.AA Formalism.BasicNotions.Host.AA0 at h2
  unfold Formalism.BasicNotions.Host.AAbar
  rw [FractionalIdeal.count_mul _ _ (hne' _ hc) (inv_ne_zero (hne' _ hb)), FractionalIdeal.count_inv] at h2
  rw [FractionalIdeal.count_mul _ _ (hne _ hc) (inv_ne_zero (hne _ hb)), FractionalIdeal.count_inv,
    count_conj_smul _ hc, count_conj_smul _ hb]
  omega

theorem gridChoice_nonempty_of {μ₀ : T} (hL : L.Is μ₀) {U : Set T} (hU : U.Finite)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ t ∈ U, ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) :
    Nonempty (GridChoice W U) := by
  obtain ⟨N⟩ := exists_std G μ₀ hL U hU
  obtain ⟨Z⟩ := normal_nonempty W μ₀ hL U N
  exact gridChoice_nonempty W N Z (hU.biUnion fun t _ => (locPl G t).finite_toSet)
    fun t ht w hw => count_AA_AAbar w (Good.badInt_notMem hL hde (hc t ht) hw)

end GlobalTheory.FunObj

namespace GlobalTheory.FunObj

open GlobalTheory.ChiGrid Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem wtOf_entries_eq {N n : ℕ} (h : N = n) {lam : DomWeight N} {S : Formalism.BasicNotions.TH.SPar}
    (hS : Formalism.IndefR.Bridge.IsWtOfPar lam S) (a : Fin N) :
    (wtOf n (GlobalTheory.SignedHC.entries S)).w (Fin.cast h a) = lam.w a := by
  subst h
  obtain ⟨hcard, c, hc, hmem, hw⟩ := hS
  have hsub : Finset.univ.image c ⊆ GlobalTheory.SignedHC.entries S := fun x hx => by
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨s, hs⟩ := hmem i
    exact Finset.mem_image.2 ⟨(c i, s), hs, rfl⟩
  have hci : (Finset.univ.image c).card = N := by
    rw [Finset.card_image_of_injective _ hc.injective]
    simp
  have hcardE : (GlobalTheory.SignedHC.entries S).card = N := by
    apply le_antisymm
    · rw [← hcard]
      exact Finset.card_image_le
    · rw [← hci]
      exact Finset.card_le_card hsub
  have heq : Finset.univ.image c = GlobalTheory.SignedHC.entries S := Finset.eq_of_subset_of_card_le hsub (by rw [hcardE, hci])
  have hcos : GlobalTheory.SignedHC.InCoset (((N : ℚ) - 1) / 2) (GlobalTheory.SignedHC.entries S) := fun x hx => by
    rw [← heq] at hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    refine ⟨lam.w i - (i : ℕ), ?_⟩
    have := hw i
    unfold Formalism.BasicNotions.rhoVec at this
    push_cast
    linarith
  have h1 := wtOf_cast hcardE hcos a
  have h2 : GlobalTheory.SignedHC.descEnum (GlobalTheory.SignedHC.entries S) hcardE = c :=
    GlobalTheory.SignedHC.descEnum_unique hcardE hc fun i => heq ▸ Finset.mem_image_of_mem c (Finset.mem_univ i)
  have h3 : (((wtOf N (GlobalTheory.SignedHC.entries S)).w a : ℤ) : ℚ) = (lam.w a : ℚ) := by
    rw [h1, GlobalTheory.SignedHC.highestWeight, h2, hw a]
    unfold Formalism.BasicNotions.rhoVec
    ring
  change (wtOf N (GlobalTheory.SignedHC.entries S)).w a = lam.w a
  exact_mod_cast h3

theorem exists_castVV {ι : Type} [Fintype ι] {N n : ℕ} (h : N = n) (lam : ι → DomWeight N) (lam' : ι → DomWeight n)
    (hw : ∀ τ a, (lam' τ).w (Fin.cast h a) = (lam τ).w a) :
    ∃ φ : VV ℂ lam →ₗ[ℂ] VV ℂ lam', ∀ v,
      (φ v).1 = MvPolynomial.rename (Prod.map id (Prod.map (Fin.cast h) (Fin.cast h))) v.1 := by
  subst h
  have e : lam' = lam := funext fun τ => by
    have := hw τ
    generalize lam' τ = a at this
    generalize lam τ = b at this
    cases a
    cases b
    congr
    funext i
    exact this i
  subst e
  refine ⟨LinearMap.id, fun v => ?_⟩
  have : (Prod.map id (Prod.map (Fin.cast rfl) (Fin.cast rfl)) : ι × Fin N × Fin N → ι × Fin N × Fin N) = id := by
    funext x
    rfl
  rw [this, MvPolynomial.rename_id_apply]
  rfl

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts}
  {G : GridData R.toLevCh sc} (W : G.Weil)

theorem sumChoice_nonempty {U : Set T} (S : GridChoice W U) (htie : R.fam_tie)
    (hF : Formalism.IndefR.Bridge.LamRForced (Ptw D)) : Nonempty (SumChoice W U) := by
  obtain ⟨gram, c₀, c₁, ht⟩ := htie
  obtain ⟨e, he⟩ := GlobalTheory.CoefReal.exists_scalarExt D.what₂.embLL _ c₀ ht.mapR.2.1 ht.mapR.2.2
  have hw : ∀ τ a, (listedWt G (.grid 0 D.R.m) τ).w (Fin.cast (rank_zero_m G) a) =
      (Formalism.IndefR.Bridge.lamRdef (Ptw D) τ).w a := fun τ a => by
    change (wtOf _ (GlobalTheory.SignedHC.entries (parV D sc.cGap 0 D.R.m τ))).w _ = _
    rw [parV_zero D sc.cGap le_rfl τ]
    exact wtOf_entries_eq (rank_zero_m G) (hF τ) a
  obtain ⟨φ, hφ⟩ := exists_castVV (rank_zero_m G) _ _ hw
  exact ⟨{ toGridChoice := S, co := φ ∘ₗ e.symm.toLinearMap, co_is := ⟨gram, c₀, c₁, ht, fun v => by
    show (φ (e.symm (c₀ v))).1 = _
    rw [← he, LinearEquiv.symm_apply_apply, hφ, GlobalTheory.CoefModel.mapVV_coe]⟩ }⟩

end GlobalTheory.FunObj
