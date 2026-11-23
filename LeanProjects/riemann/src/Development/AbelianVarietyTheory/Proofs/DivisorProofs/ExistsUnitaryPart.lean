import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulEqOneOfCovolumeIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeoLevelActionIffGeoAct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelGroupLiftExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeBasisHermitianSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedLatticeStabilizerIffBasisIntegralStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PrincipalLevelEqHalfMarkingStabilizer
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelSubgroup

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.LevelReduction

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open Formalism.L2.DIV (oToS idS frGL St pullFr)
open Formalism.IndefR.Lev (finE swapAE EAf)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level)
open GlobalTheory.LevSplit GlobalTheory.IdemSupport GlobalTheory.ParahoricLift GlobalTheory.GeoActCompare
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_gen_pow {E : Type} [Field E] [NumberField E] {I : Ideal (𝓞 E)} (hI : I ≠ ⊥) :
    ∃ x ∈ I, x ≠ 0 ∧ ∀ Q : HeightOneSpectrum (𝓞 E), x ∈ Q.asIdeal → I ≤ Q.asIdeal := by
  let J : nonZeroDivisors (Ideal (𝓞 E)) := ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩
  obtain ⟨h, hh, e⟩ := isOfFinOrder_iff_pow_eq_one.1 (isOfFinOrder_of_finite (ClassGroup.mk0 J))
  rw [← map_pow] at e
  obtain ⟨x, hx⟩ : (I ^ h).IsPrincipal := (ClassGroup.mk0_eq_one_iff (J ^ h).2).1 e
  have hx' : I ^ h = Ideal.span {x} := hx
  refine ⟨x, Ideal.pow_le_self hh.ne' (hx' ▸ Ideal.mem_span_singleton_self x), ?_, fun Q hQ => ?_⟩
  · rintro rfl
    exact pow_ne_zero h hI (by rw [hx']; simp)
  · have := Q.isPrime
    exact Ideal.IsPrime.le_of_pow_le (hx'.le.trans ((Ideal.span_singleton_le_iff_mem _).2 hQ))

theorem map_eq_of_smul_eq {A T : Type} [CommRing A] [CommRing T] {n : ℕ} (S : Subring A) (β : GL (Fin n) A)
    (ψ : S →+* T) (p : S) (hp : ψ p = 1) (y Y : Matrix (Fin n) (Fin n) S)
    (hx : (p : A) • (β.1 * y.map S.subtype * (β⁻¹).1) = (p : A) • (β.1 * Y.map S.subtype * (β⁻¹).1)) :
    y.map ψ = Y.map ψ := by
  have h2 := congrArg (fun M => (β⁻¹).1 * M * β.1) hx
  simp only [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at h2
  simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one] at h2
  ext i j
  have h3 : p * y i j = p * Y i j := Subtype.ext (congrFun (congrFun h2 i) j)
  have h4 := congrArg ψ h3
  rw [map_mul, map_mul, hp, one_mul, one_mul] at h4
  exact h4

theorem map_eq_one_of_sub {R A T : Type} [CommRing R] [CommRing A] [CommRing T] (S : Subring A) (f : R →+* A)
    (ψ : S →+* T) {e : R} {p w x : S} (hp : (p : A) = f e) (hw : (w : A) * x = f (1 - e)) (hx : ψ x = 0) : ψ p = 1 := by
  have h6 : 1 - p = w * x := Subtype.ext (by
    show (1 : A) - p = w * x
    rw [hw, map_sub, map_one, hp])
  have h7 := congrArg ψ h6
  rw [map_mul, hx, mul_zero, map_sub, map_one, sub_eq_zero] at h7
  exact h7.symm

theorem exists_matrix {O : Type} [CommRing O] (I : Ideal O) {n : ℕ} (f : (Fin n → O ⧸ I) ≃ₗ[O] (Fin n → O ⧸ I)) :
    ∃ Y : Matrix (Fin n) (Fin n) O, IsUnit (Ideal.Quotient.mk I Y.det) ∧
      ∀ x, f x = Y.map (Ideal.Quotient.mk I) *ᵥ x := by
  let g : (Fin n → O ⧸ I) ≃ₗ[O ⧸ I] (Fin n → O ⧸ I) := f.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  choose M hM using fun i j => Ideal.Quotient.mk_surjective (LinearMap.toMatrix' g.toLinearMap i j)
  have e : Matrix.map (Matrix.of M) (Ideal.Quotient.mk I) = LinearMap.toMatrix' g.toLinearMap := Matrix.ext hM
  refine ⟨Matrix.of M, ?_, fun x => ?_⟩
  · rw [RingHom.map_det, RingHom.mapMatrix_apply, e, LinearMap.det_toMatrix']
    exact g.isUnit_det'
  · rw [e, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl

variable {D : D7}

theorem exists_div {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} (hΦ : Comp D Φ) {e : AE D} (he : e * e = e)
    {d : 𝓞 D.host.E} (d0 : d ≠ 0) (hd : ∀ Q, Φ e Q ≠ 0 → d ∉ Q.asIdeal) :
    ∃ u : Formalism.L2.Herm.intAf D.host.F D.host.E,
      (u : EAf D) * (oToS D.host.F D.host.E d : Formalism.L2.Herm.intAf D.host.F D.host.E) = finSw D e := by
  refine ⟨⟨_, swapAE_int (not_not.1 fun hn => ?_ : finPart D (e * incA D ((d : D.host.E)⁻¹)) ∈ intAE D)⟩, ?_⟩
  · obtain ⟨Q, h1, h2⟩ := (not_int_iff hΦ he d0).1 hn
    exact hd Q h1 h2
  · show finSw D (e * incA D ((d : D.host.E)⁻¹)) * finSw D (incA D (d : D.host.E)) = _
    have : (d : D.host.E) ≠ 0 := by simpa using d0
    rw [← RingHom.map_mul, mul_assoc, ← RingHom.map_mul, inv_mul_cancel₀ this, RingHom.map_one, mul_one]

theorem exists_idem_finset {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} (hΦ : Comp D Φ)
    (T : Finset (HeightOneSpectrum (𝓞 D.host.E))) (hT : ∀ P ∈ T, cP P ∉ T) :
    ∃ e : AE D, infPart D e = 0 ∧ (∀ Q ∈ T, Φ e Q = 1) ∧ (∀ Q ∉ T, Φ e Q = 0) ∧ ∀ Q ∈ T, Φ (cA D e) Q = 0 := by
  classical
  choose δ hδ using exists_delta hΦ
  have ev : ∀ (f : HeightOneSpectrum (𝓞 D.host.E) → AE D) (s : Finset (HeightOneSpectrum (𝓞 D.host.E))) Q,
      Φ (∑ P ∈ s, f P) Q = ∑ P ∈ s, Φ (f P) Q := by
    intro f s Q
    induction s using Finset.cons_induction with
    | empty => rw [Finset.sum_empty, Finset.sum_empty, ev_zero]
    | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, ev_add, ih]
  refine ⟨∑ P ∈ T, δ P, ?_, fun Q hQ => ?_, fun Q hQ => ?_, fun Q hQ => ?_⟩
  · rw [map_sum]
    exact Finset.sum_eq_zero fun P _ => (hδ P).1
  · rw [ev, Finset.sum_eq_single_of_mem Q hQ fun P _ h => (hδ P).2.2 Q h.symm, (hδ Q).2.1]
  · rw [ev]
    exact Finset.sum_eq_zero fun P hP => (hδ P).2.2 Q fun h => hQ (h ▸ hP)
  · rw [map_sum, ev]
    exact Finset.sum_eq_zero fun P hP => (delta_conj hΦ (hδ P)).2.2 Q fun h => hT P hP (h ▸ hQ)

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E}

theorem exists_half_idem (l : Level H) :
    ∃ (e : AE D) (p : Formalism.L2.Herm.intAf D.host.F D.host.E), e * e = e ∧ e * cA D e = 0 ∧ infPart D e = 0 ∧
      (p : EAf D) = finSw D e ∧ resI D.host.F l.Mb (half_ne_bot l) p = 1 ∧
      ∀ d : 𝓞 D.host.E, IsUnit (Ideal.Quotient.mk l.Mb d) → ∃ u, u * oToS D.host.F D.host.E d = p := by
  classical
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have hT : ∀ Q, Q ∈ (Ideal.finite_factors (half_ne_bot l)).toFinset ↔ l.Mb ≤ Q.asIdeal := fun Q => by
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le]
  generalize (Ideal.finite_factors (half_ne_bot l)).toFinset = T at hT
  obtain ⟨e, h0, h1, h2, h3⟩ := exists_idem_finset hΦ T fun P hP hP' =>
    GlobalTheory.GeoLevel.not_isConjPl_of_le l ((hT _).1 hP) ((hT _).1 hP') ((isConjPl_iff _ _).2 rfl)
  have he : e * e = e := hΦ.ext' (by rw [map_mul, h0, mul_zero]) fun Q => by
    rw [ev_mul]
    by_cases hQ : Q ∈ T
    · rw [h1 Q hQ, mul_one]
    · rw [h2 Q hQ, mul_zero]
  have he' : e * cA D e = 0 := hΦ.ext' (by rw [map_mul, h0, zero_mul, map_zero]) fun Q => by
    rw [ev_mul, ev_zero]
    by_cases hQ : Q ∈ T
    · rw [h3 Q hQ, mul_zero]
    · rw [h2 Q hQ, zero_mul]
  have hdiv : ∀ d : 𝓞 D.host.E, IsUnit (Ideal.Quotient.mk l.Mb d) → ∃ u : Formalism.L2.Herm.intAf D.host.F D.host.E,
      (u : EAf D) * (oToS D.host.F D.host.E d : Formalism.L2.Herm.intAf D.host.F D.host.E) = finSw D e := by
    intro d hd
    have hd' : ∀ Q ∈ T, d ∉ Q.asIdeal := fun Q hQ h => by
      have h4 := hd.map (Ideal.Quotient.factor ((hT Q).1 hQ))
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.2 h] at h4
      have := Q.isPrime
      exact not_isUnit_zero h4
    by_cases d0 : d = 0
    · have : e = 0 := hΦ.ext' (h0.trans (map_zero _).symm) fun Q => by
        rw [ev_zero, h2 Q fun hQ => hd' Q hQ (d0 ▸ zero_mem _)]
      exact ⟨0, by rw [this, map_zero, ZeroMemClass.coe_zero, zero_mul]⟩
    · exact exists_div hΦ he d0 fun Q hQ => hd' Q (by_contra fun h => hQ (h2 Q h))
  obtain ⟨u, hu⟩ := hdiv 1 (by rw [map_one]; exact isUnit_one)
  obtain ⟨p, hp⟩ : ∃ p : Formalism.L2.Herm.intAf D.host.F D.host.E, (p : EAf D) = finSw D e :=
    ⟨u * oToS D.host.F D.host.E 1, hu⟩
  refine ⟨e, p, he, he', h0, hp, ?_, fun d hd => ?_⟩
  · obtain ⟨x, hx, x0, hxQ⟩ := exists_gen_pow (half_ne_bot l)
    obtain ⟨w, hw⟩ := exists_div hΦ (e := 1 - e) (by linear_combination he) x0 fun Q hQ h => hQ (by
      have h5 := ev_add (Φ := Φ) (1 - e) e Q
      rw [sub_add_cancel, map_one, h1 Q ((hT Q).2 (hxQ Q h))] at h5
      exact left_eq_add.1 (h5.trans (add_comm _ _)))
    exact map_eq_one_of_sub _ (finSw D) _ hp hw
      ((resI_oToS l.Mb (half_ne_bot l) x).trans (Ideal.Quotient.eq_zero_iff_mem.2 hx))
  · obtain ⟨u, hu⟩ := hdiv d hd
    exact ⟨u, Subtype.ext (hu.trans hp.symm)⟩

theorem exists_unitary_part (V : HSp D) {e : AE D} (he : e * e = e) (he' : e * cA D e = 0) (hinf : infPart D e = 0)
    (m m' : Matrix (Fin V.rank) (Fin V.rank) (EAf D))
    (h : finSw D e • (m * m') = finSw D e • (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D))) :
    ∃ g : GA D V, Formalism.L2.Theta.SuppAt e V g ∧ finSw D e • (finE V g).1 = finSw D e • m := by
  obtain ⟨M, M', hM, hMM⟩ := part_lift (swapAE D) (swp_bij (F := D.host.F) (E := D.host.E)) (finPart D e) m m' h
  obtain ⟨φ, hφ, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hφ' : ∀ z, (φ z).1 = infPart D z ∧ (φ z).2 = finPart D z := hφ
  have hJK : JR (AF D.host.F) V.gram * (V.gram⁻¹).map (incA D) = 1 := by
    show V.gram.map (incA D) * (V.gram⁻¹).map (incA D) = 1
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (GlobalTheory.UnitaryGlue.gram_det_ne_zero V).isUnit,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hJ : Formalism.UG.cT (cA D) (JR (AF D.host.F) V.gram) = JR (AF D.host.F) V.gram := by
    refine Matrix.ext fun i j => ?_
    show cA D (incA D (V.gram j i)) = incA D (V.gram i j)
    rw [GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.gram_star]
  obtain ⟨g, hg, h1, h2⟩ := GlobalTheory.SplitLift.exists_unitary_prod (infPart D) (finPart D) φ hφ' (cA D)
    GlobalTheory.DualPairCheck.cA_cA _ _ hJ hJK e he he' hinf M M' hMM
  refine ⟨⟨g, hg⟩, h1, ?_⟩
  rw [← hM]
  exact part_map (swapAE D) _ _ _ h2

theorem exists_stab_lift (l : Level H) {V : HSp D} {β : GL (Fin V.rank) (EAf D)}
    (hβ : GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts.IsLatBasis V rfl β) (Y₀ : Matrix (Fin V.rank) (Fin V.rank) (𝓞 D.host.E))
    (hY₀ : IsUnit (Ideal.Quotient.mk l.Mb Y₀.det)) :
    ∃ κ ∈ GfC V, ∃ h : GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts.finR V rfl κ ∈ St β,
      (pullFr β ⟨_, h⟩).1.map (resI D.host.F l.Mb (half_ne_bot l)) = Y₀.map (Ideal.Quotient.mk l.Mb) := by
  have hB := GlobalTheory.GeoLevel.isBaseFrame_of_isLatBasis V β hβ
  obtain ⟨e, p, he, he', hinf, hp, hres, hdiv⟩ := exists_half_idem l
  have hpp : p * p = p := Subtype.ext (by
    show (p : EAf D) * p = p
    rw [hp, ← RingHom.map_mul, he])
  obtain ⟨u, hu⟩ := hdiv _ hY₀
  obtain ⟨Y, hY⟩ : ∃ Y, Y = Y₀.map (oToS D.host.F D.host.E) := ⟨_, rfl⟩
  have hu' : u * Y.det = p := by
    rw [hY, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hu
  have hmm := conj_inv_part β p u Y hu' hpp
  rw [hp] at hmm
  obtain ⟨κ, hs, hκ⟩ := exists_unitary_part V he he' hinf _ _ hmm
  have hsf := supp_fin V (f := e + cA D e) hs
  rw [← hp] at hκ
  have hf : finSw D (e + cA D e) = p + Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) p := by
    rw [RingHom.map_add, finSw_cA, hp]
  have hSt : finE V κ ∈ St β :=
    mem_St_of_part D.sp.cm.sig V.gram _ β hB.1 (hatL_selfDual hB) p u hpp (sigR_int p.2) Y hu' (finE V κ)
      (finE_mem_UA V κ) _ hf hsf hκ
  have hSt' : GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts.finR V rfl κ ∈ St β := by rw [GlobalTheory.GeoLevel.finR_rfl]; exact hSt
  refine ⟨κ, mem_GfC_of_suppF V (f := e + cA D e) ?_ hs, hSt', ?_⟩
  · rw [map_add, (parts_cA e).1, hinf, map_zero, add_zero]
  · have h1 := (Formalism.L2.DIV.frGL_pullFr β ⟨_, hSt'⟩).trans (GlobalTheory.GeoLevel.finR_rfl V κ)
    rw [← h1] at hκ
    rw [map_eq_of_smul_eq _ β _ p hres _ Y hκ, hY]
    exact Matrix.ext fun i j => resI_oToS l.Mb (half_ne_bot l) _

variable {Dw : Datum H}

theorem exists_isLevLift (l : Level H) (V : HSp D) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hι : LatEmb V ι)
    (γ : GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions.LevGrp Dw l) : ∃ κ, GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions.IsLevLift l V ι γ κ := by
  obtain ⟨β, hβ⟩ := GlobalTheory.T.exists_lattice_basis_hermitian_space D V _ rfl
  obtain ⟨φ, hφ⟩ := exists_coord l V rfl β hβ ι hι
  obtain ⟨Y, hY, hf⟩ := exists_matrix l.Mb (φ.symm.trans (LinearEquiv.trans γ φ))
  obtain ⟨κ, h1, h2, h3⟩ := exists_stab_lift l hβ Y hY
  refine ⟨κ, h1, (GlobalTheory.T.completedLattice_stabilizer_iff_basis_integral D V _ rfl β hβ κ).2 h2, (graph_iff φ _ _ (hφ κ h2) γ).1 fun q => ?_⟩
  rw [h3, ← hf, LinearEquiv.trans_apply, φ.symm_apply_apply]
  rfl

open GlobalTheory.UnifEvery in

theorem exists_isReduction : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (V : Formalism.BasicNotions.TH.HSp D) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (@HSpace.rank D.host.E _ _ D.host.cmStar V) → D.host.E)), LatEmb V ι → ∃ red : GlobalTheory.IndefiniteRowSideFullHecke.LiftedCharacterResidue.stabLat V →* GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms.LevelAut Dw l, GlobalTheory.LevDesc.IsReduction V ι red := by
  intro D H Dw l V ι hι
  have hs : ∀ k : GlobalTheory.IndefiniteRowSideFullHecke.LiftedCharacterResidue.stabLat V, (k : GA D V) ∈ GlobalTheory.IndefiniteRowSideFullHecke.EmbeddingLevelSets.levSet V 1 := fun k =>
    mem_levSet_one.2 ⟨k.2.1, fun z hz => (k.2.2 z).2 hz⟩
  have hs' : ∀ {k : GA D V}, k ∈ GlobalTheory.IndefiniteRowSideFullHecke.EmbeddingLevelSets.levSet V 1 → k ∈ GlobalTheory.IndefiniteRowSideFullHecke.LiftedCharacterResidue.stabLat V := fun {k} h =>
    ⟨h.1, fun z => ⟨fun hz => by
      have := GlobalTheory.RecDict.finHom_inv_mulVec_mem V k (mem_levSet_one.1 h).2 _ hz
      rwa [← finHom_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec] at this,
      (mem_levSet_one.1 h).2 z⟩⟩
  choose r hr using fun k : GlobalTheory.IndefiniteRowSideFullHecke.LiftedCharacterResidue.stabLat V => GlobalTheory.T.exists_lattice_automorphism_mod_halfLevel D V H Dw l ι hι k (hs k)
  have hi : ∀ k, Ind V l ι (r k) k := fun k => ⟨hs k, hr k⟩
  obtain ⟨Kf, hK, -⟩ := GlobalTheory.RecDict.exists_isLevelK D V l.M
  have hone := ind_one_iff hι hK ((GlobalTheory.Member.finCong_iff_half_and_kfHalf D H l V).2 Kf hK)
  refine ⟨MonoidHom.mk' r fun a b => (hi (a * b)).unique hι ((hi a).mul hι (hi b)), fun γ => ?_, fun k => ⟨fun h => ?_,
    fun h => ?_⟩, fun k a ha => ?_⟩
  · obtain ⟨κ, hκ⟩ := exists_isLevLift l V ι hι γ
    have h := ind_of_isLevLift hι hκ
    exact ⟨⟨κ, hs' h.1⟩, (hi _).unique hι h⟩
  · have h1 : r k = 1 := h
    exact ⟨k.2, ((hone k).1 (h1 ▸ hi k)).2⟩
  · exact (hi k).unique hι ((hone k).2 ⟨k.2.1, h.2⟩)
  · obtain ⟨w, hw, e⟩ := ((hi k).isLevLift hι).2.2 a ha _ (map_mem_smul_top (liftLa (r k)) ha) (liftLa_spec _ a)
    exact ⟨-w, neg_mem hw, by rw [neg_nsmul, ← e, neg_sub]; rfl⟩

end GlobalTheory.LevelReduction
