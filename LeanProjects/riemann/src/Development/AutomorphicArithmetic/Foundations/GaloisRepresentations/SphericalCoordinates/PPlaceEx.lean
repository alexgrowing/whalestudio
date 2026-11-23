import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsRationalEquivOfRank
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsRealPeriodIsoOfPolarizedLattice
import Development.AutomorphicArithmetic.CommutativeAlgebra.LiftBaseChangeRealBijectiveOfLattice
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsUnitaryUnitHermitianFormOfCmLattice
import Development.AutomorphicArithmetic.CommutativeAlgebra.TraceComplexStructurePlaces
import Development.AutomorphicArithmetic.CommutativeAlgebra.HermitianCongruentAndPositiveEigenvectorOfSignat
import Development.AutomorphicArithmetic.CommutativeAlgebra.PositivityIffGramPosDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTripleTrivialOverRealsOfGramCongruent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotMkEqIffPositiveScalarFormIsomorphic

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem typeAt_of {p : ℕ} [Fact p.Prime] (D : Datum p) (ha : D.a = 1) (hm : D.m = 1) (t₀ : D.F →+* ℂ)
    (ht : ∀ i, D.tau i = t₀) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (h : IsSigD D ρ t₀) :
    UpperTheory.ComplexUniformization.TypeAt D ρ := by
  intro c
  have hs : IsSig (algebraMap (𝓞 D.F) D.O) D.inv ρ D.n t₀ (epsD D) := h
  have i0 : Fin D.a := ⟨0, by omega⟩
  have hω : t₀ (D.ω : D.F) = D.ρc := by
    rw [← ht i0]
    exact D.tau_ω i0
  have hre : D.ρc.im ≠ 0 := by
    intro him
    have hr := congrArg Complex.re D.ρc_root
    have hd : ((D.tr : ℝ)) ^ 2 - 4 * (D.nm : ℝ) < 0 := by exact_mod_cast D.disc_neg
    simp [pow_two, him] at hr
    nlinarith [sq_nonneg (2 * D.ρc.re - D.tr)]
  have hsω' : (starRingEnd ℂ) (t₀ (D.ω : D.F)) ≠ D.ρc := by
    rw [hω]
    intro e
    apply hre
    have e2 := congrArg Complex.im e
    simp at e2
    linarith
  have hsω : (ComplexEmbedding.conjugate t₀) (D.ω : D.F) ≠ D.ρc := by
    rwa [ComplexEmbedding.conjugate_coe_eq]
  have hne : t₀ ≠ ComplexEmbedding.conjugate t₀ := fun e => hs.cx t₀ e.symm
  rw [hs.tr c, hm]
  simp only [ht, Finset.sum_const, Finset.card_univ, Fintype.card_fin, ha, one_smul, Nat.cast_one, _root_.one_mul]
  rw [Finset.sum_filter, ← ComplexEmbedding.conjugate_coe_eq]
  have key : ∀ τ : D.F →+* ℂ, (typeMult D.n t₀ (epsD D) τ : ℂ) * τ (c : D.F) =
      ((if τ = t₀ then τ (c : D.F) else 0) - (if τ = ComplexEmbedding.conjugate t₀ then τ (c : D.F) else 0)) +
        (if τ (D.ω : D.F) ≠ D.ρc then (D.n : ℂ) * τ (c : D.F) else 0) := by
    intro τ
    by_cases h1 : τ = t₀
    · subst h1
      simp [typeMult, hne, hω]
    by_cases h2 : τ = ComplexEmbedding.conjugate t₀
    · subst h2
      simp [typeMult, h1, hsω', Nat.cast_sub hs.pos]
      ring
    by_cases h3 : τ (D.ω : D.F) = D.ρc
    · simp [typeMult, h1, h2, h3, epsD]
    · simp [typeMult, h1, h2, h3, epsD]
  rw [Finset.sum_congr rfl (fun τ _ => key τ), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp
  ring

private theorem tens_int (M : Type) [AddCommGroup M] (t : ℚ ⊗[ℤ] M) :
    ∃ (m : ℕ) (u : M), m ≠ 0 ∧ m • t = (1 : ℚ) ⊗ₜ[ℤ] u := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | tmul q u =>
    refine ⟨q.den, q.num • u, q.den_nz, ?_⟩
    rw [TensorProduct.smul_tmul', TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    congr 1
    rw [nsmul_eq_mul, zsmul_eq_mul, _root_.mul_one, _root_.mul_comm]
    exact Rat.mul_den_eq_num q
  | add a b ha hb =>
    obtain ⟨m, u, hm, hu⟩ := ha
    obtain ⟨n, w, hn, hw⟩ := hb
    refine ⟨m * n, n • u + m • w, Nat.mul_ne_zero hm hn, ?_⟩
    rw [smul_add, TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul, ← hu, ← hw,
      mul_smul, smul_comm m n a, mul_smul]

private theorem tmul_inj (M : Type) [AddCommGroup M] [Module.Free ℤ M] :
    Function.Injective (fun u : M => (1 : ℚ) ⊗ₜ[ℤ] u) := by
  have hf : Function.Injective (Algebra.linearMap ℤ ℚ) := fun a b h => by
    simpa using h
  have h1 := Module.Flat.rTensor_preserves_injective_linearMap (M := M) (Algebra.linearMap ℤ ℚ) hf
  intro a b hab
  apply (TensorProduct.lid ℤ M).symm.injective
  apply h1
  simpa [TensorProduct.lid_symm_apply] using hab

private theorem rank_of_period {O : Type} [Ring O] {bar : O → O} {g : ℕ} (ρ : O →+* Matrix (Fin g) (Fin g) ℂ)
    (Y : PLat O bar) (P : Y.La →+ (Fin g → ℂ)) (hP : IsPeriod Y ρ P) : Module.finrank ℤ Y.La = 2 * g := by
  obtain ⟨-, hinj, hdisc, hspan, -⟩ := hP
  let f : Y.La →ₗ[ℤ] (Fin g → ℂ) := P.toIntLinearMap
  have hf : Function.Injective f := hinj
  have hset : ((LinearMap.range f : Submodule ℤ (Fin g → ℂ)) : Set (Fin g → ℂ)) = Set.range P := by
    ext x
    simp [f]
  haveI : DiscreteTopology (LinearMap.range f) := hdisc
  haveI : IsZLattice ℝ (LinearMap.range f) := ⟨by rw [hset]; exact hspan⟩
  rw [(LinearEquiv.ofInjective f hf).finrank_eq, ZLattice.rank ℝ (LinearMap.range f),
    Module.finrank_pi_fintype]
  simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

private theorem rank_datum {p : ℕ} [Fact p.Prime] (D : Datum p) (hm : D.m = 1) : Module.finrank ℤ D.La = 2 * D.g := by
  have hd := NumberField.IsTotallyComplex.finrank D.F
  rw [D.rankLa, Datum.g, hm, hd]
  rw [show 1 * D.n * (2 * NumberField.InfinitePlace.nrComplexPlaces D.F) =
      2 * (D.n * NumberField.InfinitePlace.nrComplexPlaces D.F) by ring, Nat.mul_div_cancel_left _ two_pos]

private theorem sh_mul' {p : ℕ} [Fact p.Prime] (G : HTGroup p) (a b : G.C) : sh G (a * b) = sh G b * sh G a := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

private theorem sh_one' {p : ℕ} [Fact p.Prime] (G : HTGroup p) : sh G (1 : G.C) = 1 := by
  simp only [sh, map_one, MulOpposite.unop_one]

private theorem sh_inv_eq {p : ℕ} [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (h : sh G (β : G.C) = β) :
    sh G ((β⁻¹ : G.Cˣ) : G.C) = ((β⁻¹ : G.Cˣ) : G.C) := by
  have h1 : sh G ((β⁻¹ : G.Cˣ) : G.C) * (β : G.C) = 1 := by
    rw [← h, ← sh_mul', Units.mul_inv, sh_one']
  calc sh G ((β⁻¹ : G.Cˣ) : G.C) = sh G ((β⁻¹ : G.Cˣ) : G.C) * ((β : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) := by
        rw [Units.mul_inv, _root_.mul_one]
    _ = ((β⁻¹ : G.Cˣ) : G.C) := by rw [← _root_.mul_assoc, h1, _root_.one_mul]

private theorem herm_sym {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (x : G.C) (h : sh G x = x) :
    (G.gram v * G.psi v x).IsHermitian := by
  have e : G.psi v x = (G.gram v)⁻¹ * (G.psi v x)ᴴ * G.gram v := by
    have e0 := G.psi_star v x
    rw [show MulOpposite.unop (G.star x) = x from h] at e0
    exact e0
  have hu : IsUnit (G.gram v).det := isUnit_iff_ne_zero.2 (G.gram_det v)
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, (G.gram_herm v).eq]
  conv_rhs => rw [e]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

private theorem sig_zero {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (ha : D.a = 1)
    (v v' : InfinitePlace G.F) (hv : sigPosH (G.gram_herm v) = 1) (hne : v' ≠ v) : sigPosH (G.gram_herm v') = 0 := by
  rcases G.sig v' with h | h
  · exfalso
    obtain ⟨i, hi⟩ := (L.sig v').1 h.1
    obtain ⟨k, hk⟩ := (L.sig v).1 hv
    have hik : i = k := Fin.ext (by omega)
    subst hik
    exact hne (hi.trans hk.symm)
  · exact h.1

private theorem inv_rel {p : ℕ} [Fact p.Prime] (G : HTGroup p) (β β' y : G.Cˣ) (s : ℚ) (hs : 0 < s)
    (hβ : (β' : G.C) = algebraMap ℚ G.C s * (y * β * sh G y)) :
    sh G y * ((β'⁻¹ : G.Cˣ) : G.C) * y = algebraMap ℚ G.C s⁻¹ * ((β⁻¹ : G.Cˣ) : G.C) := by
  have hy : sh G (y : G.C) * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
    rw [← sh_mul', Units.inv_mul, sh_one']
  have hc : algebraMap ℚ G.C s * algebraMap ℚ G.C s⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hs.ne', map_one]
  have hz : (β' : G.C) * (algebraMap ℚ G.C s⁻¹ *
      (sh G ((y⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C) * ((y⁻¹ : G.Cˣ) : G.C))) = 1 := by
    rw [hβ, _root_.mul_assoc, Algebra.left_comm, ← _root_.mul_assoc (algebraMap ℚ G.C s), hc, _root_.one_mul]
    simp only [_root_.mul_assoc]
    rw [← _root_.mul_assoc (sh G (y : G.C)), hy, _root_.one_mul, Units.mul_inv_cancel_left, Units.mul_inv]
  rw [Units.inv_eq_of_mul_eq_one_right hz, Algebra.left_comm, _root_.mul_assoc (algebraMap ℚ G.C s⁻¹)]
  congr 1
  simp only [_root_.mul_assoc]
  rw [Units.inv_mul, _root_.mul_one, ← _root_.mul_assoc, hy, _root_.one_mul]

private theorem place_move {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {β β' y : G.Cˣ} {s : ℚ}
    {D' : PLat D.O D.inv} {j : D'.La →+ VQ D} (h : IsPlace L β D' j) (hs : 0 < s)
    (hβ : (β' : G.C) = algebraMap ℚ G.C s * (y * β * sh G y)) :
    IsPlace L β' D' ((L.rep (y : G.C)).toAddMonoidHom.comp j) := by
  obtain ⟨hinj, hact, hspan, s0, hs0, hEF⟩ := h
  have hRRi : ∀ w, L.rep (y : G.C) (L.rep ((y⁻¹ : G.Cˣ) : G.C) w) = w := fun w => by
    rw [← Module.End.mul_apply, ← map_mul, Units.mul_inv, map_one, Module.End.one_apply]
  have hRiR : ∀ w, L.rep ((y⁻¹ : G.Cˣ) : G.C) (L.rep (y : G.C) w) = w := fun w => by
    rw [← Module.End.mul_apply, ← map_mul, Units.inv_mul, map_one, Module.End.one_apply]
  have key : ∀ a b, formB L β' (L.rep (y : G.C) a) (L.rep (y : G.C) b) = s⁻¹ * formB L β a b := by
    intro a b
    unfold formB
    have hyy : (y : G.C) = sh G (sh G (y : G.C)) := (G.star_star _).symm
    conv_lhs => rw [hyy]
    rw [← L.adj, ← hyy, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
      inv_rel G β β' y s hs hβ, map_mul, Module.End.mul_apply, AlgHom.commutes, Module.algebraMap_end_apply,
      map_smul, LinearMap.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_, ?_, ⟨s0 * s, mul_pos hs0 hs, fun u u' => ?_⟩⟩
  · intro a b hab
    apply hinj
    have e := congrArg (L.rep ((y⁻¹ : G.Cˣ) : G.C)) hab
    simpa [hRiR] using e
  · intro c u
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, hact]
    exact LinearMap.congr_fun ((L.rep_range _).1 ⟨_, rfl⟩ c) (j u)
  · intro w
    obtain ⟨m, u, hm, hu⟩ := hspan (L.rep ((y⁻¹ : G.Cˣ) : G.C) w)
    refine ⟨m, u, hm, ?_⟩
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, ← hu]
    simp [hRRi]
  · simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe]
    rw [hEF, key, ← _root_.mul_assoc, _root_.mul_assoc s0, mul_inv_cancel₀ hs.ne', _root_.mul_one]

theorem UpperTheory.Gal.W2.placeEx_of :
    UpperTheory.Gal.W2.AdCore → UpperTheory.Gal.W2.LatForm → UpperTheory.Gal.W2.PlaceEx := by
  intro hAd _ p _ D G L ha hm v hv t₀ ht ρ hρ N D' t hcls hPe
  obtain ⟨P, hP⟩ := hPe
  haveI := D'.free
  haveI := D'.fin
  have hrk : Module.finrank ℤ D'.La = Module.finrank ℤ D.La := by
    rw [rank_of_period ρ D' P hP, rank_datum D hm]
  have hs : IsSig (algebraMap (𝓞 D.F) D.O) D.inv ρ D.n t₀ (epsD D) := hρ
  obtain ⟨e, he⟩ := UpperTheory.exists_rational_equiv_of_rank p D D' hs.onto hrk
  obtain ⟨β, hβs, hβf⟩ := UpperTheory.exists_unitary_unit_hermitian_form_of_cm_lattice p D G L D' e he
  let j : D'.La →+ VQ D := e.toAddEquiv.toAddMonoidHom.comp (TensorProduct.mk ℤ ℚ D'.La 1).toAddMonoidHom
  have hj : ∀ u, j u = e (1 ⊗ₜ u) := fun u => rfl
  have hinj : Function.Injective j := e.injective.comp (tmul_inj D'.La)
  have hact : ∀ (c : D.O) (u : D'.La), j (c • u) = actQ D c (j u) := by
    intro c u
    rw [hj, hj, ← he c (1 ⊗ₜ u)]
    simp
    rfl
  have hsp : ∀ w : VQ D, ∃ (m : ℕ) (u : D'.La), m ≠ 0 ∧ m • w = j u := by
    intro w
    obtain ⟨m, u, hm0, hmu⟩ := tens_int D'.La (e.symm w)
    refine ⟨m, u, hm0, ?_⟩
    rw [hj, ← hmu, map_nsmul, LinearEquiv.apply_symm_apply]
  have hform : ∀ z z' : D'.La, ((D'.EF z z' : ℤ) : ℚ) =
      2 * (LinearMap.BilinForm.baseChange ℚ D.EF) ((L.rep ((β⁻¹ : G.Cˣ) : G.C)) (j z)) (j z') := by
    intro z z'
    have h0 := hβf (1 ⊗ₜ z) (1 ⊗ₜ z')
    rw [hj, hj]
    simpa using h0
  have hplace : IsPlace L β D' j := by
    refine ⟨hinj, hact, ?_, ⟨2, two_pos, fun u u' => ?_⟩⟩
    · intro w
      obtain ⟨m, u, hm0, hmu⟩ := hsp w
      exact ⟨m, u, hm0, hmu⟩
    · rw [hform]
      rfl
  have hspan : Submodule.span ℚ (Set.range j) = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨m, u, hm0, hmu⟩ := hsp w
    have hw : w = (m : ℚ)⁻¹ • j u := by
      rw [← hmu, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hm0), one_smul]
    rw [hw]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨u, rfl⟩)
  obtain ⟨Φ, Jc, hJ, hΦJ, hΦ, hstar, hpos⟩ := UpperTheory.exists_real_period_iso_of_polarized_lattice p D G L ρ D' P hP j hinj hspan hact β hform
  have hT := typeAt_of D ha hm t₀ ht ρ hρ
  have htr := UpperTheory.trace_complex_structure_places p D G L ρ v ha hT hv Φ Jc hJ hΦ hΦJ
  have hpd := (UpperTheory.positivity_iff_gram_posDef p D G L _ hstar).1 hpos
  have hpsiC : ∀ (v' : InfinitePlace G.F) (x : G.C), G.psiR v' (inC G ℝ x) = G.psi v' x := by
    intro v' x
    show G.psiR v' (1 ⊗ₜ x) = _
    rw [G.psiR_tmul, one_smul]
  have hR : ∃ z, Triv G ℝ (β : G.C) z 1 := by
    apply trivR_of_gram_psi_inv_congr p G β
    intro v'
    have hH := herm_sym G v' _ (sh_inv_eq G β hβs)
    have hJJ : G.psiR v' Jc * G.psiR v' Jc = -1 := by
      rw [← map_mul, hJ, map_neg, map_one]
    have hdelta : sigPosH (G.gram_herm v') = (if v' = v then 1 else 0) := by
      by_cases hvv : v' = v
      · subst hvv
        simpa using hv
      · rw [if_neg hvv]
        exact sig_zero L ha v v' hv hvv
    refine (UpperTheory.hermitian_congruent_and_positive_eigenvector_of_signature G.n (if v' = v then 1 else 0) (G.gram v' * G.psi v' ((β⁻¹ : G.Cˣ) : G.C))
      (G.gram v') (G.psiR v' Jc) (if v'.embedding (L.e D.ω) = D.ρc then Complex.I else -Complex.I) hH
      (G.gram_herm v') (by split_ifs <;> simp) hJJ ?_ ?_ (G.gram_det v') hdelta).1
    · have h1 := hpd v'
      rw [map_mul, hpsiC, ← Matrix.mul_assoc] at h1
      split_ifs at h1 ⊢ <;> simpa using h1
    · rw [htr v']
      split_ifs <;> simp
  obtain ⟨f, ν, -, hw1, hw2⟩ := hcls.1
  have hwit : IsWit D' f ν := by
    refine ⟨hw1, fun n hn hc => ?_⟩
    obtain ⟨a1, a2, a3, a4, a5⟩ := hw2 n hn hc
    refine ⟨a1, a2, a3, a4, fun a a' => ?_⟩
    have h5 := a5 a a'
    simp only [Datum.plat, LinearMap.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] at h5
    exact h5
  obtain ⟨x, c, htriv, -⟩ := hAd p D G L β D' j hplace f ν hwit
  let F : LKCx.Form G := ⟨β, hβs, ⟨x, c, htriv⟩, hR⟩
  obtain ⟨y, s, hs0, hys⟩ := (LKCx.Form.mk_eq_iff_rel p G F
    (Quot.out (Quot.mk LKCx.Form.Rel F : LKCx.FCls G))).1 (Quot.out_eq _).symm
  exact ⟨Quot.mk LKCx.Form.Rel F, _, place_move L hplace hs0 hys⟩
