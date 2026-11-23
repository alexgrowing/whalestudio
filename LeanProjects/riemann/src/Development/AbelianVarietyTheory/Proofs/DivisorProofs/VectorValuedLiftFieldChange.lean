import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPinsRec
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.MemOfForallLocP
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TensorMapDescent
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FFVMap

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.FieldBC

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IoExtend

section Coef

variable {K K' : Type} [Field K] [Field K'] (j : K →+* K') {σ τ : Type}

def cf (φ : K' →+ K) (P : MvPolynomial σ K') : MvPolynomial σ K :=
  ∑ m ∈ P.support, monomial m (φ (P.coeff m))

theorem coeff_cf (φ : K' →+ K) (P : MvPolynomial σ K') (m : σ →₀ ℕ) : (cf φ P).coeff m = φ (P.coeff m) := by
  classical
  simp only [cf, coeff_sum, coeff_monomial, Finset.sum_ite_eq', mem_support_iff]
  split_ifs with h
  · rfl
  · rw [not_not.1 h, map_zero]

theorem cf_add (φ : K' →+ K) (P Q : MvPolynomial σ K') : cf φ (P + Q) = cf φ P + cf φ Q := by
  ext m; simp [coeff_cf]

theorem cf_zero (φ : K' →+ K) : cf φ (0 : MvPolynomial σ K') = 0 := by
  ext m; simp [coeff_cf]

theorem cf_smul_map {φ : K' →+ K} (hφ : ∀ a x, φ (j a * x) = a * φ x) (x : K') (Q : MvPolynomial σ K) :
    cf φ (x • map j Q) = φ x • Q := by
  ext m
  rw [coeff_cf, coeff_smul, coeff_smul, coeff_map, smul_eq_mul, smul_eq_mul, mul_comm, hφ, mul_comm]

theorem map_smul' (a : K) (Q : MvPolynomial σ K) : map j (a • Q) = j a • map j Q := by
  rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]

theorem cf_comm {φ : K' →+ K} (hφ : ∀ a x, φ (j a * x) = a * φ x)
    (T : MvPolynomial σ K →ₗ[K] MvPolynomial τ K) (T' : MvPolynomial σ K' →ₗ[K'] MvPolynomial τ K')
    (h : ∀ Q, T' (map j Q) = map j (T Q)) (P : MvPolynomial σ K') : cf φ (T' P) = T (cf φ P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial m x =>
    have e : (monomial m x : MvPolynomial σ K') = x • map j (monomial m 1) := by
      rw [map_monomial, map_one, smul_monomial, smul_eq_mul, mul_one]
    rw [e, map_smul, h, cf_smul_map j hφ, cf_smul_map j hφ, map_smul]
  | add p q hp hq => rw [map_add, cf_add, cf_add, map_add, hp, hq]

theorem eq_sum_cf {I : Type} [Fintype I] (e : I → K') (φ : I → K' →+ K) (h : ∀ x, ∑ i, e i * j (φ i x) = x)
    (P : MvPolynomial σ K') : P = ∑ i, e i • map j (cf (φ i) P) := by
  ext m
  simp only [coeff_sum, coeff_smul, coeff_map, coeff_cf, smul_eq_mul, h]

theorem exists_ext (T : MvPolynomial σ K →ₗ[K] MvPolynomial τ K) :
    ∃ T' : MvPolynomial σ K' →ₗ[K'] MvPolynomial τ K', ∀ Q, T' (map j Q) = map j (T Q) := by
  refine ⟨(basisMonomials σ K').constr K' fun m => map j (T (monomial m 1)), fun Q => ?_⟩
  induction Q using MvPolynomial.induction_on' with
  | monomial m x =>
    have e : (monomial m x : MvPolynomial σ K) = x • monomial m 1 := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    have e' : map j (monomial m 1) = basisMonomials σ K' m := by simp
    rw [e, map_smul', map_smul, map_smul, map_smul', e', Module.Basis.constr_basis]
  | add p q hp hq => simp only [map_add, hp, hq]

theorem cf_mem_VV {φ : K' →+ K} (hφ : ∀ a x, φ (j a * x) = a * φ x) {ι : Type} [Fintype ι] {n : ℕ}
    (lam : ι → DomWeight n) {F : Pol K' ι n} (hF : F ∈ VV K' lam) : cf φ F ∈ VV K lam := by
  rw [← (bVVfun_spec K' lam).2] at hF
  have key : ∀ x : K', cf φ (x • F) ∈ VV K lam := by
    induction hF using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      obtain ⟨G, hG, e⟩ := GlobalTheory.Proof.TensorMapDescent.bVVfun_desc j lam i
      intro x
      rw [e, cf_smul_map j hφ]
      exact Submodule.smul_mem _ _ hG
    | zero => intro x; rw [smul_zero, cf_zero]; exact zero_mem _
    | add y z _ _ hy hz => intro x; rw [smul_add, cf_add]; exact add_mem (hy x) (hz x)
    | smul a y _ hy => intro x; rw [smul_smul]; exact hy _
  simpa using key 1

theorem cf_mem_HHa {φ : K' →+ K} (hφ : ∀ a x, φ (j a * x) = a * φ x) {T : Type} {r : T → ℕ} {n : ℕ}
    {cc : T → T} {isX : T → Prop} {a : T → ℕ → ℕ} {P : MvPolynomial (Letter T r n) K'}
    (hP : P ∈ HHa r n K' cc isX a) : cf φ P ∈ HHa r n K cc isX a := by
  obtain ⟨hh, hi, hd⟩ := hP
  refine ⟨?_, ?_, ?_⟩
  · simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker] at hh ⊢
    intro t ht i i'
    rw [← cf_comm j hφ _ (lap r n K' 1 t (cc t) i i'), hh t ht i i', cf_zero]
    intro Q
    simp [lap, Matrix.one_apply, ite_smul, Finset.sum_ite_eq, LinearMap.sum_apply, pderiv_map, map_sum]
  · intro s i i' hlt t
    have := cf_comm j hφ (rowShift r n K s i i' t).toLinearMap (rowShift r n K' s i i' (j t)).toLinearMap ?_ P
    · rw [AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, hi s i i' hlt] at this
      exact this.symm
    · intro Q
      simp only [AlgHom.toLinearMap_apply]
      induction Q using MvPolynomial.induction_on with
      | C x => simp [rowShift]
      | add p q hp hq => simp only [map_add, hp, hq]
      | mul_X p v hp =>
        simp only [map_mul, hp, map_X]
        congr 1
        simp only [rowShift, aeval_X]
        split_ifs <;> simp
  · intro m hm
    refine hd m ?_
    rw [mem_support_iff] at hm ⊢
    intro h0
    exact hm (by rw [coeff_cf, h0, map_zero])

theorem polyAction_map {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (g : ι → GL (Fin n) K)
    (g' : ι → GL (Fin n) K')
    (h : ∀ t, (g' t : Matrix (Fin n) (Fin n) K') = (g t : Matrix (Fin n) (Fin n) K).map j) (F : Pol K ι n) :
    actP lam g' (map j F) = map j (actP lam g F) := by
  have h1 : detTwK lam g' = j (detTwK lam g) := by
    simp only [detTwK, detPow, map_prod, Units.val_zpow_eq_zpow_val, map_zpow₀,
      Matrix.GeneralLinearGroup.val_det_apply, h, RingHom.map_det, RingHom.mapMatrix_apply]
  have h2 : trAct g' (map j F) = map j (trAct g F) := by
    induction F using MvPolynomial.induction_on with
    | C x => simp [trAct]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p v hp =>
      simp only [map_mul, hp, map_X]
      congr 1
      simp [trAct, Formalism.GradedWeylDivisibility.blockAct, h]
  simp only [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_smul', h1, h2]

end Coef

section Int

variable {K K' : Type} [Field K] [Field K'] [NumberField K] [NumberField K'] (j : K →+* K')

theorem map_smul_alg {R k O L σ : Type} [CommRing R] [CommRing k] [Algebra R k] [CommRing O] [CommRing L] [Algebra O L]
    (φ : k →+* L) (ψ : R →+* O) (h : ∀ r, algebraMap O L (ψ r) = φ (algebraMap R k r)) (a : R) (y : MvPolynomial σ k) :
    map φ (a • y) = ψ a • map φ y := by
  rw [← algebraMap_smul k a y, ← algebraMap_smul L (ψ a), smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C, h]

theorem map_mem_nabStd {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) {F : Pol K ι n}
    (hF : F ∈ nabStd K lam) : map j F ∈ nabStd K' lam := by
  unfold nabStd Formalism.GradedWeylDivisibility.tensorLat at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    refine Submodule.subset_span ⟨fun s => map j (f s), fun s => ?_, GlobalTheory.Proof.TensorMapDescent.map_ten j f⟩
    obtain ⟨G, hG, e⟩ := hf s
    refine ⟨map (RingOfIntegers.mapRingHom j) G, Formalism.GradedWeylDivisibility.dualWeylMap _ _ _ n n _ _ hG, ?_⟩
    beta_reduce
    rw [← e, GlobalTheory.NabStab.toK_apply, GlobalTheory.NabStab.toK_apply, map_map, map_map]
    rfl
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [map_smul_alg j (RingOfIntegers.mapRingHom j) (fun _ => rfl)]
    exact Submodule.smul_mem _ _ hx

theorem exists_coords : ∃ (N : ℕ) (e : Fin N → 𝓞 K') (φ : Fin N → K' →+ K),
    (∀ i a x, φ i (j a * x) = a * φ i x) ∧ (∀ x, ∑ i, (e i : K') * j (φ i x) = x) ∧
      ∀ i x, IsIntegral ℤ x → IsIntegral ℤ (φ i x) := by
  classical
  let _ : Algebra K K' := j.toAlgebra
  have : Module.FinitePresentation (𝓞 K) (𝓞 K') := Module.finitePresentation_of_finite _ _
  have : Module.Flat (𝓞 K) (𝓞 K') := inferInstance
  have : Module.Projective (𝓞 K) (𝓞 K') := Module.Flat.projective_of_finitePresentation
  obtain ⟨N, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 K) (𝓞 K')
  have : FiniteDimensional K K' := Module.Finite.of_restrictScalars_finite ℚ K K'
  have hl : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 K') (nonZeroDivisors (𝓞 K))) K' :=
    IsIntegralClosure.isLocalization (𝓞 K) K K' (𝓞 K')
  have hm : IsLocalizedModule (nonZeroDivisors (𝓞 K)) (IsScalarTower.toAlgHom (𝓞 K) (𝓞 K') K').toLinearMap :=
    isLocalizedModule_iff_isLocalization.2 hl
  let φ : Fin N → K' →ₗ[K] K := fun i =>
    IsLocalizedModule.mapExtendScalars (nonZeroDivisors (𝓞 K)) (IsScalarTower.toAlgHom (𝓞 K) (𝓞 K') K').toLinearMap
      (Algebra.linearMap (𝓞 K) K) K (LinearMap.proj i ∘ₗ g)
  have hφ : ∀ i (y : 𝓞 K'), φ i (y : K') = (g y i : K) := fun i y =>
    IsLocalizedModule.mapExtendScalars_apply_apply (nonZeroDivisors (𝓞 K))
      (IsScalarTower.toAlgHom (𝓞 K) (𝓞 K') K').toLinearMap (Algebra.linearMap (𝓞 K) K) K _ _ |>.trans
      (IsLocalizedModule.map_apply _ _ _ _ y)
  have hs : ∀ i a x, φ i (j a * x) = a * φ i x := fun i a x => (φ i).map_smul a x
  refine ⟨N, fun i => f (Pi.single i 1), fun i => (φ i).toAddMonoidHom, hs, fun x => ?_, fun i x hx => ?_⟩
  · have h0 : ∀ y : 𝓞 K', ∑ i, ((f (Pi.single i 1) : 𝓞 K') : K') * j (φ i y) = y := by
      intro y
      have h1 : y = ∑ i, g y i • f (Pi.single i 1) := by
        conv_lhs => rw [← show f (g y) = y from LinearMap.congr_fun hfg y, pi_eq_sum_univ' (g y), map_sum]
        simp only [map_smul]
      conv_rhs => rw [h1]
      simp only [hφ, map_sum, Algebra.smul_def, map_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm]; rfl
    obtain ⟨⟨y, s⟩, hy⟩ := IsLocalizedModule.surj (nonZeroDivisors (𝓞 K))
      (IsScalarTower.toAlgHom (𝓞 K) (𝓞 K') K').toLinearMap x
    have hy' : j ((s : 𝓞 K) : K) * x = (y : K') := by
      rw [← show _ = (y : K') from hy, Submonoid.smul_def, Algebra.smul_def]; rfl
    have hs0 : j ((s : 𝓞 K) : K) ≠ 0 := by
      rw [map_ne_zero]
      exact RingOfIntegers.coe_ne_zero_iff.2 (nonZeroDivisors.ne_zero s.2)
    refine mul_left_cancel₀ hs0 ?_
    rw [hy', ← h0 y, ← hy', Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hs, map_mul]
    show _ * (_ * j (φ i x)) = _
    ring
  · have := hφ i ⟨x, hx⟩
    show IsIntegral ℤ (φ i x)
    rw [show φ i x = _ from this]
    exact (g _ i).isIntegral_coe

end Int

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {c c' : Coeff l} (hle : c.F ≤ c'.F) {n : ℕ}

theorem gaStar_map (ga : Matrix (Fin n) (Fin n) E) (P : MvPolynomial (LtN Dw n) c.F) :
    Formalism.L2.Pj.gaStar c' ga (map (incF c c' hle) P) = map (incF c c' hle) (Formalism.L2.Pj.gaStar c ga P) := by
  induction P using MvPolynomial.induction_on with
  | C x => rw [map_C, Formalism.L2.Pj.gaStar, Formalism.L2.Pj.gaStar, aeval_C, aeval_C, algebraMap_eq, algebraMap_eq, map_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp only [Formalism.L2.Pj.gaStar, aeval_X, letB, map_sum, map_mul, map_C, map_X]
    rfl

theorem pG_map (a : (E →+* ℂ) × ℕ → ℕ) :
    pG (Dw := Dw) c' a n = map (incF c c' hle) (pG (Dw := Dw) c a n) := by
  have h : ∀ s i hi col, minorPolynomial (Dw := Dw) (n := n) c' s i hi col = map (incF c c' hle) (minorPolynomial c s i hi col) := by
    intro s i hi col
    unfold minorPolynomial
    rw [RingHom.map_det]
    congr 1
    ext p q : 2
    simp
  unfold pG
  simp only [map_prod, map_pow]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun i _ => ?_
  congr 1
  split_ifs
  · exact h _ _ _ _
  · exact h _ _ _ _
  · rw [map_zero]

theorem rhoM_map {Ix : Type} [Fintype Ix] (pl : Ix → (E →+* ℂ)) (lam : Ix → DomWeight n)
    (ga : Matrix (Fin n) (Fin n) E) (v : VVc c lam) (v' : VVc c' lam)
    (h : (v' : Pol c'.F Ix n) = map (incF c c' hle) (v : Pol c.F Ix n)) :
    (rhoM c' (fun t => embF c' (pl t)) lam ga v' : Pol c'.F Ix n) =
      map (incF c c' hle) (rhoM c (fun t => embF c (pl t)) lam ga v : Pol c.F Ix n) := by
  unfold rhoM
  split_ifs with hg
  · show actP lam _ (v' : Pol c'.F Ix n) = map _ (actP lam _ (v : Pol c.F Ix n))
    rw [h]
    refine polyAction_map _ lam _ _ (fun t => ?_) _
    rfl
  · simp

end Main

theorem exists_ioLFRec_over : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c c' : Coeff l) (hle : c.F ≤ c'.F) (n : ℕ) (Ix : Type) [Fintype Ix] (pl : Ix → (E →+* ℂ)) (lam : Ix → DomWeight n) (a : (E →+* ℂ) × ℕ → ℕ) (io : VVc c lam →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (hw : VVc c lam), IoLFRec c (fun t => embF c (pl t)) lam a io hw → ∃ (io' : VVc c' lam →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F) (hw' : VVc c' lam), IoLFRec c' (fun t => embF c' (pl t)) lam a io' hw' ∧ IoOver hle lam io io' := by
  intro E _ _ _ H Dw l c c' hle n Ix _ pl lam a io hw ⟨hok, cga, h1, h2, h3, h4, _, _, h7, h8⟩
  obtain ⟨p, hp⟩ := LinearMap.exists_extend io
  obtain ⟨p', hp'⟩ := exists_ext (incF c c' hle) p
  obtain ⟨N, e, φ, hφ, hsum, hint⟩ := exists_coords (incF c c' hle)
  have hpv : ∀ v : VVc c lam, p v = io v := fun v => LinearMap.congr_fun hp v
  let up : VVc c lam → VVc c' lam := fun v => ⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV (incF c c' hle) lam _ v.2⟩
  let io' : VVc c' lam →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F := p' ∘ₗ (VV c'.F lam).subtype
  have hov : IoOver hle lam io io' := by
    intro v v' h
    show p' v' = _
    rw [h, hp', hpv]
  have hup : ∀ v, io' (up v) = map (incF c c' hle) (io v) := fun v => hov v _ rfl
  have hbas : ∀ i, ∃ v, bVV c'.F lam i = up v := by
    intro i
    obtain ⟨F, hF, h⟩ := GlobalTheory.Proof.TensorMapDescent.bVVfun_desc (incF c c' hle) lam i
    exact ⟨⟨F, hF⟩, Subtype.ext ((bVV_coe _ _ _).trans h)⟩
  have hHa : ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)),
      map (incF c c' hle) P ∈ HHa Dw.mult n c'.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) :=
    fun P hP => ⟨PullbackSections.harmK_map _ hP.1, PullbackSections.rowInv_map _ hP.2.1, PullbackSections.rowDeg_map _ hP.2.2⟩
  have hok' : hwOK c' lam (up hw) := by
    show map (incF c c' hle) (hw : Pol c.F Ix n) = _
    rw [show (hw : Pol c.F Ix n) = _ from hok, GlobalTheory.Proof.TensorMapDescent.map_ten]
    simp only [Formalism.L2.DIV.map_extremal]
  obtain ⟨n1, -, -⟩ := GlobalTheory.StdNab.nabAtr_stdLat E c.F Ix n (fun t => embF c (pl t)) lam
  obtain ⟨m1, m2, m3⟩ := GlobalTheory.StdNab.nabAtr_stdLat E c'.F Ix n (fun t => embF c' (pl t)) lam
  refine ⟨io', up hw, ⟨hok', fun ga => incF c c' hle (cga ga), h1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hov⟩
  · rw [injective_iff_map_eq_zero]
    intro v hv
    have h0 : ∀ i, cf (φ i) (v : Pol c'.F Ix n) = 0 := by
      intro i
      have h5 := cf_comm (incF c c' hle) (hφ i) p p' hp' v
      rw [show p' v = 0 from hv, cf_zero] at h5
      have h6 := hpv ⟨_, cf_mem_VV (incF c c' hle) (hφ i) lam v.2⟩
      have := h2 ((h6.symm.trans h5.symm).trans (map_zero io).symm)
      exact congrArg Subtype.val this
    apply Subtype.ext
    rw [eq_sum_cf (incF c c' hle) _ φ hsum (v : Pol c'.F Ix n)]
    simp [h0]
  · apply le_antisymm
    · rw [LinearMap.range_eq_map, ← (bVV c'.F lam).span_eq, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      obtain ⟨v, hv⟩ := hbas i
      rw [hv, hup]
      have hm : io v ∈ LinearMap.range io := LinearMap.mem_range_self _ _
      rw [h3] at hm
      generalize io v = P at hm
      induction hm using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span (hHa x hx)
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul s x _ hx => rw [map_smul']; exact Submodule.smul_mem _ _ hx
    · rw [Submodule.span_le]
      intro P hP
      rw [eq_sum_cf (incF c c' hle) _ φ hsum P]
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
      obtain ⟨v, hv⟩ : cf (φ i) P ∈ LinearMap.range io := by
        rw [h3]
        exact Submodule.subset_span (cf_mem_HHa (incF c c' hle) (hφ i) hP)
      exact ⟨up v, by rw [hup, hv]⟩
  · intro ga hga v
    have : io' ∘ₗ rhoM c' (fun t => embF c' (pl t)) lam ga =
        incF c c' hle (cga ga) • ((Formalism.L2.Pj.gaStar c' (ga.map (IsCMField.complexConj E))).toLinearMap ∘ₗ io') := by
      refine (bVV c'.F lam).ext fun i => ?_
      obtain ⟨u, hu⟩ := hbas i
      rw [hu]
      show io' (rhoM c' (fun t => embF c' (pl t)) lam ga (up u)) =
        incF c c' hle (cga ga) • Formalism.L2.Pj.gaStar c' (ga.map (IsCMField.complexConj E)) (io' (up u))
      rw [hup, hov _ _ (rhoM_map hle pl lam ga u (up u) rfl), h4 ga hga, map_smul', gaStar_map]
    exact LinearMap.congr_fun this v
  · exact (m1 _).2 (by rw [show (up hw : Pol c'.F Ix n) = _ from hok']; exact m2)
  · intro s hs
    refine m3 s ?_
    have := (m1 _).1 hs
    rwa [Submodule.coe_smul, show (up hw : Pol c'.F Ix n) = _ from hok'] at this
  · rw [hup, h7, ← pG_map]
  · intro P hP
    have h9 : ∀ i, ∃ v ∈ nab0M c (fun t => embF c (pl t)) lam, io v = cf (φ i) P := fun i =>
      h8 ⟨cf_mem_HHa (incF c c' hle) (hφ i) hP.1, fun m => by rw [coeff_cf]; exact hint i _ (hP.2 m)⟩
    choose v hv hv' using h9
    refine ⟨∑ i, (e i : c'.F) • up (v i), ?_, ?_⟩
    · refine Submodule.sum_mem _ fun i _ => ?_
      exact Submodule.smul_mem _ (e i) ((m1 (up (v i))).2 (map_mem_nabStd _ lam ((n1 _).1 (hv i))))
    · rw [eq_sum_cf (incF c c' hle) _ φ hsum P, map_sum]
      simp only [map_smul, hup, hv']

end GlobalTheory.IoExtend
