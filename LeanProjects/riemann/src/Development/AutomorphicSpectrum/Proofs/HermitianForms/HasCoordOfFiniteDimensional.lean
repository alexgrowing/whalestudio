import Mathlib
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Formalism.UnipotentAdelicQuotients.StdAdditiveCharExists
import Development.AutomorphicSpectrum.Proofs.HermitianForms.BijectiveLinearCombinationOfRankAtStalk
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.HermitianCharacters.SelfDualLatticeFiltrationCharacter
open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.SelfDualInf

def HasCoord (V : Type) [AddCommGroup V] [TopologicalSpace V] : Prop :=
  ∃ (N : ℕ) (e : V ≃+ (Fin N → ℝ)), Continuous e ∧ Continuous e.symm

theorem HasCoord.of_equiv {V W : Type} [AddCommGroup V] [TopologicalSpace V] [AddCommGroup W]
    [TopologicalSpace W] (e : V ≃+ W) (h1 : Continuous e) (h2 : Continuous e.symm)
    (h : HasCoord W) : HasCoord V := by
  obtain ⟨N, f, g1, g2⟩ := h
  exact ⟨N, e.trans f, g1.comp h1, h2.comp g2⟩

theorem hasCoord_of_finiteDimensional (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] : HasCoord W := by
  let T := (Module.finBasis ℝ W).equivFunL
  exact ⟨_, T.toLinearEquiv.toAddEquiv, T.continuous, T.symm.continuous⟩

theorem HasCoord.pi {V : Type} [AddCommGroup V] [TopologicalSpace V] (h : HasCoord V)
    (ι : Type) [Fintype ι] : HasCoord (ι → V) := by
  obtain ⟨N, f, g1, g2⟩ := h
  refine HasCoord.of_equiv (AddEquiv.piCongrRight fun _ : ι => f) ?_ ?_
    (hasCoord_of_finiteDimensional (ι → Fin N → ℝ))
  · exact continuous_pi fun i => g1.comp (continuous_apply i)
  · exact continuous_pi fun i => g2.comp (continuous_apply i)

theorem HasCoord.fixed {V : Type} [AddCommGroup V] [TopologicalSpace V] (h : HasCoord V)
    (f : V →+ V) (hf : Continuous f) (H : AddSubgroup V) (hH : ∀ x, x ∈ H ↔ f x = x) :
    HasCoord H := by
  obtain ⟨N, e, g1, g2⟩ := h
  let f' : (Fin N → ℝ) →+ (Fin N → ℝ) :=
    (e.toAddMonoidHom.comp f).comp e.symm.toAddMonoidHom
  have hf' : Continuous f' := g1.comp (hf.comp g2)
  let K : Submodule ℝ (Fin N → ℝ) :=
    LinearMap.eqLocus (f'.toRealLinearMap hf' : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ)) LinearMap.id
  have hK : ∀ u, u ∈ K ↔ e (f (e.symm u)) = u := fun u => Iff.rfl
  let T : H ≃+ K :=
    { toFun := fun x => ⟨e x, (hK _).2 (by rw [e.symm_apply_apply, (hH _).1 x.2])⟩
      invFun := fun u => ⟨e.symm u, (hH _).2 (by
        apply e.injective; rw [(hK _).1 u.2, e.apply_symm_apply])⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply _)
      right_inv := fun u => Subtype.ext (e.apply_symm_apply _)
      map_add' := fun x y => Subtype.ext (e.map_add _ _) }
  refine HasCoord.of_equiv T ?_ ?_ (hasCoord_of_finiteDimensional K)
  · exact (g1.comp continuous_subtype_val).subtype_mk _
  · exact (g2.comp continuous_subtype_val).subtype_mk _

theorem HasCoord.secondCountable {V : Type} [AddCommGroup V] [TopologicalSpace V]
    (h : HasCoord V) : SecondCountableTopology V := by
  obtain ⟨N, e, g1, g2⟩ := h
  exact (Homeomorph.mk e.toEquiv g1 g2).secondCountableTopology

theorem HasCoord.char_eq_exp {V : Type} [AddCommGroup V] [TopologicalSpace V] (h : HasCoord V)
    (χ : V → ℂ) (hc : Continuous χ) (ha : ∀ x y, χ (x + y) = χ x * χ y) (hn : ∀ x, ‖χ x‖ = 1) :
    ∃ L : V →+ ℝ, Continuous L ∧ ∀ x, χ x = Complex.exp ((L x : ℂ) * Complex.I) := by
  obtain ⟨N, e, g1, g2⟩ := h
  let f : C((Fin N → ℝ), Circle) :=
    ⟨fun u => ⟨χ (e.symm u), mem_sphere_zero_iff_norm.2 (hn _)⟩,
      (hc.comp g2).subtype_mk fun u => mem_sphere_zero_iff_norm.2 (hn _)⟩
  have hfa : ∀ u v, f (u + v) = f u * f v := fun u v => by
    apply Subtype.ext
    show χ (e.symm (u + v)) = χ (e.symm u) * χ (e.symm v)
    rw [map_add, ha]
  have hf0 : f 0 = 1 := by
    have := hfa 0 0
    rw [add_zero] at this
    exact mul_left_cancel (a := f 0) (by rw [mul_one]; exact this.symm)
  obtain ⟨G, ⟨hG0, hG⟩, -⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 0
    (by rw [hf0]; exact Circle.exp_zero)
  have hGx : ∀ u, Circle.exp (G u) = f u := fun u => congrFun hG u
  have hadd : ∀ u v, G (u + v) = G u + G v := by
    intro u v
    have := Circle.isCoveringMap_exp.eq_of_comp_eq (g₁ := fun u => G (u + v))
      (g₂ := fun u => G u + G v) (by fun_prop) (by fun_prop)
      (by funext u; simp only [Function.comp, Circle.exp_add, hGx, hfa]) 0 (by simp [hG0])
    exact congrFun this u
  refine ⟨(AddMonoidHom.mk' G hadd).comp e.toAddMonoidHom, G.continuous.comp g1, fun x => ?_⟩
  have := congrArg (fun z : Circle => (z : ℂ)) (hGx (e x))
  simp only [Circle.coe_exp] at this
  show χ x = Complex.exp ((G (e x) : ℂ) * Complex.I)
  rw [this]
  show χ x = χ (e.symm (e x))
  rw [e.symm_apply_apply]

theorem HasCoord.exists_selfDual {V : Type} [AddCommGroup V] [TopologicalSpace V]
    [MeasurableSpace V] [BorelSpace V] (h : HasCoord V) (β : V → V → ℝ)
    (ha : ∀ x y y', β x (y + y') = β x y + β x y') (hc : ∀ x, Continuous (β x))
    (hs : ∀ x y, β x y = β y x) (hn : ∀ x, (∀ y, β x y = 0) → x = 0) (χ : V → V → ℂ)
    (hχ : ∀ x y, χ x y = Complex.exp ((β x y : ℂ) * Complex.I)) :
    ∃ μ : Measure V, SelfDual μ χ := by
  obtain ⟨N, e, g1, g2⟩ := h
  let l : V → (Fin N → ℝ) →L[ℝ] ℝ := fun x =>
    ((AddMonoidHom.mk' (β x) (ha x)).comp e.symm.toAddMonoidHom).toRealLinearMap ((hc x).comp g2)
  have hl : ∀ x u, l x u = β x (e.symm u) := fun x u => rfl
  have hexp : ∀ x y, β x y = ∑ j, e y j * β x (e.symm (Pi.single j 1)) := by
    intro x y
    have h1 : e y = ∑ j, e y j • (Pi.single j 1 : Fin N → ℝ) := by
      funext k; simp [Finset.sum_apply, Pi.single_apply]
    have h2 : β x y = l x (e y) := by rw [hl, e.symm_apply_apply]
    rw [h2]
    conv_lhs => rw [h1]
    simp only [map_sum, map_smul, smul_eq_mul]
    rfl
  let A : Matrix (Fin N) (Fin N) ℝ := fun i j =>
    β (e.symm (Pi.single i 1)) (e.symm (Pi.single j 1))
  have hA : ∀ x y, β x y = dotProduct (e x) (A.mulVec (e y)) := by
    intro x y
    rw [hs, hexp]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [hs, hexp]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  refine GlobalTheory.CompanionTheory.SelfDualReal.exists_selfDual V N e A χ g1 g2 ?_ ?_ fun x y => by rw [hχ, hA]
  · ext i j; exact hs _ _
  · intro hd
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
    apply hv0
    have : e.symm v = 0 := hn _ fun y => by
      rw [hs, hA, e.apply_symm_apply, hv, dotProduct_zero]
    simpa using congrArg e this

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)

theorem trace_tmul (r : R) (x : E) : Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] x) =
    r * algebraMap F R (Algebra.trace F E x) := by
  have h : Algebra.lmul R (R ⊗[F] E) (r ⊗ₜ[F] x) =
      r • (Algebra.lmul F E x).baseChange R := by
    refine TensorProduct.AlgebraTensorModule.curry_injective ?_
    ext y
    simp [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul', mul_comm]
  rw [Algebra.trace_apply, h, map_smul, LinearMap.trace_baseChange, smul_eq_mul, Algebra.trace_apply]

theorem sigR_tmul (r : R) (x : E) : sigR R σ (r ⊗ₜ[F] x) = r ⊗ₜ[F] σ x := rfl

theorem sigR_invol (hσ : ∀ x, σ (σ x) = x) (z : R ⊗[F] E) : sigR R σ (sigR R σ z) = z := by
  induction z with
  | zero => simp
  | tmul r x => rw [sigR_tmul, sigR_tmul, hσ]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem sigR_smul (r : R) (z : R ⊗[F] E) : sigR R σ (r • z) = r • sigR R σ z := by
  induction z with
  | zero => simp
  | tmul s x => simp [TensorProduct.smul_tmul', sigR_tmul]
  | add a b ha hb => rw [smul_add, map_add, ha, hb, map_add, smul_add]

def sigLin : R ⊗[F] E →ₗ[R] R ⊗[F] E where
  toFun := sigR R σ
  map_add' := map_add _
  map_smul' := sigR_smul R σ

theorem trace_sigR (hσ : ∀ x, σ (σ x) = x) (z : R ⊗[F] E) :
    Algebra.trace R (R ⊗[F] E) (sigR R σ z) = Algebra.trace R (R ⊗[F] E) z := by
  induction z with
  | zero => simp
  | tmul r x =>
    rw [sigR_tmul, trace_tmul, trace_tmul]
    congr 2
    exact Algebra.trace_eq_of_algEquiv (AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)) x
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

theorem trace_nondeg [Algebra.IsSeparable F E] (z : R ⊗[F] E)
    (h : ∀ u, Algebra.trace R (R ⊗[F] E) (z * u) = 0) : z = 0 := by
  classical
  let b := Module.finBasis F E
  let B := Algebra.traceForm F E
  have hB : B.Nondegenerate := traceForm_nondegenerate F E
  let b' := B.dualBasis hB b
  let c := Algebra.TensorProduct.basis R b
  have hz : z = ∑ i, c.repr z i ⊗ₜ[F] b i := by
    conv_lhs => rw [← c.sum_repr z]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [c, TensorProduct.smul_tmul']
  have hc : ∀ j, c.repr z j = 0 := by
    intro j
    have h1 := h ((1 : R) ⊗ₜ[F] b' j)
    rw [hz, Finset.sum_mul, map_sum] at h1
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, trace_tmul] at h1
    rw [Finset.sum_eq_single j] at h1
    · have h2 : Algebra.trace F E (b j * b' j) = 1 := by
        have := LinearMap.BilinForm.apply_dualBasis_right hB (Algebra.traceForm_isSymm F) b j j
        simpa [B, b', Algebra.traceForm_apply] using this
      rw [h2, map_one, mul_one] at h1
      exact h1
    · intro i _ hij
      have h2 : Algebra.trace F E (b i * b' j) = 0 := by
        have := LinearMap.BilinForm.apply_dualBasis_right hB (Algebra.traceForm_isSymm F) b i j
        simpa [B, b', Algebra.traceForm_apply, hij] using this
      rw [h2, map_zero, mul_zero]
    · simp
  rw [← c.sum_repr z]
  simp [hc]

end Alg

section Form

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)

theorem sigR_JR {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : ∀ i j, σ (J j i) = J i j)
    (i j : Fin M) : sigR R σ (JR R J i j) = JR R J j i := by
  show sigR R σ ((1 : R) ⊗ₜ[F] J i j) = (1 : R) ⊗ₜ[F] J j i
  rw [sigR_tmul, hJ]

theorem sigR_hR (hσ : ∀ x, σ (σ x) = x) {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin M → R ⊗[F] E) :
    sigR R σ (hR R σ J x y) = hR R σ J y x := by
  simp only [hR, hform, map_sum, map_mul, sigR_invol R σ hσ, sigR_JR R σ hJ]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem BR_comm (hσ : ∀ x, σ (σ x) = x) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (X Y : Fin n → Fin M → R ⊗[F] E) :
    BR R σ J X Y = BR R σ J Y X :=
  Finset.sum_congr rfl fun a _ => by rw [← sigR_hR R σ hσ hJ (Y a) (X a), trace_sigR R σ hσ]

theorem BR_add_right {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X Y Y' : Fin n → Fin M → R ⊗[F] E) :
    BR R σ J X (Y + Y') = BR R σ J X Y + BR R σ J X Y' := by
  simp only [BR, hR, hform, Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add]

theorem trace_nondeg_of [Algebra.IsSeparable F E] (L : R →+ ℝ)
    (hL : ∀ t, (∀ r, L (r * t) = 0) → t = 0) (z : R ⊗[F] E)
    (h : ∀ u, L (Algebra.trace R (R ⊗[F] E) (z * u)) = 0) : z = 0 :=
  trace_nondeg R z fun u => hL _ fun r => by
    have := h (r • u)
    rwa [mul_smul_comm, map_smul, smul_eq_mul] at this

theorem BR_nondeg [Algebra.IsSeparable F E] (L : R →+ ℝ)
    (hL : ∀ t, (∀ r, L (r * t) = 0) → t = 0) (hσ : ∀ x, σ (σ x) = x) {M n : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hdet : J.det ≠ 0) (X : Fin n → Fin M → R ⊗[F] E)
    (h : ∀ Y, L (BR R σ J X Y) = 0) : X = 0 := by
  classical
  funext a
  let v : Fin M → R ⊗[F] E := fun i => sigR R σ (X a i)
  have hv : ∀ j, ∑ i, v i * JR R J i j = 0 := by
    intro j
    refine trace_nondeg_of R L hL _ fun u => ?_
    have e : BR R σ J X (Pi.single a (Pi.single j u)) =
        Algebra.trace R (R ⊗[F] E) ((∑ i, v i * JR R J i j) * u) := by
      unfold BR
      rw [Finset.sum_eq_single a]
      · congr 1
        simp [hR, hform, v, Pi.single_apply, Finset.sum_mul]
      · intro c _ hc
        simp [hR, hform, Pi.single_apply, hc]
      · simp
    rw [← e]
    exact h _
  have hinv : JR (F := F) R J * JR (F := F) R J⁻¹ = 1 := by
    unfold JR
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv J (isUnit_iff_ne_zero.2 hdet),
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hv0 : Matrix.vecMul v (JR R J) = 0 := funext fun j => by
    simpa [Matrix.vecMul, dotProduct] using hv j
  have hz : v = 0 := by
    calc v = Matrix.vecMul v (JR (F := F) R J * JR (F := F) R J⁻¹) := by rw [hinv, Matrix.vecMul_one]
      _ = Matrix.vecMul (Matrix.vecMul v (JR (F := F) R J)) (JR (F := F) R J⁻¹) := (Matrix.vecMul_vecMul _ _ _).symm
      _ = 0 := by rw [hv0, Matrix.zero_vecMul]
  funext i
  have := congrArg (sigR R σ) (congrFun hz i)
  simpa [v, sigR_invol R σ hσ] using this

theorem pairHerm_comm (n : ℕ) (S T : HermR R σ n) : pairHerm R σ n S T = pairHerm R σ n T S := by
  unfold pairHerm
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem pairHerm_add_right (n : ℕ) (S T T' : HermR R σ n) :
    pairHerm R σ n S (T + T') = pairHerm R σ n S T + pairHerm R σ n S T' := by
  simp only [pairHerm, AddSubgroup.coe_add, Matrix.add_apply, mul_add, Finset.sum_add_distrib,
    map_add]

def hermUnit (hσ : ∀ x, σ (σ x) = x) (n : ℕ) (a b : Fin n) (u : R ⊗[F] E) : HermR R σ n :=
  ⟨fun i j => (if i = b ∧ j = a then u else 0) + (if i = a ∧ j = b then sigR R σ u else 0), by
    intro i j
    have e1 : (j = b ∧ i = a) ↔ (i = a ∧ j = b) := and_comm
    have e2 : (j = a ∧ i = b) ↔ (i = b ∧ j = a) := and_comm
    simp only [map_add, apply_ite (sigR R σ), map_zero, sigR_invol R σ hσ, e1, e2]
    rw [add_comm]⟩

theorem pairHerm_hermUnit [CharZero F] (hσ : ∀ x, σ (σ x) = x) (n : ℕ) (S : HermR R σ n)
    (a b : Fin n) (u : R ⊗[F] E) :
    pairHerm R σ n S (hermUnit R σ hσ n a b u) = Algebra.trace R (R ⊗[F] E)
      ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) a b * u) := by
  set w := (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) a b * u with hw
  have hs : sigR R σ w = (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) b a * sigR R σ u := by
    rw [hw, map_mul, S.2 b a]
  have hsum : (∑ c, ∑ d, (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) c d *
      (hermUnit R σ hσ n a b u : Matrix (Fin n) (Fin n) (R ⊗[F] E)) d c) = w + sigR R σ w := by
    rw [hs, hw]
    simp [hermUnit, mul_add, Finset.sum_add_distrib, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']
  have h2 : algebraMap F R (1 / 2) * 2 = 1 := by
    rw [show (2 : R) = algebraMap F R 2 from (map_ofNat _ 2).symm, ← map_mul,
      one_div_mul_cancel (two_ne_zero), map_one]
  unfold pairHerm
  rw [hsum, map_add, trace_sigR R σ hσ, ← two_mul, ← mul_assoc, h2, one_mul]

theorem pairHerm_nondeg [CharZero F] [Algebra.IsSeparable F E] (L : R →+ ℝ)
    (hL : ∀ t, (∀ r, L (r * t) = 0) → t = 0) (hσ : ∀ x, σ (σ x) = x) (n : ℕ) (S : HermR R σ n)
    (h : ∀ T, L (pairHerm R σ n S T) = 0) : S = 0 := by
  apply Subtype.ext
  funext a b
  refine trace_nondeg_of R L hL _ fun u => ?_
  rw [← pairHerm_hermUnit R σ hσ n S a b u]
  exact h _

end Form

section Top

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  (σ : E →ₐ[F] E)

theorem isModuleTopology_tens : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩

theorem isTopologicalRing_tens : IsTopologicalRing (R ⊗[F] E) :=
  have := isModuleTopology_tens (F := F) (E := E) R
  IsModuleTopology.isTopologicalRing R (R ⊗[F] E)

theorem continuous_trace : Continuous (Algebra.trace R (R ⊗[F] E)) :=
  have := isModuleTopology_tens (F := F) (E := E) R
  have := isTopologicalRing_tens (F := F) (E := E) R
  IsModuleTopology.continuous_of_linearMap _

theorem continuous_sigR : Continuous (sigR R σ) :=
  have := isModuleTopology_tens (F := F) (E := E) R
  have := isTopologicalRing_tens (F := F) (E := E) R
  IsModuleTopology.continuous_of_linearMap (sigLin R σ)

theorem continuous_BR {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) : Continuous (BR R σ J X) := by
  have := isTopologicalRing_tens (F := F) (E := E) R
  show Continuous fun Y : Fin n → Fin M → R ⊗[F] E => ∑ a, Algebra.trace R (R ⊗[F] E)
    (∑ i, ∑ j, sigR R σ (X a i) * JR R J i j * Y a j)
  exact continuous_finset_sum _ fun a _ => (continuous_trace R).comp
    (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      continuous_const.mul ((continuous_apply j).comp (continuous_apply a)))

theorem continuous_pairHerm (n : ℕ) (S : HermR R σ n) : Continuous (pairHerm R σ n S) := by
  have := isTopologicalRing_tens (F := F) (E := E) R
  show Continuous fun T : HermR R σ n => algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E)
    (∑ a, ∑ b, (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) a b * (T : Matrix (Fin n) (Fin n) _) b a)
  exact continuous_const.mul ((continuous_trace R).comp
    (continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ =>
      continuous_const.mul (continuous_subtype_val.matrix_elem b a)))

theorem hasCoord_tens (h : HasCoord R) : HasCoord (R ⊗[F] E) := by
  have := isModuleTopology_tens (F := F) (E := E) R
  have := isTopologicalRing_tens (F := F) (E := E) R
  let e := (Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun
  exact HasCoord.of_equiv e.toAddEquiv (IsModuleTopology.continuous_of_linearMap e.toLinearMap)
    (IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap) (h.pi _)

theorem hasCoord_herm (h : HasCoord R) (n : ℕ) (hσ : ∀ x, σ (σ x) = x) :
    HasCoord (HermR R σ n) := by
  have := isTopologicalRing_tens (F := F) (E := E) R
  have hm : HasCoord (Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    ((hasCoord_tens R h).pi (Fin n)).pi (Fin n)
  let f : Matrix (Fin n) (Fin n) (R ⊗[F] E) →+ Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
    AddMonoidHom.mk' (fun S => (S.map (sigR R σ)).transpose) fun S T => by
      ext i j; simp
  have hf : Continuous f := ((continuous_id.matrix_map (continuous_sigR R σ))).matrix_transpose
  refine hm.fixed f hf _ fun S => ⟨fun hS => ?_, fun hS a b => ?_⟩
  · ext a b; exact hS a b
  · exact congrFun (congrFun hS a) b

end Top

section Arch

variable {F : Type} [Field F] [NumberField F]

theorem hasCoord_ainf (hF : IsTotallyReal F) : HasCoord (Ainf F) := by
  let ρ := fun w : InfinitePlace F => InfinitePlace.Completion.ringEquivRealOfIsReal (hF.isReal w)
  have h1 : ∀ w, Continuous (ρ w) := fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (hF.isReal w)).continuous
  have h2 : ∀ w, Continuous (ρ w).symm := fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (hF.isReal w)).symm.continuous
  exact HasCoord.of_equiv (AddEquiv.piCongrRight fun w => (ρ w).toAddEquiv)
    (continuous_pi fun w => (h1 w).comp (continuous_apply w))
    (continuous_pi fun w => (h2 w).comp (continuous_apply w))
    (hasCoord_of_finiteDimensional (InfinitePlace F → ℝ))

theorem psiInf_add (ψ : AddChar (AF F) ℂ) (x y : Ainf F) :
    psiInf F ψ (x + y) = psiInf F ψ x * psiInf F ψ y := by
  unfold psiInf
  rw [← AddChar.map_add_eq_mul]
  congr 1
  exact Prod.ext rfl (add_zero _).symm

theorem exists_functional (hF : IsTotallyReal F) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) :
    ∃ L : Ainf F →+ ℝ, Continuous L ∧
      (∀ x, psiInf F ψ x = Complex.exp ((L x : ℂ) * Complex.I)) ∧
      ∀ t, (∀ r, L (r * t) = 0) → t = 0 := by
  obtain ⟨-, hc, hw⟩ := GlobalTheory.CompanionTheory.AdeleCharLocal.char_nontrivial_at_every_place F ψ hψ
  obtain ⟨L, hL, hx⟩ := (hasCoord_ainf hF).char_eq_exp _ hc (psiInf_add ψ) fun x => hψ.2.1 _
  refine ⟨L, hL, hx, fun t ht => ?_⟩
  funext w
  by_contra h0
  obtain ⟨x, hx0, hx1⟩ := hw w
  let r : Ainf F := fun u => x u * (t u)⁻¹
  have hr : r * t = x := by
    funext u
    show x u * (t u)⁻¹ * t u = x u
    by_cases hu : u = w
    · subst hu
      exact inv_mul_cancel_right₀ h0 _
    · rw [hx0 u hu, zero_mul, zero_mul]
  apply hx1
  have := ht r
  rw [hr] at this
  rw [hx, this]
  simp

end Arch

theorem exists_sdW_sdHerm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → (∃ μ, SdW F E σ M J (Ainf F) (psiInf F ψ) n μ) ∧ ∃ ν, SdHerm F E σ (Ainf F) (psiInf F ψ) n ν := by
  intro F E _ _ _ _ _ σ hCM M J hJ n ψ hψ
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hσ : ∀ x, σ (σ x) = x := by
    intro x
    let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ) : E →ₐ[ℚ] ℂ).toRingHom
    apply τ.injective
    rw [hCM.2.2.2, hCM.2.2.2, star_star]
  obtain ⟨L, hLc, hLx, hLn⟩ := exists_functional hCM.1 ψ hψ
  have hA := hasCoord_ainf hCM.1
  have hT := hasCoord_tens (F := F) (E := E) (Ainf F) hA
  have := hT.secondCountable
  have : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR (Ainf F) σ n) := ⟨rfl⟩
  constructor
  · exact ((hT.pi (Fin M)).pi (Fin n)).exists_selfDual (fun X Y => L (BR (Ainf F) σ J X Y))
      (fun X Y Y' => by rw [BR_add_right, map_add])
      (fun X => hLc.comp (continuous_BR (Ainf F) σ J X))
      (fun X Y => by rw [BR_comm (Ainf F) σ hσ hJ.1])
      (fun X h => BR_nondeg (Ainf F) σ L hLn hσ hJ.2 X h) _ (fun X Y => hLx _)
  · exact (hasCoord_herm (Ainf F) σ hA n hσ).exists_selfDual
      (fun S T => L (pairHerm (Ainf F) σ n S T))
      (fun S T T' => by rw [pairHerm_add_right, map_add])
      (fun S => hLc.comp (continuous_pairHerm (Ainf F) σ n S))
      (fun S T => by rw [pairHerm_comm])
      (fun S h => pairHerm_nondeg (Ainf F) σ L hLn hσ n S h) _ (fun S T => hLx _)

end GlobalTheory.CompanionTheory.SelfDualInf
