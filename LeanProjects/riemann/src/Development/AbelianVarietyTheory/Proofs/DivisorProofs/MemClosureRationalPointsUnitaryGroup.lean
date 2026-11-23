import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLocAdele
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureDivMem

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

namespace GlobalTheory.SUWeakApprox

section Abstract

open Formalism.UG Matrix

theorem exists_aniso {K : Type} [Field K] (c : K →+* K) (hne : ∃ z, c z ≠ z) {n : ℕ} (hn : 0 < n)
    (J : Matrix (Fin n) (Fin n) K) (hdet : J.det ≠ 0) :
    ∃ x : Fin n → K, (c ∘ x) ⬝ᵥ (J *ᵥ x) ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨z, hz⟩ := hne
  have hs : ∀ (i : Fin n) (t : K), c ∘ (Pi.single i t : Fin n → K) = Pi.single i (c t) := by
    intro i t
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  have hd : ∀ i, J i i = 0 := by
    intro i
    have := h (Pi.single i 1)
    simpa [hs] using this
  have ho : ∀ i j t, J i j * t + c t * J j i = 0 := by
    intro i j t
    have := h (Pi.single i 1 + Pi.single j t)
    have e : c ∘ (Pi.single i 1 + Pi.single j t : Fin n → K) = Pi.single i 1 + Pi.single j (c t) := by
      have e1 := hs i 1
      rw [map_one] at e1
      calc _ = c ∘ (Pi.single i 1 : Fin n → K) + c ∘ (Pi.single j t : Fin n → K) := funext fun k => map_add c _ _
        _ = _ := by rw [e1, hs]
    rw [e] at this
    simp only [mulVec_add, add_dotProduct, dotProduct_add, single_dotProduct, mulVec_single, Pi.smul_apply, col_apply, hd] at this
    simpa [add_comm] using this
  have hJ : J = 0 := by
    ext i j
    have h1 := ho i j 1
    have h2 := ho i j z
    rw [map_one] at h1
    have : (z - c z) * J i j = 0 := by linear_combination h2 - c z * h1
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hz.symm)
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact hdet (by rw [hJ, det_zero])

theorem exists_proj {K : Type} [Field K] (c : K →+* K) (hc : ∀ x, c (c x) = x) (hne : ∃ z, c z ≠ z) {n : ℕ}
    (hn : 0 < n) (J : Matrix (Fin n) (Fin n) K) (hJ : cT c J = J) (hdet : J.det ≠ 0) :
    ∃ P : Matrix (Fin n) (Fin n) K, P * P = P ∧ cT c P * J = J * P ∧ ∀ a : K, (1 + a • P).det = 1 + a := by
  obtain ⟨x, hx⟩ := exists_aniso c hne hn J hdet
  have hJ' : ∀ i j, c (J j i) = J i j := fun i j => congrFun (congrFun hJ i) j
  set d := (c ∘ x) ⬝ᵥ (J *ᵥ x) with hd
  set y : Fin n → K := (c ∘ x) ᵥ* J with hy
  have hyx : y ⬝ᵥ x = d := by rw [hd, dotProduct_mulVec]
  have hcy : c ∘ y = J *ᵥ x := by
    funext i
    simp [hy, vecMul, mulVec, dotProduct, map_sum, hc, hJ', mul_comm]
  have hcd : c d = d := by
    conv_lhs => rw [← hyx]
    rw [hd, ← hcy]
    simp [dotProduct, map_sum, mul_comm]
  refine ⟨d⁻¹ • vecMulVec x y, ?_, ?_, fun a => ?_⟩
  · rw [smul_mul_assoc, mul_smul_comm, vecMulVec_mul_vecMulVec, hyx, vecMulVec_smul, smul_smul d⁻¹ d,
      inv_mul_cancel₀ hx, one_smul]
  · have e : cT c (d⁻¹ • vecMulVec x y) = d⁻¹ • vecMulVec (c ∘ y) (c ∘ x) := by
      ext i j
      simp [cT, vecMulVec_apply, hcd, mul_comm]
    rw [e, smul_mul_assoc, mul_smul_comm, vecMulVec_mul, mul_vecMulVec, hcy]
  · rw [smul_smul, ← smul_vecMulVec, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow,
      dotProduct_smul, hyx, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hx, mul_one]

theorem mem_closure_su {K R : Type} [Field K] [CharZero K] [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsArtinianRing R] (ι : K →+* R) (c : K →+* K) (σ : R →+* R)
    (hσι : ∀ x, σ (ι x) = ι (c x)) (hc : ∀ x, c (c x) = x) (hne : ∃ z, c z ≠ z) (hσ : ∀ x, σ (σ x) = x)
    (hσc : Continuous σ) (hd : DenseRange ι) (h1 : IsOpen {x : R | IsUnit x})
    (h2 : ∀ x : R, IsUnit x → ContinuousAt Ring.inverse x) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) K) (hJ : cT c J = J) (hdet : J.det ≠ 0)
    (g : Matrix (Fin n) (Fin n) R) (hg : cT σ g * J.map ι * g = J.map ι) (hg1 : g.det = 1) :
    g ∈ closure {m | ∃ γ : Matrix (Fin n) (Fin n) K, cT c γ * J * γ = J ∧ γ.det = 1 ∧ m = γ.map ι} := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact subset_closure ⟨1, by rw [cT_one, Matrix.one_mul, Matrix.mul_one], det_one, Subsingleton.elim _ _⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact subset_closure ⟨1, by rw [cT_one, Matrix.one_mul, Matrix.mul_one], det_one, Subsingleton.elim _ _⟩
  obtain ⟨P, hPP, hPJ, hPd⟩ := exists_proj c hc hne hn J hJ hdet
  have h := GlobalTheory.RealApprox.mem_closure_unitary ι c σ hσι hc hne hσ hσc hd h1 h2 Jᵀ
    (by rw [Matrix.transpose_map]; exact congrArg Matrix.transpose hJ) (by rwa [Matrix.det_transpose]) g
    (by rw [Matrix.transpose_map]; exact (GlobalTheory.Mass.OnePlace.unitary_transpose _ _ _).1 hg)
  let Ψ : Matrix (Fin n) (Fin n) R → Matrix (Fin n) (Fin n) R := fun m => m * (1 + (σ m.det - 1) • P.map ι)
  have hΨ : Continuous Ψ :=
    continuous_id.matrix_mul (continuous_const.add
      (((hσc.comp continuous_id.matrix_det).sub continuous_const).smul continuous_const))
  have hΨg : Ψ g = g := by simp [Ψ, hg1]
  rw [← hΨg]
  refine hΨ.continuousWithinAt.mem_closure h ?_
  rintro _ ⟨γ, hγ, rfl⟩
  have hγ' : cT c γ * J * γ = J := (GlobalTheory.Mass.OnePlace.unitary_transpose _ _ _).2 hγ
  have hN : c γ.det * γ.det = 1 := by
    have := congrArg Matrix.det hγ'
    rw [det_mul, det_mul, cT, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
    apply mul_right_cancel₀ hdet
    linear_combination this
  refine ⟨γ * (1 + (c γ.det - 1) • P), ?_, ?_, ?_⟩
  · have e : cT c (1 + (c γ.det - 1) • P) = 1 + (γ.det - 1) • cT c P := by
      ext i j
      simp [cT, hc, one_apply, eq_comm]
    rw [cT_mul, e, Matrix.mul_assoc _ _ J, Matrix.mul_assoc, ← Matrix.mul_assoc _ γ, hγ', ← Matrix.mul_assoc]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hPJ,
      Matrix.mul_assoc, hPP, smul_add, smul_smul]
    rw [add_assoc, ← add_smul, ← add_smul,
      show γ.det - 1 + (c γ.det - 1 + (c γ.det - 1) * (γ.det - 1)) = 0 by linear_combination hN, zero_smul, add_zero]
  · rw [det_mul, hPd]
    linear_combination hN
  · simp only [Ψ]
    rw [Matrix.map_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hσι, Matrix.map_add _ (map_add ι),
      Matrix.map_one _ (map_zero ι) (map_one ι), GlobalTheory.UnRep.WeakApprox.map_smul'', map_sub, map_one]

end Abstract

section Transfer

open Matrix
open Formalism.UG hiding sigR

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem sigR_inclR (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (x : E) :
    sigR R σ (inclR (F := F) R x) = inclR (F := F) R (σ x) := by
  simp [sigR, inclR]

theorem sigR_sigR (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (hc : ∀ x, σ (σ x) = x) (x : R ⊗[F] E) :
    sigR R σ (sigR R σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => simp [sigR, hc]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem continuous_sigR (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    (σ : E →ₐ[F] E) : Continuous (sigR R σ) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
  exact IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.map (AlgHom.id R R) σ).toLinearMap

theorem denseRange_inclR (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [FiniteDimensional F E] (hd : DenseRange (algebraMap F R)) : DenseRange (inclR (F := F) (E := E) R) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  intro y
  let S : AddSubgroup (R ⊗[F] E) := (inclR (F := F) (E := E) R).toAddMonoidHom.range.topologicalClosure
  have hS : IsClosed (S : Set (R ⊗[F] E)) := AddSubgroup.isClosed_topologicalClosure _
  show y ∈ S
  induction y using TensorProduct.induction_on with
  | zero => exact S.zero_mem
  | add a b ha hb => exact S.add_mem ha hb
  | tmul a x =>
    have hc : Continuous fun a : R => a ⊗ₜ[F] x := by
      have : (fun a : R => a ⊗ₜ[F] x) = fun a : R => a • ((1 : R) ⊗ₜ[F] x) := by
        funext a
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]
      exact Continuous.smul (f := fun a : R => a) (g := fun _ : R => ((1 : R) ⊗ₜ[F] x : R ⊗[F] E))
        continuous_id continuous_const
    refine DenseRange.induction_on hd a (p := fun a => a ⊗ₜ[F] x ∈ S) (hS.preimage hc) fun f => ?_
    refine AddSubgroup.le_topologicalClosure _ ⟨f • x, ?_⟩
    show (1 : R) ⊗ₜ[F] (f • x) = algebraMap F _ f ⊗ₜ[F] x
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem mem_closure_trunc [CharZero E] [FiniteDimensional F E] (A B : Type) [CommRing A] [Algebra F A]
    [TopologicalSpace A] [IsTopologicalRing A] [CommRing B] [Algebra F B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsArtinianRing B] (π : A →ₐ[F] B) (s : B → A) (hs : Continuous s) (η : A) (hη : ∀ a, s (π a) = η * a)
    (hd : DenseRange (algebraMap F B)) (h1 : IsOpen {x : B | IsUnit x})
    (h2 : ∀ x : B, IsUnit x → ContinuousAt Ring.inverse x)
    (σ : E →ₐ[F] E) (hc : ∀ x, σ (σ x) = x) (hne : ∃ z, σ z ≠ z) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : cT (σ : E →+* E) J = J) (hdet : J.det ≠ 0)
    (g : Matrix (Fin n) (Fin n) (A ⊗[F] E)) (hg : cT (sigR A σ) g * JR A J * g = JR A J) (hg1 : g.det = 1)
    (hgη : algebraMap A (A ⊗[F] E) η • (g - 1) = g - 1) :
    g ∈ closure {m | ∃ γ : Matrix (Fin n) (Fin n) E, cT (σ : E →+* E) γ * J * γ = J ∧ γ.det = 1 ∧
      m = 1 + algebraMap A (A ⊗[F] E) η • (γ.map (inclR (F := F) A) - 1)} := by
  classical
  haveI : IsModuleTopology A (A ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (A ⊗[F] E) := IsModuleTopology.isTopologicalRing A _
  haveI : IsModuleTopology B (B ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (B ⊗[F] E) := IsModuleTopology.isTopologicalRing B _
  haveI : IsArtinianRing (B ⊗[F] E) := IsArtinianRing.of_finite B _
  let b := Module.finBasis F E
  let bA := Algebra.TensorProduct.basis A b
  let bB := Algebra.TensorProduct.basis B b
  obtain ⟨u1, u2⟩ := GlobalTheory.RealApprox.units_of_free (A := B) (R := B ⊗[F] E) bB h1 h2
  let p : A ⊗[F] E →+* B ⊗[F] E := (Algebra.TensorProduct.map π (AlgHom.id F E)).toRingHom
  have hp : ∀ a x, p (a ⊗ₜ[F] x) = π a ⊗ₜ[F] x := fun a x => rfl
  have hpι : ∀ x, p (inclR (F := F) A x) = inclR (F := F) B x := fun x =>
    (hp 1 x).trans (by rw [map_one]; rfl)
  have hpσ : ∀ y, sigR B σ (p y) = p (sigR A σ y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a y => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have hrepr : ∀ y i, bB.repr (p y) i = π (bA.repr y i) := by
    intro y i
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a y => simp [hp, bA, bB, Algebra.TensorProduct.basis_repr_tmul]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  let S : B ⊗[F] E → A ⊗[F] E := fun y => ∑ i, s (bB.repr y i) • bA i
  have hS : Continuous S := continuous_finsetSum _ fun i _ =>
    (hs.comp (IsModuleTopology.continuous_of_linearMap (bB.coord i))).smul continuous_const
  have hSp : ∀ y, S (p y) = algebraMap A (A ⊗[F] E) η * y := by
    intro y
    simp only [S, hrepr, hη, mul_smul]
    rw [← Finset.smul_sum, bA.sum_repr, Algebra.smul_def]
  have hmap : ∀ γ : Matrix (Fin n) (Fin n) E, (γ.map (inclR (F := F) A)).map p = γ.map (inclR (F := F) B) := by
    intro γ
    ext i j
    exact hpι _
  have h := mem_closure_su (inclR (F := F) B) (σ : E →+* E) (sigR B σ) (sigR_inclR B σ) hc hne (sigR_sigR B σ hc)
    (continuous_sigR B σ) (denseRange_inclR B hd) u1 u2 J hJ hdet (g.map p)
    (by
      have e : cT (sigR B σ) (g.map p) = (cT (sigR A σ) g).map p := by
        ext i j
        exact hpσ _
      rw [e, ← hmap, ← Matrix.map_mul, ← Matrix.map_mul]
      exact congrArg (·.map p) hg)
    (by rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hg1, map_one])
  let Ψ : Matrix (Fin n) (Fin n) (B ⊗[F] E) → Matrix (Fin n) (Fin n) (A ⊗[F] E) := fun m => 1 + (m - 1).map S
  have hΨ : Continuous Ψ := continuous_const.add ((continuous_id.sub continuous_const).matrix_map hS)
  have hΨp : ∀ m : Matrix (Fin n) (Fin n) (A ⊗[F] E), Ψ (m.map p) = 1 + algebraMap A (A ⊗[F] E) η • (m - 1) := by
    intro m
    simp only [Ψ]
    rw [← Matrix.map_one p (map_zero p) (map_one p), ← Matrix.map_sub _ (map_sub p)]
    congr 1
    ext i j
    exact hSp _
  have hΨg : Ψ (g.map p) = g := by rw [hΨp, hgη, add_sub_cancel]
  rw [← hΨg]
  refine hΨ.continuousWithinAt.mem_closure h ?_
  rintro _ ⟨γ, hγ, hγ1, rfl⟩
  exact ⟨γ, hγ, hγ1, by rw [← hmap, hΨp]⟩

end Transfer

section Main

open Matrix
open Formalism.UG hiding sigR evalV

theorem isInducing_val {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (σ : R →+* R)
    (hσ : Continuous σ) {n : ℕ} (J K : Matrix (Fin n) (Fin n) R) (hK : K * J = 1) :
    Topology.IsInducing fun u : UJ σ J => (u.1 : Matrix (Fin n) (Fin n) R) := by
  have hφ : Continuous fun m : Matrix (Fin n) (Fin n) R => (m, MulOpposite.op (K * cT σ m * J)) :=
    continuous_id.prodMk (MulOpposite.continuous_op.comp
      ((continuous_const.matrix_mul (continuous_id.matrix_map hσ).matrix_transpose).matrix_mul continuous_const))
  refine Topology.IsInducing.of_comp (Units.continuous_val.comp continuous_subtype_val) hφ ?_
  have he := (Units.isInducing_embedProduct (M := Matrix (Fin n) (Fin n) R)).comp
    (Topology.IsInducing.subtypeVal (t := (UJ σ J : Set (GL (Fin n) R))))
  suffices e : ((fun m : Matrix (Fin n) (Fin n) R => (m, MulOpposite.op (K * cT σ m * J))) ∘
      fun u : UJ σ J => (u.1 : Matrix (Fin n) (Fin n) R)) =
      fun u : UJ σ J => Units.embedProduct (Matrix (Fin n) (Fin n) R) u.1 by
    rw [e]
    exact he
  funext u
  refine Prod.ext rfl (congrArg MulOpposite.op ?_)
  have hu : cT σ u.1.1 * J * u.1.1 = J := u.2
  refine (Units.inv_eq_of_mul_eq_one_left ?_).symm
  rw [Matrix.mul_assoc K, Matrix.mul_assoc K, hu, hK]

theorem unitary_trunc {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} (J u : Matrix (Fin n) (Fin n) R) (e : R)
    (he : e * e = e) (hσ : σ e = e) (hu : cT σ u * J * u = J) :
    cT σ (1 + e • (u - 1)) * J * (1 + e • (u - 1)) = J := by
  have e1 : cT σ (1 + e • (u - 1)) = 1 + e • (cT σ u - 1) := by
    ext i j
    simp [cT, hσ, one_apply, eq_comm]
  rw [e1]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_sub, smul_smul, he, hu]
  abel

theorem weak_approx_SU : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (η : AF F), IsPlacesIdem T₁ T₂ η → ∀ h ∈ SUSupp σ J η, h ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, (∀ i j, ((HA.mat (AF F) σ J x).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j = (1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j + algebraMap (AF F) (AF F ⊗[F] E) η * (((HA.mat (AF F) σ J γ).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1) i j)} := by
  intro F E _ _ _ _ _ σ hCM M J hJ T₁ T₂ η hη h hh
  classical
  obtain ⟨-, hE, -, hτ⟩ := hCM
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hc : ∀ x, σ (σ x) = x := fun x => τ.injective (by rw [hτ, hτ, star_star])
  have hne : ∃ z, σ z ≠ z := by
    by_contra hn
    push Not at hn
    refine IsTotallyComplex.complexEmbedding_not_isReal τ (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_))
    have := hτ τ x
    rw [hn] at this
    exact this.symm
  let B : Type := ((v : T₂) → Fv F v.1) × ((w : T₁) → w.1.Completion)
  let π : AF F →ₐ[F] B :=
    AlgHom.prod (AlgHom.pi fun v : T₂ => (evalV F v.1).comp (sndA F))
      (AlgHom.pi fun w : T₁ => (Pi.evalAlgHom F (fun u : InfinitePlace F => u.Completion) w.1).comp (fstA F))
  have hπ : ∀ a, GlobalTheory.PlaceApprox.locAdele T₁ T₂ (π a) = η * a := fun a =>
    (GlobalTheory.PlaceApprox.mul_eq_locAdele hη a).symm
  have hηη : η * η = η := by
    have e : π η = π 1 := by
      refine Prod.ext (funext fun v => ?_) (funext fun w => ?_)
      · exact (hη.2.2.1 v.1 v.2).trans (map_one ((evalV F v.1).comp (sndA F))).symm
      · exact (hη.1 w.1 w.2).trans (by rw [map_one]; rfl)
    rw [← hπ, e, hπ, mul_one]
  have a1 : IsOpen {x : B | IsUnit x} := Units.isOpen
  have a2 : ∀ x : B, IsUnit x → ContinuousAt Ring.inverse x := by
    rintro _ ⟨x, rfl⟩
    exact NormedRing.inverse_continuousAt x
  have hJ' : cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 i j
  obtain ⟨hh1, hh2⟩ := (GlobalTheory.SUSuppSub.mem_SUSupp_iff σ J).1 hh
  have key := mem_closure_trunc (AF F) B π _ (GlobalTheory.PlaceApprox.continuous_locAdele T₁ T₂) η hπ
    (GroundTheory.Global.denseRange_algebraMap_prod_pi (K := F) T₂ T₁) a1 a2 σ hc hne J hJ' hJ.2
    (GlobalTheory.SUSuppSub.mv σ J h) (show HR (AF F) σ J from h).2 (StrongApprox.mem_SUAdelic.1 hh1) hh2
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hu : IsUnit (JR (F := F) (AF F) J).det := by
    unfold JR
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (IsUnit.mk0 _ hJ.2).map _
  have hind : Topology.IsInducing (GlobalTheory.SUSuppSub.mv σ J) :=
    isInducing_val (sigR (AF F) σ) (continuous_sigR _ σ) _ _ (Matrix.nonsing_inv_mul _ hu)
  rw [hind.closure_eq_preimage_closure_image]
  refine closure_mono ?_ key
  rintro _ ⟨γ, hγ, hγ1, rfl⟩
  have hγA : cT (sigR (AF F) σ) (γ.map (inclR (F := F) (AF F))) * JR (F := F) (AF F) J *
      γ.map (inclR (F := F) (AF F)) = JR (F := F) (AF F) J := by
    have e : cT (sigR (AF F) σ) (γ.map (inclR (F := F) (AF F))) =
        (cT (σ : E →+* E) γ).map (inclR (F := F) (AF F)) := by
      ext i j
      exact sigR_inclR _ σ _
    unfold JR
    rw [e, ← Matrix.map_mul, ← Matrix.map_mul, hγ]
  have hx := unitary_trunc _ _ _ (algebraMap (AF F) (AF F ⊗[F] E) η) (by rw [← map_mul, hηη])
    (StrongApprox.sigR_algebraMap σ η) hγA
  have hxu : IsUnit (1 + algebraMap (AF F) (AF F ⊗[F] E) η • (γ.map (inclR (F := F) (AF F)) - 1)).det := by
    have := hu
    rw [← hx, det_mul] at this
    exact isUnit_of_mul_isUnit_right this
  let γ₀ : GL (Fin M) E := Matrix.GeneralLinearGroup.mkOfDetNeZero γ (by rw [hγ1]; exact one_ne_zero)
  let γA : HA (AF F) σ J := (⟨bc (inclR (F := F) (AF F)) γ₀, hγA⟩ : HR (AF F) σ J)
  let x : HA (AF F) σ J := (⟨Matrix.GeneralLinearGroup.mk'' _ hxu, hx⟩ : HR (AF F) σ J)
  refine ⟨x, ⟨γA, ⟨StrongApprox.mem_SUAdelic.2 ?_, ⟨γ₀, hγ, rfl⟩⟩, fun i j => rfl⟩, rfl⟩
  change (γ.map (inclR (F := F) (AF F))).det = 1
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hγ1, map_one]

end Main

end GlobalTheory.SUWeakApprox

end
