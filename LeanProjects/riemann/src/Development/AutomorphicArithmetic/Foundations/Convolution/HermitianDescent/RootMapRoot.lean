import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NormAlmostAll
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalBase
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalExt
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.ConjSep
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.RepNmSucc
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NormProd

open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.D

private theorem aeval_map_sg {k R : Type} [CommRing k] [CommRing R] [Algebra k R] {n : ℕ} (s : R ≃ₐ[k] R)
    (γ : GL (Fin n) k) (p : R[X]) :
    (aeval (up R γ).val p).map s = aeval (up R γ).val (p.map (s : R →+* R)) := by
  have hγ : ((up R γ).val).map s = (up R γ).val := by
    ext i j
    simp [up]
  induction p using Polynomial.induction_on with
  | C r =>
    ext i j
    simp [Matrix.algebraMap_matrix_apply, apply_ite s]
  | add p q hp hq => rw [map_add, Polynomial.map_add, map_add, ← hp, ← hq, Matrix.map_add _ (map_add s)]
  | monomial m r h =>
    rw [pow_succ, ← mul_assoc, map_mul, Matrix.map_mul, h, Polynomial.map_mul (p := C r * X ^ m), map_mul]
    simp [hγ]

private theorem nm_aeval {k R : Type} [CommRing k] [CommRing R] [Algebra k R] {n : ℕ} (σ : R ≃ₐ[k] R)
    (γ : GL (Fin n) k) (p : R[X]) (a : GL (Fin n) R) (ha : a.val = aeval (up R γ).val p) (q : ℕ) :
    (nm σ q a).val = aeval (up R γ).val (∏ i ∈ Finset.range q, p.map ((σ ^ i : R ≃ₐ[k] R) : R →+* R)) := by
  induction q with
  | zero => simp [nm]
  | succ q ih =>
    rw [Finset.prod_range_succ, map_mul, ← ih, ← aeval_map_sg, ← ha]
    simp only [nm, List.range_succ, List.map_append, List.prod_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, Units.val_mul]
    rfl

private theorem core {k R A T : Type} [Field k] [CommRing R] [Algebra k R] [CommRing A] [CommRing T] [Algebra A T]
    [Module.Free A T] {n : ℕ} (σ : R ≃ₐ[k] R) (τ : T ≃ₐ[A] T) (q : ℕ) (hσ : IsGal σ q) (hτ : IsGal τ q)
    (γ : GL (Fin n) k) (hγ : (cp γ).Separable) (j : R →+* T) (α : A) (hj : ∀ r, τ (j r) = j (σ r))
    (P : R[X]) (hP : P = (cp γ).map (algebraMap k R))
    (hs : Function.Surjective (eval₂RingHom j (algebraMap A T α)))
    (h0 : P.eval₂ j (algebraMap A T α) = 0) (φ : T →+* AdjoinRoot P)
    (hφj : ∀ r, φ (j r) = AdjoinRoot.of P r) (hφα : φ (algebraMap A T α) = AdjoinRoot.root P) :
    (∃ a : GL (Fin n) R, nm σ q a = up R γ ∧ Commute a (up R γ)) ↔ ∃ z : T, Algebra.norm A z = α := by
  haveI := (galBase k R k σ q hσ).1
  set χ := eval₂RingHom j (algebraMap A T α) with hχ
  have hch : (up R γ).val.charpoly = P := by
    rw [hP, cp, ← Matrix.charpoly_map]; rfl
  obtain ⟨-, hc, hk⟩ := conjSep k R n (up R γ).val (by rw [hch, hP]; exact hγ.map)
  rw [hch] at hk
  have hφ : φ.comp χ = AdjoinRoot.mk P := by
    apply Polynomial.ringHom_ext
    · intro r; simp [hχ, hφj]
    · simp [hχ, hφα]
  have hker : ∀ p, χ p = 0 ↔ P ∣ p := by
    intro p
    constructor
    · intro h
      rw [← AdjoinRoot.mk_eq_zero, ← hφ, RingHom.comp_apply, h, map_zero]
    · rintro ⟨u, rfl⟩
      rw [map_mul, hχ, coe_eval₂RingHom, h0, zero_mul]
  have heq : ∀ p p', χ p = χ p' ↔ aeval (up R γ).val p = aeval (up R γ).val p' := by
    intro p p'
    rw [← sub_eq_zero, ← map_sub, hker, ← hk, map_sub, sub_eq_zero]
  have hjp : ∀ (i : ℕ) r, (τ ^ i) (j r) = j ((σ ^ i) r) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => intro r; rw [pow_succ, pow_succ, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hj, ih]
  have hχp : ∀ (i : ℕ) p, (τ ^ i) (χ p) = χ (p.map ((σ ^ i : R ≃ₐ[k] R) : R →+* R)) := by
    intro i p
    have : ((τ ^ i : T ≃ₐ[A] T) : T →+* T).comp χ = χ.comp (mapRingHom ((σ ^ i : R ≃ₐ[k] R) : R →+* R)) := by
      apply Polynomial.ringHom_ext
      · intro r; simpa [hχ] using hjp i r
      · simp [hχ, -AlgEquiv.coe_pow]
    exact DFunLike.congr_fun this p
  have key : ∀ p, Algebra.norm A (χ p) = α ↔
      aeval (up R γ).val (∏ i ∈ Finset.range q, p.map ((σ ^ i : R ≃ₐ[k] R) : R →+* R)) = (up R γ).val := by
    intro p
    rw [← hτ.inj.eq_iff, normProd A T τ q hτ]
    simp only [hχp]
    rw [← map_prod]
    have h1 : algebraMap A T α = χ X := by simp [hχ]
    rw [h1, heq, aeval_X]
  constructor
  · rintro ⟨a, h1, h2⟩
    obtain ⟨p, hp⟩ := hc a.val (congrArg Units.val h2.eq)
    exact ⟨χ p, (key p).2 (by rw [← nm_aeval σ γ p a hp, h1])⟩
  · rintro ⟨z, hz⟩
    obtain ⟨p, rfl⟩ := hs z
    have h1 := (key p).1 hz
    have hu : IsUnit (aeval (up R γ).val p) := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hσ.pos.ne'
      have h2 := h1
      rw [Finset.prod_range_succ', mul_comm, map_mul] at h2
      have h3 : p.map ((σ ^ 0 : R ≃ₐ[k] R) : R →+* R) = p := by
        ext i; simp
      rw [h3] at h2
      have h4 := congrArg Matrix.det h2
      rw [Matrix.det_mul] at h4
      rw [Matrix.isUnit_iff_isUnit_det]
      exact isUnit_of_mul_isUnit_left (h4 ▸ (Matrix.isUnit_iff_isUnit_det _).1 (up R γ).isUnit)
    refine ⟨hu.unit, Units.ext (by rw [nm_aeval σ γ p hu.unit rfl, h1]), Units.ext ?_⟩
    have : aeval (up R γ).val (p * X) = aeval (up R γ).val (X * p) := by rw [mul_comm]
    simpa using this

private theorem mk_eval {F R T : Type} [CommRing F] [CommRing R] [CommRing T] (p : F[X]) (g : AdjoinRoot p →+* T)
    (j : R →+* T) (i : F →+* R) (h : ∀ c, g (AdjoinRoot.of p c) = j (i c)) (f : F[X]) :
    g (AdjoinRoot.mk p f) = (f.map i).eval₂ j (g (AdjoinRoot.root p)) := by
  have : g.comp (AdjoinRoot.mk p) = (eval₂RingHom j (g (AdjoinRoot.root p))).comp (mapRingHom i) := by
    apply Polynomial.ringHom_ext
    · intro r; simp [h]
    · simp
  exact DFunLike.congr_fun this f

private noncomputable def rootMap {F : Type} [CommRing F] (p : F[X]) (R : Type) [CommRing R] [Algebra F R] (P : R[X])
    (hP : P = p.map (algebraMap F R)) : AdjoinRoot p →ₐ[F] AdjoinRoot P :=
  AdjoinRoot.liftAlgHom p (Algebra.ofId F _) (AdjoinRoot.root P) (by
    have := AdjoinRoot.eval₂_root P
    rw [hP, eval₂_map, ← hP] at this
    exact this)

private theorem rootMap_root {F : Type} [CommRing F] (p : F[X]) (R : Type) [CommRing R] [Algebra F R] (P : R[X])
    (hP : P = p.map (algebraMap F R)) : rootMap p R P hP (AdjoinRoot.root p) = AdjoinRoot.root P :=
  AdjoinRoot.liftAlgHom_root ..

private theorem second (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E ≃ₐ[F] E) (q : ℕ) (hσ : IsGal σ q)
    (n : ℕ) (γ : GL (Fin n) F) (hγ : (cp γ).Separable) :
    (∃ a : GL (Fin n) E, nm σ q a = up E γ ∧ Commute a (up E γ)) ↔ IsNm F E (AdjoinRoot.root (cp γ)) := by
  have hm := mk_eval (cp γ) (algebraMap (AdjoinRoot (cp γ)) (AdjoinRoot (cp γ) ⊗[F] E))
    (inc (AdjoinRoot (cp γ))) (algebraMap F E) (fun c => by
      rw [← AdjoinRoot.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      exact (Algebra.TensorProduct.includeRight.commutes c).symm)
  refine core σ (ext (AdjoinRoot (cp γ)) σ) q hσ (galExt F E _ σ q hσ) γ hγ (inc _) _ (fun r => by simp [ext, inc])
    _ rfl ?_ ?_ (Algebra.TensorProduct.lift (rootMap (cp γ) E _ rfl) (AdjoinRoot.ofAlgHom F _)
      fun _ _ => Commute.all _ _).toRingHom (fun r => by simp [inc]) (by simp [rootMap_root])
  · rw [← RingHom.range_eq_top, eq_top_iff]
    rintro t -
    induction t using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | add x y hx hy => exact add_mem hx hy
    | tmul x e =>
      induction x using AdjoinRoot.induction_on with
      | ih f =>
        refine ⟨f.map (algebraMap F E) * C e, ?_⟩
        rw [map_mul, coe_eval₂RingHom, ← hm]
        simp [inc]
  · rw [← hm]; simp

private theorem first (F E k : Type) [Field F] [Field E] [Algebra F E] [Field k] [Algebra F k] (σ : E ≃ₐ[F] E) (q : ℕ)
    (hσ : IsGal σ q) (n : ℕ) (γ : GL (Fin n) F) (hγ : (cp γ).Separable) :
    (∃ a : GL (Fin n) (k ⊗[F] E), nm (ext k σ) q a = up _ (up k γ) ∧ Commute a (up _ (up k γ))) ↔
      IsNm F E ((1 : k) ⊗ₜ[F] AdjoinRoot.root (cp γ)) := by
  have hc : cp (up k γ) = (cp γ).map (algebraMap F k) := by
    rw [cp, cp, ← Matrix.charpoly_map]; rfl
  let j : k ⊗[F] E →ₐ[F] (k ⊗[F] AdjoinRoot (cp γ)) ⊗[F] E :=
    Algebra.TensorProduct.map Algebra.TensorProduct.includeLeft (AlgHom.id F E)
  have hm := mk_eval (cp γ) ((algebraMap (k ⊗[F] AdjoinRoot (cp γ)) ((k ⊗[F] AdjoinRoot (cp γ)) ⊗[F] E)).comp
      (Algebra.TensorProduct.includeRight : AdjoinRoot (cp γ) →ₐ[F] k ⊗[F] AdjoinRoot (cp γ)).toRingHom)
    j.toRingHom (algebraMap F (k ⊗[F] E)) (fun c => by
      rw [← AdjoinRoot.algebraMap_eq]
      simp only [AlgHom.toRingHom_eq_coe, RingHom.comp_apply, RingHom.coe_coe, AlgHom.commutes]
      rw [← IsScalarTower.algebraMap_apply])
  refine core (ext k σ) (ext (k ⊗[F] AdjoinRoot (cp γ)) σ) q (galExt F E _ σ q hσ) (galExt F E _ σ q hσ) (up k γ)
    (hc ▸ hγ.map) j.toRingHom _ ?_ ((cp γ).map (algebraMap F (k ⊗[F] E))) ?_ ?_ ?_
    (Algebra.TensorProduct.lift
      (Algebra.TensorProduct.lift ((AdjoinRoot.ofAlgHom F _).comp Algebra.TensorProduct.includeLeft)
        (rootMap (cp γ) (k ⊗[F] E) _ rfl) fun _ _ => Commute.all _ _)
      ((AdjoinRoot.ofAlgHom F _).comp Algebra.TensorProduct.includeRight)
      fun _ _ => Commute.all _ _).toRingHom ?_ (by simp [rootMap_root, ← Algebra.TensorProduct.one_def])
  · intro r
    induction r using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x e => simp [j, ext]
  · rw [hc, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  · rw [← RingHom.range_eq_top, eq_top_iff]
    rintro t -
    induction t using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | add x y hx hy => exact add_mem hx hy
    | tmul x e =>
      induction x using TensorProduct.induction_on with
      | zero => rw [TensorProduct.zero_tmul]; exact zero_mem _
      | add x y hx hy => rw [TensorProduct.add_tmul]; exact add_mem hx hy
      | tmul c x =>
        induction x using AdjoinRoot.induction_on with
        | ih f =>
          refine ⟨f.map (algebraMap F _) * C (c ⊗ₜ e), ?_⟩
          rw [map_mul, coe_eval₂RingHom]
          erw [← hm]
          simp [j]
  · erw [← hm]; simp
  · intro r
    induction r using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x e => simp [j, ← map_mul]

end UpperTheory.ConvolutionTheory.D

theorem UpperTheory.ConvolutionTheory.D.nmAlg :
    UpperTheory.ConvolutionTheory.D.NmAlg := by
  intro F E k _ _ _ _ _ σ q hσ n γ hγ
  refine ⟨?_, second F E σ q hσ n γ hγ⟩
  rw [← first F E k σ q hσ n γ hγ]
  have hc : cp (up k γ) = (cp γ).map (algebraMap F k) := by
    rw [cp, cp, ← Matrix.charpoly_map]; rfl
  have he : (cp γ).map ((inc k).comp (algebraMap F E)) = (cp (up k γ)).map (algebraMap k (k ⊗[F] E)) := by
    rw [hc, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
    congr 1
    exact RingHom.ext fun c => Algebra.TensorProduct.includeRight.commutes c
  rw [he]
  constructor
  · rintro ⟨δ, hδ⟩
    obtain ⟨x, hx⟩ := nmRep k _ (ext k σ) q (galExt F E _ σ q hσ) n δ (up k γ) (hc ▸ hγ.map) hδ
    exact ⟨_, hx⟩
  · rintro ⟨a, ha, -⟩
    refine ⟨a, ?_⟩
    rw [ha, cp, cp, ← Matrix.charpoly_map]; rfl
