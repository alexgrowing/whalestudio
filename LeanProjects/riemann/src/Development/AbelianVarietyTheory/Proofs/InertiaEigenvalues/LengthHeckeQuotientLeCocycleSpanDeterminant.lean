import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CMemCoeffSub
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeterminantLemmaDiscreteValuationRingQuotientLenStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CutValueMemHeckeValueIdealOffSupportStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmer

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

noncomputable section

namespace GlobalTheory.CutDet

section Abs

open scoped Kronecker

variable {O : Type} [CommRing O] [IsDomain O]

theorem baer_KOG [IsPrincipalIdealRing O] (k : ℕ) : Module.Baer O (KOG O k) := by
  intro I g
  obtain ⟨a, rfl⟩ := (IsPrincipalIdealRing.principal I)
  by_cases ha : a = 0
  · refine ⟨0, fun x hx => ?_⟩
    have hx0 : x = 0 := by simpa [ha] using hx
    subst hx0
    exact (map_zero g).symm
  · have hmem : a ∈ Submodule.span O ({a} : Set O) := Submodule.mem_span_singleton_self a
    obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (g ⟨a, hmem⟩)
    have ha' : algebraMap O (FractionRing O) a ≠ 0 := by simpa using ha
    let m : KOG O k := Submodule.Quotient.mk ((algebraMap O (FractionRing O) a)⁻¹ • v)
    have hm : a • m = g ⟨a, hmem⟩ := by
      rw [← hv, ← Submodule.Quotient.mk_smul, ← algebraMap_smul (FractionRing O) a, smul_smul,
        mul_inv_cancel₀ ha', one_smul]
    refine ⟨LinearMap.toSpanSingleton O _ m, fun x hx => ?_⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [LinearMap.toSpanSingleton_apply, smul_assoc, hm, ← map_smul]
    rfl

theorem exists_ext {P M Q : Type} [AddCommGroup P] [Module O P] [AddCommGroup M] [Module O M]
    [AddCommGroup Q] [Module O Q] (hQ : Module.Baer O Q) (F : P →ₗ[O] M) (G : P →ₗ[O] Q)
    (h : LinearMap.ker F ≤ LinearMap.ker G) : ∃ φ : M →ₗ[O] Q, ∀ p, φ (F p) = G p := by
  obtain ⟨φ, hφ⟩ := hQ.extension_property ((LinearMap.ker F).liftQ F le_rfl)
    (LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)) ((LinearMap.ker F).liftQ G h)
  exact ⟨φ, fun p => LinearMap.congr_fun hφ (Submodule.Quotient.mk p)⟩

theorem matKO_mk {k : ℕ} (A : Matrix (Fin k) (Fin k) O) (v : Fin k → FractionRing O) :
    matKO A (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk ((A.map (algebraMap O (FractionRing O))).mulVec v) := rfl

def matHom (k : ℕ) : Matrix (Fin k) (Fin k) O →ₐ[O] Module.End O (KOG O k) :=
  AlgHom.ofLinearMap
    { toFun := matKO
      map_add' := fun A B => LinearMap.ext fun x => by
        obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        rw [LinearMap.add_apply, matKO_mk, matKO_mk, matKO_mk, ← Submodule.Quotient.mk_add,
          Matrix.map_add _ (map_add _), Matrix.add_mulVec]
      map_smul' := fun c A => LinearMap.ext fun x => by
        obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        rw [LinearMap.smul_apply, matKO_mk, matKO_mk, RingHom.id_apply, ← Submodule.Quotient.mk_smul]
        congr 1
        funext j
        rw [Pi.smul_apply, Algebra.smul_def c (Matrix.mulVec _ _ _)]
        simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] }
    (LinearMap.ext fun x => by
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      change matKO 1 _ = _
      rw [matKO_mk, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
      rfl)
    (fun A B => LinearMap.ext fun x => by
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      change matKO (A * B) (Submodule.Quotient.mk v) = matKO A (matKO B (Submodule.Quotient.mk v))
      rw [matKO_mk, matKO_mk, matKO_mk, Matrix.map_mul, Matrix.mulVec_mulVec])

theorem matHom_apply {k : ℕ} (A : Matrix (Fin k) (Fin k) O) : matHom k A = matKO A := rfl

theorem length_sol_le [IsPrincipalIdealRing O] {M Γ : Type} [Ring M] [Algebra O M] (A : Subalgebra O M)
    {d g : ℕ} (ψ : A →ₐ[O] Matrix (Fin d) (Fin d) O) (ψ' : M → Matrix (Fin d) (Fin d) O)
    (hψ : ∀ a : A, ψ a = ψ' a) (y : Γ → M) (γ : Fin g → Γ) (Y Z : M → Prop)
    (hY : ∀ m, Y m → ∃ θ : Fin g → A, m = ∑ q, (θ q : M) * y (γ q))
    (Rel : Submodule A (Fin g → A)) (hRel : ∀ θ : Fin g → A, Z (∑ q, (θ q : M) * y (γ q)) → θ ∈ Rel)
    (hZ : Z 0) :
    Module.length O ↥(⨅ θ ∈ Rel, LinearMap.ker (∑ q : Fin g, (matKO (ψ (θ q))).comp
      (LinearMap.proj q : (Fin g → KOG O d) →ₗ[O] KOG O d))) ≤
    Module.length O ↥(Submodule.span O {c : Γ → KOG O d | ∃ φ : M →ₗ[O] KOG O d,
      (∀ a, a ∈ A → ∀ m, Y m → φ (a * m) = matKO (ψ' a) (φ m)) ∧
      (∀ m, Y m → Z m → φ m = 0) ∧ c = fun s => φ (y s)}) := by
  classical
  set C := Submodule.span O {c : Γ → KOG O d | ∃ φ : M →ₗ[O] KOG O d,
      (∀ a, a ∈ A → ∀ m, Y m → φ (a * m) = matKO (ψ' a) (φ m)) ∧
      (∀ m, Y m → Z m → φ m = 0) ∧ c = fun s => φ (y s)} with hC
  have hle : (⨅ θ ∈ Rel, LinearMap.ker (∑ q : Fin g, (matKO (ψ (θ q))).comp
      (LinearMap.proj q : (Fin g → KOG O d) →ₗ[O] KOG O d))) ≤
      C.map (LinearMap.funLeft O (KOG O d) γ) := by
    intro w hw
    have hw' : ∀ θ ∈ Rel, ∑ q, matKO (ψ (θ q)) (w q) = 0 := by
      intro θ hθ
      have := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hw θ) hθ
      simpa [LinearMap.sum_apply] using this
    let F : (Fin g → A) →ₗ[O] M := ∑ q, (LinearMap.mulRight O (y (γ q))).comp
      (A.val.toLinearMap.comp (LinearMap.proj q))
    let G : (Fin g → A) →ₗ[O] KOG O d := ∑ q, (LinearMap.applyₗ (w q)).comp
      ((matHom d).toLinearMap.comp (ψ.toLinearMap.comp (LinearMap.proj q)))
    have hF : ∀ θ, F θ = ∑ q, (θ q : M) * y (γ q) := fun θ => by
      simp [F, LinearMap.sum_apply]
    have hG : ∀ θ, G θ = ∑ q, matKO (ψ (θ q)) (w q) := fun θ => by
      simp [G, LinearMap.sum_apply, matHom_apply]
    obtain ⟨φ, hφ⟩ := exists_ext (baer_KOG d) F G (by
      intro θ hθ
      rw [LinearMap.mem_ker] at hθ ⊢
      rw [hG]
      refine hw' θ (hRel θ ?_)
      rw [← hF, hθ]
      exact hZ)
    refine ⟨fun s => φ (y s), Submodule.subset_span ⟨φ, ?_, ?_, rfl⟩, ?_⟩
    · intro a ha m hm
      obtain ⟨θ, rfl⟩ := hY m hm
      have h1 : a * ∑ q, (θ q : M) * y (γ q) = F (fun q => ⟨a, ha⟩ * θ q) := by
        rw [hF, Finset.mul_sum]
        simp [mul_assoc]
      rw [h1, ← hF, hφ, hφ, hG, hG, map_sum, ← hψ ⟨a, ha⟩]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [map_mul, ← matHom_apply, map_mul]
      rfl
    · intro m hm hz
      obtain ⟨θ, rfl⟩ := hY m hm
      rw [← hF, hφ, hG]
      exact hw' θ (hRel θ hz)
    · funext q
      have h1 : y (γ q) = F (Pi.single q 1) := by
        rw [hF, Finset.sum_eq_single q] <;> simp +contextual
      change φ (y (γ q)) = w q
      rw [h1, hφ, hG, Finset.sum_eq_single q]
      · rw [Pi.single_eq_same, map_one, ← matHom_apply, map_one]
        rfl
      · intro b _ hb
        rw [Pi.single_eq_of_ne hb, map_zero, ← matHom_apply, map_zero]
        rfl
      · simp
  refine (Module.length_le_of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective _)).trans ?_
  exact Module.length_le_of_surjective ((LinearMap.funLeft O (KOG O d) γ).submoduleMap C)
    (LinearMap.submoduleMap_surjective _ _)

theorem det_blocks {L ι ρ τ G : Type} [CommRing L] [Fintype ι] [DecidableEq ι] [Fintype ρ] [DecidableEq ρ]
    [Fintype τ] [DecidableEq τ] [Fintype G] [DecidableEq G]
    (P : Matrix (ρ ⊕ τ) ι L) (Q : Matrix ι (ρ ⊕ τ) L) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (a : G → G → Matrix ι ι L) (b : G → G → Matrix ρ ρ L) (c : τ → G → G → L)
    (h : ∀ p q, P * a p q * Q = Matrix.fromBlocks (b p q) 0 0 (Matrix.diagonal fun j => c j p q)) :
    (Matrix.of fun pa qb : G × ι => a pa.1 qb.1 pa.2 qb.2).det =
      (Matrix.of fun pa qb : G × ρ => b pa.1 qb.1 pa.2 qb.2).det *
        ∏ j, (Matrix.of fun p q => c j p q).det := by
  have h1 : ((1 : Matrix G G L) ⊗ₖ P) * ((1 : Matrix G G L) ⊗ₖ Q) = 1 := by
    rw [← Matrix.mul_kronecker_mul, hPQ, one_mul, Matrix.one_kronecker_one]
  have h2 : ((1 : Matrix G G L) ⊗ₖ Q) * ((1 : Matrix G G L) ⊗ₖ P) = 1 := by
    rw [← Matrix.mul_kronecker_mul, hQP, one_mul, Matrix.one_kronecker_one]
  rw [← Matrix.det_conj_of_mul_eq_one h1 h2, ← Matrix.det_blockDiagonal, ← Matrix.det_fromBlocks_zero₂₁ _ 0,
    ← Matrix.det_submatrix_equiv_self (Equiv.prodSumDistrib G ρ τ)]
  congr 1
  ext ⟨p, i⟩ ⟨q, j⟩
  have h3 : (((1 : Matrix G G L) ⊗ₖ P) * (Matrix.of fun pa qb : G × ι => a pa.1 qb.1 pa.2 qb.2) *
      ((1 : Matrix G G L) ⊗ₖ Q)) (p, i) (q, j) = (P * a p q * Q) i j := by
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, Finset.sum_ite_eq]
  rw [h3, h]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.blockDiagonal_apply, Matrix.diagonal_apply]

theorem exists_conj {K ι ρ τ : Type} [Field K] [Fintype ι] [DecidableEq ι] [Fintype ρ] [DecidableEq ρ]
    [Fintype τ] [DecidableEq τ] (e : (ι → K) ≃ₗ[K] ((ρ → K) × (τ → K))) :
    ∃ (P : Matrix (ρ ⊕ τ) ι K) (Q : Matrix ι (ρ ⊕ τ) K), P * Q = 1 ∧ Q * P = 1 ∧
      ∀ (a : Matrix ι ι K) (b : Matrix ρ ρ K) (c : τ → K),
        (∀ u, e (a.mulVec u) = (b.mulVec (e u).1, fun j => c j * (e u).2 j)) →
        P * a * Q = Matrix.fromBlocks b 0 0 (Matrix.diagonal c) := by
  let e' := e.trans (LinearEquiv.sumArrowLequivProdArrow ρ τ K K).symm
  refine ⟨LinearMap.toMatrix' e'.toLinearMap, LinearMap.toMatrix' e'.symm.toLinearMap, ?_, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp]; simp
  · rw [← LinearMap.toMatrix'_comp]; simp
  · intro a b c h
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
    refine LinearMap.ext fun v => ?_
    change (LinearEquiv.sumArrowLequivProdArrow ρ τ K K).symm (e (a.mulVec (e.symm
      (LinearEquiv.sumArrowLequivProdArrow ρ τ K K v)))) = _
    rw [h, e.apply_symm_apply, Matrix.toLin'_apply, Matrix.fromBlocks_mulVec]
    funext j
    rcases j with j | j
    · simp
      rfl
    · simp [Matrix.mulVec_diagonal]

end Abs

section Abs2

variable {O K : Type} [CommRing O] [Field K] [Algebra O K]

theorem exists_homs (hinj : Function.Injective (algebraMap O K)) {X ι ρ τ : Type}
    [Fintype ι] [DecidableEq ι] [Fintype ρ] [DecidableEq ρ] [Fintype τ] [DecidableEq τ]
    (A : Subalgebra O (X → Matrix ι ι O)) (π : X)
    (P : Matrix (ρ ⊕ τ) ι K) (Q : Matrix ι (ρ ⊕ τ) K) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (ψρ : (X → Matrix ι ι O) → Matrix ρ ρ O) (ψχ : τ → (X → Matrix ι ι O) → O)
    (h : ∀ a ∈ A, P * (a π).map (algebraMap O K) * Q = Matrix.fromBlocks ((ψρ a).map (algebraMap O K)) 0 0
      (Matrix.diagonal fun j => algebraMap O K (ψχ j a))) :
    (∃ f : A →ₐ[O] Matrix ρ ρ O, ∀ a, f a = ψρ a) ∧ ∀ j, ∃ f : A →ₐ[O] O, ∀ a, f a = ψχ j a := by
  have uniq : ∀ (b b' : Matrix ρ ρ O) (c c' : τ → O),
      Matrix.fromBlocks (b.map (algebraMap O K)) 0 0 (Matrix.diagonal fun j => algebraMap O K (c j)) =
      Matrix.fromBlocks (b'.map (algebraMap O K)) 0 0 (Matrix.diagonal fun j => algebraMap O K (c' j)) →
      b = b' ∧ ∀ j, c j = c' j := by
    intro b b' c c' hh
    obtain ⟨h1, -, -, h2⟩ := Matrix.fromBlocks_inj.1 hh
    exact ⟨Matrix.map_injective hinj h1, fun j => hinj (congrFun (Matrix.diagonal_injective h2) j)⟩
  have hmul : ∀ a b : A, ψρ (a * b) = ψρ a * ψρ b ∧ ∀ j, ψχ j (a * b) = ψχ j a * ψχ j b := by
    intro a b
    refine uniq _ _ (fun j => ψχ j (a * b)) (fun j => ψχ j a * ψχ j b) ?_
    have h1 : P * ((a * b : X → Matrix ι ι O) π).map (algebraMap O K) * Q =
        (P * (a.1 π).map (algebraMap O K) * Q) * (P * (b.1 π).map (algebraMap O K) * Q) := by
      rw [Pi.mul_apply, Matrix.map_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Q P, hQP, Matrix.one_mul]
    rw [← h _ (A.mul_mem a.2 b.2), h1, h _ a.2, h _ b.2, Matrix.fromBlocks_multiply]
    simp [Matrix.map_mul]
  have hadd : ∀ a b : A, ψρ (a + b) = ψρ a + ψρ b ∧ ∀ j, ψχ j (a + b) = ψχ j a + ψχ j b := by
    intro a b
    refine uniq _ _ (fun j => ψχ j (a + b)) (fun j => ψχ j a + ψχ j b) ?_
    rw [← h _ (A.add_mem a.2 b.2), Pi.add_apply, Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul,
      h _ a.2, h _ b.2, Matrix.fromBlocks_add]
    simp [Matrix.map_add]
  have halg : ∀ c : O, ψρ (algebraMap O _ c) = algebraMap O _ c ∧ ∀ j, ψχ j (algebraMap O _ c) = c := by
    intro c
    refine uniq _ _ (fun j => ψχ j (algebraMap O _ c)) (fun _ => c) ?_
    have h1 : ∀ {κ : Type} [Fintype κ] [DecidableEq κ], (algebraMap O (Matrix κ κ O) c).map (algebraMap O K) =
        algebraMap O K c • (1 : Matrix κ κ K) := by
      intro κ _ _
      ext i j
      by_cases hij : i = j <;> simp [Matrix.algebraMap_matrix_apply, Matrix.one_apply, hij]
    rw [← h _ (A.algebraMap_mem c), Pi.algebraMap_apply, h1, h1, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hPQ, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, Matrix.smul_one_eq_diagonal,
      Matrix.smul_one_eq_diagonal]
    simp
  refine ⟨⟨{ toFun := fun a => ψρ a
             map_one' := by simpa using (halg 1).1
             map_mul' := fun a b => (hmul a b).1
             map_zero' := by simpa using (halg 0).1
             map_add' := fun a b => (hadd a b).1
             commutes' := fun c => (halg c).1 }, fun _ => rfl⟩, fun j =>
    ⟨{ toFun := fun a => ψχ j a
       map_one' := by simpa using (halg 1).2 j
       map_mul' := fun a b => (hmul a b).2 j
       map_zero' := by simpa using (halg 0).2 j
       map_add' := fun a b => (hadd a b).2 j
       commutes' := fun c => (halg c).2 j }, fun _ => rfl⟩⟩

open MvPolynomial in

theorem det_generic_blocks (hinj : Function.Injective (algebraMap O K)) {ι ρ τ G N : Type}
    [Fintype ι] [DecidableEq ι] [Fintype ρ] [DecidableEq ρ] [Fintype τ] [DecidableEq τ]
    [Fintype G] [DecidableEq G] [Fintype N]
    (P : Matrix (ρ ⊕ τ) ι K) (Q : Matrix ι (ρ ⊕ τ) K) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (a : N → G → G → Matrix ι ι O) (b : N → G → G → Matrix ρ ρ O) (c : τ → N → G → G → O)
    (h : ∀ k p q, P * (a k p q).map (algebraMap O K) * Q =
      Matrix.fromBlocks ((b k p q).map (algebraMap O K)) 0 0
        (Matrix.diagonal fun j => algebraMap O K (c j k p q))) :
    (Matrix.of fun pa qb : G × ι => ∑ k, (X k : MvPolynomial N O) * C (a k pa.1 qb.1 pa.2 qb.2)).det =
      (Matrix.of fun pa qb : G × ρ => ∑ k, (X k : MvPolynomial N O) * C (b k pa.1 qb.1 pa.2 qb.2)).det *
        ∏ j, (Matrix.of fun p q : G => ∑ k, (X k : MvPolynomial N O) * C (c j k p q)).det := by
  apply MvPolynomial.map_injective _ hinj
  have key := det_blocks (L := MvPolynomial N K) (P.map C) (Q.map C)
    (by rw [← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _)])
    (fun p q => ∑ k, (X k : MvPolynomial N K) • ((a k p q).map (algebraMap O K)).map C)
    (fun p q => ∑ k, (X k : MvPolynomial N K) • ((b k p q).map (algebraMap O K)).map C)
    (fun j p q => ∑ k, (X k : MvPolynomial N K) * C (algebraMap O K (c j k p q))) (by
      intro p q
      rw [Matrix.mul_sum, Matrix.sum_mul]
      simp only [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.map_mul, h]
      ext1 i j
      rcases i with i | i <;> rcases j with j | j <;>
        simp [Matrix.sum_apply, Matrix.diagonal_apply]
      split_ifs <;> simp)
  rw [map_mul, map_prod, RingHom.map_det, RingHom.map_det]
  simp only [RingHom.map_det]
  convert key using 2
  · ext1 i j
    simp [Matrix.sum_apply]
  · congr 1
    ext1 i j
    simp [Matrix.sum_apply]
  · congr 1
    funext l
    congr 1
    ext1 i j
    simp

open MvPolynomial in

theorem det_generic_eq_zero (hinj : Function.Injective (algebraMap O K)) {ι G N : Type}
    [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G] [Fintype N]
    (a : N → G → G → Matrix ι ι O) (v : G → ι → K) (hv : v ≠ 0)
    (h : ∀ k p, ∑ q, ((a k p q).map (algebraMap O K)).mulVec (v q) = 0) :
    (Matrix.of fun pa qb : G × ι => ∑ k, (X k : MvPolynomial N O) * C (a k pa.1 qb.1 pa.2 qb.2)).det = 0 := by
  apply MvPolynomial.map_injective _ hinj
  rw [RingHom.map_det, map_zero, ← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨fun qb => C (v qb.1 qb.2), fun h0 => hv ?_, ?_⟩
  · funext q j
    simpa using congrFun h0 (q, j)
  · funext ⟨p, i⟩
    have h1 : ∀ k, ∑ q, ∑ j, algebraMap O K (a k p q i j) * v q j = 0 := fun k => by
      simpa [Finset.sum_apply, Matrix.mulVec, dotProduct] using congrFun (h k p) i
    calc _ = ∑ k, (X k : MvPolynomial N K) * C (∑ q, ∑ j, algebraMap O K (a k p q i j) * v q j) := by
          simp only [Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
            map_sum, map_mul, map_X, map_C, Finset.sum_mul, Finset.mul_sum, mul_assoc]
          rw [Finset.sum_comm]
          simp only [Fintype.sum_prod_type]
      _ = 0 := by simp [h1]

end Abs2

section Span

variable {O X Γ M : Type} [CommRing O] [Ring M] [Algebra O M] [Monoid Γ]

def spanAlg (T : Subalgebra O (X → O)) (rep : X → (Γ →* M)) : Subalgebra O (X → M) where
  carrier := {a | ∃ (m : ℕ) (f : Fin m → X → O) (g : Fin m → Γ), (∀ k, f k ∈ T) ∧
      a = ∑ k, fun x => f k x • rep x (g k)}
  mul_mem' := by
    rintro _ _ ⟨m, f, g, hf, rfl⟩ ⟨m', f', g', hf', rfl⟩
    let e := (finProdFinEquiv (m := m) (n := m')).symm
    refine ⟨m * m', fun k => f (e k).1 * f' (e k).2, fun k => g (e k).1 * g' (e k).2,
      fun k => T.mul_mem (hf _) (hf' _), ?_⟩
    rw [e.sum_comp (fun k => fun x => (f k.1 * f' k.2) x • rep x (g k.1 * g' k.2)), Finset.sum_mul_sum,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    funext x
    simp [smul_smul, mul_comm]
  add_mem' := by
    rintro _ _ ⟨m, f, g, hf, rfl⟩ ⟨m', f', g', hf', rfl⟩
    refine ⟨m + m', Fin.append f f', Fin.append g g', fun k => ?_, ?_⟩
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) k
      · simpa using hf k
      · simpa using hf' k
    · rw [Fin.sum_univ_add]
      simp
  algebraMap_mem' := fun c => ⟨1, fun _ => algebraMap O _ c, fun _ => 1, fun _ => T.algebraMap_mem c, by
    funext x
    simp [Algebra.algebraMap_eq_smul_one]⟩

theorem exists_gens {B : Type} [Ring B] [Algebra O B] [IsNoetherian O B] (A : Subalgebra O B) (y : Γ → B) :
    ∃ (g : ℕ) (γ : Fin g → Γ), ∀ (m : ℕ) (a : Fin m → B) (s : Fin m → Γ), (∀ k, a k ∈ A) →
      ∃ θ : Fin g → A, ∑ k, a k * y (s k) = ∑ q, (θ q : B) * y (γ q) := by
  classical
  haveI : IsNoetherian A B := isNoetherian_of_tower O inferInstance
  obtain ⟨t, ht, hsp⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (R := A) (Set.range y)).1
    (IsNoetherian.noetherian _)
  choose σ hσ using fun b : t => ht b.2
  let e := t.equivFin.symm
  refine ⟨t.card, fun q => σ (e q), fun m a s ha => ?_⟩
  have h1 : ∑ k, a k * y (s k) ∈ Submodule.span A (Set.range fun q => y (σ (e q))) := by
    refine Submodule.sum_mem _ fun k _ => ?_
    refine Submodule.smul_mem _ (⟨a k, ha k⟩ : A) (Submodule.span_mono ?_
      (hsp ▸ Submodule.subset_span ⟨s k, rfl⟩ : y (s k) ∈ Submodule.span A (t : Set B)))
    intro b hb
    exact ⟨e.symm ⟨b, hb⟩, by simp [hσ]⟩
  obtain ⟨θ, hθ⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h1
  exact ⟨θ, hθ.symm⟩

@[reducible] def blockDim (r : ℕ) {τ : Type} : Option τ → ℕ
  | none => r
  | some _ => 1

def blockHom {A τ : Type} [Ring A] [Algebra O A] {r : ℕ} (f : A →ₐ[O] Matrix (Fin r) (Fin r) O)
    (χ : τ → (A →ₐ[O] O)) : ∀ j : Option τ, A →ₐ[O] Matrix (Fin (blockDim r j)) (Fin (blockDim r j)) O
  | none => f
  | some c => (Algebra.ofId O (Matrix (Fin 1) (Fin 1) O)).comp (χ c)

end Span

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → π ∈ D.nd.Z i → NoChiOff i r Xs → Module.length (D.nd.O i) (D.nd.O i ⧸ ccOff i Xs π) ≤ Module.length (D.nd.O i) ↥(cocRho i r S Xs) + ∑ c : Fin D.R.t, Module.length (D.nd.O i) ↥(cocChi i r S Xs c) := by
  intro D i r ρ π Xs S hr hS hπ _ hchi
  classical
  have h52 := GlobalTheory.T.cutValue_mem_heckeValueIdealOffSupport D i r ρ π Xs S hr hS hπ
  have h54 := GlobalTheory.Cut.ResidualSelmer.main D i r ρ π Xs S hr hS hπ hchi
  obtain ⟨-, -, hcomp, hsurj, -, -, -, -, -, -, -, h51, -⟩ := hS
  have hinj : Function.Injective (algebraMap (D.nd.O i) (KK D.nd i)) := IsFractionRing.injective _ _
  let A : Subalgebra (D.nd.O i) (S.X' → MatN D.nd i) := spanAlg S.T' (fun x' => rO D.nd i r (S.p x'))
  obtain ⟨g, γ, hγ⟩ := exists_gens A (yg D.nd r S)
  have hY : ∀ m, InY D.nd r S m → ∃ θ : Fin g → A, m = ∑ q, (θ q : S.X' → MatN D.nd i) * yg D.nd r S (γ q) := by
    rintro _ ⟨m, a, s, ha, rfl⟩
    exact hγ m a s ha
  obtain ⟨P, Q, hPQ, hQP, hconj⟩ := exists_conj S.e
  have hbl := fun a (ha : a ∈ A) => hconj _ _ _ (hcomp a ha)
  obtain ⟨⟨fρ, hfρ⟩, hχ⟩ := exists_homs hinj A S.π' P Q hPQ hQP S.ψρ S.ψχ hbl
  choose fχ hfχ using hχ
  let Rel : Submodule A (Fin g → A) :=
    { carrier := {θ | ∀ x', S.p x' ∈ Xs → (∑ q, (θ q : S.X' → MatN D.nd i) * yg D.nd r S (γ q)) x' = 0}
      add_mem' := fun {a b} ha hb x' hx => by
        have := congrArg₂ (· + ·) (ha x' hx) (hb x' hx)
        simpa [add_mul, Finset.sum_add_distrib] using this
      zero_mem' := fun x' _ => by simp
      smul_mem' := fun c θ hθ x' hx => by
        have := congrArg (fun z => (c : S.X' → MatN D.nd i) x' * z) (hθ x' hx)
        simpa [Finset.sum_apply, Finset.mul_sum, mul_assoc] using this }
  let d : Option (Fin D.R.t) → ℕ := blockDim D.R.r
  let ψ := blockHom fρ fχ
  have hψχ : ∀ c (a : A), ψ (some c) a = S.ψχ c a • (1 : Matrix (Fin 1) (Fin 1) (D.nd.O i)) := by
    intro c a
    rw [← hfχ, ← Algebra.algebraMap_eq_smul_one]
    rfl
  have key := GlobalTheory.T.determinantLemma_discreteValuationRing_quotientLength_bound (D.nd.O i) A (Option (Fin D.R.t)) d ψ (by
    rintro (_ | c) B
    · obtain ⟨a, ha, rfl⟩ := hsurj B
      exact ⟨⟨a, ha⟩, hfρ _⟩
    · change Matrix (Fin 1) (Fin 1) (D.nd.O i) at B
      refine ⟨algebraMap _ _ (B 0 0), ((ψ (some c)).commutes _).trans ?_⟩
      change algebraMap _ (Matrix (Fin 1) (Fin 1) (D.nd.O i)) _ = B
      ext a b
      rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
      simp [Matrix.algebraMap_matrix_apply]) g Rel (ccOff i Xs π) (by
    intro n θ hθ m
    have hT := GlobalTheory.BlockDetPoly.main S.T' D.R.nV A h51 n g (fun k p q => θ k p q) (fun k p q => (θ k p q).2) m
    have h2 := h52 _ hT (by
      intro x' hx hz
      obtain ⟨η, s, hs⟩ := h54 x' hx hz
      rw [det_generic_eq_zero hinj (fun k p q => (θ k p q : S.X' → MatN D.nd i) x')
        (fun q => ((yg D.nd r S (γ q) x').map (toK D.nd i)).mulVec η) ?_ ?_, MvPolynomial.coeff_zero]
      · intro h0
        apply hs
        obtain ⟨t, ht⟩ := hγ 1 (fun _ => 1) (fun _ => s) (fun _ => A.one_mem)
        rw [Fin.sum_univ_one, one_mul] at ht
        rw [ht, Finset.sum_apply, ← RingHom.mapMatrix_apply, map_sum, Matrix.sum_mulVec]
        refine Finset.sum_eq_zero fun q _ => ?_
        rw [Pi.mul_apply, map_mul, ← Matrix.mulVec_mulVec, RingHom.mapMatrix_apply _ (yg D.nd r S (γ q) x'),
          show ((yg D.nd r S (γ q) x').map (toK D.nd i)).mulVec η = 0 from congrFun h0 q, Matrix.mulVec_zero]
      · intro k p
        have h3 := congrArg (fun z => ((toK D.nd i).mapMatrix z).mulVec η) (hθ k p x' hx)
        simp only [Finset.sum_apply, map_sum, Matrix.sum_mulVec, Pi.mul_apply, map_mul, map_zero,
          Matrix.zero_mulVec, ← Matrix.mulVec_mulVec] at h3
        exact h3)
    rw [det_generic_blocks hinj P Q hPQ hQP (fun k p q => (θ k p q : S.X' → MatN D.nd i) S.π')
      (fun k p q => S.ψρ (θ k p q)) (fun c k p q => S.ψχ c (θ k p q))
      (fun k p q => hbl _ (θ k p q).2)] at h2
    rw [Fintype.prod_option]
    convert h2 using 3
    · congr 1
      ext1 pa qb
      simp only [Matrix.of_apply, ← hfρ]
      rfl
    · refine Finset.prod_congr rfl fun c _ => ?_
      refine (Matrix.det_submatrix_equiv_self (Equiv.prodUnique (Fin g) (Fin 1)).symm _).symm.trans ?_
      congr 1
      ext1 p q
      simp [hψχ])
  refine key.trans ?_
  rw [Fintype.sum_option]
  refine add_le_add ?_ (Finset.sum_le_sum fun c _ => ?_)
  · exact length_sol_le A fρ S.ψρ hfρ (yg D.nd r S) γ (InY D.nd r S) (fun y => ∀ x', S.p x' ∈ Xs → y x' = 0)
      hY Rel (fun _ h => h) (fun _ _ => rfl)
  · exact length_sol_le A (ψ (some c)) _ (hψχ c) (yg D.nd r S) γ (InY D.nd r S)
      (fun y => ∀ x', S.p x' ∈ Xs → y x' = 0) hY Rel (fun _ h => h) (fun _ _ => rfl)

end GlobalTheory.CutDet

end
