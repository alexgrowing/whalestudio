import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.LemmaDetPoly
import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.BridgeDet

noncomputable section

open Formalism.BasicNotions

namespace Formalism.MainNotions.LargeLevelLemmas

theorem second_proposition_every_localisation {D : D7} (i : D.nd.Loc) : Conclusion2 i :=
  endomorphism_bound_at_good_points (Formalism.MainNotions.TruncatedSeriesCountingIdentities.second_statement D) i

theorem second_statement (D : D7) : HodgeTateFromSandwich D := by
  show ∀ i, Conclusion2 i
  exact fun i => second_proposition_every_localisation i

namespace Br

open Formalism.NG Matrix Module Kronecker

section Lin

variable {R K : Type*} [CommRing K] {g n d : Type*} [Fintype g] [DecidableEq g] [Fintype n]
  [DecidableEq n] [Fintype d] [DecidableEq d]

private theorem kron_mul_apply_lemma {m : Type*} (C : Matrix d n K) (X : Matrix (g × n) m K)
    (p : g) (a : d) (y : m) :
    (kroneckerMap (· * ·) (1 : Matrix g g K) C * X) (p, a) y = ∑ e, C a e * X (p, e) y := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_comm]
  simp [Matrix.kroneckerMap_apply, Matrix.one_apply, ite_mul]

private theorem mul_kron_apply_lemma_2 {m : Type*} (X : Matrix m (g × n) K) (C : Matrix n d K)
    (y : m) (q : g) (b : d) :
    (X * kroneckerMap (· * ·) (1 : Matrix g g K) C) y (q, b) = ∑ e, X y (q, e) * C e b := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_comm]
  simp [Matrix.kroneckerMap_apply, Matrix.one_apply, ite_mul, mul_ite]

theorem bigMat_conj (F : R → Matrix n n K) (Cm : Matrix d n K) (Cm' : Matrix n d K)
    (Θ : Matrix g g R) :
    bigMat (fun a => Cm * F a * Cm') Θ =
      (kroneckerMap (· * ·) (1 : Matrix g g K) Cm) * bigMat F Θ *
        (kroneckerMap (· * ·) (1 : Matrix g g K) Cm') := by
  ext ⟨p, a⟩ ⟨q, b⟩
  rw [mul_kron_apply_lemma_2]
  simp only [kron_mul_apply_lemma]
  simp only [bigMat, Matrix.mul_apply]

theorem det_bigMat_conj (F : R → Matrix n n K) (Cm : Matrix d n K) (Cm' : Matrix n d K)
    (h1 : Cm * Cm' = 1) (h2 : Cm' * Cm = 1) (Θ : Matrix g g R) :
    (bigMat (fun a => Cm * F a * Cm') Θ).det = (bigMat F Θ).det := by
  rw [bigMat_conj]
  refine Matrix.det_conj_of_mul_eq_one ?_ ?_
  · rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, h1, Matrix.one_kronecker_one]
  · rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, h2, Matrix.one_kronecker_one]

theorem toMat_mul_symm (c : (n → K) ≃ₗ[K] (d → K)) :
    LinearMap.toMatrix' c.toLinearMap * LinearMap.toMatrix' c.symm.toLinearMap = 1 := by
  rw [← LinearMap.toMatrix'_comp]
  have hc : c.toLinearMap ∘ₗ c.symm.toLinearMap = LinearMap.id := LinearMap.ext fun x => by simp
  rw [hc, LinearMap.toMatrix'_id]

theorem toMat_symm_mul (c : (n → K) ≃ₗ[K] (d → K)) :
    LinearMap.toMatrix' c.symm.toLinearMap * LinearMap.toMatrix' c.toLinearMap = 1 := by
  rw [← LinearMap.toMatrix'_comp]
  have hc : c.symm.toLinearMap ∘ₗ c.toLinearMap = LinearMap.id := LinearMap.ext fun x => by simp
  rw [hc, LinearMap.toMatrix'_id]

theorem det_bigMat_blocks {r t : Type*} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t]
    (Fρ : R → Matrix r r K) (Fχ : t → R → K) (Θ : Matrix g g R) :
    (bigMat (fun a => fromBlocks (Fρ a) 0 0 (diagonal fun c => Fχ c a)) Θ).det =
      (bigMat Fρ Θ).det * ∏ c, (Matrix.of fun p q => Fχ c (Θ p q)).det := by
  have hre : Matrix.reindex (Equiv.prodSumDistrib g r t) (Equiv.prodSumDistrib g r t)
      (bigMat (fun a => fromBlocks (Fρ a) 0 0 (diagonal fun c => Fχ c a)) Θ) =
      fromBlocks (bigMat Fρ Θ) 0 0
        (Matrix.blockDiagonal fun c => Matrix.of fun p q => Fχ c (Θ p q)) := by
    ext (⟨p, x⟩ | ⟨p, c⟩) (⟨q, y⟩ | ⟨q, c'⟩) <;>
      simp [bigMat, Matrix.blockDiagonal_apply, Matrix.diagonal_apply]
  rw [← Matrix.det_reindex_self (Equiv.prodSumDistrib g r t), hre, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_blockDiagonal]

theorem det_bigMat_unit (F : R → K) (Θ : Matrix g g R) :
    (bigMat (fun a => (Matrix.of fun _ _ : Unit => F a)) Θ).det =
      (Matrix.of fun p q => F (Θ p q)).det := by
  have hb : bigMat (fun a => (Matrix.of fun _ _ : Unit => F a)) Θ =
      Matrix.reindex (Equiv.prodPUnit g).symm (Equiv.prodPUnit g).symm
        (Matrix.of fun p q => F (Θ p q)) := by
    ext ⟨p, u⟩ ⟨q, v⟩
    rfl
  rw [hb, Matrix.det_reindex_self]

end Lin

section Hom

variable {O : Type*} [CommRing O] [IsDomain O] {A : Type*} [Ring A] [Algebra O A]
  {n δ : Type*} [Fintype n] [DecidableEq n] [Fintype δ] [DecidableEq δ]

theorem mat_uniq (pr : (n → FractionRing O) →ₗ[FractionRing O] (δ → FractionRing O))
    (hpr : Function.Surjective pr) (B B' : Matrix δ δ O)
    (h : ∀ u, (B.map (algebraMap O (FractionRing O))) *ᵥ pr u =
      (B'.map (algebraMap O (FractionRing O))) *ᵥ pr u) : B = B' := by
  ext i j
  obtain ⟨u, hu⟩ := hpr (Pi.single j 1)
  have h1 := congrFun (h u) i
  rw [hu] at h1
  have h2 : algebraMap O (FractionRing O) (B i j) = algebraMap O (FractionRing O) (B' i j) := by
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h1
  exact IsFractionRing.injective O (FractionRing O) h2

def mkHom (ev : A →ₐ[O] Matrix n n (FractionRing O))
    (pr : (n → FractionRing O) →ₗ[FractionRing O] (δ → FractionRing O))
    (hpr : Function.Surjective pr) (F : A → Matrix δ δ O)
    (h : ∀ a u, pr (ev a *ᵥ u) = ((F a).map (algebraMap O (FractionRing O))) *ᵥ pr u) :
    A →ₐ[O] Matrix δ δ O where
  toFun := F
  map_one' := mat_uniq pr hpr _ _ fun u => by
    rw [← h, map_one, Matrix.one_mulVec, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.one_mulVec]
  map_mul' a b := mat_uniq pr hpr _ _ fun u => by
    rw [← h, map_mul, ← Matrix.mulVec_mulVec, h, h, Matrix.mulVec_mulVec, Matrix.map_mul]
  map_zero' := mat_uniq pr hpr _ _ fun u => by
    rw [← h, map_zero, Matrix.zero_mulVec, map_zero, Matrix.map_zero _ (map_zero _),
      Matrix.zero_mulVec]
  map_add' a b := mat_uniq pr hpr _ _ fun u => by
    rw [← h, map_add, Matrix.add_mulVec, map_add, h, h,
      Matrix.map_add _ (map_add _), Matrix.add_mulVec]
  commutes' c := mat_uniq pr hpr _ _ fun u => by
    rw [← h, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mulVec, Matrix.one_mulVec, LinearMap.map_smul_of_tower]
    ext a
    simp [Matrix.mulVec, dotProduct, Matrix.algebraMap_matrix_apply, Algebra.smul_def, apply_ite,
      ite_mul]

@[simp] theorem mkHom_apply (ev : A →ₐ[O] Matrix n n (FractionRing O))
    (pr : (n → FractionRing O) →ₗ[FractionRing O] (δ → FractionRing O))
    (hpr : Function.Surjective pr) (F : A → Matrix δ δ O)
    (h : ∀ a u, pr (ev a *ᵥ u) = ((F a).map (algebraMap O (FractionRing O))) *ᵥ pr u) (a : A) :
    mkHom ev pr hpr F h a = F a := rfl

end Hom

section Ker

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {A : Type*} [Ring A]
  [Algebra O A] {δ : Type*} [Fintype δ] {Q : Type*} [AddCommGroup Q] [Module O Q]

theorem len_ker_le (F : A →ₗ[O] Matrix δ δ O) (κ : (δ → KO O) →ₗ[O] Q)
    (hκ : Function.Injective κ) (actQ : Matrix δ δ O → Q →ₗ[O] Q)
    (hact : ∀ B v, actQ B (κ v) = κ (relMap O (KO O) B v)) {g m : ℕ}
    (P : Matrix (Fin m) (Fin g) A) (H : Submodule O (Fin g → Q))
    (hH : ∀ w : Fin g → Q, (∀ θ ∈ Submodule.span O (Set.range (fun k => P k)),
      ∑ j, actQ (F (θ j)) (w j) = 0) → w ∈ H) :
    Module.length O (LinearMap.ker (relMap O (KO O) (bigRect F P))) ≤ Module.length O H := by
  classical
  let φ : (Fin g × δ → KO O) →ₗ[O] (Fin g → Q) :=
    LinearMap.pi fun j => κ.comp (LinearMap.funLeft O (KO O) (Prod.mk j))
  have hφinj : Function.Injective φ := by
    intro v w hvw
    funext x
    obtain ⟨j, b⟩ := x
    have h1 : κ (fun b => v (j, b)) = κ (fun b => w (j, b)) := congrFun hvw j
    exact congrFun (hκ h1) b
  have hmem : ∀ v ∈ LinearMap.ker (relMap O (KO O) (bigRect F P)), φ v ∈ H := by
    intro v hv
    rw [LinearMap.mem_ker] at hv
    apply hH
    intro θ hθ
    let L : (Fin g → A) →ₗ[O] (δ → KO O) :=
      { toFun := fun θ => ∑ j, relMap O (KO O) (F (θ j)) (fun b => v (j, b))
        map_add' := fun θ θ' => by
          funext b
          simp [relMap, Finset.sum_apply, add_smul, Finset.sum_add_distrib]
        map_smul' := fun c θ => by
          funext b
          simp [relMap, Finset.sum_apply, Finset.smul_sum, smul_smul] }
    have hL : θ ∈ LinearMap.ker L := by
      refine Submodule.span_le.mpr ?_ hθ
      rintro _ ⟨k, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      funext b
      have hk := congrFun hv (k, b)
      simpa [L, relMap, bigRect, Fintype.sum_prod_type, Finset.sum_apply] using hk
    rw [LinearMap.mem_ker] at hL
    have hs : ∑ j, actQ (F (θ j)) (φ v j) = κ (L θ) := by
      simp only [L, LinearMap.coe_mk, AddHom.coe_mk, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact hact _ _
    rw [hs, hL, map_zero]
  let ψ : LinearMap.ker (relMap O (KO O) (bigRect F P)) →ₗ[O] H :=
    LinearMap.codRestrict H (φ.comp (LinearMap.ker _).subtype) fun v => hmem v v.2
  have hψ : Function.Injective ψ := by
    intro v w hvw
    apply Subtype.ext
    apply hφinj
    exact congrArg Subtype.val hvw
  first
  | exact Module.length_le_of_injective ψ hψ
  | exact Module.length_le_of_injective hψ

end Ker

def dW (r t : ℕ) : Option (Fin t) → Type
  | none => Fin r
  | some _ => Unit

instance (r t : ℕ) : ∀ w, Fintype (dW r t w)
  | none => inferInstanceAs (Fintype (Fin r))
  | some _ => inferInstanceAs (Fintype Unit)

instance (r t : ℕ) : ∀ w, DecidableEq (dW r t w)
  | none => inferInstanceAs (DecidableEq (Fin r))
  | some _ => inferInstanceAs (DecidableEq Unit)

theorem sum_card_dW (r t : ℕ) : ∑ w, Fintype.card (dW r t w) = r + t := by
  rw [Fintype.sum_option]
  show Fintype.card (Fin r) + ∑ _c : Fin t, Fintype.card Unit = r + t
  simp

section Core

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {X' : Type} {n : Type} [Fintype n] [DecidableEq n] {r t : ℕ}
  (A : Subalgebra O (X' → Matrix n n O)) (π' : X')

def evK : A →ₐ[O] Matrix n n (FractionRing O) :=
  ((Algebra.ofId O (FractionRing O)).mapMatrix).comp
    ((Pi.evalAlgHom O (fun _ : X' => Matrix n n O) π').comp A.val)

theorem evK_apply (a : A) :
    evK A π' a = ((a : X' → Matrix n n O) π').map (algebraMap O (FractionRing O)) := rfl

variable (e : (n → FractionRing O) ≃ₗ[FractionRing O]
    ((Fin r → FractionRing O) × (Fin t → FractionRing O)))
  (ψρ : A → Matrix (Fin r) (Fin r) O) (ψχ : Fin t → A → O)
  (hint : ∀ (a : A) u, e (((a : X' → Matrix n n O) π').map (algebraMap O (FractionRing O)) *ᵥ u) =
    ((ψρ a).map (algebraMap O (FractionRing O)) *ᵥ (e u).1,
      fun c => algebraMap O (FractionRing O) (ψχ c a) * (e u).2 c))

def homρ : A →ₐ[O] Matrix (Fin r) (Fin r) O :=
  mkHom (evK A π') ((LinearMap.fst _ _ _).comp e.toLinearMap)
    (fun w => ⟨e.symm (w, 0), by simp⟩) ψρ
    (fun a u => by
      show (e (evK A π' a *ᵥ u)).1 = _
      rw [evK_apply, hint]
      rfl)

def homχ (c : Fin t) : A →ₐ[O] Matrix Unit Unit O :=
  mkHom (evK A π')
    ((LinearMap.pi fun _ : Unit => LinearMap.proj c).comp
      ((LinearMap.snd _ _ _).comp e.toLinearMap))
    (fun w => ⟨e.symm (0, fun _ => w ()), by funext x; simp⟩)
    (fun a => Matrix.of fun _ _ => ψχ c a)
    (fun a u => by
      funext x
      show (e (evK A π' a *ᵥ u)).2 c = _
      rw [evK_apply, hint]
      simp [Matrix.mulVec, dotProduct])

def homW : ∀ w, A →ₐ[O] Matrix (dW r t w) (dW r t w) O
  | none => homρ A π' e ψρ ψχ hint
  | some c => homχ A π' e ψρ ψχ hint c

include hint

theorem blocks_eq (a : A) :
    (fromBlocks (ψρ a) 0 0 (diagonal fun c => ψχ c a)).map (algebraMap O (FractionRing O)) =
      LinearMap.toMatrix' ((e.trans (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin t)
          (FractionRing O) (FractionRing O)).symm).toLinearMap) * evK A π' a *
        LinearMap.toMatrix' ((e.trans (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin t)
          (FractionRing O) (FractionRing O)).symm).symm.toLinearMap) := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun w => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
  have hu : e ((e.trans (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin t) (FractionRing O)
      (FractionRing O)).symm).symm w) =
      LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin t) (FractionRing O) (FractionRing O) w := by
    simp
  have h := hint a ((e.trans (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin t) (FractionRing O)
      (FractionRing O)).symm).symm w)
  rw [← evK_apply, hu] at h
  simp only [LinearEquiv.coe_coe]
  rw [LinearEquiv.trans_apply, h]
  clear h hu hint
  funext x
  rcases x with x | c
  · simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.map_apply,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, map_zero, zero_mul,
      Finset.sum_const_zero, add_zero]
    rfl
  · simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.map_apply,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, map_zero, zero_mul,
      Finset.sum_const_zero, zero_add, Matrix.diagonal_apply]
    rw [Finset.sum_eq_single c]
    · simp
    · intro b _ hb
      rw [if_neg (Ne.symm hb), map_zero, zero_mul]
    · simp

theorem det_at (g : ℕ) (Θ : Matrix (Fin g) (Fin g) A) :
    (bigMat (fun a : A => (a : X' → Matrix n n O) π') Θ).det =
      (bigMat ψρ Θ).det * ∏ c, (bigMat (fun a => (Matrix.of fun _ _ : Unit => ψχ c a)) Θ).det := by
  apply IsFractionRing.injective O (FractionRing O)
  simp only [det_bigMat_unit]
  rw [← det_bigMat_blocks ψρ ψχ Θ, RingHom.map_det, RingHom.map_det]
  have e1 : (algebraMap O (FractionRing O)).mapMatrix
      (bigMat (fun a : A => (a : X' → Matrix n n O) π') Θ) = bigMat (fun a => evK A π' a) Θ := by
    ext p q
    rfl
  have e2 : (algebraMap O (FractionRing O)).mapMatrix
      (bigMat (fun a => fromBlocks (ψρ a) 0 0 (diagonal fun c => ψχ c a)) Θ) =
      bigMat (fun a => LinearMap.toMatrix' (e.trans (LinearEquiv.sumArrowLequivProdArrow (Fin r)
          (Fin t) (FractionRing O) (FractionRing O)).symm).toLinearMap * evK A π' a *
        LinearMap.toMatrix' (e.trans (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin t)
          (FractionRing O) (FractionRing O)).symm).symm.toLinearMap) Θ := by
    ext p q
    exact congrFun (congrFun (blocks_eq A π' e ψρ ψχ hint (Θ p.1 q.1)) p.2) q.2
  rw [e1, e2, det_bigMat_conj _ _ _ (toMat_mul_symm _) (toMat_symm_mul _)]

theorem det_valuation_eq_length (hsurj : Function.Surjective ψρ) (g m : ℕ)
    (hcard : ((g * (r + t) : ℕ) : Cardinal) < Cardinal.mk (IsLocalRing.ResidueField O))
    (P : Matrix (Fin m) (Fin g) A) :
    ∃ C : Matrix (Fin g) (Fin m) A,
      IsDiscreteValuationRing.addVal O
          (bigMat (fun a : A => (a : X' → Matrix n n O) π') (C * P)).det =
        Module.length O (LinearMap.ker (relMap O (KO O) (bigRect ψρ P))) +
          ∑ c, Module.length O (LinearMap.ker (relMap O (KO O)
            (bigRect (fun a => (Matrix.of fun _ _ : Unit => ψχ c a)) P))) := by
  have hs : ∀ w, Function.Surjective (homW A π' e ψρ ψχ hint w) := by
    intro w
    cases w with
    | none => exact hsurj
    | some c =>
      intro B
      refine ⟨algebraMap O A (B () ()), ?_⟩
      rw [AlgHom.commutes]
      ext x y
      have h : ∀ (x y : Unit) (B : Matrix Unit Unit O),
          algebraMap O (Matrix Unit Unit O) (B () ()) x y = B x y :=
        fun _ _ _ => by simp [Matrix.algebraMap_matrix_apply]
      exact h x y B
  obtain ⟨C, hC⟩ := genericFin A O (Fin m) (Fin g) (Option (Fin t)) (dW r t)
    (by rw [sum_card_dW, Fintype.card_fin]; exact hcard) (homW A π' e ψρ ψχ hint) hs P
  refine ⟨C, ?_⟩
  rw [det_at A π' e ψρ ψχ hint, IsDiscreteValuationRing.addVal_mul, IdempotentNormalFormsLenFacts.addVal_prod]
  have h0 := (lenKer O _ (bigMat (homW A π' e ψρ ψχ hint none) (C * P))).symm.trans (hC none)
  have hc := fun c =>
    (lenKer O _ (bigMat (homW A π' e ψρ ψχ hint (some c)) (C * P))).symm.trans (hC (some c))
  exact congrArg₂ (· + ·) h0 (Finset.sum_congr rfl fun c _ => hc c)

end Core

section Kap

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (δ : Type*) [Fintype δ]
  [DecidableEq δ]

theorem pi_one_eq :
    Submodule.pi Set.univ (fun _ : δ => (1 : Submodule O (FractionRing O))) =
      LinearMap.range (LinearMap.compLeft (Algebra.linearMap O (FractionRing O)) δ) := by
  ext v
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies, forall_const, Submodule.mem_one,
    LinearMap.mem_range]
  constructor
  · intro h
    choose w hw using h
    exact ⟨w, funext fun b => hw b⟩
  · rintro ⟨w, rfl⟩ b
    exact ⟨w b, rfl⟩

def kap : (δ → KO O) ≃ₗ[O] ((δ → FractionRing O) ⧸
    LinearMap.range (LinearMap.compLeft (Algebra.linearMap O (FractionRing O)) δ)) :=
  (Submodule.quotientPi (fun _ : δ => (1 : Submodule O (FractionRing O)))).symm.trans
    (Submodule.quotEquivOfEq _ _ (pi_one_eq O δ))

theorem kap_mk (v : δ → FractionRing O) :
    kap O δ (fun b => Submodule.Quotient.mk (v b)) = Submodule.Quotient.mk v := by
  have h : (Submodule.quotientPi fun _ : δ => (1 : Submodule O (FractionRing O))).symm
      (fun b => Submodule.Quotient.mk (v b)) = Submodule.Quotient.mk v :=
    (LinearEquiv.symm_apply_eq _).mpr rfl
  rw [kap, LinearEquiv.trans_apply, h]
  rfl

theorem kap_act (B : Matrix δ δ O)
    (h : LinearMap.range (LinearMap.compLeft (Algebra.linearMap O (FractionRing O)) δ) ≤
      (LinearMap.range (LinearMap.compLeft (Algebra.linearMap O (FractionRing O)) δ)).comap
        (((B.map (algebraMap O (FractionRing O))).mulVecLin).restrictScalars O))
    (v : δ → KO O) :
    Submodule.mapQ _ _ (((B.map (algebraMap O (FractionRing O))).mulVecLin).restrictScalars O) h
        (kap O δ v) = kap O δ (relMap O (KO O) B v) := by
  choose w hw using fun b => Submodule.Quotient.mk_surjective _ (v b)
  have hv : v = fun b => Submodule.Quotient.mk (w b) := funext fun b => (hw b).symm
  subst hv
  have hr : relMap O (KO O) B (fun b => Submodule.Quotient.mk (w b)) =
      fun b => Submodule.Quotient.mk (p := (1 : Submodule O (FractionRing O)))
        (((B.map (algebraMap O (FractionRing O))) *ᵥ w) b) := by
    funext b
    show ∑ j, B b j • (Submodule.mkQ _ (w j)) =
      Submodule.mkQ _ (∑ j, algebraMap O (FractionRing O) (B b j) * w j)
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← map_smul, Algebra.smul_def]
  rw [hr, kap_mk, kap_mk]
  rfl

end Kap

section Abs

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {X X' : Type} {n : Type} [Fintype n] [DecidableEq n] {r t : ℕ}
  (A : Subalgebra O (X' → Matrix n n O)) (π' : X')
  (e : (n → FractionRing O) ≃ₗ[FractionRing O]
    ((Fin r → FractionRing O) × (Fin t → FractionRing O)))
  (ψρ : A → Matrix (Fin r) (Fin r) O) (ψχ : Fin t → A → O)
  (hint : ∀ (a : A) u, e (((a : X' → Matrix n n O) π').map (algebraMap O (FractionRing O)) *ᵥ u) =
    ((ψρ a).map (algebraMap O (FractionRing O)) *ᵥ (e u).1,
      fun c => algebraMap O (FractionRing O) (ψχ c a) * (e u).2 c))

include hint

theorem relation_length_abstract (T : Subalgebra O (X → O)) (T' : Subalgebra O (X' → O)) (Z : Set X) (p : X' → X)
    (q : ℕ) (b : Fin q → X' → O)
    (hspan : ∀ f' ∈ T', ∃ a : Fin q → (X → O), (∀ k, a k ∈ T) ∧ f' = ∑ k, (a k ∘ p) * b k)
    (hinj : ∀ x ∉ Z, ∀ a : Fin q → O, (∀ x', p x' = x → ∑ k, a k * b k x' = 0) → a = 0)
    (hsurj : Function.Surjective ψρ) (g : ℕ)
    (hcard : ((g * (r + t) : ℕ) : Cardinal) < Cardinal.mk (IsLocalRing.ResidueField O))
    (hdet : ∀ Θ : Matrix (Fin g) (Fin g) A,
      (fun x' => (bigMat (fun a : A => (a : X' → Matrix n n O) x') Θ).det) ∈ T')
    (Rel : Submodule O (Fin g → A)) (hfg : Rel.FG)
    (hmul : ∀ a : A, ∀ θ ∈ Rel, (fun j => a * θ j) ∈ Rel)
    (hne : ∀ x', p x' ∉ Z → ∃ v : Fin g → n → FractionRing O, v ≠ 0 ∧
      ∀ θ ∈ Rel, ∑ j, ((θ j : X' → Matrix n n O) x').map (algebraMap O (FractionRing O)) *ᵥ v j = 0)
    {Qρ Qχ : Type} [AddCommGroup Qρ] [Module O Qρ] [AddCommGroup Qχ] [Module O Qχ]
    (κρ : (Fin r → KO O) →ₗ[O] Qρ) (hκρ : Function.Injective κρ)
    (actρ : Matrix (Fin r) (Fin r) O → Qρ →ₗ[O] Qρ)
    (hactρ : ∀ B v, actρ B (κρ v) = κρ (relMap O (KO O) B v))
    (Hρ : Submodule O (Fin g → Qρ))
    (hHρ : ∀ w : Fin g → Qρ, (∀ θ ∈ Rel, ∑ j, actρ (ψρ (θ j)) (w j) = 0) → w ∈ Hρ)
    (κχ : (Unit → KO O) →ₗ[O] Qχ) (hκχ : Function.Injective κχ)
    (Hχ : Fin t → Submodule O (Fin g → Qχ))
    (hHχ : ∀ c (w : Fin g → Qχ), (∀ θ ∈ Rel, ∑ j, ψχ c (θ j) • w j = 0) → w ∈ Hχ c) :
    vcc T Z (p π') ≤ Module.length O Hρ + ∑ c, Module.length O (Hχ c) := by
  obtain ⟨m, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  let P : Matrix (Fin m) (Fin g) A := Matrix.of s
  have hsP : Submodule.span O (Set.range (fun k => P k)) = Rel := hs
  obtain ⟨C, hC⟩ := det_valuation_eq_length A π' e ψρ ψχ hint hsurj g m hcard P
  have hsmem : ∀ k, s k ∈ Rel := fun k => hs ▸ Submodule.subset_span ⟨k, rfl⟩
  have hrow : ∀ a, (fun j => (C * P) a j) ∈ Rel := by
    intro a
    have h : (fun j => (C * P) a j) = ∑ k, fun j => C a k * s k j := by
      funext j
      simp [Matrix.mul_apply, P]
    rw [h]
    exact Submodule.sum_mem _ fun k _ => hmul _ _ (hsmem k)
  have hvan : ∀ x', p x' ∉ Z →
      (bigMat (fun a : A => (a : X' → Matrix n n O) x') (C * P)).det = 0 := by
    intro x' hx'
    obtain ⟨v, hv0, hv⟩ := hne x' hx'
    apply IsFractionRing.injective O (FractionRing O)
    rw [RingHom.map_det, map_zero]
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨fun qb => v qb.1 qb.2, ?_, ?_⟩
    · intro h
      apply hv0
      funext j c
      exact congrFun h (j, c)
    · funext ⟨a, c⟩
      have h := congrFun (hv _ (hrow a)) c
      simp only [Finset.sum_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at h
      simpa [Matrix.mulVec, dotProduct, bigMat, Fintype.sum_prod_type] using h
  have h1 := vccSpan O X T Z (p π') _
    (descent O X X' T T' Z p q b hspan hinj _ (hdet (C * P)) hvan π')
  rw [hC] at h1
  refine h1.trans (add_le_add ?_ (Finset.sum_le_sum fun c _ => ?_))
  · exact len_ker_le (homρ A π' e ψρ ψχ hint).toLinearMap κρ hκρ actρ hactρ P Hρ
      (fun w hw => hHρ w (fun θ hθ => hw θ (hsP ▸ hθ)))
  · refine len_ker_le (homχ A π' e ψρ ψχ hint c).toLinearMap κχ hκχ
      (fun B => B () () • LinearMap.id) ?_ P (Hχ c)
      (fun w hw => hHχ c w (fun θ hθ => hw θ (hsP ▸ hθ)))
    intro B v
    have h : relMap O (KO O) B v = B () () • v := by
      funext x
      simp [relMap]
    rw [h, map_smul]
    rfl

end Abs

section Conc

open Formalism.MainNotions.N

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}

theorem inSpan_of_fintype {X' : Type} (T' : Subalgebra (N.O i) (X' → N.O i))
    (rep : X' → (GE N →* MatN N i)) {ι : Type} [Fintype ι] (f : ι → X' → N.O i) (γ : ι → GE N)
    (hf : ∀ k, f k ∈ T') : InSpan N i T' rep (∑ k, fun x' => f k x' • rep x' (γ k)) := by
  classical
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun k => f (e.symm k), fun k => γ (e.symm k), fun k => hf _, ?_⟩
  first
  | exact (Equiv.sum_comp e.symm (fun k => fun x' => f k x' • rep x' (γ k))).symm
  | exact Equiv.sum_comp e.symm (fun k => fun x' => f k x' • rep x' (γ k))

def spanAlg {X' : Type} (T' : Subalgebra (N.O i) (X' → N.O i)) (rep : X' → (GE N →* MatN N i)) :
    Subalgebra (N.O i) (X' → MatN N i) where
  carrier := {a | InSpan N i T' rep a}
  mul_mem' := by
    rintro _ _ ⟨m, f, γ, hf, rfl⟩ ⟨m', f', γ', hf', rfl⟩
    have h := inSpan_of_fintype N T' rep (ι := Fin m × Fin m') (fun k => f k.1 * f' k.2)
      (fun k => γ k.1 * γ' k.2) (fun k => T'.mul_mem (hf _) (hf' _))
    have he : (∑ k, fun x' => f k x' • rep x' (γ k)) * (∑ k, fun x' => f' k x' • rep x' (γ' k)) =
        ∑ k : Fin m × Fin m', fun x' => (f k.1 * f' k.2) x' • rep x' (γ k.1 * γ' k.2) := by
      rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
      funext x'
      simp only [Pi.mul_apply, map_mul, smul_mul_assoc, mul_smul_comm, smul_smul]
      rw [mul_comm]
    show InSpan N i T' rep _
    rw [he]
    exact h
  add_mem' := by
    rintro _ _ ⟨m, f, γ, hf, rfl⟩ ⟨m', f', γ', hf', rfl⟩
    have h := inSpan_of_fintype N T' rep (ι := Fin m ⊕ Fin m') (Sum.elim f f') (Sum.elim γ γ')
      (fun k => by cases k <;> simp [hf, hf'])
    show InSpan N i T' rep _
    rw [Fintype.sum_sum_type] at h
    exact h
  algebraMap_mem' c := by
    have h := inSpan_of_fintype N T' rep (ι := Unit) (fun _ => algebraMap (N.O i) (X' → N.O i) c)
      (fun _ => 1) (fun _ => T'.algebraMap_mem c)
    have he : algebraMap (N.O i) (X' → MatN N i) c =
        ∑ _k : Unit, fun x' => algebraMap (N.O i) (X' → N.O i) c x' • rep x' 1 := by
      funext x'
      simp [Algebra.algebraMap_eq_smul_one]
    show InSpan N i T' rep _
    rw [he]
    exact h

variable (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
  (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) (π : N.X i) (S : IdempotentChoiceData N i)

abbrev algR' : Subalgebra (N.O i) (S.X' → MatN N i) :=
  spanAlg N S.T' (fun x' => rO N i r (S.p x'))

def kapN (i : N.Loc) : (Fin R.r → KO (N.O i)) ≃ₗ[N.O i] KOr N i := kap (N.O i) (Fin R.r)

theorem kapN_act (B : Matrix (Fin R.r) (Fin R.r) (N.O i)) (v : Fin R.r → KO (N.O i)) :
    Formalism.MainNotions.N.matQ N B (kapN N i v) = kapN N i (relMap (N.O i) (KO (N.O i)) B v) := kap_act (N.O i) (Fin R.r) B _ v

def kapU (i : N.Loc) : (Unit → KO (N.O i)) →ₗ[N.O i] KmodO (N.O i) :=
  (Submodule.quotEquivOfEq (1 : Submodule (N.O i) (KK N i)) _
    Submodule.one_eq_range).toLinearMap.comp (LinearMap.proj ())

theorem kapU_inj : Function.Injective (kapU N i) := by
  intro v w h
  funext u
  cases u
  exact (Submodule.quotEquivOfEq (1 : Submodule (N.O i) (KK N i)) _ Submodule.one_eq_range).injective h

theorem mem_homRho {g : ℕ} (Rel : Set (Fin g → S.X' → MatN N i)) (w : Fin g → KOr N i) :
    w ∈ homRho N S Rel ↔ ∀ θ ∈ Rel, ∑ j, Formalism.MainNotions.N.matQ N (S.ψρ (θ j)) (w j) = 0 := by
  unfold homRho
  simp [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sum_apply]

theorem mem_homChi {g : ℕ} (Rel : Set (Fin g → S.X' → MatN N i)) (c : Fin R.t)
    (w : Fin g → KmodO (N.O i)) :
    w ∈ homChi N S Rel c ↔ ∀ θ ∈ Rel, ∑ j, S.ψχ c (θ j) • w j = 0 := by
  unfold homChi
  simp [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sum_apply]

theorem relation_lemma_of_large_residue (hG : GoodCongruenceObjects N r ρ π S) (g : ℕ)
    (hcard : ((g * R.nV : ℕ) : Cardinal) < Cardinal.mk (kk N i))
    (Rel : Set (Fin g → S.X' → MatN N i))
    (hRel : ∀ θ ∈ Rel, ∀ j, InR' N r S (θ j)) (h0 : 0 ∈ Rel)
    (hadd : ∀ θ ∈ Rel, ∀ θ' ∈ Rel, θ + θ' ∈ Rel)
    (hmul : ∀ a, InR' N r S a → ∀ θ ∈ Rel, (fun j => a * θ j) ∈ Rel)
    (hne : ∀ x', S.p x' ∉ N.Z i → ∃ v : Fin g → Fin R.nV → KK N i, v ≠ 0 ∧
      ∀ θ ∈ Rel, ∑ j, ((θ j x').map (toK N i)).mulVec (v j) = 0)
    (hfρ : Module.length (N.O i) ↥(homRho N S Rel) < ⊤)
    (hfχ : ∀ c, Module.length (N.O i) ↥(homChi N S Rel c) < ⊤) :
    N.vcc i π ≤ lenUnit (O := N.O i) (N.l i) ↥(homRho N S Rel) +
      ∑ c, lenUnit (O := N.O i) (N.l i) ↥(homChi N S Rel c) := by
  classical
  obtain ⟨-, -, hint, hsurj, -, -, -, ⟨-, -, -, ⟨b, -, hfree⟩, -⟩, -, ⟨hπ', -⟩, -, hL51⟩ := hG
  let RelS : Submodule (N.O i) (Fin g → algR' N r S) :=
    { carrier := {θ | (fun j => (θ j : S.X' → MatN N i)) ∈ Rel}
      zero_mem' := h0
      add_mem' := fun {θ θ'} hθ hθ' => hadd _ hθ _ hθ'
      smul_mem' := fun c θ hθ => by
        have h := hmul _ ((algR' N r S).algebraMap_mem c) _ hθ
        have he : (fun j => algebraMap (N.O i) (S.X' → MatN N i) c * (θ j : S.X' → MatN N i)) =
            fun j => (((c • θ) j : algR' N r S) : S.X' → MatN N i) := by
          funext j
          simp [Algebra.smul_def]
        rw [he] at h
        exact h }
  have hnoeth : IsNoetherian (N.O i) (algR' N r S) :=
    inferInstanceAs (IsNoetherian (N.O i) (Subalgebra.toSubmodule (algR' N r S)))
  have key := relation_length_abstract (algR' N r S) S.π' S.e (fun a => S.ψρ a.1) (fun c a => S.ψχ c a.1)
    (fun a u => hint a.1 a.2 u) (N.T i) S.T' (N.Z i : Set (N.X i)) S.p R.t.factorial b
    (fun f' hf' => by
      obtain ⟨cf, hcf, -⟩ := hfree f' hf'
      exact ⟨fun k => (cf k : N.X i → N.O i), fun k => (cf k).2, hcf⟩)
    (fun x _ a ha => by
      obtain ⟨gx, hgx, hgx0⟩ := Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.exists_bump (N.T i) (N.T_sep i) x
      have hu := (hfree 0 S.T'.zero_mem).unique (y₁ := fun k => a k • gx) (y₂ := 0)
        (by
          funext x'
          simp only [Pi.zero_apply, Finset.sum_apply, Pi.mul_apply]
          by_cases hx' : S.p x' = x
          · have h := ha x' hx'
            have h2 : ∑ k, ((a k • gx : N.T i) : N.X i → N.O i) (S.p x') * b k x' =
                (gx : N.X i → N.O i) (S.p x') * ∑ k, a k * b k x' := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun k _ => ?_
              show a k * (gx : N.X i → N.O i) (S.p x') * b k x' = _
              ring
            rw [h2, h, mul_zero]
          · refine (Finset.sum_eq_zero fun k _ => ?_).symm
            show a k * (gx : N.X i → N.O i) (S.p x') * b k x' = 0
            rw [hgx0 _ hx', mul_zero, zero_mul])
        (by
          funext x'
          simp [Finset.sum_apply])
      funext k
      have hk := congrArg (fun z : N.T i => (z : N.X i → N.O i) x) (congrFun hu k)
      have hk' : a k * (gx : N.X i → N.O i) x = 0 := hk
      exact (mul_eq_zero.mp hk').resolve_right hgx)
    (fun B => by
      obtain ⟨a, ha, hB⟩ := hsurj B
      exact ⟨⟨a, ha⟩, hB⟩)
    g hcard
    (fun Θ => hL51.2 g (fun p q => (Θ p q : S.X' → MatN N i)) (fun p q => (Θ p q).2))
    RelS (IsNoetherian.noetherian RelS)
    (fun a θ hθ => hmul a.1 a.2 _ hθ)
    (fun x' hx' => by
      obtain ⟨v, hv0, hv⟩ := hne x' (by simpa using hx')
      exact ⟨v, hv0, fun θ hθ => hv _ hθ⟩)
    (Qρ := KOr N i) (Qχ := KmodO (N.O i))
    (kapN N i).toLinearMap (kapN N i).injective (Formalism.MainNotions.N.matQ N) (kapN_act N)
    (homRho N S Rel)
    (fun w hw => (mem_homRho N S Rel w).mpr fun θ hθ => hw (fun j => ⟨θ j, hRel θ hθ j⟩) hθ)
    (kapU N i) (kapU_inj N)
    (homChi N S Rel)
    (fun c w hw => (mem_homChi N S Rel c w).mpr fun θ hθ => hw (fun j => ⟨θ j, hRel θ hθ j⟩) hθ)
  rw [hπ', ← Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.length_ccAt] at key
  obtain ⟨nρ, hnρ⟩ := ENat.ne_top_iff_exists.mp hfρ.ne
  have hχ' : ∀ c, ∃ k : ℕ, (k : ℕ∞) = Module.length (N.O i) ↥(homChi N S Rel c) :=
    fun c => ENat.ne_top_iff_exists.mp (hfχ c).ne
  choose nχ hnχ using hχ'
  simp only [NData.vcc, lenUnit, ← hnρ, ← hnχ, ENat.toNat_natCast]
  have key2 : Module.length (N.O i) (N.O i ⧸ ccAt (N.T i) (N.Z i) π) ≤
      ((nρ + ∑ c, nχ c : ℕ) : ℕ∞) := by
    push_cast
    rw [hnρ]
    simp only [hnχ]
    exact key
  have key3 := ENat.toNat_le_of_le_natCast key2
  rw [← Finset.sum_div, ← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast key3

def RelationLemmaGenerators (g : ℕ) : Prop :=
  ∀ Rel : Set (Fin g → S.X' → MatN N i),
    (∀ θ ∈ Rel, ∀ j, InR' N r S (θ j)) → 0 ∈ Rel → (∀ θ ∈ Rel, ∀ θ' ∈ Rel, θ + θ' ∈ Rel) →
    (∀ a, InR' N r S a → ∀ θ ∈ Rel, (fun j => a * θ j) ∈ Rel) →
    (∀ x', S.p x' ∉ N.Z i → ∃ v : Fin g → Fin R.nV → KK N i, v ≠ 0 ∧
      ∀ θ ∈ Rel, ∑ j, ((θ j x').map (toK N i)).mulVec (v j) = 0) →
    Module.length (N.O i) ↥(homRho N S Rel) < ⊤ →
    (∀ c, Module.length (N.O i) ↥(homChi N S Rel c) < ⊤) →
    N.vcc i π ≤ lenUnit (O := N.O i) (N.l i) ↥(homRho N S Rel) +
      ∑ c, lenUnit (O := N.O i) (N.l i) ↥(homChi N S Rel c)

theorem relation_lemma_iff : QuotientHomNonvanishingBound N r π S ↔
    ∀ g, ((g * R.nV : ℕ) : Cardinal) < Cardinal.mk (kk N i) → RelationLemmaGenerators N r π S g := Iff.rfl

theorem relation_lemma_at_of_large (hG : GoodCongruenceObjects N r ρ π S) (g : ℕ)
    (hcard : ((g * R.nV : ℕ) : Cardinal) < Cardinal.mk (kk N i)) : RelationLemmaGenerators N r π S g := by
  intro Rel h1 h2 h3 h4 h5 h6 h7
  exact relation_lemma_of_large_residue N r ρ π S hG g hcard Rel h1 h2 h3 h4 h5 h6 h7

theorem relation_lemma (hG : GoodCongruenceObjects N r ρ π S) : QuotientHomNonvanishingBound N r π S := (relation_lemma_iff N r π S).2 fun g hg => relation_lemma_at_of_large N r ρ π S hG g hg

end Conc

end Br

theorem relation_lemma_clause {D : D7} (i : D.nd.Loc)
    (r : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* Matrix.GeneralLinearGroup (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* Matrix.GeneralLinearGroup (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i) : HomRelationsLemmaAllChoices i r ρ π := by
  intro _ S hG
  exact Br.relation_lemma D.nd r ρ π S hG

end Formalism.MainNotions.LargeLevelLemmas

namespace Formalism.MainNotions.N.Inst

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.MainNotions.N

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)

section Count

theorem inj_of_card {A : Type} [CommRing A] [IsDomain A] {t : ℕ} {F : Type} [Fintype F]
    (Φ : F → (Fin t → A)) (hinj : Function.Injective Φ) (P : Polynomial A)
    (hP : ∀ x, ∏ c, (Polynomial.X - Polynomial.C (Φ x c)) = P)
    (hcard : t.factorial ≤ Fintype.card F) (x : F) : Function.Injective (Φ x) := by
  classical
  by_contra hni
  obtain ⟨i, j, hij, hne⟩ : ∃ i j, Φ x i = Φ x j ∧ i ≠ j := by
    unfold Function.Injective at hni
    push_neg at hni
    exact hni
  have hroot : ∀ z, Multiset.map (Φ z) Finset.univ.val = P.roots := by
    intro z
    have hm : (Finset.univ.val.map fun c => Polynomial.X - Polynomial.C (Φ z c)) =
        (Finset.univ.val.map (Φ z)).map fun a => Polynomial.X - Polynomial.C a := by
      rw [Multiset.map_map]
      rfl
    rw [← hP z, Finset.prod_eq_multiset_prod, hm, Polynomial.roots_multiset_prod_X_sub_C]
  have hperm : ∀ y, ∃ σ : Fin t ≃ Fin t, ∀ c, Φ y c = Φ x (σ c) := by
    intro y
    have hcd : ∀ a, Fintype.card {c // Φ y c = a} = Fintype.card {c // Φ x c = a} := by
      intro a
      have h := congrArg (Multiset.count a) ((hroot y).trans (hroot x).symm)
      rw [Multiset.count_map, Multiset.count_map] at h
      rw [Fintype.card_congr (Equiv.subtypeEquivRight fun c => eq_comm (a := Φ y c) (b := a)),
        Fintype.card_congr (Equiv.subtypeEquivRight fun c => eq_comm (a := Φ x c) (b := a)),
        Fintype.card_subtype, Fintype.card_subtype]
      rw [Finset.card_def, Finset.card_def, Finset.filter_val, Finset.filter_val]
      convert h
    exact ⟨Equiv.ofFiberEquiv fun a => Fintype.equivOfCardEq (hcd a),
      fun c => (Equiv.ofFiberEquiv_map _ c).symm⟩
  choose σ hσ using hperm
  let τ : F → Equiv.Perm (Fin t) := fun y => if σ y = Equiv.swap i j then 1 else σ y
  have hswap : ∀ c, Φ x (Equiv.swap i j c) = Φ x c := by
    intro c
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · rw [h1, hij]
    · rw [h2, hij]
    · rfl
  have hsw : (Equiv.swap i j : Equiv.Perm (Fin t)) ≠ 1 := by
    intro h
    have h1 := congrArg (fun f : Equiv.Perm (Fin t) => f i) h
    have h2 : j = i := by simpa using h1
    exact hne h2.symm
  have hτv : ∀ y c, Φ y c = Φ x (τ y c) := by
    intro y c
    by_cases h : σ y = Equiv.swap i j
    · dsimp only [τ]
      rw [if_pos h, hσ y c, h]
      exact hswap c
    · dsimp only [τ]
      rw [if_neg h, hσ y c]
  have hτne : ∀ y, τ y ≠ Equiv.swap i j := by
    intro y
    by_cases h : σ y = Equiv.swap i j
    · dsimp only [τ]
      rw [if_pos h]
      exact hsw.symm
    · dsimp only [τ]
      rw [if_neg h]
      exact h
  have hτinj : Function.Injective τ := by
    intro y y' h
    apply hinj
    funext c
    rw [hτv y c, hτv y' c, h]
  have hlt := Fintype.card_lt_of_injective_not_surjective τ hτinj
    (fun hs => by
      obtain ⟨y, hy⟩ := hs (Equiv.swap i j)
      exact hτne y hy)
  rw [Fintype.card_perm, Fintype.card_fin] at hlt
  omega

theorem sep_of_indep {A : Type} [CommRing A] [IsDomain A] {F : Type} [Fintype F] {q : ℕ}
    (hq : Fintype.card F = q) (b : Fin q → F → A)
    (hind : ∀ a : Fin q → A, (∀ x, ∑ k, a k * b k x = 0) → a = 0) (x y : F)
    (hxy : ∀ k, b k x = b k y) : x = y := by
  by_contra hne
  let e := Fintype.equivFinOfCardEq hq
  let M : Matrix (Fin q) (Fin q) A := Matrix.of fun k j => b k (e.symm j)
  have hdet : M.det = 0 := by
    apply Matrix.det_zero_of_column_eq (i := e x) (j := e y)
    · exact fun h => hne (e.injective h)
    · intro k
      simp [M, hxy k]
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  apply hv
  apply hind
  intro z
  have hz := congrFun hMv (e z)
  simpa [M, Matrix.vecMul, dotProduct] using hz

end Count

section Sep

variable {i : N.Loc}

theorem sepElt (x : N.X i) : ∃ g ∈ N.T i, g x ≠ 0 ∧ ∀ y, y ≠ x → g y = 0 := by
  classical
  choose f hfT hf using fun y (h : x ≠ y) => N.T_sep i x y h
  let F : N.X i → (N.X i → N.O i) := fun y =>
    if h : x ≠ y then f y h - algebraMap (N.O i) (N.X i → N.O i) (f y h y) else 1
  refine ⟨∏ y, F y, Subalgebra.prod_mem _ (fun y _ => ?_), ?_, ?_⟩
  · by_cases h : x ≠ y
    · simp only [F, dif_pos h]
      exact Subalgebra.sub_mem _ (hfT y h) (Subalgebra.algebraMap_mem _ _)
    · simp only [F, dif_neg h]
      exact Subalgebra.one_mem _
  · rw [Finset.prod_apply]
    refine Finset.prod_ne_zero_iff.mpr (fun y _ => ?_)
    by_cases h : x ≠ y
    · simp only [F, dif_pos h, Pi.sub_apply]
      exact sub_ne_zero.mpr (hf y h)
    · simp only [F, dif_neg h, Pi.one_apply]
      exact one_ne_zero
  · intro y hy
    rw [Finset.prod_apply]
    refine Finset.prod_eq_zero (Finset.mem_univ y) ?_
    have h : x ≠ y := fun e => hy e.symm
    simp only [F, dif_pos h, Pi.sub_apply]
    exact sub_self _

variable {r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))}
  {ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))} {π : N.X i} {S : IdempotentChoiceData N i}

theorem descent_hyps (hG : GoodCongruenceObjects N r ρ π S) :
    ∃ b : Fin R.t.factorial → (S.X' → N.O i), (∀ k, b k ∈ S.T') ∧
      (∀ f' ∈ S.T', ∃ a : Fin R.t.factorial → (N.X i → N.O i), (∀ k, a k ∈ N.T i) ∧
        f' = ∑ k, (a k ∘ S.p) * b k) ∧
      (∀ x, ∀ a : Fin R.t.factorial → N.O i,
        (∀ x', S.p x' = x → ∑ k, a k * b k x' = 0) → a = 0) := by
  obtain ⟨-, -, -, -, -, -, -, ⟨-, -, -, ⟨b, hbT, hb⟩, -⟩, -⟩ := hG
  refine ⟨b, hbT, ?_, ?_⟩
  · intro f' hf'
    obtain ⟨cf, hcf, -⟩ := hb f' hf'
    exact ⟨fun k => (cf k : N.X i → N.O i), fun k => (cf k).2, hcf⟩
  · intro x a ha
    obtain ⟨g, hgT, hgx, hg0⟩ := sepElt N x
    have h1 : (0 : S.X' → N.O i) = ∑ k, ((fun x' =>
        ((⟨a k • g, Subalgebra.smul_mem _ hgT _⟩ : N.T i) : N.X i → N.O i) (S.p x')) :
          S.X' → N.O i) * b k := by
      funext x'
      simp only [Finset.sum_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      by_cases hx : S.p x' = x
      · have := ha x' hx
        calc (0 : N.O i) = g (S.p x') * ∑ k, a k * b k x' := by rw [this, mul_zero]
          _ = _ := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun k _ => by ring)
      · simp [hg0 _ hx]
    have h2 : (0 : S.X' → N.O i) = ∑ k, ((fun x' =>
        (((0 : Fin R.t.factorial → N.T i) k : N.T i) : N.X i → N.O i) (S.p x')) :
          S.X' → N.O i) * b k := by
      funext x'
      simp
    have h3 := (hb 0 (Subalgebra.zero_mem _)).unique h1 h2
    funext k
    have h4 : a k * g x = 0 := by
      have := congrArg (fun c : N.T i => (c : N.X i → N.O i) x) (congrFun h3 k)
      simpa using this
    exact (mul_eq_zero.mp h4).resolve_right hgx

theorem eigenspace_lemma (hG : GoodCongruenceObjects N r ρ π S) : VanishingLemma N π S := by
  obtain ⟨b, -, hspan, hind⟩ := descent_hyps N hG
  obtain ⟨-, -, -, -, -, -, -, -, -, ⟨hπ, -⟩, -⟩ := hG
  intro f hf hvan
  have h := Formalism.NG.descent (N.O i) (N.X i) S.X' (N.T i) S.T' (↑(N.Z i) : Set (N.X i)) S.p _ b hspan
    (fun x _ => hind x) f hf (fun x' hx' => hvan x' (by simpa using hx')) S.π'
  rw [hπ] at h
  refine (Ideal.span_le.mpr ?_) h
  rintro y ⟨c, hc, rfl⟩
  refine Ideal.mem_map_of_mem _ ?_
  change c ∈ RingHom.ker _
  rw [RingHom.mem_ker]
  change c ∈ RingHom.ker _ at hc
  rw [RingHom.mem_ker] at hc
  funext z
  exact congrFun hc ⟨z.1, by simpa using z.2⟩

end Sep

section Det

open Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.NG

variable (i : N.Loc) {X' : Type} (T' : Subalgebra (N.O i) (X' → N.O i)) (rep : X' → (GE N →* MatN N i))

def repF (Kf : Type) [CommRing Kf] [Algebra (N.O i) Kf] :
    GE N →* (X' → Matrix (Fin R.nV) (Fin R.nV) Kf) :=
  MonoidHom.pi fun x' => ((algebraMap (N.O i) Kf).mapMatrix.toMonoidHom).comp (rep x')

theorem repF_apply (Kf : Type) [CommRing Kf] [Algebra (N.O i) Kf] (g : GE N) (x' : X') :
    repF N i rep Kf g x' = (rep x' g).map (algebraMap (N.O i) Kf) := rfl

theorem map_self {A : Type} [CommRing A] {n : Type} (M : Matrix n n A) :
    M.map (algebraMap A A) = M := by
  ext i j
  simp

theorem charpolyRev_map {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n]
    (f : A →+* B) (M : Matrix n n A) : (M.map f).charpolyRev = M.charpolyRev.map f := by
  unfold Matrix.charpolyRev
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases hij : i = j <;> simp [hij, Matrix.one_apply]

theorem inSpan_tSpan (Kf : Type) [CommRing Kf] [Algebra (N.O i) Kf] {a : X' → MatN N i}
    (ha : InSpan N i T' rep a) :
    (fun x' => (a x').map (algebraMap (N.O i) Kf)) ∈ tSpan T' (repF N i rep Kf) := by
  classical
  obtain ⟨m, f, g, hf, rfl⟩ := ha
  refine ⟨Finset.univ.image g, fun γ => ∑ k with g k = γ, f k,
    fun γ => Subalgebra.sum_mem _ (fun k _ => hf k), ?_⟩
  funext x'
  have hL : ((∑ k, fun x' => f k x' • rep x' (g k)) x').map (algebraMap (N.O i) Kf) =
      ∑ k, algebraMap (N.O i) Kf (f k x') • repF N i rep Kf (g k) x' := by
    rw [Finset.sum_apply]
    change (algebraMap (N.O i) Kf).mapMatrix (∑ k, f k x' • rep x' (g k)) = _
    rw [map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [repF_apply]
    ext p q
    simp [Matrix.smul_apply]
  rw [hL, Finset.sum_apply,
    ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image g) (g := g)
      (fun k _ => Finset.mem_image_of_mem g (Finset.mem_univ k))]
  refine Finset.sum_congr rfl (fun γ _ => ?_)
  beta_reduce
  rw [Finset.sum_apply, map_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [(Finset.mem_filter.mp hk).2]

def spanSub : Submodule (N.O i) (X' → MatN N i) :=
  Submodule.span (N.O i) {F | ∃ f ∈ T', ∃ g : GE N, F = fun x' => f x' • rep x' g}

theorem inSpan_iff (a : X' → MatN N i) : InSpan N i T' rep a ↔ a ∈ spanSub N i T' rep := by
  constructor
  · rintro ⟨m, f, γ, hf, he⟩
    subst he
    exact Submodule.sum_mem _ fun k _ => Submodule.subset_span ⟨f k, hf k, γ k, rfl⟩
  · intro ha
    unfold spanSub at ha
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, hf, g, rfl⟩ := hx
      have h := Formalism.MainNotions.LargeLevelLemmas.Br.inSpan_of_fintype N T' rep (ι := Unit) (fun _ => f) (fun _ => g)
        (fun _ => hf)
      simpa using h
    | zero => exact (Formalism.MainNotions.LargeLevelLemmas.Br.spanAlg N T' rep).zero_mem
    | add x y _ _ hx hy => exact (Formalism.MainNotions.LargeLevelLemmas.Br.spanAlg N T' rep).add_mem hx hy
    | smul c x _ hx => exact (Formalism.MainNotions.LargeLevelLemmas.Br.spanAlg N T' rep).smul_mem hx c

def spanAlg : Subalgebra (N.O i) (X' → MatN N i) :=
  (spanSub N i T' rep).toSubalgebra
    (Submodule.subset_span ⟨1, Subalgebra.one_mem _, 1, by funext x'; simp⟩)
    (by
      intro x y hx hy
      have h := Submodule.mul_mem_mul hx hy
      rw [spanSub, Submodule.span_mul_span] at h
      refine Submodule.span_mono ?_ h
      rintro _ ⟨_, ⟨f, hf, g, rfl⟩, _, ⟨f', hf', g', rfl⟩, rfl⟩
      refine ⟨f * f', Subalgebra.mul_mem _ hf hf', g * g', ?_⟩
      funext x'
      change (f x' • rep x' g) * (f' x' • rep x' g') = (f x' * f' x') • rep x' (g * g')
      rw [smul_mul_smul_comm, map_mul])

def toKfun : (X' → MatN N i) →ₐ[N.O i] (X' → Matrix (Fin R.nV) (Fin R.nV) (KK N i)) :=
  ((Algebra.ofId (N.O i) (KK N i)).mapMatrix).compLeft X'

theorem span_lemma_of_charpoly
    (h : ∀ (g : GE N) (k : ℕ), (fun x' => ((rep x' g).charpolyRev).coeff k) ∈ T') :
    CharpolyCoeffsInSubalgebra N i T' rep := by
  constructor
  · intro m a ha d
    obtain ⟨t, ht, hx⟩ := det_poly_statement (N.O i) (N.O i) X' (GE N) (Fin R.nV) T'
      (repF N i rep (N.O i))
      (fun g k => ⟨_, h g k, fun x' => by
        beta_reduce
        rw [repF_apply, map_self]
        rfl⟩)
      m (fun k x' => (a k x').map (algebraMap (N.O i) (N.O i)))
      (fun k => inSpan_tSpan N i T' rep (N.O i) (ha k)) d
    have : (fun x' => MvPolynomial.coeff d (Matrix.det (∑ k,
        (MvPolynomial.X k : MvPolynomial (Fin m) (N.O i)) • (a k x').map MvPolynomial.C))) = t := by
      funext x'
      have := hx x'
      simp only [map_self] at this
      exact this.symm
    rw [this]
    exact ht
  · intro g Θ hΘ
    have hsub : LemmaDetSub.{0, 0, 0} := eta_determinant_comparison det_poly_statement blockDet
    let R'K : Subalgebra (N.O i) (X' → Matrix (Fin R.nV) (Fin R.nV) (KK N i)) :=
      (spanAlg N i T' rep).map (toKfun N i)
    let ΘK : Matrix (Fin g) (Fin g) R'K := fun p q =>
      ⟨toKfun N i (Θ p q), Subalgebra.mem_map.mpr ⟨Θ p q, (inSpan_iff N i T' rep _).mp (hΘ p q), rfl⟩⟩
    obtain ⟨f, hf, hx⟩ := hsub (N.O i) X' (GE N) T' (Fin R.nV) R'K (repF N i rep (KK N i))
      (fun γ k => ⟨_, h γ k, fun x' => by
        change _ = (Matrix.charpolyRev ((rep x' γ).map (algebraMap (N.O i) (KK N i)))).coeff k
        rw [charpolyRev_map, Polynomial.coeff_map]⟩)
      (by
        rintro _ ⟨a, ha, rfl⟩
        exact inSpan_tSpan N i T' rep (KK N i) ((inSpan_iff N i T' rep a).mpr ha))
      (Fin g) ΘK
    have : (fun x' => Matrix.det (Matrix.of fun (pa qb : Fin g × Fin R.nV) =>
        Θ pa.1 qb.1 x' pa.2 qb.2)) = f := by
      funext x'
      apply IsFractionRing.injective (N.O i) (KK N i)
      rw [hx x', RingHom.map_det]
      rfl
    rw [this]
    exact hf

end Det

section Cor

variable {i : N.Loc} (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))

theorem span_lemma_of_charpoly_coeffs
    (hG1 : ∀ (g : GE N) (k : ℕ), (fun x : N.X i => ((rO N i r x g).charpolyRev).coeff k) ∈ N.T i) :
    CharpolyCoeffsInSubalgebra N i (N.T i) (rO N i r) := span_lemma_of_charpoly N i (N.T i) (rO N i r) hG1

end Cor

section Rings

variable {i : N.Loc} {r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))}
  {ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))} {π : N.X i} {S : IdempotentChoiceData N i}

theorem inR'_of_inR (hT : ∀ f ∈ N.T i, (fun x' => f (S.p x')) ∈ S.T') {a : N.X i → MatN N i}
    (ha : InR N i r a) : InR' N r S (fun x' => a (S.p x')) := by
  obtain ⟨m, f, γ, hf, he⟩ := ha
  refine ⟨m, fun k x' => f k (S.p x'), γ, fun k => hT _ (hf k), ?_⟩
  subst he
  funext x'
  simp [Finset.sum_apply]

theorem exists_nonfixed_twisted_vector
    (hG6 : ∀ x : N.X i, (∃ u : Fin R.nV → KK N i, u ≠ 0 ∧ ∀ g,
      (mapM (toK N i) (rO N i r x) g).mulVec u =
        toK N i ((chiU N i 1 g : (N.O i)ˣ) : N.O i) • u) → x ∈ N.Z i)
    (x : N.X i) (hx : x ∉ N.Z i) (η : Fin R.nV → KK N i) (hη : η ≠ 0) :
    ∃ g : GE N, toK N i (((chiU N i 1 g)⁻¹ : (N.O i)ˣ) : N.O i) •
      (mapM (toK N i) (rO N i r x) g).mulVec η ≠ η := by
  by_contra hcon
  push_neg at hcon
  apply hx
  apply hG6 x
  refine ⟨η, hη, fun g => ?_⟩
  have h1 := hcon g
  calc (mapM (toK N i) (rO N i r x) g).mulVec η
      = (toK N i ((chiU N i 1 g : (N.O i)ˣ) : N.O i) *
          toK N i (((chiU N i 1 g)⁻¹ : (N.O i)ˣ) : N.O i)) •
          (mapM (toK N i) (rO N i r x) g).mulVec η := by
        rw [← map_mul, Units.mul_inv, map_one, one_smul]
    _ = toK N i ((chiU N i 1 g : (N.O i)ˣ) : N.O i) • η := by
        rw [mul_smul, h1]

theorem psiChi_eB (hG : GoodCongruenceObjects N r ρ π S) (c : Fin R.t) :
    S.ψχ c (fun x' => S.eB (S.p x')) = 1 := by
  obtain ⟨⟨heB, -⟩, -, hact, -, -, -, ⟨-, heX, -, hX0π⟩, ⟨hT, -⟩, -, ⟨hπ, -⟩, -⟩ := hG
  have hB := inR'_of_inR N (r := r) hT heB
  have hw := hX0π (S.e.symm ((0 : Fin R.r → KK N i), Pi.single c (1 : KK N i)))
  have h1 := hact _ hB (((S.X0 π).map (toK N i)).mulVec
    (S.e.symm ((0 : Fin R.r → KK N i), Pi.single c (1 : KK N i))))
  beta_reduce at h1
  have hXe : S.eB π * S.X0 π = S.X0 π := congrFun heX π
  rw [hπ, Matrix.mulVec_mulVec, ← Matrix.map_mul, hXe, hw] at h1
  have h3 := congrFun (congrArg Prod.snd h1) c
  simp only [LinearEquiv.apply_symm_apply, Pi.single_eq_same, mul_one] at h3
  have hne : toK N i ((chiU N i ((c : ℕ) + 1) S.g0 : (N.O i)ˣ) : N.O i) ≠ 0 :=
    ((Units.isUnit _).map (toK N i)).ne_zero
  apply IsFractionRing.injective (N.O i) (KK N i)
  apply mul_right_cancel₀ hne
  rw [map_one, one_mul]
  exact h3.symm

theorem T'_eq_of_rr (hG : GoodCongruenceObjects N r ρ π S) {x1 x2 : S.X'} (hp : S.p x1 = S.p x2)
    (hrr : ∀ c ∈ Finset.Icc 1 R.t, S.rr c x1 = S.rr c x2) : ∀ f ∈ S.T', f x1 = f x2 := by
  obtain ⟨-, -, -, -, -, -, -, ⟨-, -, hadj, -⟩, -⟩ := hG
  intro f hf
  rw [hadj] at hf
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    rcases hf with ⟨f0, -, rfl⟩ | ⟨c, hc, rfl⟩
    · simp only [hp]
    · exact hrr c (by simpa using hc)
  | algebraMap c => rfl
  | add f g _ _ hf hg => simp only [Pi.add_apply, hf, hg]
  | mul f g _ _ hf hg => simp only [Pi.mul_apply, hf, hg]

end Rings

end Formalism.MainNotions.N.Inst

namespace Formalism.MainNotions.LargeLevelLemmas

open Formalism.BasicNotions Formalism.MainNotions.N

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem eigenspace_lemma_clause : SpanQuotientLemma i r ρ π := by
  intro _ S hG
  exact Formalism.MainNotions.N.Inst.eigenspace_lemma D.nd hG

theorem span_lemma_clause (h : Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG1 i r) : CharpolyCoeffsLemmaFamily i r := Formalism.MainNotions.N.Inst.span_lemma_of_charpoly_coeffs D.nd r h

end Formalism.MainNotions.LargeLevelLemmas
