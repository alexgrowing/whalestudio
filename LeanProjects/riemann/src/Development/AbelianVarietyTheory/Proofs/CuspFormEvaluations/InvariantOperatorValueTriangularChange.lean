import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndBC
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.InvariantDerivationsCommuteFormalConnection
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.WeightAddLeOfMemSupportDividedContraction

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RowTriangular

section Poly

open MvPolynomial

variable {Ty : Type} {r : Ty → ℕ} {n : ℕ} {k T : Type} [Field k] [CommRing T]

theorem eval₂_shift [Infinite k] (φ : k →+* T) {P : MvPolynomial (Letter Ty r n) k} (hP : RowInv r n k P)
    (σ : Ty) (i i' : Fin (r σ)) (hi : i' < i) (t : T) (y y' : Letter Ty r n → T)
    (h₁ : ∀ b, y' ⟨σ, i, b⟩ = y ⟨σ, i, b⟩ + t * y ⟨σ, i', b⟩)
    (h₂ : ∀ ℓ, (¬ ∃ b, ℓ = ⟨σ, i, b⟩) → y' ℓ = y ℓ) :
    eval₂Hom φ y' P = eval₂Hom φ y P := by
  classical
  let _ : Algebra k T := φ.toAlgebra
  let G : Letter Ty r n → MvPolynomial (Option (Letter Ty r n)) k := fun ℓ =>
    if ∃ b, ℓ = ⟨σ, (i, b)⟩ then X (some ℓ) + X none * X (some ⟨σ, (i', ℓ.snd.2)⟩) else X (some ℓ)
  have hQ : aeval G P = rename some P := by
    apply MvPolynomial.funext
    intro x
    have h1 := congrArg (aeval (x ∘ some)) (hP σ i i' hi (x none))
    unfold rowShift at h1
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval] at h1
    change aeval x (aeval G P) = aeval x (rename some P)
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval, aeval_rename, ← h1]
    congr 2
    funext ℓ
    by_cases hℓ : ∃ b, ℓ = ⟨σ, (i, b)⟩
    · simp [G, hℓ]
    · simp [G, hℓ]
  let g : Option (Letter Ty r n) → T := fun o => o.elim t y
  have e1 : (fun ℓ => aeval g (G ℓ)) = y' := by
    funext ℓ
    by_cases hℓ : ∃ b, ℓ = ⟨σ, (i, b)⟩
    · obtain ⟨b, rfl⟩ := hℓ
      simp only [G, if_pos (show ∃ b', (⟨σ, (i, b)⟩ : Letter Ty r n) = ⟨σ, (i, b')⟩ from ⟨b, rfl⟩)]
      simp [g, h₁]
    · simp only [G, if_neg hℓ]
      simp [g, h₂ ℓ hℓ]
  have e2 := congrArg (aeval g) hQ
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval, aeval_rename, e1] at e2
  exact e2

private theorem eval₂Hom_unipotent_substitution_eq [Infinite k] (φ : k →+* T) {P : MvPolynomial (Letter Ty r n) k}
    (hP : RowInv r n k P) (σ : Ty) (i : Fin (r σ))
    [DecidablePred fun ℓ : Letter Ty r n => ∃ b, ℓ = ⟨σ, (i, b)⟩] (N : Fin (r σ) → T) (hN : ∀ j, i ≤ j → N j = 0)
    (y : Letter Ty r n → T) [DecidableEq (Fin (r σ))] (S : Finset (Fin (r σ))) :
    eval₂Hom φ (fun ℓ : Letter Ty r n =>
      if ∃ b, ℓ = ⟨σ, (i, b)⟩ then y ℓ + ∑ j ∈ S, N j * y ⟨σ, (j, ℓ.2.2)⟩ else y ℓ) P = eval₂Hom φ y P := by
  refine Finset.induction_on S ?_ ?_
  · simp
  · intro j S hj ih
    rw [← ih]
    by_cases hji : j < i
    · refine eval₂_shift φ hP σ i j hji (N j) _ _ ?_ ?_
      · intro b
        have hb : ∃ b', (⟨σ, (i, b)⟩ : Letter Ty r n) = ⟨σ, (i, b')⟩ := ⟨b, rfl⟩
        have hb' : ¬ ∃ b', (⟨σ, (j, b)⟩ : Letter Ty r n) = ⟨σ, (i, b')⟩ := by
          rintro ⟨b', h⟩
          simp only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and] at h
          exact hji.ne h.1
        simp only [if_pos hb, if_neg hb', Finset.sum_insert hj]
        ring
      · intro ℓ hℓ
        simp only [if_neg hℓ]
    · have h0 : N j = 0 := hN j (not_lt.1 hji)
      refine congrArg (fun g => eval₂Hom φ g P) (funext fun ℓ => ?_)
      split_ifs <;> simp [Finset.sum_insert hj, h0]

private theorem eval₂Hom_unipotent_block_substitution_eq [Infinite k] (φ : k →+* T) {P : MvPolynomial (Letter Ty r n) k}
    (hP : RowInv r n k P) (N : ∀ σ, Fin (r σ) → Fin (r σ) → T) (hN : ∀ σ i j, i ≤ j → N σ i j = 0)
    [DecidableEq (Σ σ : Ty, Fin (r σ))] (R : Finset (Σ σ : Ty, Fin (r σ))) :
    ∀ y : Letter Ty r n → T, eval₂Hom φ (fun ℓ : Letter Ty r n => y ℓ +
      if (⟨ℓ.1, ℓ.2.1⟩ : Σ σ : Ty, Fin (r σ)) ∈ R then ∑ j, N ℓ.1 ℓ.2.1 j * y ⟨ℓ.1, (j, ℓ.2.2)⟩ else 0) P =
      eval₂Hom φ y P := by
  refine Finset.induction_on_max_value (fun p : (Σ σ : Ty, Fin (r σ)) => (p.2 : ℕ)) R ?_ ?_
  · intro y
    simp
  · intro p R hp hmax ih y
    obtain ⟨σ, i⟩ := p
    classical
    have hA := eval₂Hom_unipotent_substitution_eq φ hP σ i (N σ i) (hN σ i) y Finset.univ
    refine Eq.trans ?_ ((ih _).trans hA)
    refine congrArg (fun g => eval₂Hom φ g P) (funext fun ℓ => ?_)
    rcases ℓ with ⟨σ', i', b⟩
    by_cases hrow : (⟨σ', i'⟩ : Σ σ : Ty, Fin (r σ)) = ⟨σ, i⟩
    · cases hrow
      dsimp only
      rw [if_pos (Finset.mem_insert_self _ _), if_neg hp,
        if_pos (show ∃ b', (⟨σ, (i, b)⟩ : Letter Ty r n) = ⟨σ, (i, b')⟩ from ⟨b, rfl⟩), add_zero]
    · have hne : ∀ j : Fin (r σ'), (⟨σ', j⟩ : Σ σ : Ty, Fin (r σ)) ≠ ⟨σ, i⟩ →
          ¬ ∃ b', (⟨σ', (j, b)⟩ : Letter Ty r n) = ⟨σ, (i, b')⟩ := by
        rintro j hj ⟨b', h⟩
        apply hj
        cases h
        rfl
      dsimp only
      rw [if_neg (hne i' hrow)]
      by_cases hR : (⟨σ', i'⟩ : Σ σ : Ty, Fin (r σ)) ∈ R
      · rw [if_pos (Finset.mem_insert_of_mem hR), if_pos hR]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : i' ≤ j
        · rw [hN σ' i' j hj, zero_mul, zero_mul]
        · rw [if_neg (hne j ?_)]
          intro hji
          cases hji
          exact hj (Fin.le_iff_val_le_val.2 (hmax _ hR))
      · have hI : (⟨σ', i'⟩ : Σ σ : Ty, Fin (r σ)) ∉ insert ⟨σ, i⟩ R := by
          rw [Finset.mem_insert]
          rintro (h | h)
          exacts [hrow h, hR h]
        rw [if_neg hI, if_neg hR]

theorem eval₂_unip [Infinite k] [Fintype Ty] (φ : k →+* T) {P : MvPolynomial (Letter Ty r n) k}
    (hP : RowInv r n k P) (N : ∀ σ, Fin (r σ) → Fin (r σ) → T) (hN : ∀ σ i j, i ≤ j → N σ i j = 0)
    (y : Letter Ty r n → T) :
    eval₂Hom φ (fun ℓ : Letter Ty r n => y ℓ + ∑ j, N ℓ.1 ℓ.2.1 j * y ⟨ℓ.1, j, ℓ.2.2⟩) P = eval₂Hom φ y P := by
  classical
  have h := eval₂Hom_unipotent_block_substitution_eq φ hP N hN Finset.univ y
  simpa only [Finset.mem_univ, ↓reduceIte] using h

theorem eval₂_diag [Fintype Ty] (φ : k →+* T) {a : Ty → ℕ → ℕ} {P : MvPolynomial (Letter Ty r n) k}
    (hP : RowDeg r n k a P) (c : ∀ σ, Fin (r σ) → T) (y : Letter Ty r n → T) :
    eval₂Hom φ (fun ℓ : Letter Ty r n => c ℓ.1 ℓ.2.1 * y ℓ) P =
      (∏ p : (Σ σ : Ty, Fin (r σ)), c p.1 p.2 ^ a p.1 p.2) * eval₂Hom φ y P := by
  classical
  simp only [coe_eval₂Hom, eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [mul_pow, Finset.prod_mul_distrib]
  have hc : ∏ ℓ : Letter Ty r n, c ℓ.1 ℓ.2.1 ^ m ℓ = ∏ p : (Σ σ : Ty, Fin (r σ)), c p.1 p.2 ^ a p.1 p.2 := by
    rw [Fintype.prod_sigma, Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun σ _ => ?_
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    dsimp only
    rw [Finset.prod_pow_eq_pow_sum, hP m hm σ i]
  rw [hc]
  ring

theorem eval₂_triangular [Infinite k] [Fintype Ty] (φ : k →+* T) {a : Ty → ℕ → ℕ}
    {P : MvPolynomial (Letter Ty r n) k} (hI : RowInv r n k P) (hD : RowDeg r n k a P)
    (c : ∀ σ, Fin (r σ) → Fin (r σ) → T) (hc : ∀ σ i j, i < j → c σ i j = 0) (hu : ∀ σ i, IsUnit (c σ i i))
    (y : Letter Ty r n → T) :
    eval₂Hom φ (fun ℓ : Letter Ty r n => ∑ j, c ℓ.1 ℓ.2.1 j * y ⟨ℓ.1, j, ℓ.2.2⟩) P =
      (∏ p : (Σ σ : Ty, Fin (r σ)), c p.1 p.2 p.2 ^ a p.1 p.2) * eval₂Hom φ y P := by
  classical
  let N : ∀ σ, Fin (r σ) → Fin (r σ) → T := fun σ i j => if j < i then ↑(hu σ i).unit⁻¹ * c σ i j else 0
  have hN : ∀ σ i j, i ≤ j → N σ i j = 0 := fun σ i j h => by simp [N, not_lt.2 h]
  have hfun : (fun ℓ : Letter Ty r n => ∑ j, c ℓ.1 ℓ.2.1 j * y ⟨ℓ.1, j, ℓ.2.2⟩) =
      fun ℓ => c ℓ.1 ℓ.2.1 ℓ.2.1 * (y ℓ + ∑ j, N ℓ.1 ℓ.2.1 j * y ⟨ℓ.1, j, ℓ.2.2⟩) := by
    funext ℓ
    rcases ℓ with ⟨σ, i, b⟩
    have e : ∀ j, c σ i j * y ⟨σ, j, b⟩ =
        (if j = i then c σ i i * y ⟨σ, i, b⟩ else 0) + c σ i i * (N σ i j * y ⟨σ, j, b⟩) := by
      intro j
      rcases lt_trichotomy j i with h | h | h
      · simp only [N, if_pos h, if_neg h.ne, zero_add]
        rw [← _root_.mul_assoc, ← _root_.mul_assoc, (hu σ i).mul_val_inv, _root_.one_mul]
      · subst h
        simp [N]
      · simp [N, h.ne', not_lt.2 h.le, hc σ i j h]
    dsimp only
    rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_add_distrib, Finset.sum_ite_eq',
      if_pos (Finset.mem_univ _), mul_add, Finset.mul_sum]
  have h1 := eval₂_diag φ hD (fun σ i => c σ i i) (fun ℓ => y ℓ + ∑ j, N ℓ.1 ℓ.2.1 j * y ⟨ℓ.1, j, ℓ.2.2⟩)
  have h2 := eval₂_unip φ hI N hN y
  rw [hfun]
  exact h1.trans (by rw [h2])

end Poly

section Op

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open scoped TensorProduct

variable {S : Type} [CommRing S] {d : ℕ}

def dEnd (F : Fin d → PS S 2 d) (v : Fin d → S) : Module.End S (PS S 1 d) := (GE.dofD F v).toLinearMap

theorem dEnd_apply (F : Fin d → PS S 2 d) (v : Fin d → S) (g : PS S 1 d) : dEnd F v g = Dof F v g := by
  exact GE.dofD_apply F v g

theorem dEnd_comb (F : Fin d → PS S 2 d) {κ : Type} [Fintype κ] (c : κ → S) (w : κ → Fin d → S) (v : Fin d → S)
    (hv : ∀ e, v e = ∑ j, c j * w j e) : dEnd F v = ∑ j, c j • dEnd F (w j) := by
  refine LinearMap.ext fun g => ?_
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, dEnd_apply, Dof, hv, map_sum, map_mul, Finset.sum_mul,
    Finset.smul_sum, MvPowerSeries.smul_eq_C_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem dmon_eq {A : Type} [CommRing A] [Algebra S A] (F : Fin d → PS S 2 d) (Ψ : A →ₐ[S] Module.End S (PS S 1 d))
    {I : Type} [Fintype I] (u : I → Fin d → S) (x : I → A) (hx : ∀ l, Ψ (x l) = dEnd F (u l)) (m : I →₀ ℕ)
    (g : PS S 1 d) : DmonOf F u m g = Ψ (∏ l, x l ^ m l) g := by
  classical
  have hD : ∀ v, ⇑(dEnd F v) = Dof F v := fun v => funext (dEnd_apply F v)
  have key : ∀ L : List I,
      L.foldr (fun l h => (Dof F (u l))^[m l] h) g = Ψ ((L.map fun l => x l ^ m l).prod) g := by
    intro L
    induction L with
    | nil => simp
    | cons l L ih =>
      rw [List.foldr_cons, List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, ← ih, map_pow,
        hx, Module.End.pow_apply, hD]
  rw [DmonOf, key, Finset.prod_map_toList]

theorem dpoly_monomial (F : Fin d → PS S 2 d) {I : Type} [Fintype I] (u : I → Fin d → S) (m : I →₀ ℕ)
    (g : PS S 1 d) : DpolyOf F u (MvPolynomial.monomial m 1) g = DmonOf F u m g := by
  classical
  by_cases h : (1 : S) = 0
  · have : Subsingleton S := subsingleton_of_zero_eq_one h.symm
    exact MvPowerSeries.ext fun _ => Subsingleton.elim _ _
  · simp [DpolyOf, MvPolynomial.support_monomial, h]

def prodForm {A : Type} [CommRing A] [Algebra S A] {n : ℕ} (lam : Fin n → A →ₗ[S] S) :
    (⨂[S] _ : Fin n, A) →ₗ[S] S :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra S (Fin n) S).compLinearMap lam)

theorem prodForm_prod {A : Type} [CommRing A] [Algebra S A] {n : ℕ} (lam : Fin n → A →ₗ[S] S) (x : Fin n → A) :
    prodForm lam (∏ b, PiTensorProduct.singleAlgHom (R := S) (A := fun _ : Fin n => A) b (x b)) = ∏ b, lam b (x b) := by
  have e : (∏ b, PiTensorProduct.singleAlgHom (R := S) (A := fun _ : Fin n => A) b (x b)) =
      PiTensorProduct.tprod S x := by
    simp only [PiTensorProduct.singleAlgHom_apply, MonoidHom.mulSingle_apply]
    rw [← PiTensorProduct.tprod_prod, Finset.univ_prod_mulSingle]
  rw [e]
  simp [prodForm]

end Op

end GlobalTheory.RowTriangular

namespace GlobalTheory

open RowTriangular ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ in
open scoped TensorProduct in

theorem nabVal_triangular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) [StarRing (𝓞 E)] (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (d : ℕ) (B : Germ.FB S d (𝓞 E)) (hg : Germ.PS S 2 d), B.IsCanonGauge S hg → ∀ (k n : ℕ) (f : Fin n → MvPowerSeries (Fin 1 × Fin d) S) (uvec uvec' : Lt1 Dw → Fin d → S) (cf : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Fin (Dw.mult τ) → S), (∀ τ i j, i < j → cf τ i j = 0) → (∀ τ i e, uvec' ⟨τ, i⟩ e = ∑ j, cf τ i j * uvec ⟨τ, j⟩ e) → (∀ τ i, IsUnit (cf τ i i)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, B.nabVal S hg H.w0 k (f b) uvec' (MvPolynomial.monomial (colOf m b) 1) = (∏ ℓ : Lt1 Dw, cf ℓ.1 ℓ.2 ℓ.2 ^ a (ℓ.1, ℓ.2)) * ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, B.nabVal S hg H.w0 k (f b) uvec (MvPolynomial.monomial (colOf m b) 1) := by
  classical
  intro E _ _ _ H Dw l c _ S _ _ _ d B hg _ k n f uvec uvec' cf hcf huv hu a P hP
  unfold HHa at hP
  obtain ⟨-, hI, hD⟩ := hP
  have t4 : B.FK S = B.G.F := by
    funext i
    simp [FB.FK, FGLaw.mapF]
  have hcomm : ∀ u v : Fin d → S, dEnd (B.FK S) u * dEnd (B.FK S) v = dEnd (B.FK S) v * dEnd (B.FK S) u := by
    intro u v
    refine LinearMap.ext fun g => ?_
    simp only [Module.End.mul_apply, dEnd_apply]
    rw [t4]
    exact FormalConnection.dof_comm_law B.G u v g
  let s : Set (Module.End S (PS S 1 d)) := Set.range fun e : Fin d => dEnd (B.FK S) (Pi.single e 1)
  have hs : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x := by
    rintro _ ⟨e, rfl⟩ _ ⟨e', rfl⟩
    exact hcomm _ _
  letI : CommRing (Algebra.adjoin S s) := Algebra.adjoinCommRingOfComm S hs
  have hmem : ∀ v : Fin d → S, dEnd (B.FK S) v ∈ Algebra.adjoin S s := by
    intro v
    rw [dEnd_comb (B.FK S) (fun e => v e) (fun e => Pi.single e 1) v (fun e' => by simp [Pi.single_apply])]
    exact Subalgebra.sum_mem _ fun e _ => Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range_self e)) _
  obtain ⟨G, hG⟩ : ∃ G : Fin n → PS S 1 d, ∀ (b : Fin n) (u : Lt1 Dw → Fin d → S) (Q : MvPolynomial (Lt1 Dw) S),
      B.nabVal S hg H.w0 k (f b) u Q = MvPowerSeries.constantCoeff (DpolyOf (B.FK S) u Q (G b)) :=
    ⟨_, fun b u Q => rfl⟩
  let lam : Fin n → Algebra.adjoin S s →ₗ[S] S := fun b =>
    { toFun := fun z => MvPowerSeries.constantCoeff ((z : Module.End S (PS S 1 d)) (G b))
      map_add' := fun z z' => by simp
      map_smul' := fun r z => by simp [MvPowerSeries.smul_eq_C_mul] }
  let φ : c.F →+* (⨂[S] _ : Fin n, Algebra.adjoin S s) :=
    (algebraMap S (⨂[S] _ : Fin n, Algebra.adjoin S s)).comp (algebraMap c.F S)
  have hpull : ∀ (r : S) (t : ⨂[S] _ : Fin n, Algebra.adjoin S s),
      prodForm lam (algebraMap S _ r * t) = r * prodForm lam t := by
    intro r t
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have hval : ∀ (U : Lt1 Dw → Fin d → S) (X : Lt1 Dw → Algebra.adjoin S s),
      (∀ l, (Algebra.adjoin S s).val (X l) = dEnd (B.FK S) (U l)) →
      ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) *
          ∏ b, B.nabVal S hg H.w0 k (f b) U (MvPolynomial.monomial (colOf m b) 1) =
        prodForm lam (MvPolynomial.eval₂Hom φ (fun ℓ : LtN Dw n =>
          PiTensorProduct.singleAlgHom (R := S) (A := fun _ : Fin n => Algebra.adjoin S s) ℓ.2.2
            (X ⟨ℓ.1, ℓ.2.1⟩)) P) := by
    intro U X hX
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq', map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [show φ (P.coeff m) = algebraMap S _ (algebraMap c.F S (P.coeff m)) from rfl, hpull]
    congr 1
    have e1 : ∀ b, B.nabVal S hg H.w0 k (f b) U (MvPolynomial.monomial (colOf m b) 1) =
        lam b (∏ l, X l ^ (colOf m b) l) := by
      intro b
      rw [hG, dpoly_monomial, dmon_eq (B.FK S) (Algebra.adjoin S s).val U X hX]
      rfl
    simp only [e1]
    rw [← prodForm_prod]
    congr 1
    simp only [map_prod, map_pow]
    rw [Finset.prod_comm, Fintype.prod_sigma, Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun b _ => ?_
    simp [colOf]
  let X : Lt1 Dw → Algebra.adjoin S s := fun l => ⟨dEnd (B.FK S) (uvec l), hmem _⟩
  let X' : Lt1 Dw → Algebra.adjoin S s := fun l => ⟨dEnd (B.FK S) (uvec' l), hmem _⟩
  have hx' : ∀ τ i, X' ⟨τ, i⟩ = ∑ j, cf τ i j • X ⟨τ, j⟩ := by
    intro τ i
    apply Subtype.val_injective
    change dEnd (B.FK S) (uvec' ⟨τ, i⟩) = (Algebra.adjoin S s).val (∑ j, cf τ i j • X ⟨τ, j⟩)
    rw [map_sum]
    simp only [map_smul]
    exact dEnd_comb (B.FK S) (cf τ i) (fun j => uvec ⟨τ, j⟩) _ (huv τ i)
  rw [hval uvec' X' (fun l => rfl), hval uvec X (fun l => rfl)]
  have hY : (fun ℓ : LtN Dw n => PiTensorProduct.singleAlgHom (R := S)
        (A := fun _ : Fin n => Algebra.adjoin S s) ℓ.2.2 (X' ⟨ℓ.1, ℓ.2.1⟩)) =
      fun ℓ => ∑ j, algebraMap S (⨂[S] _ : Fin n, Algebra.adjoin S s) (cf ℓ.1 ℓ.2.1 j) *
        PiTensorProduct.singleAlgHom (R := S) (A := fun _ : Fin n => Algebra.adjoin S s) ℓ.2.2 (X ⟨ℓ.1, j⟩) := by
    funext ℓ
    rw [hx', map_sum]
    simp only [map_smul]
    simp only [Algebra.smul_def]
  have h3 := eval₂_triangular φ hI hD (fun τ i j => algebraMap S (⨂[S] _ : Fin n, Algebra.adjoin S s) (cf τ i j))
    (fun τ i j h => by simp [hcf τ i j h]) (fun τ i => (hu τ i).map _)
    (fun ℓ : LtN Dw n => PiTensorProduct.singleAlgHom (R := S)
        (A := fun _ : Fin n => Algebra.adjoin S s) ℓ.2.2 (X ⟨ℓ.1, ℓ.2.1⟩))
  rw [hY]
  refine (congrArg (prodForm lam) h3).trans ?_
  rw [← hpull]
  congr 2
  simp [map_prod, map_pow]

end GlobalTheory
