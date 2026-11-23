import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal

theorem taylor_alg {K A B : Type} [CommRing K] [CommRing A] [Algebra K A] [CommRing B] [Algebra K B] {d : ℕ}
    (t : Fin d → A)
    (hf : (MvPolynomial.eval₂Hom (algebraMap K A) t : MvPolynomial (Fin d) K →+* A).FormallyUnramified)
    (D : Fin d → Derivation K A A) (hD : ∀ k j, D k (t j) = if k = j then 1 else 0)
    (N P : Ideal B) (hNP : N * N ≤ P) (a b : A →ₐ[K] B) (hab : ∀ x, a x - b x ∈ N) (x : A) :
    a x - b x - ∑ k, (a (t k) - b (t k)) * b (D k x) ∈ P := by
  classical
  let f : MvPolynomial (Fin d) K →+* A := MvPolynomial.eval₂Hom (algebraMap K A) t
  let π : B →+* B ⧸ P := Ideal.Quotient.mk P
  let e : Fin d → B := fun k => a (t k) - b (t k)
  have he : ∀ k, e k ∈ N := fun k => hab _
  let S : A → B := fun x => ∑ k, e k * b (D k x)
  have hS : ∀ x, S x ∈ N := fun x => Ideal.sum_mem _ fun k _ => N.mul_mem_right _ (he k)
  have hSadd : ∀ x y, S (x + y) = S x + S y := fun x y => by
    simp only [S, map_add, mul_add, Finset.sum_add_distrib]
  have hSmul : ∀ x y, S (x * y) = b x * S y + b y * S x := fun x y => by
    simp only [S, Derivation.leibniz, smul_eq_mul, map_add, map_mul, mul_add, Finset.sum_add_distrib,
      Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun k _ => by ring
  have hSone : S 1 = 0 := by simp [S]
  have hSzero : S 0 = 0 := by simp [S]
  let c : A →+* B ⧸ P :=
    { toFun := fun x => π (b x + S x)
      map_one' := by simp [hSone]
      map_zero' := by simp [hSzero]
      map_add' := fun x y => by
        rw [hSadd, map_add b, ← map_add π]
        congr 1
        ring
      map_mul' := fun x y => by
        rw [← map_mul π]
        refine Ideal.Quotient.eq.2 ?_
        have h := hNP (Ideal.mul_mem_mul (hS x) (hS y))
        have e2 : b (x * y) + S (x * y) - (b x + S x) * (b y + S y) = -(S x * S y) := by
          rw [hSmul, map_mul]
          ring
        rw [e2]
        exact P.neg_mem h }
  have hc : ∀ x, c x = π (b x + S x) := fun _ => rfl
  have hcf : c.comp f = π.comp ((a : A →+* B).comp f) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) fun i => ?_
    · simp only [RingHom.comp_apply, f, MvPolynomial.eval₂Hom_C, hc]
      have : S (algebraMap K A r) = 0 := by simp [S]
      simp [this]
    · simp only [RingHom.comp_apply, f, MvPolynomial.eval₂Hom_X', hc]
      have : S (t i) = e i := by simp [S, hD, e]
      rw [this]
      simp [e]
  letI algA : Algebra (MvPolynomial (Fin d) K) A := f.toAlgebra
  letI algC : Algebra (MvPolynomial (Fin d) K) (B ⧸ P) := (π.comp ((a : A →+* B).comp f)).toAlgebra
  haveI : Algebra.FormallyUnramified (MvPolynomial (Fin d) K) A := hf
  let g₁ : A →ₐ[MvPolynomial (Fin d) K] B ⧸ P :=
    { toRingHom := π.comp (a : A →+* B), commutes' := fun _ => rfl }
  let g₂ : A →ₐ[MvPolynomial (Fin d) K] B ⧸ P :=
    { toRingHom := c, commutes' := fun p => RingHom.congr_fun hcf p }
  have hnil : IsNilpotent (N.map π) := by
    refine ⟨2, ?_⟩
    rw [pow_two, ← Ideal.map_mul, Ideal.zero_eq_bot]
    refine le_bot_iff.1 ((Ideal.map_mono hNP).trans ?_)
    rw [Ideal.map_quotient_self]
  have hg : g₁ = g₂ := by
    refine Algebra.FormallyUnramified.ext (N.map π) hnil fun y => ?_
    refine Ideal.Quotient.eq.2 ?_
    have : g₁ y - g₂ y = π (a y - (b y + S y)) := by
      rw [map_sub]
      rfl
    rw [this]
    refine Ideal.mem_map_of_mem π ?_
    have e3 : a y - (b y + S y) = (a y - b y) - S y := by ring
    rw [e3]
    exact N.sub_mem (hab y) (hS y)
  have h1 : π (a x) = π (b x + S x) := DFunLike.congr_fun hg x
  have h2 := Ideal.Quotient.eq.1 h1
  have e4 : a x - (b x + S x) = a x - b x - ∑ k, (a (t k) - b (t k)) * b (D k x) := by
    simp only [S, e]
    ring
  rwa [e4] at h2

theorem taylor_loc : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens} {d : ℕ} (c : Coord q W d) (s : ℕ) (E : Frame (sP (KS q s {W})) d)
    (ε : Γ(X, W) ≃+* (sP (KS q s {W})).A.obj E.D), IsLoc q s c.t E ε →
    letI := (strV q W).toAlgebra
    ∀ (D : Fin d → Derivation K Γ(X, W) Γ(X, W)), (∀ k j, D k (c.t j) = if k = j then 1 else 0) →
    Taylor (sFil (KS q s {W})) E (fun k x => ε (D k (ε.symm x))) := by
  intro K _ _ X q W d c s E ε h
  letI := (strV q W).toAlgebra
  intro D hD
  obtain ⟨-, -, h3, h4, h5⟩ := h
  intro T u v x
  obtain ⟨y, rfl⟩ := ε.surjective x
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {W})
  have hcomm : ∀ (w : E.D ⟶ T) (r : K), ((sP (KS q s {W})).A.map w).hom (ε (algebraMap K Γ(X, W) r)) =
      algebraMap K ((sP (KS q s {W})).A.obj T) r := fun w r => by
    have e : ε (algebraMap K Γ(X, W) r) = algebraMap K _ r := h3 r
    rw [e]
    exact AlgHom.commutes _ r
  let ev' : (E.D ⟶ T) → (Γ(X, W) →ₐ[K] (sP (KS q s {W})).A.obj T) := fun w =>
    { toRingHom := RingHom.comp (AlgHom.toRingHom ((sP (KS q s {W})).A.map w).hom) ε.toRingHom
      commutes' := hcomm w }
  have hNP : (sFil (KS q s {W}) 1).S T * (sFil (KS q s {W}) 1).S T ≤ (sFil (KS q s {W}) 2).S T :=
    Ideal.mul_le.2 fun a ha b hb => hF.mul 1 1 T ha hb
  have hab : ∀ g, ev' u g - ev' v g ∈ (sFil (KS q s {W}) 1).S T := fun g => by
    rw [hF.one T]
    have e := (h4 T u g).symm.trans (h4 T v g)
    exact Ideal.Quotient.eq.1 e
  have hf : (MvPolynomial.eval₂Hom (algebraMap K Γ(X, W)) c.t : MvPolynomial (Fin d) K →+* Γ(X, W)).FormallyUnramified :=
    by
      have he := c.etale
      letI := (MvPolynomial.eval₂Hom (strV q W) c.t : MvPolynomial (Fin d) K →+* Γ(X, W)).toAlgebra
      haveI : Algebra.Etale (MvPolynomial (Fin d) K) Γ(X, W) := he
      exact (inferInstance : Algebra.FormallyUnramified (MvPolynomial (Fin d) K) Γ(X, W))
  have key := taylor_alg c.t hf D hD _ _ hNP (ev' u) (ev' v) hab y
  have e : ∀ k, E.τ k v u = ev' u (c.t k) - ev' v (c.t k) := fun k => h5 k v u
  simp only [ε.symm_apply_apply, e]
  exact key

end GlobalTheory.CompanionTheory.ConeLocal
