import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacGlueIndicator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneTransformSymplectic
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneCo

noncomputable section

namespace GlobalTheory.ThK.PlaneCo

section Gen

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S) {α β : Type} [Fintype α] [Fintype β]

theorem hTens_smul_left' (JA : Matrix α α S) (JB : Matrix β β S) (t : S) (x y : Matrix α β S) :
    hTens c JA JB (t • x) y = t * hTens c JA JB x y := by
  simp only [hTens, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem hTens_smul_right' (JA : Matrix α α S) (JB : Matrix β β S) (t : S) (x y : Matrix α β S) :
    hTens c JA JB x (t • y) = c t * hTens c JA JB x y := by
  simp only [hTens, Matrix.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem hTens_add_left' (JA : Matrix α α S) (JB : Matrix β β S) (x x' y : Matrix α β S) :
    hTens c JA JB (x + x') y = hTens c JA JB x y + hTens c JA JB x' y := by
  simp only [hTens, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem hTens_add_right' (JA : Matrix α α S) (JB : Matrix β β S) (x y y' : Matrix α β S) :
    hTens c JA JB x (y + y') = hTens c JA JB x y + hTens c JA JB x y' := by
  simp only [hTens, Matrix.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem symp_add_left' (ξ : S) (JA : Matrix α α S) (JB : Matrix β β S) (x x' y : Matrix α β S) :
    symp c ξ JA JB (x + x') y = symp c ξ JA JB x y + symp c ξ JA JB x' y := by
  simp only [symp, hTens_add_left', mul_add, map_add]

theorem symp_add_right' (ξ : S) (JA : Matrix α α S) (JB : Matrix β β S) (x y y' : Matrix α β S) :
    symp c ξ JA JB x (y + y') = symp c ξ JA JB x y + symp c ξ JA JB x y' := by
  simp only [symp, hTens_add_right', mul_add, map_add]

theorem symp_zero_left' (ξ : S) (JA : Matrix α α S) (JB : Matrix β β S) (y : Matrix α β S) :
    symp c ξ JA JB 0 y = 0 := by
  have h := symp_add_left' c ξ JA JB 0 0 y
  rw [add_zero] at h
  linear_combination -h

theorem symp_zero_right' (ξ : S) (JA : Matrix α α S) (JB : Matrix β β S) (x : Matrix α β S) :
    symp c ξ JA JB x 0 = 0 := by
  have h := symp_add_right' c ξ JA JB x 0 0
  rw [add_zero] at h
  linear_combination -h

theorem symp_neg_left' (ξ : S) (JA : Matrix α α S) (JB : Matrix β β S) (x y : Matrix α β S) :
    symp c ξ JA JB (-x) y = -symp c ξ JA JB x y := by
  have h := hTens_smul_left' c JA JB (-1) x y
  rw [neg_one_smul, neg_one_mul] at h
  simp only [symp, h, mul_neg, map_neg]

theorem symp_eq_neg_one' (ξ : S) (JA : Matrix α α S) (JB : Matrix β β S) (x y : Matrix α β S) :
    symp c ξ JA JB x y = -symp c (-1) JA JB (ξ • x) y := by
  simp only [symp, hTens_smul_left', neg_one_mul, map_neg, neg_neg]

theorem symp_neg_one_smul_right' (t : S) (JA : Matrix α α S) (JB : Matrix β β S) (x y : Matrix α β S) :
    symp c (-1) JA JB x (t • y) = symp c (-1) JA JB (c t • x) y := by
  simp only [symp, hTens_smul_left', hTens_smul_right']

end Gen

section Pl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem coefLin_smul' {n d n₁ d₁ : ℕ} (H : Plane E n n₁) (H' : Plane E d d₁) (t : AE F E)
    (u : Matrix (Fin n) (Fin d) (AE F E)) : coefLin H H' (t • u) = t • coefLin H H' u := by
  simp only [coefLin, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_smul, Matrix.smul_mul]

theorem planeT_smul_snd' (σ : E →ₐ[F] E) {n d n₁ d₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (H : Plane E n n₁)
    (H' : Plane E d d₁) (t : AE F E) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    (planeT σ X W H H' (t • u)).2 = t • (planeT σ X W H H' u).2 := by
  simp only [planeT, LinearMap.coe_mk, AddHom.coe_mk, coefLin_smul']
  rfl

theorem sI_eq_zero' (σ : E →ₐ[F] E) {n d n₁ d₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (H : Plane E n n₁)
    (H' : Plane E d d₁) (u : Matrix (Fin n) (Fin d) (AE F E)) (h : (planeT σ X W H H' u).1.1 = 0)
    (k : Ic d₁ n₁) : sI H H' u k = 0 := by
  apply (bA F E).repr.injective
  rw [map_zero]
  ext j
  exact congrFun h (k, j)

theorem pairI_eq_zero' (σ : E →ₐ[F] E) {n d n₁ d₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (H : Plane E n n₁)
    (H' : Plane E d d₁) (u : Matrix (Fin n) (Fin d) (AE F E)) (h : (planeT σ X W H H' u).1.2 = 0)
    (k : Ic d₁ n₁) : pairI σ X W H H' u k = 0 := by
  apply (bA' F E).repr.injective
  rw [map_zero]
  ext j
  exact congrFun h (k, j)

theorem planeT_smul_p' (σ : E →ₐ[F] E) {n d n₁ d₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (H : Plane E n n₁)
    (H' : Plane E d d₁) (t : AE F E) (u : Matrix (Fin n) (Fin d) (AE F E)) (h : (planeT σ X W H H' u).1.1 = 0) :
    (planeT σ X W H H' (t • u)).1.1 = 0 := by
  funext k
  have hs : sI H H' (t • u) k.1 = 0 := by
    simp only [sI, coefLin_smul', Matrix.smul_apply, smul_eq_mul]
    have := sI_eq_zero' σ X W H H' u h k.1
    simp only [sI] at this
    rw [this, mul_zero]
  simp only [planeT, LinearMap.coe_mk, AddHom.coe_mk, hs, map_zero, Finsupp.coe_zero, Pi.zero_apply]

theorem planeT_smul_q' (σ : E →ₐ[F] E) {n d n₁ d₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (H : Plane E n n₁)
    (H' : Plane E d d₁) (t : AE F E) (u : Matrix (Fin n) (Fin d) (AE F E)) (h : (planeT σ X W H H' u).1.2 = 0) :
    (planeT σ X W H H' (t • u)).1.2 = 0 := by
  funext k
  have hp : pairI σ X W H H' (t • u) k.1 = cA σ t * pairI σ X W H H' u k.1 := by
    simp only [pairI, tI, coefLin_smul', Matrix.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_neg]
    congr 1
    refine Finset.sum_congr rfl fun _ _ => by ring
  have hs : pairI σ X W H H' (t • u) k.1 = 0 := by
    rw [hp, pairI_eq_zero' σ X W H H' u h k.1, mul_zero]
  simp only [planeT, LinearMap.coe_mk, AddHom.coe_mk, hs, map_zero, Finsupp.coe_zero, Pi.zero_apply]

end Pl

end GlobalTheory.ThK.PlaneCo

namespace GlobalTheory.ThK.PlaneCo

theorem symp_self_planeT : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (H : Plane E n n₁) (H' : Plane E d d₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ θ : E, θ + σ θ = 1 →
    ∀ γ a b : Matrix (Fin n) (Fin d) (AE F E), planeT σ X W H H' a = ((0, (planeT σ X W H H' γ).1.2), 0) →
    planeT σ X W H H' b = (((planeT σ X W H H' γ).1.1, 0), 0) →
    symp (cA σ) (inclR (F := F) (AF F) θ) (incM F X.J) (incM F W.J) γ γ =
      (planeT σ X W H H' γ).1.1 ⬝ᵥ (planeT σ X W H H' γ).1.2 +
        2 * symp (cA σ) (inclR (F := F) (AF F) θ) (incM F X.J) (incM F W.J) b a +
        symp (cA σ) (inclR (F := F) (AF F) θ) (incM F X₁.J) (incM F W₁.J) (planeT σ X W H H' γ).2 (planeT σ X W H H' γ).2 := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' hB hX hW hH hH' θ hθ γ a b ha hb
  set T := planeT σ X W H H' with hT
  set t : AE F E := inclR (F := F) (AF F) θ with ht
  set sy := symp (cA σ) (-1) (incM F X.J) (incM F W.J) with hsy
  set sy₁ := symp (cA σ) (-1) (incM F X₁.J) (incM F W₁.J) with hsy₁
  have G : ∀ w w', sy w w' = (T w).1.1 ⬝ᵥ (T w').1.2 - (T w').1.1 ⬝ᵥ (T w).1.2 + sy₁ (T w).2 (T w').2 :=
    GlobalTheory.ThK.PlaneForm.form_eq σ B X W X₁ W₁ H H' hB hX hW hH hH'
  set c := γ - a - b with hc
  have hγ : γ = a + b + c := by rw [hc]; abel
  have hTc : T c = ((0, 0), (T γ).2) := by
    rw [hc, map_sub, map_sub, ha, hb]
    ext <;> simp

  have pa : (T a).1.1 = 0 := by rw [ha]
  have qa : (T a).1.2 = (T γ).1.2 := by rw [ha]
  have za : (T a).2 = 0 := by rw [ha]
  have pb : (T b).1.1 = (T γ).1.1 := by rw [hb]
  have qb : (T b).1.2 = 0 := by rw [hb]
  have zb : (T b).2 = 0 := by rw [hb]
  have pc : (T c).1.1 = 0 := by rw [hTc]
  have qc : (T c).1.2 = 0 := by rw [hTc]
  have zc : (T c).2 = (T γ).2 := by rw [hTc]
  have pta : (T (t • a)).1.1 = 0 := planeT_smul_p' σ X W H H' t a pa
  have ptc : (T (t • c)).1.1 = 0 := planeT_smul_p' σ X W H H' t c pc
  have qtb : (T (t • b)).1.2 = 0 := planeT_smul_q' σ X W H H' t b qb
  have qtc : (T (t • c)).1.2 = 0 := planeT_smul_q' σ X W H H' t c qc
  have zt : ∀ u, (T (t • u)).2 = t • (T u).2 := planeT_smul_snd' σ X W H H' t
  have z0 : sy₁ 0 0 = 0 := symp_zero_left' _ _ _ _ _
  have zl : ∀ y, sy₁ 0 y = 0 := symp_zero_left' _ _ _ _
  have zr : ∀ x, sy₁ x 0 = 0 := symp_zero_right' _ _ _ _
  have E1 : ∀ x y, symp (cA σ) t (incM F X.J) (incM F W.J) x y = -sy (t • x) y :=
    symp_eq_neg_one' (cA σ) t _ _

  have taa : symp (cA σ) t (incM F X.J) (incM F W.J) a a = 0 := by
    rw [E1, G, pta, pa, zt, za, smul_zero, z0]; simp
  have tbb : symp (cA σ) t (incM F X.J) (incM F W.J) b b = 0 := by
    rw [E1, G, qtb, qb, zt, zb, smul_zero, z0]; simp
  have tac : symp (cA σ) t (incM F X.J) (incM F W.J) a c = 0 := by
    rw [E1, G, pta, pc, qc, zt, za, smul_zero, zl]; simp
  have tca : symp (cA σ) t (incM F X.J) (incM F W.J) c a = 0 := by
    rw [E1, G, ptc, pa, za, zr]; simp
  have tbc : symp (cA σ) t (incM F X.J) (incM F W.J) b c = 0 := by
    rw [E1, G, qc, pc, zt, zb, smul_zero, zl]; simp
  have tcb : symp (cA σ) t (incM F X.J) (incM F W.J) c b = 0 := by
    rw [E1, G, qb, qtc, zb, zr]; simp
  have tcc : symp (cA σ) t (incM F X.J) (incM F W.J) c c =
      symp (cA σ) t (incM F X₁.J) (incM F W₁.J) (T γ).2 (T γ).2 := by
    rw [E1, G, ptc, pc, qc, qtc, zt, zc, symp_eq_neg_one' (cA σ) t (incM F X₁.J) (incM F W₁.J)]
    simp [hsy₁]

  have hct : cA σ t = 1 - t := by
    rw [ht, show (1 : AE F E) = inclR (F := F) (AF F) 1 from (map_one _).symm, ← map_sub,
      ← hθ, add_sub_cancel_left]
    simp [cA, inclR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  have sba : sy b a = (T γ).1.1 ⬝ᵥ (T γ).1.2 := by
    rw [G, pb, qa, pa, qb, zb, za, z0]; simp
  have anti : sy (t • a) b = -sy b (t • a) := by
    rw [G, G, pta, zt, za, zb, smul_zero, z0]; simp
  have tab : symp (cA σ) t (incM F X.J) (incM F W.J) a b =
      sy b a + symp (cA σ) t (incM F X.J) (incM F W.J) b a := by
    have h1 : sy b (t • a) = sy b a - sy (t • b) a := by
      rw [hsy, symp_neg_one_smul_right', hct, sub_smul, one_smul, sub_eq_add_neg, symp_add_left', symp_neg_left',
        ← sub_eq_add_neg]
    rw [E1, E1 b a, anti, neg_neg, h1]
    ring
  conv_lhs => rw [hγ]
  rw [symp_add_left', symp_add_left', symp_add_right', symp_add_right', symp_add_right', symp_add_right',
    symp_add_right', symp_add_right', taa, tbb, tac, tca, tbc, tcb, tcc, tab, sba]
  ring

end GlobalTheory.ThK.PlaneCo
