import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VsizeNonneg

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EmbHeight

open scoped NNReal TensorProduct
open NumberField IsDedekindDomain GlobalTheory.AdelicU Formalism.UG

variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in

theorem exists_opNorm_le (J : Matrix n m ℂ) (P : Matrix m n ℂ) (K : Matrix n n ℂ) :
    ∃ c : ℝ≥0, ∀ (x : Matrix m m ℂ) (h : ℝ≥0), 1 ≤ h → opNorm x ≤ h → opNorm (J * x * P + K) ≤ c * h := by
  refine ⟨‖J‖₊ * ‖P‖₊ + ‖K‖₊, fun x h h1 hx => ?_⟩
  have hx' : ‖x‖₊ ≤ h := hx
  calc opNorm (J * x * P + K) = ‖J * x * P + K‖₊ := rfl
    _ ≤ ‖J * x * P‖₊ + ‖K‖₊ := nnnorm_add_le _ _
    _ ≤ ‖J‖₊ * ‖x‖₊ * ‖P‖₊ + ‖K‖₊ := by
        gcongr
        exact (Matrix.l2_opNNNorm_mul _ _).trans (by gcongr; exact Matrix.l2_opNNNorm_mul _ _)
    _ ≤ ‖J‖₊ * h * ‖P‖₊ + ‖K‖₊ * h := by
        gcongr
        exact le_mul_of_one_le_right (by positivity) h1
    _ = (‖J‖₊ * ‖P‖₊ + ‖K‖₊) * h := by ring

theorem htOf_le {R : Type} [CommRing R] {N₁ : Matrix m m R → ℝ≥0} {N : Matrix n n R → ℝ≥0}
    {f : Matrix m m R → Matrix n n R} {c : ℝ≥0} (hc : 1 ≤ c)
    (hN : ∀ (x : Matrix m m R) (h : ℝ≥0), 1 ≤ h → N₁ x ≤ h → N (f x) ≤ c * h)
    (X : GL n R) (x : GL m R) (h1 : (X : Matrix n n R) = f x)
    (h2 : ((X⁻¹ : GL n R) : Matrix n n R) = f (x⁻¹ : GL m R)) : htOf N X ≤ c * htOf N₁ x := by
  have hx1 : 1 ≤ htOf N₁ x := one_le_htOf N₁ x
  have hc1 : 1 ≤ c * htOf N₁ x := one_le_mul_of_one_le_of_one_le hc hx1
  show max 1 (max (N (X : Matrix n n R)) (N ((X⁻¹ : GL n R) : Matrix n n R))) ≤ c * htOf N₁ x
  refine max_le hc1 (max_le ?_ ?_)
  · rw [h1]
    exact hN _ _ hx1 (le_htOf N₁ x)
  · rw [h2]
    exact hN _ _ hx1 (inv_le_htOf N₁ x)

variable (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem exists_normInf_le (w : InfinitePlace F) (J : Matrix n m (w.Completion ⊗[F] E))
    (P : Matrix m n (w.Completion ⊗[F] E)) (K : Matrix n n (w.Completion ⊗[F] E)) :
    ∃ c : ℝ≥0, 1 ≤ c ∧ ∀ (x : Matrix m m (w.Completion ⊗[F] E)) (h : ℝ≥0), 1 ≤ h → normInf F w x ≤ h →
      normInf F w (J * x * P + K) ≤ c * h := by
  classical
  have hτ : ∀ τ : EmbOver E w, ∃ c : ℝ≥0, ∀ (x : Matrix m m ℂ) (h : ℝ≥0), 1 ≤ h → opNorm x ≤ h →
      opNorm (J.map (infEmb τ) * x * P.map (infEmb τ) + K.map (infEmb τ)) ≤ c * h :=
    fun τ => GlobalTheory.EmbHeight.exists_opNorm_le _ _ _
  choose c hc using hτ
  refine ⟨max 1 (Finset.univ.sup c), le_max_left _ _, fun x h h1 hx => ?_⟩
  rw [normInf_le_iff] at hx ⊢
  intro τ
  rw [Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul]
  refine (hc τ _ h h1 (hx τ)).trans ?_
  gcongr
  exact (Finset.le_sup (Finset.mem_univ τ)).trans (le_max_right _ _)

private lemma normFin_add_le_max (v : HeightOneSpectrum (𝓞 F)) {p q : Type} [Fintype p] [Fintype q]
    (a b : Matrix p q (Fv F v ⊗[F] E)) : normFin F v (a + b) ≤ max (normFin F v a) (normFin F v b) := by
  rw [normFin_le_iff]
  intro i j
  exact (absFin_add_le F v _ _).trans (max_le_max (absFin_le_normFin F v a i j) (absFin_le_normFin F v b i j))

omit [DecidableEq m] [DecidableEq n] in

theorem normFin_le (v : HeightOneSpectrum (𝓞 F)) (J : Matrix n m (Fv F v ⊗[F] E))
    (P : Matrix m n (Fv F v ⊗[F] E)) (K : Matrix n n (Fv F v ⊗[F] E))
    (x : Matrix m m (Fv F v ⊗[F] E)) (h : ℝ≥0) (h1 : 1 ≤ h) (hx : normFin F v x ≤ h) :
    normFin F v (J * x * P + K) ≤ max 1 (max (normFin F v J * normFin F v P) (normFin F v K)) * h := by
  calc normFin F v (J * x * P + K) ≤ max (normFin F v (J * x * P)) (normFin F v K) :=
        normFin_add_le_max F v _ _
    _ ≤ max 1 (max (normFin F v J * normFin F v P) (normFin F v K)) * h := by
        refine max_le ?_ ?_
        · calc normFin F v (J * x * P) ≤ normFin F v J * normFin F v x * normFin F v P :=
                (normFin_mul_le F v _ _).trans (by gcongr; exact normFin_mul_le F v _ _)
            _ ≤ normFin F v J * h * normFin F v P := by gcongr
            _ = normFin F v J * normFin F v P * h := by ring
            _ ≤ _ := by
                gcongr
                exact (le_max_left _ _).trans (le_max_right _ _)
        · calc normFin F v K ≤ max 1 (max (normFin F v J * normFin F v P) (normFin F v K)) :=
                (le_max_right _ _).trans (le_max_right _ _)
            _ ≤ _ := le_mul_of_one_le_right (by positivity) h1

omit [DecidableEq m] [DecidableEq n] in

theorem eventually_normFin_le (y : Matrix m n (AF F ⊗[F] E)) :
    ∀ᶠ v in Filter.cofinite, normFin F v (y.map (compFin F E v)) ≤ 1 := by
  have hall : ∀ᶠ v in Filter.cofinite, ∀ p : m × n, absFin F v (compFin F E v (y p.1 p.2)) ≤ 1 :=
    Filter.eventually_all.2 fun p => eventually_absFin_le_one F (y p.1 p.2)
  filter_upwards [hall] with v hv
  rw [normFin_le_iff]
  intro i j
  exact hv (i, j)

private lemma matrix_map_eq_of_eq {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {p q : Type} [Fintype p]
    [Fintype q] (J : Matrix q p R) (P : Matrix p q R) (K : Matrix q q R) (X : Matrix q q R) (x : Matrix p p R)
    (h : X = J * x * P + K) : X.map φ = J.map φ * x.map φ * P.map φ + K.map φ := by
  rw [h, Matrix.map_add _ (map_add φ), Matrix.map_mul, Matrix.map_mul]

theorem exists_heightGL_le (J : Matrix n m (AF F ⊗[F] E)) (P : Matrix m n (AF F ⊗[F] E))
    (K : Matrix n n (AF F ⊗[F] E)) :
    ∃ C : ℝ≥0, ∀ (X : GL n (AF F ⊗[F] E)) (x : GL m (AF F ⊗[F] E)),
      (X : Matrix n n (AF F ⊗[F] E)) = J * (x : Matrix m m (AF F ⊗[F] E)) * P + K →
      ((X⁻¹ : GL n (AF F ⊗[F] E)) : Matrix n n (AF F ⊗[F] E)) =
        J * ((x⁻¹ : GL m (AF F ⊗[F] E)) : Matrix m m (AF F ⊗[F] E)) * P + K →
      heightGL F X ≤ C * heightGL F x := by
  classical
  have hinf : ∀ w : InfinitePlace F, ∃ c : ℝ≥0, 1 ≤ c ∧ ∀ (x : Matrix m m (w.Completion ⊗[F] E)) (h : ℝ≥0),
      1 ≤ h → normInf F w x ≤ h →
        normInf F w (J.map (compInf F E w) * x * P.map (compInf F E w) + K.map (compInf F E w)) ≤ c * h :=
    fun w => GlobalTheory.EmbHeight.exists_normInf_le F w _ _ _
  choose c hc1 hc using hinf
  let M : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v =>
    max 1 (max (normFin F v (J.map (compFin F E v)) * normFin F v (P.map (compFin F E v)))
      (normFin F v (K.map (compFin F E v))))
  have hM1 : ∀ v, 1 ≤ M v := fun v => le_max_left _ _
  have hMfin : (Function.mulSupport M).Finite := by
    have h3 := (GlobalTheory.EmbHeight.eventually_normFin_le F J).and
      ((GlobalTheory.EmbHeight.eventually_normFin_le F P).and (GlobalTheory.EmbHeight.eventually_normFin_le F K))
    refine (Filter.eventually_cofinite.1 h3).subset ?_
    intro v hv hv3
    exact hv (max_eq_left (max_le (mul_le_one' hv3.1 hv3.2.1) hv3.2.2))
  refine ⟨(∏ w, c w) * ∏ᶠ v, M v, fun X x hX hXi => ?_⟩
  have key_inf : ∀ w, htInf F w (Formalism.UG.bc (compInf F E w) X) ≤ c w * htInf F w (Formalism.UG.bc (compInf F E w) x) :=
    fun w => GlobalTheory.EmbHeight.htOf_le (hc1 w) (hc w) _ _ (matrix_map_eq_of_eq _ _ _ _ _ _ hX) (matrix_map_eq_of_eq _ _ _ _ _ _ hXi)
  have key_fin : ∀ v, htFin F v (Formalism.UG.bc (compFin F E v) X) ≤ M v * htFin F v (Formalism.UG.bc (compFin F E v) x) :=
    fun v => GlobalTheory.EmbHeight.htOf_le (hM1 v) (fun y h h1 hy => GlobalTheory.EmbHeight.normFin_le F v _ _ _ y h h1 hy) _ _
      (matrix_map_eq_of_eq _ _ _ _ _ _ hX) (matrix_map_eq_of_eq _ _ _ _ _ _ hXi)
  have hfinX := finite_mulSupport_htFin F X
  have hfinx := finite_mulSupport_htFin F x
  have hI : ∏ w, htInf F w (Formalism.UG.bc (compInf F E w) X) ≤
      (∏ w, c w) * ∏ w, htInf F w (Formalism.UG.bc (compInf F E w) x) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod' fun w _ => key_inf w
  have hF : ∏ᶠ v, htFin F v (Formalism.UG.bc (compFin F E v) X) ≤
      (∏ᶠ v, M v) * ∏ᶠ v, htFin F v (Formalism.UG.bc (compFin F E v) x) := by
    rw [← finprod_mul_distrib hMfin hfinx]
    exact finprod_le_finprod' hfinX ((hMfin.union hfinx).subset (Function.mulSupport_mul _ _)) fun v => key_fin v
  unfold heightGL
  calc _ ≤ ((∏ w, c w) * ∏ w, htInf F w (Formalism.UG.bc (compInf F E w) x)) *
        ((∏ᶠ v, M v) * ∏ᶠ v, htFin F v (Formalism.UG.bc (compFin F E v) x)) := mul_le_mul' hI hF
    _ = _ := by ring

theorem height_emb_le : ∀ (D : D7) (S A B : HSp D) (o : GlobalTheory.MixModel.OrthDec S A B), ∃ (C : ℝ) (a : ℕ),
    ∀ g : GA D A, GlobalTheory.Grow.height S (o.emb (g, 1)) ≤ C * GlobalTheory.Grow.height A g ^ a := by
  intro D S A B o
  obtain ⟨C, hC⟩ := GlobalTheory.EmbHeight.exists_heightGL_le D.host.F o.jA o.pA (o.jB * o.pB)
  refine ⟨(C : ℝ), 1, fun g => ?_⟩
  have e : ∀ a : GA D A, (Formalism.L2.Theta.matHom S (o.emb (a, 1)) :
      Matrix (Fin S.rank) (Fin S.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) =
      o.jA * (Formalism.L2.Theta.matHom A a : Matrix (Fin A.rank) (Fin A.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) *
        o.pA + o.jB * o.pB := by
    intro a
    have hm := o.mt_emb a 1
    rw [GlobalTheory.MixModel.mt_one, Matrix.mul_one] at hm
    exact hm
  have hinv : o.emb (g⁻¹, 1) = (o.emb (g, 1))⁻¹ := by
    rw [← map_inv, Prod.inv_mk, inv_one]
  have e2 := e g⁻¹
  rw [hinv, map_inv, map_inv] at e2
  have key := hC _ _ (e g) e2
  unfold GlobalTheory.Grow.height
  rw [pow_one]
  exact_mod_cast key

end GlobalTheory.EmbHeight

end
