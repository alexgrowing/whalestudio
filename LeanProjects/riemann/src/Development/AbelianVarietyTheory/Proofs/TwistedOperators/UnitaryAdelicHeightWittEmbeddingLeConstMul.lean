import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittAnisotropicGroupNormalizesFlagUnipotent
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.EmbHeight

open scoped NNReal
open GlobalTheory.AdelicU Formalism.UG

section Generic

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

theorem htOf_le_mul {R : Type} [CommRing R] {N : Matrix n n R → ℝ≥0} {N₁ : Matrix m m R → ℝ≥0} {c : ℝ≥0}
    (hc : 1 ≤ c) (X : GL n R) (x : GL m R) (h1 : N (X : Matrix n n R) ≤ c * max 1 (N₁ (x : Matrix m m R)))
    (h2 : N ((X⁻¹ : GL n R) : Matrix n n R) ≤ c * max 1 (N₁ ((x⁻¹ : GL m R) : Matrix m m R))) :
    htOf N X ≤ c * htOf N₁ x := by
  refine max_le (one_le_mul_of_one_le_of_one_le hc (one_le_htOf _ _)) (max_le ?_ ?_)
  · exact h1.trans (mul_le_mul' le_rfl (max_le (one_le_htOf _ _) (le_htOf _ _)))
  · exact h2.trans (mul_le_mul' le_rfl (max_le (one_le_htOf _ _) (inv_le_htOf _ _)))

theorem bc_val_aff {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (A : Matrix n n R) (B : Matrix n m R)
    (C : Matrix m n R) {X : GL n R} {x : GL m R} (h : (X : Matrix n n R) = A + B * (x : Matrix m m R) * C) :
    ((bc φ X : GL n R') : Matrix n n R') = A.map φ + B.map φ * ((bc φ x : GL m R') : Matrix m m R') * C.map φ := by
  show (X : Matrix n n R).map φ = A.map φ + B.map φ * (x : Matrix m m R).map φ * C.map φ
  rw [h, Matrix.map_add _ (map_add φ), Matrix.map_mul, Matrix.map_mul]

theorem bc_inv_aff {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (A : Matrix n n R) (B : Matrix n m R)
    (C : Matrix m n R) {X : GL n R} {x : GL m R}
    (h : ((X⁻¹ : GL n R) : Matrix n n R) = A + B * ((x⁻¹ : GL m R) : Matrix m m R) * C) :
    (((bc φ X)⁻¹ : GL n R') : Matrix n n R') =
      A.map φ + B.map φ * (((bc φ x)⁻¹ : GL m R') : Matrix m m R') * C.map φ := by
  simp only [← map_inv]
  exact bc_val_aff φ A B C h

theorem map_aff {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (A : Matrix n n R) (B : Matrix n m R)
    (C : Matrix m n R) (y : Matrix m m R) : (A + B * y * C).map φ = A.map φ + B.map φ * y.map φ * C.map φ := by
  rw [Matrix.map_add _ (map_add φ), Matrix.map_mul, Matrix.map_mul]

theorem opNorm_add_le (a b : Matrix n n ℂ) : opNorm (a + b) ≤ opNorm a + opNorm b := by
  unfold opNorm; rw [map_add]; exact nnnorm_add_le _ _

theorem exists_opNorm_mul_mul_le (B : Matrix n m ℂ) (C : Matrix m n ℂ) :
    ∃ K : ℝ≥0, ∀ y : Matrix m m ℂ, opNorm (B * y * C) ≤ K * opNorm y := by
  let L : (EuclideanSpace ℂ m →L[ℂ] EuclideanSpace ℂ m) →ₗ[ℂ] (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :=
    { toFun := fun T => Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (B * (Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ)).symm T * C)
      map_add' := fun S T => by simp only [map_add, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun r T => by simp only [map_smul, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }
  let Lc := LinearMap.toContinuousLinearMap L
  refine ⟨‖Lc‖₊, fun y => ?_⟩
  have e : opNorm (B * y * C) = ‖Lc (Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) y)‖₊ := by
    show _ = ‖L _‖₊
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, StarAlgEquiv.symm_apply_apply]
    rfl
  rw [e]
  exact Lc.le_opNNNorm _

end Generic

variable (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

theorem normFin_add_le (v : HeightOneSpectrum (𝓞 F)) {p q : Type} [Fintype p] [Fintype q]
    (a b : Matrix p q (Fv F v ⊗[F] E)) : normFin F v (a + b) ≤ max (normFin F v a) (normFin F v b) :=
  (normFin_le_iff F v).2 fun i j =>
    (absFin_add_le F v _ _).trans (max_le_max (absFin_le_normFin F v a i j) (absFin_le_normFin F v b i j))

theorem normFin_aff_le (v : HeightOneSpectrum (𝓞 F)) (A : Matrix n n (Fv F v ⊗[F] E)) (B : Matrix n m (Fv F v ⊗[F] E))
    (C : Matrix m n (Fv F v ⊗[F] E)) (y : Matrix m m (Fv F v ⊗[F] E)) :
    normFin F v (A + B * y * C) ≤
      max 1 (max (normFin F v A) (normFin F v B * normFin F v C)) * max 1 (normFin F v y) := by
  set M := max 1 (max (normFin F v A) (normFin F v B * normFin F v C))
  have h1 : (1 : ℝ≥0) ≤ M := le_max_left _ _
  refine (normFin_add_le F v _ _).trans (max_le ?_ ?_)
  · exact (le_max_left _ _ |>.trans (le_max_right 1 _) : normFin F v A ≤ M).trans (le_mul_of_one_le_right' (le_max_left _ _))
  · calc normFin F v (B * y * C) ≤ normFin F v B * normFin F v y * normFin F v C :=
          (normFin_mul_le F v _ _).trans (mul_le_mul' (normFin_mul_le F v _ _) le_rfl)
      _ = (normFin F v B * normFin F v C) * normFin F v y := by ring
      _ ≤ M * max 1 (normFin F v y) :=
          mul_le_mul' ((le_max_right _ _).trans (le_max_right _ _)) (le_max_right _ _)

theorem exists_normInf_aff_le (w : InfinitePlace F) (A : Matrix n n (w.Completion ⊗[F] E))
    (B : Matrix n m (w.Completion ⊗[F] E)) (C : Matrix m n (w.Completion ⊗[F] E)) :
    ∃ c : ℝ≥0, 1 ≤ c ∧ ∀ y : Matrix m m (w.Completion ⊗[F] E),
      normInf F w (A + B * y * C) ≤ c * max 1 (normInf F w y) := by
  classical
  have hK : ∀ τ : EmbOver E w, ∃ K : ℝ≥0, ∀ y : Matrix m m ℂ,
      opNorm (B.map (infEmb τ) * y * C.map (infEmb τ)) ≤ K * opNorm y := fun τ =>
    exists_opNorm_mul_mul_le _ _
  choose K hK using hK
  refine ⟨1 + ∑ τ, (opNorm (A.map (infEmb τ)) + K τ), le_self_add, fun y => (normInf_le_iff F w).2 fun τ => ?_⟩
  have hy : opNorm (y.map (infEmb τ)) ≤ max 1 (normInf F w y) :=
    ((normInf_le_iff F w).1 le_rfl τ).trans (le_max_right _ _)
  have hs : opNorm (A.map (infEmb τ)) + K τ ≤ 1 + ∑ τ, (opNorm (A.map (infEmb τ)) + K τ) :=
    (Finset.single_le_sum (f := fun τ => opNorm (A.map (infEmb τ)) + K τ) (fun _ _ => zero_le)
      (Finset.mem_univ τ)).trans le_add_self
  have e := map_aff (infEmb τ) A B C y
  rw [e]
  refine (opNorm_add_le _ _).trans ?_
  have h3 := hK τ (y.map (infEmb τ))
  refine (add_le_add le_rfl h3).trans ?_
  calc opNorm (A.map (infEmb τ)) + K τ * opNorm (y.map (infEmb τ))
      ≤ opNorm (A.map (infEmb τ)) * max 1 (normInf F w y) + K τ * max 1 (normInf F w y) :=
        add_le_add (le_mul_of_one_le_right' (le_max_left _ _)) (mul_le_mul' le_rfl hy)
    _ = (opNorm (A.map (infEmb τ)) + K τ) * max 1 (normInf F w y) := by rw [add_mul]
    _ ≤ _ := mul_le_mul' hs le_rfl

theorem eventually_normFin_rect_le_one {p q : Type} [Fintype p] [Fintype q] (y : Matrix p q (AF F ⊗[F] E)) :
    ∀ᶠ v in Filter.cofinite, normFin F v (y.map (compFin F E v)) ≤ 1 := by
  simp only [normFin_le_iff, Filter.eventually_all]
  exact fun i j => eventually_absFin_le_one F (y i j)

theorem exists_heightGL_aff_le (A : Matrix n n (AF F ⊗[F] E)) (B : Matrix n m (AF F ⊗[F] E))
    (C : Matrix m n (AF F ⊗[F] E)) :
    ∃ K : ℝ≥0, ∀ (X : GL n (AF F ⊗[F] E)) (x : GL m (AF F ⊗[F] E)),
      (X : Matrix n n (AF F ⊗[F] E)) = A + B * (x : Matrix m m (AF F ⊗[F] E)) * C →
      ((X⁻¹ : GL n (AF F ⊗[F] E)) : Matrix n n (AF F ⊗[F] E)) =
        A + B * ((x⁻¹ : GL m (AF F ⊗[F] E)) : Matrix m m (AF F ⊗[F] E)) * C →
      heightGL F X ≤ K * heightGL F x := by
  have hw := fun w : InfinitePlace F =>
    exists_normInf_aff_le F w (A.map (compInf F E w)) (B.map (compInf F E w)) (C.map (compInf F E w))
  choose cw hcw1 hcw using hw
  set cv : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v => max 1 (max (normFin F v (A.map (compFin F E v)))
    (normFin F v (B.map (compFin F E v)) * normFin F v (C.map (compFin F E v)))) with hcv
  have hfin : (Function.mulSupport cv).Finite := by
    have h := ((eventually_normFin_rect_le_one F A).and (eventually_normFin_rect_le_one F B)).and
      (eventually_normFin_rect_le_one F C)
    refine (Filter.eventually_cofinite.1 h).subset fun v hv hv' => hv ?_
    refine max_eq_left (max_le hv'.1.1 ?_)
    exact mul_le_one' hv'.1.2 hv'.2
  refine ⟨(∏ w, cw w) * ∏ᶠ v, cv v, fun X x h1 h2 => ?_⟩
  unfold heightGL
  rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib,
    ← finprod_mul_distrib hfin (finite_mulSupport_htFin F x)]
  refine mul_le_mul' (Finset.prod_le_prod' fun w _ => ?_)
    (finprod_le_finprod' (finite_mulSupport_htFin F _) (hfin.union (finite_mulSupport_htFin F x) |>.subset
      (Function.mulSupport_mul _ _)) fun v => ?_)
  · refine htOf_le_mul (hcw1 w) _ _ ?_ ?_
    · rw [bc_val_aff _ _ _ _ h1]; exact hcw w _
    · rw [bc_inv_aff _ _ _ _ h2]; exact hcw w _
  · refine htOf_le_mul (le_max_left _ _) _ _ ?_ ?_
    · rw [bc_val_aff _ _ _ _ h1]; exact normFin_aff_le F v _ _ _ _
    · rw [bc_inv_aff _ _ _ _ h2]; exact normFin_aff_le F v _ _ _ _

end GlobalTheory.EmbHeight

namespace GlobalTheory.EmbHeight

open scoped NNReal
open GlobalTheory.AdelicU

theorem unitaryAdelicHeight_wittEmbedding_le : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ C : ℝ, ∀ g : GA D S₀,
    height S (d.emb0 g) ≤ C * height S₀ g := by
  intro D S S₀ ρ d
  obtain ⟨K, hK⟩ := exists_heightGL_aff_le D.host.F (d.jX ⬝ d.pX + d.jY ⬝ d.pY) d.j0 d.p0
  refine ⟨K, fun g => ?_⟩
  have h1 : ∀ g : GA D S₀, mt S (d.emb0 g) = (d.jX ⬝ d.pX + d.jY ⬝ d.pY) + d.j0 ⬝ mt S₀ g ⬝ d.p0 := fun g => by
    rw [d.unitaryMatrix_wittCoreEmbedding, add_right_comm]
  have h := hK (matHom S (d.emb0 g)) (matHom S₀ g) (h1 g) (by
    rw [← map_inv, ← map_inv]
    exact h1 g⁻¹)
  show ((heightGL D.host.F _ : ℝ≥0) : ℝ) ≤ (K : ℝ) * ((heightGL D.host.F _ : ℝ≥0) : ℝ)
  exact_mod_cast h

end GlobalTheory.EmbHeight

end
