import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
open PositivityTheory.Rg.Tf.Geo

private def piGL {W : Type} (K : W → Type) [∀ w, CommRing (K w)] (n : ℕ) (g : ∀ w, GL (Fin n) (K w)) :
    GL (Fin n) (∀ w, K w) where
  val := Matrix.of fun i j w => (g w : Matrix (Fin n) (Fin n) (K w)) i j
  inv := Matrix.of fun i j w => ((g w)⁻¹ : GL (Fin n) (K w)).val i j
  val_inv := by
    ext i j w
    have h := congrFun (congrFun (g w).mul_inv i) j
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply] at h ⊢
    rw [h]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  inv_val := by
    ext i j w
    have h := congrFun (congrFun (g w).inv_mul i) j
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply] at h ⊢
    rw [h]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

private def prGL {W : Type} (K : W → Type) [∀ w, CommRing (K w)] (n : ℕ) (w : W) :
    GL (Fin n) (∀ w, K w) →* GL (Fin n) (K w) :=
  Matrix.GeneralLinearGroup.map (Pi.evalRingHom K w)

private theorem prGL_piGL {W : Type} (K : W → Type) [∀ w, CommRing (K w)] (n : ℕ) (g : ∀ w, GL (Fin n) (K w)) (w : W) :
    prGL K n w (piGL K n g) = g w := by
  ext i j
  rfl

private theorem prGL_ext {W : Type} (K : W → Type) [∀ w, CommRing (K w)] (n : ℕ) (a b : GL (Fin n) (∀ w, K w))
    (h : ∀ w, prGL K n w a = prGL K n w b) : a = b := by
  ext i j w
  exact congrArg (fun g : GL (Fin n) (K w) => (g : Matrix (Fin n) (Fin n) (K w)) i j) (h w)

private theorem prGL_cont {W : Type} (K : W → Type) [∀ w, CommRing (K w)] [∀ w, TopologicalSpace (K w)] (n : ℕ) (w : W) :
    Continuous (prGL K n w) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (continuous_apply w).comp ((continuous_apply j).comp ((continuous_apply i).comp
      (Units.continuous_val (M := Matrix (Fin n) (Fin n) (∀ w, K w)))))
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (continuous_apply w).comp ((continuous_apply j).comp ((continuous_apply i).comp
      (Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) (∀ w, K w)))))

private theorem piGL_cont {W : Type} (K : W → Type) [∀ w, CommRing (K w)] [∀ w, TopologicalSpace (K w)] (n : ℕ) :
    Continuous (piGL K n) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_pi fun i => continuous_pi fun j => continuous_pi fun w => ?_
    exact (continuous_apply j).comp ((continuous_apply i).comp
      ((Units.continuous_val (M := Matrix (Fin n) (Fin n) (K w))).comp (continuous_apply w)))
  · refine continuous_pi fun i => continuous_pi fun j => continuous_pi fun w => ?_
    exact (continuous_apply j).comp ((continuous_apply i).comp
      ((Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) (K w))).comp (continuous_apply w)))

theorem UpperTheory.exists_compact_conj_mem_centralizer_mul_of_separable_charpoly :
    P1 → ∀ (W : Type) [Finite W] (K : W → Type) [∀ w, NontriviallyNormedField (K w)] [∀ w, LocallyCompactSpace (K w)] [∀ w, CharZero (K w)] (n : ℕ) (γ : GL (Fin n) (∀ w, K w)), (γ : Matrix (Fin n) (Fin n) (∀ w, K w)).charpoly.Separable → ∀ D : Set (GL (Fin n) (∀ w, K w)), IsCompact D → ∃ C : Set (GL (Fin n) (∀ w, K w)), IsCompact C ∧ ∀ x, x⁻¹ * γ * x ∈ D → ∃ t, t * γ = γ * t ∧ ∃ y ∈ C, x = t * y := by
  intro hP W _ K _ _ _ n γ hγ D hD
  have hsep : ∀ w, ((prGL K n w γ : GL (Fin n) (K w)) : Matrix (Fin n) (Fin n) (K w)).charpoly.Separable := by
    intro w
    have h : ((prGL K n w γ : GL (Fin n) (K w)) : Matrix (Fin n) (Fin n) (K w))
        = (γ : Matrix (Fin n) (Fin n) (∀ w, K w)).map (Pi.evalRingHom K w) := rfl
    rw [h, Matrix.charpoly_map]
    exact hγ.map
  choose C hC hCx using fun w => hP (K w) n (prGL K n w γ) (hsep w) (prGL K n w '' D) (hD.image (prGL_cont K n w))
  refine ⟨piGL K n '' Set.pi Set.univ C, (isCompact_univ_pi hC).image (piGL_cont K n), fun x hx => ?_⟩
  choose t ht y hy hxy using fun w => hCx w (prGL K n w x) ⟨_, hx, by simp only [map_mul, map_inv]⟩
  refine ⟨piGL K n t, prGL_ext K n _ _ fun w => ?_, piGL K n y, ⟨y, fun w _ => hy w, rfl⟩, prGL_ext K n _ _ fun w => ?_⟩
  · simp only [map_mul, prGL_piGL, ht w]
  · simp only [map_mul, prGL_piGL, hxy w]
