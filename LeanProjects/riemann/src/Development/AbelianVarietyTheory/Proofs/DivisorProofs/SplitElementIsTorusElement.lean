import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

noncomputable section

open Formalism.UG (cT)

namespace GlobalTheory.IdTorus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem infEmb_archUnit (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (c : ℝ) :
    infEmb τ (compInf F E w (archUnit F E c : AF F ⊗[F] E)) = (Real.exp c : ℂ) := by
  have := h.1
  have hw : w.IsReal := IsTotallyReal.isReal w
  change infEmb τ (evInf F w (archUnitF F c : AF F) ⊗ₜ[F] (1 : E)) = _
  rw [infEmb_tmul, map_one, mul_one]
  have e1 := congrArg (fun p => p.1 ⟨w, hw⟩) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply
    (fun _ => Real.exp c, fun _ => (Real.exp c : ℂ)))
  simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at e1
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw]
  exact congrArg (fun x : ℝ => (x : ℂ)) e1

theorem eq_of_frame {n r : ℕ} {K : Type} [Field K] (τ : K →+* ℂ) {X Y : Matrix (Fin n) (Fin r) K}
    {P Q : Matrix (Fin r) (Fin n) K} (hPX : P * X = 0) (hPY : P * Y = 1) (hQX : Q * X = 1) (hQY : Q * Y = 0)
    {A : Matrix (Fin n) (Fin n) ℂ} {D D' : Matrix (Fin r) (Fin r) ℂ}
    (hX : A * X.map τ = X.map τ * D) (hY : A * Y.map τ = Y.map τ * D')
    (hz : ∀ z : Fin n → K, P *ᵥ z = 0 → Q *ᵥ z = 0 → A *ᵥ (fun i => τ (z i)) = fun i => τ (z i)) :
    A = 1 + X.map τ * (D - 1) * Q.map τ + Y.map τ * (D' - 1) * P.map τ := by
  set R0 : Matrix (Fin n) (Fin n) K := 1 - X * Q - Y * P with hR0
  have hP : P * R0 = 0 := by
    rw [hR0, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPX, hPY]; simp
  have hQ : Q * R0 = 0 := by
    rw [hR0, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQX, hQY]; simp
  have hA : A * R0.map τ = R0.map τ := by
    ext i j
    have := congrFun (hz (fun k => R0 k j) (funext fun k => congrFun (congrFun hP k) j)
      (funext fun k => congrFun (congrFun hQ k) j)) i
    exact this
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) = R0.map τ + X.map τ * Q.map τ + Y.map τ * P.map τ := by
    have e : (1 : Matrix (Fin n) (Fin n) K) = R0 + X * Q + Y * P := by rw [hR0]; abel
    have := congrArg (Matrix.map · τ) e
    rw [Matrix.map_add _ (map_add τ), Matrix.map_add _ (map_add τ), Matrix.map_mul, Matrix.map_mul,
      Matrix.map_one _ (map_zero τ) (map_one τ)] at this
    exact this
  have h2 : R0.map τ = 1 - X.map τ * Q.map τ - Y.map τ * P.map τ := by
    rw [h1]; abel
  calc A = A * 1 := (Matrix.mul_one A).symm
    _ = R0.map τ + X.map τ * D * Q.map τ + Y.map τ * D' * P.map τ := by
      conv_lhs => rw [h1]
      rw [Matrix.mul_add, Matrix.mul_add, hA, ← Matrix.mul_assoc, hX, ← Matrix.mul_assoc, hY]
    _ = _ := by
      rw [h2, Matrix.mul_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_one]
      abel

theorem isIdTorusElt_of_isSplitElt {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}
    (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) (S : Finset (Fin r)) (u : Fin r → ℝ)
    {a : GAd σ J} (ha : IsSplitElt σ J X Y S u a) :
    IsIdTorusElt σ J X Y (fun k => archUnit F E (stepSum S u k)) a := by
  obtain ⟨hfin, harch⟩ : IsTorusElt σ J X Y (fun i => Real.exp (stepSum S u i)) a := ha
  let d : Fin r → (AF F ⊗[F] E)ˣ := fun k => archUnit F E (stepSum S u k)
  have c1 : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E), cT (sigR (AF F) σ) (adMat F Z) = adMat F (cT (σ : E →+* E) Z) :=
    fun Z => rfl
  have c3 : ∀ Z : Matrix (Fin n) (Fin r) E, (cT (sigR (AF F) σ) (adMat F Z) * JR (F := F) (AF F) J :
      Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) = adMat F (cT (σ : E →+* E) Z * J) := fun Z => by
    rw [c1]; simp only [adMat, JR, Matrix.map_mul]
  have c2 : ∀ Z Z' : Matrix (Fin n) (Fin r) E, (cT (sigR (AF F) σ) (adMat F Z) * JR (F := F) (AF F) J :
      Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) * adMat F Z' = adMat F (cT (σ : E →+* E) Z * J * Z') := fun Z Z' => by
    rw [c3]; simp only [adMat, Matrix.map_mul]
  have hsd : ∀ k, sigR (AF F) σ (d k).1 = (d k).1 := fun k =>
    congrArg ((archUnitF F (stepSum S u k) : AF F) ⊗ₜ[F] ·) (map_one σ)
  obtain ⟨m, hm, hX, hY, he⟩ := exists_unit_torus (s := sigR (AF F) σ) (J := JR (F := F) (AF F) J) (X := adMat F X)
    (Y := adMat F Y)
    (fun a => by
      induction a using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (sigma_sigma h x))
    ((c1 J).trans (congrArg (adMat F) (Matrix.ext fun i j => hJ.1 i j)))
    ((c2 X X).trans (hW.xx ▸ Matrix.map_zero _ (map_zero _))) ((c2 Y Y).trans (hW.yy ▸ Matrix.map_zero _ (map_zero _)))
    ((c2 X Y).trans (hW.xy ▸ Matrix.map_one _ (map_zero _) (map_one _))) d hsd
  have key : a = ⟨m, hm⟩ := by
    refine ext_inf_fin σ J ?_ ?_
    · refine GInf_ext σ J fun w => ?_
      rw [projInfArch_projInf σ J w a, projInfArch_projInf σ J w (⟨m, hm⟩ : GAd σ J)]
      obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
      apply (archEquiv J h τ).injective
      apply Subtype.ext
      apply Units.ext
      rw [← GlobalTheory.Orb.archMat_eq_archEquiv J h, ← GlobalTheory.Orb.archMat_eq_archEquiv J h]
      obtain ⟨hA1, hA2, hA3⟩ := harch w τ
      rw [eq_of_frame τ.1 (P := cT (σ : E →+* E) X * J) (Q := cT (σ : E →+* E) Y * J) hW.xx hW.xy (yx h hJ hW) hW.yy
        hA1 hA2 hA3]
      let φ := (infEmb τ).comp (compInf F E w)
      have h0 : ∀ x : E, φ (inclR (F := F) (AF F) x) = τ.1 x := fun x => by
        change infEmb τ (evInf F w 1 ⊗ₜ[F] x) = _
        simp
      have h2 : ∀ {p q : ℕ} (Z : Matrix (Fin p) (Fin q) E), (adMat F Z).map φ = Z.map τ.1 := fun Z =>
        Matrix.ext fun i j => h0 _
      have h3 : GlobalTheory.Orb.archMat σ J τ (projArch σ J w ⟨m, hm⟩) = m.1.map φ := rfl
      have hd1 : ∀ k, φ (d k).1 = (Real.exp (stepSum S u k) : ℂ) := fun k => infEmb_archUnit h τ _
      have hd2 : ∀ k, φ (d k)⁻¹.1 = (Real.exp (stepSum S u k) : ℂ)⁻¹ := fun k => by
        rw [map_units_inv φ (d k), hd1]
      have hR : m.1.map φ = 1 + X.map τ.1 * diagonal (fun i => (Real.exp (stepSum S u i) : ℂ) - 1) *
          (cT (σ : E →+* E) Y * J).map τ.1 +
          Y.map τ.1 * diagonal (fun i => (Real.exp (stepSum S u i) : ℂ)⁻¹ - 1) * (cT (σ : E →+* E) X * J).map τ.1 := by
        conv_lhs => rw [he, c3, c3, Matrix.map_add _ (map_add φ), Matrix.map_add _ (map_add φ), Matrix.map_mul,
          Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_one _ (map_zero φ) (map_one φ), h2, h2, h2, h2,
          diagonal_map (map_zero φ), diagonal_map (map_zero φ)]
        simp only [map_sub, map_one, hd1, hd2]
      have hD : ∀ f : Fin r → ℂ, diagonal f - 1 = diagonal (fun i => f i - 1) := fun f => by
        rw [← diagonal_one, diagonal_sub]
      rw [h3, hR, hD, hD]
    · have e1 : projFin σ J a = 1 := matHom_injective _ σ J (by rw [map_one]; exact MonoidHom.mem_ker.1 hfin)
      have e2 : projFin σ J ⟨m, hm⟩ = 1 := matHom_injective _ σ J (by
        rw [map_one]
        refine Units.ext (Matrix.ext fun i j => ?_)
        let ψ := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
        have h1 : ∀ k, ψ (d k).1 = 1 := fun k => rfl
        have h2 : ∀ k, ψ (d k)⁻¹.1 = 1 := fun k => rfl
        change ψ (m.1 i j) = (1 : Matrix (Fin n) (Fin n) _) i j
        rw [he]
        simp only [Matrix.add_apply, Matrix.mul_apply (N := cT _ _ * _), mul_diagonal, map_add, map_sum, map_mul, map_sub,
          h1, h2, map_one, sub_self, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Matrix.one_apply, apply_ite ψ,
          map_zero])
      rw [e1, e2]
  subst key
  have hc : ∀ k, conjUnit σ (d k) = d k := fun k => Units.ext (hsd k)
  have hperp : ∀ (Z : Matrix (Fin n) (Fin r) E) (z : Fin n → AF F ⊗[F] E), z ∈ colPerp σ J Z Set.univ →
      (cT (sigR (AF F) σ) (adMat F Z) * JR (F := F) (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) *ᵥ z = 0 :=
    fun Z z hz => by
      rw [c3]
      funext i
      have := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hz i) (Set.mem_univ i)
      exact LinearMap.mem_ker.1 this
  refine ⟨hX, ?_, fun z hz => ?_⟩
  · change m.1 * adMat F Y = adMat F Y * diagonal (fun k => (((conjUnit σ (d k))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E))
    simp only [hc]
    exact hY
  · change m.1 *ᵥ z = z
    rw [he, add_mulVec, add_mulVec, ← mulVec_mulVec, hperp Y z hz.2, mulVec_zero, ← mulVec_mulVec, hperp X z hz.1]
    simp

end GlobalTheory.IdTorus
