import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumDiagonalIntegralRationalHeisenbergStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicModuleNormRationalUnitEqOneStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.ThetaSiegelRat

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem inclR_injective : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)

theorem incM_injective {m n : Type} : Function.Injective (incM F : Matrix m n E → Matrix m n (AE F E)) :=
  fun _ _ h => Matrix.map_injective inclR_injective h

theorem psi_half_rat (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {ι : Type} [Fintype ι] (a1 a2 b1 b2 : ι → F) :
    ψ (⅟(2 : AF F) * ((fun i => algebraMap F (AF F) (a1 i)) ⬝ᵥ (fun i => algebraMap F (AF F) (b2 i)) -
      (fun i => algebraMap F (AF F) (b1 i)) ⬝ᵥ (fun i => algebraMap F (AF F) (a2 i)))) = 1 := by
  have h2 : ⅟(2 : AF F) = algebraMap F (AF F) (1 / 2) := by
    apply invOf_eq_right_inv
    rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]
    norm_num
  have e : ⅟(2 : AF F) * ((fun i => algebraMap F (AF F) (a1 i)) ⬝ᵥ (fun i => algebraMap F (AF F) (b2 i)) -
      (fun i => algebraMap F (AF F) (b1 i)) ⬝ᵥ (fun i => algebraMap F (AF F) (a2 i))) =
      algebraMap F (AF F) (1 / 2 * (a1 ⬝ᵥ b2 - b1 ⬝ᵥ a2)) := by
    simp only [dotProduct, map_sub, map_mul, map_sum, h2]
  rw [e]
  exact hψ.2.1 _

end SlopeTestRemainingChoices

theorem schr_schr' {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add, add_assoc, ← mul_assoc,
    ← AddChar.map_add_eq_mul, add_dotProduct, dotProduct_add]
  congr 2
  have h : ⅟(2 : R) * 2 = 1 := invOf_mul_self 2
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * h

theorem fromCols_add' {R : Type} [Add R] {m n₁ n₂ : Type} (x z : Matrix m n₁ R) (y w : Matrix m n₂ R) :
    Matrix.fromCols x y + Matrix.fromCols z w = Matrix.fromCols (x + z) (y + w) := by
  ext i j; rcases j with j | j <;> rfl

theorem mul_diagCols_transpose {R : Type} [CommRing R] {a b : ℕ} (z : Matrix (Fin a) (Fin b) R) :
    z * (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) R)ᵀ = Matrix.fromCols z z := by
  rw [diagCols, Matrix.transpose_fromRows, Matrix.transpose_one, Matrix.mul_fromCols, Matrix.mul_one]

end GlobalTheory.ThetaSiegelRat

namespace GlobalTheory.ThetaSiegelRat

section Mat

variable {K L : Type} [Field K] [CommRing L] {a b : ℕ}

theorem stab_blocks (f : K →+* L) (P Q R S : Matrix (Fin b) (Fin b) K) (T : Matrix (Fin b) (Fin b) L)
    (h : (Matrix.fromBlocks P Q R S).map f * (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) L) = (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) L) * T) :
    (P + Q).map f = T ∧ (R + S).map f = T := by
  have h1 : (Matrix.fromBlocks P Q R S * (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) K)).map f = (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) L) * T := by
    rw [Matrix.map_mul]
    have hd : (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) K).map f = (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) L) := by
      rw [diagCols, Matrix.fromRows_map, Matrix.map_one _ (map_zero f) (map_one f)]; rfl
    rw [hd]; exact h
  unfold diagCols at h1
  simp only [Matrix.fromBlocks_mul_fromRows, Matrix.mul_one, Matrix.fromRows_mul, Matrix.one_mul,
    Matrix.fromRows_map] at h1
  exact Matrix.fromRows_inj h1

theorem diff_inv (P Q R S P₂ Q₂ R₂ S₂ : Matrix (Fin b) (Fin b) K)
    (h : Matrix.fromBlocks P Q R S * Matrix.fromBlocks P₂ Q₂ R₂ S₂ = 1) (hd : P + Q = R + S) :
    (P₂ - R₂)ᵀ * (P - R)ᵀ = 1 := by
  rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one] at h
  obtain ⟨e1, -, e3, -⟩ := Matrix.fromBlocks_inj.mp h
  have e : (P - R) * (P₂ - R₂) = (P * P₂ + Q * R₂) - (R * P₂ + S * R₂) - ((P + Q) - (R + S)) * R₂ := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul]; abel
  rw [← Matrix.transpose_mul, e, e1, e3, hd, sub_self, Matrix.zero_mul, sub_zero, sub_zero, Matrix.transpose_one]

theorem row_decomp (x : Matrix (Fin a) (Fin b) K) (P Q R S : Matrix (Fin b) (Fin b) K) :
    Matrix.fromCols x (0 : Matrix (Fin a) (Fin b) K) * (Matrix.fromBlocks P Q R S)ᵀ =
      Matrix.fromCols (x * (P - R)ᵀ) (0 : Matrix (Fin a) (Fin b) K) + Matrix.fromCols (x * Rᵀ) (x * Rᵀ) := by
  rw [Matrix.fromBlocks_transpose, Matrix.fromCols_mul_fromBlocks, fromCols_add']
  congr 1
  · rw [Matrix.transpose_sub, Matrix.mul_sub]; simp
  · simp

theorem map_row (f : K →+* L) (x : Matrix (Fin a) (Fin b) K) (M : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) K) :
    Matrix.fromCols (x.map f) (0 : Matrix (Fin a) (Fin b) L) * (M.map f)ᵀ = (Matrix.fromCols x (0 : Matrix (Fin a) (Fin b) K) * Mᵀ).map f := by
  rw [Matrix.map_mul, Matrix.fromCols_map, Matrix.transpose_map, Matrix.map_zero _ (map_zero f)]

theorem map_decomp (f : K →+* L) (x y : Matrix (Fin a) (Fin b) K) :
    (Matrix.fromCols x (0 : Matrix (Fin a) (Fin b) K) + Matrix.fromCols y y).map f =
      Matrix.fromCols (x.map f) (0 : Matrix (Fin a) (Fin b) L) + Matrix.fromCols (y.map f) (y.map f) := by
  rw [Matrix.map_add _ (map_add f), Matrix.fromCols_map, Matrix.fromCols_map, Matrix.map_zero _ (map_zero f)]

end Mat

end GlobalTheory.ThetaSiegelRat

namespace GlobalTheory.ThetaSiegelRat

theorem cocycle_one {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {κ : Type} [Fintype κ]
    (v1 v2 z1 z2 : κ → F) :
    ψ (⅟(2 : AF F) * (Sum.elim (fun i => algebraMap F (AF F) (v1 i)) (fun i => algebraMap F (AF F) (v1 i)) ⬝ᵥ
        Sum.elim (fun i => algebraMap F (AF F) (z2 i)) 0 -
      Sum.elim (fun i => algebraMap F (AF F) (z1 i)) 0 ⬝ᵥ
        Sum.elim (fun i => algebraMap F (AF F) (v2 i)) (-fun i => algebraMap F (AF F) (v2 i)))) = 1 := by
  rw [sumElim_dotProduct_sumElim, sumElim_dotProduct_sumElim, dotProduct_zero, zero_dotProduct,
    add_zero, add_zero]
  exact psi_half_rat ψ hψ v1 v2 z1 z2

theorem exists_ratCoord {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (hE : Module.finrank F E = 2) {a b : ℕ} {κ : Type} [Fintype κ] (hκ : Fintype.card κ = a * b)
    {B : Matrix (Fin a) (Fin b) (AE F E) → Matrix (Fin a) (Fin b) (AE F E) → AF F} (d : Darboux B κ)
    (hrat : ∀ x : Matrix (Fin a) (Fin b) E, ∃ y z : κ → F,
      d.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) :
    ∃ r : Matrix (Fin a) (Fin b) E ≃ (κ → F) × (κ → F), ∀ x,
      d.e (incM F x) = (fun i => algebraMap F (AF F) ((r x).1 i), fun i => algebraMap F (AF F) ((r x).2 i)) := by
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hE]; norm_num)
  let L : Matrix (Fin a) (Fin b) E →ₗ[F] (κ → AF F) × (κ → AF F) :=
    (d.e.toLinearMap.restrictScalars F).comp
      ((Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E).toLinearMap.mapMatrix)
  have hLx : ∀ x, L x = d.e (incM F x) := fun x => rfl
  let g : (κ → F) →ₗ[F] (κ → AF F) := (Algebra.linearMap F (AF F)).compLeft κ
  let Qm : ((κ → F) × (κ → F)) →ₗ[F] (κ → AF F) × (κ → AF F) := g.prodMap g
  have hQx : ∀ u : (κ → F) × (κ → F),
      Qm u = (fun i => algebraMap F (AF F) (u.1 i), fun i => algebraMap F (AF F) (u.2 i)) := fun u => rfl
  have hg : Function.Injective g := fun u v h =>
    funext fun i => AdeleRing.algebraMap_injective (𝓞 F) F (congrFun h i)
  have hQ : Function.Injective Qm := fun u v h =>
    Prod.ext (hg (congrArg Prod.fst h)) (hg (congrArg Prod.snd h))
  have hL : ∀ x, L x ∈ LinearMap.range Qm := fun x => by
    obtain ⟨y, z, h⟩ := hrat x
    exact ⟨(y, z), by rw [hQx, hLx, h]⟩
  let r₀ : Matrix (Fin a) (Fin b) E →ₗ[F] (κ → F) × (κ → F) :=
    (LinearEquiv.ofInjective Qm hQ).symm.toLinearMap ∘ₗ L.codRestrict (LinearMap.range Qm) hL
  have hr₀ : ∀ x, Qm (r₀ x) = L x := fun x => by
    rw [← LinearEquiv.ofInjective_apply (h := hQ) Qm (r₀ x)]
    simp [r₀]
  have hinj : Function.Injective r₀ := fun x y h => by
    have h1 : d.e (incM F x) = d.e (incM F y) := by rw [← hLx, ← hLx, ← hr₀, ← hr₀, h]
    exact incM_injective (d.e.injective h1)
  have hsurj : Function.Surjective r₀ := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj
    rw [Module.finrank_matrix, Module.finrank_prod, Module.finrank_fintype_fun_eq_card, hE, hκ]
    simp only [Fintype.card_fin]
    ring
  refine ⟨Equiv.ofBijective r₀ ⟨hinj, hsurj⟩, fun x => ?_⟩
  rw [← hLx, ← hr₀]
  rfl

end GlobalTheory.ThetaSiegelRat

open GlobalTheory.ThetaSiegelRat in

theorem GlobalTheory.ThetaSiegelRat.thetaSum_omd_of_fix_diag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (a b : ℕ) (JA : Matrix (Fin a) (Fin a) E) (JB : Matrix (Fin b) (Fin b) E) (κ : Type) [Fintype κ], Fintype.card κ = a * b → ∀ (d : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F JB)) κ), (∀ x : Matrix (Fin a) (Fin b) E, ∃ y z : κ → F, d.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) → ∀ (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (dbl (incM F JB))) (κ ⊕ κ)), IsDblCoord (cA σ) (-1) (incM F JA) (incM F JB) d dd → ∀ (χ : Chr F E), IsHecke F E χ → ∀ (omd : UG (cA σ) (dbl (incM F JB)) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)), IsSplitting (adeleClass F) ψ dd (actB (cA σ)) omd → SiegelRule (cA σ) (adeleClass F) ψ (-1) (incM F JA) (dbl (incM F JB)) dd χ (diagCols (Fin b)) omd → ∀ (p : UG (cA σ) (dbl (incM F JB))) (p₀ : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E), ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) = incM F p₀ → ∀ (t : GL (Fin b) (AE F E)), ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) * diagCols (Fin b) = diagCols (Fin b) * (t : Matrix (Fin b) (Fin b) (AE F E)) → ∀ φ ∈ schA F (κ ⊕ κ), thetaSum F (omd p φ) = thetaSum F φ := by
  intro F E _ _ _ _ _ σ hσ ψ hψ a b JA JB κ _ hκ d hrat dd hdd χ hχ omd hS hR p p₀ hp t ht φ hφ
  obtain ⟨P, Q, R, S, rfl⟩ : ∃ P Q R S, p₀ = Matrix.fromBlocks P Q R S :=
    ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks p₀).symm⟩
  have hNT : Nontrivial (AE F E) := (inclR_injective (F := F) (E := E)).nontrivial

  obtain ⟨htP, htR⟩ := stab_blocks (inclR (F := F) (E := E) (AF F)) P Q R S t.1 (by rw [hp] at ht; exact ht)
  have hPQ : P + Q = R + S := incM_injective (F := F) (htP.trans htR.symm)

  have hdett : ((Matrix.GeneralLinearGroup.det t : (AE F E)ˣ) : AE F E) = inclR (F := F) (AF F) (P + Q).det := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, ← htP, RingHom.map_det]; rfl
  have hz : (P + Q).det ≠ 0 := fun h0 => by
    have := (Matrix.GeneralLinearGroup.det t).ne_zero
    rw [hdett, h0, map_zero] at this
    exact this rfl
  have hχ1 : χ (Matrix.GeneralLinearGroup.det t) = 1 := by
    have e : Matrix.GeneralLinearGroup.det t = Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 _ hz) :=
      Units.ext (by rw [hdett]; rfl)
    rw [e]
    exact hχ.2 _
  have hmod := GlobalTheory.T.adelicModule_norm_rationalUnit_eq_one F E (Matrix.GeneralLinearGroup.det t) _ hdett

  have hdiag : ∀ (y : Matrix (Fin a) (Fin b) (AE F E)), ∀ φ' ∈ schA F (κ ⊕ κ),
      GlobalTheory.DiagForm.lDiag F κ (dd.rho ψ (Matrix.fromCols y y) φ') = GlobalTheory.DiagForm.lDiag F κ φ' := by
    intro y φ' hφ'
    rw [Darboux.rho, hdd]
    exact GlobalTheory.DiagForm.lDiag_schr ψ _ _ hφ'
  have hsieg : ∀ φ' ∈ schA F (κ ⊕ κ), GlobalTheory.DiagForm.lDiag F κ (omd p φ') = GlobalTheory.DiagForm.lDiag F κ φ' := by
    intro φ' hφ'
    have := hR (GlobalTheory.DiagForm.lDiag F κ) GlobalTheory.DiagForm.lDiag_adm (fun z φ'' hφ'' => by
      erw [mul_diagCols_transpose]; exact hdiag z φ'' hφ'') p t ht φ' hφ'
    rw [this, hχ1, hmod]
    simp

  obtain ⟨r, hr⟩ := exists_ratCoord hσ.2.2.1 hκ d hrat
  have hdetp : ((Matrix.GeneralLinearGroup.det (p : GL (Fin b ⊕ Fin b) (AE F E)) : (AE F E)ˣ) : AE F E) =
      inclR (F := F) (AF F) (Matrix.fromBlocks P Q R S).det := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hp, RingHom.map_det]; rfl
  have hzp : (Matrix.fromBlocks P Q R S).det ≠ 0 := fun h0 => by
    have := (Matrix.GeneralLinearGroup.det (p : GL (Fin b ⊕ Fin b) (AE F E))).ne_zero
    rw [hdetp, h0, map_zero] at this
    exact this rfl
  have hpq : Matrix.fromBlocks P Q R S * (Matrix.fromBlocks P Q R S)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hzp)
  obtain ⟨P₂, Q₂, R₂, S₂, hq⟩ : ∃ P₂ Q₂ R₂ S₂, (Matrix.fromBlocks P Q R S)⁻¹ = Matrix.fromBlocks P₂ Q₂ R₂ S₂ :=
    ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks _).symm⟩
  rw [hq] at hpq
  have hKK : (P₂ - R₂)ᵀ * (P - R)ᵀ = 1 := diff_inv P Q R S P₂ Q₂ R₂ S₂ hpq hPQ
  have hKK' : (P - R)ᵀ * (P₂ - R₂)ᵀ = 1 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).mp hKK
  let T : Matrix (Fin a) (Fin b) E ≃ Matrix (Fin a) (Fin b) E :=
    { toFun := fun x => x * (P - R)ᵀ
      invFun := fun z => z * (P₂ - R₂)ᵀ
      left_inv := fun x => by simp only [Matrix.mul_assoc, hKK', Matrix.mul_one]
      right_inv := fun z => by simp only [Matrix.mul_assoc, hKK, Matrix.mul_one] }
  let e := r.symm.trans (T.trans r)
  have hU : ∀ x : Matrix (Fin a) (Fin b) E,
      dd.e (Matrix.fromCols (incM F x) (0 : Matrix (Fin a) (Fin b) (AE F E))) =
        (Sum.elim (fun i => algebraMap F (AF F) ((r x).1 i)) 0, Sum.elim (fun i => algebraMap F (AF F) ((r x).2 i)) 0) := by
    intro x
    rw [hdd, hr x, map_zero]
    simp
  have key : ∀ uv : (κ → F) × (κ → F),
      GlobalTheory.DiagForm.lDiag F κ (schr ψ (Sum.elim (fun i => algebraMap F (AF F) (uv.1 i)) 0,
        Sum.elim (fun i => algebraMap F (AF F) (uv.2 i)) 0) φ) =
      GlobalTheory.DiagForm.lDiag F κ (schr ψ (Sum.elim (fun i => algebraMap F (AF F) ((e uv).1 i)) 0,
        Sum.elim (fun i => algebraMap F (AF F) ((e uv).2 i)) 0) (omd p φ)) := by
    intro uv
    obtain ⟨x, rfl⟩ := r.surjective uv
    have he : e (r x) = r (x * (P - R)ᵀ) := by simp [e, T]
    rw [he, ← hU x, ← hU (x * (P - R)ᵀ)]
    have hact : actB (cA σ) p (Matrix.fromCols (incM F x) (0 : Matrix (Fin a) (Fin b) (AE F E))) =
        Matrix.fromCols (incM F (x * (P - R)ᵀ)) (0 : Matrix (Fin a) (Fin b) (AE F E)) +
          Matrix.fromCols (incM F (x * Rᵀ)) (incM F (x * Rᵀ)) := by
      unfold actB
      rw [hp]
      have := map_row (inclR (F := F) (E := E) (AF F)) x (Matrix.fromBlocks P Q R S)
      rw [row_decomp, map_decomp] at this
      exact this
    have hsplit : ∀ φ' : (κ ⊕ κ → AF F) → ℂ,
        dd.rho ψ (Matrix.fromCols (incM F (x * (P - R)ᵀ)) (0 : Matrix (Fin a) (Fin b) (AE F E)) +
          Matrix.fromCols (incM F (x * Rᵀ)) (incM F (x * Rᵀ))) φ' =
        dd.rho ψ (Matrix.fromCols (incM F (x * Rᵀ)) (incM F (x * Rᵀ)))
          (dd.rho ψ (Matrix.fromCols (incM F (x * (P - R)ᵀ)) (0 : Matrix (Fin a) (Fin b) (AE F E))) φ') := by
      intro φ'
      simp only [Darboux.rho]
      rw [schr_schr', map_add, add_comm (dd.e (Matrix.fromCols (incM F (x * (P - R)ᵀ)) _)), hdd (incM F (x * Rᵀ)),
        hr (x * Rᵀ), hU (x * (P - R)ᵀ)]
      rw [cocycle_one ψ hψ, one_smul]
    calc GlobalTheory.DiagForm.lDiag F κ (dd.rho ψ (Matrix.fromCols (incM F x) (0 : Matrix (Fin a) (Fin b) (AE F E))) φ)
        = GlobalTheory.DiagForm.lDiag F κ (omd p (dd.rho ψ (Matrix.fromCols (incM F x) (0 : Matrix (Fin a) (Fin b) (AE F E))) φ)) :=
          (hsieg _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ _ hφ)).symm
      _ = GlobalTheory.DiagForm.lDiag F κ (dd.rho ψ (actB (cA σ) p (Matrix.fromCols (incM F x) (0 : Matrix (Fin a) (Fin b) (AE F E))))
            (omd p φ)) := by rw [hS.impl p _ φ hφ]
      _ = GlobalTheory.DiagForm.lDiag F κ (dd.rho ψ (Matrix.fromCols (incM F (x * Rᵀ)) (incM F (x * Rᵀ)))
            (dd.rho ψ (Matrix.fromCols (incM F (x * (P - R)ᵀ)) (0 : Matrix (Fin a) (Fin b) (AE F E))) (omd p φ))) := by
          rw [hact, hsplit]
      _ = GlobalTheory.DiagForm.lDiag F κ
            (dd.rho ψ (Matrix.fromCols (incM F (x * (P - R)ᵀ)) (0 : Matrix (Fin a) (Fin b) (AE F E))) (omd p φ)) :=
          hdiag _ _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ _ (hS.pres p φ hφ))

  obtain ⟨c, hc0, hc⟩ := GlobalTheory.T.hasSum_diagonalIntegral_rationalHeisenberg F ψ hψ κ
  have h1 := hc φ hφ
  have h3 := (e.hasSum_iff).mpr (hc (omd p φ) (hS.pres p φ hφ))
  have h4 : HasSum (fun uv : (κ → F) × (κ → F) => GlobalTheory.DiagForm.lDiag F κ (schr ψ
      (Sum.elim (fun i => algebraMap F (AF F) (uv.1 i)) 0, Sum.elim (fun i => algebraMap F (AF F) (uv.2 i)) 0) φ))
      (c * thetaSum F (omd p φ)) := by
    convert h3 using 1
    funext uv
    exact key uv
  exact mul_left_cancel₀ hc0 (h4.unique h1)
