import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodingerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianSplitSymplecticPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruhStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupVStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryAdelicSchwartzOfNonzeroLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartzStatement

open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB
open scoped TensorProduct Matrix GlobalTheory.VacAny GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SoLocV

theorem piW_cA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {v : Pl F} (τ : E →ₐ[F] Fv F v) (w : AE F E) : piW τ (cA σ w) = piW (τ.comp σ) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem piW_incl {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl F}
    (τ : E →ₐ[F] Fv F v) (e : E) : piW τ (inclR (F := F) (AF F) e) = τ e := by
  change GlobalTheory.AdelicU.evFin F v 1 * τ e = τ e
  simp

theorem comp_unitary {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (k : UA σ J) {v : Pl F} (t : E →ₐ[F] Fv F v) :
    ((mat k).map (piW t))ᵀ * J.map t * (mat k).map (piW (t.comp σ)) = J.map t := by
  have h : (mat k)ᵀ * incM F J * (mat k).map (cA σ) = incM F J := k.2
  have h2 : ((mat k)ᵀ * incM F J * (mat k).map (cA σ)).map (piW t) = (incM F J).map (piW t) := by rw [h]
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.map_map] at h2
  have e1 : (piW t ∘ cA σ) = piW (t.comp σ) := funext fun w => piW_cA t w
  have e2 : (incM F J).map (piW t) = J.map t := Matrix.ext fun i j => piW_incl t (J i j)
  rw [e1, e2] at h2
  exact h2

theorem exists_comp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (k : UA σ J) {v : Pl F} (t : E →ₐ[F] Fv F v) (hJ : IsUnit (J.map t).det) :
    ∃ g : GL (Fin n) (Fv F v), (mat k).map (piW t) = g.val ∧
      (mat k).map (piW (t.comp σ)) = (J.map t)⁻¹ * ((g⁻¹ : GL (Fin n) (Fv F v)).val)ᵀ * J.map t := by
  set P := (mat k).map (piW t) with hP
  set P' := (((k.1)⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)).map (piW t) with hP'
  set Q := (mat k).map (piW (t.comp σ)) with hQ
  have hm1 : mat k * (((k.1)⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) = 1 := Units.mul_inv k.1
  have hm2 : (((k.1)⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) * mat k = 1 := Units.inv_mul k.1
  have h1 : P * P' = 1 := by
    rw [hP, hP', ← Matrix.map_mul, hm1, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : P' * P = 1 := by
    rw [hP, hP', ← Matrix.map_mul, hm2, Matrix.map_one _ (map_zero _) (map_one _)]
  let g : GL (Fin n) (Fv F v) := ⟨P, P', h1, h2⟩
  refine ⟨g, rfl, ?_⟩
  have hu : Pᵀ * J.map t * Q = J.map t := comp_unitary J k t
  have e : P'ᵀ * J.map t = J.map t * Q := by
    calc P'ᵀ * J.map t = P'ᵀ * (Pᵀ * J.map t * Q) := by rw [hu]
      _ = (P * P')ᵀ * J.map t * Q := by rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = J.map t * Q := by rw [h1, Matrix.transpose_one, Matrix.one_mul]
  have hg : ((g⁻¹ : GL (Fin n) (Fv F v)).val) = P' := rfl
  rw [hg, Matrix.mul_assoc, e, Matrix.nonsing_inv_mul_cancel_left _ _ hJ]

theorem linForm_eq {K : Type} [Field K] {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (l : Matrix m n K →ₗ[K] K) (Y : Matrix m n K) :
    l Y = ∑ k, ∑ j, Y k j * l (Matrix.single k j 1) := by
  conv_lhs => rw [Y.matrix_eq_sum_single]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show Matrix.single k j (Y k j) = Y k j • Matrix.single k j (1 : K) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul]

theorem sum_transpose_mul {K : Type} [CommRing K] {m n : Type} [Fintype m] [Fintype n]
    (g : Matrix m m K) (Y L : Matrix m n K) :
    ∑ k, ∑ j, (gᵀ * Y) k j * L k j = ∑ k, ∑ j, Y k j * (g * L) k j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  calc _ = ∑ x, ∑ i, ∑ j, g i x * Y i j * L x j := Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ i, ∑ x, ∑ j, g i x * Y i j * L x j := Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ x, g i x * Y i j * L x j := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun x _ => by ring

theorem at_hTens {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {v : Pl F} {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E)
    (x u : Matrix (Fin m) (Fin n) (AE F E)) (hx : At (evFin F v) x) :
    At (evFin F v) ((-1 : AE F E) * hTens (cA σ) (incM F JA) (incM F JB) x u) := by
  intro r hr
  have h : ∀ i j, r • x i j = 0 := fun i j => by
    have := congrFun (congrFun (hx r hr) i) j
    simpa using this
  rw [← mul_smul_comm]
  unfold hTens
  simp only [Finset.smul_sum, ← smul_mul_assoc, h, zero_mul, Finset.sum_const_zero, mul_zero]

theorem heis_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : Base F E) (Γ : Geo σ a a') (X : Chars F E) (om : Rep σ Γ.V Γ.W) (om' : Rep σ Γ.V' Γ.W), IsTriple Bs Γ X om om' →
    ∀ (k : UA σ Γ.V'.J) (g : GL (Fin a') (Fv F Bs.v₁)), k ∈ UAt σ Γ.V' (evFin F Bs.v₁) →
    (mat k).map (piW Bs.τ₁) = g.val →
    (mat k).map (piW (Bs.τ₁.comp σ)) = (Γ.V'.J.map Bs.τ₁)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * Γ.V'.J.map Bs.τ₁ →
    ∀ (S : ((Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ) → (Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ),
    (∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F Bs.v₁), S φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ (γ : Matrix (Fin a') (Fin (a + a')) (AE F E)), At (evFin F Bs.v₁) γ →
      ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F Bs.v₁),
        S (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ) =
          GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁)
            (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ (GlobalTheory.WeilM.actAB (cA σ) (k, (1 : UA σ Γ.W.J)) γ)) (S φ)) →
    Continuous (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) ∧ GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁ ≠ 1 ∧
    ∃ (wT : Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) → (Fin a' × Fin (a + a') → Fv F Bs.v₁) × (Fin a' × Fin (a + a') → Fv F Bs.v₁))
      (wM : (Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) →ₗ[Fv F Bs.v₁] Fv F Bs.v₁) → (Fin a' × Fin (a + a') → Fv F Bs.v₁) × (Fin a' × Fin (a + a') → Fv F Bs.v₁)),
    ∀ ι, Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι →
      (∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F Bs.v₁), ι (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wT C) φ) = fun Y => ι φ (Y + C)) ∧
      (∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F Bs.v₁), ι (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wM l) φ) = fun Y => GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁ (l Y) * ι φ Y) ∧
      (∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F Bs.v₁), ι (S (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wT C) φ)) =
        fun Y => ι (S φ) (Y + ((g⁻¹ : GL (Fin a') (Fv F Bs.v₁)).val)ᵀ * C)) ∧
      (∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F Bs.v₁), ι (S (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wM l) φ)) =
        fun Y => GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁ (l (g.valᵀ * Y)) * ι (S φ) Y) := by
  intro F E _ _ _ _ _ σ a a' Bs Γ X om om' hT k g hk hP hQ S hSB h4
  have hcm : IsCMExt F E σ := hT.base.cm
  have hstd := hT.base.std
  refine ⟨GlobalTheory.SchrSB.continuous_psiAt _ hstd.1 _, GlobalTheory.PsiNontriv.psiAt_ne_one _ hstd _, ?_⟩
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdV : Γ.V'.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hT.geo.hV'.sig w)
    have e : (Γ.V'.J.map (Bs.emb w).1).det = (Bs.emb w).1 Γ.V'.J.det := (RingHom.map_det _ _).symm
    rw [e, h0, map_zero]
  have hdW : Γ.W.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hT.geo.hW.sig w)
    have e : (Γ.W.J.map (Bs.emb w).1).det = (Bs.emb w).1 Γ.W.J.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_smul, e, h0, map_zero, mul_zero]
  set A := Γ.V'.J.map Bs.τ₁ with hAdef
  set B := Γ.W.J.map Bs.τ₁ with hBdef
  have hA : IsUnit A.det := by
    have e : A.det = (Bs.τ₁ : E →+* Fv F Bs.v₁) Γ.V'.J.det := (RingHom.map_det _ _).symm
    rw [e]
    exact isUnit_iff_ne_zero.2 fun h => hdV ((Bs.τ₁ : E →+* Fv F Bs.v₁).injective (by rw [map_zero]; exact h))
  have hB : IsUnit Bᵀ.det := by
    have e : B.det = (Bs.τ₁ : E →+* Fv F Bs.v₁) Γ.W.J.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_transpose, e]
    exact isUnit_iff_ne_zero.2 fun h => hdW ((Bs.τ₁ : E →+* Fv F Bs.v₁).injective (by rw [map_zero]; exact h))
  choose U hUat hU0 hU1 using fun (P₀ P₁ : Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁)) =>
    GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hcm Bs.v₁ Bs.τ₁ P₀ P₁
  let Pm : Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) → Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) :=
    fun C => -(A⁻¹ * C * (Bᵀ)⁻¹)
  let Lm : (Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) →ₗ[Fv F Bs.v₁] Fv F Bs.v₁) →
      Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) := fun l => Matrix.of fun k j => l (Matrix.single k j 1)
  have hcoP : ∀ C, -(A * (U 0 (Pm C)).map (piW (Bs.τ₁.comp σ)) * Bᵀ) = C := by
    intro C
    rw [hU1]
    simp only [Pm, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ hB, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hA]
  have hsymp : ∀ x u : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F Bs.v₁) x → x.map (piW Bs.τ₁) = 0 →
      u.map (piW (Bs.τ₁.comp σ)) = 0 →
      Bs.ψ (symp (R := AF F) (cA σ) (-1) (incM F Γ.V'.J) (incM F Γ.W.J) x u) =
        GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁
          (-(∑ k, ∑ j, (-(A * x.map (piW (Bs.τ₁.comp σ)) * Bᵀ)) k j * u.map (piW Bs.τ₁) k j)) := by
    intro x u hx hx0 hu1
    unfold symp
    rw [GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm Bs.v₁ Bs.τ₁ _ (at_hTens _ _ x u hx)]
    rw [map_mul, map_mul, map_neg, map_neg, map_one, map_one, neg_one_mul, neg_one_mul, ← neg_add,
      GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair hcm Bs.τ₁ Γ.V'.J Γ.W.J hT.geo.hV'.herm hT.geo.hW.skew x u hx0 hu1]
    rfl
  refine ⟨fun C => GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ (U 0 (Pm C)),
    fun l => GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ (U (-Lm l) 0), ?_⟩
  intro ι hι
  have hL := hι
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLinBar at hL
  simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at hL
  have htr := hL.trans
  have hmu := hL.mult
  have hK' : ∀ (u : Matrix (Fin a') (Fin (a + a')) (AE F E)),
      GlobalTheory.WeilM.actAB (cA σ) (k, (1 : UA σ Γ.W.J)) u = mat k * u := by
    intro u
    simp [GlobalTheory.WeilM.actAB, mat]
  have hKat : ∀ (u : Matrix (Fin a') (Fin (a + a')) (AE F E)), At (evFin F Bs.v₁) u →
      At (evFin F Bs.v₁) (mat k * u) := by
    intro u hu r hr
    rw [← Matrix.mul_smul, hu r hr, Matrix.mul_zero]
  have hKmap : ∀ (u : Matrix (Fin a') (Fin (a + a')) (AE F E)) (t : E →ₐ[F] Fv F Bs.v₁),
      (mat k * u).map (piW t) = (mat k).map (piW t) * u.map (piW t) :=
    fun u t => Matrix.map_mul
  have hbr := fun (γ : Matrix (Fin a') (Fin (a + a')) (AE F E)) hγ (φ : (Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ) => GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger Γ.M'.co Bs.ψ Bs.v₁ γ hγ φ
  have hsb := fun (w : (Fin a' × Fin (a + a') → Fv F Bs.v₁) × (Fin a' × Fin (a + a') → Fv F Bs.v₁)) (φ : (Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ) (hφ : φ ∈ GlobalTheory.WeilM.SB _) => GlobalTheory.SchrSB.schr_mem_SB Bs.ψ hstd.1 Bs.v₁ w φ hφ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro C φ hφ
    funext Y
    rw [htr (U 0 (Pm C)) (hUat 0 (Pm C)) (hU0 0 (Pm C)) φ hφ _ (hsb _ φ hφ) (hbr _ (hUat 0 (Pm C)) φ) Y, hcoP]
  · intro l φ hφ
    funext Y
    have hm := hmu (U (-Lm l) 0) (hUat (-Lm l) 0) (hU1 (-Lm l) 0) φ hφ _ (hsb _ φ hφ) (hbr _ (hUat (-Lm l) 0) φ)
      (U 0 (Pm Y)) (hUat 0 (Pm Y)) (hU0 0 (Pm Y))
    rw [hcoP] at hm
    rw [hm, hsymp _ _ (hUat 0 (Pm Y)) (hU0 0 (Pm Y)) (hU1 (-Lm l) 0), hcoP, hU0, linForm_eq l Y]
    congr 2
    simp [Lm, Finset.sum_neg_distrib]
  · intro C φ hφ
    funext Y
    rw [h4 _ (hUat 0 (Pm C)) φ hφ, hK']
    have hat := hKat _ (hUat 0 (Pm C))
    rw [htr _ hat (by rw [hKmap, hU0, Matrix.mul_zero]) _ (hSB φ hφ) _ (hsb _ _ (hSB φ hφ)) (hbr _ hat _) Y]
    congr 2
    rw [hKmap, hQ, hU1]
    simp only [Pm, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ hB, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hA,
      Matrix.mul_nonsing_inv_cancel_left _ _ hA]
  · intro l φ hφ
    funext Y
    rw [h4 _ (hUat (-Lm l) 0) φ hφ, hK']
    have hat := hKat _ (hUat (-Lm l) 0)
    have h1 : (mat k * U (-Lm l) 0).map (piW (Bs.τ₁.comp σ)) = 0 := by
      rw [hKmap, hU1, Matrix.mul_zero]
    have hm := hmu _ hat h1 _ (hSB φ hφ) _ (hsb _ _ (hSB φ hφ)) (hbr _ hat _) (U 0 (Pm Y)) (hUat 0 (Pm Y)) (hU0 0 (Pm Y))
    rw [hcoP] at hm
    rw [hm, hsymp _ _ (hUat 0 (Pm Y)) (hU0 0 (Pm Y)) h1, hcoP, hKmap, hP, hU0, linForm_eq l]
    congr 2
    rw [show (∑ k, ∑ j, ((g : Matrix (Fin a') (Fin a') (Fv F Bs.v₁))ᵀ * Y) k j * l (Matrix.single k j 1)) =
      ∑ k, ∑ j, ((g : Matrix (Fin a') (Fin a') (Fv F Bs.v₁))ᵀ * Y) k j * Lm l k j from rfl, sum_transpose_mul]
    simp [Matrix.mul_neg, Finset.sum_neg_distrib]

theorem soLoc_stable : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {a a' : ℕ}
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ k ∈ UAt σ G.V' (evFin F B.v₁), ∀ φ ∈ G.M'.SoLoc B.ψ B.τ₁, ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁),
      Acts (evFin F B.v₁) (om' (k, 1)) φ φ₁ → φ₁ ∈ G.M'.SoLoc B.ψ B.τ₁ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT k hk φ hφ φ₁ hφ₁ hA
  obtain ⟨hφSB, ι, hι, hsupp⟩ := hφ
  refine ⟨hφ₁, ι, hι, fun Y hY => ?_⟩
  have hJ : IsUnit (G.V'.J.map B.τ₁).det := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have h0 : G.V'.J.det ≠ 0 := by
      intro h0
      apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hT.geo.hV'.sig w)
      have e : (G.V'.J.map (B.emb w).1).det = (B.emb w).1 G.V'.J.det := (RingHom.map_det _ _).symm
      rw [e, h0, map_zero]
    have e : (G.V'.J.map B.τ₁).det = (B.τ₁ : E →+* Fv F B.v₁) G.V'.J.det := (RingHom.map_det _ _).symm
    rw [e]
    exact isUnit_iff_ne_zero.2 fun h => h0 ((B.τ₁ : E →+* Fv F B.v₁).injective (by rw [map_zero]; exact h))
  obtain ⟨g, hP, hQ⟩ := exists_comp G.V'.J k B.τ₁ hJ
  obtain ⟨S, hS⟩ := GlobalTheory.T.weilRepresentationLocality_unitaryGroupV' B G X om om' hT B.v₁ k hk
  have h1 : ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁), S φ ∈ SB _ := fun φ hφ => (hS φ hφ).1
  have hSplit := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil'
  have pres : ∀ p Φ, Φ ∈ GlobalTheory.WeilM.schA F _ → om' p Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun p Φ hΦ => hSplit.pres p Φ hΦ
  have restS : ∀ φ r, φ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁) → Rest (evFin F B.v₁) φ r →
      Rest (evFin F B.v₁) (S φ) r := fun φ r hφ hr =>
    ⟨hr.1, by rw [← (hS φ hφ).2 r hr]; exact pres _ _ hr.2⟩
  have hvac := hT.geo.hM'.vac B.v₁
  have hlin : ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁), ∀ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁), ∀ c : ℂ,
      S (c • φ + φ') = c • S φ + S φ' := by
    intro φ hφ φ' hφ' c
    refine GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq B.v₁ (G.M'.vac B.v₁) _ _ hvac.1 fun r hr => ?_
    have hsum : c • φ + φ' ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁) :=
      Submodule.add_mem _ (Submodule.smul_mem _ c hφ) hφ'
    have r0 := GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local B.v₁ _ _ r hvac.2.1 hsum hr
    have r1 := GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local B.v₁ _ _ r hvac.2.1 hφ hr
    have r2 := GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local B.v₁ _ _ r hvac.2.1 hφ' hr
    have et : ∀ (ψ₁ ψ₂ : (Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ), tens (evFin F B.v₁) (c • ψ₁ + ψ₂) r =
        c • tens (evFin F B.v₁) ψ₁ r + tens (evFin F B.v₁) ψ₂ r := fun ψ₁ ψ₂ => by
      funext x; simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [← (hS _ hsum).2 r r0, et, map_add, map_smul, (hS φ hφ).2 r r1, (hS φ' hφ').2 r r2, et]
  have hψ : Continuous B.ψ := hT.base.std.1
  have atAct : ∀ (γ : Matrix (Fin a') (Fin (a + a')) (AE F E)), At (evFin F B.v₁) γ →
      At (evFin F B.v₁) (GlobalTheory.WeilM.actAB (cA σ) (k, (1 : UA σ G.W.J)) γ) := by
    intro γ hγ u hu
    simp only [GlobalTheory.WeilM.actAB]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hγ u hu, Matrix.mul_zero, Matrix.zero_mul]
  have h4 : ∀ (γ : Matrix (Fin a') (Fin (a + a')) (AE F E)), At (evFin F B.v₁) γ →
      ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁),
        S (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (GlobalTheory.LatVac.locCo G.M'.co B.v₁ γ) φ) =
          GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁)
            (GlobalTheory.LatVac.locCo G.M'.co B.v₁ (GlobalTheory.WeilM.actAB (cA σ) (k, (1 : UA σ G.W.J)) γ)) (S φ) := by
    intro γ hγ φ hφ
    have hw := GlobalTheory.SchrSB.schr_mem_SB B.ψ hψ B.v₁ (GlobalTheory.LatVac.locCo G.M'.co B.v₁ γ) φ hφ
    refine GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq B.v₁ φ _ _ hφ fun r hr => ?_
    have hb1 := GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M'.co B.ψ B.v₁ γ hγ φ r hr
    have hRw : Rest (evFin F B.v₁) (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (GlobalTheory.LatVac.locCo G.M'.co B.v₁ γ) φ) r :=
      ⟨hr.1, by rw [← hb1]; exact GlobalTheory.T.weil_representation_preserves_schwartz G.M' B.ψ hT.base.std γ _ hr.2⟩
    rw [← (hS _ hw).2 r hRw, ← hb1, hSplit.impl _ _ _ hr.2, (hS φ hφ).2 r hr,
      GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M'.co B.ψ B.v₁ _ (atAct γ hγ) (S φ) r (restS φ r hφ hr)]
  have hφ₁S : φ₁ = S φ :=
    GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq B.v₁ φ φ₁ (S φ) hφSB fun r hr => by rw [← hA r hr, (hS φ hφSB).2 r hr]
  obtain ⟨hψc, hψ1, wT, wM, hops⟩ := heis_one B G X om om' hT k g hk hP hQ S h1 h4
  obtain ⟨hT0, hM0, hST0, hSM0⟩ := hops ι hι
  have hbij := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLin.bij hι
  have hU0 : ∀ (w : (Fin a' × Fin (a + a') → Fv F B.v₁) × (Fin a' × Fin (a + a') → Fv F B.v₁)),
      ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁), GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) w φ ∈ SB _ :=
    fun w => GlobalTheory.SchrSB.schr_mem_SB B.ψ hψ B.v₁ w
  have key1 : ∀ (Z : Matrix (Fin a') (Fin (a + a')) (Fv F B.v₁)),
      g.valᵀ * (((g⁻¹ : GL (Fin a') (Fv F B.v₁)).val)ᵀ * Z) = Z := by
    intro Z
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one, Matrix.one_mul]
  have key2 : ∀ (Z : Matrix (Fin a') (Fin (a + a')) (Fv F B.v₁)),
      ((g⁻¹ : GL (Fin a') (Fv F B.v₁)).val)ᵀ * (g.valᵀ * Z) = Z := by
    intro Z
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.one_mul]
  have hlin2 : ∀ x ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁), ∀ y ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁), ∀ c : ℂ,
      (fun (φ : (Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ) (Z : Matrix (Fin a') (Fin (a + a')) (Fv F B.v₁)) => ι (S φ) (((g⁻¹ : GL (Fin a') (Fv F B.v₁)).val)ᵀ * Z)) (c • x + y) =
        c • (fun (φ : (Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ) (Z : Matrix (Fin a') (Fin (a + a')) (Fv F B.v₁)) => ι (S φ) (((g⁻¹ : GL (Fin a') (Fv F B.v₁)).val)ᵀ * Z)) x +
          (fun (φ : (Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ) (Z : Matrix (Fin a') (Fin (a + a')) (Fv F B.v₁)) => ι (S φ) (((g⁻¹ : GL (Fin a') (Fv F B.v₁)).val)ᵀ * Z)) y := by
    intro x hx y hy c
    funext Z
    simp only [hlin x hx y hy c, map_add, map_smul, Pi.add_apply, Pi.smul_apply]
  have htr2 : ∀ C, ∀ x ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁),
      GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (wT C) x ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁) ∧
      ι (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (wT C) x) = (fun Z => ι x (Z + C)) ∧
      (fun (φ : (Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ) (Z : Matrix (Fin a') (Fin (a + a')) (Fv F B.v₁)) => ι (S φ) (((g⁻¹ : GL (Fin a') (Fv F B.v₁)).val)ᵀ * Z)) (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (wT C) x) =
        fun Z => (fun (φ : (Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ) (Z : Matrix (Fin a') (Fin (a + a')) (Fv F B.v₁)) => ι (S φ) (((g⁻¹ : GL (Fin a') (Fv F B.v₁)).val)ᵀ * Z)) x (Z + C) := by
    intro C x hx
    refine ⟨hU0 _ x hx, hT0 C x hx, ?_⟩
    funext Z
    simp only [hST0 C x hx, Matrix.mul_add]
  have hmu2 : ∀ l, ∀ x ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁),
      GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (wM l) x ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁) ∧
      ι (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (wM l) x) = (fun Z => GlobalTheory.LatVac.psiAt B.ψ B.v₁ (l Z) * ι x Z) ∧
      (fun (φ : (Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ) (Z : Matrix (Fin a') (Fin (a + a')) (Fv F B.v₁)) => ι (S φ) (((g⁻¹ : GL (Fin a') (Fv F B.v₁)).val)ᵀ * Z)) (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (wM l) x) =
        fun Z => GlobalTheory.LatVac.psiAt B.ψ B.v₁ (l Z) * (fun (φ : (Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ) (Z : Matrix (Fin a') (Fin (a + a')) (Fv F B.v₁)) => ι (S φ) (((g⁻¹ : GL (Fin a') (Fv F B.v₁)).val)ᵀ * Z)) x Z := by
    intro l x hx
    refine ⟨hU0 _ x hx, hM0 l x hx, ?_⟩
    funext Z
    simp only [hSM0 l x hx, key1]
  obtain ⟨c, hc⟩ := GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat (SB (Fin a' × Fin (a + a') → Fv F B.v₁)) (GlobalTheory.LatVac.psiAt B.ψ B.v₁) hψc hψ1 ι
    (fun (φ : (Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ) (Z : Matrix (Fin a') (Fin (a + a')) (Fv F B.v₁)) => ι (S φ) (((g⁻¹ : GL (Fin a') (Fv F B.v₁)).val)ᵀ * Z)) hbij hlin2
    (fun C => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (wT C))
    (fun l => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (wM l)) htr2 hmu2
  have hval := congrFun (hc φ hφSB) (g.valᵀ * Y)
  simp only [key2, Pi.smul_apply, smul_eq_mul] at hval
  have hr : (g.valᵀ * Y).rank = Y.rank := by
    refine Matrix.rank_mul_eq_right_of_isUnit_det _ _ ?_
    rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
  rw [hφ₁S, hval, hsupp _ (by rw [hr]; exact hY), mul_zero]

end GlobalTheory.SoLocV
