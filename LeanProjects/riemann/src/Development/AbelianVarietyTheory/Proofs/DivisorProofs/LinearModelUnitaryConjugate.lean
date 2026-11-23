import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairLocalSchwartzAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruhStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianSplitSymplecticPairStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped Matrix
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.LinWShape

theorem frob_mul {K : Type} [CommRing K] {m n : Type} [Fintype m] [Fintype n]
    (A : Matrix m m K) (Y : Matrix m n K) (B : Matrix n n K) (P : Matrix m n K) :
    ∑ k, ∑ l, (A * Y * B) k l * P k l = ∑ k, ∑ l, Y k l * (Aᵀ * P * Bᵀ) k l := by
  have e : ∀ M Q : Matrix m n K, ∑ k, ∑ l, M k l * Q k l = Matrix.trace (M * Qᵀ) := by
    intro M Q
    simp [Matrix.trace, Matrix.mul_apply]
  rw [e, e, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    show A * Y * B * Pᵀ = A * (Y * B * Pᵀ) by simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc, Matrix.transpose_transpose]

theorem linForm_eq {K : Type} [Field K] {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (l : Matrix m n K →ₗ[K] K) (Y : Matrix m n K) :
    l Y = ∑ k, ∑ j, Y k j * l (Matrix.single k j 1) := by
  conv_lhs => rw [Y.matrix_eq_sum_single]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show Matrix.single k j (Y k j) = Y k j • Matrix.single k j (1 : K) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul]

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

end GlobalTheory.LinWShape

namespace GlobalTheory.LinWShape

theorem shape_right : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∃ κ : UA σ W.J → ℂ, ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → ι φ₁ = κ h • fun Y => ι φ (Y * (GlobalTheory.SplitFlip.invT (locMat t c h)).val) := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp v t b c ι hι
  have hA : ActsEx := GlobalTheory.T.theta_action_exists hPr
  have hcm : IsCMExt F E σ := hp.base.cm
  have hstd := hp.base.std
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.SchrSB.continuous_psiAt _ hstd.1 v
  have hψ1 : GlobalTheory.LatVac.psiAt B.ψ v ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one _ hstd v
  have hσσ : ∀ x : E, σ (σ x) = x := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    intro x
    apply w.embedding.injective
    rw [hcm.2.2.2 w.embedding (σ x), hcm.2.2.2 w.embedding x, star_star]
  have hts : (t.comp σ).comp σ = t := AlgHom.ext fun x => by simp [hσσ]
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdX : X.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hp.herm.sig w)
    have e : (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det := (RingHom.map_det _ _).symm
    rw [e, h0, map_zero]
  have hdW : W.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hp.skew.sig w)
    have e : (W.J.map (B.emb w).1).det = (B.emb w).1 W.J.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_smul, e, h0, map_zero, mul_zero]
  set A0 : Matrix (Fin n) (Fin n) (Fv F v) := X.J.map (t.comp σ) with hA0
  set B0 : Matrix (Fin d) (Fin d) (Fv F v) := (W.J.map (t.comp σ))ᵀ with hB0
  set A : Matrix (Fin n) (Fin n) (Fv F v) := A0 * b.1 with hAdef
  set Bm : Matrix (Fin d) (Fin d) (Fv F v) := c.1ᵀ * B0 with hBdef
  have hAu : IsUnit A.det := by
    have e : A0.det = ((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v) X.J.det := (RingHom.map_det _ _).symm
    rw [hAdef, Matrix.det_mul]
    refine IsUnit.mul ?_ (Matrix.isUnits_det_units b)
    rw [e]
    exact isUnit_iff_ne_zero.2 fun h => hdX (RingHom.injective ((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v) (by rw [map_zero]; exact h))
  have hBu : IsUnit Bm.det := by
    have e : (W.J.map (t.comp σ)).det = ((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v) W.J.det := (RingHom.map_det _ _).symm
    rw [hBdef, Matrix.det_mul, Matrix.det_transpose, hB0, Matrix.det_transpose]
    refine IsUnit.mul (Matrix.isUnits_det_units c) ?_
    rw [e]
    exact isUnit_iff_ne_zero.2 fun h => hdW (RingHom.injective ((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v) (by rw [map_zero]; exact h))
  choose U hUat hU0 hU1 using fun (P₀ P₁ : Matrix (Fin n) (Fin d) (Fv F v)) => GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hcm v t P₀ P₁
  let coF : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n) (Fin d) (Fv F v) :=
    fun u => (b⁻¹).1 * u.map (piW t) * (c⁻¹).1ᵀ
  have hcc : c.1ᵀ * (c⁻¹).1ᵀ = 1 := by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
  have hcc' : (c⁻¹).1ᵀ * c.1ᵀ = 1 := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have htr : ∀ u, At (evFin F v) u → u.map (piW (t.comp σ)) = 0 → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (M.co.rho B.ψ u) φ φ₁ → ∀ Y, ι φ₁ Y = ι φ (Y + coF u) :=
    hι.trans
  have hmu : ∀ u, At (evFin F v) u → u.map (piW t) = 0 → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (M.co.rho B.ψ u) φ φ₁ →
      ∀ x, At (evFin F v) x → x.map (piW (t.comp σ)) = 0 →
        ι φ₁ (coF x) = B.ψ (symp (cA σ) (-1) (incM F X.J) (incM F W.J) x u) * ι φ (coF x) :=
    hι.mult
  let xY : Matrix (Fin n) (Fin d) (Fv F v) → Matrix (Fin n) (Fin d) (AE F E) := fun Y => U (b.1 * Y * c.1ᵀ) 0
  have hcoY : ∀ Y, coF (xY Y) = Y := by
    intro Y
    simp only [coF, xY, hU0, Matrix.mul_assoc, hcc, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  have hxt : ∀ x, x.map (piW t) = b.1 * coF x * c.1ᵀ := by
    intro x
    simp only [coF, Matrix.mul_assoc, hcc', Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  have hmatW : ∀ h : UA σ W.J, (mat h).map (piW t) = c.1 * (locMat t c h).val * (c⁻¹).1 := by
    intro h
    rw [locMat_val]
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  have hcoH : ∀ (u : Matrix (Fin n) (Fin d) (AE F E)) (h : UA σ W.J),
      coF (u * (mat h)ᵀ) = coF u * (locMat t c h).valᵀ := by
    intro u h
    simp only [coF]
    rw [Matrix.map_mul, Matrix.transpose_map, hmatW h]
    simp only [Matrix.transpose_mul, Matrix.mul_assoc, hcc, Matrix.mul_one]
  have hsymp : ∀ x u : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) x → x.map (piW (t.comp σ)) = 0 →
      u.map (piW t) = 0 →
      B.ψ (symp (cA σ) (-1) (incM F X.J) (incM F W.J) x u) =
        GlobalTheory.LatVac.psiAt B.ψ v (∑ k, ∑ l, (A0 * x.map (piW t) * B0) k l * u.map (piW (t.comp σ)) k l) := by
    intro x u hx hx0 hu1
    have key := GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair hcm (t.comp σ) X.J W.J hp.herm.herm hp.skew.skew x u hx0 (by rw [hts]; exact hu1)
    rw [hts] at key
    unfold symp
    rw [GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm v t _ (at_hTens _ _ x u hx)]
    rw [map_mul, map_mul, map_neg, map_neg, map_one, map_one, neg_one_mul, neg_one_mul, ← neg_add, add_comm, key]
    show GlobalTheory.LatVac.psiAt B.ψ v _ = GlobalTheory.LatVac.psiAt B.ψ v _
    congr 1
    simp [hA0, hB0, Matrix.neg_mul, Matrix.mul_neg, Finset.sum_neg_distrib]
  let Lm : (Matrix (Fin n) (Fin d) (Fv F v) →ₗ[Fv F v] Fv F v) → Matrix (Fin n) (Fin d) (Fv F v) :=
    fun l => Matrix.of fun k j => l (Matrix.single k j 1)
  let uM : (Matrix (Fin n) (Fin d) (Fv F v) →ₗ[Fv F v] Fv F v) → Matrix (Fin n) (Fin d) (AE F E) :=
    fun l => U 0 ((A⁻¹)ᵀ * Lm l * (Bm⁻¹)ᵀ)
  have hMu : ∀ l x, At (evFin F v) x → x.map (piW (t.comp σ)) = 0 →
      B.ψ (symp (cA σ) (-1) (incM F X.J) (incM F W.J) x (uM l)) = GlobalTheory.LatVac.psiAt B.ψ v (l (coF x)) := by
    intro l x hx hx0
    rw [hsymp x (uM l) hx hx0 (hU0 _ _), hU1, hxt x]
    congr 1
    have e1 : A0 * (b.1 * coF x * c.1ᵀ) * B0 = A * coF x * Bm := by
      simp only [hAdef, hBdef, Matrix.mul_assoc]
    have e2 : Aᵀ * ((A⁻¹)ᵀ * Lm l * (Bm⁻¹)ᵀ) * Bmᵀ = Lm l := by
      have iA : Aᵀ * (A⁻¹)ᵀ = 1 := by rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hAu, Matrix.transpose_one]
      have iB : (Bm⁻¹)ᵀ * Bmᵀ = 1 := by rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hBu, Matrix.transpose_one]
      simp only [Matrix.mul_assoc]
      rw [iB, Matrix.mul_one, ← Matrix.mul_assoc, iA, Matrix.one_mul]
    rw [e1, frob_mul, e2, linForm_eq l (coF x)]
    rfl
  have h1X : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := by
    show At _ (mat (1 : UA σ X.J) - 1)
    rw [show mat (1 : UA σ X.J) = 1 from rfl, sub_self]
    intro u _
    exact smul_zero u
  have hatR : ∀ (u : Matrix (Fin n) (Fin d) (AE F E)) (N : Matrix (Fin d) (Fin d) (AE F E)), At (evFin F v) u →
      At (evFin F v) (u * N) := by
    intro u N hu r hr
    rw [← Matrix.smul_mul, hu r hr, Matrix.zero_mul]
  have hmain : ∀ h ∈ UAt σ W (evFin F v), ∃ κ : ℂ, ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      (fun (Y : Matrix (Fin n) (Fin d) (Fv F v)) => ι (locOp v (om (1, h)) φ) (Y * (locMat t c h).valᵀ)) = κ • ι φ := by
    intro h hh
    have hSacts : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (om (1, h)) φ (locOp v (om (1, h)) φ) :=
      fun φ hφ => acts_locOp_om hA hp h1X hh hφ
    have hSSB : ∀ φ, locOp v (om (1, h)) φ ∈ SB (Fin n × Fin d → Fv F v) := fun φ => locOp_mem v _ φ
    have hex : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∃ φ₁ ∈ SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ :=
      fun φ hφ => ⟨_, hSSB φ, hSacts φ hφ⟩
    have hsb := fun (u : Matrix (Fin n) (Fin d) (AE F E)) (φ : (Fin n × Fin d → Fv F v) → ℂ) (hφ : φ ∈ SB (Fin n × Fin d → Fv F v)) =>
      GlobalTheory.SchrSB.schr_mem_SB B.ψ hstd.1 v (GlobalTheory.LatVac.locCo M.co v u) φ hφ
    have hint : ∀ (u : Matrix (Fin n) (Fin d) (AE F E)), At (evFin F v) u → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
        locOp v (om (1, h)) (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v u) φ) =
          schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v (u * (mat h)ᵀ)) (locOp v (om (1, h)) φ) := by
      intro u hu φ hφ
      have hm1 : mat (1 : UA σ X.J) = 1 := rfl
      have hu' : At (evFin F v) (mat (1 : UA σ X.J) * u * (mat ((1 : UA σ X.J), h).2)ᵀ) := by
        rw [hm1, Matrix.one_mul]; exact hatR u _ hu
      have e := GlobalTheory.IntertwLocal.local_intertw F E σ B n d X W M χX χW om r s r' s' hp v (1, h) u φ _ _ _ _ hφ
        (hsb u φ hφ) (hSSB φ) (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v u hu φ) (hSacts φ hφ) (hSacts _ (hsb u φ hφ))
        (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v _ hu' _)
      simp only [hm1, Matrix.one_mul] at e
      exact e.symm
    have hinv : (mat h)ᵀ * (mat h⁻¹)ᵀ = 1 := by
      rw [← Matrix.transpose_mul]
      have : mat (h⁻¹ * h) = mat h⁻¹ * mat h := rfl
      rw [← this, inv_mul_cancel, show mat (1 : UA σ W.J) = 1 from rfl, Matrix.transpose_one]
    have hh' : (locMat t c h).valᵀ * (locMat t c h⁻¹).valᵀ = 1 := by
      rw [map_inv, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
    have hlin : ∀ x ∈ SB (Fin n × Fin d → Fv F v), ∀ y ∈ SB (Fin n × Fin d → Fv F v), ∀ a : ℂ,
        (fun (Y : Matrix (Fin n) (Fin d) (Fv F v)) => ι (locOp v (om (1, h)) (a • x + y)) (Y * (locMat t c h).valᵀ)) =
          a • (fun (Y : Matrix (Fin n) (Fin d) (Fv F v)) => ι (locOp v (om (1, h)) x) (Y * (locMat t c h).valᵀ)) +
            (fun (Y : Matrix (Fin n) (Fin d) (Fv F v)) => ι (locOp v (om (1, h)) y) (Y * (locMat t c h).valᵀ)) := by
      intro x hx y hy a
      have e := locOp_lin (om (1, h)).isLinear hex a 1 hx hy
      rw [one_smul, one_smul] at e
      funext Y
      simp only [e, map_add, map_smul, Pi.add_apply, Pi.smul_apply]
    have htrS : ∀ C, ∀ x ∈ SB (Fin n × Fin d → Fv F v),
        schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v (xY C)) x ∈ SB (Fin n × Fin d → Fv F v) ∧
        ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v (xY C)) x) = (fun Y => ι x (Y + C)) ∧
        (fun (Y : Matrix (Fin n) (Fin d) (Fv F v)) => ι (locOp v (om (1, h)) (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v (xY C)) x))
          (Y * (locMat t c h).valᵀ)) = fun (Y : Matrix (Fin n) (Fin d) (Fv F v)) => ι (locOp v (om (1, h)) x) ((Y + C) * (locMat t c h).valᵀ) := by
      intro C x hx
      have hat := hUat (b.1 * C * c.1ᵀ) 0
      have hat' := hatR _ (mat h)ᵀ hat
      have h0' : (xY C * (mat h)ᵀ).map (piW (t.comp σ)) = 0 := by
        rw [Matrix.map_mul]; simp only [xY, hU1, Matrix.zero_mul]
      refine ⟨hsb _ x hx, ?_, ?_⟩
      · funext Y
        rw [htr (xY C) hat (hU1 _ _) x hx _ (hsb _ x hx) (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v _ hat x) Y, hcoY]
      · funext Y
        rw [hint _ hat x hx, htr _ hat' h0' _ (hSSB x) _ (hsb _ _ (hSSB x))
          (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v _ hat' _), hcoH, hcoY, Matrix.add_mul]
    have hmuS : ∀ l, ∀ x ∈ SB (Fin n × Fin d → Fv F v),
        schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v (uM l)) x ∈ SB (Fin n × Fin d → Fv F v) ∧
        ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v (uM l)) x) =
          (fun Y => GlobalTheory.LatVac.psiAt B.ψ v (l Y) * ι x Y) ∧
        (fun (Y : Matrix (Fin n) (Fin d) (Fv F v)) => ι (locOp v (om (1, h)) (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v (uM l)) x))
          (Y * (locMat t c h).valᵀ)) =
          fun (Y : Matrix (Fin n) (Fin d) (Fv F v)) => GlobalTheory.LatVac.psiAt B.ψ v (l Y) * ι (locOp v (om (1, h)) x) (Y * (locMat t c h).valᵀ) := by
      intro l x hx
      have hat := hUat 0 ((A⁻¹)ᵀ * Lm l * (Bm⁻¹)ᵀ)
      have hat' := hatR _ (mat h)ᵀ hat
      have h1' : (uM l * (mat h)ᵀ).map (piW t) = 0 := by
        rw [Matrix.map_mul]; simp only [uM, hU0, Matrix.zero_mul]
      refine ⟨hsb _ x hx, ?_, ?_⟩
      · funext Y
        have e := hmu (uM l) hat (hU0 _ _) x hx _ (hsb _ x hx) (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v _ hat x)
          (xY Y) (hUat _ _) (hU1 _ _)
        rw [hcoY] at e
        rw [e, hMu l (xY Y) (hUat _ _) (hU1 _ _), hcoY]
      · funext Y
        have hZ := hUat (b.1 * (Y * (locMat t c h).valᵀ) * c.1ᵀ) 0
        have e := hmu _ hat' h1' _ (hSSB x) _ (hsb _ _ (hSSB x)) (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v _ hat' _)
          (xY (Y * (locMat t c h).valᵀ)) hZ (hU1 _ _)
        rw [hcoY] at e
        rw [hint _ hat x hx, e]
        congr 1
        have hs := GlobalTheory.SympInv.symp_act F E σ n d X W 1 h⁻¹ (xY (Y * (locMat t c h).valᵀ)) (uM l * (mat h)ᵀ)
        have hm1 : mat (1 : UA σ X.J) = 1 := rfl
        rw [hm1, Matrix.one_mul, Matrix.one_mul, Matrix.mul_assoc, hinv, Matrix.mul_one] at hs
        have hx0 : (xY (Y * (locMat t c h).valᵀ) * (mat h⁻¹)ᵀ).map (piW (t.comp σ)) = 0 := by
          rw [Matrix.map_mul]; simp only [xY, hU1, Matrix.zero_mul]
        rw [← hs, hMu l _ (hatR _ _ hZ) hx0, hcoH, hcoY, Matrix.mul_assoc, hh', Matrix.mul_one]

    exact GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat (SB (Fin n × Fin d → Fv F v)) (GlobalTheory.LatVac.psiAt B.ψ v) hψc hψ1 ι
      (fun φ Y => ι (locOp v (om (1, h)) φ) (Y * (locMat t c h).valᵀ)) hι.bij hlin
      (fun C φ => schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v (xY C)) φ)
      (fun l φ => schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v (uM l)) φ) htrS hmuS
  choose! κ hκ using hmain
  refine ⟨κ, fun h hh φ hφ φ₁ hφ₁ hact => ?_⟩
  have e2 := hκ h hh φ hφ
  rw [locOp_eq hφ hφ₁ hact] at e2
  funext Y
  have e3 := congrFun e2 (Y * (GlobalTheory.SplitFlip.invT (locMat t c h)).val)
  simp only [Pi.smul_apply, smul_eq_mul] at e3 ⊢
  rw [GlobalTheory.SplitFlip.invT_val, Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one,
    Matrix.mul_one] at e3
  rw [GlobalTheory.SplitFlip.invT_val]
  exact e3

end GlobalTheory.LinWShape
