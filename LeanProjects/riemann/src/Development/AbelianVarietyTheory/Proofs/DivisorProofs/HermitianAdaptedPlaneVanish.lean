import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDblOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryCharacterTrivialOfSiegelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryDoubledBlockDiagOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawLeftRestrictionLeviStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlacesBoundTupleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatBoundTupleStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

open GlobalTheory.MixXChar

namespace GlobalTheory.MixXChar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem det_ne_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have h1 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]; ext i j; simp [A', Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.map_apply]
  have h2 : (A'ᵀ * M * A'.map star).det ≠ 0 := by
    rw [h1, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
    simp [Matrix.det_neg]
  intro h0
  apply h2
  rw [Matrix.det_mul, Matrix.det_mul, h0]; simp

theorem det_ne_of_sig {n r s : ℕ} (B : Base F E) (J : Matrix (Fin n) (Fin n) E)
    (h : ∀ w, HasSig (J.map (B.emb w).1) r s) : J.det ≠ 0 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have := det_ne_of_hasSig (h w)
  intro h0; apply this
  have e := RingHom.map_det (B.emb w).1 J
  rw [RingHom.mapMatrix_apply] at e
  rw [← e, h0, map_zero]

open scoped Classical in

theorem evalPt_mem_adm {κ : Type} [Fintype κ] (x : κ → AF F) :
    (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x i).2) • ((BoundedContinuousFunction.evalCLM ℂ
    (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)), fun f => ?_⟩
  simp [pureA, mul_comm]

theorem rho_diag {a b : ℕ} {JA : Matrix (Fin a) (Fin a) E} {JB : Matrix (Fin b) (Fin b) E} {κ : Type}
    [Fintype κ] {d : Darboux (symp (cA σ) (-1) (incM F JA) (incM F JB)) κ}
    {dd : Darboux (symp (cA σ) (-1) (incM F JA) (dbl (incM F JB))) (κ ⊕ κ)}
    (h : IsDblCoord (cA σ) (-1) (incM F JA) (incM F JB) d dd) (ψ : AddChar (AF F) ℂ)
    (z : Matrix (Fin a) (Fin b) (AE F E)) :
    dd.rho ψ (z * (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E))ᵀ) =
      schr ψ (Sum.elim (d.e z).1 (d.e z).1, Sum.elim (d.e z).2 (-(d.e z).2)) := by
  unfold Darboux.rho
  rw [← h]
  congr 2
  ext i j
  rcases j with j | j <;> erw [Matrix.mul_apply] <;> simp [diagCols, Matrix.one_apply]

theorem siegel_transfer {a b : ℕ} {JA : Matrix (Fin a) (Fin a) E} {JB : Matrix (Fin b) (Fin b) E} {κ : Type} [Fintype κ]
    {ψ : AddChar (AF F) ℂ} {dd : Darboux (symp (cA σ) (-1) (incM F JA) (dbl (incM F JB))) κ} {χ : Chr F E}
    {omd : UG (cA σ) (dbl (incM F JB)) →* Module.End ℂ ((κ → AF F) → ℂ)}
    (h : IsUWeilSplit (cA σ) (adeleClass F) ψ (-1) (incM F JA) (dbl (incM F JB)) dd χ (diagCols (Fin b)) omd)
    (g₀ : UG (cA σ) (dbl (incM F JB))) (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (hl : l ∈ (adeleClass F).adm κ)
    (hinv : ∀ z : Matrix (Fin a) (Fin b) (AE F E), ∀ φ ∈ schA F κ,
      l (dd.rho ψ (z * (g₀.1.1 * (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E)))ᵀ) φ) = l φ)
    (p : UG (cA σ) (dbl (incM F JB))) (t : GL (Fin b) (AE F E))
    (hp : p.1.1 * (g₀.1.1 * (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E))) =
      (g₀.1.1 * (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E))) * t.1) :
    ∀ φ ∈ schA F κ, l (omd p φ) = (χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
        ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t)) : ℝ) ^
          ((Fintype.card (Fin a) : ℝ) / 2) : ℝ) : ℂ) * l φ := by
  obtain ⟨-, hS, hR⟩ := h
  intro φ hφ
  set Δ : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E) := diagCols (Fin b) with hΔ
  have hl'' : l ∘ₗ omd g₀ ∈ (adeleClass F).adm κ := hS.adm g₀ l hl
  have hinv'' : ∀ z : Matrix (Fin a) (Fin b) (AE F E), ∀ φ ∈ (adeleClass F).sp κ,
      (l ∘ₗ omd g₀) (dd.rho ψ (z * Δᵀ) φ) = (l ∘ₗ omd g₀) φ := by
    intro z φ hφ
    simp only [LinearMap.comp_apply]
    rw [hS.impl g₀ _ φ hφ]
    have ea : actB (cA σ) g₀ (z * Δᵀ) = z * (g₀.1.1 * Δ)ᵀ := by
      simp only [actB, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [ea]
    exact hinv z _ (hS.pres g₀ φ hφ)
  have hg : (g₀⁻¹).1.1 * g₀.1.1 = 1 := by rw [Subgroup.coe_inv]; exact Units.inv_mul _
  have hp' : (g₀⁻¹ * p * g₀).1.1 * Δ = Δ * t.1 := by
    show (g₀⁻¹).1.1 * p.1.1 * g₀.1.1 * Δ = Δ * t.1
    calc (g₀⁻¹).1.1 * p.1.1 * g₀.1.1 * Δ = (g₀⁻¹).1.1 * (p.1.1 * (g₀.1.1 * Δ)) := by simp only [Matrix.mul_assoc]
      _ = (g₀⁻¹).1.1 * ((g₀.1.1 * Δ) * t.1) := by rw [hp]
      _ = ((g₀⁻¹).1.1 * g₀.1.1) * Δ * t.1 := by simp only [Matrix.mul_assoc]
      _ = Δ * t.1 := by rw [hg, Matrix.one_mul]
  have key := hR (l ∘ₗ omd g₀) hl'' hinv'' (g₀⁻¹ * p * g₀) t hp' (omd g₀⁻¹ φ) (hS.pres _ φ hφ)
  simp only [LinearMap.comp_apply] at key
  have hq : g₀ * (g₀⁻¹ * p * g₀) * g₀⁻¹ = p := by group
  have e1 : omd g₀ (omd (g₀⁻¹ * p * g₀) (omd g₀⁻¹ φ)) = omd p φ := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hq]
  have e2 : omd g₀ (omd g₀⁻¹ φ) = φ := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [e1, e2] at key
  exact key

end GlobalTheory.MixXChar

namespace GlobalTheory.MixXChar

theorem levi_scalar_one : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      (∀ (g₁ : UA σ X₁.J) (m : UA σ X.J), IsLevi H 1 g₁ m → ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d),
        e (om (m, 1) Φ) = c • om₁ (g₁, 1) (e Φ)) →
      ∀ (g₁ : UA σ X₁.J) (m : UA σ X.J), IsLevi H 1 g₁ m → ∀ Φ ∈ schA F (Fin n × Fin d),
        e (om (m, 1) Φ) = om₁ (g₁, 1) (e Φ) := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he _ g₁ m hL Φ hΦ
  obtain ⟨dd, omd, hD⟩ := exists_isDblOf hP
  obtain ⟨dd₁, omd₁, hD₁⟩ := exists_isDblOf hP₁
  obtain ⟨et, e₂, hmaps, he₂m, ⟨φ₂, hφ₂, hφ₂0⟩, hbox, hde, hadm, hnz⟩ :=
    GlobalTheory.T.seesaw_left_restriction_is_pair F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he dd omd dd₁ omd₁ hD hD₁
  obtain ⟨emb, g₀, hcont, hlev, hlevi, hsieg, hdec⟩ :=
    GlobalTheory.T.seesaw_left_restriction_global F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁
  have hlam0 := fun gd₁ => GlobalTheory.T.seesaw_left_restriction_levi F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he
    dd omd dd₁ omd₁ hD hD₁ et hmaps hde hadm gd₁ (emb gd₁) (hlev gd₁)
  choose lam hlam using hlam0
  obtain ⟨d₁', -, hdd₁, hW₁, hres₁⟩ := hD₁
  obtain ⟨d', -, hdd, hW, hres⟩ := hD
  have hS := hW.2.1
  have hS₁ := hW₁.2.1
  have hR₁ := hW₁.2.2
  obtain ⟨l₁, hl₁, hl₁inv, ψ₀, hψ₀, hψ₀0⟩ := GlobalTheory.T.exists_diagonalLagrangian_invariant_form F B.ψ (Fin n₁ × Fin d)
  have hl₁inv' : ∀ z : Matrix (Fin d) (Fin n₁) (AE F E), ∀ φ ∈ schA F ((Fin n₁ × Fin d) ⊕ (Fin n₁ × Fin d)),
      l₁ (dd₁.rho B.ψ (z * (diagCols (Fin n₁) : Matrix (Fin n₁ ⊕ Fin n₁) (Fin n₁) (AE F E))ᵀ) φ) = l₁ φ := by
    intro z φ hφ
    rw [rho_diag hdd₁]
    exact hl₁inv _ _ φ hφ
  obtain ⟨Φ₁, hΦ₁, hΦ₁0⟩ := hnz l₁ hl₁ hl₁inv' ⟨ψ₀, hψ₀, hψ₀0⟩
  have hetΦ₁ : et Φ₁ ≠ 0 := fun h0 => hΦ₁0 (by rw [h0, map_zero])
  have inv₁ : ∀ p φ, omd₁ p⁻¹ (omd₁ p φ) = φ := fun p φ => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

  have huniq : ∀ p (a : ℂ), (∀ Ψ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), et (omd (emb p) Ψ) = a • omd₁ p (et Ψ)) → a = lam p := by
    intro p a ha
    have h1 := (ha Φ₁ hΦ₁).symm.trans (hlam p Φ₁ hΦ₁)
    have hv : omd₁ p (et Φ₁) ≠ 0 := fun h0 => hetΦ₁ (by rw [← inv₁ p (et Φ₁), h0, map_zero])
    exact smul_left_injective ℂ hv h1
  have hmul : ∀ p q, lam (p * q) = lam p * lam q := fun p q => (huniq (p * q) _ fun Ψ hΨ => by
    rw [map_mul, map_mul, Module.End.mul_apply, hlam p _ (hS.pres _ Ψ hΨ), hlam q Ψ hΨ, map_smul, smul_smul,
      map_mul, Module.End.mul_apply]).symm
  have hone : lam 1 = 1 := (huniq 1 1 fun Ψ _ => by simp).symm
  let cM : UG (cA σ) (dbl (incM F X₁.J)) →* ℂ := { toFun := lam, map_one' := hone, map_mul' := hmul }
  let c := cM.toHomUnits
  have hcv : ∀ p, ((c p : ℂˣ) : ℂ) = lam p := fun p => rfl
  obtain ⟨x, hx⟩ : ∃ x, et Φ₁ x ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact hetΦ₁ (funext h0)
  let Lx : ((((Fin n₁ × Fin d) ⊕ (Fin n₁ × Fin d)) → AF F) → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj x
  have hLx : Lx ∈ (adeleClass F).adm ((Fin n₁ × Fin d) ⊕ (Fin n₁ × Fin d)) := evalPt_mem_adm (F := F) x
  have hcont_l : Continuous lam := by
    refine continuous_iff_continuousAt.2 fun p₀ => ?_
    have hΨ := hS.pres (emb p₀⁻¹) Φ₁ hΦ₁
    have hN := (hS.cont _ (hadm _ hLx) _ hΨ).comp hcont
    have hDc := hS₁.cont _ hLx _ (hmaps _ hΨ)
    have hrel : ∀ p, (Lx ∘ₗ et) (omd (emb p) (omd (emb p₀⁻¹) Φ₁)) =
        lam p * Lx (omd₁ p (et (omd (emb p₀⁻¹) Φ₁))) := fun p => by
      simp only [LinearMap.comp_apply]
      rw [hlam p _ hΨ]
      simp
    have hN0 : (Lx ∘ₗ et) (omd (emb p₀) (omd (emb p₀⁻¹) Φ₁)) ≠ 0 := by
      rw [← Module.End.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, Module.End.one_apply]
      exact hx
    have hD0 : Lx (omd₁ p₀ (et (omd (emb p₀⁻¹) Φ₁))) ≠ 0 := by
      intro h0
      apply hN0
      rw [hrel, h0, mul_zero]
    refine (hN.continuousAt.div hDc.continuousAt hD0).congr ?_
    filter_upwards [hDc.continuousAt.eventually_ne hD0] with p hp
    change (Lx ∘ₗ et) (omd (emb p) (omd (emb p₀⁻¹) Φ₁)) / Lx (omd₁ p (et (omd (emb p₀⁻¹) Φ₁))) = lam p
    rw [hrel p, mul_div_assoc, div_self hp, mul_one]
  have hcontc : Continuous c := by
    refine Units.continuous_iff.2 ⟨hcont_l, ?_⟩
    have : (fun p => ((c p)⁻¹ : ℂˣ).val) = fun p => (lam p)⁻¹ := funext fun p => by
      rw [Units.val_inv_eq_inv_val, hcv]
    rw [this]
    exact hcont_l.inv₀ fun p => by rw [← hcv]; exact (c p).ne_zero

  have hP' : ∀ (p : UG (cA σ) (dbl (incM F X₁.J))) (t : GL (Fin n₁) (AE F E)),
      (p.1.1 : Matrix (Fin n₁ ⊕ Fin n₁) (Fin n₁ ⊕ Fin n₁) (AE F E)) * diagCols (Fin n₁) = diagCols (Fin n₁) * t.1 →
        c p = 1 := fun p t hpt => by
    obtain ⟨t', ht', hdet⟩ := hsieg p t hpt
    have hinv' : ∀ z : Matrix (Fin d) (Fin n) (AE F E), ∀ φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
        (l₁ ∘ₗ et) (dd.rho B.ψ (z * (g₀.1.1 * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)))ᵀ) φ) =
          (l₁ ∘ₗ et) φ := by
      intro z φ hφ
      obtain ⟨z₁, u, hu, hz⟩ := hdec z
      simp only [LinearMap.comp_apply]
      rw [hz, hde _ u hu φ hφ]
      exact hl₁inv' z₁ _ (hmaps φ hφ)
    have e1 := siegel_transfer hW g₀ (l₁ ∘ₗ et) (hadm l₁ hl₁) hinv' (emb p) t' ht' Φ₁ hΦ₁
    have e2 := hR₁ l₁ hl₁ hl₁inv' p t hpt (et Φ₁) (hmaps _ hΦ₁)
    simp only [LinearMap.comp_apply] at e1
    rw [hlam p Φ₁ hΦ₁, map_smul, smul_eq_mul, e2, hdet] at e1
    have hmod : ∀ u : (AF F)ˣ, ((((adeleClass F).modu u : ℝ) ^ ((Fintype.card (Fin d) : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
      intro u
      have hu : ((adeleClass F).modu u : ℝ) ≠ 0 :=
        NNReal.coe_ne_zero.2 (IsUnit.map (adeleClass F).modu (Group.isUnit u)).ne_zero
      exact Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (lt_of_le_of_ne (NNReal.coe_nonneg _) hu.symm) _).ne'
    have hK : (χW (Matrix.GeneralLinearGroup.det t) : ℂ) *
        ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t)) : ℝ) ^
          ((Fintype.card (Fin d) : ℝ) / 2) : ℝ) : ℂ) * l₁ (et Φ₁) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (Circle.coe_ne_zero _) (hmod _)) hΦ₁0
    refine Units.ext ?_
    rw [hcv, Units.val_one]
    exact mul_right_cancel₀ hK (by rw [one_mul]; exact e1)
  have hσ : IsCMExt F E σ := hP.base.cm
  have hJ : ∀ i j, σ (X₁.J j i) = (((1 : ℤˣ) : ℤ) : E) * X₁.J i j := fun i j => by simp [hP₁.herm.herm i j]
  have hdetJ : X₁.J.det ≠ 0 := det_ne_of_sig B X₁.J hP₁.herm.sig
  have hc1 := GlobalTheory.T.doubledUnitary_character_trivial_of_siegel F E σ hσ n₁ X₁.J 1 hJ hdetJ c hcontc hP'
  have hlam1 : ∀ p, lam p = 1 := fun p => by rw [← hcv, hc1]; rfl

  obtain ⟨gd₁, hgd₁⟩ := GlobalTheory.T.exists_unitaryDoubled_blockDiag_one (AF F) (AE F E) (cA σ) (Fin n₁) (incM F X₁.J) g₁
  have hmd := hlevi g₁ m hL gd₁ hgd₁
  have hsp := hP.weil.isUSplitting
  have e3 := hlam gd₁ (boxFun Φ φ₂) (GlobalTheory.T.productFunctionOnSumCoords_mem_adelicSchwartzSpace F _ _ Φ hΦ φ₂ hφ₂)
  rw [hres m (emb gd₁) hmd Φ hΦ φ₂ hφ₂, hbox _ (hsp.pres _ Φ hΦ) φ₂ hφ₂, hbox Φ hΦ φ₂ hφ₂,
    hres₁ g₁ gd₁ hgd₁ (e Φ) (he.maps Φ hΦ) (e₂ φ₂) (he₂m φ₂ hφ₂), hlam1, one_smul] at e3
  obtain ⟨y, hy⟩ : ∃ y, e₂ φ₂ y ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact hφ₂0 (funext h0)
  funext z
  have := congrFun e3 (Sum.elim z y)
  simp only [boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr] at this
  exact mul_right_cancel₀ hy this

end GlobalTheory.MixXChar

end
