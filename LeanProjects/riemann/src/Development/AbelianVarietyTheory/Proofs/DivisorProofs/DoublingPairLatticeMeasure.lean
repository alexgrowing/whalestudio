import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxSymplecticDoubledHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantAdmissibleFormEqMulDiagonalIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryCharacterTrivialOfSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicWeilRepSchrodingerModelUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewDeterminantNeZeroFirstSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUgReindex
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer
open GlobalTheory.DblDatum

noncomputable section

namespace GlobalTheory.DblWeilBox

open GlobalTheory.WeilSchrodinger.DblTarget

variable {F : Type} [Field F] [NumberField F]

theorem exists_smul_of_intertwine (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {κ κ₂ V : Type} [Fintype κ] [Fintype κ₂]
    (a : V → (κ ⊕ κ → AF F) × (κ ⊕ κ → AF F)) (b : V → (κ₂ → AF F) × (κ₂ → AF F))
    (hdiag : ∀ x y, ∃ u, a u = (Sum.elim x x, Sum.elim y (-y)) ∧ (b u).1 = 0) (hb : ∀ x, ∃ u, b u = (x, 0))
    (T T' : ((κ ⊕ κ → AF F) → ℂ) →ₗ[ℂ] ((κ₂ → AF F) → ℂ))
    (hT : LinearMap.proj 0 ∘ₗ T ∈ (adeleClass F).adm (κ ⊕ κ)) (hT' : LinearMap.proj 0 ∘ₗ T' ∈ (adeleClass F).adm (κ ⊕ κ))
    (hi : ∀ u, ∀ Ψ ∈ schA F (κ ⊕ κ), T (schr ψ (a u) Ψ) = schr ψ (b u) (T Ψ))
    (hi' : ∀ u, ∀ Ψ ∈ schA F (κ ⊕ κ), T' (schr ψ (a u) Ψ) = schr ψ (b u) (T' Ψ))
    {Ψ₀ : (κ ⊕ κ → AF F) → ℂ} (hΨ₀ : Ψ₀ ∈ schA F (κ ⊕ κ)) (h0 : T' Ψ₀ 0 ≠ 0) :
    ∃ c : ℂ, ∀ Ψ ∈ schA F (κ ⊕ κ), T Ψ = c • T' Ψ := by
  have hinv : ∀ S : ((κ ⊕ κ → AF F) → ℂ) →ₗ[ℂ] ((κ₂ → AF F) → ℂ),
      (∀ u, ∀ Ψ ∈ schA F (κ ⊕ κ), S (schr ψ (a u) Ψ) = schr ψ (b u) (S Ψ)) → ∀ x y : κ → AF F, ∀ Φ ∈ schA F (κ ⊕ κ),
      (LinearMap.proj (R := ℂ) (φ := fun _ : (κ₂ → AF F) => ℂ) 0 ∘ₗ S) (schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) =
        (LinearMap.proj (R := ℂ) (φ := fun _ : (κ₂ → AF F) => ℂ) 0 ∘ₗ S) Φ := by
    intro S hS x y Φ hΦ
    obtain ⟨u, hu, hu0⟩ := hdiag x y
    simp only [LinearMap.comp_apply, LinearMap.proj_apply]
    rw [← hu, hS u Φ hΦ]
    simp [schr, hu0]
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  obtain ⟨c, hc⟩ := GlobalTheory.DiagUniq.eq_mul_diagInt F ψ hψ κ _ hT (hinv T hi) Measure.addHaar inferInstance
  obtain ⟨c', hc'⟩ := GlobalTheory.DiagUniq.eq_mul_diagInt F ψ hψ κ _ hT' (hinv T' hi') Measure.addHaar inferInstance
  simp only [LinearMap.comp_apply, LinearMap.proj_apply] at hc hc'
  have hc0 : c' ≠ 0 := fun h => h0 (by rw [hc' _ hΨ₀, h, zero_mul])
  refine ⟨c / c', fun Ψ hΨ => funext fun x => ?_⟩
  obtain ⟨u, hu⟩ := hb x
  have hm := GlobalTheory.HeisSchA.schr_mem_schA ψ hψ (a u) Ψ hΨ
  have e1 := hc _ hm
  have e2 := hc' _ hm
  rw [hi u Ψ hΨ, hu] at e1
  rw [hi' u Ψ hΨ, hu] at e2
  simp only [schr, dotProduct_zero, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul, zero_add] at e1 e2
  rw [Pi.smul_apply, smul_eq_mul, e1, e2]
  field_simp

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem keepsDiag_reindex {A β ι : Type} [CommRing A] [Fintype β] [DecidableEq β] (f : β ⊕ β ≃ ι)
    {P : Matrix (β ⊕ β) (β ⊕ β) A} {t : Matrix β β A}
    (h : P * (diagCols β : Matrix (β ⊕ β) β A) = (diagCols β : Matrix (β ⊕ β) β A) * t) :
    KeepsDiag f (Matrix.reindex f f P) ∧ leviMat f (Matrix.reindex f f P) = t := by
  have hP : (Matrix.reindex f f P).submatrix f f = P := by simp
  rw [← Matrix.fromBlocks_toBlocks P, diagCols, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul,
    Matrix.fromRows_inj.eq_iff] at h
  simp only [Matrix.mul_one, Matrix.one_mul] at h
  rw [KeepsDiag, leviMat, hP, h.1, h.2]
  exact ⟨rfl, rfl⟩

theorem mul_diagCols_transpose {A α β : Type} [CommRing A] [Fintype β] [DecidableEq β] (z : Matrix α β A) :
    z * (diagCols β : Matrix (β ⊕ β) β A)ᵀ = Matrix.fromCols z z := by
  rw [diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols, Matrix.transpose_one, Matrix.mul_one]

theorem intertwine (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {a b : ℕ} (JA : Matrix (Fin a) (Fin a) E)
    (JB : Matrix (Fin b) (Fin b) E) (ε : ℤˣ) (hJ : ∀ i j, σ (JB j i) = ((ε : ℤ) : E) * JB i j) (hdet : JB.det ≠ 0)
    (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {κ κ₂ ι : Type} [Fintype κ] [Fintype κ₂] [Fintype ι] [DecidableEq ι]
    {d : Darboux (symp (cA σ) (-1) (incM F JA) (incM F JB)) κ}
    {dd : Darboux (symp (cA σ) (-1) (incM F JA) (WeilM.dbl (incM F JB))) (κ ⊕ κ)}
    (hdd : IsDblCoord (cA σ) (-1) (incM F JA) (incM F JB) d dd) {χ : Chr F E}
    {omd : UG (cA σ) (WeilM.dbl (incM F JB)) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)}
    (hS : IsUSplitting (adeleClass F) ψ dd (actB (cA σ)) omd)
    (hR : SiegelRule (cA σ) (adeleClass F) ψ (-1) (incM F JA) (WeilM.dbl (incM F JB)) dd χ (diagCols (Fin b)) omd)
    (f : Fin b ⊕ Fin b ≃ ι) {J₂ : Matrix ι ι (AE F E)} (hJ₂ : Matrix.reindex f f (WeilM.dbl (incM F JB)) = J₂)
    {co : Darboux (symp (cA σ) (-1) (incM F JA) J₂) κ₂}
    (hΔ : ∀ u : Matrix (Fin a) ι (AE F E), (∀ i, u i ∈ diagSub (AE F E) f) → (co.e u).1 = 0)
    {om₂ : UG (cA σ) J₂ →* Module.End ℂ ((κ₂ → AF F) → ℂ)}
    (h₂ : IsUWeilB (cA σ) (adeleClass F) ψ (-1) (incM F JA) J₂ co χ om₂)
    (e : ((κ ⊕ κ → AF F) → ℂ) →ₗ[ℂ] ((κ₂ → AF F) → ℂ))
    (he : ∀ Ψ ∈ schA F (κ ⊕ κ), e Ψ ∈ schA F κ₂) {Ψ₀ : (κ ⊕ κ → AF F) → ℂ} (hΨ₀ : Ψ₀ ∈ schA F (κ ⊕ κ)) (h0 : e Ψ₀ 0 ≠ 0)
    (hadm : ∀ l ∈ (adeleClass F).adm κ₂, l ∘ₗ e ∈ (adeleClass F).adm (κ ⊕ κ))
    (hi : ∀ u : Matrix (Fin a) ι (AE F E), ∀ Ψ ∈ schA F (κ ⊕ κ), e (dd.rho ψ (u.submatrix id f) Ψ) = co.rho ψ u (e Ψ)) :
    ∀ p, ∀ Ψ ∈ schA F (κ ⊕ κ), om₂ (ugReindex f hJ₂ p) (e Ψ) = e (omd p Ψ) := by
  obtain ⟨hS₂, dd₂, omd₂, hdd₂, ⟨-, hus₂, hSR₂⟩, hbox₂⟩ := h₂
  let ρ := om₂.comp (ugReindex f hJ₂)
  have hρ : ∀ p, ρ p = om₂ (ugReindex f hJ₂ p) := fun _ => rfl
  have hev := GlobalTheory.DblEvalLaw.proj_mem_adm F κ₂ 0
  have inv_mul : ∀ p φ, omd p (omd p⁻¹ φ) = φ := fun p φ => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have ρinv : ∀ p φ, ρ p (ρ p⁻¹ φ) = φ := fun p φ => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have ρinv' : ∀ p φ, ρ p⁻¹ (ρ p φ) = φ := fun p φ => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hsp : ∀ p, ∀ φ ∈ schA F (κ ⊕ κ), omd p φ ∈ schA F (κ ⊕ κ) := fun p φ hφ => hS.pres p φ hφ
  have hi2 : ∀ w : Matrix (Fin a) (Fin b ⊕ Fin b) (AE F E), ∀ Ψ ∈ schA F (κ ⊕ κ),
      e (dd.rho ψ w Ψ) = co.rho ψ (w.submatrix id f.symm) (e Ψ) := fun w Ψ hΨ => by
    rw [← hi _ Ψ hΨ]; simp
  have hrow : ∀ (z : Matrix (Fin a) (Fin b) (AE F E)) (i : Fin a),
      ((Matrix.fromCols z z).submatrix id f.symm) i ∈ diagSub (AE F E) f := by
    intro z i
    rw [diagSub, LinearMap.mem_eqLocus]
    funext j
    simp [LinearMap.funLeft_apply]
  have key : ∀ p, ∃ c : ℂ, ∀ φ ∈ schA F (κ ⊕ κ), e (omd p φ) = c • ρ p (e φ) := fun p => by
    obtain ⟨c, hc⟩ := exists_smul_of_intertwine ψ hψ (V := Matrix (Fin a) (Fin b ⊕ Fin b) (AE F E)) dd.e
      (fun w => co.e (w.submatrix id f.symm))
      (fun x y => ⟨Matrix.fromCols (d.e.symm (x, y)) (d.e.symm (x, y)), by rw [hdd]; simp, hΔ _ (hrow _)⟩)
      (fun x => ⟨(co.e.symm (x, 0)).submatrix id f, by simp⟩)
      (ρ p⁻¹ ∘ₗ e ∘ₗ omd p) e
      (hS.adm p _ (hadm _ (hS₂.adm (ugReindex f hJ₂ p⁻¹) _ hev))) (hadm _ hev)
      (fun w φ hφ => by
        show ρ p⁻¹ (e (omd p (dd.rho ψ w φ))) = co.rho ψ (w.submatrix id f.symm) (ρ p⁻¹ (e (omd p φ)))
        rw [hS.impl p w φ hφ, hi2 _ _ (hsp p φ hφ), hρ, hS₂.impl _ _ _ (he _ (hsp p φ hφ)), actB_reindex,
          GlobalTheory.WeilSchUnique.actB_inv_actB])
      hi2 hΨ₀ h0
    refine ⟨c, fun φ hφ => ?_⟩
    have := congrArg (ρ p) (hc φ hφ)
    rwa [LinearMap.comp_apply, ρinv, map_smul] at this
  choose cf hcf using key
  have huniq : ∀ p (c : ℂ), (∀ φ ∈ schA F (κ ⊕ κ), e (omd p φ) = c • ρ p (e φ)) → c = cf p := fun p c hc => by
    have h1 := hc _ hΨ₀
    rw [hcf p _ hΨ₀] at h1
    have h2 := congrFun (congrArg (ρ p⁻¹) h1) 0
    simp only [map_smul, ρinv', Pi.smul_apply, smul_eq_mul] at h2
    exact (mul_right_cancel₀ h0 h2).symm
  have hmul : ∀ p q, cf (p * q) = cf p * cf q := fun p q => (huniq (p * q) _ fun φ hφ => by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hcf p _ (hsp q φ hφ), hcf q φ hφ, map_smul,
      smul_smul]).symm
  have hone : cf 1 = 1 := (huniq 1 1 fun φ _ => by simp).symm
  let cM : UG (cA σ) (WeilM.dbl (incM F JB)) →* ℂ := { toFun := cf, map_one' := hone, map_mul' := hmul }
  let c := cM.toHomUnits
  have hcv : ∀ p, ((c p : ℂˣ) : ℂ) = cf p := fun p => rfl
  have hcont_cf : Continuous cf := by
    refine continuous_iff_continuousAt.2 fun p₀ => ?_
    have hφ := hsp p₀⁻¹ Ψ₀ hΨ₀
    have hf := (hS₂.cont.comp (continuous_ugReindex f hJ₂)) _ hev _ (he _ hφ)
    have hf₁ := hS.cont _ (hadm _ hev) _ hφ
    simp only [LinearMap.proj_apply, LinearMap.comp_apply] at hf hf₁
    have h1 : ρ p₀ (e (omd p₀⁻¹ Ψ₀)) 0 ≠ 0 := fun h => h0 (by
      have := congrFun (hcf p₀ _ hφ) 0
      rwa [inv_mul, Pi.smul_apply, h, smul_zero] at this)
    refine (hf₁.continuousAt.div hf.continuousAt h1).congr ?_
    filter_upwards [hf.continuousAt.eventually_ne h1] with p hp
    show e (omd p _) 0 / ρ p _ 0 = cf p
    rw [hcf p _ hφ]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_div_cancel_right₀ _ hp
  have hcont : Continuous c := by
    refine Units.continuous_iff.2 ⟨hcont_cf, ?_⟩
    have : (fun p => ((c p)⁻¹ : ℂˣ).val) = fun p => (cf p)⁻¹ := funext fun p => by
      rw [Units.val_inv_eq_inv_val, hcv]
    rw [this]
    exact hcont_cf.inv₀ fun p => by rw [← hcv]; exact (c p).ne_zero
  have hP : ∀ (p : UG (cA σ) (WeilM.dbl (incM F JB))) (t : GL (Fin b) (AE F E)),
      ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix _ _ (AE F E)) * diagCols (Fin b) = diagCols (Fin b) * t.1 →
        c p = 1 := fun p t hpt => by
    have hφ := hsp p⁻¹ Ψ₀ hΨ₀
    have e1 := hR _ (hadm _ hev) (fun z φ hφ => by
      simp only [LinearMap.comp_apply, LinearMap.proj_apply]
      rw [mul_diagCols_transpose, hi2 _ φ hφ]
      simp [Darboux.rho, schr, hΔ _ (hrow z)]) p t hpt _ hφ
    obtain ⟨hk, hl⟩ := keepsDiag_reindex f hpt
    have hg : ((ugReindex f hJ₂ p : UG (cA σ) J₂) : GL ι (AE F E)) ∈ Formalism.UG.stabGL (diagSub (AE F E) f) :=
      mem_stabGL_diagSub.2 hk
    have hlev : leviGL f ⟨_, hg⟩ = t := Units.ext hl
    have e2 := GlobalTheory.DblEvalLaw.apply_zero_of_keepsDiag f (J := incM F JB) hJ₂.symm hdd₂ hus₂.toIsSplitting hSR₂ hbox₂ hΔ
      (GlobalTheory.DblEvalLaw.proj_mem_adm F _ 0) (fun φ₁ h₁ φ₂ h₂ => GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ₁ h₁ φ₂ h₂)
      (GlobalTheory.SchANonzero.exists_mem_schA_ne_zero F _) _ hg _ (he _ hφ)
    have e3 := congrFun (hcf p _ hφ) 0
    simp only [LinearMap.comp_apply, LinearMap.proj_apply] at e1
    rw [hlev, ← e1, inv_mul] at e2
    rw [inv_mul, Pi.smul_apply, smul_eq_mul, hρ, e2] at e3
    refine Units.ext ?_
    rw [hcv, Units.val_one]
    exact mul_right_cancel₀ h0 (by rw [one_mul]; exact e3.symm)
  have hc1 := GlobalTheory.SiegelChar.eq_one_of_siegel F E σ hσ b JB ε hJ hdet c hcont hP
  intro p Ψ hΨ
  have hcf1 : cf p = 1 := by rw [← hcv, hc1]; rfl
  rw [hcf p Ψ hΨ, hcf1, one_smul, hρ]

theorem om₂_left_boxC : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (Xs : Spc F E n) (W : Spc F E d) (M : Model σ Xs W) (χX χW : Chr F E) (om : Rep σ Xs W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ →
    ∀ W₂ : Spc F E (d + d), W₂.J = dblGram finSumFinEquiv W.J → W₂.L = sumLat finSumFinEquiv W.L W.L →
    (∀ w, W₂.θ w = blkMat finSumFinEquiv (W.θ w) (-W.θ w)) →
    ∀ i : UA σ W.J × UA σ W.J →* UA σ W₂.J, (∀ h h', mat (i (h, h')) = blkMat finSumFinEquiv (mat h) (mat h')) →
    ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F Xs.J) (incM F W₂.J)) (Fin n × Fin (d + d)),
      (∀ x : Matrix (Fin n) (Fin (d + d)) E, ∃ y z : Fin n × Fin (d + d) → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      (∀ u, (∀ i, u i ∈ diagSub (AE F E) finSumFinEquiv) → (co.e u).1 = 0) →
      (∀ u, (∀ i, u i ∈ antiSub (AE F E) finSumFinEquiv) → (co.e u).2 = 0) →
    ∀ om₂ : Rep σ Xs W₂, IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F Xs.J) (incM F W₂.J) co χX 1 om₂ →
    ∀ e : (((Fin n × Fin d ⊕ Fin n × Fin d) → AF F) → ℂ) →ₗ[ℂ] ((Fin n × Fin (d + d) → AF F) → ℂ),
      Set.BijOn e (schA F (Fin n × Fin d ⊕ Fin n × Fin d) : Set _) (schA F (Fin n × Fin (d + d)) : Set _) →
      (∀ l ∈ (adeleClass F).adm (Fin n × Fin (d + d)), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d)) →
      (∀ u, ∀ Ψ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), e (schr B.ψ (dblE M.co u) Ψ) = co.rho B.ψ u (e Ψ)) →
    ∀ h : UA σ W.J, ∀ Φ₁ ∈ schA F (Fin n × Fin d), ∀ Φ₂ ∈ schA F (Fin n × Fin d),
      om₂ (1, i (h, 1)) (e (boxC Φ₁ Φ₂)) = e (boxC (om (1, h) Φ₁) Φ₂) := by
  intro F E _ _ _ _ _ σ B n d Xs W M χX χW om r s' r₁ s₁ hP W₂ hW₂ _ _ i hi co _ hΔ _ om₂ hom₂ e hbij hadm hint h Φ₁ hΦ₁ Φ₂ hΦ₂
  obtain ⟨-, dd, omd, hdd, ⟨-, hS, hR⟩, hbox⟩ := hP.weil.1
  have hJ₂ : Matrix.reindex finSumFinEquiv finSumFinEquiv (WeilM.dbl (incM F W.J)) = incM F W₂.J := by
    rw [hW₂, dblGram, incM, incM, blkMat_map _ _ (map_zero _), Matrix.map_neg _ (map_neg _)]
    rfl
  obtain ⟨φ, hφ, hφ0⟩ := GlobalTheory.SchANonzero.exists_mem_schA_ne_zero F (Fin n × Fin (d + d))
  obtain ⟨Ψ₀, hΨ₀, rfl⟩ := hbij.surjOn hφ
  have key := intertwine σ hP.base.cm Xs.J W.J (-1) (fun i j => by simp [hP.skew.skew i j])
    (GlobalTheory.SkewGram.det_ne_zero F E σ B d W r₁ s₁ hP.skew) B.ψ hP.base.std hdd hS hR finSumFinEquiv hJ₂ hΔ hom₂.1 e
    (fun Ψ hΨ => hbij.mapsTo hΨ) hΨ₀ hφ0 hadm (fun u Ψ hΨ => by
      rw [← hint u Ψ hΨ, Darboux.rho, ← Matrix.fromCols_toCols (u.submatrix id finSumFinEquiv), hdd]
      rfl)
  have hs := GlobalTheory.SchAConj.star_mem_schA F _ Φ₂ hΦ₂
  have hk := key (GlobalTheory.DblEvalLaw.leftU h) _ (GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Φ₁ hΦ₁ _ hs)
  rw [hbox h _ (GlobalTheory.DblEvalLaw.val_leftU h) Φ₁ hΦ₁ _ hs] at hk
  have hih : i (h, 1) = ugReindex finSumFinEquiv hJ₂ (GlobalTheory.DblEvalLaw.leftU h) := Subtype.ext (Units.ext (hi h 1))
  rw [hih]
  exact hk

end GlobalTheory.DblWeilBox

end
