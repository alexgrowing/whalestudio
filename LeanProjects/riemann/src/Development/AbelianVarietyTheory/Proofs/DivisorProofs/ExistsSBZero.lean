import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSubAug
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEmbeddingAtEveryPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalUnipotentAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLatticeHermitianSkewStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalGoodPlaceEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalUnramifiedVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalLocalUniqueness
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormRightMulTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActsExists

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.Published
open scoped TensorProduct Matrix GlobalTheory.VacAny GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SplitTransportPair

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

omit [NumberField E] in
theorem isUnit_det_map {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (hJ : J.det ≠ 0) {v : Pl F} (t : E →ₐ[F] Fv F v) :
    IsUnit (J.map t).det := by
  rw [show J.map t = (t : E →+* Fv F v).mapMatrix J from rfl, ← RingHom.map_det]
  exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 hJ)

def pairCo (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (K : Matrix (Fin d) (Fin d) E) {v : Pl F} (t : E →ₐ[F] Fv F v)
    (u : Matrix (Fin n) (Fin d) (AE F E)) : Matrix (Fin n) (Fin d) (Fv F v) :=
  -(J.map t * u.map (piW (t.comp σ)) * (K.map t)ᵀ)

omit [NumberField E] in
theorem pairCo_eq_zero (J : Matrix (Fin n) (Fin n) E) (K : Matrix (Fin d) (Fin d) E) {v : Pl F} (t : E →ₐ[F] Fv F v)
    (u : Matrix (Fin n) (Fin d) (AE F E)) (h : u.map (piW (t.comp σ)) = 0) : pairCo σ J K t u = 0 := by
  unfold pairCo; rw [h]; simp

theorem exists_coords (hcm : IsCMExt F E σ) (J : Matrix (Fin n) (Fin n) E) (K : Matrix (Fin d) (Fin d) E)
    (hJ : J.det ≠ 0) (hK : K.det ≠ 0) (v : Pl F) (t : E →ₐ[F] Fv F v) :
    ∃ uT uM : Matrix (Fin n) (Fin d) (Fv F v) →+ Matrix (Fin n) (Fin d) (AE F E),
      (∀ Y, At (evFin F v) (uT Y) ∧ (uT Y).map (piW (t.comp σ)) = 0 ∧ (uT Y).map (piW t) = Y) ∧
      (∀ z, At (evFin F v) (uM z) ∧ (uM z).map (piW t) = 0 ∧ pairCo σ J K t (uM z) = z) ∧
      (∀ u, At (evFin F v) u → ∃ Y z, u = uT Y + uM z) := by
  have hP : IsUnit (J.map t).det := isUnit_det_map J hJ t
  have hQ : IsUnit ((K.map t)ᵀ).det := by
    rw [Matrix.det_transpose]
    exact isUnit_det_map K hK t
  set P := J.map t with hPdef
  set Q := (K.map t)ᵀ with hQdef
  let L := GlobalTheory.LinBarCoords.liftM σ hcm (m := Fin n) (n := Fin d) v t
  let uT : Matrix (Fin n) (Fin d) (Fv F v) →+ Matrix (Fin n) (Fin d) (AE F E) :=
    AddMonoidHom.mk' (fun Y => L (Y, 0)) (fun Y Y' => by rw [← map_add, Prod.mk_add_mk, add_zero])
  let uM : Matrix (Fin n) (Fin d) (Fv F v) →+ Matrix (Fin n) (Fin d) (AE F E) :=
    AddMonoidHom.mk' (fun z => L (0, -(P⁻¹ * z * Q⁻¹))) (fun z z' => by
      rw [Matrix.mul_add, Matrix.add_mul, neg_add, ← map_add, Prod.mk_add_mk, add_zero])
  have hco : ∀ u, pairCo σ J K t u = -(P * u.map (piW (t.comp σ)) * Q) := fun u => rfl
  have hTc : ∀ Y, (uT Y).map (piW (t.comp σ)) = 0 := fun Y => GlobalTheory.LinBarCoords.liftM_snd σ hcm v t _
  have hTt : ∀ Y, (uT Y).map (piW t) = Y := fun Y => GlobalTheory.LinBarCoords.liftM_fst σ hcm v t _
  have hMc : ∀ z, (uM z).map (piW (t.comp σ)) = -(P⁻¹ * z * Q⁻¹) := fun z => GlobalTheory.LinBarCoords.liftM_snd σ hcm v t _
  have hMt : ∀ z, (uM z).map (piW t) = 0 := fun z => GlobalTheory.LinBarCoords.liftM_fst σ hcm v t _
  have hTa : ∀ Y, At (evFin F v) (uT Y) := fun Y => GlobalTheory.LinBarCoords.liftM_at σ hcm v t _
  have hMa : ∀ z, At (evFin F v) (uM z) := fun z => GlobalTheory.LinBarCoords.liftM_at σ hcm v t _
  refine ⟨uT, uM, fun Y => ⟨hTa Y, hTc Y, hTt Y⟩, fun z => ⟨hMa z, hMt z, ?_⟩, fun u hu => ?_⟩
  · have e1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hP
    have e2 : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul _ hQ
    rw [hco, hMc, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    simp only [← Matrix.mul_assoc, e1, Matrix.one_mul]
    simp only [Matrix.mul_assoc, e2, Matrix.mul_one]
  · refine ⟨u.map (piW t), pairCo σ J K t u, ?_⟩
    have hd : At (evFin F v) (u - (uT (u.map (piW t)) + uM (pairCo σ J K t u))) := by
      intro c hc
      rw [smul_sub, smul_add, hu c hc, hTa _ c hc, hMa _ c hc, add_zero, sub_zero]
    refine (sub_eq_zero.1 (GlobalTheory.LinBarCoords.eq_zero_of_at σ hcm v t hd ?_ ?_))
    · rw [Matrix.map_sub _ (map_sub _), Matrix.map_add _ (map_add _), hTt, hMt, add_zero, sub_self]
    · rw [Matrix.map_sub _ (map_sub _), Matrix.map_add _ (map_add _), hTc, hMc, zero_add, hco, Matrix.mul_neg, Matrix.neg_mul,
        neg_neg, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQ, Matrix.mul_one, ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hP, Matrix.one_mul, sub_self]

theorem symp_coords (hcm : IsCMExt F E σ) (J : Matrix (Fin n) (Fin n) E) (K : Matrix (Fin d) (Fin d) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (hK : ∀ i j, σ (K j i) = -K i j) (v : Pl F) (t : E →ₐ[F] Fv F v)
    (x u : Matrix (Fin n) (Fin d) (AE F E)) (hx : At (evFin F v) x) :
    evFin F v (symp (cA σ) (-1) (incM F J) (incM F K) x u) =
      ∑ i, ∑ j, (x.map (piW t)) i j * pairCo σ J K t u i j - ∑ i, ∑ j, pairCo σ J K t x i j * (u.map (piW t)) i j :=
  GlobalTheory.T.local_lattice_hermitian_skew hcm v t J K hJ hK x u hx

variable {X : Spc F E n} {W : Spc F E d}

open GlobalTheory.LinWAt in

theorem exists_isLinW (hcm : IsCMExt F E σ) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hstd : IsStd ψ)
    (hXh : ∀ i j, σ (X.J j i) = X.J i j) (hXd : X.J.det ≠ 0) (hWh : ∀ i j, σ (W.J j i) = -W.J i j) (hWd : W.J.det ≠ 0)
    (v : Pl F) (t : E →ₐ[F] Fv F v) :
    ∃ ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ), M.IsLinW ψ t 1 1 ι := by
  obtain ⟨uT, uM, hT, hM, hspan⟩ := exists_coords hcm X.J W.J hXd hWd v t
  have hsymp := symp_coords hcm X.J W.J hXh hWh v t
  have hψc : Continuous (GlobalTheory.LatVac.psiAt ψ v) := GlobalTheory.VacAny.continuous_psiV hstd.1 v
  have hψ1 : GlobalTheory.LatVac.psiAt ψ v ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one _ hstd v
  have hcoT : ∀ Y, pairCo σ X.J W.J t (uT Y) = 0 := fun Y => pairCo_eq_zero _ _ t _ (hT Y).2.1
  haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F _).injective
  obtain ⟨ι, hbij, htr, hmu⟩ := GlobalTheory.T.lagrangian_decomposition_weil (GlobalTheory.LatVac.psiAt ψ v) hψc hψ1
    ((GlobalTheory.LatVac.locCo M.co v).comp uT) ((GlobalTheory.LatVac.locCo M.co v).comp uM)
    (fun Y Y' => by
      simp only [AddMonoidHom.comp_apply]
      rw [locCo_form, hsymp _ _ (hT Y).1, hcoT, hcoT]
      simp)
    (fun z z' => by
      simp only [AddMonoidHom.comp_apply]
      rw [locCo_form, hsymp _ _ (hM z).1, (hM z).2.1, (hM z').2.1]
      simp)
    (fun Y z => by
      simp only [AddMonoidHom.comp_apply]
      rw [locCo_form, hsymp _ _ (hT Y).1, (hT Y).2.2, (hM z).2.2, hcoT, (hM z).2.1]
      simp)
    (fun w => by
      obtain ⟨u, hu, rfl⟩ := locCo_surj M.co v w
      obtain ⟨Y, z, rfl⟩ := hspan u hu
      exact ⟨Y, z, by simp only [AddMonoidHom.comp_apply, map_add]⟩)
  have hφ₁ : ∀ (u : Matrix (Fin n) (Fin d) (AE F E)), At (evFin F v) u →
      ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ₁, Acts (evFin F v) (M.co.rho ψ u) φ φ₁ →
        φ₁ = GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo M.co v u) φ :=
    fun u hu φ hφ φ₁ hact => GlobalTheory.TensUniq.eq_of_tens_eq v φ φ₁ _ hφ fun r hr =>
      (hact r hr).symm.trans (GlobalTheory.VacBridge.rho_acts_locCo M.co ψ v u hu φ r hr)
  refine ⟨ι, hbij, ?_, ?_⟩
  · intro u hu hu0 φ hφ φ₁ _ hact Y
    have e1 := hφ₁ u hu φ hφ φ₁ hact
    obtain ⟨Y₀, z, rfl⟩ := hspan u hu
    have hz : z = 0 := by
      have h := hu0
      rw [Matrix.map_add _ (map_add _), (hT Y₀).2.1, zero_add] at h
      rw [← (hM z).2.2]
      exact pairCo_eq_zero _ _ t _ h
    subst hz
    rw [map_zero, add_zero] at e1 ⊢
    rw [co_one, (hT Y₀).2.2, e1]
    exact congrFun (htr Y₀ φ hφ) Y
  · intro u hu hu1 φ hφ φ₁ _ hact x hx hx0
    have e1 := hφ₁ u hu φ hφ φ₁ hact
    obtain ⟨Y₀, z, rfl⟩ := hspan u hu
    have hY : Y₀ = 0 := by
      have h := hu1
      rw [Matrix.map_add _ (map_add _), (hM z).2.1, add_zero] at h
      rw [← (hT Y₀).2.2]
      exact h
    subst hY
    rw [map_zero, zero_add] at e1 ⊢
    rw [co_one, e1, GlobalTheory.VacIndic.psi_of_at ψ (at_symp _ _ _ x (uM z) hx), hsymp x (uM z) hx,
      pairCo_eq_zero _ _ t x hx0, (hM z).2.1, (hM z).2.2]
    have h2 := congrFun (hmu z φ hφ) (x.map (piW t))
    simp only [AddMonoidHom.comp_apply] at h2
    rw [h2, ← GlobalTheory.LatVac.psiAt_apply]
    congr 2
    simp

theorem shape (hcm : IsCMExt F E σ) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hstd : IsStd ψ)
    (hXh : ∀ i j, σ (X.J j i) = X.J i j) (hXd : X.J.det ≠ 0) (hWh : ∀ i j, σ (W.J j i) = -W.J i j) (hWd : W.J.det ≠ 0)
    (χX χW : Chr F E) (om : Rep σ X W) (hWeil : M.IsWeil ψ χX χW om) (v : Pl F) (t : E →ₐ[F] Fv F v)
    (ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)) (hι : M.IsLinW ψ t 1 1 ι)
    (g : UA σ X.J) (h : UA σ W.J)
    (hex : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∃ φ₁ ∈ SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (om (g, h)) φ φ₁) :
    ∃ c : ℂ, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁, Acts (evFin F v) (om (g, h)) φ φ₁ →
      ∀ Y : Matrix (Fin n) (Fin d) (Fv F v), ι φ₁ ((mat g).map (piW t) * Y * ((mat h).map (piW t))ᵀ) = c * ι φ Y := by
  have hψc : Continuous (GlobalTheory.LatVac.psiAt ψ v) := GlobalTheory.SchrSB.continuous_psiAt _ hstd.1 v
  have hψ1 : GlobalTheory.LatVac.psiAt ψ v ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one _ hstd v
  have hSplit := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hWeil
  have hex' : ∀ φ, ∃ φ₁, φ ∈ SB (Fin n × Fin d → Fv F v) →
      φ₁ ∈ SB (Fin n × Fin d → Fv F v) ∧ Acts (evFin F v) (om (g, h)) φ φ₁ := by
    intro φ
    by_cases hφ : φ ∈ SB (Fin n × Fin d → Fv F v)
    · obtain ⟨φ₁, hφ₁⟩ := hex φ hφ
      exact ⟨φ₁, fun _ => hφ₁⟩
    · exact ⟨0, fun h' => absurd h' hφ⟩
  choose A hA using hex'
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (Fin n × Fin d) v
  have hinv := (hR 0 (Submodule.zero_mem _)).1
  have huniq : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁, Acts (evFin F v) (om (g, h)) φ φ₁ → φ₁ = A φ :=
    fun φ hφ φ₁ hB => GlobalTheory.UnitWShape.eq_of_tens_eq v R hR0 hinv φ₁ (A φ)
      ((hB R (hR φ hφ)).symm.trans ((hA φ hφ).2 R (hR φ hφ)))
  have hASB : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), A φ ∈ SB (Fin n × Fin d → Fv F v) := fun φ hφ => (hA φ hφ).1
  have hlin : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ' ∈ SB (Fin n × Fin d → Fv F v), ∀ c : ℂ,
      A (c • φ + φ') = c • A φ + A φ' := by
    intro x hx y hy c
    have hz : c • x + y ∈ SB (Fin n × Fin d → Fv F v) := add_mem (Submodule.smul_mem _ c hx) hy
    apply GlobalTheory.UnitWShape.eq_of_tens_eq v R hR0 hinv
    rw [← (hA _ hz).2 R (hR _ hz), GlobalTheory.UnitWShape.tens_add_smul, map_add, map_smul, (hA x hx).2 R (hR x hx),
      (hA y hy).2 R (hR y hy), ← GlobalTheory.UnitWShape.tens_add_smul]
  have atMul : ∀ (P : Matrix (Fin n) (Fin n) (AE F E)) (Q : Matrix (Fin d) (Fin d) (AE F E))
      (γ : Matrix (Fin n) (Fin d) (AE F E)), At (evFin F v) γ → At (evFin F v) (P * γ * Q) := by
    intro P Q γ hγ u hu
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hγ u hu, Matrix.mul_zero, Matrix.zero_mul]
  have hsb : ∀ (w : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) (φ : (Fin n × Fin d → Fv F v) → ℂ),
      φ ∈ SB (Fin n × Fin d → Fv F v) → schr (GlobalTheory.LatVac.psiAt ψ v) w φ ∈ SB (Fin n × Fin d → Fv F v) :=
    fun w φ hφ => GlobalTheory.SchrSB.schr_mem_SB ψ hstd.1 v w φ hφ
  have hcov : ∀ γ : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) γ → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      A (schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo M.co v γ) φ) =
        schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo M.co v (mat g * γ * (mat h)ᵀ)) (A φ) := by
    intro γ hγ φ hφ
    have hψ₁ := hsb (GlobalTheory.LatVac.locCo M.co v γ) φ hφ
    apply GlobalTheory.UnitWShape.eq_of_tens_eq v R hR0 hinv
    have e1 := GlobalTheory.VacBridge.rho_acts_locCo M.co ψ v γ hγ φ R (hR φ hφ)
    have e2 := hSplit.impl (g, h) γ _ (hR φ hφ).2
    rw [← (hA _ hψ₁).2 R (hR _ hψ₁), ← e1, e2, (hA φ hφ).2 R (hR φ hφ)]
    exact GlobalTheory.VacBridge.rho_acts_locCo M.co ψ v _ (atMul _ _ γ hγ) (A φ) R (hR _ (hASB φ hφ))

  have hL := hι
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLinW at hL
  simp only [inv_one, Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at hL
  have hT : ∀ γ : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) γ → γ.map (piW (t.comp σ)) = 0 →
      ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ Y,
        ι (schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo M.co v γ) φ) Y = ι φ (Y + γ.map (piW t)) :=
    fun γ hγ h0 φ hφ Y => hL.trans γ hγ h0 φ hφ _ (hsb _ φ hφ) (GlobalTheory.VacBridge.rho_acts_locCo M.co ψ v γ hγ φ) Y
  have hM : ∀ γ : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) γ → γ.map (piW t) = 0 →
      ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ x : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) x →
        x.map (piW (t.comp σ)) = 0 →
        ι (schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo M.co v γ) φ) (x.map (piW t)) =
          ψ (symp (cA σ) (-1) (incM F X.J) (incM F W.J) x γ) * ι φ (x.map (piW t)) :=
    fun γ hγ h0 φ hφ x hx hx0 =>
      hL.mult γ hγ h0 φ hφ _ (hsb _ φ hφ) (GlobalTheory.VacBridge.rho_acts_locCo M.co ψ v γ hγ φ) x hx hx0
  obtain ⟨uT, uM, hT', hM', -⟩ := exists_coords hcm X.J W.J hXd hWd v t
  let Lm : (Matrix (Fin n) (Fin d) (Fv F v) →ₗ[Fv F v] Fv F v) → Matrix (Fin n) (Fin d) (Fv F v) :=
    fun l => Matrix.of fun k j => l (Matrix.single k j 1)
  have hchar : ∀ (l : Matrix (Fin n) (Fin d) (Fv F v) →ₗ[Fv F v] Fv F v) (Y : Matrix (Fin n) (Fin d) (Fv F v)),
      ψ (symp (cA σ) (-1) (incM F X.J) (incM F W.J) (uT Y) (uM (Lm l))) = GlobalTheory.LatVac.psiAt ψ v (l Y) := by
    intro l Y
    rw [GlobalTheory.VacIndic.psi_of_at ψ (GlobalTheory.LinWAt.at_symp _ _ _ (uT Y) (uM (Lm l)) (hT' Y).1),
      symp_coords hcm X.J W.J hXh hWh v t _ _ (hT' Y).1, (hM' _).2.1, (hM' _).2.2, (hT' Y).2.2,
      GlobalTheory.ShapeUV.linForm_sum l Y, ← GlobalTheory.LatVac.psiAt_apply]
    congr 1
    simp [Lm]
  have hmap : ∀ (τ : E →ₐ[F] Fv F v) (γ : Matrix (Fin n) (Fin d) (AE F E)),
      (mat g * γ * (mat h)ᵀ).map (piW τ) = (mat g).map (piW τ) * γ.map (piW τ) * ((mat h).map (piW τ))ᵀ := by
    intro τ γ
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  have hinvar : ∀ x y : Matrix (Fin n) (Fin d) (AE F E),
      symp (cA σ) (-1) (incM F X.J) (incM F W.J) (mat g * x * (mat h)ᵀ) (mat g * y * (mat h)ᵀ) =
        symp (cA σ) (-1) (incM F X.J) (incM F W.J) x y := by
    intro x y
    have hU : (mat g)ᵀ * incM F X.J * (mat g).map (cA σ) = incM F X.J := g.2
    have hU' : (mat h)ᵀ * incM F W.J * (mat h).map (cA σ) = incM F W.J := h.2
    rw [GlobalTheory.SympRight.symp_mul_transpose_right, hU', GlobalTheory.ShapeUV.symp_mul_mul _ _ _ _ _ hU]
  set gt := (mat g).map (piW t) with hgt
  set ht := (mat h).map (piW t) with hht
  obtain ⟨c, hc⟩ := GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat (SB (Fin n × Fin d → Fv F v)) (GlobalTheory.LatVac.psiAt ψ v) hψc hψ1 ι
    (fun φ (Y : Matrix (Fin n) (Fin d) (Fv F v)) => ι (A φ) (gt * Y * htᵀ)) hL.bij
    (fun x hx y hy c => by
      funext Y
      simp only [hlin x hx y hy c, map_add, map_smul, Pi.add_apply, Pi.smul_apply])
    (fun C => schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo M.co v (uT C)))
    (fun l => schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo M.co v (uM (Lm l))))
    (fun C x hx => by
      refine ⟨hsb _ x hx, ?_, ?_⟩
      · funext Y
        rw [hT _ (hT' C).1 (hT' C).2.1 x hx Y, (hT' C).2.2]
      · funext Y
        have h0 : (mat g * uT C * (mat h)ᵀ).map (piW (t.comp σ)) = 0 := by
          rw [hmap, (hT' C).2.1, Matrix.mul_zero, Matrix.zero_mul]
        rw [hcov _ (hT' C).1 x hx, hT _ (atMul _ _ _ (hT' C).1) h0 (A x) (hASB x hx), hmap, (hT' C).2.2,
          Matrix.mul_add, Matrix.add_mul])
    (fun l x hx => by
      refine ⟨hsb _ x hx, ?_, ?_⟩
      · funext Y
        have hm := hM _ (hM' (Lm l)).1 (hM' _).2.1 x hx (uT Y) (hT' Y).1 (hT' Y).2.1
        rw [(hT' Y).2.2, hchar] at hm
        exact hm
      · funext Y
        have h0 : (mat g * uM (Lm l) * (mat h)ᵀ).map (piW t) = 0 := by
          rw [hmap, (hM' _).2.1, Matrix.mul_zero, Matrix.zero_mul]
        have h1 : (mat g * uT Y * (mat h)ᵀ).map (piW (t.comp σ)) = 0 := by
          rw [hmap, (hT' Y).2.1, Matrix.mul_zero, Matrix.zero_mul]
        have hm := hM _ (atMul _ _ _ (hM' (Lm l)).1) h0 (A x) (hASB x hx) _ (atMul _ _ _ (hT' Y).1) h1
        rw [hinvar, hchar, hmap, (hT' Y).2.2] at hm
        rw [hcov _ (hM' _).1 x hx]
        exact hm)
  refine ⟨c, fun φ hφ φ₁ hact Y => ?_⟩
  rw [huniq φ hφ φ₁ hact]
  exact congrFun (hc φ hφ) Y

theorem one_mem_UAt (X : Spc F E n) (v : Pl F) : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := by
  intro u _
  show u • (mat (1 : UA σ X.J) - 1) = 0
  rw [show mat (1 : UA σ X.J) = 1 from rfl, sub_self, smul_zero]

omit [NumberField E] in
theorem mat_one_map (X : Spc F E n) {v : Pl F} (t : E →ₐ[F] Fv F v) : (mat (1 : UA σ X.J)).map (piW t) = 1 := by
  rw [show mat (1 : UA σ X.J) = 1 from rfl, Matrix.map_one _ (map_zero _) (map_one _)]

theorem exists_SB_zero (v : Pl F) (n d : ℕ) : ∃ f ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)), f 0 ≠ 0 := by
  obtain ⟨Λ, -, f, hf, hne⟩ := GlobalTheory.T.exists_translation_invariant_functional F v n d
  obtain ⟨Y₀, hY⟩ : ∃ Y₀, f Y₀ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hne (by rw [show f = 0 from funext hc, map_zero])
  exact ⟨fun Y => f (Y + Y₀), ⟨hf.1.comp_continuous (continuous_add_const Y₀),
    hf.2.comp_homeomorph (Homeomorph.addRight Y₀)⟩, by simpa using hY⟩

theorem left_action (hcm : IsCMExt F E σ) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hstd : IsStd ψ)
    (hXh : ∀ i j, σ (X.J j i) = X.J i j) (hXd : X.J.det ≠ 0) (hWh : ∀ i j, σ (W.J j i) = -W.J i j) (hWd : W.J.det ≠ 0)
    (χX χW : Chr F E) (om : Rep σ X W) (hWeil : M.IsWeil ψ χX χW om) (v : Pl F) (t : E →ₐ[F] Fv F v)
    (ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)) (hι : M.IsLinW ψ t 1 1 ι)
    (g : UA σ X.J) (hg : g ∈ UAt σ X (evFin F v)) (g' : GL (Fin n) (Fv F v)) (hg' : (mat g).map (piW t) = g'.1)
    (hex : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∃ φ₁ ∈ SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁) :
    ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁, Acts (evFin F v) (om (g, 1)) φ φ₁ →
      ι φ₁ = (((chrW χW (t.comp σ) (Matrix.GeneralLinearGroup.det g'))⁻¹ : ℂˣ) : ℂ) •
        GlobalTheory.SplitWeil.om 1 (1 : GL (Fin d) (Fv F v)) g' (ι φ) := by
  obtain ⟨c, hc⟩ := shape hcm M ψ hstd hXh hXd hWh hWd χX χW om hWeil v t ι hι g 1 hex
  simp only [hg', mat_one_map, Matrix.transpose_one, Matrix.mul_one] at hc
  have hJ := isUnit_det_map X.J hXd t
  have g2 : Units.val ((Matrix.GeneralLinearGroup.det g')⁻¹ : (Fv F v)ˣ) = ((mat g).map (piW (t.comp σ))).det := by
    have u := congrArg Matrix.det (GlobalTheory.UnitaryInjAtPlace.unitary_at_components v t g)
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hg'] at u
    have u' : (g'.1.det * ((mat g).map (piW (t.comp σ))).det) * (X.J.map t).det = 1 * (X.J.map t).det := by
      linear_combination u
    have u'' := mul_right_cancel₀ hJ.ne_zero u'
    exact Units.inv_eq_of_mul_eq_one_right (u := Matrix.GeneralLinearGroup.det g') u''
  obtain ⟨f, hf, hf0⟩ := exists_SB_zero v n d
  obtain ⟨φ₀, hφ₀, rfl⟩ := hι.bij.surjOn hf
  obtain ⟨φ₀', -, hA₀⟩ := hex φ₀ hφ₀
  have k1 := GlobalTheory.MixedForm.lin_zero hcm M ψ hstd χX χW om hWeil t ι hι g hg (Matrix.GeneralLinearGroup.det g')⁻¹ g2 φ₀ φ₀' hφ₀ hA₀
  have k2 := hc φ₀ hφ₀ φ₀' hA₀ 0
  rw [Matrix.mul_zero, k1] at k2
  have k3 := mul_right_cancel₀ hf0 k2
  intro φ hφ φ₁ hA
  funext Y
  have e := hc φ hφ φ₁ hA ((g'⁻¹).1 * Y)
  rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, ← k3] at e
  have hn : GlobalTheory.SplitWeil.nabs (Fv F v) (Matrix.GeneralLinearGroup.det g')⁻¹ ^ ((d : ℝ) / 2) =
      GlobalTheory.SplitWeil.nabs (Fv F v) (Matrix.GeneralLinearGroup.det g') ^ (-(d : ℝ) / 2) := by
    have h0 : 0 ≤ GlobalTheory.SplitWeil.nabs (Fv F v) (Matrix.GeneralLinearGroup.det g') := NNReal.coe_nonneg _
    rw [neg_div, Real.rpow_neg h0, ← Real.inv_rpow h0]
    simp [GlobalTheory.SplitWeil.nabs]
  rw [e, hn, map_inv]
  simp only [GlobalTheory.SplitWeil.om, Pi.smul_apply, smul_eq_mul, map_one, MonoidHom.one_apply, Units.val_one, inv_one,
    one_mul, Matrix.mul_one, Fintype.card_fin]
  simp only [GlobalTheory.SplitWeil.nabs, map_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_mul, mul_assoc]

theorem right_action (hcm : IsCMExt F E σ) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hstd : IsStd ψ)
    (hXh : ∀ i j, σ (X.J j i) = X.J i j) (hXd : X.J.det ≠ 0) (hWh : ∀ i j, σ (W.J j i) = -W.J i j) (hWd : W.J.det ≠ 0)
    (χX χW : Chr F E) (om : Rep σ X W) (hWeil : M.IsWeil ψ χX χW om) (v : Pl F) (t : E →ₐ[F] Fv F v)
    (ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)) (hι : M.IsLinW ψ t 1 1 ι)
    (h : UA σ W.J) (g : GL (Fin d) (Fv F v)) (hg : (mat h).map (piW t) = (GlobalTheory.SplitFlip.invT g).1)
    (hex : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∃ φ₁ ∈ SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁) :
    ∃ s : ℂ, s ≠ 0 ∧ ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁, Acts (evFin F v) (om (1, h)) φ φ₁ →
      ι φ₁ = s • GlobalTheory.SplitWeil.om 1 g (1 : GL (Fin n) (Fv F v)) (ι φ) := by
  obtain ⟨c, hc⟩ := shape hcm M ψ hstd hXh hXd hWh hWd χX χW om hWeil v t ι hι 1 h hex
  simp only [hg, mat_one_map, Matrix.one_mul, GlobalTheory.SplitFlip.invT_val, Matrix.transpose_transpose] at hc
  have hc' : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁, Acts (evFin F v) (om (1, h)) φ φ₁ →
      ∀ Y, ι φ₁ Y = c * ι φ (Y * g.1) := by
    intro φ hφ φ₁ hA Y
    rw [← hc φ hφ φ₁ hA, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨f, hf, hf0⟩ := exists_SB_zero v n d
    obtain ⟨φ₀, hφ₀, rfl⟩ := hι.bij.surjOn hf
    obtain ⟨φ₁, hφ₁, hA⟩ := hex φ₀ hφ₀
    have h1 : φ₁ = 0 := hι.bij.injOn hφ₁ (Submodule.zero_mem _) (by
      funext Y; rw [hc' φ₀ hφ₀ φ₁ hA, map_zero]; simp)
    have h2 : φ₀ = 0 := GlobalTheory.TensUniq.eq_of_tens_eq v φ₀ φ₀ 0 hφ₀ fun r hr => by
      have e := hA r hr
      have z : tens (evFin F v) (0 : (Fin n × Fin d → Fv F v) → ℂ) r = 0 := by
        funext x; simp [tens]
      rw [h1, z] at e
      have e2 := congrArg (om (1, h)⁻¹) e
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero, Module.End.one_apply] at e2
      rw [e2, z]
    exact hf0 (by rw [h2, map_zero]; rfl)
  have h2 : ((GlobalTheory.SplitWeil.nabs (Fv F v) (Matrix.GeneralLinearGroup.det g) ^ ((n : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
    have := GlobalTheory.SplitWeil.Model.nabs_pos (Matrix.GeneralLinearGroup.det g)
    exact_mod_cast (Real.rpow_pos_of_pos this _).ne'
  refine ⟨c / ((GlobalTheory.SplitWeil.nabs (Fv F v) (Matrix.GeneralLinearGroup.det g) ^ ((n : ℝ) / 2) : ℝ) : ℂ),
    div_ne_zero hc0 h2, fun φ hφ φ₁ hA => ?_⟩
  funext Y
  rw [hc' φ hφ φ₁ hA]
  have h1 : GlobalTheory.SplitWeil.nabs (Fv F v) 1 = 1 := by simp [GlobalTheory.SplitWeil.nabs]
  simp only [GlobalTheory.SplitWeil.om, Pi.smul_apply, smul_eq_mul, map_one, MonoidHom.one_apply, Units.val_one, inv_one,
    one_mul, Matrix.one_mul, Fintype.card_fin, h1, Real.one_rpow, Complex.ofReal_one, mul_one]
  field_simp

theorem transport : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      1 ≤ n → 1 ≤ d → ∀ v : Pl F, Nonempty (E →ₐ[F] Fv F v) →
      ∃ (χ : GL (Fin n) (Fv F v) →* ℂˣ) (ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)),
        IsOpen {g | χ g = 1} ∧
        Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _) ∧
        ∀ N : Submodule ℂ ((Fin n × Fin d → Fv F v) → ℂ), N ≤ SB _ → (ThetaSub om v N ↔ GlobalTheory.ThetaGLSub.IsSub χ (N.map ι)) := by
  intro hP F E _ _ _ _ _ σ hcm n d X W M ψ χX χW om hstd hXh hXd hWh hWd hrX hrW hχX hχW hWeil _ _ v ⟨t⟩
  obtain ⟨ι, hι⟩ := exists_isLinW hcm M ψ hstd hXh hXd hWh hWd v t
  have hloc := (GlobalTheory.LocalOpsW.ops hP F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWh hWd hrX hrW hχX hχW hWeil v).1
  have hex : ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ∃ φ₁ ∈ SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (om (g, h)) φ φ₁ :=
    fun g hg h hh φ hφ => (hloc g hg h hh φ hφ).exists
  have surjX : ∀ g' : GL (Fin n) (Fv F v), ∃ g ∈ UAt σ X (evFin F v), (mat g).map (piW t) = g'.1 := by
    intro g'
    have herm : ∀ i j, σ (X.J j i) = algebraMap F E 1 * X.J i j := fun i j => by
      rw [map_one, one_mul]; exact hXh i j
    exact ⟨_, GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm t X 1 herm (isUnit_det_map _ hXd t) g',
      GlobalTheory.SplitUnitLift.liftU_piW hcm t X.J 1 herm (isUnit_det_map _ hXd t) g'⟩
  have surjW : ∀ g' : GL (Fin d) (Fv F v), ∃ g ∈ UAt σ W (evFin F v), (mat g).map (piW t) = g'.1 := by
    intro g'
    have herm : ∀ i j, σ (W.J j i) = algebraMap F E (-1) * W.J i j := fun i j => by
      rw [map_neg, map_one, neg_one_mul]; exact hWh i j
    exact ⟨_, GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm t W (-1) herm (isUnit_det_map _ hWd t) g',
      GlobalTheory.SplitUnitLift.liftU_piW hcm t W.J (-1) herm (isUnit_det_map _ hWd t) g'⟩
  have hνs : GlobalTheory.SmGL.IsSmoothChar (chrW χW (t.comp σ)) :=
    GlobalTheory.RootEx.UniformLattices.isOpen_ker_of_continuous _ (GlobalTheory.ChrWSmooth.continuous_chrW hχW.1 _)
  set χ : GL (Fin n) (Fv F v) →* ℂˣ := GlobalTheory.SmGL.detChar (Fin n) (chrW χW (t.comp σ)) with hχ
  have hχv : ∀ g, χ g = chrW χW (t.comp σ) (Matrix.GeneralLinearGroup.det g) := fun g => rfl
  have hbij := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLin.bij hι
  have hinj := hbij.injOn
  have hmaps : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ι φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) (Fv F v)) :=
    fun φ hφ => hbij.mapsTo hφ
  refine ⟨χ, ι, ?_, hbij, ?_⟩
  · have := hνs.detChar (n := Fin n)
    exact this
  intro N hN

  have hAugSB : augAt om v ≤ SB (Fin n × Fin d → Fv F v) := by
    rw [augAt, Submodule.span_le]
    rintro _ ⟨g, hg, φ, hφ, φ₁, hφ₁, -, rfl⟩
    exact Submodule.sub_mem _ hφ₁ hφ
  have hVsc : ∀ g ∈ UAt σ X (evFin F v), ∀ g' : GL (Fin n) (Fv F v), (mat g).map (piW t) = g'.1 →
      ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁, Acts (evFin F v) (om (g, 1)) φ φ₁ →
        ι (φ₁ - φ) = (((χ g')⁻¹ : ℂˣ) : ℂ) • (GlobalTheory.SplitWeil.om 1 1 g' (ι φ) - (χ g' : ℂ) • ι φ) := by
    intro g hg g' hg' φ hφ φ₁ hA
    rw [map_sub, left_action hcm M ψ hstd hXh hXd hWh hWd χX χW om hWeil v t ι hι g hg g' hg'
      (hex g hg 1 (one_mem_UAt W v)) φ hφ φ₁ hA, smul_sub, smul_smul, hχv]
    simp
  have hmapAug : (augAt om v).map ι = GlobalTheory.ThetaGLSub.aug d χ := by
    apply le_antisymm
    · rw [augAt, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨g, hg, φ, hφ, φ₁, hφ₁, hA, rfl⟩, rfl⟩
      have e := hVsc g hg (Matrix.GeneralLinearGroup.map (piW t) g.1) rfl φ hφ φ₁ hA
      rw [SetLike.mem_coe, e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ι φ, hmaps φ hφ, rfl⟩)
    · rw [GlobalTheory.ThetaGLSub.aug, Submodule.span_le]
      rintro _ ⟨g', Φ, hΦ, rfl⟩
      obtain ⟨φ, hφ, rfl⟩ := hbij.surjOn hΦ
      obtain ⟨g, hg, hgt⟩ := surjX g'
      obtain ⟨φ₁, hφ₁, hA⟩ := hex g hg 1 (one_mem_UAt W v) φ hφ
      have e := hVsc g hg g' hgt φ hφ φ₁ hA
      refine ⟨(χ g' : ℂ) • (φ₁ - φ), Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, hg, φ, hφ, φ₁, hφ₁, hA, rfl⟩), ?_⟩
      rw [map_smul, e, smul_smul]
      simp
  have hiffAug : augAt om v ≤ N ↔ GlobalTheory.ThetaGLSub.aug d χ ≤ N.map ι := by
    rw [← hmapAug]
    refine ⟨Submodule.map_mono, fun h x hx => ?_⟩
    obtain ⟨y, hy, e⟩ := Submodule.mem_map.1 (h (Submodule.mem_map_of_mem hx))
    rwa [hinj (hN hy) (hAugSB hx) e] at hy

  have hiffW : (∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ N, ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → φ₁ ∈ N) ↔
      ∀ g : GL (Fin d) (Fv F v), ∀ Φ ∈ N.map ι, GlobalTheory.SplitWeil.om 1 g (1 : GL (Fin n) (Fv F v)) Φ ∈ N.map ι := by
    constructor
    · intro H g Φ hΦ
      obtain ⟨φ, hφN, rfl⟩ := Submodule.mem_map.1 hΦ
      obtain ⟨h, hh, hht⟩ := surjW (GlobalTheory.SplitFlip.invT g)
      obtain ⟨φ₁, hφ₁, hA⟩ := hex 1 (one_mem_UAt X v) h hh φ (hN hφN)
      obtain ⟨s, hs0, hs⟩ := right_action hcm M ψ hstd hXh hXd hWh hWd χX χW om hWeil v t ι hι h g hht
        (hex 1 (one_mem_UAt X v) h hh)
      have h1 : ι φ₁ ∈ N.map ι := Submodule.mem_map_of_mem (H h hh φ hφN φ₁ hφ₁ hA)
      rw [hs φ (hN hφN) φ₁ hA] at h1
      exact (Submodule.smul_mem_iff _ hs0).1 h1
    · intro H h hh φ hφN φ₁ hφ₁ hA
      obtain ⟨s, -, hs⟩ := right_action hcm M ψ hstd hXh hXd hWh hWd χX χW om hWeil v t ι hι h
        (GlobalTheory.SplitFlip.invT (Matrix.GeneralLinearGroup.map (piW t) h.1)) (by rw [GlobalTheory.SplitFlip.invT_invT]; rfl)
        (hex 1 (one_mem_UAt X v) h hh)
      have h1 : ι φ₁ ∈ N.map ι := by
        rw [hs φ (hN hφN) φ₁ hA]
        exact Submodule.smul_mem _ _ (H _ _ (Submodule.mem_map_of_mem hφN))
      obtain ⟨y, hy, e⟩ := Submodule.mem_map.1 h1
      rwa [hinj (hN hy) hφ₁ e] at hy
  constructor
  · rintro ⟨h1, -, h3⟩
    refine ⟨hiffAug.1 h1, ?_, hiffW.1 h3⟩
    rintro _ ⟨φ, hφ, rfl⟩
    exact hmaps φ (hN hφ)
  · rintro ⟨h1, -, h3⟩
    exact ⟨hiffAug.2 h1, hN, hiffW.2 h3⟩

end GlobalTheory.SplitTransportPair
