import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalImageLatticeSupportedAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeLocalDarbouxCoordsBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalSubgroupFirstProjEqAnnihilator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceSchwartzBruhatVacuumConditionEqSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorLatticeStabiliserRightPreservesVacuu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeSelfDualEveryFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryElementActsLocalOperatorAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.DblVacLine

section Alg

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

omit [DecidableEq α] [DecidableEq β] in

theorem symp_dbl (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (x₁ x₂ y₁ y₂ : Matrix α β E) :
    symp (R := R) c ξ JA (dbl JB) (Matrix.fromCols x₁ x₂) (Matrix.fromCols y₁ y₂) =
      symp (R := R) c ξ JA JB x₁ y₁ - symp (R := R) c ξ JA JB x₂ y₂ := by
  unfold symp
  rw [← map_sub, ← mul_sub]
  congr 2
  simp only [hTens, dbl, Fintype.sum_sum_type, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, Matrix.neg_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, mul_neg, neg_mul,
    Finset.sum_neg_distrib, Finset.sum_add_distrib, sub_eq_add_neg]

theorem star_eq_neg (ψ : AddChar R ℂ) (hψ : ∀ t, ‖ψ t‖ = 1) (t : R) : star (ψ t) = ψ (-t) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψ]
  simp

variable [Invertible (2 : R)]

theorem schr_box (ψ : AddChar R ℂ) (hψ : ∀ t, ‖ψ t‖ = 1) {κ : Type} [Fintype κ] (w₁ w₂ : (κ → R) × (κ → R))
    (φ₁ φ₂ : (κ → R) → ℂ) :
    schr ψ (Sum.elim w₁.1 w₂.1, Sum.elim w₁.2 (-w₂.2)) (boxFun φ₁ fun x => star (φ₂ x)) =
      boxFun (schr ψ w₁ φ₁) fun x => star (schr ψ w₂ φ₂ x) := by
  funext x
  have e : x = Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr) := (Sum.elim_comp_inl_inr x).symm
  have e1 : (x + Sum.elim w₁.1 w₂.1) ∘ Sum.inl = x ∘ Sum.inl + w₁.1 := rfl
  have e2 : (x + Sum.elim w₁.1 w₂.1) ∘ Sum.inr = x ∘ Sum.inr + w₂.1 := rfl
  have e3 : x ⬝ᵥ Sum.elim w₁.2 (-w₂.2) = (x ∘ Sum.inl) ⬝ᵥ w₁.2 - (x ∘ Sum.inr) ⬝ᵥ w₂.2 := by
    conv_lhs => rw [e]
    rw [sumElim_dotProduct_sumElim, dotProduct_neg, sub_eq_add_neg]
  simp only [schr, boxFun, e1, e2, e3, sumElim_dotProduct_sumElim, dotProduct_neg, star_mul', star_eq_neg ψ hψ]
  rw [mul_mul_mul_comm, ← AddChar.map_add_eq_mul]
  congr 2
  ring

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem fromCols_mul_transpose {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl F)
    (h : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E))
    (hh : ∀ z ∈ GlobalTheory.InertDbl.latAtD Y v, h *ᵥ z ∈ GlobalTheory.InertDbl.latAtD Y v)
    {γ₁ γ₂ : Matrix (Fin n) (Fin d) (AE F E)} (h₁ : γ₁ ∈ latAtV X Y v) (h₂ : γ₂ ∈ latAtV X Y v) :
    ∃ δ₁ ∈ latAtV X Y v, ∃ δ₂ ∈ latAtV X Y v, Matrix.fromCols γ₁ γ₂ * hᵀ = Matrix.fromCols δ₁ δ₂ := by
  rw [← Matrix.fromBlocks_toBlocks h] at hh ⊢
  set A := h.toBlocks₁₁
  set B := h.toBlocks₁₂
  set C := h.toBlocks₂₁
  set D := h.toBlocks₂₂
  have hl : ∀ z ∈ GlobalTheory.InertSph.latAt Y v, A *ᵥ z ∈ GlobalTheory.InertSph.latAt Y v ∧ C *ᵥ z ∈ GlobalTheory.InertSph.latAt Y v := by
    intro z hz
    have := hh (Sum.elim z 0) ⟨hz, zero_mem _⟩
    rw [Matrix.fromBlocks_mulVec] at this
    simpa [GlobalTheory.InertDbl.latAtD] using this
  have hr : ∀ z ∈ GlobalTheory.InertSph.latAt Y v, B *ᵥ z ∈ GlobalTheory.InertSph.latAt Y v ∧ D *ᵥ z ∈ GlobalTheory.InertSph.latAt Y v := by
    intro z hz
    have := hh (Sum.elim 0 z) ⟨zero_mem _, hz⟩
    rw [Matrix.fromBlocks_mulVec] at this
    simpa [GlobalTheory.InertDbl.latAtD] using this
  refine ⟨γ₁ * Aᵀ + γ₂ * Bᵀ, add_mem ?_ ?_, γ₁ * Cᵀ + γ₂ * Dᵀ, add_mem ?_ ?_, ?_⟩
  · exact GlobalTheory.VacTransport.mul_transpose_mem X Y v _ (fun z hz => (hl z hz).1) h₁
  · exact GlobalTheory.VacTransport.mul_transpose_mem X Y v _ (fun z hz => (hr z hz).1) h₂
  · exact GlobalTheory.VacTransport.mul_transpose_mem X Y v _ (fun z hz => (hl z hz).2) h₁
  · exact GlobalTheory.VacTransport.mul_transpose_mem X Y v _ (fun z hz => (hr z hz).2) h₂
  · rw [Matrix.fromBlocks_transpose, Matrix.fromCols_mul_fromBlocks]

omit [NumberField E] in
theorem at_fromCols {n d : ℕ} (v : Pl F) {γ₁ γ₂ : Matrix (Fin n) (Fin d) (AE F E)} (h₁ : At (evFin F v) γ₁)
    (h₂ : At (evFin F v) γ₂) : At (evFin F v) (Matrix.fromCols γ₁ γ₂) := by
  intro u hu
  ext i (j | j)
  · exact congrFun (congrFun (h₁ u hu) i) j
  · exact congrFun (congrFun (h₂ u hu) i) j

theorem box_mem_SB {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] {κ κ' : Type}
    {φ₁ : (κ → k) → ℂ} {φ₂ : (κ' → k) → ℂ} (h₁ : φ₁ ∈ SB (κ → k)) (h₂ : φ₂ ∈ SB (κ' → k)) :
    boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → k) := by
  have cl : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inl := continuous_pi fun i => continuous_apply _
  have cr : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inr := continuous_pi fun i => continuous_apply _
  refine ⟨(h₁.1.comp_continuous cl).mul (h₂.1.comp_continuous cr), ?_⟩
  let e := (Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ'))
  refine HasCompactSupport.intro ((h₁.2.prod h₂.2).image e.symm.continuous) fun x hx => ?_
  have hx' : e x ∉ tsupport φ₁ ×ˢ tsupport φ₂ := fun h => hx ⟨e x, h, e.symm_apply_apply x⟩
  rw [Homeomorph.sumArrowHomeomorphProdArrow_apply, Set.mem_prod, not_and_or] at hx'
  simp only [boxFun]
  rcases hx' with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

theorem eq_of_tens (v : Pl F) {κ : Type} {φ₁ φ₂ : (κ → Fv F v) → ℂ} {r : (κ → AF F) → ℂ}
    (hr : ∀ x z, At (evFin F v) z → r (x + z) = r x) {x₀ : κ → AF F} (h0 : r x₀ ≠ 0)
    (h : tens (evFin F v) φ₁ r = tens (evFin F v) φ₂ r) : φ₁ = φ₂ := by
  funext y
  let z : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (y i - evFin F v (x₀ i))
  have hz : At (evFin F v) z := by
    intro u hu; funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu
  have hev : (fun i => evFin F v ((x₀ + z) i)) = y := by
    funext i
    simp only [Pi.add_apply, z, map_add, GlobalTheory.LatVac.evFin_liftV]
    abel
  have e := congrFun h (x₀ + z)
  simp only [tens, hev, hr x₀ z hz] at e
  exact mul_right_cancel₀ h0 e

theorem dblFun_tens (v : Pl F) {κ : Type} (φ : (κ → Fv F v) → ℂ) (r : (κ → AF F) → ℂ) :
    GlobalTheory.InertDbl.dblFun (tens (evFin F v) φ r) =
      tens (evFin F v) (boxFun φ fun x => star (φ x)) (GlobalTheory.InertDbl.dblFun r) := by
  funext x
  simp only [GlobalTheory.InertDbl.dblFun, tens, boxFun, Function.comp_def, star_mul']
  ring

theorem rest_dbl (v : Pl F) {κ : Type} [Fintype κ] {φ : (κ → Fv F v) → ℂ} {r : (κ → AF F) → ℂ}
    (h : Rest (evFin F v) φ r) : Rest (evFin F v) (boxFun φ fun x => star (φ x)) (GlobalTheory.InertDbl.dblFun r) := by
  refine ⟨fun x z hz => ?_, ?_⟩
  · have hz1 : At (evFin F v) (z ∘ Sum.inl) := fun u hu => by
      funext i; exact congrFun (hz u hu) (Sum.inl i)
    have hz2 : At (evFin F v) (z ∘ Sum.inr) := fun u hu => by
      funext i; exact congrFun (hz u hu) (Sum.inr i)
    show r ((x + z) ∘ Sum.inl) * star (r ((x + z) ∘ Sum.inr)) = r (x ∘ Sum.inl) * star (r (x ∘ Sum.inr))
    rw [show (x + z) ∘ Sum.inl = x ∘ Sum.inl + z ∘ Sum.inl from rfl,
      show (x + z) ∘ Sum.inr = x ∘ Sum.inr + z ∘ Sum.inr from rfl, h.1 _ _ hz1, h.1 _ _ hz2]
  · rw [← dblFun_tens]
    exact GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ _ h.2 _ (GlobalTheory.SchAConj.star_mem_schA F _ _ h.2)

theorem acts_of_at {σ : E →ₐ[F] E} {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
    {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)} {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (omd : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ))
    (hS : IsUSplitting (adeleClass F) ψ dd (actB (cA σ)) omd) (v : Pl F) (p : UG (cA σ) JB)
    (hp : At (evFin F v) (((p : GL β (AE F E)) : Matrix β β (AE F E)) - 1)) (φ : (κ → Fv F v) → ℂ)
    (hφ : φ ∈ SB (κ → Fv F v)) : ∃ φ₁ ∈ SB (κ → Fv F v), Acts (evFin F v) (omd p) φ φ₁ := by
  refine GlobalTheory.DblActs.acts_of_comm v ψ hψ (omd p) (fun Φ hΦ => hS.pres p Φ hΦ)
    (fun μ hμ Φ hΦ => hS.unit μ hμ p Φ hΦ) ?_ φ hφ
  intro u hu x y Φ hΦ
  set w := dd.e.symm (x, y) with hw
  have he : dd.e (u • w) = (u • x, u • y) := by
    rw [LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]
  have h2 := hp u hu
  have e2 : actB (cA σ) p (u • w) = u • w := by
    simp only [actB]
    set P : Matrix β β (AE F E) := ((p : GL β (AE F E)) : Matrix β β (AE F E)) with hP
    have : (u • w) * Pᵀ - u • w = w * (u • (P - 1))ᵀ := by
      rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
        Matrix.mul_sub, Matrix.mul_one, smul_sub]
    rw [h2] at this
    simpa only [Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] using this
  have h3 := hS.impl p (u • w) Φ hΦ
  simp only [Darboux.rho, he, e2] at h3
  exact h3

theorem dbl_line {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {Y : Spc F E d} {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    (v : Pl F) (hunr : PsiUnr ψ v) (hX : X.L.IsLattice E) (hY : Y.L.IsLattice E)
    (hsd : ∀ z : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) z → (z ∈ latAtV X Y v ↔ ∀ γ ∈ latAtV X Y v,
      ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F Y.J) z γ) = 1))
    (M : Model σ X Y) (φ : (Fin n × Fin d → Fv F v) → ℂ) (hφ : M.IsVac ψ v φ)
    (dd : Darboux (symp (cA σ) (-1) (incM F X.J) (dbl (incM F Y.J))) (Fin n × Fin d ⊕ Fin n × Fin d))
    (omd : UG (cA σ) (dbl (incM F Y.J)) →* Module.End ℂ ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ))
    (hdd : IsDblCoord (cA σ) (-1) (incM F X.J) (incM F Y.J) M.co dd)
    (hS : IsUSplitting (adeleClass F) ψ dd (actB (cA σ)) omd)
    (R : (Fin n × Fin d → AF F) → ℂ) (hR : Rest (evFin F v) φ R)
    (g : GlobalTheory.InertDbl.UD σ Y) (hg : g ∈ GlobalTheory.InertDbl.KAtD σ Y v) :
    ∃ c : ℂ, omd g (GlobalTheory.InertDbl.dblFun (tens (evFin F v) φ R)) = c • GlobalTheory.InertDbl.dblFun (tens (evFin F v) φ R) := by
  classical
  by_cases hR0 : R = 0
  · have e : GlobalTheory.InertDbl.dblFun (tens (evFin F v) φ R) = 0 := by
      funext x; simp [hR0, GlobalTheory.InertDbl.dblFun, boxFun, tens]
    exact ⟨0, by rw [e, map_zero, smul_zero]⟩
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp hR0
  obtain ⟨hφSB, hφ0, θ, -, hvac⟩ := hφ
  have hn := GlobalTheory.StdCharFromIsStd.norm_psi hψ
  set Λ := latAtV X Y v with hΛ
  have hat : ∀ γ ∈ Λ, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable X Y v).1
  set φd := boxFun φ fun x => star (φ x) with hφd
  set Rd := GlobalTheory.InertDbl.dblFun R with hRd
  set Φ := GlobalTheory.InertDbl.dblFun (tens (evFin F v) φ R) with hΦ
  have hΦt : Φ = tens (evFin F v) φd Rd := dblFun_tens v φ R
  have hrest : Rest (evFin F v) φd Rd := rest_dbl v hR
  have hΦs : Φ ∈ schA F _ := hΦt ▸ hrest.2
  have hRd0 : Rd (Sum.elim x₀ x₀) ≠ 0 := by
    show R x₀ * star (R x₀) ≠ 0
    exact mul_ne_zero hx₀ (star_ne_zero.mpr hx₀)
  have hφdSB : φd ∈ SB _ := box_mem_SB hφSB ⟨hφSB.1.comp star, hφSB.2.comp_left (star_zero ℂ)⟩
  let cf : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E) → ℂ := fun w =>
    ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (dbl (incM F Y.J)) w w)

  have h1 : ∀ γ₁ ∈ Λ, ∀ γ₂ ∈ Λ, dd.rho ψ (Matrix.fromCols γ₁ γ₂) Φ = cf (Matrix.fromCols γ₁ γ₂) • Φ := by
    intro γ₁ h₁ γ₂ h₂
    have e₁ := hvac γ₁ h₁ R hR
    have e₂ := hvac γ₂ h₂ R hR
    rw [GlobalTheory.VacTransport.tens_smul] at e₁ e₂
    simp only [Darboux.rho] at e₁ e₂
    rw [Darboux.rho, hdd, hΦ, GlobalTheory.InertDbl.dblFun, schr_box ψ hn, e₁, e₂]
    funext x
    simp only [cf, symp_dbl, boxFun, Pi.smul_apply, smul_eq_mul, star_mul', star_eq_neg ψ hn, mul_sub]
    rw [sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring

  have h2 : ∀ γ₁ ∈ Λ, ∀ γ₂ ∈ Λ,
      dd.rho ψ (Matrix.fromCols γ₁ γ₂) (omd g Φ) = cf (Matrix.fromCols γ₁ γ₂) • omd g Φ := by
    intro γ₁ h₁ γ₂ h₂
    obtain ⟨δ₁, k₁, δ₂, k₂, he⟩ := fromCols_mul_transpose X Y v (GlobalTheory.InertDbl.matD g⁻¹) (fun z hz => (hg.2 z hz).2) h₁ h₂
    have hback : actB (cA σ) g (Matrix.fromCols δ₁ δ₂) = Matrix.fromCols γ₁ γ₂ := by
      change Matrix.fromCols δ₁ δ₂ * (GlobalTheory.InertDbl.matD g)ᵀ = _
      have e : GlobalTheory.InertDbl.matD g * GlobalTheory.InertDbl.matD g⁻¹ = 1 := Units.mul_inv g.1
      rw [← he, Matrix.mul_assoc, ← Matrix.transpose_mul, e, Matrix.transpose_one, Matrix.mul_one]
    have hsy : cf (Matrix.fromCols δ₁ δ₂) = cf (Matrix.fromCols γ₁ γ₂) := by
      simp only [cf]
      rw [← he, GlobalTheory.VacTransport.symp_mul_transpose (cA σ) _ _ _ (GlobalTheory.InertDbl.matD g⁻¹) (g⁻¹).2]
    have h := hS.impl g (Matrix.fromCols δ₁ δ₂) Φ hΦs
    rw [hback, h1 δ₁ k₁ δ₂ k₂, map_smul, hsy] at h
    exact h.symm

  obtain ⟨φ₁, -, hact⟩ := acts_of_at hψ dd omd hS v g hg.1 φd hφdSB
  have hT : omd g Φ = tens (evFin F v) φ₁ Rd := by rw [hΦt]; exact hact Rd hrest
  have hrest₁ : Rest (evFin F v) φ₁ Rd := ⟨hrest.1, hT ▸ hS.pres g Φ hΦs⟩
  have hloc : ∀ f, Rest (evFin F v) f Rd → ∀ γ₁ ∈ Λ, ∀ γ₂ ∈ Λ,
      dd.rho ψ (Matrix.fromCols γ₁ γ₂) (tens (evFin F v) f Rd) = cf (Matrix.fromCols γ₁ γ₂) • tens (evFin F v) f Rd →
      schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols γ₁ γ₂)) f = cf (Matrix.fromCols γ₁ γ₂) • f := by
    intro f hf γ₁ h₁ γ₂ h₂ h
    refine eq_of_tens v hf.1 hRd0 ?_
    rw [GlobalTheory.VacTransport.tens_smul, ← h]
    exact (GlobalTheory.VacBridge.rho_acts_locCo dd ψ v _ (at_fromCols v (hat _ h₁) (hat _ h₂)) f Rd hf).symm
  have hco : ∀ γ₁ γ₂, GlobalTheory.LatVac.locCo dd v (Matrix.fromCols γ₁ γ₂) =
      (Sum.elim (GlobalTheory.LatVac.locCo M.co v γ₁).1 (GlobalTheory.LatVac.locCo M.co v γ₂).1,
        Sum.elim (GlobalTheory.LatVac.locCo M.co v γ₁).2 (-(GlobalTheory.LatVac.locCo M.co v γ₂).2)) := by
    intro γ₁ γ₂
    change ((fun k => evFin F v ((dd.e (Matrix.fromCols γ₁ γ₂)).1 k)),
      fun k => evFin F v ((dd.e (Matrix.fromCols γ₁ γ₂)).2 k)) = _
    rw [hdd]
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · cases k <;> rfl
    · cases k with
      | inl k => rfl
      | inr k => exact map_neg (evFin F v) _

  obtain ⟨c, hc0, hcb⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded X Y v M.co hX hY
  have hfill := GlobalTheory.SelfDualFirstProj.exists_pair_of_annihilator v (GlobalTheory.LatVac.psiAt ψ v)
    (Λ.map (GlobalTheory.LatVac.locCo M.co v)) c hc0 (fun x => hunr x) (GlobalTheory.LatVac.DualLoc.map_selfDual v M.co ψ Λ hat hsd)
    (fun l hl i => by
      obtain ⟨γ, hγ, rfl⟩ := AddSubgroup.mem_map.mp hl
      exact hcb γ hγ i)
  have hφd0 : φd ≠ 0 := by
    obtain ⟨t, ht⟩ := Function.ne_iff.mp hφ0
    refine Function.ne_iff.mpr ⟨Sum.elim t t, ?_⟩
    show φ t * star (φ t) ≠ 0
    exact mul_ne_zero ht (star_ne_zero.mpr ht)
  obtain ⟨c', hc'⟩ := GlobalTheory.VacUniqInert.eq_smul_of_eigen (GlobalTheory.LatVac.psiAt ψ v)
    (fun i : Λ × Λ => GlobalTheory.LatVac.locCo dd v (Matrix.fromCols i.1.1 i.2.1))
    (fun i => cf (Matrix.fromCols i.1.1 i.2.1)) (fun u hu => by
      have eu : u = Sum.elim (u ∘ Sum.inl) (u ∘ Sum.inr) := (Sum.elim_comp_inl_inr u).symm
      obtain ⟨y₁, γ₁, h₁, e₁⟩ := hfill (u ∘ Sum.inl) (by
        rintro b ⟨γ, hγ, he⟩
        have := hu (⟨γ, hγ⟩, 0) (by
          simp only [hco, he, ZeroMemClass.coe_zero, map_zero]
          funext k; cases k <;> rfl)
        simp only [hco, he, ZeroMemClass.coe_zero, map_zero] at this
        rw [eu, sumElim_dotProduct_sumElim] at this
        simpa using this)
      obtain ⟨y₂, γ₂, h₂, e₂⟩ := hfill (u ∘ Sum.inr) (by
        rintro b ⟨γ, hγ, he⟩
        have := hu (0, ⟨-γ, neg_mem hγ⟩) (by
          simp only [hco, he, ZeroMemClass.coe_zero, map_zero, map_neg]
          funext k; cases k <;> simp)
        simp only [hco, he, ZeroMemClass.coe_zero, map_zero, map_neg] at this
        rw [eu, sumElim_dotProduct_sumElim] at this
        simpa using this)
      refine ⟨(⟨γ₁, h₁⟩, ⟨γ₂, h₂⟩), ?_⟩
      simp only [hco, e₁, e₂]
      exact eu.symm) φ₁ φd
    (fun i => hloc φ₁ hrest₁ _ i.1.2 _ i.2.2 (hT ▸ h2 _ i.1.2 _ i.2.2))
    (fun i => hloc φd hrest _ i.1.2 _ i.2.2 (hΦt ▸ h1 _ i.1.2 _ i.2.2)) hφd0
  exact ⟨c', by rw [hT, hc', GlobalTheory.VacTransport.tens_smul, ← hΦt]⟩

theorem dblFun_eigen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T → ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.V'.J) (dbl (incM F G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (cA σ) (dbl (incM F G.W.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (dbl (incM F G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ g ∈ GlobalTheory.InertDbl.KAtD σ G.W v, ∃ c : ℂ, omd g (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      c • GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin _ dd omd hdd hS R _ hR g hg
  exact dbl_line hT.base.std v (hT.base.inert v w hin).2.2 hT.geo.hV'.lat hT.geo.hW.lat
    (GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B _ _ G.V' G.W _ _ _ _ hT.base hT.geo.hV' hT.geo.hW v)
    G.M' _ (hT.geo.hM'.vac v) dd omd hdd hS.2.1 R hR g hg

end GlobalTheory.DblVacLine

end
