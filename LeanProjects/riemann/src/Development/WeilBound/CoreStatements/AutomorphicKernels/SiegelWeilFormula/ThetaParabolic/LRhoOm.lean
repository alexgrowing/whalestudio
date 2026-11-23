import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaParabolic.InvMulSelfMatrixDoubled

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

set_option linter.unusedSectionVars false

namespace PositivityTheory.SiegelWeilFormula.Tpar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {κ : Type} [Fintype κ] {m n : ℕ} {A : Spc F E m} {Y : Spc F E n} {ψ : AddChar (AF F) ℂ}
  {dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) κ} {χ : Chr F E}
  {om : G2 σ Y →* Module.End ℂ ((κ → AF F) → ℂ)} {S : UA σ A.J →* Module.End ℂ ((κ → AF F) → ℂ)}
  {l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ}

theorem rho_rho (a b : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) (φ : (κ → AF F) → ℂ) :
    dd.rho ψ a (dd.rho ψ b φ) =
      ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J)) a b) • dd.rho ψ (a + b) φ := by
  rw [dd.form]
  funext x
  simp only [Darboux.rho, schr, map_add, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul,
    Prod.fst_add, Prod.snd_add, add_assoc, add_dotProduct, dotProduct_add]
  congr 2
  linear_combination (-((dd.e a).1 ⬝ᵥ (dd.e b).2)) * invOf_mul_self (2 : AF F)

theorem l_shift (h : IsDbl (σ := σ) (A := A) (Y := Y) (κ := κ) ψ dd χ om S l) (hψ : IsStd ψ)
    (Z : Matrix (Fin m) (Fin n) (AE F E)) (w : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) {Φ : (κ → AF F) → ℂ}
    (hΦ : Φ ∈ schA F κ) :
    l (dd.rho ψ (Z * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ + w) Φ) =
      ψ (-(⅟(2 : AF F) * symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))
        (Z * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ) w)) * l (dd.rho ψ w Φ) := by
  have e1 := congrArg l (rho_rho (dd := dd) (ψ := ψ) (Z * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ) w Φ)
  have mem : dd.rho ψ w Φ ∈ schA F κ := GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ Φ hΦ
  rw [map_smul, smul_eq_mul] at e1
  have e2 := (h.kill Z _ mem).symm.trans e1
  rw [e2, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]

theorem l_rho_om (h : IsDbl (σ := σ) (A := A) (Y := Y) (κ := κ) ψ dd χ om S l) (x : G2 σ Y)
    (u : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    l (dd.rho ψ u (om x Φ)) = l (om x (dd.rho ψ (u * (mat2 x⁻¹)ᵀ) Φ)) := by
  rw [h.weil.2.1.impl x _ Φ hΦ]
  congr 3
  simp only [actB]
  rw [Matrix.mul_assoc, ← Matrix.transpose_mul]
  change u = u * (mat2 x * mat2 x⁻¹)ᵀ
  rw [show mat2 x * mat2 x⁻¹ = 1 from Units.mul_inv x.1, Matrix.transpose_one, Matrix.mul_one]

theorem l_om_par (h : IsDbl (σ := σ) (A := A) (Y := Y) (κ := κ) ψ dd χ om S l) {x : G2 σ Y}
    {t : GL (Fin n) (AE F E)} (hx : IsPar x t) {φ : (κ → AF F) → ℂ} (hφ : φ ∈ schA F κ) :
    l (om x φ) = (χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
      (((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) ^ ((m : ℝ) / 2) : ℝ) : ℂ) * l φ := by
  rw [h.weil.2.2 l h.adm h.kill x t hx φ hφ, modu_norm, Fintype.card_fin]

theorem l_rho_S (h : IsDbl (σ := σ) (A := A) (Y := Y) (κ := κ) ψ dd χ om S l) (hψ : IsStd ψ) (g : UA σ A.J)
    (u : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    l (dd.rho ψ u (S g Φ)) = l (dd.rho ψ (mat g⁻¹ * u) Φ) := by
  have e : S g (dd.rho ψ (mat g⁻¹ * u) Φ) = dd.rho ψ (mat g * (mat g⁻¹ * u)) (S g Φ) := h.lin.impl g _ Φ hΦ
  rw [← Matrix.mul_assoc, show mat g * mat g⁻¹ = 1 from Units.mul_inv g.1, Matrix.one_mul] at e
  have mem : dd.rho ψ (mat g⁻¹ * u) Φ ∈ schA F κ := GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ Φ hΦ
  rw [← e, h.fix g _ mem]

theorem psi_rat (h : IsDbl (σ := σ) (A := A) (Y := Y) (κ := κ) ψ dd χ om S l) (hψ : IsStd ψ)
    (a c : Matrix (Fin m) (Fin n ⊕ Fin n) E) :
    ψ (-(⅟(2 : AF F) * symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J)) (incM F a) (incM F c))) = 1 := by
  obtain ⟨y, z, hyz⟩ := h.rat a
  obtain ⟨y', z', hyz'⟩ := h.rat c
  have h2 : ⅟(2 : AF F) = algebraMap F (AF F) (1 / 2) := invOf_eq_right_inv (by
    rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul, mul_one_div_cancel two_ne_zero, map_one])
  have hd : ∀ u v : κ → F, (fun i => algebraMap F (AF F) (u i)) ⬝ᵥ (fun i => algebraMap F (AF F) (v i)) =
      algebraMap F (AF F) (u ⬝ᵥ v) := fun u v => by simp [dotProduct]
  rw [dd.form, hyz, hyz']
  simp only [hd, h2, ← map_sub, ← map_mul, ← map_neg]
  exact hψ.2.1 _

end PositivityTheory.SiegelWeilFormula.Tpar

end
