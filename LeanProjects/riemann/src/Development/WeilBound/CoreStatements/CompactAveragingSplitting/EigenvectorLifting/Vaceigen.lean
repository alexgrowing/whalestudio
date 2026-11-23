import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.VaceigenDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.CyclicAndLine
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.DualNumberGraphFiltrationIsotropicOfSkew
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.LocallyCompactOfGoodChar

noncomputable section

namespace PositivityTheory.ThK

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.LatVac

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace Vac

theorem hTens_mul {R E α β : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) [Fintype α] [Fintype β]
    (JA : Matrix α α E) {JB k : Matrix β β E} (hk : kᵀ * JB * k.map c = JB) (x y : Matrix α β E) :
    hTens c JA JB (x * kᵀ) (y * kᵀ) = hTens c JA JB x y := by
  have e : ∀ x y, hTens c JA JB x y = ∑ i, ∑ p, JA i p * (x * JB * (y.map c)ᵀ) i p := fun x y => by
    simp only [hTens, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by ring
  have e2 : (y * kᵀ).map c = y.map c * (k.map c)ᵀ := Matrix.map_mul (f := (c : E →+* E))
  rw [e, e, e2, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc x, ← Matrix.mul_assoc, Matrix.mul_assoc x, hk]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

theorem latAtV_mul {X : Spc F E n} {W : Spc F E d} {v : Pl F} {k : Matrix (Fin d) (Fin d) (AE F E)}
    (hk : ∀ y ∈ latW W v, k *ᵥ y ∈ latW W v) {γ} (hγ : γ ∈ latAtV X W v) : γ * kᵀ ∈ latAtV X W v := by
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hav, x, hx, y, hy, rfl⟩ := hz
    have e : a • incM F (Matrix.vecMulVec x y) = Matrix.vecMulVec (incV x) fun i => a • inclR (F := F) (AF F) (y i) := by
      ext i j
      simp [incM, incV, Matrix.vecMulVec_apply]
    rw [e, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
    exact vecMulVec_mem hx (hk _ (AddSubgroup.subset_closure ⟨a, ha, hav, y, hy, rfl⟩))
  | zero => rw [Matrix.zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => rw [Matrix.add_mul]; exact add_mem hy hz
  | neg y _ hy => rw [Matrix.neg_mul]; exact neg_mem hy

theorem local_line {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ] (co : Darboux B κ)
    {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (v : Pl F) (Γ : Set W) (hAt : ∀ γ ∈ Γ, At (evFin F v) γ)
    (hΓ : ∀ z, At (evFin F v) z → (∀ γ ∈ Γ, ψ (B γ z) = 1) → z ∈ Γ) (χ : W → ℂ) {φ φ' : (κ → Fv F v) → ℂ}
    (hs : φ ∈ SB _) (hs' : φ' ∈ SB _) (h0 : φ ≠ 0) (hφ : ∀ γ ∈ Γ, schr (psiAt ψ v) (locCo co v γ) φ = χ γ • φ)
    (hφ' : ∀ γ ∈ Γ, schr (psiAt ψ v) (locCo co v γ) φ' = χ γ • φ') : ∃ a : ℂ, φ' = a • φ := by
  have hc : Continuous (psiAt ψ v) := GlobalTheory.VacAny.continuous_psiV hψ.1 v
  obtain ⟨u, hg⟩ := (GlobalTheory.CompanionTheory.VacLoc.GoodInh.exists_goodChar (Fv F v)).2 (psiAt ψ v) hc
    (norm_addChar _ (GlobalTheory.SplitWeil.isCompact_int (Fv F v)) _ hc) (GlobalTheory.PsiNontriv.psiAt_ne_one ψ hψ v)
  let d₀ : Darboux (fun w w' : (κ → Fv F v) × (κ → Fv F v) => w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) κ := ⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩
  let _ : MeasurableSpace (κ → Fv F v) := borel _
  have : BorelSpace (κ → Fv F v) := ⟨rfl⟩
  obtain ⟨S, hS⟩ := GlobalTheory.CompanionTheory.SchrModel.exists_isModel hg d₀ MeasureTheory.Measure.addHaar inferInstance
  let up : (κ → Fv F v) × (κ → Fv F v) → W := fun w => co.e.symm (fun i => liftV v (w.1 i), fun i => liftV v (w.2 i))
  have hup : ∀ w, At (evFin F v) (up w) := fun w a ha => by
    rw [← map_smul, LinearEquiv.map_eq_zero_iff]
    exact Prod.ext (funext fun i => at_liftV v _ a ha) (funext fun i => at_liftV v _ a ha)
  have hlo : ∀ w, locCo co v (up w) = w := fun w => by
    ext i <;> simp [locCo, up, evFin_liftV]
  have hul : ∀ γ, At (evFin F v) γ → up (locCo co v γ) = γ := fun γ hγ => by
    have e : ∀ a : AF F, evFin F v a = 0 → a • co.e γ = 0 := fun a ha => by rw [← map_smul, hγ a ha, map_zero]
    rw [LinearEquiv.symm_apply_eq]
    exact Prod.ext (funext fun i => (eq_liftV fun a ha => congrArg (fun p => p.1 i) (e a ha)).symm)
      (funext fun i => (eq_liftV fun a ha => congrArg (fun p => p.2 i) (e a ha)).symm)
  have h0' : (⟨φ, hs⟩ : SB (κ → Fv F v)) ≠ 0 := fun h => h0 (congrArg Subtype.val h)
  have hd : ∀ w, (∀ x ∈ locCo co v '' Γ, S.c x w ^ 2 = 1) → ∀ γ ∈ Γ, ψ (B γ (up w)) = 1 := fun w hw γ hγ => by
    have h := hw _ ⟨γ, hγ, rfl⟩
    rw [hS.2.2, pow_two, ← AddChar.map_add_eq_mul, ← add_mul, invOf_two_add_invOf_two, one_mul] at h
    rw [← h]
    change _ = ψ (liftV v _)
    congr 1
    simp only [co.form, up, LinearEquiv.apply_symm_apply, dotProduct, map_sub, map_sum, liftV_mul, mul_comm ((co.e γ).1 _)]
    simp only [locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, mul_comm]
  obtain ⟨a, ha⟩ := line_of_eigen S (locCo co v '' Γ) (fun w => χ (up w)) (φ := ⟨φ, hs⟩) (φ' := ⟨φ', hs'⟩)
    (fun w hw => ⟨up w, hΓ _ (hup w) (hd w hw), hlo w⟩) h0'
    ((GlobalTheory.CompanionTheory.VacLoc.ModelLine.cyclic_and_line _ _ u d₀ _ S ⊥ 1 _ 0 hg hS).1 h0')
    (by rintro _ ⟨γ, hγ, rfl⟩; exact Subtype.ext ((hS.1 _ _).trans (by rw [hul γ (hAt γ hγ)]; exact hφ γ hγ)))
    (by rintro _ ⟨γ, hγ, rfl⟩; exact Subtype.ext ((hS.1 _ _).trans (by rw [hul γ (hAt γ hγ)]; exact hφ' γ hγ)))
  exact ⟨a, congrArg Subtype.val ha⟩

end Vac

open Vac in

theorem vacuum_eigenline_of_local : LocRepEx → VacEigen := by
  intro hA F E _ _ _ _ _ σ n d B X W M om P v k hk
  obtain ⟨ω, ρ, L⟩ := hA F E σ n d B X W M om P v
  obtain ⟨r, s, hX⟩ := P.herm
  obtain ⟨r', s', hW⟩ := P.skew
  obtain ⟨hs, h0, θ, -, hθ⟩ := P.good.vac v
  have m1 : mat (1 : UA σ X.J) = 1 := rfl
  have o1 : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := fun u _ => by rw [m1, sub_self, smul_zero]
  have hAt := (latAtV_at_stable X W v).1
  have hρ : ∀ γ ∈ latAtV X W v, ∀ φ ∈ SB _, schr (psiAt B.ψ v) (locCo M.co v γ) φ = ρ γ φ := fun γ hγ φ hφ =>
    (L.actsH γ (hAt γ hγ) φ hφ _).1 (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v γ (hAt γ hγ) φ)
  have hv := fun γ hγ => (L.actsH γ (hAt γ hγ) _ hs _).1 (hθ γ hγ)
  have hs' := L.pres 1 o1 k hk.1 _ hs
  obtain ⟨c, hc⟩ := local_line M.co P.base.std v (latAtV X W v) hAt (fun z hz h => mem_latAtV P.base hX hW v hz h) _ hs hs' h0
    (fun γ hγ => (hρ γ hγ _ hs).trans (hv γ hγ).symm) fun γ hγ => by
      have hγ' := latAtV_mul (fun y hy => (hk.2 y hy).2) hγ
      have e : γ * (mat k⁻¹)ᵀ * (mat k)ᵀ = γ := by
        have : mat k * mat k⁻¹ = 1 := k.1.mul_inv
        rw [Matrix.mul_assoc, ← Matrix.transpose_mul, this, Matrix.transpose_one, Matrix.mul_one]
      have h := L.impl 1 o1 k hk.1 _ (hAt _ hγ') _ hs
      rw [m1, Matrix.one_mul, e, ← hv _ hγ', map_smul] at h
      rw [hρ γ hγ _ hs', ← h, symp, symp, hTens_mul (cA σ) _ (k := mat k⁻¹) (k⁻¹).2]
  exact ⟨c, (L.acts 1 o1 k hk.1 _ hs _).2 hc.symm⟩

end PositivityTheory.ThK
