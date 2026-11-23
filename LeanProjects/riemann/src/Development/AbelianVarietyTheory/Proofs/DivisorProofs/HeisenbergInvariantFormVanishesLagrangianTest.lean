import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLagrAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerMemSchwartzBruhatFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianInvariantFormsProportionalFinitePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormEqZeroOfLagrangianAtPlaceStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.InertLagUniq

open GlobalTheory.LatVac GlobalTheory.InertVacLag

theorem finrank_le_of_isotropic {K : Type} [Field K] {κ : Type} [Fintype κ] (Λ : Submodule K ((κ → K) × (κ → K)))
    (h : ∀ a ∈ Λ, ∀ b ∈ Λ, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) : Module.finrank K Λ ≤ Fintype.card κ := by
  classical
  let B : LinearMap.BilinForm K ((κ → K) × (κ → K)) :=
    LinearMap.mk₂ K (fun a b => a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2)
      (fun a a' b => by simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring)
      (fun c a b => by simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring)
      (fun a b b' => by simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring)
      (fun c a b => by simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring)
  have hB : ∀ a b, B a b = a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2 := fun _ _ => rfl
  have hker : LinearMap.ker B = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    have ha' : ∀ b, B a b = 0 := fun b => by rw [LinearMap.mem_ker.1 ha]; rfl
    refine (Submodule.mem_bot _).2 (Prod.ext (funext fun k => ?_) (funext fun k => ?_))
    · have := ha' (0, Pi.single k 1)
      simpa [hB] using this
    · have := ha' (Pi.single k 1, 0)
      simpa [hB] using this
  have h1 := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := B) Λ
  rw [hker, inf_bot_eq, finrank_bot, add_zero, Module.finrank_prod, Module.finrank_fintype_fun_eq_card] at h1
  have h2 : Λ ≤ B.orthogonal Λ := fun b hb a ha => by
    show B a b = 0
    rw [hB, h a ha b hb, sub_self]
  have h3 := Submodule.finrank_mono h2
  omega

theorem finrank_eq_of_isotropic {K : Type} [Field K] {κ : Type} [Fintype κ] (Λ Λ' : Submodule K ((κ → K) × (κ → K)))
    (h : ∀ a ∈ Λ, ∀ b ∈ Λ, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) (h' : ∀ a ∈ Λ', ∀ b ∈ Λ', a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2)
    (hs : Λ ⊔ Λ' = ⊤) : Module.finrank K Λ = Fintype.card κ := by
  have h1 := finrank_le_of_isotropic Λ h
  have h2 := finrank_le_of_isotropic Λ' h'
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq Λ Λ'
  rw [hs, finrank_top, Module.finrank_prod, Module.finrank_fintype_fun_eq_card] at h3
  omega

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem continuous_psiAt (ψ : AddChar (AF F) ℂ) (v : Pl F) (h : PsiUnr ψ v) : Continuous (psiAt ψ v) := by
  have hker : ∀ y ∈ v.adicCompletionIntegers F, psiAt ψ v y = 1 := fun y hy => by
    have := (h 1).2 (one_mem _) y hy
    rwa [one_mul] at this
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  refine IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  rw [← map_add_left_nhds_zero, Filter.eventually_map]
  filter_upwards [hO.mem_nhds (zero_mem _)] with s hs
  rw [AddChar.map_add_eq_mul, hker s hs, mul_one]

theorem psiAt_ne_one (ψ : AddChar (AF F) ℂ) (v : Pl F) (h : PsiUnr ψ v) : psiAt ψ v ≠ 1 := by
  intro h1
  have hall : ∀ x : Fv F v, x ∈ v.adicCompletionIntegers F := fun x => (h x).1 fun y _ => by
    rw [← psiAt_apply, h1]; rfl
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have h2 := hall (algebraMap F (Fv F v) π⁻¹)
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h2
  erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h2
  rw [map_inv₀, map_inv₀, Algebra.algebraMap_self_apply, hπ, ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp] at h2
  omega

theorem liftV_one_smul {M : Type} [AddCommGroup M] [Module (AF F) M] (v : Pl F) (u : M) (hu : At (evFin F v) u) :
    liftV v (1 : Fv F v) • u = u := by
  have h := hu (1 - liftV v 1) (by rw [map_sub, map_one, evFin_liftV, sub_self])
  rw [sub_smul, one_smul] at h
  exact (sub_eq_zero.1 h).symm

theorem liftV_one_mul (v : Pl F) (x : AF F) : liftV v (1 : Fv F v) * x = liftV v (evFin F v x) := by
  have h := at_liftV v (1 : Fv F v) (x - liftV v (evFin F v x)) (by rw [map_sub, evFin_liftV, sub_self])
  have h2 := liftV_one_smul v _ (at_liftV v (evFin F v x))
  rw [smul_eq_mul] at h h2
  linear_combination h + h2

theorem liftV_one_smul_eq_zero (v : Pl F) (a : AE F E) (ha : compFin F E v a = 0) : liftV v (1 : Fv F v) • a = 0 := by
  have key : ∀ a : AE F E, liftV v (1 : Fv F v) • a = (liftV v).rTensor E (compFin F E v a) := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul x e =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, liftV_one_mul]
      simp [compFin]
    | add x y hx hy => rw [smul_add, hx, hy, map_add, map_add]
  rw [key, ha, map_zero]

theorem exists_map_compFin (v : Pl F) {α β : Type} (A : Matrix α β (Fv F v ⊗[F] E)) :
    ∃ C : Matrix α β (AE F E), C.map (compFin F E v) = A := by
  refine ⟨A.map ((liftV v).rTensor E), ?_⟩
  ext i j
  simp only [Matrix.map_apply]
  induction A i j using TensorProduct.induction_on with
  | zero => simp
  | tmul x e => simp [compFin, evFin_liftV]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem mul_eq_self {n d : ℕ} (v : Pl F) (u : Matrix (Fin n) (Fin d) (AE F E)) (hu : At (evFin F v) u)
    (N : Matrix (Fin d) (Fin d) (AE F E)) (hN : N.map (compFin F E v) = 1) : u * N = u := by
  have h0 : liftV v (1 : Fv F v) • (N - 1) = 0 := by
    ext i j
    refine liftV_one_smul_eq_zero v _ ?_
    have := congrFun (congrFun hN i) j
    rw [Matrix.map_apply] at this
    rw [Matrix.sub_apply, map_sub, this]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  have h1 : u * (N - 1) = 0 := by
    rw [← liftV_one_smul v u hu, Matrix.smul_mul, ← Matrix.mul_smul, h0, Matrix.mul_zero]
  rwa [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h1

theorem at_mul {α β γ : Type} [Fintype β] (v : Pl F) (u : Matrix α β (AE F E)) (hu : At (evFin F v) u)
    (A : Matrix β γ (AE F E)) : At (evFin F v) (u * A) := fun t ht => by
  rw [← Matrix.smul_mul, hu t ht, Matrix.zero_mul]

theorem exists_compl (σ : E →ₐ[F] E) {d m : ℕ} (W : Spc F E d) (v : Pl F) (C : Matrix (Fin d) (Fin m) (AE F E))
    (hC : IsLagrAt σ W v C) (n : ℕ) : ∃ C' : Matrix (Fin d) (Fin m) (AE F E), IsLagrAt σ W v C' ∧
      ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) u → ∃ x ∈ lagAt v C, ∃ y ∈ lagAt v C', u = x + y := by
  obtain ⟨h0, Cx, M, hx, h1, h2⟩ := hC
  obtain ⟨C', hC'⟩ := exists_map_compFin v Cx
  obtain ⟨M₁, hM₁⟩ := exists_map_compFin v M.toRows₁
  obtain ⟨M₂, hM₂⟩ := exists_map_compFin v M.toRows₂
  rw [← Matrix.fromRows_toRows M] at h1 h2
  rw [Matrix.fromCols_mul_fromRows] at h1
  rw [Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at h2
  refine ⟨C', ⟨by rw [hC']; exact hx, _, Matrix.fromRows M.toRows₂ M.toRows₁, h0, ?_, ?_⟩, fun u hu => ?_⟩
  · rw [hC', Matrix.fromCols_mul_fromRows, add_comm, h1]
  · rw [hC', Matrix.fromRows_mul_fromCols, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2, Matrix.fromBlocks_one]
  · have hN : ((C * M₁ + C' * M₂)ᵀ).map (compFin F E v) = 1 := by
      rw [Matrix.transpose_map, Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul, hC', hM₁, hM₂, h1,
        Matrix.transpose_one]
    refine ⟨u * M₁ᵀ * Cᵀ, ⟨at_mul v _ (at_mul v u hu _) _, _, rfl⟩, u * M₂ᵀ * C'ᵀ,
      ⟨at_mul v _ (at_mul v u hu _) _, _, rfl⟩, ?_⟩
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add, ← Matrix.transpose_mul, ← Matrix.transpose_mul,
      ← Matrix.transpose_add, mul_eq_self v u hu _ hN]

theorem exists_at_locCo {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : Darboux B κ) (v : Pl F) (p : (κ → Fv F v) × (κ → Fv F v)) :
    ∃ u : W, At (evFin F v) u ∧ locCo co v u = p := by
  refine ⟨co.e.symm (fun k => liftV v (p.1 k), fun k => liftV v (p.2 k)), ?_, ?_⟩
  · intro r hr
    rw [← LinearEquiv.map_smul]
    have h0 : r • ((fun k => liftV v (p.1 k), fun k => liftV v (p.2 k)) : (κ → AF F) × (κ → AF F)) = 0 :=
      Prod.ext (funext fun k => at_liftV v (p.1 k) r hr) (funext fun k => at_liftV v (p.2 k) r hr)
    rw [h0, map_zero]
  · show ((fun k => evFin F v ((co.e _).1 k)), fun k => evFin F v ((co.e _).2 k)) = p
    rw [LinearEquiv.apply_symm_apply]
    exact Prod.ext (funext fun k => evFin_liftV v _) (funext fun k => evFin_liftV v _)

variable {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def lagCo (M : Model σ X W) (v : Pl F) {m : ℕ} (C : Matrix (Fin d) (Fin m) (AE F E)) :
    Submodule (Fv F v) ((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) where
  carrier := locCo M.co v '' lagAt v C
  zero_mem' := ⟨0, ⟨fun u _ => smul_zero u, 0, by simp⟩, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨_, ⟨hx, z, rfl⟩, rfl⟩ ⟨_, ⟨hy, z', rfl⟩, rfl⟩
    exact ⟨_, ⟨fun u hu => by rw [smul_add, hx u hu, hy u hu, add_zero], z + z', by rw [Matrix.add_mul]⟩, map_add _ _ _⟩
  smul_mem' := by
    rintro a _ ⟨_, ⟨hx, z, rfl⟩, rfl⟩
    refine ⟨liftV v a • (z * Cᵀ), ⟨fun u hu => by rw [smul_comm, hx u hu, smul_zero], liftV v a • z,
      by rw [Matrix.smul_mul]⟩, ?_⟩
    ext k <;> simp [locCo, evFin_liftV, -Matrix.smul_mul]

theorem lagCo_isotropic (M : Model σ X W) (v : Pl F) {m : ℕ} (C : Matrix (Fin d) (Fin m) (AE F E))
    (hC : IsLagrAt σ W v C) : ∀ a ∈ lagCo M v C, ∀ b ∈ lagCo M v C, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2 := by
  rintro _ ⟨u, hu, rfl⟩ _ ⟨u', hu', rfl⟩
  have h0 := GlobalTheory.T.symplecticForm_eq_zero_of_lagrangianAtPlace σ X.J W v C hC (-1) u u' hu hu'
  rw [M.co.form] at h0
  have h1 := congrArg (evFin F v) h0
  rw [← sub_eq_zero]
  simpa [locCo, dotProduct, map_sum, map_mul, map_sub] using h1

theorem finrank_lagCo (M : Model σ X W) (v : Pl F) {m : ℕ} (C : Matrix (Fin d) (Fin m) (AE F E))
    (hC : IsLagrAt σ W v C) : Module.finrank (Fv F v) (lagCo M v C) = Fintype.card (Fin n × Fin d) := by
  obtain ⟨C', hC', hdec⟩ := exists_compl σ W v C hC n
  refine finrank_eq_of_isotropic _ (lagCo M v C') (lagCo_isotropic M v C hC) (lagCo_isotropic M v C' hC') ?_
  rw [eq_top_iff]
  intro p _
  obtain ⟨u, hu, rfl⟩ := exists_at_locCo M.co v p
  obtain ⟨x, hx, y, hy, rfl⟩ := hdec u hu
  rw [map_add]
  exact Submodule.add_mem_sup ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩

theorem exists_test : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (v : Pl F), PsiUnr ψ v →
    ∀ (m : ℕ) (C : Matrix (Fin d) (Fin m) (AE F E)), GlobalTheory.InertVacLag.IsLagrAt σ W v C →
    ∃ φ₀ ∈ SB (Fin n × Fin d → Fv F v), ∀ l : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
      GlobalTheory.InertVacLag.HeisInv M ψ v C l → l φ₀ = 0 → ∀ φ ∈ SB (Fin n × Fin d → Fv F v), l φ = 0 := by
  intro F E _ _ _ _ _ σ n d X W M ψ v hψ m C hC
  have hc := continuous_psiAt ψ v hψ
  have hinv : ∀ l, HeisInv M ψ v C l → ∀ w ∈ lagCo M v C, ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      l (schr (psiAt ψ v) w φ) = l φ := by
    rintro l hl _ ⟨u, hu, rfl⟩ φ hφ
    exact hl u hu φ hφ _ (GlobalTheory.SchrSBFin.schr_mem_SB v _ hc _ φ hφ) (GlobalTheory.VacBridge.rho_acts_locCo M.co ψ v u hu.1 φ)
  by_cases hex : ∃ l₂, HeisInv M ψ v C l₂ ∧ ∃ φ ∈ SB (Fin n × Fin d → Fv F v), l₂ φ ≠ 0
  · obtain ⟨l₂, hl₂, φ₀, hφ₀, hne⟩ := hex
    refine ⟨φ₀, hφ₀, fun l hl h0 φ hφ => ?_⟩
    obtain ⟨c, hcl⟩ := GlobalTheory.T.lagrangian_invariant_forms_proportional_finitePlace F v (psiAt ψ v) hc (psiAt_ne_one ψ v hψ) _ (lagCo M v C) (lagCo_isotropic M v C hC)
      (finrank_lagCo M v C hC) l l₂ (hinv l hl) (hinv l₂ hl₂) ⟨φ₀, hφ₀, hne⟩
    have hc0 : c = 0 := (mul_eq_zero.1 ((hcl φ₀ hφ₀).symm.trans h0)).resolve_right hne
    rw [hcl φ hφ, hc0, zero_mul]
  · refine ⟨0, zero_mem _, fun l hl _ φ hφ => ?_⟩
    by_contra hne
    exact hex ⟨l, hl, φ, hφ, hne⟩

end GlobalTheory.InertLagUniq

end
