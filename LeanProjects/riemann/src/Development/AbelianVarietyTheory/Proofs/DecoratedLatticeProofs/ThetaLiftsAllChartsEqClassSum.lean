import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockSubstitutionIdentities
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCompactGinfCOfOntoUni
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameValuesPolynomialDetStableHomogeneous
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawScalarFormsLawsOnClassDataStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteElementsActFockVectorsThroughDatumStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.LiftSum

variable {D : D7}

theorem ontoUni_inB (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) {n : ℕ} (hn : V.rank = n)
    (h : OntoUni fun k : GinfC V => inN θ V B hn k.1) : OntoUni fun k : GinfC V => inB θ V B k.1 := by
  subst hn
  exact h

theorem castP_surj {p q a b : ℕ} (hp : p = a) (hq : q = b) (Q : FP D.what₂.Tau a b) :
    ∃ P : PolF D q p, castP hp hq P = Q := by
  subst hp hq
  exact ⟨Q, MvPolynomial.rename_id_apply Q⟩

theorem det_ne_zero_of_isUni {ι : Type} {a : ℕ} {u : ι → Matrix (Fin a) (Fin a) ℂ} (hu : IsUni u) (τ : ι) :
    (u τ).det ≠ 0 := by
  have := Matrix.mem_unitaryGroup_iff.1 (hu τ)
  intro h0
  have h1 := congrArg Matrix.det this
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
  exact zero_ne_one h1

def trF {n : ℕ} {u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ} (hu : IsUni u) (y : FrN D n) : FrN D n :=
  ⟨fun τ => u τ * y.1 τ, fun τ => by
    rw [Matrix.det_mul]
    exact (isUnit_iff_ne_zero.2 (det_ne_zero_of_isUni hu τ)).mul (y.2 τ)⟩

theorem isTr_trF {n : ℕ} {u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ} (hu : IsUni u) (y : FrN D n) :
    IsTr u y (trF hu y) := fun _ => rfl

section Weil

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}

theorem theta_snd (hw : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {γ : GA D T} (hγ : γ ∈ GQ T)
    (g : GA D S) (x κ : GA D T) {p : ℂ} (hp : om (1, κ) f = p • f) : om (g, γ * x * κ) f 0 = p * om (g, x) f 0 := by
  have : ((g, γ * x * κ) : GA D S × GA D T) = (1, γ) * ((g, x) * (1, κ)) := by
    simp [mul_assoc]
  rw [this, map_mul, Module.End.mul_apply, hw.om_aut 1 (one_mem _) γ hγ _ (hw.om_pres _ _ hf), map_mul, Module.End.mul_apply,
    hp, map_smul]
  rfl

theorem theta_fst_left (hw : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {γ : GA D S}
    (hγ : γ ∈ GQ S) (g : GA D S) (x : GA D T) : om (γ * g, x) f 0 = om (g, x) f 0 := by
  have : ((γ * g, x) : GA D S × GA D T) = (γ, 1) * (g, x) := by simp
  rw [this, map_mul, Module.End.mul_apply, hw.om_aut γ hγ 1 (one_mem _) _ (hw.om_pres _ _ hf)]

theorem theta_fst_right {f : WO S T → ℂ} (g κ : GA D S) (x : GA D T) {p : ℂ} (hp : om (κ, 1) f = p • f) :
    om (g * κ, x) f 0 = p * om (g, x) f 0 := by
  have : ((g * κ, x) : GA D S × GA D T) = (g, x) * (κ, 1) := by simp
  rw [this, map_mul, Module.End.mul_apply, hp, map_smul]
  rfl

theorem theta_mul {f f' : WO S T → ℂ} (g k : GA D S) (x k' : GA D T) {p : ℂ} (hp : om (k, k') f = p • f') :
    om (g * k, x * k') f 0 = p * thetaKO om g x f' := by
  have : ((g * k, x * k') : GA D S × GA D T) = (g, x) * (k, k') := rfl
  rw [this, map_mul, Module.End.mul_apply, hp, map_smul]
  rfl

end Weil

def formAt {ι : Type} {a b : ℕ} (Λ : FP ι a b →ₗ[ℂ] ℂ) (s : ι → ℂ) (u : ι → Matrix (Fin b) (Fin b) ℂ) : FP ι a b →ₗ[ℂ] ℂ :=
  Λ ∘ₗ (mvZ (fun _ => 1) fun τ => s τ • u τ).toLinearMap

theorem formAt_mvZ {ι : Type} [Fintype ι] {a b : ℕ} (hab : a ≤ b) (Λ : FP ι a b →ₗ[ℂ] ℂ) (s : ι → ℂ)
    (u : ι → Matrix (Fin b) (Fin b) ℂ) (g : ι → Matrix (Fin a) (Fin a) ℂ) (Q : FP ι a b) :
    Λ (mvZ (fun _ => 1) (fun τ => s τ • 1) (mvZ g u Q)) = formAt Λ s u (mvZ g (fun _ => 1) Q) := by
  unfold formAt
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, (substIdentities ι a b hab).2.1, Matrix.mul_one, Matrix.smul_mul,
    Matrix.one_mul]

theorem formAt_subY {ι : Type} {a b : ℕ} (hab : a ≤ b) (Λ : FP ι a b →ₗ[ℂ] ℂ) (s : ι → ℂ)
    (u y' : ι → Matrix (Fin b) (Fin b) ℂ) (F : PY ι a) :
    formAt Λ s u (subY hab y' F) = Λ (subY hab (fun τ => u τ * s τ • y' τ) F) := by
  unfold formAt
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, mvZ_subY, Matrix.smul_mul, Matrix.mul_smul]

theorem prod_det_cancel {ι : Type} [Fintype ι] {a : ℕ} (u y : ι → Matrix (Fin a) (Fin a) ℂ) (hu : ∀ τ, (u τ).det ≠ 0) (s : ι → ℤ)
    (d : ι → ℂ) : (∏ τ, (u τ).det ^ s τ * d τ) * ∏ τ, (u τ * y τ).det ^ (-s τ) = (∏ τ, d τ) * ∏ τ, (y τ).det ^ (-s τ) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Matrix.det_mul, mul_zpow, _root_.zpow_neg (u τ).det]
  have := zpow_ne_zero (s τ) (hu τ)
  field_simp

theorem prod_det_cancel' {ι : Type} [Fintype ι] {a : ℕ} (u y : ι → Matrix (Fin a) (Fin a) ℂ) (hy : ∀ τ, (y τ).det ≠ 0) (s : ι → ℤ) :
    (∏ τ, (y τ).det ^ s τ) * ∏ τ, (u τ * y τ).det ^ (-s τ) = ∏ τ, (u τ).det ^ (-s τ) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Matrix.det_mul, mul_zpow, _root_.zpow_neg (y τ).det]
  have := zpow_ne_zero (s τ) (hy τ)
  field_simp

variable {c : Comm D} {ρ : RealD c} {t : Tup c} {A : ClsK ρ t}

theorem lev_pt (hc : c.Is) (ht : t.Is) (hA : A.Is) {j : ℕ} (hj : j + 1 ≤ D.R.m) (α γ P) (κ : A.U j α) (κ' : A.U (j + 1) γ) :
    t.kom j (κ.1, κ'.1) ((t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P) =
      (((A.chi j α κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (j + 1) γ κ' : ℂˣ) : ℂ)) • (t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P :=
  (GlobalTheory.T.finiteElements_act_fockVectors_through_datum D c.ψ c.θ hc.inf _ _ (c.x j) (c.x (j + 1)) (t.ker j α γ) (hc.x j (Nat.le_of_succ_le hj)) (hc.x _ hj)
    (ht.ker j hj α γ) P).2 _ ((hA.1.reps j (Nat.le_of_succ_le hj) α).le κ.2) _ ((hA.1.reps _ hj γ).le κ'.2) _
    (hA.2.2.1 j hj α γ κ κ')

theorem integrand_eq (hρ : ρ.Is) (hA : A.Is) {j : ℕ} (hj : j + 1 ≤ D.R.m) (hab : ρ.N j ≤ ρ.N (j + 1)) {ψ} (hψ : ψ ∈ t.Ram j)
    (α γ a a' y P) (F : PY D.what₂.Tau (ρ.N j))
    (hF : ∀ z, A.val j α ψ a z = GlobalTheory.KJInf.evalAt z.1 F * ∏ τ, (z.1 τ).det ^ (-ρ.sS j τ))
    (k : GinfC (c.X j)) (k' : GinfC (c.X (j + 1))) :
    (volLev (c.x j).vol (A.U j α) : ℂ) *
      (t.kom j (A.h j α a * k.1, A.h (j + 1) γ a' * k'.1) ((t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P) 0 *
        t.rd j α ψ y (A.h j α a * k.1)) =
    (t.cK j * (∏ τ, (ρ.r (j + 1) hj k'.1 τ).det ^ (-ρ.sD j τ)) * ∏ τ, ((ρ.fr j y).1 τ).det ^ (-ρ.sS j τ)) *
      (formAt (A.abelian₂ j α γ a a') (ρ.sc j) (ρ.r (j + 1) hj k'.1)
        (mvZ (fun τ => (ρ.r j (Nat.le_of_succ_le hj) k.1 τ)⁻¹) (fun _ => 1)
          (castP (ρ.hN j (Nat.le_of_succ_le hj)) (ρ.hN (j + 1) hj) P)) *
        GlobalTheory.KJInf.evalAt (fun τ => ρ.r j (Nat.le_of_succ_le hj) k.1 τ * (ρ.fr j y).1 τ) F) := by
  have hu : IsUni (ρ.r j (Nat.le_of_succ_le hj) k.1) := (hρ.uni j (Nat.le_of_succ_le hj)).uni k
  obtain ⟨P', hP'⟩ := castP_surj (ρ.hN j (Nat.le_of_succ_le hj)) (ρ.hN (j + 1) hj)
    (mvZ (fun τ => (ρ.r j (Nat.le_of_succ_le hj) k.1 τ)⁻¹) (ρ.r (j + 1) hj k'.1)
        (castP (ρ.hN j (Nat.le_of_succ_le hj)) (ρ.hN (j + 1) hj) P))
  have h1 := hA.2.1 j hj α γ k.1 k.2 k'.1 k'.2 P P' hP'
  have h2 := hA.2.2.2.1 j hj α γ a a' P'
  have h3 := hA.1.rd j (Nat.le_of_succ_le hj) ψ hψ α y 1 (one_mem _) a k.1 k.2 1 _ (isTr_trF hu (ρ.fr j y))
  rw [hF] at h3
  simp only [OneMemClass.coe_one, one_mul, mul_one, map_one, Units.val_one] at h3
  rw [hP', formAt_mvZ hab] at h2
  have h4 := prod_det_cancel (ρ.r j (Nat.le_of_succ_le hj) k.1) (ρ.fr j y).1 (det_ne_zero_of_isUni hu) (ρ.sS j)
    fun τ => (ρ.r (j + 1) hj k'.1 τ).det ^ (-ρ.sD j τ)
  rw [theta_mul _ _ _ _ h1, h3]
  simp only [trF]
  set e := GlobalTheory.KJInf.evalAt (fun τ => ρ.r j (Nat.le_of_succ_le hj) k.1 τ * (ρ.fr j y).1 τ) F
  linear_combination
    ((∏ τ, (ρ.r j (Nat.le_of_succ_le hj) k.1 τ).det ^ ρ.sS j τ * (ρ.r (j + 1) hj k'.1 τ).det ^ (-ρ.sD j τ)) * e *
      ∏ τ, (ρ.r j (Nat.le_of_succ_le hj) k.1 τ * (ρ.fr j y).1 τ).det ^ (-ρ.sS j τ)) * h2 +
    (t.cK j * e * formAt (A.abelian₂ j α γ a a') (ρ.sc j) (ρ.r (j + 1) hj k'.1)
        (mvZ (fun τ => (ρ.r j (Nat.le_of_succ_le hj) k.1 τ)⁻¹) (fun _ => 1)
          (castP (ρ.hN j (Nat.le_of_succ_le hj)) (ρ.hN (j + 1) hj) P))) * h4

theorem lift_eq (hc : c.Is) (hρ : ρ.Is) (ht : t.Is) (hA : A.Is) {j : ℕ} (hj : j + 1 ≤ D.R.m) (hab : ρ.N j ≤ ρ.N (j + 1))
    {ψ} (hψ : ψ ∈ t.Ram j) (α γ a' y P) (ν : Measure (GinfC (c.X j)))
    (hcl : ∀ Φ : GA D (c.X j) → ℂ, Continuous Φ → (∀ γ ∈ GQ (c.X j), ∀ g, Φ (γ * g) = Φ g) →
      (∀ κ ∈ A.U j α, ∀ g, Φ (g * κ) = Φ g) → ∫ g in (c.x j).vol.𝓕, Φ g ∂(c.x j).vol.μ =
        (volLev (c.x j).vol (A.U j α) : ℂ) * ∑ a, ((stabOrd (A.U j α) (A.h j α a) : ℕ) : ℂ)⁻¹ * ∫ k, Φ (A.h j α a * k.1) ∂ν)
    (F : A.cl j α → PY D.what₂.Tau (ρ.N j))
    (hF : ∀ a z, A.val j α ψ a z = GlobalTheory.KJInf.evalAt z.1 (F a) * ∏ τ, (z.1 τ).det ^ (-ρ.sS j τ))
    {g' : GA D (c.X (j + 1))} (hg' : g' ∈ GQ (c.X (j + 1))) (k' : GinfC (c.X (j + 1))) (κ' : A.U (j + 1) γ) :
    (t.ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) P (t.rd j α ψ y) (g' * (A.h (j + 1) γ a' * k'.1) * κ'.1) =
      ∑ a, (((A.chi (j + 1) γ κ' : ℂˣ) : ℂ) * t.cK j * (∏ τ, (ρ.r (j + 1) hj k'.1 τ).det ^ (-ρ.sD j τ)) *
        ((stabOrd (A.U j α) (A.h j α a) : ℕ) : ℂ)⁻¹) * ((∏ τ, ((ρ.fr j y).1 τ).det ^ (-ρ.sS j τ)) *
        ∫ k, formAt (A.abelian₂ j α γ a a') (ρ.sc j) (ρ.r (j + 1) hj k'.1)
          (mvZ (fun τ => (ρ.r j (Nat.le_of_succ_le hj) k.1 τ)⁻¹) (fun _ => 1)
            (castP (ρ.hN j (Nat.le_of_succ_le hj)) (ρ.hN (j + 1) hj) P)) *
          GlobalTheory.KJInf.evalAt (fun τ => ρ.r j (Nat.le_of_succ_le hj) k.1 τ * (ρ.fr j y).1 τ) (F a) ∂ν) := by
  obtain ⟨χS, χT, hw⟩ := (ht.ker j hj α γ).weil
  have hw' : IsWeilDatumO c.ψ _ _ χS χT (t.kom j) := hw
  have hf := (GlobalTheory.T.finiteElements_act_fockVectors_through_datum D c.ψ c.θ hc.inf _ _ (c.x j) (c.x (j + 1)) (t.ker j α γ) (hc.x j (Nat.le_of_succ_le hj)) (hc.x _ hj)
    (ht.ker j hj α γ) P).1
  obtain ⟨hr1, hr2, -, -⟩ := GlobalTheory.T.seesaw_scalar_forms_laws_on_class_data D c t ρ A hc hρ hA.1 j (Nat.le_of_succ_le hj) ψ hψ α
  have hk' := lev_pt hc ht hA hj α γ P 1 κ'
  simp only [OneMemClass.coe_one, map_one, Units.val_one, inv_one, one_mul] at hk'
  have hI := fun a (k : GinfC (c.X j)) => integrand_eq hρ hA hj hab hψ α γ a a' y P (F a) (hF a) k k'
  have hk : ∀ κ : A.U j α, t.kom j (κ.1, 1) ((t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P) =
      ((A.chi j α κ : ℂˣ) : ℂ)⁻¹ • (t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P := fun κ => by
    have := lev_pt hc ht hA hj α γ P κ 1
    simpa only [OneMemClass.coe_one, map_one, Units.val_one, mul_one] using this
  unfold KerDat.lift
  rw [liftT_apply]
  generalize (t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P = f at *
  change ∫ g in (c.x j).vol.𝓕, t.kom j (g, g' * (A.h (j + 1) γ a' * k'.1) * κ'.1) f 0 * t.rd j α ψ y g ∂(c.x j).vol.μ = _
  simp only [theta_snd hw' hf hg' _ _ _ hk', mul_assoc ((A.chi (j + 1) γ κ' : ℂˣ) : ℂ)]
  rw [integral_const_mul, hcl (fun g => t.kom j (g, A.h (j + 1) γ a' * k'.1) f 0 * t.rd j α ψ y g)]
  · rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h1 := congrArg (fun φ : GinfC (c.X j) → ℂ => ∫ k, φ k ∂ν) (funext (hI a))
    simp only [integral_const_mul] at h1
    linear_combination (((A.chi (j + 1) γ κ' : ℂˣ) : ℂ) * ((stabOrd (A.U j α) (A.h j α a) : ℕ) : ℂ)⁻¹) * h1
  · exact ((hw'.om_cont f hf 0).comp (continuous_id.prodMk continuous_const)).mul (hr1 y).2
  · intro γ₀ hγ₀ g
    simp only [theta_fst_left hw' hf hγ₀, (hr1 y).1 γ₀ hγ₀ g]
  · intro κ hκ g
    have h1 := hr2 y g ⟨κ, hκ⟩
    have h2 := theta_fst_right g κ (A.h (j + 1) γ a' * k'.1) (hk ⟨κ, hκ⟩)
    simp only at h1 ⊢
    rw [h1, h2]
    have := (A.chi j α ⟨κ, hκ⟩).ne_zero
    field_simp

end GlobalTheory.SeeSaw.LiftSum

namespace GlobalTheory.SeeSaw

open LiftSum

theorem lift_eq_classSum : ∀ (D : D7) (c : Comm D) (ρ : RealD c), c.Is → ρ.Is → ∀ j (hj : j + 1 ≤ D.R.m) (hab : ρ.N j ≤ ρ.N (j + 1)), BorelSpace (GinfC (c.X j)) ∧ ∃ ν : Measure (GinfC (c.X j)), IsProbabilityMeasure ν ∧ ν.IsMulLeftInvariant ∧ ∀ (m : ℕ) (y : Fin m → c.Fr j) (P : Fin m → PolF D (c.X (j + 1)).rank (c.X j).rank) (m' : ℕ) (y' : Fin m' → D.what₂.Tau → Matrix (Fin (ρ.N (j + 1))) (Fin (ρ.N (j + 1))) ℂ) (y'' : Fin m' → c.Fr (j + 1)) (s : Fin m' → ℂ), (∀ i τ, (ρ.fr (j + 1) (y'' i)).1 τ = ρ.sc j τ • y' i τ) → (∀ F ∈ Vn (ρ.lam j) (ρ.n j), ∀ Λ : FP D.what₂.Tau (ρ.N j) (ρ.N (j + 1)) →ₗ[ℂ] ℂ, ∑ i, (∏ τ, ((ρ.fr j (y i)).1 τ).det ^ (-ρ.sS j τ)) * ∫ k, Λ (mvZ (fun τ => (ρ.r j (Nat.le_of_succ_le hj) k.1 τ)⁻¹) (fun _ => 1) (castP (ρ.hN j (Nat.le_of_succ_le hj)) (ρ.hN (j + 1) hj) (P i))) * evalAt (fun τ => ρ.r j (Nat.le_of_succ_le hj) k.1 τ * (ρ.fr j (y i)).1 τ) F ∂ν = ∑ i, s i * Λ (subY hab (y' i) F)) → ∀ (t : Tup c) (A : ClsK ρ t), t.Is → A.Is → ∀ ψ ∈ t.Ram j, ∀ γ, ∑ i, ∑ α, (t.ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) (t.rd j α ψ (y i)) = t.cK j • ∑ i, (s i * ∏ τ, ((ρ.fr (j + 1) (y'' i)).1 τ).det ^ ρ.sD j τ) • t.rd (j + 1) γ (t.K j ψ) (y'' i) := by
  intro D c ρ hc hρ j hj hab
  obtain ⟨hB, -, -, ν, hν1, hν2, hcl⟩ := integral_eq_classSum D c.θ (c.X j) (c.x j).B hc.inf
    (ontoUni_inB _ _ _ _ (hρ.uni j (Nat.le_of_succ_le hj)))
  refine ⟨hB, ν, hν1, hν2, ?_⟩
  intro m y P m' y' y'' s hy hav t A ht hA ψ hψ γ
  have hV := fun α a => ((valC_poly _ _ _ (ρ.lam j)).1 (ρ.n j) (ρ.sS j) (hρ.n j hj) _).1
    (hA.1.valC j (Nat.le_of_succ_le hj) ψ hψ α a)
  choose F hF1 hF2 using hV
  funext h
  obtain ⟨g', hg', a', k', hk', κ', hκ', rfl⟩ := (hA.1.reps (j + 1) hj γ).dec h
  have hu : IsUni (ρ.r (j + 1) hj k') := (hρ.uni (j + 1) hj).uni ⟨k', hk'⟩
  have hL := fun i α => lift_eq hc hρ ht hA hj hab hψ α γ a' (y i) (P i) ν
    (hcl (c.x j).vol (A.U j α) _ (A.h j α) (hA.1.reps j (Nat.le_of_succ_le hj) α)).2.2 (F α) (hF2 α) hg' ⟨k', hk'⟩ ⟨κ', hκ'⟩
  have hR := fun i => hA.1.rd (j + 1) hj _ (ht.stabK j hj ψ hψ) γ (y'' i) g' hg' a' k' hk' ⟨κ', hκ'⟩ _
    (isTr_trF hu (ρ.fr (j + 1) (y'' i)))
  have hK := fun i => hA.2.2.2.2 j hj hab ψ hψ F hF1 hF2 γ a' (trF hu (ρ.fr (j + 1) (y'' i)))
  simp only at hL hR
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hL, hR, hK]
  rw [Finset.sum_comm]
  conv_rhs =>
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.mul_sum, hav (F α a) (hF1 α a) (formAt (A.abelian₂ j α γ a a') (ρ.sc j) (ρ.r (j + 1) hj k')), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := prod_det_cancel' (ρ.r (j + 1) hj k') (ρ.fr (j + 1) (y'' i)).1
    (fun τ => ((ρ.fr (j + 1) (y'' i)).2 τ).ne_zero) (ρ.sD j)
  rw [formAt_subY]
  simp only [trF, ← hy i]
  rw [← h1]
  ring

end GlobalTheory.SeeSaw

end
