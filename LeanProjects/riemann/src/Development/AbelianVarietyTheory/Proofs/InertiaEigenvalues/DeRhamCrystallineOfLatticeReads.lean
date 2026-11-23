import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineAndJumps
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.ReadPass

variable {l : ℕ} [Fact l.Prime]

theorem exists_read_map {Γ : Type} [Group Γ] {a d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l])
    (r : Γ →* GL (Fin a) (Om l)) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)) (e : Fin d → ℤ_[l])
    (hR : Reads ρ r b e) (L : FinExt l) (r' : Γ →* GL (Fin a) ↥L.1)
    (R : Representation ↥L.1 Γ (Fin a → ↥L.1)) (hRr : ∀ g v, R g v = (r' g).val *ᵥ v)
    (hr : ∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (r g).val i j) (v : Fin a → ↥L.1) :
    ∃ (F : (Fin d → ℚ_[l]) →ₗ[ℚ_[l]] (Fin a → ↥L.1)) (x : Fin d → ℚ_[l]),
      (∀ g y, F (qRep ρ g y) = R g (F y)) ∧ F x = v := by
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap ↥L.1 (Om l))
    (LinearMap.ker_eq_bot.2 (algebraMap ↥L.1 (Om l)).injective)
  have hp' : ∀ c : ↥L.1, p (c : Om l) = c := fun c => LinearMap.congr_fun hp c
  let Φ : (Fin d → ℚ_[l]) → Matrix (Fin a) (Fin a) (Om l) := fun x => ∑ j, algebraMap ℚ_[l] (Om l) (x j) • b j
  let w : Fin a → Om l := fun k => (v k : Om l)
  have hΦs : ∀ (c : ℚ_[l]) x, Φ (c • x) = c • Φ x := by
    intro c x
    simp only [Φ, Finset.smul_sum, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, algebraMap_smul]
  have hΦa : ∀ x y, Φ (x + y) = Φ x + Φ y := by
    intro x y
    simp only [Φ, Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]
  let F : (Fin d → ℚ_[l]) →ₗ[ℚ_[l]] (Fin a → ↥L.1) :=
    { toFun := fun x i => p ((Φ x *ᵥ w) i)
      map_add' := by
        intro x y; funext i
        simp only [hΦa, Matrix.add_mulVec, Pi.add_apply, map_add]
      map_smul' := by
        intro c x; funext i
        have h1 : ((Φ (c • x)) *ᵥ w) i = c • ((Φ x *ᵥ w) i) := by
          rw [hΦs]
          simp only [Matrix.mulVec, dotProduct, Finset.smul_sum, Matrix.smul_apply, smul_mul_assoc]
        simp only [RingHom.id_apply, Pi.smul_apply]
        rw [h1]
        exact LinearMap.map_smul_of_tower p c _ }
  have hq : ∀ g y, qRep ρ g y = ((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])) *ᵥ y := fun g y => rfl
  have hΦg : ∀ g y, Φ (qRep ρ g y) = (r g).val * Φ y := by
    intro g y
    rw [hq]
    simp only [Φ, Matrix.mul_sum, Matrix.mul_smul, hR.equi, Finset.smul_sum, smul_smul]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
    rfl
  refine ⟨F, fun j => algebraMap ℤ_[l] ℚ_[l] (e j), fun g y => ?_, ?_⟩
  · funext i
    rw [hRr]
    change p ((Φ (qRep ρ g y) *ᵥ w) i) = ∑ k, (r' g).val i k * p ((Φ y *ᵥ w) k)
    rw [hΦg, ← Matrix.mulVec_mulVec]
    generalize Φ y *ᵥ w = z
    change p (∑ k, (r g).val i k * z k) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hr]
    exact LinearMap.map_smul p ((r' g).val i k) (z k)
  · funext i
    change p ((Φ _ *ᵥ w) i) = v i
    have h1 : Φ (fun j => algebraMap ℤ_[l] ℚ_[l] (e j)) = 1 := hR.one
    rw [h1, Matrix.one_mulVec]
    exact hp' (v i)

end GlobalTheory.ReadPass

namespace GlobalTheory.ReadPass

open GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

theorem crys_pass (T : LocTied l P AI) (K L : FinExt l) {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [FiniteDimensional ℚ_[l] V] {a : ℕ} (ρq : Representation ℚ_[l] ↥(GK K) V)
    (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1))
    (hF : ∀ v : Fin a → ↥L.1, ∃ (F : V →ₗ[ℚ_[l]] (Fin a → ↥L.1)) (x : V),
      (∀ g y, F (ρq g y) = R g (F y)) ∧ F x = v)
    (h : IsCrys (P.PD K) ρq) : IsCrys (P.PD K) R := by
  haveI := L.2
  haveI : IsDomain P.R.B := GlobalTheory.RegularRing.isDomain_of_tied T K
  have hf := GlobalTheory.TateDualCrys.fracInv_of_tied T K
  have hu := GlobalTheory.TateDualCrys.lineUnit_of_tied T K
  rw [GlobalTheory.RegularRing.isCrys_iff_span (P.PD K) hf hu] at h ⊢
  refine GlobalTheory.RegularRing.eq_top_of_tmul _ fun c v => ?_
  obtain ⟨F, x, hFe, rfl⟩ := hF v
  have hm : ∀ y ∈ DcrisK₀ (P.PD K) ρq, F.baseChange P.R.B y ∈ DcrisK₀ (P.PD K) R := by
    intro y hy
    rw [GlobalTheory.RegularRing.mem_DcrisK₀] at hy ⊢
    intro g
    have hc : ∀ z, F.baseChange P.R.B (GlobalTheory.RegularRing.sig (P.PD K) ρq g z) =
        GlobalTheory.RegularRing.sig (P.PD K) R g (F.baseChange P.R.B z) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul b w => simp [GlobalTheory.RegularRing.sig_tmul, hFe]
      | add z z' hz hz' => simp only [map_add, hz, hz']
    rw [← hc, hy g]
  have h1 : Submodule.span P.R.B (DcrisK₀ (P.PD K) ρq : Set (P.R.B ⊗[ℚ_[l]] V)) ≤
      (Submodule.span P.R.B (DcrisK₀ (P.PD K) R : Set (P.R.B ⊗[ℚ_[l]] (Fin a → ↥L.1)))).comap
        (F.baseChange P.R.B) :=
    Submodule.span_le.2 fun y hy => Submodule.subset_span (hm y hy)
  have h2 := h1 (h ▸ Submodule.mem_top : c ⊗ₜ[ℚ_[l]] x ∈ _)
  simpa using h2

theorem dr_pass (T : LocTied l P AI) (K L : FinExt l) {LL0 : Type} [Field LL0] [Algebra ℚ_[l] LL0]
    {V : Type} [AddCommGroup V] [Module LL0 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL0 V] {a : ℕ}
    (ρ0 : Representation LL0 ↥(GK K) V) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1))
    (hF : ∀ v : Fin a → ↥L.1, ∃ (F : V →ₗ[ℚ_[l]] (Fin a → ↥L.1)) (x : V),
      (∀ g y, F (ρ0 g y) = R g (F y)) ∧ F x = v)
    (h : GlobalTheory.DRFil.Spans (P.PD K) ρ0) : IsDR (P.PD K) R := by
  haveI := L.2
  apply GlobalTheory.DRFil.isDR_of_spans T K L R
  intro y
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩
  | add y z hy hz =>
    obtain ⟨m, b, dd, hd, rfl⟩ := hy
    obtain ⟨m', b', dd', hd', rfl⟩ := hz
    refine ⟨m + m', Fin.append b b', Fin.append dd dd', fun i => ?_, ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa using hd i
      · simpa using hd' i
    · rw [Fin.sum_univ_add]
      simp
  | tmul v c =>
    obtain ⟨F, x, hFe, rfl⟩ := hF v
    obtain ⟨m, b, dd, hd, hx⟩ := h (x ⊗ₜ[ℚ_[l]] c)
    let E : V ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR :=
      TensorProduct.map F (LinearMap.id : P.R.BdR →ₗ[ℚ_[l]] P.R.BdR)
    have hE : ∀ (β : P.R.BdR) z, E (GlobalTheory.DRFil.mulR ℚ_[l] P.R.BdR LL0 V β z) =
        GlobalTheory.DRFil.mulR ℚ_[l] P.R.BdR ↥L.1 (Fin a → ↥L.1) β (E z) := by
      intro β z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul u c' => simp [E]
      | add z z' hz hz' => simp only [map_add, hz, hz']
    have hg : ∀ g z, E (actVdR (P.PD K) ρ0 g z) = actVdR (P.PD K) R g (E z) := by
      intro g z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul u c' => simp [E, actVdR, hFe]
      | add z z' hz hz' => simp only [map_add, hz, hz']
    refine ⟨m, b, fun i => E (dd i), fun i => ?_, ?_⟩
    · have h1 := hd i
      simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
        sub_eq_zero] at h1 ⊢
      intro g
      rw [← hg, h1 g]
    · have h2 := congrArg E hx
      rw [map_sum] at h2
      simp only [hE] at h2
      simpa [E] using h2

end GlobalTheory.ReadPass

namespace GlobalTheory.ReadPass

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

theorem dr_pass_rat (T : LocTied l P AI) (K L : FinExt l) {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [FiniteDimensional ℚ_[l] V] {a : ℕ} (ρq : Representation ℚ_[l] ↥(GK K) V)
    (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1))
    (hF : ∀ v : Fin a → ↥L.1, ∃ (F : V →ₗ[ℚ_[l]] (Fin a → ↥L.1)) (x : V),
      (∀ g y, F (ρq g y) = R g (F y)) ∧ F x = v)
    (h : IsDR (P.PD K) ρq) : IsDR (P.PD K) R := by
  let LL : FinExt l := ⟨⊥, inferInstance⟩
  let e : (↥(LL.1)) ≃ₐ[ℚ_[l]] ℚ_[l] := IntermediateField.botEquiv ℚ_[l] (Om l)
  letI iM : Module (↥(LL.1)) V := Module.compHom V e.toRingEquiv.toRingHom
  haveI iT : IsScalarTower ℚ_[l] (↥(LL.1)) V :=
    ⟨fun q x v => by
      show e (q • x) • v = q • (e x • v)
      rw [show e (q • x) = q • e x from e.toLinearEquiv.map_smul q x, smul_eq_mul, mul_smul]⟩
  haveI iF : FiniteDimensional (↥(LL.1)) V := Module.Finite.of_restrictScalars_finite ℚ_[l] (↥(LL.1)) V
  let ρ' : Representation (↥(LL.1)) (↥(GK K)) V :=
    { toFun := fun g =>
        { toFun := ρq g, map_add' := (ρq g).map_add, map_smul' := fun x v => (ρq g).map_smul (e x) v }
      map_one' := by ext v; simp
      map_mul' := by intro g h; ext v; simp; rfl }
  have hact : ∀ g (x : V ⊗[ℚ_[l]] P.R.BdR), actVdR (P.PD K) ρ' g x = actVdR (P.PD K) ρq g x := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => rfl
    | add x z hx hz => rw [map_add, map_add, hx, hz]
  have hmem : ∀ x : V ⊗[ℚ_[l]] P.R.BdR, x ∈ DdR (P.PD K) ρ' ↔ x ∈ DdR (P.PD K) ρq := by
    intro x
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero, hact]
  have hfr : ∀ (W : Type) [AddCommGroup W] [Module (↥(LL.1)) W] [Module ℚ_[l] W]
      [IsScalarTower ℚ_[l] (↥(LL.1)) W], Module.finrank (↥(LL.1)) W = Module.finrank ℚ_[l] W := by
    intro W _ _ _ _
    rw [← Module.finrank_mul_finrank ℚ_[l] (↥(LL.1)) W]
    have : Module.finrank ℚ_[l] (↥(LL.1)) = 1 := IntermediateField.finrank_bot
    rw [this, one_mul]
  let eq : ↥(DdR (P.PD K) ρ') ≃ₗ[ℚ_[l]] ↥(DdR (P.PD K) ρq) :=
    { toFun := fun x => ⟨x.1, (hmem x.1).1 x.2⟩
      invFun := fun x => ⟨x.1, (hmem x.1).2 x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h' : IsDR (P.PD K) ρ' := by
    unfold IsDR at h ⊢
    rw [hfr, hfr, eq.finrank_eq, h]
  exact dr_pass T K L ρ' R hF ((GlobalTheory.DRFil.filSpans T K LL ρ' h').spans)

theorem isDR_isCrys_of_reads : ∀ (l : ℕ) [Fact l.Prime] (K L₀ : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (a : ℕ) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (r : ↥(GK K) →* GL (Fin a) (Om l)) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)) (e : Fin d → ℤ_[l]), Reads ρ r b e → ∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (r g).val i j) → (Formalism.MainNotions.N.IsDR (P.PD K) (qRep ρ) → Formalism.MainNotions.N.IsDR (P.PD K) R) ∧ (IsCrys (P.PD K) (qRep ρ) → IsCrys (P.PD K) R) := by
  intro l _ K L₀ P AI T a d ρ r b e hR L r' R _ hRr hr
  have hF := exists_read_map ρ r b e hR L r' R hRr hr
  exact ⟨dr_pass_rat T K L (qRep ρ) R hF, crys_pass T K L (qRep ρ) R hF⟩

end GlobalTheory.ReadPass

end
