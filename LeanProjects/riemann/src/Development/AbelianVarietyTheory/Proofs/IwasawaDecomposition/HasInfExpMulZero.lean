import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsStdIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivariantOfWave
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoInfMulProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.Cx GlobalTheory.Chain NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InnerSteps

variable {D : D7}

theorem hasInfQ_tauE {χ : Formalism.L2.Host.HChar D.host.E} {a : D.R.Psi → ℚ}
    (h : χ.HasInfQ (Formalism.L2.Host.embPsi D.host) a) : χ.HasInfQ (tauE D) fun τ => a (D.eTau τ) := by
  obtain ⟨n, hn, h⟩ := h
  refine ⟨fun τ => n (D.eTau τ), fun τ => hn _, fun k => ?_⟩
  rw [h k]
  exact (Equiv.prod_comp D.eTau (fun g => (Formalism.L2.Host.embPsi D.host g (k : D.host.E) /
      ((‖Formalism.L2.Host.embPsi D.host g (k : D.host.E)‖ : ℝ) : ℂ)) ^ n g)).symm

theorem hasInfExp_mul_zero {χ η : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {a : ℚ} (hχ : HasInfExp D χ τ a)
    (hη : HasInfExp D η τ 0) : HasInfExp D (χ * η) τ a := by
  obtain ⟨n, hn, h1, h2⟩ := hχ
  obtain ⟨m, hm, -, h3⟩ := hη
  have hm0 : m = 0 := by exact_mod_cast hm.trans (mul_zero _)
  refine ⟨n, hn, h1, fun θ hθ x hx hτ => ?_⟩
  rw [MonoidHom.mul_apply, Circle.coe_mul, h2 θ hθ x hx hτ, h3 θ hθ x hx hτ, hm0, zpow_zero, mul_one]

theorem exp_chrStep {T0 : Type} (L : LevCh D T0) {μ0 : T0} (hL : L.Is μ0) (t : T0) (k : Fin D.R.m) (τ : D.what₂.Tau) :
    HasInfExp D (Lift.chrStep (L.mu t) L.eta ((k : ℕ) + 1)).1 τ (expS D k τ) ∧
      HasInfExp D (Lift.chrStep (L.mu t) L.eta ((k : ℕ) + 1)).2 τ (expT D k τ) := by
  have h1 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hL.mu0 k) (hasInfQ_tauE (L.C.isMu0 k).inf) τ
  simp only [Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at h1
  have h2 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hL.eta
    (hasInfQ_tauE (a := fun _ => 1 / 2) ⟨fun _ => 1, fun _ => by norm_num, L.C.isEta.inf⟩) τ
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  haveI : IsTotallyComplex D.host.E := by infer_instance
  have h3 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun _ => 0) (hL.xi t)
    ⟨fun _ => 0, fun _ => by norm_num, fun x => by
      rw [GlobalTheory.TypeValues.inf_eq_one _ hn ho x]; simp⟩ τ
  have h4 : HasInfExp D (L.mu t ((k : ℕ) + 1)) τ (-(D.hc τ).e k) := hasInfExp_mul_zero h1 h3
  unfold Lift.chrStep
  by_cases hk : Even (k : ℕ)
  · rw [if_pos hk.add_one, (exp_of_even hk τ).1, (exp_of_even hk τ).2]
    exact ⟨hasInfExp_div h4 h2, h4⟩
  · rw [if_neg (fun h => hk (by simpa [Nat.odd_add_one, Nat.not_odd_iff_even] using h)), (exp_of_odd hk τ).1,
      (exp_of_odd hk τ).2]
    exact ⟨h4, hasInfExp_div h4 h2⟩

theorem toEAf_surjective : Function.Surjective (toEAf D) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, RingHom.map_add _ _ _⟩
  | tmul x a => exact ⟨pairA D.host.F 0 a ⊗ₜ[D.host.F] x, rfl⟩

theorem sum_mul_idem {R ι : Type} [CommRing R] (p : ι → R) (s : Finset ι) (h : ∀ i ∈ s, p i * p i = p i)
    (h0 : ∀ i ∈ s, ∀ j ∈ s, j ≠ i → p i * p j = 0) {i : ι} (hi : i ∈ s) : p i * (∑ i ∈ s, p i) = p i := by
  rw [Finset.mul_sum, Finset.sum_eq_single i (fun j hj hji => h0 i hi j hj hji) (fun h => absurd hi h), h i hi]

theorem resS_idemSum {e : AE D} {P : Finset (Pl D.host.E)} (h : IsIdemSum e P) :
    ∃ hi : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ∀ PP ∈ P, resS D.host.F PP ⟨toEAf D e, hi⟩ = 1 := by
  have he := GlobalTheory.PlaceDatum.idemSum_mul_self h
  have hint : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    GlobalTheory.IdemRes.toEAf_mem_of_finPart (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he]))
  refine ⟨hint, fun PP hP => ?_⟩
  obtain ⟨⟨es, hes, hsum⟩, hc⟩ := h
  have h1 : ∀ i ∈ P, es i * es i = es i := fun i hi => (hes i hi).1.1
  have hcross : ∀ i ∈ P, ∀ j ∈ P, es i * cA D (es j) = 0 :=
    GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es P h1 (hsum ▸ hc)
  have h2 : ∀ i ∈ P, ∀ j ∈ P, j ≠ i → es i * es j = 0 := fun i hi j hj hji =>
    GlobalTheory.PlaceDatum.idemAt_mul (hes i hi) (hes j hj) (hcross i hi j hj) (hcross j hj i hi) hji
  have h3 : es PP * e = es PP := by
    rw [hsum]; exact sum_mul_idem (R := AE D) es P h1 h2 hP
  obtain ⟨h4, h5⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D (es PP) PP (hes PP hP)
  have h6 : (⟨_, h4⟩ * ⟨_, hint⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨_, h4⟩ :=
    Subtype.ext (by change toEAf D _ * toEAf D _ = toEAf D _; rw [← RingHom.map_mul, h3])
  have h7 := congrArg (resS D.host.F PP) h6
  rwa [map_mul, h5, one_mul] at h7

def rect (κ : Type) [Zero κ] [One κ] (b a : ℕ) : Matrix (Fin b) (Fin a) κ := fun i j => if i.val = j.val then 1 else 0

theorem lowZero_rect {κ : Type} [Zero κ] [One κ] (b a k : ℕ) : LowZero k (rect κ b a) :=
  fun i j hi hj => if_neg (by omega)

theorem topL_rect {κ : Type} [Zero κ] [One κ] {b a k : ℕ} (hb : k ≤ b) (ha : k ≤ a) : topL k (rect κ b a) = 1 := by
  ext i j
  unfold topL rect
  rw [dif_pos ⟨lt_of_lt_of_le i.2 hb, lt_of_lt_of_le j.2 ha⟩, Matrix.one_apply]
  simp only [Fin.ext_iff]

theorem frame_smul {R : Type} [CommRing R] {a b : ℕ} (p : GL (Fin a) R) (q : GL (Fin b) R) (c : R)
    (y z : Matrix (Fin b) (Fin a) R) (h : ∀ i j, z i j = c * (q.val * y * (p⁻¹).val) i j) (i : Fin b) (j : Fin a) :
    ((q⁻¹).val * z * p.val) i j = c * y i j := by
  have hz : z = c • (q.val * y * (p⁻¹).val) := Matrix.ext h
  rw [hz, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc q.val, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul,
    Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, Matrix.smul_apply, smul_eq_mul]

theorem exists_rect (S T : HSp D) (βS : GL (Fin S.rank) (Datum.EAf D)) (βT : GL (Fin T.rank) (Datum.EAf D))
    {e : AE D} {P : Finset (Pl D.host.E)} (h : IsIdemSum e P) :
    ∃ x : WO S T, IsHalf e x ∧ IsIntM (frMapO S T βS βT x) ∧
      ∀ PP ∈ P, redM PP (frMapO S T βS βT x) = rect _ _ _ := by
  obtain ⟨hi, hr⟩ := resS_idemSum h
  have he := GlobalTheory.PlaceDatum.idemSum_mul_self h
  choose s hs using toEAf_surjective (D := D)
  let x : Matrix (Fin T.rank) (Fin S.rank) (AE D) :=
    fun i j => e * s (HMul.hMul (HMul.hMul βT.val (rect (Datum.EAf D) T.rank S.rank)) (βS⁻¹).val i j)
  have hf : ∀ i j, frMapO S T βS βT x i j = if i.val = j.val then toEAf D e else 0 := by
    intro i j
    refine (frame_smul βS βT (toEAf D e) (rect (Datum.EAf D) T.rank S.rank) (x.map (toEAf D)) (fun i j => ?_) i j).trans ?_
    · exact (RingHom.map_mul _ _ _).trans (congrArg _ (hs _))
    · rw [rect, mul_ite, mul_one, mul_zero]
  have hI : IsIntM (frMapO S T βS βT x) := fun i j => by
    rw [hf]
    split_ifs
    · exact hi
    · exact zero_mem _
  refine ⟨x, fun i j => by simp only [x]; rw [← mul_assoc, he], hI, fun PP hP => ?_⟩
  ext i j
  refine (dif_pos (hI i j)).trans ?_
  unfold rect
  split_ifs with hij
  · rw [← hr PP hP]
    exact congrArg _ (Subtype.ext ((hf i j).trans (if_pos hij)))
  · rw [← map_zero (resS D.host.F PP)]
    exact congrArg _ (Subtype.ext ((hf i j).trans (if_neg hij)))

theorem omegaG_ne_zero {a b : ℕ} (hab : a ≤ b) (L : LevDat D.host.E ℂ a) (χ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) (hy : ∀ PP ∈ L.Pg, y PP = rect _ _ _) :
    omegaG L χ y ≠ 0 := by
  unfold omegaG
  split_ifs with h
  · refine mul_ne_zero (mul_ne_zero (Units.ne_zero _) ?_) ?_
    · exact Finset.prod_ne_zero_iff.2 fun _ _ => Finset.prod_ne_zero_iff.2 fun _ _ => Units.ne_zero _
    · exact Finset.prod_ne_zero_iff.2 fun _ _ => inv_ne_zero (Units.ne_zero _)
  · refine absurd ⟨fun PP hP => ?_, fun _ => 1, fun PP => ?_, fun _ => one_mem _, ?_⟩ h
    · rw [hy PP hP]; exact lowZero_rect _ _ _
    · rw [hy PP.1 PP.2, topL_rect hab le_rfl, Units.val_one]
    · convert L.P.H.one_mem using 1
      funext PP
      exact blockDiagonalExtendByOnePrimeField_one _ _

theorem omegaQ_ne_zero {a b r : ℕ} (ha : r ≤ a) (hb : r ≤ b) (Q : Finset (Pl D.host.E))
    (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) (hy : ∀ PP ∈ Q, y PP = rect _ _ _) :
    omegaQ Q r ξ k y ≠ 0 := by
  unfold omegaQ
  split_ifs with h
  · exact Finset.prod_ne_zero_iff.2 fun _ _ => zpow_ne_zero _ (Units.ne_zero _)
  · refine absurd (fun PP hP => ?_) h
    rw [hy PP hP, topL_rect hb ha, Matrix.det_one]
    exact ⟨lowZero_rect _ _ _, isUnit_one⟩

theorem stepVec_vac {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {βS : GL (Fin S.rank) (Datum.EAf D)} {βT : GL (Fin T.rank) (Datum.EAf D)} {L : LevDat D.host.E ℂ S.rank}
    {χ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {Q : Finset (Pl D.host.E)}
    {ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {f₀ f : WO S T → ℂ} (dS : IsSelfDualC S ΛS) (dT : IsSelfDualC T ΛT)
    (hr : S.rank ≤ T.rank) (h : IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT L χ Q ξ f₀ f) :
    IsThetaFunO ψ S T f ∧ f ≠ 0 ∧ ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f := by
  classical
  obtain ⟨hv, e, he', ⟨Tm, hTm⟩, hall⟩ := h
  obtain ⟨P, he, hP⟩ : ∃ P, IsIdemSum e P ∧ ∀ PP, PP ∈ P ↔ PP ∈ L.Pg ∨ PP ∈ Q :=
    ⟨_, he', fun PP => Finset.mem_union⟩
  have h0 : f₀ ≠ 0 := by
    rintro rfl
    obtain ⟨⟨p, hp⟩, h2⟩ := hv.2.norm
    have := h2 p hp
    simp [nrm2] at this
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO dS.1 dT.1 βS βT
  have hSB := GlobalTheory.PlaceDatum.isSBHalf_of_red e _ (frMapO S T βS βT) (GlobalTheory.PlaceDatum.frMapO_add βS βT)
      (GlobalTheory.PlaceDatum.exists_den_frMapO dS.1.fg dT.1.fg βS βT)
      ⟨K, hK, fun t ht => hC t (GlobalTheory.PlaceDatum.infPart_of_half hinf ht)⟩ P
      (fun y => omegaG L χ y * omegaQ Q L.r ξ 1 y) fun y y' h => by
        rw [GlobalTheory.PlaceDatum.omegaG_congr _ _ y y' fun PP hPP => h PP ((hP PP).2 (Or.inl hPP)),
          GlobalTheory.PlaceDatum.omegaQ_congr _ _ _ 1 y y' fun PP hPP => h PP ((hP PP).2 (Or.inr hPP))]
  obtain ⟨k1, k2⟩ := GlobalTheory.Chain.StepVac.placeModel_span_ne hv.1 dS dT (GlobalTheory.PlaceDatum.idemSum_mul_self he) he.2 hinf hTm hSB
  rw [← hall Tm hTm] at k1 k2
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 k1
  refine ⟨?_, k2 h0 fun hz => ?_, fun τ => ?_⟩
  · rw [← hc]
    exact GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hv.1.1 f₀ hv.2.theta _ c.support (fun a => a.1) c fun a _ => a.2
  · obtain ⟨x, h1, h2, h3⟩ := exists_rect S T βS βT he
    have := congrFun hz x
    rw [if_pos ⟨h1, h2⟩] at this
    exact mul_ne_zero (omegaG_ne_zero hr L χ _ fun PP h => h3 PP ((hP PP).2 (Or.inl h)))
      (omegaQ_ne_zero L.hr (L.hr.trans hr) Q ξ 1 _ fun PP h => h3 PP ((hP PP).2 (Or.inr h))) this
  · rw [← hc]
    exact GlobalTheory.FockTranslate.isFockVacAt_sum D ψ θ S T hv.1.1 hv.2.inf f₀ hv.2.theta τ _ (hv.2.fock τ) _ c.support
      (fun a => a.1) c fun a _ => a.2

end GlobalTheory.InnerSteps

end
