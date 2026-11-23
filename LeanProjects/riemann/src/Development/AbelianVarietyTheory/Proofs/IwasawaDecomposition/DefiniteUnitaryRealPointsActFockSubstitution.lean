import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorOMulSource
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactActsOnRealVacuaByDetPowers

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefLift.FockAct

open GlobalTheory.AdTh.SourceBasis GlobalTheory.OrientedHeis

theorem unitMap_mul_mul {m n : ℕ} (B U : Matrix (Fin n) (Fin n) ℂ) (B' H : Matrix (Fin m) (Fin m) ℂ) (i : Fin m)
    (j : Fin n) : unitMap (B * U) (B' * H) i j = ∑ i', ∑ c, (H i' i * U⁻¹ j c) • unitMap B B' i' c := by
  have e : H * Matrix.single i j (1 : ℂ) * U⁻¹ = ∑ i', ∑ c, (H i' i * U⁻¹ j c) • Matrix.single i' c (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single (H * Matrix.single i j (1 : ℂ) * U⁻¹)]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
    congr 1
    rw [Matrix.mul_apply, Finset.sum_eq_single j (fun c _ hc => by simp [Matrix.mul_single_apply_of_ne, hc]) (by simp)]
    simp
  unfold unitMap
  calc _ = B' * (H * Matrix.single i j (1 : ℂ) * U⁻¹) * B⁻¹ := by
        rw [Matrix.mul_inv_rev]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [e, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D}

theorem pureTensorO_mul_mul (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (BV U : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (BW H : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (P : Pol D.what₂.Tau W.rank V.rank) :
    pureTensorO ψ θ V W (fun _ => 1) (fun _ => 1) (fun τ => BV τ * U τ) (fun τ => BW τ * H τ) f P =
      pureTensorO ψ θ V W (fun _ => 1) (fun _ => 1) BV BW f (subst (fun τ => (U τ)⁻¹) H P) := by
  have hadd : ∀ f f', IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → IsThetaFunO ψ V W (f + f') := fun _ _ => theta_add
  have hsm : ∀ (a : ℂ) f, IsThetaFunO ψ V W f → IsThetaFunO ψ V W (a • f) := fun a _ => theta_smul a
  have hA : ∀ (BS : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
      (BT : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) i f, IsThetaFunO ψ V W f →
      IsThetaFunO ψ V W (aPlusAll (heisO ψ V W) θ (fun _ => cplxO 1 1) BS BT i f) :=
    fun _ _ _ _ h => aPlus_th hψ hθ _ _ _ h
  have hm : ∀ (BS : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
      (BT : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) Q,
      IsThetaFunO ψ V W (pureTensorO ψ θ V W (fun _ => 1) (fun _ => 1) BS BT f Q) := fun BS BT Q =>
    GlobalTheory.Ker.FockAlg.pure_mem (P := IsThetaFunO ψ V W) hadd hsm (hA BS BT) hf Q
  have hX : ∀ (BS : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
      (BT : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) Q v,
      pureTensorO ψ θ V W (fun _ => 1) (fun _ => 1) BS BT f (MvPolynomial.X v * Q) =
        aPlusAll (heisO ψ V W) θ (fun _ => cplxO 1 1) BS BT v
          (pureTensorO ψ θ V W (fun _ => 1) (fun _ => 1) BS BT f Q) :=
    fun BS BT Q v => GlobalTheory.Ker.FockAlg.pure_X_mul (A := aPlusAll (heisO ψ V W) θ (fun _ => cplxO 1 1) BS BT)
      (P := IsThetaFunO ψ V W) hadd hsm (hA BS BT)
      (fun i j _ h => aPlus_comm hψ hθ i.1 _ (s := fun _ => 1) (fun τ => by simp) (fun τ => by simp) j.1 _ h)
      (fun _ _ _ h h' => aPlus_add hψ hθ _ _ _ h h') (fun _ a _ h => aPlus_smul hψ hθ _ _ _ a h) hf Q v
  have h1 := fun BS BT => GlobalTheory.FiniteFock.pureTensorO_one ψ θ V W (fun _ => 1) (fun _ => 1) BS BT f
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, ← mul_one (MvPolynomial.C a), ← MvPolynomial.smul_eq_C_mul,
      map_smul, map_smul, h1, h1]
  | add P Q hP hQ => rw [map_add, map_add, map_add, hP, hQ]
  | mul_X P v hP =>
    obtain ⟨τ, i, j⟩ := v
    rw [mul_comm, hX, hP, map_mul]
    clear hP
    generalize (subst _ H P : Pol D.what₂.Tau W.rank V.rank) = Q
    rw [subst, MvPolynomial.aeval_X]
    simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, hX]
    simp only [aPlusAll, aPlus]
    rw [unitMap_mul_mul, crea_sum hψ hθ _ (hm _ _ _), Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [crea_sum hψ hθ _ (hm _ _ _), Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [crea_smul hψ hθ τ _ (hm _ _ _) _ True (by simp), if_pos trivial, smul_comm]

theorem om_vac {χS χT : (AE D)ˣ →* Circle} {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}
    (hω : IsWeilDatumO ψ V W χS χT ω) (hθ : IsInfFam θ) (kV : V.SigOK) (kW : W.SigOK)
    {sS : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ}
    (hS : ∀ τ, IsCartanInv (gramAt D V τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D W τ) (sT τ))
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
    (hv : ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (sS τ) (sT τ)) f) {g : GA D V} (hg : g ∈ GinfC V)
    {h : GA D W} (hh : h ∈ GinfC W)
    (cS : ∀ τ, sS τ * compAt θ τ (Formalism.L2.Theta.mt V g) = compAt θ τ (Formalism.L2.Theta.mt V g) * sS τ)
    (cT : ∀ τ, sT τ * compAt θ τ (Formalism.L2.Theta.mt W h) = compAt θ τ (Formalism.L2.Theta.mt W h) * sT τ) :
    ∃ c : ℂ, ω (g, h) f = c • f := by
  have dS := GlobalTheory.PlaceModel.isSelfDualC_latFrame V
  have dT := GlobalTheory.PlaceModel.isSelfDualC_latFrame W
  obtain ⟨f₀, h₀⟩ := GlobalTheory.VacuumO.vacExists D ψ θ hω.std hθ V W sS sT kV kW hS hT _ _ dS dT
  have h1 := GlobalTheory.WeilVacMove.isVacO_om D ψ θ V W χS χT ω hω hθ sS sS sT sT _ _ _ _ g h cS cT
    (fun u => ⟨fun hu => ⟨u, hu, (GlobalTheory.VacuumChar.actO_fin hg hh (GlobalTheory.SplitScalar.latO_fin hu)).symm⟩,
      fun ⟨u₀, hu, e⟩ => by rwa [e, GlobalTheory.VacuumChar.actO_fin hg hh (GlobalTheory.SplitScalar.latO_fin hu)]⟩) f₀ h₀
  obtain ⟨c, -, e⟩ := GlobalTheory.VacUnique.vacUniqueO D ψ θ hω.std hθ V W sS sT kV kW hS hT _ _ dS dT f₀ _ h₀ h1
  refine ⟨c, ?_⟩
  have hs := GlobalTheory.VacuumChar.mem_span kV kW hS hT dS dT h₀ (f := f) ⟨hf, hv⟩
  clear hf hv
  induction hs using Submodule.span_induction with
  | mem _ hx =>
    obtain ⟨x, rfl⟩ := hx
    show ω (g, h) (heisO ψ V W x f₀) = c • heisO ψ V W x f₀
    rw [hω.om_heis g h _ _ h₀.2.theta, GlobalTheory.VacuumChar.actO_fin hg hh x.2, e, GlobalTheory.SplitScalar.heisO_smul]
  | zero => rw [map_zero, smul_zero]
  | add a b _ _ ha hb => rw [map_add, ha, hb, smul_add]
  | smul r a _ ha => rw [map_smul, ha, smul_comm]

open Classical in
theorem compAt_atTau {S : D.what₂.Tau → SPar} {M : DSModel V S} (hθ : IsInfFam θ) (h : AllPlus M) (τ : D.what₂.Tau)
    (u : Matrix.unitaryGroup (Fin V.rank) ℂ) (ρ : D.what₂.Tau) :
    onb M ρ * (if ρ = τ then (u : Matrix (Fin V.rank) (Fin V.rank) ℂ) else 1) =
      compAt θ ρ (Formalism.L2.Theta.mt V (atTau θ V τ (unfr M τ u))) * onb M ρ := by
  have s := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ (h.unfr_mem τ u)
  split_ifs with e
  · subst e
    have e1 : compAt θ ρ (Formalism.L2.Theta.mt V (atTau θ V ρ (unfr M ρ u))) = unfr M ρ u := s.2.1
    rw [e1, unfr, onb, Matrix.mul_nonsing_inv_cancel_right _ _ (fr_det M ρ)]
  · have e1 : compAt θ ρ (Formalism.L2.Theta.mt V (atTau θ V τ (unfr M τ u))) = 1 := s.2.2 ρ e
    rw [e1, Matrix.mul_one, Matrix.one_mul]

theorem compAt_one (B : Matrix (Fin V.rank) (Fin V.rank) ℂ) (ρ : D.what₂.Tau) :
    B * 1 = compAt θ ρ (Formalism.L2.Theta.mt V 1) * B := by
  have e1 : compAt θ ρ (Formalism.L2.Theta.mt V 1) = 1 := GlobalTheory.PointAtPlaceHom.infMat_one V (θ ρ)
  rw [e1, Matrix.mul_one, Matrix.one_mul]

theorem om_ptOf {χS χT : (AE D)ˣ →* Circle} {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}
    {S S' : D.what₂.Tau → SPar} {M : DSModel V S} {M' : DSModel W S'} {f : WO V W → ℂ}
    (hω : IsWeilDatumO ψ V W χS χT ω) (hθ : IsInfFam θ) (kV : V.SigOK) (kW : W.SigOK) (hM : AllPlus M)
    (hM' : AllPlus M') (hf : IsThetaFunO ψ V W f)
    (hv : ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) f) {g : GA D V} (hg : g ∈ GinfC V)
    {h : GA D W} (hh : h ∈ GinfC W) (U : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (H : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (hU : ∀ ρ, onb M ρ * U ρ = compAt θ ρ (Formalism.L2.Theta.mt V g) * onb M ρ)
    (hH : ∀ ρ, onb M' ρ * H ρ = compAt θ ρ (Formalism.L2.Theta.mt W h) * onb M' ρ) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ P, ω (g, h) (ptOf ψ θ M M' f P) = c • ptOf ψ θ M M' f (subst (fun ρ => (U ρ)⁻¹) H P) := by
  have e1 : cart M = fun _ => 1 := funext hM.cart
  have e2 : cart M' = fun _ => 1 := funext hM'.cart
  unfold ptOf
  rw [e1, e2] at hv ⊢
  obtain ⟨c, c0, hc⟩ : ∃ c : ℂ, c ≠ 0 ∧ ω (g, h) f = c • f := by
    by_cases f0 : f = 0
    · exact ⟨1, one_ne_zero, by rw [f0, map_zero, smul_zero]⟩
    obtain ⟨c, e⟩ := om_vac hω hθ kV kW (sS := fun _ => 1) (sT := fun _ => 1)
      (fun τ => ⟨by simp, by simp, by simpa using hM.posDef τ⟩) (fun τ => ⟨by simp, by simp, by simpa using hM'.posDef τ⟩)
      hf hv hg hh (fun τ => by simp) (fun τ => by simp)
    refine ⟨c, fun c0 => f0 ?_, e⟩
    rw [c0, zero_smul] at e
    have e' := congrArg (ω (g, h)⁻¹) e
    rwa [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at e'
  refine ⟨c, c0, fun P => ?_⟩
  rw [(om_pureTensorO D ψ θ V W χS χT ω hω hθ (fun _ => 1) (fun _ => 1) (onb M) (fun ρ => onb M ρ * U ρ)
    (fun _ => 1) (fun _ => 1) (onb M') (fun ρ => onb M' ρ * H ρ) g h (fun τ => by simp) (fun τ => by simp) hU hH f hf P).2,
    hc, GlobalTheory.FiniteFock.pureTensorO_smul, pureTensorO_mul_mul hω.std hθ _ _ _ _ hf]

theorem fock_act : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (θ : InfFam D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (f : WO V W → ℂ), IsWeilDatumO ψ V W χS χT ω → IsInfFam θ → V.SigOK → W.SigOK → AllPlus M → AllPlus M' → IsThetaFunO ψ V W f → (∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) f) → ∀ τ, (∀ g : Matrix.unitaryGroup (Fin V.rank) ℂ, ∃ c : ℂ, c ≠ 0 ∧ ∀ P, ω (atTau θ V τ (unfr M τ g), 1) (ptOf ψ θ M M' f P) = c • ptOf ψ θ M M' f (colSub W.rank τ g P)) ∧ ∀ u : Matrix.unitaryGroup (Fin W.rank) ℂ, ∃ c : ℂ, c ≠ 0 ∧ ∀ P, ω (1, atTau θ W τ (unfr M' τ u)) (ptOf ψ θ M M' f P) = c • ptOf ψ θ M M' f (rowSub V.rank τ u P) := by
  classical
  intro D ψ V W χS χT ω θ S S' M M' f hω hθ kV kW hM hM' hf hv τ
  refine ⟨fun g => ?_, fun u => ?_⟩
  · have := om_ptOf hω hθ kV kW hM hM' hf hv (GlobalTheory.PointAtPlaceHom.atTau_mem V τ _) (one_mem _) _ (fun _ => 1)
      (compAt_atTau hθ hM τ g) (fun ρ => compAt_one _ ρ)
    have e : (fun ρ => (if ρ = τ then (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) else 1)⁻¹) =
        fun ρ => if ρ = τ then star (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) else 1 := by
      funext ρ
      split_ifs
      · exact Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 g.2)
      · exact inv_one
    rw [e] at this
    exact this
  · have := om_ptOf hω hθ kV kW hM hM' hf hv (one_mem _) (GlobalTheory.PointAtPlaceHom.atTau_mem W τ _) (fun _ => 1) _
      (fun ρ => compAt_one _ ρ) (compAt_atTau hθ hM' τ u)
    simp only [inv_one] at this
    exact this

end GlobalTheory.DefLift.FockAct

end
