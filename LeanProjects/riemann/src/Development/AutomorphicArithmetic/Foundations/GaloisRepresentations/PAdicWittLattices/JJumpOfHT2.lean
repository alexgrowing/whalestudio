import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.CoverLowOfCov
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamExistsHodgeTateEigenbasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateNoTwistedInvariantsComplexPadicStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemClosureOfJumps
import Formalism.LocalToGlobal.CyclotomicLocalNorms.AddValuationAlgebraMapPadicIntUnitEqZero
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

namespace UpperTheory.Gal.G3

private theorem eig_coord {F : Type} [Field F] {m : ℕ} (s : F →+* F) (A : Matrix (Fin m) (Fin m) F)
    (Q : Matrix.GeneralLinearGroup (Fin m) F) (D : Fin m → F) (z : Fin m → F) (u : F)
    (h1 : A * (Q : Matrix (Fin m) (Fin m) F).map s = (Q : Matrix (Fin m) (Fin m) F) * Matrix.diagonal D)
    (h2 : A.mulVec (fun q => s (z q)) = u • z) (i : Fin m) :
    D i * s (((Q⁻¹ : Matrix.GeneralLinearGroup (Fin m) F) : Matrix (Fin m) (Fin m) F).mulVec z i) =
      u * ((Q⁻¹ : Matrix.GeneralLinearGroup (Fin m) F) : Matrix (Fin m) (Fin m) F).mulVec z i := by
  set Qi : Matrix (Fin m) (Fin m) F := ((Q⁻¹ : Matrix.GeneralLinearGroup (Fin m) F) : Matrix (Fin m) (Fin m) F) with hQi
  set Qm : Matrix (Fin m) (Fin m) F := (Q : Matrix (Fin m) (Fin m) F) with hQm
  have hQ1 : Qm * Qi = 1 := by
    rw [hQi, hQm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hQ2 : Qi * Qm = 1 := by
    rw [hQi, hQm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  set c : Fin m → F := Qi.mulVec z with hc
  have hz : Qm.mulVec c = z := by
    rw [hc, Matrix.mulVec_mulVec, hQ1, Matrix.one_mulVec]
  have hsz : (fun q => s (z q)) = (Qm.map s).mulVec (fun q => s (c q)) := by
    funext q
    rw [← hz]
    exact RingHom.map_mulVec s Qm c q
  have key : Qm.mulVec ((Matrix.diagonal D).mulVec (fun q => s (c q))) = Qm.mulVec (u • c) := by
    rw [Matrix.mulVec_mulVec, ← h1, ← Matrix.mulVec_mulVec, ← hsz, h2, Matrix.mulVec_smul, hz]
  have key2 : (Matrix.diagonal D).mulVec (fun q => s (c q)) = u • c := by
    have h3 : ∀ v : Fin m → F, Qi.mulVec (Qm.mulVec v) = v := fun v => by
      rw [Matrix.mulVec_mulVec, hQ2, Matrix.one_mulVec]
    rw [← h3 ((Matrix.diagonal D).mulVec fun q => s (c q)), key, h3]
  have := congrFun key2 i
  simpa [Matrix.mulVec_diagonal] using this

private theorem chi_solve {l : ℕ} [Fact l.Prime] (t : ℚ_[l]ˣ) (n b : ℤ) (x y : ℂ_[l])
    (h : (((t ^ (-n) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) * y = (((t ^ (-b) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) * x) :
    y = (((t ^ (n - b) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) * x := by
  have e : ∀ u v : ℚ_[l]ˣ, (((u * v : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) = ((u : ℚ_[l]) : ℂ_[l]) * ((v : ℚ_[l]) : ℂ_[l]) :=
    fun u v => by rw [Units.val_mul]; exact map_mul (algebraMap ℚ_[l] ℂ_[l]) _ _
  have one : (((1 : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) = 1 := by
    rw [Units.val_one]; exact map_one (algebraMap ℚ_[l] ℂ_[l])
  calc y = (((t ^ n * t ^ (-n) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) * y := by
        rw [← zpow_add, add_neg_cancel, zpow_zero, one, one_mul]
    _ = (((t ^ n : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) * ((((t ^ (-n) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) * y) := by
        rw [e, mul_assoc]
    _ = (((t ^ n : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) * ((((t ^ (-b) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) * x) := by rw [h]
    _ = (((t ^ (n - b) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) * x := by
        rw [← mul_assoc, ← e, ← zpow_add, sub_eq_add_neg]

private theorem gal_cont {l : ℕ} [Fact l.Prime] (g : GQ l) : Continuous fun x : Om l => g x := by
  refine (AddMonoidHomClass.isometry_of_norm g fun x => ?_).continuous
  have h := GlobalTheory.RingBasics.norm_σC g (x : ℂ_[l])
  rw [GlobalTheory.RingBasics.σC_coe, UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe] at h
  exact h

private theorem chiPow_eq {l : ℕ} [Fact l.Prime] (P : LocPrime l) (σ : GQ l) (n : ℤ) :
    GlobalTheory.HTLink.chiPow σ n = ((((P.χQ σ) ^ n : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) := by
  have hχ : P.χQ = Formalism.L2.LocGap.Gal.χQ l := Formalism.L2.LocGap.Gal.eq_χQ_of_cyc P.χQ P.χQ_cyc
  rw [GlobalTheory.HTLink.chiPow, hχ, Units.val_zpow_eq_zpow_val]
  exact (map_zpow₀ (algebraMap ℚ_[l] ℂ_[l]) _ n).symm

end UpperTheory.Gal.G3

set_option maxHeartbeats 1000000 in

theorem UpperTheory.Gal.G3.jJumpOfHT2 :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.JumpOfHT2 := by
  classical
  unfold PositivityTheory.AutomorphicGaloisHodgeTate.G8.JumpOfHT2
  intro E Ω _ _ _ _ _ l _ P AI hT' Gw O O' _ _ _ _ _ _ Bw Bw' γ hC d r a Jm hOcc hJ
  obtain ⟨hT⟩ := hT'
  obtain ⟨LL', r', ⟨hLL, hmod⟩, hdR, τ', hInd, hcnt⟩ := hJ
  obtain ⟨S, z, hz0, hz⟩ := hOcc
  haveI := Bw.Kw.2
  haveI := Bw'.Kw.2
  haveI := LL'.2

  have hg : ∀ y : ↥Bw.Kw.1, γ (y : Om l) = ((τ' y : ↥LL'.1) : Om l) := by
    let τo : ↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l := LL'.1.val.comp τ'
    let g₁ : GQ l := AlgEquiv.ofBijective (τo.liftNormal (Om l)) (Algebra.IsAlgebraic.algHom_bijective _)
    have hg₁ : ∀ y : ↥Bw.Kw.1, g₁ (y : Om l) = ((τ' y : ↥LL'.1) : Om l) := fun y =>
      τo.liftNormal_commutes (Om l) y
    have hclosed : IsClosed {x : Om l | g₁ x = γ x} := isClosed_eq (gal_cont g₁) (gal_cont γ)
    have hsub : Set.range (fun x : E => Bw.j (algebraMap E Ω x)) ⊆ {x : Om l | g₁ x = γ x} := by
      rintro _ ⟨x, rfl⟩
      calc g₁ (Bw.j (algebraMap E Ω x)) = ((τ' ⟨Bw.j (algebraMap E Ω x), Bw.j_E x⟩ : ↥LL'.1) : Om l) :=
            hg₁ ⟨_, Bw.j_E x⟩
        _ = Bw'.j (algebraMap E Ω x) := (hInd x).symm
        _ = γ (Bw.j (algebraMap E Ω x)) := hC.1 _
    intro y
    rw [← hg₁ y]
    exact ((hclosed.closure_subset_iff.2 hsub) (Bw.j_dense y.2)).symm

  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : FinExt l, K₁.1 = Bw.Kw.1.map (γ : Om l →ₐ[ℚ_[l]] Om l) :=
    ⟨⟨Bw.Kw.1.map (γ : Om l →ₐ[ℚ_[l]] Om l),
      LinearEquiv.finiteDimensional (IntermediateField.equivMap Bw.Kw.1 (γ : Om l →ₐ[ℚ_[l]] Om l)).toLinearEquiv⟩, rfl⟩
  have hK : ∀ x, x ∈ Bw.Kw.1 ↔ γ x ∈ K₁.1 := GlobalTheory.Pst.BridgeInd.mem_iff_of_map_eq hK₁
  have hK₁LL : K₁.1 ≤ LL'.1 := by
    rw [hK₁]
    rintro _ ⟨x, hx, rfl⟩
    change γ x ∈ LL'.1
    rw [show γ x = _ from hg ⟨x, hx⟩]
    exact (τ' ⟨x, hx⟩).2

  let cj : ↥(GK K₁) →* ↥(GK Bw.Kw) :=
    { toFun := fun h => ⟨γ⁻¹ * (h : GQ l) * γ, GlobalTheory.Pst.BridgeInd.mem_GK_conj_inv hK h.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun h₁ h₂ => Subtype.ext (by simp [mul_assoc]) }
  let r₁ : ↥(GK K₁) →* Matrix.GeneralLinearGroup (Fin d) ↥LL'.1 :=
    (r'.comp Bw.e.symm.toMonoidHom).comp cj
  have hρ : ∀ (h : ↥(GK Bw.Kw)) (h' : ↥(GK K₁)), (h' : GQ l) = γ * h * γ⁻¹ →
      (((Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ↥LL'.1 ≃ₐ[↥LL'.1] _) : _ →* _).comp
        ((Units.coeHom _).comp r₁)) h' = Bw.repE LL' r' h := by
    intro h h' hh
    have : cj h' = h := Subtype.ext (by simp [cj, hh, mul_assoc])
    simp only [MonoidHom.comp_apply, r₁, this]
    rfl
  have hD := GlobalTheory.Pst.BridgeInd.finrank_DdR_conj P hρ hK
  have hdR₁ : Module.finrank ↥LL'.1 ↥(DdR (P.PD K₁) (LL := ↥LL'.1) (V := Fin d → ↥LL'.1)
      (((Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ↥LL'.1 ≃ₐ[↥LL'.1] _) : _ →* _).comp
        ((Units.coeHom _).comp r₁))) = Module.finrank ℚ_[l] ↥K₁.1 * d := by
    rw [← hD, ← GlobalTheory.Pst.BridgeInd.finrank_eq_of_mem_iff_field hK]
    exact hdR
  let τ₂ : ↥K₁.1 →ₐ[ℚ_[l]] ↥LL'.1 := IntermediateField.inclusion hK₁LL
  have hτ₂ : ∀ x : ↥K₁.1, ((τ₂ x : ↥LL'.1) : Om l) = (x : Om l) := fun x => rfl
  have hM : ∀ n, multV (P.PD Bw.Kw) (Bw.repE LL' r') τ' n = multV (P.PD K₁) _ τ₂ n :=
    fun n => GlobalTheory.Pst.BridgeInd.multV_conj P hρ hK τ' τ₂ (fun c c' hc => Subtype.ext (by
      change (c' : Om l) = _; rw [hc, hg])) n
  have hsplit : ∀ (σ : ↥K₁.1 →ₐ[ℚ_[l]] Om l) (x : ↥K₁.1), σ x ∈ LL'.1 := by
    intro σ x
    have hx : γ⁻¹ (x : Om l) ∈ Bw.Kw.1 := (hK _).2 (by simp)
    let e₁ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥K₁.1 :=
      ((γ : Om l →ₐ[ℚ_[l]] Om l).comp Bw.Kw.1.val).codRestrict K₁.1.toSubalgebra fun c => (hK _).1 c.2
    have he : e₁ ⟨γ⁻¹ (x : Om l), hx⟩ = x := Subtype.ext (by
      change γ (γ⁻¹ (x : Om l)) = (x : Om l)
      rw [← AlgEquiv.mul_apply, mul_inv_cancel]; rfl)
    rw [← he]
    exact hLL (Bw.LL_split (σ.comp e₁) ⟨γ⁻¹ (x : Om l), hx⟩)
  haveI := K₁.2
  let K₀ : FinExt l := ⟨K₁.1 ⊔ LL'.1, inferInstance⟩
  obtain ⟨Pm, k, hk, heig⟩ := GlobalTheory.T.deRham_exists_hodgeTate_eigenbasis l P AI hT K₁ LL' d r₁ hdR₁ hsplit τ₂ hτ₂ K₀
    le_sup_left le_sup_right
  have hJm : Multiset.map k Finset.univ.val = Jm := by
    refine Multiset.ext.mpr fun n => ?_
    have := (hk n).trans ((hM n).symm.trans (hcnt n).symm)
    exact_mod_cast this

  let F : IntermediateField ℚ_[l] (Om l) := IntermediateField.adjoin ℚ_[l] (S : Set (Om l))
  haveI : FiniteDimensional ℚ_[l] F :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  haveI := K₀.2
  let K'' : FinExt l := ⟨K₀.1 ⊔ Bw'.Kw.1 ⊔ F, inferInstance⟩
  set c : Fin d → ℂ_[l] :=
    ((Pm⁻¹ : Matrix.GeneralLinearGroup (Fin d) ℂ_[l]) : Matrix (Fin d) (Fin d) ℂ_[l]).mulVec z with hc
  have hcoord : ∀ h : GQ l, h ∈ GK K'' → ∀ i,
      ((((P.χQ h) ^ (-k i) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) * Per.σC h (c i) =
        ((((P.χQ h) ^ (-a) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) * c i := by
    intro h hh i
    have h0 : h ∈ GK K₀ := GK_le (le_trans le_sup_left le_sup_left) hh
    have hw : h ∈ GK Bw'.Kw := GK_le (le_trans le_sup_right le_sup_left) hh
    have h1 : h ∈ GK K₁ := GK_le le_sup_left h0
    have hS : ∀ x ∈ S, h x = x := fun x hx =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hh x
        ((le_sup_right : F ≤ K''.1) (IntermediateField.subset_adjoin _ _ hx))
    have hx : Bw'.e.symm ⟨h, hw⟩ = Bw.e.symm (cj ⟨h, h1⟩) := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      rw [hC.2, MulEquiv.apply_symm_apply]
      change h = γ * (γ⁻¹ * h * γ) * γ⁻¹
      group
    have e1 : ((r (Bw'.e.symm ⟨h, hw⟩)).val.map (algebraMap (Om l) ℂ_[l])).mulVec (fun q => Per.σC h (z q)) =
        GlobalTheory.HTLink.chiPow h (-a) • z := hz ⟨h, hw⟩ hS
    have e2 := heig ⟨h, h1⟩ h0
    have hr : (r (Bw.e.symm (cj ⟨h, h1⟩))).val.map (algebraMap (Om l) ℂ_[l]) =
        (r₁ ⟨h, h1⟩ : Matrix (Fin d) (Fin d) ↥LL'.1).map (fun x => (((x : ↥LL'.1) : Om l) : ℂ_[l])) := by
      rw [← hmod]
      rfl
    rw [hx, hr, chiPow_eq P] at e1
    exact eig_coord (Per.σC h) _ Pm _ z _ e2 e1 i
  have hc0 : ∃ i, c i ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hz0
    have hc' : c = 0 := funext hall
    have : (Pm : Matrix (Fin d) (Fin d) ℂ_[l]).mulVec c = z := by
      rw [hc, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [← this, hc', Matrix.mulVec_zero]
  obtain ⟨i, hi⟩ := hc0
  have hki : k i = a := by
    by_contra hne
    exact hi (GlobalTheory.T.tate_no_twisted_invariants_complexPadic l P AI hT K'' (k i - a) (sub_ne_zero.2 hne) (c i) fun g =>
      UpperTheory.Gal.G3.chi_solve _ _ _ _ _ (hcoord g g.2 i))
  rw [← hJm, ← hki]
  exact Multiset.mem_map_of_mem k (Finset.mem_univ_val i)

end
