import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryClassRepresentativesBijective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteAdeleIdempotentOfFMulSelf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousPf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdForm.RdLaw
variable {D : D7}

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem continuous_comm : letI := tensTopL (F := D.host.F) (E := D.host.E) (Af D.host.F)
    Continuous (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E) := by
  letI : Algebra (Af D.host.F) (D.host.E ⊗[D.host.F] Af D.host.F) := Algebra.TensorProduct.rightAlgebra
  letI : TopologicalSpace (D.host.E ⊗[D.host.F] Af D.host.F) := moduleTopology (Af D.host.F) _
  haveI : IsModuleTopology (Af D.host.F) (D.host.E ⊗[D.host.F] Af D.host.F) := ⟨rfl⟩
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  let φ : (Af D.host.F ⊗[D.host.F] D.host.E) →ₗ[Af D.host.F] (D.host.E ⊗[D.host.F] Af D.host.F) :=
    { toFun := Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E
      map_add' := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).map_add
      map_smul' := fun r x => by
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul a e =>
          rw [TensorProduct.smul_tmul', Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.comm_tmul,
            Algebra.smul_def]
          show e ⊗ₜ[D.host.F] (r • a) = ((1 : D.host.E) ⊗ₜ[D.host.F] r) * (e ⊗ₜ[D.host.F] a)
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, smul_eq_mul]
        | add x y hx hy =>
          rw [smul_add, map_add (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E),
            map_add (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E), hx, hy, smul_add] }
  haveI : ContinuousAdd (D.host.E ⊗[D.host.F] Af D.host.F) := IsModuleTopology.toContinuousAdd (Af D.host.F) _
  haveI : ContinuousSMul (Af D.host.F) (D.host.E ⊗[D.host.F] Af D.host.F) := IsModuleTopology.toContinuousSMul (Af D.host.F) _
  exact IsModuleTopology.continuous_of_linearMap φ

def finGL (V : HSp D) (h : GA D V) : GL (Fin V.rank) (EAf D) := bc (toEAf D) (matHom V h)

theorem finGL_val (V : HSp D) (h : GA D V) : (finGL V h).val = finM V rfl h := by
  rw [finM_rfl]; rfl

theorem continuous_finGL (V : HSp D) : letI := tensTopL (F := D.host.F) (E := D.host.E) (Af D.host.F)
    Continuous (finGL V) := by
  letI := tensTopL (F := D.host.F) (E := D.host.E) (Af D.host.F)
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have hv : Continuous fun h : GA D V => (finGL V h).val :=
    (GlobalTheory.Mem.VolExists.continuous_finMat (σ := D.sp.cm.sig) V.gram).matrix_map continuous_comm
  refine Units.continuous_iff.2 ⟨hv, ?_⟩
  have e : (fun h : GA D V => ((finGL V h)⁻¹ : GL (Fin V.rank) (EAf D)).val) = fun h => (finGL V h⁻¹).val := by
    funext h
    simp only [finGL, map_inv]
  rw [e]
  exact hv.comp continuous_inv

end GlobalTheory.AdForm.RdLaw

noncomputable section
namespace GlobalTheory.AdForm.RdLaw
variable {D : D7}
theorem law_left (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 D.host.F)))
    (S : StepLevel D.host.F D.host.E (sigD D) V.gram T f bad) (cl : Type)
    (yc : cl → UPts (sigD D) V.gram (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hb : Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S)))
    (Ψ) (hΨ : Ψ ∈ AdFun S (embT D)) (y : Frames (gramC V.gram (embT D))) :
    ∀ γ ∈ GQ V, ∀ g, rdS θ V rfl S yc (fun c => Ψ (yc c)) y (γ * g) = rdS θ V rfl S yc (fun c => Ψ (yc c)) y g := by
  have key := GlobalTheory.AdForm.rdS_val D θ hθ V V.rank rfl V.gram (by simp) T f bad S cl yc hb Ψ hΨ
  intro γ hγ g
  obtain ⟨γ0, h0, e⟩ := rat_mt V γ hγ
  obtain ⟨⟨x, hx⟩, hu, hv⟩ := key y g
  obtain ⟨⟨x', hx'⟩, hu', hv'⟩ := key y (γ * g)
  let z : Frames (gramC V.gram (embT D)) :=
    ⟨fun τ => infM θ V rfl g τ * y.1 τ, fun τ => by rw [det_mul]; exact (hu τ).mul (y.2 τ)⟩
  let z' : Frames (gramC V.gram (embT D)) :=
    ⟨fun τ => infM θ V rfl (γ * g) τ * y.1 τ, fun τ => by rw [det_mul]; exact (hu' τ).mul (y.2 τ)⟩
  have e1 := hv' x' z' hx' (fun τ => rfl)
  have e2 := hv x z hx (fun τ => rfl)
  have hxx : x'.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ0 * x.1 * (1 : S.U).1 := by
    apply Units.ext
    simp only [Units.val_mul, OneMemClass.coe_one, Units.val_one, Matrix.mul_one]
    rw [hx', finM_mul, rat_finM V γ0 γ e, hx]
  have hzz : IsTr (atInf (embT D) γ0.val) z z' := fun τ => by
    show infM θ V rfl (γ * g) τ * y.1 τ = atInf (embT D) γ0.val τ * (infM θ V rfl g τ * y.1 τ)
    rw [infM_mul, rat_infM θ hθ V γ0 γ e, Matrix.mul_assoc]
  have e3 := hΨ γ0 h0 x x' 1 hxx z' z hzz
  rw [map_one, Units.val_one, one_mul] at e3
  exact e1.trans (e3.trans e2.symm)

theorem law_level (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 D.host.F)))
    (S : StepLevel D.host.F D.host.E (sigD D) V.gram T f bad) (cl : Type)
    (yc : cl → UPts (sigD D) V.gram (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hb : Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S)))
    (Ψ) (hΨ : Ψ ∈ AdFun S (embT D)) (y : Frames (gramC V.gram (embT D))) :
    ∀ k ∈ GfC V, ∀ κ : S.U, κ.1.1 = finM V rfl k → ∀ g,
      rdS θ V rfl S yc (fun c => Ψ (yc c)) y (g * k) = (S.chi κ : ℂ) * rdS θ V rfl S yc (fun c => Ψ (yc c)) y g := by
  have key := GlobalTheory.AdForm.rdS_val D θ hθ V V.rank rfl V.gram (by simp) T f bad S cl yc hb Ψ hΨ
  intro k hk κ hκ g
  obtain ⟨⟨x, hx⟩, hu, hv⟩ := key y g
  obtain ⟨⟨x', hx'⟩, hu', hv'⟩ := key y (g * k)
  let z : Frames (gramC V.gram (embT D)) :=
    ⟨fun τ => infM θ V rfl g τ * y.1 τ, fun τ => by rw [det_mul]; exact (hu τ).mul (y.2 τ)⟩
  have hz : IsTr (infM θ V rfl (g * k)) y z := fun τ => by
    show infM θ V rfl g τ * y.1 τ = infM θ V rfl (g * k) τ * y.1 τ
    rw [infM_mul, infM_fin θ V k hk, Matrix.mul_one]
  have e1 := hv' x' z hx' hz
  have e2 := hv x z hx (fun τ => rfl)
  have hxx : x'.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) 1 * x.1 * κ.1 := by
    apply Units.ext
    simp only [Units.val_mul, map_one, Units.val_one, Matrix.one_mul]
    rw [hx', finM_mul, hx, hκ]
  have h1 : IsTr (atInf (embT D) (1 : GL (Fin V.rank) D.host.E).val) z z := fun τ => by
    show z.1 τ = atInf (embT D) (1 : GL (Fin V.rank) D.host.E).val τ * z.1 τ
    simp [atInf]
  have e3 := hΨ 1 (Subgroup.one_mem _) x x' κ hxx z z h1
  exact e1.trans (e3.trans (congrArg _ e2.symm))

theorem law_real (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 D.host.F)))
    (S : StepLevel D.host.F D.host.E (sigD D) V.gram T f bad) (cl : Type)
    (yc : cl → UPts (sigD D) V.gram (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hb : Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S)))
    (Ψ) (hΨ : Ψ ∈ AdFun S (embT D)) (y : Frames (gramC V.gram (embT D))) :
    ∀ k ∈ GinfC V, ∀ y', IsTr (infM θ V rfl k) y y' → ∀ g,
      rdS θ V rfl S yc (fun c => Ψ (yc c)) y (g * k) = rdS θ V rfl S yc (fun c => Ψ (yc c)) y' g := by
  have key := GlobalTheory.AdForm.rdS_val D θ hθ V V.rank rfl V.gram (by simp) T f bad S cl yc hb Ψ hΨ
  intro k hk y' hy' g
  obtain ⟨⟨x, hx⟩, hu, hv⟩ := key y' g
  obtain ⟨-, -, hv'⟩ := key y (g * k)
  let z : Frames (gramC V.gram (embT D)) :=
    ⟨fun τ => infM θ V rfl g τ * y'.1 τ, fun τ => by rw [det_mul]; exact (hu τ).mul (y'.2 τ)⟩
  have hz : IsTr (infM θ V rfl (g * k)) y z := fun τ => by
    show infM θ V rfl g τ * y'.1 τ = infM θ V rfl (g * k) τ * y.1 τ
    rw [infM_mul, Matrix.mul_assoc, ← hy' τ]
  have hx2 : x.1.1 = finM V rfl (g * k) := by rw [finM_mul, finM_inf V k hk, Matrix.mul_one, hx]
  exact (hv' x z hx2 hz).trans (hv x z hx (fun τ => rfl)).symm

end GlobalTheory.AdForm.RdLaw

noncomputable section
namespace GlobalTheory.AdForm.RdLaw
variable {D : D7}

theorem continuous_infM (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) :
    Continuous fun g : GA D V => infM θ V rfl g τ := by
  simp_rw [infM_rfl]
  exact GlobalTheory.Mem.VolExists.continuous_infMat (σ := D.sp.cm.sig) V.gram (hθ τ)

theorem law_cont (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 D.host.F)))
    (S : StepLevel D.host.F D.host.E (sigD D) V.gram T f bad) (cl : Type)
    (yc : cl → UPts (sigD D) V.gram (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hb : Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S)))
    (Ψ) (hΨ : Ψ ∈ AdFun S (embT D)) (lam) (hval : ∀ x, Ψ x ∈ ValC (gramC V.gram (embT D)) lam)
    (y : Frames (gramC V.gram (embT D)))
    (hW : ∃ W : Subgroup (GA D V), IsOpen (W : Set (GA D V)) ∧ ∀ k ∈ W, k ∈ GfC V → ∀ κ : S.U, κ.1.1 = finM V rfl k → S.chi κ = 1) :
    Continuous (rdS θ V rfl S yc (fun c => Ψ (yc c)) y) := by
  obtain ⟨W, hWo, hW⟩ := hW
  have key := GlobalTheory.AdForm.rdS_val D θ hθ V V.rank rfl V.gram (by simp) T f bad S cl yc hb Ψ hΨ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  letI := tensTopL (F := D.host.F) (E := D.host.E) (Af D.host.F)
  have hmem : ∀ h : GA D V, finGL V h ∈ UPts (sigD D) V.gram (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := fun h => by
    obtain ⟨⟨x, hx⟩, -⟩ := key y h
    have e : finGL V h = x.1 := Units.ext (by rw [finGL_val, hx])
    rw [e]; exact x.2
  let fin2 : GA D V → UPts (sigD D) V.gram (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := fun h => ⟨finGL V h, hmem h⟩
  have hc2 : Continuous fin2 := (continuous_finGL V).subtype_mk _
  have hO := S.U_open
  rw [continuous_iff_continuousAt]
  intro g0
  obtain ⟨⟨x0, hx0⟩, -, -⟩ := key y g0
  obtain ⟨P, -, hP⟩ := Submodule.mem_map.1 (hval x0)
  let F : GA D V → ℂ := fun g =>
    (∏ τ, ((1 : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) τ * (infM θ V rfl g τ * y.1 τ)).det ^ shiftOf lam τ) *
    MvPolynomial.eval (fun q : D.what₂.Tau × Fin V.rank × Fin V.rank =>
      ((1 : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) q.1 * (infM θ V rfl g q.1 * y.1 q.1)) q.2.1 q.2.2) P
  have hM : ∀ τ, Continuous fun g : GA D V =>
      (1 : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) τ * (infM θ V rfl g τ * y.1 τ) := fun τ =>
    continuous_const.matrix_mul ((continuous_infM θ hθ V τ).matrix_mul continuous_const)
  have hFc : Continuous F := by
    refine Continuous.mul (continuous_finset_prod _ fun τ _ => ((hM τ).matrix_det).zpow₀ _ fun g => Or.inl ?_) ?_
    · obtain ⟨-, hu, -⟩ := key y g
      rw [Pi.one_apply, one_mul, det_mul]
      exact ((hu τ).mul (y.2 τ)).ne_zero
    · exact (MvPolynomial.continuous_eval P).comp (continuous_pi fun q => (hM q.1).matrix_elem q.2.1 q.2.2)
  refine hFc.continuousAt.congr ?_
  have hN : IsOpen {g : GA D V | ((fin2 (g0⁻¹ * g) : GL (Fin V.rank) (EAf D)) ∈ S.U) ∧ pf V (g0⁻¹ * g) ∈ W} :=
    (hO.preimage (hc2.comp (continuous_const.mul continuous_id))).inter
      (hWo.preimage ((continuous_pf V).comp (continuous_const.mul continuous_id)))
  have hg0 : g0 ∈ {g : GA D V | ((fin2 (g0⁻¹ * g) : GL (Fin V.rank) (EAf D)) ∈ S.U) ∧ pf V (g0⁻¹ * g) ∈ W} := by
    refine ⟨?_, ?_⟩
    · have e : (fin2 (g0⁻¹ * g0) : GL (Fin V.rank) (EAf D)) = 1 := by
        show finGL V (g0⁻¹ * g0) = 1
        rw [inv_mul_cancel]; exact map_one _
      show (fin2 (g0⁻¹ * g0) : GL (Fin V.rank) (EAf D)) ∈ S.U
      rw [e]; exact S.U.one_mem
    · show pf V (g0⁻¹ * g0) ∈ W
      rw [inv_mul_cancel, pf_one]; exact W.one_mem
  filter_upwards [hN.mem_nhds hg0] with g hg
  obtain ⟨hU, hWg⟩ := hg
  let κ : S.U := ⟨(fin2 (g0⁻¹ * g) : GL (Fin V.rank) (EAf D)), hU⟩
  have hκ1 : S.chi κ = 1 := hW (pf V (g0⁻¹ * g)) hWg (pf_fin V _) κ (by
    show (finGL V (g0⁻¹ * g)).val = _
    rw [finGL_val, finM_pf])
  obtain ⟨⟨x, hx⟩, hu, hv⟩ := key y g
  let z : Frames (gramC V.gram (embT D)) :=
    ⟨fun τ => infM θ V rfl g τ * y.1 τ, fun τ => by rw [det_mul]; exact (hu τ).mul (y.2 τ)⟩
  have hxx : x.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) 1 * x0.1 * κ.1 := by
    apply Units.ext
    simp only [Units.val_mul, map_one, Units.val_one, Matrix.one_mul]
    have e : g = g0 * (g0⁻¹ * g) := by rw [mul_inv_cancel_left]
    rw [hx, e, finM_mul, ← hx0]
    exact congrArg _ (finGL_val V _).symm
  have h1 : IsTr (atInf (embT D) (1 : GL (Fin V.rank) D.host.E).val) z z := fun τ => by
    show z.1 τ = atInf (embT D) (1 : GL (Fin V.rank) D.host.E).val τ * z.1 τ
    simp [atInf]
  have e3 := hΨ 1 (Subgroup.one_mem _) x0 x κ hxx z z h1
  rw [hκ1, Units.val_one, one_mul] at e3
  rw [hv x z hx (fun τ => rfl), e3, ← hP]
  rfl

end GlobalTheory.AdForm.RdLaw

noncomputable section
namespace GlobalTheory.AdForm.RdLaw

theorem rdS_laws : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (hn : V.rank = n) (J : Matrix (Fin n) (Fin n) D.host.E), J = V.gram.reindex (finCongr hn) (finCongr hn) → ∀ (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 D.host.F))) (S : StepLevel D.host.F D.host.E (sigD D) J T f bad) (cl : Type) (yc : cl → UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S)) → ∀ lam, ∀ φ ∈ FiC S (embT D) lam yc, ∀ y : Frames (gramC J (embT D)), (∀ γ ∈ GQ V, ∀ g, rdS θ V hn S yc φ y (γ * g) = rdS θ V hn S yc φ y g) ∧ (∀ k ∈ GfC V, ∀ κ : S.U, κ.1.1 = finM V hn k → ∀ g, rdS θ V hn S yc φ y (g * k) = (S.chi κ : ℂ) * rdS θ V hn S yc φ y g) ∧ (∀ k ∈ GinfC V, ∀ y', IsTr (infM θ V hn k) y y' → ∀ g, rdS θ V hn S yc φ y (g * k) = rdS θ V hn S yc φ y' g) ∧ ((∃ W : Subgroup (GA D V), IsOpen (W : Set (GA D V)) ∧ ∀ k ∈ W, k ∈ GfC V → ∀ κ : S.U, κ.1.1 = finM V hn k → S.chi κ = 1) → Continuous (rdS θ V hn S yc φ y)) := by
  intro D θ hθ V n hn J hJ T f bad S cl yc hb lam φ hφ y
  subst hn
  simp only [finCongr_refl, reindex_refl_refl] at hJ
  subst hJ
  obtain ⟨Ψ, hΨ, rfl⟩ := Submodule.mem_map.1 hφ
  have hA : Ψ ∈ AdFun S (embT D) := (Submodule.mem_inf.1 hΨ).1
  have hval : ∀ x, Ψ x ∈ ValC (gramC V.gram (embT D)) lam := fun x =>
    (Submodule.mem_pi.1 (Submodule.mem_inf.1 hΨ).2) x (Set.mem_univ _)
  exact ⟨law_left θ hθ V T f bad S cl yc hb Ψ hA y, law_level θ hθ V T f bad S cl yc hb Ψ hA y,
    law_real θ hθ V T f bad S cl yc hb Ψ hA y, law_cont θ hθ V T f bad S cl yc hb Ψ hA lam hval y⟩

end GlobalTheory.AdForm.RdLaw
