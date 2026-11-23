import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameDescentCharactersEqAndFrobeniusStableStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KisinInfGaloisActsThroughDescentDatumStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBcrisComparisonFrobeniusNaturalityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisEqMulKisinInfTameSemidirectStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBcrisTensorLatticeEquivPeriodRingStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinSectionTrivialisesInvertPrimeTensorStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbeddingProductSeriesToTensorBcrisInjectiveFinEStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

namespace GlobalTheory.CharsDesc

theorem toBcris_inj {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
    {ι : Type} [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (hB : Function.Injective (ϖ.iB t K)) :
    Function.Injective (toBcris t ϖ P) := by
  intro m m' h
  have hc : coordL P (invL l (S O K e)) m = coordL P (invL l (S O K e)) m' := by
    funext i
    apply hB
    have := congrFun h i
    rwa [toBcris_apply, toBcris_apply] at this
  apply Subtype.ext
  funext τ
  rw [← mx_mulVec_coordL P _ m τ, ← mx_mulVec_coordL P _ m' τ, hc]

theorem xi_mem_MMl {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [Algebra O K] [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι) (d : P.D) :
    P.xi d ∈ P.MMl := by
  refine ((GlobalTheory.T.breuilKisin_section_trivialises_invertPrime_tensor O K l e a ι P).2 (cst d)).2 ?_
  refine mem_tot.2 fun τ i => ?_
  obtain ⟨n, b, hb⟩ := exists_pow_mul_mem (O := O) l (d τ i)
  refine ⟨n, ?_⟩
  have h1 : (((l : S O K e) : K⟦X⟧)) ^ n * cst d τ i = algebraMap O K⟦X⟧ b := by
    rw [IsScalarTower.algebraMap_apply O K K⟦X⟧, ← hb]
    simp [cst, PowerSeries.algebraMap_apply]
  rw [h1]
  exact Subalgebra.algebraMap_mem _ b

theorem actD_single {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero a] [TameDescentExponentData K l e a] {P : PhiMod O K l e a ι} (Δ : Descent P)
    (ζ : rootsOfUnity e K) (d : P.D) (τ : ZMod a) :
    Δ.actD (TameGal.inertia ζ) (Pi.single τ (d τ) : P.D) = Pi.single τ (Δ.actD (TameGal.inertia ζ) d τ) := by
  classical
  have hf : ringAct (TameGal.inertia ζ : TameGal K l e a) (Pi.single τ 1) = Pi.single τ 1 := by
    funext σ
    rw [ringAct_apply, TameGal.shift_inertia, sub_zero]
    by_cases h : σ = τ
    · subst h; simp
    · simp [h]
  have hc : cst (Pi.single τ (d τ) : P.D) = (Pi.single τ 1 : ZMod a → K⟦X⟧) • cst d := by
    funext σ i
    by_cases h : σ = τ
    · subst h; simp [cst]
    · simp [cst, h]
  have hr : ∀ w : Vec K a ι, red ((Pi.single τ 1 : ZMod a → K⟦X⟧) • w) = Pi.single τ (red w τ) := by
    intro w
    funext σ i
    by_cases h : σ = τ
    · subst h; simp [red, red0]
    · simp [red, red0, h]
  change red (Δ.act _ (cst _)) = _
  rw [hc, Δ.act_smul_tot, hf, hr]
  rfl

theorem jB_smul {l : ℕ} [Fact l.Prime] {LL : FinExt l} {T : QLat LL} {ι : Type} [Fintype ι]
    (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (o : ↥(OL LL))
    (v : ι → OB l ↥(OL LL)) : jB (o • v) = o • jB v := by
  rw [← algebraMap_smul (OB l ↥(OL LL)) o v, map_smul, algebraMap_smul]

theorem smul_eq_algebraMap_smul {l : ℕ} [Fact l.Prime] {LL : FinExt l} (T : QLat LL) (Pl : LocPrime l)
    (o : ↥(OL LL)) (x : T.V ⊗[ℚ_[l]] Pl.R.B) : o • x = (algebraMap ↥(OL LL) ↥LL.1 o) • x :=
  (algebraMap_smul (↥LL.1) o x).symm

theorem mem_Dcris_res {l : ℕ} [Fact l.Prime] {LL : FinExt l} (T : QLat LL) (Pl : LocPrime l) (F : FinExt l)
    (x : (resF T F).V ⊗[ℚ_[l]] Pl.R.B)
    (h : ∀ g : ↥(GK F), actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ (inclG F g) (x : T.V ⊗[ℚ_[l]] Pl.R.B) = x) :
    x ∈ Dcris (Pl.PD F) (resF T F).ρ := by
  refine (Submodule.mem_iInf _).2 fun g => LinearMap.mem_ker.2 (sub_eq_zero.2 ?_)
  have key : actVB (Pl.PD F) (resF T F).ρ g = actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ (inclG F g) := by
    unfold actVB
    congr 1
    ext b
    exact (Pl.PD_actB F g b).trans (Pl.PD_actB _ (inclG F g) b).symm
  exact (LinearMap.congr_fun key x).trans (h g)

end GlobalTheory.CharsDesc

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
open GlobalTheory.CharsDesc in

theorem GlobalTheory.CharsDesc.chars_subset_sig : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Δ : Descent P) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → IsGalDesc (sQ l) I Δ → ∀ Sig : Finset (ZMod e), TameType a ϖ Pl T Sig → ∀ τ, Δ.chars τ ⊆ (Sig : Set (ZMod e)) := by
  intro l _ a e _ _ ϖ LL _ _ _ ι _ _ P T I jB Δ Pl AI hStd hCmp hHor hDesc Sig hType τ c hc
  have hc0 : c ∈ Δ.chars 0 := by
    rw [← (GlobalTheory.T.tameDescent_characters_eq_and_frobenius_stable _ _ l e a ι P Δ).1 τ 0]; exact hc
  obtain ⟨d, hd0, hdc⟩ := hc0

  obtain ⟨ζ, hζ⟩ := TameDescentExponentData.prim (K := ↥LL.1) (l := l) (e := e) (a := a)
  obtain ⟨ζu, hζu⟩ : ∃ ζu : rootsOfUnity e ↥LL.1, (((ζu : (↥LL.1)ˣ) : ↥LL.1)) = ζ := ⟨hζ.toRootsOfUnity, rfl⟩
  have I8 := GlobalTheory.T.galois_eq_mul_kisinInf_tameSemidirect l a e ϖ LL
  obtain ⟨k, -, hkc⟩ := I8.2.2.1 (TameGal.inertia ζu)
  obtain ⟨k', hk'I, hk'c, hk'π⟩ := I8.2.2.2.2.2.2 k ζu hkc
  classical
  obtain ⟨d', hd'_def⟩ : ∃ d' : P.D, d' = Pi.single 0 (d 0) := ⟨_, rfl⟩
  have hd'0 : d' ≠ 0 := by
    intro h; apply hd0; have := congrFun h 0; rw [hd'_def, Pi.single_eq_same] at this; exact this
  have hact' : Δ.actD (TameGal.inertia ζu) d' = (ζ ^ c.val) • d' := by
    rw [hd'_def, actD_single, hdc ζu, TameGal.root_inertia_zero, hζu, Pi.single_smul]
  have hm := xi_mem_MMl P d'
  obtain ⟨σ, hσ_def⟩ : ∃ σ : P.MMl, σ = ⟨P.xi d', hm⟩ := ⟨_, rfl⟩
  have hnorm : ‖ζ ^ c.val‖ ≤ 1 := by
    have h1 : ‖ζ‖ = 1 := by
      have h := congrArg norm hζ.pow_eq_one
      rw [norm_pow, norm_one] at h
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (NeZero.ne e)).1 h
    rw [norm_pow, h1, one_pow]
  obtain ⟨o, ho⟩ := (IsUnitBall.mem_range_iff (O := ↥(OL LL)) (ζ ^ c.val)).2 hnorm
  have hσ' : (o • σ).1 = Δ.act (TameGal.inertia ζu) σ.1 := by
    rw [hσ_def, Descent.act_xi, hact', map_smul, Submodule.coe_smul_of_tower, ← ho, algebraMap_smul]
  have hA := GlobalTheory.T.kisinInfGalois_acts_through_descentDatum l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P T I jB Δ hCmp hDesc k'
    (TameGal.inertia ζu) hk'c σ (o • σ) hσ'
  obtain ⟨β, -, hβ2, -, -⟩ := GlobalTheory.T.exists_bcrisTensorLattice_equiv_periodRing l LL T Pl AI hStd
  obtain ⟨x, hx_def⟩ : ∃ x, x = β (jB (toBcris (thetaW a LL) ϖ P σ)) := ⟨_, rfl⟩
  have hx0 : x ≠ 0 := by
    intro h
    rw [hx_def, LinearEquiv.map_eq_zero_iff, LinearEquiv.map_eq_zero_iff] at h
    have h2 : σ = 0 := toBcris_inj (thetaW a LL) ϖ P (GlobalTheory.T.embeddingProductSeriesToTensorBcris_injective_finExt l a e LL (thetaW a LL) ϖ)
      (h.trans (map_zero _).symm)
    apply hd'0
    have h3 : P.xi d' = 0 := by rw [hσ_def] at h2; exact congrArg Subtype.val h2
    have h4 := congrArg red h3
    rwa [PhiMod.red_xi, map_zero] at h4
  have hxD : x ∈ Dcris (Pl.PD (ϖ.field a)) (resF T (ϖ.field a)).ρ := by
    refine mem_Dcris_res T Pl (ϖ.field a) x fun g => ?_
    have e := hβ2 (inclG (ϖ.field a) g) (jB (toBcris (thetaW a LL) ϖ P σ))
    have e' : actB (sQ l) T (inclG (ϖ.field a) g) (jB (toBcris (thetaW a LL) ϖ P σ)) =
        jB (toBcris (thetaW a LL) ϖ P σ) := by
      subst hσ_def; exact hHor (inclG (ϖ.field a) g) g.2 d' hm
    rw [e'] at e
    subst hx_def; exact e.symm
  have hA' : actB (sQ l) T k' (jB (toBcris (thetaW a LL) ϖ P σ)) =
      jB (toBcris (thetaW a LL) ϖ P (o • σ)) := hA
  have hact : (actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ k' : Module.End ↥LL.1 (T.V ⊗[ℚ_[l]] Pl.R.B)) x =
      (ζ ^ c.val) • x := by
    have e1 := (hβ2 k' (jB (toBcris (thetaW a LL) ϖ P σ))).symm
    have e6 := congrArg β hA'
    have e2 : toBcris (thetaW a LL) ϖ P (o • σ) = o • toBcris (thetaW a LL) ϖ P σ := map_smul _ _ _
    have e3 : jB (o • toBcris (thetaW a LL) ϖ P σ) = o • jB (toBcris (thetaW a LL) ϖ P σ) :=
      jB_smul jB o _
    have e4 : β (jB (toBcris (thetaW a LL) ϖ P (o • σ))) = o • β (jB (toBcris (thetaW a LL) ϖ P σ)) :=
      (congrArg (fun v => β (jB v)) e2).trans ((congrArg β e3).trans (β.map_smul o _))
    subst hx_def
    refine e1.trans (e6.trans (e4.trans ?_))
    exact (smul_eq_algebraMap_smul T Pl o _).trans
      (congrArg (fun s : ↥LL.1 => s • β (jB (toBcris (thetaW a LL) ϖ P σ))) ho)
  have hk'π' : ((ζ : ↥LL.1) : Om l) * ϖ.seq 0 = (k' : GQ l) (ϖ.seq 0) := by rw [← hζu]; exact hk'π
  have hT := hType k' hk'I ζ hk'π' x hxD
  have hev : Module.End.HasEigenvector
      (actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ k' : Module.End ↥LL.1 (T.V ⊗[ℚ_[l]] Pl.R.B)) (ζ ^ c.val) x :=
    Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 hact, hx0⟩
  rw [Module.End.aeval_apply_of_hasEigenvector hev, smul_eq_zero] at hT
  rcases hT with hT | hT
  · rw [Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hT
    obtain ⟨c', hc', hcc⟩ := hT
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hcc
    have := hζ.pow_inj (ZMod.val_lt c) (ZMod.val_lt c') hcc
    rw [ZMod.val_injective e this]
    exact hc'
  · exact absurd hT hx0
