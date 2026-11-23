import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemFormsOnOfMemSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicConstantTermParabolic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviDecompositionGradedIsotropicFlagStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousIteratedRealLineDerivUnitaryAdelicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealOneParamProductChartAdelicUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousIteratedFDerivRealOneParamProductLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffConstantTermCocompactSmoothParameterFamiStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.ConstMod

section General

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open GlobalTheory.AutomorphicL2Unitary (LeftInv)
open GlobalTheory.Cusp (Cocompact constTermOn)
open GlobalTheory.UAut.ConstAut
open GlobalTheory.ThK.SmoothLev (IsSmModOn)
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem isSmModOn_constTermOn (h : IsCMExt F E σ) (hJ : IsHermND σ J) {r : ℕ} {C : Matrix (Fin n) (Fin r) E}
    (d : Fin r → ℕ) (hC : IsIsoCols σ J C) {Γ : Set (GAd σ J)} {φ c : GAd σ J → ℂ}
    (hΓ : ((ratPts σ J ⊓ parFlag σ J C d : Subgroup (GAd σ J)) : Set (GAd σ J)) ⊆ Γ)
    (hφ : IsSmModOn σ J Γ φ) (hc : IsConstTermOn σ J (unipFlag σ J C d) φ c) :
    IsSmModOn σ J (leftGrp σ J C d : Set (GAd σ J)) c ∧ ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      IsConstTermOn σ J (unipFlag σ J C d) (l.foldr lineDer φ) (l.foldr lineDer c) := by
  classical
  haveI := locallyCompact_unipFlag hJ (sigma_sigma h) hC d
  have hs : IsSm σ J φ := hφ.smooth
  have hφΓ : LeftInv (ratPts σ J ⊓ parFlag σ J C d) φ := fun γ hγ => hφ.left γ (hΓ hγ)
  obtain ⟨hco, e⟩ := hc.eq_constTermOn_par h hJ hC hφΓ
  have hcont : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → Continuous (l.foldr lineDer φ) :=
    GlobalTheory.T.continuous_iteratedRealLineDeriv_unitaryAdelic F E σ h n J hJ φ hφ.level hφ.cont hs
  have hleft : ∀ l : List (ℝ → GAd σ J), LeftInv (ratPts σ J ⊓ parFlag σ J C d) (l.foldr lineDer φ) :=
    leftInv_foldr hφΓ
  have hder : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      l.foldr lineDer c = constTermOn (ratPts σ J ⊓ parFlag σ J C d) (unipFlag σ J C d) (l.foldr lineDer φ) := by
    intro l
    induction l with
    | nil => intro _; exact e
    | cons γ l ih =>
      intro hl
      have hl' : ∀ γ' ∈ l, IsRealLine σ J γ' := fun γ' h' => hl γ' (List.mem_cons_of_mem _ h')
      have hγ : IsRealLine σ J γ := hl γ List.mem_cons_self
      funext x
      have hx := GlobalTheory.CuspLie.hasDerivAt_constTermOn hco (hleft l) (hcont l hl') (hleft (γ :: l)) (hcont (γ :: l) hl)
        (GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ h n J γ hγ) (hasDerivAt_foldr h hs hl' hγ) x
      rw [realLine_zero h hγ, mul_one] at hx
      rw [List.foldr_cons, ih hl']
      exact hx.deriv
  have hct : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      IsConstTermOn σ J (unipFlag σ J C d) (l.foldr lineDer φ) (l.foldr lineDer c) := by
    intro l hl
    obtain ⟨c', hc', -⟩ := existsUnique_isConstTermOn h hJ hC d (φ := l.foldr lineDer φ)
      fun γ hγ => hleft l γ ⟨hγ.1, unipFlag_le_parFlag hJ (sigma_sigma h) hC d hγ.2⟩
    rwa [hder l hl, ← (hc'.eq_constTermOn_par h hJ hC (hleft l)).2]
  have hlevel : ∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧
      ∀ k ∈ U, k ∈ finPts σ J → ∀ g, c (g * k) = c g := by
    obtain ⟨U, hU, hUk⟩ := hφ.level
    refine ⟨U, hU, fun k hk hf g => ?_⟩
    rw [e, ← GlobalTheory.Cusp.constTermOn_mul_right]
    exact congrArg (fun f => constTermOn _ _ f g) (funext fun y => hUk k hk hf y)
  have hsm : IsSm σ J c := by
    obtain ⟨dd, δ, hδ, hW⟩ := GlobalTheory.T.exists_realOneParamProduct_chart_adelicUnitary F E σ h n J hJ
    intro k γ hγ g
    have := GlobalTheory.T.contDiff_constantTermCocompact_smoothParameterFamily hco (fun x t => φ (x * (List.ofFn fun i => γ i (t i)).prod))
      (fun γ' hγ' x t => by simp only [mul_assoc]; exact hφΓ γ' hγ' _) (fun x => hs k γ hγ x)
      (GlobalTheory.T.continuous_iteratedFDeriv_realOneParamProduct_levelFunction F E σ h n J hJ dd δ hδ hW φ hφ.level hs k γ hγ) g
    simpa [e, GlobalTheory.Cusp.constTermOn_mul_right] using this
  have hgrowth : ∃ M : ℕ, ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      ∃ B : ℝ, ∀ g, ‖l.foldr lineDer c g‖ ≤ B * (height σ J g : ℝ) ^ M := by
    obtain ⟨M, hM⟩ := hφ.growth
    obtain ⟨K0, hK0, hs'⟩ := id hco
    haveI := hco.isProbabilityMeasure
    obtain ⟨A, hA⟩ := (hK0.image continuous_subtype_val).exists_bound_of_continuousOn
      (f := fun x => (height σ J x : ℝ)) (NNReal.continuous_coe.comp (continuous_height_GAd σ J)).continuousOn
    refine ⟨M, fun l hl => ?_⟩
    obtain ⟨B, hB⟩ := hM l hl
    refine ⟨max B 0 * max A 0 ^ M, fun g => ?_⟩
    have h1 : ∀ x : unipFlag σ J C d, ‖l.foldr lineDer φ ((x : GAd σ J) * g)‖ ≤
        max B 0 * (max A 0 * (height σ J g : ℝ)) ^ M := by
      intro x
      obtain ⟨γ, hγ, hk⟩ := hs' x
      have e1 : l.foldr lineDer φ ((x : GAd σ J) * g) =
          l.foldr lineDer φ (((γ * x : unipFlag σ J C d) : GAd σ J) * g) := by
        rw [Subgroup.coe_mul, mul_assoc]; exact (hleft l _ hγ _).symm
      have e2 : (height σ J ((γ * x : unipFlag σ J C d) : GAd σ J) : ℝ) ≤ max A 0 := by
        have := hA _ ⟨_, hk, rfl⟩
        rw [Real.norm_eq_abs] at this
        exact (le_abs_self _).trans (this.trans (le_max_left _ _))
      have e3 : (height σ J (((γ * x : unipFlag σ J C d) : GAd σ J) * g) : ℝ) ≤ max A 0 * height σ J g :=
        calc (height σ J (((γ * x : unipFlag σ J C d) : GAd σ J) * g) : ℝ)
            ≤ height σ J ((γ * x : unipFlag σ J C d) : GAd σ J) * height σ J g := by
              exact_mod_cast height_mul_le σ J _ _
          _ ≤ max A 0 * height σ J g := mul_le_mul_of_nonneg_right e2 (NNReal.coe_nonneg _)
      rw [e1]
      calc _ ≤ B * (height σ J (((γ * x : unipFlag σ J C d) : GAd σ J) * g) : ℝ) ^ M := hB _
        _ ≤ max B 0 * (height σ J (((γ * x : unipFlag σ J C d) : GAd σ J) * g) : ℝ) ^ M :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (NNReal.coe_nonneg _) _)
        _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) e3 _) (le_max_right _ _)
    rw [hder l hl]
    refine (norm_integral_le_of_norm_le_const (μ := GlobalTheory.Cusp.probMeasure _ _) (.of_forall fun q => h1 q.out)).trans
      (le_of_eq ?_)
    simp [mul_pow, mul_assoc]
  exact ⟨⟨hc.leftInv h hJ hC hφΓ, hlevel, hc.continuous h hJ hC hφΓ hφ.cont, hsm, hgrowth⟩, hct⟩

theorem depth_lt {r t : ℕ} (ht : t ≤ r) {T : Finset (Fin r)} {i j : Fin t} {k : Fin r} (hk : k ∈ T)
    (h1 : j.val ≤ k.val) (h2 : k.val < i.val) :
    (T.filter (· < Fin.castLE ht j)).card < (T.filter (· < Fin.castLE ht i)).card := by
  refine Finset.card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter, Fin.lt_def, Fin.val_castLE] at hx ⊢
    exact ⟨hx.1, by omega⟩
  · have h3 := hsub (Finset.mem_filter.2 ⟨hk, Fin.lt_def.2 (by simpa using h2)⟩)
    have h4 := Fin.lt_def.1 (Finset.mem_filter.1 h3).2
    simp only [Fin.val_castLE] at h4
    omega

theorem exists_block_of_subset {r s t : ℕ} (X : Matrix (Fin n) (Fin r) E) {S T : Finset (Fin r)} (hST : S ⊆ T)
    (hs : s ≤ r) (ht : t ≤ r) (hst : s ≤ t) (hS : ∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k)
    {M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)} {B : Matrix (Fin t) (Fin t) (AF F ⊗[F] E)}
    (hB : B.BlockTriangular fun i : Fin t => (T.filter (· < Fin.castLE ht i)).card)
    (e : M * adMat F (X.submatrix id (Fin.castLE ht)) = adMat F (X.submatrix id (Fin.castLE ht)) * B) :
    ∃ B' : Matrix (Fin s) (Fin s) (AF F ⊗[F] E),
      (B'.BlockTriangular fun i : Fin s => (S.filter (· < Fin.castLE hs i)).card) ∧
      M * adMat F (X.submatrix id (Fin.castLE hs)) = adMat F (X.submatrix id (Fin.castLE hs)) * B' := by
  refine ⟨B.submatrix (Fin.castLE hst) (Fin.castLE hst), fun i j hij => ?_, Matrix.ext fun x j => ?_⟩
  · obtain ⟨k, hk, hk'⟩ := Finset.exists_mem_notMem_of_card_lt_card hij
    have hk1 := Finset.mem_filter.1 hk
    have h2 : k.val < i.val := by simpa [Fin.lt_def] using hk1.2
    have h1 : j.val ≤ k.val := by
      by_contra hc
      exact hk' (Finset.mem_filter.2 ⟨hk1.1, Fin.lt_def.2 (by simpa using not_le.1 hc)⟩)
    exact hB (depth_lt ht (hST hk1.1) (i := Fin.castLE hst i) (j := Fin.castLE hst j) (by simpa using h1) (by simpa using h2))
  · have e1 := congrFun (congrFun e x) (Fin.castLE hst j)
    have l1 : (M * adMat F (X.submatrix id (Fin.castLE hs))) x j =
        (M * adMat F (X.submatrix id (Fin.castLE ht))) x (Fin.castLE hst j) := rfl
    rw [l1, e1, Matrix.mul_apply, Matrix.mul_apply]
    symm
    refine Fintype.sum_of_injective (Fin.castLE hst) (Fin.castLE_injective hst) _ _ (fun i hi => ?_) fun i => rfl
    have hi' : s ≤ i.val := by
      by_contra hc
      exact hi ⟨⟨i.val, not_le.1 hc⟩, rfl⟩
    obtain ⟨k, hk, hjk⟩ := (hS (Fin.castLE hs j)).1 (by simp)
    have hks : k.val < s := (hS k).2 ⟨k, hk, le_rfl⟩
    have hz : B i (Fin.castLE hst j) = 0 :=
      hB (depth_lt ht (hST hk) (by simpa [Fin.le_def] using hjk) (by omega))
    rw [hz, mul_zero]

theorem parFlag_le_of_subset {r s t : ℕ} (X : Matrix (Fin n) (Fin r) E) {S T : Finset (Fin r)} (hST : S ⊆ T)
    (hs : s ≤ r) (ht : t ≤ r) (hst : s ≤ t) (hS : ∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k) :
    parFlag σ J (X.submatrix id (Fin.castLE ht)) (fun i : Fin t => (T.filter (· < Fin.castLE ht i)).card) ≤
      parFlag σ J (X.submatrix id (Fin.castLE hs)) (fun i : Fin s => (S.filter (· < Fin.castLE hs i)).card) :=
  fun _ ⟨⟨B, hB, e⟩, B', hB', e'⟩ =>
    ⟨exists_block_of_subset X hST hs ht hst hS hB e, exists_block_of_subset X hST hs ht hst hS hB' e'⟩

def top {r : ℕ} (S : Finset (Fin r)) : ℕ := S.sup fun k => k.val + 1

theorem top_le {r : ℕ} (S : Finset (Fin r)) : top S ≤ r := Finset.sup_le fun k _ => k.2

theorem top_mono {r : ℕ} {S T : Finset (Fin r)} (h : S ⊆ T) : top S ≤ top T := Finset.sup_mono h

theorem lt_top_iff {r : ℕ} (S : Finset (Fin r)) (i : Fin r) : i.val < top S ↔ ∃ k ∈ S, i ≤ k := by
  rw [top, Finset.lt_sup_iff]
  exact exists_congr fun k => and_congr_right fun _ => by rw [Fin.le_def]; omega

theorem leftGrp_eq (h : IsCMExt F E σ) (hJ : IsHermND σ J) {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}
    (hW : IsWittFrame σ J X Y) (S : Finset (Fin r)) :
    leftGrp σ J (X.submatrix id (Fin.castLE (top_le S)))
        (fun i : Fin (top S) => (S.filter (· < Fin.castLE (top_le S) i)).card) =
      GlobalTheory.StdPar.unip σ J X S ⊔ (ratPts σ J ⊓ GlobalTheory.StdPar.levi σ J X Y S) := by
  obtain ⟨hu, hl, -⟩ := GlobalTheory.TieStd.stdPar_eq_flag F E σ h n J hJ r X Y hW S (top S) (top_le S) (lt_top_iff S)
    (fun i : Fin (top S) => (S.filter (· < Fin.castLE (top_le S) i)).card) fun _ => rfl
  have hg := (GlobalTheory.T.leviDecomposition_gradedIsotropicFlag F E σ h n J hJ (top S) (X.submatrix id (Fin.castLE (top_le S)))
    (Y.submatrix id (Fin.castLE (top_le S))) (fun i : Fin (top S) => (S.filter (· < Fin.castLE (top_le S) i)).card)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xx]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.yy]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xy]; exact Matrix.submatrix_one _ (Fin.castLE_injective _))).2.2.1
  rw [hg, hu, hl]

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin

theorem isSmModOn_constAlong : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ S T : Finset (Fin m), S ⊆ T → T.Nonempty → ∀ φ c : GA D V → ℂ, IsSmModOn D.sp.cm.sig V.gram (leftSub V X Y S : Set (GA D V)) φ → IsConstAlong D.sp.cm.sig V.gram X T φ c → IsSmModOn D.sp.cm.sig V.gram (leftSub V X Y T : Set (GA D V)) c ∧ ∀ l : List (ℝ → GA D V), (∀ γ ∈ l, GlobalTheory.SiegelSet.IsRealLine D.sp.cm.sig V.gram γ) → IsConstAlong D.sp.cm.sig V.gram X T (l.foldr GlobalTheory.SiegelSet.lineDer φ) (l.foldr GlobalTheory.SiegelSet.lineDer c) := by
  intro D V m X Y hW S T hST _ φ c hφ hc
  obtain ⟨h, hJ'⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have hJ := hJ' V
  obtain ⟨hu, -, -⟩ := GlobalTheory.TieStd.stdPar_eq_flag _ _ D.sp.cm.sig h _ V.gram hJ m X Y hW T (top T) (top_le T) (lt_top_iff T)
    (fun i : Fin (top T) => (T.filter (· < Fin.castLE (top_le T) i)).card) fun _ => rfl
  have hC := GlobalTheory.UAut.isIsoCols_of_isWittFrame hW (GlobalTheory.SiegelSet.sigma_sigma h) hJ (top_le T)
  have hc' : GlobalTheory.UAut.IsConstTermOn D.sp.cm.sig V.gram (GlobalTheory.UAut.unipFlag D.sp.cm.sig V.gram (X.submatrix id (Fin.castLE (top_le T)))
      (fun i : Fin (top T) => (T.filter (· < Fin.castLE (top_le T) i)).card)) φ c := hu ▸ hc
  have hΓ : ((GlobalTheory.AdelicU.ratPts D.sp.cm.sig V.gram ⊓ GlobalTheory.UAut.parFlag D.sp.cm.sig V.gram (X.submatrix id (Fin.castLE (top_le T)))
      (fun i : Fin (top T) => (T.filter (· < Fin.castLE (top_le T) i)).card) : Subgroup (GA D V)) : Set (GA D V)) ⊆
      (leftSub V X Y S : Set (GA D V)) := by
    intro p hp
    have e := leftGrp_eq h hJ hW S
    have : p ∈ GlobalTheory.UAut.leftGrp D.sp.cm.sig V.gram (X.submatrix id (Fin.castLE (top_le S)))
        (fun i : Fin (top S) => (S.filter (· < Fin.castLE (top_le S) i)).card) :=
      Subgroup.mem_sup_right ⟨hp.1, parFlag_le_of_subset X hST (top_le S) (top_le T) (top_mono hST) (lt_top_iff S) hp.2⟩
    rw [e] at this
    exact this
  obtain ⟨r1, r2⟩ := isSmModOn_constTermOn h hJ _ hC hΓ hφ hc'
  refine ⟨?_, fun l hl => ?_⟩
  · have e : (leftSub V X Y T : Subgroup (GA D V)) = GlobalTheory.UAut.leftGrp D.sp.cm.sig V.gram (X.submatrix id (Fin.castLE (top_le T)))
        (fun i : Fin (top T) => (T.filter (· < Fin.castLE (top_le T) i)).card) := (leftGrp_eq h hJ hW T).symm
    rw [e]
    exact r1
  · have := r2 l hl
    rw [← hu] at this
    exact this

end GlobalTheory.CompanionTheory.Hypotheses₂.ConstMod

end
