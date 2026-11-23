import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepBeforeLastEqSSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleFreeLevelLeCompact
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnKernelDataCompatibleStepCharts
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdAtKStdOfTwist
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPrimeRationalCosetSameOrbitIffLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReduction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceProjectionEqOfPrimeComponentEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSwapR
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistLocalData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BcPrVMemLevelVLOfMoves

noncomputable section

section LocalPart
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
open GlobalTheory.SymBridge (toLoc IsOrd yPos xPos IsCompl)
open GlobalTheory.PenVol GlobalTheory.TwBridge.Lev GlobalTheory.TwBridge.LevOrb
open scoped TensorProduct

namespace GlobalTheory.PenLoc

section Stab
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A : Type} [Fintype A] [DecidableEq A]
  {J : Subgroup (GL (A ⊕ Fin 0) k)}

theorem box_iff {g : GL (A ⊕ Fin 0) k} (hg : g ∈ KO k _) (c : kˣ) (y : A → k) :
    g.val.toBlocks₁₁ *ᵥ y ∈ box A c ↔ y ∈ box A c := by
  refine ⟨fun h => ?_, mulVec_mem_box hg c⟩
  have := mulVec_mem_box (inv_mem hg) c h
  rwa [Matrix.mulVec_mulVec, ← toBlocks_mul_fin_zero, show (g⁻¹).val * g.val = 1 from g.inv_mul, toBlocks_one_fin_zero,
    Matrix.one_mulVec] at this

theorem mem_stab_iff (hJ : J ≤ KO k _) (c : kˣ) (y : A → k) (g : GL (A ⊕ Fin 0) k) :
    g ∈ cosStab J (box A c) (Submodule.Quotient.mk y) ↔ g ∈ J ∧ g.val.toBlocks₁₁ *ᵥ y - y ∈ box A c := by
  rw [mem_cosStab]
  refine and_congr_right fun hg => ⟨fun h => (Submodule.Quotient.eq _).1 ((h y).2 rfl), fun h z => ?_⟩
  rw [Submodule.Quotient.eq, Submodule.Quotient.eq, ← box_iff (hJ hg) c (z - y), Matrix.mulVec_sub]
  have e : g.val.toBlocks₁₁ *ᵥ z - y = (g.val.toBlocks₁₁ *ᵥ z - g.val.toBlocks₁₁ *ᵥ y) + (g.val.toBlocks₁₁ *ᵥ y - y) := by abel
  rw [e]
  exact Submodule.add_mem_iff_left _ h

theorem conj_iff (hJ : J ≤ KO k _) (c : kˣ) (y : A → k) {K : GL (A ⊕ Fin 0) k} (hK : K ∈ J) (x : GL (A ⊕ Fin 0) k) :
    K⁻¹ * x * K ∈ cosStab J (box A c) (Submodule.Quotient.mk y) ↔
      x ∈ cosStab J (box A c) (Submodule.Quotient.mk (K.val.toBlocks₁₁ *ᵥ y)) := by
  rw [mem_stab_iff hJ, mem_stab_iff hJ]
  have h1 : K⁻¹ * x * K ∈ J ↔ x ∈ J := by rw [J.mul_mem_cancel_right hK, J.mul_mem_cancel_left (inv_mem hK)]
  rw [h1, ← box_iff (hJ hK) c (_ - y)]
  refine and_congr_right fun _ => ?_
  have e : K.val.toBlocks₁₁ *ᵥ ((K⁻¹ * x * K).val.toBlocks₁₁ *ᵥ y - y) =
      x.val.toBlocks₁₁ *ᵥ (K.val.toBlocks₁₁ *ᵥ y) - K.val.toBlocks₁₁ *ᵥ y := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← toBlocks_mul_fin_zero, ← toBlocks_mul_fin_zero, ← Units.val_mul,
      ← Units.val_mul, show K * (K⁻¹ * x * K) = x * K by group]
  rw [e]

theorem deep_mem (h1 : KOne k _ ≤ J) (hJ : J ≤ KO k _) {ϖ : kˣ} (hϖ : valuation k (ϖ : k) < 1) {M D : ℕ} (hD : 1 ≤ D)
    (hM : 2 * M ≤ D) {y : A → k} (hy : y ∈ box A (ϖ ^ M)⁻¹) {u : GL (A ⊕ Fin 0) k}
    (hu : ∀ a b, valuation k ((u.val - 1) a b) ≤ valuation k (ϖ : k) ^ D) :
    u ∈ cosStab J (box A (ϖ ^ M)) (Submodule.Quotient.mk y) := by
  rw [mem_stab_iff hJ]
  refine ⟨h1 (mem_KOne.2 fun a b => (hu a b).trans_lt (pow_lt_one₀ zero_le' hϖ (by omega))), fun a => ?_⟩
  have e : (u.val.toBlocks₁₁ *ᵥ y - y) a = ∑ b, (u.val - 1) (Sum.inl a) (Sum.inl b) * y b := by
    simp [Matrix.mulVec, dotProduct, Matrix.toBlocks₁₁, _root_.sub_mul, Finset.sum_sub_distrib, Matrix.one_apply]
  rw [e]
  refine Valuation.map_sum_le _ fun b _ => ?_
  rw [map_mul]
  refine (mul_le_mul' (hu _ _) (hy b)).trans ?_
  obtain ⟨d, rfl⟩ : ∃ d, D = d + M + M := ⟨D - 2 * M, by omega⟩
  simp only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀, map_pow, pow_add]
  have h0 : valuation k (ϖ : k) ^ M ≠ 0 := pow_ne_zero _ (by simp)
  rw [mul_inv_cancel_right₀ h0]
  exact mul_le_of_le_one_left' (pow_le_one' hϖ.le d)

end Stab

section Read
variable {k : Type} [Field k] {R : Type} [CommRing R] {Y : Type} [Fintype Y] [DecidableEq Y] {n : ℕ}

def locG (π : R →+* k) (e : Y ≃ Fin n) : GL (Fin n) R →* GL Y k :=
  (Units.mapEquiv (Matrix.reindexAlgEquiv k k e.symm).toMulEquiv).toMonoidHom.comp (Formalism.UG.bc π)

theorem locG_apply (π : R →+* k) (e : Y ≃ Fin n) (z : GL (Fin n) R) (a b : Y) : (locG π e z).val a b = π (z.val (e a) (e b)) := rfl

end Read

section Cong
variable {F E k : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem val_le_of_congAt {Y : Type} [Fintype Y] [DecidableEq Y] {P : HeightOneSpectrum (𝓞 E)}
    (π : E ⊗[F] FiniteAdeleRing (𝓞 F) F →+* k) (hπ : ∀ z, IntAtA (F := F) P z → π z ∈ 𝒪[k]) {ϖ : kˣ}
    (hϖ : π (iA F E ((qOf P : ℕ) : E)) = ϖ) (e : Y ≃ Fin n) {D : ℕ} {z : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)}
    (hz : GlobalTheory.TwU.CongAt P D z) (a b : Y) : valuation k (((locG π e z).val - 1) a b) ≤ valuation k (ϖ : k) ^ D := by
  have h := hπ _ (hz (e a) (e b))
  have e1 : π (iA F E (((qOf P : ℕ) : E) ^ D)⁻¹) = ((ϖ : k) ^ D)⁻¹ := by
    rw [← hϖ, ← map_pow, ← map_pow]
    exact map_inv₀ (π.comp (iA F E : E →+* _)) _
  have e2 : π ((z.val - 1) (e a) (e b)) = ((locG π e z).val - 1) a b := by
    rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, locG_apply]
    congr 1
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  rw [map_mul, e1, e2, Valuation.mem_integer_iff, map_mul, map_inv₀, map_pow,
    inv_mul_le_iff₀ (zero_lt_iff.2 (pow_ne_zero _ (by simp))), mul_one] at h
  exact h

theorem transfer {A : Type} [Fintype A] [DecidableEq A] {J : Subgroup (GL (A ⊕ Fin 0) k)} (h1 : KOne k _ ≤ J) (hJ : J ≤ KO k _)
    {P : HeightOneSpectrum (𝓞 E)} (π : E ⊗[F] FiniteAdeleRing (𝓞 F) F →+* k) (hπ : ∀ z, IntAtA (F := F) P z → π z ∈ 𝒪[k]) {ϖ : kˣ}
    (hϖ : π (iA F E ((qOf P : ℕ) : E)) = ϖ) (hϖ1 : valuation k (ϖ : k) < 1) (e : A ⊕ Fin 0 ≃ Fin n) {M D : ℕ} (hD : 1 ≤ D)
    (hM : 2 * M ≤ D) {y : A → k} (hy : y ∈ box A (ϖ ^ M)⁻¹) {K f κ r : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)}
    (hK : locG π e K ∈ J) (hf : GlobalTheory.TwU.CongAt P D (K⁻¹ * f)) (hr : GlobalTheory.TwU.CongAt P D ((f⁻¹ * κ * f)⁻¹ * r)) :
    locG π e r ∈ cosStab J (box A (ϖ ^ M)) (Submodule.Quotient.mk y) ↔
      locG π e κ ∈ cosStab J (box A (ϖ ^ M)) (Submodule.Quotient.mk ((locG π e K).val.toBlocks₁₁ *ᵥ y)) := by
  have u1 := deep_mem h1 hJ hϖ1 hD hM hy (val_le_of_congAt π hπ hϖ e hf)
  have u2 := deep_mem h1 hJ hϖ1 hD hM hy (val_le_of_congAt π hπ hϖ e hr)
  have er : r = (K⁻¹ * f)⁻¹ * ((K⁻¹ * κ * K) * ((K⁻¹ * f) * ((f⁻¹ * κ * f)⁻¹ * r))) := by group
  rw [← conj_iff hJ _ y hK, ← map_inv, ← map_mul, ← map_mul]
  conv_lhs => rw [er]
  rw [map_mul, map_mul _ (K⁻¹ * κ * K), map_mul _ (K⁻¹ * f), map_inv, Subgroup.mul_mem_cancel_left _ (inv_mem u1),
    Subgroup.mul_mem_cancel_right _ (mul_mem u1 u2)]

end Cong

theorem lev_facts {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S₀ : Set ℕ} {mu : Tup X.F X.E X.K S₀}
    {cst : LocCst X (rowSG Pr sel mu)} {σ₀ : X.K →+* ℂ} {P : rowSG Pr sel mu} {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : X.E →+* k} {s : ℕ} {W : TwData k}
    (hA : AtTwist (R := R) sel mu cst σ₀ P ι s W) {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m}
    (hL : L.Ok Ch sel mu cst G s) (b : L.β (s + 1)) (e : XIx (Fin R.k) (Fin R.t) (s + 1) ≃ Fin (R.N (s + 1))) (he : IsOrd xPos e) :
    KOne k _ ≤ ((W.T s R).lev (s + 1) 0 rfl).J ∧ ((W.T s R).lev (s + 1) 0 rfl).J ≤ KO k _ ∧
      ∀ γ : Sp X.E (R.N (s + 1)) ≃ₗ[X.E] Sp X.E (R.N (s + 1)),
        phi ι ((Equiv.sumEmpty _ (Fin 0)).trans e) γ ∈ ((W.T s R).lev (s + 1) 0 rfl).J ↔
          γ ∈ prCat (Pr := Pr) cst.sharp (s + 1) P.1 (L.h (s + 1) b P) := by
  have hc : cOf R (s + 1) = 0 := by have := hA.steps; unfold cOf; omega
  have hn : R.N (s + 1) = R.k + (s + 1) * (R.t + 1) := rfl
  let e' : XIx (Fin R.k) (Fin R.t) (s + 1) ⊕ Fin 0 ≃ Fin (R.N (s + 1) + 0) := (Equiv.sumEmpty _ _).trans e
  have he' : IsOrd (yPos xPos (R.N (s + 1))) e' := by
    rintro (a | a)
    · exact he a
    · exact a.elim0
  set o := stdOrd (Fin R.k) (Fin R.t) (s + 1) 0 (rfl : s + 1 + 0 = s + 1) with ho
  have hconj : ∀ g : GL _ k, (plainFrame (k := k) o).conj.symm g = (reGL o).symm g := fun g => by
    rw [MulEquiv.symm_apply_eq, LatFrame.conj_apply, show (plainFrame (k := k) o).bas = 1 from rfl,
      show (plainFrame (k := k) o).ord = o from rfl, MulEquiv.apply_symm_apply]
    simp
  have hJ : ∀ g, g ∈ ((W.T s R).lev (s + 1) 0 rfl).J ↔ (reGL o).symm g ∈ (parahoric _ (Fin (s + 1) × Fin R.t) W.δ W.tame).J :=
    fun g => by rw [← hconj]; rfl
  refine ⟨fun u hu => (hJ u).2 (((parahoric _ (Fin (s + 1) × Fin R.t) W.δ W.tame).reindex o).KOne_le hu), fun g hg => ?_,
    fun γ => ?_⟩
  · have h := (mem_parahoric.1 ((hJ g).1 hg)).1
    rw [mem_KO] at h ⊢
    rw [← map_inv] at h
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · simpa [reGL_symm_val] using h.1 (o.symm i) (o.symm j)
    · simpa [reGL_symm_val] using h.2 (o.symm i) (o.symm j)
  · rw [hJ, hL.last_h, prCat, Jat, if_neg hA.nmem, mem_prX_JQ _ _ _ _ _ hc]
    exact mem_par_iff (c := 0) (s := s) hA.compl W.unif rfl hn he' W.tame γ

open GlobalTheory.Mem.Col2 in

theorem pow_smul_rep_mem {X : Fields} {Pr : Primes X} {R : Ranks}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S₀ : Set ℕ} {mu : Tup X.F X.E X.K S₀}
    {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ} (p : PtAt R sel mu cst u j) (h : j + 1 = R.m) (P : rowSG Pr sel mu)
    (hP : P.1 ∉ Pr.vGs) (hq : ((qOf P.1 : ℕ) : X.E) ≠ 0) :
    ((qOf P.1 : ℕ) : X.E) ^ cst.M • (frsF sel mu p.1.1 P).symm (repY p.1.2) ∈ stdAt X.E (R.N j) P.1 := by
  obtain ⟨y0, hy0, hY⟩ := p.mem_ybSet h
  have hr := p.repY_mem h
  generalize repY p.1.2 = y at hr ⊢
  rw [hY] at hr
  have a1 : ((qOf P.1 : ℕ) : X.E) ^ cst.M • y0 ∈ localization₂ P.1.asIdeal p.1.1.deco.1.N := by
    have := (Submodule.mem_iInf _).1 hy0 P
    simpa [hP] using this
  have a2 : (((qOf P.1 : ℕ) : X.E) ^ cst.M)⁻¹ • (y - y0) ∈ localization₂ P.1.asIdeal p.1.1.deco.1.N := by
    have := (Submodule.mem_iInf _).1 hr P
    simpa [hP] using this
  have a3 := GlobalTheory.Mem.Col2.AdT.CosShape.pow_smul_mem _ (qOf P.1 : 𝓞 X.E) (cst.M + cst.M) a2
  have a4 : ((qOf P.1 : ℕ) : X.E) ^ cst.M • y ∈ localization₂ P.1.asIdeal p.1.1.deco.1.N := by
    have := add_mem a3 a1
    convert this using 1
    have hq' : ((qOf P.1 : ℕ) : X.E) ^ cst.M ≠ 0 := pow_ne_zero _ hq
    rw [smul_smul, show (((qOf P.1 : ℕ) : 𝓞 X.E) : X.E) = ((qOf P.1 : ℕ) : X.E) by simp, pow_add, mul_inv_cancel_right₀ hq',
      ← smul_add, sub_add_cancel]
  have hfr := frsF_eq_ptFr sel mu p.1.1 P ▸ isFr_ptFr p.1.1 P.1
  rw [← map_smul]
  exact (hfr _).1 (by rwa [LinearEquiv.apply_symm_apply])

theorem mem_box_inv {E k : Type} [Field E] [NumberField E] [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ} {ι : E →+* k} {ϖ : kˣ} {A : Type} {n : ℕ}
    (hc : IsCompl P q ι ϖ) (e : A ≃ Fin n) (M : ℕ) (v : Sp E n) (hv : (q : E) ^ M • v ∈ stdAt E n P) :
    (fun r => ι (v (e r))) ∈ box A (ϖ ^ M)⁻¹ := fun r => by
  have h := (mem_box_iff hc e 0 ((q : E) ^ M • v)).2 (by simpa using hv) r
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_pow, ← hc.unif, pow_zero, Units.val_one, map_one] at h
  rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀, map_pow, ← one_mul (_ ^ M)⁻¹,
    le_mul_inv_iff₀ (zero_lt_iff.2 (pow_ne_zero _ (by simp))), mul_comm]
  exact h

section Seam
open Formalism.L2.Ker Formalism.MainNotions
variable {D : D7} {X : Fields} (s : Seam D X) {n : ℕ}

theorem seamGL_surj (M : GL (Fin n) D.host.E) : ∃ g : Sp X.E n ≃ₗ[X.E] Sp X.E n, GlobalTheory.TwU.seamGL s g = M := by
  refine ⟨LinearMap.GeneralLinearGroup.generalLinearEquiv X.E (Fin n → X.E)
    (Matrix.GeneralLinearGroup.toLin (Formalism.UG.bc (s.iE.symm : D.host.E →+* X.E) M)), ?_⟩
  simp only [GlobalTheory.TwU.seamGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  exact Units.ext (Matrix.ext fun a b => s.iE.apply_symm_apply _)

theorem locG_seamGL {k : Type} [Field k] {Y : Type} [Fintype Y] [DecidableEq Y]
    (π : D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F →+* k) (ι : X.E →+* k)
    (h : ∀ x, π (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (s.iE x)) = ι x) (e : Y ≃ Fin n)
    (g : Sp X.E n ≃ₗ[X.E] Sp X.E n) : locG π e (GlobalTheory.TwU.ratA D.host.F (GlobalTheory.TwU.seamGL s g)) = phi ι e g := by
  ext a b
  rw [locG_apply, phi_val]
  refine (h (LinearMap.toMatrix' g.toLinearMap (e a) (e b))).trans ?_
  rw [LinearMap.toMatrix'_apply]
  unfold toLoc
  congr 3

theorem transfer_rat {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A : Type} [Fintype A] [DecidableEq A] {J : Subgroup (GL (A ⊕ Fin 0) k)} (h1 : KOne k _ ≤ J) (hJ : J ≤ KO k _)
    {P : HeightOneSpectrum (𝓞 D.host.E)} (π : D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F →+* k)
    (hπ : ∀ z, IntAtA (F := D.host.F) P z → π z ∈ 𝒪[k]) {ϖ : kˣ}
    (hϖ : π (iA D.host.F D.host.E ((qOf P : ℕ) : D.host.E)) = ϖ) (hϖ1 : valuation k (ϖ : k) < 1) (ι : X.E →+* k)
    (h : ∀ x, π (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (s.iE x)) = ι x) (e : A ≃ Fin n)
    {M d : ℕ} (hd : 1 ≤ d) (hM : 2 * M ≤ d) (fr : Sp X.E n ≃ₗ[X.E] Sp X.E n) (Y : Sp X.E n)
    (hy : (fun r => ι (fr.symm Y (e r))) ∈ box A (ϖ ^ M)⁻¹)
    {K f κ : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)}
    (hK : ∀ x y, π (K.val x y) = ι (fr (Pi.single y 1) x)) (hKJ : phi ι ((Equiv.sumEmpty _ (Fin 0)).trans e) fr ∈ J)
    (hf : GlobalTheory.TwU.CongAt P d (K⁻¹ * f)) (g : Sp X.E n ≃ₗ[X.E] Sp X.E n)
    (hr : GlobalTheory.TwU.CongAt P d ((f⁻¹ * κ * f)⁻¹ * GlobalTheory.TwU.ratA D.host.F (GlobalTheory.TwU.seamGL s g))) :
    phi ι ((Equiv.sumEmpty _ (Fin 0)).trans e) g ∈ cosStab J (box A (ϖ ^ M)) (Submodule.Quotient.mk fun r => ι (fr.symm Y (e r))) ↔
      locG π ((Equiv.sumEmpty _ (Fin 0)).trans e) κ ∈ cosStab J (box A (ϖ ^ M)) (Submodule.Quotient.mk fun r => ι (Y (e r))) := by
  have hkb : locG π ((Equiv.sumEmpty _ (Fin 0)).trans e) K = phi ι ((Equiv.sumEmpty _ (Fin 0)).trans e) fr :=
    Units.ext (Matrix.ext fun x y => hK _ _)
  have := transfer h1 hJ π hπ hϖ hϖ1 ((Equiv.sumEmpty _ (Fin 0)).trans e) hd hM hy (hkb ▸ hKJ) hf hr
  rwa [locG_seamGL s π ι h, hkb, phi_mulVec e _ (fun _ => rfl), LinearEquiv.apply_symm_apply] at this

end Seam

theorem phi_stab_iff {E k : Type} [Field E] [NumberField E] [StarRing E] [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ} {ι : E →+* k} {ϖ : kˣ} {A : Type} [Fintype A]
    [DecidableEq A] {n : ℕ} (hc : IsCompl P q ι ϖ) (e : A ≃ Fin n) {J : Subgroup (GL (A ⊕ Fin 0) k)} (hJ : J ≤ KO k _) (M : ℕ)
    (y : Sp E n) (g : Sp E n ≃ₗ[E] Sp E n) :
    phi ι ((Equiv.sumEmpty _ (Fin 0)).trans e) g ∈ cosStab J (box A (ϖ ^ M)) (Submodule.Quotient.mk fun r => ι (y (e r))) ↔
      phi ι ((Equiv.sumEmpty _ (Fin 0)).trans e) g ∈ J ∧ ∀ l, IntAt P (((q : E) ^ M)⁻¹ * (g y - y) l) := by
  rw [mem_stab_iff hJ, phi_mulVec e _ (fun _ => rfl)]
  have e1 : ((fun r => ι (g y (e r))) - fun r => ι (y (e r))) = fun r => ι ((g y - y) (e r)) := by
    funext r
    exact (map_sub ι _ _).symm
  rw [e1, mem_box_iff hc e, GlobalTheory.GO.ChRoot.mem_stdAt']
  rfl

end GlobalTheory.PenLoc
end LocalPart

section GlobalPart
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

namespace GlobalTheory.PenLoc

section Split
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem prF_int (q : GlobalTheory.FinPl.SplitPt D k) {P : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt q.e P) (z : EAf D)
    (hz : Formalism.L2.Col.IntAtA (F := D.host.F) P z) : q.prF he z ∈ 𝒪[k] := by
  obtain ⟨s, hs, h⟩ := hz
  have h1 := (q.prF_mem_iff he _).2 (mul_mem (GlobalTheory.IdemRes.resS_idem_eq_one D q.e P he).1 h)
  have h2 : 1 ≤ valuation k (q.prF he (Formalism.L2.Col.iA D.host.F D.host.E (algebraMap (𝓞 D.host.E) D.host.E s))) :=
    not_lt.1 fun h' => hs ((q.mem_iff_val_lt he s).2 h')
  rw [map_mul, Valuation.mem_integer_iff, map_mul] at h1
  exact (le_mul_of_one_le_left' h2).trans h1

theorem prF_inclE (q : GlobalTheory.FinPl.SplitPt D k) {P : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt q.e P)
    (x : D.host.E) : q.prF he (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) x) = q.pr (incA D x) :=
  q.prF_toEAf he (incA D x)

theorem prF_eq_of_adAt (q : GlobalTheory.FinPl.SplitPt D k) {P : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt q.e P)
    (z : EAf D) (x : D.host.E) (h : adAt D.host.F P z = algebraMap D.host.E (P.adicCompletion D.host.E) x) :
    q.prF he z = q.pr (incA D x) := by
  obtain ⟨a, rfl⟩ := GlobalTheory.ResLoc.toEAf_surj z
  rw [q.prF_toEAf]
  exact GlobalTheory.SplitProj.pr_eq_of_adAt q P he a x h

theorem locHom_std (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y)
    (e : Y ≃ Fin S.rank) (hF : F.β = (1 : Matrix (Fin S.rank) (Fin S.rank) k).submatrix id e) (g : GA D S) (a b : Y) :
    (GlobalTheory.LevIdx.locHom q S F g).val a b = q.pr (Formalism.L2.Theta.mt S g (e a) (e b)) := by
  have h := congrFun (congrFun ((GlobalTheory.LevIdx.eq_locHom_iff q S F g _).2 rfl) (e a)) (e b)
  rw [GlobalTheory.Fam.MovedJoin.mul_frameγ_std F e hF, GlobalTheory.Fam.MovedJoin.frameβ_mul_std F e hF] at h
  exact h.symm

set_option synthInstance.maxHeartbeats 200000 in
theorem prV_comm (v : GlobalTheory.FinPl.Pl D) (z : Af ↥D.host.F ⊗[↥D.host.F] D.host.E) :
    Formalism.UG.prV (E := D.host.E) v ((Algebra.TensorProduct.comm (↥D.host.F) (Af ↥D.host.F) D.host.E) z) =
      (Algebra.TensorProduct.comm _ _ _) (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul a e =>
    rw [Algebra.TensorProduct.comm_tmul]
    simp only [Formalism.UG.prV, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.comm_tmul]
    rfl
  | add a b ha hb =>
    simp only [map_add]
    exact congrArg₂ (· + ·) ha hb

set_option synthInstance.maxHeartbeats 200000 in
theorem prV_toEAf_eq_zero (v : GlobalTheory.FinPl.Pl D) (y : AE D) (h : GlobalTheory.FinPl.compAt D v y = 0) :
    Formalism.UG.prV (E := D.host.E) v (toEAf D y) = 0 := by
  unfold GlobalTheory.FinPl.compAt at h
  unfold toEAf
  simp only [RingHom.comp_apply] at h ⊢
  generalize finPart D y = z at h ⊢
  refine (prV_comm v z).trans ?_
  rw [h, map_zero]

set_option synthInstance.maxHeartbeats 200000 in

theorem bc_prV_eq_one (S : HSp D) {P : GlobalTheory.FinPl.Pl D → Prop} {g : GA D S} (hg : g ∈ GlobalTheory.FinPl.grpAt S P) {m : ℕ} (hm : S.rank = m)
    (x : GL (Fin m) (EF D)) (hx : x.1 = finM S hm g) (v : GlobalTheory.FinPl.Pl D) (hv : ¬ P v) :
    Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x = 1 := by
  have key : ∀ i j, GlobalTheory.FinPl.compAt D v (Formalism.L2.Theta.mt S g i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) = 0 := by
    intro i j
    unfold GlobalTheory.FinPl.grpAt GlobalTheory.FinPl.congGrp at hg
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hg
    have h1 := congrArg (fun u => u.1 i j) hg
    simp only [GeneralLinearGroup.map_apply, Units.val_one] at h1
    have h2 : Ideal.Quotient.mk (GlobalTheory.FinPl.idAt D P) (Formalism.L2.Theta.mt S g i j) =
        Ideal.Quotient.mk (GlobalTheory.FinPl.idAt D P) ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) := by
      refine h1.trans ?_
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    rw [Ideal.Quotient.eq] at h2
    unfold GlobalTheory.FinPl.idAt at h2
    rw [Ideal.mem_inf] at h2
    have h3 := h2.2
    rw [Submodule.mem_iInf] at h3
    exact (RingHom.mem_ker).1 (h3 ⟨v, hv⟩)
  apply Units.ext
  ext i j
  change Formalism.UG.prV (E := D.host.E) v (x.1 i j) = (1 : Matrix (Fin m) (Fin m) _) i j
  rw [hx]
  simp only [GlobalTheory.AdForm.finM, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]
  have h := prV_toEAf_eq_zero v _ (key ((finCongr hm).symm i) ((finCongr hm).symm j))
  rw [map_sub, map_sub, sub_eq_zero] at h
  rw [h]
  by_cases hij : i = j
  · subst hij
    simp [Matrix.one_apply]
  · have hij' : (finCongr hm).symm i ≠ (finCongr hm).symm j := fun e => hij ((finCongr hm).symm.injective e)
    simp [Matrix.one_apply, hij, hij']

end Split

set_option maxHeartbeats 2000000 in

theorem uloc_iff {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
    {Ch₀ : ℕ → Type} (hOk : I.Ok) (hP : TC.Pins B X) (A : TwDat I l Z u a Ch₀) (hA : A.Is) (P : BadPr I a)
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt (I.rec7 l Z) k) (PP : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E)) (hPP : P.1 = PP)
    (hq : Formalism.L2.NTheta.IsIdemAt q.e PP) (s : ℕ) (W : GlobalTheory.TwBridge.TwData k) (ι : B.fields.E →+* k)
    (hι : ∀ x, q.pr (incA (I.rec7 l Z) x) = ι x)
    (hW : GlobalTheory.TwBridge.AtTwist (R := B.R) (k := k) I.sel (I.tup a) (I.cst a) B.embLL P ι s W)
    (hm : s + 1 ≤ B.R.m) (β : Ch₀ (s + 1)) (e : XIx (Fin B.R.k) (Fin B.R.t) (s + 1) ≃ Fin (B.R.N (s + 1)))
    (he : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e)
    (hK : GlobalTheory.TwBridge.Lev.phi ι ((Equiv.sumEmpty _ (Fin 0)).trans e)
      (Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 (s + 1) β).1.1 P) ∈ ((W.T s B.R).lev (s + 1) 0 rfl).J)
    (M : ℕ) (hM : M = (I.cst a).M) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (hv : Formalism.L2.Col.IsOver v PP)
    (κ : GL (Fin (B.R.N (s + 1))) (EF (I.rec7 l Z)))
    (hκ : κ ∈ Formalism.UG.UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) (s + 1) hm) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) :
    Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) κ ∈ (A.K (s + 1) hm β).lev.Uloc v ↔
      locG (q.prF hq) ((Equiv.sumEmpty _ (Fin 0)).trans e) κ ∈ GlobalTheory.PenVol.cosStab ((W.T s B.R).lev (s + 1) 0 rfl).J (box _ (W.ϖ ^ M))
        (Submodule.Quotient.mk fun r => ι (Formalism.L2.Col.repY (A.p0 (s + 1) β).1.2 (e r))) := by
  subst hM
  subst hPP
  have hs := hW.steps
  have h1 : s + 1 + 1 = B.R.m := by omega
  have hm' : s + 1 < B.R.m := by omega
  obtain ⟨c, rfl⟩ := hA.chOf_onto _ hm β
  obtain ⟨fb, hfb⟩ := GlobalTheory.T.exists_rational_frames_near_adelic_at_bad_primes I hOk l Z a _ (A.kb _ (A.chOf _ c))
  have hL : Formalism.L2.Col.ChIdx.Ok I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.glob s :=
    (show B.R.m - 2 = s by omega) ▸ hOk.idx_ok a
  obtain ⟨hJ1, hJ2, hJ3⟩ := lev_facts hW hL (Idx.get c.1 hm') e he
  have hy0 : ∀ P', (Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 (s + 1) (A.chOf _ c)).1.1 P').symm
      (Formalism.L2.Col.repY (A.p0 (s + 1) (A.chOf _ c)).1.2) ∈ cosetIn ((I.stp u a (s + 1)).rep c) P' := fun P' => by
    rw [(hA.rep _ hm c).2]
    exact ((GlobalTheory.T.couplingCosetInFrames_shape_at_bad_prime I hOk u a _ _ P').2 h1).2.1 _ (PtAt.repY_mem _ h1)
  have hfin : AdT.ChiFin I l Z (A.K (s + 1) hm (A.chOf _ c)).lev := by
    obtain ⟨n, hn, h⟩ := hA.fin _ hm (A.chOf _ c)
    exact ⟨n, hn, fun κ _ => h κ⟩
  obtain ⟨hle, hge, -⟩ := AdT.lev_mid hOk hP (hA.reads _ hm) c hfb hfin hm' _ (fun _ => hy0) (fun _ _ _ => Iff.rfl)
  have hseam : GlobalTheory.TwU.seamP (AdT.sm I l Z) P.1 = P.1 := by
    ext x
    exact GlobalTheory.TwU.mem_seamP (AdT.sm I l Z) P.1 x
  have hq0 : ((Formalism.L2.Col.qOf P.1 : ℕ) : B.fields.E) ≠ 0 := Nat.cast_ne_zero.2 (GlobalTheory.GO.ChRoot.qOf_pos P.1).ne'
  have hbox := mem_box_inv hW.compl e (I.cst a).M _ (pow_smul_rep_mem (A.p0 (s + 1) (A.chOf _ c)) h1 P hW.nmem hq0)
  have hϖ : q.prF hq (Formalism.L2.Col.iA (I.rec7 l Z).host.F (I.rec7 l Z).host.E ((Formalism.L2.Col.qOf P.1 : ℕ) : (I.rec7 l Z).host.E)) = W.ϖ :=
    (prF_inclE q hq _).trans ((hι _).trans hW.compl.unif.symm)
  have hf := (hfb P).1
  rw [hseam] at hf
  have htr := fun g (hg : GlobalTheory.TwU.InFrame (i := s + 1) (AdT.sm I l Z) fb (I.cst a).D P κ g) =>
    transfer_rat (κ := κ) (AdT.sm I l Z) hJ1 hJ2 (q.prF hq) (prF_int q hq) hϖ ((W.unif _).2 le_rfl) ι
      (fun x => (prF_inclE q hq x).trans (hι x)) e ((hOk.idx_ok a).cst_ok.D_pos P) ((hOk.idx_ok a).depthQ P hW.nmem) _ _ hbox
      (fun x y => (prF_eq_of_adAt q hq _ _ (GlobalTheory.Fam.MovedJoin.adAt_kb_eq_frsF A hA P hW.nmem _ hm _ x y)).trans (hι _)) hK hf g
      (by unfold GlobalTheory.TwU.InFrame GlobalTheory.TwU.NearAt at hg; rw [hseam] at hg; exact hg)
  have hsc : ∀ y y', GlobalTheory.TwU.SameCoset (n := B.R.N (s + 1)) I.sel (I.tup a) (I.cst a) P y y' ↔
      ∀ r, Formalism.L2.Col.IntAt P.1 ((((Formalism.L2.Col.qOf P.1 : ℕ) : B.fields.E) ^ (I.cst a).M)⁻¹ * (y - y') r) := fun y y' => by
    unfold GlobalTheory.TwU.SameCoset
    rw [if_neg hW.nmem]
  constructor
  · intro h
    obtain ⟨g, z, hg, hin⟩ := hle P v (by rw [hseam]; exact hv) κ hκ h
    exact (htr g hin).1 ((phi_stab_iff hW.compl e hJ2 _ _ g).2
      ⟨(hJ3 g).2 ((GlobalTheory.TwU.exists_midLev_iff _ _ _ _ _ _ _ _).1 ⟨z, hg.1⟩), (hsc _ _).1 (hg.2 h1)⟩)
  · intro h
    obtain ⟨fb', hfb'⟩ := GlobalTheory.T.exists_rational_frames_near_adelic_at_bad_primes I hOk l Z a (B.R.N (s + 1))
      ((GlobalTheory.TwU.ratA (I.rec7 l Z).host.F (fb P))⁻¹ * κ * GlobalTheory.TwU.ratA (I.rec7 l Z).host.F (fb P))
    obtain ⟨g, hg⟩ := seamGL_surj (AdT.sm I l Z) (fb' P)
    have hin : GlobalTheory.TwU.InFrame (i := s + 1) (AdT.sm I l Z) fb (I.cst a).D P κ g := by
      have h2 := (hfb' P).1
      rw [← hg] at h2
      exact h2
    obtain ⟨a1, a2⟩ := (phi_stab_iff hW.compl e hJ2 _ _ g).1 ((htr g hin).2 h)
    obtain ⟨z, hz⟩ := (GlobalTheory.TwU.exists_midLev_iff I.Ch _ _ _ _ _ _ _).2 ((hJ3 g).1 a1)
    exact hge P v (by rw [hseam]; exact hv) κ hκ ⟨g, z, ⟨hz, fun _ => (hsc _ _).2 a2⟩, hin⟩

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word}
  {a : GeoAll W u} {t : W.P.T}

set_option maxHeartbeats 2000000 in

theorem rd_iff (hW : AllTrue W) (ha : a.Is) (hTr : a.True) (J : QJ a t) (hJ : J.Reads) (i : Fin J.r) (j : ℕ)
    (e : j = (J.G i).s + 1) (hm : j ≤ B.R.m) (β : J.Ch₀ j) (g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))
    (κ : GL (Fin (B.R.N j)) (EF (I.rec7 l Z))) (hg : κ.1 = finM _ (rankN (I.rec7 l Z) j hm) g)
    (hκ : κ ∈ Formalism.UG.UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) j hm) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) :
    Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) (J.G i).q.v) κ ∈ (J.A.K j hm β).lev.Uloc (J.G i).q.v ↔
      GlobalTheory.PenBridge.rdAt J j i e g ∈ GlobalTheory.PenVol.cosStab (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J
        (box _ ((J.G i).ϖ ^ (J.E i).M)) ((J.E i).cos (cast (congrArg (J.E i).Ch e) (J.π i j β))) := by
  subst e
  obtain ⟨e', he', hF⟩ := (ha.stdQ (J.pl i) ⟨t, J.mem i⟩).1 ((J.G i).s + 1) le_rfl
  let e : XIx (Fin B.R.k) (Fin B.R.t) ((J.G i).s + 1) ≃ Fin (B.R.N ((J.G i).s + 1)) :=
    e'.trans (finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm))
  have he : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e := fun x => he' x
  obtain ⟨K, hKJ, hK, -⟩ := (GlobalTheory.Fam.QJ.Reads.movedAt W hW u a ha t J hJ i).pen hm β e he
  have hKe : GlobalTheory.TwBridge.Lev.phi (E := B.fields.E) ((J.G i).q.pr.comp (incA (I.rec7 l Z))) ((Equiv.sumEmpty _ (Fin 0)).trans e)
      (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((J.G i).s + 1) β).1.1 (J.P i)) = K := by
    refine Units.ext (Matrix.ext ?_)
    rintro (x | x) (y | y)
    · exact (hK (e' x) y).trans (GlobalTheory.Fam.MovedJoin.frameβ_mul_std _ e' hF _ x y)
    · exact y.elim0
    · exact x.elim0
    · exact x.elim0
  have hv : Formalism.L2.Col.IsOver (J.G i).q.v (J.pl i) :=
    congrArg HeightOneSpectrum.asIdeal ((GlobalTheory.Fam.QJPlaces.places_under W hW u a ha hTr t J hJ).2 i)
  have hrd : GlobalTheory.PenBridge.rdAt J _ i rfl g = locG ((J.G i).q.prF (J.G i).idem) ((Equiv.sumEmpty _ (Fin 0)).trans e) κ := by
    refine Units.ext (Matrix.ext ?_)
    rintro (x | x) (y | y)
    · refine (locHom_std (J.G i).q _ _ e' hF g x y).trans ?_
      refine ((J.G i).q.prF_toEAf (J.G i).idem _).symm.trans (congrArg _ ?_)
      exact (congrFun (congrFun hg (e x)) (e y)).symm
    · exact y.elim0
    · exact x.elim0
    · exact x.elim0
  rw [hrd]
  refine (uloc_iff hW.tr.ok hW.tr.pins.some J.A hJ.is (J.P i) (J.G i).q (J.pl i) (hJ.eq i) (J.G i).idem (J.G i).s
    ((J.E i).tw (J.hψ i) (J.sg i)) _ (fun _ => rfl) (hJ.tw i) hm β e he (hKe ▸ hKJ) (J.E i).M (hJ.M i) _ hv κ hκ).trans ?_
  exact Iff.of_eq (congrArg (fun c => locG ((J.G i).q.prF (J.G i).idem) ((Equiv.sumEmpty _ (Fin 0)).trans e) κ ∈
    GlobalTheory.PenVol.cosStab (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J
      (box _ ((J.G i).ϖ ^ (J.E i).M)) c) (hJ.cos i β e he).symm)

end GlobalTheory.PenLoc

set_option maxHeartbeats 2000000 in
open scoped Pointwise in

theorem GlobalTheory.PenLoc.level_iff_relax : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : QJ a t), J.Reads → ∀ α : J.Ch j, ∃ c : (i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1) ⊕ Fin 0) (J.G i).k, (∀ i, c i ∈ (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J) ∧ ∀ g, g ∈ J.A.U j (J.ι j α) ↔ g ∈ GlobalTheory.PenLev.relax J j hj α ∧ ∀ i, c i * GlobalTheory.PenBridge.rd J j hj g i * (c i)⁻¹ ∈ GlobalTheory.PenVol.cosStab (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J (GlobalTheory.StepData.box _ ((J.G i).ϖ ^ (J.E i).M)) ((J.E i).cos (cast (congrArg (J.E i).Ch (show j = (J.G i).s + 1 by have h1 := (J.G i).hs; have h2 : (I.rec7 l Z).R.m = B.R.m := rfl; omega)) (α i))) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ α
  have hm : j ≤ B.R.m := by omega
  refine ⟨1, fun i => one_mem _, fun g => ?_⟩
  simp only [Pi.one_apply, one_mul, inv_one, mul_one]
  have key := fun i => GlobalTheory.PenLoc.rd_iff hW ha hTr J hJ i j (GlobalTheory.PenBridge.step_before_last_eq_s_succ J hj i) hm (J.ι j α)
  simp only [hJ.sec j hm α] at key
  have fwd := fun x (hx : x ∈ J.A.U j (J.ι j α)) i =>
    ((hJ.is.U j hm _ x).1 hx).2.elim fun κ hκ =>
      (key i x κ.1 hκ (((J.A.K j hm _).lev.U_eq _).1 κ.2).1).1 ((((J.A.K j hm _).lev.U_eq _).1 κ.2).2 _)
  constructor
  · intro hg
    exact ⟨(GlobalTheory.PenLev.mem_relax_iff J j hj α g).2 ⟨Subgroup.mem_sup_left hg, ((hJ.is.U j hm _ g).1 hg).1,
      fun i => (J.E i).le _ _ _ (GlobalTheory.PenVol.cosStab_le _ _ _ (fwd g hg i))⟩, fwd g hg⟩
  · rintro ⟨hr, hH⟩
    obtain ⟨hs, hgf, -⟩ := (GlobalTheory.PenLev.mem_relax_iff J j hj α g).1 hr
    have hN : (GlobalTheory.FinPl.grpAt ((I.rec7 l Z).sp.X j) (GlobalTheory.PenBridge.plF J)).Normal := by
      unfold GlobalTheory.FinPl.grpAt GlobalTheory.FinPl.congGrp; exact MonoidHom.normal_ker _
    have : g ∈ ((J.A.U j (J.ι j α) : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))) *
        (GlobalTheory.FinPl.grpAt ((I.rec7 l Z).sp.X j) (GlobalTheory.PenBridge.plF J) : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)))) := by
      rw [← Subgroup.mul_normal]; exact hs
    obtain ⟨x, hx, n, hn, rfl⟩ := this
    refine mul_mem hx ?_
    have hnf : n ∈ GfC ((I.rec7 l Z).sp.X j) := (Subgroup.mul_mem_cancel_left _ ((hJ.is.U j hm _ x).1 hx).1).1 hgf
    obtain ⟨φ, hφ⟩ := GlobalTheory.FinPartIso.exists_finIso (I.rec7 l Z) _ _ (rankN (I.rec7 l Z) j hm)
    refine (hJ.is.U j hm _ n).2 ⟨hnf, ⟨(φ ⟨n, hnf⟩).1, ((J.A.K j hm _).lev.U_eq _).2 ⟨(φ ⟨n, hnf⟩).2, fun v => ?_⟩⟩, hφ ⟨n, hnf⟩⟩
    by_cases hv : GlobalTheory.PenBridge.plF J v
    · obtain ⟨i, rfl⟩ := hv
      refine (key i n _ (hφ ⟨n, hnf⟩) (φ ⟨n, hnf⟩).2).2 ?_
      have h2 := hH i
      rw [map_mul, Pi.mul_apply] at h2
      exact (Subgroup.mul_mem_cancel_left _ (fwd x hx i)).1 h2
    · rw [GlobalTheory.PenLoc.bc_prV_eq_one _ hn _ _ (hφ ⟨n, hnf⟩) v hv]
      exact one_mem _

end GlobalPart
end
