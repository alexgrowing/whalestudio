import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsAdaptedEmpty
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviNormalizesUnipotentVariant
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanIwasawaMinimalParabolic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousAdelicUnitaryEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommuteGelfandInvariantMatrixUnitsOfGlRel
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QminorPolyMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetAddOneSubEqSumQminorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TracedQminorComatrixTruncatedInverseStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetPolyMapMonicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuantumDeterminantPolynomialCoefficients
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliPolynomialCoefficientsIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LongWConjApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliLeviFactorizationSum
import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.FrameMatEqGlobal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
import Formalism.LocalToGlobal.GlobalTheory.VolumeCarry.VolumeTheoremTwoOfRationalFrames
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbRelAtRealPlaceOfUnitaryEmbedding
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterActionTransportChart
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousConjBlockEmbeddingStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BlockBasisChangeEntriesStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdaptedFrameOrthogonalSubspaceStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterLocalNontrivialStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GlRelationsDerivativePreservedStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GelfandEigenvalueCasimirScalarStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AutomorphicFunctionRestrictBlockStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdaptedBasisConjugateZeroEntriesStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConjugatedMatrixUnitEntriesStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.OrthogonalSubspaceWittFrameExtensionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCentre

section Gelf

open Formalism.REAL Finset

theorem epow_eq_pow' {B : Type} [Ring B] {n : ℕ} (E : Fin n → Fin n → B) (m : ℕ) (a b : Fin n) :
    epow E m a b = (Matrix.of E ^ m) a b := by
  induction m generalizing a b with
  | zero => simp [epow, Matrix.one_apply]
  | succ m ih => simp [epow, pow_succ, Matrix.mul_apply, ih]

theorem etr_succ_eq_gelfA' {B : Type} [Ring B] [Algebra ℂ B] {n : ℕ} (E : Fin n → Fin n → B) (k : ℕ) :
    etr E (k + 1) = GlobalTheory.SmoothForms.gelfA E k := by
  rw [GlobalTheory.SmoothForms.gelfA_eq_sum_pow]; simp [etr, epow_eq_pow']

theorem etr_mem_adjoin_qdet' (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A)
    (hX : GlRel X) (N : ℕ) : etr X N ∈ Algebra.adjoin ℂ (Set.range (qdet X)) := by
  set S := Algebra.adjoin ℂ (Set.range (qdet X)) with hS
  have hq : ∀ u, qdet X u ∈ S := fun u => Algebra.subset_adjoin ⟨u, rfl⟩
  cases n with
  | zero => simp [etr]
  | succ m =>
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      obtain ⟨c, hc1, hc⟩ := GlobalTheory.T.exists_monic_poly_eq_qdet A (m + 1) X
      have hmin : ∀ i j : Fin (m + 1), ∃ c' : ℕ → A, ∀ w : ℂ,
          qminor X (Fin.succAbove j) (Fin.succAbove i) w = ∑ d ∈ range (m + 1), w ^ d • c' d := by
        intro i j
        obtain ⟨c', hc'⟩ := GlobalTheory.qminor_polyMap A (m + 1) m X (Fin.succAbove j) (Fin.succAbove i) 0
        exact ⟨c', fun w => by simpa using hc' w⟩
      choose cm hcm using hmin
      let Rs : ℂ → A := fun w => ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
        (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) * qminor X (Fin.succAbove j) (Fin.succAbove i) w
          * epow X (N + 1) j i
      let Rc : ℕ → A := fun d => ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
        (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) * cm i j d * epow X (N + 1) j i
      have hR : ∀ w : ℂ, Rs w = ∑ d ∈ range (m + 1), w ^ d • Rc d := by
        intro w
        simp only [Rs, Rc, hcm, mul_sum, sum_mul, smul_sum, mul_smul_comm, smul_mul_assoc]
        conv_lhs => enter [2, x]; rw [sum_comm]
        rw [sum_comm]
      let f : ℂ → A := fun u => qdet X u * etr X N - Rs u
      let a : ℕ → A := fun i => c i * etr X N - if i < m + 1 then Rc i else 0
      have hf : ∀ u, f u = ∑ i ∈ range (m + 1 + 1), u ^ i • a i := by
        intro u
        simp only [f, a, hc u, hR u, sum_mul, smul_mul_assoc, smul_sub, sum_sub_distrib]
        congr 1
        rw [sum_range_succ _ (m + 1), if_neg (lt_irrefl _), smul_zero, add_zero]
        exact sum_congr rfl fun i hi => by rw [if_pos (mem_range.mp hi)]
      have hmem : ∀ u, f u ∈ S := by
        intro u
        have h1 := GlobalTheory.T.traced_qminor_comatrix_truncated_inverse A m X hX u N
        rw [← GlobalTheory.T.qdet_add_one_sub_eq_sum_qminor', sum_range_succ, Nat.sub_self, pow_zero, mul_one, mul_add] at h1
        have key : algebraMap ℂ A ((-1) ^ N) * f u = algebraMap ℂ A ((u - m) ^ (N + 1)) * (qdet X (u + 1) - qdet X u)
            - qdet X u * ∑ k ∈ range N, algebraMap ℂ A ((-1) ^ k * (u - m) ^ (N - k)) * etr X k := by
          simp only [f]
          rw [mul_sub, ← mul_assoc, Algebra.commutes, mul_assoc, sub_eq_sub_iff_add_eq_add, h1]
          abel
        have hm : algebraMap ℂ A ((-1) ^ N) * f u ∈ S := by
          rw [key]
          refine sub_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (sub_mem (hq _) (hq _)))
            (mul_mem (hq _) (sum_mem fun k hk => mul_mem (Subalgebra.algebraMap_mem _ _) (ih k (mem_range.mp hk))))
        have : f u = algebraMap ℂ A ((-1) ^ N) * (algebraMap ℂ A ((-1) ^ N) * f u) := by
          rw [← mul_assoc, ← map_mul, ← mul_pow, neg_one_mul, neg_neg, one_pow, map_one, one_mul]
        rw [this]
        exact mul_mem (Subalgebra.algebraMap_mem _ _) hm
      have htop := GlobalTheory.CompanionTheory.CTFin.QdetCoeff.coeff_mem_span_values (m + 1) a f hf (m + 1) le_rfl
      have ha : a (m + 1) = etr X N := by simp [a, hc1]
      rw [ha] at htop
      have hle : Submodule.span ℂ (Set.range f) ≤ Subalgebra.toSubmodule S :=
        Submodule.span_le.mpr (by rintro _ ⟨u, rfl⟩; exact hmem u)
      exact hle htop

end Gelf

section Abstract

variable {W : Type} [AddCommGroup W] [Module ℂ W]

theorem qdet_commute {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {E : Fin n → Fin n → A} (hE : Formalism.REAL.GlRel E) (u v : ℂ) :
    Commute (Formalism.REAL.qdet E u) (Formalism.REAL.qdet E v) := by
  have h : Formalism.REAL.qdet E v ∈ Subalgebra.centralizer ℂ {Formalism.REAL.qdet E u} := by
    refine GlobalTheory.CompanionTheory.CTFin.CapFactor.qdet_mem _ _ (fun i j => ?_) _
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ rfl
    exact Formalism.REAL.qDetCentral A n E hE u i j
  exact (Subalgebra.mem_centralizer_iff ℂ).1 h _ rfl

def nW {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (Xf : Fin N → Fin N → Module.End ℂ W) (Wn : Submodule ℂ W) : Submodule ℂ W :=
  Submodule.span ℂ {G | ∃ p q, GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks n h) p < GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks n h) q ∧ ∃ F ∈ Wn, G = Xf p q F}

theorem block_keeps {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (Xf : Fin N → Fin N → Module.End ℂ W)
    (hX : Formalism.REAL.GlRel Xf) (Wn : Submodule ℂ W) (hW : ∀ p q, ∀ F ∈ Wn, Xf p q F ∈ Wn) (a b : Fin N)
    (hab : GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks n h) a = GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks n h) b) :
    ∀ G ∈ nW n h Xf Wn, Xf a b G ∈ nW n h Xf Wn := by
  intro G hG
  induction hG using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨p, q, hpq, F, hF, rfl⟩ := hG
    have e := LinearMap.congr_fun (hX a b p q) F
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at e
    have e' : Xf a b (Xf p q F) = Xf p q (Xf a b F) + (((if b = p then Xf a q else 0) - (if q = a then Xf p b else 0)) F) := by
      rw [LinearMap.sub_apply, ← e]; abel
    rw [e']
    refine Submodule.add_mem _ (Submodule.subset_span ⟨p, q, hpq, _, hW a b F hF, rfl⟩) ?_
    rw [LinearMap.sub_apply]
    refine Submodule.sub_mem _ ?_ ?_
    · split_ifs with e1
      · subst e1
        exact Submodule.subset_span ⟨a, q, hab ▸ hpq, F, hF, rfl⟩
      · exact Submodule.zero_mem _
    · split_ifs with e1
      · subst e1
        exact Submodule.subset_span ⟨p, b, hab ▸ hpq, F, hF, rfl⟩
      · exact Submodule.zero_mem _
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem monic_gelf_block {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (Xf : Fin N → Fin N → Module.End ℂ W)
    (hX : Formalism.REAL.GlRel Xf) (Wn : Submodule ℂ W) (hW : ∀ p q, ∀ F ∈ Wn, Xf p q F ∈ Wn) (W₀ : Set W) (h0 : W₀ ⊆ Wn)
    (hs : ∀ v : ℂ, ∃ s : ℂ, ∀ F ∈ W₀, Formalism.REAL.qdet Xf v F = s • F) (i : Fin c) (k : ℕ) :
    ∃ q : Polynomial ℂ, q.Monic ∧ ∀ F ∈ W₀,
      Polynomial.aeval (GlobalTheory.SmoothForms.gelfA (fun p q : Fin (n i) => Xf (GlobalTheory.SmGL.stdBlocks n h ⟨i, p⟩) (GlobalTheory.SmGL.stdBlocks n h ⟨i, q⟩)) k) q F ∈
        nW n h Xf Wn := by
  classical
  set I := nW n h Xf Wn with hI
  set Ei : Fin (n i) → Fin (n i) → Module.End ℂ W := fun p q => Xf (GlobalTheory.SmGL.stdBlocks n h ⟨i, p⟩) (GlobalTheory.SmGL.stdBlocks n h ⟨i, q⟩) with hEi
  have hEg : Formalism.REAL.GlRel Ei := fun a b c' d => by
    have := hX (GlobalTheory.SmGL.stdBlocks n h ⟨i, a⟩) (GlobalTheory.SmGL.stdBlocks n h ⟨i, b⟩) (GlobalTheory.SmGL.stdBlocks n h ⟨i, c'⟩) (GlobalTheory.SmGL.stdBlocks n h ⟨i, d⟩)
    simp only [EmbeddingLike.apply_eq_iff_eq, Sigma.mk.injEq, heq_eq_eq, true_and] at this
    exact this
  have hL : ∀ p q, GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks n h) p < GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks n h) q → ∀ F ∈ Wn, I.mkQ (Xf p q F) = 0 :=
    fun p q hpq F hF => (Submodule.Quotient.mk_eq_zero I).2 (Submodule.subset_span ⟨p, q, hpq, F, hF, rfl⟩)
  have hq := GlobalTheory.T.gl_relations_triangular_annihilation W (W ⧸ I) c N n h Xf hX Wn hW I.mkQ hL W₀ h0 hs i
  have hEI : ∀ p q, ∀ G ∈ I, Ei p q G ∈ I := fun p q =>
    block_keeps n h Xf hX Wn hW _ _ (by simp [GlobalTheory.SmGL.blk])
  let pres : Subalgebra ℂ (Module.End ℂ W) := GlobalTheory.CompanionTheory.Dblock.CentreBlocks.preserving I
  let s : Set (Module.End ℂ W) := Set.range (Formalism.REAL.qdet Ei)
  have hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x := by
    rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    exact (qdet_commute hEg u v).eq
  letI : CommRing (Algebra.adjoin ℂ s) := Algebra.adjoinCommRingOfComm ℂ hcomm
  have hpres : Algebra.adjoin ℂ s ≤ pres := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨u, rfl⟩
    exact GlobalTheory.CompanionTheory.CTFin.CapFactor.qdet_mem pres Ei (fun p q G hG => hEI p q G hG) u
  let Y : Ideal (Algebra.adjoin ℂ s) :=
    { carrier := {x | ∀ F ∈ W₀, (x : Module.End ℂ W) F ∈ I}
      add_mem' := fun {x y} hx hy F hF => by
        simpa using I.add_mem (hx F hF) (hy F hF)
      zero_mem' := fun F _ => by simp
      smul_mem' := fun c x hx F hF => by
        show ((c * x : Algebra.adjoin ℂ s) : Module.End ℂ W) F ∈ I
        rw [Subalgebra.coe_mul, Module.End.mul_apply]
        exact hpres c.2 _ (hx F hF) }
  let π := Ideal.Quotient.mkₐ ℂ Y
  have hint : ∀ x (hx : x ∈ Algebra.adjoin ℂ s), IsIntegral ℂ (π ⟨x, hx⟩) := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      obtain ⟨p, hpm, hp⟩ := hq w
      refine ⟨p, hpm, ?_⟩
      rw [← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      intro F hF
      rw [Polynomial.aeval_subalgebra_coe]
      exact (Submodule.Quotient.mk_eq_zero I).1 (hp F hF)
    | algebraMap r =>
      have : (⟨algebraMap ℂ _ r, Subalgebra.algebraMap_mem _ r⟩ : Algebra.adjoin ℂ s) = algebraMap ℂ (Algebra.adjoin ℂ s) r := rfl
      rw [this, AlgHom.commutes]
      exact isIntegral_algebraMap
    | add x y hx hy ihx ihy =>
      have : (⟨x + y, add_mem hx hy⟩ : Algebra.adjoin ℂ s) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [this, map_add]
      exact ihx.add ihy
    | mul x y hx hy ihx ihy =>
      have : (⟨x * y, mul_mem hx hy⟩ : Algebra.adjoin ℂ s) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [this, map_mul]
      exact ihx.mul ihy
  have hg : GlobalTheory.SmoothForms.gelfA Ei k ∈ Algebra.adjoin ℂ s := by
    rw [← etr_succ_eq_gelfA']
    exact etr_mem_adjoin_qdet' _ _ Ei hEg _
  obtain ⟨q, hqm, hq0⟩ := hint _ hg
  refine ⟨q, hqm, fun F hF => ?_⟩
  rw [← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at hq0
  have := hq0 F hF
  rwa [Polynomial.aeval_subalgebra_coe] at this

end Abstract

section Statements

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}

theorem frame_isom {V V' : HSp D} {ι : V'.V →ₗ[D.host.E] V.V} (hι : HSpace.IsIsomEmb V' V ι) (τ : D.what₂.Tau) :
    ((frameMat V V' ι).map (tauE D τ))ᴴ * gramAt D V τ * (frameMat V V' ι).map (tauE D τ) = gramAt D V' τ := by
  have hG : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V V' ι) * V.gram * frameMat V V' ι = V'.gram := by
    have hG' := Formalism.L2.GlobalTheoryTheory.VolumeCarry.gram_frameMat D V V' ι hι
    rw [← Formalism.IndefR.Mi.frameMat_eq_global] at hG'
    exact hG'.symm
  have e : ((frameMat V V' ι).map (tauE D τ))ᴴ = (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V V' ι)).map (tauE D τ) := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Formalism.UG.cT, Matrix.transpose_apply]
    exact (GlobalTheory.Mem.Isom.tauE_sig D τ _).symm
  rw [e]
  simp only [gramAt]
  rw [← Matrix.map_mul, ← Matrix.map_mul]
  rw [hG]

theorem s_oneP (hθ : IsInfFam θ) {V V' : HSp D} {ι : V'.V →ₗ[D.host.E] V.V} (hι : HSpace.IsIsomEmb V' V ι)
    {s : GA D V' →* GA D V} (hs : ∀ h, EmbRel V V' ι (s h) h) {τ : D.what₂.Tau}
    {A : Matrix (Fin V'.rank) (Fin V'.rank) ℂ} (hA : A ∈ lieAt V' τ) (t : ℝ) :
    s (oneP θ V' τ A t) = oneP θ V τ ((frameMat V V' ι).map (tauE D τ) * A *
      ((gramAt D V' τ)⁻¹ * ((frameMat V V' ι).map (tauE D τ))ᴴ * gramAt D V τ)) t := by
  obtain ⟨-, -, f3, f4, f5⟩ := GlobalTheory.T.hermitian_form_change_of_basis_lie (gramAt D V τ) (gramAt D V' τ) ((frameMat V V' ι).map (tauE D τ)) (GlobalTheory.SmoothForms.RealPts.gramAt_herm V τ) (GlobalTheory.SmoothForms.RealPts.gramAt_herm V' τ) (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ) (GlobalTheory.SmoothForms.RealPts.gramAt_unit V' τ) (frame_isom hι τ)
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  have R' := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V'
  obtain ⟨s₀, -, hs₀, -⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D V V' ι hι
  have hg := GlobalTheory.SmoothAutCheck.exp_mem_UH (R.1 τ).2 (X := (frameMat V V' ι).map (tauE D τ) * A *
      ((gramAt D V' τ)⁻¹ * ((frameMat V V' ι).map (tauE D τ))ᴴ * gramAt D V τ)) (f3 A hA) t
  have hh := GlobalTheory.SmoothAutCheck.exp_mem_UH (R'.1 τ).2 hA t
  have e := GlobalTheory.EmbAtPlace.embRel_atTau D θ hθ V' V ι τ _ _ hh hg ⟨f4 A t, f5 A t⟩
  rw [hs₀] at e
  have e' := (hs₀ _ _).1 (hs (oneP θ V' τ A t))
  exact e'.trans e.symm

theorem rder_slice (hθ : IsInfFam θ) {V V' : HSp D} {ι : V'.V →ₗ[D.host.E] V.V} (hι : HSpace.IsIsomEmb V' V ι)
    {s : GA D V' →* GA D V} (hs : ∀ h, EmbRel V V' ι (s h) h) {τ : D.what₂.Tau}
    {A : Matrix (Fin V'.rank) (Fin V'.rank) ℂ} (hA : A ∈ lieAt V' τ) {y : GA D V} (hy : ∀ h, s h * y = y * s h) (F : GA D V → ℂ) :
    Rder θ V' τ A (fun h => F (s h * y)) = fun h => Rder θ V τ ((frameMat V V' ι).map (tauE D τ) * A *
      ((gramAt D V' τ)⁻¹ * ((frameMat V V' ι).map (tauE D τ))ᴴ * gramAt D V τ)) F (s h * y) := by
  funext h
  unfold Rder
  congr 1
  funext t
  show F (s (h * oneP θ V' τ A t) * y) = _
  rw [map_mul, mul_assoc, hy, ← mul_assoc, s_oneP hθ hι hs hA t]

theorem rderC_slice : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
    ∀ (V V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → ∀ s : GA D V' →* GA D V, (∀ h, EmbRel V V' ι (s h) h) →
    ∀ (τ : D.what₂.Tau) (Z : Matrix (Fin V'.rank) (Fin V'.rank) ℂ) (y : GA D V), (∀ h, s h * y = y * s h) → ∀ F : GA D V → ℂ,
      RderC θ V' τ Z (fun h => F (s h * y)) = fun h =>
        RderC θ V τ ((frameMat V V' ι).map (tauE D τ) * Z *
          ((gramAt D V' τ)⁻¹ * ((frameMat V V' ι).map (tauE D τ))ᴴ * gramAt D V τ)) F (s h * y) := by
  intro D θ hθ V V' ι hι s hs τ Z y hy F
  obtain ⟨-, f2, -, -, -⟩ := GlobalTheory.T.hermitian_form_change_of_basis_lie (gramAt D V τ) (gramAt D V' τ) ((frameMat V V' ι).map (tauE D τ)) (GlobalTheory.SmoothForms.RealPts.gramAt_herm V τ) (GlobalTheory.SmoothForms.RealPts.gramAt_herm V' τ) (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ) (GlobalTheory.SmoothForms.RealPts.gramAt_unit V' τ) (frame_isom hι τ)
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V' τ Z
  have e : ∀ Z, conjAt V τ ((frameMat V V' ι).map (tauE D τ) * Z *
      ((gramAt D V' τ)⁻¹ * ((frameMat V V' ι).map (tauE D τ))ᴴ * gramAt D V τ)) = (frameMat V V' ι).map (tauE D τ) * conjAt V' τ Z *
      ((gramAt D V' τ)⁻¹ * ((frameMat V V' ι).map (tauE D τ))ᴴ * gramAt D V τ) := f2
  funext h
  simp only [RderC, Pi.add_apply, Pi.smul_apply, rder_slice hθ hι hs h1 hy, rder_slice hθ hι hs h2 hy, e]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul]

theorem mid_frame : ∀ (D : D7) (V V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι →
    ∀ (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), IsWittFrame D.sp.cm.sig V.gram X Y →
    ∀ T : Finset (Fin m), (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) →
    ∀ C : GL (Fin V.rank) D.host.E, GlobalTheory.BlockForms.IsAdapted D.sp.cm.sig V.gram X Y C →
    ∀ a : ℕ, a ≤ m → (∀ i : Fin m, i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T ↔ i.val < a) →
    ∃ hdim : a + V'.rank + a = V.rank, ∀ τ : D.what₂.Tau, ∃ B Bi : Matrix (Fin V'.rank) (Fin V'.rank) ℂ, B * Bi = 1 ∧
      ∀ p q : Fin V'.rank,
        (frameMat V V' ι).map (tauE D τ) * Matrix.single p q (1 : ℂ) *
            ((gramAt D V' τ)⁻¹ * ((frameMat V V' ι).map (tauE D τ))ᴴ * gramAt D V τ) =
          ∑ r : Fin V'.rank, ∑ u : Fin V'.rank, (B r p * Bi q u) •
            (C.1.map (tauE D τ) * Matrix.single (⟨a + r.val, by omega⟩ : Fin V.rank) (⟨a + u.val, by omega⟩ : Fin V.rank) (1 : ℂ) *
              (C.1.map (tauE D τ))⁻¹) := by
  intro D V V' ι hι m X Y hW T hr C hC a ham hup
  obtain ⟨hdim, B, Bi, hBB, hB, hperp⟩ := GlobalTheory.T.adapted_frame_orthogonal_subspace D V V' ι hι m X Y hW T hr C hC a ham hup
  refine ⟨hdim, fun τ => ⟨B.map (tauE D τ), Bi.map (tauE D τ), ?_, ?_⟩⟩
  · rw [← Matrix.map_mul, hBB, Matrix.map_one _ (map_zero _) (map_one _)]
  · obtain ⟨f1, -, -, -, -⟩ := GlobalTheory.T.hermitian_form_change_of_basis_lie (gramAt D V τ) (gramAt D V' τ) ((frameMat V V' ι).map (tauE D τ)) (GlobalTheory.SmoothForms.RealPts.gramAt_herm V τ) (GlobalTheory.SmoothForms.RealPts.gramAt_herm V' τ) (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ) (GlobalTheory.SmoothForms.RealPts.gramAt_unit V' τ) (frame_isom hι τ)
    have hPu : IsUnit (C.1.map (tauE D τ)).det := by
      have h1 : C.1.map (tauE D τ) * ((C⁻¹).1.map (tauE D τ)) = 1 := by
        rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
      exact isUnit_det_of_right_inverse h1
    refine GlobalTheory.T.block_basis_change_entries V.rank V'.rank a hdim _ hPu _ _ _ _ f1 ?_ ?_ ?_
    · rw [← Matrix.map_mul, hBB, Matrix.map_one _ (map_zero _) (map_one _)]
    · intro i j
      simp only [Matrix.map_apply, hB i j, map_sum, map_mul]
    · intro b hb
      have h1 := hperp b hb
      have h2 : ((frameMat V V' ι).map (tauE D τ))ᴴ * gramAt D V τ = (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V V' ι) * V.gram).map (tauE D τ) := by
        rw [Matrix.map_mul]
        congr 1
        ext i j
        simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Formalism.UG.cT, Matrix.transpose_apply]
        exact (GlobalTheory.Mem.Isom.tauE_sig D τ _).symm
      have h3 : (((frameMat V V' ι).map (tauE D τ))ᴴ * gramAt D V τ) *ᵥ (fun k => C.1.map (tauE D τ) k b) = 0 := by
        rw [h2]
        have h4 := RingHom.map_mulVec (tauE D τ) (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V V' ι) * V.gram) (fun k => C.1 k b)
        funext i
        have h5 := h4 i
        rw [h1] at h5
        simpa [Function.comp_def] using h5.symm
      rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, h3, Matrix.mulVec_zero]

end Statements

section Vanish

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}

theorem derEnd_coe' (hθ : IsInfFam θ) {V : HSp D} (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (F : GlobalTheory.Mem.AutSpace.SmFun θ V) : (GlobalTheory.Mem.RealTranslate.derEnd hθ τ Z F).1 = RderC θ V τ Z F.1 := rfl

theorem rderC_left {V : HSp D} (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) {f : GA D V → ℂ} {u : GA D V}
    (h : ∀ g, f (u * g) = f g) (g : GA D V) : RderC θ V τ Z f (u * g) = RderC θ V τ Z f g := by
  simp only [RderC, Rder, Pi.add_apply, Pi.smul_apply, mul_assoc, h]

theorem rder_eq_zero {V : HSp D} {m : ℕ} {X Y : Matrix (Fin V.rank) (Fin m) D.host.E} (hW : IsWittFrame D.sp.cm.sig V.gram X Y)
    {T : Finset (Fin m)} {τ : D.what₂.Tau} {A : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hA : ∀ t : ℝ, oneP θ V τ A t ∈ unip D.sp.cm.sig V.gram X T) {f : GA D V → ℂ}
    (hf : ∀ u ∈ unip D.sp.cm.sig V.gram X T, ∀ g, f (u * g) = f g) {g : GA D V} (hg : g ∈ levi D.sp.cm.sig V.gram X Y T) :
    Rder θ V τ A f g = 0 := by
  have e : (fun t : ℝ => f (g * oneP θ V τ A t)) = fun _ => f g := by
    funext t
    have h1 := GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.conj_mem_unip_of_mem_levi D V m X Y hW T g hg _ (hA t)
    have := hf _ h1 g
    rwa [inv_mul_cancel_right] at this
  simp only [Rder, e, deriv_const]

theorem der_unip_vanish (hθ : IsInfFam θ) {V : HSp D} {m : ℕ} {X Y : Matrix (Fin V.rank) (Fin m) D.host.E}
    (hW : IsWittFrame D.sp.cm.sig V.gram X Y) {T : Finset (Fin m)} {a : ℕ} (ham : a ≤ m) (hk : ∃ k ∈ T, k.val + 1 = a)
    {C : GL (Fin V.rank) D.host.E} (hC : GlobalTheory.BlockForms.IsAdapted D.sp.cm.sig V.gram X Y C) (τ : D.what₂.Tau)
    {p q : Fin V.rank} (hpq : ∃ e : ℕ, (e = a ∨ e + a = V.rank) ∧ p.val < e ∧ e ≤ q.val)
    (F : GlobalTheory.Mem.AutSpace.SmFun θ V) (hF : ∀ u ∈ unip D.sp.cm.sig V.gram X T, ∀ g, F.1 (u * g) = F.1 g)
    {g : GA D V} (hg : g ∈ levi D.sp.cm.sig V.gram X Y T) :
    (GlobalTheory.Mem.RealTranslate.derEnd hθ τ (C.1.map (tauE D τ) * Matrix.single p q (1 : ℂ) * (C.1.map (tauE D τ))⁻¹) F).1 g = 0 := by
  classical
  set P := C.1.map (tauE D τ) with hP
  have hPu : IsUnit P.det := by
    have h1 : P * ((C⁻¹).1.map (tauE D τ)) = 1 := by
      rw [hP, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    exact isUnit_det_of_right_inverse h1
  set Z := P * Matrix.single p q (1 : ℂ) * P⁻¹ with hZ
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
  have cut : ∀ b c : Fin V.rank, (∃ e : ℕ, (e = 0 ∨ e = 0 + a ∨ e + 0 + a = V.rank ∨ e + 0 = V.rank) ∧ b.val < e ∧ e ≤ c.val) ∨ False →
      ∃ e : ℕ, (e = 0 ∨ e = 0 + a ∨ e + 0 + a = V.rank ∨ e + 0 = V.rank) ∧ b.val < e ∧ e ≤ c.val := fun b c h => by simpa using h
  have hcut : ∃ e : ℕ, (e = 0 ∨ e = 0 + a ∨ e + 0 + a = V.rank ∨ e + 0 = V.rank) ∧ p.val < e ∧ e ≤ q.val := by
    obtain ⟨e, he, h3, h4⟩ := hpq
    refine ⟨e, ?_, h3, h4⟩
    rcases he with rfl | he
    · right; left; omega
    · right; right; left; omega
  have hZ0 : P⁻¹ * Z * P = Matrix.single p q (1 : ℂ) := by
    rw [hZ]
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ hPu, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hPu, Matrix.one_mul]
  have hc1 : ∀ b c : Fin V.rank, (P⁻¹ * conjAt V τ Z * P) b c ≠ 0 →
      ∃ e : ℕ, (e = 0 ∨ e = 0 + a ∨ e + 0 + a = V.rank ∨ e + 0 = V.rank) ∧ b.val < e ∧ e ≤ c.val :=
    fun b c h => GlobalTheory.T.adapted_basis_conjugate_zero_entries D V m X Y hW 0 a (by omega) C hC τ p q b c hcut h
  have hc0 : ∀ b c : Fin V.rank, (P⁻¹ * Z * P) b c ≠ 0 →
      ∃ e : ℕ, (e = 0 ∨ e = 0 + a ∨ e + 0 + a = V.rank ∨ e + 0 = V.rank) ∧ b.val < e ∧ e ≤ c.val := by
    intro b c h
    rw [hZ0] at h
    have hb : p = b ∧ q = c := by
      by_contra hne
      exact h (Matrix.single_apply_of_ne _ _ _ _ _ (by tauto))
    obtain ⟨rfl, rfl⟩ := hb
    exact hcut
  have hA : ∀ (x y : ℂ) (A : Matrix (Fin V.rank) (Fin V.rank) ℂ), A = x • Z + y • conjAt V τ Z → ∀ b c : Fin V.rank,
      (P⁻¹ * A * P) b c ≠ 0 →
      ∃ e : ℕ, (e = 0 ∨ e = 0 + a ∨ e + 0 + a = V.rank ∨ e + 0 = V.rank) ∧ b.val < e ∧ e ≤ c.val := by
    rintro x y A rfl b c h
    by_cases h0 : (P⁻¹ * Z * P) b c = 0
    · refine hc1 b c fun h1 => h ?_
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_apply, Matrix.smul_apply, h0, h1,
        smul_zero, add_zero]
    · exact hc0 b c h0
  have u1 := fun t => GlobalTheory.T.adapted_basis_block_entries D θ hθ V m X Y hW T 0 a (by omega) (by simpa using hk) (Or.inl rfl) C hC τ _ h1
    (hA (1 / 2) (1 / 2) _ (by simp only [smul_add])) t
  have u2 := fun t => GlobalTheory.T.adapted_basis_block_entries D θ hθ V m X Y hW T 0 a (by omega) (by simpa using hk) (Or.inl rfl) C hC τ _ h2
    (hA (1 / (2 * Complex.I)) (-(1 / (2 * Complex.I))) _ (by rw [smul_sub, neg_smul, sub_eq_add_neg])) t
  rw [derEnd_coe']
  simp only [RderC, Pi.add_apply, Pi.smul_apply, rder_eq_zero hW u1 hF hg, rder_eq_zero hW u2 hF hg, smul_zero, add_zero]

end Vanish

section Key

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}

theorem glRel_conj {n : ℕ} {P Q : Matrix (Fin n) (Fin n) ℂ} (hQP : Q * P = 1) :
    Formalism.REAL.GlRel (fun a b : Fin n => P * Matrix.single a b (1 : ℂ) * Q) := by
  have e : ∀ A B : Matrix (Fin n) (Fin n) ℂ, (P * A * Q) * (P * B * Q) = P * (A * B) * Q := fun A B => by
    calc (P * A * Q) * (P * B * Q) = P * A * (Q * P) * B * Q := by simp only [Matrix.mul_assoc]
      _ = P * (A * B) * Q := by rw [hQP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have sm : ∀ a b c d : Fin n, Matrix.single a b (1 : ℂ) * Matrix.single c d (1 : ℂ) =
      if b = c then Matrix.single a d (1 : ℂ) else 0 := by
    intro a b c d
    split_ifs with h
    · subst h
      simp
    · ext i j
      simp only [Matrix.mul_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      rcases eq_or_ne b k with rfl | hk
      · have h1 : ¬(c = b ∧ d = j) := fun x => h x.1.symm
        simp [Matrix.single_apply, h1]
      · have h1 : ¬(a = i ∧ b = k) := fun x => hk x.2
        simp [Matrix.single_apply, h1]
  intro a b c d
  simp only [e, sm]
  split_ifs <;> simp

theorem span_conj {n : ℕ} {P Q : Matrix (Fin n) (Fin n) ℂ} (hPQ : P * Q = 1) :
    Submodule.span ℂ (Set.range fun p : Fin n × Fin n => P * Matrix.single p.1 p.2 (1 : ℂ) * Q) = ⊤ := by
  refine eq_top_iff.2 fun Z _ => ?_
  have e : Z = P * (Q * Z * P) * Q := by
    calc Z = (P * Q) * Z * (P * Q) := by rw [hPQ, Matrix.one_mul, Matrix.mul_one]
      _ = P * (Q * Z * P) * Q := by simp only [Matrix.mul_assoc]
  rw [e, Matrix.matrix_eq_sum_single (Q * Z * P)]
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have : Matrix.single i j ((Q * Z * P) i j) = ((Q * Z * P) i j) • Matrix.single i j (1 : ℂ) := by simp
  rw [this, Matrix.mul_smul, Matrix.smul_mul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)

theorem standard_three_block_index {a n' N : ℕ} (h : ∑ i, (![a, n', a] : Fin 3 → ℕ) i = N) (b : Fin 3) (i : Fin ((![a, n', a] : Fin 3 → ℕ) b)) :
    ((GlobalTheory.SmGL.stdBlocks (![a, n', a] : Fin 3 → ℕ) h ⟨b, i⟩ : Fin N) : ℕ) =
      (if b = 0 then 0 else if b = 1 then a else a + n') + i.val := by
  rw [GlobalTheory.SmGL.stdBlocks_val]
  fin_cases b <;> simp [Fin.sum_univ_succ]

theorem cut_of_blk {a n' N : ℕ} (h : ∑ i, (![a, n', a] : Fin 3 → ℕ) i = N) {p q : Fin N}
    (hpq : GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks (![a, n', a] : Fin 3 → ℕ) h) p < GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks (![a, n', a] : Fin 3 → ℕ) h) q) :
    ∃ e : ℕ, (e = a ∨ e + a = N) ∧ p.val < e ∧ e ≤ q.val := by
  obtain ⟨⟨b, i⟩, rfl⟩ := (GlobalTheory.SmGL.stdBlocks (![a, n', a] : Fin 3 → ℕ) h).surjective p
  obtain ⟨⟨c, j⟩, rfl⟩ := (GlobalTheory.SmGL.stdBlocks (![a, n', a] : Fin 3 → ℕ) h).surjective q
  have hbc : b < c := by simpa [GlobalTheory.SmGL.blk] using hpq
  have hN : a + n' + a = N := by
    have := h
    simp only [Fin.sum_univ_three] at this
    simpa using this
  rw [standard_three_block_index h, standard_three_block_index h]
  have hi := i.2
  have hj := j.2
  fin_cases b <;> fin_cases c <;> simp at hbc hi hj
  · exact ⟨a, Or.inl rfl, by simpa using hi, by simp⟩
  · exact ⟨a, Or.inl rfl, by simpa using hi, by simp; omega⟩
  · exact ⟨a + n', Or.inr hN, by simpa using hi, by simp⟩

def leftSm (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (N : Subgroup (GA D V)) :
    Submodule ℂ (GlobalTheory.Mem.AutSpace.SmFun θ V) where
  carrier := {F | ∀ u ∈ N, ∀ g, F.1 (u * g) = F.1 g}
  add_mem' := fun {x y} hx hy u hu g => by
    simp only [Submodule.coe_add, Pi.add_apply, hx u hu g, hy u hu g]
  zero_mem' := fun _ _ _ => rfl
  smul_mem' := fun r x hx u hu g => by
    simp only [Submodule.coe_smul, Pi.smul_apply, hx u hu g]

theorem key_monic (hθ : IsInfFam θ) {V : HSp D} {m : ℕ} {X Y : Matrix (Fin V.rank) (Fin m) D.host.E}
    (hW : IsWittFrame D.sp.cm.sig V.gram X Y) {T : Finset (Fin m)} {a n' : ℕ} (ham : a ≤ m) (hcut : a ≠ 0 → ∃ k ∈ T, k.val + 1 = a)
    {C : GL (Fin V.rank) D.host.E} (hC : GlobalTheory.BlockForms.IsAdapted D.sp.cm.sig V.gram X Y C) (τ : D.what₂.Tau)
    (hdim : a + n' + a = V.rank) (c : ℕ → ℂ) (k : ℕ) :
    ∃ q : Polynomial ℂ, q.Monic ∧ ∀ F : GlobalTheory.Mem.AutSpace.SmFun θ V, (∀ u ∈ unip D.sp.cm.sig V.gram X T, ∀ g, F.1 (u * g) = F.1 g) →
      (∀ k', gelf θ V τ k' F.1 = c k' • F.1) → ∀ g ∈ levi D.sp.cm.sig V.gram X Y T,
        (Polynomial.aeval (GlobalTheory.SmoothForms.gelfA (fun p q : Fin n' => GlobalTheory.Mem.RealTranslate.derEnd hθ τ
          (C.1.map (tauE D τ) * Matrix.single (⟨a + p.val, by omega⟩ : Fin V.rank) (⟨a + q.val, by omega⟩ : Fin V.rank) (1 : ℂ) *
            (C.1.map (tauE D τ))⁻¹)) k) q F).1 g = 0 := by
  classical
  set P := C.1.map (tauE D τ) with hP
  have hPC : P * ((C⁻¹).1.map (tauE D τ)) = 1 := by
    rw [hP, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hPu : IsUnit P.det := isUnit_det_of_right_inverse hPC
  have hPQ : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hPu
  have hQP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hPu
  let nn : Fin 3 → ℕ := ![a, n', a]
  have h : ∑ i, nn i = V.rank := by
    simp only [nn, Fin.sum_univ_three]
    simpa using hdim
  let M : Fin V.rank → Fin V.rank → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun i j => P * Matrix.single i j (1 : ℂ) * P⁻¹
  have hM : Formalism.REAL.GlRel M := glRel_conj hQP
  let Xf : Fin V.rank → Fin V.rank → Module.End ℂ (GlobalTheory.Mem.AutSpace.SmFun θ V) := fun i j => GlobalTheory.Mem.RealTranslate.derEnd hθ τ (M i j)
  have hX : Formalism.REAL.GlRel Xf := GlobalTheory.T.gl_relations_derivative_preserved D θ hθ V τ M hM
  let Wn := leftSm θ V (unip D.sp.cm.sig V.gram X T)
  have hWn : ∀ p q, ∀ F ∈ Wn, Xf p q F ∈ Wn := fun p q F hF u hu g =>
    rderC_left τ _ (hF u hu) g
  let W₀ : Set (GlobalTheory.Mem.AutSpace.SmFun θ V) := {F | F ∈ Wn ∧ ∀ k', gelf θ V τ k' F.1 = c k' • F.1}
  have hs : ∀ v : ℂ, ∃ s : ℂ, ∀ F ∈ W₀, Formalism.REAL.qdet Xf v F = s • F := fun v => by
    obtain ⟨s, hs⟩ := GlobalTheory.T.gelfand_eigenvalue_casimir_scalar D θ hθ V τ M hM (span_conj hPQ) c v
    exact ⟨s, fun F hF => hs F hF.2⟩
  obtain ⟨q, hqm, hq⟩ := monic_gelf_block nn h Xf hX Wn hWn W₀ (fun F hF => hF.1) hs (1 : Fin 3) k
  have hmid : ∀ p : Fin n', (GlobalTheory.SmGL.stdBlocks nn h ⟨(1 : Fin 3), p⟩ : Fin V.rank) = ⟨a + p.val, by omega⟩ := fun p =>
    Fin.ext (by simpa using standard_three_block_index h (1 : Fin 3) p)
  have hfam : GlobalTheory.SmoothForms.gelfA (fun p q : Fin n' => GlobalTheory.Mem.RealTranslate.derEnd hθ τ
      (P * Matrix.single (⟨a + p.val, by omega⟩ : Fin V.rank) (⟨a + q.val, by omega⟩ : Fin V.rank) (1 : ℂ) * P⁻¹)) k =
      GlobalTheory.SmoothForms.gelfA (fun p q : Fin (nn 1) => Xf (GlobalTheory.SmGL.stdBlocks nn h ⟨(1 : Fin 3), p⟩) (GlobalTheory.SmGL.stdBlocks nn h ⟨(1 : Fin 3), q⟩)) k := by
    have e : (fun p q : Fin (nn 1) => Xf (GlobalTheory.SmGL.stdBlocks nn h ⟨(1 : Fin 3), p⟩) (GlobalTheory.SmGL.stdBlocks nn h ⟨(1 : Fin 3), q⟩)) =
        fun p q : Fin n' => GlobalTheory.Mem.RealTranslate.derEnd hθ τ
          (P * Matrix.single (⟨a + p.val, by omega⟩ : Fin V.rank) (⟨a + q.val, by omega⟩ : Fin V.rank) (1 : ℂ) * P⁻¹) := by
      funext p q
      exact congrArg₂ Xf (hmid p) (hmid q)
    rw [e]
    rfl
  refine ⟨q, hqm, fun F hF1 hF2 g hg => ?_⟩
  rw [hfam]
  have hv : ∀ G ∈ nW nn h Xf Wn, G.1 g = 0 := fun G hG => by
    induction hG using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨p, q, hpq, F, hF, rfl⟩ := hx
      have hc := cut_of_blk h hpq
      have ha : a ≠ 0 := by
        rintro rfl
        obtain ⟨e, he, h1, h2⟩ := hc
        have := q.2
        omega
      exact der_unip_vanish hθ hW ham (hcut ha) hC τ hc F hF hg
    | zero => rfl
    | add x y _ _ hx hy => simp only [Submodule.coe_add, Pi.add_apply, hx, hy, add_zero]
    | smul r x _ hx => simp only [Submodule.coe_smul, Pi.smul_apply, hx, smul_zero]
  exact hv _ (hq F ⟨hF1, hF2⟩)

end Key

section Final

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}

theorem gelfA_conj {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) {B Bi : Matrix (Fin n) (Fin n) ℂ}
    (hB : B * Bi = 1) (k : ℕ) :
    GlobalTheory.SmoothForms.gelfA (fun p q => ∑ r, ∑ u, (B r p * Bi q u) • E r u) k = GlobalTheory.SmoothForms.gelfA E k := by
  rw [GlobalTheory.SmoothForms.gelfA_eq_sum_pow, GlobalTheory.SmoothForms.gelfA_eq_sum_pow]
  exact GlobalTheory.RegSch.GChart.trace_pow_conj E Bᵀ Biᵀ (by rw [← Matrix.transpose_mul, hB, Matrix.transpose_one]) (k + 1)

theorem word_slice (hθ : IsInfFam θ) {V V' : HSp D} {ι : V'.V →ₗ[D.host.E] V.V} (hι : HSpace.IsIsomEmb V' V ι)
    {s : GA D V' →* GA D V} (hs : ∀ h, EmbRel V V' ι (s h) h) (τ : D.what₂.Tau) {y : GA D V} (hy : ∀ h, s h * y = y * s h)
    (l : List (Matrix (Fin V'.rank) (Fin V'.rank) ℂ)) (G : GlobalTheory.Mem.AutSpace.SmFun θ V) :
    (l.map (RderC θ V' τ)).foldr (fun f acc => f acc) (fun h => G.1 (s h * y)) = fun h =>
      ((l.map fun Z => GlobalTheory.Mem.RealTranslate.derEnd hθ τ ((frameMat V V' ι).map (tauE D τ) * Z *
        ((gramAt D V' τ)⁻¹ * ((frameMat V V' ι).map (tauE D τ))ᴴ * gramAt D V τ))).prod G).1 (s h * y) := by
  induction l with
  | nil => rfl
  | cons Z l ih =>
    simp only [List.map_cons, List.foldr_cons, List.prod_cons, Module.End.mul_apply]
    rw [ih, rderC_slice D θ hθ V V' ι hι s hs τ Z y hy]
    rfl

theorem gelf_slice (hθ : IsInfFam θ) {V V' : HSp D} {ι : V'.V →ₗ[D.host.E] V.V} (hι : HSpace.IsIsomEmb V' V ι)
    {s : GA D V' →* GA D V} (hs : ∀ h, EmbRel V V' ι (s h) h) (τ : D.what₂.Tau) {y : GA D V} (hy : ∀ h, s h * y = y * s h)
    (k : ℕ) (G : GlobalTheory.Mem.AutSpace.SmFun θ V) :
    gelf θ V' τ k (fun h => G.1 (s h * y)) = fun h =>
      (GlobalTheory.SmoothForms.gelfA (fun p q : Fin V'.rank => GlobalTheory.Mem.RealTranslate.derEnd hθ τ ((frameMat V V' ι).map (tauE D τ) *
        Matrix.single p q (1 : ℂ) * ((gramAt D V' τ)⁻¹ * ((frameMat V V' ι).map (tauE D τ))ᴴ * gramAt D V τ))) k G).1 (s h * y) := by
  funext h
  rw [gelf, GlobalTheory.SmoothForms.gelfA, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun idx _ => ?_
  have e := word_slice hθ hι hs τ hy (List.ofFn fun a : Fin (k + 1) => Matrix.single (idx a) (idx (a + 1)) (1 : ℂ)) G
  rw [List.map_ofFn, List.map_ofFn] at e
  exact congrFun e h

theorem foldr_slice {V V' : HSp D} {s : GA D V' →* GA D V} {y : GA D V} (τ : D.what₂.Tau) (k : ℕ)
    (E : Module.End ℂ (GlobalTheory.Mem.AutSpace.SmFun θ V))
    (hE : ∀ G : GlobalTheory.Mem.AutSpace.SmFun θ V, gelf θ V' τ k (fun h => G.1 (s h * y)) = fun h => (E G).1 (s h * y))
    (L : List ℂ) (G : GlobalTheory.Mem.AutSpace.SmFun θ V) :
    L.foldr (fun a f => gelf θ V' τ k f - a • f) (fun h => G.1 (s h * y)) = fun h =>
      (Polynomial.aeval E ((L.map fun a => Polynomial.X - Polynomial.C a).prod) G).1 (s h * y) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.foldr_cons, List.map_cons, List.prod_cons]
    rw [ih, hE]
    funext h
    simp [map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Module.End.mul_apply, LinearMap.sub_apply,
      Module.algebraMap_end_apply]

theorem prod_roots_toList {q : Polynomial ℂ} (hq : q.Monic) :
    (q.roots.toList.map fun a => Polynomial.X - Polynomial.C a).prod = q := by
  have h := (IsAlgClosed.splits q).eq_prod_roots_of_monic hq
  conv_rhs => rw [h]
  conv_rhs => rw [← Multiset.coe_toList q.roots]
  simp

theorem exists_cut {m : ℕ} (T : Finset (Fin m)) :
    ∃ a ≤ m, (∀ i : Fin m, i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T ↔ i.val < a) ∧ (a ≠ 0 → ∃ k ∈ T, k.val + 1 = a) := by
  by_cases hT : T.Nonempty
  · refine ⟨(T.max' hT).val + 1, (T.max' hT).2, fun i => ⟨?_, fun h => ⟨_, T.max'_mem hT, Nat.lt_succ_iff.1 h⟩⟩,
      fun _ => ⟨_, T.max'_mem hT, rfl⟩⟩
    rintro ⟨k, hk, hik⟩
    exact Nat.lt_succ_iff.2 (le_trans hik (T.le_max' k hk))
  · rw [Finset.not_nonempty_iff_eq_empty] at hT
    subst hT
    exact ⟨0, Nat.zero_le _, fun i => ⟨fun ⟨k, hk, _⟩ => by simp at hk, fun h => by omega⟩, fun h => absurd rfl h⟩

end Final

theorem gelf_slices_monic : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)) (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)) (c : D.what₂.Tau → ℕ → ℂ) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) → ∀ s : GA D V' →* GA D V, (∀ h, EmbRel V V' ι (s h) h) → ∃ A : D.what₂.Tau → ℕ → List ℂ, ∀ ψ ∈ formsOn θ V X Y T U ε fr ρ c, ∀ y ∈ levi D.sp.cm.sig V.gram X Y T, (∀ t ∈ uPart D.sp.cm.sig V.gram X Y T, t * y = y * t) → ∀ τ k, (A τ k).foldr (fun a f => gelf θ V' τ k f - a • f) (fun h => ψ (s h * y)) = 0 := by
  intro D θ hθ V U ε fr W _ _ ρ c m X Y hW T V' ι hι hr s hs
  classical
  obtain ⟨C, hC⟩ := GlobalTheory.T.exists_adapted_witt_basis D V m X Y hW
  obtain ⟨a, ham, hup, hcut⟩ := exists_cut T
  obtain ⟨hdim, hB⟩ := mid_frame D V V' ι hι m X Y hW T hr C hC a ham hup
  have key : ∀ τ k, ∃ q : Polynomial ℂ, q.Monic ∧ ∀ F : GlobalTheory.Mem.AutSpace.SmFun θ V,
      (∀ u ∈ unip D.sp.cm.sig V.gram X T, ∀ g, F.1 (u * g) = F.1 g) → (∀ k', gelf θ V τ k' F.1 = c τ k' • F.1) →
      ∀ g ∈ levi D.sp.cm.sig V.gram X Y T,
        (Polynomial.aeval (GlobalTheory.SmoothForms.gelfA (fun p q : Fin V'.rank => GlobalTheory.Mem.RealTranslate.derEnd hθ τ
          ((frameMat V V' ι).map (tauE D τ) * Matrix.single p q (1 : ℂ) *
            ((gramAt D V' τ)⁻¹ * ((frameMat V V' ι).map (tauE D τ))ᴴ * gramAt D V τ))) k) q F).1 g = 0 := by
    intro τ k
    obtain ⟨q, hqm, hq⟩ := key_monic hθ hW ham hcut hC τ hdim (c τ) k
    obtain ⟨B, Bi, hBB, hBe⟩ := hB τ
    refine ⟨q, hqm, fun F h1 h2 g hg => ?_⟩
    have e : (fun p q : Fin V'.rank => GlobalTheory.Mem.RealTranslate.derEnd hθ τ ((frameMat V V' ι).map (tauE D τ) * Matrix.single p q (1 : ℂ) *
        ((gramAt D V' τ)⁻¹ * ((frameMat V V' ι).map (tauE D τ))ᴴ * gramAt D V τ))) = fun p q => ∑ r, ∑ u, (B r p * Bi q u) •
          GlobalTheory.Mem.RealTranslate.derEnd hθ τ (C.1.map (tauE D τ) * Matrix.single (⟨a + r.val, by omega⟩ : Fin V.rank)
            (⟨a + u.val, by omega⟩ : Fin V.rank) (1 : ℂ) * (C.1.map (tauE D τ))⁻¹) := by
      funext p q
      rw [hBe p q]
      simp only [map_sum, map_smul]
    rw [e, gelfA_conj _ hBB]
    exact hq F h1 h2 g hg
  choose q hqm hq using key
  refine ⟨fun τ k => (q τ k).roots.toList, fun ψ hψ y hy hcomm τ k => ?_⟩
  have hsu := (GlobalTheory.T.orthogonal_subspace_unitary_embedding D V m X Y hW T V' ι hι hr s hs).1
  have hy' : ∀ h, s h * y = y * s h := fun h => hcomm _ (hsu h)
  let G : GlobalTheory.Mem.AutSpace.SmFun θ V := ⟨ψ, GlobalTheory.SphSmooth.mem_smFun_of_isSm hθ hψ.1.smooth⟩
  have e := foldr_slice τ k _ (fun G' => gelf_slice hθ hι hs τ hy' k G') (q τ k).roots.toList G
  rw [prod_roots_toList (hqm τ k)] at e
  refine e.trans (funext fun h => ?_)
  refine hq τ k G (fun u hu g => hψ.1.left u (show u ∈ leftSub V X Y T from Subgroup.mem_sup_left hu) g) (hψ.2.2.2 τ) _ ?_
  exact mul_mem (GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.uPart_le_levi D V m X Y T (hsu h)) hy

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCentre
end
