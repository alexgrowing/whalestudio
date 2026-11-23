import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTw
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NormalRepresentationLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingIntegralTwistPrimeEqDeepFiniteSumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EntriesWellDefined
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeClasses
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatNeZeroOfMemR
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUniqueCompletionMatrixOfRationalTwistAut
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

noncomputable section
namespace GlobalTheory.TwBridge.RepsOnto
open GlobalTheory.SymBridge GlobalTheory.TwBridge.MatGL

theorem val_unif {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ϖ : kˣ} (hϖ : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) : valuation k (ϖ : k) = uniformizer k := by
  apply le_antisymm
  · rw [le_uniformizer_iff]; exact (hϖ _).2 le_rfl
  · obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (uniformizer k)
    rw [← hx]
    exact (hϖ x).1 (by rw [hx]; exact uniformizer_lt_one)

theorem denseRange_toLoc {E k : Type} [Field E] [Field k] [TopologicalSpace k] {ι : E →+* k} (hι : DenseRange ι)
    {A B : Type} {a b : ℕ} (e : A ≃ Fin a) (e' : B ≃ Fin b) : DenseRange (toLoc ι e e') := by
  have h1 : DenseRange (Pi.map fun (_ : A) => Pi.map fun (_ : B) => (ι : E → k)) :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ => hι
  refine Dense.mono ?_ h1
  rintro _ ⟨M, rfl⟩
  refine ⟨Matrix.toLin' ((Matrix.of M).submatrix e.symm e'.symm), ?_⟩
  rw [toLoc_eq, LinearMap.toMatrix'_toLin']
  ext i l
  simp

open GlobalTheory.LatClass GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice in

theorem exists_bounded_rep : ∀ (R : Ranks) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν →
    ∀ j c (h : j + 1 + c = s) (g : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1 + 1)) k),
    (∃ r ∈ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1 + 1) 1,
      GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.IsNormalRep (W.T s R) W.ϖ j (c + 1) (by omega) (r * g)) →
    ∀ h' : GL (XIx (Fin R.k) (Fin R.t) (j + 1) ⊕ Fin (c + 1)) k,
    flat W.ψ ν ((W.T s R).mu (j + 1)) ((W.T s R).Phi j (c + 1) (by omega)) g h' ≠ 0 →
    ∃ g₁ : GL (XIx (Fin R.k) (Fin R.t) (j + 1) ⊕ Fin (c + 1)) k,
      DoubleCoset.mk (GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j + 1)) (c + 1) 1) ((W.T s R).lev (j + 1) (c + 1) (by omega)).J g₁ =
        DoubleCoset.mk (GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j + 1)) (c + 1) 1) ((W.T s R).lev (j + 1) (c + 1) (by omega)).J h' ∧
      ∀ κ ∈ ((W.T s R).lev (j + 1) (c + 1) (by omega)).J,
        latOf 1 ≤ latOf (g₁ * κ) ∧ ∀ y ∈ latOf (g₁ * κ), ((W.ϖ : k) ^ (j + 1)) • y ∈ latOf 1 := by
  intro R k _ _ _ _ s W _ _ ν hν j c h g hr h' hf
  haveI := hν.1
  have hϖ := val_unif W.unif
  have hb : ∀ j c h, latOf ((W.T s R).bas j c h) = latOf 1 := fun _ _ _ => rfl
  have H : (∀ j c h x, (W.T s R).Phi j c h x ≠ 0 → IntM x) ∧
      (∀ j c h x y, MaxM y → (W.T s R).Phi j c h (x + y) = (W.T s R).Phi j c h x) ∧
      ∀ j c h, ((W.T s R).lev j c h).J ≤ KO k _ :=
    GlobalTheory.Proof.TwistSupportPeriodicLevels.ofTwist_support_periodic_levels k s _ _ _ _ W.δ W.tame W.η _ _ (fun _ _ _ => rfl)
  obtain ⟨hs, hp, hJ⟩ := H
  obtain ⟨r, hr, e', z', he', hz', hl⟩ := hr
  rw [lat_bas hb, ← nfBasis_one] at hl
  obtain ⟨x₀, h0⟩ := Function.ne_iff.1 (GlobalTheory.FlatSourceStable.flat_ne_zero_of_mem_R k _ _ c W.ψ ν _ _ g h' hf r hr)
  obtain ⟨r₂, hr₂, e, z, he, hz, hl₂⟩ := step_normal (NormalForm.normalFormModN k) hϖ W.cond he' hz'
    (hl ▸ om_supp (hs _ _ _) (r * g) h') (hl ▸ om_per hϖ (hp _ _ _) (r * g) h') h0
  refine ⟨r₂ * h', ((DoubleCoset.eq _ _ _ _).2 ⟨r₂, hr₂, 1, one_mem _, (mul_one _).symm⟩).symm, fun κ hκ => ?_⟩
  rw [latOf_mul_congr _ (latOf_eq_of_KO (hJ _ _ _ hκ)), mul_one, hl₂]
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · rw [mem_latOf_one] at hy
    exact mem_normal.2 ⟨fun r => sub_mem (hy _) (mul_mem (hy _) (hz r)),
      fun i => pow_mono hϖ (he i).2 (mem_pow_zero.2 (hy _))⟩
  · obtain ⟨h1, h2⟩ := mem_normal.1 hy
    have h3 : ∀ i, (W.ϖ : k) ^ ((j + 1 : ℕ) : ℤ) * y (.inr i) ∈ 𝒪[k] := fun i =>
      mem_pow_zero.1 (zpow_mul_mem_pow.2 (pow_mono hϖ (by have := he i; omega) (h2 i)))
    have h4 : (W.ϖ : k) ^ ((j + 1 : ℕ) : ℤ) ∈ 𝒪[k] := mem_pow_zero.1 ((zpow_mem_pow hϖ).2 (by omega))
    rw [mem_latOf_one, ← zpow_natCast]
    rintro (r | i)
    · convert add_mem (mul_mem h4 (h1 r)) (mul_mem (h3 0) (hz r)) using 1
      simp only [Pi.smul_apply, smul_eq_mul]; ring
    · exact h3 i

theorem exists_toLocGL_mem : ∀ (E k : Type) [Field E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ι : E →+* k), DenseRange ι → ∀ (A : Type) [Fintype A] [DecidableEq A] (a : ℕ) (e : A ≃ Fin a) (U : Set (GL A k)),
    IsOpen U → U.Nonempty → ∃ γ : (Fin a → E) ≃ₗ[E] (Fin a → E), toLocGL ι e γ ∈ U := by
  intro E k _ _ _ _ _ ι hι A _ _ a e U hU ⟨g₀, hg₀⟩
  haveI : T2Space k := by
    let := IsTopologicalAddGroup.rightUniformSpace k
    have := isUniformAddGroup_of_addCommGroup (G := k)
    infer_instance
  have hS : IsOpen {M : Matrix A A k | M.det ≠ 0} := isOpen_ne_fun (continuous_id.matrix_det) continuous_const
  let F : {M : Matrix A A k | M.det ≠ 0} → GL A k := fun M => GeneralLinearGroup.mkOfDetNeZero M.1 M.2
  have hF : Continuous F := by
    refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
    have : (fun M => ((F M)⁻¹ : GL A k).val) = fun M => (M.1.det)⁻¹ • M.1.adjugate := by
      funext M
      rw [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv']
      rfl
    rw [this]
    exact ((continuous_subtype_val.matrix_det).inv₀ fun M => M.2).smul continuous_subtype_val.matrix_adjugate
  have hV := hS.isOpenMap_subtype_val _ (hU.preimage hF)
  have hne : (Subtype.val '' (F ⁻¹' U)).Nonempty := by
    refine ⟨_, ⟨g₀.val, g₀.det_ne_zero⟩, ?_, rfl⟩
    have : F ⟨g₀.val, g₀.det_ne_zero⟩ = g₀ := Units.ext rfl
    rw [Set.mem_preimage, this]
    exact hg₀
  obtain ⟨x, M, hM, hx⟩ := (denseRange_toLoc hι e e).exists_mem_open hV hne
  have hd : LinearMap.det x ≠ 0 := by
    intro h0
    have h1 := M.2
    rw [Set.mem_setOf_eq, hx, toLoc_eq, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_submatrix_equiv_self,
      LinearMap.det_toMatrix', h0, map_zero] at h1
    exact h1 rfl
  have hbij : Function.Bijective x := (Module.End.isUnit_iff x).1 ((LinearMap.isUnit_iff_isUnit_det x).2 hd.isUnit)
  refine ⟨LinearEquiv.ofBijective x hbij, ?_⟩
  have : toLocGL ι e (LinearEquiv.ofBijective x hbij) = F M := Units.ext hx.symm
  rw [this]
  exact hM

theorem exists_toLoc_ne_zero : ∀ (E k : Type) [Field E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ι : E →+* k), DenseRange ι → ∀ (A B : Type) [Fintype A] [Fintype B] (a b : ℕ) (e : A ≃ Fin a) (e' : B ≃ Fin b)
    (f : Matrix A B k → ℂ), IsLocallyConstant f → f ≠ 0 → ∃ x : (Fin b → E) →ₗ[E] (Fin a → E), f (toLoc ι e e' x) ≠ 0 := by
  intro E k _ _ _ _ _ ι hι A B _ _ a b e e' f hf hne
  exact (denseRange_toLoc hι e e').exists_mem_open (hf {z | z ≠ 0}) (Function.ne_iff.1 hne)

theorem toLoc_mulVec {E k : Type} [Field E] [Field k] (ι : E →+* k) {A : Type} [Fintype A] {a : ℕ} (e : A ≃ Fin a)
    (x : (Fin a → E) →ₗ[E] (Fin a → E)) (y : Fin a → E) :
    (toLoc ι e e x *ᵥ fun i => ι (y (e i))) = fun i => ι (x y (e i)) := by
  funext i
  rw [toLoc_eq, ← LinearMap.toMatrix'_mulVec]
  simp only [mulVec, dotProduct, map_sum, map_mul, map_apply, submatrix_apply]
  exact Equiv.sum_comp e fun l => ι (LinearMap.toMatrix' x (e i) l) * ι (y l)

theorem bounds_of_isGL : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (P : HeightOneSpectrum (𝓞 X.E)) (k : Type) [Field k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (ϖ : kˣ),
    IsCompl P (qOf P) ι ϖ → P ∉ Pr.vGs → ∀ (j c n : ℕ) (γ : AutY X R j) (g' : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin c) k),
    IsGL ι γ g' → latOf 1 ≤ latOf g' → (∀ y ∈ latOf g', ((ϖ : k) ^ n) • y ∈ latOf 1) →
    ∀ x ∈ lamYat (Pr := Pr) (R := R) j P, γ⁻¹ x ∈ lamYat (Pr := Pr) (R := R) j P ∧
      ((qOf P : X.E) ^ n) • γ x ∈ lamYat (Pr := Pr) (R := R) j P := by
  intro X Pr R P k _ _ _ _ ι ϖ hC hP j c n γ g' ⟨e, _, hg⟩ h1 h2 x hx
  have hmem : ∀ y, y ∈ lamYat (Pr := Pr) (R := R) j P ↔ (fun i => ι (y (e i))) ∈ latOf (1 : GL _ k) := fun y => by
    unfold lamYat LocE.lamY LocE.sclLat stdAt
    rw [if_neg hP, Submodule.mem_comap, mem_localization_standardLattice, mem_latOf_one]
    simp only [hC.int]
    rw [e.surjective.forall]
    simp [LocE.scE]
  obtain rfl : g' = toLocGL ι e γ := Units.ext hg
  rw [hmem] at hx
  refine ⟨(hmem _).2 (mem_latOf_one.2 ?_), (hmem _).2 ?_⟩
  · have h3 : ∀ i, (toLoc ι e e γ.symm.toLinearMap *ᵥ fun i => ι (x (e i))) i ∈ 𝒪[k] := h1 hx
    rw [toLoc_mulVec] at h3
    exact h3
  · have h3 : (toLocGL ι e γ).val *ᵥ (fun i => ι (x (e i))) ∈ latOf (toLocGL ι e γ * 1) := (mulVec_mem_latOf _).2 hx
    rw [mul_one] at h3
    have h4 := h2 _ h3
    change (ϖ : k) ^ n • (toLoc ι e e γ.toLinearMap *ᵥ fun i => ι (x (e i))) ∈ _ at h4
    rw [toLoc_mulVec, hC.unif] at h4
    convert h4 using 1
    funext i
    simp

theorem ordX_exists (R : Ranks) (j : ℕ) : ∃ e : XIx (Fin R.k) (Fin R.t) j ≃ Fin (R.N j), IsOrd xPos e := by
  have hN : R.k + j + j * R.t + 0 = R.N j := by simp only [Ranks.N]; ring
  refine ⟨(Equiv.sumEmpty _ (Fin 0)).symm.trans (ordY R.k R.t j 0 _ hN), fun a => ?_⟩
  have := ordY_isOrd R.k R.t j 0 _ hN (Sum.inl a)
  simpa [yPos] using this

end GlobalTheory.TwBridge.RepsOnto

open GlobalTheory.TwBridge.RepsOnto GlobalTheory.SymBridge GlobalTheory.TwBridge.MatGL in

theorem GlobalTheory.TwBridge.repsOnto : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → ∀ j c (h : j + 1 + c = s) (al : L.β j) (g : GL (XIx (Fin R.k) (Fin R.t) (j) ⊕ Fin (c + 1 + 1)) k), IsGL ι (L.h j al P) g → (∃ r ∈ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j)) (c + 1 + 1) 1, GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.IsNormalRep (W.T s R) W.ϖ j (c + 1) (by omega) (r * g)) → ∀ h' : GL (XIx (Fin R.k) (Fin R.t) (j + 1) ⊕ Fin (c + 1)) k, flat W.ψ ν ((W.T s R).mu (j + 1)) ((W.T s R).Phi j (c + 1) (by omega)) g h' ≠ 0 → ∃ γ : AutY X R (j + 1), (∃ g' : GL (XIx (Fin R.k) (Fin R.t) (j + 1) ⊕ Fin (c + 1)) k, IsGL ι γ g' ∧ DoubleCoset.mk (GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j + 1)) (c + 1) 1) ((W.T s R).lev (j + 1) (c + 1) (by omega)).J g' = DoubleCoset.mk (GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j + 1)) (c + 1) 1) ((W.T s R).lev (j + 1) (c + 1) (by omega)).J h') ∧ (∀ x ∈ lamYat (Pr := Pr) (R := R) (j + 1) P.1, γ⁻¹ x ∈ lamYat (Pr := Pr) (R := R) (j + 1) P.1 ∧ ((qOf P.1 : X.E) ^ (j + 1)) • γ x ∈ lamYat (Pr := Pr) (R := R) (j + 1) P.1) ∧ FiniteSumNonzeroLargeDepth Ch sel mu cst j P (L.h j al P) γ := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hν hc hA L G hL hI j c h al g hg hr h' hf
  haveI : ν.IsAddHaarMeasure := hν.1
  obtain ⟨g₁, hdc, hbd⟩ := exists_bounded_rep R k s W ν hν j c h g hr h' hf
  set J := ((W.T s R).lev (j + 1) (c + 1) (by omega)).J with hJ
  have hreg : (W.T s R).Regular := GlobalTheory.StepData.Chain.ofTwist_regular _ _ _ _ _
  have hlaws : (W.T s R).Laws := GlobalTheory.StepData.Chain.ofTwist_laws _ _ _ W.unr _ _
  have hJo := (hreg.2.2 (j + 1) (c + 1) (by omega)).1
  have hm := hA.steps
  have hN : R.k + (j + 1) + (j + 1) * R.t + (c + 1) = R.N (j + 1) + cOf R (j + 1) := by
    have e2 : R.N (j + 1) = R.k + (j + 1) + (j + 1) * R.t := by simp only [Ranks.N]; ring
    rw [e2]; simp only [cOf]; rw [hm]; omega
  have ho : IsOrdY (ordY R.k R.t (j + 1) (c + 1) _ hN) := by
    have := ordY_isOrd R.k R.t (j + 1) (c + 1) _ hN
    have e2 : R.k + (j + 1) + (j + 1) * R.t = R.N (j + 1) := by simp only [Ranks.N]; ring
    rwa [e2] at this
  obtain ⟨γ, hγ⟩ := exists_toLocGL_mem X.E k ι hA.compl.dense _ _ (ordY R.k R.t (j + 1) (c + 1) _ hN)
    {x | g₁⁻¹ * x ∈ J} (hJo.preimage (continuous_const.mul continuous_id)) ⟨g₁, by simp [J.one_mem]⟩
  set g' := toLocGL ι (ordY R.k R.t (j + 1) (c + 1) _ hN) γ with hg'
  have hgl : IsGL ι γ g' := ⟨_, ho, rfl⟩
  have hκ : g₁⁻¹ * g' ∈ J := hγ
  have hdc' : DoubleCoset.mk (GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j + 1)) (c + 1) 1) J g' =
      DoubleCoset.mk (GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j + 1)) (c + 1) 1) J h' := by
    rw [← hdc]
    exact (DoubleCoset.eq _ _ _ _).2 ⟨1, one_mem _, (g₁⁻¹ * g')⁻¹, inv_mem hκ, by group⟩
  obtain ⟨hb1, hb2⟩ := hbd _ hκ
  rw [mul_inv_cancel_left] at hb1 hb2
  have hbd' := bounds_of_isGL X Pr R P.1 k ι W.ϖ hA.compl hA.nmem (j + 1) (c + 1) (j + 1) γ g' hgl hb1 hb2
  refine ⟨γ, ⟨g', hgl, hdc'⟩, hbd', ?_⟩
  have hfl : flat W.ψ ν ((W.T s R).mu (j + 1)) ((W.T s R).Phi j (c + 1) (by omega)) g g' ≠ 0 := by
    have hT := hlaws.1 j (c + 1) (by omega)
    exact (GlobalTheory.UnfoldedEntries.flat_ne_zero_congr (by omega) hT rfl hdc'.symm).1 hf
  have hSB := GlobalTheory.RootEx.opE_mem_SB 1 W.ψ ν (GlobalTheory.SplitWeil.om_mem_SB ((W.T s R).mu (j + 1)) g g'
    (hreg.1 j (c + 1) (by omega)))
  obtain ⟨e', he'⟩ := ordX_exists R j
  obtain ⟨e, he⟩ := ordX_exists R (j + 1)
  obtain ⟨x, hx⟩ := exists_toLoc_ne_zero X.E k ι hA.compl.dense _ _ _ _ e e'
    (flat W.ψ ν ((W.T s R).mu (j + 1)) ((W.T s R).Phi j (c + 1) (by omega)) g g') hSB.1 hfl
  obtain ⟨A₀, B₀, hAB⟩ := GlobalTheory.T.unfoldingIntegral_twistPrime_eq_deep_finite_sum X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hc hA j c h (L.h j al P) γ g g' hg hgl
    (hL.boundQ j al P hA.nmem) hbd' (hL.depthQ' P hA.nmem)
  refine ⟨A₀, B₀, fun A' B' h1 h2 hz => hx ?_⟩
  rw [hAB A' B' h1 h2 e' e he' he x]
  have := congrFun hz x
  simp only [Pi.zero_apply] at this
  rw [this, map_zero, mul_zero]
