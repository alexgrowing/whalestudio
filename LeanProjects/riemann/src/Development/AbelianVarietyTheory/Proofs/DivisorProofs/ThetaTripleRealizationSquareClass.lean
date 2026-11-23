import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlipAtEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNatDatumSquareFlip
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrientedHermitianFormQuadSumEqTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNegConjMemberHermitianLatticeSpaceData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomSuppSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticSelfZeroSplitSupported
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruhStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityTensorModelVWStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPartialFourierColumnBlockSchwartzBruhatStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PartialFourierSumInverseOfLatticeDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorSymplecticFormAtSplitFinitePlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorIsotropicTranslationCharSplitStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlaceIsoReadingComponentsCharactersStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMixedLagrangianChartIntegralRowChangeStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf At piW psiLoc)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.MixCompare

open GlobalTheory.FlipMatch

section Pair

variable {k k' A C A' C' : Type} [Fintype A] [Fintype C]

theorem pairM_comm [CommRing k] (X Y : Matrix A C k) : pairM X Y = pairM Y X := by
  simp only [pairM, mul_comm]

theorem pairM_add_left [CommRing k] (X X' Y : Matrix A C k) : pairM (X + X') Y = pairM X Y + pairM X' Y := by
  simp only [pairM, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem pairM_smul_right [CommRing k] (c : k) (X Y : Matrix A C k) : pairM X (c • Y) = c * pairM X Y := by
  simp only [pairM, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]

theorem pairM_eq_zero [CommRing k] {P : Finset C} {X Y : Matrix A C k} (hX : ∀ r, ∀ s ∈ P, X r s = 0)
    (hY : ∀ r, ∀ s ∉ P, Y r s = 0) : pairM X Y = 0 :=
  Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun s _ => by
    by_cases h : s ∈ P
    · rw [hX r s h, zero_mul]
    · rw [hY r s h, mul_zero]

theorem pairM_eq_trace [CommRing k] (X Y : Matrix A C k) : pairM X Y = (X * Yᵀ).trace := by
  simp [pairM, trace, Matrix.mul_apply]

variable [Field k] [Field k'] [DecidableEq A] [DecidableEq C] [Fintype A'] [Fintype C'] (j : k ≃+* k') (eA : A ≃ A') (eC : C ≃ C')
  (g : GL A k') (h : GL C k')

theorem pairM_chart (X Y : Matrix A C k) :
    pairM (chart j eA eC g h X) (chart j eA eC (invT g) (invT h) Y) = j (pairM X Y) := by
  have e1 : ∀ M N : Matrix A C k', pairM (reindex eA eC M) (reindex eA eC N) = pairM M N := fun M N => by
    unfold pairM
    rw [← eA.sum_comp]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← eC.sum_comp]
    simp
  have e2 : j (pairM X Y) = pairM (X.map j) (Y.map j) := by simp [pairM]
  rw [chart, chart, e1, e2, pairM_eq_trace, pairM_eq_trace, invT_val, invT_val, transpose_mul, transpose_mul,
    transpose_transpose, transpose_transpose, Matrix.mul_assoc (g.val * _), ← Matrix.mul_assoc h.val, Units.mul_inv,
    Matrix.one_mul, ← Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

omit [Fintype A'] [Fintype C'] in
theorem chart_add (X Y : Matrix A C k) : chart j eA eC g h (X + Y) = chart j eA eC g h X + chart j eA eC g h Y := by
  rw [chart, chart, chart, Matrix.map_add _ (map_add j), Matrix.mul_add, Matrix.add_mul]
  rfl

omit [Fintype A'] [Fintype C'] in

theorem exists_homeo [TopologicalSpace k] [TopologicalSpace k'] [IsTopologicalRing k'] (h1 : Continuous j) (h2 : Continuous j.symm) :
    ∃ Θ : Matrix A C k ≃ₜ Matrix A' C' k', ∀ X, Θ X = chart j eA eC g h X :=
  ⟨{ toFun := chart j eA eC g h
     invFun := fun Z => ((g⁻¹).val * Z.submatrix eA eC * (h⁻¹).val).map j.symm
     left_inv := fun X => by
      simp only [chart, reindex_apply, submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id]
      rw [Matrix.mul_assoc g.val, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      ext; simp
     right_inv := fun Z => by
      have : ∀ M : Matrix A C k', (M.map j.symm).map j = M := fun M => by ext; simp
      simp only [chart, this]
      rw [Matrix.mul_assoc (g⁻¹).val, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      simp
     continuous_toFun := ((continuous_const.matrix_mul (continuous_id.matrix_map h1)).matrix_mul continuous_const).matrix_reindex _ _
     continuous_invFun := ((continuous_const.matrix_mul (continuous_id.matrix_submatrix _ _)).matrix_mul
        continuous_const).matrix_map h2 }, fun _ => rfl⟩

end Pair

theorem bijOn_funLeft {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (Θ : X ≃ₜ Y) :
    Set.BijOn (LinearMap.funLeft ℂ ℂ Θ.symm) (GlobalTheory.WeilM.SB X : Set _) (GlobalTheory.WeilM.SB Y : Set _) := by
  have key : ∀ {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (Θ : X ≃ₜ Y), ∀ f ∈ GlobalTheory.WeilM.SB Y, f ∘ Θ ∈ GlobalTheory.WeilM.SB X :=
    fun Θ f hf => ⟨hf.1.comp_continuous Θ.continuous, hf.2.comp_homeomorph Θ⟩
  refine ⟨fun f hf => key Θ.symm f hf, fun f _ f' _ e => funext fun x => ?_, fun f hf => ⟨f ∘ Θ, key Θ f hf, ?_⟩⟩
  · simpa [LinearMap.funLeft_apply] using congrFun e (Θ x)
  · funext y; simp [LinearMap.funLeft_apply]

section Mix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {Y : Spc F E d} {M : Model σ X Y} {ψ : AddChar (AF F) ℂ} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F}

theorem exists_mixed {k R C : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C] {ψ₀ : AddChar k Circle} {ϖ : kˣ} (hϖ : IsUnif ϖ)
    (hψ : HasConductor ψ₀ 1) {j : Fv F v ≃+* k} (hj : IsLocIso j) {κ : k} (hκ : κ ≠ 0) {χ : Fv F v → ℂ}
    (hχ : ∀ x, χ x = ψ₀ (κ * j x)) {eA : Fin n ≃ R} {eC : Fin d ≃ C} {g h} {P : Finset C} {A A' co}
    {a b : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) → Matrix (Fin n) (Fin d) (Fv F v)}
    (hc : IsMixChart v A A' co (fun u => chart j eA eC g h (a u)) (fun u => κ • chart j eA eC (invT g) (invT h) (b u)) P)
    {ι₀ : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)}
    (hb : Set.BijOn ι₀ (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v) : Set _) (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _))
    (ha : ∀ u, At (evFin F v) u → pairM (a u) (b u) = 0 → ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ₁ ∈ GlobalTheory.WeilM.SB _,
      Acts (evFin F v) (M.co.rho ψ u) φ φ₁ → ∀ Z, ι₀ φ₁ Z = χ (pairM Z (b u)) * ι₀ φ (Z + a u))
    (hs : ∀ x u, At (evFin F v) x → At (evFin F v) u →
      ψ (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) x u) =
        χ (pairM (a x) (b u) - pairM (b x) (a u))) :
    ∃ ι, IsLagrModel M ψ v A A' co ι ∧ ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ m, IsNatDatum ϖ m (ι φ) →
      ι₀ φ = fun Z => fourierSum ψ₀⁻¹ ϖ m P (ι φ) (chart j eA eC g h Z) := by
  obtain ⟨𝓕, f1, f2, f3, f4⟩ := GlobalTheory.T.exists_partialFourier_columnBlock_schwartzBruhat k R C ψ₀ ϖ P hϖ hψ
  obtain ⟨Θ, hΘ⟩ := exists_homeo j eA eC g h hj.1 hj.2.1
  let ι₁ := LinearMap.funLeft ℂ ℂ Θ.symm ∘ₗ ι₀
  have b1 : Set.BijOn ι₁ (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v) : Set _) (GlobalTheory.WeilM.SB (Matrix R C k) : Set _) := (bijOn_funLeft Θ).comp hb
  have e1 : ∀ φ Z, ι₁ φ (chart j eA eC g h Z) = ι₀ φ Z := fun φ Z => by
    rw [← hΘ]; exact congrArg (ι₀ φ) (Θ.symm_apply_apply Z)
  have pc : ∀ Z Z', pairM (chart j eA eC g h Z) (κ • chart j eA eC (invT g) (invT h) Z') = κ * j (pairM Z Z') := fun Z Z' => by
    rw [pairM_smul_right, pairM_chart]
  have act : ∀ u, At (evFin F v) u → pairM (chart j eA eC g h (a u)) (κ • chart j eA eC (invT g) (invT h) (b u)) = 0 →
      ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ₁ ∈ GlobalTheory.WeilM.SB _, Acts (evFin F v) (M.co.rho ψ u) φ φ₁ →
      ι₁ φ₁ = fun S => (ψ₀ (pairM S (κ • chart j eA eC (invT g) (invT h) (b u))) : ℂ) * ι₁ φ (S + chart j eA eC g h (a u)) := by
    intro u hu h0 φ hφ φ₁ h₁ hact
    funext S
    obtain ⟨Z, rfl⟩ := Θ.surjective S
    rw [pc, mul_eq_zero, map_eq_zero] at h0
    rw [hΘ, ← chart_add, e1, e1, pc, ← hχ]
    exact ha u hu (h0.resolve_left hκ) φ hφ φ₁ h₁ hact Z
  refine ⟨𝓕 ∘ₗ ι₁, ⟨f1.comp b1, fun u hu φ hφ φ₁ h₁ hact z => ?_, fun u hu φ hφ φ₁ h₁ hact x hx => ?_⟩, fun φ hφ m hm => ?_⟩
  · obtain ⟨c1, c2, c3, c4⟩ := hc.1 u hu
    rw [LinearMap.comp_apply, act u c1 (pairM_eq_zero c2 c3) φ hφ φ₁ h₁ hact, f2 _ (b1.1 hφ) _ _ c2 c3, c4]
    rfl
  · obtain ⟨c1, c2, c3⟩ := hc.2 u hu
    obtain ⟨d1, d2, d3, d4⟩ := hc.1 x hx
    rw [LinearMap.comp_apply, act u c1 ((pairM_comm _ _).trans (pairM_eq_zero c3 c2)) φ hφ φ₁ h₁ hact, f3 _ (b1.1 hφ) _ _ c2 c3,
      hs x u d1 c1, hχ, map_sub, mul_sub, ← pc, pairM_comm (b x), ← pc, d4]
    beta_reduce
    rw [pairM_add_left, pairM_add_left, pairM_eq_zero d2 c2, pairM_comm (κ • _) (κ • _), pairM_eq_zero c3 d3, add_zero, zero_add,
      pairM_comm _ (κ • chart j eA eC (invT g) (invT h) (b x))]
    rfl
  · funext Z
    rw [LinearMap.comp_apply, f4 _ (b1.1 hφ) m hm, e1]

end Mix

theorem mem_SB_of_isNatDatum {k A C : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Fintype A] [Fintype C] {ϖ : kˣ} {n : ℕ} {Φ : Matrix A C k → ℂ} (h : IsNatDatum ϖ n Φ) : Φ ∈ GlobalTheory.WeilM.SB (Matrix A C k) := by
  have h0 : 0 < ValuativeRel.valuation k ((ϖ ^ n : kˣ) : k) := zero_lt_iff.2 (by simp)
  refine ⟨(IsLocallyConstant.iff_exists_open Φ).2 fun x =>
      ⟨{x' | ∀ r s, (x' - x) r s / ((ϖ ^ n : kˣ) : k) ∈ (ValuativeRel.valuation k).integer}, ?_, fun r s => by simp,
      fun x' hx' => ?_⟩,
    HasCompactSupport.intro (GlobalTheory.SplitFlip.isCompact_intMatrix (k := k) (m := A) (n := C))
      fun x hx => h.1 x fun hm => hx (mem_matLat_stdLat.1 hm)⟩
  · simp only [Set.ofPred_forall]
    refine isOpen_iInter_of_finite fun r => isOpen_iInter_of_finite fun s => ?_
    exact IsOpen.preimage (f := fun x' : Matrix A C k => (x' - x) r s / ((ϖ ^ n : kˣ) : k)) (by fun_prop) Valuation.isOpen_integer
  · rw [← h.2 x (x' - x), add_sub_cancel]
    classical
    refine GlobalTheory.SplitFlip.FourierDepth.mem_matLat_smul_stdLat.2 fun r s => ?_
    have := hx' r s
    rwa [Valuation.mem_integer_iff, map_div₀, div_le_one₀ h0] at this

section Grid

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}

theorem det_skewGram_ne (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram A B e).det ≠ 0 := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram, det_smul, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, det_reindex_self, det_fromBlocks_zero₂₁, det_transpose, det_transpose]
  exact mul_ne_zero (pow_ne_zero _ GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero)
    (mul_ne_zero (GlobalTheory.RouteCoords.gram_det_ne A) (GlobalTheory.RouteCoords.gram_det_ne B))

end Grid

section Shape

open GlobalTheory.WeilM
open scoped GlobalTheory.VacAny
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (tens AE cA incM)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem eq_of_tens_eq {κ : Type} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (R : (κ → AF F) → ℂ)
    (hR0 : R 0 ≠ 0) (hinv : ∀ x z, At (evFin F v) z → R (x + z) = R x) (φ₁ φ₂ : (κ → Fv F v) → ℂ)
    (h : tens (evFin F v) φ₁ R = tens (evFin F v) φ₂ R) : φ₁ = φ₂ := by
  funext y
  have hz : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (y i)) := by
    intro u hu
    funext i
    exact GlobalTheory.LatVac.at_liftV v _ u hu
  have e := congrFun h (fun i => GlobalTheory.LatVac.liftV v (y i))
  have hR : R (fun i => GlobalTheory.LatVac.liftV v (y i)) = R 0 := by simpa using hinv 0 _ hz
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, hR] at e
  exact mul_right_cancel₀ hR0 e

theorem tens_add_smul {κ : Type} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (R : (κ → AF F) → ℂ) (x y : (κ → Fv F v) → ℂ) (c : ℂ) :
    tens (evFin F v) (c • x + y) R = c • tens (evFin F v) x R + tens (evFin F v) y R := by
  funext z
  simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem exists_comps (hcm : IsCMExt F E σ) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (t : E →ₐ[F] Fv F v) {m n : Type}
    (P Q : Matrix m n (Fv F v)) :
    ∃ u : Matrix m n (AE F E), At (evFin F v) u ∧ u.map (piW t) = P ∧ u.map (piW (t.comp σ)) = Q :=
  ⟨Matrix.of fun r s => GlobalTheory.SplitGLLift.liftPair hcm t (P r s, Q r s),
    fun a ha => Matrix.ext fun _ _ => GlobalTheory.SplitGLLift.at_liftPair hcm t _ a ha,
    Matrix.ext fun _ _ => GlobalTheory.SplitGLLift.piW_liftPair hcm t _,
    Matrix.ext fun _ _ => GlobalTheory.SplitGLLift.piW_comp_liftPair hcm t _⟩

theorem linForm_eq {K : Type} [Field K] {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (l : Matrix m n K →ₗ[K] K) (Y : Matrix m n K) : l Y = pairM Y (Matrix.of fun k j => l (Matrix.single k j 1)) := by
  conv_lhs => rw [Y.matrix_eq_sum_single]
  simp only [map_sum, pairM]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show Matrix.single k j (Y k j) = Y k j • Matrix.single k j (1 : K) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul, Matrix.of_apply]

theorem isUnit_det_map {K : Type} [Field K] [Algebra F K] (t : E →ₐ[F] K) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : J.det ≠ 0) :
    IsUnit (J.map t).det := by
  have e : (J.map t).det = t J.det := by rw [AlgHom.map_det]; rfl
  rw [e, isUnit_iff_ne_zero]
  exact (_root_.map_ne_zero _).2 hJ

variable {a a' : ℕ} {B : Base F E} {G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

set_option maxHeartbeats 1000000 in

theorem exists_right_translate (hT : IsTriple B G X om om') (dV : G.V.J.det ≠ 0) (dW : G.W.J.det ≠ 0)
    {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (t : E →ₐ[F] Fv F v) (b : GL (Fin a) (Fv F v)) (c : GL (Fin (a + a')) (Fv F v)) {ι}
    (hι : G.M.IsLinW B.ψ t b c ι) {h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v))
    {k : GL (Fin (a + a')) (Fv F v)} (hk : (mat h).map (piW t) = k.val) :
    ∃ c' : ℂ, c' ≠ 0 ∧ ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), ∃ φ₃ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₃ ∧ ∀ Z, ι φ₃ Z = c' * ι φ (Z * (invT (c⁻¹ * k * c)).val) := by
  have hcm := hT.base.cm
  have hstd := hT.base.std
  choose! S hSB hS using GlobalTheory.T.weilRepresentationLocality_tensorModelVW B G X om om' hT v h hh
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (Fin a × Fin (a + a')) v
  have hinv := (hR 0 (Submodule.zero_mem _)).1
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil
  have hlin : ∀ x ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), ∀ y ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), ∀ r : ℂ,
      S (r • x + y) = r • S x + S y := by
    intro x hx y hy r
    have hz : r • x + y ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v) := add_mem (Submodule.smul_mem _ r hx) hy
    apply eq_of_tens_eq v R hR0 hinv
    rw [← hS _ hz R (hR _ hz), tens_add_smul, map_add, map_smul, hS x hx R (hR x hx), hS y hy R (hR y hy), ← tens_add_smul]
  have hsb := fun (u : Matrix (Fin a) (Fin (a + a')) (AE F E)) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) (hφ : φ ∈ GlobalTheory.WeilM.SB _) =>
    GlobalTheory.SchrSB.schr_mem_SB B.ψ hstd.1 v (GlobalTheory.LatVac.locCo G.M.co v u) φ hφ
  have hbr := GlobalTheory.VacBridge.rho_acts_locCo G.M.co B.ψ v
  have hat : ∀ u : Matrix (Fin a) (Fin (a + a')) (AE F E), At (evFin F v) u → At (evFin F v) (u * (mat h)ᵀ) := by
    intro u hu r hr
    rw [← Matrix.smul_mul, hu r hr, Matrix.zero_mul]
  have hcomm : ∀ u : Matrix (Fin a) (Fin (a + a')) (AE F E), At (evFin F v) u → ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v),
      S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v u) φ) =
        schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v (u * (mat h)ᵀ)) (S φ) := by
    intro u hu φ hφ
    have hact : actAB (cA σ) ((1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.V.J), h) u = u * (mat h)ᵀ := by simp [actAB, mat]
    apply eq_of_tens_eq v R hR0 hinv
    rw [← hS _ (hsb u φ hφ) R (hR _ (hsb u φ hφ)), ← hbr u hu φ R (hR φ hφ), hW.impl (1, h) u _ (hR φ hφ).2,
      hS φ hφ R (hR φ hφ), hact]
    exact hbr _ (hat u hu) (S φ) R (hR _ (hSB φ hφ))
  have Heisenberg₂ : ∀ u : Matrix (Fin a) (Fin (a + a')) (AE F E), At (evFin F v) u →
      pairM (coX t b c u) (coY σ G.V G.W t b c u) = 0 → ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), ∀ Z,
      ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v u) φ) Z =
        GlobalTheory.LatVac.psiAt B.ψ v (pairM Z (coY σ G.V G.W t b c u)) * ι φ (Z + coX t b c u) := fun u hu h0 φ hφ =>
    (GlobalTheory.T.heisenbergOperator_isotropic_translation_char_split hcm G.V G.W hT.geo.hV.herm hT.geo.hW.skew dV dW G.M B.ψ hstd t b c u hu h0 φ hφ _ (hsb u φ hφ)
      (hbr u hu φ)).1 ι hι
  set H : GL (Fin (a + a')) (Fv F v) := c⁻¹ * k * c with hH
  have uV := isUnit_det_map t dV
  have uW : IsUnit (G.W.J.map t)ᵀ.det := by rw [det_transpose]; exact isUnit_det_map t dW
  have eX : ∀ u : Matrix (Fin a) (Fin (a + a')) (AE F E), coX t b c (u * (mat h)ᵀ) = coX t b c u * H.valᵀ := by
    intro u
    rw [coX, coX, Matrix.map_mul, Matrix.transpose_map, hk, hH, Units.val_mul, Units.val_mul]
    simp only [Matrix.mul_assoc, ← transpose_mul, Units.mul_inv, Matrix.mul_one]
  have hunit : ((mat h).map (piW (t.comp σ)))ᵀ * (G.W.J.map t)ᵀ = (G.W.J.map t)ᵀ * (k⁻¹).val := by
    have hu : (mat h)ᵀ * incM F G.W.J * (mat h).map (cA σ) = incM F G.W.J := h.2
    have e := congrArg (fun M => (M.map (piW t))ᵀ) hu
    have hJ : (incM F G.W.J).map (piW t) = G.W.J.map t := Matrix.ext fun r s => GlobalTheory.SplitGLLift.piW_inclR t (G.W.J r s)
    have hc : ((mat h).map (cA σ)).map (piW t) = (mat h).map (piW (t.comp σ)) :=
      Matrix.ext fun r s => by
        simp only [Matrix.map_apply]
        rw [GlobalTheory.VacIso.piW_cA]
    simp only [Matrix.map_mul, hJ, hc, Matrix.transpose_map, hk, transpose_mul, transpose_transpose] at e
    conv_rhs => rw [← e]
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have eY : ∀ u : Matrix (Fin a) (Fin (a + a')) (AE F E),
      coY σ G.V G.W t b c (u * (mat h)ᵀ) = coY σ G.V G.W t b c u * (H⁻¹).val := by
    intro u
    have : H⁻¹ = c⁻¹ * k⁻¹ * c := by rw [hH]; group
    rw [coY, coY, Matrix.map_mul, Matrix.transpose_map, this, Units.val_mul, Units.val_mul, Matrix.neg_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc _ (G.W.J.map t)ᵀ, hunit, ← Matrix.mul_assoc c.val, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc]
  have exT : ∀ C, ∃ u : Matrix (Fin a) (Fin (a + a')) (AE F E), At (evFin F v) u ∧ coX t b c u = C ∧
      coY σ G.V G.W t b c u = 0 := fun C => by
    obtain ⟨u, h1, h2, h3⟩ := exists_comps hcm t (b.val * C * c.valᵀ) 0
    refine ⟨u, h1, ?_, by simp [coY, h3]⟩
    rw [coX, h2]
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, ← transpose_mul, Units.inv_mul, transpose_one, Matrix.mul_one]
  have exM : ∀ C, ∃ u : Matrix (Fin a) (Fin (a + a')) (AE F E), At (evFin F v) u ∧ coX t b c u = 0 ∧
      coY σ G.V G.W t b c u = C := fun C => by
    obtain ⟨u, h1, h2, h3⟩ := exists_comps hcm t 0
      (-((G.V.J.map t)⁻¹ * ((b⁻¹).valᵀ * C * (c⁻¹).val) * ((G.W.J.map t)ᵀ)⁻¹))
    refine ⟨u, h1, by simp [coX, h2], ?_⟩
    rw [coY, h3]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ uV, Matrix.nonsing_inv_mul_cancel_left _ _ uW, Units.inv_mul, Matrix.mul_one,
      ← Matrix.mul_assoc, ← transpose_mul, Units.inv_mul, transpose_one, Matrix.one_mul]
  choose uT t1 t2 t3 using exT
  choose uM m1 m2 m3 using exM
  have p0 : ∀ Z : Matrix (Fin a) (Fin (a + a')) (Fv F v), pairM Z 0 = 0 := fun Z => by simp [pairM]
  have p1 : ∀ Z : Matrix (Fin a) (Fin (a + a')) (Fv F v), pairM 0 Z = 0 := fun Z => by simp [pairM]
  obtain ⟨c', hc'⟩ := GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat (GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v)) (GlobalTheory.LatVac.psiAt B.ψ v)
    (GlobalTheory.SchrSB.continuous_psiAt _ hstd.1 _) (GlobalTheory.PsiNontriv.psiAt_ne_one _ hstd _) ι (fun x Y => ι (S x) (Y * H.valᵀ)) hι.bij
    (fun x hx y hy r => by funext Y; simp only [hlin x hx y hy r, map_add, map_smul, Pi.add_apply, Pi.smul_apply])
    (fun C => schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v (uT C)))
    (fun l => schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v (uM (Matrix.of fun k j => l (Matrix.single k j 1)))))
    (fun C x hx => ⟨hsb _ x hx, funext fun Y => by
        rw [Heisenberg₂ _ (t1 C) (by rw [t3, p0]) x hx, t2, t3, p0, AddChar.map_zero_eq_one, one_mul], funext fun Y => by
        beta_reduce
        rw [hcomm _ (t1 C) x hx, Heisenberg₂ _ (hat _ (t1 C)) (by rw [eY, t3, Matrix.zero_mul, p0]) _ (hSB x hx), eX, eY, t2, t3,
          Matrix.zero_mul, p0, AddChar.map_zero_eq_one, one_mul, Matrix.add_mul]⟩)
    (fun l x hx => ⟨hsb _ x hx, funext fun Y => by
        rw [Heisenberg₂ _ (m1 _) (by rw [m2, p1]) x hx, m2, m3, add_zero, ← linForm_eq], funext fun Y => by
        beta_reduce
        rw [hcomm _ (m1 _) x hx, Heisenberg₂ _ (hat _ (m1 _)) (by rw [eX, m2, Matrix.zero_mul, p1]) _ (hSB x hx), eX, eY, m2, m3,
          Matrix.zero_mul, add_zero, linForm_eq l Y, pairM_eq_trace, pairM_eq_trace, transpose_mul, Matrix.mul_assoc,
          ← Matrix.mul_assoc H.valᵀ, ← transpose_mul, Units.inv_mul, transpose_one, Matrix.one_mul]⟩)
  have key : ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), ∀ Z, ι (S φ) Z = c' * ι φ (Z * (invT H).val) := fun φ hφ Z => by
    have e := congrFun (hc' φ hφ) (Z * (invT H).val)
    rwa [invT_val, Matrix.mul_assoc, ← transpose_mul, Units.mul_inv, transpose_one, Matrix.mul_one] at e
  refine ⟨c', fun h0 => ?_, fun φ hφ => ⟨S φ, hSB φ hφ, hS φ hφ, key φ hφ⟩⟩
  obtain ⟨v1, v2, -⟩ := hT.geo.hM.vac v
  have e1 : S (G.M.vac v) = 0 := hι.bij.injOn (hSB _ v1) (Submodule.zero_mem _) (by
    funext Z; rw [key _ v1, h0, zero_mul, map_zero]; rfl)
  have e2 := hS _ v1 R (hR _ v1)
  have z : tens (evFin F v) (0 : (Fin a × Fin (a + a') → Fv F v) → ℂ) R = 0 := funext fun _ => zero_mul _
  have e3 := congrArg (om (1, h)⁻¹) e2
  rw [e1, z, map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, ← z] at e3
  exact v2 (eq_of_tens_eq v R hR0 hinv _ _ e3)

end Shape

section Lift

variable {D : D7}

theorem exists_lift (hcm : IsCMExt D.host.F D.host.E D.sp.cm.sig) (V : HSp D) {v : Pl D.host.F}
    (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (K : GL (Fin V.rank) (Fv D.host.F v)) :
    ∃ g : GA D V, At (evFin D.host.F v) (mt V g - 1) ∧ (mt V g).map (piW τ) = K.val := by
  have hJ : IsUnit (V.gramᵀ.map τ).det := isUnit_det_map τ (by rw [det_transpose]; exact GlobalTheory.RouteCoords.gram_det_ne V)
  let N₀ := (GlobalTheory.SplitGLLift.oneAdd (GlobalTheory.SplitGLLift.liftMat hcm τ)).comp (GlobalTheory.SplitGLLift.pairHom (V.gramᵀ.map τ) hJ)
  have hU := GlobalTheory.SplitGLLift.unitary hcm τ V.gramᵀ (fun i j => V.herm.eq (V.frame i) (V.frame j)) hJ K
  have hN : N₀ K = 1 + GlobalTheory.SplitGLLift.liftMat hcm τ (GlobalTheory.SplitGLLift.pairHom (V.gramᵀ.map τ) hJ K - 1) := rfl
  refine ⟨⟨N₀.toHomUnits K, ?_⟩, ?_, ?_⟩
  · have := congrArg transpose hU
    rw [transpose_mul, transpose_mul, transpose_transpose, ← Matrix.mul_assoc] at this
    exact this
  · show At (evFin D.host.F v) (N₀ K - 1)
    rw [hN, add_sub_cancel_left]
    exact GlobalTheory.SplitGLLift.at_liftMat hcm τ _
  · show (N₀ K).map (piW τ) = K.val
    rw [hN, GlobalTheory.SplitGLLift.map_one_add_piW]
    exact add_sub_cancel _ _

theorem placeIso_eq {v : Pl D.host.F} {w : Pl D.host.E} (hv : w.under (𝓞 D.host.F) = v)
    {τ : D.host.E →ₐ[D.host.F] Fv D.host.F v} {jj : Fv D.host.F v ≃+* Kw w} (h1 : IsPlaceIso τ w jj) (h2 : Continuous jj) (x) :
    GlobalTheory.LFun.complMap hv x = jj x := by
  refine congrFun ((HeightOneSpectrum.denseRange_algebraMap D.host.F v).equalizer
    (GlobalTheory.LFun.SplitChart.continuous_complMap hv) h2 (funext fun y => ?_)) x
  have e := h1 (incA D (algebraMap _ _ y))
  have e2 : cpt w (toEAf D (incA D (algebraMap D.host.F D.host.E y))) = algebraMap D.host.E (Kw w) (algebraMap _ _ y) :=
    congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z w) (GlobalTheory.AdeleBaseChange.map_tmul_one (toAd_spec D) _)
  have e3 : piW τ (incA D (algebraMap D.host.F D.host.E y)) = algebraMap _ _ y :=
    (GlobalTheory.SplitGLLift.piW_inclR τ _).trans (τ.commutes y)
  rw [e2, e3] at e
  exact (GlobalTheory.LFun.complMap_algebraMap hv y).trans e.symm

end Lift

section Main

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (blk_mul blk_one blk_map blk_transpose)

def blkGL {K : Type} [Field K] {p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) : GL (Fin p) K × GL (Fin q) K →* GL (Fin d) K where
  toFun x := ⟨GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e x.1.val x.2.val, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (x.1⁻¹).val (x.2⁻¹).val, by rw [blk_mul, Units.mul_inv, Units.mul_inv, blk_one],
    by rw [blk_mul, Units.inv_mul, Units.inv_mul, blk_one]⟩
  map_one' := Units.ext (blk_one e)
  map_mul' _ _ := Units.ext (blk_mul e _ _ _ _).symm

theorem invT_blkGL {K : Type} [Field K] {p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (A : GL (Fin p) K) (B : GL (Fin q) K) :
    invT (blkGL e (A, B)) = blkGL e (invT A, invT B) := Units.ext (blk_transpose e _ _)

theorem invT_conj_blkGL {K : Type} [Field K] {p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (c : GL (Fin d) K) (C₁ K₁ : GL (Fin p) K)
    (C₂ K₂ : GL (Fin q) K) : invT (c⁻¹ * blkGL e (C₁ * invT K₁ * C₁⁻¹, C₂ * invT K₂ * C₂⁻¹) * c) =
      invT (c⁻¹ * blkGL e (C₁, C₂)) * blkGL e (K₁, K₂) * (invT (c⁻¹ * blkGL e (C₁, C₂)))⁻¹ := by
  have : (C₁ * invT K₁ * C₁⁻¹, C₂ * invT K₂ * C₂⁻¹) = (C₁, C₂) * (invT K₁, invT K₂) * (C₁, C₂)⁻¹ := rfl
  rw [this, map_mul (blkGL e), map_mul (blkGL e), map_inv, ← invT_blkGL]
  simp only [map_mul, map_inv, invT_invT]
  group

theorem smul_blk_sub_one {R S : Type} [Ring S] [SMulZeroClass R S] {p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (u : R)
    {A : Matrix (Fin p) (Fin p) S} {B : Matrix (Fin q) (Fin q) S} (hA : u • (A - 1) = 0) (hB : u • (B - 1) = 0) :
    u • (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e A B - 1) = 0 := by
  ext r s
  obtain ⟨r, rfl⟩ := e.surjective r
  obtain ⟨s, rfl⟩ := e.surjective s
  have c1 := fun r s => congrFun (congrFun hA r) s
  have c2 := fun r s => congrFun (congrFun hB r) s
  rcases r with r | r <;> rcases s with s | s
  · simpa [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, Matrix.one_apply] using c1 r s
  · simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, Matrix.one_apply]
  · simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, Matrix.one_apply]
  · simpa [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, Matrix.one_apply] using c2 r s

attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv

set_option maxHeartbeats 2000000 in

theorem mixed_compare : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t) (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E) (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F _ _) (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F _ _),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ X om om' R Rf → IsTied t i j e Bs Γ X →
    ∀ w ∈ locPl G t, ∀ v (hv : w.under (𝓞 D.host.F) = v) (hP : v ∈ Bs.P) ιA,
      Γ.M.IsLinW Bs.ψ (Bs.τ ⟨v, hP⟩) (Γ.V.bas v) (Γ.W.bas v) ιA →
    ∃ ι, IsLagrModel Γ.M W.ψ v (mixHalf e (atPl w 1)) (mixHalf e (cA D (atPl w 1))) (mixCo B t e w) ι ∧
    ∃ c : ℂ, c ≠ 0 ∧ ∃ g₀ : GL (Fin (spW G i j).rank) (Fv D.host.F v),
    ∃ c₀ : GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Fv D.host.F v),
      (∀ n Φ, depthAt G w ≤ n → IsNatDatum (unifAt w) n Φ → ∃ φ ∈ GlobalTheory.WeilM.SB _, ι φ = flipAt W t i j w n Φ ∧
        ∀ Z, ιA φ Z = c * GlobalTheory.SquareFlipReach.sqCore W t i j w n Φ (GlobalTheory.SquareFlipReach.trA t hv e (g₀.1 * Z * c₀.1))) ∧
      ∀ (K₁ : GL (Fin (spV G i j).rank) (Fv D.host.F v)) (K₂ : GL (Fin (spV₁ G i j).rank) (Fv D.host.F v)),
        ∃ g, ∃ c' : ℂ, c' ≠ 0 ∧ ∀ φ ∈ GlobalTheory.WeilM.SB _, ∃ φ₃ ∈ GlobalTheory.WeilM.SB _,
          Acts (evFin D.host.F v) (om (1, blkU _ _ e h.JWW g)) φ φ₃ ∧
          ∀ Z, ιA φ₃ Z = c' * ιA φ (Z * (c₀.1 * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e K₁.1 K₂.1 * (c₀⁻¹).1)) := by
  intro D T L sc G μ₀ hL W B t i j M hst e Bs Γ X om om' h R Rf hm hti w hw v hv hP ιA hA
  classical
  have hT := hm.triple
  let v' : Bs.P := ⟨v, hP⟩
  have hτ : splitPrime (Bs.τ v') = w := hti.2.2.2 v' w hw hv
  obtain ⟨jj, j1, j2, -, j4⟩ := GlobalTheory.T.exists_placeIso_reading_components_characters hL W t i j X h.α h.β (Bs.τ v') w hτ
  have back : ∀ {m n : Type} (A : Matrix m n (Kw w)), (A.map jj.symm).map jj = A := fun A => by ext; simp
  let C₁ := GeneralLinearGroup.map (jj.symm : Kw w →+* Fv D.host.F v) (loc w (B.β i (j + 1)))
  let C₂ := -GeneralLinearGroup.map (jj.symm : Kw w →+* Fv D.host.F v) (loc w (B.β (i + 1) j))
  let cF := (Γ.W.bas v)⁻¹ * blkGL e (C₁, C₂)
  let cc := GeneralLinearGroup.map (jj : Fv D.host.F v →+* Kw w) cF
  have hcc : (Γ.W.bas v).val.map jj * cc.val = basCols B e w := by
    have e1 : (Γ.W.bas v).val * cF.val = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e C₁.val C₂.val := congrArg Units.val (mul_inv_cancel_left (Γ.W.bas v) _)
    have e2 : (Γ.W.bas v).val.map jj * cc.val = ((Γ.W.bas v).val * cF.val).map jj :=
      (Matrix.map_mul (f := (jj : Fv D.host.F v →+* Kw w))).symm
    rw [e2, e1, blk_map _ _ _ (map_zero jj), basCols]
    congr 1
    · exact back _
    · exact (Matrix.map_neg _ (map_neg jj) _).trans (congrArg Neg.neg (back _))
  obtain ⟨g, -, cA⟩ := GlobalTheory.T.exists_mixedLagrangian_chart_integral_rowChange hL W B t i j M e Bs Γ X om om' h hT hti v' w hτ jj j1 j2 cc hcc
  have hb : ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := fun hmem => hst.2 w hw (by
    have e : ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) =
        (D.host.d : 𝓞 D.host.E) * ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) := by push_cast; ring
    rw [e]; exact Ideal.mul_mem_left _ _ hmem)
  have hS := (Good.isGood_of_notMem hL W hw hb).square i i.2 j j.2
  have hξ : (xiAt w)⁻¹ ≠ 0 := inv_ne_zero ((_root_.map_ne_zero _).2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero)
  have dW : Γ.W.J.det ≠ 0 := h.JWW ▸ det_skewGram_ne _ _ e
  have dV : Γ.V.J.det ≠ 0 := by rw [h.JW, one_smul]; exact GlobalTheory.RouteCoords.gram_det_ne _
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd W.ψ := h.ψ ▸ hT.base.std
  have hA' := hA
  rw [h.ψ] at hA'
  obtain ⟨ι, i1, i2⟩ := exists_mixed (M := Γ.M) (ψ := W.ψ) hS.unif hS.cond j2 hξ j4 (h := invT cc) cA hA'.bij
    (fun u hu h0 φ hφ φ₁ h₁ ha => (GlobalTheory.T.heisenbergOperator_isotropic_translation_char_split hT.base.cm Γ.V Γ.W hT.geo.hV.herm hT.geo.hW.skew dV dW Γ.M W.ψ hstd _ _ _ u hu h0
      φ hφ φ₁ h₁ ha).1 ιA hA')
    fun x u hx hu => GlobalTheory.T.tensorSymplecticForm_at_split_finite_place hT.base.cm Γ.V Γ.W hT.geo.hV.herm hT.geo.hW.skew W.ψ _ _ _ x u hx hu
  have h1 := GivenAdm.givenLevel_open hL hw ((i : ℕ), (j : ℕ))
  have h2 := isOpen_map_invT h1.1 h1.2
  haveI hμ := isHaarMeasure_haarVol h2.1 h2.2
  refine ⟨ι, i1, 1, one_ne_zero, GeneralLinearGroup.map (jj.symm : Kw w →+* Fv D.host.F v) g, invT cF, fun n Φ hn hΦ => ?_,
    fun K₁ K₂ => ?_⟩
  · have hN := LocTensor.isNatDatum_flipAt hL W i j hw hb hn hΦ
    obtain ⟨φ, hφ, e1⟩ := i1.1.surjOn (mem_SB_of_isNatDatum hN)
    refine ⟨φ, hφ, e1, fun Z => ?_⟩
    have e5 := i2 φ hφ n (e1 ▸ hN)
    rw [e1, GlobalTheory.SquareFlipReach.flipAt_eq, GlobalTheory.FlipMatch.FourierInv.fourierSum_invFourierSum _ _ _ _ _ _ _ hS.unif hS.inv.cond _ (by
      rw [GlobalTheory.SquareFlipReach.sqCore, ← latA_blockLat, ← Grid.alpha_div_beta]
      exact GlobalTheory.FrameDepth.hasDepth_phiA _ _ _ _ _ (hμ := hμ) _ _ _ _ _ _ hS.unif (hS.one_le.trans hn)
        (LocTensor.condLE_mono hS.unif hn hS.condν)
        (GlobalTheory.SplitFlip.FourierDepth.hasDepth_fourierSum hS.unif hS.cond n _ hΦ))] at e5
    rw [e5, one_mul]
    beta_reduce
    congr 1
    have e6 : g.val * Z.map jj * (invT cc).val =
        ((GeneralLinearGroup.map (jj.symm : Kw w →+* Fv D.host.F v) g).val * Z * (invT cF).val).map jj := by
      refine Eq.trans ?_ (Matrix.map_mul (f := (jj : Fv D.host.F v →+* Kw w))).symm
      refine congrArg₂ HMul.hMul (Eq.trans ?_ (Matrix.map_mul (f := (jj : Fv D.host.F v →+* Kw w))).symm) rfl
      exact congrArg₂ HMul.hMul (back _).symm rfl
    ext r s
    rw [chart, e6, GlobalTheory.SquareFlipReach.trA, Matrix.of_apply, placeIso_eq hv j1 j2.1]
    rcases s with s | s <;> rfl
  · obtain ⟨g₁, a1, b1⟩ := exists_lift hT.base.cm (spV G i j) (Bs.τ v') (C₁ * invT K₁ * C₁⁻¹)
    obtain ⟨g₂, a2, b2⟩ := exists_lift hT.base.cm (spV₁ G i j) (Bs.τ v') (C₂ * invT K₂ * C₂⁻¹)
    have hmat : mat (σ := D.sp.cm.sig) (blkU _ _ e h.JWW (g₁, g₂)) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (mt _ g₁) (mt _ g₂) := rfl
    have hh : blkU _ _ e h.JWW (g₁, g₂) ∈ UAt D.sp.cm.sig Γ.W (evFin D.host.F v) := fun u hu =>
      smul_blk_sub_one e u (a1 u hu) (a2 u hu)
    have hk : (mat (σ := D.sp.cm.sig) (blkU _ _ e h.JWW (g₁, g₂))).map (piW (Bs.τ v')) =
        (blkGL e (C₁ * invT K₁ * C₁⁻¹, C₂ * invT K₂ * C₂⁻¹)).val := by
      rw [hmat, blk_map _ _ _ (map_zero _), b1, b2]
      rfl
    obtain ⟨c', hc', H⟩ := exists_right_translate hT dV dW (Bs.τ v') _ _ hA hh hk
    rw [invT_conj_blkGL] at H
    exact ⟨(g₁, g₂), c', hc', H⟩

end Main

end GlobalTheory.MixCompare

end
