import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaUnfoldingEquivariantUnitaryGroups
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLinearModelLatticeVacuumBaseStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SourceLiftAtGluedPlaceProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GluedLatticeFiniteExpansionsLocalFieldStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLineComponentsContractionStatement
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IndicatorFunctionIdentity
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClopenIsCompactMapsPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DualLatticeCosetIndicatorIsSchwartzBruhatStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GluedLatticeDatumMainPartMemSchwartzBruhatStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierPairingPairCharIndicatorDualLatticeIndicaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierPairingPairCharIndicatorCosetIndicatorStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierPairingDualIndicatorAddNonzeroCosetsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierPairingCharIndicatorDualLatticeCosetsStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd InDual mainDatum)
open GlobalTheory.FinPl.Comm (fpair)

namespace GlobalTheory.FinPl.Vertex

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

def mkLin {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (f : M → N)
    (h : ∀ (c : ℂ) x y, f (c • x + y) = c • f x + f y) : M →ₗ[ℂ] N where
  toFun := f
  map_add' x y := by simpa using h 1 x y
  map_smul' c x := by
    have h0 : f 0 = 0 := by simpa using h 1 0 0
    simpa [h0] using h c x 0

def caSub (V : HSp D) : Submodule ℂ (GA D V → ℂ) where
  carrier := {φ | IsContAut V φ}
  add_mem' h h' := ⟨fun γ hγ g => by rw [Pi.add_apply, Pi.add_apply, h.1 γ hγ, h'.1 γ hγ], h.2.add h'.2⟩
  zero_mem' := ⟨fun _ _ _ => rfl, continuous_const⟩
  smul_mem' c φ h := ⟨fun γ hγ g => by rw [Pi.smul_apply, Pi.smul_apply, h.1 γ hγ], h.2.const_smul c⟩

theorem exists_trilinear {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ} (s₁ : StepBF ψ B J)
    (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) {M₁ M₂ : Type} [AddCommGroup M₁]
    [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂] (U₁ : M₁ →ₗ[ℂ] WO B.V₀ J.W₀ → ℂ) (U₂ : M₂ →ₗ[ℂ] WO J.W₀ B'.V₀ → ℂ)
    (h₁ : ∀ x, IsThetaFunO ψ B.V₀ J.W₀ (U₁ x)) (h₂ : ∀ y, IsThetaFunO ψ J.W₀ B'.V₀ (U₂ y)) :
    ∃ Θ : caSub B.A →ₗ[ℂ] M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] caSub B'.A, ∀ v x y, (Θ v x y).1 = hand0 s₁ s₂ l vL v.1 (U₁ x) (U₂ y) := by
  refine ⟨mkLin (fun v => mkLin (fun x => mkLin
    (fun y => ⟨hand0 s₁ s₂ l vL v.1 (U₁ x) (U₂ y), Comm.contAut_hand0 s₁ s₂ l vL v.2 (h₁ x) (h₂ y)⟩) ?_) ?_) ?_,
    fun _ _ _ => rfl⟩
  · intro c y y'
    refine Subtype.ext ?_
    change hand0 s₁ s₂ l vL v.1 (U₁ x) (U₂ (c • y + y')) = _
    rw [map_add, map_smul]
    exact Comm.doubleThetaUnfolding_linear_second_datum s₁ s₂ l vL v.2 (h₁ x) (h₂ y) (h₂ y') c
  · intro c x x'
    refine LinearMap.ext fun y => Subtype.ext ?_
    change hand0 s₁ s₂ l vL v.1 (U₁ (c • x + x')) (U₂ y) = _
    rw [map_add, map_smul]
    exact Comm.doubleThetaUnfolding_linear_first_datum s₁ s₂ l vL v.2 (h₁ x) (h₁ x') (h₂ y) c
  · intro c v v'
    refine LinearMap.ext fun x => LinearMap.ext fun y => Subtype.ext ?_
    exact Comm.doubleThetaUnfolding_linear_function s₁ s₂ l vL v.2 v'.2 (h₁ x) (h₂ y) c

theorem handFB_smul' {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ} (s : StepFB ψ J B)
    (vL : VolM D B.L.rank J.W₀.rank) (c : ℂ) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (Ξ : WO J.W₀ B.V₀ → ℂ) :
    handFB s vL (c • Y) Ξ = star c • handFB s vL Y Ξ := by
  funext h₁
  simp only [handFB, pairKer, contractT, thPair, Pi.smul_apply, smul_eq_mul, star_mul']
  simp_rw [show ∀ x y : ℂ, x * (star c * y) = star c * (x * y) from fun x y => by ring, integral_const_mul]

theorem handFB_zero {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ} (s : StepFB ψ J B)
    (vL : VolM D B.L.rank J.W₀.rank) (Ξ : WO J.W₀ B.V₀ → ℂ) : handFB s vL 0 Ξ = 0 := by
  have := handFB_smul' s vL 0 0 Ξ
  simpa using this

theorem handBF_sum {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) {L' : HSp D}
    {ζ' : Fin L'.rank → D.host.E} (l : Link B L' ζ') {φ : GA D B.A → ℂ} (hφ : IsContAut B.A φ) {M : Type}
    [AddCommGroup M] [Module ℂ M] (U : M →ₗ[ℂ] WO B.V₀ J.W₀ → ℂ) (hU : ∀ x, IsThetaFunO ψ B.V₀ J.W₀ (U x))
    {ι : Type} (S : Finset ι) (x : ι → M) :
    ∑ i ∈ S, handBF s l φ (U (x i)) = handBF s l φ (U (∑ i ∈ S, x i)) := by
  classical
  refine Finset.induction_on S ?_ ?_
  · funext h w
    simp [handBF]
  · intro a S ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, map_add]
    have := Comm.handBF_right s l hφ (hU (x a)) (hU (∑ i ∈ S, x i)) 1
    rw [one_smul, star_one, one_smul] at this
    exact this.symm

theorem lift_step {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ} (s₁ : StepBF ψ B J)
    (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) {c₀ : ℂ} {φ₀ φ' : GA D B.A → ℂ}
    (hφ' : IsContAut B.A φ') {M : Type} [AddCommGroup M] [Module ℂ M] (U : M →ₗ[ℂ] WO B.V₀ J.W₀ → ℂ)
    (hU : ∀ x, IsThetaFunO ψ B.V₀ J.W₀ (U x)) {ι : Type} (S : Finset ι) (x : ι → M) (Ξ₁ : WO B.V₀ J.W₀ → ℂ)
    (Ξ₂ : WO J.W₀ B'.V₀ → ℂ)
    (h : liftA B.o s₁.om₀ B.vA φ₀ Ξ₁ = c₀ • ∑ i ∈ S, liftA B.o s₁.om₀ B.vA φ' (U (x i))) :
    hand0 s₁ s₂ l vL φ₀ Ξ₁ Ξ₂ = c₀ • hand0 s₁ s₂ l vL φ' (U (∑ i ∈ S, x i)) Ξ₂ := by
  have e1 : handBF s₁ l φ₀ Ξ₁ = star c₀ • handBF s₁ l φ' (U (∑ i ∈ S, x i)) := by
    rw [← handBF_sum s₁ l hφ' U hU S x]
    funext g w
    rw [handBF_eq, h]
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, star_mul', star_sum, handBF_eq]
  rw [hand0, e1, handFB_smul', star_star]
  rfl

end GlobalTheory.FinPl.Vertex

namespace GlobalTheory.FinPl.Vertex

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

theorem charInd_mem' (χ : AddChar 𝓀[k] ℂ) (Q : Pair k n) : charInd χ Q ∈ SB (n → k) := by
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun y => ?_,
    HasCompactSupport.intro (Comm.isCompact_lat Q.lat) fun y hy => ?_⟩
  · by_cases hy : y ∈ Q.lat
    · refine ⟨{z | z - y ∈ Q.ker}, (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.isOpen_lat Q.ker).preimage (continuous_id.sub continuous_const),
        by simp [zero_mem], fun z hz => ?_⟩
      have hz' : Q.HasVal z (Q.ev y) := by
        have := (GlobalTheory.LatPair.Pair.mem_ker.1 hz).add (GlobalTheory.LatPair.Pair.hasVal_ev hy)
        simpa using this
      simp only [charInd, vecInd, if_pos hz'.mem, if_pos hy, hz'.ev_eq]
    · refine ⟨(Q.lat : Set (n → k))ᶜ, (Comm.isCompact_lat Q.lat).isClosed.isOpen_compl, hy, fun z hz => ?_⟩
      have hz' : z ∉ Q.lat := hz
      simp only [charInd, vecInd, if_neg hz', if_neg hy, mul_zero]
  · have hy' : y ∉ Q.lat := hy
    simp only [charInd, vecInd, if_neg hy', mul_zero]

theorem inDual_vecMul {L : Submodule 𝒪[k] (n → k)} {g : GL n k} (hg : g • L = L) (η : n → k) :
    InDual L (η ᵥ* g.val) ↔ InDual L η := by
  have h1 : ∀ y, y ∈ L → g • y ∈ L := fun y hy => by
    rw [← hg]; exact Submodule.smul_mem_pointwise_smul y g L hy
  have h2 : ∀ y, y ∈ L → g⁻¹ • y ∈ L := fun y hy => GlobalTheory.LatPair.mem_smul_iff.1 (by rw [hg]; exact hy)
  constructor
  · intro h y hy
    have := h _ (h2 y hy)
    rwa [← dotProduct_mulVec, show g.val *ᵥ (g⁻¹ • y) = y from smul_inv_smul g y] at this
  · intro h y hy
    rw [← dotProduct_mulVec]
    exact h _ (h1 y hy)

theorem dualInd_vecMul {L : Submodule 𝒪[k] (n → k)} {g : GL n k} (hg : g • L = L) (η : n → k) :
    dualInd L (η ᵥ* g.val) = dualInd L η := by
  classical
  unfold dualInd
  exact if_congr (inDual_vecMul hg η) rfl rfl

theorem vecInd_mulVec {L : Submodule 𝒪[k] (n → k)} {g : GL n k} (hg : g • L = L) (y : n → k) :
    vecInd L (g.val *ᵥ y) = vecInd L y := by
  classical
  have : g.val *ᵥ y ∈ L ↔ y ∈ L := by
    constructor
    · intro h
      have := GlobalTheory.LatPair.mem_smul_iff.1 (show g.val *ᵥ y ∈ g • L by rw [hg]; exact h)
      rwa [show g⁻¹ • (g.val *ᵥ y) = y from inv_smul_smul g y] at this
    · intro h
      rw [← hg]; exact Submodule.smul_mem_pointwise_smul y g L h
  unfold vecInd
  exact if_congr this rfl rfl

theorem hasVal_neg {P : Pair k n} {x : n → k} {a : 𝓀[k]} (h : P.HasVal x a) : P.HasVal (-x) (-a) := by
  have := h.smul (-1)
  simpa using this

theorem neg_one_smul_pair (P : Pair k n) : ((-1 : GL n k) • P) = ((-1 : 𝓀[k]ˣ) • P) := by
  refine Pair.ext fun x a => ?_
  rw [Pair.smul_hasVal, Pair.dia_hasVal]
  have e1 : ((-1 : GL n k)⁻¹ • x) = -x := by
    show (((-1 : GL n k)⁻¹ : GL n k) : Matrix n n k) *ᵥ x = -x
    simp [Matrix.neg_mulVec]
  have e2 : (((-1 : 𝓀[k]ˣ)⁻¹ : 𝓀[k]ˣ) : 𝓀[k]) * a = -a := by simp
  rw [e1, e2]
  constructor
  · intro h; simpa using hasVal_neg h
  · intro h; simpa using hasVal_neg h

theorem val_det_neg_one : valuation k ((Matrix.GeneralLinearGroup.det (-1 : GL n k) : kˣ) : k) = 1 := by
  simp [Matrix.det_neg]

omit [Fintype n] [DecidableEq n] in
theorem val_FFStar' {S : HSp D} (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (φ : Form k n (caSub S)) (P : Pair k n) :
    (FFStar q χ φ P).1 = FFStar q χ (fun Q => (φ Q).1) P := by
  simp only [FFStar_apply, Submodule.coe_sum, Submodule.coe_smul]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem det_embX_one' (g : GL n k) :
    Matrix.GeneralLinearGroup.det (GlobalTheory.RootEx.embX 1 g) = Matrix.GeneralLinearGroup.det g :=
  Units.ext (by
    change (fromBlocks g.val 0 0 (1 : Matrix (Fin 1) (Fin 1) k)).det = g.val.det
    rw [det_fromBlocks_zero₂₁, det_one, mul_one])

end Local

section Over

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
  {S T : HSp D} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem overMap (hψ : IsStdChar D ψ (-1)) {α : Frame p S n'} {β : Frame p T n} {LS : Lat S} {LT : Lat T}
    {f₀ : WO S T → ℂ} {Ψ₀ : Matrix n n' k → ℂ} {Ξ : WO S T → ℂ} (h : Over ψ α β LS LT f₀ Ψ₀ Ξ)
    (hlin : ∀ (Ψ : Matrix n n' k → ℂ) (f : WO S T → ℂ), Over ψ α β LS LT f₀ Ψ f → ∀ (c : ℂ) (Ψ' : Matrix n n' k → ℂ)
      (f' : WO S T → ℂ), Over ψ α β LS LT f₀ Ψ' f' → Over ψ α β LS LT f₀ (c • Ψ + Ψ') (c • f + f')) :
    ∃ U : SB (Matrix n n' k) →ₗ[ℂ] WO S T → ℂ, (∀ Ψ, Over ψ α β LS LT f₀ Ψ.1 (U Ψ)) ∧
      (∀ Ψ f, Over ψ α β LS LT f₀ Ψ.1 f → f = U Ψ) ∧ ∀ Ψ, IsThetaFunO ψ S T (U Ψ) := by
  obtain ⟨H1, H2, -⟩ := GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n n' ψ hψ S T α β LS LT h.1 h.2.1 f₀ h.2.2.1
  choose U hU hU' using fun Ψ : SB (Matrix n n' k) => H1 Ψ.1 Ψ.2
  exact ⟨mkLin U fun c x y => (hU' _ _ (hlin _ _ (hU x) c _ _ (hU y))).symm, hU, hU', fun Ψ => (H2 _ _ (hU Ψ)).1⟩

theorem tensCol_subst' {Ψ Ψ' : Matrix n n' k → ℂ} (a : (n → k) → ℂ) (u : Matrix n n k) (g : GL n' k)
    (h : ∀ x, Ψ' x = Ψ (u * x * g.val)) (x : Matrix n (n' ⊕ Fin 1) k) :
    tensCol Ψ a (u * x * (GlobalTheory.RootEx.embX 1 g).val) = tensCol Ψ' (fun y => a (u *ᵥ y)) x := by
  rw [show (GlobalTheory.RootEx.embX 1 g).val = fromBlocks g.val 0 0 1 from rfl, tensCol, tensCol, h]
  congr 2
  · ext i j
    simp [Matrix.mul_apply]
  · ext i
    simp [Matrix.mul_apply, mulVec, dotProduct]

theorem tensRow_subst' {Ψ Ψ' : Matrix n n' k → ℂ} (b : (n' → k) → ℂ) (h₀ : GL n k) (u : Matrix n' n' k)
    (h : ∀ x, Ψ' x = Ψ ((h₀⁻¹ : GL n k).val * x * u)) (x : Matrix (n ⊕ Fin 1) n' k) :
    tensRow Ψ b (((GlobalTheory.RootEx.embX 1 h₀)⁻¹ : GL (n ⊕ Fin 1) k).val * x * u) = tensRow Ψ' (fun η => b (η ᵥ* u)) x := by
  rw [← map_inv, show (GlobalTheory.RootEx.embX 1 h₀⁻¹).val = fromBlocks (h₀⁻¹ : GL n k).val 0 0 1 from rfl, tensRow, tensRow, h]
  generalize (h₀⁻¹ : GL n k).val = w
  congr 2
  · ext i j
    simp [Matrix.mul_apply]
  · ext i
    simp [Matrix.mul_apply, vecMul, dotProduct]

end Over

end GlobalTheory.FinPl.Vertex

namespace GlobalTheory.FinPl.Vertex

open Classical in

theorem vertexGlued (D : D7) : VertexGlued D := by
  intro k _ _ _ _ p q ψ χ hχ hIs
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  haveI := secondCountable k
  obtain ⟨e, he, HC⟩ := GlobalTheory.T.splitPlace_lineComponents_contraction D k p ψ χ hIs
  obtain ⟨ν, hν, -⟩ := exists_isUnitVol k
  let ε : 𝓀[k]ˣ := if e = 1 then 1 else -1
  have hεe : (e = 1 ∧ ε = 1) ∨ (e = -1 ∧ ε = -1) := by
    by_cases h1 : e = 1
    · exact Or.inl ⟨h1, if_pos h1⟩
    · exact Or.inr ⟨he.resolve_left h1, if_neg h1⟩
  refine ⟨ε, ?_, ?_⟩
  · rcases hεe with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  intro n n' n'' _ _ _ _ _ _ σ B J B' s₁ s₂ l vL hu₁ hu₂ α α₀ β γ γ₀ hα hγ P P₁ Q
  have hψ : IsStdChar D ψ (-1) := s₁.weil₀.std

  have hχc : Continuous χ := by
    have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
    have h1 : Continuous fun a => psiE ψ (p.sec a) := hψ.1.1.comp (ht.comp p.cont_sec)
    have h2 : (fun a => ((χ a : Circle) : ℂ)) = fun a => psiE ψ (p.sec a) := funext hIs
    refine continuous_induced_rng.2 ?_
    change Continuous (fun a => ((χ a : Circle) : ℂ))
    rw [h2]
    exact h1
  obtain ⟨lS₁, lT₁, uS₁, uT₁, lin₁⟩ := GlobalTheory.T.splitPlace_linearModel_latticeVacuum_base D k p ψ _ _ _ _ _ s₁.weil₀
  obtain ⟨lS₂, lT₂, uS₂, uT₂, lin₂⟩ := GlobalTheory.T.splitPlace_linearModel_latticeVacuum_base D k p ψ _ _ _ _ _ s₂.weil₀
  have vS₁ := uS₁ hu₁.2
  have vT₁ := uT₁ hu₁.1
  have vS₂ := uS₂ hu₂.2
  have vT₂ := uT₂ hu₂.1
  obtain ⟨⟨c₀, HS⟩, SG2⟩ := GlobalTheory.T.sourceLiftAtGluedPlace_proof D k p n n' q χ hχ (resChar χ hχ q) rfl ψ B.V₀ B.A B.L J.W₀ B.o B.ζ B.line
    B.cpt B.vA s₁.χV s₁.χW s₁.om₀ s₁.weil₀ hu₁.1 hu₁.2 α α₀ β hα P P₁ Q.lat
  obtain ⟨D1, -, -⟩ := GlobalTheory.T.gluedLattice_finite_expansions_localField k n n' q (resChar χ hχ q) (resChar_ne_one hχ q) Q.lat
  obtain ⟨-, D2, D3⟩ := GlobalTheory.T.gluedLattice_finite_expansions_localField k n n'' q (resChar χ hχ q) (resChar_ne_one hχ q) Q.lat
  let μ : Measure (n → k) := Measure.pi fun _ => ν
  have I0 : fpair χ e μ (vecInd Q.lat) (dualInd Q.lat) ≠ 0 := Comm.fpair_ne_zero χ hχc e he μ Q.lat
  have hvec := Comm.vecInd_mem Q.lat
  have hdual := Comm.dualInd_mem Q.lat
  let col : ∀ Ψ : Matrix n n' k → ℂ, Ψ ∈ SB (Matrix n n' k) → ∀ a : (n → k) → ℂ, a ∈ SB (n → k) →
      SB (Matrix n (n' ⊕ Fin 1) k) := fun Ψ hΨ a ha => ⟨tensCol Ψ a, Comm.tensCol_mem hΨ ha⟩
  let row : ∀ Ψ : Matrix n'' n k → ℂ, Ψ ∈ SB (Matrix n'' n k) → ∀ b : (n → k) → ℂ, b ∈ SB (n → k) →
      SB (Matrix (n'' ⊕ Fin 1) n k) := fun Ψ hΨ b hb => ⟨tensRow Ψ b, Comm.tensRow_mem hΨ hb⟩
  have one_emb : ∀ {S₀ A L : HSp D} (o : OrthDec S₀ A L), o.emb (1, 1) = 1 := fun o => map_one o.emb

  refine ⟨fun R => ⟨c₀ * ((withLat Q.lat).card : ℂ), ?_⟩, ?_⟩
  · intro L₁ L₂ L₂' L₃ f₁ Ξ₁ Ξ₁' f₂ Ξ₂ Ξ₂' o₁ o₁' o₂ o₂' φ hφ
    obtain ⟨U₁, a₁, b₁, t₁⟩ := overMap hψ o₁ fun Ψ f h => (lin₁ _ _ α₀ β L₁ L₂ f₁ Ψ f h).2.2
    obtain ⟨U₂, a₂, b₂, t₂⟩ := overMap hψ o₂ fun Ψ f h => (lin₂ _ _ β γ₀ L₂' L₃ f₂ Ψ f h).2.2
    obtain ⟨Θ, hΘ⟩ := exists_trilinear s₁ s₂ l vL U₁ U₂ t₁ t₂
    have key : ∀ (v : caSub B.A) (Ψ₁ : Matrix n n' k → ℂ) (h₁ : Ψ₁ ∈ SB (Matrix n n' k)) (Ψ₂ : Matrix n'' n k → ℂ)
        (h₂ : Ψ₂ ∈ SB (Matrix n'' n k)) (a a' b b' : (n → k) → ℂ) (ha : a ∈ SB (n → k)) (ha' : a' ∈ SB (n → k))
        (hb : b ∈ SB (n → k)) (hb' : b' ∈ SB (n → k)),
        fpair χ e μ a' b' • (Θ v (col Ψ₁ h₁ a ha) (row Ψ₂ h₂ b hb)).1 =
          fpair χ e μ a b • (Θ v (col Ψ₁ h₁ a' ha') (row Ψ₂ h₂ b' hb')).1 := by
      intro v Ψ₁ h₁ Ψ₂ h₂ a a' b b' ha ha' hb hb'
      rw [hΘ, hΘ]
      exact HC n n' n'' σ B J B' s₁ s₂ l vL α α₀ β γ γ₀ hα hγ μ L₁ L₂ L₂' L₃ f₁ _ _ f₂ _ _ Ψ₁ Ψ₂ a a' b b' ha ha' hb hb'
        (a₁ (col Ψ₁ h₁ a ha)) (a₁ (col Ψ₁ h₁ a' ha')) (a₂ (row Ψ₂ h₂ b hb)) (a₂ (row Ψ₂ h₂ b' hb')) v.1 v.2
    have hFF : ∀ A : Pair k n', IsContAut B.A (FFStar q (resChar χ hχ q) φ A) := fun A => by
      have := (FFStar q (resChar χ hχ q) (fun P₂ => (⟨φ P₂, hφ.2.2 P₂⟩ : caSub B.A)) A).2
      rwa [val_FFStar'] at this
    let v' : caSub B.A := ⟨_, hFF P₁⟩
    let x : Pair k n → SB (Matrix n (n' ⊕ Fin 1) k) := fun Q' =>
      col (phiOne P₁ Q') (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem P₁ Q') (charInd (resChar χ hχ q) Q') (charInd_mem' _ Q')
    let xv : Pair k n' → Pair k n → SB (Matrix n (n' ⊕ Fin 1) k) := fun A Q' =>
      col (phiOne A Q') (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem A Q') (vecInd Q.lat) hvec
    let yd : Pair k n → SB (Matrix (n'' ⊕ Fin 1) n k) := fun Q'' =>
      row (phiOne Q'' R) (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem Q'' R) (dualInd Q.lat) hdual
    let y₀ : SB (Matrix (n'' ⊕ Fin 1) n k) := row (latInd Q.lat R.ker) (latInd_mem_SB _ _) (dualInd Q.lat) hdual
    let y : Pair k n → SB (Matrix (n'' ⊕ Fin 1) n k) := fun Q'' =>
      row (phiOne Q'' R) (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem Q'' R) (cosetInd q Q''.lat Q''.red) (GlobalTheory.T.dualLatticeCoset_indicator_isSchwartzBruhat k n q _ _)

    have h2 : hand0 s₁ s₂ l vL (φ P) Ξ₁ Ξ₂ = c₀ • hand0 s₁ s₂ l vL (FFStar q (resChar χ hχ q) φ P₁)
        (U₁ (∑ Q' ∈ withLat Q.lat, x Q')) Ξ₂ :=
      lift_step s₁ s₂ l vL (hFF P₁) U₁ t₁ (withLat Q.lat) x Ξ₁ Ξ₂
        (HS L₁ L₂ f₁ Ξ₁ (fun Q' => U₁ (x Q')) o₁ (fun Q' _ => a₁ (x Q')) φ hφ)

    have hΞ₂ : Ξ₂ = U₂ (y₀ + ∑ Q'' ∈ withLat Q.lat, y Q'') := by
      rw [b₂ ⟨_, o₂.2.2.2.1⟩ Ξ₂ o₂]
      congr 1
      apply Subtype.ext
      simp only [Submodule.coe_add, Submodule.coe_sum]
      exact D2 R

    have t0 : ∀ Q' ∈ withLat Q.lat, (Θ v' (x Q') y₀).1 = 0 := fun Q' hQ' => by
      have := key v' (phiOne P₁ Q') (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem P₁ Q') (latInd Q.lat R.ker) (latInd_mem_SB _ _)
        (charInd (resChar χ hχ q) Q') (vecInd Q.lat) (dualInd Q.lat) (dualInd Q.lat) (charInd_mem' _ Q') hvec hdual hdual
      have hf := GlobalTheory.T.fourierPairing_pairCharIndicator_dualLatticeIndicator_zero k n q χ hχ e he μ Q'
      rw [mem_withLat.1 hQ'] at hf
      rw [hf, zero_smul] at this
      exact (smul_eq_zero.1 this).resolve_left I0

    have t1 : ∀ Q' ∈ withLat Q.lat, ∑ Q'' ∈ withLat Q.lat, (Θ v' (x Q') (y Q'')).1 =
        (Θ v' (xv P₁ Q') (yd (ε • Q'))).1 := by
      intro Q' hQ'
      have hQ'l : Q'.lat = Q.lat := mem_withLat.1 hQ'
      have hmem : ε • Q' ∈ withLat Q.lat := mem_withLat.2 (by rw [Pair.dia_lat, hQ'l])
      rw [Finset.sum_eq_single_of_mem (ε • Q') hmem]
      · have := key v' (phiOne P₁ Q') (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem P₁ Q') (phiOne (ε • Q') R)
          (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem _ R) (charInd (resChar χ hχ q) Q') (vecInd Q.lat)
          (cosetInd q (ε • Q').lat (ε • Q').red) (dualInd Q.lat) (charInd_mem' _ Q') hvec (GlobalTheory.T.dualLatticeCoset_indicator_isSchwartzBruhat k n q _ _) hdual
        rw [(GlobalTheory.T.fourierPairing_pairCharIndicator_cosetIndicator k n q χ hχ e ε hεe μ Q' (ε • Q') (by rw [Pair.dia_lat])).1 rfl, hQ'l] at this
        exact smul_right_injective _ I0 this
      · intro Q'' hQ'' hne
        have hQ''l : Q''.lat = Q.lat := mem_withLat.1 hQ''
        have := key v' (phiOne P₁ Q') (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem P₁ Q') (phiOne Q'' R)
          (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem _ R) (charInd (resChar χ hχ q) Q') (vecInd Q.lat)
          (cosetInd q Q''.lat Q''.red) (dualInd Q.lat) (charInd_mem' _ Q') hvec (GlobalTheory.T.dualLatticeCoset_indicator_isSchwartzBruhat k n q _ _) hdual
        rw [(GlobalTheory.T.fourierPairing_pairCharIndicator_cosetIndicator k n q χ hχ e ε hεe μ Q' Q'' (hQ''l.trans hQ'l.symm)).2 hne, zero_smul] at this
        exact (smul_eq_zero.1 this).resolve_left I0

    have hmove : ∀ (Q₀ : Pair k n) (g : GL n k), g • Q.lat = Q.lat →
        (Θ v' (xv P₁ (g • Q₀)) (yd (g • ε • Q₀))).1 = (Θ v' (xv P₁ Q₀) (yd (ε • Q₀))).1 := by
      intro Q₀ g hgL
      have hdet := GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.valuation_det_of_fix Q.lat hgL
      have hgL' : g⁻¹ • Q.lat = Q.lat := by
        conv_lhs => rw [← hgL]
        exact inv_smul_smul g Q.lat
      have e1 : s₁.om₀ (α₀.gl 1, β.gl g) (U₁ (xv P₁ Q₀)) = U₁ (xv P₁ (g • Q₀)) := by
        refine b₁ _ _ ?_
        have := (lin₁ _ _ α₀ β L₁ L₂ f₁ _ _ (a₁ (xv P₁ Q₀))).1 1 g
        convert this using 1
        funext z
        have hl : ((lS₁ (Matrix.GeneralLinearGroup.det (1 : GL (n' ⊕ Fin 1) k)) : ℂˣ) : ℂ) = 1 := by simp
        have hr : ((lT₁ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) = 1 := by rw [vT₁ _ hdet]; rfl
        show tensCol (phiOne P₁ (g • Q₀)) (vecInd Q.lat) z = _ * _ * tensCol (phiOne P₁ Q₀) (vecInd Q.lat) _
        rw [hl, hr, one_mul, one_mul,
          show (1 : GL (n' ⊕ Fin 1) k) = GlobalTheory.RootEx.embX 1 (1 : GL n' k) from (map_one _).symm,
          tensCol_subst' (vecInd Q.lat) ((g⁻¹ : GL n k) : Matrix n n k) (1 : GL n' k)
            (Ψ' := phiOne P₁ (g • Q₀)) (fun x => by
              have := phiOne_smul (P := P₁) (Q := Q₀) (x := x) (1 : GL n' k) g
              rw [one_smul] at this
              exact this) z]
        congr 1
        funext w
        exact (vecInd_mulVec hgL' w).symm
      have e2 : s₂.om₀ (β.gl g, γ₀.gl 1) (U₂ (yd (ε • Q₀))) = U₂ (yd (g • ε • Q₀)) := by
        refine b₂ _ _ ?_
        have := (lin₂ _ _ β γ₀ L₂' L₃ f₂ _ _ (a₂ (yd (ε • Q₀)))).1 g 1
        convert this using 1
        funext z
        have hl : ((lS₂ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) = 1 := by rw [vS₂ _ hdet]; rfl
        have hr : ((lT₂ (Matrix.GeneralLinearGroup.det (1 : GL (n'' ⊕ Fin 1) k)) : ℂˣ) : ℂ) = 1 := by simp
        show tensRow (phiOne (g • ε • Q₀) R) (dualInd Q.lat) z = _ * _ * tensRow (phiOne (ε • Q₀) R) (dualInd Q.lat) _
        rw [hl, hr, one_mul, one_mul,
          show (1 : GL (n'' ⊕ Fin 1) k) = GlobalTheory.RootEx.embX 1 (1 : GL n'' k) from (map_one _).symm,
          tensRow_subst' (dualInd Q.lat) (1 : GL n'' k) (g : Matrix n n k)
            (Ψ' := phiOne (g • ε • Q₀) R) (fun x => by
              have := phiOne_smul (P := ε • Q₀) (Q := R) (x := x) g (1 : GL n'' k)
              rw [one_smul] at this
              exact this) z]
        congr 1
        funext w
        exact (dualInd_vecMul hgL w).symm
      have e3 := Comm.doubleThetaUnfolding_equivariant_unitaryGroups s₁ s₂ l vL (hFF P₁) (t₁ (xv P₁ Q₀)) (t₂ (yd (ε • Q₀))) 1 (β.gl g) 1
      rw [one_emb, one_emb] at e3
      rw [hΘ, hΘ, ← e1, ← e2, map_one α₀.gl, map_one γ₀.gl]
      rw [show (fun x : GA D B.A => FFStar q (resChar χ hχ q) φ P₁ (x * 1)) = FFStar q (resChar χ hχ q) φ P₁ from
        funext fun x => by rw [mul_one]] at e3
      rw [e3]
      funext x
      rw [mul_one]
    have hall : ∀ Q' ∈ withLat Q.lat, (Θ v' (xv P₁ Q') (yd (ε • Q'))).1 =
        (Θ v' (xv P₁ (ε⁻¹ • Q)) (yd (ε • ε⁻¹ • Q))).1 := by
      intro Q' hQ'
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GL n k) (ε⁻¹ • Q) Q'
      have hgL : g • Q.lat = Q.lat := by
        have := congrArg Pair.lat hg
        rw [Pair.smul_lat, Pair.dia_lat, mem_withLat.1 hQ'] at this
        exact this
      have := hmove (ε⁻¹ • Q) g hgL
      rw [hg, smul_comm g ε (ε⁻¹ • Q), hg] at this
      exact this

    have hid : ∀ Y', s₂.om₀ (1, 1) Y' = Y' := fun Y' => by
      rw [show ((1 : GA D J.W₀), (1 : GA D B'.V₀)) = 1 from rfl, map_one]
      rfl
    have hsrc : ∀ (g : GL n' k), valuation k ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = 1 → ∀ A A' : Pair k n',
        hand0 s₁ s₂ l vL (FFStar q (resChar χ hχ q) φ (g • A)) (U₁ (xv (g • A') Q)) (U₂ (yd Q)) =
          hand0 s₁ s₂ l vL (FFStar q (resChar χ hχ q) φ A) (U₁ (xv A' Q)) (U₂ (yd Q)) := by
      intro g hdet A A'
      have e1 : s₁.om₀ (α₀.gl (GlobalTheory.RootEx.embX 1 g), β.gl 1) (U₁ (xv A' Q)) = U₁ (xv (g • A') Q) := by
        refine b₁ _ _ ?_
        have := (lin₁ _ _ α₀ β L₁ L₂ f₁ _ _ (a₁ (xv A' Q))).1 (GlobalTheory.RootEx.embX 1 g) 1
        convert this using 1
        funext z
        have hl : ((lS₁ (Matrix.GeneralLinearGroup.det (GlobalTheory.RootEx.embX 1 g)) : ℂˣ) : ℂ) = 1 := by
          rw [det_embX_one', vS₁ _ hdet]; rfl
        have hr : ((lT₁ (Matrix.GeneralLinearGroup.det (1 : GL n k)) : ℂˣ) : ℂ) = 1 := by simp
        show tensCol (phiOne (g • A') Q) (vecInd Q.lat) z = _ * _ * tensCol (phiOne A' Q) (vecInd Q.lat) _
        rw [hl, hr, one_mul, one_mul,
          tensCol_subst' (vecInd Q.lat) (((1 : GL n k)⁻¹ : GL n k) : Matrix n n k) g
            (Ψ' := phiOne (g • A') Q) (fun x => by
              have := phiOne_smul (P := A') (Q := Q) (x := x) g (1 : GL n k)
              rw [one_smul] at this
              exact this) z]
        congr 1
        funext w
        simp
      have e3 := Comm.doubleThetaUnfolding_equivariant_unitaryGroups s₁ s₂ l vL (hFF A) (t₁ (xv A' Q)) (t₂ (yd Q)) (α.gl g) 1 1
      rw [one_emb, Comm.emb_gl hα g, hid] at e3
      have e4 : FFStar q (resChar χ hχ q) φ (g • A) = fun x => FFStar q (resChar χ hχ q) φ A (x * α.gl g) :=
        FFStar_mem_EqForm q _ hφ.1 g A
      rw [e4, ← e1, map_one β.gl, e3]
      funext x
      rw [mul_one]
    obtain ⟨g₁, hg₁a, hg₁b, hg₁d⟩ : ∃ g₁ : GL n' k, g₁ • P₁ = ε • P₁ ∧ g₁ • (ε • P₁) = P₁ ∧
        valuation k ((Matrix.GeneralLinearGroup.det g₁ : kˣ) : k) = 1 := by
      rcases hεe with ⟨-, h⟩ | ⟨-, h⟩
      · exact ⟨1, by rw [h, one_smul, one_smul], by rw [h, one_smul, one_smul], by simp⟩
      · refine ⟨-1, by rw [neg_one_smul_pair, h], ?_, val_det_neg_one⟩
        rw [neg_one_smul_pair, h, smul_smul]
        simp
    have hfin : (Θ v' (xv P₁ (ε⁻¹ • Q)) (yd (ε • ε⁻¹ • Q))).1 =
        hand0 s₁ s₂ l vL (dia ε (FFStar q (resChar χ hχ q) φ) P₁) Ξ₁' Ξ₂' := by
      rw [hΘ, b₁ (xv P₁ Q) Ξ₁' o₁', b₂ (yd Q) Ξ₂' o₂', dia_apply, smul_inv_smul]
      have hx : xv P₁ (ε⁻¹ • Q) = xv (ε • P₁) Q := by
        apply Subtype.ext
        show tensCol (phiOne P₁ (ε⁻¹ • Q)) _ = tensCol (phiOne (ε • P₁) Q) _
        have := phiOne_dia (P := P₁) (Q := ε⁻¹ • Q) ε
        rw [smul_inv_smul] at this
        rw [this]
      rw [hx]
      have := hsrc g₁ hg₁d P₁ (ε • P₁)
      rw [hg₁a, hg₁b] at this
      exact this.symm
    have hexp : hand0 s₁ s₂ l vL (FFStar q (resChar χ hχ q) φ P₁) (U₁ (∑ Q' ∈ withLat Q.lat, x Q'))
        (U₂ (y₀ + ∑ Q'' ∈ withLat Q.lat, y Q'')) =
        ∑ Q' ∈ withLat Q.lat, ((Θ v' (x Q') y₀).1 + ∑ Q'' ∈ withLat Q.lat, (Θ v' (x Q') (y Q'')).1) := by
      refine (hΘ v' _ _).symm.trans ?_
      rw [map_sum, LinearMap.sum_apply, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun Q' _ => ?_
      rw [map_add, map_sum, Submodule.coe_add, Submodule.coe_sum]
    rw [h2, hΞ₂, hexp, Finset.sum_congr rfl fun Q' hQ' => by rw [t0 Q' hQ', zero_add, t1 Q' hQ', hall Q' hQ'],
      Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hfin]

  · intro Λ _ L₁ L₂ L₂' L₃ f₁ Ξ₁ f₂ Ξ₂ o₁ o₂ φ hφ
    have hL : latInd Q.lat Λ ∈ SB (Matrix n'' n k) := latInd_mem_SB _ _
    rcases o₂ with o₂ | o₂
    ·
      rw [(D3 Λ).1] at o₂
      obtain ⟨U₁, a₁, b₁, t₁⟩ := overMap hψ o₁ fun Ψ f h => (lin₁ _ _ α₀ β L₁ L₂ f₁ Ψ f h).2.2
      obtain ⟨U₂, a₂, b₂, t₂⟩ := overMap hψ o₂ fun Ψ f h => (lin₂ _ _ β γ₀ L₂' L₃ f₂ Ψ f h).2.2
      obtain ⟨Θ, hΘ⟩ := exists_trilinear s₁ s₂ l vL U₁ U₂ t₁ t₂

      have key : ∀ (v : caSub B.A) (Ψ₁ : Matrix n n' k → ℂ) (h₁ : Ψ₁ ∈ SB (Matrix n n' k)) (Ψ₂ : Matrix n'' n k → ℂ)
          (h₂ : Ψ₂ ∈ SB (Matrix n'' n k)) (a a' b b' : (n → k) → ℂ) (ha : a ∈ SB (n → k)) (ha' : a' ∈ SB (n → k))
          (hb : b ∈ SB (n → k)) (hb' : b' ∈ SB (n → k)),
          fpair χ e μ a' b' • (Θ v (col Ψ₁ h₁ a ha) (row Ψ₂ h₂ b hb)).1 =
            fpair χ e μ a b • (Θ v (col Ψ₁ h₁ a' ha') (row Ψ₂ h₂ b' hb')).1 := by
        intro v Ψ₁ h₁ Ψ₂ h₂ a a' b b' ha ha' hb hb'
        rw [hΘ, hΘ]
        exact HC n n' n'' σ B J B' s₁ s₂ l vL α α₀ β γ γ₀ hα hγ μ L₁ L₂ L₂' L₃ f₁ _ _ f₂ _ _ Ψ₁ Ψ₂ a a' b b' ha ha' hb hb'
          (a₁ (col Ψ₁ h₁ a ha)) (a₁ (col Ψ₁ h₁ a' ha')) (a₂ (row Ψ₂ h₂ b hb)) (a₂ (row Ψ₂ h₂ b' hb')) v.1 v.2

      have hFF : IsContAut B.A (FFStar q (resChar χ hχ q) φ P₁) := by
        have := (FFStar q (resChar χ hχ q) (fun P₂ => (⟨φ P₂, hφ.2.2 P₂⟩ : caSub B.A)) P₁).2
        rwa [val_FFStar'] at this
      let v' : caSub B.A := ⟨_, hFF⟩
      let x : Pair k n → SB (Matrix n (n' ⊕ Fin 1) k) := fun Q' =>
        col (phiOne P₁ Q') (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem P₁ Q') (charInd (resChar χ hχ q) Q') (charInd_mem' _ Q')
      let yK : SB (Matrix (n'' ⊕ Fin 1) n k) := row (latInd Q.lat Λ) hL (dualInd Q.lat) hdual
      have h2 : hand0 s₁ s₂ l vL (φ P) Ξ₁ Ξ₂ = c₀ • hand0 s₁ s₂ l vL (FFStar q (resChar χ hχ q) φ P₁)
          (U₁ (∑ Q' ∈ withLat Q.lat, x Q')) Ξ₂ :=
        lift_step s₁ s₂ l vL hFF U₁ t₁ (withLat Q.lat) x Ξ₁ Ξ₂
          (HS L₁ L₂ f₁ Ξ₁ (fun Q' => U₁ (x Q')) o₁ (fun Q' _ => a₁ (x Q')) φ hφ)
      have hsum : hand0 s₁ s₂ l vL (FFStar q (resChar χ hχ q) φ P₁) (U₁ (∑ Q' ∈ withLat Q.lat, x Q')) (U₂ yK) =
          ∑ Q' ∈ withLat Q.lat, (Θ v' (x Q') yK).1 := by
        refine (hΘ v' _ _).symm.trans ?_
        rw [map_sum, LinearMap.sum_apply, Submodule.coe_sum]
      have t0 : ∀ Q' ∈ withLat Q.lat, (Θ v' (x Q') yK).1 = 0 := fun Q' hQ' => by
        have := key v' (phiOne P₁ Q') (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem P₁ Q') (latInd Q.lat Λ) hL
          (charInd (resChar χ hχ q) Q') (vecInd Q.lat) (dualInd Q.lat) (dualInd Q.lat) (charInd_mem' _ Q') hvec hdual hdual
        have hf := GlobalTheory.T.fourierPairing_pairCharIndicator_dualLatticeIndicator_zero k n q χ hχ e he μ Q'
        rw [mem_withLat.1 hQ'] at hf
        rw [hf, zero_smul] at this
        exact (smul_eq_zero.1 this).resolve_left I0
      rw [h2, b₂ yK Ξ₂ o₂, hsum, Finset.sum_eq_zero t0, smul_zero]
    ·
      rw [(D3 Λ).2] at o₂
      obtain ⟨btot, hbdef⟩ : ∃ b, b = dualInd Q.lat + ∑ Q'' ∈ withLat Q.lat, cosetInd q Q''.lat Q''.red := ⟨_, rfl⟩
      rw [← hbdef] at o₂
      have hbtot : btot ∈ SB (n → k) := by
        rw [hbdef]
        exact add_mem hdual (Submodule.sum_mem _ fun Q'' _ => GlobalTheory.T.dualLatticeCoset_indicator_isSchwartzBruhat k n q _ _)
      obtain ⟨U₁, a₁, b₁, t₁⟩ := overMap hψ o₁ fun Ψ f h => (lin₁ _ _ α₀ β L₁ L₂ f₁ Ψ f h).2.2
      obtain ⟨U₂, a₂, b₂, t₂⟩ := overMap hψ o₂ fun Ψ f h => (lin₂ _ _ β γ₀ L₂' L₃ f₂ Ψ f h).2.2
      obtain ⟨Θ, hΘ⟩ := exists_trilinear s₁ s₂ l vL U₁ U₂ t₁ t₂

      have key : ∀ (v : caSub B.A) (Ψ₁ : Matrix n n' k → ℂ) (h₁ : Ψ₁ ∈ SB (Matrix n n' k)) (Ψ₂ : Matrix n'' n k → ℂ)
          (h₂ : Ψ₂ ∈ SB (Matrix n'' n k)) (a a' b b' : (n → k) → ℂ) (ha : a ∈ SB (n → k)) (ha' : a' ∈ SB (n → k))
          (hb : b ∈ SB (n → k)) (hb' : b' ∈ SB (n → k)),
          fpair χ e μ a' b' • (Θ v (col Ψ₁ h₁ a ha) (row Ψ₂ h₂ b hb)).1 =
            fpair χ e μ a b • (Θ v (col Ψ₁ h₁ a' ha') (row Ψ₂ h₂ b' hb')).1 := by
        intro v Ψ₁ h₁ Ψ₂ h₂ a a' b b' ha ha' hb hb'
        rw [hΘ, hΘ]
        exact HC n n' n'' σ B J B' s₁ s₂ l vL α α₀ β γ γ₀ hα hγ μ L₁ L₂ L₂' L₃ f₁ _ _ f₂ _ _ Ψ₁ Ψ₂ a a' b b' ha ha' hb hb'
          (a₁ (col Ψ₁ h₁ a ha)) (a₁ (col Ψ₁ h₁ a' ha')) (a₂ (row Ψ₂ h₂ b hb)) (a₂ (row Ψ₂ h₂ b' hb')) v.1 v.2

      obtain ⟨DualityPairingFormula, DualityIsometry⟩ := D1 P
      generalize ((resCard k : ℂ) ^ Fintype.card n) = r at DualityPairingFormula DualityIsometry
      let vP : caSub B.A := ⟨φ P, hφ.2.2 P⟩
      let yP : SB (Matrix (n'' ⊕ Fin 1) n k) := row (latInd Q.lat Λ) hL btot hbtot
      have hM : ∀ Q' : Pair k n, (latInd P.ker Q'.ker + mainDatum q (resChar χ hχ q) 1 P Q') ∈ SB (Matrix n n' k) :=
        fun Q' => add_mem (latInd_mem_SB _ _) (GlobalTheory.T.gluedLatticeDatum_mainPart_mem_schwartzBruhat k n n' q _ 1 P Q')
      let x₀ : SB (Matrix n (n' ⊕ Fin 1) k) := col (latInd P.ker Q.lat) (latInd_mem_SB _ _) (vecInd Q.lat) hvec
      let xm : Pair k n → SB (Matrix n (n' ⊕ Fin 1) k) := fun Q' =>
        col (latInd P.ker Q'.ker + mainDatum q (resChar χ hχ q) 1 P Q') (hM Q') (charInd (resChar χ hχ q) Q')
          (charInd_mem' _ Q')
      let xmv : Pair k n → SB (Matrix n (n' ⊕ Fin 1) k) := fun Q' =>
        col (latInd P.ker Q'.ker + mainDatum q (resChar χ hχ q) 1 P Q') (hM Q') (vecInd Q.lat) hvec
      let xL : SB (Matrix n (n' ⊕ Fin 1) k) := col (latInd P.lat Q.lat) (latInd_mem_SB _ _) (vecInd Q.lat) hvec
      have hΞ₁ : Ξ₁ = U₁ (r⁻¹ • (x₀ + ∑ Q' ∈ withLat Q.lat, xm Q')) := by
        rw [b₁ ⟨_, o₁.2.2.2.1⟩ Ξ₁ o₁]
        congr 1
        apply Subtype.ext
        simp only [Submodule.coe_smul, Submodule.coe_add, Submodule.coe_sum]
        exact DualityPairingFormula
      have hs : x₀ + ∑ Q' ∈ withLat Q.lat, xmv Q' = r • xL := by
        apply Subtype.ext
        simp only [Submodule.coe_smul, Submodule.coe_add, Submodule.coe_sum]
        show tensCol (latInd P.ker Q.lat) (vecInd Q.lat) + ∑ Q' ∈ withLat Q.lat,
            tensCol (latInd P.ker Q'.ker + mainDatum q (resChar χ hχ q) 1 P Q') (vecInd Q.lat) =
          r • tensCol (latInd P.lat Q.lat) (vecInd Q.lat)
        have e : r • tensCol (latInd P.lat Q.lat) (vecInd Q.lat) = tensCol (r • latInd P.lat Q.lat) (vecInd Q.lat) := by
          funext z
          simp only [tensCol, Pi.smul_apply, smul_eq_mul, mul_assoc]
        rw [e, ← DualityIsometry]
        funext z
        simp only [tensCol, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_mul]
      have hm : ∀ Q' ∈ withLat Q.lat, (Θ vP (xm Q') yP).1 = (Θ vP (xmv Q') yP).1 := by
        intro Q' hQ'
        have := key vP _ (hM Q') (latInd Q.lat Λ) hL (charInd (resChar χ hχ q) Q') (vecInd Q.lat) btot btot
          (charInd_mem' _ Q') hvec hbtot hbtot
        have f4 := GlobalTheory.T.fourierPairing_charIndicator_dualLattice_cosets k n q χ hχ e he μ Q'
        have f3 := GlobalTheory.T.fourierPairing_dualIndicator_add_nonzeroCosets k n q χ hχ e he μ Q.lat
        rw [mem_withLat.1 hQ', ← hbdef] at f4
        rw [← hbdef] at f3
        rw [f3, f4] at this
        exact smul_right_injective _ I0 this
      have hzero : (Θ vP xL yP).1 = 0 := by
        rw [hΘ]
        have h0 := SG2 L₁ L₂ f₁ (U₁ xL) (vecInd Q.lat) (Or.inl (a₁ xL)) φ hφ
        have : handBF s₁ l (φ P) (U₁ xL) = 0 := by
          funext g w
          rw [handBF_eq, h0]
          simp
        show handFB s₂ vL (handBF s₁ l (φ P) (U₁ xL)) (U₂ yP) = 0
        rw [this, handFB_zero]
      rw [hΞ₁, b₂ yP Ξ₂ o₂]
      calc hand0 s₁ s₂ l vL (φ P) (U₁ (r⁻¹ • (x₀ + ∑ Q' ∈ withLat Q.lat, xm Q'))) (U₂ yP)
          = (Θ vP (r⁻¹ • (x₀ + ∑ Q' ∈ withLat Q.lat, xm Q')) yP).1 := (hΘ vP _ _).symm
        _ = r⁻¹ • ((Θ vP x₀ yP).1 + ∑ Q' ∈ withLat Q.lat, (Θ vP (xm Q') yP).1) := by
          rw [map_smul, map_add, map_sum, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sum_apply,
            Submodule.coe_smul, Submodule.coe_add, Submodule.coe_sum]
        _ = r⁻¹ • ((Θ vP x₀ yP).1 + ∑ Q' ∈ withLat Q.lat, (Θ vP (xmv Q') yP).1) := by
          rw [Finset.sum_congr rfl hm]
        _ = r⁻¹ • (Θ vP (x₀ + ∑ Q' ∈ withLat Q.lat, xmv Q') yP).1 := by
          rw [map_add, map_sum, LinearMap.add_apply, LinearMap.sum_apply, Submodule.coe_add, Submodule.coe_sum]
        _ = 0 := by
          rw [hs, map_smul, LinearMap.smul_apply, Submodule.coe_smul, hzero, smul_zero, smul_zero]

end GlobalTheory.FinPl.Vertex
