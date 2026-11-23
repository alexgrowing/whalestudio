import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleUnif
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleUnfoldingStepAtGluedFinitePlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GluedPlaceSourceConstantProofStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd InDual mainDatum)
open GlobalTheory.FinPl.Comm (fpair)
open GlobalTheory.FinPl.Vertex

namespace GlobalTheory.FinPl.VertexExactCount

section Count

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

theorem card_withLat_smul (g : GL n k) (L : Submodule 𝒪[k] (n → k)) :
    (withLat (g • L)).card = (withLat L).card := by
  refine Finset.card_bij (fun P _ => g⁻¹ • P) ?_ ?_ ?_
  · intro P hP
    rw [mem_withLat] at hP ⊢
    rw [Pair.smul_lat, hP, inv_smul_smul]
  · intro P _ P' _ h
    exact MulAction.injective g⁻¹ h
  · intro P hP
    refine ⟨g • P, ?_, inv_smul_smul g P⟩
    rw [mem_withLat] at hP ⊢
    rw [Pair.smul_lat, hP]

theorem card_withLat_eq (Q Q₀ : Pair k n) : (withLat Q.lat).card = (withLat Q₀.lat).card := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GL n k) Q₀ Q
  rw [← hg, Pair.smul_lat, card_withLat_smul]

theorem card_withLat_pos (Q : Pair k n) : 0 < (withLat Q.lat).card :=
  Finset.card_pos.2 ⟨Q, mem_withLat.2 rfl⟩

open Classical in

def pairCount (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : Type) [Fintype n] [DecidableEq n] : ℕ :=
  if h : Nonempty (Pair k n) then (withLat h.some.lat).card else 1

theorem pairCount_pos : 0 < pairCount k n := by
  unfold pairCount
  split_ifs with h
  · exact card_withLat_pos _
  · exact one_pos

theorem card_withLat_eq_pairCount (Q : Pair k n) : (withLat Q.lat).card = pairCount k n := by
  unfold pairCount
  rw [dif_pos ⟨Q⟩]
  exact card_withLat_eq _ _

end Count

end GlobalTheory.FinPl.VertexExactCount

namespace GlobalTheory.FinPl.VertexExactCount

open Classical in

theorem vertexExact (D : D7) : VertexExact D := by
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
  intro n n' n'' _ _ _ _ _ _
  obtain ⟨r₁, e₁, hr₁, HS⟩ := GlobalTheory.T.gluedPlaceSourceConstant_proof D k p n n' q χ hχ
  refine ⟨r₁ * (pairCount k n : ℝ), e₁, mul_pos hr₁ (Nat.cast_pos.2 pairCount_pos), ?_⟩
  intro P Q R σ B J B' s₁ s₂ l vL hu₁ hu₂ α α₀ β γ γ₀ hα hγ L₁ L₂ L₂' L₃ f₁ Ξ₁ Ξ₁' f₂ Ξ₂ Ξ₂' o₁ o₁' o₂ o₂' φ hφ
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
  obtain ⟨-, D2, -⟩ := GlobalTheory.T.gluedLattice_finite_expansions_localField k n n'' q (resChar χ hχ q) (resChar_ne_one hχ q) Q.lat
  let μ : Measure (n → k) := Measure.pi fun _ => ν
  have I0 : fpair χ e μ (vecInd Q.lat) (dualInd Q.lat) ≠ 0 := Comm.fpair_ne_zero χ hχc e he μ Q.lat
  have hvec := Comm.vecInd_mem Q.lat
  have hdual := Comm.dualInd_mem Q.lat
  let col : ∀ Ψ : Matrix n n' k → ℂ, Ψ ∈ SB (Matrix n n' k) → ∀ a : (n → k) → ℂ, a ∈ SB (n → k) →
      SB (Matrix n (n' ⊕ Fin 1) k) := fun Ψ hΨ a ha => ⟨tensCol Ψ a, Comm.tensCol_mem hΨ ha⟩
  let row : ∀ Ψ : Matrix n'' n k → ℂ, Ψ ∈ SB (Matrix n'' n k) → ∀ b : (n → k) → ℂ, b ∈ SB (n → k) →
      SB (Matrix (n'' ⊕ Fin 1) n k) := fun Ψ hΨ b hb => ⟨tensRow Ψ b, Comm.tensRow_mem hΨ hb⟩
  have one_emb : ∀ {S₀ A L : HSp D} (o : OrthDec S₀ A L), o.emb (1, 1) = 1 := fun o => map_one o.emb
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
  let v' : caSub B.A := ⟨_, hFF P⟩
  let x : Pair k n → SB (Matrix n (n' ⊕ Fin 1) k) := fun Q' =>
    col (phiOne P Q') (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem P Q') (charInd (resChar χ hχ q) Q') (charInd_mem' _ Q')
  let xv : Pair k n' → Pair k n → SB (Matrix n (n' ⊕ Fin 1) k) := fun A Q' =>
    col (phiOne A Q') (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem A Q') (vecInd Q.lat) hvec
  let yd : Pair k n → SB (Matrix (n'' ⊕ Fin 1) n k) := fun Q'' =>
    row (phiOne Q'' R) (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem Q'' R) (dualInd Q.lat) hdual
  let y₀ : SB (Matrix (n'' ⊕ Fin 1) n k) := row (latInd Q.lat R.ker) (latInd_mem_SB _ _) (dualInd Q.lat) hdual
  let y : Pair k n → SB (Matrix (n'' ⊕ Fin 1) n k) := fun Q'' =>
    row (phiOne Q'' R) (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem Q'' R) (cosetInd q Q''.lat Q''.red) (GlobalTheory.T.dualLatticeCoset_indicator_isSchwartzBruhat k n q _ _)

  have h2 : hand0 s₁ s₂ l vL (φ P) Ξ₁ Ξ₂ = ((r₁ : ℂ) * chrPow s₁.χW (p.idele q.unit) e₁) •
      hand0 s₁ s₂ l vL (FFStar q (resChar χ hχ q) φ P) (U₁ (∑ Q' ∈ withLat Q.lat, x Q')) Ξ₂ :=
    lift_step s₁ s₂ l vL (hFF P) U₁ t₁ (withLat Q.lat) x Ξ₁ Ξ₂
      (HS ψ B.V₀ B.A B.L J.W₀ B.o B.ζ B.line B.cpt B.vA s₁.χV s₁.χW s₁.om₀ s₁.weil₀ hu₁.1 hu₁.2 α α₀ β hα P Q.lat
        L₁ L₂ f₁ Ξ₁ (fun Q' => U₁ (x Q')) o₁ (fun Q' _ => a₁ (x Q')) φ hφ)

  have hΞ₂ : Ξ₂ = U₂ (y₀ + ∑ Q'' ∈ withLat Q.lat, y Q'') := by
    rw [b₂ ⟨_, o₂.2.2.2.1⟩ Ξ₂ o₂]
    congr 1
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_sum]
    exact D2 R

  have t0 : ∀ Q' ∈ withLat Q.lat, (Θ v' (x Q') y₀).1 = 0 := fun Q' hQ' => by
    have := key v' (phiOne P Q') (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem P Q') (latInd Q.lat R.ker) (latInd_mem_SB _ _)
      (charInd (resChar χ hχ q) Q') (vecInd Q.lat) (dualInd Q.lat) (dualInd Q.lat) (charInd_mem' _ Q') hvec hdual hdual
    have hf := GlobalTheory.T.fourierPairing_pairCharIndicator_dualLatticeIndicator_zero k n q χ hχ e he μ Q'
    rw [mem_withLat.1 hQ'] at hf
    rw [hf, zero_smul] at this
    exact (smul_eq_zero.1 this).resolve_left I0

  have t1 : ∀ Q' ∈ withLat Q.lat, ∑ Q'' ∈ withLat Q.lat, (Θ v' (x Q') (y Q'')).1 =
      (Θ v' (xv P Q') (yd (ε • Q'))).1 := by
    intro Q' hQ'
    have hQ'l : Q'.lat = Q.lat := mem_withLat.1 hQ'
    have hmem : ε • Q' ∈ withLat Q.lat := mem_withLat.2 (by rw [Pair.dia_lat, hQ'l])
    rw [Finset.sum_eq_single_of_mem (ε • Q') hmem]
    · have := key v' (phiOne P Q') (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem P Q') (phiOne (ε • Q') R)
        (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem _ R) (charInd (resChar χ hχ q) Q') (vecInd Q.lat)
        (cosetInd q (ε • Q').lat (ε • Q').red) (dualInd Q.lat) (charInd_mem' _ Q') hvec (GlobalTheory.T.dualLatticeCoset_indicator_isSchwartzBruhat k n q _ _) hdual
      rw [(GlobalTheory.T.fourierPairing_pairCharIndicator_cosetIndicator k n q χ hχ e ε hεe μ Q' (ε • Q') (by rw [Pair.dia_lat])).1 rfl, hQ'l] at this
      exact smul_right_injective _ I0 this
    · intro Q'' hQ'' hne
      have hQ''l : Q''.lat = Q.lat := mem_withLat.1 hQ''
      have := key v' (phiOne P Q') (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem P Q') (phiOne Q'' R)
        (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem _ R) (charInd (resChar χ hχ q) Q') (vecInd Q.lat)
        (cosetInd q Q''.lat Q''.red) (dualInd Q.lat) (charInd_mem' _ Q') hvec (GlobalTheory.T.dualLatticeCoset_indicator_isSchwartzBruhat k n q _ _) hdual
      rw [(GlobalTheory.T.fourierPairing_pairCharIndicator_cosetIndicator k n q χ hχ e ε hεe μ Q' Q'' (hQ''l.trans hQ'l.symm)).2 hne, zero_smul] at this
      exact (smul_eq_zero.1 this).resolve_left I0

  have hmove : ∀ (Q₀ : Pair k n) (g : GL n k), g • Q.lat = Q.lat →
      (Θ v' (xv P (g • Q₀)) (yd (g • ε • Q₀))).1 = (Θ v' (xv P Q₀) (yd (ε • Q₀))).1 := by
    intro Q₀ g hgL
    have hdet := GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.valuation_det_of_fix Q.lat hgL
    have hgL' : g⁻¹ • Q.lat = Q.lat := by
      conv_lhs => rw [← hgL]
      exact inv_smul_smul g Q.lat
    have e1 : s₁.om₀ (α₀.gl 1, β.gl g) (U₁ (xv P Q₀)) = U₁ (xv P (g • Q₀)) := by
      refine b₁ _ _ ?_
      have := (lin₁ _ _ α₀ β L₁ L₂ f₁ _ _ (a₁ (xv P Q₀))).1 1 g
      convert this using 1
      funext z
      have hl : ((lS₁ (Matrix.GeneralLinearGroup.det (1 : GL (n' ⊕ Fin 1) k)) : ℂˣ) : ℂ) = 1 := by simp
      have hr : ((lT₁ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) = 1 := by rw [vT₁ _ hdet]; rfl
      show tensCol (phiOne P (g • Q₀)) (vecInd Q.lat) z = _ * _ * tensCol (phiOne P Q₀) (vecInd Q.lat) _
      rw [hl, hr, one_mul, one_mul,
        show (1 : GL (n' ⊕ Fin 1) k) = GlobalTheory.RootEx.embX 1 (1 : GL n' k) from (map_one _).symm,
        tensCol_subst' (vecInd Q.lat) ((g⁻¹ : GL n k) : Matrix n n k) (1 : GL n' k)
          (Ψ' := phiOne P (g • Q₀)) (fun x => by
            have := phiOne_smul (P := P) (Q := Q₀) (x := x) (1 : GL n' k) g
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
    have e3 := Comm.doubleThetaUnfolding_equivariant_unitaryGroups s₁ s₂ l vL (hFF P) (t₁ (xv P Q₀)) (t₂ (yd (ε • Q₀))) 1 (β.gl g) 1
    rw [one_emb, one_emb] at e3
    rw [hΘ, hΘ, ← e1, ← e2, map_one α₀.gl, map_one γ₀.gl]
    rw [show (fun x : GA D B.A => FFStar q (resChar χ hχ q) φ P (x * 1)) = FFStar q (resChar χ hχ q) φ P from
      funext fun x => by rw [mul_one]] at e3
    rw [e3]
    funext x
    rw [mul_one]
  have hall : ∀ Q' ∈ withLat Q.lat, (Θ v' (xv P Q') (yd (ε • Q'))).1 =
      (Θ v' (xv P (ε⁻¹ • Q)) (yd (ε • ε⁻¹ • Q))).1 := by
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
  obtain ⟨g₁, hg₁a, hg₁b, hg₁d⟩ : ∃ g₁ : GL n' k, g₁ • P = ε • P ∧ g₁ • (ε • P) = P ∧
      valuation k ((Matrix.GeneralLinearGroup.det g₁ : kˣ) : k) = 1 := by
    rcases hεe with ⟨-, h⟩ | ⟨-, h⟩
    · exact ⟨1, by rw [h, one_smul, one_smul], by rw [h, one_smul, one_smul], by simp⟩
    · refine ⟨-1, by rw [neg_one_smul_pair, h], ?_, val_det_neg_one⟩
      rw [neg_one_smul_pair, h, smul_smul]
      simp
  have hfin : (Θ v' (xv P (ε⁻¹ • Q)) (yd (ε • ε⁻¹ • Q))).1 =
      hand0 s₁ s₂ l vL (dia ε (FFStar q (resChar χ hχ q) φ) P) Ξ₁' Ξ₂' := by
    rw [hΘ, b₁ (xv P Q) Ξ₁' o₁', b₂ (yd Q) Ξ₂' o₂', dia_apply, smul_inv_smul]
    have hx : xv P (ε⁻¹ • Q) = xv (ε • P) Q := by
      apply Subtype.ext
      show tensCol (phiOne P (ε⁻¹ • Q)) _ = tensCol (phiOne (ε • P) Q) _
      have := phiOne_dia (P := P) (Q := ε⁻¹ • Q) ε
      rw [smul_inv_smul] at this
      rw [this]
    rw [hx]
    have := hsrc g₁ hg₁d P (ε • P)
    rw [hg₁a, hg₁b] at this
    exact this.symm
  have hexp : hand0 s₁ s₂ l vL (FFStar q (resChar χ hχ q) φ P) (U₁ (∑ Q' ∈ withLat Q.lat, x Q'))
      (U₂ (y₀ + ∑ Q'' ∈ withLat Q.lat, y Q'')) =
      ∑ Q' ∈ withLat Q.lat, ((Θ v' (x Q') y₀).1 + ∑ Q'' ∈ withLat Q.lat, (Θ v' (x Q') (y Q'')).1) := by
    refine (hΘ v' _ _).symm.trans ?_
    rw [map_sum, LinearMap.sum_apply, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun Q' _ => ?_
    rw [map_add, map_sum, Submodule.coe_add, Submodule.coe_sum]
  rw [h2, hΞ₂, hexp, Finset.sum_congr rfl fun Q' hQ' => by rw [t0 Q' hQ', zero_add, t1 Q' hQ', hall Q' hQ'],
    Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hfin, card_withLat_eq_pairCount Q]
  congr 1
  push_cast
  ring

end GlobalTheory.FinPl.VertexExactCount
