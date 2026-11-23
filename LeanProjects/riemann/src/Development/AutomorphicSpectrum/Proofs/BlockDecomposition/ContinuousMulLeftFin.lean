import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.EmDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBoundFiniteInfinite
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperateMultiplierPreservesSchwartz
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroCoefficientTotal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEqSmulOfInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationInvariantFunctionalRestrict
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnipotentAtTauMemStabilizer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSmallCompactLevelSymplecticCharacterTrivia
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionAdeleRealComponentsCmType
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsClopenCompactNbhdZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntOffOfSmul

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology SchwartzMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.AlgRich

variable {D : D7}

variable {a r t n : ℕ} {S : Finset (Pl D)} {e : AE D}

theorem theta_idem {θ : InfFam D} (hθ : IsInfFam θ) (hid : IsIdem S e) (τ : D.what₂.Tau) : θ τ (infPart D e) = 1 := by
  have h := ((GlobalTheory.StdUnn.RealComp.real_components D θ hθ).1 (e - 1)).1 (fun w => by
    rw [RingHom.map_sub, hid.1 w, map_one, sub_self])
  have h' := h τ
  rw [RingHom.map_sub, RingHom.map_sub, map_one, map_one, sub_eq_zero] at h'
  exact h'

theorem clopen_sep (D : D7) {x y : Af D.host.F ⊗[D.host.F] D.host.E} (h : x ≠ y) :
    ∃ U : Set (Af D.host.F ⊗[D.host.F] D.host.E), IsClopen U ∧ x ∈ U ∧ y ∉ U := by
  have hne : GlobalTheory.AfTensNbhd.coordEquiv D.host.F D.host.E x ≠ GlobalTheory.AfTensNbhd.coordEquiv D.host.F D.host.E y :=
    fun h' => h ((GlobalTheory.AfTensNbhd.coordEquiv D.host.F D.host.E).injective h')
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hne
  haveI : T2Space (Af D.host.F) := GlobalTheory.IntegralFinAdele.t2Space_finiteAdeleRing' D.host.F
  have hd : GlobalTheory.AfTensNbhd.coordEquiv D.host.F D.host.E y k - GlobalTheory.AfTensNbhd.coordEquiv D.host.F D.host.E x k ≠ 0 :=
    sub_ne_zero.2 hk.symm
  obtain ⟨G, hGo, hGs⟩ := GlobalTheory.SmallLevel.exists_open_subgroup D.host.F
    {GlobalTheory.AfTensNbhd.coordEquiv D.host.F D.host.E y k - GlobalTheory.AfTensNbhd.coordEquiv D.host.F D.host.E x k}ᶜ
    (isOpen_compl_singleton.mem_nhds (by simpa using hd.symm))
  have hGc : IsClosed (G : Set (Af D.host.F)) := G.isClosed_of_isOpen hGo
  have hcont : Continuous fun w => GlobalTheory.AfTensNbhd.coordEquiv D.host.F D.host.E w k -
      GlobalTheory.AfTensNbhd.coordEquiv D.host.F D.host.E x k :=
    ((continuous_apply k).comp (GlobalTheory.AfTensNbhd.continuous_coordEquiv _ _)).sub continuous_const
  refine ⟨(fun w => GlobalTheory.AfTensNbhd.coordEquiv D.host.F D.host.E w k -
      GlobalTheory.AfTensNbhd.coordEquiv D.host.F D.host.E x k) ⁻¹' G, ⟨hGc.preimage hcont, hGo.preimage hcont⟩, ?_, ?_⟩
  · simp
  · intro hy
    exact hGs hy rfl

theorem continuous_mul_left_fin (D : D7) (c : Af D.host.F ⊗[D.host.F] D.host.E) :
    Continuous fun y : Af D.host.F ⊗[D.host.F] D.host.E => c * y := by
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (Af D.host.F) _
  exact continuous_const.mul continuous_id

theorem sep_pts {θ : InfFam D} (hθ : IsInfFam θ) (hid : IsIdem S e) (he : e * e = e) {p q : Mx D a n}
    (hp : e • p = p) (hq : e • q = q) (hpq : p ≠ q) {B : Mx D a n → ℂ} (hB : B ∈ schwartzA θ a n) (hG : Good S e B)
    (hC : HasCompactSupport B) (Bp : B p = 1) (Bq : B q = 1) :
    ∃ Φ ∈ schwartzA θ a n, Good S e Φ ∧ HasCompactSupport Φ ∧ Φ p ≠ Φ q := by
  have hsm : ∀ (x : Mx D a n) i j, (e • x) i j = e * x i j := fun _ _ _ => rfl
  by_cases hf : p.map (finPart D) = q.map (finPart D)
  · have hi : ¬ ∀ τ, compAt θ τ p = compAt θ τ q := fun h => hpq (GlobalTheory.StabAtPlace.mx_ext hθ hf h)
    simp only [not_forall] at hi
    obtain ⟨τ, hτ⟩ := hi
    obtain ⟨i, j, hij⟩ : ∃ i j, compAt θ τ p i j ≠ compAt θ τ q i j := by
      by_contra hc
      simp only [not_exists, not_not] at hc
      exact hτ (Matrix.ext hc)
    let L : (D.what₂.Tau → Fin a → Fin n → ℂ) →L[ℝ] ℂ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j).comp
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin a => Fin n → ℂ) i).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : D.what₂.Tau => Fin a → Fin n → ℂ) τ))
    refine ⟨_, GlobalTheory.CompanionTheory.WSum.mul_mem_schwartzA D θ a n L L.hasTemperateGrowth _ hB, ?_, hC.mul_left, ?_⟩
    · refine good_factor (M := fun x => L fun τ i j => compAt θ τ x i j) (fun x => ?_) hG
      show θ τ (infPart D (e * x i j)) = θ τ (infPart D (x i j))
      rw [map_mul, map_mul, theta_idem hθ hid, one_mul]
    · show compAt θ τ p i j * B p ≠ compAt θ τ q i j * B q
      rw [Bp, Bq, mul_one, mul_one]
      exact hij
  · obtain ⟨i, j, hij⟩ : ∃ i j, finPart D (p i j) ≠ finPart D (q i j) := by
      by_contra hc
      simp only [not_exists, not_not] at hc
      exact hf (Matrix.ext hc)
    obtain ⟨U, hU, hxU, hyU⟩ := clopen_sep D hij
    have hI : IsLocallyConstant (U.indicator fun _ => (1 : ℂ)) :=
      (LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) hU).isLocallyConstant
    let H : (Fin a → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ :=
      fun y => U.indicator (fun _ => (1 : ℂ)) (finPart D e * y i j)
    have hH : IsLocallyConstant H := hI.comp_continuous
      ((continuous_mul_left_fin D _).comp ((continuous_apply j).comp (continuous_apply i)))
    have hval : ∀ {x : Mx D a n}, e • x = x → H (fun i j => finPart D (x i j)) = U.indicator (fun _ => (1 : ℂ)) (finPart D (x i j)) := by
      intro x hx
      show U.indicator (fun _ => (1 : ℂ)) (finPart D e * finPart D (x i j)) = _
      rw [← map_mul, ← hsm, hx]
    refine ⟨_, fin_mul_mem θ hH hB, ?_, hC.mul_left, ?_⟩
    · refine good_factor (M := fun x => H fun i j => finPart D (x i j)) (fun x => ?_) hG
      show U.indicator (fun _ => (1 : ℂ)) (finPart D e * finPart D (e * x i j)) =
        U.indicator (fun _ => (1 : ℂ)) (finPart D e * finPart D (x i j))
      rw [← map_mul, ← map_mul, ← mul_assoc, he]
    · show (H fun i j => finPart D (p i j)) * B p ≠ (H fun i j => finPart D (q i j)) * B q
      rw [hval hp, hval hq, Bp, Bq, Set.indicator_of_mem hxU, Set.indicator_of_notMem hyU]
      simp

theorem bump_of (hBump : BumpEx) {θ : InfFam D} (hθ : IsInfFam θ) (hid : IsIdem S e) {C : Set (Mx D a n)}
    (hC : IsCompact C) (hCi : ∀ x ∈ C, e • x = x) :
    ∃ Φ ∈ schwartzA θ a n, Good S e Φ ∧ HasCompactSupport Φ ∧ (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧ ∀ x ∈ C, Φ x = 1 := by
  obtain ⟨η, hη⟩ := hBump D θ hθ a n S e hid C hC (fun x hx => intOff_of_smul hid (hCi x hx))
  obtain ⟨m1, m2, m3⟩ := row_prod (S := S) (e := e) (θ := θ) a η (fun i => ⟨(hη i).1, (hη i).2.1, (hη i).2.2.1⟩)
  refine ⟨_, m1, m2, m3, fun x => ?_, fun x hx => Finset.prod_eq_one fun i _ => (hη i).2.2.2.2 x hx⟩
  have e1 : (∏ i, η i (x.submatrix (fun _ => i) id)) = ((∏ i, (η i (x.submatrix (fun _ => i) id)).re : ℝ) : ℂ) := by
    push_cast
    exact Finset.prod_congr rfl fun i _ => Complex.ext (by simp) (by simpa using (hη i).2.2.2.1 _ |>.2.2)
  show 0 ≤ (∏ i, η i (x.submatrix (fun _ => i) id)).re ∧ (∏ i, η i (x.submatrix (fun _ => i) id)).im = 0
  rw [e1, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨Finset.prod_nonneg fun i _ => ((hη i).2.2.2.1 _).1, rfl⟩

theorem smul_jn (hn : r + t = n) (x : Mx D a r) (v : Mx D a t) : e • jn hn x v = jn hn (e • x) (e • v) := by
  ext i j
  simp only [jn, Matrix.smul_apply, Matrix.submatrix_apply, id]
  generalize (finSumFinEquiv.trans (finCongr hn)).symm j = k
  cases k <;> simp

theorem isClosedEmbedding_jn (hn : r + t = n) (e : AE D) :
    Topology.IsClosedEmbedding (fun z : XS D a r t e => jn hn z.1.1 z.1.2) := by
  subst hn
  obtain ⟨-, -, h2, -⟩ := GlobalTheory.CompanionTheory.OrbUniq.mx_facts D a (r + t)
  obtain ⟨-, -, h2r, -⟩ := GlobalTheory.CompanionTheory.OrbUniq.mx_facts D a r
  obtain ⟨-, -, h2t, -⟩ := GlobalTheory.CompanionTheory.OrbUniq.mx_facts D a t
  haveI : IsTopologicalRing (AE D) := GlobalTheory.Doubling.isTopologicalRing_tens
  have hcl : IsClosed {z : Mx D a r × Mx D a t | e • z.1 = z.1 ∧ e • z.2 = z.2} :=
    (isClosed_eq ((continuous_const_smul e).comp continuous_fst) continuous_fst).inter
      (isClosed_eq ((continuous_const_smul e).comp continuous_snd) continuous_snd)
  have hs : Topology.IsClosedEmbedding (Subtype.val : XS D a r t e → Mx D a r × Mx D a t) := hcl.isClosedEmbedding_subtypeVal
  have hj : Continuous fun z : Mx D a r × Mx D a t => jn (rfl : r + t = r + t) z.1 z.2 := by
    refine continuous_matrix fun i j => ?_
    simp only [jn, Matrix.submatrix_apply, id]
    generalize (finSumFinEquiv.trans (finCongr (rfl : r + t = r + t))).symm j = k
    cases k with
    | inl k =>
      simp only [Matrix.fromCols_apply_inl]
      exact continuous_fst.matrix_elem i k
    | inr k =>
      simp only [Matrix.fromCols_apply_inr]
      exact continuous_snd.matrix_elem i k
  have hu : Continuous fun x : Mx D a (r + t) =>
      ((x.submatrix id (Fin.castAdd t) : Mx D a r), (x.submatrix id (Fin.natAdd r) : Mx D a t)) :=
    (continuous_id.matrix_submatrix _ _).prodMk (continuous_id.matrix_submatrix _ _)
  have hl : Function.LeftInverse (fun x : Mx D a (r + t) =>
      ((x.submatrix id (Fin.castAdd t) : Mx D a r), (x.submatrix id (Fin.natAdd r) : Mx D a t)))
      (fun z : Mx D a r × Mx D a t => jn (rfl : r + t = r + t) z.1 z.2) := by
    intro z
    refine Prod.ext ?_ ?_
    · ext i j
      simp [jn]
    · ext i j
      simp [jn]
  exact (hl.isClosedEmbedding hu hj).comp hs

theorem exists_of_mem_algA {θ : InfFam D} (hn : r + t = n) {f : XS D a r t e → ℂ}
    (hf : f ∈ algA (a := a) θ hn S e) :
    ∃ Φ ∈ schwartzA θ a n, Good S e Φ ∧ HasCompactSupport Φ ∧ f = fun z => Φ (jn hn z.1.1 z.1.2) := by
  induction hf using Submodule.span_induction with
  | mem f h => exact h
  | zero => exact ⟨fun _ => 0, (schwartzA θ a n).zero_mem, good_zero, HasCompactSupport.zero, rfl⟩
  | add f g _ _ h₁ h₂ =>
    obtain ⟨Φ, m1, g1, c1, rfl⟩ := h₁
    obtain ⟨Ψ, m2, g2, c2, rfl⟩ := h₂
    exact ⟨fun x => Φ x + Ψ x, (schwartzA θ a n).add_mem m1 m2, good_add g1 g2, c1.add c2, rfl⟩
  | smul c f _ h₁ =>
    obtain ⟨Φ, m1, g1, c1, rfl⟩ := h₁
    exact ⟨fun x => c * Φ x, (schwartzA θ a n).smul_mem c m1, good_smul c g1, c1.mul_left, rfl⟩

theorem algRich : IdemEx → BumpEx → TopX → AlgRich := by
  intro hI hBump _ D θ hθ a r t n hn S e hid
  have he : e * e = e := ((hI D S).2 e hid).1
  have hι := isClosedEmbedding_jn (D := D) (a := a) hn e
  have gen : ∀ Φ ∈ schwartzA θ a n, Good S e Φ → HasCompactSupport Φ →
      (fun z : XS D a r t e => Φ (jn hn z.1.1 z.1.2)) ∈ algA (a := a) θ hn S e :=
    fun Φ h1 h2 h3 => Submodule.subset_span ⟨Φ, h1, h2, h3, rfl⟩
  have hfix : ∀ z : XS D a r t e, e • jn hn z.1.1 z.1.2 = jn hn z.1.1 z.1.2 := fun z => by
    rw [smul_jn, z.2.1, z.2.2]
  refine ⟨⟨fun f hf => ?_, fun f hf g hg => ?_, fun f hf => ?_, fun x y hxy => ?_, fun C hC => ?_⟩,
    fun f hf => exists_of_mem_algA hn hf⟩
  · obtain ⟨Φ, h1, -, h3, rfl⟩ := exists_of_mem_algA hn hf
    exact ⟨(GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ a n Φ h1).1.comp hι.continuous,
      h3.comp_isClosedEmbedding hι⟩
  · obtain ⟨Φ, h1, h2, h3, rfl⟩ := exists_of_mem_algA hn hf
    obtain ⟨Ψ, k1, k2, k3, rfl⟩ := exists_of_mem_algA hn hg
    exact gen (fun x => Φ x * Ψ x) (mul_mem θ h1 k1) (good_mul h2 k2) h3.mul_right
  · obtain ⟨Φ, h1, h2, h3, rfl⟩ := exists_of_mem_algA hn hf
    exact gen (fun x => conj (Φ x)) (conj_mem θ h1) (good_conj h2) (h3.comp_left (map_zero _))
  · have hne : jn hn x.1.1 x.1.2 ≠ jn hn y.1.1 y.1.2 := fun h => hxy (hι.injective h)
    have hfin : ({jn hn x.1.1 x.1.2, jn hn y.1.1 y.1.2} : Set (Mx D a n)).Finite := by simp
    obtain ⟨B, b1, b2, b3, -, b5⟩ := bump_of hBump hθ hid hfin.isCompact (by
      rintro w (rfl | rfl)
      · exact hfix x
      · exact hfix y)
    obtain ⟨Φ, h1, h2, h3, h4⟩ := sep_pts hθ hid he (hfix x) (hfix y) hne b1 b2 b3 (b5 _ (by simp)) (b5 _ (by simp))
    exact ⟨_, gen Φ h1 h2 h3, h4⟩
  · obtain ⟨B, b1, b2, b3, b4, b5⟩ := bump_of hBump hθ hid (hC.image hι.continuous) (by
      rintro _ ⟨z, -, rfl⟩
      exact hfix z)
    exact ⟨_, gen B b1 b2 b3, fun z => b4 _, fun z hz => b5 _ ⟨z, hz, rfl⟩⟩

end GlobalTheory.CompanionTheory.AlgRich

end
