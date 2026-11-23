import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierCoefficientConjugation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianBlockDiagonalNormalForm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankDirectSumHermitianLt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicUnipotentLeviFactor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionLeftInvariantRationalParabolic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientUnipotentLeviInvariance
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResEtaOfIsWeilSch

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L GlobalTheory.CompanionTheory.PcFc GlobalTheory.CompanionTheory.FourierN

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace GlobalTheory.CompanionTheory.RkCoef

variable {D : D7} {a b c n r t : ℕ}

theorem weil_law {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω)
    (hψ : IsCharAF D.host.F ψ)
    (s : ℂ) (hs : s + (n : ℂ) / 2 = (V.rank : ℂ) / 2) (Φ : schwartzA θ V.rank n) :
    IsLaw χ s (fun g => (ω g Φ).1 0) := by
  intro q hq a ha g
  obtain ⟨g₁, g₂, b, rfl, h1, h2⟩ := GlobalTheory.CompanionTheory.SiegelNM.unip_mul_levi D n q hq a ha
  show (ω (g₁ * g₂ * g) Φ).1 0 = _
  rw [map_mul, map_mul]
  show (ω g₁ (ω g₂ (ω g Φ))).1 0 = _
  rw [hω.unip g₁ b h1, hω.levi g₂ a h2, hs]
  have e0 : GlobalTheory.StdUnn.inner V (0 : Mx D V.rank n) 0 = 0 := by
    simp [GlobalTheory.StdUnn.inner, adj]
  rw [e0]
  simp [halfTr]

theorem rsec_translate {V : HSp D} {ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ)
    (b₀ : HermE D ρ) {θ : InfFam D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (Φ : schwartzA θ V.rank n) (g : G D n)
    (Ω : G D p → Mx D ρ p → ℂ) :
    Rsec M m ψ b₀ (fun g' => (ω g' Φ).1 0) g Ω = Rsec M m ψ b₀ (fun g' => (ω g' (ω g Φ)).1 0) 1 Ω := by
  funext h
  unfold Rsec Wz
  simp only [mul_one]
  congr 1
  funext y
  congr 1
  congr 1
  funext z
  have : ω (M.w * M.nzx z 0 * (M.sh y * M.emb h * g)) Φ = ω (M.w * M.nzx z 0 * (M.sh y * M.emb h)) (ω g Φ) := by
    rw [← mul_assoc (M.w * M.nzx z 0), map_mul]
    rfl
  rw [this]

theorem sh_zero {ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) : M.sh 0 = 1 := by
  apply GlobalTheory.CompanionTheory.FourierN.mat_injective
  have h0 : adj (0 : Mx D ρ p) = 0 := by simp [adj]
  rw [M.sh_mat, h0, neg_zero, GlobalTheory.CompanionTheory.WzHeis.blockRowSubstitution_one, GlobalTheory.StdUnn.LeftInvSect.mat_one, block_matrix_one]

theorem weil_rat {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω)
    (hχ : IsHeckeChar D χ) (a : GL (Fin n) D.host.E) {q : G D n}
    (hq : mat q = blk4 (rat a.1) 0 0 (adj (rat (a⁻¹).1))) (Ψ : schwartzA θ V.rank n) (x : Mx D V.rank n) :
    (ω q Ψ).1 x = Ψ.1 (mm x (rat a.1)) := by
  let aA : GL (Fin n) (AE D) := Matrix.GeneralLinearGroup.map (incA D) a
  have h1 : aA.1 = rat a.1 := rfl
  have h2 : (aA⁻¹).1 = rat (a⁻¹).1 := by
    show ((Matrix.GeneralLinearGroup.map (incA D) a)⁻¹).1 = _
    rw [← map_inv]
    rfl
  have hd : Matrix.GeneralLinearGroup.det aA = Units.map (incA D).toMonoidHom (Matrix.GeneralLinearGroup.det a) := by
    apply Units.ext
    show aA.1.det = incA D a.1.det
    rw [h1]
    exact (RingHom.map_det (incA D) a.1).symm
  have := hω.levi q aA (by rw [h1, h2]; exact hq) Ψ x
  rw [this, hd, hχ.2, show absA D (Units.map (incA D).toMonoidHom (Matrix.GeneralLinearGroup.det a)) = 1 from absE_inclR _]
  simp [npow]
  rfl

section Transport
variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [T2Space A] [LocallyCompactSpace A]
  [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]

theorem map_eq_self (Γ : AddSubgroup A) [Countable Γ] (T : A ≃ₜ+ A) (hT : ∀ a, T a ∈ Γ ↔ a ∈ Γ) (μ : Measure A)
    [μ.IsAddHaarMeasure] {s : Set A} (hs : IsAddFundamentalDomain Γ s μ) (hs1 : μ s = 1) : μ.map T = μ := by
  have hAC : (μ.map T).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map μ T
  have hAC2 : (μ.map T.symm).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map μ T.symm
  have hsm : Measure.QuasiMeasurePreserving (T.symm.toAddEquiv.toEquiv) μ μ :=
    ⟨T.symm.continuous.measurable, Measure.absolutelyContinuous_isAddHaarMeasure _ _⟩
  let eΓ : Γ ≃ Γ :=
    { toFun := fun d => ⟨T.symm d.1, (hT _).1 (by simpa using d.2)⟩
      invFun := fun c => ⟨T c.1, (hT _).2 c.2⟩
      left_inv := fun d => Subtype.ext (by simp)
      right_inv := fun c => Subtype.ext (by simp) }
  have hFD : IsAddFundamentalDomain Γ (T.toAddEquiv.toEquiv '' s) μ :=
    hs.image_of_equiv T.toAddEquiv.toEquiv hsm eΓ (fun g x => by
      show T (T.symm g.1 + x) = g.1 + T x
      simp)
  have h1 : μ (T.toAddEquiv.toEquiv '' s) = 1 := by rw [hFD.measure_eq hs, hs1]
  have hemb : MeasurableEmbedding T := T.toHomeomorph.measurableEmbedding
  have h2 : μ.map T (T.toAddEquiv.toEquiv '' s) = 1 := by
    rw [hemb.map_apply, show T ⁻¹' (T.toAddEquiv.toEquiv '' s) = s from Set.preimage_image_eq _ T.injective, hs1]
  have h4 := Measure.isAddLeftInvariant_eq_smul (μ.map T) μ
  rw [h4] at h2
  have hc : Measure.addHaarScalarFactor (μ.map T) μ = 1 := by
    rw [Measure.smul_apply, h1, ENNReal.smul_def, smul_eq_mul, mul_one] at h2
    exact_mod_cast h2
  rw [h4, hc, one_smul]
end Transport

def rightT (t : ℕ) (a : GL (Fin n) D.host.E) : Mx D t n ≃ₜ+ Mx D t n where
  toFun x := mm x (rat a.1)
  invFun x := mm x (rat (a⁻¹).1)
  left_inv x := by
    show mm (mm x (rat a.1)) (rat (a⁻¹).1) = x
    rw [mm, mm, Matrix.mul_assoc, rat_gl_mul_inv, Matrix.mul_one]
  right_inv x := by
    show mm (mm x (rat (a⁻¹).1)) (rat a.1) = x
    rw [mm, mm, Matrix.mul_assoc, rat_gl_inv_mul, Matrix.mul_one]
  map_add' x y := Matrix.add_mul _ _ _
  continuous_toFun := continuous_id.matrix_mul continuous_const
  continuous_invFun := continuous_id.matrix_mul continuous_const

theorem map_right_rat {μ₁ : Measure (Mx D t n)} (h : ∃ 𝓕, IsCovolOne (ratMx D t n) μ₁ 𝓕) (a : GL (Fin n) D.host.E) :
    μ₁.map (rightT t a) = μ₁ := by
  obtain ⟨𝓕, hHaar, hFD, hvol⟩ := h
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D t n
  haveI : BorelSpace (Mx D t n) := ⟨rfl⟩
  haveI : DiscreteTopology (ratMx D t n) := i5
  haveI : SecondCountableTopology (ratMx D t n) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : Countable (ratMx D t n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  refine map_eq_self (ratMx D t n) (rightT t a) (fun x => ⟨fun hx => ?_, fun hx => ?_⟩) μ₁ hFD hvol
  · obtain ⟨γ, hγ⟩ := hx
    refine ⟨γ * (a⁻¹).1, ?_⟩
    have hγ' : rat γ = mm x (rat a.1) := hγ
    show rat (γ * (a⁻¹).1) = x
    rw [rat_mul, hγ']
    show mm (mm x (rat a.1)) (rat (a⁻¹).1) = x
    rw [mm, mm, Matrix.mul_assoc, rat_gl_mul_inv, Matrix.mul_one]
  · obtain ⟨γ, hγ⟩ := hx
    have hγ' : rat γ = x := hγ
    refine ⟨γ * a.1, ?_⟩
    show rat (γ * a.1) = mm x (rat a.1)
    rw [rat_mul, hγ']

theorem integral_right_rat {μ₁ : Measure (Mx D t n)} (h : ∃ 𝓕, IsCovolOne (ratMx D t n) μ₁ 𝓕) (a : GL (Fin n) D.host.E)
    (f : Mx D t n → ℂ) : ∫ x, f (mm x (rat a.1)) ∂μ₁ = ∫ x, f x ∂μ₁ := by
  haveI : BorelSpace (Mx D t n) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D t n
  have hemb : MeasurableEmbedding (rightT (D := D) t a) := (rightT t a).toHomeomorph.measurableEmbedding
  conv_rhs => rw [← map_right_rat h a]
  rw [hemb.integral_map]
  rfl

theorem ikp_rat {B W : HSp D} {d : HypDec B W t} (I : IkD d n) (Ψ : Mx D B.rank n → ℂ) (a : GL (Fin n) D.host.E)
    (Y : Mx D W.rank n) : ikp I (fun X => Ψ (mm X (rat a.1))) Y = ikp I Ψ (mm Y (rat a.1)) := by
  unfold ikp ikS
  have key : ∀ Z : Mx D B.rank n, projS I.νK (fun X => Ψ (mm X (rat a.1))) Z = projS I.νK Ψ (mm Z (rat a.1)) := by
    intro Z
    unfold projS
    congr 1
    funext k
    simp only [mm, Matrix.mul_assoc]
  simp only [key]
  rw [← integral_right_rat I.cov₁ a (fun x => projS I.νK Ψ (d.jX ⬝ x + d.j0 ⬝ mm Y (rat a.1)))]
  congr 1
  funext x
  congr 1
  simp only [mm, Matrix.add_mul, Matrix.mul_assoc]

theorem orb_rat (W : HSp D) (m : Measure (GA D W)) (Ψ : Mx D W.rank n → ℂ) (a : GL (Fin n) D.host.E)
    (x : Matrix (Fin W.rank) (Fin n) D.host.E) :
    orb W m (fun Y => Ψ (mm Y (rat a.1))) x = orb W m Ψ (x * a.1) := by
  unfold orb
  congr 1
  funext h
  rw [rat_mul]
  simp only [mm, Matrix.mul_assoc]

set_option synthInstance.maxHeartbeats 400000 in

theorem hasCompactSupport_rows {η : Fin r → Mx D 1 t → ℂ} (h : ∀ i, HasCompactSupport (η i)) :
    HasCompactSupport (fun y : Mx D r t => ∏ i, η i (y.submatrix (fun _ => i) id)) := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D r t
  let f : (Fin r → Mx D 1 t) → Mx D r t := fun u => Matrix.of fun i j => u i 0 j
  have hf : Continuous f := by
    refine continuous_matrix fun i j => ?_
    exact (continuous_apply i).matrix_elem 0 j
  have hK : IsCompact (f '' Set.pi Set.univ fun i => tsupport (η i)) :=
    (isCompact_univ_pi fun i => h i).image hf
  refine HasCompactSupport.intro hK fun y hy => ?_
  by_contra hne
  apply hy
  refine ⟨fun i => y.submatrix (fun _ => i) id, fun i _ => ?_, ?_⟩
  · apply subset_tsupport
    intro h0
    exact hne (Finset.prod_eq_zero (Finset.mem_univ i) h0)
  · ext i j
    rfl

theorem eq_of_pairing (hTP : ThProd) (hRT : RowTotal) (hr : 1 ≤ r) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hη : ResEta D χ r) {θ : InfFam D} (hθ : IsInfFam θ) (m : Meas D r t)
    (b₀ : HermE D r) (hb : IsDiagInv b₀) (A T : Mx D r t → ℂ) (hA : Continuous A) (hT : Continuous T)
    (h : ∀ Ω, IsTh ψ χ θ b₀ m.μ Ω → HasCompactSupport (Ω 1) →
      ∫ y, A y * conj (Ω 1 y) ∂m.μ = ∫ y, T y * conj (Ω 1 y) ∂m.μ) : A = T := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D r t
  haveI : BorelSpace (Mx D r t) := ⟨rfl⟩
  haveI : m.μ.IsAddHaarMeasure := m.hμ.1
  have hz := hRT D θ hθ r t m.μ m.hμ.1 (fun y => A y - T y) (hA.sub hT) (fun η hη' => ?_)
  · funext y
    exact sub_eq_zero.1 (congrFun hz y)
  obtain ⟨Ω, hΩ, hΩ1⟩ := hTP D r t m ψ hψ b₀ hb χ hχ hη hr θ hθ η (fun i => (hη' i).1)
  have hΩf : Ω 1 = fun y => ∏ i, η i (y.submatrix (fun _ => i) id) := funext hΩ1
  have hcs : HasCompactSupport (Ω 1) := by
    rw [hΩf]
    exact hasCompactSupport_rows fun i => (hη' i).2
  have hc1 : Continuous (Ω 1) := hΩ.cont.comp (Continuous.prodMk continuous_const continuous_id)
  have hcc : Continuous fun y => conj (Ω 1 y) := Complex.continuous_conj.comp hc1
  have hcsc : HasCompactSupport fun y => conj (Ω 1 y) := hcs.comp_left (g := fun z => conj z) (by simp)
  have iA : Integrable (fun y => A y * conj (Ω 1 y)) m.μ :=
    (hA.mul hcc).integrable_of_hasCompactSupport hcsc.mul_left
  have iT : Integrable (fun y => T y * conj (Ω 1 y)) m.μ :=
    (hT.mul hcc).integrable_of_hasCompactSupport hcsc.mul_left
  have e : ∀ y, (A y - T y) * conj (∏ i, η i (y.submatrix (fun _ => i) id)) = A y * conj (Ω 1 y) - T y * conj (Ω 1 y) := by
    intro y
    rw [hΩ1, sub_mul]
  simp only [e]
  rw [integral_sub iA iT, h Ω hΩ hcs, sub_self]

section LinAlg

theorem exists_complete {K : Type} [Field K] (hn : r + t = n) (c : Matrix (Fin r) (Fin n) K)
    (hc : LinearIndependent K (fun i => c i)) :
    ∃ a : GL (Fin n) K, ∀ (i : Fin r) j, a.1 (finSumFinEquiv.trans (finCongr hn) (Sum.inl i)) j = c i j := by
  classical
  let U := Submodule.span K (Set.range fun i => c i)
  obtain ⟨U', hU'⟩ := Submodule.exists_isCompl U
  have hdim : Module.finrank K U + Module.finrank K U' = n := by
    simpa using Submodule.finrank_add_eq_of_isCompl hU'
  have hUr : Module.finrank K U = r := by
    simpa using finrank_span_eq_card hc
  have hUt : Module.finrank K U' = t := by omega
  let b' : Module.Basis (Fin t) K U' := Module.finBasisOfFinrankEq K U' hUt
  let v : Fin r ⊕ Fin t → (Fin n → K) := Sum.elim (fun i => c i) (fun j => (b' j : Fin n → K))
  have hb' : LinearIndependent K (fun j => (b' j : Fin n → K)) :=
    b'.linearIndependent.map' U'.subtype (Submodule.ker_subtype _)
  have hsp : Submodule.span K (Set.range fun j => (b' j : Fin n → K)) ≤ U' := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact (b' j).2
  have hv : LinearIndependent K v := hc.sum_type hb' (hU'.disjoint.mono_right hsp)
  let e := finSumFinEquiv.trans (finCongr hn)
  let A : Matrix (Fin n) (Fin n) K := fun i => v (e.symm i)
  have hA : LinearIndependent K A.row := hv.comp e.symm e.symm.injective
  have hu : IsUnit A := Matrix.linearIndependent_rows_iff_isUnit.1 hA
  refine ⟨hu.unit, fun i j => ?_⟩
  show A (e (Sum.inl i)) j = c i j
  simp [A, v]

end LinAlg

theorem ext0_inl (hn : r + t = n) (x : Matrix (Fin a) (Fin r) D.host.E) (k : Fin a) (i : Fin r) :
    L.ext0 hn x k (finSumFinEquiv.trans (finCongr hn) (Sum.inl i)) = x k i := by
  simp only [L.ext0, Matrix.submatrix_apply, Equiv.symm_apply_apply, id, Matrix.fromCols_apply_inl]

theorem ext0_inr (hn : r + t = n) (x : Matrix (Fin a) (Fin r) D.host.E) (k : Fin a) (i : Fin t) :
    L.ext0 hn x k (finSumFinEquiv.trans (finCongr hn) (Sum.inr i)) = 0 := by
  simp only [L.ext0, Matrix.submatrix_apply, Equiv.symm_apply_apply, id, Matrix.fromCols_apply_inr, Matrix.zero_apply]

theorem matrixExtendByZero_mul (hn : r + t = n) (x : Matrix (Fin a) (Fin r) D.host.E) (A : Matrix (Fin n) (Fin n) D.host.E)
    (c : Matrix (Fin r) (Fin n) D.host.E)
    (h : ∀ (i : Fin r) j, A (finSumFinEquiv.trans (finCongr hn) (Sum.inl i)) j = c i j) : L.ext0 hn x * A = x * c := by
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply, ← Equiv.sum_comp (finSumFinEquiv.trans (finCongr hn)), Fintype.sum_sum_type]
  simp only [ext0_inl, ext0_inr, h, zero_mul, Finset.sum_const_zero, add_zero]

theorem gramQ_eq (W : HSp D) {p : ℕ} (x : Matrix (Fin W.rank) (Fin p) D.host.E) : gramQ W x = xᴴ * (W.gram * x) := rfl

theorem gramQ_mul (W : HSp D) {p q : ℕ} (x : Matrix (Fin W.rank) (Fin p) D.host.E) (c : Matrix (Fin p) (Fin q) D.host.E) :
    gramQ W (x * c) = cᴴ * gramQ W x * c := by
  simp only [gramQ_eq, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem gram_extend_by_zero (W : HSp D) (hn : r + t = n) (x : Matrix (Fin W.rank) (Fin r) D.host.E) :
    gramQ W (L.ext0 hn x) = bl hn (gramQ W x) 0 0 0 := by
  ext i j
  obtain ⟨i', rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective i
  obtain ⟨j', rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective j
  rcases i' with i' | i' <;> rcases j' with j' | j'
  all_goals
    simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, gramQ_eq, Matrix.mul_apply,
      Matrix.conjTranspose_apply, ext0_inl, ext0_inr, star_zero, zero_mul, mul_zero, Finset.sum_const_zero]

def ext0H (hn : r + t = n) (b₀ : HermE D r) : HermE D n := dsum hn b₀ ⟨0, by ext i j; simp⟩

set_option synthInstance.maxHeartbeats 400000 in

theorem fc_levi_mat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (F : G D n → ℂ)
    (hinv : LeftInv (GF D n) F) {nb : hermA D n → G D n} {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)}
    (hC : CoefData nb lam 𝓖) (a : GL (Fin n) D.host.E) (β : HermE D n) :
    ∃ q : G D n, mat q = blk4 (rat a.1) 0 0 (adj (rat (a⁻¹).1)) ∧
      ∀ g, fc ψ lam 𝓖 nb F β (q * g) = fc ψ lam 𝓖 nb F (cg a β) g := by
  obtain ⟨hnb, hlam, hFD, hvol⟩ := hC
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D n n
  haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
  haveI : BorelSpace (hermA D n) := Subtype.borelSpace _
  haveI : SecondCountableTopology (hermA D n) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : LocallyCompactSpace (hermA D n) := isClosed_hermA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : DiscreteTopology (ratHerm D n) := discrete_ratHerm
  haveI : SecondCountableTopology (ratHerm D n) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : Countable (ratHerm D n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨q, hqF, hq⟩ := exists_levi_rat (D := D) a
  refine ⟨q, hq, fun g => ?_⟩
  let f : hermA D n → ℂ := fun c =>
    F (nb c * g) * ψ (-halfTr (Matrix.trace (HMul.hMul ((cg a β).1.map (incA D)) c.1 : Mx D n n)))
  have hf : ∀ γ ∈ ratHerm D n, ∀ x, f (γ + x) = f x := by
    intro γ hγ x
    have e1 : F (nb (γ + x) * g) = F (nb x * g) := by
      rw [GlobalTheory.CompanionTheory.FourierN.nb_add hnb, mul_assoc]
      exact hinv _ (GlobalTheory.CompanionTheory.FourierN.nb_rat hnb γ hγ) _
    have e2 : ψ (-pr (cg a β).1 (γ + x).1) = ψ (-pr (cg a β).1 x.1) := by
      rw [show (γ + x).1 = γ.1 + x.1 from rfl, pr_add_right, neg_add, AddChar.map_add_eq_mul, ker_of_rat hψ γ hγ, one_mul]
    show F (nb (γ + x) * g) * ψ (-pr (cg a β).1 (γ + x).1) = F (nb x * g) * ψ (-pr (cg a β).1 x.1)
    rw [e1, e2]
  have key := mean_transport (ratHerm D n) (ratHerm D n) (tauH a) (tauH_rat a) lam lam hFD hFD hvol hvol f hf
  unfold fc
  refine Eq.trans (integral_congr_ae (.of_forall fun b => ?_)) key
  show F (nb b * (q * g)) * ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) =
    F (nb (tauH a b) * g) * ψ (-halfTr (Matrix.trace (HMul.hMul ((cg a β).1.map (incA D)) (tauH a b).1 : Mx D n n)))
  rw [trace_cg, ← mul_assoc, nb_levi hnb a hq b, mul_assoc, hinv q hqF]

theorem exists_orth (W : HSp D) : ∃ (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (b₀ : HermE D W.rank),
    IsDiagInv b₀ ∧ gramQ W x₀ = b₀.1 := by
  classical
  have hc : ∀ t, (D.sp.cm.sig : D.host.E →+* D.host.E) ((D.sp.cm.sig : D.host.E →+* D.host.E) t) = t :=
    fun x => star_star x
  have hGs : W.gramᴴ = W.gram := Matrix.ext fun a b => GlobalTheory.LatVac.gram_star W b a
  have hG : ∀ a b, (D.sp.cm.sig : D.host.E →+* D.host.E) (W.gram a b) = W.gram b a := fun a b => GlobalTheory.LatVac.gram_star W a b
  have hdet : W.gram.det ≠ 0 := (GlobalTheory.Doubling.isHermND_gram W).2
  obtain ⟨P, d, hP, hPG, hfix, hd⟩ := GlobalTheory.HermDiag.exists_congr_diagonal two_ne_zero hc hG
  have hG' : gramQ W (P.map (D.sp.cm.sig : D.host.E →+* D.host.E)) = Matrix.diagonal d := by
    have hT : (P.map (D.sp.cm.sig : D.host.E →+* D.host.E))ᴴ = Pᵀ := by
      refine Matrix.ext fun i j => ?_
      exact hc (P j i)
    rw [← hPG, gramQ_eq, hT, Matrix.mul_assoc]
  refine ⟨P.map (D.sp.cm.sig : D.host.E →+* D.host.E), ⟨Matrix.diagonal d, ?_⟩, ⟨Matrix.isDiag_diagonal d, ?_⟩, hG'⟩
  · ext i j
    by_cases hij : i = j
    · subst hij
      simpa using hfix i
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ (Ne.symm hij)]
  · show (Matrix.diagonal d).det ≠ 0
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hd hdet i

theorem rows_li {K : Type} [Field K] (c : Matrix (Fin r) (Fin n) K) (h : r ≤ c.rank) :
    LinearIndependent K (fun i => c i) := by
  rw [linearIndependent_iff_card_eq_finrank_span]
  have h1 : c.rank ≤ r := by simpa using c.rank_le_card_height
  have h2 := c.rank_eq_finrank_span_row
  have h3 : Set.finrank K (Set.range fun i => c i) = c.rank := by
    rw [h2]
    rfl
  rw [h3]
  simp
  omega

theorem rep_of_cg (W : HSp D) (hn : r + t = n) (a : GL (Fin n) D.host.E) (β : HermE D n) (b₁ : HermE D r) (β' : HermE D t)
    (hβ' : β'.1 = 0) (hcg : cg a β = dsum hn b₁ β') (x₁ : Matrix (Fin W.rank) (Fin r) D.host.E) (hx₁ : gramQ W x₁ = b₁.1) :
    gramQ W (L.ext0 hn x₁ * (a⁻¹).1) = β.1 := by
  rw [gramQ_mul, gram_extend_by_zero, hx₁]
  have h : bl hn b₁.1 0 0 0 = (cg a β).1 := by
    rw [hcg]
    show _ = bl hn b₁.1 0 0 β'.1
    rw [hβ']
  rw [h]
  show ((a⁻¹).1)ᴴ * (a.1ᴴ * β.1 * a.1) * (a⁻¹).1 = β.1
  have e1 : a.1 * (a⁻¹).1 = 1 := by simp
  have e2 : ((a⁻¹).1)ᴴ * a.1ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, e1, Matrix.conjTranspose_one]
  simp only [Matrix.mul_assoc, e1, Matrix.mul_one]
  rw [← Matrix.mul_assoc, e2, Matrix.one_mul]

theorem rank_cg (a : GL (Fin n) D.host.E) (β : HermE D n) : (cg a β).1.rank = β.1.rank := by
  have ha : IsUnit a.1.det := (Matrix.isUnit_iff_isUnit_det _).1 a.isUnit
  have hs : IsUnit (a.1ᴴ).det := by
    rw [Matrix.det_conjTranspose]
    exact ha.star
  show (a.1ᴴ * β.1 * a.1).rank = _
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ ha, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hs]

theorem det_ne_of_gram (W : HSp D) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (h : (gramQ W x₀).det ≠ 0) : x₀.det ≠ 0 := by
  intro h0
  apply h
  rw [gramQ_eq, Matrix.det_mul, Matrix.det_mul, h0]
  simp

theorem exists_frame (W : HSp D) (hn : W.rank + t = n) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (h0 : x₀.det ≠ 0)
    (x : Matrix (Fin W.rank) (Fin n) D.host.E) (hx : W.rank ≤ (gramQ W x).rank) :
    ∃ a : GL (Fin n) D.host.E, L.ext0 hn x₀ * a.1 = x := by
  have hu : IsUnit x₀.det := isUnit_iff_ne_zero.2 h0
  have hui : IsUnit (x₀⁻¹).det := by
    rw [Matrix.det_nonsing_inv]
    exact hu.ringInverse
  have hr : W.rank ≤ x.rank := by
    rw [gramQ_eq] at hx
    exact hx.trans ((Matrix.rank_mul_le_right _ _).trans (Matrix.rank_mul_le_right _ _))
  have hc : W.rank ≤ (x₀⁻¹ * x).rank := by
    rwa [Matrix.rank_mul_eq_right_of_isUnit_det _ _ hui]
  obtain ⟨a, ha⟩ := exists_complete hn _ (rows_li _ hc)
  refine ⟨a, ?_⟩
  rw [matrixExtendByZero_mul hn x₀ a.1 _ ha, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

theorem target : PositivityTheory.Rg.Rsw.Polar → PositivityTheory.Rg.Rsw.ResMu → PositivityTheory.Rg.Rsw.MapsExist → PositivityTheory.Rg.Rsw.CfFJ → PositivityTheory.Rg.Rsw.PcBound →
    PositivityTheory.Rg.Rsw.PcFc → PositivityTheory.Rg.Rsw.RSec → PositivityTheory.Rg.Rsw.HtExist → PositivityTheory.Rg.Rsw.L.ThProd → PositivityTheory.Rg.Rsw.L.RowTotal →
    PositivityTheory.Rg.Rsw.L.WMaj → PositivityTheory.Rg.Rsw.L.IkSch → PositivityTheory.Rg.Rsw.L.ThetaSideMeasure → PositivityTheory.Rg.Rsw.L.MuId → PositivityTheory.Rg.Rsw.L.CoefId := by
  intro hPolar hResMu hMaps hCfFJ hPcB hPcFc hRSec hHt hThP hRT hWMaj hIkS hT2 hMuId
  intro D n t B W d hn ψ χ θ μB μW ωB ωW hS I H hH Φ U dd E σ hC ε hε nb lam 𝓖 hCD
  have hr1 := hS.pos
  have hlt := hS.lt
  have hψ := hS.hψ
  have hχ := hS.hχ
  have hη := hS.hη
  have hθ := hS.hθ
  obtain ⟨⟨M⟩, ⟨m⟩⟩ := hMaps D n W.rank t hn
  obtain ⟨mu, hmu⟩ := hResMu D t (by omega)
  have hn0 : 0 < n := by omega
  obtain ⟨𝓕B, h𝓕B⟩ := hS.hμB
  have hηB : ResEta D χ B.rank := GlobalTheory.RegSch.JointCont.resEta_of_isWeilSch hn0 hψ hθ h𝓕B hS.hB
  have hcont : ∀ Φ' : schwartzA θ B.rank n, Continuous (fun g => (ωB g Φ').1 0) := fun Φ' =>
    ((hWMaj D n B ψ hψ χ hχ hηB θ hθ μB hS.hμB ωB hS.hB Φ').1).comp (Continuous.prodMk continuous_id continuous_const)
  have hlaw : ∀ Φ' : schwartzA θ B.rank n, IsLaw χ ((t : ℂ) / 2) (fun g => (ωB g Φ').1 0) := fun Φ' =>
    weil_law hS.hB hψ _ (by
      have hB' : (B.rank : ℂ) = W.rank + 2 * t := by exact_mod_cast d.rank_add.symm
      have hnC : (n : ℂ) = W.rank + t := by exact_mod_cast hn.symm
      rw [hB', hnC]
      ring) Φ'
  obtain ⟨hFc, hFi⟩ := (hCfFJ D n H _ _ U dd E σ hC ε hε).1 1
  have hpol := hPolar D n W.rank t hn hS.big ψ hψ χ hχ hη (by intro h; omega) θ hθ H hH _ (hcont Φ) (hlaw Φ) U dd E σ hC ε hε
  have hrank := hpol.1 1 le_rfl
  have hrho : ∀ b₀ : HermE D W.rank, b₀.1.det ≠ 0 → ∀ Ω, IsTh ψ χ θ b₀ m.μ Ω → ∀ Φ' : schwartzA θ B.rank n,
      IsRho (Rsec M m ψ b₀ (fun g => (ωB g Φ').1 0) 1 Ω) := by
    intro b₀ hb Ω hΩ Φ'
    obtain ⟨h1, -, h3⟩ := hRSec D n W.rank t hn M m ψ hψ b₀ hb χ χ hχ hχ θ hθ Ω hΩ H hH ((t : ℂ) / 2) _ (hcont Φ') (hlaw Φ') 1
    have hz : ((W.rank : ℝ) - t) / 2 < ((t : ℂ) / 2).re := by
      have h : (W.rank : ℝ) < t := by exact_mod_cast hlt
      have e : ((t : ℂ) / 2).re = (t : ℝ) / 2 := by simp
      rw [e]
      have ht : (0 : ℝ) ≤ W.rank := Nat.cast_nonneg _
      linarith
    have hfam : fam H (fun g => (ωB g Φ').1 0) ((t : ℂ) / 2) ((t : ℂ) / 2) = fun g => (ωB g Φ').1 0 := by
      funext g
      simp [fam, npow]
    have h3' := h3 _ hz
    rw [hfam, mul_inv_cancel] at h3'
    refine ⟨?_, h3'⟩
    have hc := h1.comp_continuous (f := fun h : G D t => (((t : ℂ) / 2), h))
      (Continuous.prodMk continuous_const continuous_id) (fun h => ⟨hz, Set.mem_univ _⟩)
    refine hc.congr fun h => ?_
    show Rsec M m ψ b₀ (fam H _ _ ((t : ℂ) / 2)) 1 Ω h = _
    rw [hfam]
  have key : ∀ b₀ : HermE D W.rank, IsDiagInv b₀ → ∀ β : HermE D n, IsExt hn b₀ β → ∀ (g : G D n) (T : Mx D W.rank t → ℂ),
      Continuous T → (∀ Ω, IsTh ψ χ θ b₀ m.μ Ω → HasCompactSupport (Ω 1) →
        mu (Rsec M m ψ b₀ (fun g' => (ωB g' (ωB g Φ)).1 0) 1 Ω) = ∫ y, T y * conj (Ω 1 y) ∂m.μ) →
      fc ψ lam 𝓖 nb (cf dd E ((t : ℂ) / 2) ε 1) β g = T 0 := by
    intro b₀ hb β hβ g T hT h
    have hpf := (hPcFc D n W.rank t hn M m ψ hψ _ hFc hFi).2 hrank b₀ hb.2 β hβ nb lam 𝓖 hCD
    have hpcc := (hPcB D n W.rank t hn M m ψ hψ b₀).1 _ hFc hFi
    have hA : Continuous fun y => fc ψ lam 𝓖 nb (cf dd E ((t : ℂ) / 2) ε 1) β (M.sh y * g) := by
      simp only [← hpf]
      exact hpcc.comp (M.sh_cont.mul continuous_const)
    have hAT := eq_of_pairing hThP hRT hS.pos hψ hχ hη hθ m b₀ hb _ T hA hT (fun Ω hΩ hcs => by
      have h2 := (hpol.2.2 mu hmu M m b₀ hb.2 β hβ nb lam 𝓖 hCD Ω hΩ g).2
      rw [h2, rsec_translate M m ψ b₀ ωB Φ g Ω]
      exact h Ω hΩ hcs)
    have h0 := congrFun hAT 0
    simpa only [sh_zero M, one_mul] using h0
  obtain ⟨x₀, b₀, hb₀, hx₀⟩ := exists_orth W
  have hmid := hMuId D n t B W d hn ψ χ θ μB μW ωB ωW hS mu hmu M m b₀ hb₀ (fun Ω hΩ Φ' => hrho b₀ hb₀.2 Ω hΩ Φ') I
  obtain ⟨κ, hκ⟩ := hmid.2 x₀ hx₀
  obtain ⟨ν, -, -, hν⟩ := hT2 D n t B W d hn I θ hθ m.μ m.hμ.1 b₀ hb₀.2 x₀ hx₀
  have hx₀d : x₀.det ≠ 0 := det_ne_of_gram W x₀ (by rw [hx₀]; exact hb₀.2)
  refine ⟨κ, fun β hβ g => ⟨fun hno => ?_, fun x hx => ?_⟩⟩
  · obtain ⟨a, b₁, β', hb₁, hcg⟩ := exists_cg_dsum hn β (le_of_eq hβ.symm)
    have hβ'0 : β'.1 = 0 := by
      by_contra hne
      have h1 := rank_dsum_ge hn b₁ hb₁.2 β' hne
      rw [← hcg, rank_cg, hβ] at h1
      omega
    have hnr : ¬ ∃ x₁, gramQ W x₁ = b₁.1 := by
      rintro ⟨x₁, hx₁⟩
      exact hno ⟨_, rep_of_cg W hn a β b₁ β' hβ'0 hcg x₁ hx₁⟩
    have hz := (hMuId D n t B W d hn ψ χ θ μB μW ωB ωW hS mu hmu M m b₁ hb₁
      (fun Ω hΩ Φ' => hrho b₁ hb₁.2 Ω hΩ Φ') I).1 hnr
    have hext : IsExt hn b₁ (dsum hn b₁ β') := by
      show bl hn b₁.1 0 0 β'.1 = _
      rw [hβ'0]
    have hzero : ∀ g', fc ψ lam 𝓖 nb (cf dd E ((t : ℂ) / 2) ε 1) (cg a β) g' = 0 := by
      intro g'
      rw [hcg]
      exact key b₁ hb₁ _ hext g' (fun _ => 0) continuous_const (fun Ω hΩ hcs => by
        rw [hz _ Ω hΩ hcs]
        simp)
    obtain ⟨q, hq⟩ := fc_levi hψ _ hFc hFi hCD a β
    have h1 := hq (q⁻¹ * g)
    rw [mul_inv_cancel_left] at h1
    rw [h1]
    exact hzero _
  · obtain ⟨a, hxa⟩ := exists_frame W hn x₀ hx₀d x (by rw [hx]; exact hβ.ge)
    have he : cg a (ext0H hn b₀) = β := by
      apply Subtype.ext
      show a.1ᴴ * (bl hn b₀.1 0 0 0) * a.1 = β.1
      rw [← hx, ← hxa, gramQ_mul, gram_extend_by_zero, hx₀]
    obtain ⟨q, hqm, hq⟩ := fc_levi_mat hψ _ hFi hCD a (ext0H hn b₀)
    rw [he] at hq
    rw [← hq g]
    have hTc : Continuous (fun y : Mx D W.rank t =>
        κ * orb W I.m (ikp I fun X => (ωB (q * g) Φ).1 (mm X (bl hn 1 y 0 1))) (L.ext0 hn x₀)) :=
      continuous_const.mul (hν (ωB (q * g) Φ).1 (ωB (q * g) Φ).2 0 (zero_mem _)).2.1
    have h1 := key b₀ hb₀ (ext0H hn b₀) rfl (q * g) _ hTc (fun Ω hΩ hcs => by
      rw [hκ (ωB (q * g) Φ) Ω hΩ hcs, ← integral_const_mul]
      simp only [mul_assoc])
    refine h1.trans ?_
    show κ * orb W I.m (ikp I fun X => (ωB (q * g) Φ).1 (mm X (bl hn 1 0 0 1))) (L.ext0 hn x₀) = _
    congr 1
    have hfun : (fun X => (ωB (q * g) Φ).1 (mm X (bl hn 1 0 0 1))) = fun X => (ωB g Φ).1 (mm X (rat a.1)) := by
      funext X
      rw [GlobalTheory.CompanionTheory.WzHeis.blockRowSubstitution_one, map_mul]
      have := weil_rat hS.hB hχ a hqm (ωB g Φ) (mm X 1)
      rw [mm, Matrix.mul_one] at this
      simpa [mm, Matrix.mul_one] using this
    rw [hfun, show ikp I (fun X => (ωB g Φ).1 (mm X (rat a.1))) = fun Y => ikp I (ωB g Φ).1 (mm Y (rat a.1)) from
      funext (ikp_rat I _ a), orb_rat W I.m _ a, hxa]

end GlobalTheory.CompanionTheory.RkCoef

end
