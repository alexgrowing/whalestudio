import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvariantOfTsupport
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaFunNeZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContinuousOfIsTheta
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsInfFamAndStdChar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitSupportedUnitaryComponent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPlaceOverTwo
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselFourierJacobiNormalFramesExistSplitPlace

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocMod Filter
open GlobalTheory.PlaceModel (half mem_half isHalf_iff heisL heisL_half heisL_comm hO_smul_left infPart_half)
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LocMod.Inhab

namespace GlobalTheory.LocMod.Exist

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

def stdFrame (k : Type) [Field k] (N : ℕ) : GlobalTheory.LocMod.Frame k N (Fin N) := ⟨1, 1, by simp, by simp⟩

def ofSplitPt (q : GlobalTheory.FinPl.SplitPt D k) : Place D k :=
  ⟨q.e, q.split, q.pr, q.sec, q.pr_sec, q.sec_pr, q.cont_pr, q.cont_sec⟩

theorem e_mul_ι (x : k) : p.e * p.ι x = p.ι x := by rw [← p.ι_π, p.π_ι]

variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}
  (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y)

def loc {m n : Type} (a : Matrix m n D.host.E) : Matrix m n k := a.map (p.π.comp (incA D))

theorem loc_gram_mul (V : HSp D) : loc p V.gram * loc p V.gram⁻¹ = 1 := by
  rw [loc, loc, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ (gram_det_ne V).isUnit, Matrix.map_one _ (map_zero _) (map_one _)]

theorem loc_mul_gram (V : HSp D) : loc p V.gram⁻¹ * loc p V.gram = 1 := mul_eq_one_comm.1 (loc_gram_mul p V)

def dual (b : Matrix Y Y' k) : WO S T :=
  (loc p S.gram * FS.β * bᵀ * FT.γ * loc p T.gram⁻¹)ᵀ.map fun z => cA D (p.ι z)

theorem up_mem (x : Matrix Y Y' k) : p.up FS FT x ∈ half S T p.e :=
  (isHalf_iff S T).1 fun _ _ => e_mul_ι p _

theorem dual_mem (b : Matrix Y Y' k) : dual p FS FT b ∈ half S T (cA D p.e) :=
  (isHalf_iff S T).1 fun _ _ => by
    simp only [dual, Matrix.map_apply]
    rw [← map_mul, e_mul_ι]

theorem up_add (x y : Matrix Y Y' k) : p.up FS FT (x + y) = p.up FS FT x + p.up FS FT y := by
  ext i j
  simp only [Place.up, Matrix.mul_add, Matrix.add_mul, Matrix.map_apply, Matrix.add_apply, map_add]

theorem dual_add (x y : Matrix Y Y' k) : dual p FS FT (x + y) = dual p FS FT x + dual p FS FT y := by
  ext i j
  simp only [dual, Matrix.mul_add, Matrix.add_mul, Matrix.transpose_add, Matrix.map_apply, Matrix.add_apply, map_add]

theorem up_zero : p.up FS FT 0 = 0 := by simpa using up_add p FS FT 0 0

theorem dual_zero : dual p FS FT 0 = 0 := by simpa using dual_add p FS FT 0 0

theorem continuous_up : Continuous (p.up FS FT) :=
  ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_map p.cont_ι

theorem continuous_dual : Continuous (dual p FS FT) :=
  ((((continuous_const.matrix_mul continuous_id.matrix_transpose).matrix_mul continuous_const).matrix_mul
    continuous_const).matrix_transpose).matrix_map ((GlobalTheory.DualPairCompare.continuous_cA D).comp p.cont_ι)

theorem π_hO (x y : WO S T) : p.π (hO S T x y) = Matrix.trace
    (loc p S.gram⁻¹ * (Matrix.map y fun z => p.π (cA D z))ᵀ * loc p T.gram * Matrix.map x p.π) := by
  simp only [hO, map_sum, map_mul, Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul, loc, Matrix.map_apply,
    Matrix.transpose_apply, RingHom.comp_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans Finset.sum_comm

theorem π_hO_dual (t b : Matrix Y Y' k) : p.π (hO S T (p.up FS FT t) (dual p FS FT b)) = ∑ r, ∑ q, b r q * t r q := by
  have h1 : (Matrix.map (dual p FS FT b) fun z => p.π (cA D z)) = (loc p S.gram * FS.β * bᵀ * FT.γ * loc p T.gram⁻¹)ᵀ := by
    ext i j
    simp only [dual, Matrix.map_apply, cA_cA, p.π_ι]
  have h2 : Matrix.map (p.up FS FT t) p.π = FT.β * t * FS.γ := by
    ext i j
    simp only [Place.up, Matrix.map_apply, p.π_ι]
  rw [π_hO, h1, h2, Matrix.transpose_transpose]
  simp only [← Matrix.mul_assoc]
  rw [loc_mul_gram, Matrix.one_mul, Matrix.mul_assoc _ _ (loc p T.gram), loc_mul_gram, Matrix.mul_one,
    Matrix.mul_assoc _ _ FT.β, FT.γβ, Matrix.mul_one, Matrix.trace_mul_comm]
  simp only [← Matrix.mul_assoc]
  rw [FS.γβ, Matrix.one_mul, Finset.sum_comm]
  rfl

theorem exists_dual {y : WO S T} (hy : IsHalf (cA D p.e) y) : ∃ b, dual p FS FT b = y := by
  refine ⟨(FS.γ * loc p S.gram⁻¹ * (Matrix.map y fun z => p.π (cA D z))ᵀ * loc p T.gram * FT.β)ᵀ, ?_⟩
  rw [dual, Matrix.transpose_transpose]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc _ FS.β, FS.βγ, Matrix.mul_one, loc_gram_mul, Matrix.one_mul, Matrix.mul_assoc _ FT.β, FT.βγ,
    Matrix.mul_one, Matrix.mul_assoc, loc_gram_mul, Matrix.mul_one, Matrix.transpose_transpose]
  ext i j
  simp only [Matrix.map_apply, p.ι_π, map_mul, cA_cA]
  exact hy i j

theorem char_sympl {ψ : AddChar (AF D.host.F) ℂ} {ψk : AddChar k Circle} (h : p.IsChar ψ ψk) (t b : Matrix Y Y' k) :
    ψ (symplO S T (p.up FS FT t) (dual p FS FT b)) = pairing ψk t b := by
  rw [pairing, ← π_hO_dual p FS FT, h, p.ι_π, ← hO_smul_left, (mem_half S T).1 (up_mem p FS FT t)]
  rfl

theorem exists_isLoc (F : GlobalTheory.LocMod.Frame k S.rank Y) (gk : GL Y k) : ∃ g, p.IsLoc F g gk := by
  obtain ⟨he1, he2, -⟩ := p.split
  have keyM : ∀ X Z : Matrix (Fin S.rank) (Fin S.rank) (Formalism.L2.Theta.AE D), X.map p.π = Z.map p.π ↔ p.e • X = p.e • Z :=
    fun X Z => by
      simp only [← Matrix.ext_iff, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, ← p.ι_π]
      exact forall₂_congr fun i j => ⟨congrArg _, fun h => by simpa only [p.π_ι] using congrArg p.π h⟩
  have lift : ∀ Z : Matrix (Fin S.rank) (Fin S.rank) k, (Z.map p.ι).map p.π = Z := fun Z => Matrix.ext fun i j => p.π_ι _
  obtain ⟨g, h1, h2, h3⟩ := GlobalTheory.SplitOnto.exists_unitary (c := cA D) cA_cA (GlobalTheory.SplitOnto.gram_mul_inv S)
    (GlobalTheory.SplitOnto.gram_conj S) he1 he2 ((F.β * gk.val * F.γ).map p.ι) ((F.β * (gk⁻¹).val * F.γ).map p.ι) (by
      rw [← keyM, Matrix.map_mul, lift, lift, Matrix.map_one _ (map_zero _) (map_one _)]
      simp only [← Matrix.mul_assoc]
      rw [Matrix.mul_assoc _ F.γ, F.γβ, Matrix.mul_one, Matrix.mul_assoc F.β, Units.inv_mul, Matrix.mul_one, F.βγ])
  let g' : HR (AF D.host.F) D.sp.cm.sig S.gram := ⟨g, h1⟩
  exact ⟨g', fun i j => congrFun (congrFun h2 i) j, ((keyM _ _).2 h3).trans (lift _)⟩

def thetaSub (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Submodule ℂ (WO S T → ℂ) where
  carrier := {f | IsThetaFunO ψ S T f}
  zero_mem' := GlobalTheory.OrientedHeis.theta_zero
  add_mem' := GlobalTheory.OrientedHeis.theta_add
  smul_mem' c _ h := GlobalTheory.OrientedHeis.theta_smul c h

theorem exists_injective_model : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y), ∃ Tm, p.IsModel ψ FS FT Tm ∧ Function.Injective Tm := by
  intro D k _ _ _ _ p ψ hψ S T Y Y' _ _ _ _ FS FT
  obtain ⟨⟨ψk, hk⟩, hk', -⟩ := GlobalTheory.LocChar.weil_char_split D k p ψ hψ
  obtain ⟨he, hec, v, ε, hε, heq⟩ := p.split
  have he' : cA D p.e * cA D p.e = cA D p.e := by rw [← map_mul, he]
  have heε : algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) ε * p.e = p.e := by rw [← heq]; linear_combination he + hec
  have heε' : algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) ε * cA D p.e = cA D p.e := by
    rw [← heq]; linear_combination he' + hec
  have i1 := fun x => infPart_half hε heε (up_mem p FS FT x)
  have i2 := fun x => infPart_half hε heε' (dual_mem p FS FT x)
  have h0 : ∀ f, heisL S T ψ 0 f = f := fun f => by
    funext w
    change ψ (symplOH S T w 0) * f (w + 0) = f w
    rw [symplOH, GlobalTheory.PlaceModel.symplO_zero_right, mul_zero, AddChar.map_zero_eq_one, one_mul, add_zero]
  have sm : ∀ j : Matrix Y Y' k → WO S T, Continuous j → j 0 = 0 → (∀ x, (j x).map (infPart D) = 0) →
      ∀ f ∈ thetaSub ψ S T, ∀ᶠ x in 𝓝 0, heisL S T ψ (j x) f = f := fun j hj j0 hi f hf => by
    obtain ⟨U, hU, h⟩ := IsThetaFunO.level hf
    filter_upwards [(hU.preimage hj).mem_nhds (show j 0 ∈ U by rw [j0]; exact U.zero_mem)] with x hx
    exact h _ hx (hi x)
  obtain ⟨f, hf, f0⟩ := GlobalTheory.Mem.ThetaNonzero.exists_thetaO_ne_zero hψ S T
  have a1 : ∀ x x' f, heisL S T ψ (p.up FS FT x) (heisL S T ψ (p.up FS FT x') f) = heisL S T ψ (p.up FS FT (x + x')) f :=
    fun x x' f => by rw [up_add, heisL_half S T ψ (by rw [mul_comm, hec]) _ (up_mem p FS FT x) _ (up_mem p FS FT x')]
  have a2 : ∀ x x' f, heisL S T ψ (dual p FS FT x) (heisL S T ψ (dual p FS FT x') f) =
      heisL S T ψ (dual p FS FT (x + x')) f := fun x x' f => by
    rw [dual_add, heisL_half S T ψ (by rw [cA_cA, hec]) _ (dual_mem p FS FT x) _ (dual_mem p FS FT x')]
  have a3 : ∀ x y f, heisL S T ψ (p.up FS FT x) (heisL S T ψ (dual p FS FT y) f) =
      pairing ψk x y • heisL S T ψ (dual p FS FT y) (heisL S T ψ (p.up FS FT x) f) := fun x y f => by
    rw [heisL_comm, char_sympl p FS FT hk]
  have a4 : ∀ x, ∀ f ∈ thetaSub ψ S T, heisL S T ψ (p.up FS FT x) f ∈ thetaSub ψ S T :=
    fun x f hf => GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 hf (i1 x)
  have a5 : ∀ x, ∀ f ∈ thetaSub ψ S T, heisL S T ψ (dual p FS FT x) f ∈ thetaSub ψ S T :=
    fun x f hf => GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 hf (i2 x)
  obtain ⟨g, hg, g0, h1, h2⟩ := exists_vacuum (hk' ψk hk).1 (hk' ψk hk).2 (fun x => heisL S T ψ (p.up FS FT x))
    (fun b => heisL S T ψ (dual p FS FT b)) a1 a2 (fun f => by rw [up_zero, h0]) (fun f => by rw [dual_zero, h0]) a3
    (thetaSub ψ S T) a4 a5 (sm _ (continuous_up p FS FT) (up_zero p FS FT) i1)
    (sm _ (continuous_dual p FS FT) (dual_zero p FS FT) i2) hf f0
  obtain ⟨Tm, hT⟩ := exists_embedding (hk' ψk hk).1 (hk' ψk hk).2 (fun x => heisL S T ψ (p.up FS FT x))
    (fun b => heisL S T ψ (dual p FS FT b)) a1 a2 a3 (thetaSub ψ S T) a4 a5 hg g0 h1 h2
  refine ⟨Tm ∘ₗ (SB (Matrix Y Y' k)).subtype, ⟨fun Φ => (hT Φ.1 Φ.2).2.1, fun x Φ Φ' h => ?_, fun y hy Φ Φ' h => ?_⟩,
    (injective_iff_map_eq_zero _).2 fun Φ hΦ => Subtype.ext ((hT Φ.1 Φ.2).1 hΦ)⟩
  · exact (congrArg Tm (funext h)).trans ((hT Φ.1 Φ.2).2.2.1 x)
  · obtain ⟨b, rfl⟩ := exists_dual p FS FT hy
    simp only [char_sympl p FS FT hk] at h
    exact (congrArg Tm (funext h)).trans ((hT Φ.1 Φ.2).2.2.2 b)

theorem exists_place : ∀ (D : D7) (e : Formalism.L2.Theta.AE D), IsSplitIdem D e → ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (p : Place D k), p.e = e := GlobalTheory.PlaceOfIdem.exists_place

theorem exists_place_closed (D : D7) : ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k)
    (_ : IsNonarchimedeanLocalField k), Nonempty (Place D k) :=
  let ⟨e, he⟩ := GlobalTheory.LocMod.Inhab.exists_isSplitIdem D
  let ⟨k, a, b, c, d, q, _⟩ := exists_place D e he
  ⟨k, a, b, c, d, ⟨q⟩⟩

theorem exists_char_comp_loc : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k), (∀ ψ, IsStdChar D ψ (-1) → ∃ ψk : AddChar k Circle, p.IsChar ψ ψk ∧ Continuous ψk ∧ ψk ≠ 1) ∧ (∀ χ : (Formalism.L2.Theta.AE D)ˣ →* Circle, ∃ μ : kˣ →* ℂˣ, p.IsComp χ μ) ∧ (∀ (S : HSp D) (Y : Type) [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k S.rank Y) (gk : GL Y k), ∃ g, p.IsLoc F g gk) :=
  fun D k _ _ _ _ p => ⟨fun ψ hψ => let ⟨⟨ψk, h⟩, h', _⟩ := GlobalTheory.LocChar.weil_char_split D k p ψ hψ; ⟨ψk, h, h' ψk h⟩,
    let ⟨ψ, hψ⟩ := (GlobalTheory.Ker.exists_infFam_and_stdChar D).2; (GlobalTheory.LocChar.weil_char_split D k p ψ hψ).2.2.2.2,
    fun _ _ _ _ F gk => exists_isLoc p F gk⟩

theorem exists_frames : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (n : Type) [Fintype n] [DecidableEq n] (ρ : ℕ) (s : k), s ≠ 0 → (∀ (B : BesLev D ρ) (FA : GlobalTheory.LocMod.Frame k B.A.rank n), (∃ F, p.IsCoreFrame B s FA F) ∧ (∃ F : GlobalTheory.LocMod.Frame k B.V.rank (n ⊕ Fin (2 * ρ + 1)), p.IsBesFrame B s FA F) ∧ p.hz B ≠ 0) ∧ ∀ (J : JacLev D ρ) (hh : k), hh ≠ 0 → ∀ F₀ : GlobalTheory.LocMod.Frame k J.W₀.rank n, ∃ F : GlobalTheory.LocMod.Frame k J.W.rank (n ⊕ Fin (2 * ρ)), p.IsJacFrame J s hh F₀ F := GlobalTheory.LocMod.normalFrames_exist

theorem inhabitants : (∀ D : D7, ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k)
      (_ : IsNonarchimedeanLocalField k), Nonempty (Place D k)) ∧
    (∀ (D : D7) (e : Formalism.L2.Theta.AE D), IsSplitIdem D e → ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (p : Place D k), p.e = e) ∧
    (∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k), (∀ ψ, IsStdChar D ψ (-1) → ∃ ψk : AddChar k Circle, p.IsChar ψ ψk ∧ Continuous ψk ∧ ψk ≠ 1) ∧ (∀ χ : (Formalism.L2.Theta.AE D)ˣ →* Circle, ∃ μ : kˣ →* ℂˣ, p.IsComp χ μ) ∧ (∀ (S : HSp D) (Y : Type) [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k S.rank Y) (gk : GL Y k), ∃ g, p.IsLoc F g gk)) ∧
    (∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y), ∃ Tm, p.IsModel ψ FS FT Tm ∧ Function.Injective Tm) ∧
    (∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (n : Type) [Fintype n] [DecidableEq n] (ρ : ℕ) (s : k), s ≠ 0 → (∀ (B : BesLev D ρ) (FA : GlobalTheory.LocMod.Frame k B.A.rank n), (∃ F, p.IsCoreFrame B s FA F) ∧ (∃ F : GlobalTheory.LocMod.Frame k B.V.rank (n ⊕ Fin (2 * ρ + 1)), p.IsBesFrame B s FA F) ∧ p.hz B ≠ 0) ∧ ∀ (J : JacLev D ρ) (hh : k), hh ≠ 0 → ∀ F₀ : GlobalTheory.LocMod.Frame k J.W₀.rank n, ∃ F : GlobalTheory.LocMod.Frame k J.W.rank (n ⊕ Fin (2 * ρ)), p.IsJacFrame J s hh F₀ F) :=
  ⟨exists_place_closed, exists_place, exists_char_comp_loc, exists_injective_model, exists_frames⟩

end GlobalTheory.LocMod.Exist
end
