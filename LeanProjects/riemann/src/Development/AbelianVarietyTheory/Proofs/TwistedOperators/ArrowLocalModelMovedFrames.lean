import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalModelOfSplitPlaceThetaFunStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalModelMovedFramesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumLocalModelFormula
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.ArrowModel

section Moves
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' Z Z' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] [Fintype Z']
  [DecidableEq Z']

def moveHomeo (εS : GL Y' k) (εT : GL Y k) (σS : Z' ≃ Y') (σT : Z ≃ Y) : Matrix Y Y' k ≃ₜ Matrix Z Z' k where
  toFun x := ((εT⁻¹).val * x * εS.val).submatrix σT σS
  invFun z := εT.val * z.reindex σT σS * (εS⁻¹).val
  left_inv x := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  right_inv z := by
    simp only [Matrix.reindex_apply]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one,
      Matrix.submatrix_submatrix, Equiv.symm_comp_self, Equiv.symm_comp_self, Matrix.submatrix_id_id]
  continuous_toFun := ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_submatrix _ _
  continuous_invFun := (continuous_const.matrix_mul (continuous_id.matrix_submatrix _ _)).matrix_mul continuous_const

omit [IsNonarchimedeanLocalField k] in

theorem comp_homeo_mem_SB {X X' : Type} [TopologicalSpace X] [TopologicalSpace X'] (e : X ≃ₜ X') {Φ : X' → ℂ}
    (h : Φ ∈ SB X') : Φ ∘ e ∈ SB X :=
  ⟨h.1.comp_continuous e.continuous, h.2.comp_homeomorph e⟩

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem frame_back {K : Type} [Field K] {n N n' N' : ℕ} (h : N = n) (h' : N' = n') (L₁ : GL (Fin n) K) (L₀ : GL (Fin n') K)
    (x : Matrix (Fin N) (Fin N') K) :
    (((L₁⁻¹).val * (L₁.val.submatrix id (Fin.cast h) * x * ((L₀⁻¹).val).submatrix (Fin.cast h') id) * L₀.val).submatrix
      (Fin.cast h) (Fin.cast h')) = x := by
  subst h h'
  simp only [Fin.cast_refl, Matrix.submatrix_id_id]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

end Moves

theorem indicator_move : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Y Y' Z Z' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] [Fintype Z'] [DecidableEq Z'] (εS : GL Y' k) (εT : GL Y k), εS ∈ KO k Y' → εT ∈ KO k Y → ∀ (σS : Z' ≃ Y') (σT : Z ≃ Y) (O : SB (Matrix Z Z' k)), IsOne O → ∃ Φ : SB (Matrix Y Y' k), IsOne Φ ∧ ∀ x, Φ.1 x = O.1 (((εT⁻¹).val * x * εS.val).submatrix σT σS) := by
  intro k _ _ _ _ Y Y' Z Z' _ _ _ _ _ _ _ _ εS εT hS hT σS σT O hO
  let e := moveHomeo εS εT σS σT
  refine ⟨⟨O.1 ∘ e, comp_homeo_mem_SB e O.2⟩, ?_, fun x => rfl⟩
  unfold IsOne at hO ⊢
  funext x
  change O.1 (e x) = _
  rw [hO]
  have key : (∀ r q, e x r q ∈ (ValuativeRel.valuation k).integer) ↔ ∀ r q, x r q ∈ (ValuativeRel.valuation k).integer := by
    have h1 := GlobalTheory.SplitFlip.mul_mul_mem_matLat_iff (inv_mem hT) hS x
    rw [GlobalTheory.SplitFlip.mem_matLat_stdLat, GlobalTheory.SplitFlip.mem_matLat_stdLat] at h1
    rw [← h1]
    exact ⟨fun h r q => by simpa [e, moveHomeo] using h (σT.symm r) (σS.symm q), fun h r q => h _ _⟩
  by_cases h : ∀ r q, x r q ∈ (ValuativeRel.valuation k).integer
  · rw [Set.indicator_of_mem (show e x ∈ {x : Matrix Z Z' k | ∀ r q, x r q ∈ (ValuativeRel.valuation k).integer} from key.2 h),
      Set.indicator_of_mem (show x ∈ {x : Matrix Y Y' k | ∀ r q, x r q ∈ (ValuativeRel.valuation k).integer} from h)]
  · rw [Set.indicator_of_notMem (show e x ∉ {x : Matrix Z Z' k | ∀ r q, x r q ∈ (ValuativeRel.valuation k).integer} from fun H => h (key.1 H)),
      Set.indicator_of_notMem (show x ∉ {x : Matrix Y Y' k | ∀ r q, x r q ∈ (ValuativeRel.valuation k).integer} from h)]

theorem exists_moved : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Y Y' Z Z' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] [Fintype Z'] [DecidableEq Z'] (εS : GL Y' k) (εT : GL Y k) (σS : Z' ≃ Y') (σT : Z ≃ Y) (Φ₁ : SB (Matrix Y Y' k)), ∃ Φ' : SB (Matrix Z Z' k), ∀ z, Φ'.1 z = Φ₁.1 (εT.val * z.reindex σT σS * (εS⁻¹).val) := by
  intro k _ _ _ _ Y Y' Z Z' _ _ _ _ _ _ _ _ εS εT σS σT Φ₁
  exact ⟨⟨Φ₁.1 ∘ (moveHomeo εS εT σS σT).symm, comp_homeo_mem_SB _ Φ₁.2⟩, fun z => rfl⟩

theorem coord_up : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (t : T) (w : Pl D.host.E) (p : Place D (Kw w)), IsPlc w p → ∀ (j : ℕ) (hj : j < D.R.m) (x : Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, j + 1))) (Fin ((locGrid ch.G t w).rank (D.R.m, j))) (Kw w)), ch.S.B.coord t w (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, hj⟩ ⟨le_rfl, hj.le⟩ ((p.up (frRow ch.S.B t w j hj.le) (frRow ch.S.B t w (j + 1) hj) x).map fun a => cpt w (toEAf D a)) = xᵀ := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch t w p hp j hj x
  have hm : ∀ M : Matrix (Fin (ch.G.V (.grid D.R.m (j + 1))).rank) (Fin (ch.G.V (.grid D.R.m j)).rank) (Kw w),
    (M.map p.ι).map (fun a => cpt w (toEAf D a)) = M := fun M => Matrix.ext fun a b => by simp [← hp.2.1, p.π_ι]
  simp only [Place.up, GlobalTheory.FunObj.Frames.coord, frRow, frOf, hm]
  exact congrArg Matrix.transpose (frame_back _ _ _ _ x)

open Classical in

theorem model_of_vec : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) {μ0 : T}, R.toLevCh.Is μ0 → LatP ch → ∀ t, ∀ w ∈ locPl ch.G t, ∀ p, IsPlc w p → ∀ (φ : EdgeDat ch t w) j (hj : j < D.R.m) v f, IsArrVec ch t w p.e φ j hj v f → ∃ Tm₀, p.IsModel ch.W.ψ (frRow ch.S.B t w j hj.le) (frRow ch.S.B t w (j + 1) hj) Tm₀ ∧ (∀ O, IsOne O → Tm₀ O = v) ∧ ∃ Φ₀ : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, j + 1))) (Fin ((locGrid ch.G t w).rank (D.R.m, j))) (Kw w)), (∀ x, Φ₀.1 x = φ (.theta D.R.m j) xᵀ) ∧ Tm₀ Φ₀ = f := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch μ0 hL hLat t w hw p hp φ j hj v f hv
  obtain ⟨hθ, hSB, hTA⟩ := hv
  obtain ⟨Tm, hM, hO, Φ, hΦ, hf⟩ := GlobalTheory.T.exists_localModel_of_splitPlaceThetaFun D (Kw w) p ch.W.ψ ch.W.ψ_std _ _ _ _
    (node_isV ch.G hL (X := .grid D.R.m j) ⟨le_rfl, hj.le⟩).sd (node_isV ch.G hL (X := .grid D.R.m (j + 1)) ⟨le_rfl, hj⟩).sd
    _ _ (frRow ch.S.B t w j hj.le) (frRow ch.S.B t w (j + 1) hj) (hLat t w hw p hp j hj).1 v _ f hθ hSB hTA
  refine ⟨Tm, hM, hO, Φ, fun x => ?_, hf⟩
  rw [hΦ, if_pos (GlobalTheory.LocMod.Witness.up_half p _ _ x), coord_up ch t w p hp j hj x]

theorem weil_move : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT ω → ∀ (Γ : GlobalTheory.SplitFlip.Grid k) (i j : ℕ), p.IsComp χS (Γ.kappa (.theta i j) (i, j + 1)) → p.IsComp χT (Γ.kappa (.theta i j) (i, j)) → ∀ (FS : Frame k S.rank (Fin (Γ.rank (i, j)))) (FT : Frame k T.rank (Fin (Γ.rank (i, j + 1)))) (Tm : SB (Matrix (Fin (Γ.rank (i, j + 1))) (Fin (Γ.rank (i, j))) k) →ₗ[ℂ] (WO S T → ℂ)), p.IsModel ψ FS FT Tm → ∀ (g : Γ.VertexGroup) (ρ : GA D S) (ρ' : GA D T), p.IsLoc FS ρ (g (i, j)) → p.IsLoc FT ρ' (g (i, j + 1)) → ∀ Φ₀ : SB (Matrix (Fin (Γ.rank (i, j + 1))) (Fin (Γ.rank (i, j))) k), ∃ Φ₁ : SB (Matrix (Fin (Γ.rank (i, j + 1))) (Fin (Γ.rank (i, j))) k), (∀ x, Φ₁.1 x = Γ.edgeFactor .one g (.theta i j) * Φ₀.1 (((g (i, j + 1))⁻¹).val * x * (g (i, j)).val)) ∧ ω (ρ, ρ') (Tm Φ₀) = Tm Φ₁ := by
  intro D k _ _ _ _ p ψ S T χS χT ω hω Γ i j hS hT FS FT Tm hM g ρ ρ' hρ hρ' Φ₀
  refine ⟨⟨_, (SB _).smul_mem (((Γ.kappa (.theta i j) (i, j + 1) * (Γ.kappa (.theta i j) (i, j))⁻¹) (Matrix.GeneralLinearGroup.det (g (i, j))) : ℂˣ) : ℂ)
    (om_mem_SB (Γ.kappa (.theta i j) (i, j + 1))⁻¹ (g (i, j)) (g (i, j + 1)) Φ₀.2)⟩, fun x => ?_,
    GlobalTheory.LocOm.omLoc D k p ψ S T χS χT ω hω _ _ hS hT _ _ FS FT Tm hM ρ (g (i, j)) ρ' (g (i, j + 1)) hρ hρ' Φ₀ _ rfl⟩
  have e1 : ∀ (a : kˣ) (r : ℕ), ((nabs k a ^ ((r : ℝ) / 2) : ℝ) : ℂ) = GlobalTheory.SplitFlip.apow a ((r : ℂ) / 2) := fun a r => by
    rw [GlobalTheory.SplitFlip.apow, Complex.ofReal_cpow (nabs_pos k a).le]; push_cast; rfl
  have e2 : ∀ (a : kˣ) (r : ℕ), ((nabs k a ^ (-((r : ℝ) / 2)) : ℝ) : ℂ) = GlobalTheory.SplitFlip.apow a (-((r : ℂ) / 2)) := fun a r => by
    rw [GlobalTheory.SplitFlip.apow, Complex.ofReal_cpow (nabs_pos k a).le]; push_cast; rfl
  simp only [om, GlobalTheory.SplitFlip.Grid.edgeFactor, Pi.smul_apply, smul_eq_mul, Fintype.card_fin, e1, e2, GlobalTheory.SplitFlip.Assignment.read,
    GlobalTheory.SplitFlip.gdet_invT, GlobalTheory.SplitFlip.apow_inv, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val,
    neg_div, neg_neg]
  have hA := Units.ne_zero ((Γ.kappa (.theta i j) (i, j + 1)) (Matrix.GeneralLinearGroup.det (g (i, j))))
  generalize ((Γ.kappa (.theta i j) (i, j + 1)) (Matrix.GeneralLinearGroup.det (g (i, j))) : ℂ) = A at hA ⊢
  simp only [GlobalTheory.SplitFlip.Edge.src, GlobalTheory.SplitFlip.Edge.tgt, inv_inv]
  field_simp

theorem arrow_model : Big fun ch => LatP ch → ChrP ch → ArrP ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  intro hLat hChr t w hw p hp φ j hj v f hv ε g hε a ρ a' ρ' hρ hρ' Z Z' _ _ _ _ σ σ'
  obtain ⟨Tm₀, hM, hO, Φ₀, hΦ₀, hf⟩ := model_of_vec ch hL hLat t w hw p hp φ j hj v f hv
  have hC := (hChr t w hw p hp).2.2 j hj
  have hωis := ch.W.om_is (.mu t D.R.m j) ⟨le_rfl, hj⟩
  obtain ⟨Φ₁, hΦ₁, hω⟩ := weil_move D (Kw w) p ch.W.ψ _ _ _ _ (ch.W.om (.mu t D.R.m j)) hωis (locGrid ch.G t w) D.R.m j hC.1 hC.2
    _ _ Tm₀ hM (ε * g) ρ ρ' hρ hρ' Φ₀
  obtain ⟨Tm', hM', hT'⟩ := GlobalTheory.T.exists_localModel_movedFrames D (Kw w) p ch.W.ψ _ _ _ _ (ch.W.om (.mu t D.R.m j)) hωis _ _ Z' Z _ _ Tm₀ hM a a'
    (ε (D.R.m, j)) (ε (D.R.m, j + 1)) σ σ'
  refine ⟨Tm', hM', fun O hO' => ?_, ?_⟩
  · obtain ⟨Φ, hΦ, hΦO⟩ := indicator_move (Kw w) _ _ _ _ (ε (D.R.m, j)) (ε (D.R.m, j + 1)) (hε _) (hε _) σ σ' O hO'
    rw [hT' Φ O hΦO, hO Φ hΦ]
  · obtain ⟨Φ', hΦ'⟩ := exists_moved (Kw w) _ _ _ _ (ε (D.R.m, j)) (ε (D.R.m, j + 1)) σ σ' Φ₁
    refine ⟨Φ', fun z => ?_, ?_⟩
    · rw [hΦ', hΦ₁, hΦ₀, phiM]
      congr 2
      simp only [Pi.mul_apply, Units.val_mul, _root_.mul_inv_rev, Matrix.transpose_mul, Matrix.mul_assoc]
      congr 1
      rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one, Matrix.one_mul]
      congr 1
      rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one, Matrix.one_mul]
    · rw [hT' Φ₁ Φ' ?_, ← hω, ← hf, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk]
      intro x
      rw [hΦ']
      congr 1
      rw [Matrix.reindex_apply, Matrix.submatrix_submatrix, Equiv.self_comp_symm, Equiv.self_comp_symm, Matrix.submatrix_id_id,
        ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

end GlobalTheory.ArrowModel

end
