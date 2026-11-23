import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatIndLastKerRow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUnique
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroSourceTensorColumnProduct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSBExtFunEqHalfInd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OfTensColMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionProductsSlicesOrthogonalDecompositi

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LastTgtSlice

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sb_sec (p : SplitPt D k) {S T : HSp D} {LS : Lat S} {LT : Lat T} (hS : Submodule.IsLattice D.host.E LS)
    (hT : Submodule.IsLattice D.host.E LT) {Φ : WO S T → ℂ}
    (hΦ : IsSBHalf p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) Φ) :
    (fun x : Matrix (Fin T.rank) (Fin S.rank) k => Φ (x.map p.sec)) ∈ SB (Matrix (Fin T.rank) (Fin S.rank) k) := by
  classical
  haveI := Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := Fin T.rank) (n' := Fin S.rank)
  have : CharZero k := charZero_of_injective_ringHom (f := p.pr.comp (incA D)) (RingHom.injective _)
  obtain ⟨-, k0, hk0, hinv, hsup⟩ := hΦ
  obtain ⟨hUo, hUc⟩ := HalfInd.open_compact_sec p hS hT
  obtain ⟨ε, hε, heε⟩ := HalfInd.exists_idem p
  have hhalf : ∀ x : Matrix (Fin T.rank) (Fin S.rank) k, IsHalf p.e (x.map p.sec : WO S T) := fun x i j => by
    rw [Matrix.map_apply, ← p.sec_pr, p.pr_sec]
  set U := {y : Matrix (Fin T.rank) (Fin S.rank) k |
      y.map p.sec ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True} with hU
  have hUv : ∀ y ∈ U, (y.map p.sec : WO S T) ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) := by
    intro y h
    have h2 := (GlobalTheory.PlaceModel.idem_smul_mem hε p.split.1 heε h).1
    rwa [(GlobalTheory.PlaceModel.mem_half S T).1 ((GlobalTheory.PlaceModel.isHalf_iff S T).1 (hhalf y))] at h2
  have hc : ((k0 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.2 hk0.ne'
  have hwr : ∀ z : Matrix (Fin T.rank) (Fin S.rank) k,
      ((((k0 : ℕ) : k) • z).map p.sec : WO S T) = k0 • (z.map p.sec : WO S T) := by
    intro z
    rw [Nat.cast_smul_eq_nsmul]
    exact Matrix.ext fun i j => map_nsmul p.sec k0 (z i j)
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, ?_⟩
  · refine ⟨{x' | ((k0 : ℕ) : k)⁻¹ • (x' - x) ∈ U}, hUo.preimage (by fun_prop), ?_, fun x' hx' => ?_⟩
    · show ((k0 : ℕ) : k)⁻¹ • (x - x) ∈ U
      rw [sub_self, smul_zero]
      show (0 : Matrix (Fin T.rank) (Fin S.rank) k).map p.sec ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True
      rw [Matrix.map_zero _ (map_zero _)]; exact zero_mem _
    · set z := ((k0 : ℕ) : k)⁻¹ • (x' - x) with hz
      have hx'z : x' = x + ((k0 : ℕ) : k) • z := by
        rw [hz, smul_smul, mul_inv_cancel₀ hc, one_smul, add_sub_cancel]
      show Φ (x'.map p.sec) = Φ (x.map p.sec)
      rw [hx'z, Matrix.map_add _ (map_add _), hwr]
      exact hinv _ (hUv _ hx') (hhalf _) _
  · refine HasCompactSupport.intro (hUc.image (f := fun z => ((k0 : ℕ) : k)⁻¹ • z) (by fun_prop)) fun x hx => ?_
    by_contra h
    have h1 := hsup _ h
    have h2 : ((k0 : ℕ) : k) • x ∈ U := by
      show (((k0 : ℕ) : k) • x).map p.sec ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True
      rw [hwr]; exact GlobalTheory.PlaceModel.latO_le_top _ h1
    exact hx ⟨_, h2, by beta_reduce; rw [smul_smul, inv_mul_cancel₀ hc, one_smul]⟩

theorem line_eq {L : HSp D} {ζ : Fin L.rank → D.host.E} (hζ : IsLineVec L ζ) (i j : Fin L.rank) : i = j := by
  have := hζ.1
  ext; omega

theorem line_ne {L : HSp D} {ζ : Fin L.rank → D.host.E} (hζ : IsLineVec L ζ) (j : Fin L.rank) : ζ j ≠ 0 := by
  intro h
  have : ζ = 0 := funext fun i => by rw [line_eq hζ i j]; exact h
  exact hζ.2 (by simp [this])

theorem line_sum {L : HSp D} {ζ : Fin L.rank → D.host.E} (hζ : IsLineVec L ζ) {M : Type} [AddCommMonoid M]
    (f : Fin L.rank → M) (j : Fin L.rank) : ∑ i, f i = f j :=
  Finset.sum_eq_single j (fun i _ h => absurd (line_eq hζ i j) h) (by simp)

theorem isLattice_span {L : HSp D} {ζ : Fin L.rank → D.host.E} (hζ : IsLineVec L ζ) :
    Submodule.IsLattice D.host.E (Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) := by
  refine ⟨Submodule.fg_span (Set.finite_singleton _), ?_⟩
  rw [eq_top_iff]
  intro x _
  have j : Fin L.rank := ⟨0, by have := hζ.1; omega⟩
  have hx : x = (x j / ζ j) • ζ := by
    funext i
    rw [line_eq hζ i j, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ (line_ne hζ j)]
  rw [hx]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.subset_span rfl))

theorem exists_colFun (p : SplitPt D k) {n : Type} [Fintype n] [DecidableEq n] {L S : HSp D}
    {ζ : Fin L.rank → D.host.E} (hζ : IsLineVec L ζ) (β : Frame p S n) {LL : Lat L} {LS : Lat S}
    (hL : Submodule.IsLattice D.host.E LL) (hS : Submodule.IsLattice D.host.E LS) {Φ : WO L S → ℂ}
    (hΦ : IsSBHalf p.e (latO L S (LL : Set _) (LS : Set _) (· = p.v)) Φ) :
    ∃ b ∈ SB (n → k), colFun β ζ b = Φ := by
  classical
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  set z : Fin L.rank → k := fun j => p.pr (incA D (ζ j)) with hz
  have hz0 : ∀ j, z j ≠ 0 := fun j h =>
    line_ne hζ j ((p.pr.comp (incA D)).injective (by rw [map_zero]; exact h))
  have h1 := sb_sec p hL hS hΦ
  have h2 := Comm.comp_mem_SB h1
    (p := fun y : n → k => Matrix.of fun i j => (β.b *ᵥ y) i * (z j)⁻¹)
    (s := fun x : Matrix (Fin S.rank) (Fin L.rank) k => β.b' *ᵥ (x *ᵥ z)) ?_ ?_ ?_
  · refine ⟨_, h2, ?_⟩
    funext t
    unfold colFun
    by_cases ht : IsHalf p.e t
    · rw [if_pos ht]
      beta_reduce
      congr 1
      ext i j
      rw [Matrix.map_apply, Matrix.of_apply, ExtZero.zcol, Matrix.mulVec_mulVec, β.bb', Matrix.one_mulVec]
      simp only [Matrix.mulVec, dotProduct]
      rw [line_sum hζ _ j, map_mul p.pr, mul_assoc, mul_inv_cancel₀ (hz0 j), mul_one, p.sec_pr, ht i j]
    · rw [if_neg ht]
      by_contra h
      exact ht (hΦ.1 t (Ne.symm h))
  · refine continuous_matrix fun i j => ?_
    exact ((continuous_apply i).comp (continuous_const.matrix_mulVec continuous_id)).mul continuous_const
  · exact continuous_const.matrix_mulVec (continuous_id.matrix_mulVec continuous_const)
  · intro y
    have : (Matrix.of fun i j => (β.b *ᵥ y) i * (z j)⁻¹) *ᵥ z = β.b *ᵥ y := by
      funext i
      have j : Fin L.rank := ⟨0, by have := hζ.1; omega⟩
      rw [Matrix.mulVec, dotProduct, line_sum hζ _ j, Matrix.of_apply, mul_assoc, inv_mul_cancel₀ (hz0 j), mul_one]
    beta_reduce
    rw [this, Matrix.mulVec_mulVec, β.b'b, Matrix.one_mulVec]

theorem isSBHalf_halfInd {m n : ℕ} (e : AE D) (Λ : AddSubgroup (Mx D m n)) : IsSBHalf e Λ (halfInd e Λ) := by
  have h0 : ∀ t, halfInd e Λ t ≠ 0 → t ∈ Λ ∧ IsHalf e t := fun t ht => by
    by_contra h
    exact ht (by unfold halfInd; rw [if_neg h])
  refine ⟨fun t ht => (h0 t ht).2, 1, one_pos, fun u hu hh t => ?_, fun t ht => by simpa using (h0 t ht).1⟩
  have h1 : IsHalf e (t + u) ↔ IsHalf e t :=
    forall_congr' fun i => forall_congr' fun j => by rw [Matrix.add_apply, mul_add, hh i j, add_left_inj]
  have h2 : t + u ∈ Λ ↔ t ∈ Λ := ⟨fun h => by simpa using sub_mem h hu, fun h => add_mem h hu⟩
  rw [one_smul]
  unfold halfInd
  by_cases h : t ∈ Λ ∧ IsHalf e t
  · rw [if_pos h, if_pos ⟨h2.2 h.1, h1.2 h.2⟩]
  · rw [if_neg h, if_neg fun h' => h ⟨h2.1 h'.1, h1.1 h'.2⟩]

theorem heisO_resS_symm_right (ψ : AddChar (AF D.host.F) ℂ) {S A L T : HSp D} (o : OrthDec S A L) (a : WO L T)
    (F : WO S T → ℂ) (w : WO A T) (y : WO L T) :
    heisO ψ S T ((o.resS T).symm (0, a)) F ((o.resS T).symm (w, y)) =
      heisO ψ L T a (fun y' => F ((o.resS T).symm (w, y'))) y := by
  simp only [heisO]
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  have h0 : symplOH A T w 0 = 0 := by simp [symplOH, symplO, hO]
  rw [h0, zero_add, ← map_add]
  simp

theorem symplO_resS_symm_right {S A L T : HSp D} (o : OrthDec S A L) (t : WO S T) (a : WO L T) :
    symplO S T t ((o.resS T).symm (0, a)) = symplO L T ((o.resS T) t).2 a := by
  rw [o.symplO_resS, AddEquiv.apply_symm_apply]
  simp [symplO, hO]

theorem half_resS_symm_right {S A L T : HSp D} (o : OrthDec S A L) {e : AE D} {a : WO L T} (ha : IsHalf e a) :
    IsHalf e ((o.resS T).symm (0, a)) := by
  intro i j
  rw [OrthDec.resS_symm_apply]
  simp only [Matrix.zero_mul, zero_add, Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [← mul_assoc, ha]

def restrRight {m n m' n' m'' n'' : ℕ} (r : Mx D m n ≃+ Mx D m' n' × Mx D m'' n'') (h : Mx D m' n' → ℂ)
    (T' : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ)) (x : Mx D m' n') :
    (Mx D m'' n'' → ℂ) →ₗ[ℂ] (Mx D m'' n'' → ℂ) where
  toFun Φ := fun y => T' (fun t => h (r t).1 * Φ (r t).2) (r.symm (x, y))
  map_add' Φ Φ' := by
    funext w
    have : (fun t => h (r t).1 * (Φ + Φ') (r t).2) =
        (fun t => h (r t).1 * Φ (r t).2) + fun t => h (r t).1 * Φ' (r t).2 := by
      funext t; simp [mul_add]
    rw [this, map_add]; rfl
  map_smul' c Φ := by
    funext w
    have : (fun t => h (r t).1 * (c • Φ) (r t).2) = c • fun t => h (r t).1 * Φ (r t).2 := by
      funext t; exact mul_left_comm _ _ _
    rw [this, map_smul]; rfl

theorem restrRight_apply {m n m' n' m'' n'' : ℕ} (r : Mx D m n ≃+ Mx D m' n' × Mx D m'' n'') (h : Mx D m' n' → ℂ)
    (T' : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ)) (x : Mx D m' n') (Φ : Mx D m'' n'' → ℂ) (y : Mx D m'' n'') :
    restrRight r h T' x Φ y = T' (fun t => h (r t).1 * Φ (r t).2) (r.symm (x, y)) := rfl

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.SchrTheta in

theorem isTheta_image (p : SplitPt D k) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) {f₀ : WO S T → ℂ}
    (hf₀ : IsThetaFunO ψ S T f₀) {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) 1 f₀ Tm)
    {Φ : WO S T → ℂ} (hΦ : IsSBHalf p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) Φ) :
    IsThetaFunO ψ S T (Tm Φ) := by
  obtain ⟨ε, hε, heq⟩ := p.above
  have hs := p.split
  have he := hs.1
  have hec := hs.2.1
  have he' : cA D p.e * cA D p.e = cA D p.e := by rw [← map_mul, he]
  have heε : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by rw [← heq]; linear_combination he + hec
  have heε' : algebraMap (AF D.host.F) (AE D) ε * cA D p.e = cA D p.e := by rw [← heq]; linear_combination he' + hec
  obtain ⟨hLL', hX, -, hfin, hden⟩ := OverProof.dualPair hψ hS hT hs hε heq
  exact placeModel_induction ψ _ hLL' hX hfin hden hTm (IsThetaFunO ψ S T) GlobalTheory.WeilVacMove.isTheta_zero
    (fun _ _ => GlobalTheory.WeilVacMove.isTheta_add) (fun c _ => GlobalTheory.WeilVacMove.isTheta_smul c)
    (fun x hx g hg => isTheta_heis_fin hψ hg (infPart_half hε heε hx))
    (fun y hy g hg => isTheta_heis_fin hψ hg (infPart_half hε heε' hy))
    hf₀ hΦ

theorem main : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (V₀ A L S : HSp D) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : Frame p A n') (α₀ : Frame p V₀ (n' ⊕ Fin 1)) (β : Frame p S n), IsSumFrame o ζ α α₀ → ∀ (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ), a ≠ 0 → ∀ (LS : Lat S), IsSelfDualC S LS → ∀ (L₁ : Lat V₀) (L₂ : Lat S) (f₁ Ξ : WO V₀ S → ℂ), Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ a) Ξ → ∀ u : WO A S, ∃ (g₁ : WO L S → ℂ) (T₁ : (WO L S → ℂ) →ₗ[ℂ] (WO L S → ℂ)), IsThetaFunO ψ L S g₁ ∧ IsPlaceModel ψ (symplO L S) (heisO ψ L S) p.e (latO L S ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) : Set _) (LS : Set _) (· = p.v)) 1 g₁ T₁ ∧ T₁ (colFun β ζ a) = fun y => Ξ ((o.resS S).symm (u, y)) := by
  intro D k _ _ _ _ p n n' _ _ _ _ ψ hψ _ V₀ A L S o ζ hζ α α₀ β hsum Ψ a ha LS hLS L₁ L₂ f₁ Ξ hΞ u
  obtain ⟨hL₁, hL₂, hf₁, hSB, ⟨T, hT⟩, hall⟩ := hΞ
  have hΞT : Ξ = T (extFun α₀ β (tensCol Ψ a)) := hall T hT
  have hΨSB : Ψ ∈ SB (Matrix n n' k) := TensSB.of_tensCol_mem hSB ha
  have hsumE := ExtZero.extFun_tensCol_sum D k p n n' V₀ A L S o ζ α α₀ β hsum
  set r := o.resS S with hr
  set h := extFun α β Ψ with hh
  set ΛL := latO L S ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) : Set _)
    (LS : Set (Fin S.rank → D.host.E)) (· = p.v) with hΛL
  set Λ₁ := latO V₀ S (L₁ : Set (Fin V₀.rank → D.host.E)) (L₂ : Set (Fin S.rank → D.host.E)) (· = p.v) with hΛ₁
  have hbox : ∀ Φ : WO L S → ℂ, (fun t => h (r t).1 * Φ (r t).2) = o.boxS S h Φ := fun Φ => rfl
  have hcol : ∀ Φ, IsSBHalf p.e ΛL Φ → ∃ b ∈ SB (n → k), colFun β ζ b = Φ := fun Φ hΦ =>
    exists_colFun p hζ β (isLattice_span hζ) hLS.1 hΦ
  have hsb : ∀ Φ, IsSBHalf p.e ΛL Φ → IsSBHalf p.e Λ₁ (fun t => h (r t).1 * Φ (r t).2) := by
    intro Φ hΦ
    obtain ⟨b, hb, rfl⟩ := hcol Φ hΦ
    rw [hbox, hh, ← hsumE]
    exact OverProof.isSBHalf_extFun D k p _ _ V₀ S α₀ β L₁ L₂ hL₁ hL₂ _ (Comm.tensCol_mem hΨSB hb)
  refine ⟨restrRight r h T u (halfInd p.e ΛL), restrRight r h T u, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact GlobalTheory.BoxSlice.isThetaFunO_slice_right o
      (isTheta_image p hψ hL₁ hL₂ hf₁.1 hT (hsb _ (isSBHalf_halfInd p.e ΛL))) u
  · intro Φ hΦ x hx
    funext w
    rw [restrRight_apply]
    have hfun : (fun t => h (r t).1 * (fun t => Φ (t + x)) (r t).2) =
        fun t => (fun t => h (r t).1 * Φ (r t).2) (t + r.symm (0, x)) := by
      funext t
      simp only [map_add, AddEquiv.apply_symm_apply, Prod.fst_add, Prod.snd_add, add_zero]
    rw [hfun, hT.trans _ (hsb Φ hΦ) _ (half_resS_symm_right o hx), hr, heisO_resS_symm_right]
    rfl
  · intro Φ hΦ y' hy'
    funext w
    rw [restrRight_apply]
    have hfun : (fun t => h (r t).1 * (fun t => ψ (symplO L S t y') * Φ t) (r t).2) =
        fun t => ψ (symplO V₀ S t (r.symm (0, y'))) * (fun t => h (r t).1 * Φ (r t).2) t := by
      funext t
      rw [hr, symplO_resS_symm_right, mul_left_comm]
    rw [hfun, hT.modul _ (hsb Φ hΦ) _ (half_resS_symm_right o hy'), hr, heisO_resS_symm_right]
    rfl
  · rw [one_smul]
  · funext y
    rw [restrRight_apply, hΞT, hsumE]
    rfl

end GlobalTheory.LastTgtSlice

end
