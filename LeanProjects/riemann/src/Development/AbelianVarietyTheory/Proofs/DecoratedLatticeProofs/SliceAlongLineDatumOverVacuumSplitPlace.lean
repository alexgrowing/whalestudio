import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUnique
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroSourceTensorColumnProductStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatIndLastKerRow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulHalf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSBExtFunEqHalfInd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OfTensColMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionProductsSlicesOrthogonalDecompositi

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LastSrcSlice

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem col_mem_SB {n n' : Type} {Ψ : Matrix n n' k → ℂ} {a : (n → k) → ℂ}
    (h : tensCol Ψ a ∈ SB (Matrix n (n' ⊕ Fin 1) k)) (hΨ : Ψ ≠ 0) : a ∈ SB (n → k) := by
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, Ψ x₀ ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact hΨ (funext h0)
  have hg := Comm.comp_mem_SB h
    (p := fun y : n → k => Matrix.of fun i j => Sum.elim (x₀ i) (fun _ => y i) j)
    (s := fun x : Matrix n (n' ⊕ Fin 1) k => fun i => x i (Sum.inr 0)) ?_ (by fun_prop) (fun y => rfl)
  · have e : a = (Ψ x₀)⁻¹ • fun y : n → k =>
        tensCol Ψ a (Matrix.of fun i j => Sum.elim (x₀ i) (fun _ => y i) j) := by
      funext y
      show a y = (Ψ x₀)⁻¹ * (Ψ x₀ * a y)
      field_simp
    rw [e]
    exact Submodule.smul_mem _ _ hg
  · refine continuous_matrix fun i j => ?_
    rcases j with j | j
    · exact continuous_const
    · exact (continuous_apply i)

theorem sb_of_sbHalf (p : SplitPt D k) {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {S T : HSp D} (α : Frame p S n') (β : Frame p T n) {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS)
    (hT : IsSelfDualC T LT) {Φ : WO S T → ℂ} (hΦ : IsSBHalf p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) Φ) :
    (fun x => Φ (HalfInd.wr α β x)) ∈ SB (Matrix n n' k) := by
  classical
  haveI := Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := n) (n' := n')
  have : CharZero k := charZero_of_injective_ringHom (f := p.pr.comp (incA D)) (RingHom.injective _)
  obtain ⟨-, k0, hk0, hinv, hsup⟩ := hΦ
  obtain ⟨hUc, hUo⟩ := HalfInd.compact_open α β hS hT
  set U := {x : Matrix n n' k | HalfInd.wr α β x ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) ∧
    IsHalf p.e (HalfInd.wr α β x)} with hU
  have hc : ((k0 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.2 hk0.ne'
  have hwr : ∀ z : Matrix n n' k, HalfInd.wr α β (((k0 : ℕ) : k) • z) = k0 • HalfInd.wr α β z := by
    intro z
    rw [Nat.cast_smul_eq_nsmul, map_nsmul]
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, ?_⟩
  · refine ⟨{x' | ((k0 : ℕ) : k)⁻¹ • (x' - x) ∈ U}, hUo.preimage (by fun_prop), ?_, fun x' hx' => ?_⟩
    · show ((k0 : ℕ) : k)⁻¹ • (x - x) ∈ U
      rw [sub_self, smul_zero]
      refine ⟨?_, HalfInd.isHalf_wr α β 0⟩
      rw [map_zero]; exact zero_mem _
    · set z := ((k0 : ℕ) : k)⁻¹ • (x' - x) with hz
      have hx'z : x' = x + ((k0 : ℕ) : k) • z := by
        rw [hz, smul_smul, mul_inv_cancel₀ hc, one_smul, add_sub_cancel]
      show Φ (HalfInd.wr α β x') = Φ (HalfInd.wr α β x)
      rw [hx'z, map_add, hwr]
      exact hinv _ hx'.1 hx'.2 _
  · refine HasCompactSupport.intro (hUc.image (f := fun z => ((k0 : ℕ) : k)⁻¹ • z) (by fun_prop)) fun x hx => ?_
    by_contra h
    have h1 := hsup _ h
    have h2 : ((k0 : ℕ) : k) • x ∈ U := by
      refine ⟨?_, HalfInd.isHalf_wr α β _⟩
      rw [hwr]; exact h1
    exact hx ⟨_, h2, by beta_reduce; rw [smul_smul, inv_mul_cancel₀ hc, one_smul]⟩

theorem extFun_wr (p : SplitPt D k) {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {S T : HSp D} (α : Frame p S n') (β : Frame p T n) {Φ : WO S T → ℂ} (hΦ : ∀ t, Φ t ≠ 0 → IsHalf p.e t) :
    extFun α β (fun x => Φ (HalfInd.wr α β x)) = Φ := by
  classical
  funext t
  unfold extFun
  by_cases ht : IsHalf p.e t
  · rw [if_pos ht]
    beta_reduce
    rw [HalfInd.wr_rd α β ht]
  · rw [if_neg ht]
    by_contra h
    exact ht (hΦ t (Ne.symm h))

end GlobalTheory.LastSrcSlice

namespace GlobalTheory.LastSrcSlice

theorem main : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (V₀ A L S : HSp D) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : Frame p A n') (α₀ : Frame p V₀ (n' ⊕ Fin 1)) (β : Frame p S n), IsSumFrame o ζ α α₀ → ∀ (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ), a ≠ 0 → ∀ (LA : Lat A) (LS : Lat S), IsSelfDualC A LA → IsSelfDualC S LS → ∀ (L₁ : Lat V₀) (L₂ : Lat S) (f₁ Ξ : WO V₀ S → ℂ), Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ a) Ξ → ∀ y : WO L S, ∃ g, Over ψ α β LA LS g Ψ (fun u => Ξ ((o.resS S).symm (u, y))) := by
  intro D k _ _ _ _ p n n' _ _ _ _ ψ hψ _ V₀ A L S o ζ _ α α₀ β hsum Ψ a ha LA LS hLA hLS L₁ L₂ f₁ Ξ hΞ y
  obtain ⟨hL₁, hL₂, hf₁, hSB, ⟨T, hT⟩, hall⟩ := hΞ
  have hΞT : Ξ = T (extFun α₀ β (tensCol Ψ a)) := hall T hT
  by_cases hΨ0 : Ψ = 0
  ·
    subst hΨ0
    have hext : extFun α₀ β (tensCol (0 : Matrix n n' k → ℂ) a) = 0 := by
      classical
      funext t
      simp [extFun, tensCol]
    have hslice : (fun u => Ξ ((o.resS S).symm (u, y))) = 0 := by
      rw [hΞT, hext, map_zero]; rfl
    have hheis0 : ∀ (w : WO A S), heisO ψ A S w (0 : WO A S → ℂ) = 0 := by
      intro w; funext x; simp [heisO]
    refine ⟨0, hLA, hLS, ⟨?_, ?_⟩, Submodule.zero_mem _, ⟨0, ?_⟩, fun T' hT' => ?_⟩
    · exact { quasi := fun γ w => by simp
              level := ⟨⊤, isOpen_univ, fun u _ _ => hheis0 u⟩
              cont := continuous_const
              smooth := fun _ _ _ _ _ => by simpa using contDiff_const }
    · exact ⟨fun u _ => hheis0 _, fun _ _ u _ _ => hheis0 u⟩
    · exact ⟨fun Φ _ x _ => by simp [hheis0], fun Φ _ y' _ => by simp [hheis0], by simp⟩
    · rw [hslice]
      have : extFun α β (0 : Matrix n n' k → ℂ) = 0 := by
        classical
        funext t; simp [extFun]
      beta_reduce
      rw [this, map_zero]
  · have haSB : a ∈ SB (n → k) := col_mem_SB hSB hΨ0
    have hΨSB : Ψ ∈ SB (Matrix n n' k) := TensSB.of_tensCol_mem hSB ha
    set r := o.resS S with hr
    set a' := ExtZero.colFun β ζ a with ha'
    set ΛA := latO A S (LA : Set (Fin A.rank → D.host.E)) (LS : Set (Fin S.rank → D.host.E)) (· = p.v) with hΛA
    set Λ₁ := latO V₀ S (L₁ : Set (Fin V₀.rank → D.host.E)) (L₂ : Set (Fin S.rank → D.host.E)) (· = p.v) with hΛ₁
    set T₁ := ExtZero.restrModel r a' T y with hT₁
    set g := T₁ (halfInd p.e ΛA) with hg
    have hbox : ∀ Φ : WO A S → ℂ, (fun t => Φ (r t).1 * a' (r t).2) = o.boxS S Φ a' := fun Φ => rfl

    have hsb : ∀ Φ, IsSBHalf p.e ΛA Φ → IsSBHalf p.e Λ₁ (fun t => Φ (r t).1 * a' (r t).2) := by
      intro Φ hΦ
      have h1 := sb_of_sbHalf p α β hLA hLS hΦ
      have h2 := extFun_wr p α β (Φ := Φ) hΦ.1
      rw [hbox, ← h2, ← GlobalTheory.T.extendByZero_source_tensor_column_product D k p n n' V₀ A L S o ζ α α₀ β hsum]
      exact OverProof.isSBHalf_extFun D k p _ _ V₀ S α₀ β L₁ L₂ hL₁ hL₂ _ (Comm.tensCol_mem h1 haSB)

    have hmodel : IsPlaceModel ψ (symplO A S) (heisO ψ A S) p.e ΛA 1 g T₁ := by
      refine ⟨?_, ?_, ?_⟩
      · intro Φ hΦ x hx
        funext w
        rw [ExtZero.restrModel_apply]
        have hfun : (fun t => (fun t => Φ (t + x)) (r t).1 * a' (r t).2) =
            fun t => (fun t => Φ (r t).1 * a' (r t).2) (t + r.symm (x, 0)) := by
          funext t
          simp only [map_add, AddEquiv.apply_symm_apply, Prod.fst_add, Prod.snd_add, add_zero]
        rw [hfun, hT.trans _ (hsb Φ hΦ) _ (ExtZero.half_resS_symm o hx), hr, ExtZero.heisO_resS_symm]
        rfl
      · intro Φ hΦ y' hy'
        funext w
        rw [ExtZero.restrModel_apply]
        have hfun : (fun t => (fun t => ψ (symplO A S t y') * Φ t) (r t).1 * a' (r t).2) =
            fun t => ψ (symplO V₀ S t (r.symm (y', 0))) * (fun t => Φ (r t).1 * a' (r t).2) t := by
          funext t
          rw [hr, ExtZero.symplO_resS_symm, mul_assoc]
        rw [hfun, hT.modul _ (hsb Φ hΦ) _ (ExtZero.half_resS_symm o hy'), hr, ExtZero.heisO_resS_symm]
        rfl
      · rw [one_smul]

    have hlat : IsLatVac (heisO ψ A S) ΛA g :=
      Rebase.latVac_image D k p ψ hψ A S LA LA LS LS hLA hLS hLA hLS g T₁ hmodel

    have htheta : IsThetaFunO ψ A S g := by
      obtain ⟨ΨA, hΨA, hΨAe⟩ := HalfInd.exists_SB_extFun_eq_halfInd D k p A S n n' α β LA LS hLA hLS
      have hover := (GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n (n' ⊕ Fin 1) ψ hψ V₀ S α₀ β L₁ L₂ hL₁ hL₂ f₁ hf₁).1
      obtain ⟨F, hF, -⟩ := hover _ (Comm.tensCol_mem hΨA haSB)
      have hFth := ((GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n (n' ⊕ Fin 1) ψ hψ V₀ S α₀ β L₁ L₂ hL₁ hL₂ f₁ hf₁).2.1 _ _ hF).1
      have hFT : F = T (extFun α₀ β (tensCol ΨA a)) := hF.2.2.2.2.2 T hT
      rw [GlobalTheory.T.extendByZero_source_tensor_column_product D k p n n' V₀ A L S o ζ α α₀ β hsum, hΨAe] at hFT
      have := GlobalTheory.BoxSlice.isThetaFunO_slice_left o hFth y
      rw [hFT] at this
      exact this
    have hvac : Vac ψ A S LA LS (· = p.v) g := ⟨htheta, hlat⟩

    have hslice : (fun u => Ξ ((o.resS S).symm (u, y))) = T₁ (extFun α β Ψ) := by
      funext u
      rw [ExtZero.restrModel_apply, hΞT, GlobalTheory.T.extendByZero_source_tensor_column_product D k p n n' V₀ A L S o ζ α α₀ β hsum]
      rfl
    refine ⟨g, ?_⟩
    obtain ⟨f, hf, -⟩ := (GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n n' ψ hψ A S α β LA LS hLA hLS g hvac).1 Ψ hΨSB
    have hfT₁ : f = T₁ (extFun α β Ψ) := hf.2.2.2.2.2 T₁ hmodel
    rw [hslice, ← hfT₁]
    exact hf

end GlobalTheory.LastSrcSlice
