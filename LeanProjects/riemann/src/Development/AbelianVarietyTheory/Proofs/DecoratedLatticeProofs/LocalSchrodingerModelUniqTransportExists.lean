import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontriviaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFrameHalfInverseStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixIntegralOfAddCharTraceDualStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSchrodingerIntertwinerIntegralMatricesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreducStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LocModU

theorem upAdd {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (x x' : Matrix Y Y' k) :
    p.up FS FT (x + x') = p.up FS FT x + p.up FS FT x' := by
  unfold Place.up
  rw [Matrix.mul_add, Matrix.add_mul]
  ext i j
  simp [Matrix.map_apply]

theorem upZero {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) : p.up FS FT 0 = 0 := by
  unfold Place.up
  ext i j
  simp [Matrix.map_apply]

theorem charZero_of_place {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : Place D k) : CharZero k :=
  (RingHom.charZero_iff (ϕ := p.π.comp (incA D)) (RingHom.injective _)).1 inferInstance

theorem localModel_uniq_transport_exist : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → (∀ T₁ T₂, p.IsModel ψ FS FT T₁ → p.IsModel ψ FS FT T₂ → ∀ Φ₀, Φ₀ ≠ 0 → T₁ Φ₀ = T₂ Φ₀ → T₁ = T₂) ∧ (∀ T₁, p.IsModel ψ FS FT T₁ → ∀ A : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), (∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (A f)) → (∀ f, IsThetaFunO ψ S T f → ∀ y : WO S T, IsHalf (p.e + cA D p.e) y → A (heisO ψ S T y f) = heisO ψ S T y (A f)) → p.IsModel ψ FS FT (A ∘ₗ T₁)) ∧ ∀ f₀, IsThetaFunO ψ S T f₀ → (∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) → heisO ψ S T (p.up FS FT x) f₀ = f₀) → (∀ y : WO S T, IsHalf (cA D p.e) y → (∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) → ψ (symplO S T (p.up FS FT x) y) = 1) → heisO ψ S T y f₀ = f₀) → ∃ T₁, p.IsModel ψ FS FT T₁ ∧ ∀ Φ : SB (Matrix Y Y' k), Φ.1 = Set.indicator {x | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) → T₁ Φ = f₀ := by
  intro D k _ _ _ _ p Y Y' _ _ _ _ S T FS FT ψ hψ
  haveI : CharZero k := charZero_of_place p
  obtain ⟨⟨ψk, hψk⟩, hcn, -, -, -⟩ := GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial D k p ψ hψ
  obtain ⟨hcont, hne⟩ := hcn ψk hψk
  obtain ⟨hup, -, -, hsymk, hsurj⟩ := GlobalTheory.T.heisenberg_frame_half_inverse D k p Y Y' S T FS FT ψ ψk hψk
  obtain ⟨-, hec, -⟩ := p.split
  have hce : cA D p.e * p.e = 0 := by rw [mul_comm, hec]
  have hcce : cA D (cA D p.e) * cA D p.e = 0 := by rw [GlobalTheory.DualPairCheck.cA_cA, hec]
  have halfSum1 : ∀ u : WO S T, IsHalf p.e u → IsHalf (p.e + cA D p.e) u := fun u hu i j => by
    rw [add_mul, hu i j, ← hu i j, ← mul_assoc, hce, zero_mul, add_zero, hu i j]
  have halfSum2 : ∀ u : WO S T, IsHalf (cA D p.e) u → IsHalf (p.e + cA D p.e) u := fun u hu i j => by
    rw [add_mul, hu i j, ← hu i j, ← mul_assoc, hec, zero_mul, zero_add, hu i j]
  refine ⟨?_, ?_, ?_⟩
  ·
    intro T₁ T₂ h₁ h₂ Φ₀ hΦ₀ h12
    let W : Submodule ℂ (Matrix Y Y' k → ℂ) := (LinearMap.ker (T₁ - T₂)).map (SB (Matrix Y Y' k)).subtype
    have memW : ∀ Φ : SB (Matrix Y Y' k), Φ.1 ∈ W ↔ T₁ Φ = T₂ Φ := by
      intro Φ
      constructor
      · rintro ⟨Ψ, hΨ, hΨe⟩
        have : Ψ = Φ := Subtype.ext hΨe
        subst this
        simpa [sub_eq_zero] using hΨ
      · intro h
        exact ⟨Φ, by simpa [sub_eq_zero] using h, rfl⟩
    have hWle : W ≤ SB (Matrix Y Y' k) := by
      rintro _ ⟨Ψ, -, rfl⟩
      exact Ψ.2
    have hWeq := GlobalTheory.T.schwartzBruhat_matrix_translation_modulation_irreducible k Y Y' ψk hcont hne W hWle
      (by
        rintro _ ⟨Φ, hΦ, rfl⟩ x hx
        have hΦ' : T₁ Φ = T₂ Φ := (memW Φ).1 ⟨Φ, hΦ, rfl⟩
        refine (memW ⟨_, hx⟩).2 ?_
        rw [h₁.trans x Φ ⟨_, hx⟩ (fun t => rfl), h₂.trans x Φ ⟨_, hx⟩ (fun t => rfl), hΦ'])
      (by
        rintro _ ⟨Φ, hΦ, rfl⟩ b hb
        have hΦ' : T₁ Φ = T₂ Φ := (memW Φ).1 ⟨Φ, hΦ, rfl⟩
        obtain ⟨y, hy, hyb⟩ := hsurj b
        have hmod : ∀ t, (⟨_, hb⟩ : SB (Matrix Y Y' k)).1 t = ψ (symplO S T (p.up FS FT t) y) * Φ.1 t := by
          intro t
          show _ = _
          rw [hsymk t y hy, hyb t]
          rfl
        refine (memW ⟨_, hb⟩).2 ?_
        rw [h₁.modul y hy Φ _ hmod, h₂.modul y hy Φ _ hmod, hΦ'])
      Φ₀.1 ((memW Φ₀).2 h12) (fun h => hΦ₀ (Subtype.ext h))
    ext1 Φ
    have hm : Φ.1 ∈ W := by rw [hWeq]; exact Φ.2
    exact (memW Φ).1 hm
  ·
    intro T₁ h₁ A hA1 hA2
    refine ⟨fun Φ => hA1 _ (h₁.theta Φ), fun x Φ Φ' h => ?_, fun y hy Φ Φ' h => ?_⟩
    · show A (T₁ Φ') = heisO ψ S T (p.up FS FT x) (A (T₁ Φ))
      rw [h₁.trans x Φ Φ' h, hA2 _ (h₁.theta Φ) _ (halfSum1 _ (hup x).1)]
    · show A (T₁ Φ') = heisO ψ S T y (A (T₁ Φ))
      rw [h₁.modul y hy Φ Φ' h, hA2 _ (h₁.theta Φ) _ (halfSum2 _ hy)]
  ·
    intro f₀ hf₀ hfx hfy
    let Z := GlobalTheory.PlaceModel.half S T (cA D p.e)
    let χ : Matrix Y Y' k → Z → ℂ := fun t z => ψ (symplO S T (p.up FS FT t) z.1)
    have hZ : ∀ z : Z, IsHalf (cA D p.e) z.1 := fun z => (GlobalTheory.PlaceModel.isHalf_iff S T).2 z.2
    obtain ⟨Tm, htr, hmo, hvac, hspan⟩ := GlobalTheory.T.exists_schrodinger_intertwiner_integralMatrices k Y Y' Z χ
      (fun a b z => by simp only [χ, upAdd, GlobalTheory.PlaceModel.symplO_add_left, AddChar.map_add_eq_mul])
      (fun a z z' => by simp only [χ, AddSubgroup.coe_add, GlobalTheory.PlaceModel.symplO_add_right, AddChar.map_add_eq_mul])
      (fun z => by simp only [χ, upZero, GlobalTheory.PlaceModel.symplO_zero_left, AddChar.map_zero_eq_one])
      (fun a => by simp only [χ, ZeroMemClass.coe_zero, GlobalTheory.PlaceModel.symplO_zero_right, AddChar.map_zero_eq_one])
      (fun n hn z => by
        obtain ⟨z', hz', e⟩ := GlobalTheory.PlaceModel.half_div S T (cA D p.e) n hn z.1 z.2
        exact ⟨⟨z', hz'⟩, Subtype.ext (by rw [AddSubgroup.coe_nsmul]; exact e)⟩)
      (fun n hn z z' h => by
        apply Subtype.ext
        have h' : n • z.1 = n • z'.1 := by
          have := congrArg Subtype.val h
          simpa only [AddSubgroup.coe_nsmul] using this
        rw [← GlobalTheory.PlaceModel.inv_smul_nsmul S T hn z.1, h', GlobalTheory.PlaceModel.inv_smul_nsmul S T hn])
      (fun x hx => GlobalTheory.T.matrix_integral_of_addChar_trace_dual k Y Y' ψk hcont hne x fun b hb => by
        obtain ⟨y, hy, hyb⟩ := hsurj b
        have key : ∀ t, χ t ⟨y, (GlobalTheory.PlaceModel.isHalf_iff S T).1 hy⟩ = ((ψk (∑ r, ∑ q, b r q * t r q) : Circle) : ℂ) := by
          intro t
          show ψ _ = _
          rw [hsymk t y hy, hyb t]
        have := hx ⟨y, (GlobalTheory.PlaceModel.isHalf_iff S T).1 hy⟩ (fun u hu => by
          rw [key, hb u hu, Circle.coe_one])
        rw [key] at this
        exact Circle.ext (by simpa using this))
      (WO S T → ℂ) (fun x => GlobalTheory.PlaceModel.heisL S T ψ (p.up FS FT x)) (fun z => GlobalTheory.PlaceModel.heisL S T ψ z.1)
      (fun x x' f => by
        rw [GlobalTheory.PlaceModel.heisL_half S T ψ hce _ ((GlobalTheory.PlaceModel.isHalf_iff S T).1 (hup x).1) _
          ((GlobalTheory.PlaceModel.isHalf_iff S T).1 (hup x').1), upAdd])
      (fun z z' f => by
        rw [GlobalTheory.PlaceModel.heisL_half S T ψ hcce _ z.2 _ z'.2]
        rfl)
      (fun x z f => GlobalTheory.PlaceModel.heisL_comm S T ψ _ _ f)
      (fun f => by
        rw [upZero]
        funext w
        show ψ (symplOH S T w 0) * f (w + 0) = f w
        rw [symplOH, GlobalTheory.PlaceModel.symplO_zero_right, mul_zero, AddChar.map_zero_eq_one, one_mul, add_zero])
      (fun f => by
        funext w
        show ψ (symplOH S T w 0) * f (w + 0) = f w
        rw [symplOH, GlobalTheory.PlaceModel.symplO_zero_right, mul_zero, AddChar.map_zero_eq_one, one_mul, add_zero])
      f₀ (fun u hu => hfx u hu)
      (fun z hz => hfy z.1 (hZ z) hz)
    have hsplit := p.split
    have hstd : IsCharAF D.host.F ψ := hψ.1
    refine ⟨Tm, ⟨fun Φ => ?_, fun x Φ Φ' h => htr x Φ Φ' h, fun y hy Φ Φ' h =>
      hmo ⟨y, (GlobalTheory.PlaceModel.isHalf_iff S T).1 hy⟩ Φ Φ' h⟩, hvac⟩
    have hs := hspan Φ
    generalize Tm Φ = g at hs
    induction hs using Submodule.span_induction with
    | mem _ hw =>
      obtain ⟨w, rfl⟩ := hw
      exact GlobalTheory.FinTranslate.isTheta_heisO_fin hstd (GlobalTheory.SplitScalar.half_fin hsplit (hup w.1).1)
        (GlobalTheory.FinTranslate.isTheta_heisO_fin hstd
          (GlobalTheory.SplitScalar.half_fin (GlobalTheory.SplitScalar.isSplitIdem_conj hsplit) (hZ w.2)) hf₀)
    | zero => exact GlobalTheory.WeilVacMove.isTheta_zero
    | add _ _ _ _ h1 h2 => exact GlobalTheory.WeilVacMove.isTheta_add h1 h2
    | smul c _ _ h1 => exact GlobalTheory.WeilVacMove.isTheta_smul c h1

end GlobalTheory.LocModU
