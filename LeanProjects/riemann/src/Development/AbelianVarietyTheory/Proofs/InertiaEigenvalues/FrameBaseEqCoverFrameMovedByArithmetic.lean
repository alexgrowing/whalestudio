import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseCoverFramesDifferByRationalIsometry
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverComponentEqImpliesBaseComponentEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGroupOfCongruent
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.CoverFrameArith

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem arch_rat {D : D7} (V : HSp D) {r : ℕ} (hr : V.rank = r) (ρ : GA D V) (hρ : ρ ∈ GQ V) :
    ∃ R : GL (Fin r) D.host.E, ∀ (τ : D.host.E →+* ℂ) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ),
      Formalism.MainNotions.StandardLattice.IsInfEmb τ θ → ∀ u : GA D V,
        Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ (ρ * u)) =
          (R : Matrix (Fin r) (Fin r) D.host.E).map τ * Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ u) := by
  subst hr
  obtain ⟨R, -, -, hRa⟩ := GlobalTheory.MarkCoset.rational_matrix V ρ hρ
  have hre : ∀ m : Matrix (Fin V.rank) (Fin V.rank) ℂ,
      Matrix.reindex (finCongr (rfl : V.rank = V.rank)) (finCongr rfl) m = m := fun m => by
    ext i j
    rfl
  refine ⟨R, fun τ θ hθ u => ?_⟩
  rw [hre, hre, archM, archM, map_mul, Units.val_mul, Matrix.map_mul, ← archM, hRa τ θ hθ]

theorem mulVec_add_nsmul {A : Type} [CommRing A] {n : ℕ} (m : Matrix (Fin n) (Fin n) A) (N : ℕ) (y y' : Fin n → A) :
    m *ᵥ (y + N • y') = m *ᵥ y + N • (m *ᵥ y') := by
  rw [Matrix.mulVec_add, Matrix.mulVec_smul]

set_option maxHeartbeats 1000000 in

theorem conj_move {D : D7} (V : HSp D) {r : ℕ} (hr : V.rank = r) (δa g₀ κ : GA D V) (hδ : δa ∈ GQ V) (N : ℕ)
    (hN : N ≠ 0) (hκ : ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V κ).1.mulVec z - z = N • y)
    (hκ' : ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V κ⁻¹).1.mulVec z - z = N • y)
    (he : finHom V (g₀⁻¹ * δa * g₀) = finHom V κ) (L : Submodule (𝓞 D.host.E) (Fin r → D.host.E))
    (hL : (L : Set (Fin r → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V g₀ : Set _))
    (G : Matrix (Fin r) (Fin r) D.host.E) (hG : G = -(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose) :
    ∃ Δ : GL (Fin r) D.host.E,
      (∀ v w, herm G ((Δ : Matrix (Fin r) (Fin r) D.host.E) *ᵥ v) ((Δ : Matrix (Fin r) (Fin r) D.host.E) *ᵥ w) =
        herm G v w) ∧
      (∀ v, v ∈ L ↔ (Δ : Matrix (Fin r) (Fin r) D.host.E) *ᵥ v ∈ L) ∧
      (∀ v ∈ L, ∃ u ∈ L, (Δ : Matrix (Fin r) (Fin r) D.host.E) *ᵥ v = v + N • u) ∧
      ∀ (τ : D.host.E →+* ℂ) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), Formalism.MainNotions.StandardLattice.IsInfEmb τ θ →
        ∀ u : GA D V, Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ (δa * u)) =
          (Δ : Matrix (Fin r) (Fin r) D.host.E).map τ * Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ u) := by
  subst hr
  have hgr : Matrix.reindex (finCongr (rfl : V.rank = V.rank)) (finCongr rfl) V.gram = V.gram := by
    ext i j
    rfl
  have hre : ∀ m : Matrix (Fin V.rank) (Fin V.rank) ℂ,
      Matrix.reindex (finCongr (rfl : V.rank = V.rank)) (finCongr rfl) m = m := fun m => by
    ext i j
    rfl
  rw [hgr] at hG
  obtain ⟨Δ, hΔu, hΔf, hΔa⟩ := GlobalTheory.MarkCoset.rational_matrix V δa hδ
  have hmem : ∀ v, v ∈ L ↔ finVec V v ∈ latGHat V g₀ := fun v => by
    rw [← (GlobalTheory.MarkCoset.latG_spec D V _).1, ← SetLike.mem_coe, hL]
    exact Set.ext_iff.1 (Set.image_id _) v
  have hfh : finHom V (δa * g₀ * κ⁻¹) = finHom V g₀ := by
    have e : δa * g₀ * κ⁻¹ = g₀ * (g₀⁻¹ * δa * g₀) * κ⁻¹ := by group
    rw [e, map_mul, map_mul, he, map_inv, mul_inv_cancel_right]
  have hLh : latGHat V (δa * g₀ * κ⁻¹) = latGHat V g₀ := by
    unfold latGHat gLat
    rw [hfh]
  obtain ⟨ht1, -⟩ := GlobalTheory.MarkCoset.transport (finHom V) (latGHat V) (fun g => (GlobalTheory.MarkCoset.latG_spec D V g).2) N
    δa g₀ κ⁻¹ (GlobalTheory.MarkCoset.level_latGHat V N κ⁻¹ hκ')
    (by rw [inv_inv]; exact GlobalTheory.MarkCoset.level_latGHat V N κ hκ)
  rw [hLh] at ht1
  refine ⟨Δ, fun v w => by rw [hG]; exact hΔu v w, fun v => by rw [hmem, hmem, ← hΔf]; exact ht1 _,
    fun v hv => ?_, fun τ θ hθ u => ?_⟩
  · obtain ⟨y, hy, hyz⟩ := ((GlobalTheory.MarkCoset.latG_spec D V g₀).2 _).1 ((hmem v).1 hv)
    obtain ⟨y', hy', ey⟩ := GlobalTheory.MarkCoset.level_latGHat V N κ hκ y hy
    have hc : (finHom V δa).1 *ᵥ ((finHom V g₀).1 *ᵥ y) = (finHom V g₀).1 *ᵥ ((finHom V κ).1 *ᵥ y) := by
      rw [← he, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul,
        show g₀ * (g₀⁻¹ * δa * g₀) = δa * g₀ by group]
    have hs : finVec V ((Δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v - v) =
        finVec V ((Δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v) - finVec V v := by
      funext i
      simp only [finVec, Pi.sub_apply, TensorProduct.tmul_sub]
    have key : finVec V ((Δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v - v) =
        N • ((finHom V g₀).1 *ᵥ y') := by
      rw [hs, ← hΔf, ← hyz, hc, ey, mulVec_add_nsmul, add_sub_cancel_left]
    obtain ⟨w, hw, e⟩ := GlobalTheory.MarkCoset.finVec_div V N hN _ _ key
    refine ⟨w, (hmem w).2 ?_, sub_eq_iff_eq_add'.1 e⟩
    rw [hw]
    exact ((GlobalTheory.MarkCoset.latG_spec D V g₀).2 _).2 ⟨y', hy', rfl⟩
  · rw [hre, hre, archM, archM, map_mul, Units.val_mul, Matrix.map_mul, ← archM, hΔa τ θ hθ]

set_option maxHeartbeats 4000000 in

theorem frame_move_arith : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (h h₀ : GA D (T.V j σ)), (C.dict₂ h).1 = (C.dict₂ h₀).1 → ∀ γ₀ : GL (Fin D.R.r) D.host.E, (((T.U j σ).X (T.dict j σ h₀).1).Λ : Set (Fin D.R.r → D.host.E)) = (γ₀ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X (C.dict₂ h₀).1).Λ : Set _) → (∀ v w, herm ((T.U j σ).X (T.dict j σ h₀).1).Gm ((γ₀ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ₀ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X (C.dict₂ h₀).1).Gm v w) → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h₀).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h₀).1).Ψ), mat (T.dict j σ h₀).2 ⟨τ, h₁⟩ = (γ₀ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h₀).2 ⟨τ, h₂⟩) → ∃ δ ∈ ((T.U j σ).X (T.dict j σ h).1).Γ, ∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat (T.dict j σ h).2 ⟨τ, h₁⟩ = (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * ((γ₀ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h).2 ⟨τ, h₂⟩) := by
  intro D T hT j hj σ hσ C hC h h₀ hh γ₀ _ _ hfr0
  have hk : (T.dict j σ h).1 = (T.dict j σ h₀).1 :=
    GlobalTheory.CoverRead.CompIndep.comp_eq_of_cover D T hT j hj σ hσ C hC h h₀ hh
  obtain ⟨hr₁, g₁, e₁, F₁, ik₁, φ₁, th₁, hι, -, hth₁, -, hd₁⟩ := hT.adPin j hj σ hσ
  obtain ⟨⟨-, hMl, -, hIl, -⟩, -, -, hU₂, hdom, hr₂, g₂, e₂, F₂, ik₂, φ₂, th₂, -, hth₂, -, hd₂⟩ := hC
  obtain ⟨hr₀, hW₁⟩ := hT.modelW j hj σ hσ
  have hU₁ := hT.unf j hj σ hσ
  have hK := hT.levelK j hj σ hσ
  rw [← hT.pins.2.1.1] at hK
  obtain ⟨γ₁, hγ₁, hL₁, hm₁, hf₁⟩ := hd₁ h
  obtain ⟨γ₁', hγ₁', hL₁', hm₁', hf₁'⟩ := hd₁ h₀
  obtain ⟨γ₂, hγ₂, hL₂, hm₂, hf₂⟩ := hd₂ h
  obtain ⟨γ₂', hγ₂', hL₂', hm₂', hf₂'⟩ := hd₂ h₀

  obtain ⟨M₀, hM₀⟩ := arch_rat (T.V j σ) hr₁ (γ₁' * γ₂'⁻¹) (mul_mem hγ₁' (inv_mem hγ₂'))
  have hΨ : ∀ (g : GA D (T.V j σ)) τ, τ ∈ ((T.U j σ).X (T.dict j σ g).1).Ψ ↔ τ ∈ (C.U₂.X (C.dict₂ g).1).Ψ :=
    fun g τ => ((hU₁.2.1 _).2 τ).trans ((hU₂.2.1 _).2 τ).symm
  have hM0eq : (M₀ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) = γ₀ := by
    obtain ⟨τ, t₂⟩ : ∃ τ, τ ∈ (C.U₂.X (C.dict₂ h₀).1).Ψ := by
      by_cases h0 : D.host.φ₀ ∈ (C.U₂.X (C.dict₂ h₀).1).Ψ
      · exact ⟨_, h0⟩
      · exact ⟨_, not_not.1 (mt ((C.U₂.X (C.dict₂ h₀).1).cmType _).2 h0)⟩
    have t₁ := (hΨ h₀ τ).2 t₂
    have a₁ := hf₁' ⟨τ, t₁⟩
    have a₂ := hf₂' ⟨τ, t₂⟩
    rw [GlobalTheory.LettersCheck.isInfEmb_unique τ _ _ (hth₂ _ ⟨τ, t₂⟩) (hth₁ _ ⟨τ, t₁⟩)] at a₂
    have e : γ₁' * h₀ = γ₁' * γ₂'⁻¹ * (γ₂' * h₀) := by group
    rw [e, hM₀ τ _ (hth₁ _ ⟨τ, t₁⟩), Matrix.mul_assoc, ← a₂] at a₁
    have a₃ := (hfr0 τ t₂ t₁).symm.trans a₁
    have hu : IsUnit (mat (C.dict₂ h₀).2 ⟨τ, t₂⟩) :=
      (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit (hdom h₀ ⟨τ, t₂⟩).1)
    exact (Matrix.map_injective τ.injective (hu.mul_right_cancel a₃)).symm

  rw [← hk] at hL₁' hm₁'
  rw [← hh] at hL₂' hm₂'
  have hinj : ∀ hr : (T.V j σ).rank = D.R.r,
      Function.Injective (fun v : Fin (T.V j σ).rank → D.host.E => v ∘ Fin.cast hr.symm) := fun hr u v huv =>
    funext fun i => congrFun huv (Fin.cast hr i)
  have hLb : latG (T.V j σ) (γ₁' * h₀) = latG (T.V j σ) (γ₁ * h) :=
    SetLike.coe_injective ((hinj hr₁).image_injective (hL₁'.symm.trans hL₁))
  have hLc : latG (T.V j σ) (γ₂ * h) = latG (T.V j σ) (γ₂' * h₀) :=
    SetLike.coe_injective ((hinj hr₂).image_injective (hL₂.symm.trans hL₂'))

  obtain ⟨a₁, ha₁, k₁, hk₁, eak₁⟩ := (GlobalTheory.UnitarySplit.real_finite_split D (T.V j σ)).1 ((γ₁' * h₀)⁻¹ * (γ₁ * h))
  obtain ⟨a₂, ha₂, k₂, hk₂, eak₂⟩ := (GlobalTheory.UnitarySplit.real_finite_split D (T.V j σ)).1 ((γ₂ * h)⁻¹ * (γ₂' * h₀))
  have hk₁K : k₁ ∈ T.Kf j σ := by
    refine (hT.kfHalf j hj σ hσ k₁).2 ⟨hk₁, ?_⟩
    have hmA := hm₁'
    have hmB := hm₁
    rw [show (T.Q.l.M : ℕ) = T.Q.l.M * 1 from (mul_one _).symm] at hmA hmB
    exact GlobalTheory.CoverRead.CompIndep.congr_of_marked (T.V j σ) _ hι _ _ one_ne_zero _ _
      (fun b hb => by rwa [Nat.cast_one, one_mul]) (γ₁' * h₀) (γ₁ * h) k₁
      (by rw [eak₁, map_mul, show finHom (T.V j σ) a₁ = 1 from ha₁, one_mul]) hLb _ hmA hmB
  have hp : C.d.pd ≠ 0 := fun h0 => by
    have := C.d.l₂.three_le
    rw [hMl, h0] at this
    omega
  have hk₂K : k₂ ∈ T.Kf j σ := by
    refine (hT.kfHalf j hj σ hσ k₂).2 ⟨hk₂, ?_⟩
    have hmA := hm₂
    have hmB := hm₂'
    rw [hMl] at hmA hmB
    exact GlobalTheory.CoverRead.CompIndep.congr_of_marked (T.V j σ) _ hι _ _ hp _ _
      (GlobalTheory.CoverRead.CompIndep.ratio_mul_mem T.Q.l C.d.l₂ _ _ hMl hIl) (γ₂ * h) (γ₂' * h₀) k₂
      (by rw [eak₂, map_mul, show finHom (T.V j σ) a₂ = 1 from ha₂, one_mul]) hLc _ hmA hmB
  have hκK : k₁ * k₂ ∈ T.Kf j σ := mul_mem hk₁K hk₂K
  have he : finHom (T.V j σ) ((γ₁' * h₀)⁻¹ * (γ₁ * γ₂⁻¹ * γ₂' * γ₁'⁻¹) * (γ₁' * h₀)) =
      finHom (T.V j σ) (k₁ * k₂) := by
    have e : (γ₁' * h₀)⁻¹ * (γ₁ * γ₂⁻¹ * γ₂' * γ₁'⁻¹) * (γ₁' * h₀) =
        ((γ₁' * h₀)⁻¹ * (γ₁ * h)) * ((γ₂ * h)⁻¹ * (γ₂' * h₀)) := by group
    rw [e, map_mul, eak₁, eak₂, map_mul, map_mul, show finHom (T.V j σ) a₁ = 1 from ha₁,
      show finHom (T.V j σ) a₂ = 1 from ha₂, one_mul, one_mul, map_mul]
  have hM0' : T.Q.l.M ≠ 0 := by
    have := T.Q.l.three_le
    omega
  have hδa : γ₁ * γ₂⁻¹ * γ₂' * γ₁'⁻¹ ∈ GQ (T.V j σ) :=
    mul_mem (mul_mem (mul_mem hγ₁ (inv_mem hγ₂)) hγ₂') (inv_mem hγ₁')
  obtain ⟨Δ, hΔi, hΔl, hΔc, hΔa⟩ := conj_move (T.V j σ) hr₁ _ (γ₁' * h₀) (k₁ * k₂) hδa T.Q.l.M hM0'
    ((hK _).1 hκK).2 ((hK _).1 (inv_mem hκK)).2 he _ hL₁' _ (hW₁ (T.dict j σ h).1).1
  refine ⟨Δ, GlobalTheory.PrincCore.mem_group_of_congruent D T.toCore hT.toLawsM j hj σ hσ _ Δ ⟨hΔi, hΔl⟩ hΔc,
    fun τ t₂ t₁ => ?_⟩
  have a₁ := hf₁ ⟨τ, t₁⟩
  have a₂ := hf₂ ⟨τ, t₂⟩
  rw [GlobalTheory.LettersCheck.isInfEmb_unique τ _ _ (hth₂ _ ⟨τ, t₂⟩) (hth₁ _ ⟨τ, t₁⟩)] at a₂
  have e : γ₁ * h = (γ₁ * γ₂⁻¹ * γ₂' * γ₁'⁻¹) * ((γ₁' * γ₂'⁻¹) * (γ₂ * h)) := by group
  rw [a₁, e, hΔa τ _ (hth₁ _ ⟨τ, t₁⟩), hM₀ τ _ (hth₁ _ ⟨τ, t₁⟩), Matrix.mul_assoc, Matrix.mul_assoc, ← a₂, hM0eq]

end GlobalTheory.CoverFrameArith
