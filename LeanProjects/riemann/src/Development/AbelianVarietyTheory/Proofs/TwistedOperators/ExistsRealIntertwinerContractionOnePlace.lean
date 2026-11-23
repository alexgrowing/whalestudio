import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqMulProdOfPartial
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesPureInnerProductsTensorProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubstitutionTotalDegreeLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt GlobalTheory.Chain.RealLine
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.RealLine.Semi

open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} [DecidableEq D.what₂.Tau]

theorem actT_tprod (M : DSModel V S) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (v : ∀ ρ, M.H ρ) :
    actT M τ g (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v τ (M.rep τ g (v τ))) := by
  unfold actT
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext ρ
  by_cases h : ρ = τ
  · subst h
    simp
  · rw [Function.update_of_ne h]
    simp [Function.update, h]

theorem ellT_left (M : DSModel V S) (τ : D.what₂.Tau) (w z : ∀ ρ, M.H ρ) (u : M.H τ) :
    ellT M (Function.update w τ u) (PiTensorProduct.tprod ℂ z) =
      ⟪u, z τ⟫_ℂ * ∏ ρ ∈ Finset.univ.erase τ, ⟪w ρ, z ρ⟫_ℂ := by
  unfold ellT
  simp only [PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun ρ hρ => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hρ)]
  rfl

theorem ellT_right (M : DSModel V S) (τ : D.what₂.Tau) (w z : ∀ ρ, M.H ρ) (u : M.H τ) :
    ellT M w (PiTensorProduct.tprod ℂ (Function.update z τ u)) =
      ⟪w τ, u⟫_ℂ * ∏ ρ ∈ Finset.univ.erase τ, ⟪w ρ, z ρ⟫_ℂ := by
  unfold ellT
  simp only [PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun ρ hρ => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hρ)]
  rfl

theorem inclT_update (M : DSModel V S) (τ : D.what₂.Tau) (v : M.Vec) (y : M.sm τ) :
    inclT M (PiTensorProduct.tprod ℂ (Function.update v τ y)) =
      PiTensorProduct.tprod ℂ (Function.update (fun ρ => (v ρ : M.H ρ)) τ (y : M.H τ)) := by
  unfold inclT
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext ρ
  by_cases h : ρ = τ
  · subst h
    simp
  · rw [Function.update_of_ne h, Function.update_of_ne h]
    rfl

theorem exists_ctr (M : DSModel V S) (τ : D.what₂.Tau) (w : ∀ ρ, M.H ρ) :
    ∃ c : (⨂[ℂ] ρ, M.H ρ) →ₗ[ℂ] M.H τ, (∀ u x, ⟪u, c x⟫_ℂ = ellT M (Function.update w τ u) x) ∧
      ∀ g x, c (actT M τ g x) = M.rep τ g (c x) := by
  have hadd : ∀ (z : ∀ ρ, M.H ρ) (i : D.what₂.Tau) (x y : M.H i),
      (∏ ρ ∈ Finset.univ.erase τ, ⟪w ρ, Function.update z i (x + y) ρ⟫_ℂ) • Function.update z i (x + y) τ =
        (∏ ρ ∈ Finset.univ.erase τ, ⟪w ρ, Function.update z i x ρ⟫_ℂ) • Function.update z i x τ +
          (∏ ρ ∈ Finset.univ.erase τ, ⟪w ρ, Function.update z i y ρ⟫_ℂ) • Function.update z i y τ := by
    intro z i x y
    by_cases h : i = τ
    · subst h
      have e : ∀ a : M.H i, ∏ ρ ∈ Finset.univ.erase i, ⟪w ρ, Function.update z i a ρ⟫_ℂ =
          ∏ ρ ∈ Finset.univ.erase i, ⟪w ρ, z ρ⟫_ℂ := fun a =>
        Finset.prod_congr rfl fun ρ hρ => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hρ)]
      simp only [e, Function.update_self, smul_add]
    · have hi : i ∈ Finset.univ.erase τ := Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩
      have e : ∀ a : M.H i, ∏ ρ ∈ Finset.univ.erase τ, ⟪w ρ, Function.update z i a ρ⟫_ℂ =
          ⟪w i, a⟫_ℂ * ∏ ρ ∈ (Finset.univ.erase τ).erase i, ⟪w ρ, z ρ⟫_ℂ := fun a => by
        rw [← Finset.mul_prod_erase _ _ hi, Function.update_self]
        congr 1
        exact Finset.prod_congr rfl fun ρ hρ => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hρ)]
      simp only [e, Function.update_of_ne (Ne.symm h), inner_add_right, add_mul, add_smul]
  have hsmul : ∀ (z : ∀ ρ, M.H ρ) (i : D.what₂.Tau) (a : ℂ) (x : M.H i),
      (∏ ρ ∈ Finset.univ.erase τ, ⟪w ρ, Function.update z i (a • x) ρ⟫_ℂ) • Function.update z i (a • x) τ =
        a • ((∏ ρ ∈ Finset.univ.erase τ, ⟪w ρ, Function.update z i x ρ⟫_ℂ) • Function.update z i x τ) := by
    intro z i a x
    by_cases h : i = τ
    · subst h
      have e : ∀ b : M.H i, ∏ ρ ∈ Finset.univ.erase i, ⟪w ρ, Function.update z i b ρ⟫_ℂ =
          ∏ ρ ∈ Finset.univ.erase i, ⟪w ρ, z ρ⟫_ℂ := fun b =>
        Finset.prod_congr rfl fun ρ hρ => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hρ)]
      simp only [e, Function.update_self]
      exact smul_comm _ _ _
    · have hi : i ∈ Finset.univ.erase τ := Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩
      have e : ∀ b : M.H i, ∏ ρ ∈ Finset.univ.erase τ, ⟪w ρ, Function.update z i b ρ⟫_ℂ =
          ⟪w i, b⟫_ℂ * ∏ ρ ∈ (Finset.univ.erase τ).erase i, ⟪w ρ, z ρ⟫_ℂ := fun b => by
        rw [← Finset.mul_prod_erase _ _ hi, Function.update_self]
        congr 1
        exact Finset.prod_congr rfl fun ρ hρ => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hρ)]
      simp only [e, Function.update_of_ne (Ne.symm h), inner_smul_right, mul_assoc, mul_smul]
  let m : MultilinearMap ℂ (fun ρ => M.H ρ) (M.H τ) :=
    { toFun := fun z => (∏ ρ ∈ Finset.univ.erase τ, ⟪w ρ, z ρ⟫_ℂ) • z τ
      map_update_add' := fun z i x y => by convert hadd z i x y
      map_update_smul' := fun z i a x => by convert hsmul z i a x }
  refine ⟨PiTensorProduct.lift m, fun u x => ?_, fun g x => ?_⟩
  · have key : (innerₛₗ ℂ u).comp (PiTensorProduct.lift m) = ellT M (Function.update w τ u) := by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro z
      show ⟪u, PiTensorProduct.lift m (PiTensorProduct.tprod ℂ z)⟫_ℂ =
        ellT M (Function.update w τ u) (PiTensorProduct.tprod ℂ z)
      rw [PiTensorProduct.lift.tprod, ellT_left]
      show ⟪u, (∏ ρ ∈ Finset.univ.erase τ, ⟪w ρ, z ρ⟫_ℂ) • z τ⟫_ℂ = _
      rw [inner_smul_right, mul_comm]
    exact LinearMap.congr_fun key x
  · have key : (PiTensorProduct.lift m).comp (actT M τ g) =
        (M.rep τ g : M.H τ →ₗ[ℂ] M.H τ).comp (PiTensorProduct.lift m) := by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro z
      show PiTensorProduct.lift m (actT M τ g (PiTensorProduct.tprod ℂ z)) =
        M.rep τ g (PiTensorProduct.lift m (PiTensorProduct.tprod ℂ z))
      rw [actT_tprod, PiTensorProduct.lift.tprod, PiTensorProduct.lift.tprod]
      show (∏ ρ ∈ Finset.univ.erase τ, ⟪w ρ, Function.update z τ (M.rep τ g (z τ)) ρ⟫_ℂ) •
          Function.update z τ (M.rep τ g (z τ)) τ = M.rep τ g ((∏ ρ ∈ Finset.univ.erase τ, ⟪w ρ, z ρ⟫_ℂ) • z τ)
      rw [Function.update_self, map_smul]
      congr 1
      exact Finset.prod_congr rfl fun ρ hρ => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hρ)]
    exact LinearMap.congr_fun key x

omit [DecidableEq D.what₂.Tau] in
theorem conj_compact (M : DSModel V S) (τ : D.what₂.Tau) {k : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hk : k ∈ Formalism.REAL.Kset (M.ε τ)) : (M.fr τ)⁻¹ * k * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧
      M.rep τ ((M.fr τ)⁻¹ * k * M.fr τ) = M.σ τ k := by
  obtain ⟨hku, hkJ⟩ := hk
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
  have hFi : ∀ X : Matrix (Fin V.rank) (Fin V.rank) ℂ, M.fr τ * ((M.fr τ)⁻¹ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]
  have hFh : ∀ X : Matrix (Fin V.rank) (Fin V.rank) ℂ, ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one,
      Matrix.one_mul]
  have hkk : ∀ X : Matrix (Fin V.rank) (Fin V.rank) ℂ, kᴴ * (k * X) = X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose, (Matrix.mem_unitaryGroup_iff').mp hku, Matrix.one_mul]
  have hJk : ∀ X : Matrix (Fin V.rank) (Fin V.rank) ℂ,
      Formalism.REAL.Jm (M.ε τ) * (k * X) = k * (Formalism.REAL.Jm (M.ε τ) * X) := fun X => by
    rw [← Matrix.mul_assoc, ← hkJ, Matrix.mul_assoc]
  refine ⟨?_, ?_⟩
  · show _ * _ * _ = _
    rw [← M.fr_gram τ, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [hFh, hFi, hJk, hkk]
  · unfold DSModel.rep
    congr 1
    simp only [Matrix.mul_assoc]
    rw [hFi, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]

omit [DecidableEq D.what₂.Tau] in
theorem elt_unit {θ : InfFam D} (hθ : IsInfFam θ) (M : DSModel V S) (τ : D.what₂.Tau) : elt θ M τ 1 = 1 := by
  unfold elt
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
  rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ hd]
  exact GlobalTheory.PointAtPlaceHom.atTau_one hθ V τ

theorem one_compact {n : ℕ} (ε : Fin n → Bool) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.REAL.Kset ε := ⟨Submonoid.one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩

end GlobalTheory.Chain.RealLine.Semi

namespace GlobalTheory.Chain.RealLine.Semi

open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

theorem exists_semiW : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ) (τ : D.what₂.Tau) (aS aT : ℚ) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) [DecidableEq D.what₂.Tau], IsInfFam θ → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.CompactFock ψ θ M M' ω f τ aS aT → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.LieFock ψ θ M M' ω f τ aS aT → IsItW θ M M' ω (ptOf ψ θ M M' f) It → ∀ (v : M'.Vec) (w : ∀ ρ, M.H ρ), ∃ A : PolF D W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.H τ, SemiW M M' τ aS aT A ∧ ∀ φ y u, ⟪u, A φ y⟫_ℂ = ellT M (Function.update w τ u) (inclT M (It φ (PiTensorProduct.tprod ℂ (Function.update v τ y)))) := by
  intro D V W S S' M M' θ ψ ω f τ aS aT It _ hθ hC hL hI v w
  obtain ⟨c, hc, hcg⟩ := exists_ctr M τ w
  rcases hI with ⟨_, hbdd, hK, hX, hK', hX'⟩
  have hlin : ∀ (d : ℂ) (Q : PolF D W.rank V.rank), ptOf ψ θ M M' f (d • Q) = d • ptOf ψ θ M M' f Q :=
    fun d Q => by
      unfold ptOf
      exact LinearMap.map_smul _ d Q
  let T : M'.sm τ →ₗ[ℂ] SmT M' := (PiTensorProduct.tprod ℂ).toLinearMap v τ
  let A : PolF D W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.H τ := (It.compr₂ (c ∘ₗ inclT M)).compl₂ T
  have hA : ∀ φ y, A φ y = c (inclT M (It φ (PiTensorProduct.tprod ℂ (Function.update v τ y)))) :=
    fun _ _ => rfl
  refine ⟨A, ⟨?_, ?_, ?_, ?_, ?_⟩, fun φ y u => by rw [hA, hc]⟩
  · intro φ u
    obtain ⟨c0, hc0⟩ := hbdd φ (Function.update w τ u)
    refine ⟨c0 * ∏ ρ ∈ Finset.univ.erase τ, ‖(v ρ : M'.H ρ)‖, fun y => ?_⟩
    have hy := hc0 (Function.update v τ y)
    have e : ∏ ρ ∈ Finset.univ.erase τ, ‖((Function.update v τ y ρ : M'.sm ρ) : M'.H ρ)‖ =
        ∏ ρ ∈ Finset.univ.erase τ, ‖(v ρ : M'.H ρ)‖ :=
      Finset.prod_congr rfl fun ρ hρ => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hρ)]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), Function.update_self, e] at hy
    rw [hA, hc]
    refine hy.trans (le_of_eq ?_)
    ring
  · intro h hh φ
    obtain ⟨x, y, -, -, hcf⟩ := hC
    have hg := conj_compact M τ hh
    have h1 := hcf h hh 1 (one_compact _) φ
    rw [elt_unit hθ M' τ] at h1
    refine ⟨(GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.signBlockDeterminant (M.ε τ) true h ^ x true * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.signBlockDeterminant (M.ε τ) false h ^ x false *
        (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.signBlockDeterminant (M'.ε τ) true 1 ^ y true * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.signBlockDeterminant (M'.ε τ) false 1 ^ y false)) •
      GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.subst τ (M.ε τ) (M'.ε τ) (h.map (starRingEnd ℂ)) 1 φ,
      (MvPolynomial.totalDegree_smul_le _ _).trans
        (GlobalTheory.Chain.RealIt.SubstDeg.totalDegree_subst_le D _ _ τ _ _ _ _ φ), fun z => ?_⟩
    have hpt := (hlin _ _).trans h1.symm
    rw [hA, hA, hK τ _ hg.1 φ _ hpt, hcg, hg.2]
  · intro k hk φ
    obtain ⟨x, y, -, -, hcf⟩ := hC
    have hg := conj_compact M' τ hk
    have h1 := hcf 1 (one_compact _) k hk φ
    rw [elt_unit hθ M τ] at h1
    refine ⟨(GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.signBlockDeterminant (M.ε τ) true 1 ^ x true * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.signBlockDeterminant (M.ε τ) false 1 ^ x false *
        (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.signBlockDeterminant (M'.ε τ) true k ^ y true * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.signBlockDeterminant (M'.ε τ) false k ^ y false)) •
      GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.subst τ (M.ε τ) (M'.ε τ) ((1 : Matrix (Fin V.rank) (Fin V.rank) ℂ).map
        (starRingEnd ℂ)) k φ,
      (MvPolynomial.totalDegree_smul_le _ _).trans
        (GlobalTheory.Chain.RealIt.SubstDeg.totalDegree_subst_le D _ _ τ _ _ _ _ φ), fun y₁ y₂ hy => ?_⟩
    have hpt := (hlin _ _).trans h1.symm
    have hincl : inclT M' (PiTensorProduct.tprod ℂ (Function.update v τ y₂)) =
        actT M' τ ((M'.fr τ)⁻¹ * k * M'.fr τ) (inclT M' (PiTensorProduct.tprod ℂ (Function.update v τ y₁))) := by
      rw [inclT_update, inclT_update, actT_tprod, Function.update_idem, Function.update_self, hg.2, ← hy]
    rw [hA, hA, hK' τ _ hg.1 φ _ _ _ hpt hincl]
  · intro X hXm φ y u
    have e : srcOp M M' τ aT X φ = GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ (M.ε τ) (M'.ε τ)
        ((M.fr τ * X * (M.fr τ)⁻¹).map (starRingEnd ℂ)) φ - ((aT : ℂ) * X.trace) • φ := by
      simp [srcOp, sub_eq_add_neg]
    have hder : ∀ z, HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, 1) (ptOf ψ θ M M' f φ) z)
        (ptOf ψ θ M M' f (srcOp M M' τ aT X φ) z) 0 := fun z => by
      rw [e]
      exact hL.1 X hXm φ z
    have h2 := hX τ X hXm φ _ hder (PiTensorProduct.tprod ℂ (Function.update v τ y)) (Function.update w τ u)
    convert h2 using 1
    · funext t
      rw [hA, ← hcg, hc]
    · rw [hA, hc]
  · intro Y hY φ y y' hy
    have e : tgtOp M M' τ aS Y φ = GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (M.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) φ +
        ((aS : ℂ) * Y.trace) • φ := by
      simp [tgtOp]
    have hder : ∀ z, HasDerivAt (fun t : ℝ => ω (1, oneP θ W τ Y t) (ptOf ψ θ M M' f φ) z)
        (ptOf ψ θ M M' f (tgtOp M M' τ aS Y φ) z) 0 := fun z => by
      rw [e]
      exact hL.2 Y hY φ z
    have hD : DerT M' τ Y (PiTensorProduct.tprod ℂ (Function.update v τ y))
        (PiTensorProduct.tprod ℂ (Function.update v τ y')) := by
      unfold DerT
      intro w'
      rw [inclT_update, inclT_update, ellT_right]
      have e2 : ∀ t : ℝ, ellT M' w' (actT M' τ (NormedSpace.exp (t • Y))
          (PiTensorProduct.tprod ℂ (Function.update (fun ρ => (v ρ : M'.H ρ)) τ (y : M'.H τ)))) =
            ⟪w' τ, M'.rep τ (NormedSpace.exp (t • Y)) y⟫_ℂ * ∏ ρ ∈ Finset.univ.erase τ, ⟪w' ρ, (v ρ : M'.H ρ)⟫_ℂ :=
        fun t => by rw [actT_tprod, Function.update_idem, Function.update_self, ellT_right]
      simp only [e2]
      have h3 := ((((innerSL ℂ (w' τ)).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt (0 : ℝ) hy).mul_const
        (∏ ρ ∈ Finset.univ.erase τ, ⟪w' ρ, (v ρ : M'.H ρ)⟫_ℂ)
      simpa [Function.comp_def] using h3
    have h4 := hX' τ Y hY φ _ _ _ hder hD
    have h5 := congrArg (fun z => c (inclT M z)) h4
    simpa [hA] using h5

end GlobalTheory.Chain.RealLine.Semi

end
