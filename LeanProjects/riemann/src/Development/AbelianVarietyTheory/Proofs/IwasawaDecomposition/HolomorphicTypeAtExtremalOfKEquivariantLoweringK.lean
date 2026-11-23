import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqTopOfTranslates
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityMapExtremalVectorHolomorphicType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFrameBorelActsExtremalVectorByWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelUnitaryIrreducibleOrthonormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicTypeOfSmoothBorelKilled
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorsSubspaceStableSobolevFormDeriv

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.KMapHol

theorem exp_mem_kset {n : ℕ} (ε : Fin n → Bool) {X : Mt n} (hX : X ∈ lieH (Formalism.REAL.Jm ε))
    (hc : Commute X (Formalism.REAL.Jm ε)) (t : ℝ) : NormedSpace.exp (t • X) ∈ Formalism.REAL.Kset ε := by
  have hd : IsUnit (Formalism.REAL.Jm ε).det := isUnit_iff_ne_zero.2 (VKill.jm_det ε)
  have h0 : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := hX
  have h1 : X ∈ lieH (1 : Mt n) := by
    show Xᴴ * 1 + 1 * X = 0
    rw [← hc.eq, ← Matrix.add_mul] at h0
    have := congrArg (· * (Formalism.REAL.Jm ε)⁻¹) h0
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.zero_mul] at this
    simpa using this
  have h2 : (NormedSpace.exp (t • X))ᴴ * 1 * NormedSpace.exp (t • X) = 1 := GlobalTheory.SmVec.exp_mem_UH isUnit_one h1 t
  refine ⟨Matrix.mem_unitaryGroup_iff'.2 (by simpa [star_eq_conjTranspose] using h2), ?_⟩
  exact ((hc.smul_left t).exp_left).eq

theorem commute_conjH {n : ℕ} (ε : Fin n → Bool) {E : Mt n} (hc : Commute E (Formalism.REAL.Jm ε)) :
    Commute (conjH (Formalism.REAL.Jm ε) E) (Formalism.REAL.Jm ε) := by
  have hd : IsUnit (Formalism.REAL.Jm ε).det := isUnit_iff_ne_zero.2 (VKill.jm_det ε)
  have h1 : Formalism.REAL.Jm ε * Eᴴ = Eᴴ * Formalism.REAL.Jm ε := by
    have := congrArg conjTranspose hc.eq
    simpa only [conjTranspose_mul, (VKill.jm_herm ε).eq] using this
  have h2 : conjH (Formalism.REAL.Jm ε) E = -Eᴴ := by
    rw [conjH, Matrix.mul_assoc, ← h1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
  rw [h2]
  exact Commute.neg_left h1.symm

theorem commute_single {n : ℕ} (ε : Fin n → Bool) {a c : Fin n} (h : ε a = ε c) :
    Commute (Matrix.single a c (1 : ℂ)) (Formalism.REAL.Jm ε) := by
  show _ * _ = _ * _
  unfold Formalism.REAL.Jm
  ext i j
  rw [mul_diagonal, diagonal_mul, Matrix.single_apply]
  split_ifs with h1 h2 h3 <;> simp_all

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}

open Classical in

theorem exists_form (h1 : LowSm M) (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) (U : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.KMap M) (e : ∀ τ, lowT M τ)
    (τ : D.what₂.Tau) (x : GA D V) :
    ∃ ℓ : M.H τ →L[ℂ] ℂ, ∀ u : lowT M τ, ℓ ((u : M.sm τ) : M.H τ) = U (Function.update e τ u) x := by
  let P := lowKSub (M.ε τ) (M.lam τ) (M.σ τ)
  haveI : FiniteDimensional ℂ P := (h2 τ).1
  haveI : CompleteSpace P := FiniteDimensional.complete ℂ P
  let ℓ₀ : P →ₗ[ℂ] ℂ :=
    { toFun := fun y => U (Function.update e τ ⟨⟨y, h1 τ y.2⟩, y.2⟩) x
      map_add' := fun y z => congrFun (U.map_update_add e τ ⟨⟨y, h1 τ y.2⟩, y.2⟩ ⟨⟨z, h1 τ z.2⟩, z.2⟩) x
      map_smul' := fun a y => congrFun (U.map_update_smul e τ a ⟨⟨y, h1 τ y.2⟩, y.2⟩) x }
  refine ⟨(LinearMap.toContinuousLinearMap ℓ₀).comp P.orthogonalProjection, fun u => ?_⟩
  have : P.orthogonalProjection ((u : M.sm τ) : M.H τ) = ⟨_, u.2⟩ :=
    Submodule.orthogonalProjection_mem_subspace_eq_self (K := P) ⟨_, u.2⟩
  rw [ContinuousLinearMap.comp_apply, this]
  rfl

open Classical in

theorem rder_eq (θ : InfFam D) (h1 : LowSm M) (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) (U : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.KMap M)
    (hK : KEquiv θ M U) (e : ∀ τ, lowT M τ) (τ : D.what₂.Tau) (x : GA D V) (ℓ : M.H τ →L[ℂ] ℂ)
    (hℓ : ∀ u : lowT M τ, ℓ ((u : M.sm τ) : M.H τ) = U (Function.update e τ u) x)
    {X Y : Mt V.rank} (hY : Y ∈ lieH (Formalism.REAL.Jm (M.ε τ))) (hc : Commute Y (Formalism.REAL.Jm (M.ε τ)))
    (hXY : X = (M.fr τ)⁻¹ * Y * M.fr τ)
    (hd : HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) ((e τ : M.sm τ) : M.H τ))
      (dRep (M.rep τ) X ((e τ : M.sm τ) : M.H τ)) 0) :
    Rder θ V τ X (U e) x = ℓ (dRep (M.rep τ) X ((e τ : M.sm τ) : M.H τ)) := by
  have hP := M.fr_unit τ
  have hPd := (Matrix.isUnit_iff_isUnit_det _).1 hP
  have e1 : M.fr τ * X * (M.fr τ)⁻¹ = Y := by
    rw [hXY, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPd, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hPd, Matrix.mul_one]
  have key : ∀ t : ℝ, U e (x * oneP θ V τ X t) = ℓ (M.rep τ (NormedSpace.exp (t • X)) ((e τ : M.sm τ) : M.H τ)) := by
    intro t
    have hk : M.fr τ * NormedSpace.exp (t • X) * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) := by
      rw [VKill.conj_exp hP, e1]; exact exp_mem_kset _ hY hc t
    have hm := (h2 τ).2.1 _ hk _ (e τ).2
    have h := hK τ _ hk e ⟨⟨_, h1 τ hm⟩, hm⟩ rfl
    have e2 : (M.fr τ)⁻¹ * (M.fr τ * NormedSpace.exp (t • X) * (M.fr τ)⁻¹) * M.fr τ = NormedSpace.exp (t • X) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hPd, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hPd, Matrix.mul_one]
    rw [e2] at h
    exact ((hℓ ⟨⟨_, h1 τ hm⟩, hm⟩).trans (congrFun h x)).symm
  unfold Rder
  simp only [key]
  exact ((ℓ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd).deriv

theorem holAd_of_kEquiv : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ), IsInfFam θ → HolShape M → WtIs M w → LowSm M → GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M → ∀ U : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.KMap M, (∀ e, GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.IsSmoothFn V θ (U e)) → KEquiv θ M U → (∀ τ, ∀ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ, ∀ e, RderC θ V τ Z (U e) = 0) → ∀ e : ∀ τ, lowT M τ, IsExtVec M (fun τ => (e τ : M.sm τ)) → HolAd θ M w (U e) := by
  classical
  intro D θ V S M w hθ hS hw h1 h2 U hsm hK hp e hv g
  obtain ⟨L, -, hmul, -, -, hinv, hat, -, -, hG⟩ := GlobalTheory.RealLift.exists_real_lift D θ V hθ
  have hexp : ∀ τ, ∀ X ∈ lieH (gramAt D V τ), ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) :=
    fun τ X hX t => GlobalTheory.SmVec.exp_mem_UH ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hG τ).2)) hX t
  have hone : ∀ τ, ∀ X ∈ lieH (gramAt D V τ), ∀ t : ℝ,
      L (Pi.mulSingle τ (NormedSpace.exp (t • X))) = oneP θ V τ X t :=
    fun τ X hX t => (hat τ _ (hexp τ X hX t)).symm
  refine ⟨fun u => U e (g * L u), ?_, fun u hu => by simp only [hinv u hu]⟩
  refine GlobalTheory.HolDict.holFn_of_killed _ _ _ _ _ _ (fun τ => ((ModelRep.model_rep D V S M τ).2.2.2 hS).1) _ ?_ ?_
  · intro k τs Xs hX u hu
    have h := hsm e k τs Xs hX (g * L u)
    convert h using 2 with t
    obtain ⟨h1, h2⟩ := GlobalTheory.MultHol.lift_prod L hmul
      (List.ofFn fun i => (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : D.what₂.Tau → Mt V.rank)) (by
        intro x hx
        obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
        exact GlobalTheory.MultHol.mulSingle_mem_UG _ (hexp _ _ (hX i) _))
    show U e (g * L (u * _)) = _
    rw [hmul u hu _ h1, h2, List.map_ofFn, mul_assoc]
    exact congrArg (fun F : Fin k → GA D V => U e (g * (L u * (List.ofFn F).prod))) (funext fun i => hone _ _ (hX i) _)
  · intro τ a c hac u hu
    have hder : ∀ X ∈ lieH (gramAt D V τ), der τ X (fun u => U e (g * L u)) u = Rder θ V τ X (U e) (g * L u) := by
      intro X hX
      unfold der Rder
      congr 1
      funext t
      show U e (g * L (u * _)) = _
      rw [hmul u hu _ (GlobalTheory.MultHol.mulSingle_mem_UG _ (hexp _ _ hX _)), hone τ X hX, mul_assoc]
    obtain ⟨hc, hU, -, hx⟩ := ModelRep.model_rep D V S M τ
    obtain ⟨-, hx⟩ := hx hS
    obtain ⟨hs, hk⟩ := VKill.borel_extVec D θ V S M w _ hθ hS hw hv τ
    have hk := hk a c hac
    rw [hx a c] at hk ⊢
    set a' := arr (nNeg (M.ε τ)) a with ha'
    set c' := arr (nNeg (M.ε τ)) c with hc'
    obtain ⟨p1, p2⟩ := GlobalTheory.MultHol.parts_mem_lieH (hG τ).1 (hG τ).2 ((M.fr τ)⁻¹ * Matrix.single a' c' 1 * M.fr τ)
    by_cases hε : M.ε τ a' = M.ε τ c'
    · obtain ⟨ℓ, hℓ⟩ := exists_form h1 h2 U e τ (g * L u)
      obtain ⟨q1, q2⟩ := GlobalTheory.MultHol.parts_mem_lieH (VKill.jm_herm (M.ε τ)) (VKill.jm_det (M.ε τ)) (Matrix.single a' c' 1)
      have c1 := commute_single (M.ε τ) hε
      have c2 := commute_conjH (M.ε τ) c1
      have hcj : conjH (gramAt D V τ) ((M.fr τ)⁻¹ * Matrix.single a' c' 1 * M.fr τ) =
          (M.fr τ)⁻¹ * conjH (Formalism.REAL.Jm (M.ε τ)) (Matrix.single a' c' 1) * M.fr τ := by
        rw [← M.fr_gram τ]; exact VKill.conjH_conj (M.fr_unit τ) _ _
      have hD := ((GlobalTheory.UnitarySmVec.smoothVec_basic _ _ _ _ (hG τ).1 (hG τ).2 hU).2 _ hs).2.1
      have r1 := rder_eq θ h1 h2 U hK e τ (g * L u) ℓ hℓ q1 ((c1.add_left c2).smul_left _)
        (by rw [hcj, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul]) (hD _ p1).2
      have r2 := rder_eq θ h1 h2 U hK e τ (g * L u) ℓ hℓ q2 ((c1.sub_left c2).smul_left _)
        (by rw [hcj, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]) (hD _ p2).2
      have hk' := congrArg ℓ hk
      unfold dRepC at hk'
      rw [map_add, map_smul, smul_eq_mul] at hk'
      unfold derC
      rw [hder _ p1, hder _ p2, r1, r2, hk']
      split_ifs
      · rw [map_smul, hℓ (e τ), Function.update_eq_self, smul_eq_mul]
      · rw [map_zero]
    · obtain ⟨-, p, hpn, hεp⟩ := hS τ
      have hq := nNeg_shape hpn hεp
      have hsg : ∀ b : Fin V.rank, M.ε τ (arr (nNeg (M.ε τ)) b) = decide (¬ (b : ℕ) < V.rank - p) := by
        intro b
        have := b.2
        rw [hεp, hq]
        unfold arr
        split_ifs with hb
        · simp only [hb, not_true_eq_false, decide_false, decide_eq_false_iff_not]; omega
        · simp only [hb, not_false_eq_true, decide_true, decide_eq_true_eq]; omega
      have hac' : (a : ℕ) ≤ c := hac
      have hne : a ≠ c := fun h => hε (by rw [ha', hc', h])
      rw [ha', hc', hsg, hsg, decide_eq_decide] at hε
      have ha : M.ε τ a' = false := by rw [ha', hsg]; simp only [decide_eq_false_iff_not]; omega
      have hb : M.ε τ c' = true := by rw [hc', hsg]; simp only [decide_eq_true_eq]; omega
      have h0 := congrFun (hp τ _ (GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.single_mem_pMinus M τ ha hb) e) (g * L u)
      rw [if_neg hne]
      unfold derC
      rw [hder _ p1, hder _ p2]
      exact h0

end GlobalTheory.KMapHol
