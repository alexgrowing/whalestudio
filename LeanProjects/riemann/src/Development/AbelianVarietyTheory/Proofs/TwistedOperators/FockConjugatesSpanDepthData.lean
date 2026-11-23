import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameFunctionalKillsFockVacuumRealTranslatesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameFunctionalVacuumIrreducibilityStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergCommutantPermutesFirstRowCosetVectorsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaHeisenbergConjugationNegHermitianSpace
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.SymplOHSmulRight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLocalPlaceLocalModelsLinearSubspace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionNegPairPureTensorFock
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.ConjFock

variable {D : D7}

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger (cj)

theorem cj_cj {X : Type} (f : X → ℂ) : cj id (cj id f) = f := by
  funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]

theorem cj_eq_star {X : Type} (f : X → ℂ) : cj id f = star f := by
  funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, Complex.star_def]

theorem cj_add {X : Type} (f g : X → ℂ) : cj id (f + g) = cj id f + cj id g := by
  funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]

theorem cj_smul {X : Type} (c : ℂ) (f : X → ℂ) : cj id (c • f) = starRingEnd ℂ c • cj id f := by
  funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]

def conjFun {S T : HSp D} (ℓ : (WO S T → ℂ) → ℂ) : (WO (negSp S) T → ℂ) → ℂ :=
  fun f => starRingEnd ℂ (ℓ (cj id f : WO S T → ℂ))

theorem theta_cj {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} (f : WO (negSp S) T → ℂ)
    (hf : IsThetaFunO ψ (negSp S) T f) : IsThetaFunO ψ S T (cj id f : WO S T → ℂ) := by
  have h := (((GlobalTheory.CjNeg.theta_heis_neg D ψ hψ S T).1 (cj id f : WO S T → ℂ)).2).1
  rw [cj_cj] at h
  exact h hf

theorem cj_heisO {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} (w : WO S T)
    (f : WO (negSp S) T → ℂ) : (cj id (heisO ψ (negSp S) T w f) : WO S T → ℂ) = heisO ψ S T w (cj id f) := by
  have h := ((GlobalTheory.CjNeg.theta_heis_neg D ψ hψ S T).2 w (cj id f : WO S T → ℂ)).2
  rw [cj_cj] at h
  rw [h, cj_cj]

theorem tame_conjFun {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {ℓ : (WO S T → ℂ) → ℂ}
    (h : Tame ψ S T ℓ) : Tame ψ (negSp S) T (conjFun ℓ) where
  add f f' hf hf' := by
    simp only [conjFun]
    rw [cj_add, h.add _ _ (theta_cj hψ f hf) (theta_cj hψ f' hf'), map_add]
  smul c f hf := by
    simp only [conjFun]
    rw [cj_smul, h.smul _ _ (theta_cj hψ f hf), map_mul, Complex.conj_conj]
  cont f hf := by
    simp only [conjFun, cj_heisO hψ]
    exact Complex.continuous_conj.comp (h.cont _ (theta_cj hψ f hf))
  bdd f hf := by
    obtain ⟨C, hC⟩ := h.bdd _ (theta_cj hψ f hf)
    exact ⟨C, fun w => by simp only [conjFun, cj_heisO hψ, Complex.norm_conj]; exact hC w⟩
  sup f hf m _ α hα hth := by
    have e1 : (cj id (fun x => ∫ w, α w * heisO ψ (negSp S) T w f x ∂m) : WO S T → ℂ) =
        fun x => ∫ w, starRingEnd ℂ (α w) * heisO ψ S T w (cj id f) x ∂m := by
      funext x
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id]
      rw [← integral_conj]
      congr 1
      funext w
      rw [map_mul]
      congr 1
      have := congrFun (cj_heisO (S := S) hψ w f) x
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id] at this
      exact this
    have hint : Integrable (fun w => starRingEnd ℂ (α w)) m :=
      (Complex.conjCLE.toContinuousLinearMap).integrable_comp hα
    have hth' : IsThetaFunO ψ S T (fun x => ∫ w, starRingEnd ℂ (α w) * heisO ψ S T w (cj id f) x ∂m) := by
      rw [← e1]; exact theta_cj hψ _ hth
    simp only [conjFun]
    rw [e1, h.sup (cj id f) (theta_cj hψ f hf) m (fun w => starRingEnd ℂ (α w)) hint hth', ← integral_conj]
    congr 1
    funext w
    rw [map_mul, Complex.conj_conj, cj_heisO hψ]

theorem det_Jm_unit {n : ℕ} (ε : Fin n → Bool) : IsUnit (Formalism.REAL.Jm ε).det := by
  unfold Formalism.REAL.Jm
  rw [det_diagonal, isUnit_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.2 fun a _ => by split_ifs <;> norm_num

theorem unit_of_gram {n : ℕ} {G b : Matrix (Fin n) (Fin n) ℂ} {ε : Fin n → Bool} (h : bᴴ * G * b = Formalism.REAL.Jm ε) :
    IsUnit b.det := by
  have hJ := det_Jm_unit ε
  rw [← h, det_mul] at hJ
  exact isUnit_of_mul_isUnit_right hJ

theorem inv_gram {n : ℕ} {G b : Matrix (Fin n) (Fin n) ℂ} {ε : Fin n → Bool} (h : bᴴ * G * b = Formalism.REAL.Jm ε) :
    (b⁻¹)ᴴ * Formalism.REAL.Jm ε * b⁻¹ = G := by
  have hb := unit_of_gram h
  have h1 : (bᴴ)⁻¹ * bᴴ = 1 := nonsing_inv_mul _ (by rw [det_conjTranspose]; exact hb.star)
  have h2 : b * b⁻¹ = 1 := mul_nonsing_inv _ hb
  rw [← h, conjTranspose_nonsing_inv]
  calc (bᴴ)⁻¹ * (bᴴ * G * b) * b⁻¹ = ((bᴴ)⁻¹ * bᴴ) * G * (b * b⁻¹) := by simp only [Matrix.mul_assoc]
    _ = G := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem Jm_not {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm (fun a => !ε a) = -Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [diagonal_neg]
  congr 1
  funext a
  cases h : ε a <;> simp [h]

theorem frame_pos (V : HSp D) (c b : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (h : ∀ τ, ∃ ε : Fin V.rank → Bool, (b τ)ᴴ * gramAt D V τ * b τ = Formalism.REAL.Jm ε ∧ c τ * b τ = b τ * Formalism.REAL.Jm ε) :
    ∃ A : GlobalTheory.ChainFr.Fr V, A.cart = c ∧ A.onb = b := by
  choose ε hε using h
  refine ⟨⟨ε, fun τ => (b τ)⁻¹, fun τ => isUnit_nonsing_inv_iff.2 ((isUnit_iff_isUnit_det _).2 (unit_of_gram (hε τ).1)),
    fun τ => inv_gram (hε τ).1⟩, ?_, ?_⟩
  · funext τ
    simp only [GlobalTheory.ChainFr.Fr.cart]
    rw [nonsing_inv_nonsing_inv _ (unit_of_gram (hε τ).1), ← (hε τ).2, Matrix.mul_assoc,
      mul_nonsing_inv _ (unit_of_gram (hε τ).1), Matrix.mul_one]
  · funext τ
    simp only [GlobalTheory.ChainFr.Fr.onb]
    rw [nonsing_inv_nonsing_inv _ (unit_of_gram (hε τ).1)]

theorem frame_neg (V : HSp D) (c b : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (h : ∀ τ, ∃ ε : Fin V.rank → Bool, (b τ)ᴴ * gramAt D V τ * b τ = Formalism.REAL.Jm ε ∧ c τ * b τ = b τ * Formalism.REAL.Jm ε) :
    ∃ A : GlobalTheory.ChainFr.Fr (negSp V), A.cart = (fun τ => -c τ) ∧ A.onb = b := by
  choose ε hε using h
  refine ⟨⟨fun τ a => !ε τ a, fun τ => (b τ)⁻¹,
    fun τ => isUnit_nonsing_inv_iff.2 ((isUnit_iff_isUnit_det _).2 (unit_of_gram (hε τ).1)), fun τ => ?_⟩, ?_, ?_⟩
  · rw [GlobalTheory.FockRealNeg.gramAt_negSp, Jm_not, Matrix.mul_neg, Matrix.neg_mul, inv_gram (hε τ).1]
  · funext τ
    simp only [GlobalTheory.ChainFr.Fr.cart]
    rw [nonsing_inv_nonsing_inv _ (unit_of_gram (hε τ).1), Jm_not, Matrix.mul_neg, Matrix.neg_mul, ← (hε τ).2,
      Matrix.mul_assoc, mul_nonsing_inv _ (unit_of_gram (hε τ).1), Matrix.mul_one]
  · funext τ
    simp only [GlobalTheory.ChainFr.Fr.onb]
    rw [nonsing_inv_nonsing_inv _ (unit_of_gram (hε τ).1)]

theorem symplO_smul_left' {S T : HSp D} (c : AF D.host.F) (x y : WO S T) :
    symplO S T (c • x) y = c * symplO S T x y := by
  simp only [symplO, Eqv.hO_smul_left, mul_smul_comm, LinearMap.map_smul, smul_eq_mul]

theorem symplO_smul_right' {S T : HSp D} (c : AF D.host.F) (x y : WO S T) :
    symplO S T x (c • y) = c * symplO S T x y := by
  simp only [symplO, Eqv.hO_smul_right, mul_smul_comm, LinearMap.map_smul, smul_eq_mul]

theorem eInf_mul_self : Eqv.eInf D * Eqv.eInf D = Eqv.eInf D :=
  Prod.ext (show (1 : Ainf D.host.F) * 1 = 1 from mul_one _) (show (0 : Af D.host.F) * 0 = 0 from mul_zero _)

theorem eFin_mul_self : Eqv.eFin D * Eqv.eFin D = Eqv.eFin D :=
  Prod.ext (show (0 : Ainf D.host.F) * 0 = 0 from mul_zero _) (show (1 : Af D.host.F) * 1 = 1 from mul_one _)

theorem infPart_latO' {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {u : WO S T}
    (hu : u ∈ latO S T LS LT fun _ => True) : u.map (infPart D) = 0 := by
  ext i j
  rw [Matrix.map_apply, Matrix.zero_apply]
  unfold latO at hu
  refine AddSubgroup.closure_induction (p := fun u _ => infPart D (u i j) = 0) ?_ ?_ ?_ ?_ hu
  · rintro w ⟨α, -, -, a, -, s, -, t, -, rfl⟩
    rw [Matrix.of_apply]
    exact (show infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) =
      (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) from rfl).trans (TensorProduct.zero_tmul _ _)
  · simp
  · intro x y _ _ hx hy; rw [Matrix.add_apply, RingHom.map_add, hx, hy, add_zero]
  · intro x _ hx; rw [Matrix.neg_apply, RingHom.map_neg, hx, neg_zero]

section
variable {T : Type} {L : LevCh D T} {sc : Consts}

theorem depLat_fin {G : GridData L sc} (p : Pair T) {u : WO (G.pS p) (G.pT p)} (hu : u ∈ depLat G p) :
    u.map (infPart D) = 0 := infPart_latO' hu.1

theorem latRow_fin {G : GridData L sc} (i : ℕ) : ∀ u ∈ latRow G i, Eqv.eFin D • u = u := fun u hu =>
  (Eqv.wo_fin_iff u).1 (depLat_fin (.chi i 0) hu)
end

end GlobalTheory.ConjFock

namespace GlobalTheory.ConjDataTotal

open GlobalTheory.ConjFock

theorem fockTot : FockTot := by
  intro D hoff T L μ0 hL sc G W M hM i ℓ hℓ hkill f hf
  have hψ := W.ψ_std
  have hi : i.1 < D.R.m := i.2
  have cos := GlobalTheory.T.heisenbergCommutant_permutes_firstRowCosetVectors D hoff T L μ0 hL sc G W M hM i.1 hi
  obtain ⟨A, hAc, hAo⟩ := frame_neg (G.V (.grid (i.1 + 1) 0)) (W.cart (.grid (i.1 + 1) 0)) (W.onb (.grid (i.1 + 1) 0))
    (W.onb_is _ ⟨by omega, Nat.zero_le _⟩)
  obtain ⟨B, hBc, hBo⟩ := frame_pos (G.V (.grid i.1 0)) (W.cart (.grid i.1 0)) (W.onb (.grid i.1 0))
    (W.onb_is _ ⟨by omega, Nat.zero_le _⟩)
  have hfock : ∀ g P, GlobalTheory.ChainFr.ptF W.ψ W.θ A B g P = W.fock (.chi i.1 0) g P := by
    intro g P
    simp only [GlobalTheory.ChainFr.ptF, hAc, hBc, hAo, hBo]
    rfl
  have hreal : ∀ κ (w : WO (G.V (.grid (i.1 + 1) 0)) (G.V (.grid i.1 0))), w.map (finPart D) = 0 →
      ℓ (heisO W.ψ _ _ w (star (W.cosVec i.1 κ))) = 0 := by
    intro κ w hw
    obtain ⟨-, hvac, hVac, -⟩ := cos κ
    have hth : IsThetaFunO W.ψ (negSp (G.V (.grid (i.1 + 1) 0))) (G.V (.grid i.1 0)) (W.cosVec i.1 κ) := by
      have h := (((GlobalTheory.CjNeg.theta_heis_neg D W.ψ hψ (G.V (.grid (i.1 + 1) 0)) (G.V (.grid i.1 0))).1
        (star (W.cosVec i.1 κ) : WO (G.V (.grid (i.1 + 1) 0)) (G.V (.grid i.1 0)) → ℂ)).2).2 hVac.1
      rwa [cj_eq_star, star_star] at h
    have hv : GlobalTheory.ChainFr.IsVacF W.ψ W.θ A B (W.cosVec i.1 κ) := ⟨hth, fun τ => by rw [hAc, hBc]; exact hvac τ⟩
    have hk : ∀ P, conjFun ℓ (GlobalTheory.ChainFr.ptF W.ψ W.θ A B (W.cosVec i.1 κ) P) = 0 := by
      intro P
      rw [hfock]
      simp only [conjFun]
      rw [cj_eq_star, hkill κ P, map_zero]
    have h := GlobalTheory.T.tameFunctional_kills_fockVacuum_realTranslates D W.ψ W.θ hψ W.θ_is _ _ A B (conjFun ℓ) (tame_conjFun hψ hℓ) _ hv hk w hw
    simp only [conjFun] at h
    rw [cj_heisO (S := G.V (.grid (i.1 + 1) 0)) hψ, map_eq_zero, cj_eq_star] at h
    exact h
  obtain ⟨hne₀, -, hVac₀, hspan₀⟩ := cos default
  refine GlobalTheory.T.tame_functional_vacuum_irreducibility D W.ψ hψ _ _ (latRow G i.1) ℓ hℓ (star (W.cosVec i.1 default)) hVac₀ ?_ ?_ f hf
  · intro h0
    apply hne₀
    have := congrArg star h0
    rwa [star_star, star_zero] at this
  · intro w hw
    set wr : WO (G.V (.grid (i.1 + 1) 0)) (G.V (.grid i.1 0)) := Eqv.eInf D • w with hwr_def
    set wf : WO (G.V (.grid (i.1 + 1) 0)) (G.V (.grid i.1 0)) := Eqv.eFin D • w with hwf_def
    have hsum : wr + wf = w := by rw [hwr_def, hwf_def, ← add_smul, Eqv.eInf_add_eFin, one_smul]
    have hwr : Eqv.eInf D • wr = wr := by rw [hwr_def, smul_smul, eInf_mul_self]
    have hwf : Eqv.eFin D • wf = wf := by rw [hwf_def, smul_smul, eFin_mul_self]
    have hwr' : wr.map (finPart D) = 0 := (Eqv.wo_real_iff wr).2 hwr
    have hwf' : wf.map (infPart D) = 0 := (Eqv.wo_fin_iff wf).2 hwf
    have hsy : ∀ y, Eqv.eFin D • y = y → symplO _ _ wf y = symplO _ _ w y := by
      intro y hy
      rw [hwf_def, symplO_smul_left', ← symplO_smul_right', hy]
    have hfinΓ : ∀ u ∈ latRow G i.1, Eqv.eFin D • u = u := latRow_fin i.1
    have hAnn : wf ∈ Ann W.ψ _ _ (latRow G i.1) := by
      simp only [Ann, Set.mem_setOf_eq] at hw ⊢
      refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
      · rw [hsy _ (by rw [smul_comm, hfinΓ u hu])]; exact hw.1 u hu
      · rw [hsy _ (hfinΓ u hu)]; exact hw.2 e he u hu hh
    have hdec : heisO W.ψ _ _ w (star (W.cosVec i.1 default)) =
        heisO W.ψ _ _ wr (heisO W.ψ _ _ wf (star (W.cosVec i.1 default))) := by
      rw [GlobalTheory.FinTranslate.heisO_heisO, Eqv.symplOH_real_fin wr wf hwr hwf, AddChar.map_zero_eq_one, one_smul, hsum]
    have hmem := hspan₀ wf hAnn hwf'
    rw [hdec]
    have key : ∀ g ∈ Submodule.span ℂ (Set.range fun κ' =>
        (star (W.cosVec i.1 κ') : WO (G.V (.grid (i.1 + 1) 0)) (G.V (.grid i.1 0)) → ℂ)),
        IsThetaFunO W.ψ _ _ g ∧ ℓ (heisO W.ψ _ _ wr g) = 0 := by
      intro g hg
      induction hg using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨κ, rfl⟩ := hx
        exact ⟨(cos κ).2.2.1.1, hreal κ wr hwr'⟩
      | zero =>
        refine ⟨GlobalTheory.LocMod.LinSpace.isThetaFunO_zero _ _ _, ?_⟩
        rw [GlobalTheory.LocMod.LinSpace.heisO_zero']
        have h0 := hℓ.smul 0 0 (GlobalTheory.LocMod.LinSpace.isThetaFunO_zero _ _ _)
        rwa [zero_smul, zero_mul] at h0
      | add x y _ _ hx hy =>
        refine ⟨GlobalTheory.LocMod.LinSpace.isThetaFunO_add hx.1 hy.1, ?_⟩
        rw [GlobalTheory.LocMod.LinSpace.heisO_add', hℓ.add _ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hx.1 wr)
          (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hy.1 wr), hx.2, hy.2, add_zero]
      | smul a x _ hx =>
        refine ⟨GlobalTheory.LocMod.LinSpace.isThetaFunO_smul a hx.1, ?_⟩
        rw [GlobalTheory.LocMod.LinSpace.heisO_smul', hℓ.smul _ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hx.1 wr), hx.2,
          mul_zero]
    exact (key _ hmem).2

end GlobalTheory.ConjDataTotal

end
