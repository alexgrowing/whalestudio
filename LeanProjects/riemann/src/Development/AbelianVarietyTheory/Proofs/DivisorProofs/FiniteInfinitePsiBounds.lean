import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfConjMemOfPow
import Formalism.LocalToGlobal.Columns.CoefColLemmas

namespace TestFunctionNorms
section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.CoefModel
open Formalism.UG
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.TestVal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lat

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}

theorem del_le_nab (emb : ι → E →+* K) (lam : ι → DomWeight n) (M : Submodule (𝓞 E) (Fin n → E)) {x : VV K lam}
    (hx : x ∈ delAtr emb lam M) : x ∈ nabAtr emb lam M :=
  transLat_mono lam (delStd_le_nabStd K lam) _ hx

theorem nabAtr_map (emb : ι → E →+* K) (lam : ι → DomWeight n)
    (γ : GL (Fin n) E) (M : Submodule (𝓞 E) (Fin n → E)) (x : VV K lam) (hx : x ∈ nabAtr emb lam M) :
    rhoVr emb lam γ x ∈
      nabAtr emb lam (M.map ((Matrix.mulVecLin (γ : Matrix (Fin n) (Fin n) E)).restrictScalars (𝓞 E))) := by
  unfold nabAtr
  simp_rw [tauLatG E K ι n emb, Formalism.L2.Col.dualFr_gLat]
  exact (Formalism.L2.Col.nabK_gLat lam _ (invTrK (embGL emb γ))).ge ⟨x, hx, rfl⟩

end Lat

section Cast

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

def castVV {lam lam' : ι → DomWeight n} (e : lam' = lam) (v : VV K lam) : VV K lam' := ⟨v.1, by rw [e]; exact v.2⟩

end Cast

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem delta_cases (rp : ClassReps G) (c : G.ClPlus) (v : WtSp G) (g : GLf G) :
    rp.delta c v g = 0 ∨ ∃ (γ : UR D.sp.cm (Xp G).gram) (k : GLf G), k ∈ G.Kplus ∧ g = ratIn G γ * (rp.x c : GLf G) * k ∧
      rp.delta c v g = rhoW G γ v := by
  by_cases h : ∃ (γ : UR D.sp.cm (Xp G).gram), ∃ k ∈ G.Kplus, g = ratIn G γ * (rp.x c : GLf G) * k
  · obtain ⟨γ, k, hk, rfl⟩ := h
    refine Or.inr ⟨γ, k, hk, rfl, ?_⟩
    unfold ClassReps.delta
    rw [deltaForm_right _ _ _ _ _ _ hk, deltaForm_left, deltaForm_self _ _ _ _ _ (ClassReps.neat rp c)]
  · exact Or.inl (deltaForm_eq_zero _ _ _ _ _ _ fun γ u hu he => h ⟨γ, u, hu, he⟩)

theorem comap_eq_map {E : Type} [Field E] [NumberField E] {n : ℕ} (fr γ : GL (Fin n) E) (A B : Submodule (𝓞 E) (Fin n → E))
    (h : ∀ z, γ.1 *ᵥ z ∈ B ↔ z ∈ A) :
    B.comap (fr.1.mulVecLin.restrictScalars (𝓞 E)) = A.map ((fr⁻¹ * γ).1.mulVecLin.restrictScalars (𝓞 E)) := by
  ext y
  constructor
  · intro hy
    have hy' : fr.1 *ᵥ y ∈ B := hy
    refine ⟨(γ⁻¹).1 *ᵥ (fr.1 *ᵥ y), (h _).1 ?_, ?_⟩
    · rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      exact hy'
    · show (fr⁻¹ * γ).1 *ᵥ ((γ⁻¹).1 *ᵥ (fr.1 *ᵥ y)) = y
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
      simp
  · rintro ⟨z, hz, rfl⟩
    show fr.1 *ᵥ ((fr⁻¹ * γ).1 *ᵥ z) ∈ B
    have e : fr.1 *ᵥ ((fr⁻¹ * γ).1 *ᵥ z) = γ.1 *ᵥ z := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul]
      simp
    rw [e]
    exact (h z).2 hz

theorem latAt_eq {W : G.Weil} (S : GridChoice W Set.univ) (rp : ClassReps G) (c : G.ClPlus) (x : FinPt G (.top 0))
    (γ : UR D.sp.cm (Xp G).gram) {k : GLf G} (hk : k ∈ G.Kplus) (hx : finG (Xp G) x = ratIn G γ * (rp.x c : GLf G) * k) :
    GlobalTheory.SumSize.latAt S (.top 0) x = (rp.lat c).map
      (((S.N.fr (.top 0))⁻¹ * γ.1).1.mulVecLin.restrictScalars (𝓞 D.host.E)) := by
  have h0 : latOf G (finG (Xp G) x) = latOf G (ratIn G γ * (rp.x c : GLf G)) := by
    rw [hx]
    exact TestLatModel.latOf_mul _ hk
  refine (congrArg (Submodule.comap _) h0).trans (comap_eq_map _ _ _ _ fun z => ?_)
  exact TestLatModel.mem_latOf_rat γ _ z

theorem rhoVr_mapVV {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (h : GL (Fin n) D.host.E) (v : VV D.what₂.LL lam) :
    rhoVr (tauE D) lam h (mapVV D.what₂.embLL lam v) = mapVV D.what₂.embLL lam (rhoVr (labLL D) lam h v) := by
  have hlab : ∀ τ x, D.what₂.embLL (labLL D τ x) = tauE D τ x := fun τ x =>
    DFunLike.congr_fun (GlobalTheory.ThetaFiresProbe.labE_fixed τ) x
  have e : (fun τ => Formalism.UG.bc D.what₂.embLL (invTrK (embGL (labLL D) h) τ)) = invTrK (embGL (tauE D) h) := by
    funext τ
    apply Units.ext
    rw [bc_coe, invTrK_coe, invTrK_coe, embGL_inv, embGL_inv, embGL_coe, embGL_coe]
    ext a b
    exact hlab _ _
  show rhoK lam _ _ = mapVV _ _ (rhoK lam (invTrK (embGL (labLL D) h)) _)
  rw [mapVV_rhoK, e]
  rfl

theorem gram_transport (V : HSp D) (σ : D.what₂.LL →+* ℂ) (h : GL (Fin V.rank) D.host.E)
    (hh : cT (D.sp.cm.sig : D.host.E →+* D.host.E) (h⁻¹).1 * V.gram * (h⁻¹).1 = 1) (τ : D.what₂.Tau) :
    (((bc σ (invTrK (embGL (labLL D) h) τ) : GL _ ℂ) : Matrix _ _ ℂ))ᴴ * 1 * ((bc σ (invTrK (embGL (labLL D) h) τ) : GL _ ℂ) : Matrix _ _ ℂ) =
      (gramKd (labLL D) V.gram τ).map σ := by
  set φ : D.host.E →+* ℂ := σ.comp (labLL D τ) with hφ
  set A : Matrix (Fin V.rank) (Fin V.rank) ℂ := (h⁻¹).1.map φ with hA
  have hc : ∀ x, φ ((D.sp.cm.sig : D.host.E →+* D.host.E) x) = starRingEnd ℂ (φ x) := fun x => D.sp.cm.cmUnram.2.1 φ x
  have h1 : (h⁻¹).1 * (cT (D.sp.cm.sig : D.host.E →+* D.host.E) (h⁻¹).1 * V.gram) = 1 := by
    exact mul_eq_one_comm.1 hh
  have h2 : A * Aᴴ * V.gram.map φ = 1 := by
    have e : Aᴴ = (cT (D.sp.cm.sig : D.host.E →+* D.host.E) (h⁻¹).1).map φ := by
      ext i j
      simp only [hA, cT, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.transpose_apply]
      exact (hc _).symm
    have := congrArg (fun M => M.map φ) h1
    simp only [Matrix.map_mul] at this
    rw [e, Matrix.mul_assoc, this, Matrix.map_one _ (map_zero _) (map_one _)]
  have hu : IsUnit (V.gram.map (labLL D τ)).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact ((_root_.map_ne_zero _).2 (GlobalTheory.UnitaryGlue.gram_det_ne_zero V)).isUnit
  have h3 : (V.gram.map (labLL D τ))⁻¹.map σ = A * Aᴴ := by
    have e1 : (V.gram.map (labLL D τ)).map σ = V.gram.map φ := by
      ext i j
      rfl
    have e2 : (V.gram.map (labLL D τ))⁻¹.map σ * V.gram.map φ = 1 := by
      rw [← e1, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
    exact (Matrix.inv_eq_left_inv e2).symm.trans (Matrix.inv_eq_left_inv h2)
  have h4 : ((bc σ (invTrK (embGL (labLL D) h) τ) : GL _ ℂ) : Matrix _ _ ℂ) = Aᵀ := by
    rw [bc_coe, invTrK_coe, embGL_inv, embGL_coe]
    ext a b
    rfl
  rw [h4, gramKd, Matrix.transpose_map, h3, Matrix.mul_one, Matrix.transpose_mul]
  rfl

theorem nrm_transport (V : HSp D) (lam : D.what₂.Tau → DomWeight V.rank) (σ : D.what₂.LL →+* ℂ) (h : GL (Fin V.rank) D.host.E)
    (hh : cT (D.sp.cm.sig : D.host.E →+* D.host.E) (h⁻¹).1 * V.gram * (h⁻¹).1 = 1) (u : VV D.what₂.LL lam) :
    nrm lam (fun _ => 1) (mapVV σ lam (rhoVr (labLL D) lam h u)) =
      nrm lam (fun τ => (gramKd (labLL D) V.gram τ).map σ) (mapVV σ lam u) := by
  have e : mapVV σ lam (rhoVr (labLL D) lam h u) =
      rhoK lam (fun τ => bc σ (invTrK (embGL (labLL D) h) τ)) (mapVV σ lam u) :=
    mapVV_rhoK σ lam _ u
  unfold nrm
  rw [e, pairK_apply, pairK_apply, rhoK_coe, pairTransport ℂ _ _ lam _ _ _]
  simp only [gram_transport V σ h hh]

theorem castVV_rhoVr_mul {n : ℕ} {lam lam' : D.what₂.Tau → DomWeight n} (e : lam' = lam) (fr γ : GL (Fin n) D.host.E)
    (v : VV D.what₂.LL lam) :
    rhoVr (labLL D) lam' fr (castVV e (rhoVr (labLL D) lam γ v)) = castVV e (rhoVr (labLL D) lam (fr * γ) v) := by
  subst e
  rw [map_mul]
  rfl

theorem castVV_mem {n : ℕ} {lam lam' : D.what₂.Tau → DomWeight n} (e : lam' = lam) {M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {v : VV D.what₂.LL lam} (hv : v ∈ nabAtr (labLL D) lam M) : castVV e v ∈ nabAtr (labLL D) lam' M := by
  subst e
  exact hv

theorem nrm_castVV {n : ℕ} {lam lam' : D.what₂.Tau → DomWeight n} (e : lam' = lam) (H : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ)
    (σ : D.what₂.LL →+* ℂ) (v : VV D.what₂.LL lam) : nrm lam' H (mapVV σ lam' (castVV e v)) = nrm lam H (mapVV σ lam v) := by
  subst e
  rfl

theorem mapVV_castVV {K : Type} [Field K] {n : ℕ} {lam lam' : D.what₂.Tau → DomWeight n} (e : lam' = lam) (φ : K →+* ℂ) (v : VV K lam) :
    mapVV φ lam' (castVV e v) = ⟨(mapVV φ lam v).1, by rw [e]; exact Subtype.prop _⟩ := by
  subst e
  rfl

theorem castVV_zero {K : Type} [Field K] {n : ℕ} {lam lam' : D.what₂.Tau → DomWeight n} (e : lam' = lam) :
    castVV e (0 : VV K lam) = 0 := by
  subst e
  rfl

theorem nrm_zero {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (H : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) :
    nrm lam H 0 = 0 := by
  simp [nrm]

theorem topVal_eq {W : G.Weil} (S : GridChoice W Set.univ) (Ψ : GLf G → WtSp G) (x : FinPt G (.top 0)) :
    topVal S Ψ x = mapVV D.what₂.embLL (wt G (.top 0))
      (rhoVr (labLL D) _ (S.N.fr (.top 0))⁻¹ (castVV (wt_top_eq G) (Ψ (finG (Xp G) x)))) := by
  have e : psiC Ψ x = mapVV D.what₂.embLL (wt G (.top 0)) (castVV (wt_top_eq G) (Ψ (finG (Xp G) x))) :=
    (mapVV_castVV (wt_top_eq G) D.what₂.embLL _).symm
  unfold topVal
  rw [e, rhoVr_mapVV]

theorem inLat_of_mem {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (w : PlL D) {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {u : VV D.what₂.LL lam} (hu : u ∈ nabAtr (labLL D) lam Λ) : InLat lam w 0 Λ (mapVV D.what₂.embLL lam u) :=
  ⟨u, 1, rfl, one_ne_zero, by rw [Formalism.DivisionValues.vw, FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]; simp, by rwa [one_smul]⟩

theorem orth_inv {W : G.Weil} (S : GridChoice W Set.univ) (γ : UR D.sp.cm (Xp G).gram) :
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) (((S.N.fr (.top 0))⁻¹ * γ.1)⁻¹).1 * (Xp G).gram * (((S.N.fr (.top 0))⁻¹ * γ.1)⁻¹).1 = 1 := by
  have h1 : cT (D.sp.cm.sig : D.host.E →+* D.host.E) (S.N.fr (.top 0)).1 * (Xp G).gram * (S.N.fr (.top 0)).1 = 1 :=
    S.N.fr_on (.top 0) (Nat.zero_le _)
  have h2 : cT (D.sp.cm.sig : D.host.E →+* D.host.E) (γ⁻¹).1.1 * (Xp G).gram * (γ⁻¹).1.1 = (Xp G).gram := (γ⁻¹).2
  have e : (((S.N.fr (.top 0))⁻¹ * γ.1)⁻¹).1 = (γ⁻¹).1.1 * (S.N.fr (.top 0)).1 := by
    rw [_root_.mul_inv_rev, inv_inv]
    rfl
  have e2 : cT (D.sp.cm.sig : D.host.E →+* D.host.E) ((γ⁻¹).1.1 * (S.N.fr (.top 0)).1) =
      cT (D.sp.cm.sig : D.host.E →+* D.host.E) (S.N.fr (.top 0)).1 * cT (D.sp.cm.sig : D.host.E →+* D.host.E) (γ⁻¹).1.1 := by
    simp only [cT, Matrix.map_mul, Matrix.transpose_mul]
  rw [e, e2]
  calc _ = cT (D.sp.cm.sig : D.host.E →+* D.host.E) (S.N.fr (.top 0)).1 *
        (cT (D.sp.cm.sig : D.host.E →+* D.host.E) (γ⁻¹).1.1 * (Xp G).gram * (γ⁻¹).1.1) * (S.N.fr (.top 0)).1 := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h2, h1]

theorem nrm_nonneg (σ : D.what₂.LL →+* ℂ) (x : VV ℂ (LaP G)) :
    0 ≤ nrm (LaP G) (fun τ => (gramKd (emb D) (Xp G).gram τ).map σ) x := by
  have hG : ∀ τ, ((gramKd (emb D) (Xp G).gram τ).map σ).PosDef := fun τ => by
    have hP := posDef_Xp G (σ.comp (emb D τ))
    have hd : IsUnit ((Xp G).gram.map (emb D τ)).det := by
      have := (Matrix.isUnit_iff_isUnit_det _).1 hP.isUnit
      rw [RingHom.coe_comp, ← Matrix.map_map, ← RingHom.mapMatrix_apply σ, ← RingHom.map_det, isUnit_iff_ne_zero,
        map_ne_zero] at this
      exact isUnit_iff_ne_zero.2 this
    have e : (((Xp G).gram.map (emb D τ))⁻¹).map σ = ((Xp G).gram.map (σ.comp (emb D τ)))⁻¹ := by
      symm
      apply Matrix.inv_eq_left_inv
      rw [RingHom.coe_comp, ← Matrix.map_map, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hd,
        Matrix.map_one _ (map_zero _) (map_one _)]
    rw [gramKd, Matrix.transpose_map, e]
    exact hP.inv.transpose
  by_cases hx : x = 0
  · simp [nrm, hx]
  · exact (Complex.le_def.1 (pairK_pos _ hG x hx).le).1

theorem pullback_fin_relation {W : G.Weil} (S : GridChoice W Set.univ) (rp : ClassReps G) (w : PlL D) (c : G.ClPlus) (u : WtSp G)
    (hu : u ∈ wLat G (rp.lat c)) (x : FinPt G (.top 0)) :
    InLat _ w 0 (GlobalTheory.SumSize.latAt S (.top 0) x) (topVal S (rp.delta c u) x) := by
  rw [topVal_eq]
  refine inLat_of_mem _ w ?_
  rcases delta_cases rp c u (finG (Xp G) x) with h0 | ⟨γ, k, hk, hx, e⟩
  · rw [h0]
    rw [castVV_zero, map_zero]
    exact zero_mem _
  · rw [e, show rhoW G γ u = rhoVr (labLL D) (LaP G) γ.1 u from rfl, castVV_rhoVr_mul, latAt_eq S rp c x γ hk hx]
    exact castVV_mem _ (nabAtr_map _ _ _ _ _ (del_le_nab _ _ _ hu))

theorem inf_aux {W : G.Weil} (S : GridChoice W Set.univ) (rp : ClassReps G) (σ : D.what₂.LL →+* ℂ) (c : G.ClPlus) (u : WtSp G)
    (x : FinPt G (.top 0)) :
    NrmLe _ σ (topVal S (rp.delta c u) x)
      (nrm (LaP G) (fun τ => (gramKd (emb D) (Xp G).gram τ).map σ) (mapVV σ _ u)) := by
  rw [topVal_eq]
  refine ⟨_, rfl, ?_⟩
  rcases delta_cases rp c u (finG (Xp G) x) with h0 | ⟨γ, k, hk, hx, e⟩
  · rw [h0]
    rw [castVV_zero, map_zero, map_zero, nrm_zero]
    exact nrm_nonneg σ _
  · rw [e, show rhoW G γ u = rhoVr (labLL D) (LaP G) γ.1 u from rfl, castVV_rhoVr_mul, nrm_castVV,
      nrm_transport (Xp G) _ σ _ (orth_inv S γ)]

theorem finPsi_infPsi : GlobalTheory.FunPr.Hypotheses₂ → FinPsiK ∧ InfPsiK := by
  intro _
  constructor
  · refine ⟨0, fun CF _ => ⟨0, fun ε C _ => ⟨0, ?_⟩⟩⟩
    intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ _ w c u hu x
    exact pullback_fin_relation _ _ w c u hu x
  · refine ⟨0, fun CF _ => ⟨0, fun ε C _ => ⟨0, ?_⟩⟩⟩
    intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ _ σ c u x
    exact inf_aux _ _ σ c u x

end GlobalTheory.CompanionTheory.TestVal

end

end

end TestFunctionNorms
section
open GlobalTheory.SumSize GlobalTheory.RowClaim
theorem _root_.GlobalTheory.Adopt.finite_infinite_psi_bounds : GlobalTheory.FunPr.Hypotheses₂ → FinPsiK ∧ InfPsiK := by
  first | exact @TestFunctionNorms.GlobalTheory.CompanionTheory.TestVal.finPsi_infPsi | exact TestFunctionNorms.GlobalTheory.CompanionTheory.TestVal.finPsi_infPsi | (intros; apply TestFunctionNorms.GlobalTheory.CompanionTheory.TestVal.finPsi_infPsi <;> assumption)

end
