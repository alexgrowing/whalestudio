import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensTInner
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicIdentificationRespectsRealFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslatedRowEvaluationSquareIntegrableNorm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuous

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowEvalHH

private lemma exists_mem_fund_rep_eq_mul (I : AutInst) (fund : Set I.GA) (hcov : ∀ y : I.GA, ∃ γ ∈ I.GFset, γ * y ∈ fund)
    (y : I.GA) : ∃ γ ∈ I.GFset, γ * y ∈ fund ∧ I.rep fund y = γ * y := by
  unfold Formalism.MainNotions.S.AutInst.rep
  split_ifs with h
  · exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2, rfl⟩
  · exact absurd (hcov y) h

private lemma ae_comp_of_map_eq (B : RowsAut) (φ : B.I.GA → B.I.GA)
    (hφ : Measure.map φ (B.I.muA B.μf) = B.I.muA B.μf) {p : B.I.GA → Prop}
    (hp : ∀ᵐ z ∂(B.I.muA B.μf), p z) : ∀ᵐ x ∂(B.I.muA B.μf), p (φ x) := by
  by_cases h0 : B.I.muA B.μf = 0
  · rw [h0]; simp
  · have hm : AEMeasurable φ (B.I.muA B.μf) := by
      by_contra hn
      rw [Measure.map_of_not_aemeasurable hn] at hφ
      exact h0 hφ.symm
    exact ae_of_ae_map hm (by rw [hφ]; exact hp)

private lemma ext_ae_eq_of_leftInvariant (B : RowsAut) (f : B.I.GA → ℂ) (hf : ∀ γ ∈ B.I.GFset, ∀ y, f (γ * y) = f y)
    (F : B.I.L2 B.μf B.fund) (hF : (F : B.I.GA → ℂ) =ᵐ[(B.I.muA B.μf).restrict B.fund] f) :
    B.I.ext F =ᵐ[B.I.muA B.μf] f := by
  obtain ⟨Γ, hΓ, hcount, -, -⟩ := GlobalTheory.T.rationalUnitaryPoints_discrete_fundamentalDomain B.I
  have hc0 : (Γ : Set B.I.GA).Countable := Set.countable_coe_iff.mp hcount
  have hc : B.I.GFset.Countable := by rw [← hΓ]; exact hc0
  have h0 : ∀ᵐ z ∂(B.I.muA B.μf), z ∈ B.fund → (F : B.I.GA → ℂ) z = f z :=
    (ae_restrict_iff' B.fund_spec.1).mp hF
  have hall : ∀ᵐ y ∂(B.I.muA B.μf), ∀ γ ∈ B.I.GFset, γ * y ∈ B.fund →
      (F : B.I.GA → ℂ) (γ * y) = f (γ * y) :=
    (ae_ball_iff hc).mpr fun γ _ =>
      ae_comp_of_map_eq B (fun y => γ * y) ((GlobalTheory.T.adelicUnitaryHaar_bi_invariant B.I B.μf).1 γ) h0
  filter_upwards [hall] with y hy
  obtain ⟨γ, hγ, hmem, hrep⟩ := exists_mem_fund_rep_eq_mul B.I B.fund B.fund_spec.2.1 y
  show (F : B.I.GA → ℂ) (B.I.rep B.fund y) = f y
  rw [hrep, hy γ hγ hmem, hf γ hγ y]

theorem rightReg_ae (B : RowsAut) (f : B.I.GA → ℂ) (hf : ∀ γ ∈ B.I.GFset, ∀ y, f (γ * y) = f y)
    (F : B.I.L2 B.μf B.fund) (hF : (F : B.I.GA → ℂ) =ᵐ[(B.I.muA B.μf).restrict B.fund] f) (g : B.I.GA) :
    (B.R g F : B.I.GA → ℂ) =ᵐ[(B.I.muA B.μf).restrict B.fund] fun x => f (x * g) := by
  have hE := ext_ae_eq_of_leftInvariant B f hf F hF
  have hr : ∀ᵐ x ∂(B.I.muA B.μf), B.I.ext F (x * g) = f (x * g) :=
    ae_comp_of_map_eq B (fun x => x * g) ((GlobalTheory.T.adelicUnitaryHaar_bi_invariant B.I B.μf).2.1 g) (p := fun z => B.I.ext F z = f z) hE
  filter_upwards [B.R_spec g F, ae_restrict_of_ae hr] with x h1 h2
  rw [h1, h2]

theorem memLp_mul_right (B : RowsAut) (f : B.I.GA → ℂ) (hf : ∀ γ ∈ B.I.GFset, ∀ y, f (γ * y) = f y)
    (hm : MemLp f 2 ((B.I.muA B.μf).restrict B.fund)) (g : B.I.GA) :
    MemLp (fun x => f (x * g)) 2 ((B.I.muA B.μf).restrict B.fund) := by
  have h := rightReg_ae B f hf (hm.toLp f) hm.coeFn_toLp g
  exact (Lp.memLp (B.R g (hm.toLp f))).ae_eq h

open Classical in

theorem mult_props {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}
    (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M) (hT : T ∈ Mult θ M J χ) :
    (∀ v, ∀ γ ∈ GQ V, ∀ z, T v (γ * z) = T v z) ∧
    (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ),
      (w : M.H τ) = M.rep τ g (v τ) → ∀ z, T (Function.update v τ w) z = T v (z * atTau θ V τ g)) := by
  unfold Formalism.IndefR.Mult.Mult at hT
  induction hT using Submodule.span_induction with
  | mem T hT =>
    have hT' : IsMultMap θ M J χ T := hT
    refine ⟨fun v γ hγ z => (hT'.aut v).left γ hγ z, fun τ g hg v w hw z => ?_⟩
    rw [hT'.equiv τ g hg v w hw]
    rfl
  | zero =>
    refine ⟨fun v γ _ z => ?_, fun τ g _ v w _ z => ?_⟩ <;>
      simp only [MultilinearMap.zero_apply, Pi.zero_apply]
  | add T₁ T₂ _ _ h₁ h₂ =>
    refine ⟨fun v γ hγ z => ?_, fun τ g hg v w hw z => ?_⟩
    · simp only [MultilinearMap.add_apply, Pi.add_apply, h₁.1 v γ hγ z, h₂.1 v γ hγ z]
    · simp only [MultilinearMap.add_apply, Pi.add_apply, h₁.2 τ g hg v w hw z, h₂.2 τ g hg v w hw z]
  | smul a T _ h =>
    refine ⟨fun v γ hγ z => ?_, fun τ g hg v w hw z => ?_⟩
    · simp only [MultilinearMap.smul_apply, Pi.smul_apply, h.1 v γ hγ z]
    · simp only [MultilinearMap.smul_apply, Pi.smul_apply, h.2 τ g hg v w hw z]

private lemma star_zero_L2 (B : RowsAut) : (star (0 : B.I.L2 B.μf B.fund)) = 0 := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (0 : B.I.L2 B.μf B.fund),
    Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (B.I.muA B.μf).restrict B.fund)] with x h1 h2
  rw [h1, Pi.star_apply, h2]
  simp

end GlobalTheory.RowEvalHH

namespace GlobalTheory.RowEvalHH

open Classical in

theorem star_dite_mul_right (B : RowsAut) (f f' : B.I.GA → ℂ) (G : B.I.GA)
    (hf : ∀ γ ∈ B.I.GFset, ∀ y, f (γ * y) = f y) (key : ∀ x, f' x = f (x * G)) :
    (star (if hm : MemLp f' 2 ((B.I.muA B.μf).restrict B.fund) then hm.toLp f' else 0) : B.I.L2 B.μf B.fund) =
      B.R G (star (if hm : MemLp f 2 ((B.I.muA B.μf).restrict B.fund) then hm.toLp f else 0)) := by
  have hf' : f' = fun x => f (x * G) := funext key
  subst hf'
  by_cases hm : MemLp f 2 ((B.I.muA B.μf).restrict B.fund)
  · have hm' := memLp_mul_right B f hf hm G
    rw [dif_pos hm', dif_pos hm]
    have hsf : ∀ γ ∈ B.I.GFset, ∀ y, (star f) (γ * y) = (star f) y := fun γ hγ y => by
      simp only [Pi.star_apply, hf γ hγ y]
    have hS : ((star (hm.toLp f) : B.I.L2 B.μf B.fund) : B.I.GA → ℂ)
        =ᵐ[(B.I.muA B.μf).restrict B.fund] star f := by
      filter_upwards [Lp.coeFn_star (hm.toLp f), hm.coeFn_toLp] with x h1 h2
      rw [h1, Pi.star_apply, h2, Pi.star_apply]
    apply Lp.ext
    filter_upwards [Lp.coeFn_star (hm'.toLp _), hm'.coeFn_toLp, rightReg_ae B (star f) hsf _ hS G]
      with x h1 h2 h3
    rw [h1, Pi.star_apply, h2, h3, Pi.star_apply]
  · have hn' : ¬ MemLp (fun x => f (x * G)) 2 ((B.I.muA B.μf).restrict B.fund) := by
      intro h'
      apply hm
      have hl : ∀ γ ∈ B.I.GFset, ∀ y, f (γ * y * G) = f (y * G) := fun γ hγ y => by
        rw [mul_assoc, hf γ hγ]
      have h2 := memLp_mul_right B (fun x => f (x * G)) hl h' G⁻¹
      have he : ∀ x, f (x * G⁻¹ * G) = f x := fun x => by rw [mul_assoc, inv_mul_cancel, mul_one]
      exact h2.ae_eq (Filter.Eventually.of_forall he)
    rw [dif_neg hn', dif_neg hm, star_zero_L2, map_zero]

private lemma isUnit_of_mem_UH' {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : IsUnit g := by
  have h1 := Formalism.IndefR.SchurOrthogonalityAlt.isUnit_of_mem_UJ _ (Formalism.IndefR.SchurOrthogonalityAlt.conj_mem M τ hg)
  have h2 : g = (M.fr τ)⁻¹ * (M.fr τ * g * (M.fr τ)⁻¹) * M.fr τ := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Formalism.IndefR.SchurOrthogonalityAlt.fr_inv_mul, Matrix.mul_one,
      ← Matrix.mul_assoc, Formalism.IndefR.SchurOrthogonalityAlt.fr_inv_mul, Matrix.one_mul]
  rw [h2]
  exact ((Matrix.isUnit_nonsing_inv_iff.mpr (M.fr_unit τ)).mul h1).mul (M.fr_unit τ)

private lemma rep_mem_sm_of_mem_UH {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) {w : M.H τ}
    (hw : w ∈ M.sm τ) : M.rep τ g w ∈ M.sm τ := by
  have hu := isUnit_of_mem_UH' M τ hg
  have hmem : hu.unit ∈ Formalism.IndefR.SchurOrthogonalityAlt.Gt V τ := by
    show ((hu.unit : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)
    rw [IsUnit.unit_spec]
    exact hg
  have h := Formalism.IndefR.SchurOrthogonalityAlt.sm_stable M τ ⟨hu.unit, hmem⟩ hw
  simpa [Formalism.IndefR.SchurOrthogonalityAlt.gm, IsUnit.unit_spec] using h

theorem evF_equiv : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ S ∈ EP R F, ∀ (g : X.B.I.Ginf) (y : ∀ τ, ↥(GlobalTheory.RowEvalHH.Wsub R X c τ)), ∃ y' : ∀ τ, ↥(GlobalTheory.RowEvalHH.Wsub R X c τ), GlobalTheory.RowEvalHH.tensT X (fun τ => (y' τ : X.B.H (X.pl.symm τ))) = X.B.σs g (GlobalTheory.RowEvalHH.tensT X (fun τ => (y τ : X.B.H (X.pl.symm τ)))) ∧ GlobalTheory.RowEvalHH.evF R X h t c S y' = X.B.R (g, 1) (GlobalTheory.RowEvalHH.evF R X h t c S y) := by
  classical
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hLev hGrp hMod _hHost hι t c ht hc S hS g y
  obtain ⟨hfin, hat, hsurj⟩ := GlobalTheory.IotaReal.iotaX_real_finite R F X h hLev hGrp hMod hι
  choose g' hg' hg'eq using fun τ => hsurj τ (g (X.pl.symm τ))
  have hS0 := hS
  unfold EP RealDat.EEat goodPart at hS0
  have hS' := mult_props R.θ (MP R) _ _ S hS0.1
  obtain ⟨w', hw'⟩ : ∃ w' : (MP R).Vec, ∀ τ, ((w' τ : (MP R).sm τ) : (MP R).H τ) =
      (MP R).rep τ (g' τ) ((vecOf R X c y τ : (MP R).sm τ) : (MP R).H τ) :=
    ⟨fun τ => ⟨_, rep_mem_sm_of_mem_UH (MP R) τ (hg' τ) (vecOf R X c y τ).2⟩, fun τ => rfl⟩
  obtain ⟨y', hy'⟩ : ∃ y' : ∀ τ, ↥(Wsub R X c τ), ∀ τ,
      ((y' τ : ↥(Wsub R X c τ)) : X.B.H (X.pl.symm τ)) = c τ (w' τ : (MP R).H τ) :=
    ⟨fun τ => ⟨c τ (w' τ : (MP R).H τ), by unfold Wsub; exact Submodule.mem_map_of_mem (w' τ).2⟩,
      fun τ => rfl⟩
  have hyσ : ∀ τ, ((y' τ : ↥(Wsub R X c τ)) : X.B.H (X.pl.symm τ)) =
      X.B.σ (X.pl.symm τ) (uMat (g (X.pl.symm τ))) (y τ : X.B.H (X.pl.symm τ)) := by
    intro τ
    rw [hy', hw', hc τ (g' τ) (hg' τ), hg'eq τ]
    congr 1
    exact (c τ).apply_symm_apply _
  obtain ⟨a, ha⟩ : ∃ a : Finset D.what₂.Tau → GA D (D.sp.Y 0), ∀ s,
      iotaX X h (a s) = ((fun v => if X.pl v ∈ s then g v else 1 : X.B.I.Ginf), (1 : X.B.I.Gf)) :=
    ⟨fun s => (iotaX X h).symm _, fun s => (iotaX X h).apply_symm_apply _⟩
  have hstep : ∀ τ (s : Finset D.what₂.Tau), τ ∉ s →
      atTau R.θ (D.sp.Y 0) τ (g' τ) * a s = a (insert τ s) := by
    intro τ s hτ
    apply (iotaX X h).injective
    obtain ⟨h2, h1, -⟩ := hat τ (g' τ) (hg' τ)
    rw [map_mul, ha, ha]
    refine Prod.ext ?_ ?_
    · funext v
      simp only [Prod.fst_mul, Pi.mul_apply]
      by_cases hv : v = X.pl.symm τ
      · subst hv
        rw [hg'eq τ]
        simp [hτ]
      · rw [h1 v hv, one_mul]
        have hne : X.pl v ≠ τ := fun e => hv (by rw [← e, Equiv.symm_apply_apply])
        simp [hne]
    · simp only [Prod.snd_mul, h2, one_mul]
  have hclaim : ∀ s : Finset D.what₂.Tau, ∀ z,
      S (fun τ => if τ ∈ s then w' τ else vecOf R X c y τ) z = S (vecOf R X c y) (z * a s) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro z
      have h1 : a ∅ = 1 := by
        apply (iotaX X h).injective
        rw [ha, map_one]
        refine Prod.ext ?_ rfl
        funext v
        simp
      simp [h1]
    | @insert τ s hτ ih =>
      intro z
      have hw : ((w' τ : (MP R).sm τ) : (MP R).H τ) = (MP R).rep τ (g' τ)
          (((fun τ' => if τ' ∈ s then w' τ' else vecOf R X c y τ') τ : (MP R).sm τ) : (MP R).H τ) := by
        simp only [if_neg hτ]
        exact hw' τ
      have e := hS'.2 τ (g' τ) (hg' τ) (fun τ' => if τ' ∈ s then w' τ' else vecOf R X c y τ') (w' τ) hw z
      refine Eq.trans (congrArg (fun v => S v z) ?_) (e.trans ?_)
      · funext τ'
        by_cases hτ' : τ' = τ
        · subst hτ'
          simp
        · simp [hτ', Function.update_of_ne hτ']
      · rw [ih, mul_assoc, hstep τ s hτ]
  have hclaim' : ∀ z, S w' z = S (vecOf R X c y) (z * a Finset.univ) := by
    intro z
    have e := hclaim Finset.univ z
    simpa using e
  refine ⟨y', ?_, ?_⟩
  · unfold tensT
    rw [X.B.tens_spec.2.1 g]
    congr 1
    funext v
    obtain ⟨τ, rfl⟩ := X.pl.symm.surjective v
    simp only [Equiv.piCongrLeft_apply_apply]
    exact hyσ τ
  · have hvec : vecOf R X c y' = w' := by
      funext τ
      apply Subtype.ext
      show (c τ).symm ((y' τ : X.B.H (X.pl.symm τ))) = _
      rw [hy']
      exact (c τ).symm_apply_apply _
    let t0 : GA D (D.sp.Y 0) := t
    have htfin : (iotaX X h t0).1 = 1 := (hfin t0).mp ht
    have ha1 : a Finset.univ = (iotaX X h).symm (g, 1) := by
      apply (iotaX X h).injective
      rw [ha, ContinuousMulEquiv.apply_symm_apply]
      refine Prod.ext ?_ rfl
      funext v
      simp
    have hcomm : t0 * a Finset.univ = a Finset.univ * t0 := by
      apply (iotaX X h).injective
      rw [map_mul, map_mul, ha]
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_mul, htfin, one_mul, mul_one]
      · simp only [Prod.snd_mul, one_mul, mul_one]
    unfold evF
    rw [hvec]
    refine star_dite_mul_right X.B _ _ (g, 1) ?_ ?_
    · intro γ hγ x
      show S (vecOf R X c y) ((iotaX X h).symm (γ * x) * t0) =
        S (vecOf R X c y) ((iotaX X h).symm x * t0)
      have hγ' : (iotaX X h).symm γ ∈ GQ (D.sp.Y 0) := by
        refine (GlobalTheory.EvalNormTransfer.iotaX_rat X h _).mpr ?_
        convert hγ using 1
        exact (iotaX X h).apply_symm_apply γ
      rw [map_mul, mul_assoc, hS'.1 _ _ hγ']
    · intro x
      show S w' ((iotaX X h).symm x * t0) =
        S (vecOf R X c y) ((iotaX X h).symm (x * (g, 1)) * t0)
      rw [hclaim', map_mul, ← ha1, mul_assoc, hcomm, ← mul_assoc]

end GlobalTheory.RowEvalHH
