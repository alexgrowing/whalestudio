import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.ConsumerA
import Formalism.PeriodIntegrals.ZuckTensor

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

open MeasureTheory

def cns_Ok (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : S7.KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) : Prop :=
  (∃ h : ℝ, GapAtLeast ε lam h ∧ thrStar ε < h) ∧ StdGap ε lam ∧ IsPsiFor ε lam T Ψ ∧ T.w ≠ 0 ∧
    (∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive) ∧
    (∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ T.w), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ T.w),
        MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
          inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2
          (Formalism.REAL.muG ε)) ∧
    HasGelfandChar (smE ε (rreg ε)) lam (genSub (smE ε (rreg ε)) (datumV ε Ψ T.w))

theorem cns_data' {ε : Fin n → Bool} (hq : 1 ≤ S7.q0 ε) {lam : Fin n → ℝ} (hlam : S7.IsHCParam lam)
    {h : ℝ} (hh : GapAtLeast ε lam h) (hth : thrStar ε < h) :
    ∃ (T : S7.KType ε (lowK ε lam)) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), cns_Ok ε lam T Ψ := by
  obtain ⟨T, Ψ, h1, h2, h3, h4, h5, h6⟩ := cns_data hq hlam hh hth
  exact ⟨T, Ψ, ⟨h, hh, hth⟩, h1, h2, h3, h4, h5, h6⟩

theorem cns_family (dual : Bool) {ε : Fin n → Bool} (hq : 1 ≤ S7.q0 ε) {μ : Fin n → ℝ}
    (hμ : S7.IsHCParam μ) {h : ℝ} (hG : GapAtLeast ε μ h) (hth : thrStar ε + 1 < h) :
    ∃ (lamS : Fin n → Fin n → ℝ) (Ts : ∀ s, S7.KType ε (lowK ε (lamS s)))
      (Ψs : ∀ s, Matrix (Fin n) (Fin n) ℂ → ((Ts s).V →L[ℂ] (Ts s).V)),
      (∀ s, cns_Ok ε (lamS s) (Ts s) (Ψs s)) ∧
      ∀ s, S7.IsHCParam (shiftF dual μ s) → lamS s = shiftF dual μ s := by
  have hth0 : thrStar ε < h := by linarith
  have hdat : ∀ s, ∃ lam' : Fin n → ℝ, ∃ (T' : S7.KType ε (lowK ε lam'))
      (Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)), cns_Ok ε lam' T' Ψ' ∧
      (S7.IsHCParam (shiftF dual μ s) → lam' = shiftF dual μ s) := by
    intro s
    by_cases hs : S7.IsHCParam (shiftF dual μ s)
    · obtain ⟨T', Ψ', hok⟩ := cns_data' hq hs (cns_shift_gap dual hG s) (by linarith)
      exact ⟨_, T', Ψ', hok, fun _ => rfl⟩
    · obtain ⟨T', Ψ', hok⟩ := cns_data' hq hμ hG hth0
      exact ⟨μ, T', Ψ', hok, fun h' => absurd h' hs⟩
  choose lamS Ts Ψs hS hsh using hdat
  exact ⟨lamS, Ts, Ψs, hS, hsh⟩

theorem cns_pole (dual : Bool) {ε : Fin n → Bool} {μ : Fin n → ℝ} (hμ : S7.IsHCParam μ)
    {T : S7.KType ε (lowK ε μ)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}
    (hgap : StdGap ε μ) (hP : IsPsiFor ε μ T Ψ) (hv₀ : v₀ ≠ 0)
    (hW : (∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
        MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
          inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2
          (Formalism.REAL.muG ε)))
    (hG : HasGelfandChar (smE ε (rreg ε)) μ (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)))
    {z : ℂ} {f : Fin n → smD ε (rreg ε)} (hf : f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)))
    (hf0 : f ≠ 0) (he : eeF dual (smE ε (rreg ε)) f = z • f) :
    ∃ s, S7.IsHCParam (shiftF dual μ s) ∧ z = poleF dual μ s := by
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  have hsm : ∀ v : smD ε (rreg ε), IsSmoothVecU ε (rreg ε) (v : _) := fun v => (mem_smD_iff ε (rreg ε) _).1 v.2
  obtain ⟨s, rfl⟩ := (pole_match dual hσ hD hsm hgap (datumV_isKIrrHW hP hv₀) (datumV_casimir hP v₀)
    (datumV_kStable hP v₀) hW hG).1 z f hf hf0 he
  refine ⟨s, ?_, rfl⟩
  by_contra hns
  exact hf0 (cc_gk_singular dual hσ hD hsm hgap (datumV_isKIrrHW hP hv₀) (datumV_casimir hP v₀)
    (datumV_kStable hP v₀) hW hG s (cns_sing dual hμ hns) f hf he)

theorem cns_toSum_core (dual : Bool) {ε : Fin n → Bool} {μ : Fin n → ℝ} (hμ : S7.IsHCParam μ)
    {T : S7.KType ε (lowK ε μ)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} (hok : cns_Ok ε μ T Ψ)
    (lamS : Fin n → Fin n → ℝ) (Ts : ∀ s, S7.KType ε (lowK ε (lamS s)))
    (Ψs : ∀ s, Matrix (Fin n) (Fin n) ℂ → ((Ts s).V →L[ℂ] (Ts s).V))
    (hS : ∀ s, cns_Ok ε (lamS s) (Ts s) (Ψs s))
    (hsh : ∀ s, S7.IsHCParam (shiftF dual μ s) → lamS s = shiftF dual μ s)
    {η f : Fin n → smD ε (rreg ε)} (hη : η ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ T.w)))
    (hf : f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ T.w))) :
    ∃ (ι : Type) (_ : Fintype ι) (sI : ι → Fin n) (vI wI : ∀ i, Hlam ε (Ψs (sI i)) (Ts (sI i)).w),
      (∀ i, S7.IsHCParam (shiftF dual μ (sI i)) ∧
        PI.UpqRep.IsKFin ε (sigLam ε (Ψs (sI i)) (Ts (sI i)).w) (vI i) ∧
        PI.UpqRep.IsKFin ε (sigLam ε (Ψs (sI i)) (Ts (sI i)).w) (wI i)) ∧
      ∀ g ∈ UJset ε, ∑ c, inner ℂ ((η c : smD ε (rreg ε)) : L2 ε)
          (tensGrp dual (rreg ε) g (fun d => ((f d : smD ε (rreg ε)) : L2 ε)) c) =
        ∑ i, inner ℂ (wI i) (sigLam ε (Ψs (sI i)) (Ts (sI i)).w g (vI i)) := by
  classical
  obtain ⟨⟨h0, hh0, hth0⟩, hgap, hP, hv, hpos, hW, hG⟩ := hok
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  obtain ⟨B, hdec, -⟩ := ee_decomp dual hσ hD hgap (datumV_isKIrrHW hP hv) (datumV_casimir hP T.w)
    (datumV_kStable hP T.w) hW
  obtain ⟨fb, hfb, rfl⟩ := hdec f hf
  have hcomp : ∀ i : {b // b ∈ B.filter (fun b => fb b ≠ 0)}, ∃ s, S7.IsHCParam (shiftF dual μ s) ∧
      ∃ x z : Hlam ε (Ψs s) (Ts s).w, PI.UpqRep.IsKFin ε (sigLam ε (Ψs s) (Ts s).w) x ∧
        PI.UpqRep.IsKFin ε (sigLam ε (Ψs s) (Ts s).w) z ∧
        ∀ g ∈ UJset ε, ∑ c, inner ℂ ((η c : smD ε (rreg ε)) : L2 ε)
          (tensGrp dual (rreg ε) g (fun d => ((fb i d : smD ε (rreg ε)) : L2 ε)) c) =
          inner ℂ z (sigLam ε (Ψs s) (Ts s).w g x) := by
    intro i
    have hi := (Finset.mem_filter.1 i.2).2
    obtain ⟨s, hs, hz⟩ := cns_pole dual hμ hgap hP hv hW hG (hfb i).1 hi (hfb i).2
    obtain ⟨⟨h', hh', hth'⟩, hgap', hP', hv', hpos', hW', hG'⟩ := hS s
    have he : eeF dual (smE ε (rreg ε)) (fb i) = poleF dual μ s • fb i := by rw [(hfb i).2, hz]
    exact ⟨s, hs, cns_term dual hgap hP hv hgap' hP' hv' hh0 hth0 hh' hth' hpos hpos' hW hW' hG hG' s
      (hsh s hs) (hfb i).1 he hη⟩
  choose sI hsI xI zI hx hz hEq using hcomp
  refine ⟨{b // b ∈ B.filter (fun b => fb b ≠ 0)}, inferInstance, sI, xI, zI,
    fun i => ⟨hsI i, hx i, hz i⟩, fun g hg => ?_⟩
  have h0 : ∀ b ∈ B, ∑ c, inner ℂ ((η c : smD ε (rreg ε)) : L2 ε)
      (tensGrp dual (rreg ε) g (fun d => ((fb b d : smD ε (rreg ε)) : L2 ε)) c) ≠ 0 → fb b ≠ 0 := by
    intro b _ hne hb
    apply hne
    simp [hb, tensGrp]
  rw [cns_tens_sum, ← Finset.sum_filter_of_ne h0, ← Finset.sum_coe_sort]
  exact Finset.sum_congr rfl fun i _ => hEq i g hg

theorem cns_ofSum_core (dual : Bool) {ε : Fin n → Bool} {μ lam' : Fin n → ℝ}
    {T : S7.KType ε (lowK ε μ)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} (hok : cns_Ok ε μ T Ψ)
    {T' : S7.KType ε (lowK ε lam')} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}
    (hok' : cns_Ok ε lam' T' Ψ') (s : Fin n) (hlam' : lam' = shiftF dual μ s) {x' z' : smD ε (rreg ε)}
    (hx' : x' ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' T'.w))
    (hz' : z' ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' T'.w)) :
    ∃ f F : Fin n → smD ε (rreg ε), f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ T.w)) ∧
      F ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ T.w)) ∧
      ∀ g ∈ UJset ε, inner ℂ ((z' : smD ε (rreg ε)) : L2 ε) (rreg ε g ((x' : smD ε (rreg ε)) : L2 ε)) =
        ∑ c, inner ℂ ((f c : smD ε (rreg ε)) : L2 ε)
          (tensGrp dual (rreg ε) g (fun d => ((F d : smD ε (rreg ε)) : L2 ε)) c) := by
  obtain ⟨⟨h, hh, hth⟩, hgap, hP, hv, hpos, hW, hG⟩ := hok
  obtain ⟨⟨h', hh', hth'⟩, hgap', hP', hv', hpos', hW', hG'⟩ := hok'
  haveI := Hlam_nontrivial hgap hP hv
  haveI := Hlam_nontrivial hgap' hP' hv'
  obtain ⟨w, hw⟩ := exists_ne (0 : Hlam ε Ψ T.w)
  obtain ⟨w', hw'⟩ := exists_ne (0 : Hlam ε Ψ' T'.w)
  obtain ⟨⟨ι, hι, -, -⟩, -⟩ := cc_gk dual hgap hP hv hgap' hP' hv' hh hth hh' hth' hpos hpos' hW hW' hG hG'
    s hlam' hw hw'
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  obtain ⟨f, hf, hfe⟩ := (coef_of_emb dual hσ hD hgap (datumV_isKIrrHW hP hv) (datumV_casimir hP T.w)
    (datumV_kStable hP T.w) hgap' (datumV_isKIrrHW hP' hv') (datumV_casimir hP' T'.w)
    (datumV_kStable hP' T'.w) hι).2 z' hz' x' hx'
  exact ⟨f, ι x', hf, hι.1 x' hx', hfe⟩

end ReciprocityTheory.ChartRestriction.DS

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

open MeasureTheory

theorem cns_zuck_nc {ε : Fin n → Bool} (hq : 1 ≤ S7.q0 ε) {μ : Fin n → ℝ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hμ : PI.UpqRep.IsHCParam μ) (hd : PI.UpqRep.IsDS ε μ σ) {h : ℝ} (hG : PI.ZuckTensor.GapAtLeast ε μ h)
    (hth : thrStar ε + 1 < h) :
    ∃ X : PI.ZuckTensor.TensorDS n ε μ H σ, ∀ s, s ∈ X.Sm ↔ PI.UpqRep.IsHCParam (μ + Pi.single s 1) := by
  classical
  have hμ' : S7.IsHCParam μ := hμ
  have hG' : GapAtLeast ε μ h := hG
  obtain ⟨T, Ψ, hok⟩ := cns_data' hq hμ' hG' (by linarith)
  obtain ⟨lamS, Ts, Ψs, hS, hsh⟩ := cns_family false hq hμ' hG' hth
  obtain ⟨U, hU⟩ := equiv_sigLam_of_isDS hd hok.2.1 hok.2.2.1 hok.2.2.2.1
  have hU' := cns_symm_intertw U hU
  refine ⟨{ Sm := univ.filter (fun s => S7.IsHCParam (shiftF false μ s))
            Hs := fun s => Hlam ε (Ψs s) (Ts s).w
            σs := fun s => sigLam ε (Ψs s) (Ts s).w
            ds := ?_, inequiv := ?_, toSum := ?_, ofSum := ?_ }, ?_⟩
  · intro s hs
    have hs' := (mem_filter.1 hs).2
    refine ⟨hs', ?_⟩
    have e : (μ + Pi.single s 1) = lamS s := (hsh s hs').symm
    rw [e]
    exact isDS_sigLam (hS s).2.1 (hS s).2.2.1 (hS s).2.2.2.1
  · rintro s hs s' hs' hne ⟨V, hV⟩
    apply hne
    have e := sigLam_inj (hS s).2.1 (hS s).2.2.1 (hS s).2.2.2.1 (hS s').2.1 (hS s').2.2.1 (hS s').2.2.2.1 V hV
    rw [hsh s (mem_filter.1 hs).2, hsh s' (mem_filter.1 hs').2] at e
    exact cns_shift_inj false μ e
  · intro v w x y hv hw
    obtain ⟨a, ha, hav⟩ := cns_kfin_gen hok.2.1 hok.2.2.1 hok.2.2.2.1 (cns_kfin_map U.symm hU' hv)
    obtain ⟨b, hb, hbw⟩ := cns_kfin_gen hok.2.1 hok.2.2.1 hok.2.2.2.1 (cns_kfin_map U.symm hU' hw)
    obtain ⟨ι, hι, sI, vI, wI, hI, hEq⟩ := cns_toSum_core false hμ' hok lamS Ts Ψs hS hsh
      (η := fun c => y c • b) (f := fun d => x d • a)
      (tset_mem.2 fun c => Submodule.smul_mem _ _ hb) (tset_mem.2 fun d => Submodule.smul_mem _ _ ha)
    refine ⟨ι, hι, sI, vI, wI, fun i => ⟨mem_filter.2 ⟨mem_univ _, (hI i).1⟩, (hI i).2.1, (hI i).2.2⟩,
      fun g hg => ?_⟩
    rw [← hEq g hg]
    simp only [Submodule.coe_smul]
    rw [← cns_coefV (rreg ε) g (a : L2 ε) (b : L2 ε) x y, ← U.apply_symm_apply v, ← U.apply_symm_apply w,
      cns_inner_tr hok.2.1 hok.2.2.1 hok.2.2.2.1 U hU hg, ← hav, ← hbw]
  · intro s hs v w hv hw
    have hs' := (mem_filter.1 hs).2
    obtain ⟨x', hx', hxv⟩ := cns_kfin_gen (hS s).2.1 (hS s).2.2.1 (hS s).2.2.2.1 hv
    obtain ⟨z', hz', hzw⟩ := cns_kfin_gen (hS s).2.1 (hS s).2.2.1 (hS s).2.2.2.1 hw
    obtain ⟨f, F, hf, hF, hfe⟩ := cns_ofSum_core false hok (hS s) s (hsh s hs') hx' hz'
    have hfm := tset_mem.1 hf
    have hFm := tset_mem.1 hF
    refine ⟨Fin n × Fin n, inferInstance,
      fun p => U ⟨((F p.2 : smD ε (rreg ε)) : L2 ε), cns_gen_mem_Hlam (hFm p.2)⟩,
      fun p => U ⟨((f p.1 : smD ε (rreg ε)) : L2 ε), cns_gen_mem_Hlam (hfm p.1)⟩,
      fun p => Pi.single p.2 1, fun p => Pi.single p.1 1,
      fun p => ⟨cns_kfin_map U hU (cns_kfin hok.2.1 hok.2.2.1 hok.2.2.2.1 (hFm p.2) _ rfl),
        cns_kfin_map U hU (cns_kfin hok.2.1 hok.2.2.1 hok.2.2.2.1 (hfm p.1) _ rfl)⟩, fun g hg => ?_⟩
    dsimp only
    rw [Submodule.coe_inner, sigLam_coe (hS s).2.1 (hS s).2.2.1 (hS s).2.2.2.1 hg, ← hxv, ← hzw, hfe g hg,
      cns_expandV]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [cns_inner_tr hok.2.1 hok.2.2.1 hok.2.2.2.1 U hU hg]
  · intro s
    exact ⟨fun hs => (mem_filter.1 hs).2, fun hs => mem_filter.2 ⟨mem_univ _, hs⟩⟩

theorem cns_zuckd_nc {ε : Fin n → Bool} (hq : 1 ≤ S7.q0 ε) {μ : Fin n → ℝ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hμ : PI.UpqRep.IsHCParam μ) (hd : PI.UpqRep.IsDS ε μ σ) {h : ℝ} (hG : PI.ZuckTensor.GapAtLeast ε μ h)
    (hth : thrStar ε + 1 < h) :
    ∃ X : PI.ZuckTensor.TensorDSd n ε μ H σ, ∀ s, s ∈ X.Sm ↔ PI.UpqRep.IsHCParam (μ - Pi.single s 1) := by
  classical
  have hμ' : S7.IsHCParam μ := hμ
  have hG' : GapAtLeast ε μ h := hG
  obtain ⟨T, Ψ, hok⟩ := cns_data' hq hμ' hG' (by linarith)
  obtain ⟨lamS, Ts, Ψs, hS, hsh⟩ := cns_family true hq hμ' hG' hth
  obtain ⟨U, hU⟩ := equiv_sigLam_of_isDS hd hok.2.1 hok.2.2.1 hok.2.2.2.1
  have hU' := cns_symm_intertw U hU
  refine ⟨{ Sm := univ.filter (fun s => S7.IsHCParam (shiftF true μ s))
            Hs := fun s => Hlam ε (Ψs s) (Ts s).w
            σs := fun s => sigLam ε (Ψs s) (Ts s).w
            ds := ?_, inequiv := ?_, toSum := ?_, ofSum := ?_ }, ?_⟩
  · intro s hs
    have hs' := (mem_filter.1 hs).2
    refine ⟨hs', ?_⟩
    have e : (μ - Pi.single s 1) = lamS s := (hsh s hs').symm
    rw [e]
    exact isDS_sigLam (hS s).2.1 (hS s).2.2.1 (hS s).2.2.2.1
  · rintro s hs s' hs' hne ⟨V, hV⟩
    apply hne
    have e := sigLam_inj (hS s).2.1 (hS s).2.2.1 (hS s).2.2.2.1 (hS s').2.1 (hS s').2.2.1 (hS s').2.2.2.1 V hV
    rw [hsh s (mem_filter.1 hs).2, hsh s' (mem_filter.1 hs').2] at e
    exact cns_shift_inj true μ e
  · intro v w x y hv hw
    obtain ⟨a, ha, hav⟩ := cns_kfin_gen hok.2.1 hok.2.2.1 hok.2.2.2.1 (cns_kfin_map U.symm hU' hv)
    obtain ⟨b, hb, hbw⟩ := cns_kfin_gen hok.2.1 hok.2.2.1 hok.2.2.2.1 (cns_kfin_map U.symm hU' hw)
    obtain ⟨ι, hι, sI, vI, wI, hI, hEq⟩ := cns_toSum_core true hμ' hok lamS Ts Ψs hS hsh
      (η := fun c => star (x c) • b) (f := fun d => star (y d) • a)
      (tset_mem.2 fun c => Submodule.smul_mem _ _ hb) (tset_mem.2 fun d => Submodule.smul_mem _ _ ha)
    refine ⟨ι, hι, sI, vI, wI, fun i => ⟨mem_filter.2 ⟨mem_univ _, (hI i).1⟩, (hI i).2.1, (hI i).2.2⟩,
      fun g hg => ?_⟩
    rw [← hEq g hg]
    simp only [Submodule.coe_smul]
    rw [← cns_coefVd (rreg ε) g (a : L2 ε) (b : L2 ε) x y, ← U.apply_symm_apply v, ← U.apply_symm_apply w,
      cns_inner_tr hok.2.1 hok.2.2.1 hok.2.2.2.1 U hU hg, ← hav, ← hbw]
  · intro s hs v w hv hw
    have hs' := (mem_filter.1 hs).2
    obtain ⟨x', hx', hxv⟩ := cns_kfin_gen (hS s).2.1 (hS s).2.2.1 (hS s).2.2.2.1 hv
    obtain ⟨z', hz', hzw⟩ := cns_kfin_gen (hS s).2.1 (hS s).2.2.1 (hS s).2.2.2.1 hw
    obtain ⟨f, F, hf, hF, hfe⟩ := cns_ofSum_core true hok (hS s) s (hsh s hs') hx' hz'
    have hfm := tset_mem.1 hf
    have hFm := tset_mem.1 hF
    refine ⟨Fin n × Fin n, inferInstance,
      fun p => U ⟨((F p.2 : smD ε (rreg ε)) : L2 ε), cns_gen_mem_Hlam (hFm p.2)⟩,
      fun p => U ⟨((f p.1 : smD ε (rreg ε)) : L2 ε), cns_gen_mem_Hlam (hfm p.1)⟩,
      fun p => Pi.single p.1 1, fun p => Pi.single p.2 1,
      fun p => ⟨cns_kfin_map U hU (cns_kfin hok.2.1 hok.2.2.1 hok.2.2.2.1 (hFm p.2) _ rfl),
        cns_kfin_map U hU (cns_kfin hok.2.1 hok.2.2.1 hok.2.2.2.1 (hfm p.1) _ rfl)⟩, fun g hg => ?_⟩
    dsimp only
    rw [Submodule.coe_inner, sigLam_coe (hS s).2.1 (hS s).2.2.1 (hS s).2.2.2.1 hg, ← hxv, ← hzw, hfe g hg,
      cns_expandVd]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [cns_inner_tr hok.2.1 hok.2.2.1 hok.2.2.2.1 U hU hg]
  · intro s
    exact ⟨fun hs => (mem_filter.1 hs).2, fun hs => mem_filter.2 ⟨mem_univ _, hs⟩⟩

end ReciprocityTheory.ChartRestriction.DS
