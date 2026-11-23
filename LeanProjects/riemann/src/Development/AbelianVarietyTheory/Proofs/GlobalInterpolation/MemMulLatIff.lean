import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralDensEqZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDivLatticeQuotient
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PerOComponents
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SmulMemLocPPerO
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSdLatTwOExpS
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsNatMulIntegral
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelIndexEqProdLocP
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CrdSurjective
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelIndexLocPNeZero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsTransvSurjInv
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.XiIndEqInter
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SignedLiftWEq
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatSumReindexOfLeSup
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JetOpIdentityOfEntire
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormEqOfSplit
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitOfConjPNe
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NotDvdDifferent
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnderEqIffMapLe
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLocalIdele
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelNotMemRowSG
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DeltaNeZero

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.ThetaMove

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

section Lattices

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Finset (HeightOneSpectrum (𝓞 E))}

section General

variable {W : Type} [AddCommGroup W] [Module (𝓞 E) W]

omit [StarRing E] in
theorem Dom.inf_le {As L₁ L₂ : Submodule (𝓞 E) W} (h : Dom S As L₁) (h' : Dom S L₁ L₂) : L₂ ⊓ As ≤ L₁ := fun x hx =>
  mem_of_locP fun Q => by
    by_cases hQ : Q ∈ S
    · exact h'.1 Q hQ (mem_localization_of_mem Q hx.1)
    · exact h.2 Q hQ (mem_localization_of_mem Q hx.2)

omit [StarRing E] in
theorem Dom.le_sup {As L₁ L₂ : Submodule (𝓞 E) W} (h : Dom S As L₁) (h' : Dom S L₁ L₂) (f : Full As) (f₁ : Full L₁) (f₂ : Full L₂) :
    L₁ ≤ (L₁ ⊓ As) ⊔ (L₁ ⊓ L₂) := by
  intro x hx
  obtain ⟨t, h1, h2⟩ := ((f.inf f₁).inf f₂).approx S x
  simp only [localization_inf, Submodule.mem_inf] at h1 h2
  have e : ∀ {M : Submodule (𝓞 E) W}, t - x ∈ M → x ∈ M → t ∈ M := fun h h' => by simpa using add_mem h h'
  have ht : t ∈ L₁ := mem_of_locP fun Q => by
    by_cases hQ : Q ∈ S
    · exact e (h1 Q hQ).1.2 (mem_localization_of_mem Q hx)
    · exact (h2 Q hQ).1.2
  refine Submodule.mem_sup.2 ⟨t, ⟨ht, mem_of_locP fun Q => ?_⟩, x - t, ⟨sub_mem hx ht, mem_of_locP fun Q => ?_⟩, by abel⟩
  · by_cases hQ : Q ∈ S
    · exact e (h1 Q hQ).1.1 (h.1 Q hQ (mem_localization_of_mem Q hx))
    · exact (h2 Q hQ).1.1
  · by_cases hQ : Q ∈ S
    · simpa using neg_mem (h1 Q hQ).2
    · exact sub_mem (h'.2 Q hQ (mem_localization_of_mem Q hx)) (h2 Q hQ).2

variable [Module E W] [IsScalarTower (𝓞 E) E W]

theorem nat_smul_mem {M : Submodule (𝓞 E) W} (c : ℕ) {x : W} (hx : x ∈ M) : (c : E) • x ∈ M := by
  have := M.smul_mem (c : 𝓞 E) hx
  rwa [← algebraMap_smul E, map_natCast] at this

theorem dom_tw (M : Submodule (𝓞 E) W) {c : ℕ} (hc : 0 < c) : Dom S M (twist₂ M c (expS S)) := by
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  refine ⟨fun P hP x hx => ?_, fun Q hQ x hx => ?_⟩
  · rw [mem_localization_twist M hc (expS_bound S), expS, if_pos hP, zpow_one] at hx
    simpa [smul_smul, hcE] using nat_smul_mem c hx
  · rw [mem_localization_twist M hc (expS_bound S), expS, if_neg hQ]
    split_ifs
    · simpa using nat_smul_mem c hx
    · simpa using hx

theorem negS_bound (Q : HeightOneSpectrum (𝓞 E)) : -1 ≤ -expS S Q ∧ -expS S Q ≤ 1 := by
  have := expS_bound S Q
  omega

theorem tw_dom (M : Submodule (𝓞 E) W) {c : ℕ} (hc : 0 < c) : Dom S (twist₂ M c fun Q => -expS S Q) M := by
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  refine ⟨fun P hP x hx => ?_, fun Q hQ x hx => ?_⟩
  · rw [mem_localization_twist M hc negS_bound, expS, if_pos hP]
    simpa using nat_smul_mem c hx
  · rw [mem_localization_twist M hc negS_bound, expS, if_neg hQ] at hx
    split_ifs at hx
    · simpa [smul_smul, hcE] using nat_smul_mem c hx
    · simpa using hx

theorem tw_congr {M M' : Submodule (𝓞 E) W} {c : ℕ} (hc : 0 < c) {e : HeightOneSpectrum (𝓞 E) → ℤ} (he : ∀ Q, -1 ≤ e Q ∧ e Q ≤ 1)
    {Q : HeightOneSpectrum (𝓞 E)} (h : localization₂ Q.asIdeal M = localization₂ Q.asIdeal M') :
    localization₂ Q.asIdeal (twist₂ M c e) = localization₂ Q.asIdeal (twist₂ M' c e) := by
  ext x
  rw [mem_localization_twist M hc he, mem_localization_twist M' hc he, h]

end General

variable {a b : ℕ} {AA : Submodule (𝓞 E) E}

theorem dom_per {M₁ M₂ : Submodule (𝓞 E) (Sp E a)} {M₁' M₂' : Submodule (𝓞 E) (Sp E b)} (h₁ : IsSdLat M₁) (h₂ : IsSdLat M₂)
    (h : Dom S M₂ M₁) (h' : Dom S M₁' M₂') : Dom S (perO AA M₁ M₁') (perO AA M₂ M₂') :=
  ⟨fun P hP => (GlobalTheory.ThetaMove.PeriodComp.perO_components E a b AA).1 P _ _ _ _ h₁.1.fg (h.1 P hP) (h'.1 P hP),
    fun Q hQ => (GlobalTheory.ThetaMove.PeriodComp.perO_components E a b AA).1 Q _ _ _ _ h₂.1.fg (h.2 Q hQ) (h'.2 Q hQ)⟩

theorem full_per {M : Submodule (𝓞 E) (Sp E a)} {M' : Submodule (𝓞 E) (Sp E b)} (h : IsSdLat M) (h' : IsSdLat M') (hA : AA ≠ ⊥) :
    Full (perO AA M M') := (GlobalTheory.ThetaMove.PeriodComp.perO_components E a b AA).2.2 M M' h.1.fg h'.1 hA

theorem perO_fg {M : Submodule (𝓞 E) (Sp E a)} {M' : Submodule (𝓞 E) (Sp E b)} (h : IsSdLat M) (h' : IsSdLat M') (hA : AA.FG) :
    (perO AA M M').FG := by
  classical
  obtain ⟨s, hs⟩ := h.1.fg
  let ev : HomE E a b →ₗ[𝓞 E] (s → Sp E b) :=
    { toFun := fun x i => x i.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective ev := by
    intro x y hxy
    have h1 : Submodule.span E (s : Set (Sp E a)) = ⊤ := by
      rw [← h.1.span_eq_top, ← hs, Submodule.span_span_of_tower]
    exact LinearMap.ext_on h1 fun i hi => congrFun hxy ⟨i, hi⟩
  have hfg : (homO M M').FG := by
    refine Submodule.fg_of_fg_map_injective ev hinj ?_
    have h2 : (Submodule.pi Set.univ fun _ : s => M').FG := Submodule.fg_pi fun _ => h'.1.fg
    refine h2.of_le ?_
    rintro _ ⟨x, hx, rfl⟩ i _
    exact hx _ (hs ▸ Submodule.subset_span i.2)
  have := hA.map₂ ((LinearMap.lsmul E (HomE E a b)).restrictScalars₁₂ (𝓞 E) (𝓞 E)) hfg
  rw [Submodule.map₂_eq_span_image2] at this
  unfold perO
  convert this using 2
  ext z
  simp [Set.mem_smul, eq_comm]

theorem idx_formula (hU : ∀ P ∈ S, localization₂ P.asIdeal AA = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E)) (hA : AA ≠ ⊥)
    {M₁ M₂ : Submodule (𝓞 E) (Sp E a)} {M₁' M₂' : Submodule (𝓞 E) (Sp E b)} (h₁ : IsSdLat M₁) (h₂ : IsSdLat M₂)
    (h₁' : IsSdLat M₁') (h₂' : IsSdLat M₂') (h : Dom S (perO AA M₁ M₁') (perO AA M₂ M₂')) :
    (((perO AA M₂ M₂').toAddSubgroup.relIndex (perO AA M₁ M₁').toAddSubgroup : ℕ) : ℝ) =
      ∏ P ∈ S, ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (volExp P M₁ M₁' - volExp P M₂ M₂') := by
  rw [GlobalTheory.ThetaMove.relIndex_eq_prod_locP E _ S _ _ (full_per h₁ h₁' hA) (full_per h₂ h₂' hA) h, Nat.cast_prod]
  refine Finset.prod_congr rfl fun P hP => ?_
  have hle := h.1 P hP
  rw [(GlobalTheory.ThetaMove.PeriodComp.perO_components E a b AA).2.1 P _ _ h₁.1.fg (hU P hP), (GlobalTheory.ThetaMove.PeriodComp.perO_components E a b AA).2.1 P _ _ h₂.1.fg (hU P hP)] at hle ⊢
  have := GlobalTheory.IdxHom.relIndex_homAt E a b P M₁ M₂ M₁' M₂' h₁.1 h₂.1 h₁'.1 h₂'.1 hle
  simpa using congrArg (fun q : ℚ => (q : ℝ)) this

omit [StarRing E] in
theorem norm_pos (P : HeightOneSpectrum (𝓞 E)) : (0 : ℝ) < ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

theorem idx_ne (hU : ∀ P ∈ S, localization₂ P.asIdeal AA = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E)) (hA : AA ≠ ⊥)
    {M₁ M₂ : Submodule (𝓞 E) (Sp E a)} {M₁' M₂' : Submodule (𝓞 E) (Sp E b)} (h₁ : IsSdLat M₁) (h₂ : IsSdLat M₂)
    (h₁' : IsSdLat M₁') (h₂' : IsSdLat M₂') (h : Dom S (perO AA M₁ M₁') (perO AA M₂ M₂')) :
    (perO AA M₂ M₂').toAddSubgroup.relIndex (perO AA M₁ M₁').toAddSubgroup ≠ 0 := by
  have h1 := idx_formula hU hA h₁ h₂ h₁' h₂' h
  have h2 : (0 : ℝ) < ∏ P ∈ S, ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (volExp P M₁ M₁' - volExp P M₂ M₂') :=
    Finset.prod_pos fun P _ => zpow_pos (norm_pos P) _
  rw [← h1] at h2
  exact_mod_cast h2.ne'

theorem mem_homAt_iff {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)}
    (hU : ∀ P ∈ S, localization₂ P.asIdeal AA = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E)) (h : IsSdLat N) (x : HomE E a b) :
    x ∈ homAt S N N' ↔ ∀ P ∈ S, x ∈ localization₂ P.asIdeal (perO AA N N') := by
  refine forall₂_congr fun P hP => ?_
  rw [(GlobalTheory.ThetaMove.PeriodComp.perO_components E a b AA).2.1 P _ _ h.1.fg (hU P hP)]
  exact ⟨fun H Q hQ => by rw [Finset.mem_singleton.1 hQ]; exact H, fun H => H P (Finset.mem_singleton_self P)⟩

theorem mem_mulLat_iff {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)}
    (hU : ∀ P ∈ S, localization₂ P.asIdeal AA = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E)) (h : IsSdLat N) {c : ℕ} (hc : 0 < c) (x : HomE E a b) :
    x ∈ mulLat c (homAt S N N') ↔ ∀ P ∈ S, x ∈ localization₂ P.asIdeal (perO AA N (twist₂ N' c (expS S))) := by
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  have e : ∀ y : HomE E a b, (c : 𝓞 E) • y = (c : E) • y := fun y => by rw [← algebraMap_smul E, map_natCast]
  have h1 : x ∈ mulLat c (homAt S N N') ↔ (c : E)⁻¹ • x ∈ homAt S N N' := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [e, smul_smul, hcE] using hy
    · intro hx
      exact ⟨_, hx, by simp [e, smul_smul, hcE]⟩
  rw [h1, mem_homAt_iff hU h, ← GlobalTheory.ThetaMove.PeriodTwist.twO_perO E a b AA N N' c _ h.1.fg hc (expS_bound S)]
  refine forall₂_congr fun P hP => ?_
  rw [mem_localization_twist _ hc (expS_bound S), expS, if_pos hP, zpow_one]

theorem mem_divLat_iff {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)}
    (hU : ∀ P ∈ S, localization₂ P.asIdeal AA = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E)) (h : IsSdLat N) {c : ℕ} (hc : 0 < c) (x : HomE E a b) :
    x ∈ divLat c (homAt S N N') ↔ ∀ P ∈ S, x ∈ localization₂ P.asIdeal (perO AA N (twist₂ N' c fun Q => -expS S Q)) := by
  have h1 : x ∈ divLat c (homAt S N N') ↔ (c : E) • x ∈ homAt S N N' := by
    change (c : 𝓞 E) • x ∈ homAt S N N' ↔ _
    rw [← algebraMap_smul E, map_natCast]
  rw [h1, mem_homAt_iff hU h, ← GlobalTheory.ThetaMove.PeriodTwist.twO_perO E a b AA N N' c _ h.1.fg hc negS_bound]
  refine forall₂_congr fun P hP => ?_
  rw [mem_localization_twist _ hc negS_bound, expS, if_pos hP]
  simp

end Lattices

section Analytic

variable {X : Fields} {A : Amb X} {a b : ℕ} {S : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem analytic_opU {ι : Type} [Fintype ι] (H : Sesq (VCx ι a b)) (x : VCx ι a b) {F : VCx ι a b → ℂ}
    (hF : AnalyticOnNhd ℂ F Set.univ) : AnalyticOnNhd ℂ (opU H x F) Set.univ := by
  intro z _
  have h1 : AnalyticAt ℂ (fun z => F (z + x)) z :=
    AnalyticAt.comp (f := fun z => z + x) (hF _ (Set.mem_univ _)) (analyticAt_id.add analyticAt_const)
  have h2 : AnalyticAt ℂ (fun z => H z x) z := (LinearMap.toContinuousLinearMap (H.flip x)).analyticAt z
  exact h1.mul ((analyticAt_const.mul h2).sub analyticAt_const).cexp

theorem e_eq (hA : Moves A a b) {N : Submodule (𝓞 X.E) (Sp X.E a)} {N' : Submodule (𝓞 X.E) (Sp X.E b)} (h : IsSdLat N) (h' : IsSdLat N') :
    A.e a b N N' = fun z => A.chiF a b N N' * vac A N N' z := by
  funext z
  rw [vac, mul_inv_cancel_left₀ (hA.2.2.2.2.1 N N' h h').1]

theorem analytic_thInd (hA : Moves A a b) {N : Submodule (𝓞 X.E) (Sp X.E a)} {N' : Submodule (𝓞 X.E) (Sp X.E b)} (h : IsSdLat N)
    (h' : IsSdLat N') (c : ℕ) (x : HomE X.E a b) : AnalyticOnNhd ℂ (A.thInd S N N' c x) Set.univ := by
  have he : AnalyticOnNhd ℂ (A.e a b N N') Set.univ := by
    rw [e_eq hA h h']
    exact analyticOnNhd_const.mul (hA.2.2.2.2.1 N N' h h').2.1.1
  refine analyticOnNhd_const.mul (analyticOnNhd_const.mul (analytic_opU _ _ ?_))
  exact Finset.analyticOnNhd_fun_sum _ fun y _ => analyticOnNhd_const.mul (analytic_opU _ _ he)

theorem xiInd_mul {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (vol : ℝ) (M : AddSubgroup V) (SA SB : Finset V)
    (k : ℂ) (θ : V → ℂ) (s z : V) : xiInd H α vol M SA SB (fun w => k * θ w) s z = k * xiInd H α vol M SA SB θ s z := by
  simp only [xiInd, xiS, sumU, opU, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem thInd_eq (hA : Moves A a b) (hS : ∀ P ∈ S, conjPrime₂ P ∉ S) (hU : A.AAUnit S)
    {N G : Submodule (𝓞 X.E) (Sp X.E a)} {N' G' : Submodule (𝓞 X.E) (Sp X.E b)} (h : IsSdLat N) (h' : IsSdLat N') (g : IsSdLat G)
    (g' : IsSdLat G') {c : ℕ} (hc : 0 < c) (hD : Dom S (perO A.AA G G') (perO A.AA N (twist₂ N' c (expS S)))) {x t : HomE X.E a b}
    (ht : t ∈ perO A.AA G G') (htx : t - x ∈ mulLat c (homAt S N N')) (z : VCx X.Tau a b) :
    (A.chiF a b N N')⁻¹ * A.thInd S N N' c x z =
      ((Real.sqrt ((perO A.AA N (twist₂ N' c (expS S))).toAddSubgroup.relIndex (perO A.AA N N').toAddSubgroup : ℕ) : ℝ) : ℂ)⁻¹ *
        (alV A.d A.sc (embH (X.embC A.σ₀) A.δ t) *
          opU (Formalism.L2.Ker.HV A.sc) (-(embH (X.embC A.σ₀) A.δ t)) (vac A N (twist₂ N' c (expS S))) z) := by
  obtain ⟨hδ, hτ, hfg, hne, hv, hm, -⟩ := id hA
  obtain ⟨tw, tw'⟩ := GlobalTheory.ThetaMove.TwistSd.isSdLat_twO_expS X.E b N' c S hS h' hc
  have inj := embH_injective (a := a) (b := b) (X.embC A.σ₀) hδ
  have hB : BC (X.embC A.σ₀) A.δ A.AA S N N' c = lam A N (twist₂ N' c (expS S)) := by
    unfold BC halfBO
    rw [GlobalTheory.ThetaMove.PeriodTwist.twO_perO X.E a b A.AA N N' c _ h.1.fg hc (expS_bound S)]
    rfl
  have hAC : AC (X.embC A.σ₀) A.δ A.AA S N N' c = lam A N (twist₂ N' c fun Q => -expS S Q) := by
    unfold AC halfAO
    rw [GlobalTheory.ThetaMove.PeriodTwist.twO_perO X.E a b A.AA N N' c _ h.1.fg hc negS_bound]
    rfl
  have d1 : Dom S (perO A.AA N (twist₂ N' c fun Q => -expS S Q)) (perO A.AA N N') := dom_per h h (Dom.refl _ _) (tw_dom _ hc)
  have d2 : Dom S (perO A.AA N N') (perO A.AA N (twist₂ N' c (expS S))) := dom_per h h (Dom.refl _ _) (dom_tw _ hc)
  have hvol := GlobalTheory.ThetaMove.VolumePos.volC_pos X.E a b A.AA S N N' h.1.fg h'.1.fg h.1.span_eq_top h'.1.span_eq_top hfg hne
  have i1 : relIdx (lam A N (twist₂ N' c (expS S))) (lam A N N') =
      (perO A.AA N (twist₂ N' c (expS S))).toAddSubgroup.relIndex (perO A.AA N N').toAddSubgroup :=
    AddSubgroup.relIndex_map_map_of_injective _ _ inj
  have i2 : relIdx (lam A N N') (lam A N (twist₂ N' c (expS S))) ≠ 0 := by
    have f1 : (lam A N (twist₂ N' c (expS S))).FG := by
      have f2 : Module.Finite (𝓞 X.E) (perO A.AA N (twist₂ N' c (expS S))) := Module.Finite.iff_fg.2 (perO_fg h tw hfg)
      have f3 : Module.Finite ℤ (perO A.AA N (twist₂ N' c (expS S))) := Module.Finite.trans (𝓞 X.E) _
      have f4 : (perO A.AA N (twist₂ N' c (expS S))).toAddSubgroup.FG :=
        (AddGroup.fg_iff_addSubgroup_fg _).1 (Module.Finite.iff_addGroup_fg.1 f3)
      obtain ⟨T, hT⟩ := f4
      classical
      exact ⟨T.image (embH (X.embC A.σ₀) A.δ), by rw [Finset.coe_image, ← AddMonoidHom.map_closure, hT]; rfl⟩
    have := GlobalTheory.ThetaInter.finite_quot (A₁ := lam A N N') f1 (by
      rintro _ ⟨y, -, rfl⟩
      obtain ⟨n, hn, hy⟩ := full_per h h' hne y
      exact ⟨n, hn, _, hy, by rw [Nat.cast_smul_eq_nsmul, map_nsmul]⟩)
    exact AddSubgroup.index_ne_zero_of_finite
  have hsup : lam A N N' ≤ (lam A N N' ⊓ lam A N (twist₂ N' c fun Q => -expS S Q)) ⊔ (lam A N N' ⊓ lam A N (twist₂ N' c (expS S))) := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 (d1.le_sup d2 (full_per h tw' hne) (full_per h h' hne) (full_per h tw hne) hy)
    rw [map_add]
    exact AddSubgroup.add_mem_sup ⟨⟨_, hu.1, rfl⟩, _, hu.2, rfl⟩ ⟨⟨_, hw.1, rfl⟩, _, hw.2, rfl⟩
  have key := GlobalTheory.XiIndZero.xiInd_eq_inter _ (Formalism.L2.Ker.HV A.sc) (alV A.d A.sc) _ _ _ _ (vac A N N') (embH (X.embC A.σ₀) A.δ (A.liftW S N N' c x)) z
    (isHerm_HV _) (hv N _ h tw).2.2.1 (hv N _ h tw).2.2.2 (hv N N' h h').2.2.1 (hv N N' h h').2.1.2 hvol hsup
    (i1 ▸ idx_ne hU hne h h h' tw d2) i2
  rw [← GlobalTheory.ThetaMove.LiftTranslate.signed_liftW_eq X A a b S N G N' G' c x t _ hA hS hU h h' g g' hc hD ht htx (hv N _ h tw).2.1.2 z, hm N N' _ h h' tw, ← i1]
  refine Eq.trans ?_ key
  unfold Amb.thInd
  rw [hB, hAC, e_eq hA h h', xiInd_mul, mul_left_comm, inv_mul_cancel_left₀ (hv N N' h h').1]

theorem latSum_const_mul {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W] [Module (𝓞 E) W] (As L : Submodule (𝓞 E) W)
    (k : ℂ) (F : W → ℂ) : latSum As L (fun t => k * F t) = k * latSum As L F := by
  unfold latSum
  rw [mul_finsum]

theorem pair_eq (hA : Moves A a b) (hS : ∀ P ∈ S, conjPrime₂ P ∉ S) (hU : A.AAUnit S)
    {N F G : Submodule (𝓞 X.E) (Sp X.E a)} {N' F' G' : Submodule (𝓞 X.E) (Sp X.E b)} (h : IsSdLat N) (h' : IsSdLat N')
    (f : IsSdLat F) (f' : IsSdLat F') (g : IsSdLat G) (g' : IsSdLat G') {cA c : ℕ} (hcA : 0 < cA) (hc : 0 < c)
    (dG : Dom S N G) (dF : Dom S F N) (dG' : Dom S G' (twist₂ N' cA fun Q => -expS S Q)) (dF' : Dom S (twist₂ N' c (expS S)) F')
    {Ξ : HomE X.E a b → ℂ} (hΞ : InBox S cA c N N' Ξ) (z : VCx X.Tau a b) :
    latSum (divLat cA (homAt S N N')) (mulLat c (homAt S N N')) (fun x => Ξ x * ((A.chiF a b N N')⁻¹ * A.thInd S N N' c x z)) =
      ((Real.sqrt (∏ P ∈ S, ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (volExp P N N' - volExp P F F')) : ℝ) : ℂ)⁻¹ *
        cosSum (Formalism.L2.Ker.HV A.sc) (alV A.d A.sc) (embH (X.embC A.σ₀) A.δ) (perO A.AA G G') (perO A.AA F F') (vac A F F') Ξ z := by
  obtain ⟨hδ, hτ, hfg, hne, hv, hm, hm'⟩ := id hA
  obtain ⟨tw, -⟩ := GlobalTheory.ThetaMove.TwistSd.isSdLat_twO_expS X.E b N' c S hS h' hc
  obtain ⟨-, tw'⟩ := GlobalTheory.ThetaMove.TwistSd.isSdLat_twO_expS X.E b N' cA S hS h' hcA
  have inj := embH_injective (a := a) (b := b) (X.embC A.σ₀) hδ
  have d0 : Dom S (perO A.AA G G') (perO A.AA N (twist₂ N' cA fun Q => -expS S Q)) := dom_per g h dG dG'
  have d1 : Dom S (perO A.AA N (twist₂ N' cA fun Q => -expS S Q)) (perO A.AA N N') := dom_per h h (Dom.refl _ _) (tw_dom _ hcA)
  have d2 : Dom S (perO A.AA N N') (perO A.AA N (twist₂ N' c (expS S))) := dom_per h h (Dom.refl _ _) (dom_tw _ hc)
  have d3 : Dom S (perO A.AA N (twist₂ N' c (expS S))) (perO A.AA N F') := dom_per h h (Dom.refl _ _) dF'
  have d4 : Dom S (perO A.AA N F') (perO A.AA F F') := dom_per h f dF (Dom.refl _ _)
  have dB := (d0.trans d1).trans d2
  have mC := fun x => mem_mulLat_iff (N' := N') hU h hc x
  have mD := fun x => mem_divLat_iff (N' := N') hU h hcA x
  have r1 := GlobalTheory.latSum_reindex_of_le_sup X.E _ (divLat cA (homAt S N N')) (mulLat c (homAt S N N')) (perO A.AA G G') (perO A.AA N (twist₂ N' c (expS S)))
    (fun x => Ξ x * ((A.chiF a b N N')⁻¹ * A.thInd S N N' c x z))
    (fun t => ((Real.sqrt ((perO A.AA N (twist₂ N' c (expS S))).toAddSubgroup.relIndex (perO A.AA N N').toAddSubgroup : ℕ) : ℝ) : ℂ)⁻¹ *
      (Ξ t * (alV A.d A.sc (embH (X.embC A.σ₀) A.δ t) *
          opU (Formalism.L2.Ker.HV A.sc) (-(embH (X.embC A.σ₀) A.δ t)) (vac A N (twist₂ N' c (expS S))) z)))
    (fun x hx => (mD x).2 fun P hP => (d1.trans d2).1 P hP ((mC x).1 hx P hP))
    (fun t ht => ⟨fun hb => (mC t).2 fun P _ => mem_localization_of_mem P hb, fun hb => mem_of_locP fun Q => by
      by_cases hQ : Q ∈ S
      · exact (mC t).1 hb Q hQ
      · exact dB.2 Q hQ (mem_localization_of_mem Q ht)⟩)
    (fun x hx => by
      obtain ⟨t, h1, h2⟩ := ((full_per g g' hne).inf (full_per h tw hne)).approx S x
      simp only [localization_inf, Submodule.mem_inf] at h1 h2
      refine Submodule.mem_sup.2 ⟨t, mem_of_locP fun Q => ?_, -(t - x), neg_mem ((mC _).2 fun P hP => (h1 P hP).2), by abel⟩
      by_cases hQ : Q ∈ S
      · simpa using add_mem (h1 Q hQ).1 (d0.1 Q hQ ((mD x).1 hx Q hQ))
      · exact (h2 Q hQ).1)
    (fun x _ t ht htx => by
      have := hΞ.2 x _ htx
      rw [add_sub_cancel] at this
      simp only [thInd_eq hA hS hU h h' g g' hc dB ht htx z, this]
      ring)
    (fun t _ ht => by
      have : Ξ t = 0 := by_contra fun h0 => ht (hΞ.1 t h0)
      simp [this])
  have s1 := GlobalTheory.ThetaMove.Step.cosSum_inter X.E _ _ (Formalism.L2.Ker.HV A.sc) (alV A.d A.sc) (embH (X.embC A.σ₀) A.δ) (perO A.AA G G')
    (perO A.AA N (twist₂ N' c (expS S))) (perO A.AA N F') (vac A N F') Ξ (isHerm_HV _) inj (hv _ _ g g').2.2.1 (hv _ _ g g').2.2.2
    (hv _ _ h tw).2.2.1 (hv _ _ h tw).2.2.2 (hv _ _ h f').2.1.2 (dB.inf_le d3)
    (dB.le_sup d3 (full_per g g' hne) (full_per h tw hne) (full_per h f' hne)) (idx_ne hU hne g h g' f' (dB.trans d3))
    (fun t _ y hy => hΞ.2 t y ((mC y).2 fun P _ => mem_localization_of_mem P hy.1)) z
  have s2 := GlobalTheory.ThetaMove.Step.cosSum_inter X.E _ _ (Formalism.L2.Ker.HV A.sc) (alV A.d A.sc) (embH (X.embC A.σ₀) A.δ) (perO A.AA G G')
    (perO A.AA N F') (perO A.AA F F') (vac A F F') Ξ (isHerm_HV _) inj (hv _ _ g g').2.2.1 (hv _ _ g g').2.2.2
    (hv _ _ h f').2.2.1 (hv _ _ h f').2.2.2 (hv _ _ f f').2.1.2 ((dB.trans d3).inf_le d4)
    ((dB.trans d3).le_sup d4 (full_per g g' hne) (full_per h f' hne) (full_per f f' hne))
    (idx_ne hU hne g f g' f' ((dB.trans d3).trans d4))
    (fun t _ y hy => hΞ.2 t y ((mC y).2 fun P hP => d3.1 P hP (mem_localization_of_mem P hy.1))) z
  have m1 := hm N F' _ h f' tw
  have m2 := hm' F N F' f h f'
  have s1' : cosSum (Formalism.L2.Ker.HV A.sc) (alV A.d A.sc) (embH (X.embC A.σ₀) A.δ) (perO A.AA G G') (perO A.AA N (twist₂ N' c (expS S)))
      (vac A N (twist₂ N' c (expS S))) Ξ z = _ := m1 ▸ s1
  have s2' : cosSum (Formalism.L2.Ker.HV A.sc) (alV A.d A.sc) (embH (X.embC A.σ₀) A.δ) (perO A.AA G G') (perO A.AA N F')
      (vac A N F') Ξ z = _ := m2 ▸ s2
  rw [r1, latSum_const_mul]
  change _ * cosSum (Formalism.L2.Ker.HV A.sc) (alV A.d A.sc) (embH (X.embC A.σ₀) A.δ) (perO A.AA G G') (perO A.AA N (twist₂ N' c (expS S)))
      (vac A N (twist₂ N' c (expS S))) Ξ z = _
  rw [s1', s2', ← mul_assoc, ← mul_assoc, ← mul_inv, ← mul_inv, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
    ← Real.sqrt_mul (Nat.cast_nonneg _), ← Real.sqrt_mul (by positivity), idx_formula hU hne h h h' tw d2,
    idx_formula hU hne h h tw f' d3, idx_formula hU hne h f f' f' d4, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  congr 4
  refine Finset.prod_congr rfl fun P _ => ?_
  rw [← zpow_add₀ (norm_pos P).ne', ← zpow_add₀ (norm_pos P).ne']
  congr 1
  ring

theorem core (hA : Moves A a b) (hS : ∀ P ∈ S, conjPrime₂ P ∉ S) (hU : A.AAUnit S)
    {N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E a)} {N₁' N₂' : Submodule (𝓞 X.E) (Sp X.E b)} (h₁ : IsSdLat N₁) (h₂ : IsSdLat N₂)
    (h₁' : IsSdLat N₁') (h₂' : IsSdLat N₂')
    (ag : ∀ Q, Q ∉ S → conjPrime₂ Q ∉ S → localization₂ Q.asIdeal N₁ = localization₂ Q.asIdeal N₂)
    (ag' : ∀ Q, Q ∉ S → conjPrime₂ Q ∉ S → localization₂ Q.asIdeal N₁' = localization₂ Q.asIdeal N₂') {cA c : ℕ} (hcA : 0 < cA) (hc : 0 < c)
    {Ξ : HomE X.E a b → ℂ} (b₁ : InBox S cA c N₁ N₁' Ξ) (b₂ : InBox S cA c N₂ N₂' Ξ) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ2 : ρ ^ 2 = ∏ P ∈ S, ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (volExp P N₂ N₂' - volExp P N₁ N₁')) (z : VCx X.Tau a b) :
    latSum (divLat cA (homAt S N₁ N₁')) (mulLat c (homAt S N₁ N₁'))
        (fun x => Ξ x * ((A.chiF a b N₁ N₁')⁻¹ * A.thInd S N₁ N₁' c x z)) =
      (ρ : ℂ) * latSum (divLat cA (homAt S N₂ N₂')) (mulLat c (homAt S N₂ N₂'))
        (fun x => Ξ x * ((A.chiF a b N₂ N₂')⁻¹ * A.thInd S N₂ N₂' c x z)) := by
  obtain ⟨G, F, g, f, dG₁, dG₂, dF₁, dF₂⟩ := GlobalTheory.ThetaMove.CommonRef.common_refinement X.E a N₁ N₂ S hS h₁ h₂ ag
  obtain ⟨F', -, f', -, dF₁', dF₂', -, -⟩ := GlobalTheory.ThetaMove.CommonRef.common_refinement X.E b _ _ S hS (GlobalTheory.ThetaMove.TwistSd.isSdLat_twO_expS X.E b N₁' c S hS h₁' hc).1
    (GlobalTheory.ThetaMove.TwistSd.isSdLat_twO_expS X.E b N₂' c S hS h₂' hc).1 fun Q h h' => tw_congr hc (expS_bound S) (ag' Q h h')
  obtain ⟨-, G', -, g', -, -, dG₁', dG₂'⟩ := GlobalTheory.ThetaMove.CommonRef.common_refinement X.E b _ _ S hS (GlobalTheory.ThetaMove.TwistSd.isSdLat_twO_expS X.E b N₁' cA S hS h₁' hcA).2
    (GlobalTheory.ThetaMove.TwistSd.isSdLat_twO_expS X.E b N₂' cA S hS h₂' hcA).2 fun Q h h' => tw_congr hcA negS_bound (ag' Q h h')
  rw [pair_eq hA hS hU h₁ h₁' f f' g g' hcA hc dG₁ dF₁ dG₁' dF₁' b₁, pair_eq hA hS hU h₂ h₂' f f' g g' hcA hc dG₂ dF₂ dG₂' dF₂' b₂,
    ← mul_assoc]
  congr 1
  have e : ∏ P ∈ S, ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (volExp P N₂ N₂' - volExp P F F') =
      ρ ^ 2 * ∏ P ∈ S, ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (volExp P N₁ N₁' - volExp P F F') := by
    rw [hρ2, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [← zpow_add₀ (norm_pos P).ne']
    congr 1
    ring
  rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hρ.le, Complex.ofReal_mul, mul_inv,
    mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.2 hρ.ne')]

end Analytic

section Final

theorem mUof_conj {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (u : Pr.Word) (σ₀ : X.K →+* ℂ)
    (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.FromHecke W σ₀) (hsel : IsSel X sel) (hT : Pr.T u ∈ S) (hg : ∀ k, Pr.g k ∈ S)
    (i : ℕ) (hi : i < R.m) (P : HeightOneSpectrum (𝓞 X.E)) (hP : P ∈ Pr.vT u) :
    mUof Ch mu i (conjPrime₂ P) = (mUof Ch mu i P)⁻¹ := by
  classical
  have hPS : P ∈ Sall sel mu u := Finset.mem_union_left _ hP
  obtain ⟨h1, -, -, h4⟩ := GlobalTheory.ThetaMove.BadPrimes.bad_primes X Pr sel S mu u hX hPr hsel hT hg P hPS
  have hne : conjPrime₂ P ≠ P := fun e => h1 (e.symm ▸ hPS)
  have hTP := h4.2 hP
  have hv := (GlobalTheory.ThetaMove.split_of_conj_ne₂ X P (P.under (𝓞 X.F)) hX hne rfl).1
  have hTc : ((Pr.T u : ℕ) : 𝓞 X.E) ∈ (conjPrime₂ P).asIdeal := by
    rw [mem_conjP, map_natCast]
    exact hTP
  have hgT : ∀ Q : HeightOneSpectrum (𝓞 X.E), ((Pr.T u : ℕ) : 𝓞 X.E) ∈ Q.asIdeal → ∀ k, ((Pr.g k : ℕ) : 𝓞 X.E) ∉ Q.asIdeal := by
    intro Q hQ k hk
    have hc : IsCoprime ((Pr.T u : ℕ) : 𝓞 X.E) ((Pr.g k : ℕ) : 𝓞 X.E) :=
      Nat.Coprime.cast ((Nat.coprime_primes (hPr.T_prime u) (hPr.g_prime k)).2 (hPr.T_ne_g u k))
    obtain ⟨x, y, hxy⟩ := hc
    exact Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hxy ▸ add_mem (Q.asIdeal.mul_mem_left _ hQ) (Q.asIdeal.mul_mem_left _ hk)))
  obtain ⟨m0, eta, ht⟩ := hCh
  have e1 : Ch.muVal ⟨i, hi⟩ (conjPrime₂ P) = (Ch.muVal ⟨i, hi⟩ P)⁻¹ := by
    have h5 := GlobalTheory.HeckeSplit.val_eq_inv_of_split X.F X.E (m0 ⟨i, hi⟩) _ P (conjPrime₂ P) (ht.mu0 _).triv ((ht.mu0 _).unr _ (hgT _ hTP))
      ((ht.mu0 _).unr _ (hgT _ hTc)) hne.symm hv
    apply Units.ext
    apply σ₀.injective
    rw [ht.muVal _ _ (hgT _ hTc), h5, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_inv₀, ht.muVal _ _ (hgT _ hTP)]
  have hplc : Formalism.EigenvalueLevelCeiling.plc (P.under (𝓞 X.F)) = Pr.T u := by
    have h6 : ((Pr.T u : ℕ) : 𝓞 X.F) ∈ (P.under (𝓞 X.F)).asIdeal := by
      change _ ∈ Ideal.comap _ _
      rw [Ideal.mem_comap, map_natCast]
      exact hTP
    have h7 : ((Pr.T u : ℕ) : 𝓞 X.F ⧸ (P.under (𝓞 X.F)).asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
      exact h6
    have := (P.under (𝓞 X.F)).isPrime
    exact CharP.ringChar_of_prime_eq_zero (hPr.T_prime u) h7
  have hmu := mu.2
  simp only [tupGrp, Subgroup.mem_inf, Subgroup.mem_iInf, mem_kills] at hmu
  have e2 := GlobalTheory.UnifConj.unifVal_conj X.F X.E X.K (mu : Chr X.F X.E X.K) _ P (conjPrime₂ P) hmu.1.1.2
    (hmu.2 _ fun hgood => hgood.2.2 (hplc ▸ hT)) hne.symm hv
  unfold mUof
  rw [dif_pos hi, dif_pos hi, e1, e2, mul_inv]

def EqAll : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsChi D χ → B.EqP χ

def LatFactsAll : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), TaylorLogMetric.IsCurveIdeal D cc → B.LatAll

def ThZeroAll : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (a b : ℕ), TaylorLogMetric.IsCurveIdeal D cc → Even a → Even b → B.ThZeroMem a b

theorem kerOf_eq {X : Fields} (A : Amb X) {a b : ℕ} (Sa SB : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (mI : SB → X.E → X.K)
    (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (fr : Frs X.E a SB) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (fr' : Frs X.E b SB)
    (Ξ : HomE X.E a b → X.K)
    [Fintype (↥(divLat cA (homAt Sa N N')) ⧸ (mulLat cB (homAt Sa N N')).comap (divLat cA (homAt Sa N N')).subtype)] :
    kerOf (thDistC A Sa SB (cA * cB) sel mU mI lam lam' n) Sa cA cB N fr N' fr' Ξ =
      (muInvDet sel SB mU mI N fr * (muInvDet sel SB mU mI N' fr')⁻¹) •
        ∑ q : ↥(divLat cA (homAt Sa N N')) ⧸ (mulLat cB (homAt Sa N N')).comap (divLat cA (homAt Sa N N')).subtype,
          Ξ (Function.surjInv (Submodule.Quotient.mk_surjective _) q : ↥(divLat cA (homAt Sa N N'))) •
            jetOp lam lam' (A.jetK Sa N N' cB
              (Function.surjInv (Submodule.Quotient.mk_surjective _) q : ↥(divLat cA (homAt Sa N N')))) n := by
  unfold kerOf latSum
  rw [finsum_eq_sum_of_fintype, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  generalize Function.surjInv (Submodule.Quotient.mk_surjective _) q = x
  have hx : (x : HomE X.E a b) ∈ divLat (cA * cB) (homAt Sa N N') := by
    change ((cA * cB : ℕ) : 𝓞 X.E) • (x : HomE X.E a b) ∈ homAt Sa N N'
    rw [Nat.cast_mul, mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ x.2
  simp only [thDistC]
  rw [if_pos ⟨Dvd.intro_left _ rfl, hx⟩, smul_comm]

end Final

end GlobalTheory.ThetaMove
