import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFinCombOfIsThetaAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDatumCarriedBackToBaseVacuum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawCombinationsOperatorDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlacesIffPlaceSetProd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOver
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StepComb

variable {D : D7}

theorem idem_mem_idAt {es : AE D} {PP : Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt es PP) :
    es ∈ GlobalTheory.FinPl.idAt D (· = PP.under (𝓞 D.host.F)) := by
  have h' := h
  obtain ⟨⟨a1, a2, w, ε, hε, a3⟩, -⟩ := h'
  have hw := GlobalTheory.IdemUnder.under_eq_of_isIdemAt D es PP w ε h hε a3
  have hε' := hε
  obtain ⟨α, rfl, -, h0⟩ := hε'
  have hm : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) ∈ GlobalTheory.FinPl.idAt D (· = w) :=
    GlobalTheory.FinPl.LatMem.tmul_mem_idAt (P := (· = w)) (fun v hv => h0 v hv) 1
  have e1 : es = es * (es + cA D es) := by rw [mul_add, a1, a2, add_zero]
  rw [e1, a3, hw]
  exact Ideal.mul_mem_left _ _ hm

theorem idemSum_mem_idAt {e : AE D} {Z : Finset (Pl D.host.E)} (h : IsIdemSum e Z) :
    e ∈ GlobalTheory.FinPl.idAt D (fun p => ∃ PP ∈ Z, p = PP.under (𝓞 D.host.F)) := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  exact Ideal.sum_mem _ fun PP hPP =>
    GlobalTheory.FinPl.KSplit.idAt_mono (fun w hw => ⟨PP, hPP, hw⟩) (idem_mem_idAt (hes PP hPP))

theorem mxAt_of_mem_half {S T : HSp D} {a : AE D} {P : GlobalTheory.FinPl.Pl D → Prop} (ha : a ∈ GlobalTheory.FinPl.idAt D P)
    {u : WO S T} (hu : u ∈ GlobalTheory.PlaceModel.half S T a) : GlobalTheory.FinPl.MxAt P u := by
  intro i j
  rw [← (GlobalTheory.PlaceModel.isHalf_iff S T).2 hu i j]
  exact Ideal.mul_mem_right _ _ ha

theorem isSBHalf_stepDatumQ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D))
    (βT : GL (Fin T.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank) (χ ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (Q : Finset (Pl D.host.E)) (e : AE D) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (he : IsIdemSum e (L.Pg ∪ Q)) :
    IsSBHalf e (latO S T ΛS ΛT fun _ => True) (fun x : WO S T =>
      if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then
        omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ Q L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x))
      else 0) := by
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO hS.1 hT.1 βS βT
  exact GlobalTheory.PlaceDatum.isSBHalf_of_red e _ (frMapO S T βS βT) (GlobalTheory.PlaceDatum.frMapO_add βS βT)
    (GlobalTheory.PlaceDatum.exists_den_frMapO hS.1.fg hT.1.fg βS βT)
    ⟨K, hK, fun t ht => hC t (GlobalTheory.PlaceDatum.infPart_of_half hinf ht)⟩ (L.Pg ∪ Q)
    (fun y => omegaG L χ y * omegaQ Q L.r ξ 1 y) fun y y' h => by
      rw [GlobalTheory.PlaceDatum.omegaG_congr L χ y y' fun PP hP => h PP (Finset.mem_union_left _ hP),
        GlobalTheory.PlaceDatum.omegaQ_congr Q L.r ξ 1 y y' fun PP hP => h PP (Finset.mem_union_right _ hP)]

theorem comb_add' (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (c c' : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (c + c') f = comb ψ S T c f + comb ψ S T c' f := by
  rw [GlobalTheory.FinPl.DatumBack.comb_eq_lc, GlobalTheory.FinPl.DatumBack.comb_eq_lc, GlobalTheory.FinPl.DatumBack.comb_eq_lc, map_add]

theorem comb_smul' (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (a : ℂ) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (a • c) f = a • comb ψ S T c f := by
  rw [GlobalTheory.FinPl.DatumBack.comb_eq_lc, GlobalTheory.FinPl.DatumBack.comb_eq_lc, map_smul]

theorem comb_zero' (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (f : WO S T → ℂ) :
    comb ψ S T 0 f = 0 := by
  rw [GlobalTheory.FinPl.DatumBack.comb_eq_lc, map_zero]

theorem comb_single' (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (u : WO S T) (a : ℂ) (f : WO S T → ℂ) :
    comb ψ S T (Finsupp.single u a) f = a • heisO ψ S T u f := by
  rw [GlobalTheory.FinPl.DatumBack.comb_eq_lc, Finsupp.linearCombination_single]

theorem mem_of_mem_support_add {S T : HSp D} {H : Set (WO S T)} {c c' : WO S T →₀ ℂ} (hc : ∀ u ∈ c.support, u ∈ H)
    (hc' : ∀ u ∈ c'.support, u ∈ H) : ∀ u ∈ (c + c').support, u ∈ H := by
  intro u hu
  by_contra hn
  have h1 : c u = 0 := by
    by_contra h
    exact hn (hc u (Finsupp.mem_support_iff.2 h))
  have h2 : c' u = 0 := by
    by_contra h
    exact hn (hc' u (Finsupp.mem_support_iff.2 h))
  exact Finsupp.mem_support_iff.1 hu (by rw [Finsupp.add_apply, h1, h2, add_zero])

theorem mem_of_mem_support_smul {S T : HSp D} {H : Set (WO S T)} (a : ℂ) {c : WO S T →₀ ℂ}
    (hc : ∀ u ∈ c.support, u ∈ H) : ∀ u ∈ (a • c).support, u ∈ H := by
  intro u hu
  by_contra hn
  have h1 : c u = 0 := by
    by_contra h
    exact hn (hc u (Finsupp.mem_support_iff.2 h))
  exact Finsupp.mem_support_iff.1 hu (by rw [Finsupp.smul_apply, h1, smul_zero])

set_option maxHeartbeats 1000000 in
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.PlaceModel GlobalTheory.PlaceDatum in

theorem exists_comb_of_isThetaAt {S T : HSp D} (ψ : AddChar (AF D.host.F) ℂ)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (e : AE D) (f₀ Φ f : WO S T → ℂ) (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (he : e * e = e) (hec : e * cA D e = 0) (hinf : infPart D e = 0)
    (hΦ : IsSBHalf e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) Φ)
    (hθ : IsThetaAt ψ (symplO S T) (heisO ψ S T) e
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Φ f) :
    ∃ d : WO S T →₀ ℂ, (∀ u ∈ d.support, u ∈ half S T (e + cA D e)) ∧ f = comb ψ S T d f₀ := by
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hθ
  rw [hall Tm hTm]
  clear hall
  have hce : cA D e * e = 0 := by rw [mul_comm, hec]
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  have he' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he]
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ latO S T ΛS ΛT fun _ => True,
      a • u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T a := fun a ha u hu =>
    AddSubgroup.mem_inf.2 ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu, by rw [mem_half, smul_smul, ha]⟩
  have hLL' : ∀ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e,
      ∀ y ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), ψ (symplO S T u y) = 1 := fun u hu y hy =>
    (hdual u (infPart_of_half hinf ((isHalf_iff S T).2 hu.2))).1 hu.1 y hy.1
  have hX : ∀ x ∈ half S T e, (∀ y ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), ψ (symplO S T x y) = 1) →
      x ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e := fun x hx h => by
    refine ⟨(hdual x (infPart_of_half hinf ((isHalf_iff S T).2 hx))).2 fun u hu => ?_, hx⟩
    have := h _ (hsm _ he' u hu)
    rwa [← symplO_smul, (mem_half S T).1 hx] at this
  have hfin' : ∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧
      ∀ t ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, ∃ r ∈ R,
        ∃ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, t = r + k • u := fun k hk => by
    obtain ⟨R, hR, h⟩ := hfin k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, hsm e he u hu, ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]
  have hden : ∀ y ∈ half S T (cA D e), ∃ k : ℕ, 0 < k ∧ k • y ∈ (latO S T ΛS ΛT fun _ => True) := fun y hy =>
    exists_nsmul_mem_latO' hS.1 hT.1 y (infPart_of_half (infPart_cA hinf) ((isHalf_iff S T).2 hy))
  have tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S T => k • t := fun k hk a b hab => by
    rw [← inv_smul_nsmul S T hk a, ← inv_smul_nsmul S T hk b]
    exact congrArg _ hab
  have hb := isBichar_symplO S T ψ
  have hm : Φ ∈ waveSpan (fun x y : WO S T => ψ (symplO S T x y)) (half S T e) (half S T (cA D e))
      ((latO S T ΛS ΛT fun _ => True) ⊓ half S T e) := by
    obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
    exact mem_waveSpan hb inf_le_right inf_le_right hLL' hX (half_div S T e) (half_div S T _) tf hfin' Φ
      (fun t ht => (isHalf_iff S T).1 (h1 t ht)) k hk (fun u hu => h2 u hu.1 ((isHalf_iff S T).2 hu.2))
      fun t ht => ⟨h3 t ht, (half S T e).nsmul_mem ((isHalf_iff S T).1 (h1 t ht)) _⟩
  clear hΦ
  induction hm using Submodule.span_induction with
  | mem _ hh =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hh
    have s0 := GlobalTheory.isSBHalf_halfInd e (latO S T ΛS ΛT fun _ => True)
    have s1 : IsSBHalf e (latO S T ΛS ΛT fun _ => True)
        fun t => ψ (symplO S T t y) * halfInd e (latO S T ΛS ΛT fun _ => True) t := by
      obtain ⟨k, hk, hk'⟩ := hden y hy
      obtain ⟨a1, k', hk1, a2, a3⟩ := s0
      refine ⟨fun t ht => a1 t (right_ne_zero_of_mul ht), k * k', Nat.mul_pos hk hk1, fun u hu hh t => ?_,
        fun t ht => ?_⟩
      · have e1 : halfInd e (latO S T ΛS ΛT fun _ => True) (t + (k * k') • u) =
            halfInd e (latO S T ΛS ΛT fun _ => True) t := by
          rw [mul_nsmul]
          exact a2 _ (nsmul_mem hu k) ((isHalf_iff S T).2 (nsmul_mem ((isHalf_iff S T).1 hh) k)) t
        have e2 : ψ (symplO S T ((k * k') • u) y) = 1 := by
          rw [mul_nsmul']
          exact (hb.nsmul k _ y).trans
            (hLL' _ (nsmul_mem (AddSubgroup.mem_inf.2 ⟨hu, (isHalf_iff S T).1 hh⟩) k') _ ⟨hk', nsmul_mem hy k⟩)
        simp only [e1, symplO_add_left, AddChar.map_add_eq_mul, e2, mul_one]
      · rw [mul_nsmul']
        exact nsmul_mem (a3 t (right_ne_zero_of_mul ht)) k
    have e1 : wave (fun x y : WO S T => ψ (symplO S T x y)) ((latO S T ΛS ΛT fun _ => True) ⊓ half S T e) x y =
        fun t => (fun t => ψ (symplO S T t y) * halfInd e (latO S T ΛS ΛT fun _ => True) t) (t + x) := by
      rw [halfInd_eq_ind]; rfl
    have v1 := hTm.vac
    rw [one_smul] at v1
    rw [e1, hTm.trans _ s1 x ((isHalf_iff S T).2 hx), hTm.modul _ s0 y ((isHalf_iff S T).2 hy), v1]
    have hxy := heisL_heisL S T ψ x y f₀
    change heisO ψ S T x (heisO ψ S T y f₀) = ψ (symplOH S T x y) • heisO ψ S T (x + y) f₀ at hxy
    rw [hxy]
    refine ⟨Finsupp.single (x + y) (ψ (symplOH S T x y)), fun u hu => ?_, ?_⟩
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hu)]
      exact add_mem (GlobalTheory.FinPl.DatumBack.half_le_sum hce hx) (GlobalTheory.FinPl.DatumBack.half_le_sum' hec hy)
    · rw [comb_single']
  | zero =>
    exact ⟨0, fun u hu => absurd hu (Finsupp.notMem_support_iff.2 rfl), by rw [LinearMap.map_zero, comb_zero']⟩
  | add g g' _ _ hg hg' =>
    obtain ⟨c, hc, hc'⟩ := hg
    obtain ⟨c', hd, hd'⟩ := hg'
    refine ⟨c + c', mem_of_mem_support_add hc hd, ?_⟩
    rw [LinearMap.map_add, hc', hd', comb_add']
  | smul a g _ hg =>
    obtain ⟨c, hc, hc'⟩ := hg
    refine ⟨a • c, mem_of_mem_support_smul a hc, ?_⟩
    rw [LinearMap.map_smul, hc', comb_smul']

theorem exists_comb_of_isStepVecOf : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (LS : LevDat D.host.E ℂ S.rank) (χj : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (f₀ f : WO S T → ℂ), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ f₀ f → ∃ d : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt (fun p => ∃ PP ∈ LS.Pg ∪ Q, p = PP.under (𝓞 D.host.F)) d ∧ f = comb ψ S T d f₀ := by
  intro D ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ f₀ f hS hT _ _ hv
  obtain ⟨hvac, e, he, hθ⟩ := hv
  have hSB := isSBHalf_stepDatumQ S T ΛS ΛT βS βT LS χj ξ Q e hS hT he
  obtain ⟨d, hd, hf⟩ := exists_comb_of_isThetaAt ψ ΛS ΛT e f₀ _ f hvac.1 hS hT
    (GlobalTheory.PlaceDatum.idemSum_mul_self he) he.2 (GlobalTheory.PlaceDatum.infPart_idemSum he) hSB hθ
  have hI := idemSum_mem_idAt he
  exact ⟨d, fun u hu => mxAt_of_mem_half (add_mem hI (GlobalTheory.LastOpPf.cA_mem_idAt hI)) (hd u hu), hf⟩

end GlobalTheory.StepComb

end
