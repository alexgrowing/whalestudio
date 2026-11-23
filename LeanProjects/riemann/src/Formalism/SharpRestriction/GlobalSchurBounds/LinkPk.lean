import Formalism.SharpRestriction.GlobalSchurBounds.TopDensityNGeSixteen
import Formalism.LocalRingCardinality.Lemmas
import Formalism.SharpRestriction.GlobalSchurBounds.FrameCodeOfAdditive
import Formalism.SharpRestriction.GlobalSchurBounds.JointsL
import Formalism.SharpRestriction.GlobalSchurBounds.JointsF
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.SlopesMFOfCountFam
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.CMFieldLemmas

section Commens

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.MainNotions.Lnk

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory

section General

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]

theorem mem_of_locally (M : Submodule (𝓞 K) V) (x : V)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), ∃ s : 𝓞 K, s ∉ v.asIdeal ∧ s • x ∈ M) : x ∈ M := by
  let I : Ideal (𝓞 K) := M.comap (LinearMap.toSpanSingleton (𝓞 K) V x)
  have hI : ∀ a : 𝓞 K, a ∈ I ↔ a • x ∈ M := fun a => Iff.rfl
  have htop : I = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I hne
    have hm0 : m ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)
    obtain ⟨s, hs, hsx⟩ := h ⟨m, hm.isPrime, hm0⟩
    exact hs (hle ((hI s).2 hsx))
  have h1 : (1 : 𝓞 K) ∈ I := by rw [htop]; trivial
  have h2 := (hI 1).1 h1
  rwa [one_smul] at h2

theorem exists_common_mul (M N : Submodule (𝓞 K) V) (hM : M.FG)
    (h : ∀ y ∈ M, ∃ s : 𝓞 K, s ≠ 0 ∧ s • y ∈ N) : ∃ c : 𝓞 K, c ≠ 0 ∧ ∀ y ∈ M, c • y ∈ N := by
  classical
  obtain ⟨S, hS⟩ := hM
  have hSM : ∀ y ∈ S, y ∈ M := fun y hy => by rw [← hS]; exact Submodule.subset_span hy
  let f : V → 𝓞 K := fun y => if hy : y ∈ M then (h y hy).choose else 1
  have hf0 : ∀ y, f y ≠ 0 := by
    intro y
    by_cases hy : y ∈ M
    · simp only [f, dif_pos hy]; exact (h y hy).choose_spec.1
    · simp only [f, dif_neg hy]; exact one_ne_zero
  have hfN : ∀ y ∈ M, f y • y ∈ N := by
    intro y hy
    simp only [f, dif_pos hy]; exact (h y hy).choose_spec.2
  refine ⟨∏ y ∈ S, f y, Finset.prod_ne_zero_iff.2 (fun y _ => hf0 y), ?_⟩
  have hle : Submodule.span (𝓞 K) (S : Set V) ≤ N.comap (LinearMap.lsmul (𝓞 K) V (∏ y ∈ S, f y)) := by
    rw [Submodule.span_le]
    intro y hy
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem f hy
    show (∏ y ∈ S, f y) • y ∈ N
    rw [hk, mul_comm, mul_smul]
    exact N.smul_mem _ (hfN y (hSM y hy))
  intro y hy
  rw [← hS] at hy
  exact hle hy

end General

theorem locLe_zero {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    {w : HeightOneSpectrum (𝓞 K)} {A B : Submodule (𝓞 K) V} (h : DV.LocLe w 0 A B) :
    ∀ x ∈ A, ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • x ∈ B := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := h x hx
  rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul] at hsx
  exact ⟨s, hs, hsx⟩

theorem place_over' (D : D7) (p : ℕ) (hp : p.Prime) : ∃ w : D.what₂.places.Pl, D.what₂.places.resChar w = p := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
  obtain ⟨P, hP, hlo⟩ :=
    (inferInstance : Nonempty (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.what₂.LL)))
  have hpP : ((p : ℕ) : 𝓞 D.what₂.LL) ∈ P := by
    have h1 : (p : ℤ) ∈ Ideal.span {(p : ℤ)} := Ideal.mem_span_singleton_self _
    rw [hlo.over, Ideal.mem_comap] at h1
    simpa using h1
  have hne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hpP
    exact hp.ne_zero (by exact_mod_cast hpP)
  refine ⟨D.plEq.symm ⟨P, hP, hne⟩, ?_⟩
  set w := D.plEq.symm ⟨P, hP, hne⟩ with hw
  have hr := J.resChar_mem D w
  rw [hw, Equiv.apply_symm_apply] at hr
  rw [← hw] at hr
  by_contra hcon
  have hco : Nat.Coprime (D.what₂.places.resChar w) p :=
    (Nat.coprime_primes (D.what₂.places.resChar_prime w) hp).2 hcon
  have hb := Nat.gcd_eq_gcd_ab (D.what₂.places.resChar w) p
  rw [hco] at hb
  have h1 : (1 : 𝓞 D.what₂.LL) = ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) *
      ((Nat.gcdA (D.what₂.places.resChar w) p : ℤ) : 𝓞 D.what₂.LL) +
      ((p : ℕ) : 𝓞 D.what₂.LL) * ((Nat.gcdB (D.what₂.places.resChar w) p : ℤ) : 𝓞 D.what₂.LL) := by
    have := congrArg (fun z : ℤ => (z : 𝓞 D.what₂.LL)) hb
    simpa using this
  exact hP.ne_top ((Ideal.eq_top_iff_one P).2 (by
    rw [h1]; exact P.add_mem (P.mul_mem_right _ hr) (P.mul_mem_right _ hpP)))

def NuAtT (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ u w, D.what₂.places.resChar w = (D.mem u).A.T → DV.LocLe (D.plEq w) 0 (L.NuLat u) (DV.MramL D u)

theorem nuAtT_of {D : D7} {L : SizeData₂ D} (hAtT : NuAtTDef D L)
    (h5 : ∀ u w, D.what₂.places.resChar w = (D.mem u).A.T → LT.Nlam D u w ≤ LT.Sram D u w) : NuAtT D L := by
  intro u w hw x hx
  have h1 : InLoc (D.plEq w) (L.NuLat u) x :=
    ⟨1, fun h => (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h), by rwa [one_smul]⟩
  have h2 : D.nuIn u x ∈ LT.Nlam D u w := (hAtT u w hw x).mp h1
  have h3 : D.nuIn u x ∈ (D.fm u).S 0 w := (h5 u w hw h2).1
  obtain ⟨s, hs, hsx⟩ := D.locSpan u w _ h3
  refine ⟨s, hs, ?_⟩
  rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
  show (D.nuIn u).restrictScalars (𝓞 D.what₂.LL) (s • x) ∈ ((D.fm u).lat 0).L
  rw [map_smul]
  exact hsx

theorem nu_le_mram {D : D7} {L : SizeData₂ D} (hNu : DV.NuDef D L) (hT : NuAtT D L) (u : D.what₂.Word) :
    L.NuLat u ≤ DV.MramL D u := by
  intro x hx
  refine mem_of_locally _ x (fun v => ?_)
  have hv : D.plEq (D.plEq.symm v) = v := Equiv.apply_symm_apply _ _
  by_cases hw : D.what₂.places.resChar (D.plEq.symm v) = (D.mem u).A.T
  · have := locLe_zero (hT u _ hw) x hx
    rwa [hv] at this
  · have := locLe_zero (hNu.1 u _ hw) x hx
    rwa [hv] at this

theorem exists_free_prime (D : D7) (u : D.what₂.Word) :
    ∃ p : ℕ, p.Prime ∧ p ≠ (D.mem u).A.T ∧ ¬ DV.InertK D p := by
  have hq2 : D.host.q ≠ 2 := by
    have := D.host.hyp.2.2.1
    omega
  by_cases hT : (D.mem u).A.T = 2
  · refine ⟨D.host.q, D.host.hyp.1, by rw [hT]; exact hq2, ?_⟩
    unfold DV.InertK Host.cls primeClass
    rw [if_neg D.host.q_notMem_small, if_pos rfl]
    simp
  · refine ⟨2, Nat.prime_two, fun h => hT h.symm, ?_⟩
    unfold DV.InertK Host.cls primeClass
    rw [if_pos D.host.two_mem_small]
    simp

theorem nuCommens_of {D : D7} {L : SizeData₂ D} (hNu : DV.NuDef D L) (hT : NuAtT D L) : NuCommens D L := by
  intro u
  have hle := nu_le_mram hNu hT u
  constructor
  · have : Module.Finite (𝓞 D.what₂.LL) (DV.MramL D u) := Module.Finite.iff_fg.2 (D.MramL_fg u)
    have : IsNoetherian (𝓞 D.what₂.LL) (DV.MramL D u) := inferInstance
    have h2 := (IsNoetherian.noetherian ((L.NuLat u).comap (DV.MramL D u).subtype)).map (DV.MramL D u).subtype
    rw [Submodule.map_comap_subtype, inf_eq_right.2 hle] at h2
    exact h2
  · obtain ⟨p, hp, hpT, hin⟩ := exists_free_prime D u
    obtain ⟨w, hw⟩ := place_over' D p hp
    have hEq := hNu.2.1 u w (by rw [hw]; exact hpT) (Or.inr (by rw [hw]; exact hin))
    refine exists_common_mul _ _ (D.MramL_fg u) (fun y hy => ?_)
    obtain ⟨s, hs, hsy⟩ := locLe_zero hEq.2 y hy
    exact ⟨s, fun h0 => hs (by rw [h0]; exact Ideal.zero_mem _), hsy⟩

theorem nuCommensF_of {eps : ℝ} (Fm : FamP eps) (crystallineComparison : ℝ) (h10 : product_first_zeroth_parts.ConclusionOnFamily Fm crystallineComparison) (hS : SettingEventually Fm) :
    NuCommensF Fm := by
  obtain ⟨a0, h10⟩ := h10
  obtain ⟨a1, hS⟩ := hS
  refine ⟨max (max a0 a1) (Fm.x1 + 1), fun x hx i => ?_⟩
  have e0 : a0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have e1 : a1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have e2 : Fm.x1 < x := by have := le_trans (le_max_right (max a0 a1) (Fm.x1 + 1)) hx; linarith
  exact nuCommens_of (Fm.nuDef x e2 i) (nuAtT_of (Fm.ex x e2 i).lat.atT
    (fun u w hw => ((h10 x e0 i u (hS x e1 e2 i u)).2.2.2.2.1 w hw).1))

end Formalism.MainNotions.Lnk

end

end Commens

noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory

theorem ramRankF_of {eps : ℝ} (Fm : FamP eps) (crystallineComparison : ℝ) (h10 : product_first_zeroth_parts.ConclusionOnFamily Fm crystallineComparison) (hS : SettingEventually Fm) : RamRankF Fm := by
  obtain ⟨a0, h10⟩ := h10
  obtain ⟨a1, hS⟩ := hS
  refine ⟨max (max a0 a1) (Fm.x1 + 1), fun x hx i u => ?_⟩
  have e0 : a0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have e1 : a1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have e2 : Fm.x1 < x := by have := le_trans (le_max_right (max a0 a1) (Fm.x1 + 1)) hx; linarith
  have h := (h10 x e0 i u (hS x e1 e2 i u)).2.1.1
  exact_mod_cast h

set_option linter.unusedVariables false in

theorem muRank_pk {eps : ℝ} (Fm : FamP eps) (Cabs CH C0 eL C3 crystallineComparison C22 : ℝ)
    (hCabs : 0 ≤ Cabs) (hCH : 0 < CH) (heL : 0 ≤ eL) (hC0 : 1 ≤ C0)

    (s59 : ∀ x : ℝ, Fm.x1 < x → ∀ i : Fm.Ix x, UnusedSlot33.division_rows_rational_lattice (Fm.D x i))
    (s22 : TaylorLogMetric.StatementFamilyConstant Fm C22) (s23 : flipTwoThree.KudlaFamilyStatement Fm) (s24 : StandardLattice.KudlaFamilyStatement Fm C3) (s10 : product_first_zeroth_parts.KudlaFamilyStatement Fm crystallineComparison)

    (provedFourF : LocalQuadraticParts.SlopeLemmaFamily Fm) (provedFiveF : LocalQuadraticParts.SlopeLossFamily Fm eL) (hF3 : StandardLattice.FamilyTheoremThreeAdmitted Fm)

    (tVol : StandardLattice.TiesF Fm)
    (tOm : ∀ x (i : Fm.Ix x), ∃ δ : ℂ, TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice (Fm.D x i) (Fm.D x i).host.ccK δ ∧
      OmLink (Fm.D x i) (TaylorLogMetric.tor0 (Fm.D x i) (Fm.D x i).host.ccK δ))
    (tFree : ∀ x (i : Fm.Ix x), ThFree (Fm.D x i))
    (tTh : ∀ x (i : Fm.Ix x), ExistsTwelfthRootCharacterThetaFamily (Fm.D x i) C22)
    (t7 : flipTwoThree.admF7 Fm) (tSet : SettingEventually Fm)
    (tCV : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u))
    (t10 : ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word), IncidenceTransportConditions (Fm.D x i) u) :
    TuSize Fm → ChosenE Fm C0 CH → NuFullF Fm ∧ J.MuRank Fm := by
  intro hTu hCh
  have hDl : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps := by
    obtain ⟨C5, c6, Cb, -, -, -, -, -, -, cQD, -, -, -⟩ := hCh
    exact dl_of_chosen Fm C5 cQD
  obtain ⟨C₅, h59a⟩ := UnusedSlot33.field_lemmas_except_seven
  have h59 : UnusedSlot33.ConclusionOnFamily Fm 100 C₅ := fun x hx i => by
    obtain ⟨p1, p2, p3, p4, p5, p5c, p6, p8⟩ := h59a (Fm.D x i) (Fm.L x i).sc
    exact ⟨p1, p2, p3, p4, p5, p5c, p6, s59 x hx i, p8⟩
  have h24 := s24 ⟨hF3, StandardLattice.column_lemma_family_of_definite Fm 100 C₅ h59 (fun _ _ => gram0Def _)⟩ tVol
  have h244 : StandardLattice.FamilyPartFour Fm C3 := h24.2.2.2.2.2.1
  have h22 : TaylorLogMetric.ConclusionOnFamily Fm C22 := s22 (TaylorLogMetric.AdmF_of Fm (fun x i => UnusedSlot33.ramification_two_and_conjugation_at_q_and_d _))
  have h4p : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), StandardLattice.Conclusion4p (Fm.D x i) (Fm.ex x hx i).lev :=
    fun x hx i => (h244 x hx i).2.2.2.1
  have h10 : product_first_zeroth_parts.ConclusionOnFamily Fm crystallineComparison := s10 (product_first_zeroth_parts.AdmF_of Fm C22 100 C₅ h22 h59 h4p t10)
  have hNF : NuFullF Fm := nuFullF_of Fm (nuCommensF_of Fm crystallineComparison h10 tSet)
  have hRank : J.MuRank Fm := muRank_of_chosen Fm crystallineComparison (by linarith) hCh hNF h10 tSet
  exact ⟨hNF, hRank⟩

theorem linkGLOBAL_pk {eps : ℝ} (Fm : FamP eps) (Cabs CH C0 eL C3 crystallineComparison C22 : ℝ)
    (hCabs : 0 ≤ Cabs) (hCH : 0 < CH) (heL : 0 ≤ eL) (hC0 : 1 ≤ C0)

    (s59 : ∀ x : ℝ, Fm.x1 < x → ∀ i : Fm.Ix x, UnusedSlot33.division_rows_rational_lattice (Fm.D x i))
    (s22 : TaylorLogMetric.StatementFamilyConstant Fm C22) (s23 : flipTwoThree.KudlaFamilyStatement Fm) (s24 : StandardLattice.KudlaFamilyStatement Fm C3) (s10 : product_first_zeroth_parts.KudlaFamilyStatement Fm crystallineComparison)

    (provedFourF : LocalQuadraticParts.SlopeLemmaFamily Fm) (provedFiveF : LocalQuadraticParts.SlopeLossFamily Fm eL) (hF3 : StandardLattice.FamilyTheoremThreeAdmitted Fm)

    (tVol : StandardLattice.TiesF Fm)
    (tOm : ∀ x (i : Fm.Ix x), ∃ δ : ℂ, TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice (Fm.D x i) (Fm.D x i).host.ccK δ ∧
      OmLink (Fm.D x i) (TaylorLogMetric.tor0 (Fm.D x i) (Fm.D x i).host.ccK δ))
    (tFree : ∀ x (i : Fm.Ix x), ThFree (Fm.D x i))
    (tTh : ∀ x (i : Fm.Ix x), ExistsTwelfthRootCharacterThetaFamily (Fm.D x i) C22)
    (t7 : flipTwoThree.admF7 Fm) (tSet : SettingEventually Fm)
    (tCV : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u))
    (t10 : ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word), IncidenceTransportConditions (Fm.D x i) u) :
    Fm.CoverAll → TuSize Fm → DGamSize Fm → LinkGLOBAL Fm Cabs CH C0 Cabs eL := by
  intro hCov hTu _ hCh hIn
  have hDl : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps := by
    obtain ⟨C5, c6, Cb, -, -, -, -, -, -, cQD, -, -, -⟩ := hCh
    exact dl_of_chosen Fm C5 cQD
  obtain ⟨C₅, h59a⟩ := UnusedSlot33.field_lemmas_except_seven
  have h59 : UnusedSlot33.ConclusionOnFamily Fm 100 C₅ := fun x hx i => by
    obtain ⟨p1, p2, p3, p4, p5, p5c, p6, p8⟩ := h59a (Fm.D x i) (Fm.L x i).sc
    exact ⟨p1, p2, p3, p4, p5, p5c, p6, s59 x hx i, p8⟩
  have h24 := s24 ⟨hF3, StandardLattice.column_lemma_family_of_definite Fm 100 C₅ h59 (fun _ _ => gram0Def _)⟩ tVol
  have h244 : StandardLattice.FamilyPartFour Fm C3 := h24.2.2.2.2.2.1
  have h22 : TaylorLogMetric.ConclusionOnFamily Fm C22 := s22 (TaylorLogMetric.AdmF_of Fm (fun x i => UnusedSlot33.ramification_two_and_conjugation_at_q_and_d _))
  have h4p : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), StandardLattice.Conclusion4p (Fm.D x i) (Fm.ex x hx i).lev :=
    fun x hx i => (h244 x hx i).2.2.2.1
  have h10 : product_first_zeroth_parts.ConclusionOnFamily Fm crystallineComparison := s10 (product_first_zeroth_parts.AdmF_of Fm C22 100 C₅ h22 h59 h4p t10)
  have hNF : NuFullF Fm := nuFullF_of Fm (nuCommensF_of Fm crystallineComparison h10 tSet)
  have hRank : J.MuRank Fm := muRank_of_chosen Fm crystallineComparison (by linarith) hCh hNF h10 tSet
  have hRR : RRRankF Fm := by
    obtain ⟨C5, c6, Cb, -, -, -, -, -, -, -, -, cPr, -⟩ := hCh
    obtain ⟨-, lS, lI, lD, -⟩ := hIn
    exact rrRankF_of Fm Cabs CH C0 (by linarith) lS cPr lI lD
  have h245 : StandardLattice.PartFiveFamilyBounds Fm := h24.2.2.2.2.2.2.2
  have hCount : CountF Fm := countF_fam Fm h245
  have h23 := s23 ⟨flipTwoThree.theta_norm_family_of_linked Fm C22 h22 tOm, flipTwoThree.theta_condition_family_of_linked Fm C22 tFree tTh,
    flipTwoThree.stabiliser_family_of_column_lemma Fm 100 C₅ h59 h4p,
    flipTwoThree.injectivity_family_of_theorem Fm crystallineComparison h10 tSet, flipTwoThree.norm_bound_family_of_theorem Fm crystallineComparison h10 tSet, t7⟩
  have hSM : SlopesMF Fm := flipTwoThree.slopesMF_of_count_fam Fm h23.2.2.2.2.1 h23.2.2.2.2.2.1 hCount hDl tCV
  exact linkGLOBAL Fm Cabs CH C0 eL hCabs hCH.le heL hCount hSM
    (fun _ _ => slopes_family_of_division_side Fm provedFourF (ioNonnegF Fm)) hNF hRank hRR
    (fun cPr cCo lS lI lD => frameF_of Fm CH C0 hCH hC0
      (frameRealF_of'' Fm Cabs CH C0 hCH.le lD lI lS cPr hNF hRank hTu (ramRankF_of Fm crystallineComparison h10 tSet)
        (matKF_of Fm Cabs CH C0 (by linarith) lS cPr lD)) (latF Fm lD hNF hRank hRR) cPr cCo hNF)
    (fun _ _ _ _ _ => losses_family_of_division_side Fm eL provedFiveF (askIsF Fm)) (charF Fm) hCov hCh hIn

end Formalism.MainNotions

end
