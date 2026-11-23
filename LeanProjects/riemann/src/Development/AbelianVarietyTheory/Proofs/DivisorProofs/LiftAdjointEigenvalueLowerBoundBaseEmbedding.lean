import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
import Development.AbelianVarietyTheory.Definitions.Divisors.RealisedChainTorusEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HookPlusLeMainTerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicScalarBase
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.LevelVectorSizeBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelEigenpartsAndConjugateCharactersStatement

noncomputable section

open NumberField IsDedekindDomain Module MeasureTheory
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.IndefR.Mult
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.Survey.LevelVectorSizeBounds
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LowTopCore

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem g_mem_ofCore {F : Face D A} (h : GlobalTheory.Hk3.Core R F) {PP : Pl D.host.E} (hP : PP ∈ R.Pg) :
    ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  obtain ⟨k, hk⟩ := (h.lev.Pg PP).1 hP
  refine ⟨k, ?_⟩
  have h1 := R.C.P.pb_over k
  rw [← hk] at h1
  have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) (D.host.g k : ℕ) ∈ PP.asIdeal := h1
  simpa using h2

open Classical in

theorem isConjChars_base_ofCore {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T0) :
    IsConjChars R i t (RingEquiv.refl ℂ) (R.toLevCh.mu t ((i : ℕ) + 1)) R.eta
      (fun PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP) := by
  refine ⟨_, _, isGalConj_refl _ _, isGalConj_refl _ _, ⟨(h.thP.ωP i t).hecS, ?_⟩, h.lev.eta, ?_⟩
  · intro P e he k x hx
    have a := (h.lev.mu0 i).2 P e he k x hx
    have b := (h.lev.xi t).2 P e he k x hx
    show (((R.mu0 ((i : ℕ) + 1) x * R.xi t x : Circle)) : ℂ) = (((R.C.mu0 i).locK P k * (R.xiH t).locK P k : ℂˣ) : ℂ)
    rw [Circle.coe_mul, a, b, Units.val_mul]
  · intro PP hPP a k u hk hu
    have ha : a ∉ PP.asIdeal := fun ha => u.ne_zero (hu.trans (Ideal.Quotient.eq_zero_iff_mem.2 ha))
    show _ = (R.C.mu0 i).locK PP k * (R.xiH t).locK PP k
    by_cases hg : PP ∈ R.Pg
    · obtain ⟨l, hl⟩ := g_mem_ofCore R h hg
      have hun : (R.xiH t).UnrAt PP := by
        by_contra hn
        rcases (h.lev.Q_ram t PP).1 hn with hq | ⟨PP', hq, hc⟩
        · obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := h.lev.Q_pl t PP hq
          exact not_both (D.host.g_prime l) hq1 (hq4 l) hl (q_mem hq2)
        · obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := h.lev.Q_pl t PP' hq
          obtain ⟨c', hc1, hc2⟩ := hc _ (q_mem hq2)
          have : c' = (q : 𝓞 D.host.E) := by
            apply NumberField.RingOfIntegers.coe_injective
            rw [map_natCast]
            have h3 : (c' : D.host.E) = (q : D.host.E) := by simpa using hc2
            exact h3
          exact not_both (D.host.g_prime l) hq1 (hq4 l) hl (this ▸ hc1)
      simp only [if_pos hg]
      rw [locK_eq_one hun a k hk ha, mul_one]
      exact h.lev.chi i PP hg a k u hk hu
    · have hq : PP ∈ R.Q t := hPP.resolve_left hg
      obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := h.lev.Q_pl t PP hq
      have hun : (R.C.mu0 i).UnrAt PP := (R.C.isMu0 i).unr PP fun l hl =>
        not_both (D.host.g_prime l) hq1 (hq4 l) hl (q_mem hq2)
      simp only [if_neg hg]
      rw [locK_eq_one hun a k hk ha, one_mul]
      exact h.lev.xiR t PP hq a k u hk hu

open Classical in

theorem isLevelVec_base_ofCore {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T0) :
    IsLevelVec R.ψ R.θ (Vc D i) (Wc D i) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) (R.datWp i R.triv) (R.Q t)
      (fun PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP) (R.vacP i) (R.vP i t) := by
  have h1 := h.thP.vP i t
  unfold Datum.IsThPVecOf at h1
  unfold IsLevelVec
  have hQ : ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP),
      Datum.omegaQ (R.Q t) (Wc D i).rank (fun PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP) (-1) y =
        Datum.omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) y := by
    intro y
    unfold Datum.omegaQ
    split_ifs with hy
    · refine Finset.prod_congr rfl fun PP _ => ?_
      have hn : PP.1 ∉ R.Pg := fun hg => by
        obtain ⟨l, hl⟩ := g_mem_ofCore R h hg
        obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := h.lev.Q_pl t PP.1 PP.2
        exact not_both (D.host.g_prime l) hq1 (hq4 l) hl (q_mem hq2)
      simp only [if_neg hn]
    · rfl
  simp only [omegaG_triv, hQ]
  exact h1

open Classical in

theorem chr_base_ofCore {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T0) :
    chrOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) R.triv
      (fun PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP)) = (levEnv _ (R.βV i) (R.datVt i t)).χ := by
  ext1 x
  refine levFn_congr (R.βV i) D.R.r (r_le_V i) D.R.t 1 R.Pg (R.Q t) R.triv
    (fun _ PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP) (fun _ PP => (R.chi ((i : ℕ) + 1) PP)⁻¹)
    (fun PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP) (R.xiR t) ?_ ?_ _
  · intro c PP hP
    simp only [if_pos hP]
  · intro PP hP
    have hn : PP ∉ R.Pg := fun hg => by
      obtain ⟨l, hl⟩ := g_mem_ofCore R h hg
      obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := h.lev.Q_pl t PP hP
      exact not_both (D.host.g_prime l) hq1 (hq4 l) hl (q_mem hq2)
    simp only [if_neg hn]

theorem exists_lift_ofCore {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T0) :
    ∃ th : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H, ∀ x, (R.HW i (sg0 D A)).e (th x) = R.thF i t x :=
  GlobalTheory.BaseScalar.exists_factor (R.HW i (sg0 D A)).e (R.thF i t) (R.Wall i (sg0 D A)) (h.models.HW i (sg0 D A)).1
    (h.models.HW i (sg0 D A)).2.1 (h.thP.thF_mem i t)

theorem isLift_of_ofCore {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T0)
    (th : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H) (hth : ∀ x, (R.HW i (sg0 D A)).e (th x) = R.thF i t x) :
    IsLift R i (sg0 D A) (R.ωP i t) (R.ptP i t) (R.cV i) (R.ioP i) (R.νV i t) (R.fdV i t) (R.HV i t) th := by
  refine (h.thP.thF i t).elim fun thP hP => ?_
  unfold IsLift
  intro x v g
  have a := GlobalTheory.BaseScalar.integrableOn_of_isThetaLift hP.1 x (PiTensorProduct.tprod ℂ v) g
  have c := (congrFun (hP.2 x v) g).trans a.2
  refine ⟨a.1, ?_⟩
  rw [hth x]
  exact c

theorem scalar_of_lift_ofCore {F : Face D A} (hA : GlobalTheory.LowRow.AdelC R F) (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (b : ℝ)
    (hb : Sizes D i b) (t : T0) (ht : PrimeToHost R t)
    (th : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H)
    (hth : IsLift R i (sg0 D A) (R.ωP i t) (R.ptP i t) (R.cV i) (R.ioP i) (R.νV i t) (R.fdV i t) (R.HV i t) th)
    (ev : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) (hev : typePart R i (sg0 D A) t R.triv ev ≠ ⊥) :
    ∃ l : ℝ, 0 < l ∧ (∀ x ∈ typePart R i (sg0 D A) t R.triv ev, th (adjLev R.triv th x) = (l : ℂ) • x) ∧
      mainTerm D i (sg0 D A) - 8 * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * Lp D b ≤ Real.log l := by
  have hσ : IsEmbOverK D (sg0 D A) (RingEquiv.refl ℂ) := by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0]; exact isEmbOverK_base
  have key := hA h i b hb t ht _ _ hσ R.triv (isLocal_triv R) _ _ _ (isConjChars_base_ofCore R h i t) (R.ωP i t) (h.thP.ωP i t)
    (onb (R.MW i (sg0 D A))) (fun ρ => GlobalTheory.IndefiniteRowSideFullHecke.LiftFormsMainTerm.isONBasis_onb _ ρ _ (h.models.order i ρ)) _ _ (isLevelVec_base_ofCore R h i t)
    (h.thP.pt_theta i t) (R.cV i) (h.models.cV i) (R.ioP i) (by rw [delta_base R]; exact h.thP.ioP i t)
    (R.νV i t) (R.fdV i t) (h.models.νV i t) _ (R.B.L i t).pres.y (R.B.L i t).pres.reps (R.HV i t)
    (by rw [chr_base_ofCore R h]; exact h.models.HV i t)
  exact key.2 th hth ev hev

theorem scalar_on_part_ofCore {F : Face D A} (hA : GlobalTheory.LowRow.AdelC R F) (h : GlobalTheory.Hk3.Core R F)
    (hp : PrimeToHost R A.μ0) (i : Fin D.R.m) (b : ℝ) (hb : Sizes D i b)
    (th : (R.HV i A.μ0).H →ₗ[ℂ] (R.HW i (sg0 D A)).H) (hth : ∀ x, (R.HW i (sg0 D A)).e (th x) = R.thF i A.μ0 x)
    (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) :
    ∃ l : ℝ, Real.exp (lowB D i b) ≤ l ∧
      ∀ y ∈ GlobalTheory.LiftLower.partH R i (sg0 D A) c, th (LinearMap.adjoint th y) = (l : ℂ) • y := by
  have e := GlobalTheory.LiftLower.typePart_base h.lev i (sg0 D A) c
  have h1 := scalar_of_lift_ofCore R hA h i b hb A.μ0 hp th (isLift_of_ofCore R h i A.μ0 th hth) c
  have h2 := GlobalTheory.BaseScalar.adjLev_triv R th
  have h3 : lowB D i b ≤ mainTerm D i (sg0 D A) -
      8 * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * Lp D b := sub_le_sub_right (GlobalTheory.LowTopBound.hookPlus_le_mainTerm R i) _
  exact GlobalTheory.LowTopBound.scalar_of_ne_bot th _ _ h2 _ _ e _ _ h3 h1

theorem lowTop_ofCore : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ (s : ℕ) (b : ℝ),
    GlobalTheory.LowRow.AdelC R F → GlobalTheory.Hk3.Core R F → A.fam.Ok s → PrimeToHost R A.μ0 → (∀ i, Sizes D i b) → GlobalTheory.BigOn.LowTop R b := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F s b hA h _ hp hb i l x hx hl hxl
  obtain ⟨th, hth⟩ := exists_lift_ofCore R h i A.μ0
  have hinj : Function.Injective (R.HW i (sg0 D A)).e := (h.models.HW i (sg0 D A)).1
  have hS : ∀ y, R.thG i A.μ0 y = GlobalTheory.LiftLower.projH R i (sg0 D A) (th y) := fun y => by
    have a1 := h.thP.thG i A.μ0 y
    have a2 := GlobalTheory.LiftLower.e_projH h.models.gW i (sg0 D A) (th y)
    have a3 := congrArg (Formalism.IndefR.Mult.postOn (R.MW i (sg0 D A)) (R.eWf i (sg0 D A))) (hth y)
    exact hinj (a1.trans (a3.symm.trans a2.symm))
  have hid := GlobalTheory.LiftScalarCompare.eC_idem (R := R) h.grp.record
  have hu := GlobalTheory.gW_norm_eq R h.models.HW h.models.gW h.models.νW i (sg0 D A)
  have htop := GlobalTheory.T.principalLevel_eigenparts_and_conjugate_characters.1 R F (GlobalTheory.Core5.of_core h) i (sg0 D A)
    (GlobalTheory.LiftLower.schurMult_of_models R h.models.HW i (sg0 D A))
  have htop' : (⨆ c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D, GlobalTheory.LiftLower.partH R i (sg0 D A) c) = ⊤ :=
    top_le_iff.1 (htop.ge.trans (iSup_mono fun c => iSup_le fun _ => le_rfl))
  have hm := GlobalTheory.mul_norm_sq_le_norm_adjoint_sq_of_spanning_parts th _ (Real.exp (lowB D i b)) htop'
    (scalar_on_part_ofCore R hA h hp i b (hb i) th hth)
  have key := GlobalTheory.LowTopBound.le_eigenvalue th (R.thG i A.μ0) (GlobalTheory.LiftLower.projH R i (sg0 D A)) _ l hS
    (GlobalTheory.LowTopBound.idem_apply (R.gW i (sg0 D A)) hid)
    (fun x hx y => GlobalTheory.LiftScalarCompare.adjoint_idem (R.gW i (sg0 D A)) hu hid hx y) hm x hx hl hxl
  exact (Real.le_log_iff_exp_le hl).2 key

end GlobalTheory.LowTopCore

end
