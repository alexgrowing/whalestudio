import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowFormOfEmb
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
import Development.AbelianVarietyTheory.Definitions.Divisors.RealisedChainTorusEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelEigenpartsAndConjugateCharactersStatement

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module MeasureTheory Matrix
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Mult
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
open GlobalTheory.LiftLower GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.Survey.LevelVectorSizeBounds
open scoped InnerProductSpace Matrix TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LowForm

section Survey

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem g_mem_six {F : Face D A} (h : GlobalTheory.Hk3.Core R F) {PP : Pl D.host.E} (hP : PP ∈ R.Pg) : ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  obtain ⟨k, hk⟩ := (h.lev.Pg PP).1 hP
  refine ⟨k, ?_⟩
  have h1 := R.C.P.pb_over k
  rw [← hk] at h1
  have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) (D.host.g k : ℕ) ∈ PP.asIdeal := h1
  simpa using h2

open Classical in

theorem isConjChars_base_six {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T) :
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
    · obtain ⟨l, hl⟩ := g_mem_six R h hg
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

theorem chr_base_six {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T) :
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
      obtain ⟨l, hl⟩ := g_mem_six R h hg
      obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := h.lev.Q_pl t PP hP
      exact not_both (D.host.g_prime l) hq1 (hq4 l) hl (q_mem hq2)
    simp only [if_neg hn]

end Survey

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem projH_idem_six (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (x : (R.HW i σ).H) :
    projH R i σ (projH R i σ x) = projH R i σ x := op_idem (R.gW i σ) (eC_idem_at h.grp.record σ) x

theorem projH_adjoint_six (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) :
    LinearMap.adjoint (projH R i σ) = projH R i σ :=
  adjoint_eq_self _ (projH_idem_six h i σ) fun _ hx y => GlobalTheory.LiftScalarCompare.adjoint_idem (R.gW i σ)
    (GlobalTheory.gW_norm_eq R h.models.HW h.models.gW h.models.νW i σ) (eC_idem_at h.grp.record σ) hx y

theorem isConjChars_at_six (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) {σ : D.what₂.LL →+* ℂ} {s : ℂ ≃+* ℂ} (hσ : IsEmbOverK D σ s)
    {μ' η' : (AE D)ˣ →* Circle} (hμ : ChiAt R i σ μ') (hη : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ R.eta η') :
    IsConjChars R i A.μ0 s μ' η' (conjChar s (blkChar R i)) := by
  obtain ⟨μH, a1, a2⟩ := GlobalTheory.T.principalLevel_eigenparts_and_conjugate_characters.2.2.1 R F (GlobalTheory.Core5.of_core h) i σ s hσ μ' hμ
  obtain ⟨ηH, b1, b2⟩ := GlobalTheory.T.principalLevel_eigenparts_and_conjugate_characters.2.2.2 R F (GlobalTheory.Core5.of_core h) σ s hσ η' hη
  obtain ⟨μB, -, c1, -, -, -, c2⟩ := isConjChars_base_six R h i A.μ0
  refine ⟨μH, ηH, a1, b1, a2, b2, fun PP hP a k u hk hu => Units.ext ?_⟩
  have e1 := a1 PP k
  have e2 := c1 PP k
  rw [twVal_zero, twVal_zero] at e1 e2
  have e3 := c2 PP hP a k u hk hu
  rw [e1]
  exact congrArg s ((congrArg Units.val e3).trans e2)

theorem chr_at_six (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) {σ : D.what₂.LL →+* ℂ} {s : ℂ ≃+* ℂ} (hσ : IsEmbOverK D σ s)
    (χ' : levJ R i A.μ0 →* ℂˣ)
    (hχ : ∀ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.ConjVal σ (((levEnv (Vc D i) (R.βV i) (R.datVt i A.μ0)).χ k : ℂˣ) : ℂ) ((χ' k : ℂˣ) : ℂ)) :
    chrOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv (conjChar s (blkChar R i))) = χ' := by
  refine MonoidHom.ext fun k : levJ R i A.μ0 => Units.ext ?_
  refine (hχ k).elim fun y hy => ?_
  have h1 := hy.1
  have h2 := hy.2
  have e1 := congrArg Units.val (DFunLike.congr_fun (chr_base_six R h i A.μ0) k)
  have e2 := chrOf_conj (R := R) i s (blkChar R i) k
  have e3 : ((χ' k : ℂˣ) : ℂ) = s (((levEnv (Vc D i) (R.βV i) (R.datVt i A.μ0)).χ k : ℂˣ) : ℂ) :=
    h2.symm.trans ((hσ.1 y).trans (congrArg s h1))
  exact e2.trans ((congrArg s e1).trans e3.symm)

theorem isLevelVec_at_six (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    {f₀ f : Datum.WO (Vc D i) (Wc D i) → ℂ}
    (hf : Datum.IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i)
      R.Pg ∅ (fun _ => 1) f₀ f) :
    IsLevelVec R.ψ R.θ (Vc D i) (Wc D i) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) (R.datWp i R.triv) (R.Q A.μ0)
      m f₀ f := by
  rw [Q_base h.lev]
  unfold Datum.IsThPVecOf at hf
  unfold IsLevelVec
  have hQ : ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP),
      Datum.omegaQ ∅ (Wc D i).rank m (-1) y = Datum.omegaQ ∅ (Wc D i).rank (fun _ => 1) (-1) y := by
    intro y
    unfold Datum.omegaQ
    simp
  simp only [omegaG_triv, hQ]
  exact hf

open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature in

theorem exists_full_lift_six (hA : GlobalTheory.LowRow.AdelC R F) (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) {b : ℝ} (hb : Sizes D i b)
    (ht : PrimeToHost R A.μ0) {σ : D.what₂.LL →+* ℂ} {s : ℂ ≃+* ℂ} (hσ : IsEmbOverK D σ s) {v : (R.MW i σ).Vec}
    (hv : IsExtVec (R.MW i σ) v) {c₀ μ' η' c c₁ H j th} (hd : IsConjDatum R i σ c₀ μ' η' c c₁ H j th) :
    ∃ T : H.H →ₗ[ℂ] (R.HW i σ).H, (∀ x, th x = projH R i σ (T x)) ∧
      ∀ ev, typePart R i σ A.μ0 R.triv ev ≠ ⊥ →
        ∃ l : ℝ, 0 < l ∧ (∀ x ∈ typePart R i σ A.μ0 R.triv ev, T (adjLev R.triv T x) = (l : ℂ) • x) ∧
          mainTerm D i σ - 8 * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * Lp D b ≤ Real.log l := by
  have hμ := hd.1
  have hη := hd.2.1
  have hF := hd.2.2.1
  refine hd.2.2.2.elim fun ω a => a.elim fun f₀ a => a.elim fun f a => a.elim fun B a => a.elim fun io a =>
    a.elim fun thP a => ?_
  refine hF.model.elim fun χ' hχ => ?_
  have hH := hχ.2
  rw [← chr_at_six h i hσ χ' hχ.1] at hH
  have key := hA h i b hb A.μ0 ht σ s hσ R.triv (isLocal_triv R) _ _ _ (isConjChars_at_six h i hσ hμ hη) ω a.1 B a.2.2.1 f₀ f
    (isLevelVec_at_six h i σ _ a.2.1) a.2.2.2.1 c hF.coef io a.2.2.2.2.1 (R.νV i A.μ0) (R.fdV i A.μ0) (h.models.νV i A.μ0) _
    (R.B.L i A.μ0).pres.y (R.B.L i A.μ0).pres.reps H hH
  refine key.1.elim fun T hT => ⟨T, fun x => eq_of_low_at h.models.HW hv fun w => ?_, key.2 T hT⟩
  have e1 : (R.HW i σ).e (T x) (fun ρ => w ρ) = thP ((c.ext ∘ₗ H.e).rangeRestrict x) (PiTensorProduct.tprod ℂ w) :=
    funext fun g => (hT x w g).2.trans
      (GlobalTheory.BaseScalar.integrableOn_of_isThetaLift a.2.2.2.2.2.1 x (PiTensorProduct.tprod ℂ w) g).2.symm
  have e2 : (R.HW i σ).e (projH R i σ (T x)) (fun ρ => w ρ) = R.eWf i σ ((R.HW i σ).e (T x) fun ρ => w ρ) :=
    congrArg (fun U : MMap (R.MW i σ) => U fun ρ => w ρ) (e_projH h.models.gW i σ (T x))
  exact (a.2.2.2.2.2.2 x w).trans (e2.trans (congrArg (R.eWf i σ) e1)).symm

theorem parts_scalar_six (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) {b : ℝ}
    (hlog : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.logHookSum i (lab σ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.logHookSum i id)
    {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X] (T : X →ₗ[ℂ] (R.HW i σ).H)
    (hT : ∀ ev, typePart R i σ A.μ0 R.triv ev ≠ ⊥ →
        ∃ l : ℝ, 0 < l ∧ (∀ x ∈ typePart R i σ A.μ0 R.triv ev, T (adjLev R.triv T x) = (l : ℂ) • x) ∧
          mainTerm D i σ - 8 * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * Lp D b ≤ Real.log l) :
    ∀ ev, partH R i σ ev ≠ ⊥ → ∃ l : ℝ, 0 < l ∧ (∀ y ∈ partH R i σ ev, T (LinearMap.adjoint T y) = (l : ℂ) • y) ∧
      GlobalTheory.BigOn.lowB D i b ≤ Real.log l := by
  intro ev hev
  have e := LiftLower.typePart_base h.lev i σ ev
  refine (hT ev (fun h0 => hev (e.symm.trans h0))).elim fun l a => ?_
  refine ⟨l, a.1, fun y hy => ?_, le_trans (sub_le_sub_right (hookPlus_le i σ hlog) _) a.2.2⟩
  have e1 := LinearMap.congr_fun (GlobalTheory.BaseScalar.adjLev_triv R T) y
  have e2 := a.2.1 y (e.ge hy)
  exact (congrArg T e1).symm.trans e2

open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature in

theorem conjLift_lower_six (hA : GlobalTheory.LowRow.AdelC R F) (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) {b : ℝ} (hb : Sizes D i b)
    (ht : PrimeToHost R A.μ0) {σ : D.what₂.LL →+* ℂ} {s : ℂ ≃+* ℂ} (hσ : IsEmbOverK D σ s) {v : (R.MW i σ).Vec}
    (hv : IsExtVec (R.MW i σ) v) (hlog : logHookSum i (lab σ) = logHookSum i id) {c₀ μ' η' c c₁ H j th}
    (hd : IsConjDatum R i σ c₀ μ' η' c c₁ H j th) :
    ∀ x ∈ (LinearMap.ker th)ᗮ, Real.exp (GlobalTheory.BigOn.lowB D i b) * ‖x‖ ^ 2 ≤ ‖th x‖ ^ 2 := by
  refine (exists_full_lift_six hA h i hb ht hσ hv hd).elim fun T hT => ?_
  have p1 := projH_adjoint_six h i σ
  have p2 := projH_idem_six h i σ
  have p3 := GlobalTheory.T.principalLevel_eigenparts_and_conjugate_characters.1 R F (GlobalTheory.Core5.of_core h) i σ (schurMult_of_models R h.models.HW i σ)
  have p4 := parts_scalar_six h i σ (b := b) hlog T hT.2
  exact lower_of_parts T th (projH R i σ) (partH R i σ) (IsNormSys R i) _ p1 p2 p3 p4 hT.1

theorem lower_overK_six (hA : GlobalTheory.LowRow.AdelC R F) (h : GlobalTheory.Hk3.Core R F) (hU : R.LUnif) (i : Fin D.R.m) {b : ℝ}
    (hb : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Sizes D i b) (ht : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.PrimeToHost R A.μ0) {σ : D.what₂.LL →+* ℂ} (hσ : OverK σ)
    {v : (R.MW i σ).Vec} (hv : IsExtVec (R.MW i σ) v) {gramR c0R c0L}
    (hT : Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
      (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L)
    (hu : ∀ x, ∃! y, IsRatLift R i 1 x y) (hC : ConjAt R i σ 1 (c0L i)) {x : A.fam.amb.FL i A.μ0}
    {y : Fin (R.nW i) → D.what₂.LL} (hy : IsRatLift R i 1 x y)
    (hx : ∀ u, R.thG i A.μ0 (R.jV i A.μ0 u) = 0 → csumAt (A.MtCSD i A.μ0) σ x u = 0) :
    Real.exp (lowB D i b) * (csumAt (A.MtCSD i A.μ0) σ x x).re ≤ ‖(R.FW i).j σ y‖ ^ 2 := by
  have : Countable D.what₂.LL := Countable.of_equiv _ (Module.finBasis ℚ D.what₂.LL).equivFun.toEquiv.symm
  have : FiniteDimensional D.what₂.LL (A.fam.amb.FL i A.μ0) := Module.Finite.of_basis (A.MtCSD i A.μ0).basis
  refine (GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq D.what₂.embLL σ).elim fun s hs => ?_
  have hs' : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s := ⟨fun a => (hs a).symm, hσ⟩
  refine hC.2.1.elim fun μ' a => a.elim fun η' a => a.elim fun c a => a.elim fun c₁ a => a.elim fun H a =>
    a.elim fun j a => a.elim fun th hd => ?_
  refine hC.2.2.elim fun u a => a.elim fun U a => a.elim fun z a => a.elim fun ζ a => ?_
  refine (a.2.2.2 μ' η' c c₁ H j th hd).2.elim fun κ hκ => ?_
  refine (exists_descent (sgAt_mk _ R.hv0) ((R.FW i).j (sg0 D A)) (R.jV i A.μ0) (R.thG i A.μ0) 1 hu).elim fun θ hθ => ?_
  have m1 := inner_conjForms_eq_csumAt R h.models.jV gramR c0R c0L hT i σ c c₁ H j hd.2.2.1
  have m2 := GlobalTheory.ConjSpan.span_conjForms R h.models.jV gramR c0R c0L hT i σ c c₁ H j hd.2.2.1
  have m3 : ∀ u, θ u = 0 → ⟪j x, j u⟫_ℂ = 0 := fun u h0 =>
    (m1 x u).trans (hx u ((one_smul ℂ _).symm.trans ((hθ u).symm.trans
      ((congrArg ((R.FW i).j (sg0 D A)) h0).trans (LinearMap.map_zero _)))))
  have m4 := mem_orth_ker θ j ((R.FW i).j σ) th U (R.gW i σ z) κ m2 (hU i σ).1 (fun x => hκ.2 x _ (hθ x)) m3
  have m5 := conjLift_lower_six hA h i hb ht hs' hv hC.1 hd _ m4
  have m6 := congrArg Complex.re (GlobalTheory.ConjLiftCounterexample.gram_of_conjAt hC hd hy hy)
  have m7 := (re_inner_self _).symm.trans (m6.trans (re_inner_self _))
  have m8 := (re_inner_self _).symm.trans (congrArg Complex.re (m1 x x))
  exact (congrArg (Real.exp (lowB D i b) * ·) m8).ge.trans (m5.trans m7.ge)

theorem lowForm_of_emb_six {s : ℕ} (hOk : A.fam.Ok s) (h : GlobalTheory.Hk3.Core R F) (hB : BaseLinks R F) {b : ℝ}
    (hE : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (x : A.fam.amb.FL i A.μ0) (y : Fin (R.nW i) → D.what₂.LL),
      IsRatLift R i 1 x y → (∀ σ' u, R.thG i A.μ0 (R.jV i A.μ0 u) = 0 → csumAt (A.MtCSD i A.μ0) σ' x u = 0) →
      Real.exp (lowB D i b) * (csumAt (A.MtCSD i A.μ0) σ x x).re ≤ ‖(R.FW i).j σ y‖ ^ 2) : LowForm R F b := by
  intro i v hv x
  have hR : IsRatHerm (cmMax D.what₂.LL) ((A.fam.L i A.μ0).HZ (liftLvl F) (liftSub R F i A.μ0))
    ((A.fam.L i A.μ0).XQ (liftLvl F) (liftSub R F i A.μ0)) := hB.2.2 i
  have hf := GlobalTheory.QuotRational.fE_mem_cmMax _ _ _ _ _ (blockHyp (F := F) hOk i A.μ0) hR
  have hm := GlobalTheory.Proof.ConjugateTransposeMajorant.majAt_eq_csumAt _ _ _ hR hf
  have h1 := (GlobalTheory.BigOnBase.j_thetaMat_base hB i A.μ0 x).trans (one_smul ℂ _).symm
  have h2 := hE i (sgAt D.what₂.embLL v) _ _ h1 fun σ' u hu =>
    hm.2 u (fun x' => csum_eq_zero h.models.HV h.models.jV i A.μ0 (toF_mem i A.μ0 x') hu) σ' x
  have e : sgAt D.what₂.embLL v = v.embedding := if_neg fun h0 => hv (h0.trans R.hv0.symm)
  have h3 := congrArg (fun σ => csumAt (A.MtCSD i A.μ0) σ ((A.fam.L i A.μ0).toF (liftLvl F) (liftSub R F i A.μ0) x)
    ((A.fam.L i A.μ0).toF (liftLvl F) (liftSub R F i A.μ0) x)) e
  have h4 := norm_wC (R := R) (F := F) i v ((thetaMat R F i A.μ0).mulVec x)
  have h5 := hm.1 v x x
  have key : ∀ (E n a : ℝ) (N : ℕ) (p q r : ℂ), 0 < n → n = N → E * p.re ≤ a → p = q → r = ((N : ℕ) : ℂ)⁻¹ * q →
      E * r.re ≤ n⁻¹ * a := by
    intro E n a N p q r k0 k1 k2 k3 k4
    rw [k4, ← k3, ← Complex.ofReal_natCast, ← k1, ← Complex.ofReal_inv, Complex.re_ofReal_mul, mul_left_comm]
    exact mul_le_mul_of_nonneg_left k2 (inv_pos.2 k0).le
  exact (key _ _ _ _ _ _ _ (RealDat.nP_pos (F := F) false) rfl h2 h3 h5).trans h4.ge

open Formalism.MainNotions.S Formalism.IndefR.Datum GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow in

theorem lowForm_six : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ (s : ℕ) (b : ℝ), AdelC R F → (∀ i, GalOut R i 1) → GlobalTheory.Hk3.Core R F → A.fam.Ok s → (∀ i σ, ∃ v : (R.MW i σ).Vec, IsExtVec (R.MW i σ) v) → R.LUnif → GlobalTheory.BigOn.BaseLinks R F → PrimeToHost R A.μ0 → (∀ i, Sizes D i b) → GlobalTheory.BigOn.LowForm R F b := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s b hA hG h hOk hv hU hB ht hb
  refine h.fam.tie.elim fun gramR a => a.elim fun c0R a => a.elim fun c0L hT => ?_
  refine lowForm_of_emb_six hOk h hB fun i σ x y hy hx => ?_
  have g := hG i
  by_cases hσ : OverK σ
  · obtain ⟨v, hv1⟩ := hv i σ
    exact lower_overK_six hA h hU i (hb i) ht hσ hv1 hT g.1 (g.2.1 gramR c0R c0L hT σ hσ) hy (hx σ)
  · have g2 := g.2.2 σ hσ
    obtain ⟨v, hv1⟩ := hv i ((starRingEnd ℂ).comp σ)
    have k1 := lower_overK_six hA h hU i (hb i) ht g2.1 hv1 hT g.1 (g.2.1 gramR c0R c0L hT _ g2.1) hy (hx _)
    have k2 := congrArg Complex.re (g2.2 y y)
    have k3 := (re_inner_self _).symm.trans ((k2.trans (Complex.conj_re _)).trans (re_inner_self _))
    have k4 := (congrArg Complex.re (csumAt_conj (A.MtCSD i A.μ0) σ x x)).trans (Complex.conj_re _)
    exact (congrArg (Real.exp (lowB D i b) * ·) k4).ge.trans (k1.trans k3.ge)

end GlobalTheory.LowForm

end
