import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralTsumOfFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicScalarBase
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLiftFormsFiniteGroupAction

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows

namespace GlobalTheory.LiftScalarL

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

section Base

open GlobalTheory.Survey.LevelVectorSizeBounds GlobalTheory.BaseScalar

theorem g_mem_core {F : Face D A} (h : GlobalTheory.Hk3.Core R F) {PP : Pl D.host.E} (hP : PP ∈ R.Pg) : ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  obtain ⟨k, hk⟩ := (h.lev.Pg PP).1 hP
  refine ⟨k, ?_⟩
  have h1 := R.C.P.pb_over k
  rw [← hk] at h1
  have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) (D.host.g k : ℕ) ∈ PP.asIdeal := h1
  simpa using h2

open Classical in

theorem isConjChars_core {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T) :
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
    · obtain ⟨l, hl⟩ := g_mem_core R h hg
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

theorem isLevelVec_core {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T) :
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
        obtain ⟨l, hl⟩ := g_mem_core R h hg
        obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := h.lev.Q_pl t PP.1 PP.2
        exact not_both (D.host.g_prime l) hq1 (hq4 l) hl (q_mem hq2)
      simp only [if_neg hn]
    · rfl
  simp only [omegaG_triv, hQ]
  exact h1

open Classical in

theorem chr_core {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T) :
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
      obtain ⟨l, hl⟩ := g_mem_core R h hg
      obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := h.lev.Q_pl t PP hP
      exact not_both (D.host.g_prime l) hq1 (hq4 l) hl (q_mem hq2)
    simp only [if_neg hn]

theorem exists_lift_core {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T) :
    ∃ th : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H, ∀ x, (R.HW i (sg0 D A)).e (th x) = R.thF i t x :=
  exists_factor (R.HW i (sg0 D A)).e (R.thF i t) (R.Wall i (sg0 D A)) (h.models.HW i (sg0 D A)).1
    (h.models.HW i (sg0 D A)).2.1 (h.thP.thF_mem i t)

theorem isLift_core {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T)
    (th : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H) (hth : ∀ x, (R.HW i (sg0 D A)).e (th x) = R.thF i t x) :
    IsLift R i (sg0 D A) (R.ωP i t) (R.ptP i t) (R.cV i) (R.ioP i) (R.νV i t) (R.fdV i t) (R.HV i t) th := by
  refine (h.thP.thF i t).elim fun thP hP => ?_
  unfold IsLift
  intro x v g
  have a := integrableOn_of_isThetaLift hP.1 x (PiTensorProduct.tprod ℂ v) g
  have c := (congrFun (hP.2 x v) g).trans a.2
  refine ⟨a.1, ?_⟩
  rw [hth x]
  exact c

theorem primeToHost_core {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (hc : D.host.ccK = ⊤) (t : T) : PrimeToHost R t := by
  intro PP hP
  rw [hc, Ideal.absNorm_top, mul_one]
  rcases hP with hP | hP
  · obtain ⟨k, hk⟩ := g_mem_core R h hP
    have h1 : Nat.Coprime (D.host.g k) (D.host.QS * D.host.q * D.host.d) := by
      rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, D.ntypes.g_cond k, Nat.gcd_one_left]
    have h2 : Nat.Coprime (D.host.g k) (D.host.QS * D.host.q * D.host.d) := h1
    intro h3
    obtain ⟨x, y, hxy⟩ : IsCoprime ((D.host.g k : ℕ) : 𝓞 D.host.E) ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) := h2.cast
    exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hxy ▸ PP.asIdeal.add_mem (PP.asIdeal.mul_mem_left _ hk) (PP.asIdeal.mul_mem_left _ h3)))
  · intro h3
    refine (h.lev.Q_off t PP hP).1 ?_
    rw [Nat.cast_mul _ D.sp.T]
    exact PP.asIdeal.mul_mem_right _ h3

open Classical in

theorem isLiftDataC_base {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (hc : D.host.ccK = ⊤) (i : Fin D.R.m) (t : T) :
    IsLiftDataC R F i t (sg0 D A) (RingEquiv.refl ℂ) R.triv (R.toLevCh.mu t ((i : ℕ) + 1)) R.eta
      (fun PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP) (R.ωP i t) (onb (R.MW i (sg0 D A)))
      (R.vacP i) (R.vP i t) (R.cV i) (R.ioP i) := by
  have hσ : IsEmbOverK D (sg0 D A) (RingEquiv.refl ℂ) := by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0]; exact isEmbOverK_base
  exact ⟨h, primeToHost_core R h hc t, hσ, isLocal_triv R, isConjChars_core R h i t, h.thP.ωP i t,
    fun ρ => GlobalTheory.IndefiniteRowSideFullHecke.LiftFormsMainTerm.isONBasis_onb _ ρ _ (h.models.order i ρ), isLevelVec_core R h i t, h.thP.pt_theta i t,
    h.models.cV i, by rw [delta_base R]; exact h.thP.ioP i t⟩

end Base

theorem adjoint_eH (hM : R.IsModels) (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (i : Fin D.R.m) :
    LinearMap.adjoint (GlobalTheory.Hk3.eH R i) = GlobalTheory.Hk3.eH R i := by
  have hu : ∀ g x y, ⟪R.gW i (sg0 D A) g x, R.gW i (sg0 D A) g y⟫_ℂ = ⟪x, y⟫_ℂ := fun g x y =>
    LinearIsometry.inner_map_map ⟨R.gW i (sg0 D A) g, GlobalTheory.gW_norm_eq R hM.HW hM.gW hM.νW i _ g⟩ x y
  have hc : ∀ g, starRingEnd ℂ (RealDat.eC (A := A) (sg0 D A) g) = RealDat.eC (A := A) (sg0 D A) g⁻¹ := by
    intro g
    unfold RealDat.eC
    rw [coeff_idemOf, coeff_idemOf, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    have h1 := (hX χ hχ).map_inv (sg0 D A) 1
    have h2 := (hX χ hχ).map_inv (sg0 D A) g⁻¹
    rw [inv_one] at h1
    simp only [map_mul, map_div₀, map_natCast]
    rw [h2, ← h1]
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  unfold GlobalTheory.Hk3.eH
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hc]
  refine Finset.sum_nbij' (fun g => g⁻¹) (fun g => g⁻¹) (by simp) (by simp) (by simp) (by simp) fun g _ => ?_
  rw [← hu g⁻¹, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem e_eH (hM : R.IsModels) (i : Fin D.R.m) (x : (R.HW i (sg0 D A)).H) :
    (R.HW i _).e (GlobalTheory.Hk3.eH R i x) = postOn _ (R.eWf i (sg0 D A)) ((R.HW i _).e x) := by
  unfold GlobalTheory.Hk3.eH RealDat.eWf gaL
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hM.gW i]
  ext v g
  simp [postOn]
  rfl

theorem Wcc_spec (hM : R.IsModels) {SF} (hSF : GlobalTheory.Hk3.IsSF R SF) (i : Fin D.R.m) (t : T) (c : Eig D) {x}
    (hx : x ∈ GlobalTheory.Hk3.Wcc R SF i c) : x ∈ typePart R i (sg0 D A) t R.triv c ∧ GlobalTheory.Hk3.eH R i x = x := by
  classical
  have h1 := (Submodule.mem_inf.1 (Submodule.mem_comap.1 hx)).1
  have h2 := (mem_partFull _ _ _ _ _ _ _).1 (Submodule.mem_inf.1 (Submodule.mem_comap.1 hx)).2
  constructor
  · refine Submodule.mem_comap.2 ((mem_partFull _ _ _ _ _ _ _).2 ⟨h2.1, fun P d Rp hR => h2.2 P d Rp ?_⟩)
    refine hR.elim fun e hR => hR.elim fun f hR => hR.elim fun ϖ hR => hR.elim fun α hR => ⟨e, f, ϖ, α, fun v hv => hR.1 v ?_, hR.2⟩
    obtain ⟨PP, hP, e⟩ := (hSF v).1 hv
    unfold finS
    exact Finset.mem_image.2 ⟨PP, by simp [hP], HeightOneSpectrum.ext e⟩
  · apply (hM.HW i _).1
    rw [e_eH R hM]
    exact MultilinearMap.ext ((mem_goodPart _ _ _ _ _ _).1 h1).2

theorem proj_scalar {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (th thG : X →ₗ[ℂ] Y) (e : Y →ₗ[ℂ] Y)
    (he : LinearMap.adjoint e = e) (h : ∀ x, thG x = e (th x)) {y : Y} (hy : e y = y) {l : ℂ}
    (hl : th (LinearMap.adjoint th y) = l • y) : thG (LinearMap.adjoint thG y) = l • y := by
  obtain rfl : thG = e ∘ₗ th := LinearMap.ext h
  rw [LinearMap.adjoint_comp, he, LinearMap.comp_apply, LinearMap.comp_apply, hy, hl, map_smul, hy]

theorem thG_eq {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T) (th : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H)
    (hth : ∀ x, (R.HW i (sg0 D A)).e (th x) = R.thF i t x) (y : (R.HV i t).H) : R.thG i t y = GlobalTheory.Hk3.eH R i (th y) :=
  (h.models.HW i _).1 ((h.thP.thG i t y).trans ((e_eH R h.models i (th y)).trans (congrArg _ (hth y))).symm)

theorem card_triv : Nat.card (R.triv).H = 1 := Subgroup.card_bot

theorem scalar_base {F : Face D A} (hS : SourceLevelLawC R F) (hI : InnerProductFormulaC R F) (hFo : FockCoefficientC R F)
    (hZ : FiniteZetaL R F) (hL : LevelIndexNormC R F) (hδ : RealLowestKTypeCoeffSquareIntegrable R) (h : GlobalTheory.Hk3.Core R F) (hc : D.host.ccK = ⊤) :
    ∃ a : Fin D.R.m → ℝ, (∀ i, 0 < a i) ∧ ∀ i t (th : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H),
      (∀ x, (R.HW i (sg0 D A)).e (th x) = R.thF i t x) → ∀ c, typePart R i (sg0 D A) t R.triv c ≠ ⊥ →
      ∃ z : ℝ, IsLval R i t c z ∧
        ∀ x ∈ typePart R i (sg0 D A) t R.triv c, th (LinearMap.adjoint th x) = ((a i * z : ℝ) : ℂ) • x := by
  refine (scalar_of_data R hS hI hFo hZ hL hδ h.models.vpos).elim fun a ha => ?_
  refine ⟨fun i => a i (sg0 D A) * Module.finrank ℂ (R.cV i).W * Nat.card (R.triv).H, fun i => ?_, fun i t th hth c hne => ?_⟩
  · haveI : Nontrivial (R.cV i).W := (h.models.cV i).2.2.2.1
    exact mul_pos (mul_pos (ha.1 i _) (by exact_mod_cast Module.finrank_pos)) (by rw [card_triv, Nat.cast_one]; exact one_pos)
  have key := ha.2 i t _ _ _ _ _ _ _ _ _ _ _ _ (isLiftDataC_base R h hc i t) (R.νV i t) (R.fdV i t) (h.models.νV i t) _
    (R.B.L i t).pres.y (R.B.L i t).pres.reps (R.HV i t) (by rw [chr_core R h]; exact h.models.HV i t) th
    (isLift_core R h i t th hth) c hne
  exact key.elim fun B hB => hB.elim fun z hz => ⟨z, ⟨B, hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1⟩, hz.2.2.2.2⟩

theorem aForm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), SourceLevelLawC R F → InnerProductFormulaC R F → FockCoefficientC R F → FiniteZetaL R F → LevelIndexNormC R F → RealLowestKTypeCoeffSquareIntegrable R → Given R F → D.host.ccK = ⊤ → ∀ SF, GlobalTheory.Hk3.IsSF R SF → AForm R SF := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hS hI hFo hZ hL hδ hG hc SF hSF
  have h := hG.core
  refine (scalar_base R hS hI hFo hZ hL hδ h hc).elim fun a ha => ⟨a, ha.1, fun i t c hne => ?_⟩
  refine (exists_lift_core R h i t).elim fun th hth => ?_
  have hle : GlobalTheory.Hk3.Wcc R SF i c ≤ typePart R i (sg0 D A) t R.triv c := fun x hx => (Wcc_spec R h.models hSF i t c hx).1
  refine (ha.2 i t th hth c fun h0 => hne (le_bot_iff.1 (hle.trans h0.le))).elim fun z hz => ⟨z, hz.1, fun x hx => ?_⟩
  exact proj_scalar th _ _ (adjoint_eH R h.models hG.irr i) (thG_eq R h i t th hth) (Wcc_spec R h.models hSF i t c hx).2
    (hz.2 x (hle hx))

end GlobalTheory.LiftScalarL

end
