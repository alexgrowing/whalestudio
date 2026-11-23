import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfPowEqOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaPrimeIsAuxiliarySplitSquarefreeLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyAlgHomOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvOfRoot

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open GlobalTheory.SeriesTie GlobalTheory.SeriesTie.BaseRat GlobalTheory.BigOn.Exp
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.SerRefCore

variable {D : D7}

section Comb

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
  {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
  (j : Fin D.R.m)

def AlgComb (φ : GA D (Wc D j) → ℂ) : Prop :=
  ∃ (n : ℕ) (z : Fin n → ℂ) (g : Fin n → NX.FmK S ((j : ℕ) + 1)), (∀ k, IsAlgebraic ℚ (z k)) ∧
    φ = ∑ k, z k • evW YS v₀ j (g k).val

variable {YS v₀ j}

theorem AlgComb.zero : AlgComb YS v₀ j 0 :=
  ⟨0, Fin.elim0, Fin.elim0, fun k => Fin.elim0 k, by rw [Finset.univ_eq_empty, Finset.sum_empty]⟩

theorem AlgComb.add {φ ψ : GA D (Wc D j) → ℂ} (h1 : AlgComb YS v₀ j φ) (h2 : AlgComb YS v₀ j ψ) :
    AlgComb YS v₀ j (φ + ψ) := by
  obtain ⟨n, z, g, hz, rfl⟩ := h1
  obtain ⟨m, z', g', hz', rfl⟩ := h2
  refine ⟨n + m, Fin.append z z', Fin.append g g', fun k => ?_, ?_⟩
  · refine Fin.addCases (fun a => ?_) (fun a => ?_) k
    · rw [Fin.append_left]; exact hz a
    · rw [Fin.append_right]; exact hz' a
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]

theorem AlgComb.smul {φ : GA D (Wc D j) → ℂ} (h : AlgComb YS v₀ j φ) {a : ℂ} (ha : IsAlgebraic ℚ a) :
    AlgComb YS v₀ j (a • φ) := by
  obtain ⟨n, z, g, hz, rfl⟩ := h
  refine ⟨n, fun k => a * z k, g, fun k => ?_, ?_⟩
  · have hmem : ∀ y : ℂ, y ∈ algebraicClosure ℚ ℂ ↔ IsAlgebraic ℚ y := fun y => mem_algebraicClosure_iff
    exact (hmem _).1 (mul_mem ((hmem _).2 ha) ((hmem _).2 (hz k)))
  · rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => smul_smul _ _ _

theorem isAlgebraic_of_smallInt {y : ℂ} (hy : y ∈ GlobalTheory.BigOn.Exp.smallInt D) : IsAlgebraic ℚ y := by
  obtain ⟨a, rfl⟩ := hy
  exact (Algebra.IsAlgebraic.isAlgebraic (algebraMap (𝓞 ↥D.LL0) ↥D.LL0 a)).algHom (embLL0 D).toRatAlgHom

theorem algComb_of_small {ρ : Setup D.ntw} {i : D.ntw.Tw} {b : Bool}
    (Φ : PolF D (Wc D j).rank (Vc D j).rank →ₗ[ℂ] (GA D (Wc D j) → ℂ))
    (hinj : ∀ P ∈ (ρ.B i j b).valSpace, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P = 0 → P = 0)
    (honto : ∀ F : VV ↥D.LL0 (ρ.B i j b).w.lam, ∃ P ∈ (ρ.B i j b).valSpace, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P =
      coefFn (embLL0 D) (ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank))
    (hΦ : ∀ P ∈ (ρ.B i j b).valSpace, ∀ F : VV ↥D.LL0 (ρ.B i j b).w.lam, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P =
      coefFn (embLL0 D) (ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) → AlgComb YS v₀ j (Φ P))
    {h : GA D (Vc D j)} {P : PolF D (Wc D j).rank (Vc D j).rank} (hP : P ∈ ρ.lat i j b (GlobalTheory.BigOn.Exp.smallInt D) h) :
    AlgComb YS v₀ j (Φ P) := by
  have key : ∀ φ ∈ coefLatFn (embLL0 D) (labLL0 D) (GlobalTheory.BigOn.Exp.smallInt D) (ρ.B i j b).w.lam ((ρ.B i j b).latAt (finPt _ h)),
      ∃ P' ∈ (ρ.B i j b).valSpace, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P' = φ ∧ AlgComb YS v₀ j (Φ P') := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem _ h1 =>
      obtain ⟨F, -, rfl⟩ := h1
      obtain ⟨P', h2, h3⟩ := honto F
      exact ⟨P', h2, h3, hΦ P' h2 F h3⟩
    | zero => exact ⟨0, zero_mem _, map_zero _, by rw [map_zero]; exact AlgComb.zero⟩
    | add _ _ _ _ h1 h2 =>
      obtain ⟨P₁, a1, rfl, f₁⟩ := h1
      obtain ⟨P₂, a2, rfl, f₂⟩ := h2
      exact ⟨P₁ + P₂, add_mem a1 a2, map_add _ _ _, by rw [map_add]; exact f₁.add f₂⟩
    | smul c _ _ h1 =>
      obtain ⟨P₁, a1, rfl, f₁⟩ := h1
      refine ⟨(c : ℂ) • P₁, Submodule.smul_mem _ _ a1, ?_, ?_⟩
      · rw [map_smul]; rfl
      · rw [map_smul]; exact f₁.smul (isAlgebraic_of_smallInt c.2)
  obtain ⟨P', h1, h2, h3⟩ := key _ hP.2
  rwa [sub_eq_zero.1 (hinj (P - P') (sub_mem hP.1 h1) (by rw [map_sub, h2]; exact sub_self _))]

end Comb

end GlobalTheory.SerRefCore

namespace GlobalTheory.SerRefCore

variable {D : D7}

section Main

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {Rl : RealDat3 D A3 T.Q.c.F} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
  {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)}
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

theorem isAlgebraic_of_mem {L : IntermediateField ℚ ℂ} [FiniteDimensional ℚ L] {z : ℂ} (hz : z ∈ L) : IsAlgebraic ℚ z :=
  IntermediateField.isAlgebraic_iff.1 (Algebra.IsAlgebraic.isAlgebraic (⟨z, hz⟩ : L))

theorem algComb_of_ratScalar (hRF : GlobalTheory.NT.RayField) {F : Face D A3.A} (fw : FWTie T Rl.toRealDat κ v₀) (hev : fw.Evaluates)
    (hcore : GlobalTheory.Hk3.Core Rl.toRealDat F) (hio : IoExt Rl.toRealDat) (hpb : T.pb = Rl.C.P.pb)
    (hnV : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) (hgal : IsGalois ℚ D.LL0) (hval : Formalism.L2.Host.ValLL0 D Rl.C)
    (hray : RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange)
    (hroots : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange)
    (hsp : D.host.cls D.host.pde = PrimeClass.splitK ∧ D.host.cls D.host.pde' = PrimeClass.splitK)
    {ρ : Setup D.ntw} (hρ : ρ.Good) (hpin : RealPin Rl cG ρ) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j) {ν : ℂ} (hν : IsRatScalar T Rl κ v₀ hV (ρ.B i j b) ν)
    (s : Finset (Pl D.host.E)) (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank) :
    ρ.IsDatum i j b s h P → P ∈ ρ.lat i j b (GlobalTheory.BigOn.Exp.smallInt D) h →
      AlgComb YS v₀ j (ν • ρ.theta i j b h P) := by
  intro hd hPl
  have hti := tieIn_of_fw fw
  have hrd := readsAs_one YS fw hev hV
  obtain ⟨gR, cR, cL, -, u, hu, c, ph, -, -, rfl, hsc, hrat⟩ := hν
  have hT := hti.laws
  have hB := hρ.base i j b
  have hBo := baseOf_of_realPin hcore.lev hρ hpin i j b

  obtain ⟨nδ, hnδ, hδ⟩ := de_values hρ i j b
  have hcard : Nat.card (ρ.B i j b).G.P.H ≠ 0 := Nat.card_pos.ne'
  haveI := GlobalTheory.CoverSmall.smallF_normal D hgal
  let K : Subfield ℂ := (algebraicClosure ℚ ℂ).toSubfield
  have hK : ∀ {z : ℂ} {m : ℕ}, m ≠ 0 → z ^ m = 1 → z ∈ K := fun hm hz =>
    mem_algebraicClosure_iff.2 (GlobalTheory.BigOn.Exp.isAlgebraic_of_pow_eq_one hm hz)
  obtain ⟨L, _, _, hL0, -, hLr⟩ := exists_normal_roots (GlobalTheory.CoverSmall.smallF D) (k := K)
    (fun z hz => mem_algebraicClosure_iff.2 (isAlgebraic_of_mem hz)) (mul_ne_zero hcard hnδ)
  obtain ⟨C, hpd, hfr, hC⟩ := exists_goodCover_pdAt YS hRF hT hti.alg hval hray hsp (D.ntw.l i) j (κ j).n L hL0
  have hLL : (embLL0 D).fieldRange ≤ C.σ₂.fieldRange := by
    rw [hfr]; exact fun z hz => hL0 hz
  have hdat := isLevDatum_vecBase YS hT hcore hgal hval hroots hsp hρ hpin i j b hLL
    (fun p => by
      have hp1 : (((ρ.B i j b).G.P.chi p : ℂˣ) : ℂ) ^ (Nat.card (ρ.B i j b).G.P.H * nδ) = 1 := by
        rw [pow_mul, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one, one_pow]
      rw [hfr]
      exact hLr _ (hK (mul_ne_zero hcard hnδ) hp1) hp1)
    (fun x => by
      have hp1 : (((ρ.B i j b).de.chi x : Circle) : ℂ) ^ (Nat.card (ρ.B i j b).G.P.H * nδ) = 1 := by
        rw [pow_mul', (hδ x).1, one_pow]
      rw [hfr]
      exact hLr _ (hK (mul_ne_zero hcard hnδ) hp1) hp1)
  rw [← hpd] at hdat
  have htw : IsTwist C.d.pd C.σ₂ (Rl.C.delAt (D.ntw.l i)) (ρ.B i j b).de.chi := by
    rw [hpd]; exact isTwist_delAt Rl.C hval _ (hpin.delta i j b) hLL
  have hω := hρ.weil_base i j b
  have hω' : IsWeilDatumO Rl.ψ (Vc D j) (Wc D j) (Lift.chrTh (Lift.tup Rl.mu0 (ρ.B i j b).de.chi) Rl.eta ((j : ℕ) + 1)).1
      (Lift.chrTh (Lift.tup Rl.mu0 (ρ.B i j b).de.chi) Rl.eta ((j : ℕ) + 1)).2 (ρ.om i j b 1) := by
    have h1 := hω
    rw [Base.IsWeil, mul_one, Base.mu, hBo.ψ, hBo.mu0, hBo.eta] at h1
    exact h1

  have hm : ∀ τ, (ρ.B i j b).w.p τ + (ρ.B i j b).w.q τ ≤ (Wc D j).rank := fun τ => by
    have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (tauE D τ)
    rw [← hB.sig τ] at h2
    exact h2.le
  have hinj := GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D _ _ (ρ.B i j b).w (ρ.B i j b).F.BS hB.wt hm
  refine algComb_of_small ((ph * c) • (ρ.B i j b).theta (ρ.om i j b 1) h) hinj (fun G => ?_) (fun P hP G hPG => ?_) hPl
  · have h3 : coefFn (embLL0 D) (ρ.B i j b).w.lam (G : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) ∈
        (harm (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS).map (harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS) := by
      rw [GlobalTheory.T.fockHarmonicValueSpace_map_eq_dualWeylModuleFunctions D _ _ _ _ hB.wt hm]
      exact Submodule.subset_span ⟨GlobalTheory.CoefModel.mapVV (embLL0 D) _ G, (Scale.coefFn_map _ _ _).symm⟩
    exact h3
  · obtain ⟨G', hG', hPG'⟩ : ∃ G' : VV D.what₂.LL (FWT.lamV D j),
        (∀ m, D.what₂.embLL (MvPolynomial.coeff m (G' : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank)) ∈ (embLL0 D).fieldRange) ∧
        harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P =
          coefFn D.what₂.embLL (FWT.lamV D j) (G' : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) := by
      rw [hPG]
      have hlam := hBo.lam
      generalize (ρ.B i j b).w.lam = lam at G hlam
      subst hlam
      refine ⟨⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV D.LL0.val.toRingHom _ _ G.2⟩, fun m => ⟨MvPolynomial.coeff m G.1, ?_⟩, ?_⟩
      · exact congrArg D.what₂.embLL (MvPolynomial.coeff_map D.LL0.val.toRingHom G.1 m).symm
      · rw [← Scale.coefFn_map, ← Scale.coefFn_map D.what₂.embLL]
        exact congrArg _ (MvPolynomial.map_map _ _ _).symm
    have hP' := hsc.ioP_eq hinj hP (ioP_mem_valSpace hcore hio (hti.hv₀ j _) hB hBo hu _) hPG'
    have hR := ((hrat C hC hLL h hd.fin _ hdat (cL j G') (Submodule.subset_span ⟨G', fun m => hLL (hG' m), rfl⟩)).2 _ _ htw).2 _ hω'
    replace hR : IsRat T j hV C (κ j) ((ph * c) • (ρ.B i j b).theta (ρ.om i j b 1) h P) :=
      (congrArg (IsRat T j hV C (κ j)) (hpin.phase_mul_thetaKO i b hP' ph (ρ.om i j b 1) h (ρ.B i j b).vecBase)).mp hR
    obtain ⟨n, z, x, hz, e⟩ := exists_sum_evW YS hti hnV hcore.lev hpb hrd hC hR fun k hk g => by
      have := GlobalTheory.ExportType.theta_type hB (D.sp.V_sig _) hω (one_mem _) (lifts_one hBo hk) h P g
      rw [show (⟨1, one_mem _⟩ : (ρ.B i j b).G.P.H) = 1 from rfl, map_one, Units.val_one, one_mul] at this
      exact congrArg ((ph * c) * ·) this
    refine ⟨n, z, x, fun k => ?_, ?_⟩
    · have hzk : z k ∈ L := by
        have := hz k
        rw [hfr] at this
        exact this
      exact isAlgebraic_of_mem hzk
    · rw [LinearMap.smul_apply, e, one_smul]

end Main

end GlobalTheory.SerRefCore
