import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockCreationPreservesFockVectorsTwoFrames

noncomputable section

namespace GlobalTheory.FockRealOrth

section Coord

open Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift GlobalTheory.Size GlobalTheory.FockDensity
open scoped ENNReal ComplexOrder

theorem inner_coord {κ : Type} [Fintype κ] [DecidableEq κ] {Q s : Matrix κ κ ℂ} (hQ : Qᴴ = Q) (hs : s * s = 1)
    (hp : (Q * s).PosDef) {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    {ρ : (κ → ℂ) → B →L[ℂ] B} (h : IsHeis (fun x y => (star y ⬝ᵥ Q *ᵥ x).im) ρ) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (Φ : B →L[ℂ] H) (hΦ : ∀ v f, ‖Φ (ρ v f)‖ = ‖Φ f‖) {Y : Type}
    (T : Y → B →L[ℂ] B) (hT : ∀ y v f, T y (ρ v f) = ρ v (T y f)) (S F : Submodule ℂ B)
    (hS : ∀ f, f ∈ S ↔ Sm ρ f ∧ ∀ y, T y f = f)
    (hF : ∀ z, ∀ f ∈ S, f ∈ F → dH ρ z f - I • dH ρ (I • s *ᵥ z) f ∈ F) {v : B} (hvS : v ∈ S) (hvF : v ∈ F)
    (hv : ∀ z, dH ρ z v + I • dH ρ (I • s *ᵥ z) v = 0) {y : H} (hy : ∀ x ∈ F, inner ℂ y (Φ x) = 0) (w : κ → ℂ) :
    inner ℂ y (Φ (ρ w v)) = 0 := by
  obtain ⟨E, J, hJ, hE, hom⟩ := GlobalTheory.T.exists_euclideanCoords_hermitian_cartanInvolution κ Q s hQ hs hp
  have hρ : IsHeis (omJ J) fun v => ρ (E v) :=
    UnitaryOsc.isHeis_comp h (E : EuclideanSpace ℂ κ →L[ℝ] (κ → ℂ)) fun x y => hom x y
  have hm : ∀ G, G ∈ S ↔ Sm (fun v => ρ (E v)) G ∧ ∀ y, T y G = G :=
    fun G => (hS G).trans (and_congr_left' (UnitaryOsc.sm_comp_iff E _ G).symm)
  have hd : ∀ z, dH (fun v => ρ (E v)) z = dH ρ (E z) := fun z => funext fun G => by
    have := E.comp_right_fderiv (f := fun v => ρ v G) (x := 0)
    rw [map_zero] at this
    exact DFunLike.congr_fun this z
  have a1 : ∀ G ∈ S, Sm (fun v => ρ (E v)) G := fun G hG => ((hm G).1 hG).1
  have a2 : ∀ v, ∀ G ∈ S, dH (fun v => ρ (E v)) v G ∈ S := fun v G hG =>
    (hm _).2 ⟨VacBd.sm_dH hρ (a1 G hG) v, fun y => by
      rw [← (dH_comm (T y) (fun v => hT y (E v)) (a1 G hG)).2, ((hm G).1 hG).2]⟩
  have := inner_translate hJ hρ (fun v => hΦ (E v)) a1 a2 (F.comap S.subtype)
    (fun z x hx => by
      rw [Submodule.mem_comap, Submodule.subtype_apply, coe_cE, hd, hd, hE]
      exact hF (E z) x x.2 hx) (v := ⟨v, hvS⟩) hvF
    (fun z => (aE_eq_zero a1 a2 z _).2 (by rw [hd, hd, hE]; exact hv (E z))) (y := y)
    (fun x hx => hy x hx) (E.symm w)
  simpa only [E.apply_symm_apply] using this

end Coord

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isUnit_det_of_onb {k : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} {p : ℕ} (h : IsONBasis G s B p) : IsUnit B.det := by
  obtain ⟨ε, h1, h2, -⟩ := h
  have h3 := congrArg Matrix.det h2
  rw [Matrix.det_mul, Matrix.det_diagonal] at h3
  refine isUnit_iff_ne_zero.2 fun h0 => ?_
  rw [h0, mul_zero] at h3
  obtain ⟨a, -, ha⟩ := Finset.prod_eq_zero_iff.1 h3.symm
  rcases h1 a with ⟨e, -⟩ | ⟨e, -⟩ <;> simp [e] at ha

theorem cplxO_pm {m n : ℕ} {s : Matrix (Fin n) (Fin n) ℂ} {t : Matrix (Fin m) (Fin m) ℂ} (hs : s = 1 ∨ s = -1)
    (ht : t = 1 ∨ t = -1) : ∃ b : Bool, ∀ z, cplxO s t z = ((if b then 1 else -1 : ℂ) * Complex.I) • z := by
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · exact ⟨true, fun z => by simp [cplxO]⟩
  · exact ⟨false, fun z => by simp [cplxO]⟩
  · exact ⟨false, fun z => by simp [cplxO]⟩
  · exact ⟨true, fun z => by simp [cplxO]⟩

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem crea_fock (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {x : DefSp S} {y : DefSp T} (hx : x.Is) (hy : y.Is)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    ∃ Q, pureTensorO ψ θ S T x.s y.s x.B y.B f Q =
      crea (heisO ψ S T) θ τ (cplxO (x.s τ) (y.s τ)) z (pureTensorO ψ θ S T x.s y.s x.B y.B f P) := by
  have hadd : ∀ g g', IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → IsThetaFunO ψ S T (g + g') :=
    fun _ _ => GlobalTheory.OrientedHeis.theta_add
  have hsm : ∀ (a : ℂ) g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (a • g) :=
    fun a _ => GlobalTheory.OrientedHeis.theta_smul a
  have hth : ∀ v g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T
      (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (x.s τ) (y.s τ)) x.B y.B v g) :=
    fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h
  have hX : ∀ v Q,
      pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (x.s τ) (y.s τ)) x.B y.B) f (MvPolynomial.X v * Q) =
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO (x.s τ) (y.s τ)) x.B y.B v
        (pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (x.s τ) (y.s τ)) x.B y.B) f Q) := fun v Q => by
    refine GlobalTheory.FockIndep.pure_X_mul (P := IsThetaFunO ψ S T) hadd hsm hth ?_ ?_ ?_ hf Q v
    · exact fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' hψ hθ i.1 _ hx.cart hy.cart j.1 _ h
    · exact fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h'
    · exact fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h
  have hg : IsThetaFunO ψ S T (pureTensorO ψ θ S T x.s y.s x.B y.B f P) :=
    GlobalTheory.FockIndep.pure_mem (P := IsThetaFunO ψ S T) hadd hsm hth hf P
  obtain ⟨c, rfl⟩ : ∃ c : Fin T.rank → Fin S.rank → ℂ,
      z = ∑ i, ∑ j, c i j • Formalism.IndefR.Datum.unitMap (x.B τ) (y.B τ) i j :=
    ⟨_, GlobalTheory.FockCreaDir.eq_sum_unitMap (isUnit_det_of_onb (hy.onb τ).choose_spec)
      (isUnit_det_of_onb (hx.onb τ).choose_spec) z⟩
  obtain ⟨b, hb⟩ := cplxO_pm (hx.pm τ) (hy.pm τ)
  refine ⟨((fockScale D τ : ℝ) : ℂ) • ∑ i, ∑ j, (if b then c i j else starRingEnd ℂ (c i j)) •
    (MvPolynomial.X (τ, i, j) * P), Eq.symm ?_⟩
  have h1 : ∀ (u : Matrix (Fin T.rank) (Fin S.rank) ℂ) g,
      crea (heisO ψ S T) θ τ (cplxO (x.s τ) (y.s τ)) u g =
        ((fockScale D τ : ℝ) : ℂ) • Formalism.IndefR.Datum.aPlus (heisO ψ S T) θ τ (cplxO (x.s τ) (y.s τ)) u g := fun u g => by
    rw [Formalism.IndefR.Datum.aPlus, smul_smul, mul_inv_cancel₀ (GlobalTheory.FockCreaDir.fockScale_ne_zero D τ), one_smul]
  rw [h1]
  have h2 : pureTensorO ψ θ S T x.s y.s x.B y.B f (((fockScale D τ : ℝ) : ℂ) • ∑ i, ∑ j,
      (if b then c i j else starRingEnd ℂ (c i j)) • (MvPolynomial.X (τ, i, j) * P)) =
      ((fockScale D τ : ℝ) : ℂ) • ∑ i, ∑ j, (if b then c i j else starRingEnd ℂ (c i j)) •
        Formalism.IndefR.Datum.aPlus (heisO ψ S T) θ τ (cplxO (x.s τ) (y.s τ))
          (Formalism.IndefR.Datum.unitMap (x.B τ) (y.B τ) i j) (pureTensorO ψ θ S T x.s y.s x.B y.B f P) := by
    unfold pureTensorO
    simp only [map_smul, map_sum, hX]
    rfl
  rw [h2]
  congr 1
  rw [GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ τ _ _ hg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ τ _ _ hg]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact GlobalTheory.FockSubst.aPlus_dir_smul hψ hθ τ _ _ hg b _ (hb _)

open GlobalTheory.RealWeil GlobalTheory.FockDensity in

theorem inner_toL2_eq_theta_pairing (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) [BorelSpace (WO S T)] [SecondCountableTopology (WO S T)]
    [IsFiniteMeasure (μ.restrict 𝓕)] (G G' : BB ψ S T) :
    inner ℂ (toL2 _ _ (μ.restrict 𝓕) G') (toL2 _ _ (μ.restrict 𝓕) G) = thPair μ 𝓕 (coeL ψ S T G) (coeL ψ S T G') :=
  BoundedContinuousFunction.inner_toLp (μ.restrict 𝓕) G'.1 G.1

open GlobalTheory.RealWeil GlobalTheory.FockDensity GlobalTheory.Mem.Lift GlobalTheory.ChainFr Classical in

theorem orth_real_translate : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ vac, IsVacO ψ θ S T x.s y.s x.L y.L vac → ∀ (v : VolM D T.rank S.rank) f, IsThetaFunO ψ S T f → (∀ P, thPair v.μ v.𝓕 f (pureTensorO ψ θ S T x.s y.s x.B y.B vac P) = 0) → ∀ u : WO S T, u.map (finPart D) = 0 → thPair v.μ v.𝓕 f (heisO ψ S T u vac) = 0 := by
  intro D ψ θ hθ S T x y hx hy vac hvac v f hf ho u hu
  have hψ := hvac.1
  have hv := hvac.2.theta
  have hm := v.covol
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨U, hU, hl⟩ := hv.level
  obtain ⟨-, i2, i3, i4, i5, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : IsFiniteMeasure (v.μ.restrict v.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, hm.2.2]; exact ENNReal.one_lt_top⟩
  have e0 : coeL ψ S T (toB hψ vac hv) = vac := coe_toB hψ vac hv
  have e1 : coeL ψ S T (toB hψ f hf) = f := coe_toB hψ f hf
  have e2 : ∀ G : BB ψ S T, inner ℂ (toL2 _ _ (v.μ.restrict v.𝓕) (toB hψ f hf)) (toL2 _ _ (v.μ.restrict v.𝓕) G) = 0 ↔
      thPair v.μ v.𝓕 f (coeL ψ S T G) = 0 := fun G => by
    rw [inner_eq_zero_symm, inner_toL2_eq_theta_pairing, e1]
  have hF : toB hψ vac hv ∈ (GlobalTheory.Size.thetaLevel ψ S T U).comap (coeL ψ S T) := by
    rw [Submodule.mem_comap, e0]
    exact ⟨hv, hl⟩
  have hc := HM_cartan hx.cart hy.cart
  have key := inner_coord HM_herm hc.1 hc.2 (isHeis_rhoB h hψ) (toL2 _ _ (v.μ.restrict v.𝓕))
    (fun w G => by
      rw [← enorm_sq_inj, ← lintegral_norm_sq_eq_toL2, ← lintegral_norm_sq_eq_toL2]
      exact lintegral_rhoB hψ v.μ v.𝓕 hm.1 hm.2.1 _ G)
    (fun u : {u : WO S T // u ∈ U ∧ u.map (infPart D) = 0} => rhoB hψ u.1) (fun u => rhoB_comm h hψ u.2.2) _
    ((LinearMap.range (pureTensorO ψ θ S T x.s y.s x.B y.B vac)).comap (coeL ψ S T))
    (fun G => (mem_level h hψ hU G).trans
      (and_congr_right' ⟨fun a u => a u.1 u.2.1 u.2.2, fun a u h1 h2 => a ⟨u, h1, h2⟩⟩))
    (fun z G hG hF => by
      have hs := ((mem_level h hψ hU G).1 hG).1
      rw [Submodule.mem_comap, map_sub, map_smul, coe_dH h hψ hs, coe_dH h hψ hs, Finset.smul_sum,
        ← Finset.sum_sub_distrib]
      refine sum_mem fun τ _ => ?_
      obtain ⟨P, hP⟩ := hF
      rw [cpt_cplx, ← hP]
      exact crea_fock hψ hθ hx hy hv τ _ P)
    hF ⟨1, (GlobalTheory.FockIndep.pure_one _).trans e0.symm⟩
    (fun z => fderiv_vac h hψ _ ((mem_level h hψ hU _).1 hF).1 x.s y.s
      (by rw [coe_toB]; exact hvac.2.fock) z)
    (y := toL2 _ _ (v.μ.restrict v.𝓕) (toB hψ f hf))
    (fun G hG => by
      obtain ⟨P, hP⟩ := hG
      rw [e2, ← hP]
      exact ho P) (vecL (GlobalTheory.FockCompare.piW θ T S u))
  rw [e2] at key
  have e3 : iotaV σ S T (vecL (GlobalTheory.FockCompare.piW θ T S u)) = u :=
    h.real_ext (V := T) (W := S) (real_iotaV h _) hu (h.pi_iota T S _)
  have e4 := coe_rhoV (σ := σ) hψ (vecL (GlobalTheory.FockCompare.piW θ T S u)) (toB hψ vac hv)
  rw [e3, coe_toB] at e4
  rw [← e4]
  exact key

end GlobalTheory.FockRealOrth

end
