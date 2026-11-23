import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGroupActsByLiftTranslationPrincipalType

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GalLift.BaseId

variable {D : D7}

section Row

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

theorem tie_baseChange {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c c' : Coeff l}
    (hle : c.F ≤ c'.F) {r n : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) (V : HSp D)
    (dict : GA D V → Σ k, Frame ((U (σ'.comp (incF c c' hle))).X k).Ψ r) (mu : GA D V → ℂ) (xr : ℝ)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) {Γ : Type} [Group Γ]
    {act : Γ → Rul Xo c →ₗ[c.F] Rul Xo c} {act' : Γ → Rul Xo c' →ₗ[c'.F] Rul Xo c'}
    {Vs : Type} [AddCommGroup Vs] [Module c'.F Vs] {Tup : Type} {dδ : Tup → DeltaDat Xo c' n}
    {Cl' : Tup → Type} [∀ t, Fintype (Cl' t)]
    {w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c'.F} {La : ∀ t, Cl' t → GenLat D.host.E n} {Nc : ∀ t, Cl' t → ℕ}
    {gam : ∀ t, Cl' t → ℕ} {vol : Tup → c'.F} {ep : ∀ t, Cl' t → c'.F} {io : Vs →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F}
    {thAd : ∀ t, (Cl' t → Vs) → (AutQ V → ℂ)} {Pl : ∀ t, (Cl' t → Vs) → Prop} {LL : IntermediateField ℚ ℂ}
    {cc : (U (σ'.comp (incF c c' hle))).Comp → ℂ} {ph : ℂ}
    (htie : OneMapTieC hle LL U σ' V dict mu xr a act act' dδ Cl' w La Nc gam vol ep io thAd Pl cc ph) (t : Tup) :
    ∃ z ∈ Subgroup.center Γ, ∃ ze ∈ LL, (∃ m : ℕ, 0 < m ∧ ze ^ m = 1) ∧ ∀ x : Cl' t → Vs, Pl t x →
      ∃ (f' : Rul Xo c') (m : ℕ) (as : Fin m → c'.F) (fs : Fin m → Rul Xo c), f' ∈ sec Xo c' a n ∧
        IsThClsD Xo c' (dδ t) (w t) (La t) (Nc t) (gam t) (vol t) (ep t) io x f' ∧ (∀ k, fs k ∈ cusp Xo c U a n) ∧
        IsBC hle f' as fs ∧ ∀ q : AutQ V, ph * thAd t x q = ∑ k, ze * σ' (as k) * ((lieFac Dw xr a : ℂ) *
          adel V dict (muPin V dict mu cc) (rdU (U (σ'.comp (incF c c' hle))) (act z (fs k))) q.out) := by
  obtain ⟨-, hC, hA, -, -, z, hz, hrow⟩ := htie
  obtain ⟨ze, hze, hroot, hrow⟩ := hrow t
  refine ⟨z, hz, ze, hze, hroot, fun x hx => ?_⟩
  obtain ⟨⟨f', hf', hcl⟩, hall⟩ := hrow x hx
  have hf's := cusp_le_sec _ _ _ _ _ hf'
  obtain ⟨m, as, fs, hfs, hBC⟩ := hC a n f' hf'
  have hBCz := hA a n z m as fs f' hf's (fun k => cusp_le_sec _ _ _ _ _ (hfs k)) hBC
  refine ⟨f', m, as, fs, hf's, hcl, hfs, hBC, fun q => ?_⟩
  have h1 := hall f' hf's hcl q
  have h2 := GlobalTheory.PhaseRational.rdU_of_isBC hle U σ' hBCz (dict q.out).1 (dict q.out).2
  have h3 : jFn V σ' (rdU (unfBC hle U σ')) dict mu (act' z f') q = mu q.out * ∑ k, σ' (as k) *
      rdU (U (σ'.comp (incF c c' hle))) (act z (fs k)) (dict q.out).1 (dict q.out).2 :=
    congrArg (mu q.out * ·) h2
  rw [h1, h3, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [adel_muPin]
  change ze * cc (dict q.out).1 * _ * _ = _
  ring

end Row

theorem phiC_congr (T : CoreJ D) {j : ℕ} {σ σ' : T.Q.c.F →+* ℂ} (e : σ = σ') {W : HSp D} (hV : T.V j σ = W)
    (hV' : T.V j σ' = W) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) : phiC T hV a f = phiC T hV' a f := by
  subst e
  rfl

theorem proj_model {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {X G : Type} [AddCommGroup X] [Module ℂ X] [Fintype G]
    (e : X →ₗ[ℂ] MMap M) (he : Function.Injective e) (L : G → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (c : G → ℂ)
    (ρ : G → X →ₗ[ℂ] X) (hρ : ∀ g x, e (ρ g x) = postOn M (L g) (e x)) (ph : ℂ) (y y' w : X)
    (hy : e y' = postOn M (∑ g, c g • L g) (e y)) (hw : ph • y = w) : ph • y' = ∑ g, c g • ρ g w := by
  have h1 : y' = ∑ g, c g • ρ g y := by
    apply he
    rw [hy, map_sum]
    simp only [map_smul, hρ]
    ext v x
    simp [postOn, LinearMap.sum_apply, Finset.sum_apply]
  rw [h1, ← hw, Finset.smul_sum]
  exact Finset.sum_congr rfl fun g _ => by rw [map_smul, smul_comm]

theorem eq_of_reps {V : HSp D} {S : D.what₂.Tau → SPar} {θ} {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ}
    {X : Type} [AddCommGroup X] [Module ℂ X] (e : X →ₗ[ℂ] MMap M) (hr : LinearMap.range e = Mult.Mult θ M J χ) (v : M.Vec)
    (hinj : Function.Injective fun x => e x v) (ph : ℂ) (y : X) {n : ℕ} (b : Fin n → ℂ) (u : Fin n → X)
    (h : ∀ q : AutQ V, ph * e y v q.out = ∑ k, b k * e (u k) v q.out) : ph • y = ∑ k, b k • u k := by
  apply hinj
  funext g
  refine GlobalTheory.PhaseRational.eq_of_out
    (GlobalTheory.PhaseRational.mult_leftInv (hr.le (LinearMap.mem_range_self e _)) v)
    (GlobalTheory.PhaseRational.mult_leftInv (hr.le (LinearMap.mem_range_self e _)) v) (fun q => ?_) g
  simpa [map_sum, Finset.sum_apply] using h q

theorem base_identity : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), fw.Evaluates → EvInj T R v₀ → ∀ (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : ℂ), OMPins T R κw v₀ O i → (O i).OneMapOf (κw i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) ph → ∀ h, RepsAt (O i) (v₀ i (sg0 D A)) h → ∃ z ∈ Subgroup.center G, ∃ ze : D.what₂.LL, (∃ m : ℕ, 0 < m ∧ ze ^ m = 1) ∧ ∀ x₀, ∃ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → Cu T κw i), IsClassSum (O i) κw h x₀ a f ∧ ∀ f₁ : Fin n → Cu T κw i, (∀ k, (f₁ k : T.R ((i : ℕ) + 1)) = actG (O i) z (f k : T.R ((i : ℕ) + 1))) → ph • R.thG i A.μ0 (R.jV i A.μ0 x₀) = ∑ g, RealDat.eC (A := A) (sg0 D A) g • R.gW i (sg0 D A) g (∑ k, D.what₂.embLL (ze * a k) • fw.jK i (sg0 D A) (f₁ k)) := by
  intro D G _ _ Pl0 T0 A T _ R F κw v₀ hch fw i hev hinj O ph hpins hone h hreps
  have hrk : (Vc D i).rank = (κw i).n :=
    (D.sp.V_rank _ (Nat.le_add_left _ _) i.2).trans (fw.kap i (D.eTau.symm 1)).2.2.symm
  have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have hpf : T.Q.PinField := fw.laws.toLawsM.pins.2.2.1
  have hres : res T (sg0 D A) = (O i).s0 :=
    (congrArg (res T) hs).trans ((res_embLL T fw.alg_eq hpf).trans (sOv_eq T.toCore (O i).c' (O i).hle).symm)
  have hgood : GoodEmb T.Q.c (res T (sg0 D A)) := base_embedding_good T R fw.alg_eq hpf
  have hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i := (congrArg (T.V ((i : ℕ) + 1)) hres).trans (O i).hV
  have hfield : ∀ b, inC (O i).c' ((O i).jL b) = D.what₂.embLL b := fun b => RingHom.congr_fun hpins.2.lift.field b
  refine (tie_baseChange (O i).hle (T.U ((i : ℕ) + 1)) (inC (O i).c') (Wc D i) (O i).dict (O i).mu
    (xiR D) (wtA (κw i)) hone.2.1 ()).imp fun z hz => ⟨hz.1, hz.2.elim fun ze hze => hze.1.elim fun ze' hze' => ?_⟩
  have hze'' : D.what₂.embLL ze' = ze := hze'
  refine ⟨ze', hze.2.1.imp fun m hm => ⟨hm.1, D.what₂.embLL.injective
    ((map_pow _ _ _).trans ((congrArg (· ^ m) hze'').trans (hm.2.trans (map_one _).symm)))⟩, fun x₀ => ?_⟩
  refine hreps.elim fun J' hJ => (hJ.2.1 x₀).elim fun x hx => ?_
  refine (hze.2.2 x ((hJ.2.2.2 x).2 ⟨x₀, hx⟩)).elim fun f' h1 => h1.elim fun m h1 => h1.elim fun as h1 => h1.elim fun fs h1 => ?_
  have has : ∀ k, ∃ b : D.what₂.LL, D.what₂.embLL b = inC (O i).c' (as k) := fun k => hpins.1.le (as k).2
  have has' : (fun k => (O i).jL (has k).choose) = as := funext fun k =>
    (inC (O i).c').injective ((hfield _).trans (has k).choose_spec)
  have hfs : ∀ k, fs k ∈ T.cuspA ((i : ℕ) + 1) (wtA (κw i)) (κw i).n := fun k => hrk ▸ h1.2.2.1 k
  refine ⟨m, fun k => (has k).choose, fun k => ⟨fs k, hfs k⟩, ⟨x, f', hx, h1.1, h1.2.1, ?_⟩, fun f₁ hf₁ => ?_⟩
  · exact (congrArg (fun b => IsBC (O i).hle f' b fs) has').mpr h1.2.2.2.1
  have hHW := hch.models.HW i (sg0 D A)
  have hy : R.thF i A.μ0 (jVx R i A.μ0 x₀) ∈ LinearMap.range (R.HW i (sg0 D A)).e :=
    hHW.2.1.ge (hch.thP.thF_mem i A.μ0 _)
  refine hy.elim fun y hy => ?_
  refine proj_model (R.MW i (sg0 D A)) (R.HW i (sg0 D A)).e hHW.1
    (fun g => Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)) _ (fun g => R.gW i (sg0 D A) g)
    (hch.models.gW i (sg0 D A)) ph y _ _
    ((hch.thP.thG i A.μ0 (jVx R i A.μ0 x₀)).trans (congrArg (postOn _ (R.eWf i (sg0 D A))) hy.symm)) ?_
  refine eq_of_reps (R.HW i (sg0 D A)).e hHW.2.1 (v₀ i (sg0 D A)) (hinj i _ hgood) ph y _ _ fun q => ?_
  have h2 : (R.HW i (sg0 D A)).e y (v₀ i (sg0 D A)) q.out = (O i).thAd () x q :=
    (congrArg (fun S : MMap (R.MW i (sg0 D A)) => S (v₀ i (sg0 D A)) q.out) hy).trans
      (congrFun (hJ.2.2.1 _ x hx) q).symm
  refine (congrArg (ph * ·) h2).trans ((h1.2.2.2.2 q).trans (Finset.sum_congr rfl fun k _ => congrArg₂ (· * ·) ?_ ?_))
  · exact (congrArg₂ (· * ·) hze'' (has k).choose_spec).symm.trans (map_mul D.what₂.embLL _ _).symm
  · refine (phi_cE T R O i (wtA (κw i)) (actG (O i) z (fs k)) q.out).trans ?_
    refine Eq.symm ((congrFun (hev i _ hgood hV (f₁ k)) q.out).trans ?_)
    exact congrFun ((phiC_congr T hres hV (O i).hV _ _).trans
      (congrArg (phiC T (O i).hV (wtA (κw i))) (hf₁ k))) q.out

end GlobalTheory.GalLift.BaseId

end
