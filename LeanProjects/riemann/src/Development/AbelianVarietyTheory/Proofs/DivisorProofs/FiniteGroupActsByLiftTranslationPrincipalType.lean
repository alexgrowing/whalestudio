import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Formalism.LocalToGlobal.ProjectiveLattices.ChiProofs
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SecBCAndCuspBC
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ActLevAndActBC

noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.PhaseRational

open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem eq_of_out {V : HSp D} {F F' : GA D V → ℂ} (hF : ∀ γ ∈ GQ V, ∀ g, F (γ * g) = F g)
    (hF' : ∀ γ ∈ GQ V, ∀ g, F' (γ * g) = F' g) (h : ∀ q : AutQ V, F q.out = F' q.out) (g : GA D V) : F g = F' g := by
  let q : AutQ V := Quotient.mk _ g
  have hq : (QuotientGroup.rightRel (GQ V)) g q.out := (QuotientGroup.rightRel (GQ V)).iseqv.symm (Quotient.exact (Quotient.out_eq q))
  rw [QuotientGroup.rightRel_apply] at hq
  have e : q.out = (q.out * g⁻¹) * g := by group
  have h1 := h q
  rw [e, hF _ hq, hF' _ hq] at h1
  exact h1

theorem mult_leftInv {V : HSp D} {S : D.what₂.Tau → SPar} {θ} {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ}
    {T : MMap M} (hT : T ∈ Mult.Mult θ M J χ) (v : M.Vec) : ∀ γ ∈ GQ V, ∀ g, T v (γ * g) = T v g := by
  intro γ hγ g
  induction hT using Submodule.span_induction with
  | mem T h => exact (h.aut v).toIsAutFun.1 γ hγ g
  | zero => rfl
  | add T T' _ _ h h' => simp [h, h']
  | smul c T _ h => simp [h]

theorem adel_muPin_leftInv {C : Core D} (hL : LawsM C) {j : ℕ} (hj : InR D j) {σ : C.Q.c.F →+* ℂ} (hσ : GoodEmb C.Q.c σ)
    {W : HSp D} (hV : C.V j σ = W) (cc : (C.U j σ).Comp → ℂ) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hd : Dom a n)
    {f : C.R j} (hf : f ∈ sec (C.Q.Xo j) C.Q.c a n) : ∀ γ ∈ GQ W, ∀ g,
    adel W (castDict hV (C.dict j σ)) (muPin W (castDict hV (C.dict j σ)) (castDict hV (C.mu j σ)) cc) (rdU (C.U j σ) f) (γ * g) =
    adel W (castDict hV (C.dict j σ)) (muPin W (castDict hV (C.dict j σ)) (castDict hV (C.mu j σ)) cc) (rdU (C.U j σ) f) g := by
  subst hV
  intro γ hγ g
  obtain ⟨th, hr, -, hD⟩ := hL.dictU j hj σ hσ
  have h1 := rdU_leftInv (C.U j σ) (C.V j σ) (C.dict j σ) (C.mu j σ) (C.Kf j σ) th hr (hL.unf j hj σ hσ) hD
    (hL.muUnit j hj σ hσ) hd (hL.chiTriv j hj σ hσ a n hd) hf γ hγ g
  obtain ⟨γ', -, he⟩ := hD.1 γ hγ g
  have h2 : (C.dict j σ (γ * g)).1 = (C.dict j σ g).1 := by rw [he]
  show cc (C.dict j σ (γ * g)).1 * C.mu j σ (γ * g) * _ = cc (C.dict j σ g).1 * C.mu j σ g * _
  rw [mul_assoc, mul_assoc]
  exact congrArg₂ (· * ·) (congrArg cc h2) h1

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem finiteGroup_acts_by_lift_translation_principalType {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (g : G)
    (hg : ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) :
    ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k ∧ ∀ F h,
      Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) F h = F (h * k) := by
  refine ⟨hg.choose, hg.choose_spec, fun F h => ?_⟩
  have h1 : Lev.levChi (Wc D i) (R.βW i) (Lev.flagL (R.datWp i R.triv)) hg.choose = 1 := by
    unfold Lev.levChi levFn
    have : ext1 (Lev.flagL (R.datWp i R.triv)).P.H (Lev.flagL (R.datWp i R.triv)).P.chi
      (rTup (R.βW i) (Lev.flagL (R.datWp i R.triv)) (Lev.finE (Wc D i) hg.choose)) = 1 := Lev.subgroupCharExtension_one_apply _ _
    rw [this]
    simp [Lev.flagL, Lev.withP, LevCh.datWp, Lev.datY]
  show Lev.actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) F h = _
  unfold Lev.actG0
  rw [dif_pos hg]
  simp only [h1, inv_one, one_mul]

theorem rdU_of_isBC {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c c' : Coeff l}
    (hle : c.F ≤ c'.F) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) {m : ℕ} {f' : Rul Xo c'}
    {as : Fin m → c'.F} {fs : Fin m → Rul Xo c} (h : IsBC hle f' as fs) (k : (U (σ'.comp (incF c c' hle))).Comp)
    (x : Frame ((U (σ'.comp (incF c c' hle))).X k).Ψ r) :
    rdU (unfBC hle U σ') f' k x = ∑ i, σ' (as i) * rdU (U (σ'.comp (incF c c' hle))) (fs i) k x := by
  classical
  by_cases hx : x ∈ ((U (σ'.comp (incF c c' hle))).X k).dom
  · let _ : Algebra c.F (CAt σ') := (σ'.comp (incF c c' hle)).toAlgebra
    have h1 := h (CAt σ') (fun _ => rfl) ((unfBC hle U σ').un k ⟨x, hx⟩)
    have e1 : rdU (unfBC hle U σ') f' k x = toC (evR Xo c' f' ((unfBC hle U σ').un k ⟨x, hx⟩)) := dif_pos hx
    have e2 : ∀ i, rdU (U (σ'.comp (incF c c' hle))) (fs i) k x =
      toC (evR Xo c (fs i) ((U (σ'.comp (incF c c' hle))).un k ⟨x, hx⟩)) := fun i => dif_pos hx
    simp only [e2]
    rw [e1]
    exact h1
  · have e1 : rdU (unfBC hle U σ') f' k x = 0 := dif_neg hx
    have e2 : ∀ i, rdU (U (σ'.comp (incF c c' hle))) (fs i) k x = 0 := fun i => dif_neg hx
    simp only [e2, e1, mul_zero, Finset.sum_const_zero]

theorem row_baseChange {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c c' : Coeff l}
    (hle : c.F ≤ c'.F) {r n : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) (V : HSp D)
    (dict : GA D V → Σ k, Frame ((U (σ'.comp (incF c c' hle))).X k).Ψ r) (mu : GA D V → ℂ) (xr : ℝ)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) {Γ : Type} [Group Γ]
    (lev : Γ → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)) (hL : ActLev (Xo := Xo) c lev)
    {Vs : Type} [AddCommGroup Vs] [Module c'.F Vs] {Tup : Type} {dδ : Tup → DeltaDat Xo c' n}
    {Cl' : Tup → Type} [∀ t, Fintype (Cl' t)]
    {w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c'.F} {La : ∀ t, Cl' t → GenLat D.host.E n} {Nc : ∀ t, Cl' t → ℕ}
    {gam : ∀ t, Cl' t → ℕ} {vol : Tup → c'.F} {ep : ∀ t, Cl' t → c'.F} {io : Vs →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F}
    {thAd : ∀ t, (Cl' t → Vs) → (AutQ V → ℂ)} {Pl : ∀ t, (Cl' t → Vs) → Prop} {LL : IntermediateField ℚ ℂ}
    {cc : (U (σ'.comp (incF c c' hle))).Comp → ℂ} {ph : ℂ}
    (hrow : OneMapRow Xo c' V (unfBC hle U σ') dict mu xr a (actLev c' lev) dδ Cl' w La Nc gam vol ep io thAd Pl LL
      (cusp Xo c' (unfBC hle U) a n) cc ph) (t : Tup) (x : Cl' t → Vs) (hx : Pl t x) :
    ∃ (z : Γ) (ze : ℂ) (m : ℕ) (as : Fin m → c'.F) (fs : Fin m → Rul Xo c), ze ∈ LL ∧ (∀ k, fs k ∈ cusp Xo c U a n) ∧
      ∀ q : AutQ V, ph * thAd t x q = ∑ k, ze * σ' (as k) * ((lieFac Dw xr a : ℂ) *
        adel V dict (muPin V dict mu cc) (rdU (U (σ'.comp (incF c c' hle))) (actLev c lev z (fs k))) q.out) := by
  obtain ⟨-, -, z, -, hrow⟩ := hrow
  obtain ⟨ze, hze, -, hrow⟩ := hrow t
  obtain ⟨⟨f', hf', hcl⟩, hall⟩ := hrow x hx
  have hf's := cusp_le_sec _ _ _ _ _ hf'
  obtain ⟨m, as, fs, hfs, hBC⟩ := (GlobalTheory.FieldBC.secBC_and_cuspBC D.host.E H Dw l Xo c c' hle).2 r U a n f' hf'
  have hBCz := (GlobalTheory.FieldBC.actLev_and_actBC D H Dw l Xo c c' hle Γ lev hL).2 a n z m as fs f' hf's
    (fun k => cusp_le_sec _ _ _ _ _ (hfs k)) hBC
  refine ⟨z, ze, m, as, fs, hze, hfs, fun q => ?_⟩
  have h1 := hall f' hf's hcl q
  have h2 := rdU_of_isBC hle U σ' hBCz (dict q.out).1 (dict q.out).2
  have h3 : jFn V σ' (rdU (unfBC hle U σ')) dict mu (actLev c' lev z f') q = mu q.out * ∑ k, σ' (as k) *
      rdU (U (σ'.comp (incF c c' hle))) (actLev c lev z (fs k)) (dict q.out).1 (dict q.out).2 :=
    congrArg (mu q.out * ·) h2
  rw [h1, h3, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [adel_muPin]
  change ze * cc (dict q.out).1 * _ * _ = _
  ring

theorem placed_of_pins {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}
    {K' : Type} [Field K'] {σ' : K' →+* ℂ} {t : T0} {v₀ : (R.MW i (sg0 D A)).Vec} {c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W}
    {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] {ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
    {bad : ℕ} {Mb I : Ideal (𝓞 D.host.E)} {N : Submodule (𝓞 D.host.E) La} {Cl : Type} [Fintype Cl]
    {Lh : Cl → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)} {gam : Cl → ℕ} {vol : K'}
    {B : Ideal (𝓞 D.host.E) → K'} {xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ}
    {φ : (Fin (Vc D i).rank → La ⧸ N) → K'} {thAd : (Cl → VsV D i K') → AutQ (Wc D i) → ℂ}
    {Plc : (Cl → VsV D i K') → Prop} (h : ThPinsT R i σ' t v₀ c0' ι bad Mb I N Lh gam vol B xi φ thAd Plc)
    (x : A.fam.amb.FL i t) : ∃ y, Plc y ∧ ∀ q, thAd y q = R.thF i t (jVx R i t x) v₀ q.out :=
  h.reps.elim fun _ h => h.elim fun _ h => (h.2.1 x).imp fun y hy =>
    ⟨(h.2.2.2 y).2 ⟨x, hy⟩, fun q => congrFun (h.2.2.1 _ y hy) q⟩

theorem comb_fin {K M X ι : Type} [Fintype ι] (e : K → ℂ) (P : M → X → ℂ) (F : X → ℂ) (a : ι → K) (f : ι → M)
    (h : ∀ x, F x = ∑ k, e (a k) * P (f k) x) :
    ∃ (n : ℕ) (a : Fin n → K) (f : Fin n → M), ∀ x, F x = ∑ k, e (a k) * P (f k) x :=
  ⟨Fintype.card ι, fun k => a ((Fintype.equivFin ι).symm k), fun k => f ((Fintype.equivFin ι).symm k), fun x =>
    (h x).trans ((Fintype.equivFin ι).symm.sum_comp fun k => e (a k) * P (f k) x).symm⟩

section Main

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  (O : OMDat C R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))

abbrev IdentityAt (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (ph : ℂ) : Prop :=
  OneMapRow (C.Q.Xo ((i : ℕ) + 1)) O.c' (Wc D i)
    (unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c')) O.dict O.mu (xiR D) (wtA κ)
    (actLev O.c' O.lev2) O.dδ O.Cl' O.w O.La O.Nc O.gam O.vol O.ep O.io
    O.thAd O.Plc D.what₂.embLL.toRatAlgHom.fieldRange
    (cusp (C.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (C.U ((i : ℕ) + 1))) (wtA κ) (Vc D i).rank) cc ph

theorem lift_rational (v₀ : (R.MW i (sg0 D A)).Vec) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (ph : ℂ)
    {ι : (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ}
    (hF : O.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange) (hpins : O.Pins κ v₀ ι x₀)
    (hlaws : LawsM C) (hn : κ.n = D.R.nV) (hmem : R.thP_thF_mem)
    (hequiv : O.EquivAt κ cc) (hid : IdentityAt O κ cc ph) (t : Tp) (t₀ : T0) (ht : tup t = t₀)
    (x : A.fam.amb.FL i t₀) :
    ∃ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n), ∀ h,
      ph * R.thF i t₀ (jVx R i t₀ x) v₀ h =
        ∑ k, D.what₂.embLL (a k) * ((lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * O.phi cc (f k : C.R ((i : ℕ) + 1)) h) := by
  revert x
  refine ht.rec fun x => ?_
  have hrk : (Vc D i).rank = κ.n := (D.sp.V_rank _ (Nat.le_add_left _ _) i.2).trans hn.symm
  refine (placed_of_pins (hpins.tuple t) x).elim fun y hy => ?_
  refine (row_baseChange O.hle (C.U ((i : ℕ) + 1)) (inC O.c') (Wc D i) O.dict O.mu
    (xiR D) (wtA κ) O.lev2 hpins.act.1 hid t y hy.1).elim fun z h => h.elim fun ze h => h.elim fun m h => h.elim fun as h =>
      h.elim fun fs h => h.1.elim fun ze' hze' => (hpins.lift.lev z).elim fun kz hkz => ?_
  have hz : ∀ k, actLev C.Q.c O.lev2 z (fs k) ∈ C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n := fun k =>
    (hequiv z kz hkz.1 (fs k) (hrk ▸ h.2.1 k)).1
  have has : ∀ k, ∃ b : D.what₂.LL, D.what₂.embLL b = inC O.c' (as k) := fun k => hF.le (as k).2
  refine ⟨m, fun k => ze' * (has k).choose, fun k => ⟨_, hz k⟩, ?_⟩
  refine eq_of_out (V := Wc D i) (fun γ hγ g => ?_) (fun γ hγ g => ?_) fun q => ?_
  · exact congrArg (ph * ·) (mult_leftInv (hmem i (tup t) _) v₀ γ hγ g)
  · refine Finset.sum_congr rfl fun k _ => congrArg (_ * ·) (congrArg (_ * ·) ?_)
    exact adel_muPin_leftInv hlaws ⟨Nat.le_add_left _ _, i.2⟩ (σ := O.s0) C.good_σ₀ O.hV cc (dom_wtA κ)
      (cusp_le_sec _ _ _ _ _ (hz k)) γ hγ g
  · refine (congrArg (ph * ·) (hy.2 q)).symm.trans ((h.2.2 q).trans ?_)
    refine Finset.sum_congr rfl fun k _ => congrArg (· * _) ?_
    exact (congrArg₂ (· * ·) hze' (has k).choose_spec).symm.trans (map_mul D.what₂.embLL _ _).symm

theorem proj_rational (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (s ph : ℂ)
    (hlift : ∀ g, ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) (hchi : R.grp_chiW)
    (hequiv : O.EquivAt κ cc) (F : GA D (Wc D i) → ℂ) (n : ℕ) (a : Fin n → D.what₂.LL)
    (f : Fin n → C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n)
    (hF : ∀ h, ph * F h = ∑ k, D.what₂.embLL (a k) * (s * O.phi cc (f k : C.R ((i : ℕ) + 1)) h)) :
    ∃ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n), ∀ h,
      ph * R.eWf i (sg0 D A) F h = ∑ k, D.what₂.embLL (a k) * (s * O.phi cc (f k : C.R ((i : ℕ) + 1)) h) := by
  have hact := fun g => finiteGroup_acts_by_lift_translation_principalType R i g (hlift g)
  have heq := fun g (k : Fin n) => hequiv g _ (hact g).choose_spec.1 _ (f k).2
  refine comb_fin D.what₂.embLL
    (fun (u : C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n) h => s * O.phi cc (u : C.R ((i : ℕ) + 1)) h)
    (fun h => ph * R.eWf i (sg0 D A) F h)
    (fun p : G × Fin n => (idemOf A.X).coeff p.1 * ((((R.FW i).chi p.1)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) * a p.2)
    (fun p => ⟨_, (heq p.1 p.2).1⟩) fun h => ?_
  have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have h1 : R.eWf i (sg0 D A) F h = ∑ g, D.what₂.embLL ((idemOf A.X).coeff g) * F (h * (hact g).choose) := by
    unfold RealDat.eWf gaL
    rw [LinearMap.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← (hact g).choose_spec.2 F h, ← hs]
    rfl
  rw [h1, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [mul_left_comm, hF, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h2 := ((heq g k).2 h).trans (congrArg (· * _) (hchi i g).symm)
  have h3 : D.what₂.embLL ((((R.FW i).chi g)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) *
      D.what₂.embLL (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  dsimp only
  rw [h2, map_mul, map_mul]
  linear_combination (-(D.what₂.embLL ((idemOf A.X).coeff g) * D.what₂.embLL (a k) * s *
    O.phi cc (f k : C.R ((i : ℕ) + 1)) (h * (hact g).choose))) * h3

theorem phRat_of_identity (v₀ : (R.MW i (sg0 D A)).Vec) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (ph : ℂ)
    {ι : (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ} (t : Tp) (ht : tup t = A.μ0)
    (hF : O.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange) (hpins : O.Pins κ v₀ ι x₀)
    (hlaws : LawsM C) (hn : κ.n = D.R.nV) (hchi : R.grp_chiW) (hmem : R.thP_thF_mem) (hG : R.thP_thG)
    (hequiv : O.EquivAt κ cc) (hid : IdentityAt O κ cc ph) : O.PhRat κ v₀ cc ph := by
  have key := lift_rational O κ v₀ cc ph hF hpins hlaws hn hmem hequiv hid t A.μ0 ht
  intro x
  refine (key x).elim fun n h => h.elim fun a h => h.elim fun f h => ?_
  have h1 := proj_rational O κ cc _ ph (fun g => (hpins.lift.lev g).imp fun _ hk => hk.1) hchi hequiv _ n a f h
  refine h1.imp fun _ h2 => h2.imp fun _ h2 => h2.imp fun _ h2 g => Eq.trans (congrArg (ph * ·) ?_) (h2 g)
  exact congrArg (fun S : MMap (R.MW i (sg0 D A)) => S v₀ g) (hG i A.μ0 (jVx R i A.μ0 x))

end Main

section Class

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
  (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m)

end Class

end GlobalTheory.PhaseRational
