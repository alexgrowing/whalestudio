import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralFramedPointOfLevelMove
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelActionMemCuspForms
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevActMemMlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetReducedBlockEqResidueDet

noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.L2.Pj Formalism.IndefR.FWT
open scoped InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeoLevel

section Core

variable {D : D7} {T : Core D} {j : ℕ} {G : Type} [Group G]
  {lev : G → ((T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La) × ((T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La)}

theorem actLev_mem_cuspA (h : LawsM T) (hj : InR D j) (hL : ActLev (Xo := T.Q.Xo j) T.Q.c lev) (w : WeightFamilies.Wt D j) (g : G)
    {f : T.R j} (hf : f ∈ T.cuspA j (wtA w) w.n) : actLev (Xo := T.Q.Xo j) T.Q.c lev g f ∈ T.cuspA j (wtA w) w.n := by
  have hp := h.pins
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    rw [(hp.2.2.2 j hj).1, (hp.2.2.2 j hj).2.1]
    have := hj.1; have := hj.2; have := D.R.m_add_three_le_k
    simp only [Ranks.sigW]; omega
  obtain ⟨hs, hc⟩ := (mem_cusp _ _ _ _ _ _).1 hf
  have hg : actLev (Xo := T.Q.Xo j) T.Q.c lev g f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n :=
    Formalism.L2.Pj.actL_mem _ _ _ _ hL.total hL.nat hL.bor _ g hs
  refine (mem_cusp _ _ _ _ _ _).2 ⟨hg, fun σ hσ => holCusp_mem_holSub _ _ fun k => ?_⟩
  have hU := h.unf j hj σ hσ
  refine GlobalTheory.LevelCusp.rdU_mem_SS (U := Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hσ hU (hU.1 ▸ hpq)
    (fun k k' τ => (h.xiAbs j hj σ hσ k τ).trans (h.xiAbs j hj σ hσ k' τ).symm) (dom_wtA w) hs hg
    (fun k => GlobalTheory.CuspSecFin.mem_SS_of_mem_holSub _ _ (hc σ hσ) k) (fun y => ?_) k
  obtain ⟨ρ, ν, -, -, hm⟩ := mvPt_spec hL.total g y
  exact ⟨ρ, ν, _, hm, evalAt_actL hL (h.evalWD j hj) frMap_trans_id g hs.1 y⟩

theorem actLev_integral (h : LawsM T) (hj : InR D j) (hL : ActLev (Xo := T.Q.Xo j) T.Q.c lev)
    {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} (g : G) {f : T.R j} (hf : f ∈ T.cuspA j a n)
    (hint : ∀ la (y : T.PtM j la), 0 ≤ y.1 f) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtM j la) :
    0 ≤ y.1 (actLev (Xo := T.Q.Xo j) T.Q.c lev g f) := by
  have hnat := ((mem_cusp _ _ _ _ _ _).1 hf).1.1
  obtain ⟨_, ⟨q, S, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩ := y
  let := io.toAlgebra
  have hmv := mvPt_spec hL.total g y.1
  let y' : IntFr (T.Q.Xo j) T.Q.c S io :=
    ⟨_, GlobalTheory.FormTies.fromTest_mvPt hL g y.2.1,
      GlobalTheory.FormTies.LevelMove.integral_of_levR _ _ _ _ _ _ (lev g) S io y.1 _ hmv y.2.2⟩
  have h0 : 0 ≤ nval S.V e (evI y' f) := hint la ⟨_, PtV.mk la ho y' hy () trivial, rfl⟩
  have e1 : evI y (actLev (Xo := T.Q.Xo j) T.Q.c lev g f) = evI y' f :=
    evalAt_actL hL (h.evalWD j hj) frMap_trans_id g hnat y.1
  show 0 ≤ nval S.V e (evI y (actLev (Xo := T.Q.Xo j) T.Q.c lev g f))
  rw [e1]
  exact h0

def levRep (h : LawsM T) (hj : InR D j) (hL : ActLev (Xo := T.Q.Xo j) T.Q.c lev) (w : WeightFamilies.Wt D j) :
    G →* (T.cuspA j (wtA w) w.n →ₗ[T.Q.c.F] T.cuspA j (wtA w) w.n) where
  toFun g := (actLev (Xo := T.Q.Xo j) T.Q.c lev g).restrict fun _ hf => actLev_mem_cuspA h hj hL w g hf
  map_one' := LinearMap.ext fun f => Subtype.ext
    (Formalism.L2.Pj.actL_one _ _ _ hL.total hL.func hL.one ((mem_cusp _ _ _ _ _ _).1 f.2).1.1)
  map_mul' g g' := LinearMap.ext fun f => Subtype.ext
    (Formalism.L2.Pj.actL_mul _ _ _ hL.total hL.func hL.mul g g' ((mem_cusp _ _ _ _ _ _).1 f.2).1.1)

end Core

section Model

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem eval_injective (M : DSModel V S) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (e : H →ₗ[ℂ] MMap M) (d : ℂ)
    (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (hip : ∀ x y, inner ℂ x y = d * ipM M μ 𝓕 (e x) (e y)) (v : M.Vec)
    (hv : IsUnitV v) : Function.Injective fun x : H => e x v := by
  have key : ∀ x : H, e x v = 0 → x = 0 := fun x hx => by
    rw [← inner_self_eq_zero (𝕜 := ℂ), hip]
    by_cases hc : ∃ c, IsMultIP M μ 𝓕 (e x) (e x) c
    · have h1 := (ipM_spec M μ 𝓕 _ _ hc v v).2
      have h2 : ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ = 1 :=
        Finset.prod_eq_one fun τ _ => by rw [inner_self_eq_norm_sq_to_K, hv τ]; simp
      rw [hx, h2, mul_one] at h1
      rw [← h1]
      simp
    · rw [ipM, dif_neg hc, mul_zero]
  intro x y hxy
  refine sub_eq_zero.1 (key _ ?_)
  rw [map_sub]
  exact sub_eq_zero.2 hxy

end Model

section Head

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem actW_apply {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (g : G)
    (hk : ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) (σ : D.what₂.LL →+* ℂ) (X : MMap (R.MW i σ))
    (v : (R.MW i σ).Vec) (h : GA D (Wc D i)) : actW R i σ g X v h = X v (h * hk.choose) := by
  have h1 : Lev.levChi (Wc D i) (R.βW i) (Lev.flagL (R.datWp i R.triv)) hk.choose = 1 := by
    have : levFn (R.βW i) (Lev.flagL (R.datWp i R.triv)) (Lev.finE (Wc D i) hk.choose) = 1 := by
      unfold levFn
      rw [Finset.prod_eq_one, Finset.prod_eq_one, mul_one, mul_one]
      · unfold ext1
        split_ifs <;> rfl
      · intro PP hPP
        exact absurd hPP (Finset.notMem_empty _)
      · intro PP _
        exact Finset.prod_eq_one fun c hc => absurd (Finset.mem_range.1 hc) (Nat.not_lt_zero _)
    rw [Lev.levChi, this, Units.val_one]
  show Lev.actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) (X v) h = _
  have h2 : Lev.actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) (X v) = fun h =>
      (Lev.levChi (Wc D i) (R.βW i) (Lev.flagL (R.datWp i R.triv)) hk.choose)⁻¹ * X v (h * hk.choose) := dif_pos hk
  rw [h2, h1, inv_one]
  exact one_mul _

theorem chiIs_of_values {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (h1 : ∀ g, ∃ a, D.what₂.embLL a = (chiC R i g : ℂ)) : ChiIs R i (chiTop R i) := by
  choose a ha using h1
  have hne : ∀ g, a g ≠ 0 := fun g h0 => (chiC R i g).ne_zero (by rw [← ha, h0, map_zero])
  have hex : ∃ chi, ChiIs R i chi :=
    ⟨MonoidHom.mk' (fun g => Units.mk0 (a g) (hne g)) fun g g' => Units.ext (D.what₂.embLL.injective (by
      simp only [Units.val_mk0, Units.val_mul, map_mul, ha, chiC_mul])), ha⟩
  rw [chiTop, dif_pos hex]
  exact hex.choose_spec

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

omit [Algebra T.Q.c.F D.what₂.LL] in
theorem phiC_eq (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (f : T.R ((i : ℕ) + 1)) (h : GA D (Wc D i)) :
    phiC T hV a f h = (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℂ) * phiAt T i σ hV (T.cE ((i : ℕ) + 1) σ) f h := by
  have key : ∀ (W : HSp D) (hV : T.V ((i : ℕ) + 1) σ = W) (g : GA D W), phiC T hV a f g =
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℂ) * castDict hV (adel (T.V ((i : ℕ) + 1) σ) (T.dict ((i : ℕ) + 1) σ)
        (muPin (T.V ((i : ℕ) + 1) σ) (T.dict ((i : ℕ) + 1) σ) (T.mu ((i : ℕ) + 1) σ) (T.cE ((i : ℕ) + 1) σ))
        (rdU (T.U ((i : ℕ) + 1) σ) f)) g := by
    intro W hV g
    subst hV
    rfl
  exact key _ hV h

theorem carried_of_eval (hW : R.models_HW) (hg : R.models_gW) {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} {g : G}
    (hk : ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) {v : (R.MW i σ).Vec} (hv : IsUnitV v)
    {x x' : (R.HW i σ).H} {c : ℂ} (h : ∀ u, evAt R i σ v x' u = c * evAt R i σ v x (u * hk.choose)) :
    (R.HW i σ).e x' = c • actW R i σ g ((R.HW i σ).e x) := by
  have h1 : actW R i σ g ((R.HW i σ).e x) = (R.HW i σ).e (R.gW i σ g x) := (hg i σ g x).symm
  rw [h1, ← map_smul]
  refine congrArg _ (eval_injective (R.MW i σ) (R.HW i σ).e _ (R.νW i) (R.fdW i) (hW i σ).2.2 v hv ?_)
  funext u
  show (R.HW i σ).e x' v u = (R.HW i σ).e (c • R.gW i σ g x) v u
  rw [map_smul, ← h1]
  exact (h u).trans (congrArg (c * ·) (actW_apply R i g hk σ _ v u).symm)

set_option maxHeartbeats 800000 in

theorem isGeoAct_levRep (ht : TieIn T R κ v₀) (hW : R.models_HW) (hg : R.models_gW) (i : Fin D.R.m) {Tp : Type} {tup : Tp → T0}
    (O : OMDat T.toCore R i Tp tup) (hL : ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c O.lev2)
    (hk : ∀ g, ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k)
    (hE : ∀ σ, GoodEmb T.Q.c σ → ∀ hV, EqAt T R κ O σ hV (T.cE ((i : ℕ) + 1) σ)) :
    IsGeoAct T R κ v₀ i (levRep ht.laws.toLawsM (inR i) hL (κ i)) := by
  have hchi : ChiIs R i (chiTop R i) := chiIs_of_values R i fun g => by
    obtain ⟨-, y, hy, -⟩ := hE _ T.good_σ₀ (ht.laws.spaceW _ (inR i) _ T.good_σ₀) g _ (hk g).choose_spec 0 (zero_mem _)
    exact ⟨_, hy.trans (Units.coe_prod _ _).symm⟩
  have key : ∀ σ, GoodEmb T.Q.c σ → ∀ (hV : T.V ((i : ℕ) + 1) σ = Wc D i) g (f : Cu T κ i), ∃ y : T.Q.c.F,
      ((chiTop R i g : D.what₂.LLˣ) : D.what₂.LL) = algebraMap _ _ y ∧ ∀ u,
        phiC T hV (wtA (κ i)) (levRep ht.laws.toLawsM (inR i) hL (κ i) g f : T.R ((i : ℕ) + 1)) u =
          σ y * phiC T hV (wtA (κ i)) (f : T.R ((i : ℕ) + 1)) (u * (hk g).choose) := fun σ hσ hV g f => by
    obtain ⟨-, y, hy, h⟩ := hE σ hσ hV g _ (hk g).choose_spec f f.2
    refine ⟨y, D.what₂.embLL.injective ((hchi g).trans ((Units.coe_prod _ _).trans hy.symm)), fun u => ?_⟩
    rw [phiC_eq, phiC_eq, mul_left_comm]
    exact congrArg _ (h u)
  refine ⟨fun σ g f => ?_, fun g f hf => actLev_integral ht.laws.toLawsM (inR i) hL g f.2 hf⟩
  have zero : jTop T R κ v₀ i σ = 0 → (R.HW i σ).e (jTop T R κ v₀ i σ (levRep ht.laws.toLawsM (inR i) hL (κ i) g f)) =
      σ ((chiTop R i g : D.what₂.LLˣ) : D.what₂.LL) • actW R i σ g ((R.HW i σ).e (jTop T R κ v₀ i σ f)) := fun h0 => by
    simp only [h0, LinearMap.zero_apply, map_zero, smul_zero]
  by_cases hσ : GoodEmb T.Q.c (res T σ)
  · have hV := ht.laws.spaceW _ (inR i) _ hσ
    by_cases hj : JEvAt T R κ v₀ i σ hV
    · obtain ⟨y, hy, h⟩ := key _ hσ hV g f
      refine carried_of_eval hW hg (hk g) (v := v₀ i σ) (fun τ => ((ht.hv₀ i σ).1 τ).1) fun u => ?_
      rw [jTop_good T R κ v₀ hσ hV hj, jTop_good T R κ v₀ hσ hV hj, hy]
      exact h u
    · exact zero (jTop_good0 T R κ v₀ hσ hV hj)
  · have hσ' := good_resC T hσ
    have hV := ht.laws.spaceW _ (inR i) _ hσ'
    by_cases hj : JEvBarAt T R κ i σ hV
    · obtain ⟨y, hy, h⟩ := key _ hσ' hV g f
      obtain ⟨v, hv, hev⟩ := jTop_bar T R κ v₀ hσ hV hj
      refine carried_of_eval hW hg (hk g) hv fun u => ?_
      rw [hev, hev, hy]
      exact (congrArg (starRingEnd ℂ) (h u)).trans ((map_mul _ _ _).trans (congrArg (· * _) (Complex.conj_conj _)))
    · exact zero (top_lift_vanishes_off_good_embeddings T R κ v₀ hσ hV hj)

omit [Algebra T.Q.c.F D.what₂.LL] in
theorem castDict_mu {j : ℕ} {σ : T.Q.c.F →+* ℂ} {χ : (AE D)ˣ →* Circle} (h : MuVal (T.V j σ) χ (T.mu j σ)) {W : HSp D}
    (hV : T.V j σ = W) {k : GA D W} {x : (AE D)ˣ} (hx : IsDetRoot W k x) :
    castDict hV (T.mu j σ) k = ((χ x : Circle) : ℂ) := by
  subst hV
  exact h.2 k x hx

theorem mem_places_iff (hR : R.toLevCh.Is A.μ0) (h : LawsM T.toCore) (hpb : T.pb = R.C.P.pb) (P : Pl D.host.E) :
    P ∈ R.Pg ↔ T.Q.l.Mb ≤ P.asIdeal := by
  rw [hR.Pg, h.half.2, P.isPrime.prod_le, hpb]
  refine exists_congr fun k => ?_
  rw [and_iff_right (Finset.mem_univ k), Ideal.map_le_iff_le_comap]
  constructor
  · intro h
    have h' : P.under (𝓞 D.host.K) = R.C.P.pb k := h
    rw [← h']
    exact le_rfl
  · intro h
    exact HeightOneSpectrum.ext ((R.C.P.pb k).isMaximal.eq_of_le (P.under (𝓞 D.host.K)).isPrime.ne_top h).symm

theorem mu_lift (hR : R.toLevCh.Is A.μ0) (ht : TieIn T R κ v₀) (hpb : T.pb = R.C.P.pb) (i : Fin D.R.m) {σ : T.Q.c.F →+* ℂ}
    (hσ : GoodEmb T.Q.c σ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i) {g : G} {k : GA D (Wc D i)}
    (hk : Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) :
    ∃ y : T.Q.c.F, D.what₂.embLL (algebraMap T.Q.c.F D.what₂.LL y) = (chiC R i g : ℂ) ∧
      σ y * castDict hV (T.mu ((i : ℕ) + 1) σ) k = 1 := by
  obtain ⟨a, b, s, s', hb, hs, hs', hin, hout⟩ := exists_half_elements T.Q.l R.Pg (mem_places_iff hR ht.laws.toLawsM hpb)
  have hM : T.Q.l.M = D.host.g 0 * D.host.g 1 := ht.laws.pins.2.1.1
  obtain ⟨x, hx, hroot, hval⟩ := exists_root_char (L := R.datWp i R.triv) (rank_Wc i).symm hk (hR.mu0 i) (R.C.isMu0 i).tame
    T.Q.l.M (fun P hP => (R.C.isMu0 i).unr P fun n hn => hP (by
      have hn' : ((D.host.g n : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := hn
      rw [hM, Nat.cast_mul]
      fin_cases n
      · exact Ideal.mul_mem_right _ _ hn'
      · exact Ideal.mul_mem_left _ _ hn'))
    (fun P => (R.chi ((i : ℕ) + 1) P)⁻¹) (hR.chi i) a b s s' hb hs hs' hin hout
  obtain ⟨y, hy0, hy⟩ := ht.laws.muConj _ (inR i) σ hσ x hx
  have h1 : ((R.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = (chiC R i g : ℂ)⁻¹ := by
    rw [hval, chiC, Units.coe_prod, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun P _ => Units.val_inv_eq_inv_val _
  rw [chiTie_of_chiR T R ht.alg ht.laws.pins.2.2.1 ht.chiR i, h1] at hy0
  have h2 : ∀ z, D.what₂.embLL (algebraMap T.Q.c.F D.what₂.LL z) = T.σ₀ z :=
    RingHom.congr_fun (res_embLL T ht.alg ht.laws.pins.2.2.1)
  refine ⟨y⁻¹, by rw [h2, map_inv₀, ← hy0, inv_inv], ?_⟩
  rw [castDict_mu (ht.laws.muVal _ (inR i) σ hσ) hV hroot, map_inv₀, ← hy]
  exact inv_mul_cancel₀ (Circle.coe_ne_zero _)

variable (T) in

def frameRead (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (c : (T.U ((i : ℕ) + 1) σ).Comp → ℂ)
    (f : T.R ((i : ℕ) + 1)) (h : GA D (Wc D i)) : ℂ :=
  c (castDict hV (T.dict ((i : ℕ) + 1) σ) h).1 * rdU (T.U ((i : ℕ) + 1) σ) f (castDict hV (T.dict ((i : ℕ) + 1) σ) h).1
    (castDict hV (T.dict ((i : ℕ) + 1) σ) h).2

omit [Algebra T.Q.c.F D.what₂.LL] in
theorem phiAt_eq (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (c : (T.U ((i : ℕ) + 1) σ).Comp → ℂ)
    (f : T.R ((i : ℕ) + 1)) (h : GA D (Wc D i)) :
    phiAt T i σ hV c f h = castDict hV (T.mu ((i : ℕ) + 1) σ) h * frameRead T i σ hV c f h :=
  (mul_assoc _ _ _).trans (mul_left_comm _ _ _)

omit [Algebra T.Q.c.F D.what₂.LL] in
theorem castDict_mu_mul {j : ℕ} {σ : T.Q.c.F →+* ℂ} (h : ∀ g g', T.mu j σ (g * g') = T.mu j σ g * T.mu j σ g') {W : HSp D}
    (hV : T.V j σ = W) (g g' : GA D W) :
    castDict hV (T.mu j σ) (g * g') = castDict hV (T.mu j σ) g * castDict hV (T.mu j σ) g' := by
  subst hV
  exact h g g'

theorem eqAt_iff (hR : R.toLevCh.Is A.μ0) (ht : TieIn T R κ v₀) (hpb : T.pb = R.C.P.pb) {i : Fin D.R.m} {Tp : Type}
    {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup) (hL : ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c O.lev2)
    {σ : T.Q.c.F →+* ℂ} (hσ : GoodEmb T.Q.c σ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (c : (T.U ((i : ℕ) + 1) σ).Comp → ℂ) :
    EqAt T R κ O σ hV c ↔ ∀ g k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k →
      ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, ∀ h,
        frameRead T i σ hV c (actLev T.Q.c O.lev2 g f) h = frameRead T i σ hV c f (h * k) := by
  have hmu := ht.laws.muUnit _ (inR i) σ hσ
  have key : ∀ {k : GA D (Wc D i)} {y : T.Q.c.F}, σ y * castDict hV (T.mu ((i : ℕ) + 1) σ) k = 1 → ∀ f f' h,
      (phiAt T i σ hV c f' h = σ y * phiAt T i σ hV c f (h * k) ↔ frameRead T i σ hV c f' h = frameRead T i σ hV c f (h * k)) := by
    intro k y hy f f' h
    have h0 : castDict hV (T.mu ((i : ℕ) + 1) σ) h ≠ 0 := norm_ne_zero_iff.1 ((hmu.2.1 _).trans_ne one_ne_zero)
    rw [phiAt_eq, phiAt_eq, castDict_mu_mul hmu.1, ← mul_assoc, mul_left_comm (σ y), hy, mul_one, mul_right_inj' h0]
  constructor
  · intro H g k hk f hf h
    obtain ⟨y, hy, hy'⟩ := mu_lift hR ht hpb i hσ hV hk
    obtain ⟨-, z, hz, hz'⟩ := H g k hk f hf
    obtain rfl : z = y := (algebraMap T.Q.c.F D.what₂.LL).injective
      (D.what₂.embLL.injective (hz.trans ((Units.coe_prod _ _).symm.trans hy.symm)))
    exact (key hy' _ _ h).1 (hz' h)
  · intro H g k hk f hf
    obtain ⟨y, hy, hy'⟩ := mu_lift hR ht hpb i hσ hV hk
    exact ⟨actLev_mem_cuspA ht.laws.toLawsM (inR i) hL (κ i) g hf, y, hy.trans (Units.coe_prod _ _),
      fun h => (key hy' _ _ h).2 (H g k hk f hf h)⟩

theorem geoAct_of_eqAt (ht : TieIn T R κ v₀) (hW : R.models_HW) (hg : R.models_gW)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (hO : ∀ i, OMPins T R κ v₀ O i)
    (hE : ∀ i σ, GoodEmb T.Q.c σ → ∀ hV, EqAt T R κ (O i) σ hV (T.cE ((i : ℕ) + 1) σ)) : GeoAct T R κ v₀ := fun i =>
  ⟨_, isGeoAct_levRep ht hW hg i (O i) (hO i).2.act.1 (fun g => ((hO i).2.lift.lev g).imp fun _ h => h.1) (hE i)⟩

end Head

end GlobalTheory.GeoLevel
