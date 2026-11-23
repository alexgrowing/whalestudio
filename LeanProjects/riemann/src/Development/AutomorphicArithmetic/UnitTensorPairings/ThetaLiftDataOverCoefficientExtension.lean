import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicCoreTransportEnlargedCoefficientBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivLift
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult GlobalTheory.RealGeo
set_option maxHeartbeats 4000000
open GlobalTheory.OneMapAll GlobalTheory.AdTh GlobalTheory.Mem.R3.Rw.GeoTies

private theorem lift_pt {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar} {M : DSModel V S} {M' : DSModel V S'} (hM : ModelSame M M')
    {Γ W W' : Type} {nW : NormedAddCommGroup W} {nW' : NormedAddCommGroup W'} {iW : InnerProductSpace ℂ W}
    {iW' : InnerProductSpace ℂ W'} (h1 : HEq W' W) (h2 : HEq nW' nW) (h3 : HEq iW' iW) {H : Links.HMod (Γ → W)} {H' : Links.HMod (Γ → W')}
    (hH : HEq H' H) {θ : H.H →ₗ[ℂ] MMap M} {θ' : H'.H →ₗ[ℂ] MMap M'} (hθ : HEq θ' θ) {v : M.Vec} {v' : M'.Vec} (hv : HEq v' v)
    (pt : AutQ V → AutQ V) (hpt : ∀ q, HEq (pt q) q) :
    ∃ e : H.H ≃ₗ[ℂ] H'.H, ∀ y, HEq (e y) y ∧ ∀ q : AutQ V, θ' (e y) v' q.out = θ y v (pt q).out := by
  obtain ⟨e, he⟩ := exists_equiv_lift hM h1 h2 h3 hH hθ hv
  exact ⟨e, fun y => ⟨(he y).1, fun q => by rw [eq_of_heq (hpt q), (he y).2]⟩⟩

private theorem heq_at {L L' : Type} {P : L → Type} {P' : L' → Type} (v : ∀ s, P s) (v' : ∀ s, P' s) {a b : L} {a' b' : L'}
    (h : a = b) (h' : a' = b') (hv : HEq (v' b') (v b)) : HEq (v' a') (v a) := by
  subst h h'
  exact hv

private theorem same_at {D D' : D7} {V : HSp D} {V' : HSp D'} {L L' : Type} {S : L → D.what₂.Tau → SPar} {S' : L' → D'.what₂.Tau → SPar}
    (M : ∀ s, DSModel V (S s)) (M' : ∀ s, DSModel V' (S' s)) {a b : L} {a' b' : L'}
    (h : a = b) (h' : a' = b') (hv : ModelSame (M b) (M' b')) : ModelSame (M a) (M' a') := by
  subst h h'
  exact hv

private theorem sign_at_base_place_eq_embedding {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) : sg0 D A = D.what₂.embLL :=
  sgAt_mk _ R.hv0

theorem UpperTheory.theta_lift_data_over_coefficient_extension :
    ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T) (w' : ColW B' f' T')
        (Z : w.Lt) (Z' : w'.Lt) (hX : B.fields.Ok) (hX' : B'.fields.Ok) (Wt : Set B.places.Pl) (Wt' : Set B'.places.Pl)
        (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq w'.px w.px →
        ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
          (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
          (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
          HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
          HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
          HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
          letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
            (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F)
            (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
            GlobalTheory.Mem.R3.Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → RSide z Wt' R' →
            ∀ (κ' : ∀ i : Fin (w'.st Z').toD7.R.m, WeightFamilies.Wt (w'.st Z').toD7 ((i : ℕ) + 1)),
            (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
              HEq (κ' i').aP (z.geo.κ i).aP ∧ HEq (κ' i').aM (z.geo.κ i).aM ∧ (κ' i').n = (z.geo.κ i).n) →
            ∀ (v₀' : ∀ (i : Fin (w'.st Z').toD7.R.m) (σ : (w'.st Z').toD7.what₂.LL →+* ℂ), (R'.MW i σ).Vec) (fw' : FWTie core' R'.toRealDat κ' v₀'),
            (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ φ φ', HEq φ' φ →
              ∀ (k : Fin (z.R.nW i)) (k' : Fin (R'.nW i')), (k : ℕ) = k' →
              (w'.st Z').toD7.what₂.embLL ((fw'.e i' φ' : (R'.FW i').WK).1 k') = (w.st Z).toD7.what₂.embLL ((z.geo.fw.e i φ : (z.R.FW i).WK).1 k)) →
            (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
              HEq (v₀' i' (w'.st Z').toD7.what₂.embLL) (z.geo.v₀ i (w.st Z).toD7.what₂.embLL)) →
            ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → MWOver z.R.toRealDat R'.toRealDat →
            ∀ (pt : AutQ (Wc (w'.st Z').toD7 i') → AutQ (Wc (w.st Z).toD7 i)), (∀ q, HEq (pt q) q) →
              ∃ e : (z.R.HV i (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).H ≃ₗ[ℂ]
                  (R'.HV i' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A.μ0).H,
                ∀ y, HEq (e y) y ∧ ∀ q, R'.thF i' _ (e y) (v₀' i' (sg0 (w'.st Z').toD7 _)) q.out =
                  z.R.thF i _ y (z.geo.v₀ i (sg0 (w.st Z).toD7 _)) (pt q).out := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hpx core' alg' halg hc Xg tr R' cG' hpins hRS κ' hκ v₀' fw' hcrd hv0 i i' hi hMW
    pt hpt
  letI := alg'
  letI := z.alg
  have hs := sign_at_base_place_eq_embedding z.R.toRealDat
  have hs' := sign_at_base_place_eq_embedding R'.toRealDat
  have hcl := hRS.1.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' hi
  have h2 := hRS.2 i i' hi
  have c1 := hcl.1
  have c2 := hcl.2.2.1
  have c3 := hcl.2.2.2.1
  have hH := h2.2.2.1
  have hθ := h2.2.2.2.1
  have hk := hcl.2.2.2.2.2.2.2
  have hMM := same_at (z.R.MW i) (R'.MW i') hs hs' ⟨hk.1, hk.2.1, hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2.1, hk.2.2.2.2.2.1, hk.2.2.2.2.2.2.1⟩
  have hv := heq_at (z.geo.v₀ i) (v₀' i') hs hs' (hv0 i i' hi)
  clear hcl h2 hk hs hs' hMW hv0 hcrd hκ hRS hpins hc halg
  have h1 := hE.1
  rcases B' with ⟨P'⟩
  change P' = B.toPre at h1
  subst h1
  have hii : i = (by with_unfolding_all exact (i' :)) := Fin.ext ((by with_unfolding_all exact (hi :)))
  subst hii
  let i' : Fin (w'.st Z').toD7.R.m := (by with_unfolding_all exact (i :))
  let S₀ : (w'.st Z').toD7.what₂.Tau → SPar := (by with_unfolding_all exact ((parAt (Wc (w.st Z).toD7 i) (sg0 (w.st Z).toD7 (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)) :))
  let M₀ : DSModel (Wc (w'.st Z').toD7 i') S₀ :=
    @DSModel.mk _ _ _ ((by with_unfolding_all exact ((z.R.MW i (sg0 (w.st Z).toD7 (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)).H :))) ((by with_unfolding_all exact ((z.R.MW i (sg0 (w.st Z).toD7 (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)).nacg :))) ((by with_unfolding_all exact ((z.R.MW i (sg0 (w.st Z).toD7 (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)).ips :)))
      ((by with_unfolding_all exact ((z.R.MW i (sg0 (w.st Z).toD7 (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)).σ :))) ((by with_unfolding_all exact ((z.R.MW i (sg0 (w.st Z).toD7 (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)).lam :))) ((by with_unfolding_all exact ((z.R.MW i (sg0 (w.st Z).toD7 (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)).ε :)))
      ((by with_unfolding_all exact ((z.R.MW i (sg0 (w.st Z).toD7 (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)).fr :))) ((by with_unfolding_all exact ((z.R.MW i (sg0 (w.st Z).toD7 (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)).enum :))) ((by with_unfolding_all exact ((z.R.MW i (sg0 (w.st Z).toD7 (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)).ds :)))
      ((by with_unfolding_all exact ((z.R.MW i (sg0 (w.st Z).toD7 (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)).fr_unit :))) ((by with_unfolding_all exact ((z.R.MW i (sg0 (w.st Z).toD7 (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)).fr_gram :)))
  let H₀ : Links.HMod (Bridge.Gf (Vc (w'.st Z').toD7 i') → (z.R.cV i).W) := (by with_unfolding_all exact ((z.R.HV i (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) :))
  let θ₀ : H₀.H →ₗ[ℂ] MMap M₀ := (by with_unfolding_all exact ((z.R.thF i (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) :))
  let u₀ : M₀.Vec := (by with_unfolding_all exact ((z.geo.v₀ i (sg0 (w.st Z).toD7 (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)) :))
  exact (by with_unfolding_all exact ((lift_pt (M := M₀) (M' := R'.MW i' (sg0 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A)) ((hMM)) (W := (z.R.cV i).W) (W' := (R'.cV i').W)
    (nW := (z.R.cV i).nW) (nW' := (R'.cV i').nW) (iW := (z.R.cV i).iW) (iW' := (R'.cV i').iW) ((c1)) ((c2)) ((c3))
    (H := H₀) (H' := R'.HV i' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A.μ0) ((hH)) (θ := θ₀) (θ' := R'.thF i' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A.μ0) ((hθ))
    (v := u₀) (v' := v₀' i' (sg0 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A)) ((hv)) ((pt)) ((hpt))) : _))
