import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GeoExV
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsAtAndSeedFacts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeoHalfUpd
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.StandardWeightCharacter

local macro "qmove " h:term : tactic => `(tactic| (
  obtain ⟨i, u, a, l, e, s, m, w, b, k⟩ := $h
  refine ⟨⟨i.tie, i.onto, i.hR, i.hL, i.SF⟩, ⟨u.mu_off, u.mu_used, u.mu_ne, u.mu_conj, u.mu_on⟩, a, l, e, s, m, w, fun hb => b hb, fun c hc => ?_⟩
  have kv := k c hc
  exact ⟨kv.std, kv.signs, kv.frames, kv.beta, kv.prX, kv.grp, kv.psi, kv.guard, kv.valKs, kv.frameKs, kv.levKs⟩))

set_option maxHeartbeats 8000000 in

theorem charW_seed_std : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr₀ : TrI X.B px) (C : Formalism.L2.Pj.CoreJ X.toD7) [Algebra C.Q.c.F X.toD7.what₂.LL] (R₀ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) C.Q.c.F) (cG : G0 R₀.Pg X.toD7.R.r ≃* G0g X.toD7.nd), Inputs X.toD7 → IdemClass (D := X.toD7) (famR X I hX U Xg tr₀).A → (∀ R : RealDat X.toD7 (famR X I hX U Xg tr₀).A C.Q.c.F, R.Pre1 (face0 X I hX U Xg tr₀).lv2 → R.IsChainW → R.IsThPW → R.FullY → R.FullP → R.ExAt) → GeoExV (famR X I hX U Xg tr₀) C (face0 X I hX U Xg tr₀).lv2 → Formalism.L2.Host.ValLL X.toD7 R₀.C → C.pb = R₀.C.P.pb → R₀.toRealDat.Pre0 (face0 X I hX U Xg tr₀).lv2 → R₀.IsInert → R₀.IsTup → R₀.AllPlaces → Keep R₀.toRealDat (face0 X I hX U Xg tr₀).lv2 cG → ∃ (tr : TrI X.B px) (dict : _) (mu : _) (chiW : _) (x₀ : _) (cE : _) (R : RealDat3 X.toD7 (famR X I hX U Xg tr) C.Q.c.F) (cG' : G0 R.Pg X.toD7.R.r ≃* G0g X.toD7.nd), Pins R (face0 X I hX U Xg tr) cG' ∧ R.toRealDat.ExAt ∧ R.toRealDat.toLevCh = R₀.toRealDat.toLevCh ∧ HEq R.eG R₀.eG ∧ HEq cG' cG ∧ R.ψ = R₀.ψ ∧ R.mu = R₀.mu ∧ R.twPl = R₀.twPl ∧ (BrgStd X I hX U Xg tr₀ R₀.toRealDat → BrgStd X I hX U Xg tr R.toRealDat) ∧ Nonempty (@GlobalTheory.RealGeo.GeoHalf X.toD7 _ _ _ _ _ (famR X I hX U Xg tr).A (GlobalTheory.RealGeo.reCore C dict mu chiW x₀ cE) (inferInstanceAs (Algebra C.Q.c.F X.toD7.what₂.LL)) R.toRealDat fun _ => 1) := by
  intro X px I hX U Xg tr₀ C _ R₀ cG hI hXi hEx hGeo hVal hpb p0 i0 t0 a0 k0
  classical
  obtain ⟨hL, hF⟩ := GlobalTheory.HeckeCharacterRestriction.liftsAt_and_seedFacts X.toD7 _ _ _ (famR X I hX U Xg tr₀).A C.Q.c.F (face0 X I hX U Xg tr₀).lv2
  obtain ⟨R1, p1, c1, t1, f1, g1, q1⟩ := analyticW_exists hI hXi hL hF
    (fun R => RealDat3.IsInert (⟨R, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) C.Q.c.F) ∧
      RealDat3.IsTup (⟨R, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) C.Q.c.F) ∧
      RealDat3.AllPlaces (⟨R, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) C.Q.c.F) ∧
      R.toLevCh = R₀.toLevCh ∧ HEq R.eG R₀.eG ∧ R.ψ = R₀.ψ ∧ R.mu = R₀.mu ∧ R.twPl = R₀.twPl ∧
      (BrgStd X I hX U Xg tr₀ R₀.toRealDat → BrgStd X I hX U Xg tr₀ R) ∧
      ∀ c : G0 R.Pg X.toD7.R.r ≃* G0g X.toD7.nd, HEq c cG → Keep (A3 := (famR X I hX U Xg tr₀)) R (face0 X I hX U Xg tr₀).lv2 c)
    (fun R a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 h => by qmove h)
    (fun R a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 h => by qmove h)
    (fun R a1 a2 a3 a4 a5 a6 h => by qmove h)
    R₀.toRealDat p0 ⟨⟨i0.tie, i0.onto, i0.hR, i0.hL, i0.SF⟩, ⟨t0.mu_off, t0.mu_used, t0.mu_ne, t0.mu_conj, t0.mu_on⟩, a0, rfl, HEq.rfl,
      rfl, rfl, rfl, id, fun c hc => by cases eq_of_heq hc; exact k0⟩
  have e1 : R1.ExAt := hEx R1 p1 c1 t1 f1 g1
  have l1 : R1.toLevCh = R₀.toLevCh := q1.2.2.2.1
  have hC : R1.C = R₀.C := congrArg (fun L => L.C) l1
  obtain ⟨cutoffDeriv, hcG1⟩ : ∃ c : G0 R1.Pg X.toD7.R.r ≃* G0g X.toD7.nd, HEq c cG := by
    rw [show R1.Pg = R₀.Pg from congrArg (fun L => L.Pg) l1]
    exact ⟨cG, HEq.rfl⟩
  have pc1 : GlobalTheory.RealGeo.PreChar R1 := ⟨p1.1.lev, p1.1.red_R, p1.1.red_L, p1.1.record, p1.1.fam, p1.2,
    RealDat.chain_of_weak c1 e1, RealDat.thP_of_weak t1 e1⟩
  have hV1 : Formalism.L2.Host.ValLL X.toD7 R1.C := by rw [hC]; exact hVal
  have hpb1 : C.pb = R1.C.P.pb := by rw [hC]; exact hpb
  obtain ⟨dict, mu, chiW, x₀, cE, nW, FW, hchi, ⟨geo⟩, hrat⟩ := hGeo R1 cutoffDeriv hV1 pc1 p1.1.levels hpb1 (q1.2.2.2.2.2.2.2.2.2 cutoffDeriv hcG1)
  let R2₀ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) C.Q.c.F := ⟨R1.upd5 nW FW R1.mu R1.twPl R1.err0, R₀.plI, R₀.SF, fun _ => 1, R₀.lam3⟩
  obtain ⟨tr, htr⟩ : ∃ tr : TrI X.B px, (∃ t', R2₀.TrISem (face0 X I hX U Xg tr₀) t' ∧ SepWith (famR X I hX U Xg tr₀) t') →
      R2₀.TrISem (face0 X I hX U Xg tr₀) tr ∧ SepWith (famR X I hX U Xg tr₀) tr := by
    by_cases h : ∃ t', R2₀.TrISem (face0 X I hX U Xg tr₀) t' ∧ SepWith (famR X I hX U Xg tr₀) t'
    · obtain ⟨t', h'⟩ := h
      exact ⟨t', fun _ => h'⟩
    · exact ⟨tr₀, fun h' => absurd h' h⟩
  let R2 : RealDat3 X.toD7 (famR X I hX U Xg tr) C.Q.c.F := ⟨R1.upd5 nW FW R1.mu R1.twPl R1.err0, R₀.plI, R₀.SF, fun _ => 1, R₀.lam3⟩
  obtain ⟨kap, lam, hs⟩ := scalars_exist (F := face0 X I hX U Xg tr) R2
  have q5 : RealDat3.IsInert (⟨R1.upd5 nW FW R1.mu R1.twPl R1.err0, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) C.Q.c.F) ∧
      RealDat3.IsTup (⟨R1.upd5 nW FW R1.mu R1.twPl R1.err0, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) C.Q.c.F) ∧
      RealDat3.AllPlaces (⟨R1.upd5 nW FW R1.mu R1.twPl R1.err0, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) C.Q.c.F) ∧
      (R1.upd5 nW FW R1.mu R1.twPl R1.err0).toLevCh = R₀.toLevCh ∧ HEq (R1.upd5 nW FW R1.mu R1.twPl R1.err0).eG R₀.eG ∧
      (R1.upd5 nW FW R1.mu R1.twPl R1.err0).ψ = R₀.ψ ∧ (R1.upd5 nW FW R1.mu R1.twPl R1.err0).mu = R₀.mu ∧
      (R1.upd5 nW FW R1.mu R1.twPl R1.err0).twPl = R₀.twPl ∧
      (BrgStd X I hX U Xg tr₀ R₀.toRealDat → BrgStd X I hX U Xg tr₀ (R1.upd5 nW FW R1.mu R1.twPl R1.err0)) ∧
      ∀ c : G0 R1.Pg X.toD7.R.r ≃* G0g X.toD7.nd, HEq c cG → Keep (A3 := (famR X I hX U Xg tr₀)) (R1.upd5 nW FW R1.mu R1.twPl R1.err0) (face0 X I hX U Xg tr₀).lv2 c := by
    qmove q1
  obtain ⟨i1, u1, a1, l6, e6, s6, m6, w6, b6, k6⟩ := q5
  have p6 := RealDat.preliminary_of_scalar_update (RealDat.preliminary_of_index_update p1 nW FW R1.mu R1.twPl R1.err0) kap R2.lam
  have f6 := RealDat.full_Y_of_scalar_update (RealDat.full_Y_of_index_update f1 nW FW R1.mu R1.twPl R1.err0) kap R2.lam
  have c6 := RealDat.weak_chain_of_scalar_update (RealDat.weak_chain_of_index_update c1 nW FW R1.mu R1.twPl R1.err0) kap R2.lam
  have t6 := RealDat.weak_theta_props_of_scalar_update (RealDat.weak_theta_props_of_index_update t1 nW FW R1.mu R1.twPl R1.err0) kap R2.lam
  have g6 := RealDat.full_P_of_scalar_update (RealDat.full_P_of_index_update g1 nW FW R1.mu R1.twPl R1.err0) kap R2.lam
  have hphs : (R2.updS kap lam).phase := by
    intro i
    refine ⟨show ‖(1 : ℂ)‖ = 1 from norm_one, fun _ x => ?_⟩
    obtain ⟨y, hy⟩ := hrat i x
    refine ⟨y, hy.trans ?_⟩
    show _ = Formalism.IndefR.Links.cj _ (1 : ℂ) • _
    rw [map_one]
    exact (one_smul ℂ _).symm
  have kv := k6 cutoffDeriv hcG1
  obtain ⟨g', -, -, -⟩ := GlobalTheory.RealGeo.geoHalf_upd X.toD7 _ _ _ (famR X I hX U Xg tr₀).A (GlobalTheory.RealGeo.reCore C dict mu chiW x₀ cE)
    (R1.upd5 nW FW R1.mu R1.twPl R1.err0) (fun _ => 1) kap R1.lam R1.err0 geo
  refine ⟨tr, dict, mu, chiW, x₀, cE, R2.updS kap lam, cutoffDeriv, ⟨⟨⟨p6.1.lev, ⟨p6.1.red_R, p6.1.red_L, p6.1.levels, p6.1.record, hchi⟩,
      p6.1.fam, p6.2, c6, t6⟩, ⟨⟨i1.tie.plI_inj, i1.tie.okI⟩, i1.onto, i1.hR, i1.hL, i1.SF⟩, f6.1, f6.2, g6, hs,
      ⟨u1.mu_off, u1.mu_used, u1.mu_ne, u1.mu_conj, u1.mu_on⟩, hphs, a1⟩,
    ⟨kv.std, kv.signs, kv.frames, kv.beta, kv.prX, kv.grp, kv.psi, kv.guard, kv.valKs, kv.frameKs, kv.levKs⟩,
    fun _ => rfl, fun h => htr h⟩, hEx _ p6 c6 t6 f6 g6, l6, e6, hcG1, s6, m6, w6, fun hb => b6 hb, ⟨g'⟩⟩

end GlobalTheory.StandardWeightCharacter
