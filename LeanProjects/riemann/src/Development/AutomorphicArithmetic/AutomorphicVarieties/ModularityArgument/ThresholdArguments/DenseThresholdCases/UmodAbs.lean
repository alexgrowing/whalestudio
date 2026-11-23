import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.SubquotientSupport.LevelUA
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryHeckeData
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryPointProperties
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevelUR2ActEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VLPiPts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevelUR2LocEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TDenseU
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExistsHeckeIdeal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypeForUp
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.LocDataT

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
attribute [local instance 2000] UpperTheory.V.W.coefLocal
open UpperTheory.V.Hi.LvR
set_option maxHeartbeats 3000000 in
theorem UpperTheory.V.Hi.LvW.umodAbs_alt (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c) (hax : H.Ax)
    (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ) (hw : H.IsWt θ) (a : H.Op → c.O) [DecidableEq H.Q]
    (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop) (haut : H.AutomorphicHeckeSet ι P) (lam0 : Wt L l n) (hl0 : lam0 ∈ H.admitted) (hd : H.DenseWt θ lam0)
    (hneat : ∀ K, H.X.Neat (H.lev K))
    (hf : ∀ (K : H.Lev) (k : GV n H.wq) (j : GV n H.wq →* H.X.Ub), (∀ q g, j (Pi.mulSingle q g) = H.sec (H.wq q) g) → j k ∈ H.lev K → k ∈ Subgroup.pi Set.univ K.1)
    (R : Type) [CommRing R] [Algebra c.O R] (D₀ : W.GDet n R H.Gq) (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Rˣ) (lam : A →ₐ[c.O] R)
    (hu : ∀ (T : Type) [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (f g : R →ₐ[c.O] T), D₀.map f.toRingHom = D₀.map g.toRingHom → (∀ v i, W.pushCh f.toRingHom (ψ₀ v i) = W.pushCh g.toRingHom (ψ₀ v i)) → f = g)
    (hJ : ∀ K, ∃ J, H.IsJ θ a K D₀ ψ₀ lam J) :
    ∃ (ρ : Representation A (GV n H.wq) (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m))) (α : R →+* Module.End A (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m))), (∀ b z, α (lam b) z = b • z) ∧ (∀ t g z, α t (ρ g z) = ρ g (α t z)) ∧ (∀ K : H.Lev, (fixd ρ (Subgroup.pi Set.univ K.1)).map (Submodule.subtype _) = H.MK θ a K ∧ Module.Finite A (fixd ρ (Subgroup.pi Set.univ K.1))) ∧ (∀ (K K' : H.Lev) [((Subgroup.pi Set.univ K'.1).subgroupOf (Subgroup.pi Set.univ K.1)).Normal], (∀ q, K'.1 q ≤ K.1 q) → ∃ ρ' : Representation A (Subgroup.pi Set.univ K.1 ⧸ (Subgroup.pi Set.univ K'.1).subgroupOf (Subgroup.pi Set.univ K.1)) (fixd ρ (Subgroup.pi Set.univ K'.1)), (∀ (u : Subgroup.pi Set.univ K.1) f, (ρ' (u : _ ⧸ _) f).1 = ρ u.1 f) ∧ Module.Projective (MonoidAlgebra A (Subgroup.pi Set.univ K.1 ⧸ (Subgroup.pi Set.univ K'.1).subgroupOf (Subgroup.pi Set.univ K.1))) ρ'.asModule) ∧ (∀ (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)], ∃ f : R →ₐ[c.O] H.TK θ a K, H.IsMap θ a K D₀ ψ₀ f ∧ ∀ t (y : H.MK θ a K) (z : (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m))), (z : H.X.Fn A H.m) = y → (α t z : H.X.Fn A H.m) = ((f t : Module.End A (H.MK θ a K)) y : H.MK θ a K)) ∧ ∀ z : (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m)), z ≠ 0 → ∃ (x : R →+* Qbar l) (ρx : H.Gq →* GL (Fin n) (Qbar l)) (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (π : Representation ℂ (GV n H.wq) Y) (sp : (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m)) →+ Y) (σ : ∀ q, SmIrr (GLw n (H.wq q))), sp z ≠ 0 ∧ Continuous ρx ∧ D₀.map x = W.GDet.ofRep (W.mat ρx) ∧ (∀ t y, sp (α t y) = ι (x t) • sp y) ∧ (∀ g y, sp (ρ g y) = π g (sp y)) ∧ (∀ q, IsoSum (π.comp (MonoidHom.mulSingle (fun q => GLw n (H.wq q)) q)) ⊤ (σ q)) ∧ ∀ q (Bq : ValuationSubring Ω) (hB : IsPlaceOver Bq (H.wq q)) (rc : IrrGL ((H.wq q).adicCompletion L) → WD hB), _root_.UpperTheory.Zero.LLC.IsRecT hB rc → _root_.UpperTheory.V.Z.Win.WOT ι (ρx.comp H.prj) (rc (algNorm (σ q))) := by
  obtain ⟨ρ, h1, h2, h3, h4⟩ := piBasic L Ω l n c H hax A θ hw a
  obtain ⟨α, a1, a2, a3⟩ := _root_.UpperTheory.V.Hi.levelUR2ActEx_alt hN L Ω l n c H hax A θ hw a ρ h1 h2 h3 R D₀ ψ₀ lam hu hJ
  refine ⟨ρ, α, a1, a2, fun K => ⟨h2 K, ?_⟩, fun K K' _ hle => h4 hneat K K' hle fun k _ j hj hk => hf K' k j hj hk, a3, ?_⟩
  · have hfin : Module.Finite A (H.MK θ a K) := ((hiComm L Ω l n c H hax A θ hw K).2.2.2 a).2.1
    rw [← h2 K] at hfin
    exact Module.Finite.equiv (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) _).symm
  · exact _root_.UpperTheory.V.Hi.piPts_n_alt hN L Ω l n c H hax A θ hw ι P haut lam0 hl0 hd a ρ h1 R D₀ α fun K _ _ => by
      obtain ⟨f, hf1, hf2⟩ := a3 K
      exact ⟨f.toRingHom, _, hf1, hf2⟩
set_option maxHeartbeats 1600000 in
theorem UpperTheory.V.Hi.LvW.step1_alt (P : _root_.UpperTheory.V.Af.HypothesesH') (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (hn : 1 ≤ n)
    (V0 : s.Lev) (Q0 : QData V0) (c : Coef l) (r : Resid V0.frame c.O n) (ι : Qbar l ≃+* ℂ)
    (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (κ : ∀ v, Fin n → V0.frame.Iv v →* Aˣ) (hi hu)
    (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (ty : _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀) (θ : (hset Q0 τ₀).X.I.T →* Aˣ)
    (th : IsTheta Q0 τ₀ (⟨A, κ, hi, hu⟩ : LamObj r) θ) (hw : (hset Q0 τ₀).IsWt θ) (a : (hset Q0 τ₀).Op → c.O) (rs : IsRes Q0 r τ₀ a) (V : s.Lev) (h : (Pa.globOf r V).Hom (Pa.globOf r V0)) (Q : QData V) [dq : DecidableEq Q.Q] (hsub : V0.S' ⊆ V.S') (hp : ∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) (B' : UniversalOrdinaryDeterminantRing (rUp h)) :
    ∃ (θ' : (hset Q τ₀).X.I.T →* Aˣ) (a' : (hset Q τ₀).Op → c.O) (lam : A →ₐ[c.O] B'.B), (hset Q τ₀).IsWt θ' ∧ @Eq ((hset Q τ₀).X.I.T →* Aˣ) θ' θ ∧
      (∀ i, a' i = a (opUp Q0 Q hsub τ₀ i)) ∧ (∀ v i (γ : V0.frame.Gv v) (hγ : γ ∈ V0.frame.Iv v), lam (κ v i ⟨γ, hγ⟩ : Aˣ) = (@id (Dec (F := L) (s.A v.1) →* B'.Bˣ) (B'.u.ψ v i) γ : B'.Bˣ)) ∧ (∀ w, (hset Q τ₀).DenseWt θ' w) ∧ ∀ K, ∃ J, (hset Q τ₀).IsJ θ' a' K B'.u.D B'.u.ψ lam J := by
  let κ' : ∀ v, Fin n → V.frame.Iv v →* Aˣ := κ
  have hi' : W.IsInert (rUp h) κ' := (lamUp h ⟨A, κ, hi, hu⟩).inert
  have hu' : ∀ (R : Type) [CommRing R] [Algebra c.O R] [Alg.IsCO c.O R] (κ'' : ∀ v, Fin n → V.frame.Iv v →* Rˣ), W.IsInert (rUp h) κ'' →
      ∃! f : A →ₐ[c.O] R, ∀ v i, W.pushCh (f : A →+* R) (κ' v i) = κ'' v i := (lamUp h ⟨A, κ, hi, hu⟩).univ
  let θ' : (hset Q τ₀).X.I.T →* Aˣ := θ
  have th' : IsTheta Q τ₀ (⟨A, κ', hi', hu'⟩ : LamObj (rUp h)) θ' := fun v i x g hg y h1 h2 => th v i x g hg y h1 h2
  have hw' : (hset Q τ₀).IsWt θ' := ⟨cont_up Q0 Q τ₀ θ hw.cont, fun K => free_of_neat _ _ _ _ (neatU l L Ω s n hn V Q c m τ₀ K)⟩
  refine ⟨θ', fun i => a (opUp Q0 Q hsub τ₀ i), LamObj.toPair ⟨A, κ', hi', hu'⟩ B'.u, hw', rfl, fun _ => rfl, fun v i γ hγ => ?_,
    (_root_.UpperTheory.V.Hi.isDomain_and_denseWt_of_isTheta P.litN l L Ω s n hn V Q c m τ₀ (rUp h) ⟨A, κ', hi', hu'⟩ θ' th').2,
    _root_.UpperTheory.V.Hi.exists_hecke_ideal P l L Ω s n hn V Q c (rUp h) ι B' ⟨A, κ', hi', hu'⟩
      ⟨m, τ₀, _root_.UpperTheory.V.Hi.LvR.type_for_r_up_of_type_for h hp ι τ₀ ty, θ', th', hw', fun i => a (opUp Q0 Q hsub τ₀ i), res_up h Q0 Q hsub hp τ₀ a rs⟩⟩
  have e0 := DFunLike.congr_fun (LamObj.toPair_spec (rUp h) ⟨A, κ', hi', hu'⟩ B'.u v i) (⟨γ, hγ⟩ : V.frame.Iv v)
  exact congrArg Units.val e0
set_option maxHeartbeats 1600000 in
theorem UpperTheory.V.Hi.LvW.step2_alt (P : _root_.UpperTheory.V.Af.HypothesesH') (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (hn : 1 ≤ n)
    (V0 : s.Lev) (Q0 : QData V0) (c : Coef l) (r : Resid V0.frame c.O n) (ι : Qbar l ≃+* ℂ)
    (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (κ : ∀ v, Fin n → V0.frame.Iv v →* Aˣ) (hi hu)
    (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (ty : _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀) (θ : (hset Q0 τ₀).X.I.T →* Aˣ)
    (th : IsTheta Q0 τ₀ (⟨A, κ, hi, hu⟩ : LamObj r) θ) (hw : (hset Q0 τ₀).IsWt θ) (a : (hset Q0 τ₀).Op → c.O) (rs : IsRes Q0 r τ₀ a) (V : s.Lev) (h : (Pa.globOf r V).Hom (Pa.globOf r V0)) (Q : QData V) [dq : DecidableEq Q.Q] (hsub : V0.S' ⊆ V.S') (hp : ∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) (B' : UniversalOrdinaryDeterminantRing (rUp h)) (hS : V0.S' = s.S) (K0 : (hset Q0 τ₀).Lev)
    (θ' : (hset Q τ₀).X.I.T →* Aˣ) (a' : (hset Q τ₀).Op → c.O) (e1 : @Eq ((hset Q τ₀).X.I.T →* Aˣ) θ' θ) (e2 : ∀ i, a' i = a (opUp Q0 Q hsub τ₀ i)) :
    (∀ i, (hset Q τ₀).op A i = (hset Q0 τ₀).op A (opUp Q0 Q hsub τ₀ i)) ∧
      ∀ f : (hset Q0 τ₀).X.Fn A m, f ∈ (hset Q τ₀).MK θ' a' (kMax Q τ₀) ↔ f ∈ (hset Q0 τ₀).MK θ a K0 := by
  obtain rfl : a' = fun i => a (opUp Q0 Q hsub τ₀ i) := funext e2
  rw [e1]
  exact _root_.UpperTheory.V.Hi.levelUR2LocEq_alt P l L Ω s n hn V0 V Q0 Q c r ι ⟨A, κ, hi, hu⟩ ⟨m, τ₀, ty, θ, th, hw, a, rs⟩ K0 (kMax Q τ₀) hS (fun _ => rfl)
    (p0 h) (continuous_levelChangeBaseGroupHom h) (surjective_levelChangeBaseGroupHom h) (levelChangeBaseGroupHom_apply_projection h hp) (opUp Q0 Q hsub τ₀) (fun _ => rfl) fun _ _ => ⟨_, rfl⟩
end
