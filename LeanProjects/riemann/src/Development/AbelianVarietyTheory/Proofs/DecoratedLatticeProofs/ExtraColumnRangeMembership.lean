import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotLevGEmpty
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtraProjectionLevelCharacterStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopStep

open GlobalTheory.Fam.Inhab GlobalTheory.Fam.FamInhab

section
variable {D : D7}
variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
  [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (P : LevelP R.Pg D.R.r ℂ)

theorem lift_lev_pt (hl : R.toLevCh.Is A.μ0) (hθ : IsInfFam R.θ) (t : T) (k : ℕ) (hk : k < D.R.m) {V : HSp D} (hV : V.SigOK)
    (hr : V.rank = D.R.r + (k + 1) * D.R.t) {S : D.what₂.Tau → SPar} (M : DSModel V S)
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {β : GL (Fin V.rank) (Lev.EAf D)} {N : ℕ} (hβ : IsSDFrame V β Λ N)
    {om : Om (Yc D k) V} (hom : IsWeilDatumO R.ψ (Yc D k) V (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1
      (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2 om) {f₀ f f' : WO (Yc D k) V → ℂ}
    (hf : IsStepVecOf R.ψ R.θ (Yc D k) V (cart (R.MY k)) (cart M) (R.ΛY k) Λ (R.βY k) β (R.datYt t k R.triv) (R.chi (k + 1))
      (R.Q t) (R.xiR t) f₀ f)
    (hf' : IsStepVecOf R.ψ R.θ (Yc D k) V (cart (R.MY k)) (cart M) (R.ΛY k) Λ (R.βY k) β (R.datYt t k P) (R.chi (k + 1))
      (R.Q t) (R.xiR t) f₀ f') (ν : Measure (GA D V)) (𝓕 : Set (GA D V)) (F : GA D V → ℂ) (φ : PolF D V.rank (Yc D k).rank)
    (hi : ∀ g, IntegrableOn (fun h => thetaKO om g h
      (pureTensorO R.ψ R.θ (Yc D k) V (cart (R.MY k)) (cart M) (onb (R.MY k)) (onb M) f φ) * F h) 𝓕 ν)
    (U : GA D (Yc D k) → ℂ)
    (hU : ∀ κ ∈ levS (Yc D k) (R.βY k) (R.datYt t k P), ∀ g, U (g * κ) = levChi (Yc D k) (R.βY k) (R.datYt t k P) κ * U g)
    (he : ∀ g, Lift.liftInt ν 𝓕 (thetaKO om)
      (pureTensorO R.ψ R.θ (Yc D k) V (cart (R.MY k)) (cart M) (onb (R.MY k)) (onb M) f φ) F g = U g) :
    liftS om ν 𝓕 F (pureTensorO R.ψ R.θ (Yc D k) V (cart (R.MY k)) (cart M) (onb (R.MY k)) (onb M) f' φ) =
      (Nat.card P.H : ℂ) • U := by
  haveI := finite_H P
  haveI : Fintype P.H := Fintype.ofFinite _
  choose κ hκ using fun p : P.H => GlobalTheory.ChainEquiv.lifts_chain R.toLevCh _ hl t k hk p.1
  obtain ⟨⟨a1, a2, a3⟩, b1, b2, b3⟩ := GlobalTheory.StepVecLaw.levRes_chrStep hl t ⟨k, hk⟩
  have s1 := sd (hl.βY k hk)
  have s2 := sd hβ
  have hs := @GlobalTheory.StepVecSum.stepVec_eq_sum D R.ψ R.θ (Yc D k) V _ _ om _ _ _ _ _ _ f₀ f f' hom (D.sp.Y_sig _) hV
    (GlobalTheory.Chain.VacVec.cart_isCartanInv (R.MY k)) (GlobalTheory.Chain.VacVec.cart_isCartanInv M) s1.1 s2.1 s1.2 s2.2 D.R.r D.R.t k (r_le_Y k)
    (rankY hk.le) hr R.Pg (R.Q t) (GlobalTheory.ChainEquiv.places_sep R.toLevCh _ hl t).2 R.chi (R.xiR t) P _ hf hf'
    (fun PP hP => ⟨a1 PP hP, b1 PP hP⟩) (fun PP hP => ⟨a2 PP hP, b2 PP hP⟩) a3 b3 κ hκ
  have hth : IsThetaFunO R.ψ (Yc D k) V f := (GlobalTheory.Chain.StepVac.stepVec_vac s1.1 s2.1 (by
    rw [rankY hk.le, hr]; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ _)) _) hf).1
  exact (lift_sum hom hθ _ _ _ _ hth κ (fun p => (hκ p).1) _ (fun p => levChi_ne_zero _ _) hs ν 𝓕 F φ hi U he
    fun p g => hU _ (levChi_lift (L := R.datYt t k R.triv) P p (hκ p)) g).2

theorem lift_ioX_pt (hl : R.toLevCh.Is A.μ0) (hm : R.IsModels) (hc : R.IsChain) (t : T) (j : ℕ)
    (h : j + 2 * 0 + 2 = D.R.m) (F : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e))
    (hF : ∀ κ ∈ levS (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) P), ∀ φ x g,
      (R.ioX t F).1 (R.ItX φ x) (g * κ) = levChi (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) P) κ *
        (R.ioX t F).1 (R.ItX φ x) g)
    {v : WO (Yc D (j + 1)) D.sp.X' → ℂ}
    (hv : IsStepVecOf R.ψ R.θ (Yc D (j + 1)) D.sp.X' (cart (R.MY (j + 1))) (cart R.MX) (R.ΛY (j + 1)) R.ΛX (R.βY (j + 1)) R.βX
      (R.datYt t (j + 1) P) (R.chi D.R.m) (R.Q t) (R.xiR t) (vacT R j h) v) (Q x) :
    liftS (omT R t j h) (R.νX t) (R.fdX t) (F.1 x) (pureTensorO R.ψ R.θ (Yc D (j + 1)) D.sp.X' (cart (R.MY (j + 1))) (cart R.MX)
      (onb (R.MY (j + 1))) (onb R.MX) v Q) = (Nat.card P.H : ℂ) • (ioXT R t j h F).1 (itXT R j h Q x) := by
  have e : R.chi D.R.m = R.chi (j + 1 + 1) := congrArg R.chi (show j + 1 + 1 = D.R.m from h).symm
  have h1 := top_vec hc t j h
  rw [e] at h1 hv
  have key : ∀ n (e : D.R.m - 1 = n), ∀ κ ∈ levS (Yc D n) (R.βY n) (R.datYt t n P), ∀ φ x g,
      ((Eq.rec (motive := fun n _ => LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) →ₗ[ℂ] R.CC t n)
        (R.ioX t) e : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) →ₗ[ℂ] R.CC t n) F).1
        ((Eq.rec (motive := fun n _ => PolF D D.sp.X'.rank (Yc D n).rank →ₗ[ℂ] SmT R.MX →ₗ[ℂ] SmT (R.MY n)) R.ItX e :
          PolF D D.sp.X'.rank (Yc D n).rank →ₗ[ℂ] SmT R.MX →ₗ[ℂ] SmT (R.MY n)) φ x) (g * κ) =
      levChi (Yc D n) (R.βY n) (R.datYt t n P) κ *
        ((Eq.rec (motive := fun n _ => LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) →ₗ[ℂ] R.CC t n)
        (R.ioX t) e : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) →ₗ[ℂ] R.CC t n) F).1
        ((Eq.rec (motive := fun n _ => PolF D D.sp.X'.rank (Yc D n).rank →ₗ[ℂ] SmT R.MX →ₗ[ℂ] SmT (R.MY n)) R.ItX e :
          PolF D D.sp.X'.rank (Yc D n).rank →ₗ[ℂ] SmT R.MX →ₗ[ℂ] SmT (R.MY n)) φ x) g := by
    intro n e; subst e; exact hF
  exact lift_lev_pt P hl hm.inf t (j + 1) (by omega) D.sp.X'_sig (rank_top h) R.MX hl.βX (top_weil hc t j h) h1 hv
    _ _ _ Q ((top_io hc t j h).integ F Q x) _ (fun κ hκ g => key _ (idx_top h) κ hκ Q x g) ((top_io hc t j h).eq F Q x)

end

theorem ioXT_levelP : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (g : GlobalTheory.Fam.Geo D) t j (h : j + 2 * 0 + 2 = D.R.m) (F : CXP (pk W) (lvP W) t), ∃ h' : F.1 ∈ LinearMap.range ((pk W).cX.toMap (pk W).prX ∘ₗ ((pk W).HX t).e), (GlobalTheory.Published.CuspRapidDecay → (ioXT (pk W) t j h ⟨F.1, h'⟩).1 ∈ CP (pk W) (lvP W) t (j + 1)) ∧ ∀ v, IsStepVecOf (pk W).ψ (pk W).θ (Yc D (j + 1)) D.sp.X' (cart ((pk W).MY (j + 1))) (cart (pk W).MX) ((pk W).ΛY (j + 1)) (pk W).ΛX ((pk W).βY (j + 1)) (pk W).βX ((pk W).datYt t (j + 1) (lvP W)) ((pk W).chi D.R.m) ((pk W).Q t) ((pk W).xiR t) (vacT (pk W) j h) v → ∀ Q x, liftS (omT (pk W) t j h) ((pk W).νX t) ((pk W).fdX t) (F.1 x) (pureTensorO (pk W).ψ (pk W).θ (Yc D (j + 1)) D.sp.X' (cart ((pk W).MY (j + 1))) (cart (pk W).MX) (onb ((pk W).MY (j + 1))) (onb (pk W).MX) v Q) = (Nat.card (lvP W).H : ℂ) • (ioXT (pk W) t j h ⟨F.1, h'⟩).1 ((commOf (pk W) u g).ItT j h Q x) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP g t j h F
  have hC := hP.bot.hyp.2.2.2.1
  have h1 := cxp_le (lvP W) hP.hTop t F.2
  exact ⟨h1, fun hc => top_mem (lvP W) hc hC.lev hC.models hC.chain t j h ⟨F.1, h1⟩ F.2,
    fun v hv Q x => lift_ioX_pt (lvP W) hC.lev hC.models hC.chain t j h ⟨F.1, h1⟩ (GlobalTheory.T.extra_projection_level_character W hP t ⟨F.1, h1⟩ F.2) hv Q x⟩

end GlobalTheory.TopStep
