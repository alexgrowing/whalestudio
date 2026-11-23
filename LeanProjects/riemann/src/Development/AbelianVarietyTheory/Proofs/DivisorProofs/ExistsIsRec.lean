import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceLatticeLeThetaLatticeAtPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodLiftOnto
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TiedRecordExistsOfActionPin
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthPageFirstZetaFactorEqPrimePower
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AMiEqAMinusQ

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn GlobalTheory.RunDepth

namespace GlobalTheory.BigOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem eq_kaR {D : D7} {L : SizeData₂ D} {Pm : ParameterChoice' D L} (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (i : Fin D.R.m)
    (w : WeightFamilies.Wt D ((i : ℕ) + 1))
    (hP : ∀ τ (k : Fin (D.R.sigW ((i : ℕ) + 1)).1), w.aP τ k = aPl D i ((Wc D i).sig (tauE D τ)).1 τ k)
    (hM : ∀ τ (k : Fin (D.R.sigW ((i : ℕ) + 1)).2),
      w.aM τ k = aMi D i ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 τ k)
    (hn : w.n = D.R.nV) : w = kaR Tp hK ((i : ℕ) + 1) := by
  have hi := i.2
  have hk := D.R.m_add_three_le_k
  have h1 := (inR_succ i).1
  have h2 := (inR_succ i).2
  have hs : ∀ τ, (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) := fun τ => D.sp.W_sigval _ h1 h2 _
  have hp : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + i := by
    simp only [Ranks.sigW]; omega
  have hq : i + 1 + (D.R.sigW ((i : ℕ) + 1)).2 = D.R.m := by
    simp only [Ranks.sigW]; omega
  have eP : w.aP = (kaR Tp hK ((i : ℕ) + 1)).aP := by
    funext τ a
    have h := (hK _ h1 h2 τ).1 a
    have h' := GlobalTheory.RecordWeightVec.aPl_eq_aPlusQ D i τ a (hp ▸ a.2)
    have e := kaWt_big D hK (even_nV Tp) _ h1 h2 τ a
    rw [← h, ← hp, ← e] at h'
    rw [hP τ a, hs τ]
    exact_mod_cast h'
  have eM : w.aM = (kaR Tp hK ((i : ℕ) + 1)).aM := by
    funext τ c
    have h := (hK _ h1 h2 τ).2 (Fin.rev c)
    have hc := c.2
    have h' := GlobalTheory.RecordWeightVec.aMi_eq_aMinusQ D i τ _ c (Fin.rev c) hq (by rw [Fin.val_rev]; omega)
    have e := kaWt_small D hK (even_nV Tp) _ h1 h2 τ c
    rw [← hp, ← neg_neg (DV.aMinusQ _ _ _ _), ← h, ← Int.cast_neg, ← e] at h'
    rw [hM τ c, hs τ]
    exact_mod_cast h'
  have en : w.n = (kaR Tp hK ((i : ℕ) + 1)).n := hn.trans (kaWt_n _ _ _ _).symm
  generalize kaR Tp hK ((i : ℕ) + 1) = u at eP eM en
  cases w; cases u
  simp only at eP eM en
  subst eP eM en
  rfl

theorem exists_isRec : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G) (c : OnConst), J.Q.Canon → HalfEX J.toCore EX → RunsOk fw r → ∃ O : OnObj ((R.toCx F).data F.cr false) (Mir R) c, IsRec Tp hK EX F fw r O := by
  intro D G _ _ Pl0 T0 A J inst R F κ v₀ fw L Pm Tp hK EX r c _ hE ok
  obtain ⟨v₁, -⟩ := exists_place3 D.what₂.LL
  have hc : LawsCore J.toCore := (ok.laws v₁).p.toLawsCore
  have hinj : Function.Injective D.what₂.OtoLL := fun x y hxy => by
    obtain ⟨x, rfl⟩ := J.Q.eO.surjective x
    obtain ⟨y, rfl⟩ := J.Q.eO.surjective y
    rw [← fw.alg_eq, ← fw.alg_eq] at hxy
    exact congrArg _ (RingOfIntegers.ext ((algebraMap J.Q.c.F D.what₂.LL).injective hxy))
  have hκ : ∀ i : Fin D.R.m, κ i = kaR Tp hK ((i : ℕ) + 1) := fun i =>
    eq_kaR Tp hK i (κ i) (fun τ => (fw.kap i τ).1) (fun τ => (fw.kap i τ).2.1)
      (fw.kap i (plOf D (false, Classical.arbitrary _))).2.2
  choose ρ hρ using fun i : Fin D.R.m =>
    ActionPin.exists_rep (T := (r.used v₁).full) (inst := inst) (R := R) (ok.action v₁ i) (mirIncl R)
  obtain ⟨O, z, act, y, ht⟩ := exists_tiedObj (F := F) (fw := fw) (hc := hc) (run := r.used) (h := fun v => (ok.laws v).p)
    (hinj := hinj) (EX := EX) (p := ownAt D) (wL := fun _ i => lR Tp hK ((i : ℕ) + 1))
    (wF := fun _ i => fR Tp hK ((i : ℕ) + 1)) (nT := Tp.TO) (ℓ := r.lev) (ph := fun _ => 1) (c := c) (mirIncl R)
    (blankObj D _ (Mir R) c fun i => R.nW i) ok.action ρ (fun _ i => hρ i)
  letI st : StarRing (𝓞 D.host.E) := J.Q.H.starRing
  letI := hostAlg D
  letI : ∀ s : GlobalTheory.RealIndexBound.RunData J, Algebra s.full.J.Q.c.F D.what₂.LL := fun _ => inst
  have hφ : ∀ x : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.what₂.LL x =
      algebraMap J.Q.c.F D.what₂.LL ((iE D hinj (recB hc) x : 𝓞 J.Q.c.F) : J.Q.c.F) := fun x => by
    refine Eq.trans ?_ (fw.alg_eq _).symm
    refine (oEOsFun_spec D x).symm.trans (congrArg D.what₂.OtoLL ?_)
    exact (J.Q.eO.apply_symm_apply _).symm
  have hσ : ∀ v (i : Fin D.R.m), O.σ v i =
      sigAt (Dw := J.Q.Dw ((i : ℕ) + 1)) (H := J.Q.H) (LL := D.what₂.LL) (depOf J.toCore EX Tp hK) ((i : ℕ) + 1) := fun v i => by
    letI : Algebra (recB (ok.laws v).p.toLawsCore).KO D.what₂.LL := inst
    refine (ht v i).1.toFormTieK.σ_eq.trans ?_
    rw [hκ i]
    exact (GlobalTheory.ScalarOfRun.sigAt_eq_sigRec D L Pm Tp hK (r.used v).full.toTop (ok.laws v).p hinj EX _ (inR_succ i) hE
      D.what₂.LL (algebraMap J.Q.c.F D.what₂.LL) hφ).symm
  refine ⟨{ O with
    E := fun v (j : Fin D.R.m) =>
      EAt (Xo := J.Q.Xo ((j : ℕ) + 1)) (c := J.Q.c) (LL := D.what₂.LL) (depOf J.toCore EX Tp hK) v ((j : ℕ) + 1)
    nnK := fun j : Fin D.R.m => nnKAt (H := J.Q.H) (LL := D.what₂.LL) (depOf J.toCore EX Tp hK) ((j : ℕ) + 1)
    T := (Tp.TO : ℝ)
    g1 := D.host.g 0
    g2 := D.host.g 1
    q1 := D.host.q
    dd := D.host.d
    sm := D.host.small
    k := (D.R.k : ℝ)
    m := (D.R.m : ℝ)
    f := (D.R.f : ℝ)
    x := L.sc.x
    eps := L.sc.eps
    Sc := L.Sc
    eta := L.etaSz
    bp := L.sc.b'
    X2 := L.sc.X'' D.R.n
    vd := vd2 D
    wt := fun _ => 2 * (D.R.f : ℝ) * L.sc.b
    th := fun l => Formalism.UnitaryBoundIntegral.thl D.R.k l
    ad := fun _ => 0
    DF := ((Finset.univ.sup fun j : Fin D.R.m => WeightAlgebra.DF (lR Tp hK ((j : ℕ) + 1)) : ℕ) : ℝ)
    rr := (D.R.r : ℝ)
    Nc := L.Nc
    T2 := D.host.T2.card
    pde := D.host.pde }, ok, hκ, ⟨hc, hinj, z, act, y, fun v i => ⟨{ (ht v i).1 with }, (ht v i).2⟩⟩, ⟨st, ?_⟩,
    rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨fun j => inR_succ j, fun _ => rfl, fun a => ?_, fun _ _ => rfl, hσ, fun _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun j => ?_⟩
  · show star (D.embE (a : D.host.E)) = D.embE ((J.toCore.Q.H.bar a : 𝓞 D.host.E) : D.host.E)
    rw [bar_core, barE_eq_conj, D.embE_conj]
  · exact Nat.cast_le.2 (Finset.le_sup (f := fun j : Fin D.R.m => WeightAlgebra.DF (lR Tp hK ((j : ℕ) + 1))) (Finset.mem_univ j))

end GlobalTheory.BigOn

end
