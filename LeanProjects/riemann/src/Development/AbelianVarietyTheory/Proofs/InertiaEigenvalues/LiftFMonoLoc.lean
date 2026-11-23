import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentiallyCrystallineModuleEqCrystallineRestric
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaThroughOfIsSubFam
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpsInVOfIsSubFam
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseFont

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

noncomputable section

namespace GlobalTheory.StepLiftPf

section Mono

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module O V'] [IsScalarTower O LL V'] [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'}

theorem liftF_mono {L : Lattice (O := O) ρ} {L' : Lattice (O := O) ρ'} (F : LatHom L L') {e e' : ℕ}
    (hF : F.LiftF PD e) (he : e ≤ e') : F.LiftF PD e' := by
  intro c hc
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le he
  rw [pow_add, mul_comm, mul_smul]
  exact (F.ImF PD).smul_mem _ (hF c hc)

end Mono

section MonoLoc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    {O : Type} [CommRing O] [Algebra O LL]

theorem liftF_mono_loc {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {e e' : ℕ}
    (hF : F.LiftF PD e) (he : e ≤ e') : F.LiftF PD e' :=
  liftF_mono PD F hF he

end MonoLoc

section Core

variable {l : ℕ} [Fact l.Prime]

theorem incl_cont {K K' : FinExt l} (h : K.1 ≤ K'.1) : Continuous (Subgroup.inclusion (GK_le h)) :=
  Continuous.subtype_mk continuous_subtype_val _

theorem sub_props (P : LocPrime l) (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal)
    (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c')
    (hFont : TruncatedSeriesCountingIdentities.FontaineAt (P.PD K') ↥LL.1 ↥(OL LL))
    {ι : Type} {k : ℕ} (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1))
    (hc : ∀ x, Continuous (Ms x))
    (Sig : Finset ((pc P h hN hF hS).Iner →* (↥LL.1)ˣ))
    (htr : ∀ a ∈ Sig, ∀ g : (pc P h hN hF hS).Iner, (g : ↥(GK K)) ∈ (pc P h hN hF hS).H → a g = 1)
    (hcop : ∀ a ∈ Sig, Nat.Coprime (orderOf a) (pc P h hN hF hS).PD.p)
    (hpot : ∀ x, (pc P h hN hF hS).IsPotCrys (matRep (Ms x)))
    (hin : ∀ x, (pc P h hN hF hS).InertiaThrough (matRep (Ms x)) Sig)
    (U : Set ℤ) (hJ : ∀ x τ, JumpsInV (P.PD K) (matRep (Ms x)) τ U)
    (W : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hW : IsSubFam Ms W) :
    (pc P h hN hF hS).IsPotCrys W.ρ ∧ (pc P h hN hF hS).InertiaThrough W.ρ Sig ∧
      ∀ τ, JumpsInV (P.PD K) W.ρ τ U := by
  refine ⟨?_, GlobalTheory.inertiaThrough_of_isSubFam l P K K' LL h hN hF hS ι k Ms W hW Sig htr hcop hin,
    fun τ => GlobalTheory.Pass.jumpsInV_of_isSubFam l P K LL ι k Ms W hW τ U fun x => hJ x τ⟩
  let incl := Subgroup.inclusion (GK_le h)
  have hincl : Continuous incl := incl_cont h
  let W' : GRep ↥(GK K') ℚ_[l] ↥LL.1 ↥(OL LL) :=
    { V := W.V, ρ := W.ρ.comp incl, cont := fun x => (W.cont x).comp hincl }
  let Ms' : ι → (↥(GK K') →* Matrix (Fin k) (Fin k) ↥LL.1) := fun x => (Ms x).comp incl
  have hc' : ∀ x v, Continuous fun g => (Ms' x g).mulVec v :=
    fun x v => ((hc x).comp hincl).matrix_mulVec continuous_const
  have hcr' : ∀ x, IsCrys (P.PD K') (matRep (Ms' x)) := fun x =>
    (GlobalTheory.PcRes.main l P K K' LL h hN hF hS _ (matRep (Ms x))).2.1 (hpot x)
  have hsub : IsSubOfSums W'.ρ (fun x => ⇑(Ms' x)) := by
    obtain ⟨a, x, p, hp, hinj⟩ := hW
    refine ⟨a, x, LinearMap.pi p, ?_, fun g v => funext fun j => hp j (incl g) v⟩
    rw [injective_iff_map_eq_zero]
    intro v hv
    exact hinj v fun j => congrFun hv j
  have hW' : IsCrys (P.PD K') W'.ρ :=
    (subsum_crys (PD := P.PD K') (Ms := Ms') (hc := hc') (hF := hFont) (S := fun _ => Set.univ)
      (hcr := hcr') (hS := fun _ _ _ _ => Set.mem_univ _) (A := W') (hA := hsub)).1
  exact (GlobalTheory.PcRes.main l P K K' LL h hN hF hS W.V W.ρ).2.2 hW'

end Core

section Apply

open Formalism.MainNotions.ElementDenominator

variable {l : ℕ} [Fact l.Prime]

set_option maxHeartbeats 1000000 in

theorem liftFam_core (P : LocPrime l) (K' LL : FinExt l) (h : (qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal)
    (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK (qlExt l))) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      (P.PD (qlExt l)).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c')
    (CT : ℕ) (hT : thmT (pc P h hN hF hS) LL CT)
    (hFont : TruncatedSeriesCountingIdentities.FontaineAt (P.PD K') ↥LL.1 ↥(OL LL))
    {ι : Type} {k : ℕ} (Ms : ι → (↥(GK (qlExt l)) →* Matrix (Fin k) (Fin k) ↥LL.1))
    (hc : ∀ x, Continuous (Ms x)) (N η H : ℕ) (hN2 : 2 ≤ N) (hη : 1 ≤ η) (hηH : η < H)
    (hsize : CT * (H * N ^ 2 + N ^ 3) < l)
    (Sig : Finset ((pc P h hN hF hS).Iner →* (↥LL.1)ˣ)) (Fr : ↥(GK (qlExt l)))
    (hFr : (pc P h hN hF hS).IsFrob Fr) (hSt : FrobStable (pc P h hN hF hS).Iner Fr Sig)
    (h1 : 1 ∈ Sig) (hcard : Sig.card ≤ N)
    (htr : ∀ a ∈ Sig, ∀ g : (pc P h hN hF hS).Iner, (g : ↥(GK (qlExt l))) ∈ (pc P h hN hF hS).H → a g = 1)
    (hcop : ∀ a ∈ Sig, Nat.Coprime (orderOf a) (pc P h hN hF hS).PD.p)
    (hpot : ∀ x, (pc P h hN hF hS).IsPotCrys (matRep (Ms x)))
    (hin : ∀ x, (pc P h hN hF hS).InertiaThrough (matRep (Ms x)) Sig)
    (U : Finset ℤ) (hU : ∀ u ∈ U, -(η : ℤ) ≤ u ∧ u ≤ H) (hU0 : (0 : ℤ) ∈ U) (hUc : U.card ≤ N + 1)
    (hJ : ∀ x τ, JumpsInV (P.PD (qlExt l)) (matRep (Ms x)) τ (U : Set ℤ)) :
    LiftFam (O := ↥(OL LL)) (P.PD (qlExt l)) Ms (CT * (N * (N ^ 2 / 4) + η * (N + N ^ 2 / 4))) := by
  intro W₁ W₂ hW₁ hW₂ L₁ L₂ F hFo
  have k₁ := sub_props P (qlExt l) K' LL h hN hF hS hFont Ms hc Sig htr hcop hpot hin _ hJ W₁ hW₁
  have k₂ := sub_props P (qlExt l) K' LL h hN hF hS hFont Ms hc Sig htr hcop hpot hin _ hJ W₂ hW₂
  let T₁ : LocLat ↥(GK (qlExt l)) ℚ_[l] ↥LL.1 ↥(OL LL) :=
    { V := W₁.V, modO := W₁.modO, towO := W₁.towO, ρ := W₁.ρ, cont := W₁.cont, L := L₁ }
  let T₂ : LocLat ↥(GK (qlExt l)) ℚ_[l] ↥LL.1 ↥(OL LL) :=
    { V := W₂.V, modO := W₂.modO, towO := W₂.towO, ρ := W₂.ρ, cont := W₂.cont, L := L₂ }
  obtain ⟨h4, hL⟩ := hT T₁ T₂ F N η H U Sig Fr k₁.1 k₂.1 hFo hFr hSt h1 hcard hN2 k₁.2.1 k₂.2.1 hU hU0
    hUc hη hηH k₁.2.2 k₂.2.2 hsize
  have hr : rPrime (pc P h hN hF hS).Iner Fr Sig ≤ N ^ 2 / 4 :=
    (Nat.le_div_iff_mul_le (by norm_num)).2 (by rw [mul_comm]; exact h4)
  have he : CT * (N * rPrime (pc P h hN hF hS).Iner Fr Sig + η * (N + rPrime (pc P h hN hF hS).Iner Fr Sig)) ≤
      CT * (N * (N ^ 2 / 4) + η * (N + N ^ 2 / 4)) := by
    gcongr
  exact liftF_mono_loc (P.PD (qlExt l)) (T₁ := T₁) (T₂ := T₂) F hL he

end Apply

section Wrap

open Formalism.MainNotions.ElementDenominator

variable {l : ℕ} [Fact l.Prime]

set_option maxHeartbeats 1000000 in

theorem liftFam_of_eq (P : LocPrime l) (K K' LL : FinExt l) (hK : K = qlExt l) (CT : ℕ)
    (hT : ∀ (K' : FinExt l) (h : (qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
      (hS : ∀ (g : ↥(GK (qlExt l))) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
        (P.PD (qlExt l)).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c'),
      thmT (pc P h hN hF hS) LL CT)
    (hFont : ∀ K'' : FinExt l, TruncatedSeriesCountingIdentities.FontaineAt (P.PD K'') ↥LL.1 ↥(OL LL))
    {ι : Type} {k : ℕ} (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1))
    (hc : ∀ x, Continuous (Ms x)) (N η H : ℕ) (hN2 : 2 ≤ N) (hη : 1 ≤ η) (hηH : η < H)
    (hsize : CT * (H * N ^ 2 + N ^ 3) < l)
    (h : K.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c')
    (Sig : Finset ((pc P h hN hF hS).Iner →* (↥LL.1)ˣ)) (Fr : ↥(GK K))
    (hFr : (pc P h hN hF hS).IsFrob Fr) (hSt : FrobStable (pc P h hN hF hS).Iner Fr Sig)
    (h1 : 1 ∈ Sig) (hcard : Sig.card ≤ N)
    (hx : ∀ x, (pc P h hN hF hS).IsPotCrys (matRep (Ms x)) ∧
      (pc P h hN hF hS).InertiaThrough (matRep (Ms x)) Sig)
    (U : Finset ℤ) (hU : ∀ u ∈ U, -(η : ℤ) ≤ u ∧ u ≤ H) (hU0 : (0 : ℤ) ∈ U) (hUc : U.card ≤ N + 1)
    (hJ : ∀ x τ, JumpsInV (P.PD K) (matRep (Ms x)) τ (U : Set ℤ)) :
    LiftFam (O := ↥(OL LL)) (P.PD K) Ms (CT * (N * (N ^ 2 / 4) + η * (N + N ^ 2 / 4))) := by
  subst hK
  by_cases hne : Nonempty ι
  · obtain ⟨x0⟩ := hne
    exact liftFam_core P K' LL h hN hF hS CT (hT K' h hN hF hS) (hFont K') Ms hc N η H hN2 hη hηH hsize
      Sig Fr hFr hSt h1 hcard (hx x0).2.1 (hx x0).2.2.1 (fun x => (hx x).1) (fun x => (hx x).2)
      U hU hU0 hUc hJ
  · have hemp : ∀ x : ι, False := fun x => hne ⟨x⟩
    refine liftFam_core P K' LL h hN hF hS CT (hT K' h hN hF hS) (hFont K') Ms hc N η H hN2 hη hηH hsize
      {1} Fr hFr ?_ (Finset.mem_singleton_self _) (by rw [Finset.card_singleton]; omega) ?_ ?_
      (fun x => (hemp x).elim) (fun x => (hemp x).elim) U hU hU0 hUc hJ
    · intro a ha
      rw [Finset.mem_singleton] at ha
      subst ha
      exact ⟨1, Finset.mem_singleton_self _, fun _ _ _ => rfl⟩
    · intro a ha g _
      rw [Finset.mem_singleton] at ha
      subst ha
      rfl
    · intro a ha
      rw [Finset.mem_singleton] at ha
      subst ha
      rw [orderOf_one]
      exact Nat.coprime_one_left _

end Wrap

theorem main : StepLift := by
  intro D CT hT hFont i w hw hdeg ι Ms hc eta H hlt hsize hPot hJump
  obtain ⟨K', h, hN, hF, hS, Sig, Fr, hFr, hSt, h1, hcard, hx⟩ := hPot
  obtain ⟨U, hU, hU0, hUc, hJ⟩ := hJump
  have hK : (D.nbr i w hw).Kw = Formalism.MainNotions.ElementDenominator.qlExt (D.nd.l i) :=
    Subtype.ext (IntermediateField.finrank_eq_one_iff.1 hdeg)
  have hT' : Formalism.MainNotions.ElementDenominator.CorollaryALocal D.loc CT := hT
  have hnV : 2 ≤ D.R.nV + 1 := by
    have h5 := D.R.rank_add_five_le
    have : D.R.nV = D.R.r + D.R.t := rfl
    omega
  have hcl : ∀ x, Continuous (Br.loc D.nbr i w hw (Ms x)) := by
    intro x
    have hfc : Continuous (D.nbr i w hw).toLL := continuous_subtype_val.comp (D.nbr i w hw).eO_cont
    have h1' : Continuous fun g : Br.G D.nbr i w hw => Ms x ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) :=
      (hc x).comp (continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw))
    exact h1'.matrix_map hfc
  exact liftFam_of_eq (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL hK CT
    (fun K' h hN hF hS => hT' (D.nd.l i) K' h hN hF hS (D.nbr i w hw).LL)
    (fun K'' => hFont (D.nd.l i) K'' (D.nbr i w hw).LL)
    (fun x => Br.loc D.nbr i w hw (Ms x)) hcl (D.R.nV + 1) (eta + D.R.t + 1) H hnV (by omega) hlt hsize
    h hN hF hS Sig Fr hFr hSt h1 hcard hx U hU hU0 hUc hJ

end GlobalTheory.StepLiftPf
