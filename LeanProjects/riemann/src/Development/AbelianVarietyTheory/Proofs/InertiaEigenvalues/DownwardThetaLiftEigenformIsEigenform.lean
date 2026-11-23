import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFormEigenMemSinglePart
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaVacuumHeckeIdentitySplitPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalThetaCorrespondenceInertPlaceOfHowe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperspecialFixesAllChainVacuaAtInertPrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplittingCharactersUnramifiedOffLevels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperspecialFixesVacuaGoodInertPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OntoPartAtOfZeroOrInjAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelOperatorsAtPrimeOffLevelDatum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightCocharacterEqOfGoodPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
import Formalism.LocalToGlobal.JointCharacters.LocEMulLocE
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardKerSubspacesAndHeckePolyOfConvolution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothVecLowKSub
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.DownEigen

open Formalism.IndefR GlobalTheory.Hk3

theorem tri_solve {X : Type} [AddCommGroup X] [Module ℂ X] (z : ℕ → ℕ → ℂ) (α : ℕ → ℂ) (hz : ∀ k, z k k ≠ 0) (m : ℕ) :
    ∃ β : ℕ → ℂ, ∀ (F : X) (T : ℕ → X), (∀ k, k < m → ∑ j ∈ Finset.range (k + 1), z k j • T j = α k • F) →
      ∀ k, k < m → T k = β k • F := by
  induction m with
  | zero => exact ⟨0, fun _ _ _ k hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ m ih =>
    obtain ⟨β, hβ⟩ := ih
    refine ⟨Function.update β m ((z m m)⁻¹ * (α m - ∑ j ∈ Finset.range m, z m j * β j)), fun F T h k hk => ?_⟩
    have hlow : ∀ k, k < m → T k = β k • F := hβ F T fun k hk => h k (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · rw [Function.update_of_ne (by omega)]
      exact hlow k hk
    · rw [Function.update_self]
      have e := h k (by omega)
      rw [Finset.sum_range_succ] at e
      have e2 : ∑ j ∈ Finset.range k, z k j • T j = (∑ j ∈ Finset.range k, z k j * β j) • F := by
        rw [Finset.sum_smul]
        exact Finset.sum_congr rfl fun j hj => by rw [hlow j (Finset.mem_range.1 hj), smul_smul]
      rw [e2] at e
      have e3 : z k k • T k = (α k - ∑ j ∈ Finset.range k, z k j * β j) • F := by
        rw [sub_smul, ← e]; abel
      rw [mul_smul, ← e3, smul_smul, inv_mul_cancel₀ (hz k), one_smul]

theorem tri_solve' {X : Type} [AddCommGroup X] [Module ℂ X] (n : ℕ) (z : ℕ → ℕ → ℂ) (α : ℕ → ℂ) (hz : ∀ k, z k k ≠ 0) :
    ∃ β : ℕ → ℂ, ∀ (F : X) (T : ℕ → X),
      (∀ k, k ≤ n → α k • F = ∑ j ∈ Finset.range (n + 1), (if j ≤ k then z k j else 0) • T j) →
      ∀ k, k ≤ n → T k = β k • F := by
  obtain ⟨β, hβ⟩ := tri_solve (X := X) z α hz (n + 1)
  refine ⟨β, fun F T h k hk => hβ F T (fun k' hk' => ?_) k (by omega)⟩
  rw [h k' (by omega)]
  refine (Finset.sum_congr rfl fun j hj => ?_).trans
    (Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun j hj hj' => ?_)
  · rw [Finset.mem_range] at hj
    rw [if_pos (by omega)]
  · rw [Finset.mem_range] at hj hj'
    rw [if_neg (by omega), zero_smul]

variable {D : D7}

theorem rep_of_not {V : HSp D} {P : Pl D.host.E} {d : List ℤ} (h : ¬ IsLab V P d) : GlobalTheory.Hk3.rep V P d = ∅ := by
  unfold GlobalTheory.Hk3.rep; rw [dif_neg h]

theorem hkF_evC (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (P : Pl D.host.E) (a : List ℤ → ℂ)
    (Φ : Bridge.Gf V → W) (h : ∀ d, IsLab V P d → hkF V P (Finsupp.single d 1) Φ = a d • Φ) (c : List ℤ →₀ ℂ) :
    hkF V P c Φ = evC V P a c • Φ := by
  classical
  funext g
  have e : ∀ d, ∑ γ ∈ GlobalTheory.Hk3.rep V P d, Φ (g * (finHom V).rangeRestrict γ) = (if IsLab V P d then a d else 0) • Φ g := by
    intro d
    by_cases hd : IsLab V P d
    · have := congrFun (h d hd) g
      unfold hkF at this
      rw [Finsupp.sum_single_index (by simp), one_smul] at this
      rw [if_pos hd, this]; rfl
    · rw [if_neg hd, rep_of_not hd, Finset.sum_empty, zero_smul]
  simp only [hkF, evC, Finsupp.sum, Pi.smul_apply, Finset.sum_smul, e, smul_smul]
  refine Finset.sum_congr rfl fun d _ => ?_
  split_ifs <;> simp

theorem hk_splitC (V : HSp D) (P : Pl D.host.E) (n : ℕ) (z : ℕ → ℂ) :
    hk V P (splitC n z) = ∑ j ∈ Finset.range (n + 1), z j • hk V P (Finsupp.single (splitLab n j) 1) := by
  unfold splitC hk
  rw [← Finsupp.sum_finsetSum_index (by simp) (by simp [add_smul])]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp), one_smul]

theorem postOn_sum {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (s : Finset ℕ) (w : ℕ → ℂ)
    (L : ℕ → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (T : MMap M) :
    postOn M (∑ j ∈ s, w j • L j) T = ∑ j ∈ s, w j • postOn M (L j) T := by
  ext v
  simp [postOn]

theorem postOn_hk_splitC {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (P : Pl D.host.E) (n : ℕ) (z : ℕ → ℂ)
    (U : MMap M) : postOn M (hk V P (splitC n z)) U =
      ∑ j ∈ Finset.range (n + 1), z j • postOn M (hk V P (Finsupp.single (splitLab n j) 1)) U := by
  rw [hk_splitC, postOn_sum]

theorem exists_split_data {P : Pl D.host.E} (hc : Formalism.DivisionValues.conjPl P ≠ P) : ∃ (e : AE D) (ϖ : 𝓞 D.host.E) (x : (AE D)ˣ),
    Formalism.L2.NTheta.IsIdemAt e P ∧ ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 ∧ (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) := by
  obtain ⟨e, he⟩ := GlobalTheory.Hk3.SplitMatch.exists_isIdemAt hc
  obtain ⟨ϖ, h1, h2⟩ : ∃ ϖ ∈ P.asIdeal, ϖ ∉ P.asIdeal ^ 2 :=
    SetLike.exists_of_lt (Ideal.pow_lt_self _ P.ne_bot P.isPrime.ne_top 2 le_rfl)
  have h0 : (ϖ : D.host.E) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 fun h => h2 (h ▸ zero_mem _)
  exact ⟨e, ϖ, Formalism.L2.JoinChr.locU he.1.1 (Units.mk0 _ h0), he, h1, h2, by
    rw [Formalism.L2.JoinChr.locU_val, Formalism.L2.JoinChr.locE, Units.val_mk0]; ring⟩

theorem diag_ne_zero (P : Pl D.host.E) (χS χT : (AE D)ˣ →* Circle) (x : (AE D)ˣ) (nS nT t k : ℕ) :
    (Ideal.absNorm P.asIdeal : ℂ) ^ ((nT - k) * (k - k)) * (Formalism.L2.Col.gaussBin (Ideal.absNorm P.asIdeal) t (k - k) : ℂ) *
      ((χT x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ nT)⁻¹ ^ k *
      ((χS x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ nS) ^ k ≠ 0 := by
  have hq0 : Ideal.absNorm P.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact P.ne_bot
  have hs0 : (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 (by exact_mod_cast Nat.pos_of_ne_zero hq0))
  have hT : (χT x : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have hS : (χS x : ℂ) ≠ 0 := Circle.coe_ne_zero _
  rw [Nat.sub_self, mul_zero, pow_zero, one_mul, GlobalTheory.KerRangeCount.gaussBin_zero_right, Nat.cast_one, one_mul]
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero (mul_ne_zero hT (pow_ne_zero _ hs0))))
    (pow_ne_zero _ (mul_ne_zero hS (pow_ne_zero _ hs0)))

theorem dualC_dualC' (c : List ℤ →₀ ℂ) : dualC (dualC c) = c := by
  unfold dualC
  rw [← Finsupp.mapDomain_comp]
  have : dualLab ∘ dualLab = id := by
    funext d
    simp [dualLab, List.map_reverse]
  rw [this, Finsupp.mapDomain_id]

theorem scalar_of_split' {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (P : Pl D.host.E)
    (hP : Formalism.DivisionValues.conjPl P ≠ P) (S : M → Prop) (fu : ∀ u, S u → ∀ k ∈ hyp V P, π k u = u)
    (ha : ∀ k, k ≤ V.rank → ∃ l : ℂ, ∀ u, S u → opOf π P (Finsupp.single (splitLab V.rank k) 1) u = l • u)
    (hb : ∀ k, k ≤ V.rank → ∃ l : ℂ, ∀ u, S u →
      opOf π (Formalism.DivisionValues.conjPl P) (Finsupp.single (splitLab V.rank k) 1) u = l • u) (d : List ℤ) :
    ∃ l : ℂ, ∀ u, S u → opOf π P (Finsupp.single d 1) u = l • u := by
  obtain ⟨x, hx, hxe⟩ := GlobalTheory.T.exists_adjoin_splitHeckeGenerators_duals_spherical V P hP M π d
  obtain ⟨l, h1⟩ := GlobalTheory.ConjScalar.OnePart.adjoin_scalar _ S (by
    rintro y ⟨k, hk, rfl | rfl⟩
    · exact ha k hk
    · have hc := (GlobalTheory.T.sphericalHecke_conjPlace_eq_dualLabel V P).2.2 (Finsupp.single (splitLab V.rank k) 1) M π
      have hd : dualC (Finsupp.single (splitLab V.rank k) 1) = Finsupp.single (dualLab (splitLab V.rank k)) 1 := by
        unfold dualC
        rw [Finsupp.mapDomain_single]
      rw [hd] at hc
      obtain ⟨l, hl⟩ := hb k hk
      exact ⟨l, fun u hu => by rw [← hc u (fu u hu)]; exact hl u hu⟩) x hx
  exact ⟨l, fun u hu => by rw [← hxe u (fu u hu), h1 u hu]⟩

theorem thF_match' {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} (hC : Core R F) (i : Fin D.R.m) (t : T)
    {P : Pl D.host.E} (hP : Good R t P) (hfix : VacFix R.ψ (R.ωP i t) P) {cV cW : List ℤ →₀ ℂ}
    (hM : Match R.ψ (R.ωP i t) P (dualC cV) cW) {y y' : (R.HV i t).H}
    (hy : (R.HV i t).e y' = hkF (Vc D i) P cV ((R.HV i t).e y)) :
    R.thF i t y' = postOn (R.MW i (sg0 D A)) (hk (Wc D i) P cW) (R.thF i t y) :=
  sub_eq_zero.1 (GlobalTheory.LowTypeDetermined.eq_zero_of_lowT D _ _ (R.MW i (sg0 D A)) R.θ hC.models.inf
    (GlobalTheory.LowTypeRestriction.lowT_ne_bot _) _ _ _
    (sub_mem (hC.thP.thF_mem i t y') (GlobalTheory.DefLiftHecke.wall_laws hC i t hP cW (hC.thP.thF_mem i t y)).1)
    fun v => sub_eq_zero.2 (GlobalTheory.DefLiftHecke.thF_low hC i t hP hfix hM hy v))

set_option maxHeartbeats 4000000 in

theorem downEig : GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, DownEig R i t := by
  intro hH D G _ _ Pl0 T A Ks _ _ _ R F hG hFP i t h hh s
  have hC := hG.core
  have hVinj : Function.Injective (R.HV i t).e := (hC.models.HV i t).1
  have hV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have hWr : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have unr : ∀ P, Good R t P → UnrPl P (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1 ∧
      UnrPl P (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 := fun P hP =>
    GlobalTheory.FixAllGood.unrPl_chrTh ((GlobalTheory.T.splittingCharacters_unramified_offLevels R F hC.lev t P hP).2 ((i : ℕ) + 1) (by omega) i.2)
      (GlobalTheory.T.splittingCharacters_unramified_offLevels R F hC.lev t P hP).1

  have eigV : ∀ P, Good R t P → ∀ cV y, IsEigV R i t h s y →
      (R.HV i t).e (evC (Vc D i) P (s P) cV • y) = hkF (Vc D i) P cV ((R.HV i t).e y) := by
    intro P hP cV y hy
    rw [map_smul, hkF_evC (Vc D i) P (s P) ((R.HV i t).e y) (fun d hd => by
      rw [← hh P hP, hy P d hP hd, map_smul]) cV]

  have matched : ∀ P, Good R t P → VacFix R.ψ (R.ωP i t) P → ∀ cV cW, Match R.ψ (R.ωP i t) P (dualC cV) cW →
      ∀ y, IsEigV R i t h s y → postOn (R.MW i (sg0 D A)) (hk (Wc D i) P cW) (R.thF i t y) =
        evC (Vc D i) P (s P) cV • R.thF i t y := by
    intro P hP hfx cV cW hM y hy
    rw [← thF_match' hC i t hP hfx hM (eigV P hP cV y hy), map_smul]

  have inert : ∀ P, Good R t P → Formalism.DivisionValues.conjPl P = P → ∀ d, ∃ l : ℂ, ∀ y, IsEigV R i t h s y →
      postOn (R.MW i (sg0 D A)) (hk (Wc D i) P (Finsupp.single d 1)) (R.thF i t y) = l • R.thF i t y := by
    intro P hP hc d
    have hr : Odd D.R.r := GlobalTheory.VacFixInert.r_odd
    have ht : Odd D.R.t := D.R.t_odd
    have hfx : VacFix R.ψ (R.ωP i t) P :=
      GlobalTheory.VacFixInert.vacFix_of_inert R.ψ (R.ωP i t) P (hFP i t).inert
        (by rw [hV, hWr]; have := ht.pos; omega) (by left; rw [hV]; exact hr.add_odd ht) hc (unr P hP).1 (unr P hP).2
    have hcorr := GlobalTheory.Hk3.CorrInert.sphCorr_of_inert hH R.ψ _ _ _ _ _ P (hC.thP.ωP i t) hc hfx
    obtain ⟨cS, hM⟩ := hcorr.2.1 (Finsupp.single d 1)
    have hM' : Match R.ψ (R.ωP i t) P (dualC (dualC cS)) (Finsupp.single d 1) := by rwa [dualC_dualC']
    exact ⟨_, matched P hP hfx (dualC cS) _ hM'⟩

  have split : ∀ P, Good R t P → Formalism.DivisionValues.conjPl P ≠ P → ∀ k, k ≤ (Wc D i).rank → ∃ l : ℂ, ∀ y, IsEigV R i t h s y →
      postOn (R.MW i (sg0 D A)) (hk (Wc D i) P (Finsupp.single (splitLab (Wc D i).rank k) 1)) (R.thF i t y) =
        l • R.thF i t y := by
    intro P hP hc
    obtain ⟨e, ϖ, x, he, h1, h2, hx⟩ := exists_split_data hc
    have hrk : (Vc D i).rank = (Wc D i).rank + D.R.t := by rw [hV, hWr]
    have hms0 := GlobalTheory.Hk3.SplitMatch.match_split R.ψ (Vc D i) (Wc D i) _ _ (R.ωP i t) P (hC.thP.ωP i t) hc
      (unr P hP).1 (unr P hP).2
    have hms := (hms0.2 e ϖ x D.R.t he h1 h2 hx).2 hrk
    obtain ⟨β, hβ⟩ := tri_solve' (X := MMap (R.MW i (sg0 D A))) (Wc D i).rank
      (fun k j => (Ideal.absNorm P.asIdeal : ℂ) ^ (((Wc D i).rank - j) * (k - j)) *
        (Formalism.L2.Col.gaussBin (Ideal.absNorm P.asIdeal) D.R.t (k - j) : ℂ) *
        (((Formalism.IndefR.Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 x : ℂ) *
          (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ (Wc D i).rank)⁻¹ ^ k *
        (((Formalism.IndefR.Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1 x : ℂ) *
          (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ (Vc D i).rank) ^ j)
      (fun k => evC (Vc D i) P (s P) (Finsupp.single (splitLab (Vc D i).rank k) 1))
      (fun k => diag_ne_zero P _ _ x (Vc D i).rank (Wc D i).rank D.R.t k)
    intro k hkr
    refine ⟨β k, fun y hy => hβ (R.thF i t y)
      (fun j => postOn (R.MW i (sg0 D A)) (hk (Wc D i) P (Finsupp.single (splitLab (Wc D i).rank j) 1)) (R.thF i t y))
      (fun k' hk' => ?_) k hkr⟩
    have := matched P hP hms0.1 _ _ (hms k' (by omega)) y hy
    exact this.symm.trans (postOn_hk_splitC _ P _ _ _)

  let Sset : MMap (R.MW i (sg0 D A)) → Prop := fun u => ∃ y, IsEigV R i t h s y ∧ u = R.thF i t y
  obtain ⟨n, hβ⟩ := hC.lev.βW i
  have hlev := fun (P : Pl D.host.E) (hP : Good R t P) =>
    GlobalTheory.LevOp.level_operators (Wc D i) (R.βW i) (R.ΛW i) (1 ^ n) (R.datWp i R.triv) hβ P
      (by rw [one_pow, Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top)
      (by
        intro PP hPP
        refine hP PP (hPP.imp id ?_)
        intro h
        exact absurd h (Finset.notMem_empty _))
  have hfix : ∀ P, Good R t P → ∀ u, Sset u → ∀ k ∈ hyp (Wc D i) P,
      GlobalTheory.Hk3.LabDet.rRep (R.MW i (sg0 D A)) k u = u := by
    rintro P hP u ⟨y, -, rfl⟩ k hk
    exact GlobalTheory.Hk3.LabDet.mult_lev _ _ _ _ _ (hC.thP.thF_mem i t y) k ((hlev P hP).1 k hk).1 ((hlev P hP).1 k hk).2
  have toOp : ∀ P d, (∃ l : ℂ, ∀ y, IsEigV R i t h s y →
      postOn (R.MW i (sg0 D A)) (hk (Wc D i) P (Finsupp.single d 1)) (R.thF i t y) = l • R.thF i t y) →
      ∃ l : ℂ, ∀ u, Sset u → opOf (GlobalTheory.Hk3.LabDet.rRep (R.MW i (sg0 D A))) P (Finsupp.single d 1) u = l • u := by
    rintro P d ⟨l, hl⟩
    refine ⟨l, ?_⟩
    rintro u ⟨y, hy, rfl⟩
    exact (GlobalTheory.ConjScalar.OnePart.postOn_hk_single _ P d _).symm.trans (hl y hy)
  have key : ∀ P, Good R t P → ∀ d, ∃ l : ℂ, ∀ u, Sset u →
      opOf (GlobalTheory.Hk3.LabDet.rRep (R.MW i (sg0 D A))) P (Finsupp.single d 1) u = l • u := by
    intro P hP d
    by_cases hc : Formalism.DivisionValues.conjPl P = P
    · exact toOp P d (inert P hP hc d)
    · have hcc : Formalism.DivisionValues.conjPl (Formalism.DivisionValues.conjPl P) = P := Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl P
      have hP' := GlobalTheory.ConjScalar.OnePart.good_conj R t P hP
      exact scalar_of_split' _ P hc Sset (hfix P hP)
        (fun k hk => toOp P _ (split P hP hc k hk))
        (fun k hk => toOp _ _ (split _ hP' (by rw [hcc]; exact fun e => hc e.symm) k hk)) d
  have key2 : ∀ P d, ∃ l : ℂ, ∀ u, Sset u → ∀ B, Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) P d B →
        heckeOn (R.MW i (sg0 D A)) B u = l • u := by
    intro P d
    by_cases hP : Good R t P
    · obtain ⟨l, hl⟩ := key P hP d
      refine ⟨l, fun u hu B hB => ?_⟩
      have hs := (((hlev P hP).2.1 _ d B).1 hB).2
      have e1 : heckeOn (R.MW i (sg0 D A)) B u = ∑ γ ∈ B, GlobalTheory.Hk3.LabDet.rRep (R.MW i (sg0 D A)) γ u := by
        rw [← GlobalTheory.Hk3.LabDet.sum_rRep, LinearMap.sum_apply]
      exact e1.trans ((((GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors (Wc D i) P).1 d B hs).2 _ _ u (hfix P hP u hu)).trans (hl u hu))
    · refine ⟨0, fun u _ B hB => ?_⟩
      obtain ⟨_, _, _, _, ho, _⟩ := hB
      exact absurd ((GlobalTheory.LiftOntoCompare.offS_iff_good (R := R) t P).1 ho) hP
  choose ev hev using key2
  refine ⟨ev, fun y hy => ?_⟩
  exact (GlobalTheory.Hk3.LabDet.mem_partFull _ _ _ _ _ _ _).2 ⟨hC.thP.thF_mem i t y, fun P d B hB => hev P d _ ⟨y, hy, rfl⟩ B hB⟩

end GlobalTheory.DownEigen
