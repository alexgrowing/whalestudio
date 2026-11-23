import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalFamilyOrthogonalDecomposition
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FamilySplitOperatorsEqLabelOperatorsModels
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftTransferHeckePolySplitPrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalOperatorsFormsOnRankSpaceNormalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassPresExtMemExtBijIsom

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.LiftAdjointBlock

section Abstract

open Formalism.L2.Col

variable {K V W I : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W] {σ : K →+* ℂ}

theorem map_mem_eigAt (j : V →ₛₗ[σ] W) {op : I → Module.End K V} {opC : I → Module.End ℂ W}
    (hj : ∀ i x, j (op i x) = opC i (j x)) {s : I → K} {v : V} (hv : v ∈ eigAt op s) :
    j v ∈ eigAt opC fun i => σ (s i) := by
  rw [eigAt, Submodule.mem_iInf]
  intro i
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 (eigAt_le op s i hv)
  rw [Module.End.mem_maxGenEigenspace]
  refine ⟨k, ?_⟩
  have key : ∀ (k : ℕ) (v : V), ((opC i - σ (s i) • (1 : Module.End ℂ W)) ^ k) (j v) =
      j (((op i - s i • (1 : Module.End K V)) ^ k) v) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ, Module.End.mul_apply, pow_succ, Module.End.mul_apply, ← ih]
      congr 1
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, LinearMap.map_smulₛₗ, hj]
  rw [key, hk, map_zero]

theorem span_eigSum_le (j : V →ₛₗ[σ] W) {op : I → Module.End K V} {opC : I → Module.End ℂ W}
    (hj : ∀ i x, j (op i x) = opC i (j x)) (Q : (I → ℂ) → Prop) :
    Submodule.span ℂ (j '' (eigSum op (fun s => Q fun i => σ (s i)) : Set V)) ≤ eigSum opC Q := by
  rw [Submodule.span_le]
  rintro _ ⟨v, hv, rfl⟩
  refine Submodule.iSup_induction _ (motive := fun v => j v ∈ eigSum opC Q) hv (fun s v hv => ?_) (by simp) fun a b ha hb => ?_
  · by_cases hs : Q fun i => σ (s i)
    · rw [iSup_pos hs] at hv
      exact eigAt_le_eigSum hs (map_mem_eigAt j hj hv)
    · rw [iSup_neg hs, Submodule.mem_bot] at hv
      rw [hv, map_zero]
      exact Submodule.zero_mem _
  · rw [map_add]
    exact Submodule.add_mem _ ha hb

theorem eigSum_le_span [FiniteDimensional K V] [FiniteDimensional ℂ W] (j : V →ₛₗ[σ] W) {op : I → Module.End K V}
    {opC : I → Module.End ℂ W} (hj : ∀ i x, j (op i x) = opC i (j x)) (hsp : Submodule.span ℂ (Set.range j) = ⊤)
    (hc : PairComm op) (hs : SplitOver op) (hcC : PairComm opC) (Q : (I → ℂ) → Prop) :
    eigSum opC Q ≤ Submodule.span ℂ (j '' (eigSum op (fun s => Q fun i => σ (s i)) : Set V)) := by
  have hA := span_eigSum_le j hj Q
  have hB := span_eigSum_le j hj fun y => ¬ Q y
  have htop : Submodule.span ℂ (j '' (eigSum op (fun s => Q fun i => σ (s i)) : Set V)) ⊔
      Submodule.span ℂ (j '' (eigSum op (fun s => ¬ Q fun i => σ (s i)) : Set V)) = ⊤ := by
    rw [eq_top_iff, ← hsp, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1
      ((isCompl_eigSum hc hs (fun s => Q fun i => σ (s i))).sup_eq_top ▸ (Submodule.mem_top : v ∈ (⊤ : Submodule K V)))
    rw [map_add]
    exact add_mem (Submodule.mem_sup_left (Submodule.subset_span ⟨a, ha, rfl⟩))
      (Submodule.mem_sup_right (Submodule.subset_span ⟨b, hb, rfl⟩))
  have hd := (disjoint_eigSum hcC (C := Q) (C' := fun y => ¬ Q y) fun _ h h' => h' h).mono_right hB
  calc eigSum opC Q = (Submodule.span ℂ (j '' (eigSum op (fun s => Q fun i => σ (s i)) : Set V)) ⊔
      Submodule.span ℂ (j '' (eigSum op (fun s => ¬ Q fun i => σ (s i)) : Set V))) ⊓ eigSum opC Q := by
        rw [htop, top_inf_eq]
    _ ≤ _ := by rw [sup_inf_assoc_of_le _ hA, hd.symm.eq_bot, sup_bot_eq]

theorem adjoint_eigen {X E : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (Θ : X →ₗ[ℂ] E) {S : Module.End ℂ X}
    {T : Module.End ℂ E} (h : ∀ u, Θ (S u) = T (Θ u)) (hS : Commute S (LinearMap.adjoint S))
    (hT : Commute T (LinearMap.adjoint T)) {l : ℂ} {w : E} (hw : T w = l • w) :
    S (LinearMap.adjoint Θ w) = l • LinearMap.adjoint Θ w := by
  have h0 : (T - l • (1 : Module.End ℂ E)) w = 0 := by simp [hw]
  have h1 := GlobalTheory.NormalFamily.adjoint_apply_eq_zero (GlobalTheory.NormalFamily.commute_sub_smul hT l) h0
  have h2 : LinearMap.adjoint (S - l • (1 : Module.End ℂ X)) (LinearMap.adjoint Θ w) = 0 := by
    refine ext_inner_right ℂ fun u => ?_
    have e : Θ ((S - l • (1 : Module.End ℂ X)) u) = (T - l • (1 : Module.End ℂ E)) (Θ u) := by simp [h]
    rw [LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left, e, ← LinearMap.adjoint_inner_left, h1,
      inner_zero_left, inner_zero_left]
  have h3 : Commute (LinearMap.adjoint (S - l • (1 : Module.End ℂ X)))
      (LinearMap.adjoint (LinearMap.adjoint (S - l • (1 : Module.End ℂ X)))) := by
    rw [LinearMap.adjoint_adjoint]
    exact (GlobalTheory.NormalFamily.commute_sub_smul hS l).symm
  have h4 := GlobalTheory.NormalFamily.adjoint_apply_eq_zero h3 h2
  rw [LinearMap.adjoint_adjoint] at h4
  simpa [sub_eq_zero] using h4

theorem range_adjoint_le_eigSum {X E J : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (Θ : X →ₗ[ℂ] E) (opC : I → Module.End ℂ X)
    (opW : J → Module.End ℂ E) (hc : PairComm opW) (ha : ∀ a, ∃ a', opW a' = LinearMap.adjoint (opW a))
    (Q : (I → ℂ) → Prop) (hup : ∀ (x : J → ℂ) (w : E), (∀ a, opW a w = x a • w) →
      ∃ y, Q y ∧ ∀ b, opC b (LinearMap.adjoint Θ w) = y b • LinearMap.adjoint Θ w) :
    LinearMap.range (LinearMap.adjoint Θ) ≤ eigSum opC Q := by
  obtain ⟨he, htop, -⟩ := GlobalTheory.normalFamily_orthogonal_decomposition opW hc ha
  rw [LinearMap.range_eq_map, ← htop, Submodule.map_iSup]
  refine iSup_le fun x => ?_
  rintro _ ⟨w, hw, rfl⟩
  rw [he] at hw
  obtain ⟨y, hy, h⟩ := hup x w fun a => Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hw a)
  exact eigAt_le_eigSum hy (mem_eigAt_of_forall_apply h)

theorem span_eq_top_of_model {Y : Type} [AddCommGroup Y] [Module ℂ Y] (e : W →ₗ[ℂ] Y) (j : V →ₛₗ[σ] W) (ext : V →ₛₗ[σ] Y)
    (hi : Function.Injective e) (he : ∀ x, e (j x) = ext x) (h : Submodule.span ℂ (Set.range ext) = LinearMap.range e) :
    Submodule.span ℂ (Set.range j) = ⊤ := by
  apply Submodule.map_injective_of_injective hi
  rw [Submodule.map_top, ← h, Submodule.map_span, ← Set.range_comp]
  exact congrArg (fun f => Submodule.span ℂ (Set.range f)) (funext he)

def cutOp {M Pl : Type} [Zero M] (n : ℕ) (f : Pl → ℕ → M) (a : Pl × ℕ) : M := if a.2 ≤ n then f a.1 a.2 else 0

theorem cutOp_le {M Pl : Type} [Zero M] {n : ℕ} (f : Pl → ℕ → M) (P : Pl) {k : ℕ} (hk : k ≤ n) : cutOp n f (P, k) = f P k :=
  if_pos hk

theorem pairComm_cutOp {Pl : Type} (n : ℕ) (f : Pl → ℕ → Module.End ℂ W) (h : ∀ P k P' k', Commute (f P k) (f P' k')) :
    PairComm (cutOp n f) := by
  intro a b
  unfold cutOp
  split_ifs
  · exact h _ _ _ _
  · exact Commute.zero_right _
  · exact Commute.zero_left _
  · exact Commute.zero_left _

theorem cutOp_eigen {Pl : Type} (n : ℕ) (f : Pl → ℕ → Module.End ℂ W) (y : Pl → ℕ → ℂ) (v : W)
    (h : ∀ P k, k ≤ n → f P k v = y P k • v) (b : Pl × ℕ) : cutOp n f b v = cutOp n y b • v := by
  unfold cutOp
  split_ifs with hk
  · exact h _ _ hk
  · rw [zero_smul, LinearMap.zero_apply]

theorem cutOp_intertwine {Pl : Type} (n : ℕ) (j : V →ₛₗ[σ] W) (op : Pl × ℕ → Module.End K V) (f : Pl → ℕ → Module.End ℂ W)
    (h : ∀ P k, k ≤ n → ∀ x, j (op (P, k) x) = f P k (j x)) (h0 : ∀ P k, n < k → op (P, k) = 0) (a : Pl × ℕ) (x : V) :
    j (op a x) = cutOp n f a (j x) := by
  unfold cutOp
  split_ifs with hk
  · exact h _ _ hk x
  · rw [h0 a.1 a.2 (not_le.1 hk), LinearMap.zero_apply, LinearMap.zero_apply, map_zero]

theorem heckePolyOf_cutOp {Pl : Type} (n q : ℕ) (f : Pl → ℕ → ℂ) (P : Pl) :
    heckePolyOf n q (fun k => cutOp n f (P, k)) = heckePolyOf n q (f P) :=
  Finset.sum_congr rfl fun k hk => by
    simp only [cutOp_le f P (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))]

theorem eigSum_le_span_ZH {K G Pl0 : Type} [Field K] [NumberField K] [StarRing K] [Group G] [Fintype G] {σ : K →+* ℂ}
    [FiniteDimensional ℂ W] (B : BlockDat K G Pl0) {s : ℕ} (hOk : B.Ok s) (j : B.S.Forms →ₛₗ[σ] W)
    (hsp : Submodule.span ℂ (Set.range j) = ⊤) (opC : B.Pl × ℕ → Module.End ℂ W) (hj : ∀ a x, j (B.op a x) = opC a (j x))
    (hc : PairComm opC) {n : ℕ} (hn : n = B.n) :
    eigSum opC (fun x => ∀ P, (B.blockProd P).map σ ∣ heckePolyOf n (B.q P) fun k => x (P, k)) ≤
      Submodule.span ℂ (j '' (B.ZH : Set B.S.Forms)) := by
  have : FiniteDimensional K B.S.Forms := Module.Finite.of_basis B.S.basis
  refine (eigSum_le_span j hj hsp hOk.comm hOk.split hc _).trans (Submodule.span_mono (Set.image_mono ?_))
  refine eigSum_mono fun x hx P => ?_
  have h1 := hx P
  rw [← map_heckePolyOf σ _ _ fun k => x (P, k), Polynomial.map_dvd_map', hn] at h1
  exact h1

end Abstract

variable {D : D7}

theorem hk_splitC (V : HSp D) (P : Pl D.host.E) (n : ℕ) (z : ℕ → ℂ) :
    GlobalTheory.Hk3.hk V P (GlobalTheory.Hk3.splitC n z) =
      ∑ j ∈ Finset.range (n + 1), z j • GlobalTheory.Hk3.hk V P (Finsupp.single (splitLab n j) 1) := by
  unfold GlobalTheory.Hk3.hk GlobalTheory.Hk3.splitC
  rw [← Finsupp.sum_finsetSum_index (by simp) (by intros; rw [add_smul])]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp), one_smul]

theorem postOn_sum {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (s : Finset ℕ) (z : ℕ → ℂ)
    (L : ℕ → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (U : MMap M) :
    postOn M (∑ j ∈ s, z j • L j) U = ∑ j ∈ s, z j • postOn M (L j) U := by
  ext v x
  simp [postOn, LinearMap.sum_apply]

theorem exists_isSF {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) : ∃ SF, IsSF R SF := by
  classical
  refine ⟨R.Pg.image fun PP => PP.under (𝓞 D.host.F), fun v => ?_⟩
  rw [Finset.mem_image]
  refine exists_congr fun PP => and_congr_right fun _ => ?_
  rw [HeightOneSpectrum.ext_iff]
  rfl

section At

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem span_jV (hV : R.models_HV) (hj : R.models_jV) (i : Fin D.R.m) (t : T) :
    Submodule.span ℂ (Set.range (R.jV i t)) = ⊤ := by
  have h0 : (R.B.L i t).pres.ExtBij := (GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ (R.B.L i t).pres).2.1
  have h2 := h0.2
  have hi := (hV i t).1
  have hr := (hV i t).2.1
  have he : ∀ x, (R.HV i t).e (R.jV i t x) = (R.B.L i t).pres.extL x := hj i t
  exact span_eq_top_of_model (V := (A.MtCSD i t).Forms) (R.HV i t).e (R.jV i t) (R.B.L i t).pres.extL hi he (h2.trans hr.symm)

theorem eigSum_le (i : Fin D.R.m) (t : T) {s : ℕ} (hOk : (A.fam.L i t).Ok s) (hsp : Submodule.span ℂ (Set.range (R.jV i t)) = ⊤)
    (opC : A.ok t × ℕ → Module.End ℂ (R.HV i t).H) (hj : ∀ a x, R.jV i t (A.heckeL i t a x) = opC a (R.jV i t x))
    (hc : Formalism.L2.Col.PairComm opC) :
    Formalism.L2.Col.eigSum opC (fun x => ∀ P : A.ok t, ((A.fam.L i t).blockProd P).map D.what₂.embLL ∣
      Formalism.L2.Col.heckePolyOf (Vc D i).rank (A.q P) fun k => x (P, k)) ≤
      Submodule.span ℂ (R.jV i t '' ((A.fam.L i t).ZH : Set (A.fam.L i t).S.Forms)) := by
  have hrk : (Vc D i).rank = A.r + A.t := R.B.rankL i
  exact eigSum_le_span_ZH (A.fam.L i t) hOk (R.jV i t) hsp opC hj hc hrk

theorem ops_splitC (i : Fin D.R.m) (hi : Function.Injective (R.HW i (sg0 D A)).e)
    {h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HW i (sg0 D A)).H} (hW : GlobalTheory.Hk3.IsOpsW R i h) {P : Pl D.host.E}
    (hP : Good R A.μ0 P) (n : ℕ) (z a : ℕ → ℂ) (w : (R.HW i (sg0 D A)).H)
    (hw : ∀ j, h P (Finsupp.single (splitLab n j) 1) w = a j • w) :
    h P (GlobalTheory.Hk3.splitC n z) w = (∑ j ∈ Finset.range (n + 1), z j * a j) • w := by
  apply hi
  rw [hW _ hP, hk_splitC, postOn_sum, Finset.sum_smul, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hW _ hP, hw, mul_smul, map_smul, map_smul, map_smul]

theorem thG_ops (i : Fin D.R.m) (t : T) (hi : Function.Injective (R.HW i (sg0 D A)).e)
    {h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HW i (sg0 D A)).H} (hW : GlobalTheory.Hk3.IsOpsW R i h)
    {hV : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV i t).H} (hVo : GlobalTheory.Hk3.IsOpsV R i t hV) {P : Pl D.host.E}
    (hP0 : Good R A.μ0 P) (hP : Good R t P) {cV cW : List ℤ →₀ ℂ} (hm : GlobalTheory.Hk3.MatchW R i t P cV cW) (u : (R.HV i t).H) :
    R.thG i t (hV P cV u) = h P cW (R.thG i t u) :=
  hi ((hm u _ (hVo P hP cV u)).trans (hW P hP0 cW _).symm)

end At

theorem normal_of_normalFam {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    {ok : Pl D.host.E → Prop} {h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ H} (hN : GlobalTheory.Hk3.NormalFam ok h)
    {P : Pl D.host.E} (hP : ok P) (c : List ℤ →₀ ℂ) : Commute (h P c) (LinearMap.adjoint (h P c)) := by
  rw [hN.2 P hP]
  exact hN.1 _ _ hP hP _ _

set_option maxHeartbeats 800000 in

theorem range_adjoint_le : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A.fam.Ok s → Core R F → SchurAll R → ∀ i t, LinearMap.range (LinearMap.adjoint (R.thG i t)) ≤ Submodule.span ℂ (R.jV i t '' ((A.fam.L i t).ZH : Set (A.fam.L i t).S.Forms)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s _ hOk hC hS i t
  refine (exists_isSF R).elim fun SF hSF => ?_
  refine (GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R F hC hS hOk.irr SF hSF i).elim fun h hh => ?_
  have hW := hh.1
  have hN := hh.2.1
  clear hh
  refine ((GlobalTheory.T.realization_family_normal_operators R F hC.lev hC.fam hC.models).2 i t).elim fun hV hh => ?_
  have hVo := hh.1
  have hNV := hh.2
  have hsplit := (GlobalTheory.SplitHeckeLabel.split_ops R F hC.lev hC.fam hC.models).2 i t hV hVo
  have hpoly := GlobalTheory.T.thetaLift_transfer_heckePoly_splitPrime R F hC hS i t
  choose z hz hpol using hpoly
  have hgood := (GlobalTheory.GoodPrimes.good_primes R F hC.lev).2.1
  have hpl := (GlobalTheory.GoodPrimes.good_primes R F hC.lev).2.2.2
  have hG : ∀ P : A.ok t, Good R t (R.pl P) := fun P => (hpl hC.fam t P P.2).1
  have hG0 : ∀ P : A.ok t, Good R A.μ0 (R.pl P) := fun P => (hgood t _ (hG P)).2.2
  have hiW := (hC.models.HW i (sg0 D A)).1
  refine le_trans ?_ (eigSum_le R i t (hOk.lifts i t) (span_jV R hC.models.HV hC.models.jV i t)
    (cutOp (Vc D i).rank fun (P : A.ok t) k => hV (R.pl P) (Finsupp.single (splitLab (Vc D i).rank k) 1)) ?_
    (pairComm_cutOp _ _ fun P k P' k' => hNV.1 _ _ (hG P) (hG P') _ _))
  · refine range_adjoint_le_eigSum (J := {P // Good R A.μ0 P} × (List ℤ →₀ ℂ)) (R.thG i t) _ (fun a => h a.1.1 a.2)
      (fun a b => hN.1 _ _ a.1.2 b.1.2 _ _)
      (fun a => ⟨(a.1, GlobalTheory.Hk3.dualC (Finsupp.mapRange star (star_zero ℂ) a.2)), (hN.2 _ a.1.2 a.2).symm⟩) _ fun x w hw => ?_
    have hex : ∃ a : A.ok t → ℕ → ℂ, ∀ (P : A.ok t) j,
        h (R.pl P) (Finsupp.single (splitLab (Wc D i).rank j) 1) w = a P j • w :=
      ⟨fun P j => x (⟨_, hG0 P⟩, Finsupp.single (splitLab (Wc D i).rank j) 1), fun P j => hw (⟨_, hG0 P⟩, _)⟩
    refine hex.elim fun a ha => ?_
    refine ⟨cutOp (Vc D i).rank fun P k => ∑ j ∈ Finset.range ((Wc D i).rank + 1), z P k j * a P j, fun P => ?_, ?_⟩
    · have e1 := heckePolyOf_cutOp (Vc D i).rank (A.q P)
        (fun (P : A.ok t) k => ∑ j ∈ Finset.range ((Wc D i).rank + 1), z P k j * a P j) P
      exact Dvd.intro_left _ (e1.trans (hpol P (a P))).symm
    · exact cutOp_eigen _ _ _ _ fun P k hk => adjoint_eigen (R.thG i t) (thG_ops R i t hiW hW hVo (hG0 P) (hG P) (hz P k hk))
        (normal_of_normalFam hNV (hG P) _) (normal_of_normalFam hN (hG0 P) _)
        (ops_splitC R i hiW hW (hG0 P) _ (z P k) (a P) w (ha P))
  · exact cutOp_intertwine (V := (A.MtCSD i t).Forms) _ (R.jV i t) (A.heckeL i t) _ hsplit fun P => (hC.fam.degL i t P).2

end GlobalTheory.LiftAdjointBlock

end
