import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFrameProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPointFrameCharacter
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGAtAllPlacesMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqUniformizerAndUnitAtPrime
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorDecompositionEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnMemLatticeIffIdeal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitIdealCompletionAtPlaceEqIntegralAdelesAtPlac
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

noncomputable section

namespace GlobalTheory.LatticeMembershipValuation

open GlobalTheory.FinPl (SplitPt Frame)
open GlobalTheory.SeeSaw (idV FI)

theorem exists_matrix_of_isLattice {O K : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] {n : ℕ} (Λ : Submodule O (Fin n → K)) (hΛ : Λ.IsLattice K) :
    ∃ b : Matrix (Fin n) (Fin n) K, Function.Injective b.mulVec ∧
      ∀ x : Fin n → K, (∀ i, x i ∈ (1 : Submodule O K)) ↔ b *ᵥ x ∈ Λ := by
  haveI : Module.Free O Λ := Submodule.IsLattice.free K Λ
  haveI : Module.Finite O Λ := Module.Finite.iff_fg.2 hΛ.fg
  let B := Module.finBasisOfFinrankEq O Λ ((Submodule.IsLattice.finrank_of_pi K Λ).trans (Fintype.card_fin n))
  let B' := B.extendOfIsLattice K
  have hB' : ∀ j, B' j = (B j : Fin n → K) := fun j => Module.Basis.extendOfIsLattice_apply K B j
  let b : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => (B j : Fin n → K) i
  have hb : ∀ x, b *ᵥ x = ∑ j, x j • (B j : Fin n → K) := fun x => by
    funext i
    simp [b, mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hinj : Function.Injective b.mulVec := fun x y h => by
    apply B'.equivFun.symm.injective
    rw [B'.equivFun_symm_apply, B'.equivFun_symm_apply]
    simp only [hB']
    rw [← hb, ← hb, h]
  refine ⟨b, hinj, fun x => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [hb]
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 (h j)
    rw [← ho, algebraMap_smul]
    exact Λ.smul_mem o (B j).2
  · have e : b *ᵥ x = b *ᵥ fun j => algebraMap O K (B.repr ⟨_, h⟩ j) := by
      have := congrArg (fun y : Λ => (y : Fin n → K)) (B.sum_repr ⟨_, h⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      refine this.symm.trans (Eq.trans ?_ (hb _).symm)
      simp only [algebraMap_smul]
    intro i
    rw [hinj e]
    exact Submodule.mem_one.2 ⟨_, rfl⟩

variable {D : D7}

theorem mulVec_mem_latV {S S' : HSp D} {L : Lat S} {L' : Lat S'} (P : Matrix (Fin S'.rank) (Fin S.rank) D.host.E)
    (h : ∀ x ∈ L, P *ᵥ x ∈ L') {v : GlobalTheory.FinPl.Pl D} {Y : Fin S.rank → AE D} (hY : Y ∈ latV S L (· = v)) :
    P.map (incA D) *ᵥ Y ∈ latV S' L' (· = v) := by
  induction hY using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, hαv, a, ha, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at ha
    subst ha
    refine AddSubgroup.subset_closure ⟨α, hα, hαv, 1, rfl, P *ᵥ x, h x hx, ?_⟩
    funext i
    simp only [mulVec, dotProduct, map_apply, GlobalTheory.UnitaryEmbeddingColumns.incA_mul_tmul', one_mul, ← TensorProduct.tmul_sum]
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add Y Z _ _ hY hZ => rw [mulVec_add]; exact add_mem hY hZ
  | neg Y _ hY => rw [mulVec_neg]; exact neg_mem hY

theorem dot_mem_idV {S : HSp D} {L : Lat S} {𝔟 : FI D} (π : Fin S.rank → D.host.E)
    (h : ∀ x ∈ L, π ⬝ᵥ x ∈ 𝔟) {v : GlobalTheory.FinPl.Pl D} {Y : Fin S.rank → AE D} (hY : Y ∈ latV S L (· = v)) :
    (fun i => incA D (π i)) ⬝ᵥ Y ∈ idV 𝔟 v := by
  induction hY using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, hαv, a, ha, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at ha
    subst ha
    refine AddSubgroup.subset_closure ⟨α, hα, hαv, π ⬝ᵥ x, h x hx, ?_⟩
    simp only [dotProduct, GlobalTheory.UnitaryEmbeddingColumns.incA_mul_tmul', one_mul, ← TensorProduct.tmul_sum]
  | zero => rw [dotProduct_zero]; exact zero_mem _
  | add Y Z _ _ hY hZ => rw [dotProduct_add]; exact add_mem hY hZ
  | neg Y _ hY => rw [dotProduct_neg]; exact neg_mem hY

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)

theorem dot_sec {n : Type} [Fintype n] (π : n → D.host.E) (y : n → k) :
    (fun i => incA D (π i)) ⬝ᵥ (fun i => p.sec (y i)) = p.sec ((fun i => p.pr (incA D (π i))) ⬝ᵥ y) := by
  simp only [dotProduct, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm, GlobalTheory.FinPl.FrameLat.sec_mul_right, mul_comm]

theorem exists_leftInv {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (hε : ε ≠ 0) :
    ∃ R : Matrix (Fin A.rank ⊕ Fin c) (Fin B.rank) D.host.E, R * fromCols (frameMat B A d.ι) d.a = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' (fromCols (frameMat B A d.ι) d.a)) (by
    rw [LinearMap.ker_eq_bot']
    intro z hz
    rw [Matrix.toLin'_apply, fromCols_mulVec] at hz
    obtain ⟨h1, h2⟩ := GlobalTheory.FunObj.auxiliaryVectorDecomposition_eq_zero hε d _ _ hz
    funext s
    rcases s with i | r
    · exact congrFun h1 i
    · exact congrFun h2 r)
  refine ⟨LinearMap.toMatrix' g, Matrix.toLin'.injective ?_⟩
  rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', hg, Matrix.toLin'_one]

theorem sec_mem_lat_iff {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (hε : ε ≠ 0) (Λ : Lat A)
    (𝔟 : Fin c → FI D) (v : GlobalTheory.FinPl.Pl D) (z : Fin A.rank ⊕ Fin c → k) :
    (fun i => p.sec (((fromCols (frameMat B A d.ι) d.a).map (fun x => p.pr (incA D x)) *ᵥ z) i)) ∈
        latV B (d.lat Λ 𝔟) (· = v) ↔
      (fun i => p.sec (z (Sum.inl i))) ∈ latV A Λ (· = v) ∧ ∀ r, p.sec (z (Sum.inr r)) ∈ idV (𝔟 r) v := by
  constructor
  · intro h
    obtain ⟨R, hR⟩ := exists_leftInv d hε
    have hx : ∀ y u, R *ᵥ (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) = Sum.elim y u := fun y u => by
      rw [← fromCols_mulVec_sumElim, mulVec_mulVec, hR, one_mulVec]
    have hR' : R.map (fun x => p.pr (incA D x)) * (fromCols (frameMat B A d.ι) d.a).map (fun x => p.pr (incA D x)) = 1 := by
      have := congrArg (fun M => M.map (p.pr.comp (incA D))) hR
      simp only [Matrix.map_mul] at this
      rw [Matrix.map_one _ (map_zero _) (map_one _)] at this
      exact this
    have key : ∀ s, (fun i => incA D (R s i)) ⬝ᵥ
        (fun i => p.sec (((fromCols (frameMat B A d.ι) d.a).map (fun x => p.pr (incA D x)) *ᵥ z) i)) = p.sec (z s) := fun s => by
      rw [dot_sec]
      congr 1
      have := congrFun (congrArg (· *ᵥ z) hR') s
      simp only [← mulVec_mulVec, one_mulVec] at this
      exact this
    refine ⟨?_, fun r => ?_⟩
    · have h1 := mulVec_mem_latV (L' := Λ) (R.submatrix Sum.inl id) (by
        rintro _ ⟨y, hy, u, -, rfl⟩
        have e : R.submatrix Sum.inl id *ᵥ (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) = y :=
          funext fun i => congrFun (hx y u) (Sum.inl i)
        rw [e]
        exact hy) h
      have e : (fun i => p.sec (z (Sum.inl i))) = _ := funext fun i => (key (Sum.inl i)).symm
      rw [e]
      exact h1
    · rw [← key]
      refine dot_mem_idV _ ?_ h
      rintro _ ⟨y, hy, u, hu, rfl⟩
      have e : R (Sum.inr r) ⬝ᵥ (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) = u r := congrFun (hx y u) (Sum.inr r)
      rw [e]
      exact hu r
  · rintro ⟨h1, h2⟩
    have h3 := mulVec_mem_latV (L' := d.lat Λ 𝔟) (frameMat B A d.ι)
      (fun y hy => ⟨y, hy, 0, fun r => (𝔟 r).zero_mem, by rw [mulVec_zero, add_zero]⟩) h1
    have h4 := sum_mem (t := Finset.univ) fun r _ => GlobalTheory.UnitaryEmbeddingColumns.mem_of_mem_idV d Λ 𝔟 v r _ (h2 r)
    convert add_mem h3 h4 using 1
    funext i
    have e := dot_sec p (fromCols (frameMat B A d.ι) d.a i) z
    refine e.symm.trans ?_
    simp only [dotProduct, Fintype.sum_sum_type, fromCols_apply_inl, fromCols_apply_inr, Pi.add_apply, mulVec, map_apply,
      Finset.sum_apply]
    congr 1
    exact Finset.sum_congr rfl fun r _ => mul_comm _ _

theorem exists_matrix_lat {S : HSp D} {L : Lat S} (hL : IsSelfDualC S L) :
    ∃ b : Matrix (Fin S.rank) (Fin S.rank) k, Function.Injective b.mulVec ∧
      ∀ x : Fin S.rank → k, (∀ i, x i ∈ (1 : Submodule 𝒪[k] k)) ↔ (fun i => p.sec ((b *ᵥ x) i)) ∈ latV S L (· = p.v) := by
  obtain ⟨β, hβ⟩ := ((GlobalTheory.InhPt.exists_splitPt_frame_char D).2 k p).1 S (Fin S.rank) 1 1 (mul_one _) (mul_one _)
  obtain ⟨Λ, h1, h2, -⟩ := GlobalTheory.FinPl.FrameLat.exists_lat D k p S _ β L hL
  obtain ⟨b, hb, hx⟩ := exists_matrix_of_isLattice Λ h1
  refine ⟨b, hb, fun x => (hx x).trans ((h2 _).trans ?_)⟩
  rw [hβ, one_mulVec]

theorem exists_frame {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (hε : ε ≠ 0) {Λ : Lat A}
    (hΛ : IsSelfDualC A Λ) (𝔟 : Fin c → FI D) (g : Fin c → k) (hg0 : ∀ r, g r ≠ 0)
    (hg : ∀ r t, p.sec t ∈ idV (𝔟 r) p.v ↔ ∃ z : 𝒪[k], t = g r * z) :
    ∃ (β : Frame p B (Fin B.rank)) (j : Fin c → Fin B.rank),
      β.IsLat (d.lat Λ 𝔟) (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)) ∧ Function.Injective j ∧
      (∀ r i, β.b i (j r) = g r * p.pr (incA D (d.a i r))) ∧
      ∀ m, m ∉ Set.range j → ∀ r, (((d.a)ᴴ * B.gram).map (fun x => p.pr (incA D x)) * β.b) r m = 0 := by
  classical
  obtain ⟨bP, hPinj, hP⟩ := exists_matrix_lat p hΛ
  obtain ⟨R, hR⟩ := exists_leftInv d hε
  let σ : Fin A.rank ⊕ Fin c ≃ Fin B.rank := finSumFinEquiv.trans (finCongr d.rank)
  obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin B.rank) (Fin A.rank ⊕ Fin c) k,
    C = (fromCols (frameMat B A d.ι) d.a).map (fun x => p.pr (incA D x)) := ⟨_, rfl⟩
  have hR' : R.map (fun x => p.pr (incA D x)) * C = 1 := by
    have := congrArg (fun M => M.map (p.pr.comp (incA D))) hR
    simp only [Matrix.map_mul] at this
    rw [Matrix.map_one _ (map_zero _) (map_one _)] at this
    rw [hC]
    exact this
  obtain ⟨b, hb⟩ : ∃ b : Matrix (Fin B.rank) (Fin B.rank) k,
    b = (C * fromBlocks bP 0 0 (diagonal g)).submatrix id σ.symm := ⟨_, rfl⟩
  have hbv : ∀ x, b *ᵥ x = C *ᵥ Sum.elim (bP *ᵥ fun i => x (σ (Sum.inl i))) (fun r => g r * x (σ (Sum.inr r))) := fun x => by
    rw [hb, submatrix_mulVec_equiv, ← mulVec_mulVec, fromBlocks_mulVec]
    simp only [zero_mulVec, add_zero, zero_add, Equiv.symm_symm, Function.comp_id]
    congr 2
    funext r
    rw [mulVec_diagonal]
    rfl
  have hunit : IsUnit b := by
    rw [← mulVec_injective_iff_isUnit]
    intro x y hxy
    have h0 : b *ᵥ (x - y) = 0 := by rw [mulVec_sub, hxy, sub_self]
    have h1 := congrArg (R.map (fun x => p.pr (incA D x)) *ᵥ ·) h0
    simp only [hbv, mulVec_mulVec, hR', one_mulVec, mulVec_zero] at h1
    refine sub_eq_zero.1 (funext fun m => ?_)
    obtain ⟨s, rfl⟩ := σ.surjective m
    rcases s with i | r
    · have h2 : bP *ᵥ (fun i => (x - y) (σ (Sum.inl i))) = bP *ᵥ 0 := by
        rw [mulVec_zero]
        exact funext fun i => congrFun h1 (Sum.inl i)
      exact congrFun (hPinj h2) i
    · exact (mul_eq_zero.1 (congrFun h1 (Sum.inr r))).resolve_left (hg0 r)
  have hdet := (Matrix.isUnit_iff_isUnit_det b).1 hunit
  obtain ⟨β, hβ⟩ := ((GlobalTheory.InhPt.exists_splitPt_frame_char D).2 k p).1 B (Fin B.rank) b b⁻¹
    (Matrix.mul_nonsing_inv _ hdet) (Matrix.nonsing_inv_mul _ hdet)
  refine ⟨β, fun r => σ (Sum.inr r), fun x => ?_, σ.injective.comp Sum.inr_injective, fun r i => ?_, fun m hm r => ?_⟩
  · rw [hβ, hbv, hC, sec_mem_lat_iff p d hε]
    simp only [Sum.elim_inl, Sum.elim_inr, ← hP, hg, Submodule.mem_pi, Set.mem_univ, true_imp_iff]
    constructor
    · intro h
      refine ⟨fun i => h _, fun r => ?_⟩
      obtain ⟨o, ho⟩ := Submodule.mem_one.1 (h (σ (Sum.inr r)))
      exact ⟨o, by rw [← ho]; rfl⟩
    · rintro ⟨h1, h2⟩ m
      obtain ⟨s, rfl⟩ := σ.surjective m
      rcases s with i | r
      · exact h1 i
      · obtain ⟨o, ho⟩ := h2 r
        exact Submodule.mem_one.2 ⟨o, (mul_left_cancel₀ (hg0 r) ho).symm⟩
  · rw [hβ, hb, submatrix_apply, Equiv.symm_apply_apply, hC, fromCols_map, fromCols_mul_fromBlocks, fromCols_apply_inr,
      Matrix.mul_zero, zero_add, mul_diagonal, mul_comm]
    rfl
  · obtain ⟨s, rfl⟩ := σ.surjective m
    rcases s with l | r'
    · have h0 : (d.a)ᴴ * B.gram * frameMat B A d.ι = 0 := by
        have h1 := congrArg conjTranspose d.perp
        rw [cT_sig, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose,
          conjTranspose_zero] at h1
        rw [Matrix.mul_assoc, h1]
      have h2 : ((d.a)ᴴ * B.gram).map (fun x => p.pr (incA D x)) * (frameMat B A d.ι).map (fun x => p.pr (incA D x)) = 0 := by
        have := congrArg (fun M => M.map (p.pr.comp (incA D))) h0
        rw [Matrix.map_mul, Matrix.map_zero _ (map_zero _)] at this
        exact this
      have h3 : (((d.a)ᴴ * B.gram).map (fun x => p.pr (incA D x)) * β.b) r (σ (Sum.inl l)) =
          (((d.a)ᴴ * B.gram).map (fun x => p.pr (incA D x)) * ((frameMat B A d.ι).map (fun x => p.pr (incA D x)) * bP)) r l := by
        rw [Matrix.mul_apply, Matrix.mul_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hβ, hb, submatrix_apply, Equiv.symm_apply_apply, hC, fromCols_map, fromCols_mul_fromBlocks, fromCols_apply_inl,
          Matrix.mul_zero, add_zero]
        rfl
      rw [h3, ← Matrix.mul_assoc, h2, Matrix.zero_mul]
      rfl
    · exact absurd ⟨r', rfl⟩ hm

theorem pr_mem_of_valuation_le {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : Formalism.L2.NTheta.IsIdemAt p.e w) {a : D.host.E}
    (ha : w.valuation D.host.E a ≤ 1) : p.pr (incA D a) ∈ 𝒪[k] := by
  obtain ⟨n, s, h⟩ := w.exists_primeCompl_mul_eq_of_integer a ha
  obtain ⟨π, hπ⟩ := w.intValuation_exists_uniformizer
  have h1 : π ∈ w.asIdeal := by
    have := (w.intValuation_le_pow_iff_mem π 1).1 (by rw [hπ]; simp)
    rwa [pow_one] at this
  have h2 : π ∉ w.asIdeal ^ 2 := fun h => by
    have := (w.intValuation_le_pow_iff_mem π 2).2 h
    rw [hπ, WithZero.exp_le_exp] at this
    omega
  have hs := (GlobalTheory.FinPl.SplitPt.val_eq_unif_and_unit D k p w hw π s.1 h1 h2 s.2).2
  have hn : valuation k (p.pr (incA D (n : D.host.E))) ≤ 1 :=
    GlobalTheory.SplitCharCond.pr_int p (AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, n, rfl⟩)
  have h3 : p.pr (incA D a) * p.pr (incA D (s.1 : D.host.E)) = p.pr (incA D (n : D.host.E)) := by
    rw [← map_mul, ← map_mul]
    exact congrArg _ (congrArg _ h)
  rw [← h3, Valuation.map_mul, hs, mul_one] at hn
  exact hn

set_option maxHeartbeats 800000 in

theorem sec_mem_idV_iff {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : Formalism.L2.NTheta.IsIdemAt p.e w) {ϖ : 𝒪[k]}
    (hϖ : Irreducible ϖ) {I : FI D} (hI : I ≠ 0) {n : ℕ} (hn : FractionalIdeal.count D.host.E w I = n) (t : k) :
    p.sec t ∈ idV I p.v ↔ ∃ z : 𝒪[k], t = (ϖ : k) ^ n * z := by
  obtain ⟨π, hπ⟩ := w.intValuation_exists_uniformizer
  have h1 : π ∈ w.asIdeal := by
    have := (w.intValuation_le_pow_iff_mem π 1).1 (by rw [hπ]; simp)
    rwa [pow_one] at this
  have h2 : π ∉ w.asIdeal ^ 2 := fun h => by
    have := (w.intValuation_le_pow_iff_mem π 2).2 h
    rw [hπ, WithZero.exp_le_exp] at this
    omega
  have hone : (1 : 𝓞 D.host.E) ∉ w.asIdeal := (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top
  obtain ⟨q, hq⟩ := (GlobalTheory.FinPl.SplitPt.val_eq_unif_and_unit D k p w hw π 1 h1 h2 hone).1
  have hqϖ : valuation k ((q.1 : 𝒪[k]) : k) = valuation k (ϖ : k) :=
    le_antisymm (GlobalTheory.FinPl.SplitPt.val_le_unif ⟨ϖ, hϖ⟩ (GlobalTheory.FinPl.SplitPt.val_unif_lt_one q))
      (GlobalTheory.FinPl.SplitPt.val_le_unif q (GlobalTheory.FinPl.SplitPt.val_unif_lt_one ⟨ϖ, hϖ⟩))
  rw [hqϖ] at hq
  have hϖ0 : (ϖ : k) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hγ : 0 < valuation k (ϖ : k) ^ n := pow_pos (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hϖ0)) n
  have hπv : w.valuation D.host.E ((π : D.host.E) ^ n) = WithZero.exp (-(n : ℤ)) := by
    rw [map_pow, show w.valuation D.host.E (π : D.host.E) = WithZero.exp (-1 : ℤ) from
      (w.valuation_of_algebraMap π).trans hπ, ← WithZero.exp_nsmul]
    simp
  have hπ0 : (π : D.host.E) ^ n ≠ 0 := fun h => by
    rw [h, map_zero] at hπv
    exact WithZero.exp_ne_zero hπv.symm
  have hiff : ∀ s : k, (∃ z : 𝒪[k], s = (ϖ : k) ^ n * z) ↔ valuation k s ≤ valuation k (ϖ : k) ^ n := fun s => by
    constructor
    · rintro ⟨z, rfl⟩
      rw [Valuation.map_mul, Valuation.map_pow]
      exact (mul_le_mul_of_nonneg_left (show valuation k (z : k) ≤ 1 from z.2) zero_le').trans_eq (mul_one _)
    · intro h
      refine ⟨⟨s / (ϖ : k) ^ n, ?_⟩, by field_simp⟩
      show valuation k _ ≤ 1
      rw [map_div₀, Valuation.map_pow, div_le_one₀ hγ]
      exact h
  rw [hiff]
  constructor
  · have key : ∀ s ∈ idV I p.v, valuation k (p.pr s) ≤ valuation k (ϖ : k) ^ n := by
      intro s hs
      induction hs using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨α, hα, -, a, ha, rfl⟩ := hy
        have e : (pairA D.host.F 0 α ⊗ₜ[D.host.F] a : AE D) =
            incA D ((π : D.host.E) ^ n) * (incA D (a / (π : D.host.E) ^ n) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] 1)) := by
          rw [GlobalTheory.UnitaryEmbeddingColumns.incA_mul_tmul', GlobalTheory.UnitaryEmbeddingColumns.incA_mul_tmul', mul_one, mul_div_cancel₀ _ hπ0]
        have a1 : valuation k (p.pr (incA D (a / (π : D.host.E) ^ n))) ≤ 1 := pr_mem_of_valuation_le p hw (by
          rw [map_div₀, hπv, div_le_one₀ (zero_lt_iff.2 WithZero.exp_ne_zero), ← hn]
          exact (GlobalTheory.Idele.mem_iff_valuation_le hI a).1 ha w)
        have a2 : valuation k (p.pr (pairA D.host.F 0 α ⊗ₜ[D.host.F] 1)) ≤ 1 :=
          GlobalTheory.SplitCharCond.pr_int p (AddSubgroup.subset_closure ⟨α, hα, 1, rfl⟩)
        rw [e, map_mul p.pr, map_mul p.pr, Valuation.map_mul, Valuation.map_mul, map_pow, map_pow, Valuation.map_pow, hq]
        exact (mul_le_mul_of_nonneg_left (mul_le_one' a1 a2) zero_le').trans_eq (mul_one _)
      | zero => rw [map_zero, map_zero]; exact zero_le'
      | add a b _ _ ha hb => rw [map_add p.pr]; exact Valuation.map_add_le _ ha hb
      | neg a _ ha => rw [map_neg p.pr, Valuation.map_neg]; exact ha
    intro h
    have := key _ h
    rwa [p.pr_sec] at this
  · intro h
    obtain ⟨a, ha, hav⟩ := GlobalTheory.Idele.exists_mem_valuation_eq hI w
    rw [hn] at hav
    have ha0 : a ≠ 0 := fun h => by
      rw [h, map_zero] at hav
      exact WithZero.exp_ne_zero hav.symm
    have a1 : valuation k (p.pr (incA D ((π : D.host.E) ^ n / a))) ≤ 1 := pr_mem_of_valuation_le p hw (by
      rw [map_div₀, hπv, hav, div_self WithZero.exp_ne_zero])
    have a2 : t * p.pr (incA D a⁻¹) ∈ 𝒪[k] := by
      show valuation k _ ≤ 1
      rw [div_eq_mul_inv, map_mul, map_mul p.pr, Valuation.map_mul, map_pow, map_pow, Valuation.map_pow, hq] at a1
      rw [Valuation.map_mul]
      exact (mul_le_mul_of_nonneg_right h zero_le').trans a1
    have a3 : p.sec (t * p.pr (incA D a⁻¹)) ∈ idV (1 : FI D) p.v :=
      (GlobalTheory.SeeSaw.idV_one_eq_intAt D p.v _).2 (GlobalTheory.FinPl.FrameLat.sec_mem_intAt p _ a2)
    have key : ∀ y ∈ idV (1 : FI D) p.v, incA D a * y ∈ idV I p.v := by
      intro y hy
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨α, hα, h0, c, hc, rfl⟩ := hy
        obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hc
        refine AddSubgroup.subset_closure ⟨α, hα, h0, _, ?_, GlobalTheory.UnitaryEmbeddingColumns.incA_mul_tmul' _ _ _⟩
        have := (I : Submodule (𝓞 D.host.E) D.host.E).smul_mem o ha
        rw [Algebra.smul_def, mul_comm] at this
        exact this
      | zero => rw [mul_zero]; exact zero_mem _
      | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
      | neg a _ ha => rw [mul_neg]; exact neg_mem ha
    have a4 := key _ a3
    rwa [mul_comm, GlobalTheory.FinPl.FrameLat.sec_mul_right, mul_assoc, ← map_mul p.pr, ← map_mul (incA D), inv_mul_cancel₀ ha0, map_one (incA D), map_one p.pr,
      mul_one] at a4

variable {T : Type} {L : LevCh D T} {sc : Consts}

theorem count_stairIdeal_at_S0 (hq : OffQ D) {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ G.pl.S0)
    (c : ℕ) (r : Fin c) :
    stairId (G.pl.stA sc) (G.pl.stAbar sc) c r ≠ 0 ∧
      FractionalIdeal.count D.host.E (G.pl.w v) (stairId (G.pl.stA sc) (G.pl.stAbar sc) c r) =
        ((G.pl.depth sc v * (r.1 + 1) : ℕ) : ℤ) := by
  classical
  have h1 := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1
  have h2 := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L G.pl sc
  have h3 := GlobalTheory.FunObj.ne_zero_of_conj h2.1 h2.2
  have hW : G.pl.w v ∈ G.pl.W0 := by simpa [Places.W0] using ⟨v, hv, rfl⟩
  have hw : G.pl.w v ∈ locPl G μ₀ := by simp [locPl, hW]
  have hA := GlobalTheory.FunObj.count_AA_AAbar (G.pl.w v) (GlobalTheory.FunObj.Good.badInt_notMem hL hq (fun P hP => by
    have h := (hL.Q_ram μ₀ P).2 (Or.inl hP)
    rw [hL.xi_base] at h
    exact absurd (fun x _ => rfl) h) hw)
  have hmo : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact G.pl.modul_ne_bot sc
  have hmb : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    intro h
    have h4 := h2.1
    rw [Places.stA, h, _root_.inv_zero, mul_zero] at h4
    exact h4 rfl
  refine ⟨mul_ne_zero (pow_ne_zero _ h2.1) (inv_ne_zero (pow_ne_zero _ h3)), ?_⟩
  rw [GlobalTheory.FunObj.count_stairId h2.1 h3, Places.stA, Places.stAbar,
    FractionalIdeal.count_mul _ _ h1.1 (inv_ne_zero hmb), FractionalIdeal.count_mul _ _ (GlobalTheory.FunObj.ne_zero_of_conj h1.1 h1.2)
      (inv_ne_zero hmo), FractionalIdeal.count_inv, FractionalIdeal.count_inv, GlobalTheory.FunObj.count_modulBar G hw,
    GlobalTheory.FunObj.count_modul, hA.1, hA.2, cosExp, if_pos hW, G.pl.under_w hv]
  push_cast
  ring

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in

theorem exists_splitPoint_at_S0 (P : Places L) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ P.S0) :
    ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k)
      (p : SplitPt D k), p.v = v ∧ Formalism.L2.NTheta.IsIdemAt p.e (P.w v) := by
  obtain ⟨e, he⟩ := P.w_split v hv
  obtain ⟨v', ε, h1, h2⟩ := he.1.2.2
  obtain ⟨p, hp, -⟩ := GlobalTheory.FinPl.SplitPoint.exists_splitPt D v' e ε he.1 h1 h2
  have hp' : Formalism.L2.NTheta.IsIdemAt p.e (P.w v) := hp ▸ he
  exact ⟨_, _, _, _, _, p, (GlobalTheory.LocMod.PinInhab.v_eq_under p hp').trans (P.under_w hv), hp'⟩

theorem exists_stairFrame (hq : OffQ D) {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ G.pl.S0)
    (i : ℕ) (h : 1 ≤ i) (h' : i ≤ D.R.m) (hp : p.v = v) (he : Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v)) {ϖ : 𝒪[k]}
    (hϖ : Irreducible ϖ) :
    ∃ (β : Frame p (G.V (.grid i 0)) (Fin (G.V (.grid i 0)).rank)) (j : Fin (i - 1) → Fin (G.V (.grid i 0)).rank),
      β.IsLat (G.Λ (.grid i 0)) (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)) ∧ Function.Injective j ∧
      (∀ r l, β.b l (j r) = (ϖ : k) ^ (G.pl.depth sc v * (r.1 + 1)) * p.pr (incA D ((G.colDec i h h').a l r))) ∧
      ∀ m, m ∉ Set.range j → ∀ r,
        ((((G.colDec i h h').a)ᴴ * (G.V (.grid i 0)).gram).map (fun x => p.pr (incA D x)) * β.b) r m = 0 := by
  have hlat : G.Λ (.grid i 0) = (G.colDec i h h').lat (G.Λ (.core i)) (stairId (G.pl.stA sc) (G.pl.stAbar sc) (i - 1)) :=
    G.sp.colLat i h h'
  rw [hlat]
  exact exists_frame p (G.colDec i h h') (neg_ne_zero.2 one_ne_zero) (G.sp.P_is i h').sd _ _
    (fun r => pow_ne_zero _ fun h0 => hϖ.ne_zero (Subtype.ext h0)) fun r t =>
      sec_mem_idV_iff p he hϖ (count_stairIdeal_at_S0 hq hL G hv _ r).1 (count_stairIdeal_at_S0 hq hL G hv _ r).2 t

end GlobalTheory.LatticeMembershipValuation

end
