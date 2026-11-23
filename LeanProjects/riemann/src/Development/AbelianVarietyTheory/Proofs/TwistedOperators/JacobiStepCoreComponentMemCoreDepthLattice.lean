import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualOrthAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemLatticeOfRationalMemCompletionAllPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.CoreComp

variable {D : D7}

def finV {n : ℕ} (z : Fin n → D.host.E) : Fin n → AE D := fun i => pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i

theorem rat_entry {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) (i : Fin m) (j : Fin n) :
    (rat A : Mx D m n) i j = (1 : AF D.host.F) ⊗ₜ[D.host.F] A i j := rfl

theorem rat_mulVec_finV {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) (z : Fin n → D.host.E) :
    (rat A : Mx D m n) *ᵥ finV z = finV (A *ᵥ z) := by
  funext i
  simp only [finV, mulVec, dotProduct, TensorProduct.tmul_sum, rat_entry, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem finV_mem {S : HSp D} {L : Lat S} {z : Fin S.rank → D.host.E} (hz : z ∈ L) :
    finV z ∈ latV S L (fun _ => True) :=
  AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, fun v hv => absurd trivial hv, 1, rfl, z, hz,
    by funext i; simp [finV]⟩

theorem mem_of_finV (S : HSp D) (L : Lat S) (hL : Submodule.IsLattice D.host.E L) (z : Fin S.rank → D.host.E)
    (hz : finV z ∈ latV S L (fun _ => True)) : z ∈ L := GlobalTheory.T.mem_lattice_of_rational_mem_completion_all_places D S L hL z hz

theorem loc_iff {S : HSp D} {L : Lat S} (hL : Submodule.IsLattice D.host.E L) (y : Fin S.rank → AE D) :
    y ∈ latV S L (fun _ => True) ↔ (∀ i, y i ∈ idAt D (fun _ => True)) ∧
      ∀ v, ∀ e ∈ intAt D (· = v), e • y ∈ latV S L (· = v) := by
  have := ((GlobalTheory.FinPl.localComponents D (fun _ => True)).2 S).2.2.2 L y hL
  simpa using this

end GlobalTheory.CoreComp

namespace GlobalTheory.CoreComp

variable {D : D7}

theorem mulVec_mem_idAt {m n : ℕ} (M : Mx D m n) {y : Fin n → AE D} (hy : ∀ i, y i ∈ idAt D (fun _ => True)) (i : Fin m) :
    (M *ᵥ y) i ∈ idAt D (fun _ => True) := mulVec_idAt M hy i

theorem witt_core_inclusion_maps_split_lattices {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀}
    (hL : Submodule.IsLattice D.host.E L) (hL₀ : Submodule.IsLattice D.host.E L₀) (hM : ∀ v, MonoAt d L L₀ v)
    {z : Fin S₀.rank → D.host.E} (hz : z ∈ L₀) : d.i₀ *ᵥ z ∈ L := by
  apply mem_of_finV S L hL
  rw [← rat_mulVec_finV]
  have hz' := (loc_iff hL₀ _).1 (finV_mem hz)
  refine (loc_iff hL _).2 ⟨mulVec_mem_idAt _ hz'.1, fun v e he => ?_⟩
  have h1 := hz'.2 v e he
  rw [← Matrix.mulVec_smul]
  refine (hM v _).2 ⟨fun i => ?_, fun i => ?_, ?_⟩
  · have e0 : (d.pX *ᵥ ((rat d.i₀ : Mx D S.rank S₀.rank) *ᵥ e • finV z)) i = 0 := by
      rw [Matrix.mulVec_mulVec, show (rat d.i₀ : Mx D S.rank S₀.rank) = d.j0 from rfl, HypDec.pX_j0, Matrix.zero_mulVec]; rfl
    rw [e0]
    have : GlobalTheory.FinPl.colMul d.jX i 0 = 0 := by funext k; simp [GlobalTheory.FinPl.colMul]
    rw [this]; exact zero_mem _
  · have e0 : (d.pY *ᵥ ((rat d.i₀ : Mx D S.rank S₀.rank) *ᵥ e • finV z)) i = 0 := by
      rw [Matrix.mulVec_mulVec, show (rat d.i₀ : Mx D S.rank S₀.rank) = d.j0 from rfl, HypDec.pY_j0, Matrix.zero_mulVec]; rfl
    rw [e0]
    have : GlobalTheory.FinPl.colMul d.jY i 0 = 0 := by funext k; simp [GlobalTheory.FinPl.colMul]
    rw [this]; exact zero_mem _
  · rw [Matrix.mulVec_mulVec, show (rat d.i₀ : Mx D S.rank S₀.rank) = d.j0 from rfl, HypDec.p0_j0, Matrix.one_mulVec]
    exact h1

theorem witt_core_projection_maps_split_lattices {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀}
    (hL : Submodule.IsLattice D.host.E L) (hL₀ : Submodule.IsLattice D.host.E L₀) (hM : ∀ v, MonoAt d L L₀ v)
    {y : Fin S.rank → D.host.E} (hy : y ∈ L) : d.q0 *ᵥ y ∈ L₀ := by
  apply mem_of_finV S₀ L₀ hL₀
  rw [← rat_mulVec_finV]
  have hy' := (loc_iff hL _).1 (finV_mem hy)
  refine (loc_iff hL₀ _).2 ⟨mulVec_mem_idAt _ hy'.1, fun v e he => ?_⟩
  rw [← Matrix.mulVec_smul]
  exact ((hM v _).1 (hy'.2 v e he)).2.2

theorem qA_maps {S A B : HSp D} (o : OrthDec S A B) {L : Lat S} {LA : Lat A} {LB : Lat B}
    (hL : Submodule.IsLattice D.host.E L) (hLA : Submodule.IsLattice D.host.E LA) (hO : ∀ v, OrthAt o L LA LB v)
    {y : Fin S.rank → D.host.E} (hy : y ∈ L) : o.qA *ᵥ y ∈ LA := by
  apply mem_of_finV A LA hLA
  rw [← rat_mulVec_finV]
  have hy' := (loc_iff hL _).1 (finV_mem hy)
  refine (loc_iff hLA _).2 ⟨mulVec_mem_idAt _ hy'.1, fun v e he => ?_⟩
  rw [← Matrix.mulVec_smul]
  exact ((hO v _).1 (hy'.2 v e he)).1

theorem rat_mulVec_mem_latA {S T : HSp D} (m : Matrix (Fin T.rank) (Fin S.rank) D.host.E) {L : Lat S} {L' : Lat T}
    (h : ∀ x ∈ L, m *ᵥ x ∈ L') {P : GlobalTheory.FinPl.Pl D → Prop} {y : Fin S.rank → AE D} (hy : y ∈ latA S L P) :
    (rat m : Mx D T.rank S.rank) *ᵥ y ∈ latA T L' P := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, hα', a, ha, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨α, hα, hα', a, ha, m *ᵥ x, h x hx, ?_⟩
    funext i
    simp only [mulVec, dotProduct, Finset.mul_sum, TensorProduct.tmul_sum, rat_entry, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1; ring
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [mulVec_neg]; exact neg_mem hx

theorem latO_sandwich {S T S' T' : HSp D} {ΛS : Lat S} {ΛT : Lat T} {ΛS' : Lat S'} {ΛT' : Lat T'}
    (M : Matrix (Fin T'.rank) (Fin T.rank) D.host.E) (N : Matrix (Fin S.rank) (Fin S'.rank) D.host.E)
    (hS : IsSelfDualC S ΛS) (hS' : IsSelfDualC S' ΛS') (hT' : IsSelfDualC T' ΛT')
    (hN : ∀ y ∈ ΛS', N *ᵥ y ∈ ΛS) (hM : ∀ y ∈ ΛT, M *ᵥ y ∈ ΛT') {u : WO S T}
    (hu : u ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) :
    ((rat M : Mx D T'.rank T.rank) * u * (rat N : Mx D S.rank S'.rank) : WO S' T') ∈
      latO S' T' (ΛS' : Set _) (ΛT' : Set _) fun _ => True := by
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S' T' ΛS' ΛT' hS' hT']
  refine ⟨fun i j => ?_, fun y hy => ?_⟩
  · simp only [Matrix.mul_apply]
    exact sum_mem fun l _ => Ideal.mul_mem_right _ _
      (sum_mem fun k _ => Ideal.mul_mem_left _ _ (GlobalTheory.FinPl.LatMem.latO_mxAt hu k l))
  · show ((rat M : Mx D T'.rank T.rank) * u * (rat N : Mx D S.rank S'.rank)) *ᵥ y ∈ _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact rat_mulVec_mem_latA M hM
      (GlobalTheory.FinPl.LatMem.latO_maps hS hu (GlobalTheory.OrthSumLat.rat_mulVec_mem_latV N hN hy))

theorem hatMx_sandwich {S T S' T' : HSp D} {ΛS : Lat S} {ΛT : Lat T} {ΛS' : Lat S'} {ΛT' : Lat T'}
    (M : Matrix (Fin T'.rank) (Fin T.rank) D.host.E) (N : Matrix (Fin S.rank) (Fin S'.rank) D.host.E)
    (hN : ∀ y ∈ ΛS', N *ᵥ y ∈ ΛS) (hM : ∀ y ∈ ΛT, M *ᵥ y ∈ ΛT') (I : Ideal (𝓞 D.host.E))
    {z : Mx D T.rank S.rank} (hz : z ∈ hatMx (I • homLat ΛS ΛT)) :
    (rat M : Mx D T'.rank T.rank) * z * (rat N : Mx D S.rank S'.rank) ∈ hatMx (I • homLat ΛS' ΛT') := by
  have key : ∀ X ∈ I • homLat ΛS ΛT, M * X * N ∈ I • homLat ΛS' ΛT' := by
    intro X hX
    refine Submodule.smul_induction_on hX (fun r hr Y hY => ?_) (fun a b ha hb => ?_)
    · have e : M * (r • Y) * N = r • (M * Y * N) := by rw [Matrix.mul_smul, Matrix.smul_mul]
      rw [e]
      refine Submodule.smul_mem_smul hr ?_
      intro y hy
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact hM _ (hY _ (hN y hy))
    · rw [Matrix.mul_add, Matrix.add_mul]; exact add_mem ha hb
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, X, hX, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, hα, M * X * N, key X hX, ?_⟩
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul, TensorProduct.tmul_sum, rat_entry,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  | zero => rw [Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg, Matrix.neg_mul]; exact neg_mem hx

end GlobalTheory.CoreComp

namespace GlobalTheory.CoreComp

theorem core_mem_latCore : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m),
    ∀ u ∈ (pcFB W F σ h h').Γ₀, ((F.oB σ h').resT _ u).1 ∈ latCore G (2 * σ + 2) := by
  intro D hq T L μ0 hL sc G W M hM F hF σ h h' u hu
  have I := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hq T L μ0 hL sc G W M hM F hF
  have sd : ∀ X : Node, X.InRange D.R.m → (∀ j, X ≠ .grid 0 j) → IsSelfDualC (G.V X) (G.Λ X) :=
    fun X h1 h2 => (G.isV h1 h2).sd
  have sdG3 : IsSelfDualC (G.V (.grid (2 * σ + 2 + 1) 0)) (G.Λ (.grid (2 * σ + 2 + 1) 0)) :=
    sd _ ⟨by omega, Nat.zero_le _⟩ (fun j e => by cases e)
  have sdG2 : IsSelfDualC (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) :=
    sd _ ⟨h', Nat.zero_le _⟩ (fun j e => by cases e)
  have sdC3 : IsSelfDualC (G.V (.core (2 * σ + 2 + 1))) (G.Λ (.core (2 * σ + 2 + 1))) :=
    sd (.core (2 * σ + 2 + 1)) (show 2 * σ + 2 + 1 ≤ D.R.m by omega) (fun j e => by cases e)
  have sdC2 : IsSelfDualC (G.V (.core (2 * σ + 2))) (G.Λ (.core (2 * σ + 2))) :=
    sd (.core (2 * σ + 2)) (show 2 * σ + 2 ≤ D.R.m by omega) (fun j e => by cases e)
  have sd0 : IsSelfDualC (F.V₀ σ) (lat0 F σ h') := (I.2.1 σ h').1
  have hMJ : ∀ v, MonoAt (F.dJ (σ + 1) h) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (G.Λ (.core (2 * (σ + 1) + 1))) v :=
    fun v => ((I.2.1 (σ + 1) h).2.1 v).2
  have hMB : ∀ v, MonoAt (F.dB σ h') (G.Λ (.grid (2 * σ + 2) 0)) (lat0 F σ h') v := fun v => ((I.2.1 σ h').2.1 v).1
  have hOB := (I.2.1 σ h').2.2.2

  have hN : ∀ y ∈ G.Λ (.core (2 * σ + 2 + 1)), (F.dJ (σ + 1) h).i₀ *ᵥ y ∈ G.Λ (.grid (2 * σ + 2 + 1) 0) :=
    fun y hy => witt_core_inclusion_maps_split_lattices (F.dJ (σ + 1) h) sdG3.1 sdC3.1 hMJ hy
  have hMm : ∀ y ∈ G.Λ (.grid (2 * σ + 2) 0),
      ((F.oB σ h').qA * (F.dB σ h').q0) *ᵥ y ∈ G.Λ (.core (2 * σ + 2)) := fun y hy => by
    rw [← Matrix.mulVec_mulVec]
    exact qA_maps (F.oB σ h') sd0.1 sdC2.1 hOB (witt_core_projection_maps_split_lattices (F.dB σ h') sdG2.1 sd0.1 hMB hy)
  have hx := AddSubgroup.mem_comap.1 hu
  set x := ((F.dJ (σ + 1) h).ext0 _).comp ((F.dB σ h').inc0 _) u with hxdef
  have hc : ((F.oB σ h').resT _ u).1 =
      (rat ((F.oB σ h').qA * (F.dB σ h').q0) : Mx D _ _) * x * (rat (F.dJ (σ + 1) h).i₀ : Mx D _ _) := by
    rw [OrthDec.resT_apply, rat_mul, hxdef]
    change (F.oB σ h').pA * u = (F.oB σ h').pA * (F.dB σ h').p0 * ((F.dB σ h').j0 * u * (F.dJ (σ + 1) h).p0) *
      (F.dJ (σ + 1) h).j0
    have e1 : (F.dB σ h').p0 * (F.dB σ h').j0 = 1 := HypDec.p0_j0 _
    have e2 : (F.dJ (σ + 1) h).p0 * (F.dJ (σ + 1) h).j0 = 1 := HypDec.p0_j0 _
    calc (F.oB σ h').pA * u = (F.oB σ h').pA * (((F.dB σ h').p0 * (F.dB σ h').j0) * u *
          ((F.dJ (σ + 1) h).p0 * (F.dJ (σ + 1) h).j0)) := by rw [e1, e2, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [hc]
  refine ⟨?_, fun e he => ?_⟩
  · exact latO_sandwich _ _ (isSelfDualC_neg sdG3) (isSelfDualC_neg sdC3) sdC2 hN hMm hx.1
  · rw [← Matrix.smul_mul, ← Matrix.mul_smul]
    exact hatMx_sandwich _ _ hN hMm _ (hx.2 e he)

end GlobalTheory.CoreComp
