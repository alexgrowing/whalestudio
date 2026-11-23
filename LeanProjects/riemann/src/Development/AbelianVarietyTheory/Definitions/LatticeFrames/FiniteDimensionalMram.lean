import Mathlib
import Formalism.LocalRingCardinality.DataAmbForm

noncomputable section

namespace GlobalTheory.Core.Rk

open NumberField Formalism.BasicNotions Module

theorem rank_map_field {K L : Type} [Field K] [Field L] (f : K →+* L) {m n : Type} [Fintype m] [Fintype n]
    (A : Matrix m n K) : (A.map f).rank = A.rank := by
  classical
  letI := f.toAlgebra
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K A.col
  haveI : Finite κ := Finite.of_injective a ha
  letI : Fintype κ := Fintype.ofFinite κ
  have hL : LinearIndependent L (fun i => algebraMap K L ∘ (A.col ∘ a) i) :=
    linearIndependent_algebraMap_comp_iff.2 hli
  have hs : Submodule.span L (Set.range (A.map f).col) =
      Submodule.span L (Set.range (fun i => algebraMap K L ∘ (A.col ∘ a) i)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have hj : A.col j ∈ Submodule.span K (Set.range (A.col ∘ a)) := hspan ▸ Submodule.subset_span ⟨j, rfl⟩
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hj
      refine (Submodule.mem_span_range_iff_exists_fun L).2 ⟨fun i => f (c i), ?_⟩
      funext r
      have := congrArg f (congrFun hc r)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul] at this ⊢
      exact this
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨a i, rfl⟩
  rw [hs, ← hspan, finrank_span_eq_card hL, finrank_span_eq_card hli]

theorem rank_toMatrix {K V W ι κ : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [Fintype ι] [DecidableEq ι] [Fintype κ] (b : Basis ι K V) (c : Basis κ K W) (φ : V →ₗ[K] W) :
    (LinearMap.toMatrix b c φ).rank = finrank K (LinearMap.range φ) := by
  rw [Matrix.rank_eq_finrank_range_toLin _ c b, Matrix.toLin_toMatrix]

section Member

variable {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc)

noncomputable def colTo (j : ℕ) : (C.cls 0 → C.Y 0 → ℂ) →ₗ[ℂ] (C.cls j → C.Y j → ℂ) :=
  Nat.rec (motive := fun j => (C.cls 0 → C.Y 0 → ℂ) →ₗ[ℂ] (C.cls j → C.Y j → ℂ)) LinearMap.id
    (fun i f => (C.Klin i).comp f) j

theorem colTo_succ (j : ℕ) : colTo C (j + 1) = (C.Klin j).comp (colTo C j) := rfl

theorem colTo_eq (j : ℕ) (φ : C.cls 0 → C.Y 0 → ℂ) : colTo C j φ = Formalism.ThetaLiftIndependence.chainOpM C.wt C.Kmap j φ := by
  induction j with
  | zero => rfl
  | succ j ih => show C.K j (colTo C j φ) = _; rw [ih]; rfl

variable (A : ColumnsAtT R C) (P : PeriodMap R C)

def PsiC : A.Mram →ₗ[ℂ] P.Wrow := P.lowerMap ∘ₗ P.evz ∘ₗ colTo C R.m ∘ₗ A.Mram.subtype

def PhiC : A.Mram →ₗ[ℂ] Module.Dual ℂ P.Mt := P.period ∘ₗ PsiC C A P

theorem PhiC_apply (φ : A.Mram) (F : P.Mt) : PhiC C A P φ F = P.PtilCol (φ : C.cls 0 → C.Y 0 → ℂ) F := by
  show P.period (P.lowerMap (P.evz (colTo C R.m _))) F = _
  rw [colTo_eq]; rfl

def rkC : ℕ := Module.finrank ℂ (LinearMap.range (PhiC C A P))

def RKC : Prop := A.du < 2 * rkC C A P

theorem finiteDimensional_Mram : FiniteDimensional ℂ A.Mram :=
  haveI := A.Mu0_fd
  Submodule.finiteDimensional_of_le (inf_le_left : A.Mram ≤ A.Mu0)

theorem rkC_add_ker : rkC C A P + finrank ℂ (LinearMap.ker (PhiC C A P)) = A.du :=
  haveI := finiteDimensional_Mram C A
  LinearMap.finrank_range_add_finrank_ker _

theorem rkC_le : rkC C A P ≤ A.du := by
  have := rkC_add_ker C A P
  omega

theorem rkc_iff_ker : RKC C A P ↔ 2 * finrank ℂ (LinearMap.ker (PhiC C A P)) < A.du := by
  have := rkC_add_ker C A P
  unfold RKC
  omega

example (h : PhiC C A P = 0) : ¬ RKC C A P := by
  unfold RKC rkC
  rw [h, LinearMap.range_zero, finrank_bot]
  omega

example (h : LinearMap.ker (PhiC C A P) = ⊥) (hd : 0 < A.du) : RKC C A P := by
  rw [rkc_iff_ker, h, finrank_bot]
  omega

end Member

def dualH {K : Type} [Field K] [NumberField K] [StarRing K] (A : HLat K) : HLat K where
  V := Module.Dual K A.V
  ι := A.ι
  b := A.dualB
  X := A.dualX
  L := A.dualL

theorem dualH_muMax {K : Type} [Field K] [NumberField K] [StarRing K] (A : HLat K) : (dualH A).muMax = A.muMaxDual := rfl

variable (D : D7) (Am : AmbForm D (RowSide.sharp D)) (u : D.what₂.Word)

def dU : ℕ := (D.mem u).A.du

def RK : Prop := RKC (D.mem u).C (D.mem u).A (D.mem u).P

abbrev Mt : HLat D.what₂.LL := Am.MtH D.what₂.mu0

abbrev MtDual : HLat D.what₂.LL := dualH (Mt D Am)

def IsPhi (Φ : (D.div.Nu u).V →ₗ[D.what₂.LL] (MtDual D Am).V) : Prop :=
  ∀ (x : (D.div.Nu u).V) (z : (Mt D Am).V),
    D.what₂.embLL ((show Module.Dual D.what₂.LL (Mt D Am).V from Φ x) z) =
      D.what₂.perCol u D.what₂.mu0 (D.jN u x) (Am.jAmb D.what₂.mu0 z)

def PhiRat : Prop := ∃ Φ, IsPhi D Am u Φ

open Classical in

def Phi : (D.div.Nu u).V →ₗ[D.what₂.LL] (MtDual D Am).V := if h : PhiRat D Am u then h.choose else 0

theorem isPhi_Phi (h : PhiRat D Am u) : IsPhi D Am u (Phi D Am u) := by
  unfold Phi; rw [dif_pos h]; exact h.choose_spec

theorem isPhi_unique {Φ Ψ} (h : IsPhi D Am u Φ) (h' : IsPhi D Am u Ψ) : Φ = Ψ := by
  ext x : 1
  apply LinearMap.ext
  intro z
  exact D.what₂.embLL.injective ((h x z).trans (h' x z).symm)

theorem IsPhi.eq_Phi {Φ} (h : IsPhi D Am u Φ) : Φ = Phi D Am u :=
  isPhi_unique D Am u h (isPhi_Phi D Am u ⟨Φ, h⟩)

def rkL : ℕ := Module.finrank D.what₂.LL (LinearMap.range (Phi D Am u))

def RKL : Prop := PhiRat D Am u ∧ Module.finrank D.what₂.LL (D.div.Nu u).V < 2 * rkL D Am u

def htPhi : ℝ := Formalism.HN.htMap (D.div.Nu u).b (D.div.Nu u).X (MtDual D Am).b (MtDual D Am).X (Phi D Am u)

def HtPhiLe (h : ℝ) : Prop := PhiRat D Am u ∧ (Phi D Am u ≠ 0 → htPhi D Am u ≤ h)

def PhiInt (N : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) : Prop :=
  PhiRat D Am u ∧ ∀ x ∈ N, Phi D Am u x ∈ (MtDual D Am).L

theorem phiInt_iff_exists (N : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) :
    PhiInt D Am u N ↔ ∃ Φ, IsPhi D Am u Φ ∧ ∀ x ∈ N, Φ x ∈ (MtDual D Am).L := by
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨_, isPhi_Phi D Am u h, h'⟩
  · rintro ⟨Φ, h, h'⟩
    refine ⟨⟨Φ, h⟩, ?_⟩
    rw [← IsPhi.eq_Phi D Am u h]
    exact h'

theorem phiInt_iff (N : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) :
    PhiInt D Am u N ↔ PhiRat D Am u ∧ ∀ x ∈ N, ∀ z ∈ (Mt D Am).L, ∃ a : 𝓞 D.what₂.LL,
      D.what₂.embLL (a : D.what₂.LL) = D.what₂.perCol u D.what₂.mu0 (D.jN u x) (Am.jAmb D.what₂.mu0 z) := by
  refine and_congr_right fun h => ?_
  refine forall₂_congr fun x _ => forall₂_congr fun z _ => exists_congr fun a => ?_
  rw [← isPhi_Phi D Am u h x z]
  exact (D.what₂.embLL.injective.eq_iff).symm

theorem htPhiLe_iff_exists (h : ℝ) : HtPhiLe D Am u h ↔ ∃ Φ, IsPhi D Am u Φ ∧
    (Φ ≠ 0 → Formalism.HN.htMap (D.div.Nu u).b (D.div.Nu u).X (MtDual D Am).b (MtDual D Am).X Φ ≤ h) := by
  constructor
  · rintro ⟨hr, h'⟩
    exact ⟨_, isPhi_Phi D Am u hr, h'⟩
  · rintro ⟨Φ, hΦ, h'⟩
    refine ⟨⟨Φ, hΦ⟩, ?_⟩
    unfold htPhi
    rw [← IsPhi.eq_Phi D Am u hΦ]
    exact h'

def basN : Basis (D.div.Nu u).ι ℂ (D.mem u).A.Mram :=
  (Basis.mk (D.jN_basis u).1 (D.jN_basis u).2.ge).map (D.eMu u)

def basM : Basis (Mt D Am).ι ℂ (D.mem u).P.Mt :=
  (Basis.mk (Am.jAmb_basis _ (Or.inl rfl)).1 (Am.jAmb_basis _ (Or.inl rfl)).2.ge).map (D.eMt u).symm

theorem finrank_Nu : finrank D.what₂.LL (D.div.Nu u).V = dU D u := by
  rw [finrank_eq_card_basis (D.div.Nu u).b]
  exact (finrank_eq_card_basis (basN D u)).symm

theorem toMatrix_PhiC {Φ} (h : IsPhi D Am u Φ) :
    LinearMap.toMatrix (basN D u) (basM D Am u).dualBasis (PhiC (D.mem u).C (D.mem u).A (D.mem u).P) =
      (LinearMap.toMatrix (D.div.Nu u).b (MtDual D Am).b Φ).map D.what₂.embLL := by
  ext i j
  show _ = D.what₂.embLL (LinearMap.toMatrix (D.div.Nu u).b (MtDual D Am).b Φ i j)
  rw [LinearMap.toMatrix_apply, Basis.dualBasis_repr, PhiC_apply]
  erw [LinearMap.toMatrix_apply]
  have e : (MtDual D Am).b.repr (Φ ((D.div.Nu u).b j)) i =
      (show Module.Dual D.what₂.LL (Mt D Am).V from Φ ((D.div.Nu u).b j)) ((Mt D Am).b i) :=
    Basis.dualBasis_repr (Mt D Am).b _ i
  rw [e, h]
  refine Eq.trans ?_ (D.perCol_base_eq_PtilCol u _ _).symm
  have e1 : basN D u j = D.eMu u (D.jN u ((D.div.Nu u).b j)) := by simp [basN]
  have e2 : basM D Am u i = (D.eMt u).symm (Am.jAmb D.what₂.mu0 ((Mt D Am).b i)) :=
    congrArg (D.eMt u).symm (Basis.mk_apply (Am.jAmb_basis _ (Or.inl rfl)).1 (Am.jAmb_basis _ (Or.inl rfl)).2.ge i)
  rw [e1, e2]

theorem rkL_eq (h : PhiRat D Am u) : rkL D Am u = rkC (D.mem u).C (D.mem u).A (D.mem u).P := by
  unfold rkL rkC
  rw [← rank_toMatrix (D.div.Nu u).b (MtDual D Am).b, ← rank_toMatrix (basN D u) (basM D Am u).dualBasis,
    toMatrix_PhiC D Am u (isPhi_Phi D Am u h)]
  exact (rank_map_field D.what₂.embLL _).symm

theorem rkl_iff : RKL D Am u ↔ PhiRat D Am u ∧ RK D u := by
  refine and_congr_right fun h => ?_
  unfold RK RKC
  rw [rkL_eq D Am u h, finrank_Nu]
  rfl

theorem RKL.phi_ne_zero (h : RKL D Am u) : Phi D Am u ≠ 0 := by
  intro h0
  have h1 := h.2
  unfold rkL at h1
  rw [h0, LinearMap.range_zero, finrank_bot] at h1
  omega

theorem RKL.htPhi_le (h : RKL D Am u) {t : ℝ} (ht : HtPhiLe D Am u t) : htPhi D Am u ≤ t :=
  ht.2 (RKL.phi_ne_zero D Am u h)

theorem PhiInt.mono {N N' : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V} (h : PhiInt D Am u N) (hle : N' ≤ N) :
    PhiInt D Am u N' := ⟨h.1, fun x hx => h.2 x (hle hx)⟩

example : PhiInt D Am u ⊥ ↔ PhiRat D Am u := by
  refine ⟨fun h => h.1, fun h => ⟨h, fun x hx => ?_⟩⟩
  rw [(Submodule.mem_bot _).1 hx, map_zero]
  exact Submodule.zero_mem _

end GlobalTheory.Core.Rk

end
