import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSStageUnconditional
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonnegShaOK

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.MemN GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df

namespace GlobalTheory.Mem.DfGen

attribute [local instance] GlobalTheory.Mem.Col2.starE

def RamSp {B : Base} (C : Cols B) (u : B.Word) : Type := (C.mem u).A.Mram

instance {B : Base} (C : Cols B) (u : B.Word) : AddCommGroup (RamSp C u) :=
  inferInstanceAs (AddCommGroup (C.mem u).A.Mram)
instance {B : Base} (C : Cols B) (u : B.Word) : Module ℂ (RamSp C u) :=
  inferInstanceAs (Module ℂ (C.mem u).A.Mram)
instance {B : Base} (C : Cols B) (u : B.Word) : FiniteDimensional ℂ (RamSp C u) :=
  haveI := (C.mem u).A.Mu0_fd
  Submodule.finiteDimensional_of_le (S₁ := (C.mem u).A.Mram) (S₂ := (C.mem u).A.Mu0) inf_le_left

def ramEq {B : Base} (C : Cols B) (u : B.Word) : RamSp C u ≃ₗ[ℂ] (C.mem u).A.Mram := LinearEquiv.refl ℂ _

@[reducible] def core {B : Base} (C : Cols B) (h : SpectralModel.ColsPos C) (u : B.Word) :
    InnerProductSpace.Core ℂ (RamSp C u) where
  inner x y := (C.fm u).ipC 0 (ramEq C u x).1 (ramEq C u y).1
  conj_inner_symm x y := (h u).1 _ (ramEq C u x).2.1 _ (ramEq C u y).2.1
  re_inner_nonneg x := by
    by_cases hx : (ramEq C u x).1 = 0
    · simp [hx, MemberForms.ipC]
    · exact ((h u).2 _ (ramEq C u x).2.1 hx).le
  add_left x y z := by simp [MemberForms.ipC, mul_add, Finset.sum_add_distrib]
  smul_left x y r := by
    simp only [MemberForms.ipC, map_smul, Submodule.coe_smul, Pi.smul_apply, LinearMap.map_smulₛₗ,
      LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  definite x hx := by
    by_contra h0
    have h1 : (ramEq C u x).1 ≠ 0 := fun h1 => h0 ((ramEq C u).injective (Subtype.ext (by simpa using h1)))
    have := (h u).2 _ (ramEq C u x).2.1 h1
    rw [show (C.fm u).ipC 0 (ramEq C u x).1 (ramEq C u x).1 = 0 from hx] at this
    simp at this

def stdCongr {a b : ℕ} (h : a = b) : EuclideanSpace ℂ (Fin a) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin b) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (finCongr h)

def stdLat (O : Type) [CommRing O] (φ : O →+* ℂ) (a : ℕ) : Rows.OLat O φ (EuclideanSpace ℂ (Fin a)) where
  gen := by classical exact Finset.univ.image (EuclideanSpace.basisFun (Fin a) ℂ).toBasis
  span_top := by
    classical
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact (EuclideanSpace.basisFun (Fin a) ℂ).toBasis.span_eq

theorem subsingleton_std {k : ℕ} (h : k = 0) : Subsingleton (EuclideanSpace ℂ (Fin k)) := by
  subst h
  exact ⟨fun x y => by ext i; exact i.elim0⟩

def sigParB (B : Base) (τ : Tau B.R) (i : ℕ) : ℚ :=
  if h : i < B.R.k - 1 then (B.hc τ).v ⟨i, h⟩
  else if hb : i - (B.R.k - 1) < B.R.m then -(B.hc τ).b ⟨i - (B.R.k - 1), hb⟩ else 0

def eQB (B : Base) (j : ℕ) (τ : Tau B.R) : ℚ :=
  if h : 1 ≤ j ∧ j ≤ B.R.m then (B.hc τ).e ⟨j - 1, by omega⟩ else 0

def aPlusB (B : Base) (j : ℕ) (τ : Tau B.R) (i : ℕ) : ℚ :=
  sigParB B τ i + eQB B j τ - ((B.R.nV : ℚ) - 1 - 2 * (i : ℚ)) / 2 -
    (((B.R.k : ℚ) + j - 1) - ((B.R.m : ℚ) - j)) / 2

def aMinusB (B : Base) (j : ℕ) (τ : Tau B.R) (c : ℕ) : ℚ :=
  (if h : j + c < B.R.m then (B.hc τ).b ⟨j + c, h⟩ else 0) - eQB B j τ - ((B.R.t : ℚ) + 1 + 2 * (c : ℚ)) / 2

theorem eQB_int (B : Base) (j : ℕ) (τ : Tau B.R) : ∃ z : ℤ, eQB B j τ = z := by
  unfold eQB
  split_ifs
  · exact (B.hc τ).e_int _
  · exact ⟨0, by simp⟩

theorem sigParB_int (B : Base) (τ : Tau B.R) (i : ℕ) : ∃ z : ℤ, sigParB B τ i = z := by
  unfold sigParB
  split_ifs
  · exact (B.hc τ).v_int _
  · obtain ⟨z, hz⟩ := (B.hc τ).b_int ⟨i - (B.R.k - 1), by assumption⟩
    exact ⟨-z, by rw [hz]; simp⟩
  · exact ⟨0, by simp⟩

theorem aPlusB_int (B : Base) (j : ℕ) (τ : Tau B.R) (i : ℕ) : ∃ z : ℤ, aPlusB B j τ i = z := by
  obtain ⟨a, ha⟩ := sigParB_int B τ i
  obtain ⟨b, hb⟩ := eQB_int B j τ
  obtain ⟨s, hs⟩ := B.R.t_odd
  refine ⟨a + b - ((B.R.k : ℤ) + j - 1 - 1 - i) - (s + 1), ?_⟩
  unfold aPlusB
  rw [DV.nV_cast, ha, hb, hs]
  push_cast
  ring

theorem aMinusB_int (B : Base) (j : ℕ) (τ : Tau B.R) (c : ℕ) : ∃ z : ℤ, aMinusB B j τ c = z := by
  obtain ⟨b, hb⟩ := eQB_int B j τ
  obtain ⟨s, hs⟩ := B.R.t_odd
  have h1 : ∃ a : ℤ, (if h : j + c < B.R.m then (B.hc τ).b ⟨j + c, h⟩ else 0) = (a : ℚ) := by
    split_ifs
    · exact (B.hc τ).b_int _
    · exact ⟨0, by simp⟩
  obtain ⟨a, ha⟩ := h1
  refine ⟨a - b - (s + 1 + c), ?_⟩
  unfold aMinusB
  rw [ha, hb, hs]
  push_cast
  ring

def kaBigB (B : Base) (j : ℕ) (τ : Tau B.R) (i : Fin (B.R.sigW j).1) : ℤ := (aPlusB_int B j τ i).choose

def kaSmallB (B : Base) (j : ℕ) (τ : Tau B.R) (c : Fin (B.R.sigW j).2) : ℤ := -(aMinusB_int B j τ c).choose

def rowsStd (B : Base) (C : Cols B) (hC : SpectralModel.ColsPos C) (n : C.Tup → ℕ)
    (e0 : ∀ u, (C.mem u).P.Mt ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (n C.mu0)))
    (eT : ∀ u a, (C.PTw u a).Mt ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (n a)))
    (L : ∀ a, Rows.OLat B.O (B.embLL.comp B.OtoLL) (EuclideanSpace ℂ (Fin (n a))))
    (mt : B.places.Pl → C.Tup) (hmt : ∀ w, mt (B.places.conj w) = mt w) : RowsRest B C :=
  letI nN : ∀ u, NormedAddCommGroup (RamSp C u) := fun u => (core C hC u).toNormedAddCommGroup
  letI nI : ∀ u, InnerProductSpace ℂ (RamSp C u) := fun u => InnerProductSpace.ofCore (core C hC u).toCore
  { muAt := fun _ => C.mu0
    muAt_conj := fun _ => rfl
    muTw := mt
    muTw_conj := hmt
    muAt_or := fun _ => Or.inl rfl
    EE := EuclideanSpace ℂ (Fin 0)
    Drows := 0
    onb := EuclideanSpace.basisFun (Fin 0) ℂ
    Dall := 0
    delp := 0
    delp_le_one := zero_le_one
    D_eq := by simp
    EE0 := EuclideanSpace ℂ (Fin 0)
    D0 := 0
    onb0 := EuclideanSpace.basisFun (Fin 0) ℂ
    FT := Empty
    ft := fun i => i.elim0
    ft0 := fun i => i.elim0
    Amb := fun a => EuclideanSpace ℂ (Fin (n a))
    Mult := fun a j => EuclideanSpace ℂ (Fin (if j = B.R.m then n a else 0))
    multZero := fun _ => stdCongr (if_neg (by have := B.R.two_le_m; omega))
    multTop := fun _ => stdCongr (if_pos rfl)
    io := fun _ _ => 0
    Mtilde := L
    eOp := fun _ => LinearMap.id
    eOp_idem := fun _ => LinearMap.id_comp _
    eOp_sa := fun _ _ _ => rfl
    Mu := RamSp C
    instMu := nN
    instMui := nI
    perCol := fun u a φ F =>
      haveI := Classical.dec (a = C.mu0)
      if h : a = C.mu0 then (C.mem u).P.PtilCol (ramEq C u φ).1 ((e0 u).symm (h ▸ F))
      else (C.PTw u a).PtilCol (C.e0Tw u a (ramEq C u φ).1) ((eT u a).symm F)
    Bu := fun _ _ _ => 0
    ze := fun _ _ => 1
    rowsRest_wordColumnUnit_baseTuple := fun _ => rfl
    Mj := fun _ => EuclideanSpace ℂ (Fin 0)
    MjLat := fun _ => stdLat _ _ _
    kaBig := kaBigB B
    kaSmall := kaSmallB B
    Mt := fun _ _ => EuclideanSpace ℂ (Fin 0)
    MtLat := fun _ _ => stdLat _ _ _
    MtL := fun _ _ => PUnit
    jMt := fun _ _ => 0
    jMt_basis := fun _ _ b => by
      haveI : IsEmpty (Module.Free.ChooseBasisIndex B.LL PUnit) :=
        ⟨fun i => b.ne_zero i (Subsingleton.elim _ _)⟩
      exact ⟨linearIndependent_empty_type, Subsingleton.elim _ _⟩
    MtLat_sub := fun _ _ x _ => ⟨0, Subsingleton.elim _ _⟩
    eMt := fun _ _ => LinearMap.id
    eMt_idem := fun _ _ => LinearMap.id_comp _
    eMt_sa := fun _ _ _ _ => rfl
    eMt_LL := fun _ _ x => ⟨x, rfl⟩
    thetaP := fun _ _ => 0
    isot := fun _ _ => ⊤
    lamP := fun _ _ _ => 0
    Ij := fun _ _ _ => 0
    jw := fun _ _ _ => 0
    etaJ := fun _ _ => 0
    etaJ_nonneg := fun _ _ => le_rfl
    shaLen := GaloisStage.shaTrue B.host
    shaLen_nonneg := GaloisStage.shaTrue_nonneg B.host
    eMu := ramEq C
    eMt0 := e0
    perCol_base_eq_PtilCol := fun u φ F => dif_pos rfl
    Bu_linL := fun _ _ => ⟨fun _ _ => by simp, fun _ _ => by simp⟩
    Bu_linR := fun _ _ => ⟨fun _ _ => by simp, fun _ _ => by simp⟩
    eMtTw := eT
    perCol_tie := fun u a h φ F => dif_neg h
    eMu_isom := fun _ _ _ => rfl }

theorem standIn_rowsStd (B : Base) (C : Cols B) (hC : SpectralModel.ColsPos C) (n : C.Tup → ℕ)
    (e0 : ∀ u, (C.mem u).P.Mt ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (n C.mu0)))
    (eT : ∀ u a, (C.PTw u a).Mt ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (n a)))
    (L : ∀ a, Rows.OLat B.O (B.embLL.comp B.OtoLL) (EuclideanSpace ℂ (Fin (n a))))
    (mt : B.places.Pl → C.Tup) (hmt : ∀ w, mt (B.places.conj w) = mt w) :
    StandIn (rowsStd B C hC n e0 eT L mt hmt) where
  drows := rfl
  d0 := rfl
  dall := rfl
  delp := rfl
  ft := inferInstanceAs (IsEmpty Empty)
  mult := fun a j hj => subsingleton_std (if_neg hj)
  io := fun _ _ => rfl
  mj := fun _ => subsingleton_std rfl
  mt := fun _ _ => subsingleton_std rfl
  eMt := fun _ _ => rfl
  bu := fun _ _ _ => rfl
  ij := fun _ _ _ => ⟨rfl, rfl⟩
  eta := fun _ _ => rfl
  sha := shaOK_shaTrue B.toPre
  kap := fun V S N G j _ _ τ =>
    ⟨fun i => (aPlusB_int B j τ i).choose_spec.symm,
     fun c => by
       show ((-(aMinusB_int B j τ c).choose : ℤ) : ℚ) = -aMinusB B j τ c
       push_cast
       rw [← (aMinusB_int B j τ c).choose_spec]⟩

theorem exists_rowsRest_std : ∀ (B : Base) (C : Cols B) (n : C.Tup → ℕ) (e0 : ∀ u, (C.mem u).P.Mt ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (n C.mu0))) (eT : ∀ u a, (C.PTw u a).Mt ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (n a))) (L : ∀ a, Rows.OLat B.O (B.embLL.comp B.OtoLL) (EuclideanSpace ℂ (Fin (n a)))) (mt : B.places.Pl → C.Tup), (∀ w, mt (B.places.conj w) = mt w) → SpectralModel.ColsPos C → ∃ (W : RowsRest B C) (g : ∀ a, EuclideanSpace ℂ (Fin (n a)) ≃ₗᵢ[ℂ] W.Amb a), StandIn W ∧ (∀ w, W.muAt w = C.mu0) ∧ (∀ w, W.muTw w = mt w) ∧ (∀ u F, W.eMt0 u F = g C.mu0 (e0 u F)) ∧ (∀ u a F, W.eMtTw u a F = g a (eT u a F)) ∧ (∀ a y, g a y ∈ (W.Mtilde a).carrier ↔ y ∈ (L a).carrier) ∧ (∀ a y, g a y ∈ (W.Mtilde a).gen ↔ y ∈ (L a).gen) ∧ (∀ a, W.eOp a = LinearMap.id) ∧ ∀ u a, W.ze u a = 1 := by
  intro B C n e0 eT L mt hmt hC
  exact ⟨rowsStd B C hC n e0 eT L mt hmt, fun a => LinearIsometryEquiv.refl ℂ _,
    standIn_rowsStd B C hC n e0 eT L mt hmt, fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ => rfl, fun _ _ => rfl⟩

end GlobalTheory.Mem.DfGen

end
