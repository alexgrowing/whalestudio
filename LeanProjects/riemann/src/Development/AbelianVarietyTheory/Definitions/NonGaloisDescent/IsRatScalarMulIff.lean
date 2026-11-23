import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspSubsetBaseForms

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField GlobalTheory.ExportSeries
open Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
open Formalism.L2.Host (embLL0)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Scale

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (Rl : RealDat3 D A3 Ks)

def IsScaleAt {j : Fin D.R.m} (B : Base (Vc D j) (Wc D j)) (u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ)
    (c0 : VsV D j D.what₂.LL →ₛₗ[D.what₂.embLL] (Rl.cV j).W) (c : ℂ) : Prop :=
  ∀ F : VV D.what₂.LL (FWT.lamV D j),
    harmFn (Wc D j).rank B.w B.F.BS (Rl.ioP j (PiTensorProduct.tprod ℂ u) (c0 F)) =
      c • coefFn D.what₂.embLL (FWT.lamV D j) (F : Formalism.L2.DIV.Pol D.what₂.LL D.what₂.Tau (Vc D j).rank)

theorem isScale_iff (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) {j : Fin D.R.m}
    (B : Base (Vc D j) (Wc D j)) (c : ℂ) :
    IsScale Rl v₀ B c ↔ ∃ gramR c0R c0L, Bridge.FamTie Rl.B Rl.pl (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) Rl.Q (labLL D)
      (fun τ => Bridge.lamRdef (Ptw D) τ) (fun j τ => Bridge.lamLdef (Vc D j).rank ((j : ℕ) + 1) τ) gramR c0R c0L ∧
      ∃ u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ, (∀ τ, (u τ : (Rl.MW j (sg0 D A3.A)).sm τ) = v₀ j _ τ) ∧
        IsScaleAt Rl B u (c0L j) c := Iff.rfl

variable {Rl}

theorem IsScaleAt.ioP_eq {j : Fin D.R.m} {B : Base (Vc D j) (Wc D j)} {u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ}
    {c0 : VsV D j D.what₂.LL →ₛₗ[D.what₂.embLL] (Rl.cV j).W} {c : ℂ} (h : IsScaleAt Rl B u c0 c)
    {H : Submodule ℂ (PolF D (Wc D j).rank (Vc D j).rank)}
    (hinj : ∀ P ∈ H, harmFn (Wc D j).rank B.w B.F.BS P = 0 → P = 0)
    {F : VV D.what₂.LL (FWT.lamV D j)} {P : PolF D (Wc D j).rank (Vc D j).rank} (hP : P ∈ H)
    (hio : Rl.ioP j (PiTensorProduct.tprod ℂ u) (c0 F) ∈ H)
    (hPF : harmFn (Wc D j).rank B.w B.F.BS P =
      coefFn D.what₂.embLL (FWT.lamV D j) (F : Formalism.L2.DIV.Pol D.what₂.LL D.what₂.Tau (Vc D j).rank)) :
    Rl.ioP j (PiTensorProduct.tprod ℂ u) (c0 F) = c • P :=
  sub_eq_zero.1 (hinj _ (H.sub_mem hio (H.smul_mem c hP)) (by rw [map_sub, map_smul, h F, hPF, sub_self]))

theorem isNorm_of_root {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec} {j : Fin D.R.m}
    {B : Base (Vc D j) (Wc D j)} {c ζ : ℂ} (hc : IsScale Rl v₀ B c) {n : ℕ} (hn : n ≠ 0) (hζ : ζ ^ n = 1)
    (h0 : ζ * cj (twAt D.what₂.embLL A3.A.v0) (Rl.phs j) * c ≠ 0) :
    IsNorm Rl v₀ B (ζ * cj (twAt D.what₂.embLL A3.A.v0) (Rl.phs j) * c) :=
  ⟨h0, c, hc, n, hn, by rw [mul_assoc, mul_pow, hζ, one_mul]⟩

theorem RealPin.phase_mul_thetaKO {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {ρ : Setup D.ntw} (h : RealPin Rl cG ρ) (i : D.ntw.Tw)
    {j : Fin D.R.m} (b : Bool) {u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ} {w : (Rl.cV j).W}
    {P : PolF D (Wc D j).rank (Vc D j).rank} {c : ℂ} (hP : Rl.ioP j (PiTensorProduct.tprod ℂ u) w = c • P) (ph : ℂ)
    (om : PairRep (Vc D j) (Wc D j)) (s : GA D (Vc D j)) (f : WO (Vc D j) (Wc D j) → ℂ) :
    (fun g => ph * thetaKO om s g (harmVec Rl.toRealDat j u w f)) = (ph * c) • series (ρ.B i j b).F om f s P := by
  have e : harmVec Rl.toRealDat j u w f = (ρ.B i j b).F.fock f (c • P) := by
    rw [← hP, GlobalTheory.ExportSeries.Frame.fock, h.psi, h.inf, h.cartT, h.onbT, funext (h.onbS i j b)]
    rfl
  rw [e, mul_smul, ← map_smul]
  rfl

end Scale

section Phase

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (j : Fin D.R.m) {σ : T.Q.c.F →+* ℂ}
  (hV : T.V ((j : ℕ) + 1) σ = Wc D j)

variable {T j hV} in

theorem isRat_mul {C : Cover T ((j : ℕ) + 1) σ} {κ : WeightFamilies.Wt D ((j : ℕ) + 1)} {φ : GA D (Wc D j) → ℂ} (h : IsRat T j hV C κ φ)
    {a : ℂ} (ha : a ∈ C.σ₂.fieldRange) : IsRat T j hV C κ fun g => a * φ g := by
  obtain ⟨φ', h1, rfl⟩ := h
  obtain ⟨x, rfl⟩ := ha
  refine ⟨C.σ₂ x • φ', GlobalTheory.CoverRead.Test.smul_mem_ratForms C _ _ x h1, ?_⟩
  have key : ∀ {V W : HSp D} (e : V = W) (z : ℂ) (ψ : GA D V → ℂ), castDict e (z • ψ) = fun g => z * castDict e ψ g := by
    rintro V _ rfl z ψ
    rfl
  exact key hV _ _

variable {T R j hV} in

theorem seriesRatOn_mul {C : Cover T ((j : ℕ) + 1) σ} {κ : WeightFamilies.Wt D ((j : ℕ) + 1)} {u : ∀ τ, lowT (R.MW j (sg0 D A)) τ}
    {c0 : VsV D j D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV j).W} {ph : ℂ} (h : SeriesRatOn T R j hV C κ u c0 ph)
    {a : ℂ} (ha : a ∈ C.σ₂.fieldRange) : SeriesRatOn T R j hV C κ u c0 (a * ph) := by
  intro s hs f hf w hw
  obtain ⟨h1, h2⟩ := h s hs f hf w hw
  refine ⟨?_, fun δ δc hδ => ⟨fun dd hdd => ?_, fun om hom => ?_⟩⟩
  · simpa only [mul_assoc] using isRat_mul h1 ha
  · simpa only [mul_assoc, mul_left_comm a] using isRat_mul ((h2 δ δc hδ).1 dd hdd) ha
  · simpa only [mul_assoc] using isRat_mul ((h2 δ δc hδ).2 om hom) ha

def IsRatPhase (κ : WeightFamilies.Wt D ((j : ℕ) + 1)) (u : ∀ τ, lowT (R.MW j (sg0 D A)) τ)
    (c0 : VsV D j D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV j).W) (ph : ℂ) : Prop :=
  ∀ C : Cover T ((j : ℕ) + 1) σ, GoodCover T R j C κ.n → (embLL0 D).fieldRange ≤ C.σ₂.fieldRange →
    SeriesRatOn T R j hV C κ u c0 ph

variable {T R j hV}

theorem IsRatPhase.mul {κ : WeightFamilies.Wt D ((j : ℕ) + 1)} {u : ∀ τ, lowT (R.MW j (sg0 D A)) τ}
    {c0 : VsV D j D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV j).W} {ph : ℂ} (h : IsRatPhase T R j hV κ u c0 ph)
    {a : ℂ} (ha : a ∈ (embLL0 D).fieldRange) : IsRatPhase T R j hV κ u c0 (a * ph) :=
  fun C hC hL => seriesRatOn_mul (h C hC hL) (hL ha)

end Phase

section Scalar

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1))
  (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) {j : Fin D.R.m}
  (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j) (B : Base (Vc D j) (Wc D j))

def IsRatScalar (ν : ℂ) : Prop :=
  ∃ gramR c0R c0L, Bridge.FamTie Rl.B Rl.pl (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) Rl.Q (labLL D)
      (fun τ => Bridge.lamRdef (Ptw D) τ) (fun j τ => Bridge.lamLdef (Vc D j).rank ((j : ℕ) + 1) τ) gramR c0R c0L ∧
    ∃ u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ, (∀ τ, (u τ : (Rl.MW j (sg0 D A3.A)).sm τ) = v₀ j _ τ) ∧
      ∃ c ph : ℂ, c ≠ 0 ∧ ‖ph‖ = 1 ∧ ν = ph * c ∧ IsScaleAt Rl B u (c0L j) c ∧
        IsRatPhase T Rl.toRealDat j hV (κ j) u (c0L j) ph

theorem isRatScalar_iff (ν : ℂ) : IsRatScalar T Rl κ v₀ hV B ν ↔
    ∃ gramR c0R c0L, Bridge.FamTie Rl.B Rl.pl (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) Rl.Q (labLL D)
      (fun τ => Bridge.lamRdef (Ptw D) τ) (fun j τ => Bridge.lamLdef (Vc D j).rank ((j : ℕ) + 1) τ) gramR c0R c0L ∧
    ∃ u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ, (∀ τ, (u τ : (Rl.MW j (sg0 D A3.A)).sm τ) = v₀ j _ τ) ∧
      ∃ c ph : ℂ, c ≠ 0 ∧ ‖ph‖ = 1 ∧ ν = ph * c ∧
        (∀ F : VV D.what₂.LL (FWT.lamV D j),
          harmFn (Wc D j).rank B.w B.F.BS (Rl.ioP j (PiTensorProduct.tprod ℂ u) (c0L j F)) =
            c • coefFn D.what₂.embLL (FWT.lamV D j) (F : Formalism.L2.DIV.Pol D.what₂.LL D.what₂.Tau (Vc D j).rank)) ∧
        ∀ C : Cover T ((j : ℕ) + 1) T.σ₀, GoodCover T Rl.toRealDat j C (κ j).n →
          (embLL0 D).fieldRange ≤ C.σ₂.fieldRange → SeriesRatOn T Rl.toRealDat j hV C (κ j) u (c0L j) ph := Iff.rfl

variable {T Rl κ v₀ hV B}

theorem IsRatScalar.intro {gramR c0R c0L} (h : Bridge.FamTie Rl.B Rl.pl (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) Rl.Q (labLL D)
      (fun τ => Bridge.lamRdef (Ptw D) τ) (fun j τ => Bridge.lamLdef (Vc D j).rank ((j : ℕ) + 1) τ) gramR c0R c0L) {u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ}
    (hu : ∀ τ, (u τ : (Rl.MW j (sg0 D A3.A)).sm τ) = v₀ j _ τ) {c ph : ℂ} (hc : c ≠ 0) (hph : ‖ph‖ = 1)
    (hs : IsScaleAt Rl B u (c0L j) c) (hr : IsRatPhase T Rl.toRealDat j hV (κ j) u (c0L j) ph) :
    IsRatScalar T Rl κ v₀ hV B (ph * c) :=
  ⟨gramR, c0R, c0L, h, u, hu, c, ph, hc, hph, rfl, hs, hr⟩

theorem IsRatScalar.isScale {ν : ℂ} (h : IsRatScalar T Rl κ v₀ hV B ν) :
    ∃ c ph : ℂ, c ≠ 0 ∧ ‖ph‖ = 1 ∧ ν = ph * c ∧ IsScale Rl v₀ B c := by
  obtain ⟨g, cR, cL, h0, u, hu, c, ph, h1, h2, h3, h4, -⟩ := h
  exact ⟨c, ph, h1, h2, h3, g, cR, cL, h0, u, hu, h4⟩

theorem IsRatScalar.ne_zero {ν : ℂ} (h : IsRatScalar T Rl κ v₀ hV B ν) : ν ≠ 0 := by
  obtain ⟨c, ph, h1, h2, rfl, -⟩ := h.isScale
  exact mul_ne_zero (fun e => by simp [e] at h2) h1

theorem IsRatScalar.mul {ν : ℂ} (h : IsRatScalar T Rl κ v₀ hV B ν) {a : ℂ} (ha : a ∈ (embLL0 D).fieldRange) (h0 : ‖a‖ = 1) :
    IsRatScalar T Rl κ v₀ hV B (a * ν) := by
  obtain ⟨g, cR, cL, h1, u, hu, c, ph, h2, h3, rfl, h4, h5⟩ := h
  exact ⟨g, cR, cL, h1, u, hu, c, a * ph, h2, by rw [norm_mul, h0, h3, one_mul], (mul_assoc _ _ _).symm, h4, h5.mul ha⟩

theorem IsRatScalar.mul_right {ν : ℂ} (h : IsRatScalar T Rl κ v₀ hV B ν) {a : ℂ} (ha : a ∈ (embLL0 D).fieldRange)
    (h0 : ‖a‖ = 1) : IsRatScalar T Rl κ v₀ hV B (ν * a) :=
  mul_comm a ν ▸ h.mul ha h0

theorem isRatScalar_mul_iff {ν a : ℂ} (ha : a ∈ (embLL0 D).fieldRange) (h0 : ‖a‖ = 1) :
    IsRatScalar T Rl κ v₀ hV B (a * ν) ↔ IsRatScalar T Rl κ v₀ hV B ν := by
  have hne : a ≠ 0 := fun e => by simp [e] at h0
  exact ⟨fun h => by simpa only [inv_mul_cancel_left₀ hne] using h.mul (inv_mem ha) (by rw [norm_inv, h0, inv_one]),
    fun h => h.mul ha h0⟩

theorem exists_isRatPhase (row : SeriesRat) {F : Face D A3.A} (hT : LawsJ T) (h0 : Rl.toRealDat.toLevCh.Is A3.A.μ0)
    (hg : Rl.toRealDat.IsGrp F) (hf : Rl.toRealDat.IsFam) (hm : Rl.toRealDat.IsModels) (ht : Rl.toRealDat.IsThP)
    (hi : TieIn T Rl.toRealDat κ v₀) (hp : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T Rl.toRealDat j T.σ₀ hV) (hstd : VStd D j)
    {gramR c0R c0L} (h : Bridge.FamTie Rl.B Rl.pl (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) Rl.Q (labLL D)
      (fun τ => Bridge.lamRdef (Ptw D) τ) (fun j τ => Bridge.lamLdef (Vc D j).rank ((j : ℕ) + 1) τ) gramR c0R c0L) {u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ}
    (hu : ∀ τ, (u τ : (Rl.MW j (sg0 D A3.A)).sm τ) = v₀ j _ τ) :
    ∃ ph : ℂ, ‖ph‖ = 1 ∧ IsRatPhase T Rl.toRealDat j hV (κ j) u (c0L j) ph := by
  obtain ⟨ph, h1, h2⟩ := row D Γ Pl0 T0 A3.A T Rl.toRealDat F κ v₀ hT h0 hg hf hm ht hi j hV hp hstd gramR c0R c0L h u hu
  exact ⟨ph, h1, fun C hC _ => h2 C hC⟩

theorem exists_isRatScalar (row : SeriesRat) {F : Face D A3.A} (hT : LawsJ T) (h0 : Rl.toRealDat.toLevCh.Is A3.A.μ0)
    (hg : Rl.toRealDat.IsGrp F) (hf : Rl.toRealDat.IsFam) (hm : Rl.toRealDat.IsModels) (ht : Rl.toRealDat.IsThP)
    (hi : TieIn T Rl.toRealDat κ v₀) (hp : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T Rl.toRealDat j T.σ₀ hV) (hstd : VStd D j)
    {c : ℂ} (hc : c ≠ 0) (hs : IsScale Rl v₀ B c) :
    ∃ ph : ℂ, ‖ph‖ = 1 ∧ IsRatScalar T Rl κ v₀ hV B (ph * c) := by
  obtain ⟨g, cR, cL, h1, u, hu, h2⟩ := hs
  obtain ⟨ph, h3, h4⟩ := exists_isRatPhase row hT h0 hg hf hm ht hi hp hstd h1 hu
  exact ⟨ph, h3, IsRatScalar.intro h1 hu hc h3 h2 h4⟩

example : ¬ IsRatScalar T Rl κ v₀ hV B 0 := fun h => h.ne_zero rfl

example {ν : ℂ} (h : IsRatScalar T Rl κ v₀ hV B ν) : IsRatScalar T Rl κ v₀ hV B (-ν) := by
  simpa using h.mul (neg_mem (one_mem _)) (by simp)

example {ν : ℂ} (h : IsRatScalar T Rl κ v₀ hV B ν) {x : ↥D.LL0} {n : ℕ} (hn : n ≠ 0) (hx : x ^ n = 1) :
    IsRatScalar T Rl κ v₀ hV B (embLL0 D x * ν) :=
  h.mul ⟨x, rfl⟩ (Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hx, map_one]) hn)

end Scalar

end GlobalTheory.SeriesTie

end
