import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures
import Formalism.FlagUnipotentLattices.FinalTr
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.FoldBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.GgExistsAddCharNeOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.RowsDef
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting

noncomputable section

namespace Formalism.L2.SG.Count

open MeasureTheory NumberField
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LeviCoordinates Formalism.L2.SG

def toC (B : RowsAut) (b h : ℝ) : CData where
  I := B.I
  b := b
  lam := B.lam
  g := B.g
  g₀ := B.g₀
  e := B.e
  H := B.H
  σ := B.σ
  w := B.w
  Hs := B.Hs
  σs := B.σs
  tens := B.tens
  μf := B.μf
  fund := B.fund
  R := B.R
  Re := B.Re
  h := h

theorem toC_Dc (B : RowsAut) (b h : ℝ) : (toC B b h).Dc = (B.D : ℝ) :=
  rfl

theorem toC_Ds (B : RowsAut) (b h : ℝ) :
    (toC B b h).Ds = B.I.Dstar (fdegAll B.I B.σ B.w) B.μf B.fund B.e :=
  rfl

theorem countData_of (B : RowsAut) (hDS : ∀ v, IsDS (B.I.ε v) (B.lam v) (B.σ v))
    (hw : ∀ v, IsLowUnit (B.I.ε v) (B.lam v) (B.σ v) (B.w v)) :
    CountData B.I B.lam B.σ B.w B.σs B.tens B.μf B.fund B.R B.e B.Re :=
  ⟨hDS, hw, B.tens_spec, B.haar, B.fund_spec, B.R_spec, B.Re_spec⟩

theorem hypB_of (B : RowsAut) {n₀ : ℕ} {A b h : ℝ} (hS : HidaSetting B.I n₀ A b B.lam B.μf B.g B.g₀ B.e)
    (hDS : ∀ v, IsDS (B.I.ε v) (B.lam v) (B.σ v)) (hw : ∀ v, IsLowUnit (B.I.ε v) (B.lam v) (B.σ v) (B.w v))
    (hG : ∀ v, Formalism.QuantumDeterminants.GapAtLeast (B.I.ε v) (B.lam v) h) : (toC B b h).HypB n₀ A :=
  ⟨hS, countData_of B hDS hw, hG⟩

theorem exists_pos_const_Lagrange_condition (D : Formalism.BasicNotions.D7) : adm5 D :=
  (admitted_iff_cover_radius D).2 Formalism.HermitianLatticeCounting.Final.S7.coverRadius'

theorem explicit_formula_bound_holds : ∃ C : ℝ, 1 ≤ C ∧ ∀ D : Formalism.BasicNotions.D7, adm7 D C :=
  residue_admitted_of_known Formalism.HermitianLatticeCounting.Final.S7.residue_bound

theorem points_bound_of_volumeCountGeometryConditions : ∃ c' cb : ℝ, 0 < c' ∧ 0 < cb ∧ ∀ Cd Cq Cv A Cb cε : ℝ, 1 ≤ Cd → 0 ≤ Cq → 16 * Cq ≤ Cd →
    1 ≤ Cv → 1 ≤ A → 0 < cε → cε ≤ 1 / 90000 →
    ∃ (n₁ : ℕ) (C₂ : ℝ), ∀ (D : Formalism.BasicNotions.D7) (n₀ : ℕ) (C : ℝ), n₁ ≤ n₀ → C₂ ≤ C → adm2 D → DiscreteSeriesDecayBound D →
      LocalProjectorRealPlace D → Conclusion2 D n₀ A Cb → DistTri → VolumeCountGeometryConditions n₀ A C cb cε Cv Cd Cq → PointsLemma D n₀ A C c' cb := by
  obtain ⟨c', cb, hc', hcb, h⟩ := packet_bound_of_volume_count_geometry
  obtain ⟨Cres, -, hres⟩ := explicit_formula_bound_holds
  refine ⟨c', cb, hc', hcb, fun Cd Cq Cv A Cb cε hCd hCq hCC hCv hA hcε hcε2 => ?_⟩
  obtain ⟨n₁, C₂, h⟩ := h Cd Cq Cv Cres A Cb cε hCd hCq hCC hCv hA hcε hcε2
  exact ⟨n₁, C₂, fun D n₀ C hn hC h2 hdec hloc hb htri hS => h D n₀ C hn hC h2 (hres D) hdec hloc hb htri hS⟩

def eta (X : CData) (c : ℝ) : ℝ := Real.exp (-c * (X.I.n : ℝ) * (X.I.f : ℝ) * Real.log (X.I.n : ℝ))

theorem dc_le_of_conC (X : CData) {c : ℝ} (hC : X.ConC c) : X.Dc ≤ (1 + eta X c) * X.Ds := by
  have h := (abs_le.1 hC).2
  show X.Dc ≤ (1 + Real.exp (-c * (X.I.n : ℝ) * (X.I.f : ℝ) * Real.log (X.I.n : ℝ))) * X.Ds
  linarith

theorem le_dc_of_conC (X : CData) {c : ℝ} (hC : X.ConC c) : (1 - eta X c) * X.Ds ≤ X.Dc := by
  have h := (abs_le.1 hC).1
  show (1 - Real.exp (-c * (X.I.n : ℝ) * (X.I.f : ℝ) * Real.log (X.I.n : ℝ))) * X.Ds ≤ X.Dc
  linarith

theorem finDim_of_conC (X : CData) {c : ℝ} (hC : X.ConC c) (hD : 0 < X.Ds) (hη : eta X c < 1) :
    FiniteDimensional ℂ (X.I.eHom X.σs X.μf X.fund X.R X.Re) := by
  by_contra hfin
  have h0 : X.Dc = 0 := by
    show ((Module.finrank ℂ (X.I.eHom X.σs X.μf X.fund X.R X.Re) : ℕ) : ℝ) = 0
    rw [Module.finrank_of_not_finite hfin]
    simp
  have h1 := le_dc_of_conC X hC
  rw [h0] at h1
  nlinarith [mul_pos (sub_pos.2 hη) hD]

def ProjCuspRows (B : RowsAut) (b h : ℝ) : Prop :=
  (toC B b h).ProjStep ∧ (toC B b h).CountedStep ∧ (toC B b h).CuspStep

theorem projCuspRows_of_stepsB (B : RowsAut) {n₀ : ℕ} {A C b h : ℝ} (hS : StepsB n₀ A C)
    (hX : (toC B b h).HypB n₀ A) (t1 : (toC B b h).GapAboveThreeHalvesPower) (t2 : (toC B b h).GapAboveSquareRootThreshold C) : ProjCuspRows B b h :=
  hS _ hX t1 t2

theorem projCuspRows_of_end (D : Formalism.BasicNotions.D7) (B : RowsAut) {n₀ : ℕ} {A C b h : ℝ} (hn₀ : 1 ≤ n₀) (hC : 46 ≤ C)
    (ha1 : adm1 D) (ha2 : adm2 D) (ha8 : adm8 D) (hdec : DiscreteSeriesDecayBound D) (hloc : LocalProjectorRealPlace D) (hE : cu_StepsEnd n₀ A C)
    (hX : (toC B b h).HypB n₀ A) (t1 : (toC B b h).GapAboveThreeHalvesPower) (t2 : (toC B b h).GapAboveSquareRootThreshold C) : ProjCuspRows B b h :=
  projCuspRows_of_stepsB B (projection_facts_of_schur D n₀ A C hn₀ hC ha1 ha2 ha8 hdec hloc hE) hX t1 t2

section Lat

variable (I : AutInst)

def LatCount : Prop :=
  ∀ x y : I.GA, 0 < LitS.Size.tau1 I x → 0 < LitS.Size.tau1 I y →
    ∀ r : InfinitePlace I.F → ℝ, (∀ v, 0 ≤ r v) → ∀ S : Finset I.GFset,
      (∀ γ ∈ S, (x⁻¹ * (γ : I.GA) * y).2 ∈ I.Kset ∧ ∀ v, cartanDistance (I.ε v) ((x⁻¹ * (γ : I.GA) * y).1 v) ≤ r v) →
      (S.card : ℝ) ≤ (3 * Real.sqrt (I.n : ℝ) / (LitS.Size.tau1 I x * LitS.Size.tau1 I y)) ^ (2 * I.n ^ 2 * I.f) *
        Real.exp (2 * (I.n : ℝ) ^ 2 * ∑ v, r v)

def Om (r : InfinitePlace I.F → ℝ) (K' : Set I.Gf) : Set I.GA :=
  {ω | (∀ v, cartanDistance (I.ε v) (ω.1 v) ≤ r v) ∧ ω.2 ∈ K'}

def COm (r : InfinitePlace I.F → ℝ) : ℝ :=
  (3 * Real.sqrt (I.n : ℝ)) ^ (2 * I.n ^ 2 * I.f) * Real.exp (4 * (I.n : ℝ) ^ 2 * ∑ v, r v)

def MultBound : Prop :=
  ∀ r : InfinitePlace I.F → ℝ, (∀ v, 0 ≤ r v) → ∀ K' : Subgroup I.Gf, (K' : Set I.Gf) ⊆ I.Kset →
    ∀ x : I.GA, 0 < LitS.Size.tau1 I x →
      FoldBound.mult (rr_GF I) (Om I r (K' : Set I.Gf)) x ≤
        ENNReal.ofReal (COm I r / LitS.Size.tau1 I x ^ (4 * I.n ^ 2 * I.f))

def FoldReady : Prop :=
  LocallyCompactSpace I.GA ∧ SecondCountableTopology I.GA ∧ T2Space I.GA ∧ BorelSpace I.GA ∧
    DiscreteTopology (rr_GF I)

end Lat

theorem allCount_of_latCount (X : CData) (hL : LatCount X.I) (hpos : ∀ x, 0 < LitS.Size.tau1 X.I x) :
    AllCount X (2 * (X.I.n : ℝ) ^ 2) := by
  refine Filter.Eventually.of_forall fun x => ?_
  refine ⟨(3 * Real.sqrt (X.I.n : ℝ) / (LitS.Size.tau1 X.I x * LitS.Size.tau1 X.I x)) ^ (2 * X.I.n ^ 2 * X.I.f),
    by have := hpos x; positivity, fun r hr S hS => ?_⟩
  exact hL x x (hpos x) (hpos x) r hr S hS

theorem finVol_of_hypB (hB : LitS.BorelFinVol) (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) : X.FinVol :=
  LitS.finVol_of_borel hB X hX.2.1.2.2.2.1 hX.2.1.2.2.2.2.1

theorem geometric_count_of_borel (hB : LitS.BorelFinVol) (hL : ∀ I : AutInst, LatCount I) (hT : LitS.ReductionTau)
    {n₀ : ℕ} (hn₀ : 1 ≤ n₀) {A C cb cε Cv Cd Cq : ℝ}
    (hG : ∀ X : CData, X.HypC n₀ A C cb → GeoS X cε Cv Cd Cq) : VolumeCountGeometryConditions n₀ A C cb cε Cv Cd Cq := by
  intro X hX
  have hn : 1 ≤ X.I.n := le_trans hn₀ hX.1.1.1
  exact ⟨finVol_of_hypB hB X hX.1, allCount_of_latCount X (hL X.I) fun x => ((hT X.I hn).2 x).1, hG X hX⟩

section DistInv

open Matrix

theorem dvi_hs_neg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Formalism.REAL.hs (-A) = Formalism.REAL.hs A := by
  simp [Formalism.REAL.hs, norm_neg]

theorem dvi_trace_hs {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (Aᴴ * A).trace = ((Formalism.REAL.hs A : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Formalism.REAL.hs]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact RCLike.conj_mul _

theorem dvi_hs_conj {n : ℕ} (k X : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Formalism.REAL.hs (k * X * kᴴ) = Formalism.REAL.hs X := by
  have hk' : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk
  apply Complex.ofReal_injective
  rw [← dvi_trace_hs, ← dvi_trace_hs, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  have e1 : k * (Xᴴ * kᴴ) * (k * X * kᴴ) = k * (Xᴴ * X) * kᴴ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc kᴴ k, hk', Matrix.one_mul]
  rw [e1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hk', Matrix.one_mul]

theorem dvi_sub {n : ℕ} (ε : Fin n → Bool) (g : Formalism.REAL.UJ ε) (t : ℝ)
    (ht : ∃ k X : Matrix (Fin n) (Fin n) ℂ, k ∈ Formalism.REAL.Kset ε ∧ Formalism.REAL.inP ε X ∧
      umat g = k * NormedSpace.exp X ∧ t = Real.sqrt (Formalism.REAL.hs X)) :
    ∃ k X : Matrix (Fin n) (Fin n) ℂ, k ∈ Formalism.REAL.Kset ε ∧ Formalism.REAL.inP ε X ∧
      umat g⁻¹ = k * NormedSpace.exp X ∧ t = Real.sqrt (Formalism.REAL.hs X) := by
  obtain ⟨k, X, hK, hX, hgm, ht⟩ := ht
  have hk1 : k ∈ Matrix.unitaryGroup (Fin n) ℂ := hK.1
  have hk : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk1
  have hk2 : k * kᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hk1
  have hJk : k * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * k := hK.2
  have hX1 : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := hX.1
  have hX2 : X * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X) := hX.2
  have hY1 : (-X)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * (-X) = 0 := by
    rw [Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, hX1, neg_zero]
  have hY2 : (-X) * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * (-X)) := by
    rw [Matrix.neg_mul, hX2, Matrix.mul_neg]
  have hφ : ∀ A B : Matrix (Fin n) (Fin n) ℂ, (k * A * kᴴ) * (k * B * kᴴ) = k * (A * B) * kᴴ := by
    intro A B
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc kᴴ k, hk, Matrix.one_mul]
  have hJφ : k * Formalism.REAL.Jm ε * kᴴ = Formalism.REAL.Jm ε := by
    rw [hJk, Matrix.mul_assoc, hk2, Matrix.mul_one]
  have hct : (k * (-X) * kᴴ)ᴴ = k * (-X)ᴴ * kᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  have hK' : kᴴ ∈ Formalism.REAL.Kset ε := by
    show kᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ kᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * kᴴ
    refine ⟨Matrix.mem_unitaryGroup_iff.2 ?_, ?_⟩
    · rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
      exact hk
    · calc kᴴ * Formalism.REAL.Jm ε = kᴴ * Formalism.REAL.Jm ε * (k * kᴴ) := by rw [hk2, Matrix.mul_one]
        _ = kᴴ * (Formalism.REAL.Jm ε * k) * kᴴ := by simp only [Matrix.mul_assoc]
        _ = kᴴ * (k * Formalism.REAL.Jm ε) * kᴴ := by rw [hJk]
        _ = Formalism.REAL.Jm ε * kᴴ := by rw [← Matrix.mul_assoc, hk, Matrix.one_mul]
  have hP' : Formalism.REAL.inP ε (k * (-X) * kᴴ) := by
    show ((k * (-X) * kᴴ)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * (k * (-X) * kᴴ) = 0) ∧
      (k * (-X) * kᴴ) * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * (k * (-X) * kᴴ))
    constructor
    · rw [hct]
      calc (k * (-X)ᴴ * kᴴ) * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * (k * (-X) * kᴴ)
          = (k * (-X)ᴴ * kᴴ) * (k * Formalism.REAL.Jm ε * kᴴ) + (k * Formalism.REAL.Jm ε * kᴴ) * (k * (-X) * kᴴ) := by
            rw [hJφ]
        _ = k * ((-X)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * (-X)) * kᴴ := by
            rw [hφ, hφ, Matrix.mul_add, Matrix.add_mul]
        _ = 0 := by rw [hY1, Matrix.mul_zero, Matrix.zero_mul]
    · calc (k * (-X) * kᴴ) * Formalism.REAL.Jm ε = (k * (-X) * kᴴ) * (k * Formalism.REAL.Jm ε * kᴴ) := by rw [hJφ]
        _ = k * ((-X) * Formalism.REAL.Jm ε) * kᴴ := hφ _ _
        _ = k * (-(Formalism.REAL.Jm ε * (-X))) * kᴴ := by rw [hY2]
        _ = -((k * Formalism.REAL.Jm ε * kᴴ) * (k * (-X) * kᴴ)) := by rw [hφ, Matrix.mul_neg, Matrix.neg_mul]
        _ = -(Formalism.REAL.Jm ε * (k * (-X) * kᴴ)) := by rw [hJφ]
  have hE : NormedSpace.exp X * NormedSpace.exp (-X) = 1 := by
    rw [← Matrix.exp_add_of_commute X (-X) (Commute.neg_right (Commute.refl X)), add_neg_cancel,
      NormedSpace.exp_zero]
  have hku : IsUnit k := ⟨⟨k, kᴴ, hk2, hk⟩, rfl⟩
  have hkinv : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv hk
  have hconj : NormedSpace.exp (k * (-X) * kᴴ) = k * NormedSpace.exp (-X) * kᴴ := by
    rw [← hkinv]
    exact Matrix.exp_conj k (-X) hku
  have hinv : umat g⁻¹ * umat g = 1 := Units.inv_mul (g : (Matrix (Fin n) (Fin n) ℂ)ˣ)
  have key : k * NormedSpace.exp X * (NormedSpace.exp (-X) * kᴴ) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (NormedSpace.exp X), hE, Matrix.one_mul, hk2]
  refine ⟨kᴴ, k * (-X) * kᴴ, hK', hP', ?_, ?_⟩
  · calc umat g⁻¹ = umat g⁻¹ * (umat g * (NormedSpace.exp (-X) * kᴴ)) := by
          rw [hgm, key, Matrix.mul_one]
      _ = NormedSpace.exp (-X) * kᴴ := by rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
      _ = kᴴ * NormedSpace.exp (k * (-X) * kᴴ) := by
          rw [hconj]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc kᴴ k, hk, Matrix.one_mul]
  · rw [ht, dvi_hs_conj k (-X) hk1, dvi_hs_neg]

theorem dV_inv {n : ℕ} (ε : Fin n → Bool) (g : Formalism.REAL.UJ ε) : cartanDistance ε g⁻¹ = cartanDistance ε g := by
  unfold cartanDistance
  congr 1
  ext t
  constructor
  · intro h
    have h2 := dvi_sub ε g⁻¹ t h
    rwa [inv_inv] at h2
  · exact dvi_sub ε g t

end DistInv

theorem encard_le_ofReal_of_finset {α : Type*} (T : Set α) (M : ℝ)
    (h : ∀ S : Finset α, (∀ a ∈ S, a ∈ T) → (S.card : ℝ) ≤ M) :
    ((T.encard : ℕ∞) : ENNReal) ≤ ENNReal.ofReal M := by
  rcases T.finite_or_infinite with hT | hT
  · have hS := h hT.toFinset (fun a ha => hT.mem_toFinset.1 ha)
    rw [hT.encard_eq_coe_toFinset_card]
    have e : (((hT.toFinset.card : ℕ∞)) : ENNReal) = ((hT.toFinset.card : ℕ) : ENNReal) := by simp
    rw [e, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hS
  · exfalso
    obtain ⟨S, hSsub, hcard⟩ := hT.exists_subset_card_eq (⌈M⌉₊ + 1)
    have h1 := h S (fun a ha => hSsub ha)
    rw [hcard] at h1
    push_cast at h1
    linarith [Nat.le_ceil M]

theorem multBound_of_latCount (I : AutInst) (hL : LatCount I) (hT : DistTri) : MultBound I := by
  intro r hr K' hK' x hx
  have hbound : (3 * Real.sqrt (I.n : ℝ) / (LitS.Size.tau1 I x * LitS.Size.tau1 I x)) ^ (2 * I.n ^ 2 * I.f) *
      Real.exp (2 * (I.n : ℝ) ^ 2 * ∑ v, 2 * r v) = COm I r / LitS.Size.tau1 I x ^ (4 * I.n ^ 2 * I.f) := by
    have e1 : (LitS.Size.tau1 I x * LitS.Size.tau1 I x) ^ (2 * I.n ^ 2 * I.f) =
        LitS.Size.tau1 I x ^ (4 * I.n ^ 2 * I.f) := by
      rw [← pow_two, ← pow_mul]
      ring_nf
    have e2 : 2 * (I.n : ℝ) ^ 2 * ∑ v, 2 * r v = 4 * (I.n : ℝ) ^ 2 * ∑ v, r v := by
      rw [← Finset.mul_sum]
      ring
    rw [div_pow, e1, e2]
    unfold COm
    ring
  unfold FoldBound.mult
  refine iSup_le fun y => ?_
  apply encard_le_ofReal_of_finset
  intro S hS
  rcases S.eq_empty_or_nonempty with hS0 | ⟨γ0, hγ0S⟩
  · rw [hS0, Finset.card_empty, Nat.cast_zero]
    unfold COm
    have := hx
    positivity
  have hγ0 := hS γ0 hγ0S
  let F : rr_GF I → I.GFset := fun γ => ⟨((γ * γ0⁻¹ : rr_GF I) : I.GA), (γ * γ0⁻¹).2⟩
  have hFinj : Function.Injective F := by
    intro γ1 γ2 h
    have h2 : γ1 * γ0⁻¹ = γ2 * γ0⁻¹ := Subtype.ext (congrArg Subtype.val h)
    exact mul_right_cancel h2
  have hc := hL x x hx hx (fun v => 2 * r v) (fun v => by linarith [hr v]) (S.map ⟨F, hFinj⟩) ?_
  · rw [Finset.card_map] at hc
    rw [← hbound]
    exact hc
  · intro δ hδ
    obtain ⟨γ, hγS, hδeq⟩ := Finset.mem_map.1 hδ
    have h1 := hS γ hγS
    have hδv : (δ : I.GA) = (γ : I.GA) * (γ0 : I.GA)⁻¹ := by
      rw [← hδeq]
      rfl
    have e : x⁻¹ * ((γ : I.GA) * (γ0 : I.GA)⁻¹) * x =
        (x⁻¹ * ((γ : I.GA) * y)) * (x⁻¹ * ((γ0 : I.GA) * y))⁻¹ := by
      group
    rw [hδv, e]
    constructor
    · exact hK' (K'.mul_mem h1.2 (K'.inv_mem hγ0.2))
    · intro v
      refine le_trans (hT _ (I.ε v) ((x⁻¹ * ((γ : I.GA) * y)).1 v) ((x⁻¹ * ((γ0 : I.GA) * y)).1 v)⁻¹) ?_
      rw [dV_inv]
      linarith [h1.1 v, hγ0.1 v]

theorem muA_isHaar (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] :
    (I.muA μf).IsHaarMeasure := by
  haveI : ∀ v, (Formalism.REAL.muG (I.ε v)).IsHaarMeasure := fun v => by
    unfold Formalism.REAL.muG
    infer_instance
  haveI hpi : (Measure.pi fun v => Formalism.REAL.muG (I.ε v)).IsHaarMeasure := by
    infer_instance
  unfold AutInst.muA
  exact Measure.prod.instIsHaarMeasure _ _

theorem foldBound_GA (I : AutInst) (hR : FoldReady I) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] :
    @FoldBound.FoldBound I.GA _ _ _ hR.1 hR.2.1 _ hR.2.2.2.1 (I.muA μf) (muA_isHaar I μf) := by
  exact @FoldBound.foldBound_holds I.GA _ _ _ hR.1 hR.2.1 _ hR.2.2.2.1 (I.muA μf) (muA_isHaar I μf)

theorem rows_D_le (B : RowsAut) {b h c : ℝ} (hC : (toC B b h).ConC c) :
    (B.D : ℝ) ≤ (1 + eta (toC B b h) c) * B.I.Dstar (fdegAll B.I B.σ B.w) B.μf B.fund B.e := by
  have h1 := dc_le_of_conC _ hC
  rwa [toC_Dc, toC_Ds] at h1

theorem finDim_HH_of_conC (hB : RowsDef.RowsBij) (B : RowsAut) (dv : InfinitePlace B.I.F → ℝ)
    (hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v)) (hIrr : ∀ v, IsIrredOn (UJset (B.I.ε v)) (B.σ v))
    (hF : ∀ v, IsFdeg (Formalism.REAL.muG (B.I.ε v)) (B.σ v) (dv v)) (hw : ∀ v, ‖B.w v‖ = 1)
    (hint : ∀ v, Integrable (ProjRows.phLoc (ε := B.I.ε v) (B.σ v) (B.w v) (dv v)) (Formalism.REAL.muG (B.I.ε v)))
    (T : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund)
    (hT : ProjRows.IsOpInt (ProjRows.muInf B.I) (fun g => B.R (g, 1)) (ProjRows.phInf B.I B.σ B.w dv) T)
    {b h c : ℝ} (hC : (toC B b h).ConC c) (hD : 0 < (toC B b h).Ds) (hη : eta (toC B b h) c < 1) :
    FiniteDimensional ℂ (RowsDef.HHB B T) := by
  obtain ⟨hinj, hran⟩ := hB B.I B.μf B.fund B.fund_spec B.R B.R_spec B.e B.Re B.Re_spec B.H B.σ dv B.w
    hU hIrr hF hw hint T hT B.Hs B.σs B.tens B.tens_spec
  have : FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) := finDim_of_conC (toC B b h) hC hD hη
  exact RowsDef.finiteDimensional_HH_of_eHom hinj hran

theorem countData_setting {D : Formalism.BasicNotions.D7} (X : HidaSetting.HidaSetting D) :
    CountData X.B.I X.B.lam X.B.σ X.B.w X.B.σs X.B.tens X.B.μf X.B.fund X.B.R X.B.e X.B.Re :=
  countData_of X.B X.ds X.low

theorem level_set_le_compact {D : Formalism.BasicNotions.D7} (X : HidaSetting.HidaSetting D) : X.K2 ⊆ X.B.I.Kset :=
  fun _ hx => hx.1

def levelSubgroupOfCharacter {D : Formalism.BasicNotions.D7} (X : HidaSetting.HidaSetting D) (hG : X.LevelSubgroupCharacter) : Subgroup X.B.I.Gf where
  carrier := X.K2
  one_mem' := hG.1
  mul_mem' := fun ha hb => hG.2.1 _ ha _ hb
  inv_mem' := fun ha => hG.2.2.1 _ ha

theorem level_subgroup_le_compact {D : Formalism.BasicNotions.D7} (X : HidaSetting.HidaSetting D) (hG : X.LevelSubgroupCharacter) :
    ((levelSubgroupOfCharacter X hG : Subgroup X.B.I.Gf) : Set X.B.I.Gf) ⊆ X.B.I.Kset :=
  level_set_le_compact X

end Formalism.L2.SG.Count
