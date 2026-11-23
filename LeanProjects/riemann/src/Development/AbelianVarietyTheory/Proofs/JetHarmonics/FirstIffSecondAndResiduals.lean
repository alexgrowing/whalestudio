import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ThetaSpanAdjoint
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.UnitaryDetClass
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PushMemHarmK
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ColumnMapShift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.EqOneOfSameClass
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTautologicalMarking
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.BetaIsPrincipal
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ChartCoverFOfSectionBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaValueExistsUniqueNaturalOfLawsStatement

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.RepCompare

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke

section Lattices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

omit [NumberField E] [IsCMField E] in
theorem mem_actLat (γ : Matrix (Fin n) (Fin n) E) (Λ : GenLat E n) (v' : Fin n → E) :
    v' ∈ (UnitaryAdjointCongruence.actLat γ Λ).La ↔ ∃ v ∈ Λ.La, γ.mulVec v = v' := by
  simp [UnitaryAdjointCongruence.actLat]

omit [NumberField E] [IsCMField E] in
theorem smul_le_iff (k : ℕ) (A B : Submodule (𝓞 E) (Fin n → E)) :
    Ideal.span {(k : 𝓞 E)} • A ≤ B ↔ ∀ v ∈ A, k • v ∈ B := by
  rw [Submodule.ideal_span_singleton_smul]
  constructor
  · intro h v hv
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact h (Submodule.smul_mem_pointwise_smul v _ A hv)
  · rintro h _ ⟨v, hv, rfl⟩
    have := h v hv
    rwa [← Nat.cast_smul_eq_nsmul (𝓞 E)] at this

omit [NumberField E] [IsCMField E] in
theorem gcd_smul_mem {B : Submodule (𝓞 E) (Fin n → E)} {v : Fin n → E} {k k' : ℕ} (h : k • v ∈ B) (h' : k' • v ∈ B) :
    Nat.gcd k k' • v ∈ B := by
  have e : Nat.gcd k k' • v = Nat.gcdA k k' • (k • v) + Nat.gcdB k k' • (k' • v) := by
    rw [← natCast_zsmul, Nat.gcd_eq_gcd_ab, add_zsmul, mul_comm (k : ℤ), mul_comm (k' : ℤ), mul_zsmul, mul_zsmul,
      natCast_zsmul, natCast_zsmul]
  rw [e]
  exact B.add_mem (zsmul_mem h _) (zsmul_mem h' _)

omit [NumberField E] [IsCMField E] in
theorem trivAt_mul (Λ : GenLat E n) (a b : ℕ) : Λ.TrivAt (a * b) ↔ Λ.TrivAt a ∧ Λ.TrivAt b := by
  constructor
  · rintro ⟨k, hk, h⟩
    exact ⟨⟨k, hk.coprime_mul_right_right, h⟩, ⟨k, hk.coprime_mul_left_right, h⟩⟩
  · rintro ⟨⟨k, hk, h1, h2⟩, ⟨k', hk', h1', h2'⟩⟩
    rw [smul_le_iff] at h1 h2 h1' h2'
    refine ⟨Nat.gcd k k', Nat.Coprime.mul_right (hk.coprime_dvd_left (Nat.gcd_dvd_left _ _))
      (hk'.coprime_dvd_left (Nat.gcd_dvd_right _ _)), ?_, ?_⟩ <;> rw [smul_le_iff]
    exacts [fun v hv => gcd_smul_mem (h1 v hv) (h1' v hv), fun v hv => gcd_smul_mem (h2 v hv) (h2' v hv)]

omit [NumberField E] [IsCMField E] in
theorem trivAt_of_dvd {Λ : GenLat E n} {a b : ℕ} (hab : a ∣ b) (h : Λ.TrivAt b) : Λ.TrivAt a := by
  obtain ⟨k, hk, h⟩ := h
  exact ⟨k, hk.coprime_dvd_right hab, h⟩

omit [NumberField E] [IsCMField E] in
theorem exists_levOK {Λ : GenLat E n} {bad M : ℕ} (h2 : 2 ∣ bad) (hM : Odd M) (h : Λ.TrivAt bad) :
    ∃ N, Λ.LevOK N M := by
  obtain ⟨k, hk, -, h⟩ := h
  rw [smul_le_iff] at h
  refine ⟨M * k, hM.mul (Nat.coprime_two_right.1 (hk.coprime_dvd_right h2)), dvd_mul_right _ _, ?_⟩
  rw [smul_le_iff]
  intro v hv
  refine ⟨?_, nsmul_mem hv _⟩
  rw [mul_nsmul']
  exact nsmul_mem (h v hv) _

theorem mul_adj {γ : Matrix (Fin n) (Fin n) E} (h : UnitaryAdjointCongruence.IsUnitaryM γ) : γ * UnitaryAdjointCongruence.adjM γ = 1 :=
  mul_eq_one_comm.1 h

theorem form_adj (γ : Matrix (Fin n) (Fin n) E) (v w : Fin n → E) :
    ∑ j, IsCMField.complexConj E (v j) * γ.mulVec w j =
      ∑ j, IsCMField.complexConj E ((UnitaryAdjointCongruence.adjM γ).mulVec v j) * w j := by
  simp only [Matrix.mulVec, dotProduct, UnitaryAdjointCongruence.adjM, Matrix.of_apply, map_sum, map_mul,
    IsCMField.complexConj_apply_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem unimod_act {γ : Matrix (Fin n) (Fin n) E} (h : UnitaryAdjointCongruence.IsUnitaryM γ) {Λ : GenLat E n} (hΛ : Λ.Unimod) :
    (UnitaryAdjointCongruence.actLat γ Λ).Unimod := by
  intro v
  have e : v ∈ (UnitaryAdjointCongruence.actLat γ Λ).La ↔ (UnitaryAdjointCongruence.adjM γ).mulVec v ∈ Λ.La := by
    rw [mem_actLat]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rwa [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
    · intro hv
      exact ⟨_, hv, by rw [Matrix.mulVec_mulVec, mul_adj h, Matrix.one_mulVec]⟩
  rw [e, hΛ]
  constructor
  · intro hv w hw
    obtain ⟨u, hu, rfl⟩ := (mem_actLat _ _ _).1 hw
    rw [form_adj]
    exact hv u hu
  · intro hv w hw
    rw [← form_adj]
    exact hv _ ((mem_actLat _ _ _).2 ⟨w, hw, rfl⟩)

end Lattices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

section Letters

variable (c : Coeff l) {n : ℕ}

theorem push_mem {γ : Matrix (Fin n) (Fin n) E} (h : UnitaryAdjointCongruence.IsUnitaryM γ) {Λ : GenLat E n}
    {a : (E →+* ℂ) × ℕ → ℕ} {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmL c Λ a) :
    UnitaryAdjointCongruence.pushLet c γ P ∈ harmL c (UnitaryAdjointCongruence.actLat γ Λ) a := by
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hP
  refine ⟨⟨GlobalTheory.PushHarm.push_mem_harmK E H Dw l c n γ P h h1, (GlobalTheory.Proof.ColumnMapShift.push_rows E H Dw l c n γ P fun τ i => a (τ, i)).1 h2,
    (GlobalTheory.Proof.ColumnMapShift.push_rows E H Dw l c n γ P fun τ i => a (τ, i)).2 h3⟩, ?_⟩
  have : symO (Dw := Dw) c Λ ≤ (symO c (UnitaryAdjointCongruence.actLat γ Λ)).comap (UnitaryAdjointCongruence.pushLet c γ).toRingHom := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨o, rfl⟩ | ⟨σ, i, b, hb, rfl⟩)
    · refine Subring.subset_closure (Or.inl ⟨o, ?_⟩)
      exact (algHom_C (UnitaryAdjointCongruence.pushLet c γ) (o : c.F)).symm
    · exact Subring.subset_closure (Or.inr ⟨σ, i, _, (mem_actLat _ _ _).2 ⟨b, hb, rfl⟩, UnitaryAdjointCongruence.pushLet_letB c γ σ i b⟩)
  exact this h4

def BadB (E : Type) [Field E] [NumberField E] (bad : ℕ) : Prop :=
  0 < bad ∧ ∀ p : ℕ, p.Prime → (p : ℤ) ∣ 2 * discr E → p ∣ bad

end Letters

section Values

variable (Xo : Moduli Dw l) (c : Coeff l)

structure FrameLaws : Prop where
  cover : ChartCoverF Xo c
  test : AllTest Xo c
  bc : ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S),
    ∃ z : FrPt Xo c T, FrMap φ y z

theorem frameLaws : FrameLaws Xo c :=
  have hB := GlobalTheory.allSixLaws.1.secBaseChange
  ⟨GlobalTheory.Frames.chartCoverF_of_secBaseChange hB E H Dw l Xo c, GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c,
    fun S T _ _ _ _ φ y => GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c S T φ y⟩

def WellDef (nab : NabV Xo c) {n : ℕ} (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (β : c.F) (N : ℕ)
    (P : MvPolynomial (LtN Dw n) c.F) : Prop :=
  (∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), ∃! v, ShortValAt Xo c nab w Λ β N P y v) ∧
  ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y0 : FrPt Xo c S)
    (y : FrPt Xo c T), FrMap φ y0 y → ∀ v0 v, ShortValAt Xo c nab w Λ β N P y0 v0 →
      ShortValAt Xo c nab w Λ β N P y v → φ v0 = v

def ValueLaws (nab : NabV Xo c) (n : ℕ) : Prop :=
  ∀ (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ a →
      ∀ (w : (Fin n → LevQ Dw l) → c.F) (β : c.F), WellDef Xo c nab w Λ β N P

def Rel (nab : NabV Xo c) {n : ℕ} (w : (Fin n → LevQ Dw l) → c.F) (ζ : c.F) (γ : Matrix (Fin n) (Fin n) E)
    (Λ : GenLat E n) (β : c.F) (Λ' : GenLat E n) (β' : c.F) : Prop :=
  ∀ (N N' : ℕ), Λ.LevOK N l.M → Λ'.LevOK N' l.M →
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ a →
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v v' : S),
    ShortValAt Xo c nab w Λ β N P y v → ShortValAt Xo c nab w Λ' β' N' (UnitaryAdjointCongruence.pushLet c γ P) y v' →
      v' = algebraMap c.F S ζ * v

instance (K : Type) [Field K] (p : TRing K) : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad

variable {Xo c} {nab : NabV Xo c} {n : ℕ}

theorem root_inv {K : Type} [Field K] {ζ : K} (h : ∃ k : ℕ, 0 < k ∧ ζ ^ k = 1) : ∃ k : ℕ, 0 < k ∧ ζ⁻¹ ^ k = 1 := by
  obtain ⟨k, hk, e⟩ := h
  exact ⟨k, hk, by rw [inv_pow, e, inv_one]⟩

theorem root_mul {K : Type} [Field K] {ζ ξ : K} (h : ∃ k : ℕ, 0 < k ∧ ζ ^ k = 1) (h' : ∃ k : ℕ, 0 < k ∧ ξ ^ k = 1) :
    ∃ k : ℕ, 0 < k ∧ (ζ * ξ) ^ k = 1 := by
  obtain ⟨k, hk, e⟩ := h
  obtain ⟨j, hj, e'⟩ := h'
  exact ⟨k * j, Nat.mul_pos hk hj, by rw [mul_pow, pow_mul, e, one_pow, one_mul, pow_mul', e', one_pow]⟩

end Values

section Clauses

variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {nab : NabV Xo c} {n : ℕ}

variable (Xo c nab n) in

def RootAll : Prop := ∀ bad, BadB E bad → UnitaryDetClass.RootOfUnityChange Xo c nab n bad

variable (Xo c nab) in

def DatumMoveAt (bad : ℕ) (Λ : GenLat E n) (γ : Matrix (Fin n) (Fin n) E) : Prop :=
  ∃ (γ₀ : Matrix (Fin n) (Fin n) E) (β₀ β₀' ζ : c.F) (N₀ N₀' : ℕ),
    UnitaryAdjointCongruence.IsUnitaryM γ₀ ∧ (UnitaryAdjointCongruence.actLat γ₀ Λ).TrivAt bad ∧
    (∀ v ∈ Λ.La, UnitaryAdjointCongruence.CongAt l.M (γ.mulVec v) (γ₀.mulVec v)) ∧
    UnitaryAdjointCongruence.IsBeta Dw c Λ β₀ ∧ UnitaryAdjointCongruence.IsBeta Dw c (UnitaryAdjointCongruence.actLat γ₀ Λ) β₀' ∧
    Λ.LevOK N₀ l.M ∧ (UnitaryAdjointCongruence.actLat γ₀ Λ).LevOK N₀' l.M ∧ (∃ k : ℕ, 0 < k ∧ ζ ^ k = 1) ∧
    ∀ (w : (Fin n → LevQ Dw l) → c.F), UnitaryAdjointCongruence.FixesDatum c γ w →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ a →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v v' : S),
      ShortValAt Xo c nab w Λ β₀ N₀ P y v →
      ShortValAt Xo c nab w (UnitaryAdjointCongruence.actLat γ₀ Λ) β₀' N₀' (UnitaryAdjointCongruence.pushLet c γ₀ P) y v' → v' = algebraMap c.F S ζ * v

variable (Xo c nab n) in

def DatumMove : Prop :=
  UnitaryAdjointCongruence.HidaSetting Xo c nab n → ∀ bad, UnitaryAdjointCongruence.BadOK l bad → ∀ (Λ : GenLat E n) (γ : Matrix (Fin n) (Fin n) E),
    Λ.Unimod → UnitaryAdjointCongruence.IsUnitaryM γ → Λ.TrivAt bad → (UnitaryAdjointCongruence.actLat γ Λ).TrivAt bad → DatumMoveAt Xo c nab bad Λ γ

end Clauses

section Cover

variable {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

end Cover

section Main

variable [StarRing (𝓞 E)] (Dw) (n : ℕ)

def Background : Prop :=
  ∀ (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (nab : NabV Xo c), IsNab Xo c nab → ValueLaws Xo c nab n

variable {Dw n}

end Main

end GlobalTheory.RepCompare
