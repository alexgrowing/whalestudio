import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetDeterminantOfDeRham
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.PeriodFamily
open GlobalTheory.LatJet GlobalTheory.LatJet.An GlobalTheory.LatJet.An.Det
open scoped Classical Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatJet.An.ZetaNonvanishing₂

theorem mem_Fil_iff {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (H : LieExact A) {x : HdR A}
    {w : Fin g → ℂ} (h : ∃ v, IsLieImage x v ∧ u.IsDiff w v) : x ∈ Fil A ↔ w = 0 := by
  obtain ⟨v, h1, h2⟩ := h
  refine ⟨fun hx ↦ ?_, fun hw ↦ ?_⟩
  · obtain rfl : v = 1 := (H.1 x).unique h1 (isLieImage_one_iff.2 hx)
    exact ArchMetricCompare.eq_zero_of_isDiff u h2
  · obtain rfl : v = 1 := (ArchMetricCompare.isDiff_ne_iff u h1.1 h2).1 hw
    exact isLieImage_one_iff.1 h1

theorem vec_unique {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (H : LieExact A) {x : HdR A}
    {w w' : Fin g → ℂ} (h : ∃ v, IsLieImage x v ∧ u.IsDiff w v) (h' : ∃ v, IsLieImage x v ∧ u.IsDiff w' v) : w = w' := by
  have key := exists_lie_comb u (fun _ : Bool ↦ x) (fun b ↦ if b then w else w') (fun b ↦ by cases b <;> simpa)
    (Finsupp.single true 1 - Finsupp.single false 1)
  simp only [map_sub, Finsupp.linearCombination_single, one_smul, sub_self, if_true, Bool.false_eq_true, if_false] at key
  exact sub_eq_zero.1 ((mem_Fil_iff u H key).1 (zero_mem _))

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {𝔠 : FracId (FR E)} {φ : I → E →+* ℂ}

theorem pair_special {L : Set E} (T : CxPt 𝔠 φ L) {ε : ℤˣ} {P : T.U.u.Λ →+ HdR T.X.A} (hP : IsPeriodMap ε T.U.u P)
    (c d : T.U.u.Λ →₀ ℂ) : T.ψ (Finsupp.linearCombination ℂ P c) (Finsupp.linearCombination ℂ P d) =
      ((ε : ℤ) : ℂ) * Real.pi * ∑ a, T.U.h (T.U.e a) * (hol _ c a * ahol _ d a - ahol _ c a * hol _ d a) := by
  obtain ⟨χ, hχ⟩ := T.U.ah
  rw [pair_comb _ P T.ψ (fun a ↦ T.U.h (T.U.e a)) _ (hP.2.2.2.2 _ χ T.ψ hχ T.pol) c d]
  congr 1
  field_simp

theorem exists_comb_eigen [IsCMField E] (H : GlobalTheory.Published.AbelianDeRham) (hφ : IsCMType φ) {c : Ideal (OF E)} (hc : c ≠ ⊥)
    {y : (Af E)ˣ} (T : CxPt 𝔠 φ (lattice c y)) {ε : ℤˣ} {P : T.U.u.Λ →+ HdR T.X.A} (hP : IsPeriodMap ε T.U.u P) (i : I) :
    ∃ d, Finsupp.linearCombination ℂ P d = T.y i ∧ hol _ d = Pi.single (T.U.e.symm i) (T.w i) ∧ ahol _ d = 0 := by
  obtain ⟨d, hd⟩ : T.y i ∈ LinearMap.range (Finsupp.linearCombination ℂ P) := by
    rw [Finsupp.range_linearCombination, hP.1]; trivial
  refine ⟨d, hd, vec_unique T.U.u (H.2.1 ℂ T.X.A _ T.X.ab T.X.dim).1 (hd ▸ exists_lie_comb T.U.u P _ hP.2.2.1 d) (T.cm i).2,
    funext fun m ↦ ?_⟩
  obtain ⟨a, h1, h2⟩ := exists_comb _ T.U.u.full (Pi.single m 1)
  have h0 : T.ψ (Finsupp.linearCombination ℂ P a) (T.y i) = 0 := by
    have e : (1 : ℂ) • (T.ψ (Finsupp.linearCombination ℂ P a) (T.y i) • T.y i) = 0 :=
      low_eq_zero hφ hc { T with s := fun _ ↦ 1 } hP h1 h2 i
    rw [one_smul] at e
    rcases smul_eq_zero.1 e with e | e
    · exact e
    · rw [e, map_zero]
  obtain ⟨χ, hχ⟩ := T.U.ah
  have hh : (T.U.h (T.U.e m) : ℂ) ≠ 0 := fun e ↦ by
    have := hχ.2.1 (Pi.single m 1) (by simp)
    simp [Matrix.mulVec_diagonal, e] at this
  rw [← hd, pair_special T hP] at h0
  simp only [h1, h2, Pi.zero_apply, zero_mul, sub_zero, Pi.single_apply, ite_mul, _root_.one_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h0
  simpa [hh, Real.pi_ne_zero] using h0

theorem low_anti [IsCMField E] (H : GlobalTheory.Published.AbelianDeRham) (hφ : IsCMType φ) {c : Ideal (OF E)} (hc : c ≠ ⊥)
    {y : (Af E)ˣ} (T : CxPt 𝔠 φ (lattice c y)) {ε : ℤˣ} {P : T.U.u.Λ →+ HdR T.X.A} (hP : IsPeriodMap ε T.U.u P) (i : I)
    {b : T.U.u.Λ →₀ ℂ} (h1 : hol _ b = 0) (h2 : ahol _ b = Pi.single (T.U.e.symm i) 1) :
    ∃ d, hol _ d = Pi.single (T.U.e.symm i) (-(((ε : ℤ) : ℂ) * T.A i)) ∧ ahol _ d = 0 ∧
      ∀ k, T.low k (Finsupp.linearCombination ℂ P b) = if k = i then Finsupp.linearCombination ℂ P d else 0 := by
  have key : ∀ k, T.low k (Finsupp.linearCombination ℂ P b) =
      (if k = i then -(((ε : ℤ) : ℂ) * Real.pi * T.U.h i * T.s i * T.w i) else 0) • T.y k := fun k ↦ by
    obtain ⟨d, e0, e1, e2⟩ := exists_comb_eigen H hφ hc T hP k
    have e := pair_special T hP b d
    rw [e0] at e
    change T.s k • (T.ψ _ (T.y k) • T.y k) = _
    rw [e, smul_smul]
    congr 1
    simp only [h1, h2, e1, Pi.zero_apply, zero_mul, zero_sub, Pi.single_apply, ite_mul, _root_.one_mul, mul_neg, mul_ite, mul_zero,
      Finset.sum_neg_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, Equiv.apply_symm_apply, EmbeddingLike.apply_eq_iff_eq]
    by_cases hk : k = i
    · subst hk
      simp only [if_true]
      ring
    · simp [hk, Ne.symm hk]
  obtain ⟨d, e0, e1, e2⟩ := exists_comb_eigen H hφ hc T hP i
  refine ⟨(-(((ε : ℤ) : ℂ) * Real.pi * T.U.h i * T.s i * T.w i)) • d, ?_, by rw [map_smul, e2, smul_zero], fun k ↦ ?_⟩
  · rw [map_smul, e1, ← Pi.single_smul, smul_eq_mul, CxPt.A]
    congr 1
    ring
  · rw [key]
    split_ifs with hk
    · rw [map_smul, e0, hk]
    · exact zero_smul _ _

theorem exists_comb_anti {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (h : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (w : Fin g → ℂ) :
    ∃ c, hol Λ c = 0 ∧ ahol Λ c = w := by
  obtain ⟨c, h1, h2⟩ := exists_comb Λ h (star w)
  have k : ∀ c : Λ →₀ ℂ, ∃ c', hol Λ c' = star (ahol Λ c) ∧ ahol Λ c' = star (hol Λ c) := fun c ↦ by
    induction c using Finsupp.induction_linear with
    | zero => exact ⟨0, by simp, by simp⟩
    | add c d hc hd =>
      obtain ⟨c', e1, e2⟩ := hc
      obtain ⟨d', e3, e4⟩ := hd
      exact ⟨c' + d', by simp only [map_add, e1, e3, star_add], by simp only [map_add, e2, e4, star_add]⟩
    | single x r => exact ⟨Finsupp.single x (star r), by simp, by simp⟩
  obtain ⟨c', e1, e2⟩ := k c
  exact ⟨c', by rw [e1, h2, star_zero], by rw [e2, h1, star_star]⟩

theorem isUnit_jet (hC : JetCalc) {n : ℕ} (J : JetRing ℂ I n) {f : (I → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) (h0 : f 0 ≠ 0) :
    IsUnit (jet J f) := by
  have e : J.π (jet J f) = f 0 := by
    rw [J.π_eq]
    exact (hC I n J).1 f hf _ [] fun _ ↦ rfl
  have hm : jet J f - algebraMap ℂ J.B (f 0) ∈ RingHom.ker J.π := by
    rw [RingHom.mem_ker, map_sub, e, J.π_algebraMap, sub_self]
  obtain ⟨N, hN⟩ := J.nil.exists_dpow_eq_zero
  have hn : IsNilpotent (jet J f - algebraMap ℂ J.B (f 0)) :=
    ⟨N, by rw [← J.κ.factorial_mul_dpow_eq_pow hm, hN N le_rfl, mul_zero]⟩
  simpa using hn.isUnit_add_right_of_commute ((Ne.isUnit h0).map (algebraMap ℂ J.B)) (Commute.all _ _)

section Main

variable {n : ℕ} {L : Set E} {T : CxPt 𝔠 φ L} {J : JetRing ℂ I n} {Y : Family J T.X T.δ T.low} {G : Germ Y} {ε : ℤˣ}

def period (K : Coord ε G) (c : T.U.u.Λ →₀ ℂ) (ω : primDR G.X.A) (z : I → ℂ) : ℂ :=
  Finsupp.linearCombination ℂ (K.P z) c ((K.mor z).pull ω)

theorem mem_Fil_fibre (H : GlobalTheory.Published.AbelianDeRham) (K : Coord ε G) {z : I → ℂ} (hz : z ∈ K.V) (c : T.U.u.Λ →₀ ℂ) :
    Finsupp.linearCombination ℂ (K.P z) c ∈ Fil (K.X z).A ↔ ∀ a, hol _ c a + K.ζ z (T.U.e a) * ahol _ c a = 0 := by
  rw [mem_Fil_iff (K.U z hz).u (H.2.1 ℂ (K.X z).A _ (K.X z).ab (K.X z).dim).1
    (exists_lie_comb (K.U z hz).u (K.P z) _ (K.lie z hz) c), funext_iff]
  refine forall_congr' fun a ↦ Eq.congr_left ?_
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.star_apply,
    RCLike.star_def, mul_add, Finset.sum_add_distrib, mul_left_comm _ (K.ζ z _), ← Finset.mul_sum]

theorem period_eq (H : GlobalTheory.Published.AbelianDeRham) (K : Coord ε G) {z : I → ℂ} (hz : z ∈ K.V) {c d : T.U.u.Λ →₀ ℂ} {r : ℂ}
    (h : ∀ a, hol _ c a + K.ζ z (T.U.e a) * ahol _ c a = r * (hol _ d a + K.ζ z (T.U.e a) * ahol _ d a))
    {ω : primDR G.X.A} (hω : ω ∈ PrimitiveSubmodule G.X.A) : period K c ω z = r * period K d ω z := by
  have e := (mem_Fil_fibre H K hz (c - r • d)).2 fun a ↦ by
    simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination h a
  have e' := (Submodule.mem_dualAnnihilator _).1 e ((K.mor z).pull ω) ((K.mor z).isMor.pullback1_mem_hodgeFiltration hω)
  rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at e'
  exact sub_eq_zero.1 e'

theorem exists_period_ne_zero (H : GlobalTheory.Published.AbelianDeRham) (K : Coord ε G) {z : I → ℂ} (hz : z ∈ K.V) {c : T.U.u.Λ →₀ ℂ}
    {a : Fin (Module.finrank ℚ (FR E))} (h : hol _ c a + K.ζ z (T.U.e a) * ahol _ c a ≠ 0) :
    ∃ ω ∈ PrimitiveSubmodule G.X.A, period K c ω z ≠ 0 := by
  by_contra hh
  push_neg at hh
  refine h ((mem_Fil_fibre H K hz c).1 ?_ a)
  letI : Algebra G.B ℂ := (G.y z : G.B →+* ℂ).toAlgebra
  have e := (H.2.2.1 G.B G.X.A _ G.X.ab G.X.dim ℂ (K.X z).A (K.q z) (K.pull z).grp).2
  refine (Submodule.mem_dualAnnihilator _).2 fun w hw ↦ ?_
  rw [e] at hw
  refine (Submodule.span_le (p := LinearMap.ker (Finsupp.linearCombination ℂ (K.P z) c))).2 ?_ hw
  rintro _ ⟨ω, hω, rfl⟩
  exact hh ω hω

theorem hasJet_period (hC : JetCalc) (K : Coord ε G) (hb : Y.mor.IsBC)
    (m' : GrpMor (dp0 G.B) (𝟙 _) G.X.A (dp0 J.B) (𝟙 _) Y.X'.A (G.j : G.B →+* J.B) (spMap (G.j : G.B →+* J.B)) G.q)
    (c : T.U.u.Λ →₀ ℂ) (ω : primDR G.X.A) : HasJet J (period K c ω)
      (crysToDR J.κ Y.pull.grp (hb.bcMap (Finsupp.linearCombination ℂ K.P₀ c)) (m'.pull ω)) := by
  induction c using Finsupp.induction_linear with
  | zero =>
    have e : period K 0 ω = fun _ ↦ 0 := funext fun z ↦ by simp only [period, map_zero, LinearMap.zero_apply]
    simpa only [e, map_zero, LinearMap.zero_apply] using hasJet_const (J := J) 0
  | add c d hc hd =>
    have e : period K (c + d) ω = fun z ↦ period K c ω z + period K d ω z :=
      funext fun z ↦ by simp only [period, map_add, LinearMap.add_apply]
    simpa only [e, map_add, LinearMap.add_apply] using hc.add hC hd
  | single x r =>
    have e : period K (Finsupp.single x r) ω = fun z ↦ r * K.P z x ((K.mor z).pull ω) :=
      funext fun z ↦ by simp only [period, Finsupp.linearCombination_single, LinearMap.smul_apply, smul_eq_mul]
    rw [e, Finsupp.linearCombination_single, LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact (hasJet_const r).mul hC ⟨SCV.analyticAt_of_differentiableOn (K.P_hol x ω) (K.isOpen.mem_nhds K.zero),
      (K.horiz m' x _ (hb.corr_iff.2 rfl) ω).symm⟩

end Main

theorem jetZeta : GlobalTheory.Published.AbelianDeRham → JetCalc → JetZeta := by
  intro H hC
  refine ⟨1, ?_⟩
  intro ε E _ _ _ I _ 𝔠 φ c y hφ hc n T J Y G K i
  rw [_root_.one_mul]
  obtain ⟨a, a1, a2⟩ := exists_comb _ T.U.u.full (Pi.single (T.U.e.symm i) 1)
  obtain ⟨b, b1, b2⟩ := exists_comb_anti _ T.U.u.full (Pi.single (T.U.e.symm i) 1)
  obtain ⟨d, d1, d2, hd⟩ := low_anti H hφ hc T K.per i b1 b2
  have hV := K.isOpen.mem_nhds K.zero
  have m' : GrpMor (dp0 G.B) (𝟙 _) G.X.A (dp0 J.B) (𝟙 _) Y.X'.A (G.j : G.B →+* J.B) (spMap (G.j : G.B →+* J.B)) G.q :=
    GrpMor.of_isGrpPullback (isDPMorphism_of_eq_bot _ rfl _ _) ((Category.comp_id _).trans (Category.id_comp _).symm) G.pull.grp
  have hb := isBC H T.X Y.mor
  obtain ⟨ω, hω, h0⟩ := exists_period_ne_zero H K K.zero (c := a) (a := T.U.e.symm i) (by simp [a1, a2])
  have hζ : AnalyticAt ℂ (fun z ↦ K.ζ z i) 0 := SCV.analyticAt_of_differentiableOn (differentiableOn_pi.1 K.ζ_hol i) hV
  have ja := hasJet_period hC K hb m' a ω
  have jb := hasJet_period hC K hb m' b ω
  have jd := hasJet_period hC K hb m' d ω
  have eb : period K b ω =ᶠ[𝓝 0] fun z ↦ K.ζ z i * period K a ω z := Filter.eventually_of_mem hV fun z hz ↦
    period_eq H K hz (fun m ↦ by
      by_cases hm : m = T.U.e.symm i
      · simp [a1, a2, b1, b2, hm]
      · simp [a1, a2, b1, b2, hm]) hω
  have ed : period K d ω =ᶠ[𝓝 0] fun z ↦ -(((ε : ℤ) : ℂ) * T.A i) * period K a ω z := Filter.eventually_of_mem hV fun z hz ↦
    period_eq H K hz (fun m ↦ by
      by_cases hm : m = T.U.e.symm i
      · simp [a1, a2, d1, d2, hm]
      · simp [a1, a2, d1, d2, hm]) hω
  have fb := jb.2.symm.trans ((Check.jet_congr J eb).trans (HasJet.mul hC ⟨hζ, rfl⟩ ⟨ja.1, rfl⟩).2)
  have fd := jd.2.symm.trans ((Check.jet_congr J ed).trans (HasJet.mul hC (hasJet_const _) ⟨ja.1, rfl⟩).2)
  have hF : Finsupp.linearCombination ℂ K.P₀ b ∈ Fil T.X.A :=
    (mem_Fil_iff T.U.u (H.2.1 ℂ T.X.A _ T.X.ab T.X.dim).1 (exists_lie_comb T.U.u K.P₀ _ K.per.2.2.1 b)).2 b1
  have hJ : IsJetElt J T.X T.low Y.mor (Finsupp.linearCombination ℂ K.P₀ b)
      (hb.bcMap (Finsupp.linearCombination ℂ K.P₀ b) + J.t i • hb.bcMap (Finsupp.linearCombination ℂ K.P₀ d)) := fun cc ↦ by
    rw [LinearMap.add_apply, LinearMap.smul_apply, hb.corr_iff.2 rfl cc, hb.corr_iff.2 rfl cc, Finset.sum_eq_single i, hd,
      if_pos rfl, smul_eq_mul]
    · intro k _ hk
      rw [hd, if_neg hk, LinearMap.zero_apply, map_zero, mul_zero]
    · exact fun h ↦ (h (Finset.mem_univ i)).elim
  have hz := (Submodule.mem_dualAnnihilator _).1 (Y.fil _ hF _ hJ) (m'.pull ω) (m'.isMor.pullback1_mem_hodgeFiltration hω)
  rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, fb, fd, smul_eq_mul, map_neg] at hz
  refine (isUnit_jet hC J ja.1 h0).mul_right_cancel ?_
  rw [Algebra.smul_def]
  linear_combination hz

end GlobalTheory.LatJet.An.ZetaNonvanishing₂
