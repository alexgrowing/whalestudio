import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsFormOfEqRatioPowMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationLtOneOfInvNotMem

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM

namespace GlobalTheory.ShFam.Pad.AdmTest

def finiteCoverTwistingSheaf (R : Type) [CommRing R] (N : ℕ) : FinLB (PSpace R N) :=
  ⟨N + 1, (GlobalTheory.ProjSpace.O1 R N).U, (GlobalTheory.ProjSpace.O1 R N).g, GlobalTheory.ProjSpace.O1_isLB R N⟩

theorem finiteTwisting_lineBundle (R : Type) [CommRing R] (N : ℕ) : (finiteCoverTwistingSheaf R N).lb = GlobalTheory.ProjSpace.O1 R N := rfl

theorem finiteTwisting_not_isGenerator (R : Type) [CommRing R] [Nontrivial R] (N : ℕ) (t : (finiteCoverTwistingSheaf R (N + 1)).lb.Gen) : ¬ t.IsGen :=
  GlobalTheory.ProjSpace.Model.not_isGen_O1 t

section Place

variable {D : D7} {p : ℕ} [Fact p.Prime] {la : PlL D p} {jc : DV.KW p →+* ℂ}

theorem placeW_spec (h : JcPin D p la jc) :
    (∀ x : D.what₂.LL, D.what₂.embLL x ∈ placeW D p la jc ↔ la.1.valuation D.what₂.LL x ≤ 1) ∧
    ∀ a : DV.KW p, jc a ∈ placeW D p la jc ↔
      a ∈ (algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p)).range :=
  Classical.epsilon_spec h

theorem placeW_nonunit (h : JcPin D p la jc) : (p : ℂ) ∈ (placeW D p la jc).nonunits := by
  have hp : (p : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have h1 : la.1.valuation D.what₂.LL (p : D.what₂.LL) < 1 := by
    have := (la.1.valuation_lt_one_iff_mem (K := D.what₂.LL) (p : 𝓞 D.what₂.LL)).2 la.2
    simpa using this
  have h2 : ¬ la.1.valuation D.what₂.LL (p : D.what₂.LL)⁻¹ ≤ 1 := by
    rw [map_inv₀, not_le]
    exact (one_lt_inv₀ (zero_lt_iff.2 ((map_ne_zero _).2 hp))).2 h1
  have h3 := mt ((placeW_spec h).1 (p : D.what₂.LL)⁻¹).1 h2
  rw [map_inv₀, map_natCast] at h3
  rw [ValuationSubring.mem_nonunits_iff_or]
  exact Or.inr h3

theorem exists_placeW_nonunit (D : D7) (p : ℕ) [Fact p.Prime] (la : PlL D p) :
    ∃ jc : DV.KW p →+* ℂ, JcPin D p la jc ∧ (p : ℂ) ∈ (placeW D p la jc).nonunits := by
  obtain ⟨jc, h⟩ := GlobalTheory.WittFracPlace.exists_jcPin D p la
  exact ⟨jc, h, placeW_nonunit h⟩

end Place

theorem valF_unit_ne {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)ˣ) : valF x U f.val ≠ 0 := by
  rw [valF, dif_pos h]
  exact ((f.isUnit.map _).map _).ne_zero

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem gen_mem {Z : Mdl Y i₀} (y : Z.Pt) (a : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* ↥y.C.S)
    (hφ : spMap φ ≫ Z.chart a = y.gen) {V : Z.X.Opens} (hV : ⊤ ≤ y.z ⁻¹ᵁ V) :
    ⊤ ≤ y.gen ⁻¹ᵁ ((Z.U a).1 ⊓ V) := by
  intro x _
  refine ⟨?_, ?_⟩
  · rw [← hφ]
    have : (Z.chart a) ((spMap φ) x) ∈ Set.range (Z.U a).2.fromSpec := ⟨_, rfl⟩
    exact (IsAffineOpen.range_fromSpec (Z.U a).2).le this
  · exact hV (x := (spMap (Formalism.MainNotions.DIV.Cons.intO ↥y.C.S).subtype) x) trivial

theorem norm_r {Z : Mdl Y i₀} {b : Bool} {st : ((E →+* ℂ) × ℕ) ⊕ ℕ} {x : Letter Dw} (M : LineModel Z b st x)
    (y : Z.Pt) (a : Fin Z.m) (i : Fin M.L.n) (φ : Γ(Z.X, (Z.U a).1) →+* ↥y.C.S)
    (hφ : spMap φ ≫ Z.chart a = y.gen) (hi : ⊤ ≤ y.z ⁻¹ᵁ M.L.U i) :
    ‖valF y.gen _ (M.r a i).val‖ = Real.exp (- lnStep (Y Z.i).t (y.gen ≫ Z.π) ((Z.fr a).bc φ) p b st) := by
  have h := M.norm y a i φ hφ hi
  have h0 := norm_pos_iff.2 (valF_unit_ne y.gen _ (gen_mem y a φ hφ hi) (M.r a i))
  rw [← Real.exp_log h0]
  congr 1
  linarith

theorem norm_r_eq {Z : Mdl Y i₀} {b : Bool} {st : ((E →+* ℂ) × ℕ) ⊕ ℕ} {x : Letter Dw} (M M' : LineModel Z b st x)
    (y : Z.Pt) (a : Fin Z.m) (i : Fin M.L.n) (i' : Fin M'.L.n) (φ : Γ(Z.X, (Z.U a).1) →+* ↥y.C.S)
    (hφ : spMap φ ≫ Z.chart a = y.gen) (hi : ⊤ ≤ y.z ⁻¹ᵁ M.L.U i) (hi' : ⊤ ≤ y.z ⁻¹ᵁ M'.L.U i') :
    ‖valF y.gen _ (M.r a i).val‖ = ‖valF y.gen _ (M'.r a i').val‖ :=
  (norm_r M y a i φ hφ hi).trans (norm_r M' y a i' φ hφ hi').symm

theorem exists_member {Z : Mdl Y i₀} (L : FinLB Z.X) (y : Z.Pt) : ∃ i, ⊤ ≤ y.z ⁻¹ᵁ L.U i := by
  have : IsLocalRing ↥(Formalism.MainNotions.DIV.Cons.intO ↥y.C.S) := by
    refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
    have key : ∀ c : ↥(Formalism.MainNotions.DIV.Cons.intO ↥y.C.S), ‖(c : ↥y.C.S)‖ = 1 → IsUnit c := fun c hc => by
      have h0 : (c : ↥y.C.S) ≠ 0 := by intro h; simp [h] at hc
      refine IsUnit.of_mul_eq_one ⟨(c : ↥y.C.S)⁻¹, ?_⟩ (Subtype.ext (mul_inv_cancel₀ h0))
      change ‖(c : ↥y.C.S)⁻¹‖ ≤ 1
      rw [norm_inv, hc, inv_one]
    have ha : ‖(a : ↥y.C.S)‖ ≤ 1 := a.2
    rcases ha.eq_or_lt with h | h
    · exact Or.inl (key a h)
    · refine Or.inr (key _ ?_)
      have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := (1 : ↥y.C.S)) (y := -(a : ↥y.C.S))
        (by rw [norm_one, norm_neg]; exact h.ne')
      rw [norm_one, norm_neg, max_eq_left h.le, ← sub_eq_add_neg] at this
      simpa using this
  have hc : y.z (IsLocalRing.closedPoint ↥(Formalism.MainNotions.DIV.Cons.intO ↥y.C.S)) ∈ (⨆ i, L.U i : Z.X.Opens) := by
    have := L.isLB.cover
    change ⨆ i, L.U i = ⊤ at this
    rw [this]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
  exact ⟨i, (Scheme.preimage_eq_top_of_closedPoint_mem y.z hi).ge⟩

theorem n_eq (hp : p.Prime) (z z' : admitted Y i₀) (h : z.Z.i.l.A = z'.Z.i.l.A) : z.n = z'.n := by
  have := z.lvl.2.2.symm.trans (h.trans z'.lvl.2.2)
  exact Nat.pow_right_injective hp.two_le (Nat.eq_of_mul_eq_mul_left i₀.l.A_pos this)

theorem letterOf_inl (x : Letter Dw) : letterOf Dw (.inl (x.1, x.2)) = some x := by
  simp [letterOf]

theorem exponent_three (p : ℕ) (hp : p.Prime) : 1 + 1 / ((p : ℝ) - 1) < (3 : ℕ) := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have : 1 / ((p : ℝ) - 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  push_cast; linarith

theorem exponent_two : ¬ (1 + 1 / (((2 : ℕ) : ℝ) - 1) < (2 : ℕ)) := by norm_num

end GlobalTheory.ShFam.Pad.AdmTest
