import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasPRatio
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsSMulRegularNatCast
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperToroidalModelStructureMap

import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DividesOfNormBoundedPointsStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLine.Overlap

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem exists_chart_gen (Z : Mdl Y i₀) (y : Z.Pt) :
    ∃ (a : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* ↥y.C.S), spMap φ ≫ Z.chart a = y.gen := by
  obtain ⟨pt⟩ : Nonempty (Sp ↥y.C.S) := inferInstance
  have e : y.gen ≫ Z.π = y.P.y ≫ (Y Z.i).j := by
    rw [Mdl.Pt.gen, Category.assoc, y.z_π, y.P.ext]
  have hpt : y.gen pt ∈ Z.opn := by
    change Z.π (y.gen pt) ∈ Set.range (Y Z.i).j
    refine ⟨y.P.y pt, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← e, Scheme.Hom.comp_apply]
  rw [← Z.cover] at hpt
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hpt
  obtain ⟨φ, hφ⟩ := Pull.exists_fromSpec (Z.U a).2 y.gen (fun q _ => by
    rw [Subsingleton.elim q pt]; exact ha)
  exact ⟨a, φ, hφ⟩

theorem valF_res {F : Type} [Field F] {X : Scheme.{0}} {x : Sp F ⟶ X} {U V : X.Opens} (e : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (a : Γ(X, U)) : valF x V ((X.presheaf.map (homOfLE e).op).hom a) = valF x U a := by
  have h' : ⊤ ≤ x ⁻¹ᵁ U := fun q hq => e (h hq)
  rw [valF, valF, dif_pos h, dif_pos h', ← Scheme.Hom.map_appLE x h (homOfLE e).op]
  rfl

theorem valF_pow_natCast {F : Type} [Field F] {X : Scheme.{0}} {x : Sp F ⟶ X} {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U)
    (n : ℕ) : valF x U ((p : Γ(X, U)) ^ n) = (p : F) ^ n := by
  rw [valF, dif_pos h, map_pow, map_pow, map_natCast, map_natCast]

theorem exists_pow_of_rad {X : Scheme.{0}} {U : X.Opens} {C : Γ(X, U)}
    (h : (p : Γ(X, U)) ∈ (Ideal.span (Set.range ![C])).radical) : ∃ (n : ℕ) (c : Γ(X, U)), c * C = (p : Γ(X, U)) ^ n := by
  obtain ⟨n, hn⟩ := h
  rw [show Set.range ![C] = {C} by simp] at hn
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
  exact ⟨n, c, hc⟩

theorem valF_ne_zero (hp : p ≠ 0) {F : Type} [Field F] [CharZero F] {X : Scheme.{0}} {x : Sp F ⟶ X} {U : X.Opens}
    (h : ⊤ ≤ x ⁻¹ᵁ U) {C c : Γ(X, U)} {n : ℕ} (hc : c * C = (p : Γ(X, U)) ^ n) : valF x U C ≠ 0 := by
  intro h0
  have := congrArg (valF x U) hc
  rw [Pull.valF_mul h, h0, mul_zero, valF_pow_natCast h] at this
  exact pow_ne_zero n (Nat.cast_ne_zero.2 hp) this.symm

theorem ratioAt_overlap_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Z : Mdl Y i₀) st (V V' : Z.X.Opens) (A B : Γ(Z.X, V)) (A' B' : Γ(Z.X, V')), IsAffineOpen (V ⊓ V') → RatioAt Z st V ![A] ![B] → RatioAt Z st V' ![A'] ![B'] → ∃ u : Γ(Z.X, V ⊓ V')ˣ, u.val * ((Z.X.presheaf.map (homOfLE (inf_le_right : V ⊓ V' ≤ V')).op).hom A' * (Z.X.presheaf.map (homOfLE (inf_le_left : V ⊓ V' ≤ V)).op).hom B) = (Z.X.presheaf.map (homOfLE (inf_le_right : V ⊓ V' ≤ V')).op).hom B' * (Z.X.presheaf.map (homOfLE (inf_le_left : V ⊓ V' ≤ V)).op).hom A := by
  intro E _ _ _ H Dw Xo p W Y i₀ hp hW Z st V V' A B A' B' hI hR hR'
  have hp0 : p ≠ 0 := hp.ne_zero
  obtain ⟨nA, cA, hA⟩ := exists_pow_of_rad hR.1
  obtain ⟨nB, cB, hB⟩ := exists_pow_of_rad hR.2.1
  obtain ⟨nA', cA', hA'⟩ := exists_pow_of_rad hR'.1
  obtain ⟨nB', cB', hB'⟩ := exists_pow_of_rad hR'.2.1
  set rl := (Z.X.presheaf.map (homOfLE (inf_le_left : V ⊓ V' ≤ V)).op).hom with hrl
  set rr := (Z.X.presheaf.map (homOfLE (inf_le_right : V ⊓ V' ≤ V')).op).hom with hrr
  have rA : rl cA * rl A = (p : Γ(Z.X, V ⊓ V')) ^ nA := by rw [← map_mul, hA, map_pow, map_natCast]
  have rB : rl cB * rl B = (p : Γ(Z.X, V ⊓ V')) ^ nB := by rw [← map_mul, hB, map_pow, map_natCast]
  have rA' : rr cA' * rr A' = (p : Γ(Z.X, V ⊓ V')) ^ nA' := by rw [← map_mul, hA', map_pow, map_natCast]
  have rB' : rr cB' * rr B' = (p : Γ(Z.X, V ⊓ V')) ^ nB' := by rw [← map_mul, hB', map_pow, map_natCast]
  obtain ⟨a, ha⟩ : ∃ a, rl A * rr B' = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, rr A' * rl B = b := ⟨_, rfl⟩
  have pa : (rl cA * rr cB') * a = (p : Γ(Z.X, V ⊓ V')) ^ (nA + nB') := by
    rw [← ha, pow_add, ← rA, ← rB']; ring
  have pb : (rr cA' * rl cB) * b = (p : Γ(Z.X, V ⊓ V')) ^ (nA' + nB) := by
    rw [← hb, pow_add, ← rA', ← rB]; ring
  have rada : (p : Γ(Z.X, V ⊓ V')) ∈ (Ideal.span {a}).radical :=
    ⟨_, Ideal.mem_span_singleton'.2 ⟨_, pa⟩⟩
  have radb : (p : Γ(Z.X, V ⊓ V')) ∈ (Ideal.span {b}).radical :=
    ⟨_, Ideal.mem_span_singleton'.2 ⟨_, pb⟩⟩
  have norms : ∀ y : Z.Pt, ⊤ ≤ y.z ⁻¹ᵁ (V ⊓ V') → ‖valF y.gen (V ⊓ V') a‖ = ‖valF y.gen (V ⊓ V') b‖ := by
    intro y hy
    obtain ⟨a₀, φ, hφ⟩ := exists_chart_gen Z y
    have hV : ⊤ ≤ y.z ⁻¹ᵁ V := fun q hq => (hy hq).1
    have hV' : ⊤ ≤ y.z ⁻¹ᵁ V' := fun q hq => (hy hq).2
    have g : ⊤ ≤ y.gen ⁻¹ᵁ (V ⊓ V') := fun q _ => hy (Set.mem_univ (spMap (intO ↥y.C.S).subtype q))
    have gV : ⊤ ≤ y.gen ⁻¹ᵁ V := fun q _ => hV (Set.mem_univ (spMap (intO ↥y.C.S).subtype q))
    have gV' : ⊤ ≤ y.gen ⁻¹ᵁ V' := fun q _ => hV' (Set.mem_univ (spMap (intO ↥y.C.S).subtype q))
    have e := (hR.2.2 y a₀ φ hφ hV).symm.trans (hR'.2.2 y a₀ φ hφ hV')
    simp only [Matrix.cons_val_fin_one, pi_norm_const, pi_norm_const'] at e
    have n1 := norm_pos_iff.2 (valF_ne_zero hp0 gV hA)
    have n2 := norm_pos_iff.2 (valF_ne_zero hp0 gV hB)
    have n3 := norm_pos_iff.2 (valF_ne_zero hp0 gV' hA')
    have n4 := norm_pos_iff.2 (valF_ne_zero hp0 gV' hB')
    rw [← ha, ← hb, Pull.valF_mul g, Pull.valF_mul g, valF_res _ g, valF_res _ g, valF_res _ g, valF_res _ g,
      norm_mul, norm_mul, ← Real.exp_log (mul_pos n1 n4), ← Real.exp_log (mul_pos n3 n2),
      Real.log_mul n1.ne' n4.ne', Real.log_mul n3.ne' n2.ne']
    congr 1
    linarith
  have hba : b ∣ a := GlobalTheory.T.divides_of_norm_bounded_points E H Dw Xo p W Y i₀ hp hW Z (V ⊓ V') hI a b radb fun y hy => (norms y hy).le
  have hab : a ∣ b := GlobalTheory.T.divides_of_norm_bounded_points E H Dw Xo p W Y i₀ hp hW Z (V ⊓ V') hI b a rada fun y hy => (norms y hy).ge
  obtain ⟨c, hc⟩ := hba
  obtain ⟨d, hd⟩ := hab
  have hdc : d * c = 1 := by
    have h0 : ((p ^ (nA + nB') : ℕ) : Γ(Z.X, V ⊓ V')) * (d * c - 1) = 0 := by
      rw [Nat.cast_pow, ← pa]
      linear_combination -(rl cA * rr cB') * hc - (rl cA * rr cB') * c * hd
    exact sub_eq_zero.1 (Z.isSMulRegular_natCast hI (pow_ne_zero _ hp0) h0)
  refine ⟨⟨c, d, by rw [mul_comm]; exact hdc, hdc⟩, ?_⟩
  change c * (rr A' * rl B) = rr B' * rl A
  rw [hb, mul_comm, ← hc, ← ha, mul_comm]

end GlobalTheory.HTLine.Overlap
