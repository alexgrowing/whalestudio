import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaChangeOfRepRootOfUnityOfChartIndependence
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixDetNotMem
import Formalism.LocalToGlobal.ProjectiveLattices.ThClass
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm

section Point

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory.Phase.ChangePt

theorem move_at_point : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (q0 n : ℕ) (hr : X.p0 + q0 = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ q0 X.p0 (Fin n)), IsSympl X bas → r = Dw.p + Dw.q → Even n → (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) → (∀ j, rowType X (idx j) = Formalism.L2.PjFree.relab c (algebraMap c.F ℂ) (e j).1) → ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (Λ : GenLat E n) (h : Matrix (Fin n) (Fin n) E), Λ.Unimod → IsUnitaryM h → Λ.TrivAt l.M → (actLat h Λ).TrivAt l.M → ∃ t : ℂ, ‖t‖ = 1 ∧ ∀ (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (_ : AnFib X bas idx e x L y), x ∈ X.dom → SelfD X L → ∀ (wq wq' : (Fin n → LevQ Dw l) → c.F), (∀ q q', LevMoves h q q' → wq' q' = wq q) → ∀ N N' : ℕ, Λ.LevOK N l.M → (actLat h Λ).LevOK N' l.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ), ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∀ (b b' : c.F) (v v' : ℂ), b ≠ 0 → b' ≠ 0 → ShortValAt Xo c nab wq Λ b N P y v → ShortValAt Xo c nab wq' (actLat h Λ) b' N' (pushLet c h P) y v' → ((actLat h Λ).Ln.toAddSubgroup.addSubgroupOf (actLat h Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) ≠ 0 ∧ v' * algebraMap c.F ℂ b' * (Real.sqrt (((Λ).Ln.toAddSubgroup.addSubgroupOf (Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) : ℕ) : ℝ) = t * algebraMap c.F ℂ b * (Real.sqrt (((actLat h Λ).Ln.toAddSubgroup.addSubgroupOf (actLat h Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) : ℕ) : ℝ) * v := by
  intro hci E _ _ _ H Dw l Xo c _ r g X bas idx e q0 n hr eL hs hrr hn hdir hty _ nab hnab Λ h hU hh hT hT'
  have hw := cmHost_idempotent_trace_eq_one H
  have hwi : IsIntegral ℤ (H.w0 : E) := H.w0.isIntegral_coe
  obtain ⟨hU', hmv, hu, -⟩ := (GlobalTheory.T.pushforward_preserves_harmonic_polynomials_and_lattices E H Dw l c n 0 h hh).2 Λ
  have hΛ := mem_vset Λ l.three_le hU hT
  have hΛ' := mem_vset (actLat h Λ) l.three_le (hU' hU) hT'
  have hΛ1 : Λ.La ∈ Vset E n 1 := (GenLatCmp.genLat_vset E n _).2.2.1 1 _ (one_dvd _) hΛ
  have hΛ1' : (actLat h Λ).La ∈ Vset E n 1 := (GenLatCmp.genLat_vset E n _).2.2.1 1 _ (one_dvd _) hΛ'
  obtain ⟨t, ht, hvac⟩ := thA_vacuum_hAct E r X g bas idx n hs hn _ hwi hw h hu _ hΛ1 _ hΛ1' hmv
  refine ⟨t, ht, fun x L y A hx hL => ?_⟩
  obtain ⟨⟨v₀, hv₀⟩, -⟩ := TensVac.vacua E r X g bas idx n hs hn _ hwi hw L hL 1 _ (Base.stdL_mem_Vset n 1)
  have hcol := hvac L hL v₀ hv₀ x hx
  intro wq wq' hwq N N' hN hN' a P hP b b' v v' hb hb' hv hv'
  obtain ⟨θ, hθ, -⟩ := (reads_existsUnique_theta E H Dw l Xo c r g X bas idx e x L y A hs hx hL 1 y.s).1
  have hθ1 := isTheta1_of_reads_generator E H Dw l Xo c r g X bas idx e x L y A hs hx hL θ hθ
  obtain ⟨κ, hκ⟩ := VacProd.prod_eq_mul_thA E r X g bas idx n hs hn _ hwi hw L hL v₀ hv₀ x hx θ hθ1
  obtain ⟨mk, hmk, hA⟩ := exists_mark E H Dw l Xo c r g X bas idx e x L y A hs hx hL
  have hroots := (DualMark.dual_marking E H Dw l r X L mk _ hL hmk
    (Complex.isPrimitiveRoot_exp _ l.odd.pos.ne')).2.2.2.2 n
  obtain ⟨Y, hY⟩ := hroots N hN.1.pos
  obtain ⟨Y', hY'⟩ := hroots N' hN'.1.pos
  have e1 := GlobalTheory.T.shortThetaValue_complexPoint_eq_classicalTheta hci E H Dw l Xo c r g X bas idx e x L y A hs hx hL q0 n hr eL hrr hn hdir nab hnab
    θ v₀ κ hθ hv₀ hκ mk hmk hA Λ.La hΛ N hN Y hY a P hP wq b v hv
  have e2 := GlobalTheory.T.shortThetaValue_complexPoint_eq_classicalTheta hci E H Dw l Xo c r g X bas idx e x L y A hs hx hL q0 n hr eL hrr hn hdir nab hnab
    θ v₀ κ hθ hv₀ hκ mk hmk hA (actLat h Λ).La hΛ' N' hN' Y' hY' a _
    ((GlobalTheory.T.pushforward_preserves_harmonic_polynomials_and_lattices E H Dw l c n a h hh).1 P hP) wq' b' v' hv'
  obtain ⟨_, -, hproj⟩ := GlobalTheory.T.heisenbergVacuum_projection_rootOfUnity_phases E r X g bas idx n hs hn _ hwi hw L hL v₀ hv₀
  obtain ⟨hu1, -, hp1⟩ := hproj _ hΛ1
  obtain ⟨hu2, -, hp2⟩ := hproj _ hΛ1'
  obtain ⟨⟨σ, hσ⟩, hmove⟩ := GlobalTheory.T.roots_levelPoints_same_vacuum_translates E H Dw l r X g bas n hs hn L hL mk hmk h hu _ hΛ _ hΛ' hmv N N' hN hN'
    Y Y' hY hY'
  obtain ⟨-, -, -, hz1, -⟩ := ZLat.exists_reps_sum E r X g bas idx n hs hn _ hwi hw L hL _ hΛ1 N hN.1
    (hN.2.2.trans inf_le_left)
  obtain ⟨-, -, -, hz2, -⟩ := ZLat.exists_reps_sum E r X g bas idx n hs hn _ hwi hw L hL _ hΛ1' N' hN'.1
    (hN'.2.2.trans inf_le_left)
  haveI := finite_levQ Dw l
  haveI := Fintype.ofFinite (Fin n → LevQ Dw l)
  generalize unitv (projA X bas (H.w0 : E) (tens Λ.La L) v₀) = u at hcol hu1 hp1
  generalize unitv (projA X bas (H.w0 : E) (tens (actLat h Λ).La L) v₀) = u' at hcol hu2 hp2
  rw [gphi, hp1, theta_finsum hr idx hs hn hx _ _ _ hu1.1] at e1
  rw [gphi, hp2, theta_finsum hr idx hs hn hx _ _ _ hu2.1] at e2
  have hsum : ∑ q, algebraMap c.F ℂ (wq' q) * thP X hr bas idx (heisG X bas (Y' q) u')
        (MvPolynomial.rename eL (MvPolynomial.map (algebraMap c.F ℂ) (pushLet c h P))) x =
      t * ∑ q, algebraMap c.F ℂ (wq q) * thP X hr bas idx (heisG X bas (Y q) u)
        (MvPolynomial.rename eL (MvPolynomial.map (algebraMap c.F ℂ) P)) x := by
    rw [← σ.sum_comp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hsb := ((heisG_laws E r X g bas idx n hs hn).2.2.2 (Y q) u hu1.1).1
    have hsb' := ((heisG_laws E r X g bas idx n hs hn).2.2.2 (h * Y q) u' hu2.1).1
    have han := (theta_holomorphic_weight E r X g q0 hr bas idx n hs hn 0 0 _ hsb' 0 (zero_mem _)).2.2.2 x hx
    rw [hwq q _ (hσ q), hmove q _ (hσ q) u' hu2, thP, thP,
      GlobalTheory.T.polyDeriv_letter_pushforward_eq_column_action E H Dw l c _ r g X idx e q0 n hr eL hdir hty h P _ han,
      funext (thA_heisG_hAct E r X g bas idx n hs hn h hu u u' hu1.1 hu2.1 t x hx hcol (Y q)),
      mul_left_comm t, ← Jet.polyDeriv_smul_fun _ _ (ThetaHol.differentiable_thA idx hs hsb hx)]
    rfl
  rw [hsum] at e2
  simp only [map_mul, map_inv₀, map_natCast] at e1 e2
  have hb0 : algebraMap c.F ℂ b ≠ 0 := (map_ne_zero _).2 hb
  have hb0' : algebraMap c.F ℂ b' ≠ 0 := (map_ne_zero _).2 hb'
  refine ⟨?_, ?_⟩
  · rw [index_Ln, ← hrr]
    exact (Nat.pos_of_mul_pos_left (lt_of_lt_of_eq hz2 (zCard_eq _ hN' r))).ne'
  rw [index_Ln, index_Ln, ← hrr, e2, cancel_idx hb0' hz2 (zCard_eq _ hN' r), mul_right_comm _ _ v,
    _root_.mul_assoc t, _root_.mul_comm _ v, e1, cancel_idx hb0 hz1 (zCard_eq _ hN r)]
  ring

end GlobalTheory.Phase.ChangePt

namespace GlobalTheory.DatumMove

theorem move_complex (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ]
    [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab) (n : ℕ) (hn : Even n)
    (hfib : ∃ (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r)
      (e : Fin g ≃ Lt1 Dw) (hr : X.p0 + Dw.p = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ Dw.p X.p0 (Fin n)),
      IsSympl X bas ∧ r = Dw.p + Dw.q ∧
      (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) ∧
      (∀ j, rowType X (idx j) = Formalism.L2.PjFree.relab c (algebraMap c.F ℂ) (e j).1) ∧
      ∀ y : FrPt Xo c ℂ, ∃ (y₀ : FrPt Xo c ℂ) (t : Ix Dw → ℂˣ) (x : Frame X.Ψ r) (L : Lt E r),
        FrBor t y₀ y ∧ x ∈ X.dom ∧ SelfD X L ∧ Nonempty (AnFib X bas idx e x L y₀))
    (Λ : GenLat E n) (h : Matrix (Fin n) (Fin n) E) (hU : Λ.Unimod) (hh : IsUnitaryM h)
    (hT : Λ.TrivAt l.M) (hT' : (actLat h Λ).TrivAt l.M) (w w' : (Fin n → LevQ Dw l) → c.F)
    (hw : ∀ q q', LevMoves h q q' → w' q' = w q) (N N' : ℕ) (hN : Λ.LevOK N l.M)
    (hN' : (actLat h Λ).LevOK N' l.M) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (hPa : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) :
    ∃ z : ℂ, ∀ (y : FrPt Xo c ℂ) (v v' : ℂ), ShortValAt Xo c nab w Λ 1 N P y v →
        ShortValAt Xo c nab w' (actLat h Λ) 1 N' (pushLet c h P) y v' → v = z * v' := by
  have hC := GlobalTheory.chartIndependence_unconditional
  obtain ⟨r, g, X, bas, idx, e, hr, eL, hS, hr', hL, hrow, hy⟩ := hfib
  have hLaws : Out.Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨t, ht1, ht⟩ := GlobalTheory.Phase.ChangePt.move_at_point hC E H Dw l Xo c r g X bas idx e Dw.p n hr eL hS hr' hn hL
    hrow nab hnab Λ h hU hh hT hT'
  have hP := (GlobalTheory.PushKeeps.push_keeps E H Dw l c n a h hh).1 P hPa
  have hΛ := ((GlobalTheory.PushKeeps.push_keeps E H Dw l c n 0 h hh).2 Λ).1 hU
  set A := ((Λ).Ln.toAddSubgroup.addSubgroupOf (Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) with hAdef
  set A' := ((actLat h Λ).Ln.toAddSubgroup.addSubgroupOf (actLat h Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q)
    with hA'def
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht1
  refine ⟨((Real.sqrt (A : ℝ) : ℝ) : ℂ) / (t * ((Real.sqrt (A' : ℝ) : ℝ) : ℂ)), fun y v v' hv hv' => ?_⟩
  obtain ⟨y₀, t₀, x, L, hB, hx, hSD, ⟨F⟩⟩ := hy y
  have ex1 := (GlobalTheory.shortThetaValue_existsUnique_natural hLaws hC E H Dw l Xo c nab hnab n Λ N hU hT hN a P hPa
    w 1).1 ℂ
  have ex2 := (GlobalTheory.shortThetaValue_existsUnique_natural hLaws hC E H Dw l Xo c nab hnab n (actLat h Λ) N' hΛ hT' hN'
    a _ hP w' 1).1 ℂ
  obtain ⟨u, hu, -⟩ := ex1 y₀
  obtain ⟨u', hu', -⟩ := ex2 y₀
  have k1 := (ex1 y).unique hv
    ((GlobalTheory.thetaValue_weight hLaws hC E H Dw l Xo c nab hnab ℂ y₀ y t₀ hB n a P).2 hPa w Λ 1 N u hu)
  have k2 := (ex2 y).unique hv'
    ((GlobalTheory.thetaValue_weight hLaws hC E H Dw l Xo c nab hnab ℂ y₀ y t₀ hB n a _).2 hP w' _ 1 N' u' hu')
  obtain ⟨hA', k3⟩ := ht x L y₀ F hx hSD w w' hw N N' hN hN' a P hPa 1 1 u u' one_ne_zero one_ne_zero hu hu'
  have hsq : ((Real.sqrt (A' : ℝ) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hA'))).ne'
  have k4 : u = ((Real.sqrt (A : ℝ) : ℝ) : ℂ) / (t * ((Real.sqrt (A' : ℝ) : ℝ) : ℂ)) * u' := by
    rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero ht0 hsq)]
    simp only [map_one, _root_.mul_one] at k3
    linear_combination -k3
  rw [k1, k2, k4]; ring

theorem exists_move_const (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l)
    [StarRing (𝓞 E)] (nab : NabV Xo c) (h1 : 1 ≤ Dw.p + Dw.q) (hnab : IsNab Xo c nab) (n : ℕ) (hn : Even n)
    (Λ : GenLat E n) (h : Matrix (Fin n) (Fin n) E) (hU : Λ.Unimod) (hh : IsUnitaryM h)
    (hT : Λ.TrivAt l.M) (hT' : (actLat h Λ).TrivAt l.M) (w w' : (Fin n → LevQ Dw l) → c.F)
    (hw : ∀ q q', LevMoves h q q' → w' q' = w q) (N N' : ℕ) (hN : Λ.LevOK N l.M)
    (hN' : (actLat h Λ).LevOK N' l.M) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (hPa : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) :
    ∃ z : c.F, ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S),
      ShortValAt Xo c nab w Λ 1 N P y v →
        ∃ v', ShortValAt Xo c nab w' (actLat h Λ) 1 N' (pushLet c h P) y v' ∧ v = algebraMap c.F S z * v' := by
  have hC := GlobalTheory.chartIndependence_unconditional
  have hLaws : Out.Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨s, hfib⟩ := GlobalTheory.Dict.exists_anFib_all_points E H Dw l Xo c h1 n hn
  obtain ⟨z, hid⟩ := @move_complex E _ _ _ H Dw l Xo c s.toAlgebra _ nab hnab n hn hfib
    Λ h hU hh hT hT' w w' hw N N' hN hN' a P hPa
  have hP := (GlobalTheory.PushKeeps.push_keeps E H Dw l c n a h hh).1 P hPa
  have hΛ := ((GlobalTheory.PushKeeps.push_keeps E H Dw l c n 0 h hh).2 Λ).1 hU
  have ex1 := GlobalTheory.shortThetaValue_existsUnique_natural hLaws hC E H Dw l Xo c nab hnab n Λ N hU hT hN a P hPa w 1
  have ex2 := GlobalTheory.shortThetaValue_existsUnique_natural hLaws hC E H Dw l Xo c nab hnab n (actLat h Λ) N' hΛ hT' hN'
    a _ hP w' 1
  choose u hu using fun (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) => (ex1.1 S y).exists
  choose u' hu' using fun (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) => (ex2.1 S y).exists
  have n1 : ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
      (y : FrPt Xo c S) (y' : FrPt Xo c T), FrMap φ y y' → φ (u S y) = u T y' :=
    fun S T _ _ _ _ φ y y' hy => ex1.2 S T φ y y' hy _ _ (hu S y) (hu T y')
  have n2 : ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
      (y : FrPt Xo c S) (y' : FrPt Xo c T), FrMap φ y y' → φ (u' S y) = u' T y' :=
    fun S T _ _ _ _ φ y y' hy => ex2.2 S T φ y y' hy _ _ (hu' S y) (hu' T y')
  have h : ∀ y : @FrPt E _ _ _ H Dw l Xo c ℂ _ s.toAlgebra,
      @u ℂ _ s.toAlgebra y = z * @u' ℂ _ s.toAlgebra y :=
    fun y => hid y _ _ (@hu ℂ _ s.toAlgebra y) (@hu' ℂ _ s.toAlgebra y)
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : c.F, ∀ y : @FrPt E _ _ _ H Dw l Xo c ℂ _ s.toAlgebra,
      @u ℂ _ s.toAlgebra y = s z₀ * @u' ℂ _ s.toAlgebra y := by
    by_cases h0 : ∀ y : @FrPt E _ _ _ H Dw l Xo c ℂ _ s.toAlgebra, @u' ℂ _ s.toAlgebra y = 0
    · refine ⟨1, fun y => ?_⟩
      rw [h y, h0 y, mul_zero, mul_zero]
    · simp only [not_forall] at h0
      obtain ⟨y, hy⟩ := h0
      obtain ⟨z₀, hz₀⟩ := @GlobalTheory.ConstRatio.ratio_mem_range E _ _ _ H Dw l Xo c ℂ _ _ s.toAlgebra
        (@u' ℂ _ s.toAlgebra) (@u ℂ _ s.toAlgebra)
        (@n2 ℂ ℂ _ s.toAlgebra _ s.toAlgebra) (@n1 ℂ ℂ _ s.toAlgebra _ s.toAlgebra) z h y hy
      have hz₀' : s z₀ = z := hz₀
      exact ⟨z₀, fun y => by rw [hz₀', h y]⟩
  have hfin := GlobalTheory.NaturalValues.eq_of_eq_complex E H Dw l Xo c s u (fun S _ _ y => algebraMap c.F S z₀ * u' S y) n1
    (fun S T _ _ _ _ φ y y' hyy => by rw [map_mul, φ.commutes, n2 S T φ y y' hyy]) hz₀
  refine ⟨z₀, fun S _ _ y v hv => ⟨u' S y, hu' S y, ?_⟩⟩
  rw [(ex1.1 S y).unique hv (hu S y)]
  exact hfin S y

end GlobalTheory.DatumMove

end Point

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DatumMove

set_option maxHeartbeats 1000000 in

theorem rawSeries_move_datum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → IsNab Xo c nab → ∀ (bad n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), 0 < bad → Dom a n → ∀ x0 x1 : Fin n → LevQc Dw l, Submodule.span (𝓞 E) (Set.range x0) = ⊤ → Submodule.span (𝓞 E) (Set.range x1) = ⊤ → {f : Formalism.L2.Pj.Rul Xo c | f ∈ sec Xo c a n ∧ ∃ (La : GenLat E n) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F), La.Unimod ∧ La.TrivAt bad ∧ La.TrivAt l.M ∧ La.LevOK N l.M ∧ P ∈ harmL c La a ∧ ∀ (p : TRing c.F) (y : FrPt Xo c p.R), thLaValAt Xo c nab (phiHat c (indPhi c x0)) La N P y (f p y)} ⊆ (Submodule.span c.F {f : Formalism.L2.Pj.Rul Xo c | f ∈ sec Xo c a n ∧ ∃ (La : GenLat E n) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F), La.Unimod ∧ La.TrivAt bad ∧ La.TrivAt l.M ∧ La.LevOK N l.M ∧ P ∈ harmL c La a ∧ ∀ (p : TRing c.F) (y : FrPt Xo c p.R), thLaValAt Xo c nab (phiHat c (indPhi c x1)) La N P y (f p y)} : Set (Formalism.L2.Pj.Rul Xo c)) := by
  intro E _ _ _ H Dw l Xo c _ nab h1 _ hnab bad n a hbad hdom x0 x1 hx0 hx1 f ⟨hf, Λ, N, P, hU, hT, hM, hN, hP, hv⟩
  obtain ⟨γ, hγ, hb, hm, hw⟩ := exists_unitary_moving c (bad := 2 * bad) (by omega) x0 x1 hx0 hx1
  have triv : ∀ d, d ∣ 2 * bad → (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.actLat γ ⟨stdLat E n⟩).TrivAt d := fun d hd => by
    obtain ⟨k, hk, h⟩ := hb
    exact ⟨k, hk.coprime_dvd_right hd, h⟩
  obtain ⟨N', hN'⟩ := exists_levOK (triv 2 (Dvd.intro _ rfl)) hN
  have hM' := trivAt_act hm hM
  obtain ⟨z, hz⟩ := exists_move_const E H Dw l Xo c nab h1 hnab n hdom.2 Λ γ hU hγ hM hM' _ _ hw N N' hN hN' a P hP.1
  obtain ⟨k1, -, -, k2⟩ := (GlobalTheory.PushKeeps.push_keeps E H Dw l c n a γ hγ).2 Λ
  by_cases hz0 : z = 0
  · have : f = 0 := by
      funext p y
      obtain ⟨v', -, e⟩ := hz p.R y _ (hv p y)
      rw [e, hz0, map_zero, zero_mul]
      rfl
    rw [this]
    exact Submodule.zero_mem _
  · have e : f = z • z⁻¹ • f := by
      funext p y
      change f p y = z • z⁻¹ • f p y
      rw [Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hz0, map_one, one_mul]
    rw [e]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨Submodule.smul_mem _ _ hf, _, N', _, k1 hU,
      trivAt_act (triv bad (Dvd.intro_left _ rfl)) hT, hM', hN', k2 P hP, fun p y => ?_⟩)
    obtain ⟨v', hv', e⟩ := hz p.R y _ (hv p y)
    have e2 : (z⁻¹ • f) p y = v' := by
      change z⁻¹ • f p y = v'
      rw [e, Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hz0, map_one, one_mul]
    rw [e2]
    exact hv'

end GlobalTheory.DatumMove
