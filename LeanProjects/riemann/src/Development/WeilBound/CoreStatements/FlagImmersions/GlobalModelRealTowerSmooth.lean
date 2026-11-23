import Mathlib
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeLatticeFlagBound
import Development.AutomorphicSpectrum.Statements.GeometryStatements.TrivFlagOnHodge
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.WeilBound.CoreStatements.FlagImmersions.GeoNumOneLinear
import Development.WeilBound.CoreStatements.FlagImmersions.InvNatCastMem
import Development.WeilBound.CoreStatements.FlagImmersions.ExistsResDegree
import Development.WeilBound.CoreStatements.FlagImmersions.ValNeOfIntegral
import Development.WeilBound.CoreStatements.FlagImmersions.VertCloseStep
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HasReferenceOfSandwichAllPrimes
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSandwichOfHodgeTateFreeStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerM1NefStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationPullbackCompatibleStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCoordArithOfFnField

noncomputable section

namespace RootFieldNumerics.Ref

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Chg Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm blockFnField)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar.Top

theorem mem_ptsOver {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)}
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : z ∈ Small.ptsOver ℂ P :=
  ⟨hz.1, fun f hf => by
    have := hz.2 f hf
    rwa [MvPolynomial.eval_map, ← algebraMap_int_eq, ← aeval_def] at this⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} [DecidableEq (CMType H)]
  {Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))} {Fx : FixedData Y Sys}
  {S : Finset ℕ} {M R : RootModel (CMType H) (D.p + D.q)}

theorem level (hRes : ResExistsStatement) (II : IntersectionSystem) (hII : IsFullIntersectionSystem II)
    (o : RootOrigin Y S M Fx) (o₀ : RootOrigin Y ∅ R Fx) {i : R.Ω →+* M.Ω} (hi : i.comp o₀.g = o.g)
    (hJ : o.Re.J = ⊤) (hJ₀ : o₀.Re.J = ⊤) (hdeg : o₀.Fl.deg = 1)
    (hloc : ∀ x : Sys.X, ∃ (U : Set Sys.X) (lam : Sys.X → Fin (Fx.m + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      (∀ j, Sys.A.HoloOn U fun y => lam y j) ∧ ∀ y ∈ U, ∃ a₀ : ℂ, a₀ ≠ 0 ∧ lam y = a₀ • Fx.pt y)
    {e L : ℕ} (s : Fin L → R.Ω) (hs : ∀ j, s j ∈ chartLatNm R.y (fun k => e * R.A.a k - 1) 1)
    (hs' : ∀ z ∈ Small.ptsOver ℂ (mCoordIdeal R.y),
      ∃ (j : Fin L) (val : ℂ), val ≠ 0 ∧ Small.HasVal R.y (fun k => e * R.A.a k - 1) (s j) z val)
    (n : ℕ) (hn : ∀ a k, -(o₀.Re.ref a).a k ≤ n)
    (hnef : ∀ p ∈ S, ∀ mu : Wt (CMType H) (D.p + D.q), Dominant mu → M.NefAt p mu 0)
    {q m : ℕ} (hq : 0 < q) (hm : 0 < m) (hmS : ∀ p : ℕ, p.Prime → p ∣ m → p ∈ S)
    (hval : ∀ (r : RootIx D) (cM : (k : M.K) → M.ι k) (cR : (k : R.K) → R.ι k) (W : ValuationSubring M.Ω),
          (∀ k, M.y ⟨k, cM k⟩ ≠ 0) → (∀ k, R.y ⟨k, cR k⟩ ≠ 0) → (∀ k j, M.y ⟨k, j⟩ / M.y ⟨k, cM k⟩ ∈ W) →
          (∀ k j, i (R.y ⟨k, j⟩ / R.y ⟨k, cR k⟩) ∈ W) →
          (m : M.Ω) * (i ((∏ k, R.y ⟨k, cR k⟩ ^ R.xdeg r k) * o₀.e r) /
            ((∏ k, M.y ⟨k, cM k⟩ ^ M.xdeg r k) * o.e r)) ^ q ∈ W ∧
          (m : M.Ω) * (((∏ k, M.y ⟨k, cM k⟩ ^ M.xdeg r k) * o.e r) /
            i ((∏ k, R.y ⟨k, cR k⟩ ^ R.xdeg r k) * o₀.e r)) ^ q ∈ W) :
    ∃ (K : Type) (_ : Fintype K) (ι : K → Type) (_ : ∀ k, Fintype (ι k)) (P : Ideal (MRing ι))
      (Re Re' : PB.Realis Sys P) (Hl : HermLine ι),
      Re.PB II = o.Re.PB II ∧ Re'.PB II = o₀.Re.PB II ∧ Re'.deg = Re.deg ∧ IsSmoothHerm Hl ∧
      PB.SamePot Re.R.A Set.univ (potOf Re.R Hl) (((Sys.th none).rsmul ((n : ℝ) * e)).pullback Re.π Re.holo.1) ∧
      (∀ a t, 0 < t → t ≤ Sys.t₀ → PB.VertClose P S (fun p => (padicValNat p (m ^ (D.p + D.q)) : ℝ) / q)
        (Re.line a t) (Re'.line a t)) ∧
      (∀ p ∈ S, PB.NefAt P p Hl.a ∧ ∀ a, PB.NefAt P p ((Re.ref a).a + Hl.a) ∧ PB.NefAt P p ((Re'.ref a).a + Hl.a)) := by
  classical
  haveI : CharZero M.Ω := Sandwich.charZero_of_hodgeCpt o.𝔐
  haveI : CharZero R.Ω := Sandwich.charZero_of_hodgeCpt o₀.𝔐
  let K : Type := (M.K ⊕ R.K) ⊕ Unit
  let ι : K → Type := Cmp.joinIdx (Cmp.joinIdx M.ι R.ι) fun _ : Unit => Fin L
  let y : (Σ k, ι k) → M.Ω := Cmp.joinVec (Ht.joinOf M R i) fun p => i (s p.2)
  let κ : M.K → K := fun k => Sum.inl (Sum.inl k)
  let κ₀ : R.K → K := fun k => Sum.inl (Sum.inr k)
  let v : (Σ k, M.ι k) → Σ k, ι k := blkV (J := ι) κ fun k => Equiv.refl _
  let v₀ : (Σ k, R.ι k) → Σ k, ι k := blkV (J := ι) κ₀ fun k => Equiv.refl _
  have hv : IsBlockMap κ v := isBlockMap_blkV _ (Sum.inl_injective.comp Sum.inl_injective)
  have hv₀ : IsBlockMap κ₀ v₀ := isBlockMap_blkV _ (Sum.inl_injective.comp Sum.inr_injective)
  have hy : ∀ p, y (v p) = M.y p := fun _ => rfl
  have hy₀ : ∀ p, y (v₀ p) = i (R.y p) := fun _ => rfl
  have hB : Birational y := birational_of_block hv hy M.birational
  have hne : ∀ k, ∃ a, y ⟨k, a⟩ ≠ 0 := by
    rintro ((k | k) | k)
    · exact ne_zero_of_arith M.arith k
    · obtain ⟨a, ha⟩ := ne_zero_of_arith R.arith k
      exact ⟨a, (map_ne_zero i).2 ha⟩
    · obtain ⟨z, hz, -⟩ := GroundTheory.Heights₂.Heights.HilbertSamuel.exists_mcPts_not_mem_mcPts o₀.Re.arith o₀.Re.R.nondeg
      obtain ⟨j, val, hval0, dg, dh, g, h, hg, -, -, e1, e2, e3⟩ := hs' z (mem_ptsOver hz)
      refine ⟨j, (map_ne_zero i).2 fun h0 => ?_⟩
      have h0' : s j = 0 := h0
      rw [h0', zero_mul] at e1
      have := (mem_ptsOver hz).2 g (GroundTheory.Heights₂.Heights.LowerBoundFree.mem_mCoordIdeal_of_aeval_eq_zero R.y hg e1)
      rw [this] at e3
      exact mul_ne_zero hval0 e2 e3.symm
  have top : ∀ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]
      (y : (Σ k, ι k) → Ω), (∀ k, ∃ a, y ⟨k, a⟩ ≠ 0) → Birational y → blockFnField y = ⊤ := by
    intro K _ ι _ Ω _ _ y h hB
    choose c hc using h
    exact GenFib.blockFnField_eq_top y c hc hB
  have tM := top M.y (ne_zero_of_arith M.arith) M.birational
  have tR := top R.y (ne_zero_of_arith R.arith) R.birational
  have ty := top y hne hB
  have hA : IsArithVar (mCoordIdeal y) (dimFl (CMType H) (D.p + D.q) + 1) :=
    GroundTheory.Heights₂.Heights.HilbertSamuel.CoordArithOfFnField.proof M.K M.ι K ι M.Ω M.y y _ ⟨Sum.inr ()⟩ hne
      (tM.trans ty.symm) M.arith
  have hfin : letI := o.g.toAlgebra; 0 < Module.finrank Fx.Ωf M.Ω := by
    have := o.g_deg
    rw [this, ← o.Re_deg]
    exact o.Re.deg_pos
  obtain ⟨J, R', h, br, hh, ho, hπ, hd⟩ := exists_res_degree hRes M.y y hv hy M.arith hA M.birational hB hJ o.Re.R Sys.A
    o.Re.π o.Re.holo o.Re.deg_pos o.Re.degree Fx.yf Fx.generate o.g hfin o.k₀ o.ix o.y_eq Fx.pt o.π_pt hloc
  have him : imageZ v (mCoordIdeal y) = M.P := imageZ_restr (RingHom.id _) hv hy
  have him₀ : imageZ v₀ (mCoordIdeal y) = R.P := imageZ_restr i hv₀ hy₀
  obtain ⟨h₀, hh₀, ho₀⟩ := exists_resProj hJ₀ o₀.Re.R R' hv₀ him₀.ge
  have eπ : o.Re.π ∘ h = o₀.Re.π ∘ h₀ := funext fun x =>
    pi_agree o o₀ hi hv hv₀ hy hy₀ (R'.mem x x (R'.mem_U x)) _ _ (ho x) (ho₀ x)
  let Re := pullRealis o.Re hA hv R' h hh ho _ hπ rfl _ o.Re.deg_pos br hd
  let Re' := pullRealis o₀.Re hA hv₀ R' h₀ hh₀ ho₀ _ hπ eπ _ o.Re.deg_pos br hd
  obtain ⟨Hl, hHs, hHa, hHp⟩ := exists_line R.y y i hv₀ hy₀ hA R.A R.A_smooth s hs hs' (Sum.inr ())
    (by rintro ⟨k, hk⟩; cases hk) (Equiv.refl _) (fun _ => rfl) n
  have hH0 : ∀ k, (n : ℤ) * pullDeg κ₀ 1 k ≤ Hl.a k := fun k => by
    rw [hHa]
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, mul_add, le_add_iff_nonneg_right]
    refine mul_nonneg (Nat.cast_nonneg _) ?_
    rw [Pi.single_apply]
    split_ifs <;> simp
  have hH1 : ∀ k, 0 ≤ Hl.a k := fun k =>
    (mul_nonneg (Nat.cast_nonneg _) (pullDeg_nonneg hv₀.1 (fun _ => zero_le_one) k)).trans (hH0 k)
  refine ⟨K, inferInstance, ι, inferInstance, mCoordIdeal y, Re, Re', Hl, ?_, ?_, rfl, hHs, ?_, ?_, ?_⟩
  · refine GlobalTheory.T.realisation_pullback_compatible II hII M.K M.ι _ _ Sys M.P o.Re K ι M.Ω y Sys Re κ v hv him
      (Eventually.of_forall fun t a => ⟨rfl, fun _ => rfl⟩) ?_
    have : y ∘ v = M.y := funext hy
    rw [this, tM, ty, IntermediateField.relfinrank_self, one_mul]
    rfl
  · refine GlobalTheory.T.realisation_pullback_compatible II hII R.K R.ι _ _ Sys R.P o₀.Re K ι M.Ω y Sys Re' κ₀ v₀ hv₀ him₀
      (Eventually.of_forall fun t a => ⟨rfl, fun _ => rfl⟩) ?_
    rw [relfinrank_restr i hy₀ tR ty, o₀.Re_deg, hdeg, mul_one]
    have h1 := finrank_comp' o₀.g i
    rw [hi] at h1
    have h2 := o.g_deg
    have h3 := o₀.g_deg
    rw [h2, h3, hdeg, one_mul] at h1
    exact o.Re_deg.trans h1
  · refine samePot_trans_rsmul _ (hHp J R') (Re'.ref_pot none) fun x => ?_
    filter_upwards [(R'.isOpen_U x).mem_nhds (R'.mem_U x)] with w hw
    show Real.log (R.A.h fun p => R'.lift x w (v₀ p)) = Real.log ((o₀.Re.ref none).h fun p => R'.lift x w (v₀ p))
    rw [o₀.ref_none.2 _ (mem_mcPts_restr hv₀ him₀.ge (R'.mem x w hw))]
  · rintro (_ | r) t h0 h1
    · exact vertClose_none o o₀ hi hv hv₀ hy hy₀ hA hJ hJ₀ S _ (fun p => by positivity) h0 h1
    · exact vertClose_some o o₀ hi hv hv₀ hy hy₀ hA hJ hJ₀ hdeg hq hm hmS hval r h0 h1
  · intro p hp
    refine ⟨nefAt_of_nonneg _ _ hH1, fun a => ⟨nefAt_add ?_ (nefAt_of_nonneg _ _ hH1), nefAt_of_nonneg _ _ fun k => ?_⟩⟩
    · refine nefAt_pull hv him.ge (o.𝔐.S_prime p hp) ?_
      rcases a with _ | ⟨τ, j⟩
      · refine nefAt_of_nonneg _ _ fun k => ?_
        rw [o.ref_none.1]
        by_cases hk : k = o.k₀
        · rw [hk, o.A_deg.1]
          exact zero_le_one
        · rw [o.A_deg.2 k hk]
      · rw [o.fund_deg]
        exact nefAt_step M p (hnef p hp) τ j
    · have h1 := pullDeg_add_nonneg hv₀.1 (hn a) k
      have h2 := hH0 k
      show 0 ≤ pullDeg κ₀ (o₀.Re.ref a).a k + Hl.a k
      linarith

end RootFieldNumerics.Ref

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

open RootFieldNumerics.Ref in
theorem RootFieldNumerics.global_model_real_tower_smooth : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → (realOf o.toTowerOrigin).RefLinked II := by
  intro hG E _ _ _ _ H D Xo l c Y _ T o II hY hX hII hp hq
  have hFar : HT.FarguesHodgeTate := hG.2.2.2.2.2.2.1
  have hRes : ResExistsStatement := hG.2.2.2.2.2.2.2.2.2.1.resExists
  have hM1 := GlobalTheory.T.good_tower_M1_nef hG E H D Xo l c Y T o II hY hII hp hq
  choose C₀ hC₀ using fun a => val_bound E H D l (Xo l) c Y (o.Sys a) (o.Fx a) (o.R a) (o.refOr a)
  choose e L s hs hs' using o.ample
  have hn : ∀ a, ∃ n : ℕ, ∀ b k, -((o.refOr a).Re.ref b).a k ≤ n := fun a => by
    obtain ⟨x, hx⟩ := (Set.finite_range fun p : Option (RootIx D) × (o.R a).K =>
      (-((o.refOr a).Re.ref p.1).a p.2).toNat).bddAbove
    exact ⟨x, fun b k => (Int.self_le_toNat _).trans (by exact_mod_cast hx ⟨(b, k), rfl⟩)⟩
  choose n hn using hn
  obtain ⟨C₃, hC₃⟩ := OrRef.sum_bound o.toTowerOrigin
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C₁ : ℝ := ∑ a, |C₀ a| with hC₁
  have hC₁0 : 0 ≤ C₁ := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hC₁a : ∀ a, C₀ a ≤ C₁ := fun a => (le_abs_self _).trans
    (Finset.single_le_sum (f := fun a => |C₀ a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a))
  refine ⟨(D.p + D.q : ℕ) * (C₁ / Real.log 2 + C₃), fun a => ((o.Sys a).th none).rsmul ((n a : ℝ) * e a),
    fun a => (o.refOr a).Re.PBs II, fun a => ReciprocityTheory.AnForm.M.isPotentialRsmul _ _ _ ((o.Sys a).sing none).1,
    fun B hB a => ?_⟩
  obtain ⟨i, hi⟩ := OrRef.exists_comparison (o.refOr a) (o.ref_deg a) (o.Or B a)
  have hSp : ∀ p ∈ o.S B, p.Prime := (o.Or B a).𝔐.S_prime
  have hdisc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ o.S B := by
    intro p hp hd
    refine (o.S_iff B p).mpr ⟨hp, Or.inr ((o.bad_iff p).mpr ⟨hp, ?_⟩)⟩
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left hd 2) _
  have hsand : ∀ p ∈ o.S B, ∃ κ, HT.IsCp p κ ∧ HT.Sandwich (o.Or B a).𝔐 p κ := fun p hpS => by
    haveI : Fact p.Prime := ⟨hSp p hpS⟩
    exact GlobalTheory.T.exists_sandwich_of_hodge_tate_free hFar E H D l (Xo l) c _ _ Y _ _ _ _ _ (o.Or B a).𝔐 p hpS (by omega) (o.omVB B a p hpS)
  obtain ⟨q, m, hq0, hm0, hmS, hlog, hval⟩ := hC₀ a (o.S B) (T.M B a) (o.Or B a) i hi hdisc hsand
  obtain ⟨K, _, ι, _, P, Re, Re', Hl, h1, h2, h3, h4, h5, h6, h7⟩ := level hRes II hII (o.Or B a) (o.refOr a) hi
    (o.smooth B a).1 (o.ref_top a) (o.ref_deg a)
    (fun x => by
      obtain ⟨U, lam, a1, a2, a3, a4, -⟩ := hX.1 a x
      exact ⟨U, lam, a1, a2, a3, a4⟩)
    (s a) (hs a) (hs' a ℂ) (n a) (hn a) (fun p hpS => hM1 B a p ((o.S_iff B p).1 hpS)) hq0 hm0 hmS hval
  refine ⟨K, inferInstance, ι, inferInstance, P, Re, Re', o.S B, _, Hl, congrArg PB.toWtS h1, congrArg PB.toWtS h2, h3,
    fun p hpS => ⟨hSp p hpS, by positivity⟩, h4, h5, h6, h7, ?_⟩
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq0
  have e1 : ∑ p ∈ o.S B, (padicValNat p (m ^ (D.p + D.q)) : ℝ) / q * Real.log p =
      (∑ p ∈ o.S B, (padicValNat p (m ^ (D.p + D.q)) : ℝ) * Real.log p) / q := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun p _ => by ring
  have e2 := sum_padicValNat_log hSp (pow_pos hm0 (D.p + D.q))
  rw [Nat.cast_pow, Real.log_pow] at e2
  have hlB : Real.log 2 ≤ Real.log B := Real.log_le_log (by norm_num) (by exact_mod_cast hB)
  have h₄ : C₁ ≤ C₁ / Real.log 2 * Real.log B := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
    exact mul_le_mul_of_nonneg_left hlB hC₁0
  have h₅ : ∑ p ∈ o.S B, (if p = 2 then 2 else 1 / ((p : ℝ) - 1)) * Real.log p ≤ C₃ * Real.log B := by
    refine le_trans (Finset.sum_le_sum fun p _ => ?_) (hC₃ B hB)
    have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    have hv : (0 : ℝ) ≤ 2 * padicValInt p (discr E) := by positivity
    nlinarith [mul_nonneg hv hl]
  have h₆ : Real.log m ≤ q * ((C₁ / Real.log 2 + C₃) * Real.log B) := by
    refine hlog.trans (mul_le_mul_of_nonneg_left ?_ hq'.le)
    have := hC₁a a
    nlinarith
  rw [e1, div_le_iff₀ hq']
  refine e2.trans ?_
  have := mul_le_mul_of_nonneg_left h₆ (Nat.cast_nonneg (D.p + D.q) : (0 : ℝ) ≤ _)
  refine this.trans (le_of_eq ?_)
  ring
