import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCptGenResidueFieldGenericStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsReferenceGeometrySameGenericStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsHolomorphicSectionOfAnalytic
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsEffectiveWeightSectionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EffectiveScaledWeightOfRetractionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginGoodPrimesFiniteStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCoordsOverFieldStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointsFiniteNonemptyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TopTower

theorem comp_data (hG : Top.Given) (hA0 : Flat.FlatLineGenerator) (hA1 : Flat.FlatLineGeneratorComponent)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l)
    (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F))
    (hgl : Top.IsGlobal Xo l c Y) (hsp : SplitComps Y) (hp : 1 ≤ D.p) (hq : 1 ≤ D.q)
    (x : Y.X) (hx : ∀ x' : Y.X, x' ⤳ x → x' = x) :
    ∃ (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys)
      (R : Top.RootModel (CMType H) (D.p + D.q)) (o : RootOrigin Y ∅ R Fx),
      genPt Fx.ξf = x ∧
      (∀ r : RootIx D, (Fx.n r : ℝ) = ((Fx.kA * Fx.q' : ℕ) : ℝ) * (-((r.2 : ℕ) : ℝ))) ∧
      o.Fl.deg = 1 ∧ o.Re.J = ⊤ ∧ Ht.AmpleQ R.y R.A.a ∧
      Cmp.IsEmbedded o.Re.R.A R.P o.Re.R.U o.Re.R.lift ∧ Function.Bijective o.Re.π ∧
      (∀ τ (i : Fin (D.p + D.q)), (i : ℕ) + 1 = D.p + D.q → ∀ t,
        ReciprocityTheory.AnForm.M.IsPsh Sys.A ((Sys.potT (some (τ, i)) t).rsmul (-1)) ∧
          ReciprocityTheory.AnForm.M.IsPsh Sys.A (Sys.potT (some (τ, i)) t)) ∧
      (∀ x : Sys.X, ∃ (U : Set Sys.X) (lam : Sys.X → Fin (Fx.m + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
        (∀ i, Sys.A.HoloOn U fun y => lam y i) ∧ (∀ y ∈ U, ∃ a₀ : ℂ, a₀ ≠ 0 ∧ lam y = a₀ • Fx.pt y) ∧
        ∀ p, lam x p ≠ 0 → ∀ j, x ∈ (Sys.A.chart j).source →
          (fderiv ℂ (fun z i => lam ((Sys.A.chart j).symm z) i / lam ((Sys.A.chart j).symm z) p)
            (Sys.A.chart j x)).ker = ⊥) := by
  have hdom : ∀ x, IsDomain (Y.X.presheaf.stalk x) := fun x => (Y.normal x).1
  have hcg := GlobalTheory.T.isCptGen_residue_field_generic Y.X hdom x hx
  obtain ⟨G, hG0⟩ := GlobalTheory.T.exists_reference_geometry_same_generic hG.2.2.2.2.1 E H D l (Xo l) c Y _ (Y.X.fromSpecResidueField x) hcg
  obtain ⟨A, hinv⟩ := GlobalTheory.T.exists_holomorphic_section_of_analytic hG hA0 hA1 E H D Xo l c Y hgl hsp hp hq G
  let ν : RootIx D → ℤ := fun r => -((r.2 : ℕ) : ℤ)
  have hν : ∀ τ (i k : Fin (D.p + D.q)), i < k → ν (τ, k) < ν (τ, i) := by
    intro τ i k hik
    simp only [ν, neg_lt_neg_iff]
    exact_mod_cast hik
  obtain ⟨k, q', s, hk, hq', hs, heff⟩ := GlobalTheory.T.exists_effective_weight_section hG E H D Xo l c Y hgl hp hq G ⟨A⟩ ν hν
  obtain ⟨Fx, R, o, hgen, hkA, hq'', hn, hdeg, hJ, hamp, hemb, hbij, hlam⟩ :=
    GlobalTheory.T.effective_scaled_weight_of_retraction E H D l (Xo l) c Y G A ν k q' s hinv hsp hk hq' hs heff
  refine ⟨A.Sys, Fx, R, o, ?_, ?_, hdeg, hJ, hamp, hemb, hbij, A.flat, hlam⟩
  · rw [hgen, hG0]
    exact Scheme.fromSpecResidueField_apply x _
  · intro r
    rw [hn r, hkA, hq'']
    simp [ν]

theorem level_data (hG : Top.Given) (hW : Out.WeilSt)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
    {Xo : Moduli D l} {c : Coeff l} (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    {Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))} (Fx : FixedData Y Sys)
    (R : Top.RootModel (CMType H) (D.p + D.q)) (o : RootOrigin Y ∅ R Fx)
    (hdeg : o.Fl.deg = 1) (hemb : Cmp.IsEmbedded o.Re.R.A R.P o.Re.R.U o.Re.R.lift)
    (hbij : Function.Bijective o.Re.π)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hdisc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S) :
    ∃ (RM : Top.RootModel (CMType H) (D.p + D.q)) (o' : RootOrigin Y S RM Fx), o'.𝔐.OmVB ∧
      (∀ p ∈ S, o'.𝔐.R p = 4) ∧ o'.Re.J = ⊤ ∧ ∃ _ : Algebra ℚ RM.Ω, SmoothGenericFibreM RM.y := by
  obtain ⟨Ω, _, _, K, _, J, _, y, bk, bx, i, 𝔐, h, Fl, xdeg, e, hbk, hy, hd, hf, hcst, hfl, hfin, hlines,
    hom, hsm, hR⟩ := GlobalTheory.T.root_origin_good_primes_finite hG hW E H D l Xo c Y Sys Fx R o S hS hdisc hdeg
  obtain ⟨RM, o', h1, h2, h3, h4⟩ := GlobalTheory.T.root_origin_coords_over_field hG E H D l Xo c Y Sys Fx R o S Ω K J y bk bx i 𝔐 h Fl
    xdeg e hdeg hemb hbij hbk hy hd hf hcst hfl hfin hlines hom hsm
  refine ⟨RM, o', h1, fun p hp => ?_, h3, h4⟩
  rw [h2]
  exact hR p hp

theorem exists_good_tower : Top.Given → Out.WeilSt → Flat.FlatLineGenerator → Flat.FlatLineGeneratorComponent → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)], Top.IsGlobal Xo l c Y → SplitComps Y → 1 ≤ D.p → 1 ≤ D.q → ∃ (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T), (∀ a, (∀ x : (o.Sys a).X, ∃ (U : Set (o.Sys a).X) (lam : (o.Sys a).X → Fin ((o.Fx a).m + 1) → ℂ), IsOpen U ∧ x ∈ U ∧ (∀ i, (o.Sys a).A.HoloOn U fun y => lam y i) ∧ (∀ y ∈ U, ∃ a₀ : ℂ, a₀ ≠ 0 ∧ lam y = a₀ • (o.Fx a).pt y) ∧ ∀ p, lam x p ≠ 0 → ∀ j, x ∈ ((o.Sys a).A.chart j).source → (fderiv ℂ (fun z i => lam (((o.Sys a).A.chart j).symm z) i / lam (((o.Sys a).A.chart j).symm z) p) ((o.Sys a).A.chart j x)).ker = ⊥)) ∧ ∀ B a, ∀ p ∈ o.S B, (o.Or B a).𝔐.R p = 4 := by
  intro hG hW hA0 hA1 E _ _ _ H D Xo l c Y _ hgl hsp hp hq
  obtain ⟨hfin, hne⟩ := GlobalTheory.T.generic_points_finite_nonempty hG E H D l (Xo l) c Y
  let Smax : Set Y.X := {x : Y.X | ∀ x' : Y.X, x' ⤳ x → x' = x}
  haveI : Fintype Smax := Set.Finite.fintype hfin
  haveI : Nonempty Smax := hne.to_subtype
  choose Sys Fx R o hgen hnu hdeg hJ hamp hemb hbij hflat hlam using
    fun a : Smax => comp_data hG hA0 hA1 Xo l c Y hgl hsp hp hq a.1 a.2
  have hM' : l.M' ≠ 0 := by
    show Nat.lcm l.M l.A ≠ 0
    exact Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
  have hn0 : 2 * (discr E).natAbs * l.M' ≠ 0 := by
    exact Nat.mul_ne_zero (Nat.mul_ne_zero two_ne_zero (Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero E))) hM'
  let bad : Finset ℕ := (2 * (discr E).natAbs * l.M').primeFactors
  have hbad : ∀ r : ℕ, r ∈ bad ↔ r.Prime ∧ (r : ℤ) ∣ 2 * discr E * l.M' := by
    intro r
    simp only [bad, Nat.mem_primeFactors, Int.natCast_dvd, Int.natAbs_mul]
    simp [hn0]
  let SB : ℕ → Finset ℕ := fun B => (Finset.range (B + 1)).filter Nat.Prime ∪ bad
  have hSB : ∀ B r, r ∈ SB B ↔ r.Prime ∧ (r ≤ B ∨ r ∈ bad) := by
    intro B r
    simp only [SB, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro (⟨h1, h2⟩ | h)
      · exact ⟨h2, Or.inl (by omega)⟩
      · exact ⟨((hbad r).1 h).1, Or.inr h⟩
    · rintro ⟨h1, h2 | h2⟩
      · exact Or.inl ⟨by omega, h1⟩
      · exact Or.inr h2
  have hSBp : ∀ B, ∀ p ∈ SB B, p.Prime := fun B p hp => ((hSB B p).1 hp).1
  have hSBd : ∀ B, ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ SB B := by
    intro B p hp hd
    refine (hSB B p).2 ⟨hp, Or.inr ((hbad p).2 ⟨hp, ?_⟩)⟩
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left hd 2) _
  choose RM o' hom hR hJ' hsm using fun (B : ℕ) (a : Smax) =>
    level_data hG hW Y (Fx a) (R a) (o a) (hdeg a) (hemb a) (hbij a) (SB B) (hSBp B) (hSBd B)
  let T : Top.RootTower (CMType H) (D.p + D.q) :=
    { j := D.p
      j_pos := hp
      j_lt := by omega
      Comp := Smax
      bad := bad
      two_mem := (hbad 2).2 ⟨Nat.prime_two, Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_refl _) _) _⟩
      nu := fun _ i => -((i : ℕ) : ℝ)
      nu_rat := fun _ i => ⟨-((i : ℕ) : ℚ), by push_cast; rfl⟩
      M := RM }
  let tor : TowerOrigin Y T :=
    { j_eq := rfl
      bad_iff := hbad
      S := SB
      S_iff := hSB
      Sys := Sys
      Fx := Fx
      comp_inj := fun a a' h => Subtype.ext (by rw [← hgen a, ← hgen a']; exact h)
      comp_onto := fun x hx => ⟨⟨x, hx⟩, hgen _⟩
      nu_eq := fun a r => hnu a r
      Or := o' }
  let go : Top.GoodOrigin Y T :=
    { toTowerOrigin := tor
      omVB := hom
      smooth := fun B a => ⟨hJ' B a, hsm B a⟩
      flat := hflat
      R := R
      refOr := o
      ref_deg := hdeg
      ref_top := hJ
      ample := hamp }
  exact ⟨T, go, fun a => hlam a, fun B a p hp => hR B a p hp⟩

end GlobalTheory.CompanionTheory.Ar.TopTower
