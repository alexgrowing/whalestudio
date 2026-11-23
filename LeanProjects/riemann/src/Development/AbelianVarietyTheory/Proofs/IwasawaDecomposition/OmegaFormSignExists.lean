import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointSmulIntegralOfFourierCoeffNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinTensAlgebraMap
import Development.AbelianVarietyTheory.Definitions.Divisors.ConstantUniqueOfEqProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.FinDatum

theorem isRoots_sign {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {r n N : ℕ} {L : Lt E r} {mk : Dw.La →ₗ[𝓞 E] (Fin r → E)} (ε : ℤˣ) (hN : l.M ∣ N)
    {Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E} (h : IsRoots l L ((ε : ℤ) • mk) N Y) :
    IsRoots l L mk l.M fun q => (ε : ℤ) • Y q := by
  intro q b
  obtain ⟨⟨a, ha, h1, h2⟩, j, hj⟩ := h q b
  obtain ⟨m, rfl⟩ := hN
  refine ⟨⟨a, ha, h1, ?_⟩, j, fun s hs => ?_⟩
  · have h3 := zsmul_mem h2 (ε : ℤ)
    rw [smul_sub, LinearMap.smul_apply, smul_comm (l.M : E)⁻¹, smul_smul, ← Units.val_mul, Int.units_mul_self,
      Units.val_one, one_smul] at h3
    exact h3
  · obtain ⟨u, hu, e⟩ := hj s hs
    refine ⟨(ε : ℤ) • m • u, zsmul_mem (nsmul_mem hu m) _, ?_⟩
    show s • (ε : ℤ) • Y q b = _
    rw [smul_comm s, e, smul_comm (2 * l.M), smul_smul (2 * l.M), mul_assoc]

variable {D : D7}

theorem lat_iotaW (T : CoreJ D) (hT : LawsJ T) (i : Fin D.R.m) :
    LatEmb (Wc D i) (iotaW T i) ∧ LatIsom (Wc D i) (T.Q.Dw ((i : ℕ) + 1)).EF (iotaW T i) := by
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  obtain ⟨hr, g, e, F, ik, φ, th, h, h', -⟩ := hT.adPin _ hj _ T.toCore.good_σ₀
  have hV := hT.spaceW _ hj _ T.toCore.good_σ₀
  have key : ∀ (V : HSp D) (hr : V.rank = D.R.r), V = Wc D i →
      LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota ((i : ℕ) + 1)) →
      LatIsom V (T.Q.Dw ((i : ℕ) + 1)).EF
        (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota ((i : ℕ) + 1)) →
      LatEmb (Wc D i) (iotaW T i) ∧ LatIsom (Wc D i) (T.Q.Dw ((i : ℕ) + 1)).EF (iotaW T i) := by
    rintro V hr rfl h h'
    exact ⟨h, h'⟩
  exact key _ hr hV h h'

theorem latR_range {E : Type} [Field E] [NumberField E] {m r : ℕ} (hr : m = r) {La : Type} [AddCommGroup La]
    [Module (𝓞 E) La] (ι : La →ₗ[𝓞 E] (Fin r → E)) :
    GlobalTheory.AdTh.latR hr (LinearMap.range (LinearMap.funLeft (𝓞 E) E (Fin.cast hr) ∘ₗ ι)) = LinearMap.range ι := by
  subst hr
  unfold GlobalTheory.AdTh.latR
  rw [← LinearMap.range_comp]
  rfl

theorem splitOffBad_one (V : HSp D) : SplitOffBad V 0 1 := by
  refine ⟨one_mem _, 0, ∅, ⟨⟨fun _ => 0, fun _ h => absurd h (Finset.notMem_empty _), by simp⟩, zero_mul _⟩,
    fun _ h => absurd h (Finset.notMem_empty _), fun i j => ?_⟩
  rw [show Formalism.L2.Theta.mt V 1 = 1 from rfl, sub_self, Matrix.zero_apply, mul_zero]

theorem isFinOf_finR (S T : HSp D) {r : ℕ} (hr : T.rank = r) (y : Matrix (Fin S.rank) (Fin r) D.host.E) :
    GlobalTheory.AdTh.colsR hr (y.submatrix id (Fin.cast hr))ᵀ = y ∧
      GlobalTheory.AdTh.IsFinOf S T (y.submatrix id (Fin.cast hr))ᵀ (finR S hr y) := by
  subst hr
  exact ⟨rfl, (GlobalTheory.VacSign.isFinOf_iff _ _).2 rfl⟩

theorem mem_std_star (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) {n : ℕ} (v : Fin n → D.host.E)
    (h : v ∈ Formalism.L2.Pj.stdLat D.host.E n) : (fun j => star (v j)) ∈ Formalism.L2.Pj.stdLat D.host.E n := by
  intro j _
  obtain ⟨a, ha⟩ := Submodule.mem_one.1 (h j trivial)
  exact Submodule.mem_one.2 ⟨H.bar a, (H.bar_eq a).trans (congrArg star ha)⟩

theorem smul_eq_zero_of_smul_rep {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} (q : LevQ Dw l) (s : 𝓞 E) (z : Dw.La) (hz : s • (cSep l • levRep q) = l.M • z) :
    s • q = 0 := by
  have hrep : (Submodule.Quotient.mk (levRep q) : LevQ Dw l) = q :=
    Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)
  rw [← hrep, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  have hM : (l.M : 𝓞 E) ∈ l.Mb := Ideal.mul_le_left (l.prod.ge (Ideal.subset_span rfl))
  have e : s • levRep q = (l.M : 𝓞 E) • z - (cSep l - 1) • s • levRep q := by
    rw [Nat.cast_smul_eq_nsmul, ← hz, sub_smul, one_smul, smul_comm s, sub_sub_cancel]
  rw [e]
  exact sub_mem (Submodule.smul_mem_smul hM trivial) (Submodule.smul_mem_smul (LevelPairing.cSep_spec _).2 trivial)

set_option maxHeartbeats 800000 in

theorem thetaVector_eq_sum_translates : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m), ∃ ε : ℤˣ, ∀ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ (t : Tp) (k : O.Cl' t), (∀ q, O.w t k q ≠ 0 → ∀ b, ∀ s ∈ (∏ PP ∈ R.Pg, PP.asIdeal) * ∏ PP ∈ R.Q (tup t), PP.asIdeal, s • q b = 0) ∧ ∀ N : ℕ, 0 < N → (O.dδ t).l₂.M ∣ N → ∀ Y : (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ t).l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E, IsRoots (O.dδ t).l₂ (LinearMap.range (T.iota ((i : ℕ) + 1))) ((ε : ℤ) • T.iota ((i : ℕ) + 1)) N Y → R.vP i (tup t) = ((Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ t).l₂) : ℕ) : ℂ)⁻¹ • ∑ᶠ q, inC O.c' (O.w t k q) • heisO R.ψ (Vc D i) (Wc D i) (finR (Vc D i) (rank_Wc i) (-(Y q))) (R.vacP i) := by
  rintro D G _ _ Pl0 T0 A T _ R F κ v₀ hR ⟨tie⟩ i
  by_cases hstd : VStd D i
  swap
  · exact ⟨1, fun Tp tup O hP => absurd hP.lift.std hstd⟩
  obtain ⟨hι, hiso⟩ := lat_iotaW T tie.laws i
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.lattice_isometry_sign_second D G Pl0 T0 A _ R F hR i hstd _ _ _ hι hiso
  refine ⟨-δ, fun Tp tup O hP t k => ?_⟩
  have hw : ∀ q, inC O.c' (O.w t k q) = GlobalTheory.AdTh.hatC (O.dδ t).l₂ (fun x => inC O.c' (O.φ t x)) q := fun q =>
    (congrArg (inC (O.dδ t).c₂) (hP.w t k q)).trans (GlobalTheory.AdTh.PairModel.hatC_phiHat (O.dδ t).c₂ _ q)
  have hφ : PhiIs R i (RingHom.id ℂ) (tup t) (iotaW T i) (Mfr (O.dδ t).l₂ • ⊤) fun x => inC O.c' (O.φ t x) :=
    (hP.tuple t).phi
  obtain ⟨h1, h2, h3⟩ := (hP.tuple t).half
  have hMb : (O.dδ t).l₂.Mb = T.Q.l.Mb * (O.dδ t).I := (hP.cov t).1.2.2.2.1
  have hPg : ∀ PP ∈ R.Pg, (∏ PP ∈ R.Pg, PP.asIdeal) ≤ PP.asIdeal := fun PP h =>
    Ideal.prod_le_inf.trans (Finset.inf_le h)
  have hQ : ∀ PP ∈ R.Q (tup t), (∏ PP ∈ R.Q (tup t), PP.asIdeal) ≤ PP.asIdeal := fun PP h =>
    Ideal.prod_le_inf.trans (Finset.inf_le h)
  refine ⟨fun q hq b s hs => ?_, fun N _ hN Y hY => ?_⟩
  · obtain ⟨z, hz⟩ := GlobalTheory.HatInt.smul_eq_of_hatC_ne_zero D G Pl0 T0 A _ R i _ _ _ _ _ _ hφ q
      (by rw [← hw]; exact (map_ne_zero _).2 hq) s
      (fun PP h => h.elim (fun h => hPg PP h (Ideal.mul_le_left hs)) fun h => hQ PP h (Ideal.mul_le_right hs)) b
    exact smul_eq_zero_of_smul_rep _ s z hz
  · have hl : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q (tup t) → (O.dδ t).l₂.Mb ≤ PP.asIdeal ∧
        ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP h =>
      ⟨by
        rw [hMb]
        exact h.elim (fun h => Ideal.mul_le_left.trans (h1.le.trans (hPg PP h))) fun h =>
          Ideal.mul_le_right.trans (h2 PP h), h3 PP h⟩
    have hY' := isRoots_sign (-δ) hN hY
    have hL : GlobalTheory.AdTh.latR (rank_Wc i) (latG (Wc D i) 1) = LinearMap.range (T.iota ((i : ℕ) + 1)) := by
      rw [← hι.2]
      exact latR_range _ _
    rw [← hL] at hY'
    have h := hδ (tup t) (O.dδ t).l₂ _ hφ hl 0 (O.dδ t).l₂.M 1 1 ⟨Formalism.L2.Pj.stdLat D.host.E _⟩ (T.iota ((i : ℕ) + 1))
      (fun PP _ => by simp) (splitOffBad_one _) ?_ ⟨1, Nat.coprime_one_left _, Submodule.smul_le_right, Submodule.smul_le_right⟩
      ⟨(O.dδ t).l₂.odd, dvd_rfl, le_inf Submodule.smul_le_right Submodule.smul_le_right⟩ ?_ _
      (fun q => ((-(Y q)).submatrix id (Fin.cast (rank_Wc i)))ᵀ) (fun q => finR (Vc D i) (rank_Wc i) (-(Y q))) hY' ?_
    · rw [show ((1, 1) : GA D (Vc D i) × GA D (Wc D i)) = 1 from rfl, map_one, Module.End.one_apply,
        Module.End.one_apply] at h
      simp only [hw]
      exact h
    · intro v
      rw [show FWT.fin (Vc D i) 1 = 1 from map_one _, hstd.2]
      refine ⟨mem_std_star T.Q.H v, fun h => ?_⟩
      have h' := mem_std_star T.Q.H _ h
      simp only [star_star] at h'
      exact h'
    · intro a _
      refine ⟨0, zero_mem _, ?_⟩
      rw [map_one, nsmul_zero, Units.val_one, Matrix.one_mulVec]
      exact sub_self _
    · intro q
      refine ⟨(isFinOf_finR _ _ _ _).1.trans ?_, (isFinOf_finR _ _ _ _).2⟩
      rw [smul_smul, Units.val_neg, mul_neg, ← Units.val_mul, Int.units_mul_self, Units.val_one, neg_smul, one_smul]

end GlobalTheory.OneMapRef.FinDatum
