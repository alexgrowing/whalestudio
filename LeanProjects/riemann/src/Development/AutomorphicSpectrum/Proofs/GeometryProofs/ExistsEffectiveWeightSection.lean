import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Proofs.MetricProofs.NefPolarizationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptBirationalArithVarStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeTensorPowerDegreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GapN
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GlobalReferenceGapPositiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ReferenceGeometryMultihomogFormStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Exists
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridgeFull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.ExRefEff

theorem tele (F : ℕ → ℤ) (k M : ℕ) (hk : k ≤ M) :
    ∑ n ∈ Finset.range M, (if k ≤ n then F n - F (n + 1) else 0) = F k - F M := by
  induction M, hk using Nat.le_induction with
  | base =>
    rw [Finset.sum_eq_zero]
    · simp
    · intro n hn
      rw [if_neg (by simpa using hn)]
  | succ M hM ih =>
    rw [Finset.sum_range_succ, ih, if_pos hM]
    ring

theorem abel (N : ℕ) (f x : Fin N → ℤ) :
    ∑ i : Fin N, (f i - if h : (i : ℕ) + 1 < N then f ⟨i + 1, h⟩ else 0) * ∑ k ∈ Finset.Iic i, x k =
      ∑ k, f k * x k := by
  classical
  let F : ℕ → ℤ := fun n => if h : n < N then f ⟨n, h⟩ else 0
  have hF : ∀ i : Fin N, (f i - if h : (i : ℕ) + 1 < N then f ⟨i + 1, h⟩ else 0) = F i - F (i + 1) := by
    intro i
    simp [F, i.2]
  have hFN : F N = 0 := by simp [F]
  have h1 : ∀ k : Fin N, ∑ i ∈ Finset.Ici k, (F i - F (i + 1)) = f k := by
    intro k
    have h2 := tele F k N k.2.le
    rw [hFN, sub_zero, ← Fin.sum_univ_eq_sum_range (fun n => if (k : ℕ) ≤ n then F n - F (n + 1) else 0) N] at h2
    have h3 : Finset.Ici k = Finset.univ.filter (fun i => k ≤ i) := by ext i; simp
    rw [h3, Finset.sum_filter]
    simp only [Fin.le_def]
    rw [h2]
    simp [F, k.2]
  simp_rw [hF, Finset.mul_sum]
  rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun k => Finset.Ici k) (by intro i k; simp)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_mul, h1]

section Chart

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {K : Type} [Fintype K]
  {J : K → Type} {y : (Σ k, J k) → Ω}

theorem ne_of_chart {p : Cpt ξ} {c : ∀ k, J k} (h : InChart ξ (fun c' : ∀ k, J k => ∏ k, y ⟨k, c' k⟩) c p) (k : K) :
    y ⟨k, c k⟩ ≠ 0 :=
  (Finset.prod_ne_zero_iff.1 h.1) k (Finset.mem_univ k)

theorem ratio_mem {p : Cpt ξ} {c : ∀ k, J k} (h : InChart ξ (fun c' : ∀ k, J k => ∏ k, y ⟨k, c' k⟩) c p)
    (k : K) (i : J k) : y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ regAt ξ p := by
  classical
  have h1 := h.2 (Function.update c k i)
  have h2 : (∏ l, y ⟨l, Function.update c k i l⟩) / ∏ l, y ⟨l, c l⟩ = y ⟨k, i⟩ / y ⟨k, c k⟩ := by
    rw [← Finset.prod_div_distrib, Finset.prod_eq_single k]
    · simp
    · intro l _ hl
      rw [Function.update_of_ne hl, div_self (ne_of_chart h l)]
    · simp
  rwa [h2] at h1

theorem chart_update {p : Cpt ξ} {c : ∀ k, J k} (h : InChart ξ (fun c' : ∀ k, J k => ∏ k, y ⟨k, c' k⟩) c p)
    [DecidableEq K] (k₀ : K) (i : J k₀) (hi : InChart ξ (fun i' : J k₀ => y ⟨k₀, i'⟩) i p) :
    InChart ξ (fun c' : ∀ k, J k => ∏ k, y ⟨k, c' k⟩) (Function.update c k₀ i) p := by
  have hne : ∀ k, y ⟨k, Function.update c k₀ i k⟩ ≠ 0 := by
    intro k
    by_cases hk : k = k₀
    · subst hk
      simpa using hi.1
    · rw [Function.update_of_ne hk]
      exact ne_of_chart h k
  refine ⟨Finset.prod_ne_zero_iff.2 fun k _ => hne k, fun c' => ?_⟩
  show (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, Function.update c k₀ i k⟩ ∈ regAt ξ p
  rw [← Finset.prod_div_distrib]
  refine Subring.prod_mem _ fun k _ => ?_
  by_cases hk : k = k₀
  · subst hk
    simpa using hi.2 (c' k)
  · rw [Function.update_of_ne hk]
    exact ratio_mem h k (c' k)

theorem chartRing_mem {p : Cpt ξ} {c : ∀ k, J k} (h : InChart ξ (fun c' : ∀ k, J k => ∏ k, y ⟨k, c' k⟩) c p)
    {a : Ω} (ha : a ∈ chartRingZ y c) : a ∈ regAt ξ p := by
  unfold chartRingZ at ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨q, rfl⟩ := hx
    exact ratio_mem h q.1 q.2
  | algebraMap r => simpa using intCast_mem (regAt ξ p) r
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

end Chart

section Ref

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β₀ : O →+* c.F} {Y : Model Xo c β₀}

theorem comb_a {G : RefGeo Y} (A : G.An) (ν : RootIx D → ℤ) (κ : G.K) :
    (PB.combLine A.Re.ref (gapN ν)).a κ = -∑ r, ν r * G.xdeg r κ := by
  rw [PB.combLine_a, Fintype.sum_option, Fintype.sum_prod_type, Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
  simp only [gapN, zero_mul, zero_add]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h := abel (D.p + D.q) (fun i => ν (τ, i)) (fun k => G.xdeg (τ, k) κ)
  rw [← h, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [A.fund_deg τ i]
  simp [Finset.sum_apply]

open Classical in

theorem isEff_of_data (G : RefGeo Y) (n : RootIx D → ℤ) (e : G.Ω) (b : G.Ω) (dβ : G.K → ℕ)
    (i₀ : ∀ k, G.J k) (hi₀ : ∀ k, G.y ⟨k, i₀ k⟩ ≠ 0)
    (he : e ∈ chartLat G.y (fun κ => (∑ r, (-n r) • G.xdeg r) κ - 1 - dβ κ) 1)
    (hb : b ∈ chartLat G.y (fun κ => (dβ κ : ℤ)) 1)
    (hbd : ∀ p : Cpt G.𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre G.𝔐.ξ r p) → p.1 ∉ abLocus G.𝔐.t.G →
      ∀ cc : ∀ k, G.J k, InChart G.𝔐.ξ (fun c' : ∀ k, G.J k => ∏ k, G.y ⟨k, c' k⟩) cc p →
        ¬ unitAt G.𝔐.ξ p (b * ∏ k, G.y ⟨k, cc k⟩ ^ (-((1 : ℕ) * (dβ k : ℤ))))) :
    G.IsEff n 1 (e * b * (∏ κ ∈ Finset.univ.erase G.k₀, G.y ⟨κ, i₀ κ⟩) * ∏ r, G.e r ^ (-n r)) := by
  classical
  have hDeg := GlobalTheory.T.lattice_tensor_power_degree _ _ G.𝔐.ξ G.K G.J G.y _ G.Fl.rootLat Set.univ G.xdeg G.e G.lines (fun r => -n r)
  intro p hp i t hi ht
  obtain ⟨c0, hc0⟩ := G.𝔐.tie.cover p
  have hc := chart_update hc0 G.k₀ i hi
  set cc := Function.update c0 G.k₀ i with hcc
  have hcck : cc G.k₀ = i := by simp [hcc]
  have hne := ne_of_chart hc
  have hgen := hDeg.2 p (Set.mem_univ _) cc hc
  set a : G.K → ℤ := ∑ r, (-n r) • G.xdeg r with ha
  set E₀ : G.Ω := ∏ r, G.e r ^ (-n r) with hE₀
  have hE₀0 : E₀ ≠ 0 := hDeg.1
  set Pa : G.Ω := ∏ k, G.y ⟨k, cc k⟩ ^ a k with hPa
  have hPa0 : Pa ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hne k)
  have hsp : (Lat.tens G.Fl.rootLat fun r => -n r) p = Submodule.span (regAt G.𝔐.ξ p) {Pa * E₀} := by
    rw [hgen, smul_eq_mul]
  have hg0 : Pa * E₀ ≠ 0 := mul_ne_zero hPa0 hE₀0
  obtain ⟨ht0, htp⟩ := ht
  have hgt : Pa * E₀ ∈ Submodule.span (regAt G.𝔐.ξ p) {t} := by
    rw [← htp, hsp]; exact Submodule.mem_span_singleton_self _
  obtain ⟨v, hv⟩ := Submodule.mem_span_singleton.1 hgt
  have hv' : (v : G.Ω) * t = Pa * E₀ := hv
  have hv0 : (v : G.Ω) ≠ 0 := fun h => hg0 (by rw [← hv', h, zero_mul])
  have hvm : (v : G.Ω) ∈ regAt G.𝔐.ξ p := v.2
  have hW := chartRing_mem hc (he cc hne)
  have hB := chartRing_mem hc (hb cc hne)
  set Q1 : G.Ω := ∏ k, G.y ⟨k, cc k⟩ ^ (-(((1 : ℕ) : ℤ) * (a k - 1 - dβ k))) with hQ1
  set Q2 : G.Ω := ∏ k, G.y ⟨k, cc k⟩ ^ (-(((1 : ℕ) : ℤ) * (dβ k : ℤ))) with hQ2
  set M : G.Ω := ∏ κ ∈ Finset.univ.erase G.k₀, G.y ⟨κ, i₀ κ⟩ with hM
  set Ec : G.Ω := ∏ κ ∈ Finset.univ.erase G.k₀, G.y ⟨κ, cc κ⟩ with hEc
  have hEc0 : Ec ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hne k
  have hMc : M / Ec ∈ regAt G.𝔐.ξ p := by
    rw [hM, hEc, ← Finset.prod_div_distrib]
    exact Subring.prod_mem _ fun k _ => ratio_mem hc k (i₀ k)
  have hP : Q1 * Q2 * Pa = G.y ⟨G.k₀, i⟩ * Ec := by
    have h1 : G.y ⟨G.k₀, i⟩ * Ec = ∏ k, G.y ⟨k, cc k⟩ := by
      rw [hEc, ← Finset.mul_prod_erase Finset.univ (fun k => G.y ⟨k, cc k⟩) (Finset.mem_univ G.k₀), hcck]
    rw [h1, hQ1, hQ2, hPa, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_add₀ (hne k), ← zpow_add₀ (hne k)]
    have : -(((1 : ℕ) : ℤ) * (a k - 1 - dβ k)) + -(((1 : ℕ) : ℤ) * (dβ k : ℤ)) + a k = 1 := by
      push_cast; ring
    rw [this, zpow_one]
  have hX : e * b * M * E₀ * G.y ⟨G.k₀, i⟩ ^ 1 / t =
      (v : G.Ω) * ((e * Q1) * (b * Q2) * (M / Ec)) := by
    have ht' : t = Pa * E₀ / v := by field_simp; rw [mul_comm]; exact hv'
    have hq : Q1 * Q2 = G.y ⟨G.k₀, i⟩ * Ec / Pa := by field_simp; exact hP
    have : (e * Q1) * (b * Q2) * (M / Ec) = e * b * (Q1 * Q2) * (M / Ec) := by ring
    rw [this, hq, ht']
    field_simp
  rw [hX]
  refine ⟨mul_mem hvm (mul_mem (mul_mem hW hB) hMc), fun hab hu => ?_⟩
  refine hbd p hp hab cc hc ⟨?_, hB, ?_⟩
  · intro h0
    apply hu.1
    rw [h0]; simp
  · have hb0 : b * Q2 ≠ 0 := fun h0 => hu.1 (by rw [h0]; simp)
    have : (b * Q2)⁻¹ = ((v : G.Ω) * ((e * Q1) * (b * Q2) * (M / Ec)))⁻¹ * ((v : G.Ω) * (e * Q1) * (M / Ec)) := by
      have hx := hu.1
      have hx1 : (v : G.Ω) * (e * Q1) * (M / Ec) ≠ 0 := by
        intro h0
        apply hx
        have : (v : G.Ω) * ((e * Q1) * (b * Q2) * (M / Ec)) = ((v : G.Ω) * (e * Q1) * (M / Ec)) * (b * Q2) := by ring
        rw [this, h0, zero_mul]
      have : (v : G.Ω) * ((e * Q1) * (b * Q2) * (M / Ec)) = ((v : G.Ω) * (e * Q1) * (M / Ec)) * (b * Q2) := by ring
      have key : ∀ w z : G.Ω, w ≠ 0 → z ≠ 0 → z⁻¹ = (w * z)⁻¹ * w := by
        intro w z hw hz
        field_simp
      rw [this]
      exact key _ _ hx1 hb0
    rw [this]
    exact mul_mem hu.2.2 (mul_mem (mul_mem hvm hW) hMc)

end Ref

theorem exists_eff : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), Top.IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → ∀ (G : RefGeo Y), Nonempty G.An → ∀ ν : RootIx D → ℤ, (∀ τ (i k : Fin (D.p + D.q)), i < k → ν (τ, k) < ν (τ, i)) → ∃ (k q' : ℕ) (s : G.Ω), 0 < k ∧ 0 < q' ∧ s ≠ 0 ∧ G.IsEff (fun r => (k * q' : ℕ) * ν r) q' s := by
  intro hG E _ _ _ H D Xo l c Y hgl hp hq G ⟨A⟩ ν hν
  classical
  have hIn : PB.Inputs := hG.2.2.2.2.2.2.2.2.2.1
  haveI : Nonempty G.K := ⟨G.k₀⟩
  have hb : Birational G.y := (GlobalTheory.T.hodge_cpt_birational_arith_var E H D l (Xo l) c (𝓞 c.F) (algebraMap _ _) Y ∅ G.Ω G.K G.J G.y G.𝔐 G.Fl
    (RingOfIntegers.coe_injective)).1
  obtain ⟨β, dβ, hβ, hβP, hb0, hβc, hbd⟩ := GlobalTheory.T.reference_geometry_multihomog_form E H D l (Xo l) c _ _ Y G
  let Fl : Set (Option (RootIx D)) := {a | ∃ (τ : CMType H) (i : Fin (D.p + D.q)), (i : ℕ) + 1 = D.p + D.q ∧ a = some (τ, i)}
  have hFl : ∀ a ∈ Fl, ∀ t, ReciprocityTheory.AnForm.M.IsPsh A.Sys.A ((A.Sys.potT a t).rsmul (-1)) ∧
      ReciprocityTheory.AnForm.M.IsPsh A.Sys.A (A.Sys.potT a t) := by
    rintro _ ⟨τ, i, hi, rfl⟩ t
    exact A.flat τ i hi t
  have hn : ∀ a ∉ Fl, 0 ≤ gapN ν a := by
    intro a ha
    cases a with
    | none => simp [gapN]
    | some r =>
      obtain ⟨τ, i⟩ := r
      have hi : (i : ℕ) + 1 < D.p + D.q := by
        by_contra h
        exact ha ⟨τ, i, by have := i.2; omega, rfl⟩
      have := hν τ i ⟨i + 1, hi⟩ (by simp [Fin.lt_def])
      simp only [gapN, dif_pos hi]
      omega
  obtain ⟨-, h2⟩ := GlobalTheory.T.nef_polarization hIn _ _ A.Sys Fl hFl G.K G.J G.Ω G.y A.Re A.J_top hb
    (fun V _ L => GroundTheory.Heights₂.Heights.NumbersDVR.intNum ℚ V L) (GroundTheory.Heights₂.Heights.NumbersDVR.IntNumIsFieldIntersection.full ℚ G.K G.J) (gapN ν) hn
  obtain ⟨k, hk, e, he, he0⟩ := h2 (GlobalTheory.T.global_reference_gap_positive hG E H D Xo l c Y hgl hp hq G A ν hν) β dβ hβ hβP
  have hne0 : ∀ κ, ∃ i, G.y ⟨κ, i⟩ ≠ 0 := by
    obtain ⟨c0, hc0⟩ := G.𝔐.tie.cover ⟨genPt G.𝔐.ξ, specializes_rfl⟩
    exact fun κ => ⟨c0 κ, ne_of_chart hc0 κ⟩
  choose i₀ hi₀ using hne0
  set n : RootIx D → ℤ := fun r => ((k * 1 : ℕ) : ℤ) * ν r with hn'
  have hdeg : ∀ κ, (∑ r, (-n r) • G.xdeg r) κ = (k : ℤ) * (PB.combLine A.Re.ref (gapN ν)).a κ := by
    intro κ
    rw [comb_a, Finset.sum_apply, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp [hn']
    ring
  have he' : e ∈ chartLat G.y (fun κ => (∑ r, (-n r) • G.xdeg r) κ - 1 - dβ κ) 1 := by
    have : (fun κ => (∑ r, (-n r) • G.xdeg r) κ - 1 - (dβ κ : ℤ)) =
        fun κ => (k : ℤ) * (PB.combLine A.Re.ref (gapN ν)).a κ - 1 - dβ κ := by
      funext κ
      rw [hdeg]
    rw [this]
    exact he
  refine ⟨k, 1, _, by omega, one_pos, ?_, isEff_of_data G n e _ dβ i₀ hi₀ he' hβc hbd⟩
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero he0 hb0) (Finset.prod_ne_zero_iff.2 fun κ _ => hi₀ κ)) ?_
  have hDeg := GlobalTheory.T.lattice_tensor_power_degree _ _ G.𝔐.ξ G.K G.J G.y _ G.Fl.rootLat Set.univ G.xdeg G.e G.lines (fun r => -n r)
  exact hDeg.1

end GlobalTheory.CompanionTheory.Ar.ExRefEff
