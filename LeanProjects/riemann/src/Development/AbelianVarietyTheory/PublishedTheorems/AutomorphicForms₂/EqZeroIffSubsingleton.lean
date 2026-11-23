import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM

namespace GlobalTheory.SiegelTor

section Param

variable {o R : Type} [CommRing o] [CommRing R] [IsLocalRing R] {m : ℕ} {b : o →+* R} {t : Fin m → R}

theorem IsRelParam.notMem_sq (h : IsRelParam b t) (i : Fin m) : t i ∉ maximalIdeal R ^ 2 := fun hi => by
  have := h.mem_of_mem_sq (Pi.single i 1) (by simpa [Pi.single_apply] using hi) i
  simp at this

theorem IsRelParam.ne_zero (h : IsRelParam b t) (i : Fin m) : t i ≠ 0 := fun h0 => h.notMem_sq i (h0 ▸ zero_mem _)

theorem IsRelParam.eq_of_dvd (h : IsRelParam b t) {i j : Fin m} (hd : t i ∣ t j) : i = j := by
  by_contra hne
  obtain ⟨c, hc⟩ := hd
  have := h.mem_of_mem_sq (Pi.single j 1 - Pi.single i c)
    (by simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]; simp [Pi.single_apply, hc, mul_comm c]) j
  simp [Ne.symm hne] at this

end Param

section Local

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {m : ℕ}

theorem eq_zero_iff_subsingleton {φ : InvFun ℤ} (D : DegData R (maximalIdeal R)) {r : Fin m → R}
    {γ : Fin m → LinearMap.BilinForm ℤ D.toPre.X} (hγ : IsCone id φ γ) {c : ℤ}
    (hm : IsMonomial D.toPre r fun i => c • γ i) : m = 0 ↔ Subsingleton D.toPre.X := by
  refine ⟨fun h0 => ⟨fun y z => sub_eq_zero.1 (by_contra fun hy => ?_)⟩, fun h => by_contra fun h0 => ?_⟩
  · obtain ⟨i, -⟩ := hm.exists_pos (maximalIdeal.isMaximal R).ne_top hy
    exact absurd i.2 (by omega)
  · exact hγ.linearIndependent.ne_zero ⟨0, Nat.pos_of_ne_zero h0⟩ (Subsingleton.elim _ _)

theorem exists_cusp_data (k : Type) [Field k] {n : ℕ} (hn : n ≠ 0) :
    ∃ (D : DegData (PowerSeries k) (maximalIdeal (PowerSeries k))) (γ : Fin 1 → LinearMap.BilinForm ℤ D.toPre.X),
      Module.finrank ℤ D.toPre.X = 1 ∧ IsCone id (InvFun.minVal ℤ) γ ∧
      (IsMonomial D.toPre ![PowerSeries.X] fun i => (2 * n : ℤ) • γ i) ∧
      ∀ i, (InvFun.minVal ℤ).evalZ ((n : ℤ) • γ i) = n := by
  rw [PowerSeries.maximalIdeal_eq_span_X]
  have hn' : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hs : ∀ y z : ℤ, ((2 * n : ℤ) • mulForm) y z = ((2 * n : ℤ) • mulForm) z y := fun y z => by simp [mul_comm]
  have hp : ∀ y : ℤ, y ≠ 0 → 0 < ((2 * n : ℤ) • mulForm) y y := fun y hy => by
    have := mul_self_pos.2 hy
    simp only [LinearMap.smul_apply, mulForm_apply, smul_eq_mul]
    positivity
  have he : ∀ y : ℤ, (2 : ℤ) ∣ ((2 * n : ℤ) • mulForm) y y := fun y => ⟨n * (y * y), by simp [mul_assoc]⟩
  refine ⟨ToricData.arcData (X := ℤ) k _ hs hp he, ![mulForm], Module.finrank_self ℤ, isCone_mulForm, ?_, fun i => ?_⟩
  · convert isMonomial_arcData (X := ℤ) k _ hs hp he using 1
    funext i
    fin_cases i
    rfl
  · refine (isCone_mulForm.evalZ_smul n i).trans ?_
    fin_cases i
    simp [evalZ_minVal_int]

omit [IsLocalRing R] in

theorem not_isMonomial_of_odd (D : DegPre R) (t : Fin 1 → R) (γ : LinearMap.BilinForm ℤ D.X) {y : D.X} (hy : γ y y = 1)
    {n : ℕ} (hn : Odd n) : ¬ IsMonomial D t fun _ => (n : ℤ) • γ := fun h => by
  obtain ⟨u, e, he, -⟩ := h y
  have := he 0
  obtain ⟨a, rfl⟩ := hn
  simp [hy] at this
  omega

end Local

section Charts

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {F : SFam g n ζ} {S : Scheme.{0}} {s : S ⟶ Sp o} {j : F.X ⟶ S}
  {G : Over S} [GrpObj G] {e : F.univ.A.left ⟶ G.left}

theorem HasChart.exists_mem_iff [IsOpenImmersion j] {φ : InvFun ℤ} {BD : EffCartierData S} {d : ℕ} {x : S}
    (h : HasChart F s j e φ BD d x) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ξ : Sp R' ⟶ S) (G' : Over (Sp R'))
      (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G.left) (D : DegData R' (maximalIdeal R'))
      (A : PolAV (Sp (FractionRing R'))) (U : Unif (maximalIdeal R') D A G'),
      ξ (closedPoint R') = x ∧ IsUnifOf F j e ξ π U ∧ (x ∈ Set.range j ↔ Subsingleton D.toPre.X) := by
  obtain ⟨R, _, _, b, ξ, m, t, R', _, _, _, ρ, r, G', _, _, π, D, A, U, γ, a, ⟨-, -, rfl, -, -⟩, ⟨ht, -, hj⟩,
    ⟨-, -, -, -, hρ, -⟩, ⟨hU, -, hγ, hm⟩, -, -⟩ := h
  refine ⟨R', _, inferInstance, inferInstance, _, G', _, inferInstance, π, D, A, U, ?_, hU, ?_⟩
  · exact congrArg ξ (comap_closedPoint ρ)
  · refine (hj _).trans (Iff.trans ?_ (eq_zero_iff_subsingleton D hγ hm))
    change ∏ i, t i ∉ maximalIdeal R ↔ _
    rw [notMem_maximalIdeal, IsUnit.prod_univ_iff]
    refine ⟨fun hu => by_contra fun h0 => ?_, fun h0 i => absurd i.2 (by omega)⟩
    exact ht.1 ⟨0, Nat.pos_of_ne_zero h0⟩ (hu _)

end Charts

theorem exists_support (h : GlobalTheory.Published.SiegelToroidalIntegral) {g n : ℕ} (hg : 1 ≤ g) (hn : 3 ≤ n) (ho : Odd n) :
    ∃ (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n)) (G : Over S) (_ : GrpObj G) (BD : EffCartierData S) (k : ℕ),
      IsProjOver s ∧ IsSemiAbelian G ∧ IsAmpleLB (CechPic.tens (lbPow (hodge G g) k) (CechPic.dual BD.lb)) ∧
      ∀ x, ReciprocityTheory.AnForm.R.FinalTheorems.stalkId BD.idealSheaf x = ⊤ ↔ x ∈ abLocus G := by
  obtain ⟨φ, hφ, h⟩ := h g hg
  obtain ⟨F, S, s, j, _, G, _, e, BD, d, N, h1, -, -, -, h2, -, -, h3, hd, hc, -, -, k₀, hk⟩ := h n hn ho
  exact ⟨S, s, G, _, BD, _, h1, h2, hk k₀ le_rfl, fun x => h3 ▸ (hc x).idl_eq_top_iff hφ (by omega) (by omega)⟩

end GlobalTheory.SiegelTor
