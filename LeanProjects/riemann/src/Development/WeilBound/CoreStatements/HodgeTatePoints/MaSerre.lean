import Development.WeilBound.CoreStatements.HodgeTatePoints.MaBase
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGenOnChart

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Ma

open ChCoh

theorem coh_chart : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat M.ξ E), L.IsCohOn Set.univ → ∀ c, x c ≠ 0 → ∃ (n : ℕ) (b : Fin n → E), ∀ p : Cpt M.ξ, InChart M.ξ x c p → L p = Submodule.span (regAt M.ξ p) (Set.range b) := by
  intro o _ Ω _ _ κ _ x M E _ _ L hL c hc
  obtain ⟨n, b, h⟩ := finite_gen (A := chRing o x c) (E := E) ((chRing o x c).val : chRing o x c →+* Ω)
    (Pt := {p : Cpt M.ξ // InChart M.ξ x c p}) (fun q => regAt M.ξ q.1)
    (fun _ _ => rfl)
    (fun q a => (regat_loc o Ω κ x M c q.1 q.2).1 _ a.2)
    (fun q a ha => by
      obtain ⟨u, hu, v, hv, hvu, e⟩ := ((regat_loc o Ω κ x M c q.1 q.2).2 a).1 ha
      exact ⟨⟨u, hu⟩, ⟨v, hv⟩, hvu, e⟩)
    (fun P hP => by
      obtain ⟨p, ⟨hp, hu⟩, -⟩ := prime_pt o Ω κ x M c hc P hP
      exact ⟨⟨p, hp⟩, hu⟩)
    (fun q => (reg_local M.X Ω M.ξ).1 q.1)
    (fun q => L q.1)
    (fun p => by
      obtain ⟨U, hU, n, b, hb⟩ := hL p.1 trivial
      obtain ⟨f, hf, hfu, hfU⟩ := basic o Ω κ x M c p.1 U p.2 hU
      exact ⟨⟨f, hf⟩, n, b, hfu, fun q hq => hb q.1 trivial (hfU q.1 q.2 hq)⟩)
  exact ⟨n, b, fun p hp => h ⟨p, hp⟩⟩

section

variable {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω}
  (M : PModel o x) {E : Type} [AddCommGroup E] [Module Ω E] (L : Lat M.ξ E)

theorem twist_mem {c j : κ} {t : Set E}
    (ht : ∀ p : Cpt M.ξ, InChart M.ξ x j p → L p = Submodule.span (regAt M.ξ p) t) {e : E}
    (he : ∀ p : Cpt M.ξ, InChart M.ξ x c p → e ∈ L p) :
    ∃ m : ℕ, ∀ p : Cpt M.ξ, InChart M.ξ x j p → (x c / x j) ^ m • e ∈ L p := by
  by_cases hj : x j = 0
  · exact ⟨0, fun p hp => (hp.1 hj).elim⟩
  let ι : chRing o x j →+* Ω := (chRing o x j).val
  have hsm : ∀ (a : chRing o x j) (e : E), a • e = ι a • e := fun _ _ => rfl
  let f : chRing o x j := ⟨x c / x j, Algebra.subset_adjoin ⟨c, rfl⟩⟩
  have hrad : f ∈ (satIdeal (Submodule.span (chRing o x j) t) 1 e).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hJP, hP⟩
    by_contra hn
    obtain ⟨q, ⟨hq, hu⟩, -⟩ := prime_pt o Ω κ x M j hj P hP
    have hf : unitAt M.ξ q (x c / x j) := not_not.1 fun h => hn ((hu f).2 h)
    have hc : x c ≠ 0 := fun h => hf.1 (by rw [h, zero_div])
    have hqc : InChart M.ξ x c q := ⟨hc, fun k => by
      have : x k / x c = x k / x j * (x c / x j)⁻¹ := by field_simp
      rw [this]
      exact mul_mem (hq.2 k) hf.2.2⟩
    have hmem : e ∈ Submodule.span (regAt M.ξ q) t := ht q hq ▸ he q hqc
    obtain ⟨v, hv, hve⟩ := clear_denoms ι hsm (S := regAt M.ξ q) (fun a ha => by
      obtain ⟨u, hu, v, hv, hvu, e⟩ := ((regat_loc o Ω κ x M j q hq).2 a).1 ha
      exact ⟨⟨u, hu⟩, ⟨v, hv⟩, hvu, e⟩) t hmem
    exact (hu v).1 (hJP ⟨0, by simpa using hve⟩) hv
  obtain ⟨m, k, hk⟩ := hrad
  refine ⟨m, fun q hq => ?_⟩
  rw [ht q hq]
  have h1 := mem_of_mem_spanA ι hsm (S := regAt M.ξ q)
    (fun a => (regat_loc o Ω κ x M j q hq).1 _ a.2) hk
  rw [hsm, one_pow, one_mul, map_pow] at h1
  exact h1

end

theorem serre : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat M.ξ E), L.IsCohOn Set.univ → ∃ (d n : ℕ) (z : Fin n → E), ∀ c (p : Cpt M.ξ), InChart M.ξ x c p → L p = Submodule.span (regAt M.ξ p) (Set.range fun k => (x c ^ d)⁻¹ • z k) := by
  intro o _ Ω _ _ κ _ x M E _ _ L hL
  have h1 : ∀ c, ∃ (n : ℕ) (b : Fin n → E), ∀ p : Cpt M.ξ, InChart M.ξ x c p →
      L p = Submodule.span (regAt M.ξ p) (Set.range b) := fun c => by
    by_cases hc : x c = 0
    · exact ⟨0, Fin.elim0, fun p hp => (hp.1 hc).elim⟩
    · exact coh_chart o Ω κ x M E L hL c hc
  choose n b hb using h1
  have h2 : ∀ s : (Σ c, Fin (n c)) × κ, ∃ m : ℕ, ∀ p : Cpt M.ξ, InChart M.ξ x s.2 p →
      (x s.1.1 / x s.2) ^ m • b s.1.1 s.1.2 ∈ L p := fun s =>
    twist_mem M L (hb s.2) fun p hp => by
      rw [hb _ p hp]
      exact Submodule.subset_span ⟨_, rfl⟩
  choose m hm using h2
  obtain ⟨d, hd⟩ := (Set.finite_range m).bddAbove
  obtain ⟨N, ⟨e⟩⟩ := Finite.exists_equiv_fin (Σ c, Fin (n c))
  refine ⟨d, N, fun k => x (e.symm k).1 ^ d • b (e.symm k).1 (e.symm k).2, fun j p hp => ?_⟩
  apply le_antisymm
  · rw [hb j p hp]
    refine Submodule.span_mono ?_
    rintro _ ⟨k, rfl⟩
    refine ⟨e ⟨j, k⟩, ?_⟩
    dsimp only
    rw [e.symm_apply_apply, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hp.1), one_smul]
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    set s := e.symm k
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (hd ⟨(s, j), rfl⟩ : m (s, j) ≤ d)
    have h3 := (L p).smul_mem (⟨(x s.1 / x j) ^ r, pow_mem (hp.2 _) _⟩ : regAt M.ξ p) (hm (s, j) p hp)
    have h4 : (x j ^ d)⁻¹ • x s.1 ^ d • b s.1 s.2 =
        (x s.1 / x j) ^ r • (x s.1 / x j) ^ m (s, j) • b s.1 s.2 := by
      rw [smul_smul, smul_smul, ← pow_add, add_comm r, ← hr, div_pow, div_eq_inv_mul]
    change (x j ^ d)⁻¹ • x s.1 ^ d • b s.1 s.2 ∈ L p
    rw [h4]
    exact h3

end PositivityTheory.HtPt.Ma
