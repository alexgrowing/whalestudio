import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsPosConstLagrangeCondition
import Formalism.SharpRestriction.LevelLetterCocycles.LocalTheoryWindows

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section PID

variable {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
  {Q : Type} [AddCommGroup Q] [Module O Q]

theorem exists_gen_of_le_span (s : Finset Q) (N : Submodule O Q)
    (hN : N ≤ Submodule.span O (↑s : Set Q)) :
    ∃ t : Finset Q, t.card ≤ s.card ∧ (↑t : Set Q) ⊆ N ∧ N ≤ Submodule.span O (↑t : Set Q) := by
  classical
  let φ : (↥s → O) →ₗ[O] Q := Fintype.linearCombination O (fun x : ↥s => (x : Q))
  have hrange : LinearMap.range φ = Submodule.span O (↑s : Set Q) := by
    rw [Fintype.range_linearCombination]
    simp
  let N' : Submodule O (↥s → O) := N.comap φ
  obtain ⟨k, bN⟩ := Submodule.basisOfPid (Pi.basisFun O ↥s) N'
  have hk : k ≤ s.card := by
    have hli : LinearIndependent O (fun i => (bN i : ↥s → O)) :=
      bN.linearIndependent.map' N'.subtype (Submodule.ker_subtype N')
    have := hli.fintype_card_le_finrank
    simpa [Module.finrank_fintype_fun_eq_card] using this
  refine ⟨Finset.univ.image (fun i : Fin k => φ (bN i)), ?_, ?_, ?_⟩
  · exact Finset.card_image_le.trans (by simpa using hk)
  · intro y hy
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hy
    obtain ⟨i, rfl⟩ := hy
    exact (bN i).2
  · intro y hy
    obtain ⟨x, hx⟩ : y ∈ LinearMap.range φ := by rw [hrange]; exact hN hy
    have hxN : x ∈ N' := by show φ x ∈ N; rw [hx]; exact hy
    have key : (φ.comp N'.subtype) ⟨x, hxN⟩ ∈ Submodule.span O (Set.range fun i => φ (bN i)) := by
      have e : (Set.range fun i => φ (bN i)) = (φ.comp N'.subtype) '' Set.range bN := by
        ext z
        simp [Set.mem_range]
      rw [e, Submodule.span_image, bN.span_eq, Submodule.map_top]
      exact LinearMap.mem_range_self _ _
    rw [← hx]
    simpa [Finset.coe_image] using key

variable {M : Type} [AddCommGroup M] [Module O M]

theorem gen_step_of_ker (A B : Submodule O M) (ob : ↥B →ₗ[O] Q)
    (hker : ∀ x : ↥B, ob x = 0 ↔ (x : M) ∈ A) (m : ℕ) (s : Finset Q) (hs : s.card ≤ m)
    (hQ : Submodule.span O (↑s : Set Q) = ⊤) :
    ∃ t : Finset M, t.card ≤ m ∧ (↑t : Set M) ⊆ B ∧ B ≤ Submodule.span O (↑t : Set M) ⊔ A := by
  classical
  obtain ⟨t', ht'c, ht'sub, ht'span⟩ := exists_gen_of_le_span s (LinearMap.range ob) (by rw [hQ]; exact le_top)
  have hpre : ∀ q ∈ t', ∃ x : ↥B, ob x = q := fun q hq => ht'sub hq
  choose! pre hpre' using hpre
  refine ⟨t'.image (fun q => (pre q : M)), Finset.card_image_le.trans (ht'c.trans hs), ?_, ?_⟩
  · intro y hy
    simp only [Finset.coe_image, Set.mem_image] at hy
    obtain ⟨q, hq, rfl⟩ := hy
    exact (pre q).2
  · intro y hyB
    have hq : ob ⟨y, hyB⟩ ∈ Submodule.span O (↑t' : Set Q) := ht'span (LinearMap.mem_range_self _ _)
    rw [Submodule.mem_span_finset] at hq
    obtain ⟨c, -, hc⟩ := hq
    let z : ↥B := ∑ q ∈ t', c q • pre q
    have hz : ob z = ob ⟨y, hyB⟩ := by
      rw [← hc, map_sum]
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [map_smul, hpre' q hq]
    rw [Submodule.mem_sup]
    refine ⟨(z : M), ?_, y - (z : M), ?_, by abel⟩
    · rw [Submodule.coe_sum]
      refine Submodule.sum_mem _ fun q hq => ?_
      rw [Submodule.coe_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp only [Finset.coe_image, Set.mem_image]; exact ⟨q, hq, rfl⟩))
    · have h0 : ob (⟨y, hyB⟩ - z) = 0 := by rw [map_sub, hz, sub_self]
      exact (hker _).1 h0

theorem len_step_of_ker (A B P : Submodule O M) (ob : ↥B →ₗ[O] Q)
    (hker : ∀ x : ↥B, ob x = 0 → (x : M) ∈ A) :
    Module.length O (↥B ⧸ (A ⊔ P).comap B.subtype) ≤ Module.length O Q := by
  have hle : LinearMap.ker ob ≤ (A ⊔ P).comap B.subtype := fun x hx =>
    Submodule.mem_comap.2 (Submodule.mem_sup_left (hker x (LinearMap.mem_ker.1 hx)))
  have h1 : Module.length O (↥B ⧸ (A ⊔ P).comap B.subtype) ≤ Module.length O (↥B ⧸ LinearMap.ker ob) :=
    Module.length_le_of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)
  have h2 : Module.length O (↥B ⧸ LinearMap.ker ob) ≤ Module.length O Q :=
    Module.length_le_of_injective ((LinearMap.range ob).subtype.comp ob.quotKerEquivRange.toLinearMap)
      ((Submodule.injective_subtype _).comp ob.quotKerEquivRange.injective)
  exact h1.trans h2

end PID

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def KerChain (PD : PeriodData G Qp K₀ K B BdR) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    {FF : Type} [AddCommGroup FF] [Module O FF] (g : FF →ₗ[O] ↥(latticeFiniteCocycles PD T₂.L)) (n m : ℕ) (c : ℝ)
    (e : ℕ) : Prop :=
  ∃ (k : ℕ) (Fl : ℕ → Submodule O FF) (gen : Finset ℕ),
    gen.card ≤ 4 * n ∧ k - gen.card ≤ 3 * n / 2 ∧ Fl 0 = ⊤ ∧ gen ⊆ Finset.range k ∧
    (∀ i < k, Fl (i + 1) ≤ Fl i ∧
      ∃ (Q : Type) (_ : AddCommGroup Q) (_ : Module O Q) (ob : ↥(Fl i) →ₗ[O] Q),
        (∀ x : ↥(Fl i), ob x = 0 ↔ (x : FF) ∈ Fl (i + 1)) ∧
        (i ∈ gen → ∃ s : Finset Q, s.card ≤ m ∧ Submodule.span O (↑s : Set Q) = ⊤) ∧
        (i ∉ gen → ∃ L kO : ℕ, Module.length O Q ≤ (L : ℕ∞) ∧ lenOl PD (O := O) = kO ∧
          (L : ℝ) ≤ c * kO)) ∧
    ∀ x ∈ Fl k, ((PD.p : O) ^ e) • (g x : G → T₂.V) ∈ F.ImF PD

theorem lengthCount_of_kerChain [IsDomain O] [IsPrincipalIdealRing O] {T₁ T₂ : LocLat G Qp LL O}
    (F : LatHom T₁.L T₂.L) (FF : Type) [AddCommGroup FF] [Module O FF] [Module.Free O FF]
    [Module.Finite O FF] (g : FF →ₗ[O] ↥(latticeFiniteCocycles PD T₂.L))
    (hg : ∀ z : ↥(latticeFiniteCocycles PD T₂.L), ∃ x : FF, (z : G → T₂.V) - (g x : G → T₂.V) ∈ latticeCoboundaries T₂.L)
    (n r m : ℕ) (c : ℝ) (e : ℕ) (hr : Module.finrank O FF ≤ (n + 1) * r)
    (h : KerChain PD F g n m c e) : MassData PD F n r m c e := by
  obtain ⟨k, Fl, gen, hgc, hk, h0, hgen, hstep, hlast⟩ := h
  refine ⟨FF, inferInstance, inferInstance, inferInstance, inferInstance, g, k, Fl, gen, hg, hr, hgc, hk, h0,
    fun i hi => (hstep i hi).1, hgen, ?_, ?_, hlast⟩
  · intro i hi
    have hik : i < k := Finset.mem_range.1 (hgen hi)
    obtain ⟨-, Q, _, _, ob, hker, hG, -⟩ := hstep i hik
    obtain ⟨s, hs, hspan⟩ := hG hi
    exact gen_step_of_ker (Fl (i + 1)) (Fl i) ob hker m s hs hspan
  · intro i hik hi
    obtain ⟨-, Q, _, _, ob, hker, -, hL⟩ := hstep i hik
    obtain ⟨L, kO, hlen, hkO, hLc⟩ := hL hi
    exact ⟨L, kO, (len_step_of_ker (Fl (i + 1)) (Fl i) (preIm PD F g) ob (fun x hx => (hker x).1 hx)).trans hlen,
      hkO, hLc⟩

theorem cover_of_gen (T : LocLat G Qp LL O) (s : Finset (LatticeCohomology T.L))
    (hs : Submodule.span O (↑s : Set (LatticeCohomology T.L)) = latticeFiniteCohomology PD T.L) :
    ∃ g : (↥s → O) →ₗ[O] ↥(latticeFiniteCocycles PD T.L),
      ∀ z : ↥(latticeFiniteCocycles PD T.L), ∃ x : ↥s → O, (z : G → T.V) - (g x : G → T.V) ∈ latticeCoboundaries T.L := by
  classical
  have hmem : ∀ σ ∈ s, σ ∈ latticeFiniteCohomology PD T.L := fun σ hσ => hs ▸ Submodule.subset_span hσ
  have hle : latticeFiniteCocycles PD T.L ≤ latticeCocycles T.L := inf_le_left
  let incl := Submodule.inclusion hle
  let cls : ↥(latticeFiniteCocycles PD T.L) →ₗ[O] LatticeCohomology T.L := ((latticeCoboundaries T.L).comap (latticeCocycles T.L).subtype).mkQ.comp incl
  have hrep : ∀ σ : ↥s, ∃ w : ↥(latticeFiniteCocycles PD T.L), cls w = σ := by
    intro σ
    obtain ⟨y, hy, hyσ⟩ := Submodule.mem_map.1 (hmem σ σ.2)
    exact ⟨⟨y, hy⟩, by rw [← hyσ]; rfl⟩
  choose rep hrep using hrep
  refine ⟨Fintype.linearCombination O rep, fun z => ?_⟩
  have hz : cls z ∈ Submodule.span O (↑s : Set (LatticeCohomology T.L)) := by
    rw [hs]
    exact Submodule.mem_map.2 ⟨incl z, z.2, rfl⟩
  rw [Submodule.mem_span_finset'] at hz
  obtain ⟨c, hc⟩ := hz
  refine ⟨c, ?_⟩
  have hcls : cls (Fintype.linearCombination O rep c) = cls z := by
    rw [Fintype.linearCombination_apply, map_sum, ← hc]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, hrep]
  have h0 : cls (z - Fintype.linearCombination O rep c) = 0 := by rw [map_sub, hcls, sub_self]
  have h1 : incl (z - Fintype.linearCombination O rep c) ∈ (latticeCoboundaries T.L).comap (latticeCocycles T.L).subtype :=
    (Submodule.Quotient.mk_eq_zero _).1 h0
  exact h1

def LatticeFiniteCohomologyGeneratorBound [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m →
      ∃ s : Finset (LatticeCohomology T₂.L), Submodule.span O (↑s : Set (LatticeCohomology T₂.L)) = latticeFiniteCohomology PD T₂.L ∧
        s.card ≤ (n + 1) * finrank LL T₂.V

theorem generator_lemma_of_count [NeZero n] (W : LocWach PD LL O v n) (h : Formalism.MainNotions.LocalTheoryWindows.H1fGeneratorBound PD LL O) :
    LatticeFiniteCohomologyGeneratorBound W := by
  intro d T₁ T₂ F b S η m hset
  obtain ⟨s, hs, hcard⟩ := h hset.1.1 T₂ hset.2.2.2.2.2.1.2.1
  exact ⟨s, hs, by rw [W.n_eq]; exact hcard⟩

def ExpC (l h η S e₀ : ℕ) : Prop :=
  ∃ (a b : ℕ) (s₁ E e₂ : ℝ), b ≤ h ∧ (a : ℝ) ≤ aR l (h + η) + 1 ∧
    s₁ ≤ (2 * (a : ℝ) + 2 * (η : ℝ) + (S : ℝ)) / ((l : ℝ) - 1) + 2 * lam l (h + η) ∧
    E ≤ (3 * (a : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((l : ℝ) - 1) + 3 * lam l (h + η) ∧
    e₂ ≤ (b : ℝ) / ((l : ℝ) * ((l : ℝ) - 1)) + E + 2 * Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig₂ l (h + η)
      + 2 * (S : ℝ) + 5 + lam l (h + η) ∧
    (e₀ : ℝ) ≤ s₁ + 2 * Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig l h η + e₂ + (S : ℝ) + E + Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig₂ l (h + η)

def LocalLiftingConditions [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m →
      ∃ e₀ : ℕ, ExpC PD.p (hpar n b S) η S e₀ ∧
        (∀ (FF : Type) [AddCommGroup FF] [Module O FF] [Module.Free O FF] [Module.Finite O FF]
          (g : FF →ₗ[O] ↥(latticeFiniteCocycles PD T₂.L)),
          (∀ z : ↥(latticeFiniteCocycles PD T₂.L), ∃ x : FF, (z : G → T₂.V) - (g x : G → T₂.V) ∈ latticeCoboundaries T₂.L) →
          KerChain PD F g n m ((finrank LL T₂.V : ℝ) * (S : ℝ) +
            2 * (m : ℝ) * cD PD.p (hpar n b S + η)) e₀) ∧
        (m = 0 → F.LiftF PD (e₀ + 3 * S))

set_option maxHeartbeats 800000 in

private lemma e0_le_eBd_of_ExpC {l h η S e₀ : ℕ} (hl : 11 ≤ l) (hE : ExpC l h η S e₀) :
    (e₀ : ℝ) ≤ eBd 32 4 10 25 l (h + η) S η := by
  obtain ⟨a, b, s₁, E, e₂, hb, ha, hs₁, hEb, he₂, he₀⟩ := hE
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  have hd : 0 < (l : ℝ) - 1 := by linarith
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 1 / ((l : ℝ) - 1) := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht1 : t ≤ 1 / 10 := by rw [ht, div_le_div_iff₀ hd (by norm_num)]; linarith
  obtain ⟨Hr, hHr⟩ : ∃ Hr : ℝ, Hr = ((h + η : ℕ) : ℝ) := ⟨_, rfl⟩
  have hH0 : 0 ≤ Hr := by rw [hHr]; positivity
  have hhH : (h : ℝ) ≤ Hr := by rw [hHr]; push_cast; linarith [(Nat.cast_nonneg η : (0 : ℝ) ≤ η)]
  have hlam : 1 ≤ lam l (h + η) := by
    unfold lam
    rcases Nat.eq_zero_or_pos (h + η) with h0 | h0
    · rw [h0]; simp
    · have h1 : (1 : ℝ) ≤ 2 * ((h + η : ℕ) : ℝ) := by
        have : (1 : ℝ) ≤ ((h + η : ℕ) : ℝ) := by exact_mod_cast h0
        linarith
      have := Real.logb_nonneg (by linarith : (1 : ℝ) < l) h1
      linarith
  have haR : aR l (h + η) = 2 * (Hr * t) + Hr * t ^ 2 + 3 + lam l (h + η) := by
    unfold aR
    rw [ht, hHr]
    field_simp
    ring
  have hsig2 : Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig₂ l (h + η) = 2 * (Hr * t ^ 2) + 1 := by
    unfold Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig₂
    rw [ht, hHr]
    field_simp
  have hsig : Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig l h η ≤ h * t ^ 2 + t + η * t + 1 := by
    unfold Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig
    have hc : ((l - 1 : ℕ) : ℝ) = (l : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    have hq : (((h / (l - 1) + 1 : ℕ)) : ℝ) ≤ h * t + 1 := by
      have h1 := Nat.cast_div_le (α := ℝ) (m := h) (n := l - 1)
      rw [hc] at h1
      have e : (h : ℝ) / ((l : ℝ) - 1) = h * t := by rw [ht]; ring
      push_cast
      linarith
    have e2 : ((((h / (l - 1) + 1 : ℕ)) : ℝ) + η) / ((l : ℝ) - 1) =
        ((((h / (l - 1) + 1 : ℕ)) : ℝ) + η) * t := by rw [ht]; ring
    rw [e2]
    have h3 := mul_le_mul_of_nonneg_right hq ht0.le
    have e3 : ((((h / (l - 1) + 1 : ℕ)) : ℝ) + η) * t + 1 = (((h / (l - 1) + 1 : ℕ)) : ℝ) * t + η * t + 1 := by ring
    have e4 : ((h : ℝ) * t + 1) * t = h * t ^ 2 + t := by ring
    linarith
  have hbt : (b : ℝ) / ((l : ℝ) * ((l : ℝ) - 1)) ≤ h * t ^ 2 := by
    have hb' : (b : ℝ) ≤ h := by exact_mod_cast hb
    have e : (h : ℝ) * t ^ 2 = (h : ℝ) / (((l : ℝ) - 1) * ((l : ℝ) - 1)) := by rw [ht]; field_simp
    rw [e]
    exact div_le_div₀ (by positivity) hb' (by positivity) (mul_le_mul_of_nonneg_right (by linarith) hd.le)
  have hl2 : Hr * t ^ 2 ≤ 121 / 100 * (Hr / (l : ℝ) ^ 2) := by
    have h1 : (l : ℝ) ≤ 11 / 10 * ((l : ℝ) - 1) := by linarith
    have h2 : t ^ 2 ≤ 121 / 100 / (l : ℝ) ^ 2 := by
      rw [ht, div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      have h3 := mul_le_mul h1 h1 (by positivity) (by positivity)
      have e5 : (11 / 10 * ((l : ℝ) - 1)) * (11 / 10 * ((l : ℝ) - 1)) = 121 / 100 * ((l : ℝ) - 1) ^ 2 := by ring
      have e6 : (1 : ℝ) * (l : ℝ) ^ 2 = (l : ℝ) * (l : ℝ) := by ring
      linarith
    calc Hr * t ^ 2 ≤ Hr * (121 / 100 / (l : ℝ) ^ 2) := mul_le_mul_of_nonneg_left h2 hH0
      _ = 121 / 100 * (Hr / (l : ℝ) ^ 2) := by ring
  have e1 : (2 * (a : ℝ) + 2 * (η : ℝ) + (S : ℝ)) / ((l : ℝ) - 1) = 2 * (a * t) + 2 * (η * t) + S * t := by
    rw [ht]; ring
  have e2 : (3 * (a : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((l : ℝ) - 1) = 3 * (a * t) + S * t + 2 * (η * t) := by
    rw [ht]; ring
  rw [e1] at hs₁
  rw [e2] at hEb
  have hat : (a : ℝ) * t ≤ 2 * (Hr * t ^ 2) + Hr * t ^ 3 + 4 * t + lam l (h + η) * t := by
    have := mul_le_mul_of_nonneg_right ha ht0.le
    rw [haR] at this
    calc (a : ℝ) * t ≤ (2 * (Hr * t) + Hr * t ^ 2 + 3 + lam l (h + η) + 1) * t := this
      _ = 2 * (Hr * t ^ 2) + Hr * t ^ 3 + 4 * t + lam l (h + η) * t := by ring
  have hHl : 0 ≤ Hr / (l : ℝ) ^ 2 := by positivity
  have hηt : 0 ≤ (η : ℝ) * t := by positivity
  have hS0 : (0 : ℝ) ≤ S := by positivity
  have hht : (h : ℝ) * t ^ 2 ≤ Hr * t ^ 2 := mul_le_mul_of_nonneg_right hhH (by positivity)
  have ht3 : Hr * t ^ 3 ≤ 1 / 10 * (Hr * t ^ 2) := by
    calc Hr * t ^ 3 = Hr * t ^ 2 * t := by ring
      _ ≤ Hr * t ^ 2 * (1 / 10) := mul_le_mul_of_nonneg_left ht1 (mul_nonneg hH0 (sq_nonneg t))
      _ = 1 / 10 * (Hr * t ^ 2) := by ring
  have hlt : lam l (h + η) * t ≤ lam l (h + η) / 10 := by
    calc lam l (h + η) * t ≤ lam l (h + η) * (1 / 10) := mul_le_mul_of_nonneg_left ht1 (by linarith)
      _ = lam l (h + η) / 10 := by ring
  have hSt : (S : ℝ) * t ≤ S / 10 := by
    calc (S : ℝ) * t ≤ S * (1 / 10) := mul_le_mul_of_nonneg_left ht1 hS0
      _ = S / 10 := by ring
  unfold eBd
  rw [hsig2] at he₂ he₀
  have e3 : 10 * (η : ℝ) / ((l : ℝ) - 1) = 10 * (η * t) := by rw [ht]; ring
  have e4 : 32 * ((h + η : ℕ) : ℝ) / (l : ℝ) ^ 2 = 32 * (Hr / (l : ℝ) ^ 2) := by rw [hHr]; ring
  rw [e3, e4]
  linarith [hsig, hbt, hat, hl2, hlam]

theorem openC_of_steps [NeZero n] (W : LocWach PD LL O v n) (hG : LatticeFiniteCohomologyGeneratorBound W) (hS : LocalLiftingConditions W) :
    OpenC W (fun _ => True) 25 := by
  intro d T₁ T₂ F b S η m hset _
  obtain ⟨e₀, hE, hK, hL0⟩ := hS d T₁ T₂ F b S η m hset
  obtain ⟨s, hs, hcard⟩ := hG d T₁ T₂ F b S η m hset
  obtain ⟨g, hg⟩ := cover_of_gen T₂ s hs
  obtain ⟨hdomO, hdvr, -⟩ := hset.2.2.2.1
  haveI := hdomO
  haveI := hdvr
  refine ⟨e₀, e0_le_eBd_of_ExpC hset.2.1 hE,
    lengthCount_of_kerChain F (↥s → O) g hg n (finrank LL T₂.V) m _ e₀ ?_ (hK (↥s → O) g hg), hL0⟩
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  exact hcard

end Core

def localLiftingConditionsGlobal (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
    [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))], LocalLiftingConditions ((HW l).W K 1 LL hg)

theorem openKR_of_steps (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (hG : Formalism.MainNotions.LocalTheoryWindows.H1fGeneratorBoundAll D.loc) (hS : localLiftingConditionsGlobal D HW F) : openKR D HW F (fun _ => True) 25 := by
  intro l _ K LL hg _
  exact openC_of_steps _ (generator_lemma_of_count _ (hG l K LL)) (hS l K LL hg)

theorem theorem_of_lifting_steps (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (CA CB CK : ℝ)
    (h10 : adm10 D HW F CA CB CK) (hG : Formalism.MainNotions.LocalTheoryWindows.H1fGeneratorBoundAll D.loc) (hS : localLiftingConditionsGlobal D HW F) :
    aux₃ D HW F 25 := by
  exact Theorem_C_of_open D HW F 25 CA CB CK h10 (openKR_of_steps D HW F hG hS)

theorem generator_count_iff (D : D7) : adm19 D ↔ Formalism.MainNotions.LocalTheoryWindows.H1fGeneratorBoundAll D.loc := by
  exact Iff.rfl

theorem stmt_of_stepsAdm (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CR CA CB CK : ℝ) (hS : admitted D HW F Cm CR CA CB CK → localLiftingConditionsGlobal D HW F) : Stmt D HW F Cm 25 CR CA CB CK := by
  intro hA
  exact theorem_of_lifting_steps D HW F CA CB CK hA.2.2.2.2.2.2.2.2.2.1
    ((generator_count_iff D).1 hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2) (hS hA)

end Formalism.MainNotions.RamifiedCoefficientChains
