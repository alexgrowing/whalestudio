import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Formalism.HermitianLattices.FinalNeighbourConstruct
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianGenusMassEqOrbitStabilizerMassStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMaximalIntegralHermitianLatticeOrthonormalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemGenusIffMaximalIntegralHermitianLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitStabilizerMassEqWeightedSumFibresStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitWeightedStabilizerSumMonoSubadditiveStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardSublatticesQuotientProdDegreeOnePrimesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CyclicDiscriminantLatticesFormOneGenusStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnimodularOverlatticeCyclicSplitDiscriminaStatement
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.CyclicDisc

section
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem nondeg_of_pd (h : V →ₗ⋆[K] V →ₗ[K] K) (hp : PD h) : h.Nondegenerate := by
  obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · by_contra hne
    have := hp τ x hne
    rw [hx x] at this
    simp at this
  · by_contra hne
    have := hp τ x hne
    rw [hx x] at this
    simp at this

omit [IsScalarTower (𝓞 K) K V] in
theorem pd_of_ortho (hK : IsCMUnram K) (h : V →ₗ⋆[K] V →ₗ[K] K) (I : Submodule (𝓞 K) V) (n : ℕ)
    (hI : IsOrthoLattice h I n) : PD h := by
  obtain ⟨e, -, hsp, -, he⟩ := hI
  intro τ x hx
  have hx' : x ∈ Submodule.span K (Set.range e) := by rw [hsp]; trivial
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx'
  have hc : ∃ i, c i ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hx (by simp [hn])
  have e1 : h (∑ i, c i • e i) (∑ i, c i • e i) = ∑ i, star (c i) * c i := by
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, he,
      smul_eq_mul, RingHom.id_apply, starRingEnd_apply]
    simp [mul_comm]
  rw [e1, map_sum, Complex.re_sum]
  have e2 : ∀ i, (τ (star (c i) * c i)).re = Complex.normSq (τ (c i)) := fun i => by
    rw [map_mul, hK.2.1, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  simp only [e2]
  obtain ⟨i, hi⟩ := hc
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
    ⟨i, Finset.mem_univ _, Complex.normSq_pos.2 ((map_ne_zero τ).2 hi)⟩

omit [NumberField K] in
theorem star_mem_range (r : 𝓞 K) : star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) := by
  have : IsIntegral ℤ (starRingEnd K (algebraMap (𝓞 K) K r)) :=
    map_isIntegral_int _ (RingOfIntegers.isIntegral_coe r)
  exact ⟨⟨_, this⟩, rfl⟩

def Over (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔓 : Ideal (𝓞 K)) (L M : Submodule (𝓞 K) V) : Prop :=
  Submodule.IsLattice K M ∧ IsUnimodular h M ∧ L ≤ M ∧
    Nonempty ((↥M ⧸ L.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ 𝔓))

omit [NumberField K] in
theorem over_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔓 : Ideal (𝓞 K)) (g : isom h) (L M : Submodule (𝓞 K) V)
    (H : Over h 𝔓 L M) : Over h 𝔓 (g • L) (g • M) := by
  obtain ⟨h1, h2, h3, ⟨e⟩⟩ := H
  have A := final_isomAct (𝓞 K) K V h g.1 g.2 M
  refine ⟨A.2.2.2.2.2 h1, A.2.2.2.1.2 h2, Submodule.map_mono h3, ⟨?_⟩⟩
  let g' : V ≃ₗ[𝓞 K] V := (g : V ≃ₗ[K] V).restrictScalars (𝓞 K)
  let f : M ≃ₗ[𝓞 K] ↥(g • M) := g'.submoduleMap M
  refine (Submodule.Quotient.equiv _ _ f ?_).symm.trans e
  ext ⟨x, hx⟩
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y.1, hy, congrArg Subtype.val hxy⟩
  · rintro ⟨y, hy, hxy⟩
    exact ⟨⟨y, h3 hy⟩, hy, Subtype.ext hxy⟩

omit [NumberField K] in
theorem over_smul_iff (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔓 : Ideal (𝓞 K)) (g : isom h) (L M : Submodule (𝓞 K) V) :
    Over h 𝔓 (g • L) (g • M) ↔ Over h 𝔓 L M :=
  ⟨fun H => by simpa using over_smul h 𝔓 g⁻¹ _ _ H, over_smul h 𝔓 g L M⟩

noncomputable def up (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔓 : Ideal (𝓞 K)) (L : Submodule (𝓞 K) V) :
    Submodule (𝓞 K) V := sSup {M | Over h 𝔓 L M}

omit [NumberField K] in
theorem up_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔓 : Ideal (𝓞 K)) (g : isom h) (L : Submodule (𝓞 K) V) :
    up h 𝔓 (g • L) = g • up h 𝔓 L := by
  have key : ∀ (g : isom h) (L : Submodule (𝓞 K) V), g • up h 𝔓 L ≤ up h 𝔓 (g • L) := by
    intro g L
    change Submodule.map _ _ ≤ _
    rw [Submodule.map_le_iff_le_comap]
    refine sSup_le fun M hM => ?_
    rw [← Submodule.map_le_iff_le_comap]
    exact le_sSup (over_smul h 𝔓 g L M hM)
  refine le_antisymm ?_ (key g L)
  have h1 := key g⁻¹ (g • L)
  rw [inv_smul_smul] at h1
  have h2 : g • g⁻¹ • up h 𝔓 (g • L) ≤ g • up h 𝔓 L := Submodule.map_mono h1
  rwa [smul_inv_smul] at h2

omit [NumberField K] in
theorem up_eq (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔓 : Ideal (𝓞 K)) (L M : Submodule (𝓞 K) V)
    (hu : ∃! M, Over h 𝔓 L M) (hM : Over h 𝔓 L M) : up h 𝔓 L = M := by
  have : {M | Over h 𝔓 L M} = {M} := by
    ext N
    exact ⟨fun hN => hu.unique hN hM, fun hN => by rw [Set.mem_singleton_iff.1 hN]; exact hM⟩
  rw [up, this, sSup_singleton]

end

theorem main : MaxMass → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → 1 ≤ Module.finrank K V → ∀ (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h' : V' →ₗ⋆[K] V' →ₗ[K] K), h'.IsSymm → ∀ I : Submodule (𝓞 K) V', IsOrthoLattice h' I (Module.finrank K V) → ∀ T : ℕ, T.Prime → (∀ P : Ideal (𝓞 K), P.IsMaximal → (T : 𝓞 K) ∈ P → Ideal.absNorm P = T ∧ (T : 𝓞 K) ∉ P ^ 2) → ∀ L : Submodule (𝓞 K) V, IsIntLat h L → Nonempty ((↥(dual h L) ⧸ L.comap (dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)})) → mass h L = mass h' I * (((T : ℝ) ^ Module.finrank K V - 1) / ((T : ℝ) - 1)) ^ fDeg K := by
  intro hMM K V _ _ _ _ _ _ _ _ h hK hs hp hn V' _ _ _ _ _ h' hs' I hI T hT hsp L hL hLq
  have hnd := nondeg_of_pd h hp
  have hp' := pd_of_ortho hK h' I _ hI
  have hnd' := nondeg_of_pd h' hp'
  obtain ⟨⟨s, hcard, hsP, hcop, hprod⟩, hgen⟩ := GlobalTheory.T.cyclicDiscriminant_lattices_form_one_genus K V h hK hs hnd T hT hsp
  have hT0 : (T : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hT.ne_zero
  have hP0 : (∏ P ∈ s, P) ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at hprod
    exact hT0 hprod
  obtain ⟨o1, o2⟩ := GlobalTheory.T.exists_unimodular_overlattice_cyclic_split_discriminant K V h hK hs hnd _ hP0 hcop
  rw [hprod] at o1 o2
  have hex : ∀ N ∈ genus h L, ∃! M, Over h (∏ P ∈ s, P) N M := fun N hN =>
    o1 N ((hgen L N hL hLq).1 hN).1 ((hgen L N hL hLq).1 hN).2
  obtain ⟨M0, hM0, -⟩ := o1 L hL hLq
  obtain ⟨-, m2, -⟩ := GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal K V h hK hs hnd
  obtain ⟨-, m2', m3'⟩ := GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal K V' h' hK hs' hnd'
  obtain ⟨c, hc⟩ := hMM K hK _ hn
  obtain ⟨iL, iU, iR⟩ := m3' I _ hI
  have e0 : mass h M0 = mass h' I := by
    rw [hc V h hs hp rfl M0 (m2 M0 hM0.1 hM0.2.1).1, (m2 M0 hM0.1 hM0.2.1).2.2,
      hc V' h' hs' hp' iR I (m2' I iL iU).1, (m2' I iL iU).2.2]
  obtain ⟨b1, b2, b3, b4, -⟩ := GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V h hK hs hp L hL.1
  obtain ⟨a1, a2, a3, -, -⟩ := GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V h hK hs hp M0 hM0.1
  have hmaps : Set.MapsTo (up h (∏ P ∈ s, P)) (genus h L) (genus h M0) := by
    intro N hN
    obtain ⟨M, hM, -⟩ := hex N hN
    rw [up_eq h _ N M (hex N hN) hM]
    exact (GlobalTheory.T.mem_genus_iff_maximalIntegralHermitianLattice K V h hK hs hp M0 M (m2 M0 hM0.1 hM0.2.1).1).2 (m2 M hM.1 hM.2.1).1
  have hfib := GlobalTheory.T.orbitStabilizerMass_eq_weightedSum_fibres (isom h) _ _ (genus h L) (genus h M0) (up h (∏ P ∈ s, P))
    (up_smul h _) b3 a3 hmaps (fun y hy => b4 y hy.1)
  set B : ℕ := (∑ i ∈ Finset.range (Module.finrank K V), T ^ i) ^ s.card with hB
  have hconst : ∀ M ∈ genus h M0,
      ((((genus h L) ∩ (up h (∏ P ∈ s, P)) ⁻¹' {M}).encard : ℕ∞) : ℝ≥0∞) = (B : ℝ≥0∞) := by
    intro M hM
    have hU : IsUnimodular h M :=
      (((final_genusBasic (𝓞 K) K V h hs star_mem_range).2.2 M0 M hM0.1.fg hM.1.fg hM.2).1).1 hM0.2.1
    have hset : (genus h L) ∩ (up h (∏ P ∈ s, P)) ⁻¹' {M} = {N : Submodule (𝓞 K) V | N ≤ M ∧
        Nonempty ((↥M ⧸ N.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ ∏ P ∈ s, P))} := by
      ext N
      constructor
      · rintro ⟨hN, hNM⟩
        obtain ⟨M1, hM1, -⟩ := hex N hN
        have : M1 = M := (up_eq h _ N M1 (hex N hN) hM1).symm.trans hNM
        subst this
        exact hM1.2.2
      · rintro ⟨h1, h2⟩
        have hN : N ∈ genus h L := (hgen L N hL hLq).2 (o2 M N hM.1 hU h1 h2)
        exact ⟨hN, up_eq h _ N M (hex N hN) ⟨hM.1, hU, h1, h2⟩⟩
    rw [hset, GlobalTheory.T.card_sublattices_quotient_prod_degree_one_primes K V M hM.1 T s hT hsP]
    exact ENat.toENNReal_coe _
  obtain ⟨p1, p2, -⟩ := GlobalTheory.T.orbitWeightedStabilizerSum_mono_subadditive (isom h) (Submodule (𝓞 K) V)
  have hsum : orbMass (isom h) (genus h L) = (B : ℝ≥0∞) * orbMass (isom h) (genus h M0) := by
    rw [hfib, ← p2]
    exact le_antisymm (p1 _ _ _ _ subset_rfl fun x hx => (hconst x hx).le)
      (p1 _ _ _ _ subset_rfl fun x hx => (hconst x hx).ge)
  rw [← b1, ← a1, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_eq_ofReal_iff b2.le (by positivity)] at hsum
  have hT1 : (T : ℝ) ≠ 1 := by exact_mod_cast hT.one_lt.ne'
  rw [hsum, e0, hB, hcard, mul_comm, ← geom_sum_eq hT1]
  push_cast
  rfl

end GlobalTheory.Mass.CyclicDisc
