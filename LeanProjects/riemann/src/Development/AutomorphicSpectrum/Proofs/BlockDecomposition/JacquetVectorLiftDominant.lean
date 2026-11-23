import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactFixedVectorProjectionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactGroupFiniteCosetRepsStatement

open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.CassPush

section SlopeTestRemainingChoices

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem pi_mul (π : Representation ℂ G V) (a b : G) (v : V) : π a (π b v) = π (a * b) v := by
  rw [map_mul, Module.End.mul_apply]

theorem mem_fixed_iff (π : Representation ℂ G V) (H : Subgroup G) (v : V) :
    v ∈ fixed π H ↔ ∀ h ∈ H, π h v = v := by
  constructor
  · intro hv h hh
    have h1 : ∀ h : H, π (h : G) v = (((1 : H →* ℂˣ) h : ℂˣ) : ℂ) • v := hv
    simpa using h1 ⟨h, hh⟩
  · intro hv
    show ∀ h : H, π (h : G) v = (((1 : H →* ℂˣ) h : ℂˣ) : ℂ) • v
    intro h
    simpa using hv h h.2

theorem mkQ_avg (W : Submodule ℂ V) (r : ℕ) (hr : 0 < r) (f : Fin r → V) (m : V ⧸ W)
    (h : ∀ i, W.mkQ (f i) = m) : W.mkQ (((r : ℂ)⁻¹) • ∑ i, f i) = m := by
  have hr' : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hr.ne'
  rw [map_smul, map_sum, Finset.sum_congr rfl (fun i _ => h i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hr', one_smul]

end SlopeTestRemainingChoices

section Avg

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem exists_avg (K : Subgroup G) (hK : IsCompact (K : Set G)) (π : Representation ℂ G V)
    (hπ : IsSmooth π) (E : V →ₗ[ℂ] V)
    (hE : ∀ (u : V) (H : Subgroup G), H ≤ K → (∀ h ∈ H, π h u = u) → ∀ (r : ℕ) (x : Fin r → G),
      0 < r → (∀ i, x i ∈ K) → (∀ y ∈ K, ∃! i, (x i)⁻¹ * y ∈ H) →
      E u = ((r : ℂ)⁻¹) • ∑ i, π (x i) u)
    (u : V) (A : Subgroup G) (hA : A ≤ K) (hc : ∀ y ∈ K, ∃ a ∈ A, π (a⁻¹ * y) u = u) :
    ∃ (r : ℕ) (x : Fin r → G), 0 < r ∧ (∀ i, x i ∈ A) ∧
      E u = ((r : ℂ)⁻¹) • ∑ i, π (x i) u := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let H' : Subgroup K :=
    { carrier := {g | π (g : G) u = u}
      mul_mem' := by
        intro a b ha hb
        show π ((a * b : K) : G) u = u
        rw [Subgroup.coe_mul, ← pi_mul, show π (b : G) u = u from hb, show π (a : G) u = u from ha]
      one_mem' := by
        show π ((1 : K) : G) u = u
        simp
      inv_mem' := by
        intro a ha
        show π ((a⁻¹ : K) : G) u = u
        have ha' : π (a : G) u = u := ha
        conv_lhs => rw [← ha']
        rw [pi_mul]
        simp }
  have hH' : IsOpen (H' : Set K) := (hπ u).preimage continuous_subtype_val
  have hcomp : IsCompact (((⊤ : Subgroup K)) : Set K) := by
    simpa using (isCompact_univ : IsCompact (Set.univ : Set K))
  obtain ⟨r, hr, x, hxA, hx⟩ := GlobalTheory.T.compact_group_finite_coset_reps K ⊤ H' (A.subgroupOf K) hcomp hH' le_top le_top (by
    intro y _
    obtain ⟨a, ha, hau⟩ := hc y y.2
    refine ⟨⟨a, hA ha⟩, Subgroup.mem_subgroupOf.2 ha, ?_⟩
    show π (((⟨a, hA ha⟩ : K)⁻¹ * y : K) : G) u = u
    simpa using hau)
  refine ⟨r, fun i => (x i : G), hr, fun i => Subgroup.mem_subgroupOf.1 (hxA i),
    hE u (H'.map K.subtype) ?_ ?_ r _ hr (fun i => (x i).2) ?_⟩
  · rintro _ ⟨g, _, rfl⟩
    exact g.2
  · rintro _ ⟨g, hg, rfl⟩
    exact hg
  · intro y hy
    obtain ⟨i, hi, huniq⟩ := hx ⟨y, hy⟩ trivial
    refine ⟨i, ⟨(x i)⁻¹ * ⟨y, hy⟩, hi, by simp⟩, ?_⟩
    rintro i' ⟨g, hg, e⟩
    refine huniq i' ?_
    have : (x i')⁻¹ * ⟨y, hy⟩ = g := by
      apply Subtype.ext
      simpa using e.symm
    show (x i')⁻¹ * ⟨y, hy⟩ ∈ H'
    rw [this]
    exact hg

end Avg

section Dom

variable {G : Type} [Group G] [TopologicalSpace G]

theorem conj_pow_mem (D : CassData G) (t : D.T) (hd : D.IsDom t) (j : ℕ) :
    ∀ b ∈ D.J ⊓ D.T, ((t : G) ^ j)⁻¹ * b * (t : G) ^ j ∈ D.J ⊓ D.T := by
  induction j with
  | zero => intro b hb; simpa using hb
  | succ j ih =>
    intro b hb
    have h := (hd.2.2 _ (ih b hb)).2
    have e : ((t : G) ^ (j + 1))⁻¹ * b * (t : G) ^ (j + 1)
        = (t : G)⁻¹ * (((t : G) ^ j)⁻¹ * b * (t : G) ^ j) * (t : G) := by
      rw [pow_succ]; group
    rw [e]
    exact h

end Dom

theorem exists_fixed_proj_eq_piN_pow : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (D : PositivityTheory.SphericalProduct.CassData G), ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ t : D.T, D.IsStrDom t → ∀ w ∈ fixed (D.piN π) D.JT, ∃ j : ℕ, ∃ v : fixed π D.J, D.proj π (v : V) = D.piN π (t ^ j) w := by
  intro G _ _ _ D V _ _ π hπ t ht w hw
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  obtain ⟨hd, -, hsh⟩ := ht
  obtain ⟨j, hj⟩ := hsh {g | π g u = u} (hπ u) (by simp)
  have hwT := (mem_fixed_iff _ _ _).1 hw
  have hKc : IsCompact ((D.J ⊓ D.T : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]
    exact D.isCompact_J.inter_right D.isClosed_alt
  have hN : ∀ n ∈ D.N, ∀ v : V,
      (twKer π D.N 1).mkQ (π n v) = (twKer π D.N 1).mkQ v := by
    intro n hn v
    refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨⟨n, hn⟩, v, by simp⟩)

  obtain ⟨x, hxdef⟩ : ∃ x, x = π ((t : G) ^ j) u := ⟨_, rfl⟩
  have hxNm : ∀ n ∈ D.J ⊓ D.Nm, π n x = x := by
    intro n hn
    have h1 : π (((t : G) ^ j)⁻¹ * n * (t : G) ^ j) u = u := hj n hn
    rw [hxdef]
    conv_rhs => rw [← h1]
    rw [pi_mul, pi_mul]
    congr 2
    group

  obtain ⟨E1, hE1fix, -, -, -, hE1⟩ := GlobalTheory.T.compact_fixed_vector_projection G (D.J ⊓ D.T) hKc V π hπ
  obtain ⟨r, b, hr, hb, hy⟩ := exists_avg (D.J ⊓ D.T) hKc π hπ E1 hE1 x (D.J ⊓ D.T) le_rfl
    (fun y hy => ⟨y, hy, by simp⟩)
  obtain ⟨y, hydef⟩ : ∃ y, y = E1 x := ⟨_, rfl⟩
  rw [← hydef] at hy
  have hyK : ∀ k ∈ D.J ⊓ D.T, π k y = y := by
    rw [hydef]
    exact (mem_fixed_iff _ _ _).1 (hE1fix x)
  have hyNm : ∀ n ∈ D.J ⊓ D.Nm, π n y = y := by
    intro n hn
    rw [hy, map_smul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have hbi := hb i
    have hn' : (b i)⁻¹ * n * b i ∈ D.J ⊓ D.Nm := by
      refine ⟨D.J.mul_mem (D.J.mul_mem (inv_mem hbi.1) hn.1) hbi.1, ?_⟩
      have h2 := (Subgroup.mem_normalizer_iff.1 (D.norm_Nm _ (inv_mem hbi.2)) n).1 hn.2
      simpa using h2
    have h3 := hxNm _ hn'
    conv_rhs => rw [← h3]
    rw [pi_mul, pi_mul]
    congr 2
    group
  have hmk : (twKer π D.N 1).mkQ y = D.piN π (t ^ j) (Submodule.Quotient.mk u) := by
    rw [hy]
    refine mkQ_avg _ r hr _ _ fun i => ?_
    have hc := conj_pow_mem D t hd j (b i) (hb i)
    have hfix := hwT ⟨_, hc.2⟩ hc.1
    have h4 : π (b i) x = π ((t : G) ^ j) (π (((t : G) ^ j)⁻¹ * b i * (t : G) ^ j) u) := by
      rw [hxdef, pi_mul, pi_mul]
      congr 2
      group
    rw [h4]
    have h5 : (twKer π D.N 1).mkQ (π (((t : G) ^ j)⁻¹ * b i * (t : G) ^ j) u)
        = Submodule.Quotient.mk u := hfix
    have h6 : ∀ m : V, (twKer π D.N 1).mkQ (π ((t : G) ^ j) m)
        = D.piN π (t ^ j) ((twKer π D.N 1).mkQ m) := by
      intro m
      have : (((t ^ j : D.T)) : G) = (t : G) ^ j := by simp
      rw [← this]
      rfl
    rw [h6, h5]

  obtain ⟨E2, hE2fix, -, -, -, hE2⟩ := GlobalTheory.T.compact_fixed_vector_projection G D.J D.isCompact_J V π hπ
  obtain ⟨r2, c, hr2, hc, hv⟩ := exists_avg D.J D.isCompact_J π hπ E2 hE2 y (D.J ⊓ D.N) inf_le_left
    (fun g hg => by
      obtain ⟨c, hc, b', hb', a, ha, rfl⟩ := D.fact_up g hg
      refine ⟨c, hc, ?_⟩
      have e : c⁻¹ * (c * b' * a) = b' * a := by group
      rw [e, ← pi_mul, hyNm a ha, hyK b' hb'])
  refine ⟨j, ⟨E2 y, hE2fix y⟩, ?_⟩
  show (twKer π D.N 1).mkQ (E2 y) = _
  rw [hv]
  refine mkQ_avg _ r2 hr2 _ _ fun i => ?_
  rw [hN _ (hc i).2, hmk]

end GlobalTheory.CompanionTheory.CassPush
