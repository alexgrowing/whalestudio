import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexCongruenceSubgroupLeAbsNormPowStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummaryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairCommonUnipotentStabiliserSummaryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairInnerLatticesUnimodularPrimitiveStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormCongruenceLiftSmallGroupStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerHermitianLatticeOfDeepStarCongruenceStatement
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt

section
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

theorem inN_map_mem_of_le (F : FlagD H r) {g : V →ₗ[K] V} (hg : F.InN g) {S : Submodule K V} (hX : F.X ≤ S)
    (hz : F.z ∈ S) : (∀ x ∈ F.X, g x ∈ S) ∧ g F.z ∈ S := by
  have hXa : ∀ a : Fin r, F.Xa a ≤ F.X := fun a =>
    Submodule.span_mono (Set.image_mono fun b _ => b.isLt)
  have he : ∀ a : Fin r, F.e a.castSucc ∈ F.X := fun a => Submodule.subset_span ⟨a, a.isLt, rfl⟩
  constructor
  · have : F.X ≤ S.comap g := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, -, rfl⟩
      have := S.add_mem (hX (hXa a (hg.2.2.1 a))) (hX (he a))
      simpa using this
    exact fun x hx => this hx
  · have := S.add_mem (hX (hg.2.2.2 F.z F.zperp)) hz
    simpa using this

theorem unipotent_map_mem_V0 (F F' : FlagD H r) {g : V →ₗ[K] V} (hg : F.InN g) (hg' : F'.InN g) :
    ∀ x ∈ V0 F F', g x ∈ V0 F F' := by
  have h1 := inN_map_mem_of_le F hg (S := V0 F F') (le_sup_left.trans le_sup_left)
    (Submodule.mem_sup_right (Submodule.subset_span (by simp)))
  have h2 := inN_map_mem_of_le F' hg' (S := V0 F F') (le_sup_right.trans le_sup_left)
    (Submodule.mem_sup_right (Submodule.subset_span (by simp)))
  have : V0 F F' ≤ (V0 F F').comap g := by
    refine sup_le (sup_le h1.1 h2.1) (Submodule.span_le.2 ?_)
    rintro _ (rfl | rfl)
    · exact h1.2
    · exact h2.2
  exact fun x hx => this hx

end

theorem star_stable_pow {K : Type} [Field K] [StarRing K] (𝔠 : Ideal (𝓞 K))
    (h : ∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) (n : ℕ) :
    ∀ x ∈ 𝔠 ^ (n + 1), ∃ y ∈ 𝔠 ^ (n + 1), (y : K) = star (x : K) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    intro x hx
    rw [pow_succ] at hx ⊢
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      obtain ⟨a', ha', ea⟩ := ih a ha
      obtain ⟨b', hb', eb⟩ := h b hb
      refine ⟨a' * b', Ideal.mul_mem_mul ha' hb', ?_⟩
      show (a' : K) * (b' : K) = star ((a : K) * (b : K))
      rw [ea, eb, star_mul']
    · rintro a b ⟨a', ha', ea⟩ ⟨b', hb', eb⟩
      refine ⟨a' + b', add_mem ha' hb', ?_⟩
      show (a' : K) + (b' : K) = star ((a : K) + (b : K))
      rw [ea, eb, star_add]

theorem invVol_top_layer_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∀ e : ℕ, N.Split Λ → N.Near (𝔠 ^ e) Λ → GlobalTheory.HL.invVol (N.Gam (N.Ref (latL N.F N.F' Λ)) ⊔ N.R1) (N.Gam Λ ⊔ N.R1) ≤ (Ideal.absNorm 𝔠 : ℝ) ^ ((3 * e + 11) * (2 * r + 1) ^ 2) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ 𝔠 hc0 hcs hcT hcD e hsp hnear
  obtain ⟨hR, -⟩ := GlobalTheory.T.hermFramePairCommonUnipotentStabiliser_summary K V H hK r N
  obtain ⟨hNF, -⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  obtain ⟨-, -, -, -, hlat, hint⟩ := GlobalTheory.T.hermFramePair_innerLattices_unimodular_primitive K V H hK r N g Λ hg hΛ
  set L := N.Ref (latL N.F N.F' Λ) with hL
  set M := N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F') with hM
  have hMfg : M.FG := by
    rw [← hint]
    exact Submodule.FG.of_le hlat.fg inf_le_left
  have hstab : ∀ A : Subgroup (V ≃ₗ[K] V), (∀ s ∈ A, ∀ x ∈ M, s x ∈ M) →
      A ≤ MulAction.stabilizer (V ≃ₗ[K] V) M := by
    intro A hA s hs
    rw [MulAction.mem_stabilizer_iff]
    apply le_antisymm
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
      exact hA s hs y hy
    · intro x hx
      refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨s⁻¹ • x, hA _ (A.inv_mem hs) x hx, ?_⟩
      rw [smul_inv_smul]
  have hG : N.Gam L ⊔ N.R1 ≤ MulAction.stabilizer (V ≃ₗ[K] V) M := by
    refine sup_le (hstab _ ?_) (hstab _ ?_)
    · intro s hs x hx
      rw [← hint] at hx ⊢
      refine ⟨?_, unipotent_map_mem_V0 N.F N.F' ((hR s).1 hs.1).1 ((hR s).1 hs.1).2 x hx.2⟩
      have h1 : s • L = L := hs.2
      have h2 := Submodule.smul_mem_pointwise_smul x s L hx.1
      rw [h1] at h2
      exact h2
    · intro s hs x hx
      have h1 : s • x = x := (mem_fixingSubgroup_iff _).1 hs.2 x hx.2
      have h2 : s x = x := h1
      rw [h2]
      exact hx
  have hGR : N.Gam L ⊔ N.R1 ≤ N.R := sup_le inf_le_left inf_le_left
  have hle : 𝔠 ^ (3 * e + 11) ≤ Ideal.span {(N.T : 𝓞 K)} * 𝔠 ^ (3 * e + 10) := by
    rw [show 3 * e + 11 = (3 * e + 10) + 1 from rfl, pow_succ']
    exact Ideal.mul_mono_left fun x hx => Ideal.mem_span_singleton.2 (hcT x hx)
  obtain ⟨h0, hidx⟩ := GlobalTheory.T.relIndex_congruence_subgroup_le_absNorm_pow K V (N.Gam L ⊔ N.R1) M (𝔠 ^ (3 * e + 11)) (N.Gam Λ ⊔ N.R1) hMfg
    (pow_ne_zero _ hc0) (fun s hs => hG hs) (by
      intro s hs hcong
      obtain ⟨s', hs', hV, hP⟩ := GlobalTheory.T.hermFramePairNormalForm_congruence_lift_smallGroup K V H hK r N (𝔠 ^ (3 * e + 10))
        (star_stable_pow 𝔠 hcs (3 * e + 9)) s (hGR hs)
        (fun x hx => Submodule.smul_mono_left hle (hcong x hx))
      have hfix := GlobalTheory.T.stabilizer_hermitianLattice_of_deep_star_congruence K V H hK r N g Λ hg hΛ 𝔠 hc0 hcs hcT hcD e hsp hnear s' hs' hP
      have h1 : s' ∈ N.Gam Λ := ⟨hs'.1, hfix⟩
      have h2 : s'⁻¹ * s ∈ N.R1 := by
        refine ⟨N.R.mul_mem (N.R.inv_mem hs'.1) (hGR hs), (mem_fixingSubgroup_iff _).2 fun y hy => ?_⟩
        have h3 : s • y = s' • y := (hV y hy).symm
        rw [mul_smul, h3, inv_smul_smul]
      have h4 := mul_mem (Subgroup.mem_sup_left h1 : s' ∈ N.Gam Λ ⊔ N.R1) (Subgroup.mem_sup_right h2)
      rwa [mul_inv_cancel_left] at h4)
  have hd : Module.finrank K (Submodule.span K (M : Set V)) ≤ 2 * r + 1 := by
    have h1 : Submodule.span K (M : Set V) ≤ V0 N.F N.F' := Submodule.span_le.2 fun x hx => hx.2
    have h2 := Submodule.finrank_mono h1
    have h3 := hNF.2.2.2.2.1
    have h4 := N.j_le
    omega
  have hn : 1 ≤ Ideal.absNorm 𝔠 := Nat.one_le_iff_ne_zero.2 (fun h => hc0 (Ideal.absNorm_eq_zero_iff.1 h))
  have hfin : (N.Gam Λ ⊔ N.R1).relIndex (N.Gam L ⊔ N.R1) ≤
      Ideal.absNorm 𝔠 ^ ((3 * e + 11) * (2 * r + 1) ^ 2) := by
    refine hidx.trans ?_
    rw [map_pow, ← pow_mul]
    exact Nat.pow_le_pow_right hn (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hd 2))
  have hdiv : ∀ a b : ℕ, (a : ℝ) / (b : ℝ) ≤ a := by
    intro a b
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    · exact div_le_self (Nat.cast_nonneg a) (by exact_mod_cast hb)
  unfold GlobalTheory.HL.invVol
  refine (hdiv _ _).trans ?_
  exact_mod_cast hfin

end GlobalTheory.DegCnt
