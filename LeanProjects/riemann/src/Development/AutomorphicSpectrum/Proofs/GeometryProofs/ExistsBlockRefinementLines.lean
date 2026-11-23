import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsJoinBlocksStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleGlobalGeneratorsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LinesDeg

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem block_chart {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {c : (k : K) → J k} {p : Cpt ξ}
    (h : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p) (k : K) :
    InChart ξ (fun i : J k => y ⟨k, i⟩) (c k) p := by
  classical
  obtain ⟨h0, hr⟩ := h
  have hne : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.mp h0) k (Finset.mem_univ k)
  refine ⟨hne k, fun j => ?_⟩
  have hreg := hr (Function.update c k j)
  have e : (∏ k', y ⟨k', Function.update c k j k'⟩) / ∏ k', y ⟨k', c k'⟩ = y ⟨k, j⟩ / y ⟨k, c k⟩ := by
    rw [← Finset.mul_prod_erase Finset.univ (fun k' => y ⟨k', Function.update c k j k'⟩) (Finset.mem_univ k),
      ← Finset.mul_prod_erase Finset.univ (fun k' => y ⟨k', c k'⟩) (Finset.mem_univ k)]
    have hrest : ∏ k' ∈ Finset.univ.erase k, y ⟨k', Function.update c k j k'⟩ =
        ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩ :=
      Finset.prod_congr rfl fun k' hk' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk')]
    have hP : ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩ ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k' _ => hne k'
    simp only [hrest, Function.update_self]
    exact mul_div_mul_right _ _ hP
  rw [← e]
  exact hreg

theorem segre_chart {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {c : (k : K) → J k} {p : Cpt ξ}
    (h : ∀ k, InChart ξ (fun i : J k => y ⟨k, i⟩) (c k) p) :
    InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p := by
  refine ⟨Finset.prod_ne_zero_iff.mpr fun k _ => (h k).1, fun c' => ?_⟩
  show (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩ ∈ regAt ξ p
  rw [← Finset.prod_div_distrib]
  exact prod_mem fun k _ => (h k).2 (c' k)

theorem exists_chart_of_gen {Q : Type} {t : Q → Ω} {d : Ω} (hd : d ≠ 0) {L : Lat ξ Ω} {p : Cpt ξ}
    (hm : ∀ i, t i / d ∈ L p) (hg : ∃ i, L.IsGenAt p (t i / d)) : ∃ i, InChart ξ t i p := by
  obtain ⟨i, hi0, hi⟩ := hg
  have ht : t i ≠ 0 := fun h => hi0 (by simp [h])
  refine ⟨i, ht, fun j => ?_⟩
  have hj := hm j
  rw [hi, Submodule.mem_span_singleton] at hj
  obtain ⟨r, hr⟩ := hj
  rw [Subring.smul_def, smul_eq_mul] at hr
  have : t j / t i = r := by
    field_simp at hr ⊢
    exact hr.symm
  rw [this]
  exact r.2

theorem isGen_of_chart {Q : Type} {t : Q → Ω} {d : Ω} (hd : d ≠ 0) {L : Lat ξ Ω} {p : Cpt ξ} {i₀ : Q}
    (hc : InChart ξ t i₀ p) (hm : ∀ i, t i / d ∈ L p) (hg : ∃ i, L.IsGenAt p (t i / d)) :
    L p = Submodule.span (regAt ξ p) {t i₀ / d} := by
  obtain ⟨i, -, hi⟩ := hg
  refine le_antisymm ?_ ((Submodule.span_singleton_le_iff_mem _ _).mpr (hm i₀))
  rw [hi, Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
  refine ⟨⟨t i / t i₀, hc.2 i⟩, ?_⟩
  rw [Subring.smul_def, smul_eq_mul]
  have := hc.1
  show t i / t i₀ * (t i₀ / d) = t i / d
  field_simp

abbrev joinJ {K I : Type} (J : K → Type) (J₂ : I → Type) : K ⊕ I → Type := Sum.elim J J₂

def joinY {K I : Type} {J : K → Type} {J₂ : I → Type} (y : (Σ k, J k) → Ω) (s : (Σ i, J₂ i) → Ω) :
    (Σ k, joinJ J J₂ k) → Ω
  | ⟨Sum.inl k, j⟩ => y ⟨k, j⟩
  | ⟨Sum.inr i, j⟩ => s ⟨i, j⟩

def joinFintype {K I : Type} {J : K → Type} {J₂ : I → Type} [∀ k, Fintype (J k)] [∀ i, Fintype (J₂ i)] :
    ∀ k, Fintype (joinJ J J₂ k)
  | Sum.inl k => inferInstanceAs (Fintype (J k))
  | Sum.inr i => inferInstanceAs (Fintype (J₂ i))

end GlobalTheory.CompanionTheory.Ar.LinesDeg

namespace GlobalTheory.CompanionTheory.Ar

open LinesDeg in

theorem exists_addBlocks_isDegOn : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (I : Type) [Fintype I] (Λ : I → Lat ξ Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ i, (Λ i).IsVB 1 ⊤) → ∃ (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k)) (y' : (Σ k, J' k) → Ω) (κ : K → K') (v : ∀ k, J k ≃ J' (κ k)), Function.Injective κ ∧ (∀ k i, y' ⟨κ k, v k i⟩ = y ⟨k, i⟩) ∧ CoordTie ℤ ξ (fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩) ∧ ∀ i, ∃ (a : K' → ℤ) (e₀ : Ω), (Λ i).IsDegOn Set.univ y' a e₀ := by
  intro X Ω _ ξ K _ J _ y I _ Λ ht hvb
  classical
  have key := fun i => GlobalTheory.T.line_bundle_global_generators X Ω ξ ((k : K) → J k) (fun c' => ∏ k, y ⟨k, c' k⟩) (Λ i) ht (hvb i)
  choose n m s hmem hgen using key
  let J₂ : I → Type := fun i => Fin (m i + 1)
  let s₂ : (Σ i, J₂ i) → Ω := fun q => s q.1 q.2
  have hbpf : ∀ (i : I) (p : Cpt ξ), ∃ j, InChart ξ (fun j' : J₂ i => s₂ ⟨i, j'⟩) j p := by
    intro i p
    obtain ⟨c, hc⟩ := ht.cover p
    exact exists_chart_of_gen (t := s i) (pow_ne_zero _ hc.1) (hmem i p c hc) (hgen i p c hc)
  have hadd := GlobalTheory.T.coords_join_blocks X Ω ξ K J y I J₂ s₂ ht hbpf
  refine ⟨K ⊕ I, inferInstance, joinJ J J₂, joinFintype, joinY y s₂, Sum.inl, fun k => Equiv.refl _,
    Sum.inl_injective, fun k i => rfl, ?_, fun i => ?_⟩
  · have e : (fun c' : (k : K ⊕ I) → joinJ J J₂ k => ∏ k, joinY y s₂ ⟨k, c' k⟩) =
        fun c' : (k : K ⊕ I) → Sum.elim J J₂ k =>
          (∏ k, y ⟨k, c' (Sum.inl k)⟩) * ∏ k, s₂ ⟨k, c' (Sum.inr k)⟩ :=
      funext fun c' => Fintype.prod_sum_type (fun k => joinY y s₂ ⟨k, c' k⟩)
    rw [e]
    exact hadd
  · refine ⟨Sum.elim (fun _ => -(n i : ℤ)) (fun i' => if i' = i then 1 else 0), 1, one_ne_zero, ?_⟩
    intro p _ c hc
    have hb := block_chart hc
    let c₀ : (k : K) → J k := fun k => c (Sum.inl k)
    have hx : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c₀ p :=
      segre_chart fun k => hb (Sum.inl k)
    have hs : InChart ξ (s i) (c (Sum.inr i)) p := hb (Sum.inr i)
    have hP : ∏ k, y ⟨k, c₀ k⟩ ≠ 0 := hx.1
    have hgen' := isGen_of_chart (t := s i) (pow_ne_zero (n i) hP) hs (hmem i p c₀ hx) (hgen i p c₀ hx)
    have hprod : (∏ k : K ⊕ I, joinY y s₂ ⟨k, c k⟩ ^
        (Sum.elim (fun _ => -(n i : ℤ)) (fun i' => if i' = i then 1 else 0) k : ℤ)) • (1 : Ω) =
        s i (c (Sum.inr i)) / (∏ k, y ⟨k, c₀ k⟩) ^ n i := by
      rw [Fintype.prod_sum_type, smul_eq_mul, _root_.mul_one]
      have h1 : ∏ k : K, joinY y s₂ ⟨Sum.inl k, c (Sum.inl k)⟩ ^
          (Sum.elim (fun _ => -(n i : ℤ)) (fun i' => if i' = i then (1 : ℤ) else 0) (Sum.inl k : K ⊕ I) : ℤ) =
          ((∏ k, y ⟨k, c₀ k⟩) ^ n i)⁻¹ := by
        simp only [Sum.elim_inl]
        rw [Finset.prod_zpow, zpow_neg, zpow_natCast]
        rfl
      have h2 : ∏ i' : I, joinY y s₂ ⟨Sum.inr i', c (Sum.inr i')⟩ ^
          (Sum.elim (fun _ => -(n i : ℤ)) (fun i' => if i' = i then (1 : ℤ) else 0) (Sum.inr i' : K ⊕ I) : ℤ) =
          s i (c (Sum.inr i)) := by
        rw [Fintype.prod_eq_single i]
        · simp only [Sum.elim_inr, if_true, zpow_one]
          rfl
        · intro i' hi'
          simp [hi']
      rw [h1, h2, div_eq_mul_inv, _root_.mul_comm]
    rw [hprod]
    exact hgen'

end GlobalTheory.CompanionTheory.Ar
