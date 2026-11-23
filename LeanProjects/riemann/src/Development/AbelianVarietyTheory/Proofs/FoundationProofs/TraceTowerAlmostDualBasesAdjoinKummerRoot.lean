import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ

noncomputable section

open GlobalTheory.K5 GlobalTheory.KumDlog

namespace GlobalTheory.TraceTower

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem eq_on_fix {T : Tower p Ω} {r : Ω} {h h' : Gal p Ω} (hh : h ∈ Hinf T) (hh' : h' ∈ Hinf T)
    (e : h r = h' r) {x : Ω} (hx : x ∈ FixI (Hfix T r)) : h x = h' x := by
  have hm : h'⁻¹ * h ∈ Hfix T r := by
    refine ⟨(Hinf T).mul_mem ((Hinf T).inv_mem hh') hh, ?_⟩
    refine MulAction.mem_stabilizer_iff.2 ?_
    rw [AlgEquiv.smul_def, AlgEquiv.mul_apply, e]
    exact h'.symm_apply_apply r
  have h1 : h'.symm (h x) = x := hx.2 _ hm
  exact h'.symm_apply_eq.1 h1

end GlobalTheory.TraceTower

open GlobalTheory.TraceTower in
theorem GlobalTheory.traceTower_dualData : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (T : Tower p Ω) (n : ℕ) (r : Ω), IsInt p r → (∀ h ∈ Hinf T, ∃ i : ℕ, h r = T.ζ n ^ i * r) →
  ∀ (ι : Type) [Fintype ι] (u v : ι → Ω), (∀ k, u k ∈ FixI (Hfix T r)) → (∀ k, v k ∈ FixI (Hfix T r)) →
  ∑ k, u k * v k = (p : Ω) → (∀ h ∈ Hinf T, h r ≠ r → ∑ k, u k * h (v k) = 0) →
  ∃ tr : Ω → Ω, DualData (FixI (Hinf T)) (FixI (Hfix T r)) u v tr := by
  intro p _ Ω _ _ T n r _ hor ι _ u v hu hv huv hz
  classical
  have hfin : {ρ : Ω | ∃ h ∈ Hinf T, h r = ρ}.Finite := by
    refine ((Finset.range (p ^ n)).image (fun i => T.ζ n ^ i * r)).finite_toSet.subset ?_
    rintro ρ ⟨h, hh, rfl⟩
    obtain ⟨i, hi⟩ := hor h hh
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
    refine ⟨i % p ^ n, Nat.mod_lt _ (ppow_pos n), ?_⟩
    rw [hi]
    congr 1
    conv_rhs => rw [← Nat.div_add_mod i (p ^ n)]
    rw [pow_add, pow_mul, (T.prim n).pow_eq_one, one_pow, one_mul]
  set O := hfin.toFinset with hOdef
  have hO : ∀ ρ, ρ ∈ O ↔ ∃ h ∈ Hinf T, h r = ρ := fun ρ => hfin.mem_toFinset
  have hg0 : ∀ ρ, ∃ f : Gal p Ω, ρ ∈ O → f ∈ Hinf T ∧ f r = ρ := by
    intro ρ
    by_cases hρ : ρ ∈ O
    · obtain ⟨h, hh, e⟩ := (hO ρ).1 hρ
      exact ⟨h, fun _ => ⟨hh, e⟩⟩
    · exact ⟨1, fun h => absurd h hρ⟩
  choose g hg using hg0
  have hrO : r ∈ O := (hO r).2 ⟨1, (Hinf T).one_mem, rfl⟩
  have fixr : ∀ x ∈ FixI (Hfix T r), g r x = x := fun x hx =>
    hx.2 _ ⟨(hg r hrO).1, MulAction.mem_stabilizer_iff.2 (by rw [AlgEquiv.smul_def]; exact (hg r hrO).2)⟩
  have kk : ∀ f ∈ Hinf T, ∀ ρ ∈ O, ∀ x ∈ FixI (Hfix T r), f (g ρ x) = g (f ρ) x ∧ f ρ ∈ O := by
    intro f hf ρ hρ x hx
    have hm : f * g ρ ∈ Hinf T := (Hinf T).mul_mem hf (hg ρ hρ).1
    have hr' : (f * g ρ) r = f ρ := by rw [AlgEquiv.mul_apply, (hg ρ hρ).2]
    have hfO : f ρ ∈ O := (hO _).2 ⟨_, hm, hr'⟩
    refine ⟨?_, hfO⟩
    have := eq_on_fix hm (hg _ hfO).1 (by rw [hr', (hg _ hfO).2]) hx
    rwa [AlgEquiv.mul_apply] at this
  have zero_inv : ∀ ρ ∈ O, ρ ≠ r → ∑ k, v k * g ρ (u k) = 0 := by
    intro ρ hρ hne
    set f := g ρ
    have hf : f ∈ Hinf T := (hg ρ hρ).1
    have hne' : f⁻¹ r ≠ r := by
      intro e
      apply hne
      rw [← (hg ρ hρ).2]
      have e' : f.symm r = r := e
      conv_lhs => rw [← e']
      exact f.apply_symm_apply r
    have h0 := hz _ ((Hinf T).inv_mem hf) hne'
    calc ∑ k, v k * f (u k) = f (∑ k, u k * f⁻¹ (v k)) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_mul]
          have : f (f⁻¹ (v k)) = v k := f.apply_symm_apply (v k)
          rw [this, mul_comm]
      _ = 0 := by rw [h0, map_zero]
  refine ⟨fun x => ∑ ρ ∈ O, g ρ x, fun x hx => ⟨hx.1, fun f hf => hx.2 f hf.1⟩, fun x hx => hx.1,
    hu, hv, ?_, ?_, ?_, ?_, ?_, huv⟩
  · intro x hx
    refine ⟨int_sum _ _ fun ρ _ => int_gal _ hx.1, fun f hf => ?_⟩
    show f (∑ ρ ∈ O, g ρ x) = ∑ ρ ∈ O, g ρ x
    rw [map_sum]
    calc ∑ ρ ∈ O, f (g ρ x) = ∑ ρ ∈ O, g (f ρ) x :=
          Finset.sum_congr rfl fun ρ hρ => (kk f hf ρ hρ x hx).1
      _ = ∑ ρ ∈ O, g ρ x := by
        refine Finset.sum_nbij' (fun ρ => f ρ) (fun ρ => f.symm ρ) (fun ρ hρ => (kk f hf ρ hρ x hx).2)
          (fun ρ hρ => (kk f⁻¹ ((Hinf T).inv_mem hf) ρ hρ x hx).2) (fun ρ _ => f.symm_apply_apply ρ)
          (fun ρ _ => f.apply_symm_apply ρ) (fun ρ _ => rfl)
  · intro x _ y _
    simp only [map_add, Finset.sum_add_distrib]
  · intro b hb x _
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    rw [map_mul, hb.2 _ (hg ρ hρ).1]
  · intro y hy
    calc ∑ k, u k * ∑ ρ ∈ O, g ρ (v k * y) = ∑ ρ ∈ O, g ρ y * ∑ k, u k * g ρ (v k) := by
          simp only [map_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun k _ => by ring
      _ = g r y * ∑ k, u k * g r (v k) := by
          refine Finset.sum_eq_single r (fun ρ hρ hne => ?_) (fun h => absurd hrO h)
          rw [hz _ (hg ρ hρ).1 (by rw [(hg ρ hρ).2]; exact hne), mul_zero]
      _ = p * y := by
          rw [fixr y hy, Finset.sum_congr rfl fun k _ => by rw [fixr (v k) (hv k)], huv, mul_comm]
  · intro y hy
    calc ∑ k, v k * ∑ ρ ∈ O, g ρ (u k * y) = ∑ ρ ∈ O, g ρ y * ∑ k, v k * g ρ (u k) := by
          simp only [map_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun k _ => by ring
      _ = g r y * ∑ k, v k * g r (u k) := by
          refine Finset.sum_eq_single r (fun ρ hρ hne => ?_) (fun h => absurd hrO h)
          rw [zero_inv ρ hρ hne, mul_zero]
      _ = p * y := by
          rw [fixr y hy, Finset.sum_congr rfl fun k _ => by rw [fixr (u k) (hu k)], ← huv,
            mul_comm]
          congr 1
          exact Finset.sum_congr rfl fun k _ => mul_comm _ _
