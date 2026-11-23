import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.TmulEqSmulToV

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC TensorProduct

namespace CrystallineSemistableComparison.AdicCoh

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section
variable (hI : ZIn) (M : Model l K) {r : ℕ} {Y : Fin r → Scheme.{0}}
  (j : ∀ s, Y s ⟶ GlobalTheory.Et.geom (PadicAlgCl l) M.q) (hj : IsSum j) (i j' : ℕ)
  (gen : ∀ s, Hl l (sch.obj (Y s)) ((i + j' : ℕ) : ℤ) 0) (hgen : ∀ s x, ∃ c : ℤ_[l], x = c • gen s)

theorem gsmul_zero {N : Type*} [AddCommGroup N] [Module ℤ_[l] N] (a : ℤ_[l]) : a • (0 : N) = 0 := smul_zero a

theorem hsum_ij : ((i : ℕ) : ℤ) + ((j' : ℕ) : ℤ) = ((i + j' : ℕ) : ℤ) := by push_cast; rfl

include hgen in
theorem phi_form (s : Fin r) (y' : Hl l (sch.obj (Y s)) j' 0) (x : M.T i) :
    ∃ a : ℤ_[l], cupL l hI (hsum_ij i j') (add_zero 0) x (extS l hI j hj j' 0 s y') =
      a • extS l hI j hj _ 0 s (gen s) := by
  obtain ⟨a, ha⟩ := hgen s (pullHl l (sch.map (j s)) _ 0
    (cupL l hI (hsum_ij i j') (add_zero 0) x (extS l hI j hj j' 0 s y')))
  refine ⟨a, sum_eq l hI j hj _ 0 _ _ fun t => ?_⟩
  rw [LinearMap.map_smul]
  by_cases ht : t = s
  · subst ht
    rw [ha, extS_self]
  · rw [pull_cupL, extS_ne l hI j hj j' 0 s y' ht, cupL_zero_right, extS_ne l hI j hj _ 0 s (gen s) ht]
    exact (gsmul_zero (N := Hl l (sch.obj (Y t)) ((i + j' : ℕ) : ℤ) 0) a).symm

include hgen in
theorem f_exists (s : Fin r) (y' : Hl l (sch.obj (Y s)) j' 0) :
    ∃ f : Module.Dual ℚ_[l] (M.V i), ∀ x : M.T i, ∃ z, M.CupT x (extS l hI j hj j' 0 s y') z ∧
        M.toV (i + j') z = f (M.toV i x) • M.toV (i + j') (extS l hI j hj _ 0 s (gen s)) := by
  set g := M.toV (i + j') (extS l hI j hj _ 0 s (gen s)) with hgdef
  have hz : ∀ x : M.T i, ∃ a : ℤ_[l], M.toV (i + j') (cupL l hI (hsum_ij i j') (add_zero 0) x (extS l hI j hj j' 0 s y')) =
      algebraMap ℤ_[l] ℚ_[l] a • g := fun x => by
    obtain ⟨a, ha⟩ := phi_form hI M j hj i j' gen hgen s y' x
    exact ⟨a, by rw [ha]; exact toV_smul M (i + j') a _⟩
  by_cases hg0 : g = 0
  · refine ⟨0, fun x => ⟨cupL l hI (hsum_ij i j') (add_zero 0) x (extS l hI j hj j' 0 s y'), fun k => rfl, ?_⟩⟩
    obtain ⟨a, ha⟩ := hz x
    rw [ha, hg0, smul_zero, smul_zero]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Module.Dual ℚ_[l] (M.V (i + j')), ψ g ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hg0 ((Module.forall_dual_apply_eq_zero_iff ℚ_[l] g).1 hne)
  let Φ : Hl l M.spc (i : ℤ) 0 →ₗ[ℤ_[l]] Hl l M.spc ((i + j' : ℕ) : ℤ) 0 :=
    cupR l hI (hsum_ij i j') (add_zero 0) (extS l hI j hj j' 0 s y')
  refine ⟨(ψ g)⁻¹ • (ψ ∘ₗ Φ.baseChange ℚ_[l]), fun x => ⟨cupL l hI (hsum_ij i j') (add_zero 0) x (extS l hI j hj j' 0 s y'), fun k => rfl, ?_⟩⟩
  obtain ⟨a, ha⟩ := hz x
  have e1 : (Φ.baseChange ℚ_[l]) (M.toV i x) = M.toV (i + j') (Φ x) := LinearMap.baseChange_tmul _ _ _
  have e2 : ((ψ g)⁻¹ • (ψ ∘ₗ Φ.baseChange ℚ_[l])) (M.toV i x) = algebraMap ℤ_[l] ℚ_[l] a := by
    have h3 : ((ψ g)⁻¹ • (ψ ∘ₗ Φ.baseChange ℚ_[l])) (M.toV i x) = (ψ g)⁻¹ * ψ (algebraMap ℤ_[l] ℚ_[l] a • g) := by
      change (ψ g)⁻¹ * ψ ((Φ.baseChange ℚ_[l]) (M.toV i x)) = _
      exact congrArg (fun w => (ψ g)⁻¹ * ψ w) (e1.trans ha)
    rw [h3, map_smul, smul_eq_mul, ← mul_assoc, mul_comm _ (algebraMap ℤ_[l] ℚ_[l] a), mul_assoc, inv_mul_cancel₀ hψ,
      mul_one]
  exact ha.trans (congrArg (· • g) e2.symm)

end

theorem dual_span (hI : ZIn) (M : Model l K) (hM : M.Good) (d : ℕ) (hc : M.Conn d) {r : ℕ} {Y : Fin r → Scheme.{0}}
    (j : ∀ s, Y s ⟶ GlobalTheory.Et.geom (PadicAlgCl l) M.q) (hj : IsSum j) (hint : ∀ s, IsIntegral (Y s))
    (i j' : ℕ) (hij : i + j' = 2 * d) (gen : ∀ s, Hl l (sch.obj (Y s)) ((i + j' : ℕ) : ℤ) 0)
    (hgen : ∀ s x, ∃ c : ℤ_[l], x = c • gen s) :
    Submodule.span ℚ_[l] {f : Module.Dual ℚ_[l] (M.V i) | ∃ (s : Fin r) (y : M.T j'),
      ∀ x : M.T i, ∃ z, M.CupT x y z ∧
        M.toV (i + j') z = f (M.toV i x) • M.toV (i + j') (extS l hI j hj _ 0 s (gen s))} = ⊤ := by
  have := fin_of hI M hM i
  refine Adic.span_dual _ fun v hv => ?_
  obtain ⟨c, x, rfl⟩ := Adic.tmul_surj v
  by_cases hc0 : c = 0
  · rw [hc0, zero_tmul]
  have hN : ((i + j' : ℕ) : ℤ) = 2 * (d : ℤ) := by exact_mod_cast hij
  obtain ⟨e, he⟩ := tors_of_restr l hI j hj (i : ℤ) 0 x fun s => by
    have := hint s
    obtain ⟨hp, hs⟩ := AdicGeo.comp_str hM hc j hj s
    refine hl_nondeg l hI (j s ≫ AdicGeo.str M) d (i : ℤ) (j' : ℤ) _ (hsum_ij i j') hN _ fun y' => ?_
    obtain ⟨f, hf⟩ := f_exists hI M j hj i j' gen hgen s y'
    have h0 := hv f ⟨s, _, hf⟩
    rw [tmul_eq_smul_toV M i c x, LinearMap.map_smul, smul_eq_mul, mul_eq_zero] at h0
    have h0' := h0.resolve_left hc0
    obtain ⟨z, hz, hzv⟩ := hf x
    rw [h0', zero_smul] at hzv
    obtain ⟨n, hn⟩ := (Adic.tmul_eq_zero (M := Hl l M.spc ((i + j' : ℕ) : ℤ) 0) z).1 hzv
    have hz' : z = cupL l hI (hsum_ij i j') (add_zero 0) x (extS l hI j hj j' 0 s y') := Subtype.ext (funext hz)
    refine ⟨n, ?_⟩
    rw [← extS_self l hI j hj j' 0 s y', ← pull_cupL, ← LinearMap.map_smul, ← hz', hn, map_zero]
  exact tmul_zero_of c x he

end CrystallineSemistableComparison.AdicCoh
