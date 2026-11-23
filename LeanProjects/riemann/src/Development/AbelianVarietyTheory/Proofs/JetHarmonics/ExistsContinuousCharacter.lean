import Mathlib
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.JetMomTA
import Formalism.LocalToGlobal.GlobalTheory.GL3.PThIndep
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ParabolicPointMembership
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTraceNorm

noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.ParabolicPointMembership

namespace GlobalTheory.CommutatorCharacter

variable {D : D7} {N N' : ℕ}

theorem Hf_nsmul_swap (T : Tor D) (k : ℕ) (w x : VC D N N') : Hf D T (k • w) x = Hf D T w (k • x) := by
  unfold Hf
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, nsmul_eq_mul, map_mul, map_natCast]
  ring

theorem kap_add_nsmul (T : Tor D) {Λ : AddSubgroup (VC D N N')} (hI : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.HfInt T Λ) (k : ℕ)
    (u : VC D N N') {w x : VC D N N'} (hw : w ∈ Λ) (hx : k • x ∈ Λ) : kap D T (u + k • w) x = kap D T u x := by
  obtain ⟨a, b, -, h⟩ := hI w hw _ hx
  have him : (Hf D T (k • w) x).im = b := by rw [Hf_nsmul_swap, h]; simp
  unfold kap
  rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.Hf_add_left, Complex.add_im, him, Complex.exp_eq_exp_iff_exists_int]
  exact ⟨-b, by push_cast; ring⟩

def vecHom (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Matrix (Fin N') (Fin N) D.host.E →+ VC D N N' :=
  AddMonoidHom.mk' (vecOf D cc δ) (GlobalTheory.PlaceComponents.vecOf_add D cc δ)

theorem vecHom_apply (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (A : Matrix (Fin N') (Fin N) D.host.E) :
    vecHom cc δ A = vecOf D cc δ A := rfl

theorem continuous_toZModPow {p : ℕ} [Fact p.Prime] (n : ℕ) {X : Type*} [TopologicalSpace X]
    (f : ZMod (p ^ n) → X) : Continuous fun a : ℤ_[p] => f (PadicInt.toZModPow n a) := by
  refine (IsLocallyConstant.comp (f := PadicInt.toZModPow n) ?_ f).continuous
  rw [IsLocallyConstant.iff_eventually_eq]
  intro a
  have hp : (0 : ℝ) < (p : ℝ) ^ (-(n : ℤ)) := zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  filter_upwards [Metric.closedBall_mem_nhds a hp] with y hy
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow]
  simpa [dist_eq_norm] using hy

theorem exists_continuous_character :
    ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' : ℕ)
      (Λ : AddSubgroup (VC D N N')), Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.HfInt (tor0 D cc δ) Λ →
      ∀ (n r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (x : VC D N N'),
      (∀ i, vecOf D cc δ (b i) ∈ Λ) → p ^ n • x ∈ Λ →
      ∃ ψ : C(Fin r → ℤ_[p], ℂ_[p]),
        (∀ a : Fin r → ℤ_[p], ψ a =
          lamC lam (kap D (tor0 D cc δ) (Formalism.L2.Ker.I3.JetMomA.vecZ D (tor0 D cc δ) δ p n b a) x)) ∧
        ∀ a : Fin r → ℤ, ψ (fun i => (a i : ℤ_[p])) =
          lamC lam (kap D (tor0 D cc δ) (vecOf D cc δ (∑ i, (a i : D.host.E) • b i)) x) := by
  intro D cc δ p _ lam N N' Λ hI n r b x hb hx
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  let F : (Fin r → ZMod (p ^ n)) → ℂ_[p] := fun c =>
    lamC lam (kap D (tor0 D cc δ) (vecOf D cc δ (∑ i, (((c i).val : ℕ) : D.host.E) • b i)) x)
  have hc : Continuous fun a : Fin r → ℤ_[p] => F fun i => PadicInt.toZModPow n (a i) := by
    letI : TopologicalSpace (ZMod (p ^ n)) := ⊥
    haveI : DiscreteTopology (ZMod (p ^ n)) := ⟨rfl⟩
    exact (continuous_of_discreteTopology (f := F)).comp
      (continuous_pi fun i => (continuous_toZModPow n id).comp (continuous_apply i))
  refine ⟨⟨_, hc⟩, fun a => rfl, fun a => ?_⟩
  show F _ = _
  have hw : vecOf D cc δ (∑ i, (a i / (p ^ n : ℕ)) • b i) ∈ Λ := by
    rw [← vecHom_apply, map_sum]
    exact sum_mem fun i _ => by rw [map_zsmul]; exact zsmul_mem (hb i) _
  have hs : ∑ i, (a i : D.host.E) • b i =
      ∑ i, (((PadicInt.toZModPow n (a i : ℤ_[p])).val : ℕ) : D.host.E) • b i +
        p ^ n • ∑ i, (a i / (p ^ n : ℕ)) • b i := by
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_intCast, ← Int.cast_natCast, ZMod.val_intCast, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul,
      ← natCast_zsmul, smul_smul, ← add_smul, Int.emod_add_mul_ediv]
  simp only [F]
  rw [hs, ← vecHom_apply cc δ (_ + _), map_add, map_nsmul, vecHom_apply, vecHom_apply,
    kap_add_nsmul _ hI _ _ hw hx]

end GlobalTheory.CommutatorCharacter
