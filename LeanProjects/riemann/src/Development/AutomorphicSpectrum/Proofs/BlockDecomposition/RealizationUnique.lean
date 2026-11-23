import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.OneSTr

open Module CrystallineSemistableComparison.Pb.Kap

namespace GlobalTheory.CompanionTheory.KapUniq

theorem eq_of_unit_smul_combination {K B V M : Type*} [Field K] [CommRing B] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [AddCommGroup M] [Module B M]
    (o : K →+* B) (μ : V → M) (c : B) (hc : IsUnit c)
    (hind : ∀ (m : ℕ) (bs : Basis (Fin m) K V) (g : Fin m → B),
      ∑ s, g s • μ (bs s) = 0 → ∀ s, g s = 0)
    (f f' : Dual K V →+ B)
    (hf : ∀ (k : K) (φ : Dual K V), f (k • φ) = o k * f φ)
    (hf' : ∀ (k : K) (φ : Dual K V), f' (k • φ) = o k * f' φ)
    (h : ∀ (m : ℕ) (bs : Basis (Fin m) K V),
      c • ∑ s, (f (bs.coord s) - f' (bs.coord s)) • μ (bs s) = 0) :
    f = f' := by
  classical
  let bs := Module.finBasis K V
  have h0 : ∑ s, (f (bs.coord s) - f' (bs.coord s)) • μ (bs s) = 0 := by
    obtain ⟨u, rfl⟩ := hc
    have := congrArg (fun x => ((u⁻¹ : Bˣ) : B) • x) (h _ bs)
    simpa [smul_smul] using this
  have hco : ∀ s, f (bs.coord s) = f' (bs.coord s) :=
    fun s => sub_eq_zero.mp (hind _ bs _ h0 s)
  have key : ∀ F : Dual K V →+ B, (∀ (k : K) (φ : Dual K V), F (k • φ) = o k * F φ) →
      ∀ φ : Dual K V, F φ = ∑ s, F (bs.coord s) * o (φ (bs s)) := by
    intro F hF φ
    have e : ∑ s, φ (bs s) • bs.coord s = φ := bs.sum_dual_apply_smul_coord φ
    calc F φ = F (∑ s, φ (bs s) • bs.coord s) := by rw [e]
      _ = _ := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun s _ => by rw [hF, mul_comm]
  ext φ
  rw [key f hf, key f' hf']
  exact Finset.sum_congr rfl fun s _ => by rw [hco]

theorem rho_unique {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K]
    (C : Chain.{1} Λ A B K) (hC : C.Good) {j : ℕ} (x : ∀ n, C.S n j)
    (f f' : Module.Dual K (C.V j) →+ B) : C.Rho x f → C.Rho x f' → f = f' := by
  rintro ⟨hfs, e, z, hz, hzb⟩ ⟨hfs', e', z', hz', hzb'⟩
  haveI := hC.fin j
  have hw : C.b j (((C.ℓ : A) ^ e) • z' - ((C.ℓ : A) ^ e') • z) = 0 := by
    apply hC.sep
    intro n
    rw [map_sub, map_smul, map_smul, hz n, hz' n, smul_smul, smul_smul, mul_comm, sub_self]
  have hb : ∀ (a : A) (y : C.Z j), C.b j (a • y) = C.ι a • C.b j y :=
    fun a y => (C.b j).map_smulₛₗ a y
  refine (eq_of_unit_smul_combination C.o (C.μ j) ((C.ℓ : B) ^ (e + e')) (hC.unit.pow _) ?_
    f' f hfs' hfs ?_).symm
  · intro m bs g hg s
    obtain ⟨g0, _, hu⟩ := hC.basis j bs 0
    have h1 := hu g hg.symm
    have h2 := hu 0 (by simp)
    exact congrFun (h1.trans h2.symm) s
  · intro m bs
    have h := hw
    rw [map_sub, hb, hb, ← hzb bs, ← hzb' bs] at h
    simp only [map_pow, map_natCast, smul_smul] at h
    simp_rw [sub_smul, Finset.sum_sub_distrib, smul_sub]
    rw [← h, pow_add, mul_comm ((C.ℓ : B) ^ e') ((C.ℓ : B) ^ e)]

end GlobalTheory.CompanionTheory.KapUniq
