import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.OneSTr

set_option backward.isDefEq.respectTransparency false

open CrystallineSemistableComparison.Pb.Kap

namespace GlobalTheory.CompanionTheory.KapRho

theorem semilinear_eq_sum_coord {K B : Type*} {V : Type*} [Field K] [CommRing B] [AddCommGroup V]
    [Module K V] (o : K →+* B) (f : Module.Dual K V →+ B)
    (hf : ∀ (k : K) φ, f (k • φ) = o k * f φ) {m : ℕ} (bs : Module.Basis (Fin m) K V)
    (φ : Module.Dual K V) : f φ = ∑ s, f (bs.coord s) * o (φ (bs s)) := by
  have hφ : φ = ∑ s, φ (bs s) • bs.coord s := by
    refine bs.ext fun t => ?_
    simp [LinearMap.sum_apply, Finsupp.single_apply]
  conv_lhs => rw [hφ]
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hf, mul_comm]

theorem rho_cup :
    ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K)
      (hC : C.Good) (P : Cup C), P.Good → ∀ {i j : ℕ} (x : ∀ n, C.S n i) (y : ∀ n, C.S n j)
      (f : Module.Dual K (C.V i) →+ B) (g : Module.Dual K (C.V j) →+ B)
      (h : Module.Dual K (C.V (i + j)) →+ B), C.Rho x f → C.Rho y g →
      C.Rho (fun n => P.cS n i j (x n) (y n)) h →
      ∀ {m m' : ℕ} (bs : Module.Basis (Fin m) K (C.V i)) (bs' : Module.Basis (Fin m') K (C.V j))
        (φ : Module.Dual K (C.V (i + j))),
        h φ = ∑ s, ∑ s', f (bs.coord s) * g (bs'.coord s') *
          C.o (φ (P.cV i j (bs s) (bs' s'))) := by
  intro Λ A B K _ _ _ _ C hC P hP i j x y f g h hf hg hh m m' bs bs' φ
  obtain ⟨-, e, z, hzr, hzb⟩ := hf
  obtain ⟨-, e', w, hwr, hwb⟩ := hg
  obtain ⟨hh1, e'', u, hur, hub⟩ := hh
  haveI := hC.fin (i + j)
  let b := Module.finBasis K (C.V (i + j))
  have hv : ∀ n, C.red n (i + j) (P.cZ i j z w) =
      ((C.ℓ : A) ^ (e + e')) • C.r n (i + j) (P.cS n i j (x n) (y n)) := by
    intro n
    rw [hP.red, hzr, hwr, hP.r, map_smul, LinearMap.map_smul₂, smul_smul, pow_add, mul_comm]
  have hd : C.b (i + j) (((C.ℓ : A) ^ (e + e')) • u - ((C.ℓ : A) ^ e'') • P.cZ i j z w) = 0 := by
    refine hC.sep _ _ fun n => ?_
    have hu := hur n
    simp only at hu
    rw [map_sub, map_smul, map_smul, hu, hv n, smul_smul, smul_smul, mul_comm, sub_self]
  have key : ((C.ℓ : B) ^ (e + e')) • C.b (i + j) u =
      ((C.ℓ : B) ^ e'') • C.b (i + j) (P.cZ i j z w) := by
    rw [map_sub, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, sub_eq_zero] at hd
    simpa only [map_pow, map_natCast] using hd
  let c : Fin (Module.finrank K (C.V (i + j))) → B := fun t =>
    ∑ s, ∑ s', f (bs.coord s) * g (bs'.coord s') *
      C.o (b.coord t (P.cV i j (bs s) (bs' s')))
  have hμ : ∀ s s', P.cW i j (C.μ i (bs s)) (C.μ j (bs' s')) =
      ∑ t, C.o (b.coord t (P.cV i j (bs s) (bs' s'))) • C.μ (i + j) (b t) := by
    intro s s'
    rw [← hP.μ]
    conv_lhs => rw [← b.sum_repr (P.cV i j (bs s) (bs' s'))]
    rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [LinearMap.map_smulₛₗ, Module.Basis.coord_apply]
  have hcup : P.cW i j (∑ s, f (bs.coord s) • C.μ i (bs s))
      (∑ s', g (bs'.coord s') • C.μ j (bs' s')) = ∑ t, c t • C.μ (i + j) (b t) := by
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, hμ, c,
      Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s' _ => Finset.sum_congr rfl fun t _ => ?_
    congr 1
    ring
  have hcoef : ∑ t, h (b.coord t) • C.μ (i + j) (b t) = ∑ t, c t • C.μ (i + j) (b t) := by
    have hu : IsUnit ((C.ℓ : B) ^ (e + e') * (C.ℓ : B) ^ e'') :=
      (hC.unit.pow _).mul (hC.unit.pow _)
    refine (hu.smul_left_cancel).1 ?_
    rw [hP.b, ← hub b, ← hzb bs, ← hwb bs', map_smul, LinearMap.map_smul₂, hcup, smul_smul,
      smul_smul, smul_smul] at key
    have hl : (C.ℓ : B) ^ e'' * (C.ℓ : B) ^ e' * (C.ℓ : B) ^ e =
        (C.ℓ : B) ^ (e + e') * (C.ℓ : B) ^ e'' := by ring
    rwa [hl] at key
  have hc : ∀ t, h (b.coord t) = c t := by
    obtain ⟨g₀, -, hg₀⟩ := hC.basis (i + j) b (∑ t, c t • C.μ (i + j) (b t))
    have h1 := hg₀ c rfl
    have h2 := hg₀ (fun t => h (b.coord t)) hcoef.symm
    exact fun t => congrFun (h2.trans h1.symm) t
  have hφ : ∀ s s', C.o (φ (P.cV i j (bs s) (bs' s'))) =
      ∑ t, C.o (b.coord t (P.cV i j (bs s) (bs' s'))) * C.o (φ (b t)) := by
    intro s s'
    conv_lhs => rw [← b.sum_repr (P.cV i j (bs s) (bs' s'))]
    simp only [map_sum, map_smul, smul_eq_mul, map_mul, Module.Basis.coord_apply]
  refine (semilinear_eq_sum_coord C.o h hh1 b φ).trans ?_
  simp only [hc, c, hφ, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s' _ => Finset.sum_congr rfl fun t _ => ?_
  rw [mul_assoc]

end GlobalTheory.CompanionTheory.KapRho
