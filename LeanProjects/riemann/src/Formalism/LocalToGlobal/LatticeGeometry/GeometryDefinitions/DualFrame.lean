import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
import Formalism.QuotientMetricDivisors.Statement
import Formalism.SatakeDualWeyl.Statement

noncomputable section

open Module Matrix

namespace Formalism.L2.Geo.Def.G1

section Frame

variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [StarRing K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module R V]
  [IsScalarTower R K V]

theorem dual_frame (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (hnd : h.Nondegenerate)
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (L : Submodule R V) (hL : Submodule.IsLattice K L) :
    ∃ (n : ℕ) (g w : Fin n → V), (∀ i, g i ∈ L) ∧ (∀ i, w i ∈ Formalism.HermitianLatticesTheory.dual h L) ∧
      ∀ z : V, z = ∑ i, h (w i) z • g i := by
  classical
  have hsp : Submodule.span K (L : Set V) = ⊤ := hL.span_eq_top

  obtain ⟨s, hsL, hspan, hli⟩ := exists_linearIndependent K (L : Set V)
  haveI : Fintype s := (LinearIndependent.setFinite hli).fintype
  let b : Module.Basis s K V := Module.Basis.mk hli (by rw [Subtype.range_coe, hspan, hsp])
  have hbL : ∀ j, b j ∈ L := fun j => by
    rw [show b j = (j : V) from Module.Basis.mk_apply hli _ j]; exact hsL j.2
  obtain ⟨bs, hbs⟩ := Formalism.HermitianLatticesTheory.dualLattice_dualBasis h hnd b
  have hbs' : ∀ j k, h (bs j) (b k) = if k = j then 1 else 0 := fun j k => by
    rw [← hs.eq (b k) (bs j), hbs k j]; split_ifs <;> simp
  have hcoord : ∀ z : V, z = ∑ j, h (bs j) z • b j := by
    have hlin : (LinearMap.id : V →ₗ[K] V) = ∑ j, (h (bs j)).smulRight (b j) := by
      apply b.ext; intro k
      simp [LinearMap.smulRight_apply, hbs']
    intro z
    simpa using congrArg (fun F : V →ₗ[K] V => F z) hlin

  haveI : Module.Finite R L := Module.Finite.iff_fg.2 hL.fg
  haveI : Module.Flat R L := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨a, hax⟩ := (Submodule.mem_torsion_iff x).1 hx
    have ha0 : algebraMap R K (a : R) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2
    have h1 : algebraMap R K (a : R) • (x : V) = 0 := by
      rw [algebraMap_smul]
      have := congrArg Subtype.val hax
      simpa [Submonoid.smul_def] using this
    rw [Submodule.mem_bot]
    exact Subtype.ext ((smul_eq_zero.1 h1).resolve_left ha0)
  haveI : Module.FinitePresentation R L := Module.finitePresentation_of_finite R L
  haveI : Module.Projective R L := Module.Flat.projective_of_finitePresentation
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R L
  obtain ⟨sec, hsec⟩ := Module.projective_lifting_property π LinearMap.id hπ
  let g : Fin n → V := fun i => (π (fun j => if i = j then 1 else 0) : V)
  let fi : Fin n → L →ₗ[R] R := fun i => (LinearMap.proj i).comp sec
  have hzL : ∀ z : L, (z : V) = ∑ i, fi i z • g i := by
    intro z
    have h1 : π (sec z) = z := LinearMap.congr_fun hsec z
    calc (z : V) = ((π (sec z) : L) : V) := by rw [h1]
      _ = _ := by rw [LinearMap.pi_apply_eq_sum_univ π (sec z)]; simp [fi, g]

  let w : Fin n → V := fun i => ∑ j, star (algebraMap R K (fi i ⟨b j, hbL j⟩)) • bs j
  have hw_b : ∀ i k, h (w i) (b k) = algebraMap R K (fi i ⟨b k, hbL k⟩) := by
    intro i k
    simp only [w, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, hbs',
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [starRingEnd_apply, star_star]
  have hw_L : ∀ i (z : L), h (w i) z = algebraMap R K (fi i z) := by
    intro i z
    obtain ⟨d, hd⟩ :=
      IsLocalization.exist_integer_multiples (nonZeroDivisors R) Finset.univ (fun j => h (bs j) (z : V))
    choose a ha using fun j => hd j (Finset.mem_univ j)
    have hdzV : (d : R) • (z : V) = ∑ j, a j • b j := by
      conv_lhs => rw [hcoord (z : V)]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← smul_assoc, ← ha j, algebraMap_smul]
    have hdz : (d : R) • z = ∑ j, a j • (⟨b j, hbL j⟩ : L) := Subtype.ext (by simp [hdzV])
    have hd0 : algebraMap R K (d : R) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
    have L1 : algebraMap R K d * h (w i) z =
        ∑ j, algebraMap R K (a j) * algebraMap R K (fi i ⟨b j, hbL j⟩) := by
      rw [← smul_eq_mul, ← LinearMap.map_smul, algebraMap_smul, hdzV, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← algebraMap_smul K (a j) (b j), LinearMap.map_smul, hw_b, smul_eq_mul]
    have L2 : algebraMap R K d * algebraMap R K (fi i z) =
        ∑ j, algebraMap R K (a j) * algebraMap R K (fi i ⟨b j, hbL j⟩) := by
      rw [← map_mul, ← smul_eq_mul, ← LinearMap.map_smul, hdz, map_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [LinearMap.map_smul, smul_eq_mul, map_mul]
    exact mul_left_cancel₀ hd0 (L1.trans L2.symm)
  refine ⟨n, g, w, fun i => (π _).2, ?_, ?_⟩
  · intro i
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply]
    intro y hy
    rw [Submodule.mem_one, ← hs.eq (w i) y, hw_L i ⟨y, hy⟩]
    obtain ⟨r, hr⟩ := hstar (fi i ⟨y, hy⟩)
    exact ⟨r, by rw [hr]; rfl⟩
  · have hlin : (LinearMap.id : V →ₗ[K] V) = ∑ i, (h (w i)).smulRight (g i) := by
      apply LinearMap.ext_on hsp
      intro z hz
      simp only [LinearMap.id_apply, LinearMap.sum_apply, LinearMap.smulRight_apply]
      calc z = ∑ i, fi i ⟨z, hz⟩ • g i := hzL ⟨z, hz⟩
        _ = ∑ i, h (w i) z • g i := Finset.sum_congr rfl fun i _ => by
          rw [show h (w i) z = h (w i) ((⟨z, hz⟩ : L) : V) from rfl, hw_L i ⟨z, hz⟩,
            algebraMap_smul]
    intro z
    simpa using congrArg (fun F : V →ₗ[K] V => F z) hlin

end Frame

section Coord

variable {K : Type} [Field K] [StarRing K]

theorem hform_eq {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    Formalism.DivisionValues.hform H x y = Formalism.UG.hform (starRingEnd K) H x y := by
  simp [Formalism.DivisionValues.hform, Formalism.UG.hform, Matrix.toLinearMapₛₗ₂'_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

def IsFrame {n k : ℕ} (H : Matrix (Fin n) (Fin n) K) (g w : Fin k → Fin n → K) : Prop :=
  ∀ a b, ∑ i, g i a * ∑ c, star (w i c) * H c b = if a = b then 1 else 0

theorem isFrame_of {n k : ℕ} (H : Matrix (Fin n) (Fin n) K) (g w : Fin k → Fin n → K)
    (h : ∀ z : Fin n → K, z = ∑ i, Formalism.DivisionValues.hform H (w i) z • g i) : IsFrame H g w := by
  intro a b
  have key := congrFun (h (Pi.single b 1)) a
  rw [Finset.sum_apply] at key
  simp only [Pi.smul_apply, smul_eq_mul, hform_eq, Formalism.UG.hform, Pi.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, starRingEnd_apply] at key
  rw [key]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem IsFrame.map {n k : ℕ} {H : Matrix (Fin n) (Fin n) K} {g w : Fin k → Fin n → K} (hf : IsFrame H g w)
    {A : Type} [CommRing A] (φ : K →+* A) (σ : A →+* A) (hσ : ∀ x, σ (φ x) = φ (star x)) (z : Fin n → A) :
    z = ∑ i, Formalism.UG.hform σ (H.map φ) (fun c => φ (w i c)) z • (fun a => φ (g i a)) := by
  funext a
  have e1 : ∀ d, φ (∑ i, g i a * ∑ c, star (w i c) * H c d) = if a = d then 1 else 0 := fun d => by
    rw [hf a d]; split_ifs <;> simp
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Formalism.UG.hform, Matrix.map_apply, hσ]
  calc z a = ∑ d, z d * (if a = d then 1 else 0) := by simp
    _ = ∑ d, z d * φ (∑ i, g i a * ∑ c, star (w i c) * H c d) := by simp only [e1]
    _ = _ := by
      simp only [map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

end Coord

end Formalism.L2.Geo.Def.G1
