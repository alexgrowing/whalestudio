import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusOfSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralSummandGoodPlaceIndicator
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthonormalBasisUnimodularHermitianLocalRi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWittBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticNormsTraceUniformizerFactsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeEqIntegralCoords
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

noncomputable section

namespace GlobalTheory.KapOrb.SelfDualPull

theorem exists_basis_of_lattice : ∀ (K : GlobalTheory.UnitLemma.UQ) (V : Type) [AddCommGroup V] [Module K.E V] [Module K.O V] [IsScalarTower K.O K.E V] [FiniteDimensional K.E V] (L : Submodule K.O V), L.FG → Submodule.span K.E (L : Set V) = ⊤ → ∃ b : Module.Basis (Fin (Module.finrank K.E V)) K.E V, ∀ y, y ∈ L ↔ ∀ i, b.repr y i ∈ (algebraMap K.O K.E).range := by
  first
  | exact @_root_.GlobalTheory.LatticeIntegralCoordinates.lattice_eq_integral_coords
  | exact _root_.GlobalTheory.LatticeIntegralCoordinates.lattice_eq_integral_coords
  | (apply _root_.GlobalTheory.LatticeIntegralCoordinates.lattice_eq_integral_coords <;> assumption)
  | (intros; apply _root_.GlobalTheory.LatticeIntegralCoordinates.lattice_eq_integral_coords <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LatticeIntegralCoordinates.lattice_eq_integral_coords <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LatticeIntegralCoordinates.lattice_eq_integral_coords ..)

theorem exists_orthonormal_of_selfDual : ∀ (K : GlobalTheory.UnitLemma.UQ) (V : Type) [AddCommGroup V] [Module K.E V] [Module K.O V] [IsScalarTower K.O K.E V] [FiniteDimensional K.E V] (h : V → V → K.E), (∀ y y' z, h (y + y') z = h y z + h y' z) → (∀ (a : K.E) y z, h (a • y) z = a * h y z) → (∀ y z, h z y = K.c (h y z)) → (∀ y, (∀ z, h y z = 0) → y = 0) → ∀ L : Submodule K.O V, L.FG → Submodule.span K.E (L : Set V) = ⊤ → (∀ y, y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap K.O K.E).range) → ∃ f : Fin (Module.finrank K.E V) → V, (∀ i j, h (f i) (f j) = if i = j then 1 else 0) ∧ ∀ y, y ∈ L ↔ ∀ i, h y (f i) ∈ (algebraMap K.O K.E).range := by
  intro K V _ _ _ _ _ h hadd hlin hsym hnd L hfg hsp hsd
  obtain ⟨b, hb⟩ := exists_basis_of_lattice K V L hfg hsp
  have inj : Function.Injective (algebraMap K.O K.E) := IsFractionRing.injective _ _
  obtain ⟨s, hs⟩ := GlobalTheory.UnitLemma.Witt.exists_conj K
  obtain ⟨hN, ⟨t, ht⟩, -⟩ := GlobalTheory.T.unramifiedQuadratic_norms_trace_uniformizer_facts K
  have hadd2 : ∀ y z z', h y (z + z') = h y z + h y z' := by
    intro y z z'
    rw [hsym, hadd, map_add, ← hsym, ← hsym]
  have hlin2 : ∀ (a : K.E) y z, h y (a • z) = K.c a * h y z := by
    intro a y z
    rw [hsym, hlin, map_mul, ← hsym]
  have hsum1 : ∀ (S : Finset (Fin (Module.finrank K.E V))) (c : Fin (Module.finrank K.E V) → K.E) (u : Fin (Module.finrank K.E V) → V) z,
      h (∑ i ∈ S, c i • u i) z = ∑ i ∈ S, c i * h (u i) z := by
    intro S c u z
    induction S using Finset.induction_on with
    | empty =>
      have : h 0 z = 0 := by
        have := hlin 0 0 z
        simpa using this
      simpa using this
    | insert i S hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hadd, hlin, ih]
  have hsum2 : ∀ (S : Finset (Fin (Module.finrank K.E V))) (c : Fin (Module.finrank K.E V) → K.E) (u : Fin (Module.finrank K.E V) → V) y,
      h y (∑ i ∈ S, c i • u i) = ∑ i ∈ S, K.c (c i) * h y (u i) := by
    intro S c u y
    rw [hsym, hsum1, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ← hsym]
  have hrng : ∀ o : K.O, K.c (algebraMap K.O K.E o) ∈ (algebraMap K.O K.E).range :=
    fun o => ⟨s o, hs o⟩
  have hbL : ∀ i, b i ∈ L := by
    intro i
    rw [hb]
    intro j
    rw [b.repr_self, Finsupp.single_apply]
    split_ifs
    · exact ⟨1, map_one _⟩
    · exact ⟨0, map_zero _⟩
  have hexp : ∀ z, z = ∑ i, b.repr z i • b i := fun z => (b.sum_repr z).symm

  have hQex : ∀ k l, ∃ o : K.O, algebraMap K.O K.E o = h (b l) (b k) :=
    fun k l => RingHom.mem_range.mp ((hsd (b l)).mp (hbL l) (b k) (hbL k))
  choose Q hQ using hQex
  have hss : ∀ o, s (s o) = o := by
    intro o; apply inj; rw [hs, hs, K.c_c]
  have hherm : cT s (Matrix.of Q) = Matrix.of Q := by
    ext i j
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]
    apply inj
    rw [hs, hQ, hQ, ← hsym]

  let T : V →ₗ[K.E] (Fin (Module.finrank K.E V) → K.E) :=
    { toFun := fun y k => h y (b k)
      map_add' := by intro y y'; funext k; exact hadd _ _ _
      map_smul' := by intro a y; funext k; exact hlin _ _ _ }
  have hTinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply hnd
    intro z
    rw [hexp z, hsum2]
    refine Finset.sum_eq_zero fun k _ => ?_
    have : h y (b k) = 0 := congrFun hy k
    rw [this, mul_zero]
  have hTsurj : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hTinj
  choose d hd using fun j : Fin (Module.finrank K.E V) => hTsurj (Pi.single j 1)
  have hdb : ∀ j k, h (d j) (b k) = if k = j then 1 else 0 := by
    intro j k
    have := congrFun (hd j) k
    simpa [T, Pi.single_apply] using this
  have hdL : ∀ j, d j ∈ L := by
    intro j
    rw [hsd]
    intro z hz
    rw [hexp z, hsum2]
    refine Subring.sum_mem _ fun k _ => ?_
    obtain ⟨o, ho⟩ := (hb z).mp hz k
    rw [← ho, hdb]
    split_ifs
    · rw [mul_one]; exact hrng o
    · rw [mul_zero]; exact Subring.zero_mem _
  have hRex : ∀ k j, ∃ o : K.O, algebraMap K.O K.E o = b.repr (d j) k :=
    fun k j => RingHom.mem_range.mp ((hb (d j)).mp (hdL j) k)
  choose R hR using hRex
  have hQR : Matrix.of Q * Matrix.of R = 1 := by
    ext i j
    apply inj
    simp only [Matrix.mul_apply, Matrix.of_apply, map_sum, map_mul, hQ, hR]
    have h5 : h (d j) (b i) = ∑ k, b.repr (d j) k * h (b k) (b i) := by
      conv_lhs => rw [hexp (d j)]
      rw [hsum1]
    rw [Finset.sum_congr rfl fun k _ => mul_comm _ _, ← h5, hdb, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  have hQu : IsUnit (Matrix.of Q) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse hQR)
  obtain ⟨a, ha⟩ := GlobalTheory.Core.Rk.Exh.exists_orthonormal_of_isLocalRing K.O s hss
    ⟨t, inj (by rw [map_add, hs, ht, map_one])⟩
    (by
      intro u hu hsu
      obtain ⟨z, hz⟩ := hN hu.unit (by rw [IsUnit.unit_spec, ← hs, hsu])
      refine ⟨z, inj ?_⟩
      rw [map_mul, hs, IsUnit.unit_spec] at *
      rw [hz, mul_comm])
    (Module.finrank K.E V) (Matrix.of Q) hherm hQu
  set A : Matrix (Fin (Module.finrank K.E V)) (Fin (Module.finrank K.E V)) K.O := a.1
  let f : Fin (Module.finrank K.E V) → V := fun j => ∑ l, algebraMap K.O K.E (A l j) • b l
  have hfo : ∀ i j, h (f i) (f j) = if i = j then 1 else 0 := by
    intro i j
    have hM := congrArg (fun M : Matrix (Fin (Module.finrank K.E V)) (Fin (Module.finrank K.E V)) K.O => algebraMap K.O K.E (M j i)) ha
    simp only [cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, map_sum,
      map_mul, Matrix.one_apply] at hM
    simp only [f, hsum1, hsum2]
    simp only [hs, hQ, apply_ite (algebraMap K.O K.E), map_one, map_zero] at hM
    rw [show (if i = j then (1 : K.E) else 0) = if j = i then 1 else 0 by
      by_cases hij : i = j <;> simp [hij, eq_comm]]
    rw [← hM]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have hfL : ∀ j, f j ∈ L := by
    intro j
    refine L.sum_mem fun l _ => ?_
    rw [algebraMap_smul]
    exact L.smul_mem _ (hbL l)
  set A' : Matrix (Fin (Module.finrank K.E V)) (Fin (Module.finrank K.E V)) K.O := (a⁻¹ : GL (Fin (Module.finrank K.E V)) K.O).1
  have hAA' : A * A' = 1 := a.mul_inv
  have hbf : ∀ l, b l = ∑ j, algebraMap K.O K.E (A' j l) • f j := by
    intro l
    have h6 : ∀ k, ∑ j, algebraMap K.O K.E (A k j) * algebraMap K.O K.E (A' j l) = if k = l then 1 else 0 := by
      intro k
      have := congrArg (fun M : Matrix (Fin (Module.finrank K.E V)) (Fin (Module.finrank K.E V)) K.O => algebraMap K.O K.E (M k l)) hAA'
      simpa [Matrix.mul_apply, map_sum, Matrix.one_apply, apply_ite] using this
    calc b l = ∑ k, (if k = l then (1 : K.E) else 0) • b k := by simp
      _ = ∑ k, (∑ j, algebraMap K.O K.E (A k j) * algebraMap K.O K.E (A' j l)) • b k := by simp only [h6]
      _ = ∑ j, algebraMap K.O K.E (A' j l) • f j := by
        simp only [f, Finset.smul_sum, smul_smul, Finset.sum_smul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]
  refine ⟨f, hfo, fun y => ⟨fun hy i => (hsd y).mp hy (f i) (hfL i), fun hy => ?_⟩⟩
  rw [hsd]
  intro z hz
  rw [hexp z, hsum2]
  refine Subring.sum_mem _ fun l _ => ?_
  obtain ⟨o, ho⟩ := (hb z).mp hz l
  rw [← ho, hbf l, hsum2]
  exact Subring.mul_mem _ (hrng o) (Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hrng _) (hy j))

theorem exists_unitary_pullLat_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (x : B.A) (n : ℕ) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)), (∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) → (∀ y z, stdH w (ψ y) (ψ z) = e (B.herm x y z)) → ∀ L : Submodule K.O B.A, GlobalTheory.UnitLemma.IsLat K.O K.E L → (∀ y, y ∈ L ↔ ∀ z ∈ L, B.herm x y z ∈ (algebraMap K.O K.E).range) → ∃ g ∈ UL n w, pullLat w B ψ g = L := by
  intro E _ _ _ w hns K e hB B x n ψ hψs hψh L hL hsd
  have hc : ∀ a, e (K.c a) = cj w (e a) := hB.1
  have hint : ∀ a, a ∈ (algebraMap K.O K.E).range ↔ e a ∈ w.adicCompletionIntegers E := by
    intro a; rw [hB.2.1 a, HeightOneSpectrum.mem_adicCompletionIntegers]
  have hcc : ∀ z : w.adicCompletion E, cj w (cj w z) = z := by
    intro z
    obtain ⟨a, rfl⟩ := e.surjective z
    rw [← hc, ← hc, K.c_c]
  have hadd : ∀ y y' z, B.herm x (y + y') z = B.herm x y z + B.herm x y' z := by
    intro y y' z
    simp only [GlobalTheory.UnitLemma.InvAlg.herm, mul_add, add_mul, map_add]
  have hlin : ∀ (a : K.E) y z, B.herm x (a • y) z = a * B.herm x y z := by
    intro a y z
    simp only [GlobalTheory.UnitLemma.InvAlg.herm]
    rw [show x * (a • y) * B.σ z = a • (x * y * B.σ z) by rw [Algebra.smul_def, Algebra.smul_def]; ring]
    rw [LinearMap.map_smul, smul_eq_mul]
  have hsym : ∀ y z, B.herm x z y = K.c (B.herm x y z) := by
    intro y z
    apply e.injective
    rw [hc, ← hψh, ← hψh]
    simp only [stdH, map_sum, map_mul, hcc]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hnd : ∀ y, (∀ z, B.herm x y z = 0) → y = 0 := by
    intro y hy
    apply ψ.injective
    rw [map_zero]
    funext i
    have h2 := congrArg e (hy (ψ.symm (Pi.single i 1)))
    rw [← hψh, map_zero, AddEquiv.apply_symm_apply] at h2
    simpa [stdH, Pi.single_apply] using h2
  let φ : B.A ≃ₗ[K.E] (Fin n → K.E) :=
    { toFun := fun y i => e.symm (ψ y i)
      invFun := fun a => ψ.symm (fun i => e (a i))
      map_add' := by intro y y'; funext i; simp
      map_smul' := by intro c y; funext i; simp [hψs]
      left_inv := by intro y; simp
      right_inv := by intro a; funext i; simp }
  have hn : Module.finrank K.E B.A = n := by rw [φ.finrank_eq, Module.finrank_fin_fun]
  have key := exists_orthonormal_of_selfDual K B.A (B.herm x) hadd hlin hsym hnd L hL.1 hL.2 hsd
  rw [hn] at key
  obtain ⟨f, hfo, hfL⟩ := key
  let gM : Matrix (Fin n) (Fin n) (w.adicCompletion E) := Matrix.of fun i j => ψ (f j) i
  have hgl : cT (cj w) gM * gM = 1 := by
    ext i j
    simp only [cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, gM, Matrix.of_apply]
    have h3 := hψh (f j) (f i)
    rw [hfo] at h3
    simp only [stdH] at h3
    rw [Finset.sum_congr rfl fun k _ => mul_comm _ _, h3, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  have hgr : gM * cT (cj w) gM = 1 := mul_eq_one_comm.mp hgl
  let g : GLw n w := ⟨gM, cT (cj w) gM, hgr, hgl⟩
  refine ⟨g, ?_, ?_⟩
  · have : g ∈ UJ (cj w) 1 := by
      show cT (cj w) gM * 1 * gM = 1
      rw [Matrix.mul_one, hgl]
    simpa [UL, hns] using this
  · have hinv : ((g⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = cT (cj w) gM := rfl
    have hcomp : ∀ v : Fin n → w.adicCompletion E, ∀ i, (cT (cj w) gM *ᵥ v) i = stdH w v (ψ (f i)) := by
      intro v i
      simp only [cT, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply, gM, Matrix.of_apply, stdH]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    ext y
    show (∀ (c : K.O) (i : Fin n), (((g⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) *ᵥ ψ (c • y)) i ∈ w.adicCompletionIntegers E) ↔ y ∈ L
    rw [hinv]
    constructor
    · intro hy
      rw [hfL]
      intro i
      have h4 := hy 1 i
      rw [one_smul, hcomp, hψh] at h4
      exact (hint _).mpr h4
    · intro hy c i
      rw [hcomp, hψh]
      exact (hint _).mp (((hfL (c • y)).mp (L.smul_mem c hy)) i)

end GlobalTheory.KapOrb.SelfDualPull
