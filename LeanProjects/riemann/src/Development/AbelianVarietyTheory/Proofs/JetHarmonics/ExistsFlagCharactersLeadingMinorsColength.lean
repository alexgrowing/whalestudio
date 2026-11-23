import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
import ReciprocityTheory.DualLattices.UpBrChar

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
open ReciprocityTheory.PGsh.Up

namespace GlobalTheory.CharDepth

theorem det_dvd_det_of_trunc_mem_span {R : Type} [CommRing R] {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (B : Matrix (Fin n) (Fin n) R)
    (h : ∀ j, (fun a : Fin n => A a.castSucc j) ∈ Submodule.span R (Set.range fun i => fun a => B a i)) :
    B.det ∣ A.det := by
  choose X hX using fun j => (Submodule.mem_span_range_iff_exists_fun R).1 (h j)
  rw [Matrix.det_succ_row A (Fin.last n)]
  refine Finset.dvd_sum fun j _ => Dvd.dvd.mul_left ?_ _
  have e : A.submatrix (Fin.last n).succAbove j.succAbove = B * Matrix.of (fun i k => X (j.succAbove k) i) := by
    ext a k
    have := congrFun (hX (j.succAbove k)) a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mul_apply, Matrix.submatrix_apply, Fin.succAbove_last, ← this]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e, Matrix.det_mul]
  exact Dvd.intro _ rfl

theorem minor_dvd_minor {R : Type} [CommRing R] {g N : ℕ} (M : Matrix (Fin g) (Fin N) R) (ι : Fin g → Fin N)
    (hι : ∀ s (hs : s ≤ g), Submodule.span R (Set.range fun b : Fin s => fun a : Fin s =>
      M (Fin.castLE hs a) (ι (Fin.castLE hs b))) = omTr M s hs)
    (n m : ℕ) (hnm : n ≤ m) (hm : m ≤ g) :
    (Matrix.of fun a b : Fin n => M (Fin.castLE (hnm.trans hm) a) (ι (Fin.castLE (hnm.trans hm) b))).det ∣
      (Matrix.of fun a b : Fin m => M (Fin.castLE hm a) (ι (Fin.castLE hm b))).det := by
  induction m, hnm using Nat.le_induction with
  | base => exact dvd_rfl
  | succ m hnm ih =>
    refine (ih (Nat.le_of_succ_le hm)).trans (det_dvd_det_of_trunc_mem_span _ _ fun j => ?_)
    have h := hι m (Nat.le_of_succ_le hm)
    have h2 : (fun a : Fin m => M (Fin.castLE (Nat.le_of_succ_le hm) a) (ι (Fin.castLE hm j))) ∈
        omTr M m (Nat.le_of_succ_le hm) := Submodule.subset_span ⟨_, rfl⟩
    rw [← h] at h2
    exact h2

theorem exists_smul_eq_zero_of_hasLen {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] (hv : v.Integers R) {M : Type} [AddCommGroup M] [Module R M] {x : NNReal}
    (h : HasLen v R M x) (hx : x ≠ 0) : x ≤ 1 ∧ ∃ c : R, c ≠ 0 ∧ ∀ m : M, c • m = 0 := by
  obtain ⟨m, c, ⟨e⟩, hc⟩ := h
  have hc' : v (algebraMap R C (∏ i, c i)) = x := by rw [map_prod, map_prod, hc]
  refine ⟨hc' ▸ hv.map_le_one _, ∏ i, c i, ?_, fun z => ?_⟩
  · intro h0
    rw [h0, map_zero, map_zero] at hc'
    exact hx hc'.symm
  · apply e.injective
    rw [map_smul, map_zero]
    funext i
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (e z i)
    rw [Pi.smul_apply, ← hy, Pi.zero_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton.2 ((Finset.dvd_prod_of_mem c (Finset.mem_univ i)).mul_right y)

theorem exists_flag_characters (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C]
    (hv : v.Integers O) (d s : ℕ) (F : Fin d → PS O 2 d) (w : Fin s → Fin d → O) (x : NNReal)
    (h : HasAF v F w x) (hx : x ≠ 0) :
    x ≤ 1 ∧ ∃ χ : Fin s → PS O 1 d, (∀ b, IsCh F (χ b)) ∧ ∀ i : Fin s, x ≤ v (algebraMap O C
      (Matrix.of fun a b : Fin (i.val + 1) =>
        ∑ j, w (Fin.castLE i.isLt a) j * dl (χ (Fin.castLE i.isLt b)) j).det) := by
  obtain ⟨N, u, hu, hlen⟩ := h
  obtain ⟨hx1, c, hc, hkill⟩ := exists_smul_eq_zero_of_hasLen hv hlen hx
  refine ⟨hx1, ?_⟩
  let M : Matrix (Fin s) (Fin N) O := fun a k => res w (dl (u k)) a
  have hom : omTr M s le_rfl = Submodule.span O (Set.range fun k => res w (dl (u k))) := rfl
  have hspan : ∀ n (hn : n ≤ s), ∀ y : Fin n → O, c • y ∈ omTr M n hn := by
    intro n hn y
    let y' : Fin s → O := Function.extend (Fin.castLE hn) y 0
    have h1 : c • y' ∈ Submodule.span O (Set.range fun k => res w (dl (u k))) := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
      exact hkill _
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 h1
    refine (Submodule.mem_span_range_iff_exists_fun O).2 ⟨r, ?_⟩
    funext a
    have h2 := congrFun hr (Fin.castLE hn a)
    have h3 : y' (Fin.castLE hn a) = y a := (Fin.castLE_injective hn).extend_apply y 0 a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, h3] at h2 ⊢
    exact h2
  obtain ⟨ι, -, hι⟩ := charThm C v O hv s N M c hc hspan
  haveI : IsDomain O := Function.Injective.isDomain _ hv.hom_inj
  have hfull := char_len hv M ι s le_rfl (hι s le_rfl)
  rw [hom] at hfull
  have hxe := hasLen_unique hv hlen hfull
  refine ⟨fun b => u (ι b), fun b => hu _, fun i => ?_⟩
  have hd := hv.le_of_dvd (minor_dvd_minor M ι hι (i.val + 1) s i.isLt le_rfl)
  rw [← hxe] at hd
  exact hd

end GlobalTheory.CharDepth
