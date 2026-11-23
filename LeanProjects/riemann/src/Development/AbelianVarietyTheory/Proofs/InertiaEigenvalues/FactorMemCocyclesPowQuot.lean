import Mathlib
import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.LocDualInt

section Pow

variable {O : Type} [CommRing O] {G : Type} [Group G] {M : Type} [AddCommGroup M] [Module O M]

def powSub (a : O) (n : ℕ) : Submodule O M := LinearMap.range ((a ^ n) • LinearMap.id : M →ₗ[O] M)

theorem mem_powSub {a : O} {n : ℕ} {x : M} : x ∈ powSub (M := M) a n ↔ ∃ y : M, a ^ n • y = x := by
  simp [powSub]

theorem smul_mem_powSub (a : O) (n : ℕ) (y : M) : a ^ n • y ∈ powSub (M := M) a n :=
  mem_powSub.2 ⟨y, rfl⟩

theorem powSub_anti (a : O) {m n : ℕ} (h : m ≤ n) : powSub (M := M) a n ≤ powSub a m := by
  intro x hx
  obtain ⟨y, rfl⟩ := mem_powSub.1 hx
  refine mem_powSub.2 ⟨a ^ (n - m) • y, ?_⟩
  rw [smul_smul, ← pow_add, Nat.add_sub_cancel' h]

theorem powSub_stable (ρ : Representation O G M) (a : O) (n : ℕ) (g : G) (x : M)
    (hx : x ∈ powSub (M := M) a n) : ρ g x ∈ powSub (M := M) a n := by
  obtain ⟨y, rfl⟩ := mem_powSub.1 hx
  exact mem_powSub.2 ⟨ρ g y, by rw [map_smul]⟩

def quotRep (ρ : Representation O G M) (a : O) (n : ℕ) :
    Representation O G (M ⧸ powSub (M := M) a n) where
  toFun g := (powSub a n).mapQ (powSub a n) (ρ g) (fun x hx => powSub_stable ρ a n g x hx)
  map_one' := by
    apply Submodule.linearMap_qext
    ext x
    simp
  map_mul' g h := by
    apply Submodule.linearMap_qext
    ext x
    simp [Module.End.mul_apply]

@[simp] theorem quotRep_mk (ρ : Representation O G M) (a : O) (n : ℕ) (g : G) (x : M) :
    quotRep ρ a n g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (ρ g x) := rfl

def qlift {N : Submodule O M} (z : M ⧸ N) : M := (Submodule.Quotient.mk_surjective N z).choose

@[simp] theorem mk_qlift {N : Submodule O M} (z : M ⧸ N) : Submodule.Quotient.mk (qlift z) = z :=
  (Submodule.Quotient.mk_surjective N z).choose_spec

end Pow

section TopPow

variable {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul O M]

theorem continuous_factor (a : O) {m n : ℕ} (h : m ≤ n) :
    Continuous (Submodule.factor (powSub_anti (M := M) a h)) := by
  rw [(Submodule.isOpenQuotientMap_mkQ _).isQuotientMap.continuous_iff]
  exact continuous_quot_mk

theorem factor_mem_cocycles_pow_quot (ρ : Representation O G M) (a : O) {m n : ℕ} (h : m ≤ n)
    {z : G → M ⧸ powSub (M := M) a n} (hz : z ∈ Z1 (quotRep ρ a n)) :
    (fun g => Submodule.factor (powSub_anti (M := M) a h) (z g)) ∈ Z1 (quotRep ρ a m) := by
  refine ⟨(continuous_factor a h).comp hz.1, fun g g' => ?_⟩
  show Submodule.factor _ (z (g * g')) = Submodule.factor _ (z g) +
    quotRep ρ a m g (Submodule.factor (powSub_anti (M := M) a h) (z g'))
  rw [hz.2 g g', map_add]
  congr 1
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (z g')
  rw [← hy]
  rfl

end TopPow

end GlobalTheory.LocDualInt

noncomputable section

namespace GlobalTheory.LocDualInt

section Lat

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {G : Type} [Group G] [TopologicalSpace G]
    {VT VT' : Type}
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] (D : LatData O G VT VT')

def cupMod (c : G → VT ⧸ D.T) (a : O) (n : ℕ) (z : G → ↥D.T' ⧸ powSub (M := ↥D.T') a n) :
    G × G → KO O :=
  fun p => pairKO D.bT D.T (c p.1) (D.ρTl' p.1 (qlift (z p.2)))

theorem pairKO_eq_zero_of_mem {a : O} {r : ℕ} {x : VT ⧸ D.T} (hx : a ^ r • x = 0) {t : ↥D.T'}
    (ht : t ∈ powSub (M := ↥D.T') a r) : pairKO D.bT D.T x t = 0 := by
  obtain ⟨y, rfl⟩ := mem_powSub.1 ht
  rw [map_smul, ← LinearMap.smul_apply, ← map_smul, hx, map_zero, LinearMap.zero_apply]

theorem pairKO_eq_of_sub_mem {a : O} {r : ℕ} {x : VT ⧸ D.T} (hx : a ^ r • x = 0) {t t' : ↥D.T'}
    (ht : t - t' ∈ powSub (M := ↥D.T') a r) : pairKO D.bT D.T x t = pairKO D.bT D.T x t' := by
  rw [← sub_eq_zero, ← map_sub]
  exact pairKO_eq_zero_of_mem D hx ht

theorem cupMod_factor {c : G → VT ⧸ D.T} {a : O} {r m n : ℕ} (hc : ∀ g, a ^ r • c g = 0)
    (hrm : r ≤ m) (hmn : m ≤ n) (z : G → ↥D.T' ⧸ powSub (M := ↥D.T') a n) :
    cupMod D c a m (fun g => Submodule.factor (powSub_anti (M := ↥D.T') a hmn) (z g)) =
      cupMod D c a n z := by
  funext p
  refine pairKO_eq_of_sub_mem D (hc p.1) ?_
  rw [← map_sub]
  refine powSub_stable _ a r p.1 _ (powSub_anti a hrm ?_)
  apply (Submodule.Quotient.eq _).1
  have e : (Submodule.Quotient.mk (qlift (z p.2)) : ↥D.T' ⧸ powSub (M := ↥D.T') a m) =
      Submodule.factor (powSub_anti (M := ↥D.T') a hmn) (z p.2) := by
    conv_rhs => rw [← mk_qlift (z p.2)]
    rfl
  rw [e, mk_qlift]

end Lat

end GlobalTheory.LocDualInt
