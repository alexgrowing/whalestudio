import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import ReciprocityTheory.DualLattices.ExistsSmulMemOfMemSpan
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ComapFgOfValuationRing

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rh

section
variable {C : Type} [Field C] (R : Type) [CommRing R] [Algebra R C]

def formR (p : ℕ) (ι : Type) [Fintype ι] : (ι → R) →ₗ[R] ((ι → ZMod p) → R) where
  toFun l x := ∑ i, l i * ((x i).val : R)
  map_add' l l' := by ext x; simp [add_mul, Finset.sum_add_distrib]
  map_smul' c l := by ext x; simp [Finset.mul_sum, mul_assoc]

variable (C) in

def toC (X : Type) : (X → R) →ₗ[R] (X → C) := (Algebra.linearMap R C).compLeft X

variable {R}

theorem mem_pInt {p : ℕ} {z : C} : z ∈ pInt (C := C) R p ↔ ∃ r : R, z = algebraMap R C r * p := by
  simp only [pInt, Submodule.mem_span_singleton, Algebra.smul_def]
  exact ⟨fun ⟨r, h⟩ => ⟨r, h.symm⟩, fun ⟨r, h⟩ => ⟨r, h.symm⟩⟩

theorem afLat_eq (p : ℕ) {ι : Type} [Fintype ι] (M : Submodule R ((ι → ZMod p) → C)) :
    afLat p M = (M ⊔ pFun R p _).comap (toC C R _ ∘ₗ formR R p ι) := by
  ext l
  rw [Submodule.mem_comap, Submodule.mem_sup]
  change (∃ g ∈ M, ∀ x, g x - algebraMap R C (∑ i, l i * ((x i).val : R)) ∈ pInt R p) ↔ _
  have hf : (toC C R _ ∘ₗ formR R p ι) l = fun x => algebraMap R C (∑ i, l i * ((x i).val : R)) := rfl
  rw [hf]
  constructor
  · rintro ⟨g, hg, h⟩
    refine ⟨g, hg, fun x => algebraMap R C (∑ i, l i * ((x i).val : R)) - g x, ?_, ?_⟩
    · rw [pFun, Submodule.mem_pi]
      intro x _
      have := neg_mem (h x)
      rwa [neg_sub] at this
    · funext x
      simp
  · rintro ⟨g, hg, z, hz, he⟩
    refine ⟨g, hg, fun x => ?_⟩
    have hx : z x ∈ pInt R p := (Submodule.mem_pi.mp hz) x (Set.mem_univ x)
    have e : g x - algebraMap R C (∑ i, l i * ((x i).val : R)) = - z x := by
      rw [← congrFun he x]
      simp
    rw [e]
    exact neg_mem hx

theorem form_mem_lin (p : ℕ) [NeZero p] {ι : Type} [Fintype ι] (l : ι → R) :
    (toC C R _ ∘ₗ formR R p ι) l ∈ linFun (C := C) R p (ι → ZMod p) := by
  rw [linFun, Submodule.mem_inf]
  have hf : (toC C R _ ∘ₗ formR R p ι) l = fun x => algebraMap R C (∑ i, l i * ((x i).val : R)) := rfl
  rw [hf]
  refine ⟨fun x => ⟨∑ i, l i * ((x i).val : R), rfl⟩, ?_⟩
  intro x y
  rw [mem_pInt]
  refine ⟨-∑ i, l i * ((((x i).val + (y i).val) / p : ℕ) : R), ?_⟩
  have key : ∀ i, (((x i + y i).val : ℕ) : R) = ((x i).val : R) + (y i).val - p * ((((x i).val + (y i).val) / p : ℕ) : R) := by
    intro i
    rw [ZMod.val_add, eq_sub_iff_add_eq, ← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div, Nat.cast_add]
  simp only [Pi.add_apply, key]
  simp only [← map_sub, ← map_neg, ← map_natCast (algebraMap R C), ← map_mul]
  congr 1
  rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem add_mem_pFun {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]
    {h : (ι → ZMod p) → C} (hh : h ∈ addFun R p (ι → ZMod p))
    (h1 : ∀ i, h (Pi.single i 1) ∈ pInt (C := C) R p) : h ∈ pFun R p (ι → ZMod p) := by
  have h0 : h 0 ∈ pInt (C := C) R p := by
    have := neg_mem (hh 0 0)
    simpa using this
  let S : AddSubmonoid (ι → ZMod p) :=
    { carrier := {x | h x ∈ pInt (C := C) R p}
      add_mem' := by
        intro a b ha hb
        have e : h (a + b) = (h (a + b) - h a - h b) + h a + h b := by ring
        show h (a + b) ∈ pInt (C := C) R p
        rw [e]
        exact add_mem (add_mem (hh a b) ha) hb
      zero_mem' := h0 }
  have hall : ∀ x, x ∈ S := by
    intro x
    rw [← Finset.univ_sum_single x]
    refine sum_mem fun i _ => ?_
    have e : Pi.single i (x i) = (x i).val • (Pi.single i (1 : ZMod p) : ι → ZMod p) := by
      ext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [Pi.single_apply, hj]
    rw [e]
    exact nsmul_mem (show (Pi.single i (1 : ZMod p) : ι → ZMod p) ∈ S from h1 i) _
  rw [pFun, Submodule.mem_pi]
  intro x _
  exact hall x

end

theorem aflat_fg : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), (afLat p AA.carrier).FG := by
  intro p _ C _ _ _ v R _ _ hv hp ι _ _ AA
  haveI : IsDomain R := Function.Injective.isDomain (algebraMap R C) hv.hom_inj
  haveI : ValuationRing R :=
    { cond' := fun a b => by
        rcases le_total (v (algebraMap R C a)) (v (algebraMap R C b)) with h | h
        · obtain ⟨c, hc⟩ := hv.dvd_of_le h
          exact ⟨c, Or.inr hc.symm⟩
        · obtain ⟨c, hc⟩ := hv.dvd_of_le h
          exact ⟨c, Or.inl hc.symm⟩ }
  rw [afLat_eq, Submodule.comap_comp]
  apply comap_fg_of_valuationRing
  have hinj : Function.Injective (toC C R (ι → ZMod p)) := by
    intro f g h
    funext x
    exact hv.hom_inj (congrFun h x)
  apply Submodule.fg_of_fg_map_injective (toC C R (ι → ZMod p)) hinj
  have hle : AA.carrier ⊔ pFun R p (ι → ZMod p) ≤ LinearMap.range (toC C R (ι → ZMod p)) := by
    apply sup_le
    · intro f hf
      have hi := AA.le_int hf
      choose r hr using hi
      exact ⟨r, funext fun x => hr x⟩
    · intro f hf
      rw [pFun, Submodule.mem_pi] at hf
      choose r hr using fun x => mem_pInt.mp (hf x (Set.mem_univ x))
      refine ⟨fun x => r x * p, funext fun x => ?_⟩
      rw [hr x]
      simp [toC]
  rw [Submodule.map_comap_eq, inf_eq_right.mpr hle]
  apply Submodule.FG.sup
  · obtain ⟨B, _, hB⟩ := AA.lat
    rw [hB]
    exact Submodule.fg_span (Set.finite_range _)
  · have hP : pFun R p (ι → ZMod p) = Submodule.map ((p : R) • toC C R (ι → ZMod p)) ⊤ := by
      ext f
      simp only [Submodule.mem_map, Submodule.mem_top, true_and]
      rw [pFun, Submodule.mem_pi]
      constructor
      · intro hf
        choose r hr using fun x => mem_pInt.mp (hf x (Set.mem_univ x))
        refine ⟨r, funext fun x => ?_⟩
        rw [hr x]
        simp [toC, Algebra.smul_def, mul_comm]
      · rintro ⟨r, rfl⟩ x _
        rw [mem_pInt]
        exact ⟨r x, by simp [toC, Algebra.smul_def, mul_comm]⟩
    rw [hP]
    exact Submodule.FG.map _ Module.Finite.fg_top

theorem afquot : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), Nonempty (AFQuot p AA.carrier ≃ₗ[R] ((ι → R) ⧸ afLat p AA.carrier)) := by
  intro p _ C _ _ _ v R _ _ hv hp ι _ _ AA
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let φ := toC C R (ι → ZMod p) ∘ₗ formR R p ι
  let K := Submodule.comap (linFun (C := C) R p (ι → ZMod p)).subtype (afFun p AA.carrier ⊔ pFun (C := C) R p (ι → ZMod p))
  let ψ : (ι → R) →ₗ[R] linFun (C := C) R p (ι → ZMod p) := LinearMap.codRestrict _ φ (fun l => form_mem_lin p l)
  let f := K.mkQ ∘ₗ ψ
  have hpf : pFun (C := C) R p (ι → ZMod p) ≤ addFun (C := C) R p (ι → ZMod p) := by
    intro z hz x y
    rw [pFun, Submodule.mem_pi] at hz
    exact sub_mem (sub_mem (hz _ (Set.mem_univ _)) (hz _ (Set.mem_univ _))) (hz _ (Set.mem_univ _))
  have hker : afLat p AA.carrier = LinearMap.ker f := by
    ext l
    rw [LinearMap.mem_ker, afLat_eq, Submodule.mem_comap]
    change _ ↔ Submodule.Quotient.mk (ψ l) = 0
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    change φ l ∈ AA.carrier ⊔ pFun (C := C) R p _ ↔ φ l ∈ afFun p AA.carrier ⊔ pFun (C := C) R p _
    constructor
    · intro h
      obtain ⟨g, hg, z, hz, he⟩ := Submodule.mem_sup.mp h
      have hadd : φ l ∈ addFun (C := C) R p (ι → ZMod p) := (Submodule.mem_inf.mp (form_mem_lin p l)).2
      have hg' : g ∈ addFun (C := C) R p (ι → ZMod p) := by
        have : g = φ l - z := by rw [← he]; abel
        rw [this]
        exact sub_mem hadd (hpf hz)
      exact Submodule.mem_sup.mpr ⟨g, Submodule.mem_inf.mpr ⟨hg, hg'⟩, z, hz, he⟩
    · intro h
      exact (sup_le_sup_right inf_le_left _ : afFun p AA.carrier ⊔ pFun (C := C) R p _ ≤ AA.carrier ⊔ pFun (C := C) R p _) h
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨⟨h, hh⟩, rfl⟩ := Submodule.mkQ_surjective K q
    have hh' := Submodule.mem_inf.mp hh
    choose l hl using fun i => hh'.1 (Pi.single i (1 : ZMod p))
    refine ⟨l, ?_⟩
    show Submodule.Quotient.mk (ψ l) = Submodule.Quotient.mk ⟨h, hh⟩
    rw [Submodule.Quotient.eq, Submodule.mem_comap]
    apply Submodule.mem_sup_right
    change φ l - h ∈ pFun (C := C) R p (ι → ZMod p)
    apply add_mem_pFun
    · exact sub_mem (Submodule.mem_inf.mp (form_mem_lin p l)).2 hh'.2
    · intro i
      have e : φ l (Pi.single i 1) = algebraMap R C (l i) := by
        show algebraMap R C (∑ j, l j * (((Pi.single i (1 : ZMod p) : ι → ZMod p) j).val : R)) = _
        simp [Pi.single_apply, apply_ite, ZMod.val_one]
      rw [Pi.sub_apply, e, hl i, sub_self]
      exact zero_mem _
  exact ⟨((Submodule.quotEquivOfEq _ _ hker).trans (LinearMap.quotKerEquivOfSurjective f hsurj)).symm⟩

end PositivityTheory.HtPt.Rh
