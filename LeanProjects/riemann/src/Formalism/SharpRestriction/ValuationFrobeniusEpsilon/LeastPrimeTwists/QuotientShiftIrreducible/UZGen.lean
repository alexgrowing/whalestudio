import Mathlib
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerAdditivityDegreeZero
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleGr

noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

open IsLocalRing Filter

section

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]

def GMod.quotsMk : (ts : List (Deg k × R)) → (F : GMod B R k) → F.M →ₗ[R] (F.quots ts).M
  | [], _ => LinearMap.id
  | (_, s) :: ts, F =>
      (GMod.quotsMk ts (F.quot s)).comp (LinearMap.range (LinearMap.lsmul R F.M s)).mkQ

theorem GMod.quotsMk_surjective (ts : List (Deg k × R)) (F : GMod B R k) :
    Function.Surjective (GMod.quotsMk ts F) := by
  induction ts generalizing F with
  | nil => exact Function.surjective_id
  | cons p ts ih =>
    obtain ⟨d, s⟩ := p
    exact (ih (F.quot s)).comp (Submodule.mkQ_surjective _)

theorem secs_cons (d : Deg k) (s : R) (ts : List (Deg k × R)) :
    secs ((d, s) :: ts) = Ideal.span {s} ⊔ secs ts := by
  unfold secs
  rw [← Ideal.span_union]
  congr 1
  ext r
  simp only [List.mem_cons, Prod.mk.injEq, Set.mem_ofPred_eq, Set.singleton_union, Set.mem_insert_iff]
  constructor
  · rintro ⟨d', ⟨-, rfl⟩ | h⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨d', h⟩
  · rintro (rfl | ⟨d', h⟩)
    · exact ⟨d, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨d', Or.inr h⟩

theorem secs_nil : secs ([] : List (Deg k × R)) = ⊥ := by
  unfold secs
  simp

theorem range_lsmul_eq (M : Type) [AddCommGroup M] [Module R M] (s : R) :
    LinearMap.range (LinearMap.lsmul R M s) = Ideal.span {s} • (⊤ : Submodule R M) := by
  rw [Submodule.ideal_span_singleton_smul]
  ext x
  simp [Submodule.mem_smul_pointwise_iff_exists]

theorem GMod.ker_quotsMk (ts : List (Deg k × R)) (F : GMod B R k) :
    LinearMap.ker (GMod.quotsMk ts F) = secs ts • (⊤ : Submodule R F.M) := by
  induction ts generalizing F with
  | nil =>
    rw [secs_nil, Submodule.bot_smul]
    exact LinearMap.ker_id
  | cons p ts ih =>
    obtain ⟨d, s⟩ := p
    have h1 : LinearMap.ker (GMod.quotsMk ((d, s) :: ts) F) =
        (LinearMap.ker (GMod.quotsMk ts (F.quot s))).comap
          (LinearMap.range (LinearMap.lsmul R F.M s)).mkQ := LinearMap.ker_comp _ _
    rw [h1, ih (F.quot s), secs_cons, Submodule.sup_smul]
    have h2 : (secs ts • (⊤ : Submodule R (F.quot s).M)) =
        (secs ts • (⊤ : Submodule R F.M)).map (LinearMap.range (LinearMap.lsmul R F.M s)).mkQ := by
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
      rfl
    rw [h2, Submodule.comap_map_mkQ, range_lsmul_eq]

theorem GMod.quots_gr (ts : List (Deg k × R)) (F : GMod B R k) (m : Deg k) :
    (F.quots ts).gr m = (F.gr m).map ((GMod.quotsMk ts F).restrictScalars B) := by
  induction ts generalizing F with
  | nil =>
    exact (Submodule.map_id _).symm
  | cons p ts ih =>
    obtain ⟨d, s⟩ := p
    have h1 := ih (F.quot s)
    have h3 : (F.quots ((d, s) :: ts)).gr m = ((F.quot s).quots ts).gr m := rfl
    rw [h3, h1]
    exact (Submodule.map_comp ((LinearMap.range (LinearMap.lsmul R F.M s)).mkQ.restrictScalars B)
      ((GMod.quotsMk ts (F.quot s)).restrictScalars B) (F.gr m)).symm

def GMod.quot0Equiv (F : GMod B R k) (hF : DirectSum.IsInternal F.gr) (β : B) (m : Deg k) :
    (F.gr m ⧸ LinearMap.range (LinearMap.lsmul B (F.gr m) β)) ≃ₗ[B]
      (F.quot (algebraMap B R β)).gr m := by
  classical
  let N : Submodule R F.M := LinearMap.range (LinearMap.lsmul R F.M (algebraMap B R β))
  let f : F.gr m →ₗ[B] (F.gr m).map (N.mkQ.restrictScalars B) :=
    (N.mkQ.restrictScalars B).submoduleMap (F.gr m)
  have hf : Function.Surjective f := LinearMap.submoduleMap_surjective _ _
  have hk : LinearMap.range (LinearMap.lsmul B (F.gr m) β) = LinearMap.ker f := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      show N.mkQ ((β • y : F.gr m) : F.M) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨(y : F.M), by simp⟩
    · intro hx
      rw [LinearMap.mem_ker] at hx
      have hx1 : N.mkQ (x : F.M) = 0 := congrArg Subtype.val hx
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx1
      obtain ⟨y, hy⟩ := hx1
      obtain ⟨Y, rfl⟩ := hF.2 y
      have hy' : β • DirectSum.coeLinearMap F.gr Y = (x : F.M) := by
        rw [← hy]
        show _ = algebraMap B R β • (DirectSum.coeAddMonoidHom F.gr Y : F.M)
        rw [algebraMap_smul]
        rfl
      have h2 : DirectSum.coeLinearMap F.gr (β • Y) =
          DirectSum.coeLinearMap F.gr (DirectSum.lof B (Deg k) (fun i => F.gr i) m x) := by
        rw [map_smul, hy', DirectSum.coeLinearMap_lof]
      have h3 : β • Y = DirectSum.lof B (Deg k) (fun i => F.gr i) m x := hF.1 h2
      refine ⟨Y m, ?_⟩
      have h4 : (β • Y) m = (DirectSum.lof B (Deg k) (fun i => F.gr i) m x) m := by rw [h3]
      rw [DirectSum.lof_apply, DirectSum.smul_apply] at h4
      exact h4
  exact (Submodule.quotEquivOfEq _ _ hk).trans (f.quotKerEquivOfSurjective hf)

def GMod.ann0Equiv (F : GMod B R k) (β : B) (m : Deg k) :
    LinearMap.ker (LinearMap.lsmul B (F.gr m) β) ≃ₗ[B] (F.ann (algebraMap B R β) 0).gr m where
  toFun x := ⟨⟨(x.1 : F.M), by
      have := x.2
      rw [LinearMap.mem_ker] at this ⊢
      show algebraMap B R β • (x.1 : F.M) = 0
      rw [algebraMap_smul]
      exact congrArg Subtype.val this⟩, by
      show (x.1 : F.M) ∈ F.gr (m - 0)
      rw [sub_zero]
      exact x.1.2⟩
  invFun y := ⟨⟨(y.1.1 : F.M), by
      have : (y.1.1 : F.M) ∈ F.gr (m - 0) := y.2
      rwa [sub_zero] at this⟩, by
      have := y.1.2
      rw [LinearMap.mem_ker] at this ⊢
      apply Subtype.ext
      show β • (y.1.1 : F.M) = 0
      rw [← algebraMap_smul R β (y.1.1 : F.M)]
      exact this⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

end

theorem quots_isGr {k : ℕ} (X : HidaSetting k) (ts : List (Deg k × X.R)) (F : X.Mod) (hv : Valid X.𝒜 ts)
    (hF : F.IsGr X.𝒜) : (F.quots ts).IsGr X.𝒜 := by
  induction ts generalizing F with
  | nil => exact hF
  | cons p ts ih =>
    obtain ⟨d, s⟩ := p
    exact ih (F.quot s) (fun p hp => hv p (List.mem_cons_of_mem _ hp))
      ((ruleGr k X F hF).2.2 d s (hv (d, s) List.mem_cons_self).2).1

theorem chi_single0 {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R] (F : GMod B R k)
    (hF : DirectSum.IsInternal F.gr) (β : B) (m : Deg k) :
    chi [((0 : Deg k), algebraMap B R β)] F m =
      ((Module.length B (F.gr m ⧸ LinearMap.range (LinearMap.lsmul B (F.gr m) β))).toNat : ℤ) -
      ((Module.length B (LinearMap.ker (LinearMap.lsmul B (F.gr m) β))).toNat : ℤ) := by
  show ((Module.length B ((F.quot (algebraMap B R β)).gr m)).toNat : ℤ) -
    ((Module.length B ((F.ann (algebraMap B R β) 0).gr m)).toNat : ℤ) = _
  rw [(F.quot0Equiv hF β m).length_eq, (F.ann0Equiv β m).length_eq]

end Formalism.MainNotions.V.Pf.V2.Calc
