import Development.EtaleCohomology.EtaleSheaves.CupProductRingLaws

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTwPairUniquePf

def PairHtpy {R : Type} [CommRing R] {I J K : Cx R} (μ μ' : Pair I J K) : Prop :=
  ∃ h : ∀ (U : Scheme.{0}) (s t w : ℤ), s + t = w + 1 →
      Sec (I.X s) U →ₗ[ULift.{1} R] Sec (J.X t) U →ₗ[ULift.{1} R] Sec (K.X w) U,
    (∀ {V U : Scheme.{0}} (g : V ⟶ U) (s t w : ℤ) (hw : s + t = w + 1) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
      Sec.res g (h U s t w hw a b) = h V s t w hw (Sec.res g a) (Sec.res g b)) ∧
    ∀ (U : Scheme.{0}) (s t w : ℤ) (hw : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
      μ.mul U s t w hw a b - μ'.mul U s t w hw a b =
        Sec.map (K.d (w - 1) w) (h U s t (w - 1) (by omega) a b) +
          h U (s + 1) t w (by omega) (Sec.map (I.d s (s + 1)) a) b +
          s.negOnePow • h U s (t + 1) w (by omega) a (Sec.map (J.d t (t + 1)) b)

def LeafTwPairHtpy : Prop := ∀ (q : ℕ) [NeZero q] (i j : ℤ) (μ μ' : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q (i + j)))),
  IsTwPair μ → IsTwPair μ' → PairHtpy μ μ'

def LeafHtpyAW : Prop := ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ μ' : Pair I J K), PairHtpy μ μ' →
  ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (γ γ' : Cocycle ((chains R).obj E) K k), μ.IsAW hk α.1 β.1 γ.1 → μ'.IsAW hk α.1 β.1 γ'.1 →
    CohomologyClass.mk γ = CohomologyClass.mk γ'

theorem cup_eq_of_aw {R : Type} [CommRing R] {I J K : Cx R} (hc : LateralTheory.E.CupProductRingLaws.LeafCupSpec) (μ μ' : Pair I J K)
    (E : Spc) {n m k : ℤ} (hk : n + m = k)
    (hAW : ∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
      (γ γ' : Cocycle ((chains R).obj E) K k), μ.IsAW hk α.1 β.1 γ.1 → μ'.IsAW hk α.1 β.1 γ'.1 →
      CohomologyClass.mk γ = CohomologyClass.mk γ') :
    μ.cup E hk = μ'.cup E hk := by
  obtain ⟨ex, sp⟩ := hc R μ E hk
  obtain ⟨ex', sp'⟩ := hc R μ' E hk
  ext a b
  obtain ⟨α, rfl⟩ := a.mk_surjective
  obtain ⟨β, rfl⟩ := b.mk_surjective
  obtain ⟨γ, hγ⟩ := ex α β
  obtain ⟨γ', hγ'⟩ := ex' α β
  rw [sp α β γ hγ, sp' α β γ' hγ']
  exact hAW α β γ γ' hγ hγ'

end LateralTheory.E.LeafTwPairUniquePf

open LateralTheory.E.LeafTwPairUniquePf in
theorem LateralTheory.E.CupProductRingLaws.LeafTwPairUnique_of (hc : LateralTheory.E.CupProductRingLaws.LeafCupSpec) (hh : LeafTwPairHtpy)
    (ha : LeafHtpyAW) : LateralTheory.E.CupProductRingLaws.LeafTwPairUnique := by
  intro q _ i j μ μ' hμ hμ' E n m k hk
  exact cup_eq_of_aw hc μ μ' E hk (ha (ZMod q) μ μ' (hh q i j μ μ' hμ hμ') E hk)
