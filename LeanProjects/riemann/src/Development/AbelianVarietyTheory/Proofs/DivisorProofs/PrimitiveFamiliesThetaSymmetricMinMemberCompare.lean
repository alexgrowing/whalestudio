import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingElementarySymmetricUnit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.PrimCmp

theorem esymm_map_hom {R R' : Type} [CommRing R] [CommRing R'] (i : R →+* R') (M : Multiset R) (j : ℕ) :
    (M.map i).esymm j = i (M.esymm j) := by
  unfold Multiset.esymm
  rw [Multiset.powersetCard_map, Multiset.map_map, map_multiset_sum, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun s _ => ?_)
  simp only [Function.comp, map_multiset_prod]

theorem symTup_map {R R' : Type} [CommRing R] [CommRing R'] (i : R →+* R') {N : ℕ} (c : Fin N → R) (j : Fin N) :
    i (symTup c j) = symTup (fun b => i (c b)) j := by
  unfold symTup
  rw [map_pow]
  congr 1
  have hm : Finset.univ.val.map (fun b => i (c b)) = (Finset.univ.val.map c).map i := by
    rw [Multiset.map_map]; rfl
  rw [hm, esymm_map_hom]

theorem esymm_map_mul {R : Type} [CommRing R] {A : Type} (t : R) (M : Multiset A) (f : A → R) (j : ℕ) :
    (M.map fun b => t * f b).esymm j = t ^ j * (M.map f).esymm j := by
  have : (M.map fun b => t * f b) = (M.map f).map (fun x => t * x) := by rw [Multiset.map_map]; rfl
  rw [this]
  unfold Multiset.esymm
  rw [Multiset.powersetCard_map, Multiset.map_map, ← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun s hs => ?_)
  have hc := (Multiset.mem_powersetCard.1 hs).2
  simp only [Function.comp]
  rw [Multiset.prod_map_mul]
  simp [hc]

theorem symTup_mul {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R) (t : R) (j : Fin N) :
    symTup (fun b => t * c b) j = t ^ N.factorial * symTup c j := by
  unfold symTup
  have h := esymm_map_mul t (Finset.univ.val) c ((j : ℕ) + 1)
  rw [h, mul_pow, ← pow_mul, Nat.mul_div_cancel' (Nat.dvd_factorial (Nat.succ_pos _) j.2)]

theorem mem_of_isIntegralElem {V K : Type} [CommRing V] [Field K] (i : V →+* K) (W : ValuationSubring K)
    (hW : ∀ v, i v ∈ W) {x : K} (hx : i.IsIntegralElem x) : x ∈ W := by
  obtain ⟨p, hm, hp⟩ := hx
  let φ : V →+* W := i.codRestrict W.toSubring hW
  have hφ : (algebraMap W K).comp φ = i := by ext v; rfl
  have hint : IsIntegral W x := ⟨p.map φ, hm.map φ, by rw [Polynomial.eval₂_map, hφ]; exact hp⟩
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  exact y.2

theorem mem_of_pow_mem {K : Type} [Field K] (W : ValuationSubring K) {w : K} {k : ℕ} (hk : 1 ≤ k)
    (h : w ^ k ∈ W) : w ∈ W := by
  rw [← W.valuation_le_one_iff] at h ⊢
  rw [map_pow] at h
  exact (pow_le_one_iff (by omega)).1 h

theorem mem_range_of_forall {V K : Type} [CommRing V] [IsDomain V] [IsIntegrallyClosed V] [Field K]
    (io : FractionRing V →+* K) (z : FractionRing V)
    (h : ∀ W : ValuationSubring K, (∀ v, io (algebraMap V (FractionRing V) v) ∈ W) → io z ∈ W) :
    z ∈ Set.range (algebraMap V (FractionRing V)) := by
  letI : Algebra V K := (io.comp (algebraMap V (FractionRing V))).toAlgebra
  have hic : IsIntegrallyClosedIn (integralClosure V K).toSubring K :=
    inferInstanceAs (IsIntegrallyClosedIn (integralClosure V K) K)
  have h1 : io z ∈ (integralClosure V K).toSubring := by
    by_contra hn
    obtain ⟨W, hW, hzW⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hn
    exact hzW (h W (fun v => hW ((integralClosure V K).algebraMap_mem v)))
  let f : FractionRing V →ₐ[V] K := { io with commutes' := fun _ => rfl }
  have h2 : IsIntegral V z := (isIntegral_algHom_iff f (f : FractionRing V →+* K).injective).1 h1
  exact IsIntegrallyClosed.isIntegral_iff.1 h2

end GlobalTheory.UMin.PrimCmp

namespace GlobalTheory.UMin.PrimCmp

theorem key {V K : Type} [CommRing V] [IsDomain V] [Field K] (io : FractionRing V →+* K) (N : ℕ) (c : Fin N → K) (a : K)
    (ha : a ≠ 0) (hP : Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c b / a)) (e : Fin N → FractionRing V)
    (he : ∀ j, io (e j) = symTup c j) (j₀ : Fin N) (he0 : e j₀ ≠ 0)
    (hq : ∀ j, e j / e j₀ ∈ Set.range (algebraMap V (FractionRing V))) (W : ValuationSubring K)
    (hW : ∀ v, io (algebraMap V (FractionRing V) v) ∈ W) :
    io (e j₀) / a ^ N.factorial ∈ W ∧ (io (e j₀) / a ^ N.factorial)⁻¹ ∈ W := by
  have hcW : ∀ b, c b / a ∈ W := fun b => mem_of_isIntegralElem _ W hW (hP.1 b)
  obtain ⟨b₀, hb0, hb0i⟩ := hP.2
  have hb0W : (c b₀ / a)⁻¹ ∈ W := mem_of_isIntegralElem _ W hW hb0i
  let y : Fin N → W := fun b => ⟨c b / a, hcW b⟩
  have hu : IsUnit (y b₀) := (Units.mkOfMulEqOne (y b₀) ⟨_, hb0W⟩ (Subtype.ext (show c b₀ / a * (c b₀ / a)⁻¹ = 1 from mul_inv_cancel₀ hb0))).isUnit
  let z : Fin N → W := fun b => y b * ↑hu.unit⁻¹
  have hz : z b₀ = 1 := by simp [z]
  obtain ⟨k, hk1, hkN, hku⟩ := GlobalTheory.exists_isUnit_esymm_of_eq_one W (Fin N) z b₀ hz
  have hyz : ∀ b, y b = y b₀ * z b := by
    intro b; simp only [z]; rw [mul_left_comm, IsUnit.mul_val_inv, _root_.mul_one]
  have hesy : IsUnit ((Finset.univ.val.map y).esymm k) := by
    have hm : Finset.univ.val.map y = Finset.univ.val.map (fun b => y b₀ * z b) :=
      Multiset.map_congr rfl fun b _ => hyz b
    rw [hm, esymm_map_mul]
    exact (hu.pow k).mul hku
  have hkN' : k ≤ N := by simpa using hkN
  let j₁ : Fin N := ⟨k - 1, by omega⟩
  have hsy : IsUnit (symTup y j₁) := by
    unfold symTup
    have : (j₁ : ℕ) + 1 = k := by simp only [j₁]; omega
    rw [this]
    exact hesy.pow _
  have hcoe : ∀ j, ((symTup y j : W) : K) = io (e j) / a ^ N.factorial := by
    intro j
    have h1 := symTup_map W.subtype y j
    rw [ValuationSubring.coe_subtype] at h1
    rw [h1]
    have h2 : (fun b => ((y b : W) : K)) = fun b => a⁻¹ * c b := by
      funext b; simp [y, div_eq_inv_mul]
    rw [h2, symTup_mul, he, inv_pow, inv_mul_eq_div]
  have ht : io (e j₀) / a ^ N.factorial ∈ W := hcoe j₀ ▸ (symTup y j₀).2
  obtain ⟨v, hv⟩ := hq j₁
  have hr : io (e j₁ / e j₀) ∈ W := by rw [← hv]; exact hW v
  have hio0 : io (e j₀) ≠ 0 := (map_ne_zero io).2 he0
  have hsplit : symTup y j₁ = ⟨_, hr⟩ * ⟨_, ht⟩ := by
    apply Subtype.ext
    rw [hcoe]
    show _ = io (e j₁ / e j₀) * (io (e j₀) / a ^ N.factorial)
    rw [map_div₀]
    field_simp
  rw [hsplit] at hsy
  have htu := isUnit_of_mul_isUnit_right hsy
  refine ⟨ht, ?_⟩
  have h3 : ((↑htu.unit⁻¹ : W) : K) * (io (e j₀) / a ^ N.factorial) = 1 := by
    have := congrArg Subtype.val (IsUnit.val_inv_mul htu)
    rw [MulMemClass.coe_mul, OneMemClass.coe_one] at this
    exact this
  rw [← eq_inv_of_mul_eq_one_left h3]
  exact (↑htu.unit⁻¹ : W).2

end GlobalTheory.UMin.PrimCmp

theorem GlobalTheory.UMin.prim_symTup_cmp : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsIntegrallyClosed V] [Field K] (io : FractionRing V →+* K) (N N' k : ℕ) (J : Type) (c : Fin N → K) (c' : Fin N' → K) (a : K) (e : Fin N → FractionRing V) (th : J → FractionRing V), a ≠ 0 → 1 ≤ k → Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c b / a) → Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c' b / a) → (∀ j, io (e j) = symTup c j) → (∀ x, ∃ b, c' x ^ k = io (th b) ^ k) → (∀ b, ∃ x, c' x ^ k = io (th b) ^ k) → ∀ j₀, e j₀ ≠ 0 → (∀ j, e j / e j₀ ∈ Set.range (algebraMap V (FractionRing V))) → (∀ b, th b ^ N.factorial / e j₀ ∈ Set.range (algebraMap V (FractionRing V))) ∧ ∃ b, th b ≠ 0 ∧ e j₀ / th b ^ N.factorial ∈ Set.range (algebraMap V (FractionRing V)) := by
  intro V K _ _ _ _ io N N' k J c c' a e th ha hk hP hP' he hth1 hth2 j₀ he0 hq
  refine ⟨fun b => ?_, ?_⟩
  · apply GlobalTheory.UMin.PrimCmp.mem_range_of_forall io
    intro W hW
    obtain ⟨-, hti⟩ := GlobalTheory.UMin.PrimCmp.key io N c a ha hP e he j₀ he0 hq W hW
    obtain ⟨x, hx⟩ := hth2 b
    have hw : io (th b) / a ∈ W := by
      refine GlobalTheory.UMin.PrimCmp.mem_of_pow_mem W hk ?_
      rw [div_pow, ← hx, ← div_pow]
      exact pow_mem (GlobalTheory.UMin.PrimCmp.mem_of_isIntegralElem _ W hW (hP'.1 x)) k
    have hio0 : io (e j₀) ≠ 0 := (map_ne_zero io).2 he0
    have heq : io (th b ^ N.factorial / e j₀) = (io (th b) / a) ^ N.factorial * (io (e j₀) / a ^ N.factorial)⁻¹ := by
      rw [map_div₀, map_pow, div_pow, inv_div]
      field_simp
    rw [heq]
    exact mul_mem (pow_mem hw _) hti
  · obtain ⟨x₀, hx0, hx0i⟩ := hP'.2
    obtain ⟨b₁, hb1⟩ := hth1 x₀
    have hk0 : k ≠ 0 := by omega
    have hth0 : io (th b₁) ≠ 0 := by
      intro h0
      apply hx0
      have h2 : c' x₀ ^ k = 0 := by rw [hb1, h0, zero_pow hk0]
      simp [pow_eq_zero_iff hk0 |>.1 h2]
    refine ⟨b₁, fun h => hth0 (by rw [h, map_zero]), ?_⟩
    apply GlobalTheory.UMin.PrimCmp.mem_range_of_forall io
    intro W hW
    obtain ⟨ht, -⟩ := GlobalTheory.UMin.PrimCmp.key io N c a ha hP e he j₀ he0 hq W hW
    have hwi : (io (th b₁) / a)⁻¹ ∈ W := by
      refine GlobalTheory.UMin.PrimCmp.mem_of_pow_mem W hk ?_
      rw [inv_pow, div_pow, ← hb1, ← div_pow, ← inv_pow]
      exact pow_mem (GlobalTheory.UMin.PrimCmp.mem_of_isIntegralElem _ W hW hx0i) k
    have heq : io (e j₀ / th b₁ ^ N.factorial) = (io (e j₀) / a ^ N.factorial) * ((io (th b₁) / a)⁻¹) ^ N.factorial := by
      rw [map_div₀, map_pow, inv_div, div_pow]
      field_simp
    rw [heq]
    exact mul_mem ht (pow_mem hwi _)
