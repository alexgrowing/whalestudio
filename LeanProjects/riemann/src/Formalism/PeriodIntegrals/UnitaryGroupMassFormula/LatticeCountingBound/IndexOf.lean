import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.IndexDefs

noncomputable section

open NumberField Matrix

namespace PI.UnitaryGroupMassFormula.LCG

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [StarRing E] {n : ℕ}

def sv (w : Fin n → E) : Fin n → E := fun i => starRingEnd E (w i)

theorem hform_dot (J : Matrix (Fin n) (Fin n) E) (w z : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J w z = (sv w ᵥ* J) ⬝ᵥ z := by
  unfold Formalism.UG.hform
  simp only [dotProduct, vecMul, sv, Finset.sum_mul]
  exact Finset.sum_comm

theorem sv_sum {k : ℕ} (s : Fin k → E) (b : Fin k → Fin n → E) :
    sv (∑ a, starRingEnd E (s a) • b a) = ∑ a, s a • sv (b a) := by
  funext i
  simp [sv, Finset.sum_apply, map_sum, map_mul]

theorem hform_herm (J : Matrix (Fin n) (Fin n) E) (hJ : Formalism.UG.IsHerm (starRingEnd E) J) (w z : Fin n → E) :
    starRingEnd E (Formalism.UG.hform (starRingEnd E) J w z) = Formalism.UG.hform (starRingEnd E) J z w := by
  have hJ' : ∀ i j, starRingEnd E (J i j) = J j i := by
    intro i j
    have := congrFun (congrFun hJ j) i
    simpa [Formalism.UG.cT] using this
  unfold Formalism.UG.hform
  simp only [map_sum, map_mul, starRingEnd_self_apply, hJ']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

end SlopeTestRemainingChoices

section Aux2

variable {E : Type} [Field E] [NumberField E]

theorem star_range [StarRing E] {x : E} (hx : x ∈ (algebraMap (𝓞 E) E).range) :
    starRingEnd E x ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨o, rfl⟩ := RingHom.mem_range.mp hx
  have hint : IsIntegral ℤ (starRingEnd E (algebraMap (𝓞 E) E o)) := by
    first
    | exact (RingOfIntegers.isIntegral_coe o).map (starRingEnd E).toIntAlgHom
    | exact (o.2).map (starRingEnd E).toIntAlgHom
  exact RingHom.mem_range.mpr ⟨⟨_, hint⟩, rfl⟩

theorem mem_oLat {k : ℕ} (v : Fin k → E) :
    v ∈ oLat E k ↔ ∃ x : Fin k → 𝓞 E, (fun c => algebraMap (𝓞 E) E (x c)) = v := by
  unfold oLat
  first
  | (rw [LinearMap.mem_range]; rfl)
  | exact Iff.rfl
  | (simp [LinearMap.mem_range, LinearMap.compLeft]; rfl)

theorem dualL_oLat (k : ℕ) : dualL (oLat E k) = oLat E k := by
  ext t
  constructor
  · intro ht
    have ht' : ∀ s ∈ oLat E k, s ⬝ᵥ t ∈ (algebraMap (𝓞 E) E).range := ht
    have h1 : ∀ c, t c ∈ (algebraMap (𝓞 E) E).range := by
      intro c
      have hs : (Pi.single c 1 : Fin k → E) ∈ oLat E k := by
        rw [mem_oLat]
        exact ⟨Pi.single c 1, by funext d; by_cases h : d = c <;> simp [Pi.single_apply, h]⟩
      have := ht' _ hs
      simpa [dotProduct, Pi.single_apply] using this
    choose x hx using fun c => RingHom.mem_range.mp (h1 c)
    rw [mem_oLat]
    exact ⟨x, funext hx⟩
  · intro ht
    show ∀ s ∈ oLat E k, s ⬝ᵥ t ∈ (algebraMap (𝓞 E) E).range
    intro s hs
    obtain ⟨x, rfl⟩ := (mem_oLat t).mp ht
    obtain ⟨y, rfl⟩ := (mem_oLat s).mp hs
    refine RingHom.mem_range.mpr ⟨∑ c, y c * x c, ?_⟩
    simp [dotProduct, map_sum, map_mul]

theorem card_quot_relIndex {M : Type*} [AddCommGroup M] [Module (𝓞 E) M] (S B : Submodule (𝓞 E) M) :
    Nat.card (B ⧸ S.comap B.subtype) = S.toAddSubgroup.relIndex B.toAddSubgroup := rfl

end Aux2

private theorem relIndex_comap_eq_of_le_range {G H : Type*} [AddGroup G] [AddGroup H] (f : G →+ H)
    (A B : AddSubgroup H) (hB : B ≤ f.range) : (A.comap f).relIndex (B.comap f) = A.relIndex B := by
  rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq, inf_eq_right.2 hB]

private theorem sum_smul_mem_span_iff_of_linearIndependent {K : Type} [Field K] [NumberField K] {n k : ℕ} (v : Fin k → Fin n → K)
    (hv : LinearIndependent K v) (t : Fin k → K) :
    (∑ c, t c • v c) ∈ Submodule.span (𝓞 K) (Set.range v) ↔ ∀ c, t c ∈ (algebraMap (𝓞 K) K).range := by
  constructor
  · intro h
    obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 h
    have h0 : ∑ c, (algebraMap (𝓞 K) K (o c) - t c) • v c = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, algebraMap_smul]
      rw [ho, sub_self]
    have h1 := Fintype.linearIndependent_iff.1 hv _ h0
    intro c
    exact ⟨o c, sub_eq_zero.1 (h1 c)⟩
  · intro h
    refine Submodule.sum_mem _ fun c _ => ?_
    obtain ⟨o, ho⟩ := RingHom.mem_range.1 (h c)
    rw [← ho, algebraMap_smul]
    exact Submodule.smul_mem _ o (Submodule.subset_span ⟨c, rfl⟩)

theorem lattice_indexOf : IndexOf := by
  unfold IndexOf
  intro hDual hDet
  unfold IndexIneq
  intro I Λ hfg hspan hdual δ k u b' hu hδu hδspan hb' hb'li hperp hperpspan hidx1 hidx2
  let v : Fin k → Fin I.n → I.E := fun c => δ *ᵥ u c

  let ιL : (Fin k → I.E) →ₗ[𝓞 I.E] (Fin I.n → I.E) :=
    { toFun := fun t => ∑ c, t c • v c
      map_add' := fun s t => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun o t => by simp only [Pi.smul_apply, smul_assoc, RingHom.id_apply, Finset.smul_sum] }
  let β : (Fin k → I.E) →+ (Fin I.n → I.E) :=
    AddMonoidHom.mk' (fun s => ∑ a, starRingEnd I.E (s a) • b' a) (fun s t => by
      simp only [Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib])
  have hι : ∀ t, ιL t = ∑ c, t c • v c := fun t => rfl
  have hβ : ∀ s, β s = ∑ a, starRingEnd I.E (s a) • b' a := fun s => rfl
  have hint_v : ∀ t : Fin k → I.E, ιL t ∈ Submodule.span (𝓞 I.E) (Set.range v) ↔ t ∈ oLat I.E k := by
    intro t
    rw [hι, sum_smul_mem_span_iff_of_linearIndependent v hδu t, mem_oLat]
    constructor
    · intro h
      choose x hx using fun c => RingHom.mem_range.1 (h c)
      exact ⟨x, funext hx⟩
    · rintro ⟨x, rfl⟩ c
      exact ⟨x c, rfl⟩
  have hint_b : ∀ s : Fin k → I.E, β s ∈ Submodule.span (𝓞 I.E) (Set.range b') ↔ s ∈ oLat I.E k := by
    intro s
    rw [hβ, sum_smul_mem_span_iff_of_linearIndependent b' hb'li, mem_oLat]
    constructor
    · intro h
      have h' : ∀ c, s c ∈ (algebraMap (𝓞 I.E) I.E).range := by
        intro c
        have h2 := star_range (h c)
        rwa [starRingEnd_self_apply] at h2
      choose x hx using fun c => RingHom.mem_range.1 (h' c)
      exact ⟨x, funext hx⟩
    · rintro ⟨x, rfl⟩ c
      exact star_range ⟨x c, rfl⟩
  have hrange_v : (imSub I Λ δ).toAddSubgroup ≤ ιL.toAddMonoidHom.range := by
    intro y hy
    simp only [imSub, Submodule.mem_toAddSubgroup, Submodule.mem_map] at hy
    obtain ⟨z, -, rfl⟩ := hy
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun I.E).1 (hδspan z)
    exact AddMonoidHom.mem_range.2 ⟨g, hg⟩
  have hrange_b : (perpSub I Λ δ).toAddSubgroup ≤ β.range := by
    intro w hw
    have hw' : PerpKer I δ w := by
      simp only [perpSub, Submodule.mem_toAddSubgroup, Submodule.mem_inf, Submodule.restrictScalars_mem] at hw
      exact hw.2
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun I.E).1 (hperpspan w hw')
    refine AddMonoidHom.mem_range.2 ⟨fun a => starRingEnd I.E (g a), ?_⟩
    rw [hβ]
    simpa only [starRingEnd_self_apply] using hg
  have hoL_v : (oLat I.E k).toAddSubgroup =
      (Submodule.span (𝓞 I.E) (Set.range v)).toAddSubgroup.comap ιL.toAddMonoidHom := by
    ext t
    simp only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_comap, LinearMap.toAddMonoidHom_coe]
    exact (hint_v t).symm
  have hoL_b : (oLat I.E k).toAddSubgroup =
      (Submodule.span (𝓞 I.E) (Set.range b')).toAddSubgroup.comap β := by
    ext s
    simp only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_comap]
    exact (hint_b s).symm
  let R : Submodule (𝓞 I.E) (Fin k → I.E) := (imSub I Λ δ).comap ιL
  let Q : AddSubgroup (Fin k → I.E) := (perpSub I Λ δ).toAddSubgroup.comap β
  have hRQ : R.toAddSubgroup = (imSub I Λ δ).toAddSubgroup.comap ιL.toAddMonoidHom := by
    ext t
    exact Iff.rfl
  have hidxv : idx I (imSub I Λ δ) v =
      (Submodule.span (𝓞 I.E) (Set.range v)).toAddSubgroup.relIndex (imSub I Λ δ).toAddSubgroup :=
    card_quot_relIndex _ _
  have hidxb : idx I (perpSub I Λ δ) b' =
      (Submodule.span (𝓞 I.E) (Set.range b')).toAddSubgroup.relIndex (perpSub I Λ δ).toAddSubgroup :=
    card_quot_relIndex _ _
  have hRidx : (oLat I.E k).toAddSubgroup.relIndex R.toAddSubgroup = idx I (imSub I Λ δ) v := by
    rw [hidxv, hoL_v, hRQ, relIndex_comap_eq_of_le_range _ _ _ hrange_v]
  have hQidx : (oLat I.E k).toAddSubgroup.relIndex Q = idx I (perpSub I Λ δ) b' := by
    rw [hidxb, hoL_b, relIndex_comap_eq_of_le_range _ _ _ hrange_b]
  have hoR : oLat I.E k ≤ R := by
    intro t ht
    obtain ⟨x, rfl⟩ := (mem_oLat t).1 ht
    show ιL _ ∈ imSub I Λ δ
    rw [hι]
    simp only [imSub, Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply]
    refine ⟨∑ c, x c • u c, Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hu c), ?_⟩
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Matrix.mulVec_smul, algebraMap_smul, v]
  have hspanperp : Submodule.span (𝓞 I.E) (Set.range b') ≤ perpSub I Λ δ := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    simp only [perpSub, SetLike.mem_coe, Submodule.mem_inf, Submodule.restrictScalars_mem]
    exact ⟨hb' a, hperp a⟩
  have hoQ : (oLat I.E k).toAddSubgroup ≤ Q := by
    intro s hs
    show β s ∈ perpSub I Λ δ
    exact hspanperp ((hint_b s).2 hs)
  have hDo : dualL R ≤ oLat I.E k := by
    conv_rhs => rw [← dualL_oLat k]
    intro t ht
    show ∀ s ∈ oLat I.E k, s ⬝ᵥ t ∈ (algebraMap (𝓞 I.E) I.E).range
    intro s hs
    exact ht s (hoR hs)

  have hadd : ∀ x y z, hf I (x + y) z = hf I x z + hf I y z := by
    intro x y z
    simp only [hf, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  have hsmul : ∀ (a : I.E) x z, hf I (a • x) z = starRingEnd I.E a * hf I x z := by
    intro a x z
    simp only [hf, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]
    simp only [← Finset.mul_sum]
  have hsum : ∀ z (g : Fin k → I.E), hf I (∑ a, g a • b' a) z = ∑ a, starRingEnd I.E (g a) * hf I (b' a) z := by
    intro z g
    let φ : (Fin I.n → I.E) →+ I.E := AddMonoidHom.mk' (fun x => hf I x z) (fun x y => hadd x y z)
    have e := map_sum φ (fun a => g a • b' a) Finset.univ
    simp only [φ, AddMonoidHom.mk'_apply, hsmul] at e
    exact e

  have hkey : ∀ r ∈ (dualL R).toAddSubgroup, ∃ s ∈ Q, s ᵥ* pairM I b' u = r := by
    intro r hr
    have hr' : ∀ t ∈ R, t ⬝ᵥ r ∈ (algebraMap (𝓞 I.E) I.E).range := hr
    let G : (Fin I.n → I.E) →ₗ[I.E] (Fin k →₀ I.E) :=
      hδu.repr.comp ((Matrix.mulVecLin δ).codRestrict (Submodule.span I.E (Set.range v)) hδspan)
    have hG : ∀ z, δ *ᵥ z = ∑ c, G z c • v c := by
      intro z
      have e : Finsupp.linearCombination I.E v (hδu.repr ⟨δ *ᵥ z, hδspan z⟩) = δ *ᵥ z := by
        first
        | exact hδu.linearCombination_repr _
        | exact hδu.total_repr _
      rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at e
      exact e.symm
    have hGu : ∀ c, G (u c) = Finsupp.single c 1 := fun c => hδu.repr_eq_single c _ rfl
    let gL : (Fin I.n → I.E) →ₗ[I.E] I.E := ∑ c, r c • ((Finsupp.lapply c).comp G)
    have hgL : ∀ z, gL z = ∑ c, r c * G z c := by
      intro z
      simp only [gL, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
        Finsupp.lapply_apply, smul_eq_mul]
    let ℓ : Fin I.n → I.E := fun j => gL (fun j' => if j = j' then 1 else 0)
    have hgℓ : ∀ z, gL z = ℓ ⬝ᵥ z := by
      intro z
      rw [LinearMap.pi_apply_eq_sum_univ gL z, dotProduct]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_eq_mul, mul_comm]
    let m : Fin I.n → I.E := ℓ ᵥ* I.J⁻¹
    let w : Fin I.n → I.E := sv m
    have hJ : I.J⁻¹ * I.J = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 I.J_det)
    have hw : ∀ z, hf I w z = gL z := by
      intro z
      have hsv : sv w = m := by
        funext i
        simp [w, sv]
      rw [hf, hform_dot, hsv, hgℓ]
      simp only [m, Matrix.vecMul_vecMul, hJ, Matrix.vecMul_one]
    have hwΛ : w ∈ Λ := by
      apply hdual
      intro y hy
      have e : hf I y w = starRingEnd I.E (hf I w y) := by
        simp only [hf]
        rw [hform_herm I.J I.J_herm w y]
      rw [e]
      apply star_range
      rw [hw, hgL]
      have htR : (fun c => G y c) ∈ R := by
        show ιL _ ∈ imSub I Λ δ
        rw [hι]
        simp only [imSub, Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply]
        exact ⟨y, hy, hG y⟩
      have h2 := hr' _ htR
      rw [show (∑ c, r c * G y c) = ∑ c, G y c * r c from Finset.sum_congr rfl fun c _ => mul_comm _ _]
      exact h2
    have hwperp : PerpKer I δ w := by
      intro z hz
      rw [hw, hgL]
      have h0 : (Matrix.mulVecLin δ).codRestrict (Submodule.span I.E (Set.range v)) hδspan z = 0 :=
        Subtype.ext hz
      have hG0 : G z = 0 := by
        simp only [G, LinearMap.comp_apply, h0, map_zero]
      simp [hG0]
    have hwperpSub : w ∈ perpSub I Λ δ := by
      simp only [perpSub, Submodule.mem_inf, Submodule.restrictScalars_mem]
      exact ⟨hwΛ, hwperp⟩
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun I.E).1 (hperpspan w hwperp)
    refine ⟨fun a => starRingEnd I.E (g a), ?_, ?_⟩
    · show β _ ∈ perpSub I Λ δ
      rw [hβ]
      simp only [starRingEnd_self_apply]
      rw [hg]
      exact hwperpSub
    · funext c
      simp only [Matrix.vecMul, dotProduct, pairM, Matrix.of_apply]
      rw [← hsum (u c) g, hg, hw, hgL, hGu]
      simp [Finsupp.single_apply]
  have hd := hDual I.E k (oLat I.E k) R hoR (by rw [hRidx]; exact hidx1)
  rw [dualL_oLat] at hd
  have hmain := hDet I.E k (pairM I b' u) Q (dualL R).toAddSubgroup hoQ (by rw [hQidx]; exact hidx2)
    (fun x hx => hDo hx) hd.1 hkey
  have h3 : (dualL R).toAddSubgroup.relIndex (oLat I.E k).toAddSubgroup ≤ idx I (imSub I Λ δ) v := by
    rw [← hRidx]
    exact hd.2
  calc |((Algebra.norm ℚ (pairM I b' u).det : ℚ) : ℝ)|
      ≤ ((oLat I.E k).toAddSubgroup.relIndex Q : ℝ) *
          ((dualL R).toAddSubgroup.relIndex (oLat I.E k).toAddSubgroup : ℝ) := hmain
    _ ≤ (idx I (perpSub I Λ δ) b' : ℝ) * (idx I (imSub I Λ δ) v : ℝ) := by
        rw [hQidx]
        gcongr
    _ = _ := mul_comm _ _

end PI.UnitaryGroupMassFormula.LCG
