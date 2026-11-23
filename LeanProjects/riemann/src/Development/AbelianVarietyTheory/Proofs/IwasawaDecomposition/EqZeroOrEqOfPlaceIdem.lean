import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceModelSum

open GlobalTheory.PlaceModel

theorem smul_tmul_one {F A E : Type} [Field F] [CommRing A] [CommRing E] [Algebra F A] [Algebra F E]
    (t : F) (a : A) : (t • a) ⊗ₜ[F] (1 : E) = a ⊗ₜ[F] algebraMap F E t := by
  rw [TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]

theorem trace_laws {R : Type} [CommRing R] {e c e' c' : R} (h1 : e * e = e) (c1 : c * c = c) (h2 : e * c = 0)
    (h1' : e' * e' = e') (c1' : c' * c' = c') (h2' : e' * c' = 0) :
    (e * e' + c * c') * (e * e' + c * c') = e * e' + c * c' ∧ (e + c) * (e * e' + c * c') = e * e' + c * c' ∧
      (e' + c') * (e * e' + c * c') = e * e' + c * c' ∧ (0 = e * e' + c * c' → e * e' = 0) ∧
      (e + c = e * e' + c * c' → e' + c' = e * e' + c * c' → e = e') :=
  ⟨by linear_combination (e' * e') * h1 + e * h1' + (c' * c') * c1 + c * c1' + (2 * e' * c') * h2,
    by linear_combination e' * h1 + c' * c1 + (e' + c') * h2,
    by linear_combination e * h1' + c * c1' + (e + c) * h2',
    fun ht => by linear_combination (-e) * ht - e' * h1 - c' * h2,
    fun b1 b2 => by
      linear_combination e * b1 - e' * b2 - h1 - h2 + h1' + h2' + e' * h1 + c' * h2 - e * h1' - c * h2'⟩

theorem eq_or_orth {A R : Type} [CommRing A] [CommRing R] (ι : A →+* R) (hinj : Function.Injective ι)
    {e c e' c' : R} {ε ε' t : A} (h1 : e * e = e) (c1 : c * c = c) (h2 : e * c = 0)
    (h1' : e' * e' = e') (c1' : c' * c' = c') (h2' : e' * c' = 0) (h3 : e + c = ι ε) (h3' : e' + c' = ι ε')
    (ht : ι t = e * e' + c * c') (p : t * t = t → ε * t = t → t = 0 ∨ t = ε)
    (p' : t * t = t → ε' * t = t → t = 0 ∨ t = ε') : e = e' ∨ e * e' = 0 := by
  obtain ⟨k1, k2, k3, k4, k5⟩ := trace_laws h1 c1 h2 h1' c1' h2'
  rw [← ht] at k1 k2 k3 k4 k5
  rw [h3] at k2 k5
  rw [h3'] at k3 k5
  have tt : t * t = t := hinj (by rw [map_mul]; exact k1)
  have t1 : ε * t = t := hinj (by rw [map_mul]; exact k2)
  have t2 : ε' * t = t := hinj (by rw [map_mul]; exact k3)
  by_cases h0 : t = 0
  · exact Or.inr (k4 (by rw [h0, map_zero]))
  · exact Or.inl (k5 (by rw [← (p tt t1).resolve_left h0]) (by rw [← (p' tt t2).resolve_left h0]))

variable {D : D7}

theorem exists_add_conj (a : AE D) : ∃ t : AF D.host.F, algebraMap (AF D.host.F) (AE D) t = a + cA D a := by
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [RingHom.map_zero, RingHom.map_zero, add_zero]⟩
  | add x y hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    exact ⟨s + t, by rw [RingHom.map_add, RingHom.map_add, hs, ht]; ring⟩
  | tmul a x =>
    have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
    obtain ⟨t, ht⟩ : ∃ t : D.host.F, algebraMap _ _ t = x + D.sp.cm.sig x := by
      apply (D.sp.cm.fixed _).1
      change D.sp.cm.sig _ = _
      rw [map_add, hσ, add_comm]
    refine ⟨t • a, ?_⟩
    change (t • a) ⊗ₜ[D.host.F] (1 : D.host.E) = a ⊗ₜ[D.host.F] x + a ⊗ₜ[D.host.F] D.sp.cm.sig x
    rw [← TensorProduct.tmul_add, ← ht, smul_tmul_one]

theorem eq_zero_or_eq_of_placeIdem {v : HeightOneSpectrum (𝓞 D.host.F)} {ε t : AF D.host.F}
    (hε : IsPlaceIdem D v ε) (ht : t * t = t) (hεt : ε * t = t) : t = 0 ∨ t = ε := by
  obtain ⟨α, rfl, h1, h0⟩ := hε
  have e1 : t.1 = 0 := by
    have : (0 : Ainf D.host.F) * t.1 = t.1 := congrArg Prod.fst hεt
    rw [← this, zero_mul]
  have e2 : α * t.2 = t.2 := congrArg Prod.snd hεt
  have e3 : t.2 * t.2 = t.2 := congrArg Prod.snd ht
  have e4 : ∀ w, w ≠ v → evalV D.host.F w t.2 = 0 := fun w hw => by rw [← e2, map_mul, h0 w hw, zero_mul]
  have e5 : evalV D.host.F v t.2 * (evalV D.host.F v t.2 - 1) = 0 := by
    rw [mul_sub, ← map_mul, e3, mul_one, sub_self]
  have ext : ∀ β : Af D.host.F, (∀ w, evalV D.host.F w t.2 = evalV D.host.F w β) → t = pairA D.host.F 0 β :=
    fun β h => Prod.ext e1 (RestrictedProduct.ext _ _ h)
  rcases mul_eq_zero.1 e5 with h | h
  · refine Or.inl (ext 0 fun w => ?_)
    rw [map_zero]
    by_cases hw : w = v
    · rw [hw, h]
    · exact e4 w hw
  · refine Or.inr (ext α fun w => ?_)
    by_cases hw : w = v
    · rw [hw, h1, sub_eq_zero.1 h]
    · rw [e4 w hw, h0 w hw]

theorem eq_or_mul_eq_zero {e e' : AE D} (he : IsSplitIdem D e) (he' : IsSplitIdem D e') : e = e' ∨ e * e' = 0 := by
  obtain ⟨h1, h2, v, ε, hε, h3⟩ := he
  obtain ⟨h1', h2', v', ε', hε', h3'⟩ := he'
  have hinj : Function.Injective (algebraMap (AF D.host.F) (AE D)) :=
    Algebra.TensorProduct.includeLeft_injective (S := D.host.F) (algebraMap D.host.F D.host.E).injective
  have c1 : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
  have c1' : cA D e' * cA D e' = cA D e' := by rw [← map_mul, h1']
  obtain ⟨t, ht⟩ := exists_add_conj (e * e')
  rw [RingHom.map_mul] at ht
  exact eq_or_orth _ hinj h1 c1 h2 h1' c1' h2' h3 h3' ht (eq_zero_or_eq_of_placeIdem hε)
    (eq_zero_or_eq_of_placeIdem hε')

theorem isSplitIdem_cA {e : AE D} (he : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hε, h3⟩ := he
  exact ⟨by rw [← map_mul, h1], by rw [cA_cA, mul_comm, h2], v, ε, hε, by rw [cA_cA, add_comm, h3]⟩

def IsOrthSum (e : AE D) : Prop :=
  ∃ (ι : Type) (P : Finset ι) (es : ι → AE D), (∀ i ∈ P, IsSplitIdem D (es i)) ∧
    (∀ i ∈ P, ∀ j ∈ P, j ≠ i → es i * es j = 0) ∧ e = ∑ i ∈ P, es i

theorem isOrthSum_of_isIdemSum {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (h : IsIdemSum e P) :
    IsOrthSum e := by
  obtain ⟨⟨es, h1, h2⟩, -⟩ := h
  refine ⟨_, P, es, fun i hi => (h1 i hi).1, fun i hi j hj hij => ?_, h2⟩
  refine (eq_or_mul_eq_zero (h1 i hi).1 (h1 j hj).1).resolve_left fun h => hij ?_
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  by_cases hx : x = 0
  · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
  · rw [(h1 i hi).2 x hx, (h1 j hj).2 x hx, h]

theorem IsOrthSum.conj {e : AE D} (h : IsOrthSum e) : IsOrthSum (cA D e) := by
  obtain ⟨ι, P, es, h1, h2, rfl⟩ := h
  exact ⟨ι, P, fun i => cA D (es i), fun i hi => isSplitIdem_cA (h1 i hi),
    fun i hi j hj hij => by rw [← map_mul, h2 i hi j hj hij, map_zero], map_sum _ _ _⟩

theorem mul_sum_orth {ι : Type} {P : Finset ι} {es : ι → AE D} (h1 : ∀ i ∈ P, IsSplitIdem D (es i))
    (h2 : ∀ i ∈ P, ∀ j ∈ P, j ≠ i → es i * es j = 0) {i : ι} (hi : i ∈ P) : es i * ∑ j ∈ P, es j = es i := by
  rw [Finset.mul_sum, Finset.sum_eq_single_of_mem i hi (h2 i hi), (h1 i hi).1]

theorem IsOrthSum.idem {e : AE D} (h : IsOrthSum e) : e * e = e := by
  obtain ⟨ι, P, es, h1, h2, rfl⟩ := h
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i hi => mul_sum_orth h1 h2 hi

theorem infPart_split {e : AE D} (he : IsSplitIdem D e) : infPart D e = 0 := by
  obtain ⟨h1, h2, v, ε, ⟨β, rfl, -⟩, h3⟩ := he
  have h0 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β)) = 0 := TensorProduct.zero_tmul _ _
  have : e = (e + cA D e) * e := by linear_combination -h1 - h2
  rw [this, h3, map_mul, h0, zero_mul]

theorem IsOrthSum.infPart_eq {e : AE D} (h : IsOrthSum e) : infPart D e = 0 := by
  obtain ⟨ι, P, es, h1, -, rfl⟩ := h
  exact Finset.sum_induction _ (fun y => infPart D y = 0)
    (fun x y hx hy => by rw [RingHom.map_add, hx, hy, add_zero]) (RingHom.map_zero _) fun i hi => infPart_split (h1 i hi)

variable {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}

theorem idem_smul_latO {e : AE D} (he : e * e = e) {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    e • u ∈ latO S T LS LT fun _ => True :=
  GlobalTheory.LatticeStable.smul_mem_latO D S T LS LT _ e (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, he])) u hu

theorem idem_smul_half {e : AE D} (he : e * e = e) {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    e • u ∈ (latO S T LS LT fun _ => True) ⊓ half S T e :=
  AddSubgroup.mem_inf.2 ⟨idem_smul_latO he hu, by rw [mem_half, smul_smul, he]⟩

theorem IsOrthSum.infPart_half {e : AE D} (h : IsOrthSum e) {u : WO S T} (hu : u ∈ half S T e) :
    u.map (infPart D) = 0 := by
  ext i j
  rw [Matrix.map_apply, ← (isHalf_iff S T).2 hu i j, map_mul, h.infPart_eq, zero_mul]
  rfl

theorem IsOrthSum.heisO_eq {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} (h : IsOrthSum e) (hec : cA D e * e = 0)
    {f : WO S T → ℂ} (hf : IsLatVac (heisO ψ S T) (latO S T LS LT fun _ => True) f) (u : WO S T)
    (hu : u ∈ (latO S T LS LT fun _ => True) ⊓ half S T e) : heisO ψ S T u f = f := by
  obtain ⟨ι, P, es, h1, h2, he⟩ := h
  have e1 : u = ∑ i ∈ P, es i • u := by rw [← Finset.sum_smul, ← he, (mem_half S T).1 hu.2]
  have key : (∑ i ∈ P, es i • u) ∈ half S T e ∧ heisL S T ψ (∑ i ∈ P, es i • u) f = f := by
    refine Finset.sum_induction _ (fun y => y ∈ half S T e ∧ heisL S T ψ y f = f) (fun x y hx hy => ?_) ?_
      fun i hi => ?_
    · exact ⟨add_mem hx.1 hy.1, by rw [← heisL_half S T ψ hec x hx.1 y hy.1, hy.2, hx.2]⟩
    · exact ⟨zero_mem _, GlobalTheory.LatVac.heisO_zero ψ f⟩
    · have := idem_smul_half (h1 i hi).1 hu.1
      refine ⟨?_, hf.2 _ (h1 i hi) _ this.1 ((isHalf_iff S T).2 this.2)⟩
      rw [mem_half, smul_smul, mul_comm, he, mul_sum_orth h1 h2 hi]
  rw [← e1] at key
  exact key.2

theorem IsOrthSum.mem_of_dual {ψ : AddChar (AF D.host.F) ℂ}
    (hdual : ∀ u : WO S T, u.map (infPart D) = 0 → (u ∈ (latO S T LS LT fun _ => True) ↔
      ∀ u' ∈ (latO S T LS LT fun _ => True), ψ (symplO S T u u') = 1))
    {a : AE D} (ha : IsOrthSum a) (x : WO S T) (hx : x ∈ half S T a)
    (h : ∀ y ∈ (latO S T LS LT fun _ => True) ⊓ half S T (cA D a), ψ (symplO S T x y) = 1) :
    x ∈ (latO S T LS LT fun _ => True) ⊓ half S T a :=
  AddSubgroup.mem_inf.2 ⟨(hdual x (ha.infPart_half hx)).2 fun u hu => by
    have := h _ (idem_smul_half ha.conj.idem hu)
    rwa [← symplO_smul, (mem_half S T).1 hx] at this, hx⟩

theorem IsOrthSum.exists_model {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {e : AE D} (he : IsOrthSum e) (hec : e * cA D e = 0)
    {f₀ : WO S T → ℂ} (hvac : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f₀) :
    ∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm := by
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  refine exists_placeModel ψ hec _ (fun u hu y hy => (hdual u (he.infPart_half hu.2)).1 hu.1 y hy.1)
    (he.mem_of_dual hdual) (fun y hy h => ?_) (fun k hk => ?_) one_ne_zero f₀
    (he.heisO_eq (by rw [mul_comm, hec]) hvac) (he.conj.heisO_eq (by rw [cA_cA, hec]) hvac)
  · refine he.conj.mem_of_dual hdual y hy fun u hu => ?_
    rw [cA_cA] at hu
    rw [symplO_skew, AddChar.map_neg_eq_inv, h u hu, inv_one]
  · obtain ⟨R, hR, h⟩ := hfin k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, idem_smul_half he.idem hu, ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]

theorem placeModelExistsSum : ∀ D : D7, PlaceModelExistsSum D := by
  intro D ψ hψ S T ΛS ΛT hS hT P e he f₀ _ hvac
  have h := isOrthSum_of_isIdemSum he
  exact ⟨h.exists_model hψ hS hT he.2 hvac,
    h.conj.exists_model hψ hS hT (by rw [cA_cA, mul_comm, he.2]) hvac⟩

end GlobalTheory.PlaceModelSum

end
