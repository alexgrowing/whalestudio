import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceIdem

section General

variable {E : Type} [Field E] [NumberField E]

theorem single_same (v : HeightOneSpectrum (𝓞 E)) : (singleV E v 1) v = 1 := by
  classical
  exact RestrictedProduct.single_eq_same
    (fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletionIntegers E) v 1

theorem single_ne {v v' : HeightOneSpectrum (𝓞 E)} (h : v' ≠ v) : (singleV E v 1) v' = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne
    (fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletionIntegers E) 1 h

theorem adele_ext {a b : Af E} (h : ∀ v, a v = b v) : a = b :=
  RestrictedProduct.ext _ _ h

theorem mul_ap (a b : Af E) (v : HeightOneSpectrum (𝓞 E)) : (a * b) v = a v * b v := rfl

theorem add_ap (a b : Af E) (v : HeightOneSpectrum (𝓞 E)) : (a + b) v = a v + b v := rfl

theorem zero_ap (v : HeightOneSpectrum (𝓞 E)) : (0 : Af E) v = 0 := rfl

theorem val_inv_le_one (P : HeightOneSpectrum (𝓞 E)) {x : 𝓞 E} (hx : x ≠ 0) :
    Valued.v ((algebraMap E (Af E) ((x : E)⁻¹)) P) ≤ 1 ↔ x ∉ P.asIdeal := by
  have h2 : Valued.v ((algebraMap E (Af E) ((x : E)⁻¹)) P) = P.valuation E ((x : E)⁻¹) :=
    P.valuedAdicCompletion_eq_valuation' _
  have h0 : P.valuation E (x : E) ≠ 0 := by
    rw [Ne, map_eq_zero]
    exact fun h => hx (RingOfIntegers.ext h)
  rw [h2, map_inv₀, inv_le_one₀ (zero_lt_iff.2 h0), ← not_lt]
  exact not_congr (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) P x)

theorem single_mul_inv (P : HeightOneSpectrum (𝓞 E)) {x : 𝓞 E} (hx : x ≠ 0) :
    (∀ Q, Valued.v ((singleV E P 1 * algebraMap E (Af E) ((x : E)⁻¹)) Q) ≤ 1) ↔ x ∉ P.asIdeal := by
  rw [← val_inv_le_one P hx]
  constructor
  · intro h
    have := h P
    rwa [mul_ap, single_same, one_mul] at this
  · intro h Q
    by_cases hQ : Q = P
    · subst hQ
      rwa [mul_ap, single_same, one_mul]
    · rw [mul_ap, single_ne hQ, zero_mul, map_zero]
      exact zero_le

theorem eq_zero_of_val (P : HeightOneSpectrum (𝓞 E)) (y : P.adicCompletion E)
    (h : ∀ n : ℕ, Valued.v y ≤ WithZero.exp (-(n : ℤ))) : y = 0 := by
  by_contra hy
  have h0 : Valued.v y ≠ 0 := by rwa [Ne, map_eq_zero]
  have h1 := h ((WithZero.log (Valued.v y)).natAbs + 1)
  rw [← WithZero.exp_log h0, WithZero.exp_le_exp, WithZero.log_exp] at h1
  omega

variable {F : Type} [Field F] [NumberField F] [Algebra F E]

theorem single_dichotomy (σ : E ≃ₐ[F] E) (hr : Module.finrank F E = 2) (hσ : σ ≠ 1) (hσσ : ∀ x, σ (σ x) = x)
    (c : Af E →+* Af E) (hcc : ∀ a, c (c a) = a)
    (hc : ∀ x, c (algebraMap E (Af E) x) = algebraMap E (Af E) (σ x))
    (hint : ∀ a : Af E, (∀ Q, Valued.v (a Q) ≤ 1) → ∀ Q, Valued.v (c a Q) ≤ 1)
    (P : HeightOneSpectrum (𝓞 E)) (η : Af E) (hη : c η = η)
    (h1 : ∀ Q : HeightOneSpectrum (𝓞 E), Q.under (𝓞 F) = P.under (𝓞 F) → η Q = 1)
    (h0 : ∀ Q : HeightOneSpectrum (𝓞 E), Q.under (𝓞 F) ≠ P.under (𝓞 F) → η Q = 0) :
    (singleV E P 1 * c (singleV E P 1) = 0 ∧ singleV E P 1 + c (singleV E P 1) = η) ∨ singleV E P 1 = η := by
  set e := singleV E P 1 with he
  by_cases h : ∃ Q, Q ≠ P ∧ Q.under (𝓞 F) = P.under (𝓞 F)
  swap
  · right
    refine adele_ext fun Q => ?_
    by_cases hQ : Q = P
    · subst hQ
      rw [single_same, h1 _ rfl]
    · rw [single_ne hQ, h0 Q fun hu => h ⟨Q, hQ, hu⟩]
  left
  obtain ⟨Q, hQP, hQ⟩ := h
  have hconj := ((GlobalTheory.Mem.Chr.under_eq_iff_conjPl σ hr hσ P Q).1 hQ).resolve_left hQP
  have hall : ∀ R : HeightOneSpectrum (𝓞 E), R ≠ P → R ≠ Q → η R = 0 := by
    intro R hRP hRQ
    refine h0 R fun hu => hRQ ?_
    exact (GlobalTheory.Mem.Chr.existsUnique_conjPl σ.toRingEquiv P).unique
      (((GlobalTheory.Mem.Chr.under_eq_iff_conjPl σ hr hσ P R).1 hu).resolve_left hRP) hconj
  have hee : e * e = e := adele_ext fun R => by
    by_cases hR : R = P
    · subst hR
      rw [mul_ap, single_same, one_mul]
    · rw [mul_ap, single_ne hR, zero_mul]
  have heη : e * η = e := adele_ext fun R => by
    by_cases hR : R = P
    · subst hR
      rw [mul_ap, h1 _ rfl, mul_one]
    · rw [mul_ap, single_ne hR, zero_mul]
  have hff : c e * c e = c e := by rw [← map_mul, hee]
  have hfη : c e * η = c e := by rw [← hη, ← map_mul, heη]
  have hfR : ∀ R : HeightOneSpectrum (𝓞 E), R ≠ P → R ≠ Q → c e R = 0 := by
    intro R hRP hRQ
    rw [← hfη, mul_ap, hall R hRP hRQ, mul_zero]
  have hf01 : ∀ R : HeightOneSpectrum (𝓞 E), c e R ≠ 0 → c e R = 1 := by
    intro R hR
    have : c e R * c e R = c e R * 1 := by rw [← mul_ap, hff, mul_one]
    exact mul_left_cancel₀ hR this
  have hfP : c e P = 0 := by
    by_contra hP
    have hnle : ¬ Q.asIdeal ≤ P.asIdeal := fun hle =>
      hQP (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top hle))
    obtain ⟨y, hyQ, hyP⟩ := Set.not_subset.1 hnle
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact hyP P.asIdeal.zero_mem
    let x : 𝓞 E := RingOfIntegers.mapRingEquiv σ.toRingEquiv y
    have hxy : (x : E) = σ (y : E) := rfl
    have hx0 : x ≠ 0 := by
      intro h
      exact hy0 ((map_eq_zero_iff _ (RingOfIntegers.mapRingEquiv σ.toRingEquiv).injective).1 h)
    have hxP : x ∈ P.asIdeal :=
      ((GlobalTheory.Mem.Chr.conjPl_iff_mem σ.toRingEquiv P Q).1 hconj x y (by rw [hxy]; exact (hσσ _).symm)).2 hyQ
    have := hint _ ((single_mul_inv P hy0).2 hyP) P
    rw [map_mul, hc, mul_ap, hf01 P hP, one_mul, map_inv₀, ← hxy, val_inv_le_one P hx0] at this
    exact this hxP
  have hfQ : c e Q = 1 := by
    refine hf01 Q fun hz => ?_
    have hf0 : c e = 0 := adele_ext fun R => by
      by_cases hRP : R = P
      · rw [hRP, hfP, zero_ap]
      · by_cases hRQ : R = Q
        · rw [hRQ, hz, zero_ap]
        · rw [hfR R hRP hRQ, zero_ap]
    have he0 : e = 0 := by rw [← hcc e, hf0, map_zero]
    have := single_same P
    rw [← he, he0, zero_ap] at this
    exact zero_ne_one this
  refine ⟨adele_ext fun R => ?_, adele_ext fun R => ?_⟩
  · by_cases hRP : R = P
    · rw [hRP, mul_ap, hfP, mul_zero, zero_ap]
    · rw [mul_ap, single_ne hRP, zero_mul, zero_ap]
  · by_cases hRP : R = P
    · rw [hRP, add_ap, hfP, single_same, add_zero, h1 P rfl]
    · by_cases hRQ : R = Q
      · rw [add_ap, single_ne hRP, hRQ, hfQ, zero_add, h1 Q hQ]
      · rw [add_ap, single_ne hRP, hfR R hRP hRQ, hall R hRP hRQ, add_zero]

end General

theorem parts_inj (D : D7) (x y : AE D) (h1 : infPart D x = infPart D y) (h2 : finPart D x = finPart D y) : x = y := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  exact e.injective (Prod.ext (((he x).1.trans h1).trans (he y).1.symm) (((he x).2.trans h2).trans (he y).2.symm))

theorem parts_surj (D : D7) (a : Ainf D.host.F ⊗[D.host.F] D.host.E) (b : Af D.host.F ⊗[D.host.F] D.host.E) :
    ∃ x : AE D, infPart D x = a ∧ finPart D x = b := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  refine ⟨e.symm (a, b), (he _).1.symm.trans ?_, (he _).2.symm.trans ?_⟩ <;> simp

theorem finPart_cA (D : D7) (z : AE D) : finPart D (cA D z) = sigR (Af D.host.F) D.sp.cm.sig (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add x y hx hy => simp only [RingHom.map_add, hx, hy]
  | tmul a x => rfl

theorem infPart_cA (D : D7) (z : AE D) : infPart D (cA D z) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add x y hx hy => simp only [RingHom.map_add, hx, hy]
  | tmul a x => rfl

theorem sig_sig (D : D7) (z : Af D.host.F ⊗[D.host.F] D.host.E) :
    sigR (Af D.host.F) D.sp.cm.sig (sigR (Af D.host.F) D.sp.cm.sig z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, hx, hy]
  | tmul a x =>
    change a ⊗ₜ[D.host.F] star (star x) = _
    rw [star_star]

theorem sig_mem (D : D7) {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) :
    sigR (Af D.host.F) D.sp.cm.sig z ∈ intAE D := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨a, ha, RingOfIntegers.mapRingHom (D.sp.cm.sig : D.host.E →+* D.host.E) x, rfl⟩
  | zero => rw [RingHom.map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [RingHom.map_add]; exact add_mem hx hy
  | neg x _ hx => rw [RingHom.map_neg]; exact neg_mem hx

set_option maxHeartbeats 1600000 in

theorem exists_isPlIdem : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → (∀ (a : Af D.host.F) (k : D.host.F) (P : HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ), Valued.v (a (P.under (𝓞 D.host.F)) - algebraMap D.host.F _ k) ≤ WithZero.exp (-(n : ℤ)) → Valued.v (ι (a ⊗ₜ[D.host.F] (1 : D.host.E)) P - algebraMap D.host.E _ (algebraMap D.host.F D.host.E k)) ≤ WithZero.exp (-(n : ℤ))) → (∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ e : AE D, IsPlIdem D e P ∧ infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0) := by
  intro D ι hι hint happ P
  let σ : D.host.E ≃ₐ[D.host.F] D.host.E := AlgEquiv.ofBijective D.sp.cm.sig (AlgHom.bijective _)
  have hσ : σ ≠ 1 := by
    intro h
    have h1 : Module.finrank D.host.F D.host.E = 1 := by
      refine (Algebra.finrank_eq_one_iff_bijective_algebraMap).2 ⟨(algebraMap D.host.F D.host.E).injective, fun a => ?_⟩
      exact (D.sp.cm.fixed a).1 (congrArg (fun f : D.host.E ≃ₐ[D.host.F] D.host.E => f a) h)
    have h2 := D.sp.cm.deg2
    omega
  let s := sigR (Af D.host.F) D.sp.cm.sig
  let c : Af D.host.E →+* Af D.host.E := (ι.toRingHom.comp s).comp ι.symm.toRingHom
  have hc : ∀ z, c (ι z) = ι (s z) := fun z => by
    change ι (s (ι.symm (ι z))) = _
    rw [ι.symm_apply_apply]
  let v := P.under (𝓞 D.host.F)
  let α : Af D.host.F := singleV D.host.F v 1
  have hd := single_dichotomy σ D.sp.cm.deg2 hσ (fun x => star_star x) c
    (fun a => by
      obtain ⟨z, rfl⟩ := ι.surjective a
      rw [hc, hc, sig_sig])
    (fun x => by
      rw [← hι, ← hι, hc]
      rfl)
    (fun a ha => by
      obtain ⟨z, rfl⟩ := ι.surjective a
      rw [hc]
      exact (hint _).1 (sig_mem D ((hint z).2 ha)))
    P (ι (α ⊗ₜ[D.host.F] (1 : D.host.E)))
    (by
      rw [hc]
      congr 1
      change α ⊗ₜ[D.host.F] D.sp.cm.sig 1 = _
      rw [map_one])
    (fun Q hQ => by
      refine sub_eq_zero.1 (eq_zero_of_val Q _ fun n => ?_)
      have := happ α 1 Q n (by
        rw [map_one, hQ, single_same, sub_self, map_zero]
        exact zero_le)
      rwa [map_one, map_one] at this)
    (fun Q hQ => by
      refine eq_zero_of_val Q _ fun n => ?_
      have := happ α 0 Q n (by
        rw [map_zero, single_ne hQ, sub_self, map_zero]
        exact zero_le)
      rwa [map_zero, map_zero, sub_zero] at this)
  obtain ⟨e, he1, he2⟩ := parts_surj D 0 (ι.symm (singleV D.host.E P 1))
  have he3 : ι (finPart D e) = singleV D.host.E P 1 := by rw [he2, ι.apply_symm_apply]
  have hε1 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 :=
    TensorProduct.zero_tmul _ _
  have hε2 : finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = α ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  refine ⟨e, ⟨?_, ⟨v, pairA D.host.F 0 α, ⟨α, rfl, single_same v, fun v' h => single_ne h⟩, ?_⟩, fun x hx => ?_⟩, he1,
    by rw [he3, single_same], fun P' h => by rw [he3, single_ne h]⟩
  · refine parts_inj D _ _ (by rw [RingHom.map_mul, he1, mul_zero]) (ι.injective ?_)
    rw [RingHom.map_mul, map_mul, he3]
    refine adele_ext fun R => ?_
    by_cases hR : R = P
    · rw [hR, mul_ap, single_same, one_mul]
    · rw [mul_ap, single_ne hR, zero_mul]
  · rcases hd with ⟨h1, h2⟩ | h
    · refine Or.inl ⟨parts_inj D _ _ ?_ (ι.injective ?_), parts_inj D _ _ ?_ (ι.injective ?_)⟩
      · rw [RingHom.map_mul, he1, zero_mul, RingHom.map_zero]
      · rw [RingHom.map_mul, map_mul, finPart_cA, ← hc, he3, h1, RingHom.map_zero, map_zero]
      · rw [RingHom.map_add, infPart_cA, he1, RingHom.map_zero, add_zero, hε1]
      · rw [RingHom.map_add, map_add, finPart_cA, ← hc, he3, h2, hε2]
    · exact Or.inr (parts_inj D _ _ (by rw [he1, hε1]) (ι.injective (by rw [he3, hε2, h])))
  · have h1 : finPart D (incA D ((x : D.host.E)⁻¹)) = (1 : Af D.host.F) ⊗ₜ[D.host.F] ((x : D.host.E)⁻¹) := rfl
    rw [hint, RingHom.map_mul, map_mul, he3, h1, hι, single_mul_inv P hx, not_not]

end GlobalTheory.PlaceIdem
