import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDetInt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqProdLocalComponentsApproximating
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIdeleExistsLocalApprox
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TameSplitChar

open GlobalTheory.CharLocProd

theorem locK_eq_of_congr {L : Type} [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L)
    (P : HeightOneSpectrum (𝓞 L)) (ht : χ.TameAt P) (k b : Lˣ) (hb : P.valuation L (b : L) = 1)
    (h : Valued.v (algebraMap L (P.adicCompletion L) (k : L) - algebraMap L (P.adicCompletion L) (b : L)) ≤
      WithZero.exp (-1 : ℤ)) : χ.locK P k = χ.locK P b := by
  have hlt : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have e : ((Formalism.L2.Host.atFin P (k * b⁻¹) : (P.adicCompletion L)ˣ) : P.adicCompletion L) - 1 =
      (algebraMap L (P.adicCompletion L) (k : L) - algebraMap L (P.adicCompletion L) (b : L)) *
        algebraMap L (P.adicCompletion L) ((b : L)⁻¹) := by
    show algebraMap L (P.adicCompletion L) ((k * b⁻¹ : Lˣ) : L) - 1 = _
    rw [sub_mul, ← map_mul, ← map_mul, mul_inv_cancel₀ b.ne_zero, map_one, Units.val_mul, Units.val_inv_eq_inv_val]
  have h1 : Valued.v (((Formalism.L2.Host.atFin P (k * b⁻¹) : (P.adicCompletion L)ˣ) : P.adicCompletion L) - 1) ≤
      WithZero.exp (-1 : ℤ) := by
    rw [e, map_mul, val_algebraMap, map_inv₀, hb, inv_one, mul_one]
    exact h
  have h2 : χ.locK P (k * b⁻¹) = 1 := by
    refine ht _ ?_ h1
    show Valued.v _ = 1
    rw [← map_one (Valued.v : Valuation (P.adicCompletion L) _)]
    refine Valuation.map_eq_of_sub_lt _ ?_
    rw [map_one]
    exact h1.trans_lt hlt
  rwa [map_mul, map_inv, mul_inv_eq_one] at h2

theorem idem_apply {L : Type} [Field L] [NumberField L] (ε : FiniteAdeleRing (𝓞 L) L) (hε : ε * ε = ε)
    (Q : HeightOneSpectrum (𝓞 L))
    (h : ∀ x : 𝓞 L, x ≠ 0 → (x ∈ Q.asIdeal ↔
      ¬ ∀ R, Valued.v (CharLocProd.evalAt R (ε * algebraMap L (FiniteAdeleRing (𝓞 L) L) ((x : L)⁻¹))) ≤ 1)) :
    CharLocProd.evalAt Q ε = 1 ∧ ∀ R, R ≠ Q → CharLocProd.evalAt R ε = 0 := by
  have h01 : ∀ R, CharLocProd.evalAt R ε ≠ 0 → CharLocProd.evalAt R ε = 1 := fun R hR =>
    mul_left_cancel₀ hR (by rw [← map_mul, hε, mul_one])
  have h0 : ∀ R, R ≠ Q → CharLocProd.evalAt R ε = 0 := by
    intro R hR
    by_contra hne
    have hnle : ¬ R.asIdeal ≤ Q.asIdeal := fun hle =>
      hR (HeightOneSpectrum.ext (R.isMaximal.eq_of_le Q.isPrime.ne_top hle))
    obtain ⟨y, hyR, hyQ⟩ := Set.not_subset.1 hnle
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact hyQ Q.asIdeal.zero_mem
    have h2 := not_not.1 (mt (h y hy0).2 hyQ) R
    rw [map_mul, h01 R hne, one_mul] at h2
    exact (GlobalTheory.PlaceIdem.val_inv_le_one R hy0).1 h2 hyR
  refine ⟨h01 Q fun hQ => ?_, h0⟩
  obtain ⟨y, hyQ, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot Q.ne_bot
  refine (h y hy0).1 hyQ fun R => ?_
  have : CharLocProd.evalAt R ε = 0 := by
    by_cases hR : R = Q
    · rw [hR, hQ]
    · exact h0 R hR
  rw [map_mul, this, zero_mul, map_zero]
  exact zero_le

theorem val_sub_le_of_resS {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : Pl E) (φ : Formalism.L2.Herm.intAf F E →+* P.adicCompletion E) (h1 : ∀ z, Valued.v (φ z) ≤ 1)
    (h2 : ∀ t : 𝓞 E, φ (oToS F E t) = algebraMap E _ (t : E)) (a : Formalism.L2.Herm.intAf F E) (b : 𝓞 E)
    (hab : resS F P a = Ideal.Quotient.mk P.asIdeal b) :
    Valued.v (φ a - algebraMap E _ (b : E)) ≤ WithZero.exp (-1 : ℤ) := by
  have h0 : resS F P (a - oToS F E b) = 0 := by rw [map_sub, resS_oToS, hab, sub_self]
  have hm : a - oToS F E b ∈ idS F P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact (map_eq_zero_iff _ (RingEquiv.ofBijective (cmpS F P.asIdeal)
      (cmpS_bij (F := F) P.asIdeal P.ne_bot)).symm.injective).1 h0
  rw [← h2, ← map_sub]
  generalize a - oToS F E b = z at hm
  induction hm using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨t, ht, rfl⟩ := hy
    rw [h2, val_algebraMap]
    have := (P.intValuation_le_pow_iff_mem t 1).2 (by simpa using ht)
    rw [show P.valuation E (t : E) = P.intValuation t from HeightOneSpectrum.valuation_of_algebraMap P t]
    simpa using this
  | zero => rw [map_zero, map_zero]; exact zero_le
  | add x y _ _ hx hy => rw [map_add]; exact Valuation.map_add_le _ hx hy
  | smul r x _ hx =>
    rw [smul_eq_mul, map_mul, map_mul]
    exact (mul_le_mul' (h1 r) hx).trans (one_mul _).le

theorem map_mix {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (e a : A) :
    f (e * a + (1 - e)) = f e * f a + (1 - f e) := by
  rw [map_add, map_mul, map_sub, map_one]

theorem map_finset_sum {A B ι : Type} [CommRing A] [CommRing B] (f : A →+* B) (s : Finset ι) (g : ι → A) :
    f (∑ i ∈ s, g i) = ∑ i ∈ s, f (g i) := map_sum f g s

set_option maxHeartbeats 800000 in

theorem char_eq_prod_res : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (P : Finset (Pl D.host.E)) (e : AE D) (ρ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), ChrEq c χ → IsIdemSum e P → (∀ PP ∈ P, χ.TameAt PP ∧ IsRes χ PP (ρ PP)) → ∀ (x : (AE D)ˣ) (a : AE D) (a' : Formalism.L2.Herm.intAf D.host.F D.host.E) (u : ∀ PP : Pl D.host.E, (kP PP)ˣ), (x : AE D) = e * a + (1 - e) → (a' : Lev.EAf D) = toEAf D a → (∀ PP ∈ P, (u PP : kP PP) = resS D.host.F PP a') → ((c x : Circle) : ℂ) = ∏ PP ∈ P, ((ρ PP (u PP) : ℂˣ) : ℂ) := by
  classical
  intro D c χ P e ρ hc he ht x a a' u hx ha hu
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2
    (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc
  have hinf : infPart D (x : AE D) = 1 := by
    rw [hx, map_mix, GlobalTheory.PlaceVec.idemSum_infPart he, zero_mul, zero_add, sub_zero]
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := he
  obtain ⟨ev, hev⟩ : ∃ ev : ∀ R : Pl D.host.E, AE D →+* R.adicCompletion D.host.E,
      ∀ R z, ev R z = CharLocProd.evalAt R (ι (finPart D z)) :=
    ⟨fun R => (CharLocProd.evalAt R).comp ((ι : _ →+* _).comp (finPart D)), fun _ _ => rfl⟩
  have hidem : ∀ Q ∈ P, ev Q (es Q) = 1 ∧ ∀ R, R ≠ Q → ev R (es Q) = 0 := by
    intro Q hQ
    simp only [hev]
    refine idem_apply _ (by rw [← RingEquiv.map_mul, ← RingHom.map_mul, (hes Q hQ).1.1]) Q fun y hy => ?_
    refine ((hes Q hQ).2 y hy).trans (not_congr ((h2 _).trans ?_))
    rw [RingHom.map_mul, RingEquiv.map_mul, show finPart D (incA D ((y : D.host.E)⁻¹)) =
      (1 : GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] ((y : D.host.E)⁻¹) from rfl, h1]
    rfl
  have hxP : ∀ R ∈ P, ev R x = ev R a := by
    intro R hR
    have : ev R e = 1 := by
      rw [hsum, map_finset_sum, Finset.sum_eq_single R, (hidem R hR).1]
      · intro Q hQ hne; exact (hidem Q hQ).2 R hne.symm
      · intro h; exact absurd hR h
    rw [hx, map_mix, this, one_mul, sub_self, add_zero]
  have hxP' : ∀ R, R ∉ P → ev R x = 1 := by
    intro R hR
    have : ev R e = 0 := by
      rw [hsum, map_finset_sum]
      exact Finset.sum_eq_zero fun Q hQ => (hidem Q hQ).2 R fun h => hR (h ▸ hQ)
    rw [hx, map_mix, this, zero_mul, zero_add, sub_zero]
  have hx0 : ∀ R, ev R x ≠ 0 := fun R => (RingHom.isUnit_map (ev R) x.isUnit).ne_zero
  choose k hk using fun R => GlobalTheory.adicCompletion_exists_unit_approx D.host.E N hN R _ (hx0 R)
  have hfin : {R : Pl D.host.E | R.asIdeal ∣ Ideal.span {(N : 𝓞 D.host.E)}}.Finite :=
    Ideal.finite_factors (by simpa [Ideal.span_singleton_eq_bot] using hN.ne')
  have key := hprod x hinf (P ∪ hfin.toFinset) (fun R => if R ∈ P then k R else 1) ?_ ?_
  rotate_left
  · intro R _
    change Valued.v (CharLocProd.evalAt R (ι (finPart D x))) = _ ∧
      Valued.v (CharLocProd.evalAt R (ι (finPart D x)) - _) ≤ _
    rw [← hev]
    by_cases hR : R ∈ P
    · simp only [if_pos hR]
      exact ⟨(hk R).1, (hk R).2.1⟩
    · simp only [if_neg hR]
      rw [hxP' R hR, Units.val_one, map_one, map_one, map_one, sub_self, map_zero]
      exact ⟨rfl, zero_le⟩
  · intro R hR
    rw [Finset.mem_union, not_or] at hR
    change Valued.v (CharLocProd.evalAt R (ι (finPart D x))) = _ ∧ _
    rw [← hev, hxP' R hR.1, map_one]
    exact ⟨rfl, fun h => hR.2 (hfin.mem_toFinset.2 (Ideal.dvd_span_singleton.2 h))⟩
  rw [key, ← Finset.prod_subset Finset.subset_union_left
    (fun R _ hR => by rw [if_neg hR, map_one, Units.val_one])]
  refine Finset.prod_congr rfl fun R hR => ?_
  rw [if_pos hR]
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (u R : kP R)
  have := R.isPrime
  have hbR : b ∉ R.asIdeal := fun h => (u R).ne_zero (hb ▸ Ideal.Quotient.eq_zero_iff_mem.2 h)
  have hb0 : (b : D.host.E) ≠ 0 := fun h => hbR (RingOfIntegers.coe_eq_zero_iff.1 h ▸ R.asIdeal.zero_mem)
  have hbv : R.valuation D.host.E (b : D.host.E) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := D.host.E) R (r := b)).2 hbR
  let cm := (Algebra.TensorProduct.comm D.host.F (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E)
  let φ : Formalism.L2.Herm.intAf D.host.F D.host.E →+* R.adicCompletion D.host.E :=
    (CharLocProd.evalAt R).comp ((ι : _ →+* _).comp (cm.symm.toRingEquiv.toRingHom.comp
      (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype))
  have hφ : ∀ z, φ z = CharLocProd.evalAt R (ι (cm.symm (z : Lev.EAf D))) := fun _ => rfl
  have hv := val_sub_le_of_resS R φ (fun z => (h2 _).1 ((GlobalTheory.HostAdeleIso.mem_intAE_iff_comm D _).2
      (by change cm (cm.symm (z : Lev.EAf D)) ∈ _; rw [AlgEquiv.apply_symm_apply]; exact z.2)) R)
    (fun t => by
      rw [hφ, show cm.symm ((oToS D.host.F D.host.E t : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) =
        (1 : GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (t : D.host.E) from rfl, h1]
      rfl) a' b ((hu R hR).symm.trans hb.symm)
  have hφa : φ a' = ev R x := by
    rw [hxP R hR, hev, hφ, ha]
    exact congrArg (fun z => CharLocProd.evalAt R (ι z)) (cm.symm_apply_apply (finPart D a))
  rw [hφa] at hv
  have hlt : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hxv : Valued.v (ev R x) = 1 := by
    rw [← hbv, ← val_algebraMap]
    refine Valuation.map_eq_of_sub_lt _ ?_
    rw [val_algebraMap, hbv]
    exact hv.trans_lt hlt
  have hk3 := (hk R).2.2
  rw [← (hk R).1, hxv, mul_one] at hk3
  rw [(ht R hR).2 b (Units.mk0 _ hb0) (u R) rfl hb.symm,
    locK_eq_of_congr χ R (ht R hR).1 (k R) (Units.mk0 _ hb0) hbv ?_]
  have e4 : algebraMap D.host.E (R.adicCompletion D.host.E) (k R : D.host.E) -
      algebraMap D.host.E (R.adicCompletion D.host.E) (b : D.host.E) =
      (ev R x - algebraMap D.host.E _ (b : D.host.E)) - (ev R x - algebraMap D.host.E _ (k R : D.host.E)) := by
    ring
  rw [Units.val_mk0, e4]
  exact Valuation.map_sub_le _ hv hk3

end GlobalTheory.TameSplitChar
