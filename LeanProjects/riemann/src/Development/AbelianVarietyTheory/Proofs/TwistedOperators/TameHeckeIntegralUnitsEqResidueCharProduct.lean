import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameOnOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqProdLocalComponentsApproximating
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIdeleExistsLocalApprox

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TameProd

theorem val_lt_one_of_resS_eq_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {K Γ : Type} [CommRing K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    (P : Pl E) (g : Formalism.L2.Herm.intAf F E →+* K) (h1 : ∀ s, v (g s) ≤ 1)
    (h2 : ∀ a ∈ P.asIdeal, v (g (oToS F E a)) < 1) (s : Formalism.L2.Herm.intAf F E) (hs : resS F P s = 0) :
    v (g s) < 1 := by
  have hm : s ∈ idS F P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact (map_eq_zero_iff _ (RingEquiv.ofBijective (cmpS F P.asIdeal)
      (cmpS_bij (F := F) P.asIdeal P.ne_bot)).symm.injective).1 hs
  refine Submodule.span_induction (p := fun s _ => v (g s) < 1) ?_ ?_ ?_ ?_ hm
  · rintro _ ⟨a, ha, rfl⟩
    exact h2 a ha
  · rw [map_zero, map_zero]
    exact zero_lt_one
  · intro x y _ _ hx hy
    rw [map_add]
    exact v.map_add_lt hx hy
  · intro c x _ hx
    rw [smul_eq_mul, map_mul, map_mul]
    exact (mul_le_of_le_one_left' (h1 c)).trans_lt hx

theorem val_sub_lt_one {D : D7} {K Γ : Type} [CommRing K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    (P : Pl D.host.E) (G : Af D.host.F ⊗[D.host.F] D.host.E →+* K) (h1 : ∀ y ∈ intAE D, v (G y) ≤ 1)
    (h2 : ∀ a ∈ P.asIdeal, v (G ((1 : Af D.host.F) ⊗ₜ[D.host.F] (a : D.host.E))) < 1) (w : AE D)
    (hw : toEAf D w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (a : 𝓞 D.host.E)
    (h : resS D.host.F P ⟨toEAf D w, hw⟩ = Ideal.Quotient.mk _ a) :
    v (G (finPart D w) - G ((1 : Af D.host.F) ⊗ₜ[D.host.F] (a : D.host.E))) < 1 := by
  let c := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E)
  let g : Formalism.L2.Herm.intAf D.host.F D.host.E →+* K :=
    (G.comp c.symm.toRingEquiv.toRingHom).comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype
  have hg : ∀ s, g s = G (c.symm s.1) := fun _ => rfl
  have hgo : ∀ b : 𝓞 D.host.E, g (oToS D.host.F D.host.E b) =
      G ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) := fun _ => rfl
  have key := val_lt_one_of_resS_eq_zero v P g
    (fun s => h1 _ ((GlobalTheory.HostAdeleIso.mem_intAE_iff_comm D _).2 (by
      have : c (c.symm s.1) = s.1 := c.apply_symm_apply _
      exact this.symm ▸ s.2)))
    (fun b hb => by rw [hgo]; exact h2 b hb) (⟨toEAf D w, hw⟩ - oToS D.host.F D.host.E a)
    (by rw [RingHom.map_sub, h, resS_oToS, sub_self])
  rw [RingHom.map_sub, hgo, hg] at key
  have e : c.symm (toEAf D w) = finPart D w := c.symm_apply_apply _
  rwa [e] at key

theorem resS_idem_eq_zero {D : D7} {e : AE D} {P Q : Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt e P) (hQ : P ≠ Q)
    (h : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) : resS D.host.F Q ⟨toEAf D e, h⟩ = 0 := by
  have hnle : ¬ Q.asIdeal ≤ P.asIdeal := fun hle =>
    hQ (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top hle)).symm
  obtain ⟨x, hxQ, hxP⟩ := Set.not_subset.1 hnle
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hxP P.asIdeal.zero_mem
  have hx0' : (x : D.host.E) ≠ 0 := fun h => hx0 (RingOfIntegers.coe_eq_zero_iff.1 h)
  have hi : finPart D (e * incA D ((x : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra hn
    exact hxP ((he.2 x hx0).2 hn)
  have e1 : (⟨toEAf D e, h⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) =
      ⟨_, GlobalTheory.IdemRes.toEAf_mem_of_finPart hi⟩ * oToS D.host.F D.host.E x := by
    apply Subtype.ext
    change toEAf D e = toEAf D (e * incA D ((x : D.host.E)⁻¹)) * toEAf D (incA D (x : D.host.E))
    rw [← RingHom.map_mul, mul_assoc, ← RingHom.map_mul, inv_mul_cancel₀ hx0', RingHom.map_one, mul_one]
  rw [e1, RingHom.map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hxQ, mul_zero]

theorem map_sum_ringHom {A B ι : Type} [Semiring A] [Semiring B] (f : A →+* B) (s : Finset ι) (g : ι → A) :
    f (∑ i ∈ s, g i) = ∑ i ∈ s, f (g i) := map_sum f g s

theorem resS_idemSum {D : D7} {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) :
    ∃ h : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ∀ Q ∈ P, resS D.host.F Q ⟨toEAf D e, h⟩ = 1 := by
  classical
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  choose hi hr using fun Q : P => GlobalTheory.IdemRes.resS_idem_eq_one D (es Q) Q (hes Q Q.2)
  let t : P → Formalism.L2.Herm.intAf D.host.F D.host.E := fun Q => ⟨toEAf D (es Q), hi Q⟩
  have ht : toEAf D (∑ PP ∈ P, es PP) = ((∑ Q, t Q : Formalism.L2.Herm.intAf D.host.F D.host.E) : Datum.EAf D) := by
    rw [← Finset.sum_coe_sort P]
    refine (map_sum_ringHom (toEAf D) _ _).trans ?_
    exact (map_sum (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype t Finset.univ).symm
  refine ⟨ht ▸ (∑ Q, t Q).2, fun Q hQ => ?_⟩
  have e1 : (⟨toEAf D (∑ PP ∈ P, es PP), ht ▸ (∑ Q, t Q).2⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ∑ Q, t Q :=
    Subtype.ext ht
  rw [e1, map_sum, Finset.sum_eq_single (⟨Q, hQ⟩ : P)]
  · exact hr ⟨Q, hQ⟩
  · intro R _ hR
    exact resS_idem_eq_zero (hes R R.2) (fun h => hR (Subtype.ext h)) _
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem le_exp_of_lt_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1 : ℤ) := by
  by_cases h0 : x = 0
  · rw [h0]
    exact zero_le
  · rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    omega

theorem loc_eq_of_tame {L : Type} [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (Q : HeightOneSpectrum (𝓞 L))
    (ht : χ.TameAt Q) (y z : (Q.adicCompletion L)ˣ) (hz : Valued.v (z : Q.adicCompletion L) = 1)
    (h : Valued.v ((y : Q.adicCompletion L) - z) < 1) : χ.loc Q y = χ.loc Q z := by
  have hy : Valued.v (y : Q.adicCompletion L) = 1 := by
    rw [← hz]
    exact Valuation.map_eq_of_sub_lt _ (hz ▸ h)
  have h1 : χ.loc Q (y * z⁻¹) = 1 := by
    refine ht _ ?_ (le_exp_of_lt_one ?_)
    · show Valued.v ((y * z⁻¹ : (Q.adicCompletion L)ˣ) : Q.adicCompletion L) = 1
      rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hy, hz, inv_one, mul_one]
    · have : ((y * z⁻¹ : (Q.adicCompletion L)ˣ) : Q.adicCompletion L) - 1 =
          ((y : Q.adicCompletion L) - z) * (z : Q.adicCompletion L)⁻¹ := by
        rw [Units.val_mul, Units.val_inv_eq_inv_val, sub_mul, mul_inv_cancel₀ z.ne_zero]
      rw [this, map_mul, map_inv₀, hz, inv_one, mul_one]
      exact h
  rwa [map_mul, map_inv, mul_inv_eq_one] at h1

theorem tameOn_of_tame : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (e : AE D) (P : Finset (Pl D.host.E)) (cR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), ChrEq c χ → (∀ PP, χ.TameAt PP) → IsIdemSum e P → (∀ PP, PP ∉ P → (¬ ∃ PP' ∈ P, IsConjPl PP' PP) → χ.UnrAt PP) → (∀ PP ∈ P, IsRes χ PP (cR PP)) → TameOn c e P cR := by
  classical
  intro D c χ e P cR hc ht he hunr hres x hx1 hx2 hx3 hxe u hu
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2
    (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc
  let G : ∀ Q : Pl D.host.E, Af D.host.F ⊗[D.host.F] D.host.E →+* Q.adicCompletion D.host.E :=
    fun Q => (GlobalTheory.CharLocProd.evalAt Q).comp ι.toRingHom
  have hG : ∀ Q y, G Q y = ι y Q := fun _ _ => rfl
  have hG1 : ∀ (Q : Pl D.host.E) (a : D.host.E), G Q ((1 : Af D.host.F) ⊗ₜ[D.host.F] a) = algebraMap D.host.E _ a :=
    fun Q a => (congrArg (GlobalTheory.CharLocProd.evalAt Q) (h1 a)).trans (GlobalTheory.CharLocProd.evalAt_algebraMap Q a)
  have hGint : ∀ Q, ∀ y ∈ intAE D, Valued.v (G Q y) ≤ 1 := fun Q y hy => (h2 y).1 hy Q
  have hGlt : ∀ (Q : Pl D.host.E), ∀ a ∈ Q.asIdeal,
      Valued.v (G Q ((1 : Af D.host.F) ⊗ₜ[D.host.F] (a : D.host.E))) < 1 := by
    intro Q a ha
    rw [hG1, GlobalTheory.CharLocProd.val_algebraMap]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.host.E) Q a).2 ha
  have hv : ∀ Q, Valued.v (G Q (finPart D (x : AE D))) = 1 := by
    intro Q
    have a := hGint Q _ (GlobalTheory.PlaceDatum.finPart_mem_of_toEAf hx2)
    have b := hGint Q _ (GlobalTheory.PlaceDatum.finPart_mem_of_toEAf hx3)
    have e' : Valued.v (G Q (finPart D (x : AE D))) * Valued.v (G Q (finPart D ((x⁻¹ : (AE D)ˣ) : AE D))) = 1 := by
      rw [← map_mul, ← RingHom.map_mul, ← RingHom.map_mul, Units.mul_inv, RingHom.map_one, RingHom.map_one, map_one]
    refine le_antisymm a ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := e'.symm
      _ ≤ Valued.v (G Q (finPart D (x : AE D))) * 1 := mul_le_mul_right b _
      _ = _ := mul_one _
  choose k hk using fun Q : Pl D.host.E => GlobalTheory.adicCompletion_exists_unit_approx D.host.E N hN Q
    (G Q (finPart D (x : AE D))) (fun h => by
      have := hv Q
      rw [h, map_zero] at this
      exact zero_ne_one this)
  have hkc : ∀ Q, Valued.v (G Q (finPart D (x : AE D)) - algebraMap D.host.E _ (k Q : D.host.E)) < 1 := by
    intro Q
    have b := (hk Q).2.2
    rw [← (hk Q).1, hv, mul_one] at b
    refine b.trans_lt ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hloc : ∀ (Q : Pl D.host.E) (z : D.host.Eˣ), Q.valuation D.host.E (z : D.host.E) = 1 →
      Valued.v (G Q (finPart D (x : AE D)) - algebraMap D.host.E _ (z : D.host.E)) < 1 →
      χ.locK Q (k Q) = χ.locK Q z := by
    intro Q z hz h
    refine loc_eq_of_tame χ Q (ht Q) _ _ ((GlobalTheory.CharLocProd.val_algebraMap Q _).trans hz) ?_
    have e4 : ((Formalism.L2.Host.atFin Q (k Q) : (Q.adicCompletion D.host.E)ˣ) : Q.adicCompletion D.host.E) -
        (Formalism.L2.Host.atFin Q z : (Q.adicCompletion D.host.E)ˣ) =
        (G Q (finPart D (x : AE D)) - algebraMap D.host.E _ (z : D.host.E)) -
          (G Q (finPart D (x : AE D)) - algebraMap D.host.E _ (k Q : D.host.E)) := by
      show algebraMap D.host.E _ (k Q : D.host.E) - algebraMap D.host.E _ (z : D.host.E) = _
      ring
    rw [e4]
    exact Valuation.map_sub_lt _ h (hkc Q)
  have hfin : {Q : Pl D.host.E | Q.asIdeal ∣ Ideal.span {(N : 𝓞 D.host.E)}}.Finite :=
    Ideal.finite_factors (by simpa [Ideal.span_singleton_eq_bot] using hN.ne')
  have key := hprod x hx1 (P ∪ hfin.toFinset) k (fun Q _ => ⟨(hk Q).1, (hk Q).2.1⟩) (fun Q hQ => ⟨hv Q, fun h =>
    hQ (Finset.mem_union_right _ (hfin.mem_toFinset.2 (Ideal.dvd_span_singleton.2 h)))⟩)
  obtain ⟨hei, her⟩ := resS_idemSum he
  rw [key]
  refine (Finset.prod_subset Finset.subset_union_left fun Q _ hQ => ?_).symm.trans
    (Finset.prod_congr rfl fun Q hQ => ?_)
  · rw [Units.val_eq_one]
    by_cases hcj : ∃ PP' ∈ P, IsConjPl PP' Q
    · obtain ⟨R, hR, hRQ⟩ := hcj
      have h5 := val_sub_lt_one Valued.v R ((G Q).comp (sigR (Af D.host.F) D.sp.cm.sig))
        (fun y hy => hGint Q _ (GlobalTheory.PlaceIdem.sig_mem D hy))
        (fun a ha => by
          obtain ⟨b, hb, hab⟩ := hRQ a ha
          have := hGlt Q b hb
          rw [hab] at this
          exact this) e hei 1 (by rw [her R hR, RingHom.map_one])
      have h6 : ((1 : Af D.host.F) ⊗ₜ[D.host.F] ((1 : 𝓞 D.host.E) : D.host.E)) = 1 := rfl
      rw [h6, RingHom.map_one, RingHom.comp_apply, ← GlobalTheory.PlaceIdem.finPart_cA] at h5
      have h7 : G Q (finPart D (cA D e)) ≠ 0 := by
        intro h
        rw [h, zero_sub, Valuation.map_neg, map_one] at h5
        exact lt_irrefl _ h5
      have h8 : G Q (finPart D (x : AE D)) = 1 := by
        refine mul_left_cancel₀ h7 ?_
        rw [← RingHom.map_mul, ← RingHom.map_mul, hxe, mul_one]
      rw [hloc Q 1 (by rw [Units.val_one, map_one]) (by
        rw [h8, Units.val_one, map_one, sub_self, map_zero]
        exact zero_lt_one), map_one]
    · exact hunr Q hQ hcj _ ((GlobalTheory.CharLocProd.val_algebraMap Q _).trans ((hk Q).1.symm.trans (hv Q)))
  · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u Q : kP Q)
    have haQ : a ∉ Q.asIdeal := by
      intro h
      have := Q.isPrime
      exact (u Q).ne_zero (ha ▸ Ideal.Quotient.eq_zero_iff_mem.2 h)
    have ha0 : (a : D.host.E) ≠ 0 := fun h => haQ (RingOfIntegers.coe_eq_zero_iff.1 h ▸ Q.asIdeal.zero_mem)
    have h5 := val_sub_lt_one Valued.v Q (G Q) (hGint Q) (hGlt Q) x hx2 a ((hu Q hQ).symm.trans ha.symm)
    rw [hG1] at h5
    rw [hres Q hQ a (Units.mk0 _ ha0) (u Q) rfl ha.symm, hloc Q (Units.mk0 _ ha0)
      ((HeightOneSpectrum.valuation_eq_one_iff_notMem (K := D.host.E) Q (r := a)).2 haQ) h5]

end GlobalTheory.TameProd

end
