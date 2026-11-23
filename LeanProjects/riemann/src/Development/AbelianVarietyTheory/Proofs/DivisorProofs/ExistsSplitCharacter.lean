import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitDetChar

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem

section Alg

variable {R : Type} [CommRing R]

def cut (a : R) (ha : a * a = a) : Rˣ →* Rˣ where
  toFun u := ⟨a * u + (1 - a), a * (u⁻¹ : Rˣ) + (1 - a),
    by linear_combination ((u : R) * (u⁻¹ : Rˣ) - u - (u⁻¹ : Rˣ) + 1) * ha + a * u.mul_inv,
    by linear_combination ((u : R) * (u⁻¹ : Rˣ) - u - (u⁻¹ : Rˣ) + 1) * ha + a * u.mul_inv⟩
  map_one' := Units.ext (by simp)
  map_mul' u w := Units.ext (by
    show a * ((u : R) * w) + (1 - a) = (a * u + (1 - a)) * (a * w + (1 - a))
    linear_combination (-((u : R) * w) + u + w - 1) * ha)

theorem cut_val (a : R) (ha : a * a = a) (u : Rˣ) : (cut a ha u : R) = a * u + (1 - a) := rfl

theorem continuous_cut [TopologicalSpace R] [IsTopologicalRing R] (a : R) (ha : a * a = a) :
    Continuous (cut a ha) :=
  Units.continuous_iff.2 ⟨(continuous_const.mul Units.continuous_val).add continuous_const,
    (continuous_const.mul Units.continuous_coe_inv).add continuous_const⟩

theorem mul_det {n : ℕ} (a : R) (M : Matrix (Fin n) (Fin n) R) (h : ∀ i j, a * (M - 1) i j = 0) :
    a * M.det = a := by
  let I : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R R a)
  have hI : ∀ x, x ∈ I ↔ x * a = 0 := fun x => Iff.rfl
  have h1 : (Ideal.Quotient.mk I).mapMatrix M = (Ideal.Quotient.mk I).mapMatrix 1 := by
    ext i j
    exact Ideal.Quotient.eq.2 ((hI _).2 ((mul_comm _ _).trans (h i j)))
  have h2 : Ideal.Quotient.mk I M.det = Ideal.Quotient.mk I 1 := by
    rw [RingHom.map_det, h1, map_one, det_one, map_one]
  have h3 := (hI _).1 (Ideal.Quotient.eq.1 h2)
  linear_combination h3

end Alg

theorem eq_single {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) :
    algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) ε = pl D v := by
  obtain ⟨α, rfl, h3, h4⟩ := h
  have : α = singleV D.host.F v 1 := af_ext _ fun w => by
    by_cases hw : w = v
    · subst hw; rw [h3, evalV_singleV_same]
    · rw [h4 w hw, evalV_singleV_ne _ v _ hw]
  subst this
  rfl

set_option maxHeartbeats 1000000 in

theorem exists_glue (D : D7) (e : HeightOneSpectrum (𝓞 D.host.F) → Formalism.L2.Theta.AE D)
    (hee : ∀ v, e v * e v = e v) (hp : ∀ v, e v * pl D v = e v) :
    ∃ a : Formalism.L2.Theta.AE D, a * a = a ∧ infPart D a = 0 ∧ ∀ v, a * pl D v = e v := by
  obtain ⟨ι, -, -, happ⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have h1 : ∀ v (Q : HeightOneSpectrum (𝓞 D.host.E)), Q.under (𝓞 D.host.F) = v →
      ι (finPart D (pl D v)) Q = 1 := fun v Q hQ => by
    refine sub_eq_zero.1 (GlobalTheory.PlaceIdem.eq_zero_of_val Q _ fun n => ?_)
    have := happ (singleV D.host.F v 1) 1 Q n (by
      rw [map_one, hQ, GlobalTheory.PlaceIdem.single_same, sub_self, map_zero]
      exact zero_le)
    rwa [map_one, map_one] at this
  have h0 : ∀ v (Q : HeightOneSpectrum (𝓞 D.host.E)), Q.under (𝓞 D.host.F) ≠ v →
      ι (finPart D (pl D v)) Q = 0 := fun v Q hQ => by
    refine GlobalTheory.PlaceIdem.eq_zero_of_val Q _ fun n => ?_
    have := happ (singleV D.host.F v 1) 0 Q n (by
      rw [map_zero, GlobalTheory.PlaceIdem.single_ne hQ, sub_self, map_zero]
      exact zero_le)
    rwa [map_zero, map_zero, sub_zero] at this
  have hinf : ∀ v, infPart D (pl D v) = 0 := fun v => TensorProduct.zero_tmul _ _
  let f : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Q.adicCompletion D.host.E :=
    fun Q => ι (finPart D (e (Q.under (𝓞 D.host.F)))) Q
  have hff : ∀ Q, f Q * f Q = f Q := fun Q => by
    simp only [f]
    rw [← GlobalTheory.PlaceIdem.mul_ap, ← map_mul, ← RingHom.map_mul, hee]
  have hint : ∀ Q, f Q ∈ Q.adicCompletionIntegers D.host.E := fun Q => by
    by_cases h : f Q = 0
    · rw [h]; exact zero_mem _
    · rw [mul_left_cancel₀ h ((hff Q).trans (mul_one _).symm)]; exact one_mem _
  let b : FiniteAdeleRing (𝓞 D.host.E) D.host.E := ⟨f, Filter.Eventually.of_forall hint⟩
  have hb : ∀ Q, b Q = f Q := fun _ => rfl
  obtain ⟨a, ha1, ha2⟩ := GlobalTheory.PlaceIdem.parts_surj D 0 (ι.symm b)
  have ha3 : ι (finPart D a) = b := by rw [ha2, ι.apply_symm_apply]
  refine ⟨a, GlobalTheory.PlaceIdem.parts_inj D _ _ (by rw [RingHom.map_mul, ha1, mul_zero]) (ι.injective ?_), ha1,
    fun v => GlobalTheory.PlaceIdem.parts_inj D _ _ ?_ (ι.injective ?_)⟩
  · rw [RingHom.map_mul, map_mul, ha3]
    exact GlobalTheory.PlaceIdem.adele_ext fun Q => hff Q
  · rw [← hp v, RingHom.map_mul, RingHom.map_mul, hinf, mul_zero, mul_zero]
  · rw [← hp v, RingHom.map_mul, RingHom.map_mul, map_mul, map_mul, ha3]
    refine GlobalTheory.PlaceIdem.adele_ext fun Q => ?_
    rw [GlobalTheory.PlaceIdem.mul_ap, GlobalTheory.PlaceIdem.mul_ap]
    by_cases hQ : Q.under (𝓞 D.host.F) = v
    · subst hQ; rfl
    · rw [h0 v Q hQ, mul_zero, mul_zero]

theorem exists_select (D : D7) : ∃ a : Formalism.L2.Theta.AE D, a * a = a ∧ infPart D a = 0 ∧
    (∀ v ε, NonSplitAt D v ε → a * algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) ε = 0) ∧
    ∀ e, IsSplitIdem D e → a * (e + cA D e) = e ∨ a * (e + cA D e) = cA D e := by
  classical
  obtain ⟨a, h1, h2, h3⟩ := exists_glue D (fun v => if h : ∃ e, SplitAt D v e then h.choose else 0)
    (fun v => by
      split_ifs with h
      · exact h.choose_spec.1
      · exact mul_zero _)
    (fun v => by
      split_ifs with h
      · rw [mul_comm]; exact h.choose_spec.pl_mul
      · exact zero_mul _)
  refine ⟨a, h1, h2, fun v ε h => ?_, fun e he => ?_⟩
  · rw [eq_single h.1, h3, dif_neg]
    rintro ⟨e, he⟩
    exact h.2 ⟨e, (isSplitIdem_iff e).2 ⟨v, he⟩, by rw [eq_single h.1, he.2.2]⟩
  · obtain ⟨v, he⟩ := (isSplitIdem_iff e).1 he
    have h : ∃ e, SplitAt D v e := ⟨e, he⟩
    rw [he.2.2, h3, dif_pos h]
    exact (h.choose_spec.unique he).imp Eq.symm Eq.symm

theorem char_norm {D : D7} {χ : (Formalism.L2.Theta.AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n)
    (x y : (Formalism.L2.Theta.AE D)ˣ) (hy : (y : Formalism.L2.Theta.AE D) = x * cA D x) : χ y = 1 := by
  obtain ⟨⟨η, hη⟩, h⟩ := h
  have := D.host.isCMField_hostE
  have e : y = idF D (Units.map (Algebra.norm (AF D.host.F) : Formalism.L2.Theta.AE D →* AF D.host.F) x) :=
    Units.ext (hy.trans (GlobalTheory.Published.algebraMap_norm_tensor (E := D.host.E) (AF D.host.F)
      (x : Formalism.L2.Theta.AE D)).symm)
  rw [e, h η hη, hη.2.2.1, one_pow]

set_option maxHeartbeats 800000 in

theorem exists_split_character : ∀ (D : D7) (V : HSp D) (χ : (Formalism.L2.Theta.AE D)ˣ →* Circle) (n : ℕ), IsHeckeChar D χ → ResEta D χ n → ∃ ν : Formalism.L2.Theta.GA D V →* Circle, Continuous ν ∧ (∀ g ∈ GinfC V, ν g = 1) ∧ (∀ v ε, NonSplitAt D v ε → ∀ g, SuppPl ε V g → ν g = 1) ∧ ∀ e, IsSplitIdem D e → ∀ g, SuppAt e V g → ∀ x, IsDetAt e V g x → ν g = χ x := by
  intro D V χ n hχ hres
  obtain ⟨a, haa, hinf, hns, hsp⟩ := exists_select D
  haveI : IsTopologicalRing (Formalism.L2.Theta.AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  let d : Formalism.L2.Theta.GA D V →* (Formalism.L2.Theta.AE D)ˣ := Matrix.GeneralLinearGroup.det.comp (matHom V)
  have hd : ∀ g, (d g : Formalism.L2.Theta.AE D) = (Formalism.L2.Theta.mt V g).det := fun _ => rfl
  have hc : Continuous d := Matrix.GeneralLinearGroup.continuous_det.comp continuous_subtype_val
  have htriv : ∀ g, (∀ i j, a * (Formalism.L2.Theta.mt V g - 1) i j = 0) → χ (cut a haa (d g)) = 1 := fun g hg => by
    have : cut a haa (d g) = 1 := Units.ext (by
      rw [cut_val, hd, mul_det a _ hg, add_sub_cancel, Units.val_one])
    rw [this, map_one]
  refine ⟨χ.comp ((cut a haa).comp d), hχ.1.comp ((continuous_cut a haa).comp hc), fun g hg => htriv g fun i j => ?_,
    fun v ε h g hg => htriv g fun i j => ?_, fun e he g hg x hx => ?_⟩
  · refine GlobalTheory.PlaceIdem.parts_inj D _ _ (by rw [RingHom.map_mul, hinf, zero_mul, RingHom.map_zero]) ?_
    have h1 : (finPart D).mapMatrix (Formalism.L2.Theta.mt V g) = 1 := congrArg Units.val hg
    have h2 : (finPart D).mapMatrix (Formalism.L2.Theta.mt V g - 1) = 0 := by
      rw [RingHom.map_sub, h1, RingHom.map_one, sub_self]
    have h3 : finPart D ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := congrFun (congrFun h2 i) j
    rw [RingHom.map_mul, h3, mul_zero, RingHom.map_zero]
  · rw [← hg i j, ← mul_assoc, hns v ε h, zero_mul]
  · show χ (cut a haa (d g)) = χ x
    have hout := mul_det (1 - (e + cA D e)) (Formalism.L2.Theta.mt V g) fun i j => by rw [sub_mul, one_mul, hg i j, sub_self]
    have hx' : (x : Formalism.L2.Theta.AE D) = e * (Formalism.L2.Theta.mt V g).det + (1 - e) := hx
    rcases hsp e he with h | h
    · congr 1
      refine Units.ext ?_
      rw [cut_val, hd, hx']
      linear_combination a * hout + ((Formalism.L2.Theta.mt V g).det - 1) * h
    · have hy : (cut a haa (d g) : Formalism.L2.Theta.AE D) = cA D e * (Formalism.L2.Theta.mt V g).det + (1 - cA D e) := by
        rw [cut_val, hd]
        linear_combination a * hout + ((Formalism.L2.Theta.mt V g).det - 1) * h
      have hcc : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he.1]
      have hu := det_conj_mul V g
      have h1 : (cut a haa (d g) : Formalism.L2.Theta.AE D) * cA D x = 1 := by
        rw [hy, hx', RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one]
        generalize (Formalism.L2.Theta.mt V g).det = z at hu
        linear_combination (z * cA D z - z - cA D z + 1) * hcc + cA D e * hu
      have h2 := char_norm hres x (x * (cut a haa (d g))⁻¹) (by
        rw [Units.val_mul, Units.inv_eq_of_mul_eq_one_right h1])
      rw [map_mul, map_inv, mul_inv_eq_one] at h2
      exact h2.symm

end GlobalTheory.SplitDetChar

end
