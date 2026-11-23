import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTildeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTwistHeckeCharactersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumUniqueOnThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormOneRootCongruentOddHostField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacInert

theorem exists_pole_idem {E : Type} [Field E] [NumberField E] (z w : FiniteAdeleRing (𝓞 E) E)
    (hzw : z * w = 1) : ∃ e : FiniteAdeleRing (𝓞 E) E, e * e = e ∧ (∀ P, Valued.v ((e * w) P) ≤ 1) ∧
      (e = 0 → ∀ P, Valued.v (z P) ≤ 1) ∧
      (∀ f : FiniteAdeleRing (𝓞 E) E, f * f = f → (∀ P, Valued.v ((f * z) P) ≤ 1) → e * f = 0) := by
  classical
  let e : FiniteAdeleRing (𝓞 E) E := ⟨fun P => if 1 < Valued.v (z P) then 1 else 0,
    Filter.Eventually.of_forall fun P => by
      by_cases h : 1 < Valued.v (z P)
      · simp only [if_pos h]; exact one_mem _
      · simp only [if_neg h]; exact zero_mem _⟩
  have he : ∀ P, e P = if 1 < Valued.v (z P) then 1 else 0 := fun _ => rfl
  have hmul : ∀ (a b : FiniteAdeleRing (𝓞 E) E) P, (a * b) P = a P * b P := fun _ _ _ => rfl
  refine ⟨e, ?_, fun P => ?_, fun h P => ?_, fun f hf hfz => ?_⟩
  · refine Subtype.ext (funext fun P => ?_)
    change e P * e P = e P
    rw [he]; split_ifs <;> simp
  · rw [hmul, he]
    split_ifs with h
    · have h1 : z P * w P = 1 := congrArg (fun a : FiniteAdeleRing (𝓞 E) E => a P) hzw
      have h2 := congrArg Valued.v h1
      rw [map_mul, map_one] at h2
      rw [one_mul]
      by_contra h3
      exact absurd h2 (one_lt_mul_of_lt_of_le' h (not_le.1 h3).le).ne'
    · simp
  · have h0 : e P = 0 := by rw [h]; rfl
    by_contra h3
    rw [he, if_pos (not_le.1 h3)] at h0
    exact one_ne_zero h0
  · refine Subtype.ext (funext fun P => ?_)
    change e P * f P = 0
    rw [he]
    split_ifs with h
    · have h1 : f P * f P = f P := congrArg (fun a : FiniteAdeleRing (𝓞 E) E => a P) hf
      rw [one_mul]
      by_contra h0
      have h2 : f P = 1 := mul_left_cancel₀ h0 (h1.trans (mul_one _).symm)
      have h3 := hfz P
      rw [hmul, h2, one_mul] at h3
      exact absurd h (not_lt.2 h3)
    · simp

variable {D : D7}

theorem conj_int (x : 𝓞 D.host.E) : ∃ y : 𝓞 D.host.E, (y : D.host.E) = D.sp.cm.sig (x : D.host.E) :=
  ⟨⟨_, (RingOfIntegers.isIntegral_coe x).map (D.sp.cm.sig : D.host.E →+* D.host.E).toIntAlgHom⟩, rfl⟩

theorem sigR_mem {y : Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ intAE D) :
    sigR (Af D.host.F) D.sp.cm.sig y ∈ intAE D := by
  induction hy using AddSubgroup.closure_induction with
  | mem y h =>
    obtain ⟨a, ha, x, rfl⟩ := h
    obtain ⟨y, hy⟩ := conj_int x
    exact AddSubgroup.subset_closure ⟨a, ha, y, by rw [hy]; rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

theorem finPart_cA (z : AE D) :
    finPart D (cA D z) = sigR (Af D.host.F) D.sp.cm.sig (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]
  | tmul a x => rfl
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, RingHom.map_add, ha, hb]

theorem infPart_cA (z : AE D) :
    infPart D (cA D z) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]
  | tmul a x => rfl
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, RingHom.map_add, ha, hb]

theorem cA_cA (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | tmul a x => exact congrArg (fun y : D.host.E => a ⊗ₜ[D.host.F] y) (star_star x)
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, ha, hb]

theorem cA_alg (a : AF D.host.F) :
    cA D (algebraMap (AF D.host.F) (AE D) a) = algebraMap (AF D.host.F) (AE D) a :=
  congrArg (fun y : D.host.E => a ⊗ₜ[D.host.F] y) (map_one D.sp.cm.sig)

theorem parts_ext {x y : AE D} (h1 : infPart D x = infPart D y) (h2 : finPart D x = finPart D y) : x = y := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  exact e.injective (Prod.ext ((he _).1.trans (h1.trans (he _).1.symm)) ((he _).2.trans (h2.trans (he _).2.symm)))

theorem exists_lift (y : Af D.host.F ⊗[D.host.F] D.host.E) : ∃ x : AE D, infPart D x = 0 ∧ finPart D x = y := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  refine ⟨e.symm (0, y), (he _).1.symm.trans ?_, (he _).2.symm.trans ?_⟩ <;> simp

theorem tmul_trace {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] (a : R) (x y : E)
    (t : F) (ht : algebraMap F E t = x + y) : a ⊗ₜ[F] x + a ⊗ₜ[F] y = (t • a) ⊗ₜ[F] (1 : E) := by
  rw [← TensorProduct.tmul_add, ← ht, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]

theorem trace_mem (z : AE D) : ∃ a, z + cA D z = algebraMap (AF D.host.F) (AE D) a := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [RingHom.map_zero, RingHom.map_zero, add_zero]⟩
  | tmul a x =>
    obtain ⟨t, ht⟩ : ∃ t : D.host.F, algebraMap _ _ t = x + D.sp.cm.sig x := by
      apply (D.sp.cm.fixed _).1
      change D.sp.cm.sig _ = _
      rw [map_add, show D.sp.cm.sig (D.sp.cm.sig x) = x from star_star x, add_comm]
    exact ⟨t • a, tmul_trace a x _ t ht⟩
  | add a b ha hb =>
    obtain ⟨s, hs⟩ := ha
    obtain ⟨t, ht⟩ := hb
    exact ⟨s + t, by rw [RingHom.map_add, RingHom.map_add, ← hs, ← ht, add_add_add_comm]⟩

theorem one_int : (1 : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D :=
  AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, 1, rfl⟩

theorem alg_inj : Function.Injective (algebraMap (AF D.host.F) (AE D)) :=
  Algebra.TensorProduct.includeLeft_injective (S := D.host.F) (algebraMap D.host.F D.host.E).injective

theorem idem_below {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε)
    {a : AF D.host.F} (ha : a * a = a) (hεa : ε * a = a) : a = 0 ∨ a = ε := by
  obtain ⟨α, rfl, h1, h0⟩ := hε
  obtain ⟨a1, a2⟩ := a
  have e1 : a1 = 0 := (congrArg Prod.fst hεa).symm.trans (zero_mul a1)
  have e2 : α * a2 = a2 := congrArg Prod.snd hεa
  have e3 : a2 * a2 = a2 := congrArg Prod.snd ha
  have e4 : ∀ w, w ≠ v → evalV D.host.F w a2 = 0 := fun w hw => by
    rw [← e2, map_mul, h0 w hw, zero_mul]
  have e5 := congrArg (evalV D.host.F v) e3
  rw [map_mul] at e5
  have ext : ∀ a b : Af D.host.F, (∀ w, evalV D.host.F w a = evalV D.host.F w b) → a = b :=
    fun a b h => Subtype.ext (funext h)
  by_cases h : evalV D.host.F v a2 = 0
  · left
    refine Prod.ext e1 (ext _ _ fun w => ?_)
    by_cases hw : w = v
    · rw [hw]; exact h.trans (map_zero _).symm
    · exact (e4 w hw).trans (map_zero _).symm
  · right
    refine Prod.ext e1 (ext _ _ fun w => ?_)
    by_cases hw : w = v
    · rw [hw]; exact (mul_left_cancel₀ h (e5.trans (mul_one _).symm)).trans h1.symm
    · exact (e4 w hw).trans (h0 w hw).symm

theorem placeIdem_facts {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) :
    ε * ε = ε ∧ infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 ∧
      finPart D (algebraMap (AF D.host.F) (AE D) ε) ∈ intAE D := by
  obtain ⟨α, rfl, h1, h0⟩ := hε
  refine ⟨Prod.ext (mul_zero _) (Subtype.ext (funext fun w => ?_)), TensorProduct.zero_tmul _ _,
    AddSubgroup.subset_closure ⟨α, fun w => ?_, 1, rfl⟩⟩
  · change evalV D.host.F w α * evalV D.host.F w α = evalV D.host.F w α
    by_cases hw : w = v
    · rw [hw, h1, one_mul]
    · rw [h0 w hw, zero_mul]
  · by_cases hw : w = v
    · rw [hw, h1]; exact one_mem _
    · rw [h0 w hw]; exact zero_mem _

set_option maxHeartbeats 1600000 in

theorem normOne_int {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : NonSplitAt D v ε)
    {u : AE D} (hu : cA D u * u = 1) (hs : algebraMap (AF D.host.F) (AE D) ε * (u - 1) = u - 1) :
    finPart D u ∈ intAE D := by
  obtain ⟨ι, -, hι, -⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨hεε, hεi, hεf⟩ := placeIdem_facts hε.1
  obtain ⟨e₀, h1, h2, h3, h4⟩ := exists_pole_idem (ι (finPart D u)) (ι (finPart D (cA D u)))
    (by rw [← map_mul, ← RingHom.map_mul, mul_comm, hu, RingHom.map_one, map_one])
  obtain ⟨e, hei, hef⟩ := exists_lift (ι.symm e₀)
  have he₀ : e₀ = ι (finPart D e) := by rw [hef, RingEquiv.apply_symm_apply]
  subst he₀
  clear hef
  have hee : e * e = e := parts_ext (by rw [RingHom.map_mul, hei, mul_zero])
    (ι.injective (by rw [RingHom.map_mul, map_mul, h1]))
  have key : ∀ f : AE D, f * f = f → finPart D (f * u) ∈ intAE D → e * f = 0 := fun f hf hfu =>
    parts_ext (by rw [RingHom.map_mul, hei, zero_mul, RingHom.map_zero]) (ι.injective (by
      rw [RingHom.map_mul, map_mul, RingHom.map_zero, map_zero]
      refine h4 _ (by rw [← map_mul, ← RingHom.map_mul, hf]) ?_
      rw [← map_mul, ← RingHom.map_mul]
      exact (hι _).1 hfu))
  have hcc : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, hee]
  have hec : e * cA D e = 0 := key _ hcc (by
    rw [← map_mul, ← RingHom.map_mul] at h2
    have := sigR_mem ((hι _).2 h2)
    rwa [← finPart_cA, RingHom.map_mul, cA_cA] at this)
  have hεε' : algebraMap (AF D.host.F) (AE D) ε * algebraMap (AF D.host.F) (AE D) ε =
      algebraMap (AF D.host.F) (AE D) ε := by rw [← RingHom.map_mul, hεε]
  have hc := cA_alg (D := D) ε
  have hone := one_int (D := D)
  have hεe : e * (1 - algebraMap (AF D.host.F) (AE D) ε) = 0 := key _ (by linear_combination hεε') (by
    rw [show (1 - algebraMap (AF D.host.F) (AE D) ε) * u = 1 - algebraMap (AF D.host.F) (AE D) ε by
      linear_combination -hs, RingHom.map_sub, RingHom.map_one]
    exact sub_mem hone hεf)
  have hεc := congrArg (cA D) hεe
  rw [RingHom.map_mul, RingHom.map_sub, RingHom.map_one, hc, RingHom.map_zero] at hεc
  obtain ⟨a, ha⟩ := trace_mem e
  have haa : a * a = a := alg_inj (D := D) (by
    rw [RingHom.map_mul, ← ha]; linear_combination hee + hcc + 2 * hec)
  have hεa : ε * a = a := alg_inj (D := D) (by
    rw [RingHom.map_mul, ← ha]; linear_combination -hεe - hεc)
  rcases idem_below hε.1 haa hεa with h | h
  · rw [h, RingHom.map_zero] at ha
    have : e = 0 := by linear_combination e * ha - hee - hec
    exact (hι _).2 (h3 (by rw [this, RingHom.map_zero, map_zero]))
  · rw [h] at ha
    exact absurd ⟨e, ⟨hee, hec, v, ε, hε.1, ha⟩, ha⟩ hε.2

theorem det_supp {R : Type} [CommRing R] {n : ℕ} (ε : R) (hε : ε * ε = ε) (m : Matrix (Fin n) (Fin n) R)
    (hm : ∀ i j, ε * (m - 1) i j = (m - 1) i j) : ε * (m.det - 1) = m.det - 1 := by
  let q := Ideal.Quotient.mk (Ideal.span {ε})
  have h0 : q ε = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self ε)
  have h1 : q.mapMatrix m = q.mapMatrix 1 := by
    rw [← sub_eq_zero, ← map_sub]
    ext i j
    change q ((m - 1) i j) = 0
    rw [← hm, map_mul, h0, zero_mul]
  have h2 : q (m.det - 1) = 0 := by
    rw [map_sub, q.map_det, h1, map_one, map_one, det_one, sub_self]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h2)
  rw [← hc]
  linear_combination c * hε

set_option maxHeartbeats 1600000 in

theorem exists_unit_root {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : NonSplitAt D v ε)
    (V : HSp D) (g : GA D V) (hg : SuppPl ε V g) : ∃ x : (AE D)ˣ, IsDetRoot V g x ∧ infPart D (x : AE D) = 1 ∧
      algebraMap (AF D.host.F) (AE D) ε * ((x : AE D) - 1) = (x : AE D) - 1 ∧
      finPart D (x : AE D) ∈ intAE D ∧ finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D := by
  obtain ⟨hεε, hεi, hεf⟩ := placeIdem_facts hε.1
  have hεε' : algebraMap (AF D.host.F) (AE D) ε * algebraMap (AF D.host.F) (AE D) ε =
      algebraMap (AF D.host.F) (AE D) ε := by rw [← RingHom.map_mul, hεε]
  have hc := cA_alg (D := D) ε
  have hs := det_supp _ hεε' _ hg
  have hn := det_conj_mul V g
  have hi := normOne_int hε hn hs
  have hone := one_int (D := D)
  obtain ⟨x, y, hx, hy, hxy, hr, -⟩ := GlobalTheory.OddRoot.exists_root_odd D 1 odd_one _ _ (sub_mem hi hone)
    (one_nsmul _).symm (by rw [← finPart_cA, ← RingHom.map_mul, mul_comm, hn, RingHom.map_one])
  obtain ⟨X, hXi, rfl⟩ := exists_lift x
  obtain ⟨Y, hYi, rfl⟩ := exists_lift y
  change ∃ x : (AE D)ˣ, (x : AE D) = (Formalism.L2.Theta.mt V g).det * cA D x ∧ _
  generalize (Formalism.L2.Theta.mt V g).det = u at *
  generalize algebraMap (AF D.host.F) (AE D) ε = η at *
  have h1 : η * (X * Y) = η := parts_ext (by rw [RingHom.map_mul, hεi, zero_mul])
    (by rw [RingHom.map_mul, RingHom.map_mul, hxy, mul_one])
  have h2 : X = u * cA D X := parts_ext
    (by rw [RingHom.map_mul, infPart_cA, hXi, RingHom.map_zero, mul_zero])
    (by rw [RingHom.map_mul, finPart_cA]; exact hr)
  have h3 : (η * X + (1 - η)) * (η * Y + (1 - η)) = 1 := by
    linear_combination (X * Y - X - Y + 1) * hεε' + h1
  have h4 : ∀ Z, finPart D Z ∈ intAE D → finPart D (η * Z + (1 - η)) ∈ intAE D := fun Z hZ => by
    rw [RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one]
    exact add_mem (GlobalTheory.HostAdeleIso.intAE_mul_mem D hεf hZ) (sub_mem hone hεf)
  refine ⟨⟨_, _, h3, by rw [mul_comm, h3]⟩, ?_, ?_, ?_, h4 X hx, h4 Y hy⟩
  · change η * X + (1 - η) = u * cA D (η * X + (1 - η))
    rw [RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, hc]
    linear_combination η * h2 + hs
  · change infPart D (η * X + (1 - η)) = 1
    rw [RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, hεi]
    ring
  · change η * (η * X + (1 - η) - 1) = η * X + (1 - η) - 1
    linear_combination (X - 1) * hεε'

theorem hecke_quot {χ η : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (h : IsHeckeChar D η) :
    IsHeckeChar D (η⁻¹ * χ) :=
  ⟨h.1.inv.mul hχ.1, fun x => by rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h.2, hχ.2, inv_one, one_mul]⟩

theorem resEta_quot {χ η : (AE D)ˣ →* Circle} {n : ℕ} (hχ : ResEta D χ n) (h : ResEta D η n) :
    ResEta D (η⁻¹ * χ) 0 :=
  resEta_parity (resEta_mul (resEta_inv h) hχ) (by omega)

theorem fixesVacAt_of_unram : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (χS χT : (AE D)ˣ →* Circle) (om : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))), (∃ η, IsEtaTilde D η) → IsWeilDatumO ψ S T χS χT om → ∀ v ε, NonSplitAt D v ε → UnramAt ε χS → UnramAt ε χT → FixesVacAt ψ S T ΛS ΛT om v ε := by
  intro D ψ hψ S T ΛS ΛT hS hT χS χT om ⟨η, hη⟩ hom v ε hε uS uT g h hg hh hlat f hf hfix
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨om₀, h0, hv, -⟩ := GlobalTheory.T.exists_weilDatum_powers_unramifiedEtaTilde D ψ hψ S T θ hθ ΛS ΛT hS hT η hη
  obtain ⟨om₁, h1, htw⟩ := GlobalTheory.T.exists_weilDatum_twist_heckeCharacters D ψ hψ S T _ _ ((η ^ S.rank)⁻¹ * χS) ((η ^ T.rank)⁻¹ * χT) om₀ h0
    (hecke_quot hom.hecS h0.hecS) (hecke_quot hom.hecT h0.hecT)
    (resEta_quot hom.resS h0.resS) (resEta_quot hom.resT h0.resT)
  rw [mul_inv_cancel_left, mul_inv_cancel_left] at h1
  obtain ⟨x, hx, xi, xs, x1, x2⟩ := exists_unit_root hε S g hg
  obtain ⟨y, hy, yi, ys, y1, y2⟩ := exists_unit_root hε T h hh
  rw [GlobalTheory.T.weilDatum_unique_on_thetaFunctions D ψ hψ S T χS χT om om₁ hom h1 _ f hf, htw g h x y hx hy, LinearMap.smul_apply,
    hv v ε hε g h hg hh hlat f hf hfix]
  simp [hη.2.1 x xi x1 x2, hη.2.1 y yi y1 y2, uT x xs x1 x2, uS y ys y1 y2]

end GlobalTheory.VacInert
