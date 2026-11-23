import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDetInt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqProdLocalComponentsApproximating
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIdeleExistsLocalApprox
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChrOff

theorem idem_apply_eq_one {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
    (a : FiniteAdeleRing (𝓞 E) E) (ha : a * a = a)
    (h : ∀ x ∈ P.asIdeal, x ≠ 0 →
      ¬ ∀ Q, Valued.v ((a * algebraMap E (FiniteAdeleRing (𝓞 E) E) ((x : E)⁻¹)) Q) ≤ 1) : a P = 1 := by
  have h01 : ∀ Q, a Q ≠ 0 → a Q = 1 := fun Q hQ =>
    mul_left_cancel₀ hQ (by rw [← GlobalTheory.PlaceIdem.mul_ap, ha, mul_one])
  refine h01 P fun h0 => ?_
  obtain ⟨n, hn, x, hx⟩ := GlobalTheory.IdemRes.exists_pow_eq_span P.asIdeal P.ne_bot
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.2 rfl] at hx
    exact P.ne_bot (pow_eq_zero_iff hn.ne' |>.1 hx)
  refine h x (Ideal.pow_le_self hn.ne' (hx ▸ Ideal.mem_span_singleton_self x)) hx0 fun Q => ?_
  rw [GlobalTheory.PlaceIdem.mul_ap]
  by_cases hQ : a Q = 0
  · rw [hQ, zero_mul, map_zero]; exact zero_le
  · rw [h01 Q hQ, one_mul, GlobalTheory.PlaceIdem.val_inv_le_one Q hx0]
    intro hxQ
    have := Q.isPrime
    have h1 : P.asIdeal ^ n ≤ Q.asIdeal := by rw [hx]; exact (Ideal.span_singleton_le_iff_mem _).2 hxQ
    have h2 : P.asIdeal ≤ Q.asIdeal := Ideal.IsPrime.le_of_pow_le h1
    have h3 : P = Q := HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top h2)
    exact hQ (h3 ▸ h0)

variable {D : D7}

theorem exists_conj_mem {P P' : Pl D.host.E} (h : Formalism.IndefR.Lev.IsConjPl P P') {x : 𝓞 D.host.E}
    (hx : x ∈ P'.asIdeal) : ∃ y ∈ P.asIdeal, D.sp.cm.sig (y : D.host.E) = (x : D.host.E) := by
  let s : 𝓞 D.host.E →+* 𝓞 D.host.E := RingOfIntegers.mapRingHom (D.sp.cm.sig : D.host.E →+* D.host.E)
  have hs : ∀ y, (s y : D.host.E) = star (y : D.host.E) := fun _ => rfl
  have hle : P.asIdeal ≤ P'.asIdeal.comap s := fun c hc => by
    obtain ⟨c', hc', e⟩ := h c hc
    have : s c = c' := RingOfIntegers.ext (by rw [hs, e])
    rw [Ideal.mem_comap, this]; exact hc'
  have he := P.isMaximal.eq_of_le (Ideal.comap_ne_top s P'.isPrime.ne_top) hle
  have hss : s (s x) = x := RingOfIntegers.ext (by rw [hs, hs, star_star])
  refine ⟨s x, ?_, congrArg Subtype.val hss⟩
  rw [he, Ideal.mem_comap, hss]; exact hx

section
variable (ι : (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
  (h1 : ∀ x : D.host.E, ι ((1 : GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] x) =
    algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x)
  (h2 : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1)
include h1 h2

theorem comp_eq_one {f : AE D} (hf : f * f = f) (P : Pl D.host.E)
    (h : ∀ x ∈ P.asIdeal, x ≠ 0 → finPart D (f * incA D ((x : D.host.E)⁻¹)) ∉ intAE D) :
    ι (finPart D f) P = 1 := by
  refine idem_apply_eq_one P _ (by rw [← map_mul, ← RingHom.map_mul, hf]) fun x hx hx0 hc => h x hx hx0 ?_
  have e : finPart D (incA D ((x : D.host.E)⁻¹)) = (1 : GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] ((x : D.host.E)⁻¹) := rfl
  rw [h2, RingHom.map_mul, map_mul, e, h1]
  exact hc

theorem comp_idem {f : AE D} {P : Pl D.host.E} (hf : Formalism.L2.NTheta.IsIdemAt f P) : ι (finPart D f) P = 1 :=
  comp_eq_one ι h1 h2 hf.1.1 P fun x hx hx0 => (hf.2 x hx0).1 hx

theorem comp_conj_idem {f : AE D} {P P' : Pl D.host.E} (hf : Formalism.L2.NTheta.IsIdemAt f P)
    (hc : Formalism.IndefR.Lev.IsConjPl P P') : ι (finPart D (cA D f)) P' = 1 := by
  refine comp_eq_one ι h1 h2 (by rw [← RingHom.map_mul, hf.1.1]) P' fun x hx hx0 hi => ?_
  obtain ⟨y, hy, hyx⟩ := exists_conj_mem hc hx
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hx0 (RingOfIntegers.ext (hyx.symm.trans (map_zero _)))
  refine (hf.2 y hy0).1 hy ?_
  have e : cA D (incA D ((y : D.host.E)⁻¹)) = incA D ((x : D.host.E)⁻¹) := by
    rw [← hyx, ← map_inv₀ D.sp.cm.sig]; rfl
  rw [← e, ← RingHom.map_mul, GlobalTheory.PlaceIdem.finPart_cA] at hi
  have := GlobalTheory.PlaceIdem.sig_mem D hi
  rwa [GlobalTheory.PlaceIdem.sig_sig] at this

end

theorem exists_idem_mul {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) {PP : Pl D.host.E} (hPP : PP ∈ P) :
    ∃ f : AE D, Formalism.L2.NTheta.IsIdemAt f PP ∧ f * (e + cA D e) = f ∧ cA D f * (e + cA D e) = cA D f := by
  obtain ⟨⟨es, h1, h2⟩, h3⟩ := he
  have h4 : es PP * e = es PP := by
    rw [h2]
    refine GlobalTheory.PlaceModelSum.mul_sum_orth (fun i hi => (h1 i hi).1) (fun i hi j hj hij => ?_) hPP
    refine (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (h1 i hi).1 (h1 j hj).1).resolve_left fun h => hij ?_
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    by_cases hx : x = 0
    · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
    · rw [(h1 i hi).2 x hx, (h1 j hj).2 x hx, h]
  have h5 : es PP * (e + cA D e) = es PP := by
    rw [mul_add, h4, ← h4, mul_assoc, h3, mul_zero, add_zero]
  refine ⟨es PP, h1 PP hPP, h5, ?_⟩
  have h6 := congrArg (cA D) h5
  rwa [RingHom.map_mul, RingHom.map_add, cA_cA, add_comm] at h6

theorem unrOff_of_unrAt : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (P : Finset (Pl D.host.E)) (e : AE D), ChrEq c χ → IsIdemSum e P → (∀ PP', PP' ∉ P → (∀ PP ∈ P, ¬ Formalism.IndefR.Lev.IsConjPl PP PP') → χ.UnrAt PP') → UnrOff (e + cA D e) c := by
  intro D c χ P₀ e hc he hu x hx1 hx2 hx3 hb
  classical
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2
    (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc
  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom x)
  have hv : ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι (finPart D (x : AE D)) P) = 1 := by
    intro P
    have a := (h2 _).1 hx2 P
    have b := (h2 _).1 hx3 P
    have e : ι (finPart D (x : AE D)) * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    have e' : Valued.v (ι (finPart D (x : AE D)) P) * Valued.v (ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P) = 1 := by
      rw [← map_mul]
      have : ι (finPart D (x : AE D)) P * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P = 1 :=
        congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z P) e
      rw [this, map_one]
    refine le_antisymm a ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := e'.symm
      _ ≤ Valued.v (ι (finPart D (x : AE D)) P) * 1 := mul_le_mul_right b _
      _ = _ := mul_one _
  have hone : ∀ (f : AE D) (P : HeightOneSpectrum (𝓞 D.host.E)), f * (e + cA D e) = f → ι (finPart D f) P = 1 →
      ι (finPart D (x : AE D)) P = 1 := by
    intro f P hf hP
    have e1 : f * (x : AE D) = f := by rw [← hf, mul_assoc, hb]
    have e2 : ι (finPart D f) * ι (finPart D (x : AE D)) = ι (finPart D f) := by
      rw [← map_mul, ← RingHom.map_mul, e1]
    have e3 : ι (finPart D f) P * ι (finPart D (x : AE D)) P = ι (finPart D f) P :=
      congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z P) e2
    rwa [hP, one_mul] at e3
  have hunr : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ι (finPart D (x : AE D)) P ≠ 1 → χ.UnrAt P := by
    intro P hP
    refine hu P (fun hm => hP ?_) fun PP hm hcj => hP ?_
    · obtain ⟨f, f1, f2, -⟩ := exists_idem_mul he hm
      exact hone f P f2 (comp_idem ι h1 h2 f1)
    · obtain ⟨f, f1, -, f3⟩ := exists_idem_mul he hm
      exact hone _ P f3 (comp_conj_idem ι h1 h2 f1 hcj)
  have key := hprod x hx1 S (fun P => if ι (finPart D (x : AE D)) P = 1 then 1 else k P) (fun P hP => by
    by_cases h : ι (finPart D (x : AE D)) P = 1
    · rw [if_pos h, h, Units.val_one, map_one, map_one, map_one, sub_self, map_zero]
      exact ⟨rfl, zero_le⟩
    · rw [if_neg h]
      exact ⟨(hS P hP).1, (hS P hP).2.1⟩) hS'
  apply Subtype.ext
  refine key.trans (Finset.prod_eq_one fun P hP => ?_)
  by_cases h : ι (finPart D (x : AE D)) P = 1
  · rw [if_pos h, map_one, Units.val_one]
  · rw [if_neg h]
    have a' : Valued.v (ι (finPart D (x : AE D)) P) = P.valuation D.host.E (k P : D.host.E) := (hS P hP).1
    rw [hv P] at a'
    have hun : Formalism.L2.Host.IsUnitAt P (Formalism.L2.Host.atFin P (k P)) := by
      show Valued.v (((k P : D.host.E)) : P.adicCompletion D.host.E) = _
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← a']
    show ((χ.loc P (Formalism.L2.Host.atFin P (k P)) : ℂˣ) : ℂ) = 1
    rw [hunr P h _ hun, Units.val_one]

end GlobalTheory.ChrOff
