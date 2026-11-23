import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdLawAtOfSteps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartEqOneOfFibres
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitB
import Formalism.LocalToGlobal.Columns.DecoFin
import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwU.MuUnr

theorem le_exp_neg_one' {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) : γ ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
  rcases eq_or_ne γ 0 with rfl | h0
  · exact zero_le'
  rw [← WithZero.exp_log h0] at h ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
  rw [WithZero.exp_le_exp]
  omega

theorem finPart_eq_one {E : Type} [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (z : (GlobalTheory.CMVal.Af E)ˣ)
    (hu : ∀ P, Valued.v ((z : GlobalTheory.CMVal.Af E) P) = 1)
    (hc : ∀ P, χ.UnrAt P ∨ (χ.TameAt P ∧ Valued.v ((z : GlobalTheory.CMVal.Af E) P - 1) < 1)) :
    GlobalTheory.CMVal.finPart χ z = 1 := by
  have e : (fun P => χ.loc P (GlobalTheory.CMVal.coord P z)) = fun _ => 1 := funext fun P => by
    rcases hc P with h | ⟨h, h'⟩
    · exact h _ (hu P)
    · exact h _ (hu P) (le_exp_neg_one' h')
  have h := GlobalTheory.CMVal.Fibre.hasProd_loc χ z
  rw [e] at h
  exact h.unique hasProd_one

theorem exists_pow_eq_span {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ (n : ℕ) (s : 𝓞 F), 0 < n ∧ v.asIdeal ^ n = Ideal.span {s} := by
  classical
  have hv : v.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 F)) := mem_nonZeroDivisors_of_ne_zero v.ne_bot
  set n := Fintype.card (ClassGroup (𝓞 F)) with hn
  have hvn : v.asIdeal ^ n ∈ nonZeroDivisors (Ideal (𝓞 F)) := pow_mem hv n
  have e : (⟨v.asIdeal ^ n, hvn⟩ : nonZeroDivisors (Ideal (𝓞 F))) = ⟨v.asIdeal, hv⟩ ^ n := Subtype.ext (by simp)
  have h1 : ClassGroup.mk0 ⟨v.asIdeal ^ n, hvn⟩ = 1 := by
    rw [e, map_pow]
    exact pow_card_eq_one
  obtain ⟨s, hs⟩ := ((ClassGroup.mk0_eq_one_iff hvn).1 h1).principal
  exact ⟨n, s, Fintype.card_pos, hs⟩

theorem one_sub_eps_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ s : 𝓞 F, s ∈ v.asIdeal ∧ ∃ c ∈ RInt F E,
      1 - Formalism.UG.P.afsplitEps E v = (algebraMap F E (s : F) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * c := by
  obtain ⟨n, s, hn, hs⟩ := exists_pow_eq_span v
  have hsv : s ∈ v.asIdeal := Ideal.pow_le_self hn.ne' (hs ▸ Ideal.mem_span_singleton_self s)
  have hsw : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → s ∉ w.asIdeal := fun w hw h => by
    have h1 : v.asIdeal ^ n ≤ w.asIdeal := by rw [hs, Ideal.span_le, Set.singleton_subset_iff]; exact h
    exact hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top (w.isPrime.le_of_pow_le h1))).symm
  have hs0 : (s : F) ≠ 0 := by
    intro h0
    have : s = 0 := by exact_mod_cast h0
    subst this
    rw [Ideal.span_singleton_eq_bot.2 rfl] at hs
    exact v.ne_bot (pow_eq_zero_iff hn.ne' |>.1 hs)
  let a : FiniteAdeleRing (𝓞 F) F := algebraMap F _ (s : F)⁻¹ * (1 - Formalism.UG.P.afsplitI v 1)
  have ha : a ∈ intAd F := by
    intro w
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    change Valued.v ((((s : F)⁻¹ : F) : HeightOneSpectrum.adicCompletion F w) * ((1 : HeightOneSpectrum.adicCompletion F w) - Formalism.UG.P.afsplitI v 1 w)) ≤ 1
    by_cases hw : w = v
    · subst hw
      rw [Formalism.UG.P.afsplitI_self, sub_self, mul_zero, map_zero]
      exact zero_le'
    · rw [Formalism.UG.P.afsplitI_ne v w hw, sub_zero, mul_one, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀,
        show ((s : F)) = algebraMap (𝓞 F) F s from rfl, (HeightOneSpectrum.valuation_eq_one_iff_notMem w).2 (hsw w hw), inv_one]
  refine ⟨s, hsv, (1 : E) ⊗ₜ[F] a, Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩), ?_⟩
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
    Formalism.UG.P.afsplitEps, show (1 : E ⊗[F] HeightOneSpectrum.adicCompletion F v) = 1 ⊗ₜ[F] 1 from rfl, Formalism.UG.P.afsplitIE_tmul,
    Algebra.TensorProduct.one_def, ← TensorProduct.tmul_sub]
  congr 1
  rw [Algebra.smul_def, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hs0, (algebraMap F (FiniteAdeleRing (𝓞 F) F)).map_one, one_mul]

end GlobalTheory.TwU.MuUnr

namespace GlobalTheory.TwU.MuUnr

open GlobalTheory.Mem.Col2 (afIso afIso_tmul_one mem_rInt_iff)

theorem val_afIso_eq_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {x : (AfE F E)ˣ} (hx : x ∈ intU F E) (P : HeightOneSpectrum (𝓞 E)) : Valued.v (afIso F E (x : AfE F E) P) = 1 := by
  obtain ⟨h1, h2⟩ := (Submonoid.mem_units_iff _ x).1 hx
  have a1 := (mem_rInt_iff F E _).1 h1 P
  have a2 := (mem_rInt_iff F E _).1 h2 P
  have e : afIso F E (x : AfE F E) P * afIso F E ((x⁻¹ : (AfE F E)ˣ) : AfE F E) P = 1 := by
    rw [show afIso F E (x : AfE F E) P * afIso F E ((x⁻¹ : (AfE F E)ˣ) : AfE F E) P =
      (afIso F E (x : AfE F E) * afIso F E ((x⁻¹ : (AfE F E)ˣ) : AfE F E)) P from rfl, ← map_mul, Units.mul_inv, map_one]; rfl
  have e2 := congrArg Valued.v e
  rw [map_mul, map_one] at e2
  exact le_antisymm a1 (by
    by_contra hlt
    push_neg at hlt
    have := mul_le_mul' (le_refl (Valued.v (afIso F E (x : AfE F E) P))) a2
    rw [mul_one, e2] at this
    exact not_le.2 hlt this)

end GlobalTheory.TwU.MuUnr

namespace GlobalTheory.TwU.MuUnr

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}

theorem host_conj_F (r : 𝓞 D.host.F) :
    D.host.conj (algebraMap (𝓞 D.host.E) D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r)) =
      algebraMap (𝓞 D.host.E) D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) :=
  (D.host.conjE_mem_hostF_iff _).1 (r : D.host.F).2

theorem isOver_conjP (t : KerEntTied ex) (v : HeightOneSpectrum (𝓞 D.host.F)) (P : HeightOneSpectrum (𝓞 t.X.E))
    (h : IsOver v (seamP t.seam P)) : IsOver v (seamP t.seam (conjPrime₂ P)) := by
  unfold IsOver at h ⊢
  rw [h]
  ext r
  simp only [Ideal.mem_comap]
  set a := algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r
  set x := (RingOfIntegers.mapRingEquiv t.seam.iE).symm a
  have hxa : RingOfIntegers.mapRingEquiv t.seam.iE x = a := RingEquiv.apply_symm_apply _ _
  rw [← hxa, mem_seamP, mem_seamP, mem_conjP]
  have hc : cO t.X.E x = x := by
    refine RingOfIntegers.ext (t.seam.iE.injective ?_)
    change t.seam.iE (star (x : t.X.E)) = t.seam.iE (x : t.X.E)
    rw [t.seam_ok.2]
    change D.host.conj (algebraMap (𝓞 D.host.E) D.host.E (RingOfIntegers.mapRingEquiv t.seam.iE x)) = _
    rw [hxa, host_conj_F]
    exact (congrArg (algebraMap (𝓞 D.host.E) D.host.E) hxa).symm
  rw [hc]

theorem exists_underSB (t : KerEntTied ex) (μ : D.what₂.Tup) (P : HeightOneSpectrum (𝓞 t.X.E)) (k : Fin 2)
    (hk : ((t.Pr.g k : ℕ) : 𝓞 t.X.E) ∈ P.asIdeal) : ∃ v, UnderSB t μ v ∧ IsOver v (seamP t.seam P) := by
  classical
  have hPr := t.pr_ok
  let v : HeightOneSpectrum (𝓞 D.host.F) := (seamP t.seam P).under (𝓞 D.host.F)
  have hv : IsOver v (seamP t.seam P) := rfl
  refine ⟨v, ?_, hv⟩
  have h0 : t.X.conjO (t.Pr.piG k) ≠ 0 := by
    refine right_ne_zero_of_mul (a := t.Pr.piG k) ?_
    rw [hPr.piG_norm k]
    exact_mod_cast (hPr.g_prime k).ne_zero
  have hsub : ∀ Q, Q ∈ t.Pr.vG k → Q ∈ SB t μ := fun Q hQ => Finset.mem_union_left _ (by
    unfold Primes.vGs
    rw [Finset.mem_union]
    fin_cases k
    exacts [Or.inl hQ, Or.inr hQ])
  rw [← hPr.piG_norm k] at hk
  rcases P.isPrime.mem_or_mem hk with h | h
  · refine ⟨conjPrime₂ P, hsub _ ((Formalism.L2.Col.mem_divs h0 _).2 ?_), isOver_conjP t v P hv⟩
    rw [mem_conjP]
    exact (cO_cO (t.Pr.piG k)).symm ▸ h
  · exact ⟨P, hsub _ ((Formalism.L2.Col.mem_divs h0 _).2 h), hv⟩

end GlobalTheory.TwU.MuUnr

namespace GlobalTheory.TwU

open GlobalTheory.Mem.Col2 (afIso afIso_tmul_one mem_rInt_iff)
open GlobalTheory.TwU.MuUnr

end GlobalTheory.TwU
