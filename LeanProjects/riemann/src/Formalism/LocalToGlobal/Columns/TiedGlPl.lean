import Formalism.LocalToGlobal.Columns.TiedGlCore
import Formalism.LocalToGlobal.Columns.RecLevelHost

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.UG.P Formalism.L2.DIV
open Formalism.L2.Forms (kv redM)

section Ker

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : Formalism.BasicNotions.CMData F E)
  (v : HeightOneSpectrum (𝓞 F)) (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
  (halg : ∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a))

theorem glk_val_lt (x : v.adicCompletionIntegers F) (h : IsLocalRing.residue (v.adicCompletionIntegers F) x = 0) :
    Valued.v (x : v.adicCompletion F) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h
  have hle := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 x.2
  refine lt_of_le_of_ne hle fun h1 => h ?_
  have hx0 : (x : v.adicCompletion F) ≠ 0 := fun h0 => by rw [h0, map_zero] at h1; exact zero_ne_one h1
  let y : v.adicCompletionIntegers F := ⟨(x : v.adicCompletion F)⁻¹,
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).2 (by rw [map_inv₀, h1, inv_one])⟩
  have hxy : x * y = 1 := Subtype.ext (mul_inv_cancel₀ hx0)
  exact ⟨⟨x, y, hxy, (mul_comm _ _).trans hxy⟩, rfl⟩

theorem gloRho_oToS (a : 𝓞 E) : gloRho v spl halg (oToS F E a) = IsLocalRing.residue (v.adicCompletionIntegers F)
    ⟨gloPhi v spl (inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E a)), by
      have := gloPhi_int v spl halg _ (afsplit_prV_int v _ (oToS F E a).2)
      rwa [show ((oToS F E a : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) =
        inclE (F := F) (Formalism.L2.Herm.Af F) (algebraMap (𝓞 E) E a) from rfl, afsplit_prV_inclE] at this⟩ := by
  rw [gloRho_apply]
  congr 1

include hc in

theorem glk_ker (w : Pl E) (hov : IsOver v w) (ϖ : 𝓞 E) (h2 : cO E ϖ ∉ w.asIdeal)
    (hval : Valued.v (gloPhi v spl (inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E ϖ))) < 1) :
    ∀ a ∈ w.asIdeal, gloRho v spl halg (oToS F E a) = 0 := by
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact h2 (by rw [map_zero]; exact zero_mem _)
  have hϖ : gloRho v spl halg (oToS F E ϖ) = 0 := by
    rw [gloRho_oToS]
    exact glo_res_zero v _ hval
  let Q : Pl E :=
    { asIdeal := RingHom.ker ((gloRho v spl halg).comp (oToS F E))
      isPrime := RingHom.ker_isPrime _
      ne_bot := fun hb => hϖ0 (by
        have : ϖ ∈ RingHom.ker ((gloRho v spl halg).comp (oToS F E)) := hϖ
        rwa [hb, Ideal.mem_bot] at this) }
  have hQ : IsOver v Q := by
    show v.asIdeal = Q.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))
    ext r
    rw [Ideal.mem_comap]
    show r ∈ v.asIdeal ↔ gloRho v spl halg (oToS F E (algebraMap (𝓞 F) (𝓞 E) r)) = 0
    rw [gloRho_algMap]
    constructor
    · intro hr
      refine glo_res_zero v _ ?_
      show Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) < 1
      rw [csApprox_val_int]
      exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v r).2 hr
    · intro hr
      have := glk_val_lt v _ hr
      change Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) < 1 at this
      rw [csApprox_val_int] at this
      exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v r).1 this
  rcases rll_over_cases hc hov hQ with h | h
  · intro a ha
    have : a ∈ Q.asIdeal := by rw [h]; exact ha
    exact this
  · exfalso
    have : ϖ ∈ Q.asIdeal := hϖ
    rw [h, mem_conjP] at this
    exact h2 this

end Ker

section Pl

variable {X : Fields} {Pr : Primes X} (hc : Formalism.BasicNotions.CMData X.F X.E) (hPr : Pr.Ok)

structure GSplit where
  sp : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)), (Pr.g i : 𝓞 X.F) ∈ v.asIdeal →
    X.E ⊗[X.F] v.adicCompletion X.F ≃+* v.adicCompletion X.F × v.adicCompletion X.F
  sp_sig : ∀ i v h x, sp i v h (sigR hc.sig (v.adicCompletion X.F) x) = swapR _ (sp i v h x)
  sp_alg : ∀ i v h (a : v.adicCompletion X.F), sp i v h ((1 : X.E) ⊗ₜ[X.F] a) = (a, a)
  sp_pi : ∀ i v h, Valued.v (sp i v h (inclE (F := X.F) (v.adicCompletion X.F) (hc.sig (Pr.piG i : X.E)))).1 < 1

include hc hPr in
theorem glk_under (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)) : v ∈ plUnder X.F (Pr.vG i) ↔ (Pr.g i : 𝓞 X.F) ∈ v.asIdeal := by
  have hne : X.conjO (Pr.piG i) ≠ 0 := by
    intro h0
    have := hPr.piG_norm i
    rw [h0, mul_zero] at this
    exact (Nat.cast_ne_zero.2 (hPr.g_prime i).ne_zero) this.symm
  refine mem_plUnder_iff_norm hc (fun P => mem_divs hne P) (Pr.g i) ?_ v
  have h2 : cO X.E (X.conjO (Pr.piG i)) = Pr.piG i := RingOfIntegers.ext (star_star _)
  rw [h2, mul_comm]; exact hPr.piG_norm i

theorem glk_vG_le (i : Fin 2) {w : Pl X.E} (h : w ∈ Pr.vG i) : w ∈ Pr.vGs := by
  classical
  unfold Primes.vGs
  fin_cases i
  · exact Finset.mem_union_left _ h
  · exact Finset.mem_union_right _ h

def gwOf (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal) : Pr.vGs :=
  ⟨((glk_under hc hPr i v).2 h).choose, glk_vG_le i ((glk_under hc hPr i v).2 h).choose_spec.1⟩

theorem gwOf_mem (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal) :
    (gwOf hc hPr i v h).1 ∈ Pr.vG i := ((glk_under hc hPr i v).2 h).choose_spec.1

theorem gwOf_over (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal) :
    IsOver v (gwOf hc hPr i v h).1 := ((glk_under hc hPr i v).2 h).choose_spec.2

theorem gwOf_uniq (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal) (w' : Pr.vGs)
    (hw' : IsOver v w'.1) : w' = gwOf hc hPr i v h := by
  rcases rll_over_cases hc (gwOf_over hc hPr i v h) hw' with e | e
  · exact Subtype.ext e
  · exact absurd e (rlh_vGs_not_conj hPr (gwOf hc hPr i v h).2 w'.2)

variable {hc}

theorem GSplit.ker (S : GSplit (Pr := Pr) hc) (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal) :
    ∀ a ∈ (gwOf hc hPr i v h).1.asIdeal, gloRho v (S.sp i v h) (S.sp_alg i v h) (oToS X.F X.E a) = 0 := by
  refine glk_ker hc v (S.sp i v h) (S.sp_alg i v h) _ (gwOf_over hc hPr i v h) (X.conjO (Pr.piG i)) ?_ (S.sp_pi i v h)
  have h2 : cO X.E (X.conjO (Pr.piG i)) = Pr.piG i := RingOfIntegers.ext (star_star _)
  rw [h2]
  intro hmem
  have h3 : X.conjO (Pr.piG i) ∈ (gwOf hc hPr i v h).1.asIdeal := decoFin_mem_of_mem_divs (gwOf_mem hc hPr i v h)
  obtain ⟨a, b, e⟩ := hPr.piG_cop i
  apply one_notMem (gwOf hc hPr i v h).1
  rw [← e]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ h3)

def GSplit.eK (S : GSplit (Pr := Pr) hc) (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal) :
    kP (gwOf hc hPr i v h).1 ≃+* kv X.F v :=
  gloE v (S.sp i v h) (S.sp_alg i v h) _ (S.ker hPr i v h)

include hPr in

theorem GSplit.res_one (S : GSplit (Pr := Pr) hc) (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal)
    (ϖ : 𝓞 X.E) (hϖ : (Pr.g i : 𝓞 X.E) ∣ ϖ - 1) : gloRho v (S.sp i v h) (S.sp_alg i v h) (oToS X.F X.E ϖ) = 1 := by
  obtain ⟨s, hs⟩ := hϖ
  have hg : (Pr.g i : 𝓞 X.E) ∈ (gwOf hc hPr i v h).1.asIdeal := by
    have h1 : (Pr.g i : 𝓞 X.F) ∈ (gwOf hc hPr i v h).1.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) := (gwOf_over hc hPr i v h) ▸ h
    rwa [Ideal.mem_comap, map_natCast] at h1
  have h2 : ϖ = 1 + (Pr.g i : 𝓞 X.E) * s := by rw [← hs]; ring
  rw [h2, map_add, map_add, map_one, map_one, S.ker hPr i v h _ (Ideal.mul_mem_right _ _ hg), add_zero]

def GSplit.unitOf (S : GSplit (Pr := Pr) hc) (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal)
    (ϖ : 𝓞 X.E) (hϖ : (Pr.g i : 𝓞 X.E) ∣ ϖ - 1) : (v.adicCompletionIntegers X.F)ˣ :=
  IsUnit.unit (a := (⟨gloPhi v (S.sp i v h) (inclE (F := X.F) (v.adicCompletion X.F) (algebraMap (𝓞 X.E) X.E ϖ)), by
      have := gloPhi_int v (S.sp i v h) (S.sp_alg i v h) _ (afsplit_prV_int v _ (oToS X.F X.E ϖ).2)
      rwa [show ((oToS X.F X.E ϖ : Formalism.L2.Herm.intAf X.F X.E) : X.E ⊗[X.F] Formalism.L2.Herm.Af X.F) =
        inclE (F := X.F) (Formalism.L2.Herm.Af X.F) (algebraMap (𝓞 X.E) X.E ϖ) from rfl, afsplit_prV_inclE] at this⟩ :
      v.adicCompletionIntegers X.F)) (by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, ← gloRho_oToS v (S.sp i v h) (S.sp_alg i v h) ϖ,
      S.res_one hPr i v h ϖ hϖ]
    exact one_ne_zero)

theorem GSplit.unitOf_val (S : GSplit (Pr := Pr) hc) (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal)
    (ϖ : 𝓞 X.E) (hϖ : (Pr.g i : 𝓞 X.E) ∣ ϖ - 1) :
    ((S.unitOf hPr i v h ϖ hϖ : v.adicCompletionIntegers X.F) : v.adicCompletion X.F) =
      gloPhi v (S.sp i v h) (inclE (F := X.F) (v.adicCompletion X.F) (algebraMap (𝓞 X.E) X.E ϖ)) := rfl

theorem GSplit.unitOf_res (S : GSplit (Pr := Pr) hc) (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal)
    (ϖ : 𝓞 X.E) (hϖ : (Pr.g i : 𝓞 X.E) ∣ ϖ - 1) :
    IsLocalRing.residue (v.adicCompletionIntegers X.F) (S.unitOf hPr i v h ϖ hϖ) = 1 := by
  rw [← S.res_one hPr i v h ϖ hϖ, gloRho_oToS]
  rfl

include hPr in
theorem glk_piT_cong (u : Pr.Word) (i : Fin 2) : (Pr.g i : 𝓞 X.E) ∣ Pr.piT u - 1 := by
  refine Dvd.dvd.trans ?_ (hPr.piT_cong u)
  have : Pr.g i ∣ Pr.cond * (Pr.g 0 * Pr.g 1) ^ 2 := by
    refine Dvd.dvd.mul_left (Dvd.dvd.trans ?_ (dvd_pow_self _ two_ne_zero)) _
    fin_cases i
    · exact Dvd.intro _ rfl
    · exact Dvd.intro_left _ rfl
  exact Nat.cast_dvd_cast this

end Pl

end Formalism.L2.Col
