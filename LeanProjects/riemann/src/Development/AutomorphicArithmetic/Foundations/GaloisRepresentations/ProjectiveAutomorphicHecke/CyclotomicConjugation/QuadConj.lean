import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CyclotomicConjugation.QuadConjAlt
import GroundTheory.AutomorphicForms.StrongApproximationSLDense
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Conjugation

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open UpperTheory.Gal.CertificateRingHomMap UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂
open scoped NumberField.AdeleRing

noncomputable section
open GroundTheory.Global GroundTheory.Global.AdeleBaseChange
open scoped Classical
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem conj_alt_bis {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) : conjE E x = -x :=
  _root_.UpperTheory.Reformulated.B.CMConjugationOfSqrtNeg.conj_alt_bis hd hx

private theorem conj_conj' (a : E) : conjE E (conjE E a) = a := IsCMField.complexConj_apply_apply E a

private theorem conj_mem {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) (a : E)
    (ha : a ∈ IntermediateField.adjoin ℚ {x}) : conjE E a ∈ IntermediateField.adjoin ℚ {x} := by
  induction ha using IntermediateField.adjoin_induction with
  | mem a h =>
    rw [Set.mem_singleton_iff.1 h, conj_alt_bis hd hx]
    exact neg_mem (IntermediateField.mem_adjoin_simple_self ℚ x)
  | algebraMap q =>
    have : conjE E (algebraMap ℚ E q) = algebraMap ℚ E q := by simp
    rw [this]
    exact IntermediateField.algebraMap_mem _ q
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | inv a _ ha => rw [map_inv₀]; exact inv_mem ha
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

private def cK {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) : Kx x ≃ₐ[ℚ] Kx x :=
  let c0 : Kx x →ₐ[ℚ] Kx x :=
    { toFun := fun a => ⟨conjE E a, conj_mem hd hx a a.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp)
      commutes' := fun q => Subtype.ext (by
        change conjE E ((algebraMap ℚ (Kx x) q : Kx x) : E) = ((algebraMap ℚ (Kx x) q : Kx x) : E)
        simp) }
  AlgEquiv.ofAlgHom c0 c0 (AlgHom.ext fun a => Subtype.ext (conj_conj' _))
    (AlgHom.ext fun a => Subtype.ext (conj_conj' _))

private theorem cK_coe {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) (a : Kx x) :
    ((cK hd hx a : Kx x) : E) = conjE E a := rfl

private theorem aut_cases {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) (σ : Kx x ≃ₐ[ℚ] Kx x) :
    σ = 1 ∨ σ = cK hd hx := by
  have hmem : x ∈ IntermediateField.adjoin ℚ {x} := IntermediateField.mem_adjoin_simple_self ℚ x
  let xk : Kx x := ⟨x, hmem⟩
  have hxk : xk ^ 2 = algebraMap ℚ (Kx x) (-(d : ℚ)) := Subtype.ext (by
    change x ^ 2 = algebraMap ℚ E (-(d : ℚ))
    rw [hx]; simp)
  have hsq : (σ xk) ^ 2 = xk ^ 2 := by rw [← map_pow, hxk, AlgEquiv.commutes]
  have ext' : ∀ τ : Kx x ≃ₐ[ℚ] Kx x, σ xk = τ xk → σ = τ := fun τ h => by
    have : (σ : Kx x →ₐ[ℚ] Kx x) = (τ : Kx x →ₐ[ℚ] Kx x) := IntermediateField.adjoin_algHom_ext ℚ (by
      intro a ha
      obtain rfl : a = x := Set.mem_singleton_iff.1 ha
      exact h)
    exact AlgEquiv.coe_algHom_injective this
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
  · exact Or.inl (ext' 1 h)
  · refine Or.inr (ext' _ (h.trans (Subtype.ext ?_)))
    change -x = conjE E x
    rw [conj_alt_bis hd hx]

private theorem cK_ne {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) : cK hd hx ≠ 1 := by
  intro h
  have hmem : x ∈ IntermediateField.adjoin ℚ {x} := IntermediateField.mem_adjoin_simple_self ℚ x
  have h1 : conjE E x = x := congrArg (fun σ : Kx x ≃ₐ[ℚ] Kx x => ((σ ⟨x, hmem⟩ : Kx x) : E)) h
  rw [conj_alt_bis hd hx] at h1
  have h0 : x = 0 := by
    have : (2 : E) * x = 0 := by linear_combination -h1
    simpa using this
  rw [h0] at hx
  have : (d : E) = 0 := by simpa using hx.symm
  exact hd.ne' (by exact_mod_cast this)

private theorem finrank_K {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) :
    Module.finrank ℚ (Kx x) = 2 := by
  have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have hmonic : (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)).Monic := Polynomial.monic_X_pow_add_C _ (by norm_num)
  have hdeg : (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)).natDegree = 2 := Polynomial.natDegree_X_pow_add_C
  have hirr : Irreducible (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)) := by
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; simp) fun q hq => ?_
    have hd' : (0 : ℚ) < d := by exact_mod_cast hd
    simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hq
    nlinarith [sq_nonneg q]
  have hmin : Polynomial.X ^ 2 + Polynomial.C (d : ℚ) = minpoly ℚ x :=
    minpoly.eq_of_irreducible_of_monic hirr (by simp [hx]) hmonic
  have := IntermediateField.adjoin.finrank hint
  rw [← hmin, hdeg] at this
  exact this

private theorem univ_eq {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) :
    (Finset.univ : Finset (Kx x ≃ₐ[ℚ] Kx x)) = {1, cK hd hx} := by
  ext σ
  simpa using aut_cases hd hx σ

private theorem isGalois_K {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) : IsGalois ℚ (Kx x) := by
  refine IsGalois.of_card_aut_eq_finrank ℚ (Kx x) ?_
  rw [finrank_K hd hx, Nat.card_eq_fintype_card, ← Finset.card_univ, univ_eq hd hx, Finset.card_pair (cK_ne hd hx).symm]

private theorem conjFin_rat (a : Af ℚ) : conjFin (conjE E) (finiteAdeleMap ℚ E a) = finiteAdeleMap ℚ E a := by
  have h := (GroundTheory.Automorphic.AdelicGLn.denseRange_algebraMap_finiteAdeleRing ℚ).equalizer
    ((continuous_conjFin (conjE E)).comp continuous_finiteAdeleMap)
    (continuous_finiteAdeleMap (K := ℚ) (L := E)) (funext fun q => ?_)
  · exact congrFun h a
  · simp only [Function.comp_apply]
    rw [finiteAdeleMap_algebraMap, conjFin_algebraMap]
    simp

private theorem fin_conj {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) (y : 𝔸[Kx x]) :
    finiteAdeleMap (Kx x) E ((cK hd hx • y).2) = conjFin (conjE E) (finiteAdeleMap (Kx x) E y.2) := by
  let Φ : 𝔸[Kx x] →+* Af E := (finiteAdeleMap (Kx x) E).comp
    ((RingHom.snd _ _).comp (adeleRingEquiv ((cK hd hx : Kx x ≃ₐ[ℚ] Kx x) : Kx x ≃+* Kx x)).toRingHom)
  let Ψ : 𝔸[Kx x] →+* Af E := ((conjFin (conjE E)).comp (finiteAdeleMap (Kx x) E)).comp (RingHom.snd _ _)
  have h : Φ = Ψ := by
    refine adeleRingHom_ext_rat (fun l => ?_) (fun a => ?_)
    · change finiteAdeleMap (Kx x) E ((adeleRingEquiv ((cK hd hx : Kx x ≃ₐ[ℚ] Kx x) : Kx x ≃+* Kx x) (algebraMap (Kx x) 𝔸[Kx x] l)).2) =
        conjFin (conjE E) (finiteAdeleMap (Kx x) E ((algebraMap (Kx x) 𝔸[Kx x] l).2))
      rw [adeleRingEquiv_algebraMap]
      change finiteAdeleMap (Kx x) E (algebraMap (Kx x) (FiniteAdeleRing (𝓞 (Kx x)) (Kx x)) _) =
        conjFin (conjE E) (finiteAdeleMap (Kx x) E (algebraMap (Kx x) (FiniteAdeleRing (𝓞 (Kx x)) (Kx x)) l))
      rw [finiteAdeleMap_algebraMap, finiteAdeleMap_algebraMap, conjFin_algebraMap]
      rfl
    · change finiteAdeleMap (Kx x) E ((adeleRingEquiv ((cK hd hx : Kx x ≃ₐ[ℚ] Kx x) : Kx x ≃+* Kx x) (adeleMap ℚ (Kx x) a)).2) =
        conjFin (conjE E) (finiteAdeleMap (Kx x) E ((adeleMap ℚ (Kx x) a).2))
      rw [adeleRingEquiv_adeleMap_rat]
      change finiteAdeleMap (Kx x) E (finiteAdeleMap ℚ (Kx x) a.2) =
        conjFin (conjE E) (finiteAdeleMap (Kx x) E (finiteAdeleMap ℚ (Kx x) a.2))
      rw [finiteAdeleMap_finiteAdeleMap, conjFin_rat]
  exact congrArg (· y) h

theorem UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.quadConj :
    UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.QuadConj := by
  intro E _ _ _ d x hd hx z
  haveI := isGalois_K hd hx
  let y : IdeleGroup (Kx x) := Units.map (MonoidHom.inr (InfiniteAdeleRing (Kx x)) (FiniteAdeleRing (𝓞 (Kx x)) (Kx x))) z
  have h1 := ideleEmbedding_ideleNorm (K := ℚ) y
  have h2 : (∏ σ : Kx x ≃ₐ[ℚ] Kx x, σ • y) = y * cK hd hx • y := by
    rw [univ_eq hd hx, Finset.prod_pair (cK_ne hd hx).symm, one_smul]
  rw [h2] at h1
  have h3 := congrArg (fun u : IdeleGroup (Kx x) => ((u : 𝔸[Kx x]).2)) h1
  have h4 : finiteAdeleMap ℚ (Kx x) ((fN ℚ (Kx x) z : (Af ℚ)ˣ) : Af ℚ) =
      (z : Af (Kx x)) * ((cK hd hx • (y : 𝔸[Kx x])).2) := h3
  have h5 := congrArg (finiteAdeleMap (Kx x) E) h4
  rw [finiteAdeleMap_finiteAdeleMap, map_mul, fin_conj] at h5
  exact h5.symm

end
