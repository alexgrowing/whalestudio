import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CsdSsOfFull
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.WdChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ArtinEl
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.NuChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.PairRel
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwJqEmbed
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwTamePair
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep

open Polynomial in
private theorem trace_of_charpoly {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → ℂ)
    (h : M.charpoly = ∏ i, (X - C (c i))) : M.trace = ∑ i, c i := by
  have hr : M.charpoly.roots = Finset.univ.val.map c := by
    rw [h, Finset.prod_eq_multiset_prod, ← roots_multiset_prod_X_sub_C (Finset.univ.val.map c), Multiset.map_map]
    rfl
  rw [Matrix.trace_eq_sum_roots_charpoly, hr]
  rfl

open Polynomial in
private theorem rel_of_chars {W : Type} [Group W] {n q : ℕ} (hq : 2 ≤ q) (R : W →* GL (Fin n) ℂ) (c : Fin n → W →* ℂ)
    (h : ∀ g, (R g : Matrix (Fin n) (Fin n) ℂ).charpoly = ∏ i, (X - C (c i g))) (f t : W)
    (h1 : R ((t ^ q)⁻¹ * (f⁻¹ * t * f)) = 1) (h2 : ∀ i, c i ((t ^ q)⁻¹ * (f⁻¹ * t * f)) = 1)
    (h3 : ∀ i i', i ≠ i' → c i f ≠ c i' f ∧ c i f ≠ (q : ℂ) * c i' f) (i : Fin n) :
    (List.ofFn fun i' => if i' = i then 1 else (R f : Matrix (Fin n) (Fin n) ℂ) - c i' f • (1 : Matrix (Fin n) (Fin n) ℂ)).prod *
      ((R t : Matrix (Fin n) (Fin n) ℂ) - c i t • (1 : Matrix (Fin n) (Fin n) ℂ)) = 0 := by
  have hinv : ∀ i g, c i g⁻¹ * c i g = 1 := fun i g => by rw [← map_mul, inv_mul_cancel, map_one]
  have hne : ∀ i g, c i g ≠ 0 := fun i g h0 => by simpa [h0] using hinv i g
  have hR : R f⁻¹ * R t * (R f⁻¹)⁻¹ = R t ^ q := by
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    rw [← map_pow, h1]
    simp
  have hc : ∀ i, c i (t ^ (q - 1)) = 1 := fun i => by
    have e1 : c i (f⁻¹ * t * f) = c i t := by
      rw [map_mul, map_mul, mul_right_comm, hinv, one_mul]
    have e2 : c i (t ^ q) = c i t := by
      have := h2 i
      rw [map_mul, e1, ← hinv i (t ^ q)] at this
      exact (mul_left_cancel₀ (hne _ _) this).symm
    have e3 : t ^ q = t ^ (q - 1) * t := by rw [← pow_succ]; congr 1; omega
    rw [e3, map_mul] at e2
    exact mul_right_cancel₀ (hne i t) (e2.trans (one_mul _).symm)
  have hN : IsNilpotent (((R t ^ (q - 1) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) - 1) := by
    refine ⟨n, ?_⟩
    have := Matrix.aeval_self_charpoly (R (t ^ (q - 1)) : Matrix (Fin n) (Fin n) ℂ)
    rw [h] at this
    simpa [hc] using this
  have ha : ∀ i j, c i f⁻¹ ≠ (q : ℂ) * c j f⁻¹ := fun i j e => by
    have e' : c j f = (q : ℂ) * c i f := by
      have a1 := hinv i f
      have a2 := hinv j f
      linear_combination (c j f * c i f) * e - c j f * a1 + q * c i f * a2
    by_cases hij : j = i
    · subst hij
      have : (1 : ℂ) = q := mul_right_cancel₀ (hne j f) ((one_mul _).trans e')
      have : 1 = q := by exact_mod_cast this
      omega
    · exact (h3 j i hij).2 e'
  have hcm := (tamePair ℂ n q (R f⁻¹) (R t) (fun i => c i f⁻¹) hq hR (h _) ha hN).2
  have hcm' : R f * R t = R t * R f := by
    rw [map_inv] at hcm
    exact (Commute.inv_left_iff.1 hcm : Commute (R f) (R t))
  refine pairRel ℂ n _ _ (fun i => c i f) (fun i => c i t) (fun i j e => ?_) ?_ (h f) (fun a => ?_) i
  · by_contra hij
    exact (h3 i j hij).1 e
  · rw [← Units.val_mul, hcm', Units.val_mul]
  · rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← map_pow, ← map_mul, trace_of_charpoly _ _ (h _)]
    simp

private theorem chi_unit {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (ψ : Fin n → kˣ →* ℂˣ) (χ : (Fin n → kˣ) →* ℂˣ)
    (hχ : torusChar ψ = χ * ((deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom))
    (i : Fin n) (u : kˣ) (hu : ord k u = 0) (h1 : ψ i u = 1) : χ (Pi.mulSingle i u) = 1 := by
  have e1 : torusChar ψ (Pi.mulSingle i u) = ψ i u := by
    rw [torusChar_apply, Finset.prod_eq_single i, Pi.mulSingle_eq_same]
    · intro j _ hj
      rw [Pi.mulSingle_eq_of_ne hj, map_one]
    · simp
  have hd : ∀ (t : Fin n → kˣ) j, Matrix.GeneralLinearGroup.det (leviTorus k (Fin n) t j) = t j := fun t =>
    congrFun ((leviTorus k (Fin n)).left_inv t)
  have e2 : deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) (Pi.mulSingle i u)) = 1 := by
    rw [deltaHalf_apply, Finset.prod_eq_single i, hd, Pi.mulSingle_eq_same]
    · refine Units.ext ?_
      rw [val_absPow, GlobalTheory.LGrp.nabs_eq_zpow, hu]
      simp
    · intro j _ hj
      rw [hd, Pi.mulSingle_eq_of_ne hj, map_one]
    · simp
  rw [hχ, h1, MonoidHom.mul_apply, MonoidHom.comp_apply] at e1
  erw [e2] at e1
  simpa using e1

theorem UpperTheory.V.Pa.Lev.locData :
    LocP → ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (Bq : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (hB : IsPlaceOver Bq w), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ fr τ : G E Ω, fr ∈ Dec (F := E) Bq → IsFrob (F := E) Bq (normV w) fr⁻¹ → GlobalTheory.TameQuot.IsProGen E Bq l τ → resCard (w.adicCompletion E) = normV w ∧ ∃ x δ : (w.adicCompletion E)ˣ, IsUnif x ∧ IsGenMod _ (ellC l _) δ ∧ ∀ (n : ℕ) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin n) (Qbar l)) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))), (∀ rc : IrrGL (w.adicCompletion E) → WD hB, IsRec hB rc → UpperTheory.V.Lev.WO ι r (rc (algNorm σ))) → LocRel l x δ σ.ρ ((r fr : Matrix (Fin n) (Fin n) (Qbar l)).map ι) ((r τ : Matrix (Fin n) (Fin n) (Qbar l)).map ι) := by
  intro hP l _ E Ω _ _ _ _ _ Bq w hB hl fr τ hfr hF hτ
  obtain ⟨rc, hrc, -⟩ := hP.ll.1 E Ω Bq w hB
  obtain ⟨a, ha, ε, -, L⟩ := id hrc
  obtain ⟨hq, h1, h2, hx, hδ, hk, hrel⟩ := artinEl hP.tame l E Ω Bq w hB hl a ha fr τ hfr hF hτ
  refine ⟨hq, _, _, hx, hδ, fun n ι r σ H C hC θ hθ χ hχ α hα => ?_⟩
  obtain ⟨ψ, hψ, hψC, hψχ, hsub⟩ := jqEmbed hP.bz _ n C σ.V σ.ρ σ.smooth σ.irred θ hθ χ hχ
  have hν := nuChar l E Ω Bq w hB hl a ha ε rc L n σ ψ χ hψ hψχ hsub
  obtain ⟨hw1, hw2⟩ := wdChar l E Ω Bq w hB hl n ι r _ (H rc hrc)
  have hq2 : 2 ≤ resCard (w.adicCompletion E) := Finite.one_lt_card (α := 𝓀[w.adicCompletion E])
  have hq0 : (resCard (w.adicCompletion E) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  let c : Fin n → Weil hB →* ℂ := fun i =>
    { toFun := fun g => (resCard (w.adicCompletion E) : ℂ) ^ (((i : ℕ) : ℤ) * ord (w.adicCompletion E) (a g)) *
        (χ (Pi.mulSingle i (a g)) : ℂ)
      map_one' := by
        rw [map_one, Pi.mulSingle_one, map_one, ord_eq_zero (by simp)]
        simp
      map_mul' := fun g g' => by
        rw [map_mul, ord_mul, Pi.mulSingle_mul, map_mul, mul_add, zpow_add₀ hq0, Units.val_mul]
        ring }
  let R : Weil hB →* GL (Fin n) ℂ :=
    ((Matrix.GeneralLinearGroup.map ι.toRingHom).comp r).comp (Weil hB).subtype
  have hR : ∀ g, (R g : Matrix (Fin n) (Fin n) ℂ).charpoly = ∏ i, (Polynomial.X - Polynomial.C (c i g)) :=
    fun g => (hw1 g).trans (hν g)
  have hord : ∀ g : Weil hB, (g : G E Ω) ∈ Ine (F := E) Bq → ord (w.adicCompletion E) (a g) = 0 := fun g hg => by
    rw [ha.ord_eq, deg_eq_zero_iff.2 hg, neg_zero]
  have hf : ∀ i, α i = c i ⟨fr, h1⟩ := fun i => by
    have e : ord (w.adicCompletion E) (a ⟨fr, h1⟩) = 1 := by
      have h2 : deg (⟨fr, h1⟩ : Weil hB)⁻¹ = 1 := deg_eq_one_iff.2 hF
      rw [ha.ord_eq, ← deg_inv, h2]
    rw [hα]
    change _ = (resCard (w.adicCompletion E) : ℂ) ^ (((i : ℕ) : ℤ) * ord (w.adicCompletion E) (a ⟨fr, h1⟩)) * _
    rw [e, mul_one, zpow_natCast]
  have ht : ∀ i, (χ (Pi.mulSingle i (a ⟨τ, h2⟩)) : ℂ) = c i ⟨τ, h2⟩ := fun i => by
    change _ = (resCard (w.adicCompletion E) : ℂ) ^ (((i : ℕ) : ℤ) * ord (w.adicCompletion E) (a ⟨τ, h2⟩)) * _
    rw [hord _ hτ.1, mul_zero, zpow_zero, one_mul]
  obtain rfl : α = fun i => c i ⟨fr, h1⟩ := funext hf
  refine ⟨hR ⟨fr, h1⟩, fun hgen i => ?_⟩
  rw [ht]
  set g : Weil hB := ((⟨τ, h2⟩ : Weil hB) ^ resCard (w.adicCompletion E))⁻¹ *
    ((⟨fr, h1⟩ : Weil hB)⁻¹ * ⟨τ, h2⟩ * ⟨fr, h1⟩) with hg
  have hgk : (g : G E Ω) ∈ GlobalTheory.TameQuot.ineKer E Bq l := by
    rw [← hq] at hrel
    exact hrel
  have hcg : ∀ i, c i g = 1 := fun i => by
    have e := hord g (GlobalTheory.TameQuot.ineKer_le_Ine Bq l hgk)
    have e2 : a g ∈ unitsC _ C := Subgroup.map_mono (Subgroup.comap_mono hC) (hk g g.2 hgk)
    change (resCard (w.adicCompletion E) : ℂ) ^ (((i : ℕ) : ℤ) * ord (w.adicCompletion E) (a g)) *
      (χ (Pi.mulSingle i (a g)) : ℂ) = 1
    rw [e, chi_unit ψ χ hψχ i _ e (hψC i _ e2)]
    simp
  have hRg : R g = 1 := by
    have e : r g = 1 := hw2 g hgk (((hw1 g).trans (hν g)).trans (by
      change ∏ i, (Polynomial.X - Polynomial.C (c i g)) = _
      simp [hcg]))
    change Matrix.GeneralLinearGroup.map ι.toRingHom (r g) = 1
    rw [e, map_one]
  exact rel_of_chars hq2 R c hR ⟨fr, h1⟩ ⟨τ, h2⟩ hRg hcg hgen i
