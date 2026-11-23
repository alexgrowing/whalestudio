import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.PlaceConjAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeVectorIffInverseDoubleCosets
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ConjSep

open NumberField IsDedekindDomain Matrix Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Classical

section SlopeTestRemainingChoices

open GlobalTheory.LFun
open Formalism.UG (IsUnifV Tj Ov diagJ GLint qV)

private theorem unif_exists {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    ∃ ϖ : w.adicCompletion E, IsUnifV E w ϖ := by
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer E
  refine ⟨algebraMap E _ π, ?_⟩
  have h1 : Valued.v (algebraMap E (w.adicCompletion E) π) = w.valuation E π :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w π
  rw [IsUnifV, h1, hπ]
  rfl

private theorem hecke_eq_sum {G : Type} [Group G] (K : Subgroup G) (h : G → ℂ) (h01 : ∀ g, h g ≠ 0 → h g = 1)
    (hfin : {q : G ⧸ K | h q.out ≠ 0}.Finite) : ∃ R : Finset G, (∀ g ∈ R, h g ≠ 0) ∧
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (x : V),
        heckeVec ρ K h x = ∑ g ∈ R, ρ g x := by
  refine ⟨hfin.toFinset.image Quotient.out, ?_, ?_⟩
  · intro g hg
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hg
    exact (Set.Finite.mem_toFinset hfin).1 hq
  · intro V _ _ ρ x
    rw [Finset.sum_image (fun a _ b _ e => Quotient.out_injective e)]
    have hsupp : (Function.support fun q : G ⧸ K => h q.out • ρ q.out x) ⊆ hfin.toFinset := by
      intro q hq
      simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
      intro h0
      exact hq (by simp [h0])
    have hsum : heckeVec ρ K h x = ∑ q ∈ hfin.toFinset, h q.out • ρ q.out x :=
      finsum_eq_sum_of_support_subset _ hsupp
    rw [hsum]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [h01 _ ((Set.Finite.mem_toFinset hfin).1 hq), one_smul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem comm_of_cLoc {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) (z : UA E n) (hz : cLoc w z = 1)
    (y : UA E n) (hy : y ∈ locU n w) : y * z = z * y := by
  have hyf := (Subgroup.mem_inf.1 hy).1
  have hyo := (Subgroup.mem_inf.1 hy).2
  have hc : z * y * z⁻¹ * y⁻¹ ∈ locU n w := by
    refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => ?_⟩
    · have h1 : cInf y = 1 := MonoidHom.mem_ker.1 hyf
      exact MonoidHom.mem_ker.2 (by simp [h1])
    · have h1 : cLoc u y = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hyo u) hu)
      exact MonoidHom.mem_ker.2 (by simp [h1])
  have h1 := GlobalTheory.SplitPts.eq_one_of_cLoc hw ⟨_, hc⟩ (by simp [hz])
  have h2 : z * y * z⁻¹ * y⁻¹ = 1 := congrArg Subtype.val h1
  exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h2)).symm

private noncomputable def repG {w : HeightOneSpectrum (𝓞 E)} (e : locU n w ≃ₜ* GL (Fin n) (w.adicCompletion E)) :
    Representation ℂ (GL (Fin n) (w.adicCompletion E)) (UA E n → ℂ) :=
  (RU E n).comp ((locU n w).subtype.comp e.symm.toMulEquiv.toMonoidHom)

private theorem satVec_of_mem {σ : Submodule ℂ (UA E n → ℂ)} (hσ : IsAutRepU σ) {w : HeightOneSpectrum (𝓞 E)}
    (hw : IsSplitAt w) (e : locU n w ≃ₜ* GL (Fin n) (w.adicCompletion E))
    (he : ∀ x : locU n w, e x = cLoc w (x : UA E n))
    (τ : SmIrr (GL (Fin n) (w.adicCompletion E))) {B : Multiset ℂˣ}
    (hc : IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ) (hB : HasSatGL w τ.ρ B)
    {φ : UA E n → ℂ} (hφ : φ ∈ σ) (hK : ∀ y ∈ locU n w, cLoc w y ∈ KGL w n → RU E n y φ = φ) (h0 : φ ≠ 0) :
    IsSatVecGL w (repG e) φ B := by
  obtain ⟨hirr, f, hf0, hfσ, hfe⟩ := hc
  have hpe : ∀ g, cLoc w ((e.symm g : locU n w) : UA E n) = g := fun g => by
    rw [← he, e.apply_symm_apply]
  have hrep : ∀ g, repG e g = RU E n ((e.symm g : locU n w) : UA E n) := fun g => rfl
  let C : Subgroup (UA E n) := Subgroup.centralizer (locU n w : Set (UA E n))
  let F : C → τ.V →ₗ[ℂ] (UA E n → ℂ) := fun c => (RU E n c.1) ∘ₗ f
  have hF : ∀ c v, F c v = RU E n c.1 (f v) := fun c v => rfl
  have hRm : ∀ (a b : UA E n) ψ, RU E n a (RU E n b ψ) = RU E n (a * b) ψ := fun a b ψ => by
    rw [map_mul]; rfl
  have hfg : ∀ g v, f (τ.ρ g v) = repG e g (f v) := fun g v => by
    have h1 := hfe (e.symm g) v
    rw [MonoidHom.comp_apply, Subgroup.subtype_apply, hpe] at h1
    exact h1
  have hFe : ∀ c g v, F c (τ.ρ g v) = repG e g (F c v) := by
    intro c g v
    rw [hF, hF, hfg, hrep, hRm, hRm]
    have hcomm := Subgroup.mem_centralizer_iff.1 c.2 _ (e.symm g).2
    rw [hcomm]
  let S : Submodule ℂ (UA E n → ℂ) := ⨆ c, LinearMap.range (F c)
  have hSσ : S ≤ σ := iSup_le fun c => by
    rintro _ ⟨v, rfl⟩
    exact hσ.stable _ _ (hfσ v)
  have hSst : ∀ x, ∀ ψ ∈ S, RU E n x ψ ∈ S := by
    intro x ψ hψ
    have hle : S ≤ S.comap (RU E n x) := iSup_le fun c => by
      rintro _ ⟨v, rfl⟩
      set g := cLoc w x with hg
      set x1 : UA E n := ((e.symm g : locU n w) : UA E n) with hx1
      have h2 : cLoc w (x1⁻¹ * x) = 1 := by
        rw [map_mul, map_inv, hx1, hpe, inv_mul_cancel]
      have hx2 : x1⁻¹ * x ∈ C := Subgroup.mem_centralizer_iff.2 fun y hy => comm_of_cLoc hw _ h2 y hy
      let c' : C := ⟨x1⁻¹ * x, hx2⟩ * c
      have e1 : F c' (τ.ρ g v) = RU E n x (F c v) := by
        have e2 : ((e.symm g : locU n w) : UA E n) * c'.1 = x * c.1 := by
          show x1 * (x1⁻¹ * x * c.1) = x * c.1
          group
        rw [hFe, hrep, hF, hF, hRm, hRm, e2]
      exact Submodule.mem_comap.2 (e1 ▸ Submodule.mem_iSup_of_mem c' ⟨_, rfl⟩)
    exact hle hψ
  have hS : S = σ := by
    refine (hσ.irred S hSσ hSst).resolve_left fun hb => hf0 ?_
    ext v : 1
    have h1 : F 1 v ∈ S := Submodule.mem_iSup_of_mem 1 ⟨v, rfl⟩
    rw [hb] at h1
    have h2 : F 1 v = f v := by
      rw [hF]; simp
    rw [← h2]
    simpa using h1
  have hφS : φ ∈ S := hS.symm ▸ hφ
  refine GlobalTheory.HeightCounting.Blocks.isSatVecGL_of_mem_iSup hirr hB F hFe hφS
    (GlobalTheory.LGrp.mem_fixed.2 fun k hk => hK _ (e.symm k).2 ?_) h0
  show cLoc w ((e.symm k : locU n w) : UA E n) ∈ KGL w n
  rw [hpe]
  exact hk

private theorem tj_one {L : Type} [Field L] {O : Subring L} {ϖ : L} {j : ℕ} (g : GL (Fin n) L)
    (hg : Tj ℂ n O ϖ j g ≠ 0) : Tj ℂ n O ϖ j g = 1 := by
  unfold Tj at hg ⊢
  exact Set.indicator_of_mem (Set.mem_of_indicator_ne_zero hg) _

private theorem glint_val {L : Type} [Field L] (O : Subring L) {m : ℕ} {M : GL (Fin m) L}
    (h : M ∈ GLint (Fin m) O) : (∀ i j, M.val i j ∈ O) ∧ (∀ i j, (M⁻¹).val i j ∈ O) := by
  obtain ⟨k, rfl⟩ := h
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · simp [Formalism.UG.bc]
  · rw [← map_inv]
    simp [Formalism.UG.bc]

private theorem det_mem {L : Type} [Field L] (O : Subring L) {m : ℕ} {M : Matrix (Fin m) (Fin m) L}
    (h : ∀ i j, M i j ∈ O) : M.det ∈ O := by
  rw [Matrix.det_apply']
  exact O.sum_mem fun σ _ => O.mul_mem (intCast_mem O _) (O.prod_mem fun i _ => h _ _)

private theorem mul_entries {L : Type} [Field L] (O : Subring L) {m : ℕ} {M N : Matrix (Fin m) (Fin m) L}
    (hM : ∀ i j, M i j ∈ O) (hN : ∀ i j, N i j ∈ O) : ∀ i j, (M * N) i j ∈ O := fun i j => by
  rw [Matrix.mul_apply]
  exact O.sum_mem fun k _ => O.mul_mem (hM _ _) (hN _ _)

private theorem v_of_mem {w : HeightOneSpectrum (𝓞 E)} {x : w.adicCompletion E} (h : x ∈ Ov E w) : Valued.v x ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).1 h

private theorem v_det_unit {w : HeightOneSpectrum (𝓞 E)} {a : GL (Fin n) (w.adicCompletion E)}
    (ha : a ∈ GLint (Fin n) (Ov E w)) : Valued.v a.val.det = 1 := by
  obtain ⟨h1, h2⟩ := glint_val _ ha
  have d1 := v_of_mem (det_mem _ h1)
  have d2 := v_of_mem (det_mem _ h2)
  have e : Valued.v a.val.det * Valued.v (a⁻¹).val.det = 1 := by
    rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel]
    simp
  refine le_antisymm d1 ?_
  calc (1 : _) = Valued.v a.val.det * Valued.v (a⁻¹).val.det := e.symm
    _ ≤ Valued.v a.val.det * 1 := by gcongr
    _ = _ := mul_one _

private theorem tj_int {w : HeightOneSpectrum (𝓞 E)} {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) {j : ℕ} (hj : j ≤ n)
    {g : GL (Fin n) (w.adicCompletion E)} (hg : Tj ℂ n (Ov E w) ϖ j g ≠ 0) :
    (∀ a b, Valued.v (g.val a b) ≤ 1) ∧ Valued.v g.val.det = WithZero.exp (-(j : ℤ)) := by
  obtain ⟨a, ha, b, hb, e⟩ := Set.mem_of_indicator_ne_zero hg
  have hϖO : ϖ ∈ Ov E w := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).2 (by
    rw [hϖ]; exact WithZero.coe_le_one.2 (by decide))
  have hD : ∀ i k, diagJ n ϖ j i k ∈ Ov E w := fun i k => by
    by_cases h : i = k
    · subst h
      rw [diagJ, Matrix.diagonal_apply_eq]
      split_ifs
      · exact hϖO
      · exact one_mem _
    · rw [diagJ, Matrix.diagonal_apply_ne _ h]
      exact zero_mem _
  refine ⟨fun i k => ?_, ?_⟩
  · rw [e]
    exact v_of_mem (mul_entries _ (mul_entries _ (glint_val _ ha).1 hD) (glint_val _ hb).1 i k)
  · have hdet : (diagJ n ϖ j).det = ϖ ^ j := by
      rw [diagJ, Matrix.det_diagonal, Finset.prod_ite]
      simp [Fin.card_filter_val_lt, hj]
    rw [e, Matrix.det_mul, Matrix.det_mul, map_mul, map_mul, v_det_unit ha, v_det_unit hb, hdet, map_pow, hϖ]
    rw [one_mul, mul_one, ← WithZero.coe_pow, ← ofAdd_nsmul]
    show _ = ((Multiplicative.ofAdd (-(j : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
    simp

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.Int.eigAll :
    UpperTheory.V.Z.Int.EigAll := by
  intro E _ _ _ n σ hσ w hw τ B hc hB
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E n w hw
  have hpe : ∀ g, cLoc w ((e.symm g : locU n w) : UA E n) = g := fun g => by
    rw [← he, e.apply_symm_apply]
  refine ⟨?_, hB.card, fun j hj => ?_⟩
  · obtain ⟨hirr, f, hf0, hfσ, hfe⟩ := hc
    obtain ⟨x, hx⟩ := hB.exists_vec
    have hker : LinearMap.ker f = ⊥ := ((GlobalTheory.CuspRep.isIrreducible_iff τ.ρ).1 hirr).2 _ (fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      have h1 := hfe (e.symm g) v
      rw [MonoidHom.comp_apply, Subgroup.subtype_apply, hpe] at h1
      rw [h1, hv, map_zero]) |>.resolve_right fun h => hf0 (LinearMap.ker_eq_top.1 h)
    refine ⟨f x, hfσ x, (map_ne_zero_iff f (LinearMap.ker_eq_bot.1 hker)).2 hx.1, fun y hy hk => ?_⟩
    have h2 := GlobalTheory.LGrp.mem_fixed.1 hx.2.1 _ hk
    have h1 := hfe ⟨y, hy⟩ x
    change f (τ.ρ (cLoc w y) x) = RU E n y (f x) at h1
    rw [h2] at h1
    exact h1.symm
  · obtain ⟨ϖ, hϖ⟩ := unif_exists w
    have hcm := Formalism.UG.Final.GLintComm E w n
    have hT := GlobalTheory.LFun.Tj_mem_hecke (n := n) hϖ j
    obtain ⟨R, hR, hRe⟩ := hecke_eq_sum (GlobalTheory.LFun.KGL w n) (Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j) tj_one
      (Formalism.UG.P.finite_support_cosets hcm hT.2)
    have hT' : Formalism.UG.FinDosetSupp (GlobalTheory.LFun.KGL w n) (fun g => Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j g⁻¹) := by
      obtain ⟨S, hS⟩ := hT.2
      refine ⟨S.image (·⁻¹), fun g hg => ?_⟩
      obtain ⟨s, hs, a, b, h⟩ := hS _ hg
      refine ⟨s⁻¹, Finset.mem_image_of_mem _ hs, b⁻¹, a⁻¹, ?_⟩
      rw [← inv_inv g, h]
      simp [mul_assoc]
    obtain ⟨R', hR', hRe'⟩ := hecke_eq_sum (GlobalTheory.LFun.KGL w n) (fun g => Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j g⁻¹)
      (fun g => tj_one _) (Formalism.UG.P.finite_support_cosets hcm hT')
    let lift : GL (Fin n) (w.adicCompletion E) → UA E n := fun g => ((e.symm g : locU n w) : UA E n)
    have hinj : Function.Injective lift := fun a b h => e.symm.injective (Subtype.ext h)
    have hq : (normV w : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (GlobalTheory.LFun.qV_ne_zero w)
    have hsc : ∀ B' : Multiset ℂˣ, (normV w : ℂ) ^ j.choose 2 * GlobalTheory.LFun.satEig (Formalism.UG.qV E w) n B' j =
        (algSat n (normV w) B').esymm j := fun B' => by
      rw [satEig_eq_algSat (GlobalTheory.LFun.qV_ne_zero w)]
      exact mul_inv_cancel_left₀ (pow_ne_zero _ hq) _
    refine ⟨R.image lift, R'.image lift, fun x hx => ?_, fun x hx => ?_, fun f hf hK => ?_⟩
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hx
      refine ⟨(e.symm g).2, ?_⟩
      show (∀ a b, Valued.v ((cLoc w ((e.symm g : locU n w) : UA E n)).val a b) ≤ 1) ∧
        Valued.v (cLoc w ((e.symm g : locU n w) : UA E n)).val.det = _
      rw [hpe]
      exact tj_int hϖ hj (hR g hg)
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hx
      refine ⟨(e.symm g).2, ?_⟩
      show (∀ a b, Valued.v ((cLoc w ((e.symm g : locU n w) : UA E n)⁻¹).val a b) ≤ 1) ∧
        Valued.v (cLoc w ((e.symm g : locU n w) : UA E n)⁻¹).val.det = _
      rw [map_inv, hpe]
      exact tj_int hϖ hj (hR' g hg)
    · by_cases f0 : f = 0
      · subst f0
        simp
      · have hs := satVec_of_mem hσ hw e he τ hc hB hf hK f0
        have h1 := hs.2.2.2 ϖ hϖ j hj
        have h2 := (GlobalTheory.ChainOnto.SatInv.satVec_iff_inv E w n _ (repG e) f B f0 hs.2.1 hs.2.2.1).1 hs ϖ hϖ j hj
        rw [hRe] at h1
        rw [hRe'] at h2
        constructor
        · rw [Finset.sum_image hinj.injOn, show ∑ x ∈ R, RU E n (lift x) f = _ from h1, smul_smul, hsc]
        · rw [Finset.sum_image hinj.injOn, show ∑ x ∈ R', RU E n (lift x) f = _ from h2, smul_smul, hsc]
