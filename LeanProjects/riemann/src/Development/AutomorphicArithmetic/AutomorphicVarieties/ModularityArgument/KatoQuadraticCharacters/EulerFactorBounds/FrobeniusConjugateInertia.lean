import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SPushPsi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.FrobeniusConjugateInertia.FrobConjIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SInteg
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.DetChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.DiamChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.DiamEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.EsOf

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

namespace UpperTheory.V.Z.Kato.Nb.EulerSystemNorms

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]

private theorem cont_bar : Continuous (cycBar ℚ Ω l) :=
  (Continuous.units_map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom
    ((continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ ℚ Ω l)

private theorem cont_hom {M : Type} [Monoid M] [TopologicalSpace M] (f : G ℚ Ω →* Mˣ) (h : Continuous fun s => (f s : M)) :
    Continuous f :=
  Units.continuous_iff.2 ⟨h, (h.comp continuous_inv).congr fun s => by simp⟩

private theorem cont_cls [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (δ : (ZMod N)ˣ → Qbar l) :
    Continuous fun s => δ (Chr.cls ℚ Ω N s) := by
  refine (IsLocallyConstant.comp ((IsLocallyConstant.iff_exists_open _).2 fun s => ?_) δ).continuous
  refine ⟨(fun t => s⁻¹ * t) ⁻¹' ((Chr.cls ℚ Ω N).ker : Set (G ℚ Ω)),
    (Chr.clsFacts ℚ Ω N).1.preimage (continuous_const.mul continuous_id), by simp, fun t ht => ?_⟩
  have h : Chr.cls ℚ Ω N (s⁻¹ * t) = 1 := ht
  rw [map_mul, map_inv, inv_mul_eq_one] at h
  exact h.symm

private theorem trace_eq {k : Type} [Field k] (g : GL (Fin 2) k) (a : k)
    (h : (g : Matrix (Fin 2) (Fin 2) k) ^ 2 - a • (g : Matrix (Fin 2) (Fin 2) k) + (g : Matrix (Fin 2) (Fin 2) k).det • 1 = 0) :
    (g : Matrix (Fin 2) (Fin 2) k).trace = a := by
  have hd : (g : Matrix (Fin 2) (Fin 2) k).det ≠ 0 := (Matrix.isUnits_det_units g).ne_zero
  generalize (g : Matrix (Fin 2) (Fin 2) k) = m at h hd
  have e := fun i j => congrFun (congrFun h i) j
  have e00 := e 0 0
  have e01 := e 0 1
  simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] at e00 e01
  rw [Matrix.det_fin_two] at hd
  rw [Matrix.trace_fin_two]
  have e10 := e 1 0
  have e11 := e 1 1
  simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] at e10 e11
  apply mul_right_cancel₀ hd
  linear_combination m 1 1 * e00 - m 1 0 * e01

private theorem stable_top {W : R2 Ω l} (h : IsIrr (W.comp (H0g W).subtype)) (U : Submodule (Qbar l) (Fin 2 → Qbar l))
    (h0 : U ≠ ⊥) (hU : ∀ s, ∀ v ∈ U, mat W s *ᵥ v ∈ U) : U = ⊤ :=
  (h.2.2 U le_top fun s v hv => hU s v hv).resolve_left h0

private theorem not_scalar {W : R2 Ω l} (h : IsIrr (W.comp (H0g W).subtype)) : ∃ s, ∀ t : Qbar l, mat W s ≠ t • 1 := by
  by_contra hn
  push Not at hn
  have h1 := stable_top h (Submodule.span (Qbar l) {![1, 0]}) (by simp) fun s v hv => by
    obtain ⟨t, ht⟩ := hn s
    rw [ht, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact Submodule.smul_mem _ _ hv
  have h2 : (![0, 1] : Fin 2 → Qbar l) ∈ Submodule.span (Qbar l) {(![1, 0] : Fin 2 → Qbar l)} := h1 ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h2
  simpa using congrFun hc 1

private theorem inv_mem (cf : Coef l) {q : ℕ} (h : Nat.Coprime q l) : ((q : Qbar l))⁻¹ ∈ cf.O := by
  have hu : IsUnit (q : ℤ_[l]) := PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2 h.symm)
  obtain ⟨y, hy⟩ := hu.exists_right_inv
  have e := congrArg (algebraMap ℤ_[l] (Qbar l)) hy
  rw [map_mul, map_natCast, map_one] at e
  rw [← eq_inv_of_mul_eq_one_right e]
  exact cf.O.algebraMap_mem y

end UpperTheory.V.Z.Kato.Nb.EulerSystemNorms

open UpperTheory.V.Z.Kato.Nb.EulerSystemNorms in
theorem UpperTheory.V.Z.Kato.Nb.sEuler :
    UpperTheory.V.Z.Kato.Nb.SEuler := by
  intro l _ Ω _ _ _ ι e gN A W ε X pr N _ x c d gm ψ cf hA he hlN S hNf hint
  obtain ⟨-, -, -, -, hO, -, -⟩ := sInteg l Ω ι e gN A W ε X pr N x c d gm ψ cf hA he hint
  have hD := sDiamChar l Ω ι e gN A W ε X pr N x c d gm ψ cf hA he hlN
  obtain ⟨hc, hd, -, -, hadd, hsm, -, hgal, ⟨δ', hT⟩, -, -, χ₀, -, -, hχ⟩ := hA
  have hl : l.Prime := Fact.out
  have hN : 0 < N := NeZero.pos N
  obtain ⟨S0, hES⟩ := sEs l Ω ε X hNf.l_odd N (2 * e - 1) hN
  let ρ : R2 Ω l := tw W (cycBar ℚ Ω l ^ e * χ₀⁻¹)
  have hρ : ∀ s, mat ρ s = rhoK W e ψ s := fun s => by
    rw [mat, tw_val, rhoK, thK, ← hχ]
    simp [mul_comm]
  have hn0 : l * N * c * d ≠ 0 := by
    have := hl.pos
    positivity
  have key : ∀ w : Pl, w ∉ S → normV w ∉ S0 → Nat.Coprime (normV w) (l * N) → ∃ a δ : Qbar l,
      (∀ b ∈ X.B N l (2 * e - 1), pr (X.heckeT N l (normV w) b) = a • pr b ∧ pr (X.diam N l (normV w) b) = δ • pr b) ∧
      ∀ (B : ValuationSubring Ω) (σ : G ℚ Ω), IsPlaceOver B w → IsFrob B (normV w) σ →
        (rhoK W e ψ σ).trace = a ∧ (rhoK W e ψ σ).det = (normV w : Qbar l) ^ (2 * e) * δ := by
    by_cases hz : ∃ b ∈ X.B N l (2 * e - 1), pr b ≠ 0
    · obtain ⟨δ, hδ⟩ := hD hz
      let χ : G ℚ Ω →* (Qbar l)ˣ := cycBar ℚ Ω l ^ (2 * e) * δ.comp (Chr.cls ℚ Ω N)
      have hspan : Submodule.span (Qbar l) (pr '' (X.B N l (2 * e - 1) : Set (X.Fn l))) = ⊤ := by
        refine stable_top hNf.irr _ (fun h => ?_) fun s v hv => ?_
        · obtain ⟨b, hb, hb0⟩ := hz
          exact hb0 ((Submodule.span_eq_bot.1 h) _ ⟨b, hb, rfl⟩)
        · have h1 : mat W s = ((cycBar ℚ Ω l ^ e * χ₀⁻¹) s⁻¹ : Qbar l) • mat ρ s := by
            rw [mat, mat, tw_val, smul_smul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_smul]
          rw [h1, Matrix.smul_mulVec]
          refine Submodule.smul_mem _ _ ?_
          refine (Submodule.span_le (p := (Submodule.span (Qbar l) (pr '' (X.B N l (2 * e - 1) : Set (X.Fn l)))).comap
            (Matrix.mulVecLin (mat ρ s)))).2 ?_ hv
          rintro _ ⟨b, hb, rfl⟩
          refine Submodule.subset_span ⟨_, (sBStab Ω ε X l N _ hN b hb).1 s, ?_⟩
          rw [hgal s b hb, ← hρ]
          rfl
      have hχF : ∀ (w : Pl), Nat.Coprime (normV w) (l * N) → ∀ (B : ValuationSubring Ω) (σ : G ℚ Ω), IsPlaceOver B w →
          IsFrob B (normV w) σ → (χ σ : Qbar l) = (normV w : Qbar l) ^ (2 * e) * δ (Chr.cls ℚ Ω N σ) := fun w hw B σ hB hσ => by
        rw [← eps_frobAt l ((normV_prime w).coprime_iff_not_dvd.1 hw.coprime_mul_right_right) hB hσ]
        simp [χ]
      have hrel : ∀ (w : Pl), normV w ∉ S0 → Nat.Coprime (normV w) (l * N) → ∀ (B : ValuationSubring Ω) (σ : G ℚ Ω),
          IsPlaceOver B w → IsFrob B (normV w) σ →
          mat ρ σ ^ 2 - ι.symm (gN.a (normV w)) • mat ρ σ + (χ σ : Qbar l) • 1 = 0 := fun w hw0 hw B σ hB hσ => by
        have hnd := (normV_prime w).coprime_iff_not_dvd.1 hw
        have h1 : Matrix.mulVecLin (mat ρ σ - ι.symm (gN.a (normV w)) • 1 + (χ σ : Qbar l) • mat ρ σ⁻¹) = 0 := by
          refine LinearMap.ext_on hspan ?_
          rintro _ ⟨b, hb, rfl⟩
          have hb' := (sBStab Ω ε X l N _ hN b hb).1 σ⁻¹
          have h2 := congrArg pr (hES w B σ hw0 (normV_prime w) hB hσ b hb)
          rw [(hT _ (normV_prime w) hnd b hb).1, hadd, hsm, hgal σ b hb,
            hδ _ _ (normV_prime w) hnd (cls_frobAt N hw.coprime_mul_left_right.symm hB hσ) _ hb', hgal _ b hb, smul_smul,
            show 2 * e - 1 + 1 = 2 * e by omega, ← hρ, ← hρ] at h2
          rw [hχF w hw B σ hB hσ, Matrix.mulVecLin_apply, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
            Matrix.smul_mulVec, Matrix.one_mulVec, h2]
          simp
        have h3 : mat ρ σ - ι.symm (gN.a (normV w)) • 1 + (χ σ : Qbar l) • mat ρ σ⁻¹ = 0 :=
          Matrix.toLin'.injective (h1.trans (map_zero _).symm)
        have h4 := congrArg (· * mat ρ σ) h3
        simp only [add_mul, sub_mul, smul_mul_assoc, one_mul, zero_mul, mat, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
          Units.val_one] at h4
        rw [pow_two, mat, ← Units.val_mul, ← map_mul]
        exact h4
      have hc0 : Continuous fun s => (χ₀ s : Qbar l) := by
        simp only [hχ]
        exact ((GlobalTheory.KZ.IwC.isLocallyConstant_cycMod 1).comp fun u : (ZMod (l ^ 1))ˣ => ψ (((u : ZMod (l ^ 1)).val : ℕ) : ZMod l)).continuous
      have hcρ : Continuous ρ := cont_hom _ (by
        simp only [ρ, tw_val]
        exact (Units.continuous_val.comp ((cont_bar.pow e).mul (cont_hom χ₀ hc0).inv)).smul (Units.continuous_val.comp hNf.cont))
      have hcχ : Continuous χ := (cont_bar.pow (2 * e)).mul (cont_hom (δ.comp (Chr.cls ℚ Ω N)) (cont_cls (Ω := Ω) N fun u => (δ u : Qbar l)))
      have hdet := sDetChar l Ω ρ χ hcρ hcχ (by
        obtain ⟨s, hs⟩ := not_scalar hNf.irr
        refine ⟨s, fun t ht => hs (((cycBar ℚ Ω l ^ e * χ₀⁻¹) s : Qbar l)⁻¹ * t) ?_⟩
        rw [mul_smul, ← ht, tw_val, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]) (S0 ∪ (l * N).primeFactors)
        fun v B σ hv hB hσ => ⟨_, hrel v (fun h => hv (Finset.mem_union_left _ h))
          ((normV_prime v).coprime_iff_not_dvd.2 fun h => hv (Finset.mem_union_right _
            (Nat.mem_primeFactors.2 ⟨normV_prime v, h, (mul_pos hl.pos hN).ne'⟩))) B σ hB hσ⟩
      intro w _ hw0 hw
      have hnd := (normV_prime w).coprime_iff_not_dvd.1 hw
      refine ⟨ι.symm (gN.a (normV w)), δ (ZMod.unitOfCoprime _ hw.coprime_mul_left_right), fun b hb =>
        ⟨(hT _ (normV_prime w) hnd b hb).1, hδ _ _ (normV_prime w) hnd (ZMod.coe_unitOfCoprime _ _) b hb⟩, fun B σ hB hσ => ?_⟩
      rw [← hρ]
      refine ⟨trace_eq _ _ (by rw [hdet]; exact hrel w hw0 hw B σ hB hσ), ?_⟩
      rw [hdet, hχF w hw B σ hB hσ]
      congr 3
      exact Units.ext ((cls_frobAt N hw.coprime_mul_left_right.symm hB hσ).trans (ZMod.coe_unitOfCoprime _ _).symm)
    · push Not at hz
      intro w hwS _ hw
      have hnd := (normV_prime w).coprime_iff_not_dvd.1 hw
      have hnl := (normV_prime w).coprime_iff_not_dvd.1 hw.coprime_mul_right_right
      have hq : ((normV w : ℕ) : Qbar l) ^ (2 * e) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (normV_prime w).ne_zero)
      obtain ⟨B₀, σ₀, hB₀, hσ₀⟩ := exists_frobAt Ω w
      refine ⟨(rhoK W e ψ σ₀).trace, (((normV w : ℕ) : Qbar l) ^ (2 * e))⁻¹ * (rhoK W e ψ σ₀).det, fun b hb => ?_,
        fun B σ hB hσ => ?_⟩
      · rw [(hT _ (normV_prime w) hnd b hb).1, (hT _ (normV_prime w) hnd b hb).2, hz b hb]
        simp
      · have hm := fun h => hnl ((mem_place_iff w l).1 h)
        have h1 : cycZ ℚ Ω l σ = cycZ ℚ Ω l σ₀ := Units.ext ((cycZ_of_isFrob hm hB hσ).trans (cycZ_of_isFrob hm hB₀ hσ₀).symm)
        have h2 : thK l e ψ σ = thK l e ψ σ₀ := by
          simp only [thK, eps, cycBar, cycMod, MonoidHom.comp_apply, h1]
        obtain ⟨h3, h4⟩ := frobInv hNf hwS hB hσ hB₀ hσ₀
        rw [mul_inv_cancel_left₀ hq]
        simp only [rhoK, Matrix.trace_smul, Matrix.det_smul, h2, h3, h4, and_self]
  refine ⟨S ∪ ((finite_normV S0).union (finite_dvd hn0)).toFinset, Finset.subset_union_left, fun w hw => ?_⟩
  simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq, not_or] at hw
  have hcop := (normV_prime w).coprime_iff_not_dvd.2 hw.2.2
  have hw' : Nat.Coprime (normV w) (l * N) := hcop.coprime_mul_right_right.coprime_mul_right_right
  obtain ⟨a, δ, h1, h2⟩ := key w hw.1 hw.2.1 hw'
  obtain ⟨B₀, σ₀, hB₀, hσ₀⟩ := exists_frobAt Ω w
  obtain ⟨h3, h4⟩ := h2 B₀ σ₀ hB₀ hσ₀
  have hq : ((normV w : ℕ) : Qbar l) ^ (2 * e) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (normV_prime w).ne_zero)
  refine ⟨normV_prime w, hcop, a, δ, ?_, ?_, h1, fun B σ hB hσ =>
    ⟨eps_frobAt l ((normV_prime w).coprime_iff_not_dvd.1 hw'.coprime_mul_right_right) hB hσ, h2 B σ hB hσ⟩⟩
  · rw [← h3, Matrix.trace_fin_two]
    exact add_mem (hO _ _ _) (hO _ _ _)
  · rw [← inv_mul_cancel_left₀ hq δ, ← h4, ← inv_pow, Matrix.det_fin_two]
    exact mul_mem (pow_mem (inv_mem cf hw'.coprime_mul_right_right) _)
      (sub_mem (mul_mem (hO _ _ _) (hO _ _ _)) (mul_mem (hO _ _ _) (hO _ _ _)))
