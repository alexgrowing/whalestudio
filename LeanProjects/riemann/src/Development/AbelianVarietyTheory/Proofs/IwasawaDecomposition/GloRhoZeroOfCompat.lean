import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
import Formalism.LocalToGlobal.Columns.RecLevelLocP
import Formalism.LocalToGlobal.Columns.RecLevelCls
import Formalism.LocalToGlobal.Columns.TiedGlCore
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.LevStd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem gloRho_eq_of_compat (v : HeightOneSpectrum (𝓞 F))
    (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (halg : ∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a)) (w : Pl E) (e : (𝓞 E ⧸ w.asIdeal) ≃+* kv F v)
    (he : ∀ z : Formalism.L2.Herm.intAf F E, ∃ hz : gloPhi v spl (prV (E := E) v z.1) ∈ v.adicCompletionIntegers F,
      IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hz⟩ = e (resS F w z)) (z : Formalism.L2.Herm.intAf F E) :
    gloRho v spl halg z = e (resS F w z) := by
  obtain ⟨hz, h⟩ := he z
  rw [gloRho_apply]
  exact h

theorem gloRho_zero_of_compat (v : HeightOneSpectrum (𝓞 F))
    (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (halg : ∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a)) (w : Pl E) (e : (𝓞 E ⧸ w.asIdeal) ≃+* kv F v)
    (he : ∀ z : Formalism.L2.Herm.intAf F E, ∃ hz : gloPhi v spl (prV (E := E) v z.1) ∈ v.adicCompletionIntegers F,
      IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hz⟩ = e (resS F w z)) :
    ∀ a ∈ w.asIdeal, gloRho v spl halg (oToS F E a) = 0 := by
  intro a ha
  rw [gloRho_eq_of_compat v spl halg w e he, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]

theorem gloE_eq_of_compat (v : HeightOneSpectrum (𝓞 F))
    (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (halg : ∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a)) (w : Pl E) (e : (𝓞 E ⧸ w.asIdeal) ≃+* kv F v)
    (he : ∀ z : Formalism.L2.Herm.intAf F E, ∃ hz : gloPhi v spl (prV (E := E) v z.1) ∈ v.adicCompletionIntegers F,
      IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hz⟩ = e (resS F w z)) (t : kP w) :
    gloE v spl halg w (gloRho_zero_of_compat v spl halg w e he) t = e t := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective t
  rw [← resS_oToS (F := F), gloE_resS, gloRho_eq_of_compat v spl halg w e he]

end GlobalTheory.Mem.LevStd

open GlobalTheory.Mem.LevStd in

theorem GlobalTheory.Mem.LevStd.levU_prod_glevH : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (gp : Fin 2 → ℕ) (Jm : Matrix (Fin n) (Fin n) E) (S : StepLevel F E hc.sig Jm T f bad) (G : GLoc F E hc.sig gp) (Hw : ∀ w : SG, Subgroup (GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))) (lamw : ∀ w, Hw w →* ℂˣ) (H : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin n) (kv F v))) (lam : ∀ a v h, H a v h →* ℂˣ) (wOf : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → SG) (e : ∀ a v h, (𝓞 E ⧸ (wOf a v h).1.asIdeal) ≃+* kv F v), Jm = 1 → S.Lb = baseLb E n ST → ∀ hU : S.U = levU hc n ST SG (Subgroup.pi Set.univ Hw), (∀ x : S.U, S.chi x = ∏ w : SG, (lamw w ⟨(levRed hc n ST SG (Subgroup.pi Set.univ Hw) ⟨x.1, hU ▸ x.2⟩).1 w, (levRed hc n ST SG (Subgroup.pi Set.univ Hw) ⟨x.1, hU ▸ x.2⟩).2 w trivial⟩)⁻¹) → (∀ a v (_ : (gp a : 𝓞 F) ∈ v.asIdeal), v ∉ plUnder F ST) → (∀ a v h (w : SG), IsOver v w.1 ↔ w = wOf a v h) → (∀ φ : SG → ℂ, ∏ w : SG, φ w = ∏ a : Fin 2, ∏ᶠ (v : HeightOneSpectrum (𝓞 F)) (h : (gp a : 𝓞 F) ∈ v.asIdeal), φ (wOf a v h)) → (∀ a v h (z : Formalism.L2.Herm.intAf F E), ∃ hz : G.phi a v h (prV (E := E) v z.1) ∈ v.adicCompletionIntegers F, IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hz⟩ = e a v h (resS F (wOf a v h).1 z)) → (∀ a v h M, M ∈ Hw (wOf a v h) ↔ Matrix.GeneralLinearGroup.map (e a v h).toRingHom M ∈ H a v h) → (∀ a v h (M : Hw (wOf a v h)) (M' : H a v h), M'.1 = Matrix.GeneralLinearGroup.map (e a v h).toRingHom M.1 → lam a v h M' = lamw (wOf a v h) M) → ∃ V : GLevH S G H lam, ∀ a v h, V.fr a v h = 1 := by
  intro F E _ _ _ _ _ _ hc n _ ST SG T f bad gp Jm S G Hw lamw H lam wOf e hJ hLb hU hchi hST hover hprod hcomp hH hlam
  subst hJ
  have hcomp' : ∀ a v h (z : Formalism.L2.Herm.intAf F E), ∃ hz : gloPhi v (G.sp a v h) (prV (E := E) v z.1) ∈ v.adicCompletionIntegers F,
      IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hz⟩ = e a v h (resS F (wOf a v h).1 z) := hcomp
  have hw := fun a v h => gloRho_zero_of_compat v (G.sp a v h) (G.sp_alg a v h) (wOf a v h).1 (e a v h) (hcomp' a v h)
  have hgE := fun a v h => gloE_eq_of_compat v (G.sp a v h) (G.sp_alg a v h) (wOf a v h).1 (e a v h) (hcomp' a v h)
  have hloc : ∀ v x, x ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) →
      (x ∈ S.Uloc v ↔ x ∈ levLoc hc n ST SG (Subgroup.pi Set.univ Hw) v) := by
    intro v x hx
    constructor
    · intro hxv
      have hxU : x ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) := hx.1
      have hp : rll_put n v x ∈ S.U := by
        refine (S.U_eq _).2 ⟨rll_put_mem_UAd hc n v hxU, fun v' => ?_⟩
        by_cases hv : v' = v
        · subst hv; rw [rll_put_self]; exact hxv
        · rw [rll_put_ne n v v' hv]; exact Subgroup.one_mem _
      rw [hU] at hp
      exact ⟨_, hp, rll_put_self n v x⟩
    · rintro ⟨k, hk, rfl⟩
      rw [← hU] at hk
      exact ((S.U_eq k).1 hk).2 v
  have hxL : ∀ x : S.U, x.1 ∈ levU hc n ST SG (Subgroup.pi Set.univ Hw) := fun x => hU ▸ x.2
  have hkJ : ∀ x : S.U, x.1 ∈ J0 hc n ST := fun x => ((mem_levU hc n ST SG _).1 (hxL x)).1
  refine ⟨{ fr := fun _ _ _ => 1
            fr_lat := ?_
            mem := ?_
            red := fun a v h x => ⟨Matrix.GeneralLinearGroup.map (e a v h).toRingHom
                ((levRed hc n ST SG (Subgroup.pi Set.univ Hw) ⟨x.1, hU ▸ x.2⟩).1 (wOf a v h)),
              (hH a v h _).1 ((levRed hc n ST SG (Subgroup.pi Set.univ Hw) ⟨x.1, hU ▸ x.2⟩).2 (wOf a v h) trivial)⟩
            red_eq := ?_
            chi_eq := ?_
            chi_unit := ?_ }, fun _ _ _ => rfl⟩
  · intro a v h x
    rw [hLb]
    exact gco_fr_lat n ST v (G.sp a v h) (G.sp_alg a v h) (hST a v h) x
  · intro a v h x hx
    rw [hLb] at hx
    have hG : ∀ y : GL (Fin n) (E ⊗[F] v.adicCompletion F), G.mat a v h 1 y =
        ((bc (gloPhi v (G.sp a v h)) y : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
      intro y; simp only [GLoc.mat, inv_one, one_mul, mul_one]; rfl
    rw [hloc v x hx, gco_mem_levLoc hc n ST SG v (G.sp a v h) (G.sp_alg a v h) Hw (wOf a v h) (hw a v h)
      ((hover a v h _).2 rfl) (fun w' hw' => (hover a v h w').1 hw') (hST a v h) x hx, hG]
    constructor
    · rintro ⟨M, hM, hMx⟩
      refine ⟨Matrix.GeneralLinearGroup.map (e a v h).toRingHom M, (hH a v h M).1 hM, ?_⟩
      rw [← hMx]
      ext i j
      rw [Matrix.map_apply, hgE]
      rfl
    · rintro ⟨M', hM', hM'x⟩
      refine ⟨Matrix.GeneralLinearGroup.map (e a v h).symm.toRingHom M', (hH a v h _).2 ?_, ?_⟩
      · convert hM' using 1
        ext i j
        simp
      · rw [← hM'x]
        ext i j
        rw [Matrix.map_apply, hgE]
        simp
  · intro a v h x
    have h1 := gco_red_map n v (G.sp a v h) (G.sp_alg a v h) (wOf a v h).1 (hw a v h) (congruence_subgroup_le_stabilizer hc n ST (hkJ x))
    have hG : G.mat a v h 1 (bc (prV (E := E) v) x.1) =
        ((bc (gloPhi v (G.sp a v h)) (bc (prV (E := E) v) x.1) : GL (Fin n) (v.adicCompletion F)) :
          Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
      simp only [GLoc.mat, inv_one, one_mul, mul_one]; rfl
    rw [hG, ← h1]
    ext i j
    rw [Matrix.map_apply, hgE]
    rfl
  · intro x
    rw [hchi x, Units.coe_prod]
    simp only [Units.val_inv_eq_inv_val]
    rw [hprod]
    congr 1; funext a; congr 1; funext v; congr 1; funext h
    rw [hlam a v h ⟨(levRed hc n ST SG (Subgroup.pi Set.univ Hw) ⟨x.1, hxL x⟩).1 (wOf a v h),
      (levRed hc n ST SG (Subgroup.pi Set.univ Hw) ⟨x.1, hxL x⟩).2 (wOf a v h) trivial⟩ _ rfl]
  · intro x
    rw [hchi x, Units.coe_prod, norm_prod]
    refine Finset.prod_eq_one fun w _ => ?_
    rw [Units.val_inv_eq_inv_val, norm_inv, inv_eq_one]
    generalize (⟨_, _⟩ : Hw w) = m
    have hfo : IsOfFinOrder m := isOfFinOrder_of_finite m
    obtain ⟨N, hN, hpow⟩ := hfo.exists_pow_eq_one
    have hp : ((lamw w m : ℂˣ) : ℂ) ^ N = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, hpow, map_one, Units.val_one]
    exact Complex.norm_eq_one_of_pow_eq_one hp hN.ne'
