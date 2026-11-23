import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.LieVal

open GlobalTheory.CatCoh

theorem main : ∀ {A : Over (Sp ℂ)} {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) (r : Real K (A.hom ≫ 𝟙 _) (algebraMap ℂ (Hol F.V))) (k : K.K) (p : Tot I g), p ∈ K.W k → ∀ (w : Fin g → ℂ) (ρ : Hol (K.W k) →ₐ[ℂ] DualNumber ℂ), (∀ h, (ρ h).fst = h.fn p ∧ (ρ h).snd = fderiv ℂ h.fn p (0, w)) → ∀ (v : epsR ℂ ⟶ A), v.left = spMap ρ.toRingHom ≫ r.x k → ∀ (f : Form (A.hom ≫ 𝟙 _)) (per : Λ →+ Hol F.V) (q : GlobalTheory.CatCoh.C0 K.Oc), GlobalTheory.CatCoh.d0 K.Oc q = (r.coef.pullbackOneCocycle f.1).1 - (K.perZ per).1 → tanVal v f = fderiv ℂ (Hol.fn (W := K.W k) (q (K.triv k))) p (0, w) := by
  intro A I _ g Λ _ F K r k p hp w ρ hρ v hv f per q hq
  let e : Hol (K.W k) →+* DualNumber ℂ := (TrivSqZeroExt.inlHom ℂ ℂ).comp (Hol.ev p hp).toRingHom
  let T : K.Obj :=
    { k := k, C := DualNumber ℂ, alg := (e.comp (K.cst k)).toAlgebra
      J := RingHom.ker ((SqExt.dual ℂ).π : DualNumber ℂ →+* ℂ)
      nil := ⟨2, (SqExt.dual ℂ).sq⟩, ρ := e, ρ_cst := fun _ ↦ rfl }
  have hder : ∀ h : Hol (K.W k), fderiv ℂ h.fn p (0, w) = ∑ a, (dw a h).fn p * w a := fun h ↦ by
    have : ((0, w) : Tot I g) = ∑ a, w a • ((0, Pi.single a 1) : Tot I g) := by
      refine Prod.ext ?_ ?_
      · simp [Prod.fst_sum]
      · simp only [Prod.snd_sum, Prod.smul_snd]
        exact pi_eq_sum_univ' w
    rw [this, map_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [map_smul, smul_eq_mul, mul_comm]
    exact congrArg (· * w a) (Hol.fn_der _ h hp).symm
  have hexp : ∀ h : Hol (K.W k), ρ h = e h + ∑ a, e (dw a h) * TrivSqZeroExt.inr (w a) := fun h ↦ by
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [(hρ h).1]
      simp [e, TrivSqZeroExt.fst_sum, Hol.ev_apply]
    · rw [(hρ h).2, hder]
      simp [e, TrivSqZeroExt.snd_sum, Hol.ev_apply, mul_comm]
  let a : K.triv k ⟶ T := Charts.ptHom T (K.le_refl k)
  let b : K.triv k ⟶ T := Charts.fromTriv T (K.le_refl k) ρ.toRingHom
    (fun c ↦ by
      change ρ (K.cst k c) = e (K.cst k c)
      rw [hexp]; simp [Charts.dw_cst])
    (Relation.ReflTransGen.single ⟨fun a ↦ TrivSqZeroExt.inr (w a), fun _ ↦ rfl,
      fun a b ↦ TrivSqZeroExt.inr_mul_inr _ _ _, fun h ↦ by
        simp only [RingHom.comp_apply, Charts.sh_refl]
        exact hexp h⟩)
  have ea := congrFun (congrFun (congrFun hq _) _) a
  have eb := congrFun (congrFun (congrFun hq _) _) b
  change ((show DualNumber ℂ from q T) - e (Charts.sh (K.le_refl k) (q (K.triv k))) : DualNumber ℂ) =
    (show DualNumber ℂ from ev f.1 (r.functor.map a)) - e (K.cst k (per 0)) at ea
  change ((show DualNumber ℂ from q T) - ρ (q (K.triv k)) : DualNumber ℂ) =
    (show DualNumber ℂ from ev f.1 (r.functor.map b)) - e (K.cst k (per 0)) at eb
  rw [Charts.sh_refl] at ea
  let E := SqExt.dual ℂ
  have hfst : (E.π : E.C →+* E.B).comp ρ.toRingHom = (Hol.ev p hp).toRingHom :=
    RingHom.ext fun h ↦ (hρ h).1.trans (Hol.ev_apply p hp h).symm
  have halg : ∀ c : ℂ, e (K.cst k (algebraMap ℂ (Hol F.V) c)) = algebraMap ℂ (DualNumber ℂ) c := fun c ↦ by
    have : K.cst k (algebraMap ℂ (Hol F.V) c) = algebraMap ℂ (Hol (K.W k)) c := rfl
    rw [this]
    change TrivSqZeroExt.inl (Hol.ev p hp (algebraMap ℂ _ c)) = _
    rw [AlgHom.commutes]; rfl
  let Φ : E.thick _ (E.red_w (pt_w v)) ⟶ r.obj T :=
    { φ := { RingHom.id (DualNumber ℂ) with commutes' := fun c ↦ (halg c).symm }
      φ₀ := (Ideal.Quotient.mk T.J).comp (TrivSqZeroExt.inlHom ℂ ℂ)
      comm := fun c ↦ Ideal.Quotient.eq.2 (by
        change (TrivSqZeroExt.inl (TrivSqZeroExt.fst (R := ℂ) (M := ℂ) c) - (show TrivSqZeroExt ℂ ℂ from c)).fst = 0
        rw [TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_inl, sub_self])
      dp := isDPMorphism_of_rat (C' := DualNumber ℂ) _ _ _ fun c hc ↦ hc
      pt := by
        have h0 : spMap ((Ideal.Quotient.mk T.J).comp (TrivSqZeroExt.inlHom ℂ ℂ)) ≫
            spMap (E.π : E.C →+* E.B) ≫ v.left = spMap ((Ideal.Quotient.mk T.J).comp e) ≫ r.x k := by
          rw [hv, ← Category.assoc (spMap (E.π : E.C →+* E.B)), ← Cris.spMap_comp, hfst, ← Category.assoc,
            ← Cris.spMap_comp]
        exact h0 }
  have mkHom : ∀ (C : Type) [CommRing C] [Algebra ℂ C] (ψ : Hol (K.W k) →ₐ[ℂ] C) (y : Sp C ⟶ A.left)
      (hy : y ≫ A.hom ≫ 𝟙 _ = spMap (algebraMap ℂ C)), y = spMap ψ.toRingHom ≫ r.x k →
      ∃ m : r.obj (K.triv k) ⟶ Thick.triv C y hy, ∀ c, m.φ c = ψ c := fun C _ _ ψ y hy e' ↦
    ⟨{ φ := { ψ.toRingHom with commutes' := fun c ↦ ψ.commutes c }
       φ₀ := Ideal.Quotient.lift ⊥ ψ.toRingHom fun c hc ↦ by rw [Ideal.mem_bot.1 hc, map_zero]
       comm := fun _ ↦ rfl
       dp := isDPMorphism_of_eq_bot _ rfl _ _
       pt := by
        refine Eq.trans ?_ e'.symm
        refine (Category.assoc _ _ _).symm.trans (congrArg (· ≫ r.x k) ?_)
        exact (Cris.spMap_comp _ _).symm }, fun _ ↦ rfl⟩
  obtain ⟨a', ha'⟩ := mkHom ℂ (Hol.ev p hp) _ (E.red_w (pt_w v)) (by
    rw [hv, ← Category.assoc, ← Cris.spMap_comp, hfst])
  obtain ⟨b', hb'⟩ := mkHom (DualNumber ℂ) ρ v.left (pt_w v) hv
  have e1 : r.functor.map a = a' ≫ E.secHom (E.red_w (pt_w v)) E.i E.π_i ≫ Φ := Thick.hom_ext fun c ↦ by
    change e (Charts.sh (K.le_refl k) c) = TrivSqZeroExt.inl (a'.φ c)
    exact (congrArg e (Charts.sh_refl _ c)).trans (congrArg TrivSqZeroExt.inl (ha' c).symm)
  have e2 : r.functor.map b = b' ≫ E.idHom (pt_w v) ≫ Φ := Thick.hom_ext fun c ↦ (hb' c).symm
  have z1 : ev f.1 a' = 0 := f.2 a' rfl rfl
  have z2 : ev f.1 b' = 0 := f.2 b' rfl rfl
  have g1 : ev f.1 (r.functor.map a) = Φ.φ (ev f.1 (E.secHom (E.red_w (pt_w v)) E.i E.π_i)) + ev f.1 Φ := by
    rw [e1]
    refine (ev_comp f.1 a' _).trans ?_
    rw [z1, map_zero, zero_add]
    exact ev_comp f.1 _ Φ
  have g2 : ev f.1 (r.functor.map b) = Φ.φ (ev f.1 (E.idHom (pt_w v))) + ev f.1 Φ := by
    rw [e2]
    refine (ev_comp f.1 b' _).trans ?_
    rw [z2, map_zero, zero_add]
    exact ev_comp f.1 _ Φ
  rw [g1] at ea
  rw [g2] at eb
  have key : (E.val v.left (pt_w v) f.1 : DualNumber ℂ) = ρ (q (K.triv k)) - e (q (K.triv k)) := by
    rw [SqExt.val_apply]
    have aux : ∀ x y z u s t c : DualNumber ℂ, x - y = s + u - c → x - z = t + u - c → s - t = z - y :=
      fun x y z u s t c h1 h2 ↦ by linear_combination h2 - h1
    exact aux _ _ _ _ _ _ _ ea eb
  rw [tanVal_apply, key, TrivSqZeroExt.snd_sub, (hρ _).2]
  exact sub_zero _

end GlobalTheory.AnPer.LieVal
