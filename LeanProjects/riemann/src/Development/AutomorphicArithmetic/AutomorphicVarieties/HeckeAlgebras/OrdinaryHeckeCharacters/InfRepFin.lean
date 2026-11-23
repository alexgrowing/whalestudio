import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PlaceBetween
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem w_under {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  exact (s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v x)

private theorem infRep_fin {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} (V : s.Lev) (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) {k : UA L n}
    (hk : k ∈ finU L n) : infRep (V := V) ι lam k = 1 := by
  have h1 : ∀ τ : L →+* ℂ, cEmb τ k = 1 := fun τ => by
    change Matrix.GeneralLinearGroup.map (coord τ) (cInf k) = 1
    rw [MonoidHom.mem_ker.1 hk, map_one]
  change PiTensorProduct.mapMonoidHom (fun y : Emb l (fun v : V.frame.Vl => s.w v.1) =>
    GlobalTheory.Branching.sqRep ℂ n (lam y.res) (cEmb (ι.toRingHom.comp y.res) k)) = 1
  simp only [h1, map_one]
  exact map_one _

private theorem comps {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} (V : s.Lev) [DecidableEq V.frame.Vl] (v : V.frame.Vl) (x y : UA L n)
    (hy : y ∈ locU n (s.w v.1)) :
    (((away l L n).rangeRestrict (x * y), fun u : V.frame.Vl => cLoc (s.w u.1) (x * y)) :
        Ga l L n × GV n (fun u : V.frame.Vl => s.w u.1)) =
      ((away l L n).rangeRestrict x, fun u : V.frame.Vl => cLoc (s.w u.1) x) *
        (1, MonoidHom.mulSingle (fun u : V.frame.Vl => GLw n (s.w u.1)) v (cLoc (s.w v.1) y)) := by
  refine Prod.ext ?_ (funext fun u => ?_)
  · have h : (away l L n).rangeRestrict y = 1 := by
      refine Subtype.ext (funext fun u => GlobalTheory.DefU.LocRet.mem_locU_ne hy fun h => u.2 ?_)
      have h2 : ((l : ℕ) : 𝓞 (Lp L)) ∈ (u.1.under (𝓞 (Lp L))).asIdeal := by
        rw [h, w_under]
        exact v.2
      have h3 : algebraMap (𝓞 (Lp L)) (𝓞 L) (l : 𝓞 (Lp L)) ∈ u.1.asIdeal := h2
      rwa [map_natCast] at h3
    rw [map_mul, h]
    rfl
  · change cLoc (s.w u.1) (x * y) = cLoc (s.w u.1) x *
      Pi.mulSingle (M := fun u : V.frame.Vl => GLw n (s.w u.1)) v (cLoc (s.w v.1) y) u
    rw [map_mul]
    congr 1
    by_cases huv : u = v
    · subst huv
      rw [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne huv]
      exact GlobalTheory.DefU.LocRet.mem_locU_ne hy fun h =>
        huv (Subtype.ext ((w_under s u.1).symm.trans (h.trans (w_under s v.1))))

theorem UpperTheory.V.Hi.partUR2AtV :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ (v : V.frame.Vl) (j : GLw n (s.w v.1) →* UA L n), (∀ g, j g ∈ locU n (s.w v.1)) → (∀ g, cLoc (s.w v.1) (j g) = g) →
    ∀ (F : Fin m → (hset Q τ₀).X.Fn ℂ d) (g : GLw n (s.w v.1)) (i : Fin m) ℓ, toForm ι e ((hset Q τ₀).atV d v g F i) ℓ = RU L n (j g) (toForm ι e (F i) ℓ) := by
  intro l _ L Ω _ _ _ _ _ _ s n _ V Q c ι m τ₀ lam d e ξ _ v j hj hj' F g i ℓ
  funext x
  have h1 := @comps l _ L Ω _ _ _ _ _ _ s n V (fun a b => Classical.propDecidable (a = b)) v x (j g) (hj g)
  rw [hj'] at h1
  have h2 : infRep (V := V) ι lam (x * j g)⁻¹ = infRep (V := V) ι lam x⁻¹ := by
    rw [mul_inv_rev, map_mul, infRep_fin V ι lam ((finU L n).inv_mem (Subgroup.mem_inf.1 (hj g)).1), one_mul]
  change _ = toForm ι e (F i) ℓ (x * j g)
  unfold toForm
  rw [h1, h2]
  rfl
