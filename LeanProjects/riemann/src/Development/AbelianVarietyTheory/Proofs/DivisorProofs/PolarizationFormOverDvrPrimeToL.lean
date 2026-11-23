import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomIdPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSurjectiveGeomFibre
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
open GlobalTheory.AbDual GlobalTheory.AbLaw GlobalTheory.CechPic

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolPrimeTo

theorem perfect_of_primeTo (HR : GlobalTheory.Published.AbelianDeRham) (HD : GlobalTheory.Published.AbelianDualCrystal)
    (F : Type) [Field F] [NumberField F] (𝔠 : FracId F)
    (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (hunit : ∀ n : ℕ, n.Coprime l → IsUnit (n : R)) (X : Obj F 𝔠 (Sp R)) (c₀ : 𝔠.elt) (hc₀ : (c₀ : F) ≠ 0)
    (hgen : ∀ c : 𝔠.elt, ∃ (n : ℕ) (t : 𝓞 F), n.Coprime l ∧ n • c = t • c₀)
    (ψ : LinearMap.BilinForm R (HdR X.A)) (hψ : GlobalTheory.AbDual.IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c₀) ψ) :
    Function.Bijective ψ := by
  obtain ⟨m, hm0, hml, hm⟩ := exists_uniform 𝔠 l c₀ hgen

  obtain ⟨B, _, Q, hB, hBg, hd, hd'⟩ := HD.1 (Sp R) X.A X.ab
  have hBg := hBg _ X.dim
  haveI : IsCommMonObj B := hB.comm

  obtain ⟨c₁, hc₁⟩ := exists_totPos 𝔠 c₀ hc₀
  have hL := pull_isLB (X.isLB c₁) (lift (𝟙 X.A) (𝟙 X.A)).left
  obtain ⟨H, hH, hamp⟩ := GlobalTheory.BirigidLift.exists_relAmple_prod X.ab X.ab hL (X.pos c₁ hc₁) hL (X.pos c₁ hc₁)
  obtain ⟨a₁, a₂⟩ := GlobalTheory.BirigidLift.additive_of_triv X.ab X.ab hH hamp (X.isLB c₀) (X.rig₁ c₀) (X.rig₂ c₀)
  obtain ⟨lam, hlam, hcls⟩ := GlobalTheory.BirigidLift.exists_hom hd hd'.additive (X.isLB c₀) a₁ a₂

  have hker : ∀ (T : Over (Sp R)) (x : T ⟶ X.A), x ≫ lam = 1 → x ^ m = 1 := by
    intro T x hx
    have tr : Triv (ev (X.P c₀) (fst X.A T) (snd X.A T ≫ x)) := by
      rw [triv_ev_iff (X.isLB c₀), GlobalTheory.BirigidLift.evc_of_cls hd.isLB (X.isLB c₀) hcls, Category.assoc, hx,
        comp_one]
      exact evc_one_right hd.isLB hd.zero _
    have k := X.ker c₀ T x tr (m : 𝓞 F) hm
    rw [act_natCast, comp_pow, Category.comp_id] at k
    exact k
  obtain ⟨μ', hμ', e₁, e₂⟩ := GlobalTheory.IsogenyQuasiInverse.exists_quasiInverse R X.A B _ X.ab hB X.dim hBg lam hlam m hm0 hker
  have hpush := bijective_push (dp0 R) (𝟙 _) lam μ' m (hunit m hml) e₁ e₂

  obtain ⟨⟨φ, hφ, -⟩, hperf⟩ := GlobalTheory.Published.AbelianDualCrystal.duality HR X.ab X.dim hB hBg (hd.isPerfect hd')
  have C := cupSquare_of_free HR.1 (AbelianSchemeGerms.isAbelianScheme_tensor X.A X.A X.ab X.ab) (smooth_prod X.dim X.dim)
  have e : LBIso (ev Q (fst X.A X.A) (snd X.A X.A ≫ lam)) (ev (X.P c₀) (fst X.A X.A ≫ 𝟙 X.A) (snd X.A X.A)) := by
    refine (cls_eq_iff (pull_isLB hd.isLB _) (pull_isLB (X.isLB c₀) _)).1 ?_
    rw [cls_ev hd.isLB, cls_ev (X.isLB c₀), GlobalTheory.BirigidLift.evc_of_cls hd.isLB (X.isLB c₀) hcls, Category.comp_id]
  have hadj : ∀ x y, φ x (push (dp0 R) (𝟙 _) lam y) = ψ x y := fun x y ↦ by
    have k := IsCorrForm.adjoint C hd.isLB (X.isLB c₀) hφ hψ (𝟙 X.A) lam e x y
    rwa [push_id] at k
  haveI := (hperf φ hφ).1
  have hφb : Function.Bijective φ := LinearMap.IsPerfPair.bijective_left φ
  let E := LinearEquiv.ofBijective _ hpush
  have : ⇑ψ = ⇑E.dualMap ∘ ⇑φ := by
    funext x
    refine LinearMap.ext fun y ↦ ?_
    rw [Function.comp_apply, LinearEquiv.dualMap_apply, ← hadj]
    rfl
  rw [this]
  exact E.dualMap.bijective.comp hφb

end GlobalTheory.PolPrimeTo
