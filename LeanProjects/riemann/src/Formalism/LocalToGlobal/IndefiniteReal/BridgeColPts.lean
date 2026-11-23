import Formalism.LocalToGlobal.IndefiniteReal.BridgeCol
import Formalism.LocalToGlobal.Columns.RowFormsAdelic

open NumberField

noncomputable section

namespace Formalism.IndefR.Bridge

open Formalism.L2

section ColPts

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Formalism.L2.DIV.Pl E))
  (H : Subgroup (Col.GLG E n SG))

def colJ : Subgroup (Col.UAd hc n) := (Col.JH hc n ST SG H).map (Col.ToUnitaryAdelic hc n ST)

abbrev principalCongruenceSubgroup : Subgroup (Col.UAd hc n) := (Col.K1 hc n ST SG).subgroupOf (Col.UAd hc n)

theorem J0toU_injective : Function.Injective (Col.ToUnitaryAdelic hc n ST) := Subgroup.inclusion_injective _

def colJEquiv : Col.JH hc n ST SG H ≃* colJ hc n ST SG H :=
  (Col.JH hc n ST SG H).equivMapOfInjective _ (J0toU_injective hc n ST)

theorem colJEquiv_symm_coe (k : colJ hc n ST SG H) :
    Col.ToUnitaryAdelic hc n ST (((colJEquiv hc n ST SG H).symm k : Col.JH hc n ST SG H) : Col.J0 hc n ST) = (k : Col.UAd hc n) := by
  rw [← Subgroup.coe_equivMapOfInjective_apply (Col.JH hc n ST SG H) (Col.ToUnitaryAdelic hc n ST) (J0toU_injective hc n ST)]
  exact congrArg Subtype.val ((colJEquiv hc n ST SG H).apply_symm_apply k)

theorem mem_principal_congruence_iff (m : Col.J0 hc n ST) : Col.ToUnitaryAdelic hc n ST m ∈ principalCongruenceSubgroup hc n ST SG ↔ Col.redG hc n ST SG m = 1 := by
  constructor
  · intro h
    obtain ⟨m', hm', he⟩ := Subgroup.mem_subgroupOf.1 h
    have e : m' = m := Subtype.ext he
    rw [← e]
    exact MonoidHom.mem_ker.1 hm'
  · intro h
    exact Col.mem_principal_congruence_of hc n ST SG h

theorem principal_congruence_le_level_subgroup : principalCongruenceSubgroup hc n ST SG ≤ colJ hc n ST SG H := by
  intro a ha
  obtain ⟨m, hm, hma⟩ := Subgroup.mem_subgroupOf.1 ha
  refine Subgroup.mem_map.2 ⟨m, Subgroup.mem_comap.2 ?_, Subtype.ext hma⟩
  rw [MonoidHom.mem_ker.1 hm]
  exact H.one_mem

def colToAdG : Col.URat hc n × colJ hc n ST SG H →* Col.AdG hc n ST SG H :=
  show Col.URat hc n × colJ hc n ST SG H →* Col.URat hc n × (Col.JH hc n ST SG H ⧸ (Col.redH hc n ST SG H).ker) from
    MonoidHom.prodMap (MonoidHom.id _)
      ((QuotientGroup.mk' (Col.redH hc n ST SG H).ker).comp (colJEquiv hc n ST SG H).symm.toMonoidHom)

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : Col.GSD K}

variable {hc n ST SG H}

def colGl (o : Col.OnDeco n ST SG H S) : Col.URat hc n × colJ hc n ST SG H →* S.G :=
  o.eG.toMonoidHom.comp ((Col.adHom hc n ST SG H).comp (colToAdG hc n ST SG H))

def colQ (o : Col.OnDeco n ST SG H S) (x : Col.UAd hc n) : S.D :=
  o.eD (Col.decoPt hc n ST SG (QuotientGroup.mk x : Col.adPt hc n ST SG))

variable (o : Col.OnDeco n ST SG H S)

theorem colGl_apply (γ : Col.URat hc n) (k : colJ hc n ST SG H) :
    colGl o (γ, k) = o.eG (Col.ratHom hc n γ, Col.redH hc n ST SG H ((colJEquiv hc n ST SG H).symm k)) := rfl

theorem colGl_surj (hR : Col.RedHSurj hc n ST SG H) : Function.Surjective (colGl (hc := hc) o) := by
  intro g
  obtain ⟨⟨u, h⟩, rfl⟩ := o.eG.surjective g
  obtain ⟨γ, hγ⟩ := (Col.ratHom_bijective hc n).2 u
  obtain ⟨k, hk⟩ := hR h
  refine ⟨(γ, colJEquiv hc n ST SG H k), ?_⟩
  rw [colGl_apply, MulEquiv.symm_apply_apply, hγ, hk]

theorem colGl_ker (γ : Col.URat hc n) (k : colJ hc n ST SG H) :
    colGl o (γ, k) = 1 ↔ γ = 1 ∧ (k : Col.UAd hc n) ∈ principalCongruenceSubgroup hc n ST SG := by
  rw [colGl_apply, MulEquiv.map_eq_one_iff, Prod.mk_eq_one,
    (injective_iff_map_eq_one' _).1 (Col.ratHom_bijective hc n).1, ← colJEquiv_symm_coe, mem_principal_congruence_iff]
  exact and_congr Iff.rfl Subtype.ext_iff

theorem colQ_surj (hS : Col.DecoPtSurj hc n ST SG) : Function.Surjective (colQ (hc := hc) o) := by
  intro d
  obtain ⟨d', rfl⟩ := o.eD.surjective d
  obtain ⟨p, rfl⟩ := hS d'
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective p
  exact ⟨x, rfl⟩

theorem colQ_fib (x x' : Col.UAd hc n) :
    colQ o x = colQ o x' ↔ ∃ k1 ∈ principalCongruenceSubgroup hc n ST SG, x' = x * k1 := by
  unfold colQ
  rw [o.eD.injective.eq_iff, (Col.decoPt_injective' hc n ST SG).eq_iff, QuotientGroup.eq]
  constructor
  · intro h
    exact ⟨_, h, by rw [mul_inv_cancel_left]⟩
  · rintro ⟨k1, hk1, rfl⟩
    rwa [inv_mul_cancel_left]

theorem colQ_eqv (γ : Col.URat hc n) (k : colJ hc n ST SG H) (x : Col.UAd hc n) :
    colQ o (Col.ratIn hc n γ * x * (k : Col.UAd hc n)⁻¹) = colGl o (γ, k) • colQ o x := by
  have e1 : Col.ratIn hc n γ * x * (k : Col.UAd hc n)⁻¹ =
      Col.rawSm hc n ST γ (((colJEquiv hc n ST SG H).symm k : Col.JH hc n ST SG H) : Col.J0 hc n ST) x := by
    unfold Col.rawSm
    rw [colJEquiv_symm_coe]
  have e2 := Col.decorated_point_equivariant hc n ST SG H
    ((γ, (((colJEquiv hc n ST SG H).symm k : Col.JH hc n ST SG H) : Col.JH hc n ST SG H ⧸ (Col.redH hc n ST SG H).ker)) :
      Col.AdG hc n ST SG H) (QuotientGroup.mk x : Col.adPt hc n ST SG)
  unfold colQ
  rw [e1, Col.adSmul_mk] at *
  rw [e2, o.smul]
  rfl

def colAdPts (hS : Col.DecoPtSurj hc n ST SG) : AdPts S (Col.ratIn hc n) (colJ hc n ST SG H) where
  K1 := principalCongruenceSubgroup hc n ST SG
  principal_congruence_le := principal_congruence_le_level_subgroup hc n ST SG H
  q := colQ o
  gl := colGl o
  gl_surj := colGl_surj o (Col.redHSurj_of hc n ST SG H (Col.decorated_lattice_exists hc n ST SG) hS)
  gl_ker := colGl_ker o
  q_surj := colQ_surj o hS
  q_eqv := colQ_eqv o
  q_fib := colQ_fib o

open Classical in

def colAdPtsG (hG : Col.UnimodGenus hc n) (hR : Formalism.L2.DIV.RedSurj) (hT : Formalism.L2.DIV.IsSplitSet (ST ∪ SG))
    (hD : Disjoint ST SG) : AdPts S (Col.ratIn hc n) (colJ hc n ST SG H) :=
  colAdPts o (Col.decoPtSurj_of hc n ST SG hG hR hT hD)

def colClassPres (hS : Col.DecoPtSurj hc n ST SG) (h : S.Ok) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (σ : K →+* ℂ) (ρ : Col.URat hc n →* Module.End ℂ W) (χ : colJ hc n ST SG H →* ℂˣ)
    (coef : S.V →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => coef (S.bV i))
    (hspan : Submodule.span ℂ (Set.range fun i => coef (S.bV i)) = ⊤)
    (hpair : ∀ x x', inner ℂ (coef x) (coef x') = σ (S.pair x x'))
    (hK1 : ∀ k : colJ hc n ST SG H, (k : Col.UAd hc n) ∈ principalCongruenceSubgroup hc n ST SG → χ k = 1)
    (hgl : ∀ (γ : Col.URat hc n) (k : colJ hc n ST SG H) (v : S.V),
      coef (S.ρ (colGl o (γ, k)) v) = ((χ k)⁻¹ : ℂˣ) • ρ γ (coef v)) :
    ClassPres (Col.ratIn hc n) (S.toCSD h) σ ρ (colJ hc n ST SG H) χ :=
  classPresOf (colAdPts o hS) h σ ρ χ coef hli hspan hpair hK1 hgl

end ColPts

section Forms

variable {X : Col.Fields} (hc : Formalism.BasicNotions.CMData X.F X.E) {n : ℕ} [NeZero n]
  {ST SG : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 X.E))}

def colAdPtsForm (C : Col.CoefPk X n (Col.DecoSet X.E n ST SG)) (Λ : Col.LevFam X.E X.K n SG)
    (hS : Col.DecoPtSurj hc n ST SG) : AdPts (Col.formGSD C Λ) (Col.ratIn hc n) (colJ hc n ST SG Λ.grp) :=
  colAdPts (Col.rf_onDeco C Λ) hS

end Forms

end Formalism.IndefR.Bridge
