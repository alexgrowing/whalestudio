import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelSubgroupRestrictedProductOfLaws

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.UpInj

def DCRep {Γ : Type} [Group Γ] (c : Γ →* Γ) (K : Subgroup Γ) (α : Γ) (C : Finset Γ) : Prop :=
  (∀ δ ∈ C, c δ = δ ∧ ∃ k₁ k₂, k₁ ∈ K ∧ c k₁ = k₁ ∧ k₂ ∈ K ∧ c k₂ = k₂ ∧ δ = k₁ * α * k₂) ∧
  ∀ x, (∃ k₁ k₂, k₁ ∈ K ∧ c k₁ = k₁ ∧ k₂ ∈ K ∧ c k₂ = k₂ ∧ x = k₁ * α * k₂) →
    ∃! δ, δ ∈ C ∧ δ⁻¹ * x ∈ K ∧ c (δ⁻¹ * x) = δ⁻¹ * x

variable {D : D7}

def cf (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) : GfC V →* GfC V where
  toFun g := ⟨GlobalTheory.LevelProduct.cmp V v g, GlobalTheory.LevelProduct.cmp_mem_GfC V v g⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)

theorem cf_val (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GfC V) :
    (cf V v g : GA D V) = GlobalTheory.LevelProduct.cmp V v g := rfl

theorem isFinIdem_fE (v : HeightOneSpectrum (𝓞 D.host.F)) : IsFinIdem D v (GlobalTheory.LevelProduct.fE D v) :=
  ⟨_, GlobalTheory.LevelProduct.epsF_spec v, rfl⟩

theorem cf_supp (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GfC V) :
    SuppF V (GlobalTheory.LevelProduct.fE D v) (cf V v g : GA D V) := GlobalTheory.LevelProduct.cmp_supp V v g

theorem cmp_eq_self {V : HSp D} {v : HeightOneSpectrum (𝓞 D.host.F)} {g : GA D V}
    (h : SuppF V (GlobalTheory.LevelProduct.fE D v) g) : GlobalTheory.LevelProduct.cmp V v g = g := by
  apply GlobalTheory.IdemSupport.mt_inj V
  rw [GlobalTheory.LevelProduct.mt_cmp, ← (GlobalTheory.IdemSupport.suppF_iff V _ g).1 h, GlobalTheory.IdemSupport.mix_self]

theorem cf_eq_self_iff (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GfC V) :
    cf V v g = g ↔ SuppF V (GlobalTheory.LevelProduct.fE D v) (g : GA D V) :=
  ⟨fun h => h ▸ cf_supp V v g, fun h => Subtype.ext (cmp_eq_self h)⟩

theorem trivAt_of_cf_eq_one (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GfC V) (h : cf V v g = 1) :
    TrivAt V (GlobalTheory.LevelProduct.fE D v) (g : GA D V) := by
  have e : GlobalTheory.LevelProduct.cmp V v (g : GA D V) = 1 := congrArg Subtype.val h
  have := GlobalTheory.LevelProduct.cmp_triv V v (g : GA D V)
  rwa [e, inv_one, mul_one] at this

theorem cf_cf (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GfC V) : cf V v (cf V v g) = cf V v g :=
  (cf_eq_self_iff V v _).2 (cf_supp V v g)

theorem cf_orth (V : HSp D) {v w : HeightOneSpectrum (𝓞 D.host.F)} (hvw : v ≠ w) (g : GfC V) :
    cf V w (cf V v g) = 1 := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have ho : GlobalTheory.LevelProduct.fE D w * GlobalTheory.LevelProduct.fE D v = 0 :=
    GlobalTheory.IdemSupport.place_orth hΦ (GlobalTheory.LevelProduct.epsF_spec w) (GlobalTheory.LevelProduct.epsF_spec v) (Ne.symm hvw)
  set h := cf V v g with hh
  have hs := cf_supp V v g
  have ht : TrivAt V (GlobalTheory.LevelProduct.fE D w) (h : GA D V) := by
    intro a b
    rw [← hs a b, ← mul_assoc, ho, zero_mul]
  apply Subtype.ext
  show GlobalTheory.LevelProduct.cmp V w (h : GA D V) = 1
  apply GlobalTheory.IdemSupport.mt_inj V
  rw [GlobalTheory.LevelProduct.mt_cmp, GlobalTheory.IdemSupport.mt_one]
  have e : GlobalTheory.LevelProduct.fE D w • mt V (h : GA D V) =
      GlobalTheory.LevelProduct.fE D w • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
    ext a b
    have := ht a b
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [Matrix.sub_apply, mul_sub, sub_eq_zero] at this
    exact this
  rw [e, GlobalTheory.IdemSupport.mix_self]

abbrev KR {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) :
    Subgroup (GfC (Wc D i)) :=
  (levW R i).subgroupOf (GfC (Wc D i))

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem kr_mem_iff (R : RealDat D A Ks) (i : Fin D.R.m) (g : GfC (Wc D i)) :
    g ∈ KR R i ↔ ∀ v, cf (Wc D i) v g ∈ KR R i := by
  have hH : (R.datWp i R.triv).P.H = ⊥ := rfl
  simp only [KR, Subgroup.mem_subgroupOf, cf_val]
  exact ⟨fun h v => GlobalTheory.LevelProduct.cmp_mem_of_mem hH h v, fun h => GlobalTheory.LevelProduct.mem_of_cmp_mem hH g.2 h⟩

theorem kr_finite (R : RealDat D A Ks) (i : Fin D.R.m) (g : GfC (Wc D i)) :
    {v | cf (Wc D i) v g ∉ KR R i}.Finite := by
  simp only [KR, Subgroup.mem_subgroupOf, cf_val]
  exact GlobalTheory.LevelProduct.finite_cmp (g : GA D (Wc D i))

end GlobalTheory.UpInj

end
