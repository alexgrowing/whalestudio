import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ThetaBaseChange

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ThetaCoord GlobalTheory.CommPairing GlobalTheory.GlobalLift GlobalTheory.VVRank

variable {S : Scheme.{0}} (P : PolAV S) {T T' : Over S}

theorem isThetaPtOver_pull_of_gen {n : ℕ} {I : Type} {x : I → (T ⟶ P.A)} {v : I → Γ(T.left, ⊤)}
    (H : IsThetaPtOver P n x v) (h : T' ⟶ T)
    (hg : ∀ th, IsGenSec P.A P.L 1 th → IsGenSec P.A P.L 1 (pullS P.A 1 h th)) :
    IsThetaPtOver P n (fun a => h ≫ x a) (fun a => h.left.appTop.hom (v a)) := by
  have hL := P.isLB
  obtain ⟨th, s₁, α, τ, U, s₂, w, u, hth, hα, hτ, hs₁, hU, hs₂, hw, hv⟩ := H
  obtain ⟨α', hα', k₁⟩ := exists_twist_pull P.A (ψ := mulT P.A T n) (hm := lift_snd _ _) (b := 1)
    hL hα h (ψ' := mulT P.A T' n) (lift_snd _ _) (mulT_comm P.A h n)
  obtain ⟨τ', hτ', k₂⟩ := exists_gen_pullTo (φ' := fun _ : Fin 1 => (1 : T' ⟶ P.A).left) τ hτ h.left
    (fun _ => by rw [← Over.comp_left, MonObj.comp_one])
  choose U' hU' k₃ using fun a => exists_symLift_act_pull hL h (hU a)
  refine ⟨_, _, α', τ', U', fun a => pullS P.A _ h (s₂ a), fun a => h.left.appTop.hom (w a),
    Units.map h.left.appTop.hom.toMonoidHom u, hg _ hth, hα', hτ', k₁ _ _ hs₁, hU',
    fun a => k₃ a _ _ (hs₂ a), fun a => isValueAt_of_sv hL hτ' fun z J hJ => ?_, fun a => ?_⟩
  · have q := sv_of_isValueAt (hw a) h hJ
    rw [MonObj.comp_one] at q
    rw [sv_pullS _ _ _ _ _ z hJ, ← Over.comp_left, lift_whiskerRight, Category.id_comp, q, k₂ _ _ z J hJ,
      Category.id_comp]
    exact congrArg (· * _) ((gs_pull (𝟙 _) h.left z ⊤ trivial _).trans (by rw [Category.id_comp])).symm
  · exact (congrArg h.left.appTop.hom (hv a)).trans (map_mul _ _ _)

theorem exists_basicOpen_isGenSec (hS : SecBaseChangeAnySt) [IsAffine T.left] (V : T.left.Opens) (p : T.left)
    (hp : p ∈ V) : ∃ f : Γ(T.left, ⊤), p ∈ T.left.basicOpen f ∧
      ∃ j : overRes (T.left.basicOpen f) ⟶ overRes V, j ≫ overResι V = overResι _ ∧
        ∀ th, IsGenSec P.A P.L 1 th → IsGenSec P.A P.L 1 (pullS P.A 1 j th) := by
  obtain ⟨V₀, hV, b, hb⟩ := hS S P 1 le_rfl (T.hom p)
  have hq : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  obtain ⟨f, hf, hpf⟩ := (isAffineOpen_top T.left).exists_basicOpen_le (V := V ⊓ T.hom ⁻¹ᵁ V₀) ⟨p, hp, hV⟩ trivial
  let W := T.left.basicOpen f
  let l : overRes W ⟶ overRes (T := baseOver S) V₀ := Over.homMk
    (IsOpenImmersion.lift V₀.ι (W.ι ≫ T.hom) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      exact (hf y.2).2)) ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _))
  have hle : W ≤ V := hf.trans inf_le_left
  let j : overRes W ⟶ overRes V := Over.homMk (T.left.homOfLE hle) (by
    change T.left.homOfLE hle ≫ V.ι ≫ T.hom = W.ι ≫ T.hom
    rw [← Category.assoc, Scheme.homOfLE_ι])
  have hj : j ≫ overResι V = overResι W := Over.OverMorphism.ext (T.left.homOfLE_ι hle)
  refine ⟨f, hpf, j, hj, fun th H s => ?_⟩
  have hW : IsAffineOpen W := (isAffineOpen_top _).basicOpen f
  have : IsAffine (overRes W).left := hW
  obtain ⟨c, hc⟩ := exists_basis P 1 b hb (overRes W) l
  obtain ⟨n, u, hu⟩ := EmbPull.exists_pow_extend_secM P 1 f (pullM P.A P.L 1 l (SecM.ofSec P.A (b hq.default)))
  obtain ⟨r, hr⟩ := H (pullS P.A 1 (overResι V) (SecM.toSec P.A u))
  have hr' : pullM P.A P.L 1 (overResι V) u = r • SecM.ofSec P.A th := Subtype.ext (funext hr)
  have e₁ := congrArg (pullM P.A P.L 1 j) hr'
  rw [pullM_comp _ P.isLB, hj, hu, LinearMap.map_smulₛₗ] at e₁
  obtain ⟨d, hd⟩ : ∃ d : Γ((overRes W).left, ⊤), SecM.ofSec P.A s =
      d • pullM P.A P.L 1 l (SecM.ofSec P.A (b hq.default)) := by
    have := c.sum_repr (SecM.ofSec P.A s)
    rw [Fintype.sum_unique, hc] at this
    exact ⟨_, this.symm⟩
  have hf₁ : IsUnit (W.ι.appTop.hom f) := by
    refine W.toScheme.toRingedSpace.isUnit_of_isUnit_germ ⊤ _ fun y _ => ?_
    refine (Scheme.mem_basicOpen_top _ _ y).1 ?_
    rw [← Scheme.preimage_basicOpen_top]
    exact y.2
  obtain ⟨a, ha⟩ : IsUnit ((overResι W).left.appTop.hom (f ^ n)) := by
    rw [map_pow]
    exact hf₁.pow n
  have key : SecM.ofSec P.A s = (d * (a⁻¹ : Γ((overRes W).left, ⊤)ˣ) * j.left.appTop.hom r) •
      pullM P.A P.L 1 j (SecM.ofSec P.A th) := by
    rw [mul_smul, ← e₁, ← ha, ← mul_smul, Units.inv_mul_cancel_right, hd]
  exact ⟨_, fun i => congrArg (fun q => q.1 i) key⟩

theorem isThetaPt_pull (hS : SecBaseChangeAnySt) [IsAffine T.left] [IsAffine T'.left] (h : T' ⟶ T) {n : ℕ} {I : Type}
    {x : I → (T ⟶ P.A)} {v : I → Γ(T.left, ⊤)} (H : IsThetaPt P n x v) :
    IsThetaPt P n (fun a => h ≫ x a) (fun a => h.left.appTop.hom (v a)) := by
  obtain ⟨h₁, h₂, H⟩ := H
  refine ⟨h₁, by simpa using h₂.map h.left.appTop.hom, fun p => ?_⟩
  obtain ⟨V, hV, H⟩ := H (h.left p)
  obtain ⟨f, hf, j, hj, hg⟩ := exists_basicOpen_isGenSec P hS V _ hV
  let f' := h.left.appTop.hom f
  have hf' : h.left ⁻¹ᵁ T.left.basicOpen f = T'.left.basicOpen f' := Scheme.preimage_basicOpen_top _ _
  let W := T.left.basicOpen f
  let W' := T'.left.basicOpen f'
  let k₀ : W'.toScheme ⟶ W.toScheme := IsOpenImmersion.lift W.ι (W'.ι ≫ h.left) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      exact hf'.ge y.2)
  have hk₀ : k₀ ≫ W.ι = W'.ι ≫ h.left := IsOpenImmersion.lift_fac _ _ _
  let k : overRes W' ⟶ overRes W := Over.homMk k₀ (by
    change k₀ ≫ W.ι ≫ T.hom = W'.ι ≫ T'.hom
    rw [← Category.assoc, hk₀, Category.assoc, Over.w])
  have hk : k ≫ overResι W = overResι W' ≫ h := Over.OverMorphism.ext hk₀
  have hW : IsAffineOpen W := (isAffineOpen_top _).basicOpen f
  have hW' : IsAffineOpen W' := (isAffineOpen_top _).basicOpen f'
  have : IsAffine (overRes W).left := hW
  have : IsAffine (overRes W').left := hW'
  have Q := isThetaPtOver_pull_of_gen P (isThetaPtOver_pull_of_gen P H j hg) k
    fun _ => EmbPull.isGenSec_pullS P hS k
  have e : k ≫ j ≫ overResι V = overResι W' ≫ h := by rw [hj]; exact hk
  refine ⟨W', hf'.le hf, ?_⟩
  convert Q using 2 with a a
  · rw [← Category.assoc, ← e]
    simp only [Category.assoc]
  · exact (congrArg (fun q => q.left.appTop.hom (v a)) e).symm

end GlobalTheory.ThetaBaseChange

theorem GlobalTheory.hasTh_baseChange : Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R), t.HasTh x v → t.HasTh (spMap φ ≫ x) (fun a => φ (v a)) := by
  intro hl o _ g N' J b S s t R R' _ _ φ x v H
  have : IsAffine (Over.mk x).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (Over.mk (spMap φ ≫ x)).left := inferInstanceAs (IsAffine (Spec _))
  have Q := GlobalTheory.ThetaBaseChange.isThetaPt_pull t.pol hl.secBaseChangeAny
    (Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ x) ⟶ Over.mk x) H
  unfold TObj.HasTh
  convert Q using 2 with a a
  · exact Over.OverMorphism.ext (Category.assoc (spMap φ) x (t.lab a).left)
  · exact congrArg (fun q => q.hom (v a)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))

end
