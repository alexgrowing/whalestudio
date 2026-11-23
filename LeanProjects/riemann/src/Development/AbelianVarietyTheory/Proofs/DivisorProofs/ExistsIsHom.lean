import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomExtOfIsOpenImmersion

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Poinc.GalAut

section General

variable {o Ω₁ Ω₂ : Type} [CommRing o] [Field Ω₁] [Algebra o Ω₁] [Field Ω₂] [Algebra o Ω₂]
  {M₁ : RatModel o Ω₁} {N : RatModel o Ω₂} {φ : Ω₁ →ₐ[o] Ω₂} {q : N.Z ⟶ M₁.Z} [IsFinite q]

theorem map_ringOn (hf : M₁.IsHom N φ q) (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N.Z) (τ : Ω₂ →ₐ[o] Ω₂) (hτ : ∀ a, τ (φ a) = φ a)
    {U₀ : M₁.Z.Opens} (hU₀ : IsAffineOpen U₀) (hne : ((q ⁻¹ᵁ U₀ : N.Z.Opens) : Set N.Z).Nonempty) :
    ∀ x ∈ N.ringOn ((q ⁻¹ᵁ U₀ : N.Z.Opens) : Set N.Z), τ x ∈ N.ringOn ((q ⁻¹ᵁ U₀ : N.Z.Opens) : Set N.Z) := by
  intro x hx
  obtain ⟨f, rfl⟩ := (RatModel.mem_ringOn_iff_exists hne).1 hx
  refine RatModel.mem_ringOn.2 fun z hz => ?_
  have hzU : q z ∈ U₀ := hz
  haveI := RatModel.isIntegrallyClosed_O hn z
  letI : Algebra Γ(M₁.Z, U₀) Γ(N.Z, q ⁻¹ᵁ U₀) := (q.app U₀).hom.toAlgebra
  have hi : IsIntegral Γ(M₁.Z, U₀) f := (IsFinite.finite_app q U₀ hU₀).to_isIntegral f
  have hmem : ∀ a : Γ(M₁.Z, U₀), φ.toRingHom (M₁.res U₀ ⟨_, hzU⟩ a) ∈ N.O z := fun a => by
    have e : φ.toRingHom (M₁.res U₀ ⟨_, hzU⟩ a) = φ (valF M₁.pt U₀ a) := congrArg φ (M₁.res_apply _ _ a)
    rw [e]
    exact hf.map_mem_O (z := z) (RatModel.valF_mem_O hzU a)
  let χ : Γ(M₁.Z, U₀) →+* N.O z :=
    RingHom.codRestrict (φ.toRingHom.comp (M₁.res U₀ ⟨_, hzU⟩)) (N.O z) hmem
  let ψ : Γ(N.Z, q ⁻¹ᵁ U₀) →+* Ω₂ := τ.toRingHom.comp (N.res (q ⁻¹ᵁ U₀) hne)
  have hc : (algebraMap (N.O z) Ω₂).comp χ = ψ.comp (algebraMap Γ(M₁.Z, U₀) Γ(N.Z, q ⁻¹ᵁ U₀)) := by
    ext a
    have e := hf.valF_app ⟨_, hzU⟩ a
    change φ (M₁.res U₀ ⟨_, hzU⟩ a) = τ (N.res (q ⁻¹ᵁ U₀) hne ((q.app U₀).hom a))
    calc φ (M₁.res U₀ ⟨_, hzU⟩ a) = φ (valF M₁.pt U₀ a) := congrArg φ (M₁.res_apply _ _ a)
      _ = τ (φ (valF M₁.pt U₀ a)) := (hτ _).symm
      _ = τ (valF N.pt (q ⁻¹ᵁ U₀) (q.app U₀ a)) := congrArg τ e.symm
      _ = τ (N.res (q ⁻¹ᵁ U₀) hne ((q.app U₀).hom a)) := congrArg τ (N.res_apply _ _ _).symm
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hi.map_of_comp_eq χ ψ hc)
  have e2 : ψ f = τ (valF N.pt (q ⁻¹ᵁ U₀) f) := congrArg τ (N.res_apply _ _ f)
  have e3 : τ (valF N.pt (q ⁻¹ᵁ U₀) f) = (w : Ω₂) := e2.symm.trans hw.symm
  rw [e3]
  exact w.2

theorem exists_isHom (hf : M₁.IsHom N φ q) (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N.Z) (τ : Ω₂ →ₐ[o] Ω₂)
    (hτ : ∀ a, τ (φ a) = φ a) : ∃ s : N.Z ⟶ N.Z, N.IsHom N τ s := by
  refine RatModel.exists_isHom_of_local fun z => ?_
  obtain ⟨U₀, hU₀, hz, -⟩ := exists_isAffineOpen_mem_and_subset (U := (⊤ : M₁.Z.Opens)) (x := q z) trivial
  exact ⟨q ⁻¹ᵁ U₀, q ⁻¹ᵁ U₀, hz, hU₀.preimage q, ⟨z, hz⟩, map_ringOn hf hn τ hτ hU₀ ⟨z, hz⟩⟩

end General

section Over

variable {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂]
  [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] [Algebra o₁ Ω₂]

def overBase (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (q : M₂.Z ⟶ M₁.Z) [IsFinite q]
    (hq : M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt)
    (hA : algebraMap o₁ Ω₂ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁)) : RatModel o₁ Ω₂ where
  Z := M₂.Z
  s := q ≫ M₁.s
  sep := by haveI := M₁.sep; infer_instance
  lft := by haveI := M₁.lft; infer_instance
  qc := by haveI := M₁.qc; infer_instance
  pt := M₂.pt
  pt_s := by
    rw [← Category.assoc, hq, Category.assoc, M₁.pt_s, hA]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  gen := M₂.gen
  onto := M₂.onto

def incl (hA : algebraMap o₁ Ω₂ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁)) : Ω₁ →ₐ[o₁] Ω₂ :=
  { algebraMap Ω₁ Ω₂ with commutes' := fun r => by rw [hA]; rfl }

theorem autO_comm (hA : algebraMap o₁ Ω₂ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁)) (σ : Ω₂ ≃ₐ[Ω₁] Ω₂)
    (r : o₁) : σ (algebraMap o₁ Ω₂ r) = algebraMap o₁ Ω₂ r := by
  rw [hA]
  exact σ.commutes (algebraMap o₁ Ω₁ r)

def autO (hA : algebraMap o₁ Ω₂ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁)) (σ : Ω₂ ≃ₐ[Ω₁] Ω₂) :
    Ω₂ →ₐ[o₁] Ω₂ :=
  { (σ : Ω₂ →+* Ω₂) with commutes' := fun r => autO_comm hA σ r }

theorem autO_apply (hA : algebraMap o₁ Ω₂ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁)) (σ : Ω₂ ≃ₐ[Ω₁] Ω₂)
    (x : Ω₂) : autO hA σ x = σ x := rfl

end Over

theorem autAct : ∀ (o₁ Ω₁ o₂ Ω₂ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (q : M₂.Z ⟶ M₁.Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₂.Z → IsFinite q → M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt → ∀ σ : Ω₂ ≃ₐ[Ω₁] Ω₂, ∃ s : M₂.Z ⟶ M₂.Z, M₂.pt ≫ s = spMap (σ : Ω₂ →+* Ω₂) ≫ M₂.pt ∧ s ≫ q = q ∧ ∀ (K : Type) [Field K] (y : Sp K ⟶ M₂.Z) (b : Ω₂), M₂.val (y ≫ s) b = M₂.val y (σ b) := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ _ M₁ M₂ q hn hfin hq σ
  haveI := hfin
  letI : Algebra o₁ Ω₂ := ((algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁)).toAlgebra
  have hA : algebraMap o₁ Ω₂ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁) := rfl
  let N := overBase M₁ M₂ q hq hA
  haveI hfN : IsFinite (show N.Z ⟶ M₁.Z from q) := hfin
  have hqN : M₁.IsHom N (incl hA) q := hq
  have hnN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N.Z := hn
  obtain ⟨s, hs⟩ := exists_isHom hqN hnN (autO hA σ) fun a => σ.commutes a
  obtain ⟨t, ht⟩ := exists_isHom hqN hnN (autO hA σ.symm) fun a => σ.symm.commutes a
  have hst : s ≫ t = 𝟙 N.Z := by
    have h1 := ht.comp hs
    have e : (autO hA σ).comp (autO hA σ.symm) = AlgHom.id o₁ Ω₂ := by
      ext x
      exact σ.apply_symm_apply x
    rw [e] at h1
    exact h1.unique (RatModel.isHom_id N)
  have hsq : s ≫ q = q := by
    have h1 := hqN.comp hs
    have e : (autO hA σ).comp (incl hA) = incl hA := by
      ext a
      exact σ.commutes a
    rw [e] at h1
    exact h1.unique hqN
  refine ⟨s, hs, hsq, fun K _ y b => ?_⟩
  let w : Sp K := IsLocalRing.closedPoint K
  have hts : ∀ z, t (s z) = z := fun z => by
    rw [← Scheme.Hom.comp_apply, hst]
    rfl
  by_cases hb : b ∈ N.O (s (y w))
  · exact hs.val_comp y w hb
  · have hb' : σ b ∉ N.O (y w) := by
      intro h
      apply hb
      have h2 := ht.map_mem_O (z := s (y w)) (x := σ b) (by
        have e : N.O (t (s (y w))) = N.O (y w) := congrArg N.O (hts (y w))
        rw [e]; exact h)
      simpa [autO_apply] using h2
    have e1 : M₂.val (y ≫ s) b = 0 := RatModel.val_of_notMem (M := N) (y := y ≫ s) w hb
    have e2 : M₂.val y (σ b) = 0 := RatModel.val_of_notMem (M := N) (y := y) w hb'
    rw [e1, e2]

end GlobalTheory.Poinc.GalAut
