import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

open MonObj

namespace GlobalTheory.Poinc.DeepLab

theorem epi_spMap_field {K L : Type} [Field K] [Field L] (f : K →+* L) : Epi (spMap f) := by
  letI := f.toAlgebra
  haveI : Flat (spMap f) := by
    rw [spMap, HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (show Module.Flat K L from inferInstance)
  haveI : Surjective (spMap f) := ⟨fun z => ⟨⟨⊥, Ideal.isPrime_bot⟩, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

section Push
variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}

theorem pushHom_injective (h : IsGrpPullback A' A f φ) (T : Over S') : Function.Injective (pushHom h T) :=
  fun _ _ e => Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w]))

theorem pushHom_surjective (h : IsGrpPullback A' A f φ) (T : Over S') : Function.Surjective (pushHom h T) :=
  fun x₀ => ⟨Over.homMk (h.1.lift x₀.left T.hom (Over.w x₀)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

end Push

theorem exists_lab {Γ₁ Γ₂ H : Type} [AddCommGroup Γ₁] [AddCommGroup Γ₂] [Group H] (L : ℕ)
    (f : Multiplicative Γ₂ →* H) (s : Multiplicative Γ₁ →* H)
    (uniq : ∀ z : H, z ^ L = 1 → ∃! b : Γ₂, f (Multiplicative.ofAdd b) = z)
    (hsL : ∀ a : Γ₁, s (Multiplicative.ofAdd a) ^ L = 1) :
    ∃ lab : Γ₁ →+ Γ₂, ∀ a, f (Multiplicative.ofAdd (lab a)) = s (Multiplicative.ofAdd a) := by
  choose l hl hu using fun a => uniq _ (hsL a)
  refine ⟨AddMonoidHom.mk' l fun a b => (hu (a + b) _ ?_).symm, hl⟩
  simp only [ofAdd_add, map_mul, hl]

theorem nsmul_self_eq_zero {κ : Type} (L : ℕ) (a : κ → ZMod L) : L • a = 0 := by
  funext i
  rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]

theorem map_pow_self {κ H : Type} [Group H] (L : ℕ) (p : Multiplicative (κ → ZMod L) →* H) (a : κ → ZMod L) :
    p (Multiplicative.ofAdd a) ^ L = 1 := by
  rw [← map_pow, ← ofAdd_nsmul, nsmul_self_eq_zero, ofAdd_zero, map_one]

end GlobalTheory.Poinc.DeepLab

namespace GlobalTheory.Poinc.DeepLab

theorem exists_lab_same : ∀ {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] (S₁ : ThetaSys o₁ Ω₁) (S₂ : ThetaSys o₂ Ω₂) (ρ₁ : S₁.Real) (ρ₂ : S₂.Real) (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₁.P.A ⟶ ρ₁.P.A)) (ε₂ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₂.P.A ⟶ ρ₂.P.A)) (φ : Ω₁ →+* Ω₂) (h : S₁.R →+* S₂.R) (ψ : ρ₂.P.A.left ⟶ ρ₁.P.A.left), (∀ a, ((h a : S₂.R) : Ω₂) = φ a) → IsGrpPullback ρ₂.P.A ρ₁.P.A (spMap h) ψ → LBIso ρ₂.P.L (ρ₁.P.L.pull ψ) → (∀ E, (ε₂ E).left ≫ ψ = ψ ≫ (ε₁ E).left) → S₁.r * S₁.N ∣ S₂.r * S₂.N → ∃ lab : S₁.Gam →+ S₂.Gam, Same ρ₁ ε₁ ρ₂ ε₂ lab φ ∧ ∀ x : S₂.Gam, ∃ a, lab a = (S₂.r * S₂.N / (S₁.r * S₁.N)) • x := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ S₁ S₂ ρ₁ ρ₂ ε₁ ε₂ φ h ψ hh hpb hL hε hd
  have hcomp : S₂.R.val.toRingHom.comp h = φ.comp S₁.R.val.toRingHom := RingHom.ext fun a => hh a
  have hsp : spMap (φ.comp S₁.R.val.toRingHom) = spMap S₂.R.val.toRingHom ≫ spMap h := by
    rw [← hcomp, spMap_comp]
  let K := AlgebraicClosure Ω₂
  let x₀ : Sp K ⟶ Sp S₂.R := spMap (algebraMap Ω₂ K) ≫ spMap S₂.R.val.toRingHom
  let U : Over.mk ((baseOver (Sp S₂.R)).hom ≫ spMap h) ⟶ baseOver (Sp S₁.R) := Over.homMk (spMap h) (by simp)
  let V₂ : Over.mk x₀ ⟶ baseOver (Sp S₂.R) := Over.homMk x₀ (by simp)
  let p₁ : Multiplicative S₁.Gam →* (baseOver (Sp S₁.R) ⟶ ρ₁.P.A) :=
    MonoidHom.mk' (fun a => ρ₁.pt (Multiplicative.toAdd a)) fun a b => ρ₁.pt_add _ _
  let p₂ : Multiplicative S₂.Gam →* (baseOver (Sp S₂.R) ⟶ ρ₂.P.A) :=
    MonoidHom.mk' (fun a => ρ₂.pt (Multiplicative.toAdd a)) fun a b => ρ₂.pt_add _ _
  have hbij : Function.Bijective (pushHom hpb (baseOver (Sp S₂.R))) :=
    ⟨pushHom_injective hpb _, pushHom_surjective hpb _⟩
  let e := MulEquiv.ofBijective (pushHom hpb (baseOver (Sp S₂.R))) hbij
  let σ : Multiplicative S₁.Gam →* (baseOver (Sp S₂.R) ⟶ ρ₂.P.A) := e.symm.toMonoidHom.comp ((preHom U).comp p₁)
  have hσ : ∀ a, pushHom hpb _ (σ a) = U ≫ ρ₁.pt (Multiplicative.toAdd a) := fun a =>
    e.apply_symm_apply (U ≫ ρ₁.pt (Multiplicative.toAdd a))
  have hσl : ∀ a, (σ a).left ≫ ψ = spMap h ≫ (ρ₁.pt (Multiplicative.toAdd a)).left := fun a =>
    congrArg (fun q => q.left) (hσ a)
  have uniq : ∀ z : Over.mk x₀ ⟶ ρ₂.P.A, z ^ (S₂.r * S₂.N) = 1 →
      ∃! b : S₂.Gam, (preHom V₂).comp p₂ (Multiplicative.ofAdd b) = z := fun z hz =>
    ρ₂.pt_bij K x₀ z hz
  have hσL : ∀ a : S₁.Gam, σ (Multiplicative.ofAdd a) ^ (S₂.r * S₂.N) = 1 := by
    intro a
    obtain ⟨c, hc⟩ := hd
    rw [hc, pow_mul, map_pow_self, one_pow]
  have hsL : ∀ a : S₁.Gam, (preHom V₂).comp σ (Multiplicative.ofAdd a) ^ (S₂.r * S₂.N) = 1 := by
    intro a
    rw [MonoidHom.comp_apply, ← map_pow, hσL, map_one]
  obtain ⟨lab, hlab⟩ := exists_lab _ _ _ uniq hsL
  have hlabl : ∀ a : S₁.Gam, x₀ ≫ (ρ₂.pt (lab a)).left = x₀ ≫ (σ (Multiplicative.ofAdd a)).left := fun a =>
    congrArg (fun q => q.left) (hlab a)
  haveI := epi_spMap_field (algebraMap Ω₂ K)
  refine ⟨lab, ?_, ?_⟩
  · let P₀ := GlobalTheory.StrictPull.polPull ρ₂.P (spMap S₂.R.val.toRingHom)
    refine ⟨P₀, pullback.fst ρ₂.P.A.hom (spMap S₂.R.val.toRingHom) ≫ ψ,
      pullback.fst ρ₂.P.A.hom (spMap S₂.R.val.toRingHom),
      fun E => (Over.pullback (spMap S₂.R.val.toRingHom)).map (ε₂ E), ?_, isGrpPullback_pullback _ _, ?_,
      GlobalTheory.PolBaseChange.lbIso_refl P₀.isLB, ?_, ?_⟩
    · rw [hsp]; exact IsGrpPullback.comp (isGrpPullback_pullback _ _) hpb
    · exact GlobalTheory.PolDeg.lbIso_pull_comp hL _ rfl
    · intro E
      have e₁ : ((Over.pullback (spMap S₂.R.val.toRingHom)).map (ε₂ E)).left ≫
          pullback.fst ρ₂.P.A.hom (spMap S₂.R.val.toRingHom) =
          pullback.fst ρ₂.P.A.hom (spMap S₂.R.val.toRingHom) ≫ (ε₂ E).left := pullback.lift_fst _ _ _
      refine ⟨?_, e₁⟩
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ψ) e₁).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) (hε E)).trans (Category.assoc _ _ _).symm)))
    · intro x
      refine ⟨pullback.lift (spMap S₂.R.val.toRingHom ≫ (ρ₂.pt (lab x)).left) (𝟙 _) ?_, ?_,
        pullback.lift_fst _ _ _⟩
      · rw [Category.assoc, Over.w]; simp
      · refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ψ) (pullback.lift_fst _ _ _)).trans ?_)
        rw [hsp, ← cancel_epi (spMap (algebraMap Ω₂ K))]
        have e₂ := congrArg (· ≫ ψ) (hlabl x)
        simp only [x₀, Category.assoc] at e₂ ⊢
        rw [e₂, hσl]
        rfl
  · intro x
    set y := (S₂.r * S₂.N / (S₁.r * S₁.N)) • x with hy
    have hyL : p₂ (Multiplicative.ofAdd y) ^ (S₁.r * S₁.N) = 1 := by
      rw [← map_pow, ← ofAdd_nsmul, hy, smul_smul, Nat.mul_div_cancel' hd, nsmul_self_eq_zero, ofAdd_zero, map_one]
    let T₀ : Over (Sp S₂.R) := Over.mk x₀
    let V₁ : Over.mk (x₀ ≫ spMap h) ⟶ baseOver (Sp S₁.R) := Over.homMk (x₀ ≫ spMap h) (by simp)
    let z₁ : Over.mk (x₀ ≫ spMap h) ⟶ ρ₁.P.A := pushHom hpb T₀ (V₂ ≫ ρ₂.pt y)
    have hz₁ : z₁ ^ (S₁.r * S₁.N) = 1 := by
      have h0 : (V₂ ≫ ρ₂.pt y) ^ (S₁.r * S₁.N) = 1 := by
        have h3 := congrArg (preHom V₂) hyL
        rwa [map_pow, map_one] at h3
      show (pushHom hpb T₀) _ ^ _ = 1
      rw [← map_pow, h0, map_one]
    obtain ⟨a, ha, -⟩ := ρ₁.pt_bij K (x₀ ≫ spMap h) z₁ hz₁
    refine ⟨a, ?_⟩
    have hpush : pushHom hpb T₀ (V₂ ≫ σ (Multiplicative.ofAdd a)) = V₁ ≫ ρ₁.pt a := by
      apply Over.OverMorphism.ext
      show (V₂ ≫ σ _).left ≫ ψ = (V₁ ≫ ρ₁.pt a).left
      simp only [Over.comp_left, Category.assoc, V₂, V₁, Over.homMk_left]
      rw [hσl]
      rfl
    have h1 : V₂ ≫ σ (Multiplicative.ofAdd a) = V₂ ≫ ρ₂.pt y := pushHom_injective hpb T₀ (hpush.trans ha)
    have h2 : (V₂ ≫ ρ₂.pt y) ^ (S₂.r * S₂.N) = 1 := by
      have h3 := congrArg (preHom V₂) (map_pow_self _ p₂ y)
      rwa [map_pow, map_one] at h3
    exact (uniq _ h2).unique ((hlab a).trans h1) rfl

end GlobalTheory.Poinc.DeepLab
