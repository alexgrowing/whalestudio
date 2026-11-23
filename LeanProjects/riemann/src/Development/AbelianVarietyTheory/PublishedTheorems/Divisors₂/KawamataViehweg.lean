import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
import Development.AbelianVarietyTheory.Definitions.Divisors.SmoothOfRelativeDimensionPspace

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CechPic

namespace GlobalTheory.Published

def KawamataViehweg : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)]
    [IsIntegral X] (D : ℕ) [SmoothOfRelativeDimension D (strHom k X)],
    IsProjOver (strHom k X) →
    ∀ (K : CanonLB (strHom k X) D) (N : LB X), IsNef k N → IsBig k N →
      ∀ q : ℕ, 0 < q → Subsingleton (coh (LB.toMod (tens K.bundle N)) q)

theorem KawamataViehweg.of_hom (h : KawamataViehweg) {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] [IsIntegral X] {p : X ⟶ Sp k}
    (hp : ∀ r, algebraMap k Γ(X, ⊤) r = p.appTop ((Scheme.ΓSpecIso (.of k)).inv r))
    {D : ℕ} [SmoothOfRelativeDimension D p] (hX : IsProjOver p) (K : CanonLB p D) {N : LB X}
    (h₁ : IsNef k N) (h₂ : IsBig k N) {q : ℕ} (hq : 0 < q) :
    Subsingleton (coh (LB.toMod (tens K.bundle N)) q) := by
  obtain rfl := strHom_eq hp
  exact h k X D hX K N h₁ h₂ q hq

theorem KawamataViehweg.twist (h : KawamataViehweg) {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] [IsIntegral X] {p : X ⟶ Sp k}
    (hp : ∀ r, algebraMap k Γ(X, ⊤) r = p.appTop ((Scheme.ΓSpecIso (.of k)).inv r))
    {D : ℕ} [SmoothOfRelativeDimension D p] (hX : IsProjOver p) (K : CanonLB p D) {N M : LB X}
    (h₁ : IsNef k N) (h₂ : IsBig k N) (hM : M.IsLB)
    (e : cls M hM = cls K.bundle K.isLB + cls N h₁.isLB) {q : ℕ} (hq : 0 < q) :
    Subsingleton (coh (twist (structureModule X) M) q) := by
  obtain ⟨i⟩ := nonempty_twist_iso_of_cls_eq (structureModule X) hM (isLB_tens K.isLB h₁.isLB) e
  exact (cohOn.mapIso Γ(X, ⊤) ⊤ q (i ≪≫ Twist.unitTwistIso _)).toEquiv.subsingleton_congr.2
    (h.of_hom hp hX K h₁ h₂ hq)

open GlobalTheory.ProjSpace in

example (D : ℕ) : IsIntegral (PSpace ℂ D) ∧ IsProjOver (strHom ℂ (PSpace ℂ D)) ∧
    IsNef ℂ (O1 ℂ D) ∧ IsBig ℂ (O1 ℂ D) ∧
    ∃ _ : SmoothOfRelativeDimension D (strHom ℂ (PSpace ℂ D)),
      Nonempty (CanonLB (strHom ℂ (PSpace ℂ D)) D) := by
  rw [strHom_eq (algebraMap_top_eq ℂ D)]
  have hs := Adelic.smoothOfRelativeDimension_pspace ℂ D
  exact ⟨inferInstance, isProjOver_str ℂ D, isNef_twistingSheaf ℂ D, isBig_twistingSheaf ℂ D,
    hs, CanonLB.nonempty⟩

end GlobalTheory.Published
