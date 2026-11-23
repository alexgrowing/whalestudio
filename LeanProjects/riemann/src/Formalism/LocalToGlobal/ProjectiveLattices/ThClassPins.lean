import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPinsRec
import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

section Field

variable (c c' : Coeff l) (hle : c.F ≤ c'.F)

abbrev incF : c.F →+* c'.F := (IntermediateField.inclusion hle).toRingHom

def AlgOver (S : Type) [CommRing S] [Algebra c.F S] [Algebra c'.F S] : Prop :=
  ∀ a : c.F, algebraMap c'.F S (incF c c' hle a) = algebraMap c.F S a

variable {c c'}

theorem embK_incF (τ : E →+* ℂ) (a : 𝓞 E) : incF c c' hle (embK c τ a) = embK c' τ a :=
  Subtype.ext rfl

theorem sOf_res {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S) :
    sOf c' S = sOf c S := by
  unfold sOf
  congr 1
  ext x
  simp only [RingHom.comp_apply]
  exact h ((IntermediateField.inclusion c.le).toRingHom x)

variable {Xo : Moduli Dw l}

theorem isEigAt_res {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S)
    (τ : E →+* ℂ) (v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) :
    IsEigAt (Xo := Xo) c' τ v ↔ IsEigAt (Xo := Xo) c τ v := by
  have key : ∀ a : 𝓞 E, algebraMap c'.F S (embK c' τ a) = algebraMap c.F S (embK c τ a) := by
    intro a
    rw [← embK_incF hle τ a]
    exact h (embK c τ a)
  unfold IsEigAt
  simp only [key]

def FrPt.res {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S)
    (y : FrPt Xo c' S) : FrPt Xo c S where
  x := y.x
  x_over := y.x_over.trans (sOf_res hle h)
  u := y.u
  tan := y.tan
  eig τ i := (isEigAt_res hle h τ _).1 (y.eig τ i)
  basis τ w ht he := y.basis τ w ht ((isEigAt_res hle h τ w).2 he)
  s := y.s
  gen := y.gen

def FrPt.ext {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S)
    (y : FrPt Xo c S) : FrPt Xo c' S where
  x := y.x
  x_over := y.x_over.trans (sOf_res hle h).symm
  u := y.u
  tan := y.tan
  eig τ i := (isEigAt_res hle h τ _).2 (y.eig τ i)
  basis τ w ht he := y.basis τ w ht ((isEigAt_res hle h τ w).1 he)
  s := y.s
  gen := y.gen

theorem FrPt.res_ext {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S)
    (y : FrPt Xo c S) : (y.ext hle h).res hle h = y := rfl

theorem FrPt.ext_res {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S)
    (y : FrPt Xo c' S) : (y.res hle h).ext hle h = y := rfl

variable {r : ℕ}

def unfBC (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) : Unf Xo c' σ' r :=
  letI : Algebra c.F (CAt σ') := (σ'.comp (incF c c' hle)).toAlgebra
  { Comp := (U (σ'.comp (incF c c' hle))).Comp
    fin := (U (σ'.comp (incF c c' hle))).fin
    X := (U (σ'.comp (incF c c' hle))).X
    un := fun k x => FrPt.ext hle (S := CAt σ') (fun _ => rfl) ((U (σ'.comp (incF c c' hle))).un k x) }

def IsBC {m : ℕ} (f' : Rul Xo c') (as : Fin m → c'.F) (fs : Fin m → Rul Xo c) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S) (y : FrPt Xo c' S),
    evR Xo c' f' y = ∑ i, algebraMap c'.F S (as i) * evR Xo c (fs i) (y.res hle h)

def CuspBC (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f' ∈ cusp Xo c' (unfBC hle U) a n,
    ∃ (m : ℕ) (as : Fin m → c'.F) (fs : Fin m → Rul Xo c), (∀ i, fs i ∈ cusp Xo c U a n) ∧ IsBC hle f' as fs

def ActBC {G : Type} [Group G] (act : G → Rul Xo c →ₗ[c.F] Rul Xo c) (act' : G → Rul Xo c' →ₗ[c'.F] Rul Xo c') :
    Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (g : G) (m : ℕ) (as : Fin m → c'.F) (fs : Fin m → Rul Xo c) (f' : Rul Xo c'),
    f' ∈ sec Xo c' a n → (∀ i, fs i ∈ sec Xo c a n) →
    IsBC hle f' as fs → IsBC hle (act' g f') as (fun i => act g (fs i))

end Field

section Comparison₂

variable {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {n : ℕ} {r : ℕ}
  {Vs : Type} [AddCommGroup Vs] [Module c'.F Vs]

def OneMapTieC (LL : IntermediateField ℚ ℂ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ0' : c'.F →+* ℂ)
    {D : D7} (V : HSp D) (dict : GA D V → Σ k, Frame ((unfBC hle U σ0').X k).Ψ r) (mu : GA D V → ℂ) (xr : ℝ)
    (a : (E →+* ℂ) × ℕ → ℕ) {G : Type} [Group G] (act : G → Rul Xo c →ₗ[c.F] Rul Xo c)
    (act' : G → Rul Xo c' →ₗ[c'.F] Rul Xo c') {Tup : Type*} (dδ : Tup → DeltaDat Xo c' n)
    (Cl' : Tup → Type) [∀ t, Fintype (Cl' t)]
    (w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c'.F) (La : ∀ t, Cl' t → GenLat E n) (Nc : ∀ t, Cl' t → ℕ)
    (gam : ∀ t, Cl' t → ℕ) (vol : Tup → c'.F) (ep : ∀ t, Cl' t → c'.F) (io : Vs →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F)
    (thAd : ∀ t, (Cl' t → Vs) → (AutQ V → ℂ)) (Pl : ∀ t, (Cl' t → Vs) → Prop) (cc : (unfBC hle U σ0').Comp → ℂ)
    (ph : ℂ) : Prop :=
  LL ≤ c'.F ∧ CuspBC hle U ∧ ActBC hle act act' ∧
    OneMapRow Xo c' V (unfBC hle U σ0') dict mu xr a act' dδ Cl' w La Nc gam vol ep io thAd Pl LL
      (cusp Xo c' (unfBC hle U) a n) cc ph

end Comparison₂

end Gen

section Dict

open scoped TensorProduct

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {n r : ℕ}

def MarkBy {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (V : HSp D) (hr : V.rank = r)
    (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) {g : ℕ}
    {lab : Fin g → D.host.E →+* ℂ} (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) lab)
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (h γ : GA D V) : Prop :=
  γ ∈ GQ V ∧
    ((U.X (dict h).1).Λ : Set (Fin r → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V (γ * h) : Set _) ∧
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V (γ * h),
        finVec V ((φ (dict h).1 (F.t (ik (dict h).1) a) : Fin r → D.host.E) ∘ Fin.cast hr) -
          (finHom V (γ * h)).1.mulVec (finVec V (ι a)) = (l.M : ℕ) • w

def CXiVal {c : Coeff l} (V : HSp D) (hr : V.rank = r) (σ0 : c.F →+* ℂ) {Tup : Type*} (dδ : Tup → DeltaDat Xo c n)
    (U₂ : ∀ t, Unf (dδ t).Xo₂ (dδ t).c₂ (σ0.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c.F)) r)
    (dict₂ : ∀ t, GA D V → Σ k, Frame ((U₂ t).X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (xi : Tup → (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) : Prop :=
  ∃ c0 : ℂ, (∃ m : ℕ, 0 < m ∧ c0 ^ m = 1) ∧ ∀ t : Tup, IsUnf (U₂ t) ∧ (∀ k, ModelW V hr ((U₂ t).X k)) ∧
    ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
      (F : FamilyUnif (dδ t).Xo₂ ((σ0.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c.F)).comp
          (IntermediateField.inclusion (dδ t).c₂.le).toRingHom)
        (fun j => relab (dδ t).c₂ (σ0.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c.F)) (e j).1))
      (ik : (U₂ t).Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] ((U₂ t).X k).Λ)
      (th : ∀ k, ((U₂ t).X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
      (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictLat (U₂ t) V hr (dict₂ t) ι e F ik φ th x₀ ∧
      ∀ h γ : GA D V, MarkBy (U₂ t) V hr (dict₂ t) ι F ik φ h γ →
        rdU (U₂ t) (dδ t).cδ (dict₂ t h).1 (dict₂ t h).2 =
          c0 * ((xi t (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ) : ℂ)

variable {c c' : Coeff l} (hle : c.F ≤ c'.F)

def actLev (c : Coeff l) {G : Type} [Group G] (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La))
    (g : G) : Rul Xo c →ₗ[c.F] Rul Xo c :=
  actL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun {S : Type} [CommRing S] [Algebra c.F S] (g' : G) (y y' : FrPt Xo c S) =>
    levActR (Xo := Xo) (c := c) lev g' y y') g

def ActLev (c : Coeff l) {G : Type} [Group G]
    (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)) : Prop :=
  ActLaws (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y')
    (fun {S : Type} [CommRing S] [Algebra c.F S] (g' : G) (y y' : FrPt Xo c S) => levActR (Xo := Xo) (c := c) lev g' y y')

def OneMapTieP (LL : IntermediateField ℚ ℂ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ0' : c'.F →+* ℂ)
    (V : HSp D) (hr : V.rank = r) (dict : GA D V → Σ k, Frame ((unfBC hle U σ0').X k).Ψ r) (mu : GA D V → ℂ) (xr : ℝ)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) {G : Type} [Group G]
    (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La))
    {Tup : Type} (dδ : Tup → DeltaDat Xo c' n) (Cl' : Tup → Type) [∀ t, Fintype (Cl' t)]
    (bad : Tup → ℕ) (Lh : ∀ t, Cl' t → Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (La : ∀ t, Cl' t → GenLat D.host.E n) (Nc : ∀ t, Cl' t → ℕ) (gam : ∀ t, Cl' t → ℕ) (vol : Tup → c'.F)
    (ep : ∀ t, Cl' t → c'.F) (B : Tup → Ideal (𝓞 D.host.E) → c'.F)
    (epF : Tup → Submodule (𝓞 D.host.E) (Fin n → D.host.E) → c'.F) (q1 d cond : ℕ)
    {Ix : Type} [Fintype Ix] (pl : Ix → (D.host.E →+* ℂ)) (lam : Ix → DomWeight n)
    (io : VVc c' lam →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F) (hw : VVc c' lam)
    (φ : ∀ t, (Fin n → LevQc Dw (dδ t).l₂) → c'.F) (w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c'.F)
    (U₂ : ∀ t, Unf (dδ t).Xo₂ (dδ t).c₂ (σ0'.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c'.F)) r)
    (dict₂ : ∀ t, GA D V → Σ k, Frame ((U₂ t).X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (xi : Tup → (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ)
    (thAd : ∀ t, (Cl' t → VVc c' lam) → (AutQ V → ℂ)) (Pl : ∀ t, (Cl' t → VVc c' lam) → Prop)
    (cc : (unfBC hle U σ0').Comp → ℂ) (ph : ℂ) : Prop :=
  Nonempty Tup ∧ (∀ t, Nonempty (Cl' t)) ∧
    ActLev (Xo := Xo) c lev ∧ ActLev (Xo := Xo) c' lev ∧
    (∀ t, BadPin (bad t) q1 d cond) ∧ RepsCov Xo c' Cl' dδ bad Lh La Nc gam ∧
    (∀ t k, ep t k = epF t (Lh t k)) ∧ (∀ t, EpIs (Dw := Dw) c' (bad t) (B t) (epF t) ∧ BAbs c' (B t)) ∧
    IoLFRec c' (fun τ => embF c' (pl τ)) lam a io hw ∧
    WPin Xo c' Cl' dδ φ w ∧
    CovPin Xo c' dδ ∧
    CXiVal V hr σ0' dδ U₂ dict₂ ι x₀ xi ∧
    OneMapTieC hle LL U σ0' V dict mu xr a (actLev c lev) (actLev c' lev) dδ Cl' w La Nc gam vol ep io thAd Pl cc ph

end Dict

end Formalism.L2.Pj
