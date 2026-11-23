import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

noncomputable section

namespace GlobalTheory.CompanionTheory.KunGlue

variable {K : Type} [Field K]

def topResEquiv (hT : TopRes) {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} K) (U : ObjectProperty C)
    (hU : ∀ T, U T) (n : ℕ) : CH.H F n ≃ₗ[K] CH.H (U.ι ⋙ F) n :=
  LinearEquiv.ofBijective ((CH.Mor.restrict F U.ι).pull n)
    (CrystallineSemistableComparison.P.mapH_bij (CH.Mor.restrict F U.ι).hom (fun m => (hT K C F U ⊥ hU m).1) n)

theorem cls_congr' {R : Type} [CommRing R] {L : Cx.{1} R} {n : ℕ} {x y : L.X n} (e : x = y) (hx : L.d n x = 0)
    (hy : L.d n y = 0) : L.cls x hx = L.cls y hy := by
  subst e
  rfl

theorem XD.pr_restrict (E : XD K) (U₁ : ObjectProperty E.C₁) (U₂ : ObjectProperty E.C₂) (U₃ : ObjectProperty E.D)
    (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T)) {a a' c p q n : ℕ} (ha : a + a' = c)
    (h : p + q = n) (x : CH.Cn (E.F₁ a) p) (y : CH.Cn (E.F₂ a') q) :
    (E.pr U₁ U₂ U₃ h₁ h₂ ha).μ h ((CH.Mor.restrict (E.F₁ a) U₁.ι).pullC p x)
        ((CH.Mor.restrict (E.F₂ a') U₂.ι).pullC q y) =
      (CH.Mor.restrict (E.F₃ c) U₃.ι).pullC n
        ((E.μ ha).cupC h ((E.m₁ a).pullC p x) ((E.m₂ a').pullC q y)) := by
  funext s
  rfl

theorem XD.kun_cup (hT : TopRes) (E : XD K) (U₁ : ObjectProperty E.C₁) (U₂ : ObjectProperty E.C₂)
    (U₃ : ObjectProperty E.D) (hU₁ : ∀ T, U₁ T) (hU₂ : ∀ T, U₂ T) (hU₃ : ∀ T, U₃ T)
    (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T)) {c n : ℕ}
    (e : (⨁ t : Idx c n, (CH.cx (U₁.ι ⋙ E.F₁ t.a)).H t.i ⊗[K] (CH.cx (U₂.ι ⋙ E.F₂ t.a')).H t.j) ≃ₗ[K]
      (CH.cx (U₃.ι ⋙ E.F₃ c)).H n)
    (he : ∀ (t : Idx c n) (x : (CH.cx (U₁.ι ⋙ E.F₁ t.a)).X t.i) (y : (CH.cx (U₂.ι ⋙ E.F₂ t.a')).X t.j)
      (hx : (CH.cx (U₁.ι ⋙ E.F₁ t.a)).d t.i x = 0) (hy : (CH.cx (U₂.ι ⋙ E.F₂ t.a')).d t.j y = 0)
      (hz : (CH.cx (U₃.ι ⋙ E.F₃ c)).d n ((E.pr U₁ U₂ U₃ h₁ h₂ t.ha).μ t.h x y) = 0),
      e (DirectSum.lof K _ (fun t : Idx c n => (CH.cx (U₁.ι ⋙ E.F₁ t.a)).H t.i ⊗[K] (CH.cx (U₂.ι ⋙ E.F₂ t.a')).H t.j) t
        ((CH.cx (U₁.ι ⋙ E.F₁ t.a)).cls x hx ⊗ₜ (CH.cx (U₂.ι ⋙ E.F₂ t.a')).cls y hy)) =
        (CH.cx (U₃.ι ⋙ E.F₃ c)).cls ((E.pr U₁ U₂ U₃ h₁ h₂ t.ha).μ t.h x y) hz)
    (t : Idx c n) (u : CH.H (E.F₁ t.a) t.i) (v : CH.H (E.F₂ t.a') t.j) :
    topResEquiv hT (E.F₃ c) U₃ hU₃ n
        ((E.μ t.ha).cup t.h ((E.m₁ t.a).pull t.i u) ((E.m₂ t.a').pull t.j v)) =
      e (DirectSum.lof K _ (fun t : Idx c n => (CH.cx (U₁.ι ⋙ E.F₁ t.a)).H t.i ⊗[K] (CH.cx (U₂.ι ⋙ E.F₂ t.a')).H t.j) t
        (topResEquiv hT (E.F₁ t.a) U₁ hU₁ t.i u ⊗ₜ topResEquiv hT (E.F₂ t.a') U₂ hU₂ t.j v)) := by
  obtain ⟨x, hx, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj u
  obtain ⟨y, hy, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj v
  have hx₁ := CrystallineSemistableComparison.CechClassBoundaries.cyc (E.m₁ t.a).hom x hx
  have hy₁ := CrystallineSemistableComparison.CechClassBoundaries.cyc (E.m₂ t.a').hom y hy
  obtain ⟨hc, ec⟩ := CrystallineSemistableComparison.P.cup_cls (E.μ t.ha) t.h _ _ hx₁ hy₁
  have hx₂ := CrystallineSemistableComparison.CechClassBoundaries.cyc (CH.Mor.restrict (E.F₁ t.a) U₁.ι).hom x hx
  have hy₂ := CrystallineSemistableComparison.CechClassBoundaries.cyc (CH.Mor.restrict (E.F₂ t.a') U₂.ι).hom y hy
  have hc₂ := CrystallineSemistableComparison.CechClassBoundaries.cyc (CH.Mor.restrict (E.F₃ c) U₃.ι).hom _ hc
  have hz : (CH.cx (U₃.ι ⋙ E.F₃ c)).d n ((E.pr U₁ U₂ U₃ h₁ h₂ t.ha).μ t.h
      ((CH.Mor.restrict (E.F₁ t.a) U₁.ι).pullC t.i x) ((CH.Mor.restrict (E.F₂ t.a') U₂.ι).pullC t.j y)) = 0 := by
    rw [XD.pr_restrict]
    exact hc₂
  have key := he t _ _ hx₂ hy₂ hz
  refine Eq.trans ?_ key.symm |>.trans rfl
  change (CH.Mor.restrict (E.F₃ c) U₃.ι).pull n ((E.μ t.ha).cup t.h ((CH.cx _).cls _ hx₁) ((CH.cx _).cls _ hy₁)) = _
  rw [ec]
  exact cls_congr' (XD.pr_restrict E U₁ U₂ U₃ h₁ h₂ t.ha t.h x y).symm hc₂ hz

def sliceMap {A₀ B₀ A B : Type*} [AddCommGroup A₀] [Module K A₀] [AddCommGroup B₀] [Module K B₀] [AddCommGroup A]
    [Module K A] [AddCommGroup B] [Module K B] (r₁ : A₀ ≃ₗ[K] A) (r₂ : B₀ ≃ₗ[K] B) (φ : Module.Dual K A₀) :
    A ⊗[K] B →ₗ[K] B₀ :=
  (TensorProduct.lid K B₀).toLinearMap ∘ₗ TensorProduct.map (φ ∘ₗ r₁.symm.toLinearMap) r₂.symm.toLinearMap

theorem sliceMap_tmul {A₀ B₀ A B : Type*} [AddCommGroup A₀] [Module K A₀] [AddCommGroup B₀] [Module K B₀] [AddCommGroup A]
    [Module K A] [AddCommGroup B] [Module K B] (r₁ : A₀ ≃ₗ[K] A) (r₂ : B₀ ≃ₗ[K] B) (φ : Module.Dual K A₀) (u : A₀) (v : B₀) :
    sliceMap r₁ r₂ φ (r₁ u ⊗ₜ r₂ v) = φ u • v := by
  simp [sliceMap]

def compMap {ι : Type*} [DecidableEq ι] (N : ι → Type*) [∀ t, AddCommGroup (N t)] [∀ t, Module K (N t)]
    {A T W : Type*} [AddCommGroup A] [Module K A] [AddCommGroup T] [Module K T] [AddCommGroup W] [Module K W]
    (ρ : A ≃ₗ[K] T) (e : (⨁ t, N t) ≃ₗ[K] T) (t₀ : ι) (g : N t₀ →ₗ[K] W) : A →ₗ[K] W :=
  g ∘ₗ DirectSum.component K ι N t₀ ∘ₗ e.symm.toLinearMap ∘ₗ ρ.toLinearMap

theorem compMap_self {ι : Type*} [DecidableEq ι] (N : ι → Type*) [∀ t, AddCommGroup (N t)] [∀ t, Module K (N t)]
    {A T W : Type*} [AddCommGroup A] [Module K A] [AddCommGroup T] [Module K T] [AddCommGroup W] [Module K W]
    (ρ : A ≃ₗ[K] T) (e : (⨁ t, N t) ≃ₗ[K] T) (t₀ : ι) (g : N t₀ →ₗ[K] W) (x : A) (w : N t₀)
    (hx : ρ x = e (DirectSum.lof K ι N t₀ w)) : compMap N ρ e t₀ g x = g w := by
  simp only [compMap, LinearMap.comp_apply, LinearEquiv.coe_coe, hx, LinearEquiv.symm_apply_apply]
  rw [DirectSum.component.lof_self]

theorem compMap_ne {ι : Type*} [DecidableEq ι] (N : ι → Type*) [∀ t, AddCommGroup (N t)] [∀ t, Module K (N t)]
    {A T W : Type*} [AddCommGroup A] [Module K A] [AddCommGroup T] [Module K T] [AddCommGroup W] [Module K W]
    (ρ : A ≃ₗ[K] T) (e : (⨁ t, N t) ≃ₗ[K] T) (t₀ : ι) (g : N t₀ →ₗ[K] W) (x : A) (t : ι) (w : N t) (ht : t ≠ t₀)
    (hx : ρ x = e (DirectSum.lof K ι N t w)) : compMap N ρ e t₀ g x = 0 := by
  simp only [compMap, LinearMap.comp_apply, LinearEquiv.coe_coe, hx, LinearEquiv.symm_apply_apply]
  rw [DirectSum.component.of, dif_neg ht, map_zero]

theorem XD.slant (hT : TopRes) (E : XD K) (U₁ : ObjectProperty E.C₁) (U₂ : ObjectProperty E.C₂)
    (U₃ : ObjectProperty E.D) (hU₁ : ∀ T, U₁ T) (hU₂ : ∀ T, U₂ T) (hU₃ : ∀ T, U₃ T)
    (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T)) (hK : E.Kun U₁ U₂ U₃ h₁ h₂)
    (a i a' j c n : ℕ) (ha : a + a' = c) (h : i + j = n) (φ : Module.Dual K (CH.H (E.F₁ a) i)) :
    ∃ sl : CH.H (E.F₃ c) n →ₗ[K] CH.H (E.F₂ a') j,
      (∀ u v, sl ((E.μ ha).cup h ((E.m₁ a).pull i u) ((E.m₂ a').pull j v)) = φ u • v) ∧
      ∀ (b i' b' j' : ℕ) (hb : b + b' = c) (h' : i' + j' = n), (b, i') ≠ (a, i) →
        ∀ (u : CH.H (E.F₁ b) i') (v : CH.H (E.F₂ b') j'),
          sl ((E.μ hb).cup h' ((E.m₁ b).pull i' u) ((E.m₂ b').pull j' v)) = 0 := by
  obtain ⟨e, he⟩ := hK c n
  have kc := XD.kun_cup hT E U₁ U₂ U₃ hU₁ hU₂ hU₃ h₁ h₂ e he
  refine ⟨compMap (fun t : Idx c n => (CH.cx (U₁.ι ⋙ E.F₁ t.a)).H t.i ⊗[K] (CH.cx (U₂.ι ⋙ E.F₂ t.a')).H t.j)
    (topResEquiv hT (E.F₃ c) U₃ hU₃ n) e ⟨a, i, a', j, ha, h⟩
    (sliceMap (topResEquiv hT (E.F₁ a) U₁ hU₁ i) (topResEquiv hT (E.F₂ a') U₂ hU₂ j) φ), ?_, ?_⟩
  · intro u v
    exact (compMap_self _ _ e _ _ _ _ (kc ⟨a, i, a', j, ha, h⟩ u v)).trans (sliceMap_tmul _ _ φ u v)
  · intro b i' b' j' hb h' hne u v
    refine compMap_ne _ _ e _ _ _ ⟨b, i', b', j', hb, h'⟩ _ ?_ (kc ⟨b, i', b', j', hb, h'⟩ u v)
    intro hh
    exact hne (by rw [show b = a from congrArg Idx.a hh, show i' = i from congrArg Idx.i hh])

theorem slant_of_kun : TopRes → SiteLaws → (∀ (K : Type) [Field K] [CharZero K] (X X' P : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) [IsProper q] [Smooth q] [IsProper q'] [Smooth q'] (p₁ : P ⟶ X) (p₂ : P ⟶ X') (hP : IsPullback p₁ p₂ q q'), ∀ (h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T)) (h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q' ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T)), (hodgeXD q q' p₁ p₂ hP.w.symm).Kun (inU q ⊤) (inU q' ⊤) (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤)) h₁ h₂) → Slant := by
  intro hT hS hK K _ _ X X' P q q' _ _ _ _ p₁ p₂ hP a i a' j c n ha h φ
  have top₁ : ∀ T, inU q ⊤ T := fun T => (hS K X X X q (𝟙 X) (𝟙 X)).2.2.1 T
  have top₂ : ∀ T, inU q' ⊤ T := fun T => (hS K X' X' X' q' (𝟙 X') (𝟙 X')).2.2.1 T
  have topP : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T := by
    have e : p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤ = ⊤ := by simp
    rw [e]
    exact fun T => (hS K P P P (p₁ ≫ q) (𝟙 P) (𝟙 P)).2.2.1 T
  have h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T) :=
    fun T _ => top₁ _
  have h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q' ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T) :=
    fun T _ => top₂ _
  exact XD.slant hT (hodgeXD q q' p₁ p₂ hP.w.symm) (inU q ⊤) (inU q' ⊤) (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤))
    top₁ top₂ topP h₁ h₂ (hK K X X' P q q' p₁ p₂ hP h₁ h₂) a i a' j c n ha h φ

end GlobalTheory.CompanionTheory.KunGlue
