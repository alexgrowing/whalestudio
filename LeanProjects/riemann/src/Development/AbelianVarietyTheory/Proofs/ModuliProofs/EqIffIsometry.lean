import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivOfPeriod
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPullCubicalOfIso
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsReducedSchemeOfSmoothOfIsIntegrallyClosed

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.UnifPoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ}

def HomAlg : Prop :=
  ∀ (P P' : Out.PolAV (Sp ℂ)) (g : ℕ) (u : HolUnif P.A P.L g) (u' : HolUnif P'.A P'.L g)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), P.g = g → P'.g = g → (∀ z ∈ u.Λ, F z ∈ u'.Λ) →
    ∃ f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, u'.ex (F z) = u.ex z ≫ f

def WeilDet : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (P P' : Out.PolAV (Sp k)) (α : P.A ⟶ P'.A) (p d : ℕ), IsMonHom α →
    p.Prime → CharZero k → (∀ (n : ℕ) (x y : 𝟙_ (Over (Sp k)) ⟶ P.A) (c : kˣ), 0 < n → n.Coprime p → x ^ n = 1 →
      y ^ n = 1 → Out.WeilIs P.A P.L n x y (unitOn c) → Out.WeilIs P'.A P'.L n (x ≫ α) (y ≫ α) (unitOn (c ^ d))) →
    LBIso (abelian₂ P.A (lbPow P.L d)) (abelian₂ P.A (P'.L.pull α.left))

theorem exists_hom (hT : ThetaUnifAV) (hA : HomAlg) (Q Q' : Out.PolAV (Sp ℂ)) (hg : Q'.g = Q.g)
    {e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ Q.A)} {e' : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ Q'.A)}
    (he : ∀ (g₀ : ℕ) (u : HolUnif Q.A Q.L g₀), ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e (h z) = u.ex z)
    (he' : ∀ (g₀ : ℕ) (u : HolUnif Q'.A Q'.L g₀), ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e' (h z) = u.ex z)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hF : ∀ z, e z = 1 → e' (F z) = 1) :
    ∃ α : Q.A ⟶ Q'.A, IsMonHom α ∧ ∀ z, e' (F z) = e z ≫ α := by
  obtain ⟨r, hr⟩ := Q.rigid
  obtain ⟨r', hr'⟩ := Q'.rigid
  obtain ⟨u, -⟩ := hT Q r hr
  obtain ⟨u₁, -⟩ := hT Q' r' hr'
  have u' : HolUnif Q'.A Q'.L Q.g := hg ▸ u₁
  obtain ⟨h, hh⟩ := he _ u
  obtain ⟨h', hh'⟩ := he' _ u'
  obtain ⟨α, hα, hu⟩ := hA Q Q' Q.g u u' (h'.symm.toLinearMap ∘ₗ F ∘ₗ h.toLinearMap) rfl hg fun z hz =>
    (u'.ker _).1 (by
      rw [← hh']
      show e' (h' (h'.symm (F (h z)))) = 1
      rw [h'.apply_symm_apply]
      exact hF _ ((hh z).trans ((u.ker z).2 hz)))
  refine ⟨α, hα, fun z => ?_⟩
  have k := hu (h.symm z)
  rw [← hh', ← hh, h.apply_symm_apply] at k
  rw [← k]
  show _ = e' (h' (h'.symm (F (h (h.symm z)))))
  rw [h'.apply_symm_apply, h.apply_symm_apply]

abbrev objPol {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}
    (o : Obj D l b s) {n : ℕ} (h : IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension n o.t.G.hom ∧
      Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) : Out.PolAV S :=
  { A := o.t.G, isAb := h.1, g := n, smoothDim := h.2.1, L := o.t.PP.L, isLB := o.t.PP.isLB, rigid := h.2.2.1,
    sym := h.2.2.2, ample := o.ample, ktriv := o.ktriv }

theorem exists_sabMap (hT : ThetaUnifAV) (hG : Out.GlobalFnsSt) (hA : HomAlg) (hD : WeilDet) {D D₁ D₂ : Datum H}
    {l : Level H} {b : Base l ℂ} {s : Sp ℂ ⟶ Sp ℂ} (o₁ o₂ : Obj D l b s) {n : ℕ}
    (p₁ : IsAbelianScheme o₁.t.G ∧ SmoothOfRelativeDimension n o₁.t.G.hom ∧
      Out.Rigidified o₁.t.G o₁.t.PP.L ∧ Out.Sym o₁.t.G o₁.t.PP.L)
    (p₂ : IsAbelianScheme o₂.t.G ∧ SmoothOfRelativeDimension n o₂.t.G.hom ∧
      Out.Rigidified o₂.t.G o₂.t.PP.L ∧ Out.Sym o₂.t.G o₂.t.PP.L)
    {ty : Fin g → (E →+* ℂ)} {P₁ : D₁.La →+ (Fin g → ℂ)} {P₂ : D₂.La →+ (Fin g → ℂ)} (hP₁ : IsPeriod D₁ ty P₁)
    (hP₂ : IsPeriod D₂ ty P₂) {e₁ : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ o₁.t.G)}
    {e₂ : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ o₂.t.G)} (a₁ : ∀ z w, e₁ (z + w) = e₁ z * e₁ w)
    (s₁ : Function.Surjective e₁) (s₂ : Function.Surjective e₂)
    (r₁ : ReadsPeriods o₁.t unitOn D₁ ty P₁ e₁) (r₂ : ReadsPeriods o₂.t unitOn D₂ ty P₂ e₂)
    (u₁ : ∀ (g₀ : ℕ) (u : HolUnif o₁.t.G o₁.t.PP.L g₀),
      ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e₁ (h z) = u.ex z)
    (u₂ : ∀ (g₀ : ℕ) (u : HolUnif o₂.t.G o₂.t.PP.L g₀),
      ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e₂ (h z) = u.ex z)
    (gam : D₁.La ≃ₗ[𝓞 E] D₂.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (hEF : ∀ a b, D₂.EF (gam a) (gam b) = D₁.EF a b) (hh : ∀ a, P₂ (gam a) = h (P₁ a)) :
    ∃ m : SABMap o₁.t o₂.t (𝟙 _), ∀ z, (e₁ z).left ≫ m.φ = (e₂ (h z)).left := by
  obtain ⟨α, hα, hα'⟩ : ∃ α : o₁.t.G ⟶ o₂.t.G, IsMonHom α ∧ ∀ z, e₂ (h z) = e₁ z ≫ α :=
    exists_hom hT hA (objPol o₁ p₁) (objPol o₂ p₂) rfl u₁ u₂ h.toLinearMap fun z hz => by
      obtain ⟨a, rfl⟩ := (r₁.1 z).1 hz
      exact (r₂.1 _).2 ⟨gam a, hh a⟩
  obtain ⟨β, -, hβ'⟩ : ∃ β : o₂.t.G ⟶ o₁.t.G, IsMonHom β ∧ ∀ z, e₁ (h.symm z) = e₂ z ≫ β :=
    exists_hom hT hA (objPol o₂ p₂) (objPol o₁ p₁) rfl u₂ u₁ h.symm.toLinearMap fun z hz => by
      obtain ⟨a, rfl⟩ := (r₂.1 z).1 hz
      refine (r₁.1 _).2 ⟨gam.symm a, h.injective ?_⟩
      rw [← hh, gam.apply_symm_apply]
      exact (h.apply_symm_apply _).symm
  have := p₁.1.smooth
  have := p₂.1.smooth
  have := p₁.1.proper
  have := p₂.1.proper
  have : IsReduced o₁.t.G.left := isReduced_of_smooth_complex _ o₁.t.G.hom inferInstance
  have : IsReduced o₂.t.G.left := isReduced_of_smooth_complex _ o₂.t.G.hom inferInstance
  let ψ : o₁.t.G ≅ o₂.t.G :=
    { hom := α
      inv := β
      hom_inv_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by
        obtain ⟨z, rfl⟩ := s₁ x
        rw [← Category.assoc, ← hα', ← hβ', h.symm_apply_apply, Category.comp_id]
      inv_hom_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by
        obtain ⟨z, rfl⟩ := s₂ x
        rw [← Category.assoc, ← hβ', ← hα', h.apply_symm_apply, Category.comp_id] }
  have hcomm : ∀ (a : 𝓞 E) z, h (fun k => ty k (a : E) * z k) = fun k => ty k (a : E) * h z k := fun a z => by
    have k : (h.toLinearMap.restrictScalars ℝ) ∘ₗ LinearMap.mulLeft ℝ (fun k => ty k (a : E)) =
        LinearMap.mulLeft ℝ (fun k => ty k (a : E)) ∘ₗ (h.toLinearMap.restrictScalars ℝ) := by
      refine LinearMap.ext_on_range hP₁.2.2.2.1 fun x => ?_
      show h (fun k => ty k (a : E) * P₁ x k) = fun k => ty k (a : E) * h (P₁ x) k
      rw [← funext (hP₁.1 a x), ← hh, ← hh, map_smul]
      exact funext (hP₂.1 a _)
    exact DFunLike.congr_fun k z
  have hact : ∀ a, o₁.t.act.act a ≫ α = α ≫ o₂.t.act.act a := fun a =>
    ComplexPoints.over_hom_ext_of_complexPoints fun x => by
      obtain ⟨z, rfl⟩ := s₁ x
      rw [← Category.assoc, ← Category.assoc, ← r₁.2.1, ← hα', ← hα', ← r₂.2.1, hcomm]
  have hlam := hD ℂ (objPol o₁ p₁) (objPol o₂ p₂) α 2 1 hα Nat.prime_two inferInstance
    fun k x y c hk _ hx hy hw => by
      obtain ⟨a, rfl⟩ := exists_div_of_pow a₁ s₁ r₁.1 hk hx
      obtain ⟨a', rfl⟩ := exists_div_of_pow a₁ s₁ r₁.1 hk hy
      have w := r₁.2.2 k a a' (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
      obtain rfl := weilIs_unique_fieldPoint _ _ _ o₁.t.PP.isLB ℂ (𝟙 _) k _ _ _ _ hw w
      have w' := r₂.2.2 k (gam a) (gam a') (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
      rw [hh, hh, ← map_smul h, ← map_smul h, hα', hα', hEF] at w'
      rw [pow_one]
      exact w'
  have : IsMonHom ψ.hom := hα
  exact ⟨⟨CubeMap.ofHom α, isGrpPullback_of_iso ψ, rfl, fun a => congrArg (fun z => z.left) (hact a),
    HeckePoint.isPullCubical_of_iso hG p₁.1 α o₁.t.cub o₂.t.cub (HeckePoint.iso_of_lam o₁.t o₂.t α hact hlam)⟩,
    fun z => congrArg (fun q => q.left) (hα' z).symm⟩

theorem exists_objMap {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}}
    {s : S ⟶ Sp B} (o₁ o₂ : Obj D l b s) (m : SABMap o₁.t o₂.t (𝟙 S))
    (h₁ : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
      (o₁.eta a).left ≫ m.φ = (o₂.eta a).left)
    (h₂ : ∀ a, (o₁.etaA a).left ≫ m.φ = (o₂.etaA a).left) : Nonempty (ObjMap o₁ o₂ (𝟙 S)) := by
  refine ⟨⟨m, fun a => ?_, fun a => (h₂ a).trans (Category.id_comp _).symm⟩⟩
  have ha : a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) ⊔
      l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) := by
    rw [← Submodule.sup_smul, l.coprime, Submodule.top_smul]
    trivial
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 ha
  rw [o₁.eta_add, o₂.eta_add, o₁.eta_ker x hx, o₂.eta_ker x hx, _root_.one_mul, _root_.one_mul]
  exact (h₁ y hy).trans (Category.id_comp _).symm

def baseOfEmb {l : Level H} (σ : KA l →+* ℂ) : Base l ℂ where
  unit _ hn := IsUnit.mk0 _ (Nat.cast_ne_zero.2 hn.ne')
  ρ := σ (baseKA l).ρ
  ρ_sq := by rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  ζ := σ (baseKA l).ζ
  ζ_prim := (baseKA l).ζ_prim.map_of_injective σ.injective

end GlobalTheory.UnifPoint
