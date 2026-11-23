import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EntireAntilinearLatticePeriodsConstStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueUniformisingVectorVerticalTangentStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDifferentiableOnVerticalVectorFieldStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section

namespace GlobalTheory.KS.Endo

private theorem valAt'_comp_lemma {Y Z : Scheme.{0}} (x : Sp ℂ ⟶ Y) (φ : Y ⟶ Z) (U : Z.Opens) (a : Γ(Z, U)) :
    valAt' (x ≫ φ) U a = valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom a) := by
  unfold valAt'
  by_cases h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U
  · have h' : ⊤ ≤ x ⁻¹ᵁ φ ⁻¹ᵁ U := h
    rw [dif_pos h, dif_pos h']
    unfold valAt
    rw [Scheme.Hom.comp_appLE]
    rfl
  · have h' : ¬ ⊤ ≤ x ⁻¹ᵁ φ ⁻¹ᵁ U := h
    rw [dif_neg h, dif_neg h']

theorem ptDer_push {X Y : Scheme.{0}} (y : Sp ℂ ⟶ X) (f : X ⟶ Y) (δ : ∀ W : X.Opens, Γ(X, W) → ℂ) (h : PtDer y δ) :
    PtDer (y ≫ f) (fun W a => δ (f ⁻¹ᵁ W) ((f.app W).hom a)) where
  add W hW a b := by
    rw [map_add]
    exact h.add (f ⁻¹ᵁ W) hW _ _
  mul W hW a b := by
    rw [map_mul, valAt'_comp_lemma y f W a, valAt'_comp_lemma y f W b]
    exact h.mul (f ⁻¹ᵁ W) hW _ _
  res W W' hle hW a := by
    have hle' : f ⁻¹ᵁ W' ≤ f ⁻¹ᵁ W := fun x hx => hle hx
    have nat : (f.app W').hom (resG Y hle a) = resG X hle' ((f.app W).hom a) :=
      congrArg (fun φ : Γ(Y, W) ⟶ Γ(X, f ⁻¹ᵁ W') => φ.hom a) (f.naturality (homOfLE hle).op)
    rw [nat]
    exact h.res (f ⁻¹ᵁ W) (f ⁻¹ᵁ W') hle' hW _

theorem ptDer_sub {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (δ δ' : ∀ W : X.Opens, Γ(X, W) → ℂ) (h : PtDer y δ) (h' : PtDer y δ') :
    PtDer y (fun W a => δ W a - δ' W a) where
  add W hW a b := by
    rw [h.add W hW, h'.add W hW]
    ring
  mul W hW a b := by
    rw [h.mul W hW, h'.mul W hW]
    ring
  res W W' hle hW a := by
    rw [h.res W W' hle hW, h'.res W W' hle hW]

theorem app_top_constFn {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (f : X ⟶ X) (hf : f ≫ p = p) (r : R) :
    (f.app ⊤).hom (constFn p ⊤ r) = resG X (le_top : f ⁻¹ᵁ ⊤ ≤ ⊤) (constFn p ⊤ r) := by
  have aux : ∀ q : X ⟶ Sp R, q = p → ∀ e e', q.appLE ⊤ (f ⁻¹ᵁ ⊤) e = p.appLE ⊤ (f ⁻¹ᵁ ⊤) e' := by
    rintro q rfl e e'
    rfl
  have key : ∀ e, p.appLE ⊤ ⊤ e ≫ f.app ⊤ =
      p.appLE ⊤ ⊤ e ≫ X.presheaf.map (homOfLE (le_top : f ⁻¹ᵁ ⊤ ≤ ⊤)).op := by
    intro e
    rw [Scheme.Hom.appLE_map, Scheme.Hom.app_eq_appLE f, Scheme.Hom.appLE_comp_appLE]
    exact aux _ hf _ _
  unfold constFn
  exact congrArg (fun φ : Γ(Sp R, ⊤) ⟶ Γ(X, f ⁻¹ᵁ ⊤) => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
    (key _)

variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g) {X : Scheme.{0}}

theorem ex_add_lattice (z l : Fin g → ℂ) (hl : l ∈ u.Λ) : u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker l).2 hl, _root_.mul_one]

theorem fn_differentiableAt (m : A₀.left ⟶ X) (W : X.Opens) (a : Γ(X, W)) (z : Fin g → ℂ) (hz : z ∈ dom u m W) :
    DifferentiableAt ℂ (fn u m W a) z := by
  have hU := u.hol (m ⁻¹ᵁ W) ((m.app W).hom a)
  have hz' : z ∈ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (m ⁻¹ᵁ W)} := hz
  have heq : fn u m W a = fun z => valAt' (u.ex z).left (m ⁻¹ᵁ W) ((m.app W).hom a) := by
    funext w
    exact valAt'_comp_lemma (u.ex w).left m W a
  rw [heq]
  exact hU.2.differentiableAt (hU.1.mem_nhds hz')

theorem fderiv_fn_add_lattice (m : A₀.left ⟶ X) (W : X.Opens) (a : Γ(X, W)) (z l : Fin g → ℂ) (hl : l ∈ u.Λ) :
    fderiv ℂ (fn u m W a) (z + l) = fderiv ℂ (fn u m W a) z := by
  have hper : (fun w => fn u m W a (w + l)) = fn u m W a := by
    funext w
    unfold fn
    rw [ex_add_lattice u w l hl]
  rw [← fderiv_comp_add_right, hper]

theorem comm_of_endo : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D Θ s, KSRel u p m D Θ s → ∀ (f : X ⟶ X) (f₀ : P₀.A ⟶ P₀.A) (F : (Fin P₀.g → ℂ) →ₗ[ℂ] (Fin P₀.g → ℂ)), f ≫ p = p → f₀.left ≫ m = m ≫ f → (∀ z, u.ex (F z) = u.ex z ≫ f₀) → Comm Θ F := by
  intro P₀ u Hm χ hU R instR x₀ X p m hp hpb D Θ s hKS f f₀ F hfp hf₀ hF
  have hFdiff : Differentiable ℂ F := by
    have := (LinearMap.toContinuousLinearMap F).differentiable
    rwa [LinearMap.coe_toContinuousLinearMap'] at this

  have hpt : ∀ z, (u.ex z).left ≫ m ≫ f = (u.ex (F z)).left ≫ m := by
    intro z
    rw [hF z, Over.comp_left, Category.assoc, hf₀]

  have hex0 : u.ex 0 = 1 := (u.ker 0).2 (zero_mem _)
  have hone : (1 : 𝟙_ (Over (Sp ℂ)) ⟶ P₀.A) ≫ f₀ = 1 := by
    have h0 := hF 0
    rw [map_zero, hex0] at h0
    exact h0.symm
  have hFl : ∀ l ∈ u.Λ, F l ∈ u.Λ := by
    intro l hl
    rw [← u.ker, hF, (u.ker l).2 hl, hone]
  have hexF : ∀ z, ∀ l ∈ u.Λ, u.ex (F (z + l)) = u.ex (F z) := by
    intro z l hl
    rw [map_add]
    exact ex_add_lattice u _ _ (hFl l hl)
  have hdom : ∀ W z, z ∈ dom u m (f ⁻¹ᵁ W) ↔ F z ∈ dom u m W := by
    intro W z
    show ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ (f ⁻¹ᵁ W) ↔ ⊤ ≤ ((u.ex (F z)).left ≫ m) ⁻¹ᵁ W
    rw [← hpt z]
    rfl
  have hfn : ∀ W a z, fn u m (f ⁻¹ᵁ W) ((f.app W).hom a) z = fn u m W a (F z) := by
    intro W a z
    show valAt' ((u.ex z).left ≫ m) (f ⁻¹ᵁ W) ((f.app W).hom a) = valAt' ((u.ex (F z)).left ≫ m) W a
    rw [← hpt z, ← Category.assoc, valAt'_comp_lemma ((u.ex z).left ≫ m) f W a]
  have hfd : ∀ W a z, F z ∈ dom u m W → fderiv ℂ (fn u m (f ⁻¹ᵁ W) ((f.app W).hom a)) z =
      (fderiv ℂ (fn u m W a) (F z)).comp (LinearMap.toContinuousLinearMap F) := by
    intro W a z hz
    have e : fn u m (f ⁻¹ᵁ W) ((f.app W).hom a) = fn u m W a ∘ (LinearMap.toContinuousLinearMap F) := by
      funext w
      exact hfn W a w
    rw [e]
    exact ((fn_differentiableAt u m W a (F z) hz).hasFDerivAt.comp z
      (LinearMap.toContinuousLinearMap F).hasFDerivAt).fderiv

  let d : (Fin P₀.g → ℂ) → ∀ W : X.Opens, Γ(X, W) → ℂ :=
    fun z W a => s (F z) W a - s z (f ⁻¹ᵁ W) ((f.app W).hom a)
  have hd : ∀ z, PtDer ((u.ex (F z)).left ≫ m) (d z) ∧ ∀ r, d z ⊤ (constFn p ⊤ r) = 0 := by
    intro z
    refine ⟨?_, ?_⟩
    · have h1 := ptDer_push _ f (s z) (hKS.der z)
      rw [Category.assoc, hpt z] at h1
      exact ptDer_sub _ _ _ (hKS.der (F z)) h1
    · intro r
      have htop : ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ (f ⁻¹ᵁ ⊤) := fun x _ => trivial
      show s (F z) ⊤ (constFn p ⊤ r) - s z (f ⁻¹ᵁ ⊤) ((f.app ⊤).hom (constFn p ⊤ r)) = 0
      rw [app_top_constFn p f hfp r, (hKS.der z).res ⊤ (f ⁻¹ᵁ ⊤) le_top htop, hKS.base, hKS.base, sub_self]
  have hdhol : ∀ W a, DifferentiableOn ℂ (fun z => d z W a) {z ∈ Set.univ | F z ∈ dom u m W} := by
    intro W a
    have h1 : DifferentiableOn ℂ (fun z => s (F z) W a) {z ∈ Set.univ | F z ∈ dom u m W} :=
      (hKS.hol W a).comp hFdiff.differentiableOn (fun z hz => hz.2)
    have h2 : DifferentiableOn ℂ (fun z => s z (f ⁻¹ᵁ W) ((f.app W).hom a)) {z ∈ Set.univ | F z ∈ dom u m W} :=
      (hKS.hol (f ⁻¹ᵁ W) ((f.app W).hom a)).mono (fun z hz => (hdom W z).2 hz.2)
    exact h1.sub h2
  obtain ⟨w, hwd, hw⟩ := GlobalTheory.T.exists_differentiableOn_verticalVectorField P₀ u Hm χ hU R x₀ X p m hp hpb P₀.g Set.univ F d isOpen_univ hFdiff
    (fun z _ => hd z) hdhol

  have hper : ∀ z, ∀ l ∈ u.Λ,
      w (z + l) = w z + (Θ.mulVec (star (F l)) - F (Θ.mulVec (star l))) := by
    intro z l hl
    have hFl' := hFl l hl
    have hpt' : PtDer ((u.ex (F z)).left ≫ m) (d (z + l)) ∧ ∀ r, d (z + l) ⊤ (constFn p ⊤ r) = 0 := by
      rw [← hexF z l hl]
      exact hd (z + l)
    obtain ⟨w0, -, huniq⟩ := GlobalTheory.T.existsUnique_uniformising_vector_vertical_tangent P₀ u Hm χ hU R x₀ X p m hp hpb (F z) (d (z + l)) hpt'.1 hpt'.2
    refine (huniq _ ?_).trans (huniq _ ?_).symm
    · intro W a hz
      have hz' : F (z + l) ∈ dom u m W := by
        show ⊤ ≤ ((u.ex (F (z + l))).left ≫ m) ⁻¹ᵁ W
        rw [hexF z l hl]
        exact hz
      rw [hw (z + l) (Set.mem_univ _) W a hz', map_add, fderiv_fn_add_lattice u m W a (F z) (F l) hFl']
    · intro W a hz
      have hzf : z ∈ dom u m (f ⁻¹ᵁ W) := (hdom W z).2 hz
      have e1 := hKS.per ⟨F l, hFl'⟩ W a (F z) hz
      have e2 := hKS.per ⟨l, hl⟩ (f ⁻¹ᵁ W) ((f.app W).hom a) z hzf
      have hd0 := hw z (Set.mem_univ _) W a hz
      show s (F (z + l)) W a - s (z + l) (f ⁻¹ᵁ W) ((f.app W).hom a) = _
      rw [map_add, e1, e2, hfd W a z hz]
      show _ = fderiv ℂ (fn u m W a) (F z) (w z + (Θ.mulVec (star (F l)) - F (Θ.mulVec (star l))))
      rw [ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap', map_add, map_sub, ← hd0]
      ring

  have hc_add : ∀ v v' : Fin P₀.g → ℂ,
      Θ.mulVec (star (F (v + v'))) - F (Θ.mulVec (star (v + v'))) =
        (Θ.mulVec (star (F v)) - F (Θ.mulVec (star v))) + (Θ.mulVec (star (F v')) - F (Θ.mulVec (star v'))) := by
    intro v v'
    rw [map_add, star_add, star_add, Matrix.mulVec_add, Matrix.mulVec_add, map_add]
    abel
  have hc_smul : ∀ (a : ℂ) (v : Fin P₀.g → ℂ),
      Θ.mulVec (star (F (a • v))) - F (Θ.mulVec (star (a • v))) =
        star a • (Θ.mulVec (star (F v)) - F (Θ.mulVec (star v))) := by
    intro a v
    rw [map_smul, star_smul, star_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, map_smul, smul_sub]
  let cA : (Fin P₀.g → ℂ) →+ (Fin P₀.g → ℂ) :=
    AddMonoidHom.mk' (fun v => Θ.mulVec (star (F v)) - F (Θ.mulVec (star v))) hc_add
  have hexp : ∀ v : Fin P₀.g → ℂ, Θ.mulVec (star (F v)) - F (Θ.mulVec (star v)) =
      ∑ j, star (v j) • cA (fun k => if j = k then 1 else 0) := by
    intro v
    have h1 : cA v = ∑ j, cA (v j • fun k => if j = k then 1 else 0) := by
      conv_lhs => rw [pi_eq_sum_univ v]
      exact map_sum cA _ _
    refine h1.trans (Finset.sum_congr rfl fun j _ => ?_)
    exact hc_smul (v j) _

  have hwdiff : Differentiable ℂ w := differentiableOn_univ.1 hwd
  have hzero : ∀ i j, cA (fun k => if j = k then 1 else 0) i = 0 := by
    intro i j
    have hperi : ∀ (l : u.Λ) (z : Fin P₀.g → ℂ), w (z + l) i =
        w z i + (fun j => cA (fun k => if j = k then 1 else 0) i) ⬝ᵥ star (l : Fin P₀.g → ℂ) := by
      intro l z
      rw [hper z l l.2, Pi.add_apply, hexp (l : Fin P₀.g → ℂ)]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, dotProduct, Pi.star_apply]
      congr 1
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hI := GlobalTheory.T.entire_antilinear_lattice_periods_const P₀.g u.Λ u.discrete u.full (fun z => w z i) _ (differentiable_pi.1 hwdiff i) hperi
    exact congrFun hI.1 j
  intro z
  have hz := hexp z
  have hz0 : Θ.mulVec (star (F z)) - F (Θ.mulVec (star z)) = 0 := by
    rw [hz]
    funext i
    simp [hzero]
  exact (sub_eq_zero.1 hz0).symm

end GlobalTheory.KS.Endo
