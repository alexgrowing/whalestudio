import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenConnectedComponentOfNoetherianSpace

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory.ProjModelDim

section Deriv

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {X : Scheme.{0}} {ex : E → (Sp ℂ ⟶ X)}

def IsHolFamily (ex : E → (Sp ℂ ⟶ X)) : Prop :=
  ∀ (U : X.Opens) (f : Γ(X, U)), IsOpen {w | ⊤ ≤ ex w ⁻¹ᵁ U} ∧
    DifferentiableOn ℂ (fun w => valAt' (ex w) U f) {w | ⊤ ≤ ex w ⁻¹ᵁ U}

theorem IsHolFamily.eventually (h : IsHolFamily ex) {U : X.Opens} {z : E} (hz : ⊤ ≤ ex z ⁻¹ᵁ U) :
    ∀ᶠ w in 𝓝 z, ⊤ ≤ ex w ⁻¹ᵁ U := by
  exact (h U 0).1.mem_nhds hz

theorem IsHolFamily.differentiableAt (h : IsHolFamily ex) {U : X.Opens} {z : E} (hz : ⊤ ≤ ex z ⁻¹ᵁ U)
    (f : Γ(X, U)) : DifferentiableAt ℂ (fun w => valAt' (ex w) U f) z := by
  exact ((h U f).2 z hz).differentiableAt ((h U f).1.mem_nhds hz)
private theorem valAt'_resG {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) {U' V' : Y.Opens} (hle : V' ≤ U')
    (hx : ⊤ ≤ x ⁻¹ᵁ V') (g : Γ(Y, U')) :
    valAt' x V' (Y.presheaf.map (homOfLE hle).op g) = valAt' x U' g := by
  have hx' : ⊤ ≤ x ⁻¹ᵁ U' := hx.trans (fun p hp => hle hp)
  unfold valAt'
  rw [dif_pos hx, dif_pos hx']
  unfold valAt
  have key : Y.presheaf.map (homOfLE hle).op ≫ x.appLE V' ⊤ hx = x.appLE U' ⊤ hx' := by
    exact Scheme.Hom.map_appLE x _ _
  rw [← key]
  rfl

private theorem valAt'_ne_zero_of_isUnit {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) {W : Y.Opens} (hx : ⊤ ≤ x ⁻¹ᵁ W)
    {g : Γ(Y, W)} (hg : IsUnit g) : valAt' x W g ≠ 0 := by
  unfold valAt'
  rw [dif_pos hx]
  unfold valAt
  exact ((hg.map (x.appLE W ⊤ hx).hom).map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom).ne_zero

private theorem valAt'_mul' {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) (U : Y.Opens) (f f' : Γ(Y, U)) :
    valAt' x U (f * f') = valAt' x U f * valAt' x U f' := by
  unfold valAt'
  split_ifs with hx
  · unfold valAt
    simp only [map_mul]
  · simp

theorem IsHolFamily.fderiv_eq_zero (h : IsHolFamily ex) {U V : X.Opens} (hU : IsAffineOpen U) {z ξ : E}
    (hz : ⊤ ≤ ex z ⁻¹ᵁ U) (hV : ⊤ ≤ ex z ⁻¹ᵁ V)
    (h0 : ∀ f : Γ(X, U), fderiv ℂ (fun w => valAt' (ex w) U f) z ξ = 0) (r : Γ(X, V)) :
    fderiv ℂ (fun w => valAt' (ex w) V r) z ξ = 0 := by
  have pt : Sp ℂ := by exact IsLocalRing.closedPoint ℂ
  have hxU : (ex z).base pt ∈ U := hz (show pt ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  have hxV : (ex z).base pt ∈ V := hV (show pt ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  obtain ⟨f, hfV, hfx⟩ := hU.exists_basicOpen_le (V := V) ⟨(ex z).base pt, hxV⟩ hxU
  letI := (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
  have hloc := hU.isLocalization_basicOpen f
  obtain ⟨⟨a, s⟩, hq⟩ := IsLocalization.surj (Submonoid.powers f) (X.presheaf.map (homOfLE hfV).op r)
  have hsu : IsUnit (algebraMap Γ(X, U) Γ(X, X.basicOpen f) (s : Γ(X, U))) := IsLocalization.map_units _ s
  have hzD : ⊤ ≤ ex z ⁻¹ᵁ X.basicOpen f := by
    intro q _
    have hq1 : q = pt := Subsingleton.elim _ _
    subst hq1
    exact hfx
  have hSz : valAt' (ex z) U (s : Γ(X, U)) ≠ 0 := by
    rw [← valAt'_resG (ex z) (X.basicOpen_le f) hzD]
    exact valAt'_ne_zero_of_isUnit (ex z) hzD hsu
  have hev : (fun w => valAt' (ex w) V r * valAt' (ex w) U (s : Γ(X, U))) =ᶠ[𝓝 z]
      fun w => valAt' (ex w) U a := by
    filter_upwards [h.eventually hzD] with w hw
    rw [← valAt'_resG (ex w) hfV hw, ← valAt'_resG (ex w) (X.basicOpen_le f) hw,
      ← valAt'_resG (ex w) (X.basicOpen_le f) hw a, ← valAt'_mul']
    exact congrArg _ hq
  have hd : fderiv ℂ (fun w => valAt' (ex w) V r * valAt' (ex w) U (s : Γ(X, U))) z ξ =
      fderiv ℂ (fun w => valAt' (ex w) U a) z ξ := by
    rw [hev.fderiv_eq]
  rw [fderiv_fun_mul (h.differentiableAt hV r) (h.differentiableAt hz _)] at hd
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, h0, mul_zero,
    zero_add] at hd
  exact (mul_eq_zero.mp hd).resolve_left hSz

def IsHolFamily.der (h : IsHolFamily ex) {U : X.Opens} {z : E} (hz : ⊤ ≤ ex z ⁻¹ᵁ U) (ξ : E) : Γ(X, U) →+ ℂ :=
  AddMonoidHom.mk' (fun f => fderiv ℂ (fun w => valAt' (ex w) U f) z ξ) fun f f' => by
    simp only [valAt'_add]
    rw [fderiv_fun_add (h.differentiableAt hz f) (h.differentiableAt hz f')]
    rfl

theorem IsHolFamily.der_apply (h : IsHolFamily ex) {U : X.Opens} {z : E} (hz : ⊤ ≤ ex z ⁻¹ᵁ U) (ξ : E)
    (f : Γ(X, U)) : h.der hz ξ f = fderiv ℂ (fun w => valAt' (ex w) U f) z ξ := rfl

theorem IsHolFamily.der_mul (h : IsHolFamily ex) {U : X.Opens} {z : E} (hz : ⊤ ≤ ex z ⁻¹ᵁ U) (ξ : E)
    (f f' : Γ(X, U)) :
    h.der hz ξ (f * f') = valAt' (ex z) U f * h.der hz ξ f' + valAt' (ex z) U f' * h.der hz ξ f := by
  simp only [IsHolFamily.der_apply]
  have e : (fun w => valAt' (ex w) U (f * f')) = fun w => valAt' (ex w) U f * valAt' (ex w) U f' := by
    funext w
    exact valAt'_mul' _ _ _ _
  rw [e]
  rw [fderiv_fun_mul (h.differentiableAt hz f) (h.differentiableAt hz f')]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
private theorem valAt'_constFn_of_section {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) (p : Y ⟶ Sp ℂ) (U : Y.Opens) (a : ℂ)
    (hx : ⊤ ≤ x ⁻¹ᵁ U) (hp : x ≫ p = 𝟙 _) : valAt' x U (constFn p U a) = a := by
  unfold valAt'
  rw [dif_pos hx]
  unfold valAt constFn
  have key : p.appLE ⊤ U (fun _ _ => trivial) ≫ x.appLE U ⊤ hx = (x ≫ p).appLE ⊤ ⊤ (by simp) := by
    exact Scheme.Hom.appLE_comp_appLE x p _ _ _ _ _
  have e := congrArg (fun φ => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom
    (φ.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a))) key
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  rw [e]
  have gen : ∀ (q : Sp ℂ ⟶ Sp ℂ) (hq : q = 𝟙 _) (e' : ⊤ ≤ q ⁻¹ᵁ ⊤),
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom ((q.appLE ⊤ ⊤ e').hom
        ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) = a := by
    rintro q rfl e'
    have hid : Scheme.Hom.appLE (𝟙 (Sp ℂ)) ⊤ ⊤ e' = 𝟙 _ := by
      simp [Scheme.Hom.appLE]
      exact (Sp ℂ).presheaf.map_id _
    rw [hid]
    simp
  exact gen _ hp _

theorem IsHolFamily.der_constFn (h : IsHolFamily ex) {U : X.Opens} {z : E} (hz : ⊤ ≤ ex z ⁻¹ᵁ U) (ξ : E)
    (p : X ⟶ Sp ℂ) (hp : ∀ w, ex w ≫ p = 𝟙 _) (a : ℂ) : h.der hz ξ (constFn p U a) = 0 := by
  rw [h.der_apply]
  have hev : (fun w => valAt' (ex w) U (constFn p U a)) =ᶠ[𝓝 z] fun _ => a := by
    filter_upwards [h.eventually hz] with w hw
    exact valAt'_constFn_of_section (ex w) p U a hw (hp w)
  rw [hev.fderiv_eq]
  simp

theorem fderiv_eq_mul_of_mem_span {κ : Type} (θ : κ → E → ℂ) (hθ : ∀ c, Differentiable ℂ (θ c)) (c : κ) {z ξ : E}
    (hc : θ c z ≠ 0) (h0 : ∀ c', fderiv ℂ (fun w => θ c' w / θ c w) z ξ = 0) (f : E → ℂ)
    (hf : f ∈ Submodule.span ℂ (Set.range θ)) :
    DifferentiableAt ℂ f z ∧ fderiv ℂ f z ξ = fderiv ℂ (θ c) z ξ / θ c z * f z := by
  have hθz : ∀ c', fderiv ℂ (θ c') z ξ = θ c' z * (fderiv ℂ (θ c) z ξ / θ c z) := by
    intro c'
    have hq : DifferentiableAt ℂ (fun w => θ c' w / θ c w) z := by
      simp only [div_eq_mul_inv]
      exact ((hθ c') z).fun_mul (((hθ c) z).inv hc)
    have hev : θ c' =ᶠ[𝓝 z] fun w => θ c' w / θ c w * θ c w := by
      filter_upwards [((hθ c).continuous.continuousAt).eventually_ne hc] with w hw
      exact (div_mul_cancel₀ _ hw).symm
    rw [hev.fderiv_eq]
    rw [fderiv_fun_mul hq ((hθ c) z)]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, h0 c']
    ring
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c', rfl⟩ := hx
    refine ⟨(hθ c') z, ?_⟩
    rw [hθz c']
    ring
  | zero =>
    refine ⟨differentiableAt_const _, ?_⟩
    rw [show (0 : E → ℂ) = fun _ => (0 : ℂ) from rfl, fderiv_const_apply]
    simp
  | add x y _ _ hx hy =>
    refine ⟨hx.1.add hy.1, ?_⟩
    rw [fderiv_add hx.1 hy.1]
    simp only [_root_.add_apply, hx.2, hy.2, Pi.add_apply]
    ring
  | smul a x _ hx =>
    refine ⟨hx.1.const_smul a, ?_⟩
    rw [fderiv_const_smul hx.1 a]
    simp only [_root_.smul_apply, hx.2, Pi.smul_apply, smul_eq_mul]
    ring
private theorem smooth_of_grpObj_reduced_finiteType (X : Over (Sp ℂ)) [GrpObj X] (hred : IsReduced X.left)
    (hft : LocallyOfFiniteType X.hom) : Smooth X.hom := by
  obtain ⟨N, _, ν, -, hci, hsm, hrange⟩ :=
    GlobalTheory.ReducedSubgroup.exists_smooth_closed_subgroup ℂ X hft ⊤ Set.univ isClosed_univ (fun x => by simp)
  have hsurj : Surjective ν.left := ⟨fun y => by
    have hy : y ∈ Set.range ν.left := by rw [hrange]; trivial
    exact hy⟩
  have hiso : IsIso ν.left := isIso_of_isClosedImmersion_of_surjective ν.left
  have e : X.hom = inv ν.left ≫ N.hom := by rw [← Over.w ν]; simp
  rw [e]
  infer_instance

end Deriv

theorem isAbelianScheme_and_dim : (∀ (K : Type) [Field K] (X : Scheme.{0}) (p : X ⟶ Sp K) (g
    : ℕ), SmoothOfRelativeDimension g p → ∀ U : X.Opens, IsAffineOpen U → (U
    : Set X).Nonempty → ringKrullDim Γ(X, U) = g) → (∀ (X : Over (Sp ℂ)) (g
    : ℕ), SmoothOfRelativeDimension g X.hom → ∀ e : (𝟙_ (Over (Sp ℂ)) ⟶ X), ∃ (W : Set (Fin g →
    ℂ)) (σ : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (U : X.left.Opens) (t : Fin g → Γ(X.left,
    U)), IsOpen W ∧ 0 ∈ W ∧ σ 0 = e ∧ IsAffineOpen U ∧ (∀ (U : (X).left.Opens) (f : Γ((X).left,
    U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (σ w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (σ
    w).left U f) {w | w ∈ W ∧ ⊤ ≤ (σ w).left ⁻¹ᵁ U}) ∧ (∀ w ∈ W, ⊤ ≤ (σ
    w).left ⁻¹ᵁ U ∧ ∀ i, valAt' (σ w).left U (t i) = w i) ∧ IsOpen[(TopologicalSpace.generateFrom {S
    : Set (𝟙_ (Over (Sp ℂ)) ⟶ X) | ∃ (U : X.left.Opens) (f : Γ(X.left, U)) (O
    : Set ℂ), IsOpen O ∧ S = {x | ⊤ ≤ (x).left ⁻¹ᵁ U ∧ valAt' x.left U f ∈ O}})] (σ ''
    W) ∧ (∀ D : Γ(X.left, U) →+ ℂ, (∀ a, D (constFn X.hom U a) = 0) → (∀ f f', D (f *
    f') = valAt' e.left U f * D f' + valAt' e.left U f' * D f) → (∀ i, D (t
    i) = 0) → D = 0)) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin
    g) → ∀ N : ℕ, 1 ≤ N → (∀ c : Fin g → Fin N, (Differentiable ℂ (fun z => theta (fun i => ((c i
    : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ (n n'
    : Fin g → ℤ) z, (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) (z
    + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 +
    ofIntVec n ⬝ᵥ z)) * (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) •
    τ)) z)) ∧ LinearIndependent ℂ (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i
    : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin
    g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → ∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n
    n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ
    ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → f ∈ Submodule.span ℂ (Set.range (fun (c
    : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N
    : ℂ) • τ)))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin
    g) → ∀ N : ℕ, 3 ≤ N → ∀ (z ξ : Fin g → ℂ) (gam : ℂ), (∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f
    ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ
    (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → fderiv ℂ f z ξ = gam * f z) → ξ = 0) → (∀ (g
    : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (X : Over (Sp
    ℂ)) (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (D : (Fin g → Fin
    N) → X.left.Opens), (IsIntegral X.left ∧ IsProper X.hom ∧ Function.Surjective ex ∧
    (∀ z z', ex z = ex z' ↔ z - z' ∈ periodLattice τ) ∧ (∀ (U : (X).left.Opens) (f : Γ((X).left,
    U)), IsOpen {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex
    w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (ex w).left U f) {w | w ∈ (Set.univ
    : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U}) ∧ (∀ c, IsAffineOpen (D c) ∧ ringKrullDim Γ(X.left,
    D c) ≤ g ∧ (∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ D c ↔ theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) •
    z) ((N : ℂ) • τ) ≠ 0) ∧ ∃ r : (Fin g → Fin N) → Γ(X.left, D c), (∀ c' z, theta (fun i => ((c i
    : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0 → valAt' (ex z).left (D c) (r
    c') = theta (fun i => ((c' i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) / theta (fun i => ((c
    i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ f : Γ(X.left, D c), ∃ F : MvPolynomial (Fin
    g → Fin N) ℂ, f = MvPolynomial.eval₂ (RingHom.comp (X.hom.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso
    (CommRingCat.of ℂ)).inv.hom) r F) ∧ (⨆ c, D c = ⊤)) → (∀ (d : ℕ) (p q : (Fin g →
    ℂ) → ℂ), (Differentiable ℂ p ∧ ∀ (n n' : Fin g → ℤ) z, p (z + τ *ᵥ ofIntVec n + ofIntVec
    n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ
    z)) * p z) → (Differentiable ℂ q ∧ ∀ (n n' : Fin g → ℤ) z, q (z + τ *ᵥ ofIntVec n + ofIntVec
    n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ
    z)) * q z) → ∃ (U : X.left.Opens) (φ : Γ(X.left, U)), ∀ z, (⊤ ≤ (ex z).left ⁻¹ᵁ U ↔ q z ≠
    0) ∧ (q z ≠ 0 → valAt' (ex z).left U φ = p z / q z)) → ∀ [GrpObj
    X], IsCommMonObj X → IsAbelianScheme X ∧ SmoothOfRelativeDimension g X.hom) := by
  intro H1 H2 H3 H4 H5 g τ hτ N hN X ex D hX _hmero _ hcomm
  obtain ⟨hint, hprop, hsurj, _hker, hhol, hD, hcov⟩ := hX
  have := hint
  have := hprop
  have hsm : Smooth X.hom := smooth_of_grpObj_reduced_finiteType X inferInstance inferInstance
  have hgc : GeometricallyConnected X.hom := geometricallyConnected_of_isAlgClosed X.hom
  have hAb : IsAbelianScheme X := ⟨hcomm, hsm, hprop, hgc⟩
  refine ⟨hAb, ?_⟩
  have pt : Sp ℂ := by exact IsLocalRing.closedPoint ℂ
  have hall : ∀ q : Sp ℂ, q = pt := fun q => Subsingleton.elim _ _
  have : PreconnectedSpace X.left := inferInstance
  obtain ⟨n, hn⟩ := exists_dim_of_preconnected X.hom ((ex 0).left.base pt)
  have htop : ∀ (x : Sp ℂ ⟶ X.left) (V : X.left.Opens), x.base pt ∈ V → ⊤ ≤ x ⁻¹ᵁ V := by
    intro x V hx q _
    rw [hall q]
    exact hx
  have hx0 : (ex 0).left.base pt ∈ ⨆ c, D c := by
    rw [hcov]
    trivial
  obtain ⟨c₀, hc₀⟩ := TopologicalSpace.Opens.mem_iSup.mp hx0
  have hz0 : ⊤ ≤ (ex 0).left ⁻¹ᵁ D c₀ := htop _ _ hc₀
  have hle : n ≤ g := by
    have hdim := H1 ℂ X.left X.hom n hn (D c₀) (hD c₀).1 ⟨_, hc₀⟩
    have hdle := (hD c₀).2.1
    rw [hdim] at hdle
    exact_mod_cast hdle
  have hge : g ≤ n := by
    by_contra hlt'
    have hlt : n < g := not_le.mp hlt'
    obtain ⟨W, σ, U, t, hW, hW0, hσ0, hU, hσhol, hσU, hopen, hder⟩ := H2 X n hn (ex 0)
    have hzU : ⊤ ≤ (ex 0).left ⁻¹ᵁ U := by
      rw [← hσ0]
      exact (hσU 0 hW0).1
    have hF : IsHolFamily (fun w => (ex w).left) := fun V f => by
      simpa using hhol V f
    let Φ : (Fin g → ℂ) →ₗ[ℂ] (Fin n → ℂ) := LinearMap.pi (fun i =>
      ((fderiv ℂ (fun w => valAt' (ex w).left U (t i)) 0 : (Fin g → ℂ) →L[ℂ] ℂ) : (Fin g → ℂ) →ₗ[ℂ] ℂ))
    have hker : LinearMap.ker Φ ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hlt)
    obtain ⟨ξ, hξ, hξ0⟩ := (Submodule.ne_bot_iff _).mp hker
    have hξt : ∀ i, fderiv ℂ (fun w => valAt' (ex w).left U (t i)) 0 ξ = 0 := fun i => by
      have h1 := congrFun (LinearMap.mem_ker.mp hξ) i
      simpa [Φ] using h1
    have hp : ∀ w, (ex w).left ≫ X.hom = 𝟙 _ := fun w => by
      simpa using Over.w (ex w)
    have hD0 := hder (hF.der hzU ξ) (fun a => hF.der_constFn hzU ξ X.hom hp a)
      (fun f f' => hF.der_mul hzU ξ f f') (fun i => by rw [hF.der_apply]; exact hξt i)
    have hUzero : ∀ f : Γ(X.left, U), fderiv ℂ (fun w => valAt' (ex w).left U f) 0 ξ = 0 := fun f =>
      (hF.der_apply hzU ξ f).symm.trans (by simp [hD0])
    have hVzero : ∀ r' : Γ(X.left, D c₀), fderiv ℂ (fun w => valAt' (ex w).left (D c₀) r') 0 ξ = 0 :=
      fun r' => hF.fderiv_eq_zero hU hzU hz0 hUzero r'
    set θ : (Fin g → Fin N) → (Fin g → ℂ) → ℂ :=
      fun c z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) with hθdef
    have hθd : ∀ c, Differentiable ℂ (θ c) := fun c => ((H3 g τ hτ N (by omega)).1 c).1
    have hθ0 : θ c₀ 0 ≠ 0 := ((hD c₀).2.2.1 0).mp hz0
    obtain ⟨r, hr, -⟩ := (hD c₀).2.2.2
    have hratio : ∀ c', fderiv ℂ (fun w => θ c' w / θ c₀ w) 0 ξ = 0 := by
      intro c'
      have hev : (fun w => valAt' (ex w).left (D c₀) (r c')) =ᶠ[𝓝 0] fun w => θ c' w / θ c₀ w := by
        filter_upwards [((hθd c₀).continuous.continuousAt).eventually_ne hθ0] with w hw
        exact hr c' w hw
      rw [← hev.fderiv_eq]
      exact hVzero (r c')
    have hall' : ∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z,
        f (z + τ *ᵥ ofIntVec n + ofIntVec n') =
          eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) →
        fderiv ℂ f 0 ξ = fderiv ℂ (θ c₀) 0 ξ / θ c₀ 0 * f 0 := by
      intro f hf
      exact (fderiv_eq_mul_of_mem_span θ hθd c₀ hθ0 hratio f (H4 g τ hτ N (by omega) f hf)).2
    exact hξ0 (H5 g τ hτ N hN 0 ξ _ hall')
  rw [← le_antisymm hle hge]
  exact hn

end GlobalTheory.ProjModelDim
