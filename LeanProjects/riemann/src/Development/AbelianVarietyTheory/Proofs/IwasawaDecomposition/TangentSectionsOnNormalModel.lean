import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineTangentBasisLocallyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomogeneousPolysTangentBasisStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LineNorm.Chart

open ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet

section Alg

theorem exists_minor_ne_zero {K : Type} [Field K] {m g k : ℕ} (a : Fin m → Fin g → K) (ha : LinearIndependent K a)
    (hk : k ≤ m) : ∃ s, minor a hk s ≠ 0 := by
  classical
  let M : Matrix (Fin k) (Fin g) K := Matrix.of fun l i => a (Fin.castLE hk l) i
  have hM : LinearIndependent K M.row := ha.comp _ (Fin.castLE_injective hk)
  obtain ⟨κ, b, hb, hsp, hli⟩ := exists_linearIndependent' K M.col
  have : Finite κ := Finite.of_injective b hb
  let : Fintype κ := Fintype.ofFinite κ
  have hκ : Fintype.card κ = k := by
    rw [← finrank_span_eq_card hli, hsp, ← Matrix.rank_eq_finrank_span_cols, hM.rank_matrix, Fintype.card_fin]
  let e : Fin k ≃ κ := (Fintype.equivFinOfCardEq hκ).symm
  have h1 : LinearIndependent K (M.submatrix id (b ∘ e)).col := hli.comp e e.injective
  exact ⟨b ∘ e, ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 h1)).ne_zero⟩

theorem map_minor {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {m g k : ℕ} (a : Fin m → Fin g → R)
    (hk : k ≤ m) (s : Fin k → Fin g) : φ (minor a hk s) = minor (fun l i => φ (a l i)) hk s := by
  rw [minor, RingHom.map_det]; rfl

theorem minor_tri {R : Type} [CommRing R] {m g k : ℕ} (a b : Fin m → Fin g → R) (T : Fin m → Fin m → R)
    (hT : ∀ i l, i < l → T i l = 0) (h : ∀ i, b i = ∑ l, T i l • a l) (hk : k ≤ m) (s : Fin k → Fin g) :
    minor b hk s = (∏ l : Fin k, T (Fin.castLE hk l) (Fin.castLE hk l)) * minor a hk s := by
  let T' : Matrix (Fin k) (Fin k) R := Matrix.of fun i l => T (Fin.castLE hk i) (Fin.castLE hk l)
  have h1 : T'.det = ∏ l : Fin k, T (Fin.castLE hk l) (Fin.castLE hk l) :=
    Matrix.det_of_isLowerTriangular T' fun i l hl => hT _ _ hl
  rw [← h1, minor, minor, ← Matrix.det_mul]
  congr 1
  ext i j
  simp only [Matrix.of_apply, Matrix.mul_apply, h, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, T']
  symm
  refine Finset.sum_of_injOn (Fin.castLE hk) (Fin.castLE_injective hk).injOn (by simp) (fun l _ hl => ?_)
    (fun _ _ => rfl)
  rw [hT, zero_mul]
  by_contra hc
  exact hl ⟨⟨l, by have := i.2; simp only [Fin.lt_def, Fin.val_castLE] at hc; omega⟩, by simp, rfl⟩

theorem eval₂_homog {A R σ : Type} [CommRing A] [CommRing R] (φ : A →+* R) {P : MvPolynomial σ A} {d : ℕ}
    (hP : P.IsHomogeneous d) (c : R) (x : σ → R) :
    MvPolynomial.eval₂ φ (fun s => c * x s) P = c ^ d * MvPolynomial.eval₂ φ x P := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have h1 : ∑ i ∈ n.support, n i = d := by
    have := hP (MvPolynomial.mem_support_iff.1 hn)
    exact (congrArg (fun q => q n) Finsupp.degree_eq_weight_one).trans this
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, h1]
  ring

theorem log_iSup {K C : Type} [Field K] [NormedField C] (w : AbsoluteValue K ℝ) (io : K →+* C) (c : ℝ)
    (h1 : ∀ a, ‖io a‖ ≤ 1 → w a ≤ 1) (h2 : ∀ a, Real.log (w a) = c * Real.log ‖io a‖) {n : ℕ} (b : Fin n → K) :
    Real.log (⨆ i, w (b i)) = c * Real.log (⨆ i, ‖io (b i)‖) := by
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · simp
  obtain ⟨i, hi⟩ := Finite.exists_max fun i => ‖io (b i)‖
  have e1 : ⨆ j, ‖io (b j)‖ = ‖io (b i)‖ :=
    le_antisymm (ciSup_le hi) (le_ciSup (f := fun j => ‖io (b j)‖) (Finite.bddAbove_range _) i)
  have e2 : ⨆ j, w (b j) = w (b i) := by
    refine le_antisymm (ciSup_le fun j => ?_) (le_ciSup (f := fun j => w (b j)) (Finite.bddAbove_range _) i)
    rcases eq_or_ne (b i) 0 with h0 | h0
    · have := hi j
      rw [h0, map_zero, norm_zero, norm_le_zero_iff, map_eq_zero] at this
      rw [this, h0]
    · have := h1 (b j / b i) (by
        rw [map_div₀, norm_div]
        exact div_le_one_of_le₀ (hi j) (norm_nonneg _))
      rwa [map_div₀, div_le_one (w.pos h0)] at this
  rw [e1, e2, h2]

end Alg

section Tan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X}

theorem dual_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S) (ψ : S →+* T) {Z : Scheme.{0}}
    (v : Sp (DualNumber R) ⟶ Z) :
    spMap (dualMap ψ) ≫ spMap (dualMap φ) ≫ v = spMap (dualMap (ψ.comp φ)) ≫ v := by
  rw [← Category.assoc, spMap_comp']
  congr 2
  refine RingHom.ext fun z => ?_
  ext <;> simp [dualMap]

variable {R : Type} [CommRing R] {x : Sp R ⟶ X} {m g : ℕ}

theorem comb_iff {u : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} (hu : ∀ l, IsTanAtG t x (u l)) (a : Fin m → R)
    (w : Sp (DualNumber R) ⟶ t.G.left) :
    IsCombAtG t x u a w ↔ w = (tv (∑ l, a l • tanOf (hu l))).left := by
  have h0 : IsCombAtG t x u a (tv (∑ l, a l • tanOf (hu l))).left := (isComb_iff (fun l => tanOf (hu l)) a _).2 rfl
  refine ⟨fun h => ?_, fun h => h ▸ h0⟩
  exact ((isCombAtG_iff t x (fun j => ovT (hu j)) a _).1 h).symm.trans
    ((isCombAtG_iff t x (fun j => ovT (hu j)) a _).1 h0)

theorem comb_tan {u : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} (hu : ∀ l, IsTanAtG t x (u l)) {a : Fin m → R}
    {w : Sp (DualNumber R) ⟶ t.G.left} (h : IsCombAtG t x u a w) : IsTanAtG t x w :=
  (comb_iff hu a w).1 h ▸ isTan_tv _

theorem sum_comb {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (he : ∀ i, IsTanAtG t x (e i))
    {u : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} (hu : ∀ l, IsTanAtG t x (u l)) {a : Fin m → Fin g → R}
    (ha : ∀ l, IsCombAtG t x e (a l) (u l)) (c : Fin m → R) :
    ∑ l, c l • tanOf (hu l) = ∑ i, (∑ l, c l • a l) i • tanOf (he i) := by
  have h : ∀ l, tanOf (hu l) = ∑ i, a l i • tanOf (he i) := fun l => tan_ext ((comb_iff he _ _).1 (ha l))
  simp only [h, Finset.smul_sum, Finset.sum_apply, Finset.sum_smul, Pi.smul_apply, smul_smul, smul_eq_mul]
  exact Finset.sum_comm

theorem comb_comb {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (he : ∀ i, IsTanAtG t x (e i))
    {u : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} {a : Fin m → Fin g → R}
    (ha : ∀ l, IsCombAtG t x e (a l) (u l)) {c : Fin m → R} {w : Sp (DualNumber R) ⟶ t.G.left}
    (hw : IsCombAtG t x u c w) : IsCombAtG t x e (∑ l, c l • a l) w := by
  have hu := fun l => comb_tan he (ha l)
  rw [comb_iff he, ← sum_comb he hu ha]
  exact (comb_iff hu _ _).1 hw

theorem linInd {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (he : ∀ i, IsTanAtG t x (e i))
    {u : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} {a : Fin m → Fin g → R}
    (ha : ∀ l, IsCombAtG t x e (a l) (u l)) (hi : IsIndep t x u) : LinearIndependent R a := by
  have hu := fun l => comb_tan he (ha l)
  refine Fintype.linearIndependent_iff.2 fun c hc => congrFun (hi c 0 _ ((comb_iff hu _ _).2 rfl) ?_)
  rw [comb_iff hu, sum_comb he hu ha, hc]
  simp

end Tan

section Geo

theorem ringHom_ext {S : Scheme.{0}} {V : S.Opens} (hV : IsAffineOpen V) {R : Type} [CommRing R]
    {φ φ' : Γ(S, V) →+* R} (h : spMap φ ≫ hV.fromSpec = spMap φ' ≫ hV.fromSpec) : φ = φ' :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 h))

theorem exists_ringHom {S : Scheme.{0}} {V : S.Opens} (hV : IsAffineOpen V) {R : Type} [CommRing R]
    (x : Sp R ⟶ S) (h : ⊤ ≤ x ⁻¹ᵁ V) : ∃ φ : Γ(S, V) →+* R, spMap φ ≫ hV.fromSpec = x :=
  ⟨(GlobalTheory.Points.valMap x V h).hom, GlobalTheory.Points.specMap_valMap_fromSpec hV x h⟩

theorem exists_stalkHom {S Y : Scheme.{0}} {V : S.Opens} (hV : IsAffineOpen V) (j : Y ⟶ S) (y : Y) (h : j y ∈ V) :
    ∃ φ : Γ(S, V) →+* Y.presheaf.stalk y, spMap φ ≫ hV.fromSpec = Y.fromSpecStalk y ≫ j := by
  refine ⟨(S.presheaf.germ V _ h ≫ j.stalkMap y).hom, ?_⟩
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, ← hV.fromSpecStalk_eq_fromSpecStalk h, IsAffineOpen.fromSpecStalk,
    ← Category.assoc, ← Spec.map_comp]
  rfl

theorem isIntegrallyClosed_sections {S : Scheme.{0}} (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) {V : S.Opens} (hV : IsAffineOpen V)
    [IsDomain Γ(S, V)] : IsIntegrallyClosed Γ(S, V) := by
  refine IsIntegrallyClosed.of_localization_maximal fun p _ hp => ?_
  let y : PrimeSpectrum Γ(S, V) := ⟨p, hp.isPrime⟩
  have hy : hV.fromSpec y ∈ V := by
    rw [← SetLike.mem_coe, ← hV.range_fromSpec]; exact ⟨y, rfl⟩
  let _ := (S.presheaf.germ V _ hy).hom.toAlgebra
  have h1 : IsLocalization.AtPrime (S.presheaf.stalk (hV.fromSpec y)) p := hV.isLocalization_stalk' y hy
  have := (hS (hV.fromSpec y)).2
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv p.primeCompl (S.presheaf.stalk (hV.fromSpec y)) (Localization.AtPrime p)).toRingEquiv

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem isUnit_natCast (y : Y.X) {c : ℕ} (hc : c ≠ 0) : IsUnit (c : Y.X.presheaf.stalk y) := by
  have := (IsUnit.mk0 (c : F) (by exact_mod_cast hc)).map (Spec.preimage (Y.X.fromSpecStalk y ≫ Y.str)).hom
  rwa [map_natCast] at this

omit [NumberField F] in
theorem gen_eq (y : Y.X) :
    spMap (algebraMap (Y.X.presheaf.stalk y) Y.X.functionField) ≫ stalkPt Y y = genericPt Y :=
  Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes y)

end Geo

section Coord

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {A : Type} [CommRing A] {x₀ : Sp A ⟶ X} {g m : ℕ} {e : Fin g → (Sp (DualNumber A) ⟶ t.G.left)}

theorem coord_map {R S : Type} [CommRing R] [CommRing S] (α : A →+* R) (ψ : R →+* S) {a : Fin g → R}
    {w : Sp (DualNumber R) ⟶ t.G.left}
    (h : IsCombAtG t (spMap α ≫ x₀) (fun i => spMap (dualMap α) ≫ e i) a w) :
    IsCombAtG t (spMap (ψ.comp α) ≫ x₀) (fun i => spMap (dualMap (ψ.comp α)) ≫ e i) (fun i => ψ (a i))
      (spMap (dualMap ψ) ≫ w) := by
  have := GlobalTheory.LatDRFree.comb_map t ψ h
  simp only [dual_comp] at this
  rwa [← Category.assoc, spMap_comp'] at this

theorem coord_linInd (he : IsTanBasis t x₀ e) {R S : Type} [CommRing R] [CommRing S] (α : A →+* R) (ψ : R →+* S)
    {a : Fin m → Fin g → R} {u : Fin m → (Sp (DualNumber R) ⟶ t.G.left)}
    (h : ∀ l, IsCombAtG t (spMap α ≫ x₀) (fun i => spMap (dualMap α) ≫ e i) (a l) (u l))
    (hi : IsIndep t (spMap ψ ≫ spMap α ≫ x₀) fun l => spMap (dualMap ψ) ≫ u l) :
    LinearIndependent S fun l i => ψ (a l i) := by
  rw [← Category.assoc, spMap_comp'] at hi
  exact linInd (fun i => isTan_map _ rfl (he.1 i)) (fun l => coord_map α ψ (h l)) hi

theorem stepLog_eq {F : Type} [Field F] [NumberField F] {Y : Var F} (ρ : Y.X ⟶ X)
    (f : ∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)) (q : ℕ) (i : Fin m)
    (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v) (y : AlgPt Y) (hp' : (resP v).Prime) [hp : Fact (resP v).Prime]
    (ψ : Y.X.presheaf.stalk (below y.1) →+* ℂ_[resP v])
    (hψ : ψ = (ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom) :
    stepLog t ρ f q i v ε y = (-Real.log (ε.w (resP v)) / Real.log (resP v)) *
      Real.log (GlobalTheory.ShFam.Pad.grNorm t (spMap ψ ≫ stalkPt Y (below y.1) ≫ ρ)
        (lat t (resP v) (spMap ψ ≫ stalkPt Y (below y.1) ≫ ρ) (decide (resP v = q)))
        (fun l => spMap (dualMap ψ) ≫ f (below y.1) l) i) := by
  obtain rfl : hp = stepLog._proof_2 v hp' := rfl
  subst hψ
  exact dif_pos hp'

end Coord

end GlobalTheory.LineNorm.Chart

open GlobalTheory.LineNorm.Chart GlobalTheory.LieMet in

theorem _root_.GlobalTheory.LineNorm.Chart.locMax_flag : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X), X.IsSeparated → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : GlobalTheory.TrueGeo.Model Y) (ρ' : M.X ⟶ X) (ρ : Y.X ⟶ X), IsNormalScheme M.X → M.j ≫ ρ' = ρ → ∀ (m : ℕ) (u₀ : Fin m → (Sp (DualNumber Y.Fn) ⟶ t.G.left)) (f : ∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)) (d : Y.X → Fin m → Y.Fnˣ), IsFlagFrame t ρ u₀ f d → ∀ (q k : ℕ) (hk : k ≤ m) (z : M.X), LocMax M (fun y => ∏ l : Fin k, d y (Fin.castLE hk l)) (fun v e y => ∑ l : Fin k, stepLog t ρ f q (Fin.castLE hk l) v e y) z := by
  intro hB E _ _ _ H X _ t hX F _ _ Y M ρ' ρ hM hρ m u₀ f d hf q k hk z
  subst hρ
  obtain ⟨⟨V, hV⟩, g, e, hz, he⟩ := GlobalTheory.T.exists_affine_tangent_basis_locally E H X t M.X ρ' z
  replace hV : IsAffineOpen V := hV
  dsimp only at e hz he
  have := M.ar.isIntegral
  have := M.ar.isLocallyNoetherian
  have : Nonempty V := ⟨⟨z, hz⟩⟩
  have hgen : M.j (genericPoint Y.X) ∈ V :=
    (SmallSec.j_gen_specializes M).mem_open V.isOpen (gen_mem hz)
  choose α hα using fun (y : Y.X) (hy : M.j y ∈ V) => exists_stalkHom hV M.j y hy
  have hα' : ∀ y hy, spMap (α y hy) ≫ hV.fromSpec ≫ ρ' = stalkPt Y y ≫ M.j ≫ ρ' := fun y hy => by
    rw [← Category.assoc, hα, Category.assoc]; rfl
  let ι₀ : Γ(M.X, V) →+* Y.Fn := α _ hgen
  have hι : spMap ι₀ ≫ hV.fromSpec ≫ ρ' = genericPt Y ≫ M.j ≫ ρ' := hα' _ hgen
  have hαι : ∀ y hy, (algebraMap (Y.X.presheaf.stalk y) Y.X.functionField).comp (α y hy) = ι₀ := fun y hy =>
    ringHom_ext hV (by
      rw [← spMap_comp', Category.assoc, hα, ← Category.assoc]
      exact (congrArg (· ≫ M.j) (gen_eq y)).trans (hα _ hgen).symm)
  have : IsIntegrallyClosed Γ(M.X, V) := isIntegrallyClosed_sections hM hV
  have : IsNoetherianRing Γ(M.X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : CharZero Y.Fn := charZero_of_inj_zero fun n hn => by
    by_contra hc
    exact (isUnit_natCast (genericPoint Y.X) hc).ne_zero hn
  have : CharZero Γ(M.X, V) := ι₀.charZero
  obtain ⟨D, n, B, hB1, hB2, hB3⟩ := GlobalTheory.T.exists_homogeneous_polys_tangent_basis hB E H X t hX Γ(M.X, V) _ g e he q k

  have ha : ∀ y (hy : M.j y ∈ V) l, ∃ a, IsCombAtG t (spMap (α y hy) ≫ hV.fromSpec ≫ ρ')
      (fun i => spMap (dualMap (α y hy)) ≫ e i) a (f y l) := fun y hy l =>
    (he.2 _ (α y hy) (f y l) (by rw [hα']; exact hf.tan y l)).exists
  choose a ha using ha
  have key : ∀ y (hy : M.j y ∈ V) i, ∃ cf : Fin m → Y.Fn, cf i = d y i ∧ (∀ k, i < k → cf k = 0) ∧
      IsCombAtG t (spMap ι₀ ≫ hV.fromSpec ≫ ρ') (fun i => spMap (dualMap ι₀) ≫ e i)
        (∑ l, cf l • fun j => algebraMap (Y.X.presheaf.stalk y) Y.X.functionField (a y hy l j)) (u₀ i) := by
    intro y hy i
    obtain ⟨cf, h1, h2, h3⟩ := hf.tri y i
    refine ⟨cf, h1, h2, comb_comb (fun j => isTan_map _ rfl (he.1 j)) (fun l => ?_) (hι ▸ h3)⟩
    have := coord_map _ (algebraMap (Y.X.presheaf.stalk y) Y.X.functionField) (ha y hy l)
    rwa [hαι] at this
  choose T hT1 hT2 hT3 using key
  have hA₀ : ∀ i, ∃ b, IsCombAtG t (spMap ι₀ ≫ hV.fromSpec ≫ ρ') (fun i => spMap (dualMap ι₀) ≫ e i) b (u₀ i) :=
    fun i => ⟨_, hT3 _ hgen i⟩
  choose A₀ hA₀ using hA₀
  have hA : ∀ y hy i, A₀ i = ∑ l, T y hy i l • fun j => algebraMap _ Y.X.functionField (a y hy l j) := fun y hy i =>
    (he.2 _ ι₀ (u₀ i) (comb_tan (fun j => isTan_map _ rfl (he.1 j)) (hT3 y hy i))).unique (hA₀ i) (hT3 y hy i)
  have hs : ∀ y hy i, MvPolynomial.eval₂ ι₀ (minor A₀ hk) (B i) *
      ((((∏ l : Fin k, d y (Fin.castLE hk l))⁻¹ ^ (D : ℕ) : Y.Fnˣ)) : Y.Fn) =
      algebraMap _ Y.X.functionField (MvPolynomial.eval₂ (α y hy) (minor (a y hy) hk) (B i)) := by
    intro y hy i
    have e1 : minor A₀ hk = fun s => ((∏ l : Fin k, d y (Fin.castLE hk l) : Y.Fnˣ) : Y.Fn) *
        algebraMap _ Y.X.functionField (minor (a y hy) hk s) := funext fun s => by
      rw [minor_tri _ A₀ (T y hy) (hT2 y hy) (hA y hy), map_minor, Units.coe_prod]
      simp only [hT1]
    rw [e1, eval₂_homog _ (hB1 i), MvPolynomial.eval₂_comp_left, hαι, mul_comm, ← _root_.mul_assoc,
      ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, inv_mul_cancel, one_pow, Units.val_one, _root_.one_mul]
    rfl
  have hli : ∀ y hy (K : Type) [Field K] (ψ : Y.X.presheaf.stalk y →+* K),
      LinearIndependent K fun l i => ψ (a y hy l i) := fun y hy K _ ψ =>
    coord_linInd he _ ψ (ha y hy) (by rw [hα']; exact hf.indep y K ψ)
  refine ⟨V, D, n, fun i => MvPolynomial.eval₂ ι₀ (minor A₀ hk) (B i), hz, fun y hy => ⟨fun i => ⟨_, (hs y hy i).symm⟩, ?_⟩,
    fun v ε y yt hyt hin => ?_⟩
  · obtain ⟨s, hs0⟩ := exists_minor_ne_zero _ (hli y hy _ (IsLocalRing.residue _)) hk
    rw [← map_minor, IsLocalRing.residue_ne_zero_iff_isUnit] at hs0
    obtain ⟨i, c, hc, hi⟩ := hB2 s
    refine ⟨i, _, ?_, (hs y hy i).symm⟩
    rw [hi, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X, map_natCast]
    exact (isUnit_natCast y hc).mul (hs0.pow _)
  · obtain ⟨hp, h1, h2⟩ := ioOf_spec F v ε
    have := Fact.mk hp
    obtain ⟨β, hβ⟩ := exists_ringHom hV yt hin
    have hy : M.j (below y.1) ∈ V := by
      have : (spMap ε.O.subtype ≫ yt) (IsLocalRing.closedPoint _) ∈ V := hin (Set.mem_univ _)
      rwa [hyt] at this
    obtain ⟨σ, hσ₀⟩ : ∃ σ : Y.X.presheaf.stalk (below y.1) →+* AlgebraicClosure F,
      σ = (Scheme.stalkClosedPointTo y.1).hom := ⟨_, rfl⟩
    have hσ : σ.comp (α _ hy) = ε.O.subtype.comp β := ringHom_ext hV (by
      rw [← spMap_comp', ← spMap_comp', Category.assoc, Category.assoc, hα, hβ, hyt, ← Category.assoc, hσ₀]
      exact congrArg (· ≫ M.j) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk y.1))
    obtain ⟨ψ, hψ⟩ : ∃ ψ, ψ = (ioOf (resP v) ε).comp σ := ⟨_, rfl⟩
    have h3 := hB3 (resP v) (ψ.comp (α _ hy)) (fun b => by
        have : σ (α _ hy b) = β b := congrArg (fun q => q b) hσ
        rw [hψ, RingHom.comp_apply, RingHom.comp_apply, h1, this]; exact (β b).2) m hk _ _ (hli _ hy _ ψ)
        fun l => coord_map _ ψ (ha _ hy l)
    rw [← spMap_comp', Category.assoc, hα'] at h3
    have hv : ∀ b, valAt y.1 (algebraMap (Y.X.presheaf.stalk (below y.1)) Y.X.functionField b) = σ b := fun b => by
      rw [hσ₀]; exact Base.valAt_stalk _ _
    have h4 : ∀ i, MvPolynomial.eval₂ (ψ.comp (α _ hy)) (minor (fun l j => ψ (a _ hy l j)) hk) (B i) =
        ioOf (resP v) ε (σ (MvPolynomial.eval₂ (α _ hy) (minor (a _ hy) hk) (B i))) := fun i => by
      rw [← RingHom.comp_apply, ← hψ, MvPolynomial.eval₂_comp_left]
      congr 1
      funext s
      exact (map_minor ψ _ hk s).symm
    simp only [h4] at h3
    simp only [hs _ hy, hv]
    rw [log_iSup ε.w (ioOf (resP v) ε) _ (fun b hb => (ε.mem_O b).1 ((h1 b).1 hb)) h2, ← h3,
      Finset.sum_congr rfl fun l _ => stepLog_eq _ f q _ v ε y hp ψ (by rw [hψ, hσ₀]), ← Finset.mul_sum, mul_left_comm]
