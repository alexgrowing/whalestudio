import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.TriFrDefs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomogeneousPolysTangentBasis
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.Mean4O
attribute [local instance] Over.cartesianMonoidalCategory

section SlopeTestRemainingChoices
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm.Chart GlobalTheory.LineNorm.WedgeMax GlobalTheory.LieMet

private theorem UpperTheory.scaled_norm_maximum_one {K C ι : Type} [Field K] [NormedField C] [Finite ι] (w : AbsoluteValue K ℝ)
    (io : K →+* C) (c : ℝ) (h1 : ∀ a, ‖io a‖ ≤ 1 → w a ≤ 1) (h2 : ∀ a, Real.log (w a) = c * Real.log ‖io a‖)
    (b : ι → K) {P : ℝ} (hP : 0 < P) (hb : P = ⨆ s, ‖io (b s)‖) {u : K} (hu : u ≠ 0)
    (h3 : Real.log (w u) = -(c * Real.log P)) : (∀ s, w (u * b s) ≤ 1) ∧ ∃ s, w (u * b s) = 1 := by
  rcases isEmpty_or_nonempty ι with hn | hn
  · simp [hb] at hP
  obtain ⟨i, hi⟩ := Finite.exists_max fun i => ‖io (b i)‖
  have e1 : P = ‖io (b i)‖ := hb.trans
    (le_antisymm (ciSup_le hi) (le_ciSup (f := fun j => ‖io (b j)‖) (Finite.bddAbove_range _) i))
  have h0 : b i ≠ 0 := fun h => by simp [e1, h] at hP
  have e2 : w (u * b i) = 1 := by
    refine Real.eq_one_of_pos_of_log_eq_zero (w.pos (mul_ne_zero hu h0)) ?_
    rw [map_mul, Real.log_mul (w.pos hu).ne' (w.pos h0).ne', h3, h2, e1, neg_add_cancel]
  refine ⟨fun j => ?_, i, e2⟩
  have := h1 (b j / b i) (by
    rw [map_div₀, norm_div]
    exact div_le_one_of_le₀ (hi j) (norm_nonneg _))
  rw [map_div₀, div_le_one (w.pos h0)] at this
  rw [← e2, map_mul, map_mul]
  exact mul_le_mul_of_nonneg_left this (w.nonneg _)

private theorem UpperTheory.tangent_coordinates_norm_le {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}} (t : SAB H X) (hX : X.IsSeparated) {A : Type} [CommRing A]
    {x₀ : Sp A ⟶ X} {g m : ℕ} {e : Fin g → (Sp (DualNumber A) ⟶ t.G.left)} (he : IsTanBasis t x₀ e)
    {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (x : A →+* C) (hx : ∀ a, ‖x a‖ ≤ 1)
    {u : Fin m → (Sp (DualNumber C) ⟶ t.G.left)} {a : Fin m → Fin g → C} (ha : LinearIndependent C a)
    (hu : ∀ l, IsCombAtG t (spMap x ≫ x₀) (fun i => spMap (dualMap x) ≫ e i) (a l) (u l)) :
    (∀ l, 0 < GlobalTheory.ShFam.Pad.grNorm t (spMap x ≫ x₀) (latDR t (spMap x ≫ x₀)) u l) ∧ ∀ (k : ℕ) (hk : k ≤ m),
      ∏ l : Fin k, GlobalTheory.ShFam.Pad.grNorm t (spMap x ≫ x₀) (latDR t (spMap x ≫ x₀)) u (Fin.castLE hk l) =
        ⨆ s, ‖minor a hk s‖ := by
  classical
  let y : A →+* ↥(intO C) := x.codRestrict _ hx
  have e1 : x = (intO C).subtype.comp y := rfl
  have h := GlobalTheory.T.successive_minima_positive_norms C g (Fin g) (fun j => Pi.single j 1) (fun b hb => funext fun i => by
      have := hb i
      rw [Finset.sum_eq_single i (fun i' _ hi => by simp [Pi.single_eq_of_ne hi]) (by simp)] at this
      simpa using this) m a ha (GlobalTheory.ShFam.Pad.grNorm t (spMap x ≫ x₀) (latDR t (spMap x ≫ x₀)) u) fun l => by
    refine grNorm_eq t (isTanBasis_map t _ he).1
      (P := fun b => ∀ j, ‖∑ i, (Pi.single j 1 : Fin g → C) i * b i‖ ≤ 1) ?_ hu l
    intro b w
    have := mem_latDR t hX (isTanBasis_map t y he) b w
    have e2 : ∀ j, ∑ i, (Pi.single j 1 : Fin g → C) i * b i = b j := fun j => by
      rw [Finset.sum_eq_single j (fun i' _ hi => by simp [Pi.single_eq_of_ne hi]) (by simp)]
      simp
    rw [e1]
    simpa only [e2, WedgeMax.spMap_comp, WedgeMax.spMap_dual_comp, Category.assoc] using this
  refine ⟨h.1, fun k hk => (h.2 k hk).trans (iSup_congr fun s => ?_)⟩
  rw [Finset.sum_eq_single s (fun s' _ hs => ?_) (by simp)]
  · simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hs
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Pi.single_eq_of_ne hi]), zero_mul]

private theorem UpperTheory.exists_stalk_map_over {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (π : X ⟶ Y)
    (φ : Y.functionField →+* X.functionField)
    (hφ : X.fromSpecStalk (genericPoint X) ≫ π = spMap φ ≫ Y.fromSpecStalk (genericPoint Y)) (z : X) (y : Y)
    (hy : π z = y) : ∃ θ : Y.presheaf.stalk y →+* X.presheaf.stalk z,
      spMap θ ≫ Y.fromSpecStalk y = X.fromSpecStalk z ≫ π ∧
      (algebraMap (X.presheaf.stalk z) X.functionField).comp θ =
        φ.comp (algebraMap (Y.presheaf.stalk y) Y.functionField) := by
  subst hy
  have h1 : spMap (π.stalkMap z).hom ≫ Y.fromSpecStalk (π z) = X.fromSpecStalk z ≫ π :=
    Scheme.SpecMap_stalkMap_fromSpecStalk π
  have h2 : spMap (algebraMap (X.presheaf.stalk z) X.functionField) ≫ X.fromSpecStalk z =
      X.fromSpecStalk (genericPoint X) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes z)
  have h3 : spMap (algebraMap (Y.presheaf.stalk (π z)) Y.functionField) ≫ Y.fromSpecStalk (π z) =
      Y.fromSpecStalk (genericPoint Y) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes _)
  refine ⟨(π.stalkMap z).hom, h1, ?_⟩
  refine congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono (Y.fromSpecStalk (π z))).1 (?_ :
    spMap _ ≫ _ = spMap _ ≫ _)))
  rw [← spMap_comp', ← spMap_comp', Category.assoc, Category.assoc, h1, h3, ← Category.assoc, h2, hφ]

private theorem UpperTheory.generic_stalk_spec_commutes {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (j : Y ⟶ X)
    (hη : j (genericPoint Y) ⤳ genericPoint X) {U : X.Opens} (hU : IsAffineOpen U) (h : genericPoint X ∈ U) :
    spMap ((SmallSec.fnMap j hη).comp (fnOf U h)) ≫ hU.fromSpec = Y.fromSpecStalk (genericPoint Y) ≫ j := by
  have h1 : spMap (fnOf U h) ≫ hU.fromSpec = X.fromSpecStalk (genericPoint X) :=
    hU.fromSpecStalk_eq_fromSpecStalk h
  have h2 : spMap (SmallSec.fnMap j hη) ≫ X.fromSpecStalk (genericPoint X) = Y.fromSpecStalk (genericPoint Y) ≫ j := by
    change Spec.map (X.presheaf.stalkSpecializes hη ≫ j.stalkMap (genericPoint Y)) ≫ _ = _
    rw [Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk]
  rw [← spMap_comp', Category.assoc, h1, h2]

private theorem UpperTheory.tangent_coordinates_naturality {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}} (t : SAB H X) {A : Type} [CommRing A]
    {x₀ : Sp A ⟶ X} {g m : ℕ} {e : Fin g → (Sp (DualNumber A) ⟶ t.G.left)} (he : IsTanBasis t x₀ e)
    {R K S L : Type} [CommRing R] [CommRing K] [CommRing S] [CommRing L] (ι : R →+* K) (ι' : S →+* L) (θ : R →+* S)
    (φ : K →+* L) (hc : ι'.comp θ = φ.comp ι) (α : A →+* S) {x : Sp R ⟶ X} (hx : spMap α ≫ x₀ = spMap θ ≫ x)
    {f : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} (hf : ∀ l, IsTanAtG t x (f l))
    {u : Fin m → (Sp (DualNumber K) ⟶ t.G.left)} {d : Fin m → K}
    (hT : ∀ i, ∃ cf : Fin m → K, cf i = d i ∧ (∀ k, i < k → cf k = 0) ∧
      IsCombAtG t (spMap ι ≫ x) (fun k => spMap (dualMap ι) ≫ f k) cf (u i))
    {A₁ : Fin m → Fin g → L}
    (hA : ∀ i, IsCombAtG t (spMap (ι'.comp α) ≫ x₀) (fun i => spMap (dualMap (ι'.comp α)) ≫ e i) (A₁ i)
      (spMap (dualMap φ) ≫ u i)) :
    ∃ a : Fin m → Fin g → S, (∀ l, IsCombAtG t (spMap α ≫ x₀) (fun i => spMap (dualMap α) ≫ e i) (a l)
      (spMap (dualMap θ) ≫ f l)) ∧ ∀ (r : Fin m → L) (k : ℕ) (hk : k ≤ m) s, minor (fun l => r l • A₁ l) hk s =
        (∏ l : Fin k, r (Fin.castLE hk l) * φ (d (Fin.castLE hk l))) * ι' (minor a hk s) := by
  have ha : ∀ l, ∃ a, IsCombAtG t (spMap α ≫ x₀) (fun i => spMap (dualMap α) ≫ e i) a (spMap (dualMap θ) ≫ f l) :=
    fun l => (he.2 _ α _ (isTan_map θ hx.symm (hf l))).exists
  choose a ha using ha
  choose T hT1 hT2 hT3 using hT
  refine ⟨a, ha, fun r k hk s => ?_⟩
  have h1 : ∀ i, A₁ i = ∑ l, φ (T i l) • fun j => ι' (a l j) := fun i => by
    refine (he.2 _ _ _ (comb_tan (fun j => isTan_map _ rfl (he.1 j)) (hA i))).unique (hA i) ?_
    refine comb_comb (fun j => isTan_map _ rfl (he.1 j)) (fun l => coord_map α ι' (ha l)) ?_
    have := GlobalTheory.LatDRFree.comb_map t φ (hT3 i)
    simp only [dual_comp] at this ⊢
    rw [← Category.assoc, spMap_comp', ← hc] at this
    rwa [← spMap_comp', Category.assoc, hx, ← Category.assoc, spMap_comp']
  rw [minor_tri (fun l j => ι' (a l j)) _ (fun i l => r i * φ (T i l)) (fun i l h => by rw [hT2 i l h]; simp)
    (fun i => by rw [h1 i, Finset.smul_sum]; simp only [smul_smul]), map_minor]
  simp only [hT1]

private theorem UpperTheory.prod_pow_expo_single {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {G : Type} [CommGroup G] (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → G)
    (a : ℕ → Bool) (R : Option ℝ) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) :
    ∏ z : Letter Dw, t z.1 z.2 ^ expo Dw (Finsupp.single (a, R, Sum.inl (τ, i)) 1 : Sym E →₀ ℤ) z = t τ i := by
  have h : letterOf Dw (a, R, (Sum.inl (τ, i) : ((E →+* ℂ) × ℕ) ⊕ ℕ)).2.2 = some ⟨τ, i⟩ := dif_pos i.2
  rw [Finset.prod_eq_single (⟨τ, i⟩ : Letter Dw) (fun b _ hb => by
    rw [GlobalTheory.Mean4O.expo_single, if_neg (fun e => hb (Option.some.inj (e.symm.trans h))), zpow_zero]) (by simp),
    GlobalTheory.Mean4O.expo_single, if_pos h, zpow_one]

section large₂
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {O : Type} [CommRing O] {β : O →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F]
    [NumberField F] {e : F ≃+* c.F}

private noncomputable def UpperTheory.eigenFrameNorm (Y : FlagCpt Z e) (w : Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F))
    (ε : GlobalTheory.TrueGeo.Ext v) (y : AlgPt Y.Y) [Fact (resP v).Prime] {χ : c.F →+* Y.Y.X.presheaf.stalk (below y.1)}
    (f : EigFrame Z χ (stalkPt Y.Y (below y.1) ≫ Y.π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ) : ℝ :=
  let ψ : Y.Y.X.presheaf.stalk (below y.1) →+* ℂ_[resP v] := (ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom
  Real.log (ε.w (valAt y.1 (((∏ x : Letter Dw, t x.1 x.2 ^ expo Dw w x) *
      (eqn (divOf Y (expo Dw w)) (below y.1))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn))) +
    (-Real.log (ε.w (resP v)) / Real.log (resP v)) *
      w.sum fun a n => (n : ℝ) * lnStep Z.t (spMap ψ ≫ stalkPt Y.Y (below y.1) ≫ Y.π ≫ genι Z)
        (fun τ i => spMap (dualMap ψ) ≫ f.v τ i) (resP v) (a.1 (resP v)) a.2.2

private theorem UpperTheory.lgOf_eq_frame_norm (Y : FlagCpt Z e) (w : Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F))
    (ε : GlobalTheory.TrueGeo.Ext v) (y : AlgPt Y.Y) (hp : (resP v).Prime) :
    lgOf Y w v ε y = @UpperTheory.eigenFrameNorm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Y w v ε y (GlobalTheory.ShFam.Pad.lgOf._proof_5 v hp) _
      (GlobalTheory.ShFam.Pad.lgOf._proof_3 Y y).choose (GlobalTheory.ShFam.Pad.lgOf._proof_4 Y y).choose := by
  unfold lgOf UpperTheory.eigenFrameNorm
  rewrite [dif_pos hp]
  refine congrArg₂ HAdd.hAdd rfl (congrArg₂ HMul.hMul rfl (congrArg (Finsupp.sum w)
    (funext fun a => funext fun n => congrArg₂ HMul.hMul rfl ?_)))
  rfl

private theorem UpperTheory.frame_norm_single (Y : FlagCpt Z e) (a : ℕ → Bool) (R : Option ℝ) (τ : E →+* ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (ha : a (resP v) = false) (ε : GlobalTheory.TrueGeo.Ext v) (y : AlgPt Y.Y)
    [hp : Fact (resP v).Prime] {χ : c.F →+* Y.Y.X.presheaf.stalk (below y.1)}
    (f : EigFrame Z χ (stalkPt Y.Y (below y.1) ≫ Y.π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ)
    (ψ : Y.Y.X.presheaf.stalk (below y.1) →+* ℂ_[resP v])
    (hψ : ψ = (ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom) (i : Fin (Dw.mult τ)) :
    UpperTheory.eigenFrameNorm Y (Finsupp.single (a, R, .inl (τ, i)) 1) v ε y f t =
      Real.log (ε.w (valAt y.1 ((t τ i : Y.Y.Fn) *
        genAt (divOf Y (expo Dw (Finsupp.single (a, R, .inl (τ, i)) 1))) (below y.1)))) +
      (-Real.log (ε.w (resP v)) / Real.log (resP v)) * Real.log (GlobalTheory.ShFam.Pad.grNorm Z.t
        (spMap ψ ≫ stalkPt Y.Y (below y.1) ≫ Y.π ≫ genι Z)
        (latDR Z.t (spMap ψ ≫ stalkPt Y.Y (below y.1) ≫ Y.π ≫ genι Z))
        (fun i => spMap (dualMap ψ) ≫ f.v τ i) i) := by
  rw [UpperTheory.eigenFrameNorm, ← hψ, Finsupp.sum_single_index (by simp), UpperTheory.prod_pow_expo_single]
  dsimp only
  rw [ha, lnStep, dif_pos i.2]
  simp only [Bool.false_eq_true, false_and, if_false, sub_zero, Int.cast_one, _root_.one_mul, Units.val_mul]
  rfl

private theorem UpperTheory.frame_log_norm_triangular (Y : FlagCpt Z e) (v : HeightOneSpectrum (𝓞 F)) (ε : GlobalTheory.TrueGeo.Ext v) (y : AlgPt Y.Y)
    [hp : Fact (resP v).Prime] : ∃ (χ : c.F →+* Y.Y.X.presheaf.stalk (below y.1))
    (f : EigFrame Z χ (stalkPt Y.Y (below y.1) ≫ Y.π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ),
    (f.Tri (algebraMap (Y.Y.X.presheaf.stalk (below y.1)) Y.Y.X.functionField) Y.f0 t ∧
      ∀ τ i, (Y.gr τ i).IsEqn (below y.1) (t τ i)) ∧ ∀ w, lgOf Y w v ε y = UpperTheory.eigenFrameNorm Y w v ε y f t := by
  obtain rfl : hp = GlobalTheory.ShFam.Pad.lgOf._proof_5 v (residueCharacteristic_prime v) := Subsingleton.elim _ _
  exact ⟨_, _, _, (GlobalTheory.ShFam.Pad.lgOf._proof_4 Y y).choose_spec, fun w => UpperTheory.lgOf_eq_frame_norm Y w v ε y (residueCharacteristic_prime v)⟩

private theorem UpperTheory.unitAt_frame_times_divisor (Y : FlagCpt Z e) (y : Y.Y.X) {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ}
    (ht : ∀ τ i, (Y.gr τ i).IsEqn y (t τ i)) (a : ℕ → Bool) (R : Option ℝ) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) :
    UnitAt y ((t τ i : Y.Y.Fn) * genAt (divOf Y (expo Dw (Finsupp.single (a, R, .inl (τ, i)) 1))) y) := by
  have hE : ∀ (n : Letter Dw → ℤ) (s : Finset (Letter Dw)),
      (∑ z ∈ s, n z • Y.gr z.1 z.2).IsEqn y (∏ z ∈ s, t z.1 z.2 ^ n z) := fun n s => by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using CartierDiv.isEqn_zero y
    | insert z s hz ih => rw [Finset.sum_insert hz, Finset.prod_insert hz]; exact ((ht _ _).zsmul _).add ih
  have h1 := hE (expo Dw (Finsupp.single (a, R, .inl (τ, i)) 1)) Finset.univ
  rw [UpperTheory.prod_pow_expo_single] at h1
  have h2 := (CartierDiv.IsEqn.iff_unitAt ((divOf Y (expo Dw
    (Finsupp.single (a, R, .inl (τ, i)) 1))).exists_isEqn y).choose_spec).1 h1
  rwa [div_eq_mul_inv, ← Units.val_inv_eq_inv_val] at h2

open MonObj in
private theorem UpperTheory.eigen_frame_independent {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x)
    (τ : E →+* ℂ) : IsIndep Z.t x fun l => f.v τ l := by
  intro cf cf' w h h'
  have h1 := (comb_iff (f.tan τ) _ _).1 h
  have h2 := (comb_iff (f.tan τ) _ _).1 h'
  exact funext ((Fintype.linearIndependent_iffₛ.1 (f.linearIndependent_vec τ)) _ _ (tan_ext (h1.symm.trans h2)))

end large₂

end SlopeTestRemainingChoices

open GlobalTheory.LineNorm.Chart GlobalTheory.LieMet ReciprocityTheory.ChartRestriction.G.PullbackSections in
theorem UpperTheory.flag_component_cover_frame_norm :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β), Z.X.IsSeparated → ∀ (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (C : FlagCpt Z e) (V : Cover C.Y) (b : V.X ⟶ Z.X), V.j ≫ b = V.π ≫ C.π ≫ genι Z → ∀ (hη : V.j (genericPoint V.G) ⤳ genericPoint V.X) (q : ℕ), q.Prime → ∀ (kind : ℕ → Bool) (R : Option ℝ), kind q = false → ∀ (τ : E →+* ℂ) (U : V.X.Opens) (hU : IsAffineOpen U) (h : genericPoint V.X ∈ U) (ρ : Fin (Dw.mult τ) → V.X.functionFieldˣ), (∀ (m : Fin (Dw.mult τ)) (z : V.G), V.j z ∈ U → UnitAt z (V.φ (genAt (divOf C (expo Dw (Finsupp.single (kind, R, .inl (τ, m)) 1))) (V.π z)) * SmallSec.fnMap V.j hη (ρ m))) → (∀ (m : Fin (Dw.mult τ)) (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v) (y : AlgPt C.Y) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp ε.O ⟶ V.X), z ≫ V.π = y.1 → spMap ε.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ U → lgOf C (Finsupp.single (kind, R, .inl (τ, m)) 1) v ε y = Real.log (ε.w (valAt z (V.φ (genAt (divOf C (expo Dw (Finsupp.single (kind, R, .inl (τ, m)) 1))) (below y.1)) * SmallSec.fnMap V.j hη (ρ m))))) → ∀ (g : ℕ) (eb : Fin g → (Sp (DualNumber Γ(V.X, U)) ⟶ Z.t.G.left)), IsTanBasis Z.t (R := Γ(V.X, U)) (hU.fromSpec ≫ b) eb → ∀ (A₀ : Fin (Dw.mult τ) → Fin g → V.X.functionField), (∀ m, IsCombAtG Z.t (spMap ((SmallSec.fnMap V.j hη).comp (fnOf U h)) ≫ hU.fromSpec ≫ b) (fun i => spMap (dualMap ((SmallSec.fnMap V.j hη).comp (fnOf U h))) ≫ eb i) (fun i => SmallSec.fnMap V.j hη (A₀ m i)) (spMap (dualMap V.φ) ≫ C.f0.v τ m)) → ∀ (k : ℕ) (hk : k ≤ Dw.mult τ), (∀ z : V.G, V.j z ∈ U → ∀ s, RegAt (V.j z) (minor (fun m => (((ρ m)⁻¹ : V.X.functionFieldˣ) : V.X.functionField) • A₀ m) hk s)) ∧ ∀ (v : HeightOneSpectrum (𝓞 F)), resP v = q → ∀ (ε : Ext v) (y : AlgPt C.Y) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp ε.O ⟶ V.X), z ≫ V.π = y.1 → spMap ε.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ U → (∀ s, ε.w (valAt (z ≫ V.j) (minor (fun m => (((ρ m)⁻¹ : V.X.functionFieldˣ) : V.X.functionField) • A₀ m) hk s)) ≤ 1) ∧ ∃ s, ε.w (valAt (z ≫ V.j) (minor (fun m => (((ρ m)⁻¹ : V.X.functionFieldˣ) : V.X.functionField) • A₀ m) hk s)) = 1 := by
  intro E _ _ _ H Dw l Xo c O _ β Z hZ F _ _ e C V b hb hη q _ kind R hkind τ U hU h ρ h1 h2 g eb he A₀ hA k hk
  have : IsPreimmersion V.j :=
    have := IsPreimmersion.of_isLocalization (R := 𝓞 F) (S := F) (nonZeroDivisors (𝓞 F))
    MorphismProperty.of_isPullback V.pb.flip this
  have key : ∀ (z : V.G) (_ : V.j z ∈ U) (y : C.Y.X) (_ : V.π z = y) (χ : c.F →+* C.Y.X.presheaf.stalk y)
      (f : EigFrame Z χ (stalkPt C.Y y ≫ C.π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ),
      f.Tri (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 t → (∀ τ i, (C.gr τ i).IsEqn y (t τ i)) →
      ∃ (θ : C.Y.X.presheaf.stalk y →+* V.G.presheaf.stalk z) (α : Γ(V.X, U) →+* V.G.presheaf.stalk z)
        (a : Fin (Dw.mult τ) → Fin g → V.G.presheaf.stalk z) (r : Fin (Dw.mult τ) → (C.Y.X.presheaf.stalk y)ˣ)
        (w : Fin (Dw.mult τ) → (V.G.presheaf.stalk z)ˣ),
        spMap θ ≫ C.Y.X.fromSpecStalk y = V.G.fromSpecStalk z ≫ V.π ∧
        spMap α ≫ hU.fromSpec = V.G.fromSpecStalk z ≫ V.j ∧
        spMap α ≫ hU.fromSpec ≫ b = spMap θ ≫ stalkPt C.Y y ≫ C.π ≫ genι Z ∧
        (∀ m, IsCombAtG Z.t (spMap α ≫ hU.fromSpec ≫ b) (fun i => spMap (dualMap α) ≫ eb i) (a m)
          (spMap (dualMap θ) ≫ f.v τ m)) ∧
        (∀ m, algebraMap _ C.Y.X.functionField (r m : C.Y.X.presheaf.stalk y) = (t τ m : C.Y.Fn) *
          genAt (divOf C (expo Dw (Finsupp.single (kind, R, .inl (τ, m)) 1))) y) ∧
        (∀ m, algebraMap _ V.G.functionField (w m : V.G.presheaf.stalk z) =
          V.φ (genAt (divOf C (expo Dw (Finsupp.single (kind, R, .inl (τ, m)) 1))) y) * SmallSec.fnMap V.j hη (ρ m)) ∧
        ∀ s, SmallSec.fnMap V.j hη
          (minor (fun m => (((ρ m)⁻¹ : V.X.functionFieldˣ) : V.X.functionField) • A₀ m) hk s) =
          algebraMap _ V.G.functionField ((∏ m : Fin k, θ (r (Fin.castLE hk m)) *
            ((w (Fin.castLE hk m))⁻¹ : (V.G.presheaf.stalk z)ˣ)) * minor a hk s) := by
    intro z hz y hy χ f t hT ht
    obtain ⟨θ, hθ1, hθ2⟩ := UpperTheory.exists_stalk_map_over V.π V.φ V.φ_spec z y hy
    obtain ⟨α, hα⟩ := exists_stalkHom hU V.j z hz
    have hx : spMap α ≫ hU.fromSpec ≫ b = spMap θ ≫ stalkPt C.Y y ≫ C.π ≫ genι Z := by
      rw [← Category.assoc, hα, Category.assoc, hb, ← Category.assoc, ← hθ1, Category.assoc]; rfl
    have hι : (SmallSec.fnMap V.j hη).comp (fnOf U h) =
        (algebraMap (V.G.presheaf.stalk z) V.G.functionField).comp α := ringHom_ext hU (by
      rw [UpperTheory.generic_stalk_spec_commutes, ← spMap_comp', Category.assoc, hα, ← Category.assoc]
      exact congrArg (· ≫ V.j) (Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes z)).symm)
    rw [hι] at hA
    obtain ⟨a, ha1, ha2⟩ := UpperTheory.tangent_coordinates_naturality Z.t he _ _ θ V.φ hθ2 α hx (f.tan τ) (d := fun m => (t τ m : C.Y.Fn))
      (fun i => hT.1 ▸ hT.2.2 τ i) hA
    have hr := fun m => UpperTheory.unitAt_frame_times_divisor C y ht kind R τ m
    have hw := fun m => h1 m z hz
    rw [hy] at hw
    choose r hr1 hr2 using hr
    choose w hw1 hw2 using hw
    refine ⟨θ, α, a, fun m => (hr1 m).unit, fun m => (hw1 m).unit, hθ1, hα, hx, ha1, hr2, hw2, fun s => ?_⟩
    have e1 := ha2 (fun m => SmallSec.fnMap V.j hη ((ρ m)⁻¹ : V.X.functionFieldˣ)) k hk s
    rw [map_minor, map_mul, map_prod]
    refine Eq.trans ?_ (e1.trans ?_)
    · congr 1
      funext m i
      exact map_mul _ _ _
    · congr 1
      refine Finset.prod_congr rfl fun m _ => ?_
      have e2 : algebraMap _ V.G.functionField (θ (r (Fin.castLE hk m))) =
          V.φ (algebraMap _ C.Y.X.functionField (r (Fin.castLE hk m))) := RingHom.congr_fun hθ2 _
      rw [map_mul, map_units_inv, map_units_inv, IsUnit.unit_spec, IsUnit.unit_spec, e2, hr2, hw2, map_mul,
        mul_inv, ← _root_.mul_assoc, mul_inv_cancel_right₀ ((map_ne_zero _).2 (Units.ne_zero _)), mul_comm]
  have reg : ∀ z : V.G, V.j z ∈ U → ∀ s,
      RegAt (V.j z) (minor (fun m => (((ρ m)⁻¹ : V.X.functionFieldˣ) : V.X.functionField) • A₀ m) hk s) := by
    intro z hz s
    obtain ⟨χ, f, t, hT, ht⟩ := C.gr_spec (V.π z)
    obtain ⟨θ, α, a, r, w, -, -, -, -, -, -, h6⟩ := key z hz _ rfl χ f t hT ht
    exact (SmallSec.regAt_fnMap_iff V.j hη).1 ⟨_, (h6 s).symm⟩
  refine ⟨reg, fun v hv ε y z yt hz hyt hin => ?_⟩
  subst hv
  obtain ⟨hp, i1, i2⟩ := ioOf_spec F v ε
  have := Fact.mk hp
  obtain ⟨γ, hγ⟩ := exists_ringHom hU yt hin
  have hy : V.j (below z) ∈ U := by
    have : (spMap ε.O.subtype ≫ yt) (IsLocalRing.closedPoint _) ∈ U := hin (Set.mem_univ _)
    rwa [hyt] at this
  have hzy : V.π (below z) = below y.1 := by rw [← hz]; rfl
  obtain ⟨χ, f, t, ⟨hT, ht⟩, hlg⟩ := UpperTheory.frame_log_norm_triangular C v ε y
  obtain ⟨θ, α, a, r, w, k1, k2, k3, k4, k5, k6, k7⟩ := key (below z) hy _ hzy χ f t hT ht
  obtain ⟨σ, hσ₀⟩ : ∃ σ : V.G.presheaf.stalk (below z) →+* AlgebraicClosure F,
    σ = (Scheme.stalkClosedPointTo z).hom := ⟨_, rfl⟩
  have hσz : spMap σ ≫ V.G.fromSpecStalk (below z) = z := by
    rw [hσ₀]; exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk z
  have hσ : σ.comp α = ε.O.subtype.comp γ := ringHom_ext hU (by
    rw [← spMap_comp', ← spMap_comp', Category.assoc, Category.assoc, k2, hγ, hyt, ← Category.assoc, hσz])
  have hσθ : σ.comp θ = (Scheme.stalkClosedPointTo y.1).hom := by
    refine congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono (C.Y.X.fromSpecStalk (below y.1))).1 (?_ :
      spMap (σ.comp θ) ≫ _ = _)))
    rw [← spMap_comp', Category.assoc, k1, ← Category.assoc, hσz, hz]
    exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk y.1).symm
  obtain ⟨ψ, hψ⟩ : ∃ ψ, ψ = (ioOf (resP v) ε).comp σ := ⟨_, rfl⟩
  have hli : LinearIndependent ℂ_[resP v] fun l i => ψ (a l i) := by
    refine coord_linInd he α ψ k4 ?_
    obtain ⟨f', hf'⟩ := f.exists_isMap (ψ.comp θ) rfl rfl
    rw [k3, ← Category.assoc, spMap_comp']
    simp only [dual_comp, ← hf' τ]
    exact UpperTheory.eigen_frame_independent f' τ
  have h3 := UpperTheory.tangent_coordinates_norm_le Z.t hZ he (ψ.comp α) (fun b => by
      have : σ (α b) = γ b := congrArg (fun q => q b) hσ
      rw [hψ, RingHom.comp_apply, RingHom.comp_apply, i1, this]; exact (γ b).2) hli fun l => coord_map α ψ (k4 l)
  rw [← spMap_comp', Category.assoc, k3, ← Category.assoc, spMap_comp'] at h3
  simp only [dual_comp] at h3
  have hv : ∀ b, valAt z (algebraMap (V.G.presheaf.stalk (below z)) V.G.functionField b) = σ b := fun b => by
    rw [hσ₀]; exact SmallSec.valAt_algebraMap _
  have hv' : ∀ b, valAt y.1 (algebraMap (C.Y.X.presheaf.stalk (below y.1)) C.Y.X.functionField b) = σ (θ b) := fun b => by
    rw [← RingHom.comp_apply, hσθ]; exact SmallSec.valAt_algebraMap _
  have h4 := fun m => ((h2 m v ε y z yt hz hyt hin).symm.trans (hlg _)).trans
    (UpperTheory.frame_norm_single C kind R τ v hkind ε y f t (ψ.comp θ) (by rw [hψ, RingHom.comp_assoc, hσθ]) m)
  simp only [← k5, ← k6, hv, hv'] at h4
  have n1 : ∀ m, σ (θ (r m)) ≠ 0 := fun m => (((r m).isUnit.map θ).map σ).ne_zero
  have n2 : ∀ m, σ (w m) ≠ 0 := fun m => ((w m).isUnit.map σ).ne_zero
  simp only [← SmallSec.valAt_fnMap V.j hη z (reg _ hy _), k7, hv, map_mul σ]
  refine UpperTheory.scaled_norm_maximum_one ε.w (ioOf (resP v) ε) _ (fun b hb => (ε.mem_O b).1 ((i1 b).1 hb)) i2 _
    (Finset.prod_pos fun m _ => h3.1 _) ((h3.2 k hk).trans (iSup_congr fun s => ?_)) ?_ ?_
  · rw [← map_minor, hψ]; rfl
  · exact (((IsUnit.prod_univ_iff).2 fun m => ((r _).isUnit.map θ).mul (Units.isUnit _)).map σ).ne_zero
  · rw [map_prod, map_prod, Real.log_prod fun m _ => (ε.w.pos
      ((((r _).isUnit.map θ).mul (Units.isUnit _)).map σ).ne_zero).ne', Real.log_prod fun m _ => (h3.1 _).ne',
      Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul, map_units_inv, map_mul, map_inv₀, Real.log_mul (ε.w.pos (n1 _)).ne' (inv_ne_zero (ε.w.pos (n2 _)).ne'),
      Real.log_inv, h4]
    ring
