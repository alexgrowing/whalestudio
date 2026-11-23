import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriFrames
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomOfCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodReductionExtendsRegular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointClosureExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelRefinementGenerating
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalModelOverProjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomogeneousPolysTangentBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverRefinementExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothOfAlgClosedUnif
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AutomorphicArithmetic.DivisorFrames.ArithmeticVarietyNormalModel
import Development.AutomorphicArithmetic.DivisorFrames.TriangularBasisFromUnitMinors
import Development.AutomorphicArithmetic.DivisorFrames.SplitEigenTangentCoordinates
import Development.AutomorphicArithmetic.DivisorFrames.TangentSectionsLineBundleUnits
import Development.AutomorphicArithmetic.DivisorFrames.FlagComponentCoverFrameNorm

section Helpers

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.Mean4O
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TriFlag.Pf

private theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := (Spec.map_comp _ _)

private theorem sp_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

private theorem shrink {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} {x : X} (hx : x ∈ U) {I J : Type} [Finite I] [Finite J]
    (f : I → X.functionField) (u : J → X.functionField) (hf : ∀ i, RegAt x (f i)) (hu : ∀ j, UnitAt x (u j)) :
    ∃ (T : X.Opens) (_ : IsAffineOpen T) (hxT : x ∈ T), T ≤ U ∧ (∀ i, ∃ c, fnOf T (gen_mem hxT) c = f i) ∧
      ∀ j, ∃ c : Γ(X, T)ˣ, fnOf T (gen_mem hxT) c = u j := by
  obtain ⟨W, hW, hc⟩ := GlobalTheory.InvertIdeal.exists_common_open (x := x) (ι := I ⊕ J ⊕ J)
    (g := Sum.elim f (Sum.elim u fun j => (u j)⁻¹)) (by
      rintro (i | j | j)
      exacts [hf i, (hu j).regAt, (hu j).inv.regAt])
  obtain ⟨T, hT, hxT, hle⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ W ⊓ U from ⟨hW, hx⟩)
  have hle' : T ≤ W ⊓ U := hle
  have key : ∀ k, ∃ c, fnOf T (gen_mem hxT) c = Sum.elim f (Sum.elim u fun j => (u j)⁻¹) k := fun k => by
    obtain ⟨a, ha⟩ := hc k
    exact ⟨resG X (hle'.trans inf_le_left) a, (fnOf_resG _ _ _).trans ha⟩
  refine ⟨T, hT, hxT, hle'.trans inf_le_right, fun i => key (.inl i), fun j => ?_⟩
  obtain ⟨a, ha⟩ := key (.inr (.inl j))
  obtain ⟨a', ha'⟩ := key (.inr (.inr j))
  have h1 : a * a' = 1 := fnOf_injective T (gen_mem hxT) (by
    rw [map_mul, ha, ha', map_one]; exact mul_inv_cancel₀ (hu j).ne_zero)
  exact ⟨⟨a, a', h1, by rw [mul_comm, h1]⟩, ha⟩

private theorem gen_eq {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U) (h : genericPoint X ∈ U) :
    spMap (fnOf U h) ≫ hU.fromSpec = GlobalTheory.CurveRootGeometry.genPt X :=
  hU.fromSpecStalk_eq_fromSpecStalk h

private theorem minors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β), Z.X.IsSeparated → ∀ (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (C : FlagCpt Z e) (V : Cover C.Y) (b : V.X ⟶ Z.X), V.j ≫ b = V.π ≫ C.π ≫ genι Z → ∀ (hη : V.j (genericPoint V.G) ⤳ genericPoint V.X) (q : ℕ), q.Prime → ∀ (kind : ℕ → Bool) (R : Option ℝ), kind q = false → ∀ (τ : E →+* ℂ) (U : V.X.Opens) (hU : IsAffineOpen U) (h : genericPoint V.X ∈ U) (ρ : Fin (Dw.mult τ) → V.X.functionFieldˣ), (∀ (m : Fin (Dw.mult τ)) (z : V.G), V.j z ∈ U → UnitAt z (V.φ (genAt (divOf C (expo Dw (Finsupp.single (kind, R, .inl (τ, m)) 1))) (V.π z)) * SmallSec.fnMap V.j hη (ρ m))) → (∀ (m : Fin (Dw.mult τ)) (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v) (y : AlgPt C.Y) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp ε.O ⟶ V.X), z ≫ V.π = y.1 → spMap ε.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ U → lgOf C (Finsupp.single (kind, R, .inl (τ, m)) 1) v ε y = Real.log (ε.w (valAt z (V.φ (genAt (divOf C (expo Dw (Finsupp.single (kind, R, .inl (τ, m)) 1))) (below y.1)) * SmallSec.fnMap V.j hη (ρ m))))) → ∀ (g : ℕ) (eb : Fin g → (Sp (DualNumber Γ(V.X, U)) ⟶ Z.t.G.left)), IsTanBasis Z.t (R := Γ(V.X, U)) (hU.fromSpec ≫ b) eb → ∀ (A₀ : Fin (Dw.mult τ) → Fin g → V.X.functionField), (∀ m, IsCombAtG Z.t (spMap ((SmallSec.fnMap V.j hη).comp (fnOf U h)) ≫ hU.fromSpec ≫ b) (fun i => spMap (dualMap ((SmallSec.fnMap V.j hη).comp (fnOf U h))) ≫ eb i) (fun i => SmallSec.fnMap V.j hη (A₀ m i)) (spMap (dualMap V.φ) ≫ C.f0.v τ m)) → ∀ x ∈ U, ¬ IsUnit (q : V.X.presheaf.stalk x) → ∀ (k : ℕ) (hk : k ≤ Dw.mult τ), (∀ s, RegAt x (minor (fun m => (((ρ m)⁻¹ : V.X.functionFieldˣ) : V.X.functionField) • A₀ m) hk s)) ∧ ∃ s, UnitAt x (minor (fun m => (((ρ m)⁻¹ : V.X.functionFieldˣ) : V.X.functionField) • A₀ m) hk s) := by
  intro E _ _ _ H Dw l Xo c O _ β Z hZ F _ _ e C V b hb hη q hq kind R hk τ U hU h ρ h1 h2 g eb he A₀ hA x hx hxq k hkn
  obtain ⟨hreg, hval⟩ := UpperTheory.flag_component_cover_frame_norm E H Dw l Xo c O β Z hZ F e C V b hb hη q hq kind R hk τ U hU h ρ h1 h2 g eb he A₀ hA k hkn
  have hR : ∀ s, ∀ x ∈ U, ¬ IsUnit (q : V.X.presheaf.stalk x) → RegAt x (minor (fun m => (((ρ m)⁻¹ : V.X.functionFieldˣ) : V.X.functionField) • A₀ m) hkn s) := fun s =>
    GlobalTheory.Mean4O.Cover.RegOverP.regAt_of_values_over F C.Y V q hq ⊤ trivial U _ (fun z hz => hreg z hz s)
      fun v hv ε y _ z yt a1 a2 a3 => (hval v hv ε y z yt a1 a2 a3).1 s
  refine ⟨fun s => hR s x hx hxq, ?_⟩
  have hxq' : (q : 𝓞 F) ∈ (V.p x).asIdeal := by
    by_contra hn
    exact hxq ((GlobalTheory.Mean4O.Cover.RegOverP.isUnit_natCast_stalk_iff V x q).2 hn)
  obtain ⟨v, ε, z, yt, hv, hz, hyt, hin, hsp, hun⟩ := GlobalTheory.HtGen.IntPt.exists_intPt F C.Y V q U x hx hxq'
  obtain ⟨s, hs⟩ := (hval v (GlobalTheory.Mean4O.Cover.RegOverP.residueCharacteristic_eq_of_mem hq hv) ε ⟨z ≫ V.π, by rw [Category.assoc, hz]⟩ z yt rfl hyt hin).2
  have hx' : yt (IsLocalRing.closedPoint ε.O) ∈ U := hin trivial
  have hq' : ¬ IsUnit (q : V.X.presheaf.stalk (yt (IsLocalRing.closedPoint ε.O))) := fun hu => by
    have := hu.map (V.X.presheaf.stalkSpecializes hsp).hom
    rw [map_natCast] at this
    exact hxq this
  obtain ⟨a, ha, ea⟩ := (hun _ (hR s _ hx' hq')).1 hs
  refine ⟨s, (V.X.presheaf.stalkSpecializes hsp).hom a, ha.map _, ?_⟩
  rw [← ea]
  exact congrArg (fun φ => φ.hom a) (V.X.presheaf.stalkSpecializes_comp (genericPoint_specializes x) hsp)

private theorem loc {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
    (t : SAB H X) {A : Type} [CommRing A] (s : X ⟶ Sp A) {S : Type} [Fintype S] (ε : S → (𝓞 E →+* A)) (τ : S)
    {W : Scheme.{0}} [IsIntegral W] (b : W ⟶ X) {U : W.Opens} (hU : IsAffineOpen U) {x : W} (hx : x ∈ U)
    (κ : A →+* W.functionField) (hκ : (GlobalTheory.CurveRootGeometry.genPt W ≫ b) ≫ s = spMap κ)
    (hsp : GlobalTheory.VB.IsSplitBy fun σ => κ.comp (ε σ)) (hsep : ∀ σ, σ ≠ τ → ∃ c, UnitAt x (κ (ε τ c) - κ (ε σ c)))
    {g : ℕ} (eb : Fin g → (Sp (DualNumber Γ(W, U)) ⟶ t.G.left)) (he : IsTanBasis t (R := Γ(W, U)) (hU.fromSpec ≫ b) eb)
    {n : ℕ} (u₀ : Fin n → (Sp (DualNumber W.functionField) ⟶ t.G.left))
    (h0 : ∀ m, IsTanAtG t (GlobalTheory.CurveRootGeometry.genPt W ≫ b) (u₀ m))
    (h1 : ∀ (m : Fin n) (c : 𝓞 E), u₀ m ≫ (t.act.act c).left = spMap (epsMul (κ (ε τ c))) ≫ u₀ m)
    (h2 : ∀ w, IsTanAtG t (GlobalTheory.CurveRootGeometry.genPt W ≫ b) w →
      (∀ c : 𝓞 E, w ≫ (t.act.act c).left = spMap (epsMul (κ (ε τ c))) ≫ w) →
      ∃ cf : Fin n → W.functionField, IsCombAtG t (GlobalTheory.CurveRootGeometry.genPt W ≫ b) u₀ cf w)
    (A₀ : Fin n → Fin g → W.functionField)
    (hA : ∀ l, IsCombAtG t (GlobalTheory.CurveRootGeometry.genPt W ≫ b) (fun i => spMap (dualMap (fnOf U (gen_mem hx))) ≫ eb i) (A₀ l) (u₀ l))
    (d : Fin n → W.functionField)
    (hm : ∀ (k : ℕ) (hk : k ≤ n), (∀ s, RegAt x (minor (fun m => d m • A₀ m) hk s)) ∧
      ∃ s, UnitAt x (minor (fun m => d m • A₀ m) hk s)) :
    ∃ (T : W.Opens) (hT : IsAffineOpen T) (hxT : x ∈ T) (w : Fin n → (Sp (DualNumber Γ(W, T)) ⟶ t.G.left)), T ≤ U ∧
      IsLocFr t s (ε τ) (R := Γ(W, T)) (hT.fromSpec ≫ b) w ∧
      IsTriOf t (GlobalTheory.CurveRootGeometry.genPt W ≫ b) u₀ d (fun m => spMap (dualMap (fnOf T (gen_mem hxT))) ≫ w m) := by
  classical
  choose cs hcs using hsep
  choose s₀ hs₀ using fun (k : ℕ) (hk : k ≤ n) => (hm k hk).2
  obtain ⟨T, hT, hxT, hle, hf, hu⟩ := shrink hx (I := Σ k : Fin (n + 1), Fin k → Fin g) (J := Fin (n + 1) ⊕ {σ // σ ≠ τ})
    (fun i => minor (fun m => d m • A₀ m) (Nat.lt_succ_iff.1 i.1.2) i.2)
    (Sum.elim (fun k => minor (fun m => d m • A₀ m) (Nat.lt_succ_iff.1 k.2) (s₀ _ (Nat.lt_succ_iff.1 k.2)))
      fun σ => κ (ε τ (cs σ.1 σ.2)) - κ (ε σ.1 (cs σ.1 σ.2)))
    (fun i => (hm _ _).1 _) (by
      rintro (k | σ)
      exacts [hs₀ _ _, hcs _ _])
  let ι := fnOf T (gen_mem hxT)
  have hι : Function.Injective ι := fnOf_injective _ _
  obtain ⟨v, Tm, hT1, hT2, hT3, hT4⟩ := UpperTheory.triangular_basis_from_unit_minors Γ(W, T) W.functionField ι hι n g (fun m => d m • A₀ m)
    (fun k hk s => hf ⟨⟨k, Nat.lt_succ_iff.2 hk⟩, s⟩) (fun k hk => ⟨_, hu (.inl ⟨k, Nat.lt_succ_iff.2 hk⟩)⟩)
  let r : Γ(W, U) →+* Γ(W, T) := resG W hle
  have hr : spMap r ≫ hU.fromSpec = hT.fromSpec := hU.map_fromSpec hT (homOfLE hle).op
  have hιr : ι.comp r = fnOf U (gen_mem hx) := RingHom.ext fun a => fnOf_resG _ _ _
  have hg : spMap ι ≫ hT.fromSpec ≫ b = GlobalTheory.CurveRootGeometry.genPt W ≫ b := by
    rw [← Category.assoc, gen_eq]
  have he' : IsTanBasis t (R := Γ(W, T)) (hT.fromSpec ≫ b) fun i => spMap (dualMap r) ≫ eb i := by
    have := GlobalTheory.LineNorm.WedgeMax.isTanBasis_map t r he
    rwa [← Category.assoc, hr] at this
  let κ' : A →+* Γ(W, T) := (Spec.preimage ((hT.fromSpec ≫ b) ≫ s)).hom
  have hκ' : (hT.fromSpec ≫ b) ≫ s = spMap κ' := (Spec.map_preimage _).symm
  have hικ : ι.comp κ' = κ := sp_inj (by rw [sp_comp, ← hκ', ← hκ, ← hg]; simp only [Category.assoc])
  have hικ' : ∀ a, ι (κ' a) = κ a := fun a => congrArg (fun f => f a) hικ
  have hA' : ∀ l, IsCombAtG t (spMap ι ≫ hT.fromSpec ≫ b) (fun i => spMap (dualMap ι) ≫ spMap (dualMap r) ≫ eb i)
      (A₀ l) (u₀ l) := fun l => by
    simp only [GlobalTheory.LineNorm.Chart.dual_comp, hιr, hg]
    exact hA l
  have hT3' : ∀ i, (fun j => ι (v i j)) = ∑ l, (Tm i l * d l) • A₀ l := fun i => by
    rw [hT3]; simp only [smul_smul]
  obtain ⟨w, hw, hL⟩ := UpperTheory.split_eigen_tangent_coordinates E H X t A s S ε τ Γ(W, T) W.functionField ι hι (hT.fromSpec ≫ b) κ' hκ'
    (by rw [hικ]; exact hsp)
    (fun σ hσ => ⟨cs σ hσ, by
      obtain ⟨c, hc⟩ := hu (.inr ⟨σ, hσ⟩)
      have : κ' (ε τ (cs σ hσ)) - κ' (ε σ (cs σ hσ)) = c := hι (by rw [map_sub, hικ', hικ']; exact hc.symm)
      rw [this]; exact c.isUnit⟩)
    g _ he' n u₀ (by simpa only [hικ'] using h1) (by simpa only [hικ', hg] using h2) A₀ hA' v
    (fun i l => Tm i l * d l) hT3' hT4
  refine ⟨T, hT, hxT, w, hle, hL, fun m => ⟨fun l => Tm m l * d l, by simp only [hT1, one_mul],
    fun m' h => by simp only [hT2 m m' h, zero_mul], ?_⟩⟩
  obtain ⟨w', -, hw'⟩ := GlobalTheory.LineNorm.WedgeMax.exists_comb t h0 fun l => Tm m l * d l
  have htan : ∀ i, IsTanAtG t (spMap ι ≫ hT.fromSpec ≫ b) (spMap (dualMap ι) ≫ spMap (dualMap r) ≫ eb i) := fun i =>
    GlobalTheory.LieMet.isTan_map _ rfl (he'.1 i)
  have a1 := GlobalTheory.LineNorm.Chart.comb_comb htan hA' (hg ▸ hw')
  have a2 := GlobalTheory.LatDRFree.comb_map t ι (hw m)
  rw [hT3'] at a2
  have a3 := GlobalTheory.LineNorm.WedgeMax.comb_unique t htan a2 a1
  rw [← a3] at hw'
  exact hw'

private theorem valR_gen {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} (h : genericPoint X ∈ U) (a : Γ(X, U)) :
    valR (GlobalTheory.CurveRootGeometry.genPt X) U a = fnOf U h a := by
  have h' : ⊤ ≤ (GlobalTheory.CurveRootGeometry.genPt X) ⁻¹ᵁ U := GlobalTheory.HtGen.IntPt.top_le_of_closedPoint _ (by
    have : GlobalTheory.CurveRootGeometry.genPt X (IsLocalRing.closedPoint _) = genericPoint X := Scheme.fromSpecStalk_closedPoint
    rwa [this])
  rw [GlobalTheory.Points.valR_eq _ _ h']
  have e : ∀ (x : X) (hx : x ∈ U) (h'' : ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U),
      (X.fromSpecStalk x).appLE U ⊤ h'' ≫ (Scheme.ΓSpecIso _).hom = X.presheaf.germ U x hx := fun x hx h'' => by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, ← op_comp, Subsingleton.elim (homOfLE _ ≫ homOfLE _) (𝟙 _), op_id,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id, Category.comp_id]
  exact congrArg (fun φ => φ.hom a) (e _ h h')

private theorem ratSec {G X Y : Scheme.{0}} [IsIntegral G] [IsIntegral X] (j : G ⟶ X) (a : X ⟶ Y) (j₀ : G ⟶ Y)
    (hj : j ≫ a = j₀) (J : X.functionField →+* G.functionField)
    (hJ : spMap J ≫ GlobalTheory.CurveRootGeometry.genPt X = GlobalTheory.CurveRootGeometry.genPt G ≫ j) (L : LB Y) (r : (L.pull j₀).ι → G.functionFieldˣ)
    (hr : IsRatSec (L.pull j₀) r) (ρ : L.ι → X.functionFieldˣ) (hρ : ∀ i, J (ρ i) = r fun _ => i) (i k : L.ι)
    (h : ⊤ ≤ (GlobalTheory.CurveRootGeometry.genPt X ≫ a) ⁻¹ᵁ (L.U i ⊓ L.U k)) :
    (ρ i : X.functionField) = valR (GlobalTheory.CurveRootGeometry.genPt X ≫ a) _ (L.g i k).val * ρ k := by
  apply J.injective
  have e : spMap J ≫ GlobalTheory.CurveRootGeometry.genPt X ≫ a = GlobalTheory.CurveRootGeometry.genPt G ≫ j₀ := by
    rw [← Category.assoc, hJ, Category.assoc, hj]
  have h1 : ⊤ ≤ (GlobalTheory.CurveRootGeometry.genPt G ≫ j₀) ⁻¹ᵁ (L.U i ⊓ L.U k) := by
    rw [← e]; exact fun z _ => h (x := spMap J z) trivial
  have h2 : genericPoint G ∈ j₀ ⁻¹ᵁ (L.U i ⊓ L.U k) := by
    have := h1 (x := IsLocalRing.closedPoint _) trivial
    have e2 : GlobalTheory.CurveRootGeometry.genPt G (IsLocalRing.closedPoint _) = genericPoint G := Scheme.fromSpecStalk_closedPoint
    rw [← e2]; exact this
  have h3 : genericPoint G ∈ (L.pull j₀).U (fun _ => i) ⊓ (L.pull j₀).U (fun _ => k) :=
    ⟨Set.mem_iInter.2 fun _ => h2.1, Set.mem_iInter.2 fun _ => h2.2⟩
  rw [map_mul, hρ, hρ, hr _ _ h3, ← GlobalTheory.Points.valR_spMap_comp J _ _ h, e, GlobalTheory.Points.valR_comp, valR_gen h2]
  congr 1
  have e3 : (L.pull j₀).g (fun _ => i) (fun _ => k) =
      res (LB.wchart_inter_le L (fun _ => j₀) (fun _ => i) (fun _ => k) ⟨⟩) (pullU j₀ _ (L.g i k)) := by
    change LB.lcg L (fun _ : PUnit => j₀) (fun _ => 1) _ _ = _
    rw [LB.lcg, Fintype.prod_unique, zpow_one]
  rw [e3]
  exact fnOf_resG _ _ _

private theorem sep {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H}
    (c : Coeff l) {q : ℕ} [Fact q.Prime] (hd : ¬ q ∣ (discr E).natAbs) {W : Scheme.{0}} [IsIntegral W]
    (p : W ⟶ Sp (𝓞 c.F)) (κ : 𝓞 c.F →+* W.functionField) (hκ : GlobalTheory.CurveRootGeometry.genPt W ≫ p = spMap κ) (x : W)
    (hx : ((q : ℕ) : W.residueField x) = 0) (τ σ : E →+* ℂ) (h : σ ≠ τ) :
    ∃ a, UnitAt x (κ (GlobalTheory.CurveRootGeometry.intEmb c τ a) - κ (GlobalTheory.CurveRootGeometry.intEmb c σ a)) := by
  let κx : 𝓞 c.F →+* W.presheaf.stalk x := (Spec.preimage (W.fromSpecStalk x ≫ p)).hom
  have h1 : spMap κx = W.fromSpecStalk x ≫ p := Spec.map_preimage _
  have h2 : (algebraMap (W.presheaf.stalk x) W.functionField).comp κx = κ := sp_inj (by
    rw [sp_comp, h1, ← hκ, ← Category.assoc]
    congr 1
    exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x))
  have : CharP (IsLocalRing.ResidueField (W.presheaf.stalk x)) q := (CharP.charP_iff_prime_eq_zero Fact.out).2 hx
  have h3 := (GlobalTheory.CurveRootGeometry.isSplitBy_intEmb c hd ((IsLocalRing.residue (W.presheaf.stalk x)).comp κx)).injective
  by_contra hn
  refine h (h3 (RingHom.ext fun a => ?_))
  by_contra ha
  refine hn ⟨a, κx (GlobalTheory.CurveRootGeometry.intEmb c τ a) - κx (GlobalTheory.CurveRootGeometry.intEmb c σ a), ?_, by rw [← h2, map_sub]; rfl⟩
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sub, sub_ne_zero]
  exact fun e => ha e.symm

private theorem gen_main {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F}
    (C : FlagCpt Z e) {cx : CxSt F} (hm : Mets C cx) (V : Cover C.Y) (q : ℕ) [Fact q.Prime] (hd : ¬ q ∣ (discr E).natAbs)
    (kind : ℕ → Bool) (R : Option ℝ) (hk : kind q = false) (L : (E →+* ℂ) → ℕ → HermLB V.p)
    (hL : ∀ τ (m : Fin (Dw.mult τ)), V.Induces (adlOf C hm (Finsupp.single (kind, R, .inl (τ, m)) 1)) (L τ m) 1) :
    ∃ (W : Scheme.{0}) (a : W ⟶ V.X) (b : W ⟶ Z.X), IsProjOver (a ≫ V.p) ∧ Surjective a ∧
      ∀ τ : E →+* ℂ, TriFrames Z.t Z.s (GlobalTheory.CurveRootGeometry.intEmb c τ) q b a (Dw.mult τ) (fun m => (L τ m).B) := by
  have : FiniteDimensional ℚ c.F := c.fin
  have : NumberField c.F := {}
  let ε₀ : 𝓞 F ≃+* 𝓞 c.F := RingOfIntegers.mapRingEquiv e
  have hgs : genι Z ≫ Z.s = genStr Z ≫ spMap (algebraMap (𝓞 c.F) c.F) := pullback.condition
  obtain ⟨X, _, j, a, b, har, hn, hpb, hja, hjb, hsur⟩ := UpperTheory.arithmetic_variety_normal_model F C.Y V Z.X (Z.s ≫ spMap ε₀.toRingHom)
    (V.π ≫ C.π ≫ genι Z) (GlobalTheory.ModelOver.isProjOver_comp_spMap ε₀ Z.proj) (by
      rw [← C.π_str]
      simp only [Category.assoc]
      rw [reassoc_of% hgs, ← sp_comp, ← sp_comp]
      rfl)
  let V' : Cover C.Y := ⟨X, a ≫ V.p, har, hn, V.G, j, V.π, hpb, V.φ, V.φ_spec⟩
  have hη : j (genericPoint V.G) ⤳ genericPoint X := GlobalTheory.HtGen.SplitCover.j_gen_specializes V'
  have : IsPreimmersion j := GlobalTheory.HtGen.SplitCover.isPreimmersion_j V'
  let J := SmallSec.fnMap j hη
  let Je : X.functionField ≃+* V.G.functionField :=
    RingEquiv.ofBijective J ⟨J.injective, SmallSec.fnMap_surjective j hη⟩
  have hJ : spMap J ≫ GlobalTheory.CurveRootGeometry.genPt X = GlobalTheory.CurveRootGeometry.genPt V.G ≫ j := GlobalTheory.HtGen.SplitCover.spMap_fnMap j hη
  let θ : C.Y.Fn →+* X.functionField := Je.symm.toRingHom.comp V.φ
  have hθ : J.comp θ = V.φ := RingHom.ext fun f => Je.apply_symm_apply _
  have hpt : GlobalTheory.CurveRootGeometry.genPt X ≫ b = spMap θ ≫ genericPt C.Y ≫ C.π ≫ genι Z := by
    have i1 : IsIso (spMap J) := by
      have : IsIso (CommRingCat.ofHom J) := Je.toCommRingCatIso.isIso_hom
      exact inferInstance
    rw [← cancel_epi (spMap J), reassoc_of% hJ, hjb, ← Category.assoc (spMap J), ← sp_comp, hθ]
    have := V.φ_spec
    simp only [← Category.assoc]
    congr 2
  obtain ⟨f0, hf0⟩ := C.f0.exists_isMap θ rfl hpt
  let κ : 𝓞 c.F →+* X.functionField := (θ.comp (constF e C.Y)).comp (algebraMap (𝓞 c.F) c.F)
  have hκ : (GlobalTheory.CurveRootGeometry.genPt X ≫ b) ≫ Z.s = spMap κ := by
    have e1 : genericPt C.Y ≫ C.Y.str = spMap (algebraMap _ C.Y.Fn) := (GlobalTheory.FlagBundle.ratOf C.Y).pt_s
    have e2 : C.π ≫ genStr Z = C.Y.str ≫ spMap e.symm.toRingHom := by
      rw [← C.π_str, Category.assoc, Category.assoc, ← sp_comp,
        show e.toRingHom.comp e.symm.toRingHom = RingHom.id _ from RingHom.ext fun a => e.apply_symm_apply a]
      exact (congrArg (fun f => C.π ≫ f) ((congrArg (genStr Z ≫ ·) (Spec.map_id _)).trans (Category.comp_id _))).symm
    rw [hpt]
    simp only [Category.assoc]
    rw [hgs, reassoc_of% e2, reassoc_of% e1, ← sp_comp, ← sp_comp, ← sp_comp]
    rfl
  have hsp : GlobalTheory.VB.IsSplitBy fun σ : E →+* ℂ => κ.comp (GlobalTheory.CurveRootGeometry.intEmb c σ) := by
    refine GlobalTheory.VB.isSplitBy_of_injective (fun σ σ' h => ?_) (by rw [NumberField.Embeddings.card, RingOfIntegers.rank])
    refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun y => ?_)
    have := (θ.comp (constF e C.Y)).injective (congrArg (fun f : 𝓞 E →+* X.functionField => f y) h)
    exact congrArg (fun z : c.F => (z : ℂ)) this
  have hP := har.isProjOver
  have hXs := (GlobalTheory.ModelOver.isSeparated_and_noetherian hP).1
  have hZs := (GlobalTheory.ModelOver.isSeparated_and_noetherian Z.proj).1
  refine ⟨X, a, b, hP, hsur, fun τ => ?_⟩
  choose r hr1 hr2 _ hr4 using hL τ
  let ρ : ∀ m : Fin (Dw.mult τ), (L τ m).B.ι → X.functionFieldˣ := fun m i =>
    Units.map Je.symm.toRingHom.toMonoidHom (r m fun _ => i)
  have hρ : ∀ m i, J (ρ m i) = r m fun _ => i := fun m i => Je.apply_symm_apply _
  refine UpperTheory.tangent_sections_line_bundle_units E H Z.X Z.t _ Z.s _ q X V.X hXs b a _ (fun m => (L τ m).B) (f0.v τ) ρ (f0.tan τ)
    (fun cf cf' w h h' => ?_) (fun m i k h => ratSec j a V.j hja J hJ _ (r m) (hr1 m) (ρ m) (hρ m) i k h) fun x hx => ?_
  · have e₁ := (isCombAtG_iff Z.t _ (fun j => ovT (f0.tan τ j)) cf w).1 h
    refine (f0.basis τ w (GlobalTheory.LineNorm.Chart.comb_tan (f0.tan τ) h) fun y => ?_).unique h h'
    have := Z.t.act.hom y
    rw [← e₁]
    exact congrArg (fun q => q.left) (combT_eig _ (fun j => ovT (f0.tan τ j)) (Z.t.act.act y) _
      (fun j => Over.OverMorphism.ext (f0.eig τ j y)) cf)
  choose idx hidx using fun m : Fin (Dw.mult τ) => exists_chart (L τ m).isLB (a x)
  obtain ⟨⟨U₀, hU₀⟩, g, e₀, hx₀, he₀⟩ := GlobalTheory.T.exists_affine_tangent_basis_locally E H Z.X Z.t X b x
  replace hU₀ : IsAffineOpen U₀ := hU₀
  obtain ⟨U, hU, hxU, hle⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ U₀ ⊓ (Finset.univ.inf fun m : Fin (Dw.mult τ) => a ⁻¹ᵁ (L τ m).B.U (idx m)) from ⟨hx₀, by
      simpa using hidx⟩)
  have hle' : U ≤ U₀ ⊓ (Finset.univ.inf fun m : Fin (Dw.mult τ) => a ⁻¹ᵁ (L τ m).B.U (idx m)) := hle
  have hUm : ∀ m : Fin (Dw.mult τ), U ≤ a ⁻¹ᵁ (L τ m).B.U (idx m) := fun m =>
    (hle'.trans inf_le_right).trans (Finset.inf_le (Finset.mem_univ m))
  let r₀ : Γ(X, U₀) →+* Γ(X, U) := resG X (hle'.trans inf_le_left)
  have hr₀ : spMap r₀ ≫ hU₀.fromSpec = hU.fromSpec := hU₀.map_fromSpec hU (homOfLE (hle'.trans inf_le_left)).op
  obtain ⟨eb, he⟩ : ∃ eb : Fin g → (Sp (DualNumber Γ(X, U)) ⟶ Z.t.G.left),
      IsTanBasis Z.t (R := Γ(X, U)) (hU.fromSpec ≫ b) eb := ⟨_, by
    have := GlobalTheory.LineNorm.WedgeMax.isTanBasis_map Z.t r₀ he₀
    rwa [← Category.assoc, hr₀] at this⟩
  have hg : spMap (fnOf U (gen_mem hxU)) ≫ hU.fromSpec ≫ b = GlobalTheory.CurveRootGeometry.genPt X ≫ b := by
    rw [← Category.assoc, gen_eq]
  choose A₀ hA₀ using fun m => (he.2 _ (fnOf U (gen_mem hxU)) (f0.v τ m) (by rw [hg]; exact f0.tan τ m)).exists
  have hxq : ¬ IsUnit (q : X.presheaf.stalk x) := fun hu => by
    have := hu.map (IsLocalRing.residue (X.presheaf.stalk x))
    rw [map_natCast] at this
    exact this.ne_zero hx
  have hmin := minors E H Dw l Xo c _ _ Z hZs F e C V' b hjb hη q Fact.out kind R hk τ U hU (gen_mem hxU)
    (fun m => ρ m (idx m))
    (fun m z hz => by
      have := hr2 m (fun _ => idx m) z (Set.mem_iInter.2 fun _ => by
        have := hUm m hz
        rw [← hja]; exact this)
      rw [pow_one, ← hρ] at this
      exact this)
    (fun m v ε y z yt h1 h2 h3 => by
      have := hr4 m v ε y z (yt ≫ a) (fun _ => idx m) h1 (by rw [← hja]; exact (reassoc_of% h2) a)
        (fun p hp => hUm m (h3 hp))
      rw [pow_one, ← hρ, Nat.cast_one, one_mul] at this
      exact this)
    g eb he A₀ (fun m => by
      have := GlobalTheory.LineNorm.Chart.coord_map _ J (hA₀ m)
      rw [hf0 τ m, GlobalTheory.LineNorm.Chart.dual_comp, hθ] at this
      exact this) x hxU hxq
  obtain ⟨T, hT, hxT, w, hTU, h1, h2⟩ := loc Z.t Z.s (GlobalTheory.CurveRootGeometry.intEmb c) τ b hU hxU κ hκ hsp
    (sep c hd (b ≫ Z.s) κ ((Category.assoc _ _ _).symm.trans hκ) x hx τ) eb he (f0.v τ) (f0.tan τ) (f0.eig τ)
    (fun w h h' => (f0.basis τ w h h').exists) A₀ (fun m => by have := hA₀ m; rwa [hg] at this) _ hmin
  exact ⟨T, hT, hxT, idx, w, fun m => hTU.trans (hUm m), h1, h2⟩

end GlobalTheory.TriFlag.Pf

end Helpers

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mean4 GlobalTheory.Mean4O
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_triangular_frames_good_primes : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ (c : O.s.Comp) (P : Finset ℕ)
    (M : O.LatModel P c) (q : ℕ) [Fact q.Prime], q ∉ P → ¬ q ∣ (discr D.host.E).natAbs →
    ∃ (W : Scheme.{0}) (a : W ⟶ M.V.X) (b : W ⟶ O.s.T.Z.X), IsProjOver (a ≫ M.V.p) ∧ Surjective a ∧
      ∀ τ : D.host.E →+* ℂ, GlobalTheory.TriFlag.TriFrames O.s.T.Z.t O.s.T.Z.s (intEmb O.κ.c τ) q b a (O.S.Dw.mult τ)
        (fun m => (M.line P (.inl (τ, m))).B) := by
  intro _ _ D O _ c P M q _ hqP hd
  refine GlobalTheory.TriFlag.Pf.gen_main O.s.T.Z (O.Φ.C c) (fun _ => O.met.h0 c) M.V q hd (GlobalTheory.ShFam.Pad.ArIn.ind P) none
    (by simp [GlobalTheory.ShFam.Pad.ArIn.ind, hqP]) (fun τ m => M.line P (.inl (τ, m))) fun τ m => ?_
  exact M.line_spec P subset_rfl (.inl (τ, m)) (by simp [GlobalTheory.ShFam.Pad.letterOf])
