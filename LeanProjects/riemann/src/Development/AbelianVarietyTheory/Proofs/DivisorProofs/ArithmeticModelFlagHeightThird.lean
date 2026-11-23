import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberMorphismEqOfLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberLocalMorphismsGlueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalizationCoverOfPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransitionCocycleAtPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransitionMatrixIdentityAtPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentCombinationIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentCombinationUniquenessStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ArLieBase

section Assign

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}

theorem land_comp {K L : Type} [CommRing K] [CommRing L] {X W : Scheme.{0}} {x : Sp K ⟶ W} {jB : W ⟶ X}
    (φ : K →+* L) {z : Sp L ⟶ W} (hz : spMap φ ≫ x = z) {U : X.Opens} (h : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U) :
    ⊤ ≤ (z ≫ jB) ⁻¹ᵁ U := by
  subst hz
  exact fun p _ => h (Set.mem_univ _)

theorem land_inf {K : Type} [CommRing K] {X : Scheme.{0}} {z : Sp K ⟶ X} {A B : X.Opens} (h1 : ⊤ ≤ z ⁻¹ᵁ A)
    (h2 : ⊤ ≤ z ⁻¹ᵁ B) : ⊤ ≤ z ⁻¹ᵁ (A ⊓ B) := fun _ hp => ⟨h1 hp, h2 hp⟩

theorem land_left {K : Type} [CommRing K] {X : Scheme.{0}} {z : Sp K ⟶ X} {A B : X.Opens} (h : ⊤ ≤ z ⁻¹ᵁ (A ⊓ B)) :
    ⊤ ≤ z ⁻¹ᵁ A := fun _ hp => (h hp).1

theorem exists_spMap {L F : Type} [CommRing L] [CommRing F] (g : Sp L ⟶ Sp F) : ∃ ψ : F →+* L, g = spMap ψ :=
  ⟨(Spec.preimage g).hom, (Spec.map_preimage g).symm⟩

theorem dualMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    Formalism.L2.Pj.dualMap (g.comp f) = (Formalism.L2.Pj.dualMap g).comp (Formalism.L2.Pj.dualMap f) := by
  exact RingHom.ext fun x => by ext <;> simp [Formalism.L2.Pj.dualMap]

theorem sp_dual_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (Formalism.L2.Pj.dualMap g) ≫ spMap (Formalism.L2.Pj.dualMap f) = spMap (Formalism.L2.Pj.dualMap (g.comp f)) := by
  rw [dualMap_comp']
  exact (Spec.map_comp _ _).symm

section Comb

variable {X0 : Scheme.{0}} {t : SAB H X0} {K : Type} [CommRing K] {y : Sp K ⟶ X0} {m n : ℕ}
  {v : Fin m → (Sp (DualNumber K) ⟶ t.G.left)}

theorem comb_recomb (hv : ∀ k, IsTanAtG t y (v k)) {w : Fin n → (Sp (DualNumber K) ⟶ t.G.left)}
    (A : Matrix (Fin m) (Fin n) K) (hw : ∀ i, IsCombAtG t y v (fun k => A k i) (w i)) {N : Fin n → K}
    {M' : Fin m → K} (hN : A.mulVec N = M') {t₀ : Sp (DualNumber K) ⟶ t.G.left} (ht : IsCombAtG t y v M' t₀) :
    IsCombAtG t y w N t₀ := by
  have hwt : ∀ i, IsTanAtG t y (w i) := fun i => Guard.comb_tan hv (hw i)
  obtain ⟨t₁, -, h1⟩ := Guard.exists_comb hwt N
  have h2 := Formalism.L2.Pj.tanLinG v hv w A N t₁ hw h1
  rw [hN] at h2
  rwa [Guard.comb_unique hv h2 ht] at h1

theorem comb_local (hv : ∀ k, IsTanAtG t y (v k)) {cf : Fin m → K} {w : Sp (DualNumber K) ⟶ t.G.left} {s : Set K}
    (hs : Ideal.span s = ⊤)
    (h : ∀ a : s, IsCombAtG t (spMap (algebraMap K (Localization.Away (a : K))) ≫ y)
      (fun i => spMap (Formalism.L2.Pj.dualMap (algebraMap K (Localization.Away (a : K)))) ≫ v i)
      (fun i => algebraMap K _ (cf i)) (spMap (Formalism.L2.Pj.dualMap (algebraMap K (Localization.Away (a : K)))) ≫ w)) :
    IsCombAtG t y v cf w := by
  obtain ⟨w', -, hw'⟩ := Guard.exists_comb hv cf
  have e : w = w' := GlobalTheory.T.dual_number_morphism_eq_of_local hs fun a =>
    Guard.comb_unique (fun k => GlobalTheory.FactorDepth.isTanAtG_map t _ (hv k)) (h a) (GlobalTheory.LatDRFree.comb_map t _ hw')
  rwa [e]

end Comb

variable {F : Type} [Field F] {e : F ≃+* c.F} {X W : Scheme.{0}} {jB : W ⟶ X} {πB : W ⟶ gen Z} {r : ℕ}
  {τ : E →+* ℂ}

theorem IsLocFrame.basis' {U : X.Opens} {u : LocAssign Z r jB U} (hu : IsLocFrame Z e jB πB r τ U u) {K : Type}
    [CommRing K] (x : Sp K ⟶ W) (hx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U) : ∃ ψ : F →+* K,
      x ≫ πB ≫ genStr Z ≫ spMap e.toRingHom = spMap ψ ∧
      IsEigBasis Z (ψ.comp e.symm.toRingHom) (x ≫ πB ≫ genι Z) τ (u K x hx) := by
  obtain ⟨ψ, hψ⟩ := exists_spMap (x ≫ πB ≫ genStr Z ≫ spMap e.toRingHom)
  exact ⟨ψ, hψ, hu.1 K x hx ψ hψ⟩

theorem IsLocFrame.tan {U : X.Opens} {u : LocAssign Z r jB U} (hu : IsLocFrame Z e jB πB r τ U u) {K : Type}
    [CommRing K] (x : Sp K ⟶ W) (hx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U) (b : Fin r) :
    IsTanAtG Z.t (x ≫ πB ≫ genι Z) (u K x hx b) := by
  obtain ⟨ψ, -, h⟩ := hu.basis' x hx
  exact (h.1 b).1

theorem IsLocFrame.nat {U : X.Opens} {u : LocAssign Z r jB U} (hu : IsLocFrame Z e jB πB r τ U u) {K L : Type}
    [CommRing K] [CommRing L] (φ : K →+* L) {x : Sp K ⟶ W} {z : Sp L ⟶ W} (hz : spMap φ ≫ x = z)
    (hx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U) (h : ⊤ ≤ (z ≫ jB) ⁻¹ᵁ U) (b : Fin r) :
    u L z h b = spMap (Formalism.L2.Pj.dualMap φ) ≫ u K x hx b := by
  subst hz
  exact hu.2 K L φ x hx h b

omit [NumberField E] [IsCMField E] in

def cf (dual : Bool) {M : X.Modules} {U V : X.Opens} {f : Fin r → Γ(M, U)} (hf : VB.IsFrame f)
    {g : Fin r → Γ(M, V)} (hg : VB.IsFrame g) {K : Type} [CommRing K] (z : Sp K ⟶ X) (h1 : ⊤ ≤ z ⁻¹ᵁ (V ⊓ U))
    (h2 : ⊤ ≤ z ⁻¹ᵁ (U ⊓ V)) (a b : Fin r) : K :=
  cond dual (TangentOrigin.evalPt z _ h2 (trCo hf g a b)) (TangentOrigin.evalPt z _ h1 (trCo hg f b a))

omit [NumberField E] [IsCMField E] in
theorem cf_map (dual : Bool) {M : X.Modules} {U V : X.Opens} {f : Fin r → Γ(M, U)} (hf : VB.IsFrame f)
    {g : Fin r → Γ(M, V)} (hg : VB.IsFrame g) {K L : Type} [CommRing K] [CommRing L] (φ : K →+* L) {z : Sp K ⟶ X}
    {z' : Sp L ⟶ X} (hz : spMap φ ≫ z = z') (h1 : ⊤ ≤ z ⁻¹ᵁ (V ⊓ U)) (h2 : ⊤ ≤ z ⁻¹ᵁ (U ⊓ V))
    (h1' : ⊤ ≤ z' ⁻¹ᵁ (V ⊓ U)) (h2' : ⊤ ≤ z' ⁻¹ᵁ (U ⊓ V)) (a b : Fin r) :
    φ (cf dual hf hg z h1 h2 a b) = cf dual hf hg z' h1' h2' a b := by
  subst hz
  cases dual
  · exact (TangentOrigin.evalPt_spMap_comp φ z _ _ _ _).symm
  · exact (TangentOrigin.evalPt_spMap_comp φ z _ _ _ _).symm

theorem comb_nat {U V : X.Opens} {u : LocAssign Z r jB V} (hu : IsLocFrame Z e jB πB r τ V u) {M : X.Modules}
    {f : Fin r → Γ(M, U)} (hf : VB.IsFrame f) {g : Fin r → Γ(M, V)} (hg : VB.IsFrame g) (dual : Bool) {K L : Type}
    [CommRing K] [CommRing L] (φ : K →+* L) {x : Sp K ⟶ W} {z : Sp L ⟶ W} (hz : spMap φ ≫ x = z)
    (hx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ V) (h1 : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ (V ⊓ U)) (h2 : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ (U ⊓ V))
    (hz0 : ⊤ ≤ (z ≫ jB) ⁻¹ᵁ V) (hz1 : ⊤ ≤ (z ≫ jB) ⁻¹ᵁ (V ⊓ U)) (hz2 : ⊤ ≤ (z ≫ jB) ⁻¹ᵁ (U ⊓ V)) (a : Fin r)
    {w : Sp (DualNumber K) ⟶ Z.t.G.left}
    (h : IsCombAtG Z.t (x ≫ πB ≫ genι Z) (u K x hx) (cf dual hf hg (x ≫ jB) h1 h2 a) w) :
    IsCombAtG Z.t (z ≫ πB ≫ genι Z) (u L z hz0) (cf dual hf hg (z ≫ jB) hz1 hz2 a)
      (spMap (Formalism.L2.Pj.dualMap φ) ≫ w) := by
  have h' := GlobalTheory.LatDRFree.comb_map Z.t φ h
  have e1 : spMap φ ≫ x ≫ πB ≫ genι Z = z ≫ πB ≫ genι Z := by rw [← hz, Category.assoc]
  have e2 : (fun i => spMap (Formalism.L2.Pj.dualMap φ) ≫ u K x hx i) = u L z hz0 :=
    funext fun i => (hu.nat φ hz hx hz0 i).symm
  have e3 : (fun i => φ (cf dual hf hg (x ≫ jB) h1 h2 a i)) = cf dual hf hg (z ≫ jB) hz1 hz2 a :=
    funext fun i => cf_map dual hf hg φ (by rw [← hz, Category.assoc]) h1 h2 hz1 hz2 a i
  rw [e1, e2, e3] at h'
  exact h'

theorem comb_indep {ι : Type} {U : X.Opens} {M : X.Modules} {f : Fin r → Γ(M, U)} (hf : VB.IsFrame f)
    {V : ι → X.Opens} {g : ∀ i, Fin r → Γ(M, V i)} (hg : ∀ i, VB.IsFrame (g i)) {u : ∀ i, LocAssign Z r jB (V i)}
    (hu : ∀ i, IsLocFrame Z e jB πB r τ (V i) (u i)) (dual : Bool)
    (hm : ∀ i j, FramesMatch Z jB πB dual (hg i) (g j) (u i) (u j)) {K : Type} [CommRing K] (z : Sp K ⟶ W)
    (i j : ι) (hi : ⊤ ≤ (z ≫ jB) ⁻¹ᵁ V i) (hj : ⊤ ≤ (z ≫ jB) ⁻¹ᵁ V j) (hi1 : ⊤ ≤ (z ≫ jB) ⁻¹ᵁ (V i ⊓ U))
    (hi2 : ⊤ ≤ (z ≫ jB) ⁻¹ᵁ (U ⊓ V i)) (hj1 : ⊤ ≤ (z ≫ jB) ⁻¹ᵁ (V j ⊓ U)) (hj2 : ⊤ ≤ (z ≫ jB) ⁻¹ᵁ (U ⊓ V j))
    (a : Fin r) {w w' : Sp (DualNumber K) ⟶ Z.t.G.left}
    (h : IsCombAtG Z.t (z ≫ πB ≫ genι Z) (u i K z hi) (cf dual hf (hg i) (z ≫ jB) hi1 hi2 a) w)
    (h' : IsCombAtG Z.t (z ≫ πB ≫ genι Z) (u j K z hj) (cf dual hf (hg j) (z ≫ jB) hj1 hj2 a) w') : w = w' := by
  have tj := (hu j).tan z hj
  cases dual
  · have hA := fun b => hm j i K z hj hi (land_inf hj hi) b
    have h2 := Formalism.L2.Pj.tanLinG _ tj _ (Matrix.of fun c b =>
      TangentOrigin.evalPt (z ≫ jB) _ (land_inf hj hi) (trCo (hg j) (g i) c b)) _ w hA h
    refine Guard.comb_unique tj h2 ?_
    convert h' using 2
    funext c
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, cf, cond]
    exact GlobalTheory.T.transition_cocycle_at_point (hg j) (hg i) f (z ≫ jB) (land_inf hj hi) hi1 hj1 c a
  · have hA := fun b => hm i j K z hi hj (land_inf hi hj) b
    have h2 := Formalism.L2.Pj.tanLinG _ tj _ (Matrix.of fun c b =>
      TangentOrigin.evalPt (z ≫ jB) _ (land_inf hi hj) (trCo (hg i) (g j) b c)) _ w hA h
    refine Guard.comb_unique tj h2 ?_
    convert h' using 2
    funext c
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, cf, cond]
    rw [← GlobalTheory.T.transition_cocycle_at_point hf (hg i) (g j) (z ≫ jB) hi2 (land_inf hi hj) hj2 a c]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _

section Glue

variable {ι : Type} {M : X.Modules} {V : ι → X.Opens} {g : ∀ i, Fin r → Γ(M, V i)} (hg : ∀ i, VB.IsFrame (g i))
  (u : ∀ i, LocAssign Z r jB (V i)) (dual : Bool)

variable (πB) in
omit [NumberField E] [IsCMField E] in

def Cand {U : X.Opens} {f : Fin r → Γ(M, U)} (hf : VB.IsFrame f) {K : Type} [CommRing K] (x : Sp K ⟶ W)
    (w : Fin r → (Sp (DualNumber K) ⟶ Z.t.G.left)) : Prop :=
  ∀ (L : Type) [CommRing L] (φ : K →+* L) (z : Sp L ⟶ W), spMap φ ≫ x = z → ∀ (j : ι) (hj : ⊤ ≤ (z ≫ jB) ⁻¹ᵁ V j)
    (h1 : ⊤ ≤ (z ≫ jB) ⁻¹ᵁ (V j ⊓ U)) (h2 : ⊤ ≤ (z ≫ jB) ⁻¹ᵁ (U ⊓ V j)) (a : Fin r),
    IsCombAtG Z.t (z ≫ πB ≫ genι Z) (u j L z hj) (cf dual hf (hg j) (z ≫ jB) h1 h2 a)
      (spMap (Formalism.L2.Pj.dualMap φ) ≫ w a)

theorem cover_of {K : Type} [CommRing K] (x : Sp K ⟶ W) (hcov : ∀ p : X, ∃ i, p ∈ V i) :
    ∃ s : Set K, Ideal.span s = ⊤ ∧ ∀ a : s, ∃ j,
      ⊤ ≤ ((spMap (algebraMap K (Localization.Away (a : K))) ≫ x) ≫ jB) ⁻¹ᵁ V j := by
  obtain ⟨s, hs, hsj⟩ := GlobalTheory.T.exists_localization_cover_of_point (x ≫ jB) V fun p => by
    obtain ⟨i, hi⟩ := hcov ((x ≫ jB).base p)
    exact ⟨i, hi⟩
  refine ⟨s, hs, fun a => ?_⟩
  obtain ⟨j, hj⟩ := hsj a
  exact ⟨j, by simpa only [Category.assoc] using hj⟩

theorem cand_unique (hu : ∀ i, IsLocFrame Z e jB πB r τ (V i) (u i)) (hcov : ∀ p : X, ∃ i, p ∈ V i) {U : X.Opens}
    {f : Fin r → Γ(M, U)} (hf : VB.IsFrame f) {K : Type} [CommRing K] (x : Sp K ⟶ W) (hx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U)
    {w w' : Fin r → (Sp (DualNumber K) ⟶ Z.t.G.left)} (h : Cand πB hg u dual hf x w) (h' : Cand πB hg u dual hf x w') :
    w = w' := by
  obtain ⟨s, hs, hsj⟩ := cover_of x hcov (jB := jB)
  refine funext fun i => GlobalTheory.T.dual_number_morphism_eq_of_local hs fun a => ?_
  obtain ⟨j, hj⟩ := hsj a
  have hU' := land_comp (algebraMap K (Localization.Away (a : K))) rfl hx
  exact Guard.comb_unique ((hu j).tan _ hj) (h _ _ _ rfl j hj (land_inf hj hU') (land_inf hU' hj) i)
    (h' _ _ _ rfl j hj (land_inf hj hU') (land_inf hU' hj) i)

theorem cand_map {U : X.Opens} {f : Fin r → Γ(M, U)} (hf : VB.IsFrame f) {K K' : Type} [CommRing K] [CommRing K']
    (ψ : K →+* K') (x : Sp K ⟶ W) {w : Fin r → (Sp (DualNumber K) ⟶ Z.t.G.left)} (h : Cand πB hg u dual hf x w) :
    Cand πB hg u dual hf (spMap ψ ≫ x) (fun i => spMap (Formalism.L2.Pj.dualMap ψ) ≫ w i) := by
  intro L _ φ z hz j hj h1 h2 a
  have e : spMap (φ.comp ψ) ≫ x = z := by rw [← hz, ← Category.assoc, Guard.sp_comp]
  have := h L (φ.comp ψ) z e j hj h1 h2 a
  rw [← sp_dual_comp, Category.assoc] at this
  exact this

theorem cand_of_local (hu : ∀ i, IsLocFrame Z e jB πB r τ (V i) (u i))
    (hm : ∀ i j, FramesMatch Z jB πB dual (hg i) (g j) (u i) (u j)) {U : X.Opens}
    {f : Fin r → Γ(M, U)} (hf : VB.IsFrame f) {K : Type} [CommRing K] (x : Sp K ⟶ W) (hx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U)
    {s : Set K} (hs : Ideal.span s = ⊤) (jj : s → ι)
    (hj' : ∀ a : s, ⊤ ≤ ((spMap (algebraMap K (Localization.Away (a : K))) ≫ x) ≫ jB) ⁻¹ᵁ V (jj a))
    (w₀ : Fin r → (Sp (DualNumber K) ⟶ Z.t.G.left))
    (hw : ∀ (a : s) (i : Fin r), IsCombAtG Z.t ((spMap (algebraMap K (Localization.Away (a : K))) ≫ x) ≫ πB ≫ genι Z)
      (u (jj a) _ _ (hj' a)) (cf dual hf (hg (jj a)) _ (land_inf (hj' a) (land_comp _ rfl hx))
        (land_inf (land_comp _ rfl hx) (hj' a)) i)
      (spMap (Formalism.L2.Pj.dualMap (algebraMap K (Localization.Away (a : K)))) ≫ w₀ i)) :
    Cand πB hg u dual hf x w₀ := by
  intro L _ φ z hz j hj h1 h2 i
  obtain ⟨t, -, ht⟩ := Guard.exists_comb ((hu j).tan z hj) (cf dual hf (hg j) (z ≫ jB) h1 h2 i)
  suffices e : spMap (Formalism.L2.Pj.dualMap φ) ≫ w₀ i = t by rw [e]; exact ht
  have hs' : Ideal.span (φ '' s) = ⊤ := by rw [← Ideal.map_span, hs, Ideal.map_top]
  refine GlobalTheory.T.dual_number_morphism_eq_of_local hs' fun b => ?_
  obtain ⟨a0, ha0, hab⟩ := b.2
  let a : s := ⟨a0, ha0⟩
  have hunit : IsUnit (((algebraMap L (Localization.Away (b : L))).comp φ) (a : K)) := by
    rw [RingHom.comp_apply, show (a : K) = a0 from rfl, hab]
    exact IsLocalization.Away.algebraMap_isUnit _
  let ψ : Localization.Away (a : K) →+* Localization.Away (b : L) := IsLocalization.Away.lift (a : K) hunit
  have hψ : ψ.comp (algebraMap K (Localization.Away (a : K))) = (algebraMap L (Localization.Away (b : L))).comp φ :=
    IsLocalization.Away.lift_comp (a : K) hunit
  have e1 : spMap (algebraMap L (Localization.Away (b : L))) ≫ z =
      spMap ((algebraMap L (Localization.Away (b : L))).comp φ) ≫ x := by
    rw [← hz, ← Category.assoc, Guard.sp_comp]
  have e2 : spMap ψ ≫ (spMap (algebraMap K (Localization.Away (a : K))) ≫ x) =
      spMap ((algebraMap L (Localization.Away (b : L))).comp φ) ≫ x := by
    rw [← Category.assoc, Guard.sp_comp, hψ]
  have hz'U := land_comp _ e2 (land_comp (algebraMap K (Localization.Away (a : K))) rfl hx)
  have hz'a := land_comp _ e2 (hj' a)
  have hz'j := land_comp _ e1 hj
  have eL : spMap (Formalism.L2.Pj.dualMap (algebraMap L (Localization.Away (b : L)))) ≫
      spMap (Formalism.L2.Pj.dualMap φ) ≫ w₀ i = spMap (Formalism.L2.Pj.dualMap ψ) ≫
        spMap (Formalism.L2.Pj.dualMap (algebraMap K (Localization.Away (a : K)))) ≫ w₀ i := by
    rw [← Category.assoc, ← Category.assoc, sp_dual_comp, sp_dual_comp, hψ]
  rw [eL]
  exact comb_indep hf hg hu dual hm _ (jj a) j hz'a hz'j (land_inf hz'a hz'U) (land_inf hz'U hz'a)
    (land_inf hz'j hz'U) (land_inf hz'U hz'j) i
    (comb_nat (hu _) hf (hg _) dual ψ e2 (hj' _) _ _ hz'a _ _ i (hw a i))
    (comb_nat (hu j) hf (hg j) dual _ e1 hj h1 h2 hz'j _ _ i ht)

theorem cand_exists (hu : ∀ i, IsLocFrame Z e jB πB r τ (V i) (u i))
    (hm : ∀ i j, FramesMatch Z jB πB dual (hg i) (g j) (u i) (u j)) (hcov : ∀ p : X, ∃ i, p ∈ V i) {U : X.Opens}
    {f : Fin r → Γ(M, U)} (hf : VB.IsFrame f) {K : Type} [CommRing K] (x : Sp K ⟶ W) (hx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U) :
    ∃ w, Cand πB hg u dual hf x w := by
  obtain ⟨s, hs, hsj⟩ := cover_of x hcov (jB := jB)
  choose jj hj' using hsj
  have hU' : ∀ a : s, ⊤ ≤ ((spMap (algebraMap K (Localization.Away (a : K))) ≫ x) ≫ jB) ⁻¹ᵁ U := fun a =>
    land_comp _ rfl hx
  have hex : ∀ (a : s) (i : Fin r), ∃ w, IsCombAtG Z.t ((spMap (algebraMap K (Localization.Away (a : K))) ≫ x) ≫ πB ≫
      genι Z) (u (jj a) _ _ (hj' a)) (cf dual hf (hg (jj a)) _ (land_inf (hj' a) (hU' a)) (land_inf (hU' a) (hj' a)) i)
      w := fun a i => (Guard.exists_comb ((hu (jj a)).tan _ (hj' a)) _).imp fun _ h => h.2
  choose wl hwl using hex
  have hglue : ∀ i : Fin r, ∃ w₀ : Sp (DualNumber K) ⟶ Z.t.G.left, ∀ a : s,
      spMap (Formalism.L2.Pj.dualMap (algebraMap K (Localization.Away (a : K)))) ≫ w₀ = wl a i := by
    intro i
    refine GlobalTheory.T.dual_number_local_morphisms_glue hs (fun a => wl a i) fun a b => ?_
    have ea : spMap (IsLocalization.Away.awayToAwayRight (S := Localization.Away (a : K))
        (P := Localization.Away ((a : K) * b)) (a : K) (b : K)) ≫ (spMap (algebraMap K (Localization.Away (a : K))) ≫ x) =
        spMap (algebraMap K (Localization.Away ((a : K) * b))) ≫ x := by
      rw [← Category.assoc, Guard.sp_comp]
      congr 2
      exact RingHom.ext fun q => IsLocalization.Away.awayToAwayRight_eq (a : K) (b : K) q
    have eb : spMap (IsLocalization.Away.awayToAwayLeft (S := Localization.Away (b : K))
        (P := Localization.Away ((a : K) * b)) (b : K) (a : K)) ≫ (spMap (algebraMap K (Localization.Away (b : K))) ≫ x) =
        spMap (algebraMap K (Localization.Away ((a : K) * b))) ≫ x := by
      rw [← Category.assoc, Guard.sp_comp]
      congr 2
      exact RingHom.ext fun q => IsLocalization.Away.awayToAwayLeft_eq (b : K) (a : K) q
    have hzU := land_comp _ ea (hU' a)
    have hza := land_comp _ ea (hj' a)
    have hzb := land_comp _ eb (hj' b)
    exact comb_indep hf hg hu dual hm _ (jj a) (jj b) hza hzb (land_inf hza hzU) (land_inf hzU hza)
      (land_inf hzb hzU) (land_inf hzU hzb) i
      (comb_nat (hu (jj a)) hf (hg (jj a)) dual _ ea (hj' a) _ _ hza _ _ i (hwl a i))
      (comb_nat (hu (jj b)) hf (hg (jj b)) dual _ eb (hj' b) _ _ hzb _ _ i (hwl b i))
  choose w₀ hw₀ using hglue
  exact ⟨w₀, cand_of_local hg u dual hu hm hf x hx hs jj hj' w₀ fun a i => by rw [hw₀ i a]; exact hwl a i⟩

end Glue

theorem evalPt_alg {K L : Type} [CommRing K] [CommRing L] (φ : K →+* L) (x : Sp K ⟶ W) (V' : X.Opens)
    (h : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ V') (h' : ⊤ ≤ ((spMap φ ≫ x) ≫ jB) ⁻¹ᵁ V') (q : Γ(X, V')) :
    TangentOrigin.evalPt ((spMap φ ≫ x) ≫ jB) V' h' q = φ (TangentOrigin.evalPt (x ≫ jB) V' h q) := by
  have e0 : (spMap φ ≫ x) ≫ jB = spMap φ ≫ (x ≫ jB) := Category.assoc _ _ _
  revert h'
  rw [e0]
  intro h'
  exact TangentOrigin.evalPt_spMap_comp φ (x ≫ jB) V' h h' q

theorem away_right_eq {K : Type} [CommRing K] (x : Sp K ⟶ W) (a b : K) :
    spMap (IsLocalization.Away.awayToAwayRight (S := Localization.Away a) (P := Localization.Away (a * b)) a b) ≫
      (spMap (algebraMap K (Localization.Away a)) ≫ x) = spMap (algebraMap K (Localization.Away (a * b))) ≫ x := by
  rw [← Category.assoc, Guard.sp_comp]
  congr 2
  exact RingHom.ext fun q => IsLocalization.Away.awayToAwayRight_eq a b q

omit [NumberField E] [IsCMField E] in
theorem cf_inv (dual : Bool) {M : X.Modules} {U V : X.Opens} {f : Fin r → Γ(M, U)} (hf : VB.IsFrame f)
    {g : Fin r → Γ(M, V)} (hg : VB.IsFrame g) {K : Type} [CommRing K] (z : Sp K ⟶ X) (h1 : ⊤ ≤ z ⁻¹ᵁ (V ⊓ U))
    (h2 : ⊤ ≤ z ⁻¹ᵁ (U ⊓ V)) :
    (Matrix.of fun b a => cf (!dual) hf hg z h1 h2 a b) * (Matrix.of fun a b => cf dual hf hg z h1 h2 a b) = 1 := by
  ext b c
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.of_apply]
  cases dual
  · simp only [Bool.not_false, cf, cond]
    have := GlobalTheory.T.transition_cocycle_at_point hg hf g z h1 h2 (land_inf (land_left h1) (land_left h1)) c b
    rw [GlobalTheory.T.transition_matrix_identity_at_point hg z _ c b] at this
    exact (Finset.sum_congr rfl fun a _ => mul_comm _ _).trans (this.trans (if_congr eq_comm rfl rfl))
  · simp only [Bool.not_true, cf, cond]
    rw [GlobalTheory.T.transition_cocycle_at_point hg hf g z h1 h2 (land_inf (land_left h1) (land_left h1)) b c, GlobalTheory.T.transition_matrix_identity_at_point hg z _ b c]

section Basis

variable {ι : Type} {M : X.Modules} {V : ι → X.Opens} {g : ∀ i, Fin r → Γ(M, V i)} (hg : ∀ i, VB.IsFrame (g i))
  (u : ∀ i, LocAssign Z r jB (V i)) (dual : Bool)

theorem cand_basis (hu : ∀ i, IsLocFrame Z e jB πB r τ (V i) (u i)) {U : X.Opens} {f : Fin r → Γ(M, U)}
    (hf : VB.IsFrame f) {K : Type} [CommRing K] {x : Sp K ⟶ W} {w : Fin r → (Sp (DualNumber K) ⟶ Z.t.G.left)}
    (hw : Cand πB hg u dual hf x w) {L : Type} [CommRing L] (φ : K →+* L) (ψ : F →+* K)
    (hψ : x ≫ πB ≫ genStr Z ≫ spMap e.toRingHom = spMap ψ) (j : ι) (hj : ⊤ ≤ ((spMap φ ≫ x) ≫ jB) ⁻¹ᵁ V j)
    (hU : ⊤ ≤ ((spMap φ ≫ x) ≫ jB) ⁻¹ᵁ U) :
    IsEigBasis Z (φ.comp (ψ.comp e.symm.toRingHom)) (spMap φ ≫ x ≫ πB ≫ genι Z) τ
      (fun i => spMap (Formalism.L2.Pj.dualMap φ) ≫ w i) := by
  have hb := (hu j).1 L (spMap φ ≫ x) hj (φ.comp ψ) (by rw [Category.assoc, hψ, Guard.sp_comp])
  have e0 : (spMap φ ≫ x) ≫ πB ≫ genι Z = spMap φ ≫ x ≫ πB ≫ genι Z := Category.assoc _ _ _
  rw [e0] at hb
  have hc : ∀ a, IsCombAtG Z.t (spMap φ ≫ x ≫ πB ≫ genι Z) (u j L (spMap φ ≫ x) hj)
      (fun b => (Matrix.of fun a b => cf dual hf (hg j) _ (land_inf hj hU) (land_inf hU hj) a b) a b)
      (spMap (Formalism.L2.Pj.dualMap φ) ≫ w a) := fun a => by
    have := hw L φ _ rfl j hj (land_inf hj hU) (land_inf hU hj) a
    rw [e0] at this
    exact this
  exact GlobalTheory.T.tangent_combination_identity Z _ _ τ _ _ _ _ hb hc (cf_inv dual hf (hg j) _ _ _)

theorem cand_isEigBasis (hu : ∀ i, IsLocFrame Z e jB πB r τ (V i) (u i)) (hcov : ∀ p : X, ∃ i, p ∈ V i)
    {U : X.Opens} {f : Fin r → Γ(M, U)} (hf : VB.IsFrame f) {K : Type} [CommRing K] (x : Sp K ⟶ W)
    (hx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U) {w : Fin r → (Sp (DualNumber K) ⟶ Z.t.G.left)} (hw : Cand πB hg u dual hf x w)
    (ψ : F →+* K) (hψ : x ≫ πB ≫ genStr Z ≫ spMap e.toRingHom = spMap ψ) :
    IsEigBasis Z (ψ.comp e.symm.toRingHom) (x ≫ πB ≫ genι Z) τ w := by
  obtain ⟨s, hs, hsj⟩ := cover_of x hcov (jB := jB)
  choose jj hj' using hsj
  refine GlobalTheory.T.tangent_combination_uniqueness Z _ _ τ w hs (fun a => ?_) (fun a b => ?_)
  · exact cand_basis hg u dual hu hf hw _ ψ hψ (jj a) (hj' a) (land_comp _ rfl hx)
  · exact cand_basis hg u dual hu hf hw _ ψ hψ (jj a) (land_comp _ (away_right_eq x (a : K) b) (hj' a))
      (land_comp _ rfl hx)

end Basis

section Final

variable {ι : Type} {M : X.Modules} {V : ι → X.Opens} {g : ∀ i, Fin r → Γ(M, V i)} (hg : ∀ i, VB.IsFrame (g i))
  (u : ∀ i, LocAssign Z r jB (V i)) (dual : Bool)

theorem cand_trans (hu : ∀ i, IsLocFrame Z e jB πB r τ (V i) (u i)) (hcov : ∀ p : X, ∃ i, p ∈ V i)
    {U U' : X.Opens} {f : Fin r → Γ(M, U)} {f' : Fin r → Γ(M, U')} (hf : VB.IsFrame f) (hf' : VB.IsFrame f')
    {K : Type} [CommRing K] (x : Sp K ⟶ W) (hx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U) (hx' : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U')
    (hxx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ (U ⊓ U')) {w w' : Fin r → (Sp (DualNumber K) ⟶ Z.t.G.left)}
    (hw : Cand πB hg u dual hf x w) (hw' : Cand πB hg u dual hf' x w')
    (htw : ∀ k, IsTanAtG Z.t (x ≫ πB ≫ genι Z) (w k)) (htw' : ∀ k, IsTanAtG Z.t (x ≫ πB ≫ genι Z) (w' k))
    (i : Fin r) :
    cond dual
      (IsCombAtG Z.t (x ≫ πB ≫ genι Z) w'
        (fun a => TangentOrigin.evalPt (x ≫ jB) (U ⊓ U') hxx (trCo hf f' i a)) (w i))
      (IsCombAtG Z.t (x ≫ πB ≫ genι Z) w
        (fun b => TangentOrigin.evalPt (x ≫ jB) (U ⊓ U') hxx (trCo hf f' b i)) (w' i)) := by
  obtain ⟨s, hs, hsj⟩ := cover_of x hcov (jB := jB)
  choose jj hj' using hsj
  cases dual
  · refine comb_local htw hs fun a => ?_
    have hU := land_comp (algebraMap K (Localization.Away (a : K))) rfl hx
    have hU' := land_comp (algebraMap K (Localization.Away (a : K))) rfl hx'
    have hUU := land_comp (algebraMap K (Localization.Away (a : K))) rfl hxx
    have e0 : (spMap (algebraMap K (Localization.Away (a : K))) ≫ x) ≫ πB ≫ genι Z =
        spMap (algebraMap K (Localization.Away (a : K))) ≫ x ≫ πB ≫ genι Z := Category.assoc _ _ _
    have h1 : ∀ k, IsCombAtG Z.t (spMap (algebraMap K (Localization.Away (a : K))) ≫ x ≫ πB ≫ genι Z)
        (u (jj a) _ _ (hj' a)) (cf false hf (hg (jj a)) _ (land_inf (hj' a) hU) (land_inf hU (hj' a)) k)
        (spMap (Formalism.L2.Pj.dualMap (algebraMap K (Localization.Away (a : K)))) ≫ w k) := fun k => by
      have := hw _ (algebraMap K (Localization.Away (a : K))) _ rfl (jj a) (hj' a) (land_inf (hj' a) hU)
        (land_inf hU (hj' a)) k
      rw [e0] at this
      exact this
    have h2 : IsCombAtG Z.t (spMap (algebraMap K (Localization.Away (a : K))) ≫ x ≫ πB ≫ genι Z)
        (u (jj a) _ _ (hj' a)) (cf false hf' (hg (jj a)) _ (land_inf (hj' a) hU') (land_inf hU' (hj' a)) i)
        (spMap (Formalism.L2.Pj.dualMap (algebraMap K (Localization.Away (a : K)))) ≫ w' i) := by
      have := hw' _ (algebraMap K (Localization.Away (a : K))) _ rfl (jj a) (hj' a) (land_inf (hj' a) hU')
        (land_inf hU' (hj' a)) i
      rw [e0] at this
      exact this
    have hv := fun k => (hu (jj a)).tan _ (hj' a) k
    rw [e0] at hv
    refine comb_recomb hv (Matrix.of fun b k => cf false hf (hg (jj a)) _ (land_inf (hj' a) hU)
      (land_inf hU (hj' a)) k b) h1 ?_ h2
    funext b
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, cf, cond]
    rw [← GlobalTheory.T.transition_cocycle_at_point (hg (jj a)) hf f' _ (land_inf (hj' a) hU) hUU (land_inf (hj' a) hU') b i]
    exact Finset.sum_congr rfl fun k _ => by rw [evalPt_alg _ x _ hxx hUU]
  · refine comb_local htw' hs fun a => ?_
    have hU := land_comp (algebraMap K (Localization.Away (a : K))) rfl hx
    have hU' := land_comp (algebraMap K (Localization.Away (a : K))) rfl hx'
    have hUU := land_comp (algebraMap K (Localization.Away (a : K))) rfl hxx
    have e0 : (spMap (algebraMap K (Localization.Away (a : K))) ≫ x) ≫ πB ≫ genι Z =
        spMap (algebraMap K (Localization.Away (a : K))) ≫ x ≫ πB ≫ genι Z := Category.assoc _ _ _
    have h1 : ∀ k, IsCombAtG Z.t (spMap (algebraMap K (Localization.Away (a : K))) ≫ x ≫ πB ≫ genι Z)
        (u (jj a) _ _ (hj' a)) (cf true hf' (hg (jj a)) _ (land_inf (hj' a) hU') (land_inf hU' (hj' a)) k)
        (spMap (Formalism.L2.Pj.dualMap (algebraMap K (Localization.Away (a : K)))) ≫ w' k) := fun k => by
      have := hw' _ (algebraMap K (Localization.Away (a : K))) _ rfl (jj a) (hj' a) (land_inf (hj' a) hU')
        (land_inf hU' (hj' a)) k
      rw [e0] at this
      exact this
    have h2 : IsCombAtG Z.t (spMap (algebraMap K (Localization.Away (a : K))) ≫ x ≫ πB ≫ genι Z)
        (u (jj a) _ _ (hj' a)) (cf true hf (hg (jj a)) _ (land_inf (hj' a) hU) (land_inf hU (hj' a)) i)
        (spMap (Formalism.L2.Pj.dualMap (algebraMap K (Localization.Away (a : K)))) ≫ w i) := by
      have := hw _ (algebraMap K (Localization.Away (a : K))) _ rfl (jj a) (hj' a) (land_inf (hj' a) hU)
        (land_inf hU (hj' a)) i
      rw [e0] at this
      exact this
    have hv := fun k => (hu (jj a)).tan _ (hj' a) k
    rw [e0] at hv
    refine comb_recomb hv (Matrix.of fun b k => cf true hf' (hg (jj a)) _ (land_inf (hj' a) hU')
      (land_inf hU' (hj' a)) k b) h1 ?_ h2
    funext b
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, cf, cond]
    rw [← GlobalTheory.T.transition_cocycle_at_point hf hf' (g (jj a)) _ hUU (land_inf hU' (hj' a)) (land_inf hU (hj' a)) i b]
    exact Finset.sum_congr rfl fun k _ => by rw [evalPt_alg _ x _ hxx hUU, mul_comm]

def uuOf (hu : ∀ i, IsLocFrame Z e jB πB r τ (V i) (u i))
    (hm : ∀ i j, FramesMatch Z jB πB dual (hg i) (g j) (u i) (u j)) (hcov : ∀ p : X, ∃ i, p ∈ V i) :
    FrAssign Z M r jB :=
  fun _ _ hf _ _ x hx => Classical.choose (cand_exists hg u dual hu hm hcov hf x hx)

theorem exists_lieFrames (hu : ∀ i, IsLocFrame Z e jB πB r τ (V i) (u i))
    (hm : ∀ i j, FramesMatch Z jB πB dual (hg i) (g j) (u i) (u j)) (hcov : ∀ p : X, ∃ i, p ∈ V i) :
    ∃ uu : FrAssign Z M r jB, IsLieFrames Z e jB πB M r τ dual uu ∧ ∀ i, uu (V i) (g i) (hg i) = u i := by
  have huu : ∀ (U : X.Opens) (f : Fin r → Γ(M, U)) (hf : VB.IsFrame f) (K : Type) [CommRing K] (x : Sp K ⟶ W)
      (hx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U), Cand πB hg u dual hf x (uuOf hg u dual hu hm hcov U f hf K x hx) := by
    intro U f hf K _ x hx
    exact Classical.choose_spec (cand_exists hg u dual hu hm hcov hf x hx)
  have htan : ∀ (U : X.Opens) (f : Fin r → Γ(M, U)) (hf : VB.IsFrame f) (K : Type) [CommRing K] (x : Sp K ⟶ W)
      (hx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U) (k : Fin r),
      IsTanAtG Z.t (x ≫ πB ≫ genι Z) (uuOf hg u dual hu hm hcov U f hf K x hx k) := by
    intro U f hf K _ x hx k
    obtain ⟨ψ, hψ⟩ := exists_spMap (x ≫ πB ≫ genStr Z ≫ spMap e.toRingHom)
    exact ((cand_isEigBasis hg u dual hu hcov hf x hx (huu U f hf K x hx) ψ hψ).1 k).1
  refine ⟨uuOf hg u dual hu hm hcov, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro U f hf K _ x hx ψ hψ
    exact cand_isEigBasis hg u dual hu hcov hf x hx (huu U f hf K x hx) ψ hψ
  · intro U U' f f' hf hf' K _ x hx hx' hxx i
    exact cand_trans hg u dual hu hcov hf hf' x hx hx' hxx (huu U f hf K x hx) (huu U' f' hf' K x hx')
      (htan U f hf K x hx) (htan U' f' hf' K x hx') i
  · intro U f hf K K' _ _ ψ x hx hx' i
    exact congrFun (cand_unique hg u dual hu hcov hf (spMap ψ ≫ x) hx' (huu U f hf K' (spMap ψ ≫ x) hx')
      (cand_map hg u dual hf ψ x (huu U f hf K x hx))) i
  · intro i
    funext K _ x hx
    refine cand_unique hg u dual hu hcov (hg i) x hx (huu _ _ (hg i) K x hx) ?_
    intro L _ φ z hz j hj h1 h2 a
    have hzi : ⊤ ≤ (z ≫ jB) ⁻¹ᵁ V i := land_comp φ hz hx
    rw [← (hu i).nat φ hz hx hzi a]
    cases dual
    · exact hm j i L z hj hzi (land_inf hj hzi) a
    · exact hm i j L z hzi hj (land_inf hzi hj) a

end Final

end Assign

theorem exists_lieFrames_of_locFrames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (Oz : Type) [CommRing Oz] (β : Oz →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (X W : Scheme.{0}) (jB : W ⟶ X) (πB : W ⟶ gen Z) (M : X.Modules) (r : ℕ) (τ : E →+* ℂ) (dual : Bool) (ι : Type) (U : ι → X.Opens) (f : ∀ i, Fin r → Γ(M, U i)) (hf : ∀ i, VB.IsFrame (f i)) (u : ∀ i, LocAssign Z r jB (U i)), (∀ x : X, ∃ i, x ∈ U i) → (∀ i, IsLocFrame Z e jB πB r τ (U i) (u i)) → (∀ i j, FramesMatch Z jB πB dual (hf i) (f j) (u i) (u j)) → ∃ uu : FrAssign Z M r jB, IsLieFrames Z e jB πB M r τ dual uu ∧ ∀ i, uu (U i) (f i) (hf i) = u i := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z F _ _ e X W jB πB M r τ dual ι U f hf u hcov hloc hmatch
  exact exists_lieFrames hf u dual hloc hmatch hcov

end GlobalTheory.ArLieBase
