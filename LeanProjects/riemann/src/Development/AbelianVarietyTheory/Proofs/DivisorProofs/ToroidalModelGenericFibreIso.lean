import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCoordMat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwoLat.OfCharts

theorem repr_app {X : Scheme.{0}} {M M' : X.Modules} {r : ℕ} (g : M ⟶ M') {U V : X.Opens}
    (f : Fin r → Γ(M, U)) {f' : Fin r → Γ(M', U)} (hf' : VB.IsFrame f') {p : Fin r → Γ(M, V)} (hp : VB.IsFrame p)
    (p' : Fin r → Γ(M', V)) (A : Matrix (Fin r) (Fin r) Γ(X, V)) (hg : ∀ a, g.app V (p a) = ∑ b, A b a • p' b)
    (i k : Fin r) :
    resG X (inf_le_left : U ⊓ V ≤ U) ((hf'.basis le_rfl).repr (Twist.resM M' le_rfl (g.app U (f i))) k) =
      ∑ a, ∑ b, resG X (le_inf inf_le_right inf_le_left : U ⊓ V ≤ V ⊓ U) (trCo hp f a i) *
        (resG X (inf_le_right : U ⊓ V ≤ V) (A b a) * trCo hf' p' k b) := by
  have h1 : Twist.resM M (inf_le_left : U ⊓ V ≤ U) (f i) =
      ∑ a, resG X (le_inf inf_le_right inf_le_left : U ⊓ V ≤ V ⊓ U) (trCo hp f a i) •
        Twist.resM M (inf_le_right : U ⊓ V ≤ V) (p a) := by
    have h := (hp.basis (inf_le_right : U ⊓ V ≤ V)).sum_repr (Twist.resM M (inf_le_left : U ⊓ V ≤ U) (f i))
    refine h.symm.trans (Finset.sum_congr rfl fun a _ => ?_)
    rw [hp.basis_apply, trCo, ← hp.repr_resM, Twist.resM_resM]
  have h2 : ∀ a, QCoh.appLinear g (U ⊓ V) (Twist.resM M (inf_le_right : U ⊓ V ≤ V) (p a)) =
      ∑ b, resG X (inf_le_right : U ⊓ V ≤ V) (A b a) • Twist.resM M' (inf_le_right : U ⊓ V ≤ V) (p' b) := fun a => by
    rw [QCoh.appLinear_apply, Twist.app_resM, hg, map_sum]
    simp only [Twist.resM_smul]
  have h3 : Twist.resM M' (inf_le_left : U ⊓ V ≤ U) (g.app U (f i)) =
      QCoh.appLinear g (U ⊓ V) (Twist.resM M (inf_le_left : U ⊓ V ≤ U) (f i)) := by
    rw [QCoh.appLinear_apply, Twist.app_resM]
  rw [← hf'.repr_resM, Twist.resM_resM, h3, h1]
  simp only [map_sum, map_smul, h2, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul, Finset.mul_sum, trCo]

theorem sum_smul_three {K N : Type} [CommRing K] {_ : AddCommMonoid N} {_ : Module K N} {r : ℕ} {P : Fin r → K}
    {A Q : Fin r → Fin r → K} {u u' v : Fin r → N} {w : N} (e1 : w = ∑ a, P a • u a)
    (e2 : ∀ a, u a = ∑ b, A a b • u' b) (e3 : ∀ b, u' b = ∑ k, Q b k • v k) :
    w = ∑ k, (∑ a, ∑ b, P a * (A a b * Q b k)) • v k := by
  rw [e1, funext e2, funext e3]
  simp only [Finset.smul_sum, Finset.sum_smul, smul_smul]
  symm
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_comm

section Tangent

open MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

theorem comb_three {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {T : Scheme.{0}} {t : SAB H T} {K : Type} [CommRing K] {x : Sp K ⟶ T} {r : ℕ}
    {u u' v : Fin r → (Sp (DualNumber K) ⟶ t.G.left)} {w : Sp (DualNumber K) ⟶ t.G.left}
    (hu : ∀ i, IsTanAtG t x (u i)) (hu' : ∀ i, IsTanAtG t x (u' i)) (hv : ∀ i, IsTanAtG t x (v i))
    (hw : IsTanAtG t x w) {P : Fin r → K} {A Q : Fin r → Fin r → K} (h1 : IsCombAtG t x u P w)
    (h2 : ∀ a, IsCombAtG t x u' (A a) (u a)) (h3 : ∀ b, IsCombAtG t x v (Q b) (u' b)) :
    IsCombAtG t x v (fun k => ∑ a, ∑ b, P a * (A a b * Q b k)) w := by
  have e1 := (GradedPieces.comb_iff hu _ hw).1 h1
  have e2 := fun a => (GradedPieces.comb_iff hu' _ (hu a)).1 (h2 a)
  have e3 := fun b => (GradedPieces.comb_iff hv _ (hu' b)).1 (h3 b)
  exact (GradedPieces.comb_iff hv _ hw).2 (sum_smul_three e1 e2 e3)

end Tangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F}
  {X W : Scheme.{0}} {jB : W ⟶ X} {πB : W ⟶ gen Z} {M M' : X.Modules} {r : ℕ} {τ : E →+* ℂ}
  {t : FrAssign Z M r jB} {t' : FrAssign Z M' r jB}

variable (e πB) in

theorem exists_over {K : Type} [CommRing K] (y : Sp K ⟶ W) :
    ∃ ψ : F →+* K, y ≫ πB ≫ genStr Z ≫ spMap e.toRingHom = spMap ψ :=
  ⟨(Spec.preimage (y ≫ πB ≫ genStr Z ≫ spMap e.toRingHom)).hom, (Spec.map_preimage _).symm⟩

theorem comb_of_chart (h : IsLieFrames Z e jB πB M r τ false t) (h' : IsLieFrames Z e jB πB M' r τ false t')
    {V : X.Opens} {p : Fin r → Γ(M, V)} (hp : VB.IsFrame p) {p' : Fin r → Γ(M', V)} (hp' : VB.IsFrame p')
    {A : Matrix (Fin r) (Fin r) Γ(X, V)} (hA : IsCoordMat Z jB πB t t' hp hp' A) {g : M ⟶ M'}
    (hg : ∀ a, g.app V (p a) = ∑ b, A b a • p' b) {U : X.Opens} {f : Fin r → Γ(M, U)} {f' : Fin r → Γ(M', U)}
    (hf : VB.IsFrame f) (hf' : VB.IsFrame f') {K : Type} [CommRing K] (x : Sp K ⟶ W) (hx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U)
    (hV : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ V) (i : Fin r) :
    IsCombAtG Z.t (x ≫ πB ≫ genι Z) (t' U f' hf' K x hx)
      (fun b => TangentOrigin.evalPt (x ≫ jB) U hx ((hf'.basis le_rfl).repr (Twist.resM M' le_rfl (g.app U (f i))) b))
      (t U f hf K x hx i) := by
  obtain ⟨ψ, hψ⟩ := exists_over e πB x
  have hUV : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ (U ⊓ V) := fun z hz => ⟨hx hz, hV hz⟩
  have hVU : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ (V ⊓ U) := fun z hz => ⟨hV hz, hx hz⟩
  have tf := fun a => ((h.1 U f hf K x hx ψ hψ).1 a).1
  have tp := fun a => ((h.1 V p hp K x hV ψ hψ).1 a).1
  have tf' := fun a => ((h'.1 U f' hf' K x hx ψ hψ).1 a).1
  have tp' := fun a => ((h'.1 V p' hp' K x hV ψ hψ).1 a).1
  have e1 := comb_three tp tp' tf' (tf i) (h.2.1 V U p f hp hf K x hV hx hVU i) (hA K x hV)
    (h'.2.1 U V f' p' hf' hp' K x hx hV hUV)
  have e4 : ∀ k, TangentOrigin.evalPt (x ≫ jB) U hx
      ((hf'.basis le_rfl).repr (Twist.resM M' le_rfl (g.app U (f i))) k) =
      ∑ a, ∑ b, TangentOrigin.evalPt (x ≫ jB) (V ⊓ U) hVU (trCo hp f a i) *
        (TangentOrigin.evalPt (x ≫ jB) V hV (A b a) * TangentOrigin.evalPt (x ≫ jB) (U ⊓ V) hUV (trCo hf' p' k b)) := by
    intro k
    rw [← TangentOrigin.evalPt_res _ inf_le_left hx hUV, repr_app g f hf' hp p' A hg]
    simp only [map_sum, map_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [TangentOrigin.evalPt_res _ _ hVU hUV, TangentOrigin.evalPt_res _ _ hV hUV]
  rw [funext e4]
  exact e1

end GlobalTheory.TwoLat.OfCharts

namespace GlobalTheory.TwoLat

theorem matches_of_charts : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
    {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {F : Type} [Field F] [NumberField F] (e : F ≃+* c.F)
    {X W : Scheme.{0}} {jB : W ⟶ X} {πB : W ⟶ gen Z},
    ∀ (M M' : X.Modules) (r : ℕ) (τ : E →+* ℂ) (t : FrAssign Z M r jB) (t' : FrAssign Z M' r jB),
    IsLieFrames Z e jB πB M r τ false t → IsLieFrames Z e jB πB M' r τ false t' →
    ∀ (ι : Type) (U : ι → X.Opens), (∀ x : X, ∃ i, x ∈ U i) → ∀ (f : ∀ i, Fin r → Γ(M, U i))
    (hf : ∀ i, VB.IsFrame (f i)) (f' : ∀ i, Fin r → Γ(M', U i)) (hf' : ∀ i, VB.IsFrame (f' i))
    (A : ∀ i, Matrix (Fin r) (Fin r) Γ(X, U i)), (∀ i, GlobalTheory.TwoLat.IsCoordMat Z jB πB t t' (hf i) (hf' i) (A i)) →
    ∀ g : M ⟶ M', (∀ i a, g.app (U i) (f i a) = ∑ b, A i b a • f' i b) → GlobalTheory.TwoLat.Matches Z jB πB g t t' := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z F _ _ e X W jB πB M M' r τ t t' h h' ι V hV p hp p' hp' A hA g hg
    U f f' hf hf' K _ x hx i
  obtain ⟨ψ, hψ⟩ := OfCharts.exists_over e πB x
  obtain ⟨a, ha, -⟩ := (h'.1 U f' hf' K x hx ψ hψ).2 _ ((h.1 U f hf K x hx ψ hψ).1 i)
  suffices hs : (fun b => TangentOrigin.evalPt (x ≫ jB) U hx
      ((hf'.basis le_rfl).repr (Twist.resM M' le_rfl (g.app U (f i))) b)) = a by
    rw [hs]; exact ha
  funext b
  refine Module.eq_of_localization_maximal (R := K) (fun P _ => Localization P.primeCompl)
    (fun P _ => Algebra.linearMap K _) _ _ fun P _ => ?_
  let φ := algebraMap K (Localization P.primeCompl)
  let y := spMap φ ≫ x
  have hy : ⊤ ≤ (y ≫ jB) ⁻¹ᵁ U := fun z _ => hx (Set.mem_univ (spMap φ z))
  obtain ⟨j, hj⟩ := hV ((y ≫ jB) (IsLocalRing.closedPoint (Localization P.primeCompl)))
  have hyV : ⊤ ≤ (y ≫ jB) ⁻¹ᵁ V j :=
    (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of (Localization P.primeCompl)) (y ≫ jB) hj).ge
  have c1 := OfCharts.comb_of_chart h h' (hp j) (hp' j) (hA j) (hg j) hf hf' y hy hyV i
  have c2 := GradedPieces.comb_map φ (x' := y ≫ πB ≫ genι Z) (Category.assoc _ _ _).symm ha
  rw [← h.2.2 U f hf K _ φ x hx hy i, ← funext (h'.2.2 U f' hf' K _ φ x hx hy)] at c2
  obtain ⟨χ, hχ⟩ := OfCharts.exists_over e πB y
  have c3 := congrFun (((h'.1 U f' hf' _ y hy χ hχ).2 _ ((h.1 U f hf _ y hy χ hχ).1 i)).unique c1 c2) b
  exact (TangentOrigin.evalPt_spMap_comp φ (x ≫ jB) U hx hy _).symm.trans c3

end GlobalTheory.TwoLat

end
