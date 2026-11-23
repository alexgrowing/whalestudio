import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentOfCutSec
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

open GlobalTheory.LineNorm.Chart in
private theorem chart' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
    {t : SAB H X} {S G : Scheme.{0}} (j : G ⟶ S) (ρ' : S ⟶ X) {K : Type} [Field K] (O : ValuationSubring K)
    {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (io : K →+* C) (ioO : O →+* intO C)
    (hio : (intO C).subtype.comp ioO = io.comp O.subtype) (z : Sp K ⟶ G) (yt : Sp O ⟶ S)
    (hyt : spMap O.subtype ≫ yt = z ≫ j) {U : S.Opens} (hU : IsAffineOpen U) (β : Γ(S, U) →+* O)
    (hβ : spMap β ≫ hU.fromSpec = yt) {g m : ℕ}
    (e : Fin g → (Sp (DualNumber Γ(S, U)) ⟶ t.G.left)) (α : Γ(S, U) →+* G.presheaf.stalk (below z))
    (hα : spMap α ≫ hU.fromSpec = G.fromSpecStalk (below z) ≫ j) (a : Fin m → Fin g → G.presheaf.stalk (below z))
    (w : Fin m → (Sp (DualNumber (G.presheaf.stalk (below z))) ⟶ t.G.left))
    (ha : ∀ l, IsCombAtG t (spMap α ≫ hU.fromSpec ≫ ρ') (fun i => spMap (dualMap α) ≫ e i) (a l) (w l))
    (ψ : G.presheaf.stalk (below z) →+* C) (hψ : ψ = io.comp (Scheme.stalkClosedPointTo z).hom) :
    (∀ r, ψ (α r) = ioO.comp β r) ∧
      ∀ l, IsCombAtG t (spMap (intO C).subtype ≫ (spMap ioO ≫ yt) ≫ ρ')
        (fun i => spMap (dualMap (intO C).subtype) ≫ spMap (dualMap (ioO.comp β)) ≫ e i) (fun i => ψ (a l i))
        (spMap (dualMap ψ) ≫ w l) := by
  obtain ⟨σ, hσ₀⟩ : ∃ σ : G.presheaf.stalk (below z) →+* K, σ = (Scheme.stalkClosedPointTo z).hom := ⟨_, rfl⟩
  have hσ : σ.comp α = O.subtype.comp β := ringHom_ext hU (by
    rw [← spMap_comp', ← spMap_comp', Category.assoc, Category.assoc, hα, hβ, hyt, ← Category.assoc, hσ₀]
    exact congrArg (· ≫ j) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z))
  have h1 : spMap (ioO.comp β) ≫ hU.fromSpec = spMap ioO ≫ yt := by
    rw [← spMap_comp', Category.assoc, hβ]
  have h2 : ψ.comp α = (intO C).subtype.comp (ioO.comp β) := by
    rw [hψ, ← hσ₀, RingHom.comp_assoc, hσ, ← RingHom.comp_assoc, ← hio, RingHom.comp_assoc]
  refine ⟨fun r => congrArg (fun φ => φ r) h2, fun l => ?_⟩
  have := coord_map α ψ (ha l)
  rw [h2, ← spMap_comp', Category.assoc, ← Category.assoc (spMap (ioO.comp β)), h1] at this
  simpa only [dual_comp] using this

private theorem val_sum {K : Type} [Field K] {Z : Scheme.{0}} [AlgebraicGeometry.IsIntegral Z] (z : Sp K ⟶ Z) {M : ℕ}
    (c : Fin M → Z.functionField) (hc : ∀ k, RegAt (below z) (c k)) (b : Fin M → Z.presheaf.stalk (below z)) :
    TrueGeo.valAt z (∑ k, c k * algebraMap _ Z.functionField (b k)) =
      ∑ k, TrueGeo.valAt z (c k) * (Scheme.stalkClosedPointTo z).hom (b k) := by
  choose c' hc' using hc
  simp only [← hc', ← map_mul, ← map_sum, Res.valAt_algebraMap]

open GlobalTheory.LineNorm.Chart in
theorem UpperTheory.test_point_lifts_to_cover :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (ρ' : V.X ⟶ X) (ρ : Y.X ⟶ X), V.j ≫ ρ' = V.π ≫ ρ → ∀ (W : Y.X.Opens) (p : ℕ) [Fact p.Prime] v e y z yt, Tst V W p v e y z yt → ∃ x : Sp ↥(intO ℂ_[p]) ⟶ V.X, spMap (intO ℂ_[p]).subtype ≫ x ≫ ρ' = spMap (psi p e y) ≫ stalkPt Y (below y.1) ≫ ρ ∧ spMap (intO ℂ_[p]).subtype ≫ x ≫ ρ' = spMap (ioOf p e) ≫ y.1 ≫ ρ ∧ ∀ (U : V.X.Opens) (hU : IsAffineOpen U), ⊤ ≤ yt ⁻¹ᵁ U → ∃ φ : Γ(V.X, U) →+* ↥(intO ℂ_[p]), spMap φ ≫ hU.fromSpec = x ∧ ∀ (g : ℕ) (ε : Fin g → (Sp (DualNumber Γ(V.X, U)) ⟶ t.G.left)) (M m : ℕ) (h : Fin M → Fin g → Γ(V.X, U)) (f : (∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left))) (T : Y.X → Matrix (Fin m) (Fin m) Y.Fn) (P : Matrix (Fin M) (Fin m) V.G.functionField), ChartCo t V ρ' hU ε h f T P → ∃ A : Fin m → Fin g → ℂ_[p], (∀ i, IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x ≫ ρ') (fun k => spMap (dualMap (intO ℂ_[p]).subtype) ≫ spMap (dualMap φ) ≫ ε k) (A i) (spMap (dualMap (psi p e y)) ≫ f (below y.1) i)) ∧ ∀ (N : ℕ) (S : Fin N → Fin M → F), (vals V (constM V S * P) T z (below y.1)).map (ioOf p e) = covMat (fun j k => ioOf p e (algebraMap F (AlgebraicClosure F) (S j k))) (fun j k => (φ (h j k) : ℂ_[p])) A := by
  intro E _ _ _ H X t F _ _ Y V ρ' ρ hρ W p hp v ε y z yt hT
  obtain ⟨hv, -, hz, hyt⟩ := hT
  subst hv
  obtain ⟨y, hy⟩ := y
  dsimp only at hz ⊢
  subst hz
  have h1 := ioOf_le_one_iff (resP v) (residueCharacteristic_mem v) ε
  unfold psi
  dsimp only
  generalize ioOf (resP v) ε = io at h1 ⊢
  let ioO : ε.O →+* intO ℂ_[resP v] := (io.comp ε.O.subtype).codRestrict _ fun b => (h1 b).2 b.2
  have hio : (intO ℂ_[resP v]).subtype.comp ioO = io.comp ε.O.subtype := rfl
  have hx : spMap (intO ℂ_[resP v]).subtype ≫ (spMap ioO ≫ yt) ≫ ρ' = spMap io ≫ (z ≫ V.π) ≫ ρ := by
    rw [Category.assoc, ← Category.assoc (spMap (intO ℂ_[resP v]).subtype), spMap_comp', hio, ← spMap_comp',
      Category.assoc, ← Category.assoc _ yt, hyt, Category.assoc, hρ, Category.assoc]
  refine ⟨spMap ioO ≫ yt, ?_, hx, fun U hU hin => ?_⟩
  · rw [hx, ← spMap_comp', Category.assoc, ← Category.assoc _ (stalkPt _ _)]
    exact congrArg (fun q => spMap io ≫ q ≫ ρ) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (z ≫ V.π)).symm
  obtain ⟨β, hβ⟩ := exists_ringHom hU yt hin
  refine ⟨ioO.comp β, by rw [← spMap_comp', Category.assoc, hβ], fun g e M m h f T P hC => ?_⟩
  have hmem : V.j (below z) ∈ U := by
    have : (spMap ε.O.subtype ≫ yt) (IsLocalRing.closedPoint _) ∈ U := hin (Set.mem_univ _)
    rwa [hyt] at this
  obtain ⟨α, a, hα, ha, hP⟩ := hC _ hmem
  obtain ⟨ψ, hψ⟩ : ∃ ψ : V.G.presheaf.stalk (below z) →+* ℂ_[resP v],
    ψ = io.comp (Scheme.stalkClosedPointTo z).hom := ⟨_, rfl⟩
  obtain ⟨hβα, hb⟩ := chart' V.j ρ' ε.O io ioO hio z yt hyt hU β hβ e α hα a _ ha ψ hψ
  obtain ⟨φ, hφ⟩ : ∃ φ : Y.X.presheaf.stalk (V.π (below z)) →+* ℂ_[resP v],
    φ = io.comp (Scheme.stalkClosedPointTo (z ≫ V.π)).hom := ⟨_, rfl⟩
  have hφψ : ψ.comp (V.π.stalkMap (below z)).hom = φ := by
    rw [hφ, hψ, Scheme.stalkClosedPointTo_comp]; rfl
  simp only [dual_comp _ ψ, hφψ] at hb
  subst hφ
  refine ⟨fun i k => ψ (a i k), hb, fun N S => ?_⟩
  ext j i
  have e1 : RootFrame.locM V (constM V S * P) T (V.π (below z)) j i = ∑ k, V.φ (algebraMap F Y.Fn (S j k)) *
      algebraMap (V.G.presheaf.stalk (below z)) V.G.functionField (∑ l, α (h k l) * a i l) := by
    simp only [← hP]
    simp only [RootFrame.locM, Matrix.mul_assoc]
    rw [Matrix.mul_apply]
    rfl
  have e2 : ∀ c : F, TrueGeo.valAt z (V.φ (algebraMap F Y.Fn c)) = algebraMap F (AlgebraicClosure F) c := fun c => by
    rw [V.valAt_φ z (Y.regAt_algebraMap _ c)]
    exact Res.valAt_const hy c
  refine (congrArg (fun r => io (TrueGeo.valAt z r)) e1).trans ?_
  rw [val_sum z _ (fun k => V.regAt_φ (Y.regAt_algebraMap _ _))]
  simp only [e2, covMat, Matrix.of_apply, map_sum, map_mul, ← hβα]
  subst hψ
  rfl
