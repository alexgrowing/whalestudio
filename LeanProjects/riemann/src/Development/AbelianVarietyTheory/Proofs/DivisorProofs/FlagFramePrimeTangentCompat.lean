import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisTorsionCountStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomogeneousPolysTangentBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineTangentBasisLocallyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.HtGen.FlagPoint

open GlobalTheory.LineNorm.Chart GlobalTheory.LieMet

theorem residueCharacteristic_eq {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {q : ℕ} (hq : q.Prime)
    (hv : (q : 𝓞 F) ∈ v.asIdeal) : resP v = q := by
  refine (Nat.prime_dvd_prime_iff_eq (residueCharacteristic_prime v) hq).1 (ringChar.dvd ?_)
  rw [← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
  exact hv

theorem chart {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
    {t : SAB H X} {S G : Scheme.{0}} (j : G ⟶ S) (ρ' : S ⟶ X) {K : Type} [Field K] (O : ValuationSubring K)
    {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (io : K →+* C) (ioO : O →+* intO C)
    (hio : (intO C).subtype.comp ioO = io.comp O.subtype) (z : Sp K ⟶ G) (yt : Sp O ⟶ S)
    (hyt : spMap O.subtype ≫ yt = z ≫ j) {U : S.Opens} (hU : IsAffineOpen U) (hin : ⊤ ≤ yt ⁻¹ᵁ U) {g m : ℕ}
    (e : Fin g → (Sp (DualNumber Γ(S, U)) ⟶ t.G.left)) (α : Γ(S, U) →+* G.presheaf.stalk (below z))
    (hα : spMap α ≫ hU.fromSpec = G.fromSpecStalk (below z) ≫ j) (a : Fin m → Fin g → G.presheaf.stalk (below z))
    (w : Fin m → (Sp (DualNumber (G.presheaf.stalk (below z))) ⟶ t.G.left))
    (ha : ∀ l, IsCombAtG t (spMap α ≫ hU.fromSpec ≫ ρ') (fun i => spMap (dualMap α) ≫ e i) (a l) (w l))
    (ψ : G.presheaf.stalk (below z) →+* C) (hψ : ψ = io.comp (Scheme.stalkClosedPointTo z).hom) :
    ∃ β : Γ(S, U) →+* intO C, spMap β ≫ hU.fromSpec = spMap ioO ≫ yt ∧ (∀ r, ψ (α r) = β r) ∧
      ∀ l, IsCombAtG t (spMap (intO C).subtype ≫ (spMap ioO ≫ yt) ≫ ρ')
        (fun i => spMap (dualMap (intO C).subtype) ≫ spMap (dualMap β) ≫ e i) (fun i => ψ (a l i))
        (spMap (dualMap ψ) ≫ w l) := by
  obtain ⟨β, hβ⟩ := exists_ringHom hU yt hin
  obtain ⟨σ, hσ₀⟩ : ∃ σ : G.presheaf.stalk (below z) →+* K, σ = (Scheme.stalkClosedPointTo z).hom := ⟨_, rfl⟩
  have hσ : σ.comp α = O.subtype.comp β := ringHom_ext hU (by
    rw [← spMap_comp', ← spMap_comp', Category.assoc, Category.assoc, hα, hβ, hyt, ← Category.assoc, hσ₀]
    exact congrArg (· ≫ j) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z))
  have h1 : spMap (ioO.comp β) ≫ hU.fromSpec = spMap ioO ≫ yt := by
    rw [← spMap_comp', Category.assoc, hβ]
  have h2 : ψ.comp α = (intO C).subtype.comp (ioO.comp β) := by
    rw [hψ, ← hσ₀, RingHom.comp_assoc, hσ, ← RingHom.comp_assoc, ← hio, RingHom.comp_assoc]
  refine ⟨ioO.comp β, h1, fun r => congrArg (fun φ => φ r) h2, fun l => ?_⟩
  have := coord_map α ψ (ha l)
  rw [h2, ← spMap_comp', Category.assoc, ← Category.assoc (spMap (ioO.comp β)), h1] at this
  simpa only [dual_comp] using this

theorem pairDet_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H
    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian
    X] (t : SAB H X), X.IsSeparated → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V
    : Cover Y) (ρ' : V.X ⟶ X) (ρ : Y.X ⟶ X), V.j ≫ ρ' = V.π ≫ ρ → ∀ (q : ℕ) [Fact q.Prime] (m
    : ℕ) (f : ∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)) (d
    : Y.X → Fin m → Y.Fnˣ), (∀ y l, IsTanAtG t (GlobalTheory.ShFam.stalkPt Y y ≫ ρ) (f y
    l)) → (∀ y (K : Type) [Field K] (ψ : Y.X.presheaf.stalk y →+* K), IsIndep t (spMap ψ ≫
    GlobalTheory.ShFam.stalkPt Y y ≫ ρ) (fun l => spMap (dualMap ψ) ≫ f y l)) → ∀ (k : ℕ) (hk
    : k ≤ m) (N : ℕ) (c : Fin N → ∀ y : Sp ↥(intO ℂ_[q]) ⟶ V.X, TorsChar t (y ≫ ρ') (q ^
    2)), (∀ y (c' : TorsChar t (y ≫ ρ') (q ^ 2)), ∃ j, Agree c' (c j y)) → ∀ (U U' : V.X.Opens) (hU
    : IsAffineOpen U) (hU' : IsAffineOpen U') (g g' : ℕ) (e : Fin g → (Sp (DualNumber Γ(V.X, U)) ⟶
    t.G.left)) (e' : Fin g' → (Sp (DualNumber Γ(V.X, U')) ⟶ t.G.left)) (h : Fin N → Fin g → Γ(V.X,
    U)) (h' : Fin N → Fin g' → Γ(V.X, U')), IsTanBasis t (hU.fromSpec ≫
    ρ') e → IsTanBasis t (hU'.fromSpec ≫ ρ') e' → (∀ (x : Γ(V.X, U) →+* ↥(intO ℂ_[q])) (y
    : Sp ↥(intO ℂ_[q]) ⟶ V.X), spMap x ≫ hU.fromSpec = y → ∀ j, DlogIs t q 2 (c j
    y) (fun i => spMap (dualMap x) ≫ e i) (fun i => x (h j i))) → (∀ (x : Γ(V.X, U') →+* ↥(intO
    ℂ_[q])) (y : Sp ↥(intO ℂ_[q]) ⟶ V.X), spMap x ≫ hU'.fromSpec = y → ∀ j, DlogIs t q 2 (c j
    y) (fun i => spMap (dualMap x) ≫ e' i) (fun i => x (h' j i))) → ∀ (s s' : (Fin k → Fin
    N) → V.G.functionField), (∀ z : V.G, V.j z ∈ U → ∃ (α : Γ(V.X, U) →+* V.G.presheaf.stalk z) (a
    : Fin m → Fin g → V.G.presheaf.stalk z), spMap α ≫ hU.fromSpec = V.G.fromSpecStalk z ≫ V.j ∧ (∀ l, IsCombAtG t (spMap
    α ≫ hU.fromSpec ≫ ρ') (fun i => spMap (dualMap α) ≫ e i) (a l) (spMap (dualMap (V.π.stalkMap
    z).hom) ≫ f (V.π z) l)) ∧ ∀ σ, s σ / V.φ ((∏ l : Fin k, d (V.π z) (Fin.castLE hk l) : Y.Fnˣ)
    : Y.Fn) = algebraMap (V.G.presheaf.stalk z) V.G.functionField (pairDet (fun j i => α (h j i)) a
    hk σ)) → (∀ z : V.G, V.j z ∈ U' → ∃ (α : Γ(V.X, U') →+* V.G.presheaf.stalk z) (a
    : Fin m → Fin g' → V.G.presheaf.stalk z), spMap α ≫ hU'.fromSpec = V.G.fromSpecStalk z ≫ V.j ∧ (∀ l, IsCombAtG t (spMap
    α ≫ hU'.fromSpec ≫ ρ') (fun i => spMap (dualMap α) ≫ e' i) (a l) (spMap (dualMap (V.π.stalkMap
    z).hom) ≫ f (V.π z) l)) ∧ ∀ σ, s' σ / V.φ ((∏ l : Fin k, d (V.π z) (Fin.castLE hk l) : Y.Fnˣ)
    : Y.Fn) = algebraMap (V.G.presheaf.stalk z) V.G.functionField (pairDet (fun j i => α (h' j i)) a
    hk σ)) → ∀ (v : HeightOneSpectrum (𝓞 F)) (ε : GlobalTheory.TrueGeo.Ext v) (y : AlgPt Y) (z
    : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp ε.O ⟶ V.X), (q
    : 𝓞 F) ∈ v.asIdeal → z ≫ V.π = y.1 → spMap ε.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ U → ⊤ ≤ yt ⁻¹ᵁ U' → ∀ [Fact
    (resP v).Prime], (∀ l, 0 < GlobalTheory.ShFam.Pad.grNorm t (spMap ((ioOf (resP v) ε).comp
    (Scheme.stalkClosedPointTo y.1).hom) ≫ GlobalTheory.ShFam.stalkPt Y (below y.1) ≫ ρ) (lat t
    (resP v) (spMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom) ≫
    GlobalTheory.ShFam.stalkPt Y (below y.1) ≫ ρ) (decide (resP v = q))) (fun l => spMap (dualMap
    ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom)) ≫ f (below y.1) l) (Fin.castLE hk
    l)) ∧ (∀ σ, ‖ioOf (resP v) ε (TrueGeo.valAt z (s σ / V.φ ((∏ l : Fin k, d (below
    y.1) (Fin.castLE hk l) : Y.Fnˣ) : Y.Fn)))‖ ≤ ∏ l : Fin k, GlobalTheory.ShFam.Pad.grNorm t (spMap
    ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom) ≫ GlobalTheory.ShFam.stalkPt Y
    (below y.1) ≫ ρ) (lat t (resP v) (spMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo
    y.1).hom) ≫ GlobalTheory.ShFam.stalkPt Y (below y.1) ≫ ρ) (decide (resP v =
    q))) (fun l => spMap (dualMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo
    y.1).hom)) ≫ f (below y.1) l) (Fin.castLE hk l)) ∧ (∃ σ, ‖ioOf (resP v) ε (TrueGeo.valAt z (s σ
    / V.φ ((∏ l : Fin k, d (below y.1) (Fin.castLE hk l) : Y.Fnˣ)
    : Y.Fn)))‖ = ∏ l : Fin k, GlobalTheory.ShFam.Pad.grNorm t (spMap ((ioOf (resP v) ε).comp
    (Scheme.stalkClosedPointTo y.1).hom) ≫ GlobalTheory.ShFam.stalkPt Y (below y.1) ≫ ρ) (lat t
    (resP v) (spMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom) ≫
    GlobalTheory.ShFam.stalkPt Y (below y.1) ≫ ρ) (decide (resP v = q))) (fun l => spMap (dualMap
    ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom)) ≫ f (below y.1) l) (Fin.castLE hk
    l)) ∧ ∀ σ, ‖ioOf (resP v) ε (TrueGeo.valAt z ((s σ - s' σ) / V.φ ((∏ l : Fin k, d (below
    y.1) (Fin.castLE hk l) : Y.Fnˣ) : Y.Fn)))‖ < ∏ l : Fin k, GlobalTheory.ShFam.Pad.grNorm t (spMap
    ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom) ≫ GlobalTheory.ShFam.stalkPt Y
    (below y.1) ≫ ρ) (lat t (resP v) (spMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo
    y.1).hom) ≫ GlobalTheory.ShFam.stalkPt Y (below y.1) ≫ ρ) (decide (resP v =
    q))) (fun l => spMap (dualMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo
    y.1).hom)) ≫ f (below y.1) l) (Fin.castLE hk l) := by
  intro E _ _ _ H X _ t hX F _ _ Y V ρ' ρ hρ q hq m f d hf hind k hk N c hc U U' hU hU' g g' e e' h h' he he' hd hd'
    s s' hs hs' v ε y z yt hv hz hyt hin hin' hp
  obtain rfl : resP v = q := residueCharacteristic_eq v hq.out hv
  obtain rfl : hq = hp := rfl
  obtain ⟨y, hy⟩ := y
  dsimp only at hz ⊢
  subst hz
  have h1 := ioOf_le_one_iff (resP v) hv ε
  generalize ioOf (resP v) ε = io at h1 ⊢
  let ioO : ε.O →+* intO ℂ_[resP v] := (io.comp ε.O.subtype).codRestrict _ fun b => (h1 b).2 b.2
  have hio : (intO ℂ_[resP v]).subtype.comp ioO = io.comp ε.O.subtype := rfl
  have hmem : ∀ W : V.X.Opens, ⊤ ≤ yt ⁻¹ᵁ W → V.j (below z) ∈ W := fun W hW => by
    have : (spMap ε.O.subtype ≫ yt) (IsLocalRing.closedPoint _) ∈ W := hW (Set.mem_univ _)
    rwa [hyt] at this
  obtain ⟨α, a, hα, ha, hsα⟩ := hs _ (hmem U hin)
  obtain ⟨α', a', hα', ha', hsα'⟩ := hs' _ (hmem U' hin')
  obtain ⟨ψ, hψ⟩ : ∃ ψ : V.G.presheaf.stalk (below z) →+* ℂ_[resP v],
    ψ = io.comp (Scheme.stalkClosedPointTo z).hom := ⟨_, rfl⟩
  obtain ⟨β, hβ, hβα, hb⟩ := chart V.j ρ' ε.O io ioO hio z yt hyt hU hin e α hα a _ ha ψ hψ
  obtain ⟨β', hβ', hβα', hb'⟩ := chart V.j ρ' ε.O io ioO hio z yt hyt hU' hin' e' α' hα' a' _ ha' ψ hψ
  obtain ⟨φ, hφ⟩ : ∃ φ : Y.X.presheaf.stalk (V.π (below z)) →+* ℂ_[resP v],
    φ = io.comp (Scheme.stalkClosedPointTo (z ≫ V.π)).hom := ⟨_, rfl⟩
  have hφψ : ψ.comp (V.π.stalkMap (below z)).hom = φ := by
    rw [hφ, hψ, Scheme.stalkClosedPointTo_comp]; rfl
  simp only [dual_comp _ ψ, hφψ] at hb hb'
  have hx : spMap φ ≫ GlobalTheory.ShFam.stalkPt Y (V.π (below z)) ≫ ρ =
      spMap (intO ℂ_[resP v]).subtype ≫ (spMap ioO ≫ yt) ≫ ρ' := by
    have e1 : spMap (Scheme.stalkClosedPointTo z).hom ≫ V.G.fromSpecStalk (below z) = z :=
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk z
    have e2 : spMap (V.π.stalkMap (below z)).hom ≫ GlobalTheory.ShFam.stalkPt Y (V.π (below z)) =
        V.G.fromSpecStalk (below z) ≫ V.π := Scheme.SpecMap_stalkMap_fromSpecStalk V.π
    rw [← hφψ, ← spMap_comp', Category.assoc, ← Category.assoc _ _ ρ, e2, Category.assoc, ← hρ, hψ, ← spMap_comp',
      Category.assoc, ← Category.assoc _ (V.G.fromSpecStalk _), e1, Category.assoc,
      ← Category.assoc (spMap (intO ℂ_[resP v]).subtype), spMap_comp', hio, ← spMap_comp', Category.assoc,
      ← Category.assoc _ yt, hyt, Category.assoc]
  have hB := GlobalTheory.LineNorm.WedgeMax.isTanBasis_map t β he
  have hB' := GlobalTheory.LineNorm.WedgeMax.isTanBasis_map t β' he'
  rw [← Category.assoc, hβ] at hB
  rw [← Category.assoc, hβ'] at hB'
  have hli : LinearIndependent ℂ_[resP v] fun l i => ψ (a l i) :=
    linInd (GlobalTheory.LineNorm.WedgeMax.isTanBasis_map t _ hB).1 hb (hx ▸ hind _ _ φ)
  obtain ⟨k1, k2, k3, k4⟩ := GlobalTheory.T.pairDet_norm_le_attained_and_sub_norm_lt E H X t hX (resP v) _ g g' _ _ hB hB' N (fun j => c j (spMap ioO ≫ yt)) _ _
    (hc _) (hd β _ hβ) (hd' β' _ hβ') m k hk _ _ _ hli hb hb' _ rfl
  rw [← hx] at k1 k2 k3 k4
  have hval : ∀ r, io (TrueGeo.valAt z (algebraMap (V.G.presheaf.stalk (below z)) V.G.functionField r)) = ψ r :=
    fun r => by rw [hψ, Base.valAt_stalk]; rfl
  have hv1 : ∀ σ, ψ (pairDet (fun j i => α (h j i)) a hk σ) =
      pairDet (fun j i => (β (h j i) : ℂ_[resP v])) (fun l i => ψ (a l i)) hk σ := fun σ => by
    simp only [map_pairDet, hβα]
  have hv2 : ∀ σ, ψ (pairDet (fun j i => α' (h' j i)) a' hk σ) =
      pairDet (fun j i => (β' (h' j i) : ℂ_[resP v])) (fun l i => ψ (a' l i)) hk σ := fun σ => by
    simp only [map_pairDet, hβα']
  rw [decide_eq_true rfl]
  subst hφ
  refine ⟨fun l => k1 _, fun σ => ?_, ?_, fun σ => ?_⟩
  · exact (congrArg norm (((congrArg (fun r => io (TrueGeo.valAt z r)) (hsα σ)).trans (hval _)).trans (hv1 σ))).trans_le
      (k2 σ)
  · obtain ⟨σ, hσ⟩ := k3
    exact ⟨σ, (congrArg norm (((congrArg (fun r => io (TrueGeo.valAt z r)) (hsα σ)).trans (hval _)).trans
      (hv1 σ))).trans hσ⟩
  · have e1 := (sub_div _ _ _).trans ((congrArg₂ (· - ·) (hsα σ) (hsα' σ)).trans (map_sub _ _ _).symm)
    refine (congrArg norm (((congrArg (fun r => io (TrueGeo.valAt z r)) e1).trans (hval _)).trans ?_)).trans_lt (k4 σ)
    rw [map_sub, hv1, hv2]

end GlobalTheory.HtGen.FlagPoint
