import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisTorsionCountStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomogeneousPolysTangentBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineTangentBasisLocallyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HtGen.CoverChart

theorem pairDet_tri {R J : Type} [CommRing R] {m g k : ℕ} (h : J → Fin g → R) (a b : Fin m → Fin g → R)
    (T : Fin m → Fin m → R) (hT : ∀ i l, i < l → T i l = 0) (hb : ∀ i, b i = ∑ l, T i l • a l) (hk : k ≤ m)
    (σ : Fin k → J) :
    pairDet h b hk σ = (∏ l : Fin k, T (Fin.castLE hk l) (Fin.castLE hk l)) * pairDet h a hk σ := by
  have e : ∀ c : Fin m → Fin g → R, pairDet h c hk σ = minor (fun l r => ∑ i, h (σ r) i * c l i) hk id := fun c =>
    (Matrix.det_transpose _).symm
  rw [e, e]
  refine Chart.minor_tri _ _ T hT (fun i => funext fun r => ?_) hk id
  simp only [hb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by ring

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := (Spec.map_comp _ _)

variable {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y)

theorem gen_eq' {G : Scheme.{0}} [IsIntegral G] (z : G) :
    spMap (algebraMap (G.presheaf.stalk z) G.functionField) ≫ G.fromSpecStalk z = G.fromSpecStalk (genericPoint G) :=
  Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes z)

theorem stalk_eq (z : V.G) :
    spMap (V.π.stalkMap z).hom ≫ Y.X.fromSpecStalk (V.π z) = V.G.fromSpecStalk z ≫ V.π :=
  Scheme.SpecMap_stalkMap_fromSpecStalk V.π

theorem alg_comp_stalkMap (z : V.G) :
    (algebraMap (V.G.presheaf.stalk z) V.G.functionField).comp (V.π.stalkMap z).hom =
      V.φ.comp (algebraMap (Y.X.presheaf.stalk (V.π z)) Y.X.functionField) := by
  have h : spMap ((algebraMap (V.G.presheaf.stalk z) V.G.functionField).comp (V.π.stalkMap z).hom) ≫
        Y.X.fromSpecStalk (V.π z) =
      spMap (V.φ.comp (algebraMap (Y.X.presheaf.stalk (V.π z)) Y.X.functionField)) ≫ Y.X.fromSpecStalk (V.π z) := by
    rw [sp_comp, sp_comp, Category.assoc, Category.assoc, stalk_eq, gen_eq', ← Category.assoc, gen_eq', V.φ_spec]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 h))

end GlobalTheory.HtGen.CoverChart

open GlobalTheory.HtGen.CoverChart GlobalTheory.LineNorm.Chart GlobalTheory.LieMet in

theorem GlobalTheory.HtGen.CoverChart.pairDet_div_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (ρ' : V.X ⟶ X) (ρ : Y.X ⟶ X), V.j ≫ ρ' = V.π ≫ ρ → ∀ (m : ℕ) (u₀ : Fin m → (Sp (DualNumber Y.Fn) ⟶ t.G.left)) (f : ∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)) (d : Y.X → Fin m → Y.Fnˣ), IsFlagFrame t ρ u₀ f d → ∀ (U : V.X.Opens) (hU : IsAffineOpen U) (g : ℕ) (e : Fin g → (Sp (DualNumber Γ(V.X, U)) ⟶ t.G.left)), IsTanBasis t (hU.fromSpec ≫ ρ') e → ∀ (J : Type) (h : J → Fin g → Γ(V.X, U)) (k : ℕ) (hk : k ≤ m), ∃ s : (Fin k → J) → V.G.functionField, ∀ z : V.G, V.j z ∈ U → ∃ (α : Γ(V.X, U) →+* V.G.presheaf.stalk z) (a : Fin m → Fin g → V.G.presheaf.stalk z), spMap α ≫ hU.fromSpec = V.G.fromSpecStalk z ≫ V.j ∧ (∀ l, IsCombAtG t (spMap α ≫ hU.fromSpec ≫ ρ') (fun i => spMap (dualMap α) ≫ e i) (a l) (spMap (dualMap (V.π.stalkMap z).hom) ≫ f (V.π z) l)) ∧ ∀ σ, s σ / V.φ ((∏ l : Fin k, d (V.π z) (Fin.castLE hk l) : Y.Fnˣ) : Y.Fn) = algebraMap (V.G.presheaf.stalk z) V.G.functionField (pairDet (fun j i => α (h j i)) a hk σ) := by
  intro E _ _ _ H X t F _ _ Y V ρ' ρ hρ m u₀ f d hf U hU g e he J h k hk
  by_cases hgen : V.j (genericPoint V.G) ∈ U
  swap
  · exact ⟨fun _ => 0, fun z hz => absurd
      (((genericPoint_specializes z).map V.j.continuous).mem_open U.isOpen hz) hgen⟩
  choose α hα using fun (z : V.G) (hz : V.j z ∈ U) => exists_stalkHom hU V.j z hz
  have hα' : ∀ z hz, spMap (α z hz) ≫ hU.fromSpec ≫ ρ' = V.G.fromSpecStalk z ≫ V.π ≫ ρ := fun z hz => by
    rw [← Category.assoc, hα, Category.assoc, hρ]
  let ι₀ : Γ(V.X, U) →+* V.G.functionField := α _ hgen
  have hι : spMap ι₀ ≫ hU.fromSpec ≫ ρ' = spMap V.φ ≫ GlobalTheory.ShFam.genericPt Y ≫ ρ :=
    (hα' _ hgen).trans (by rw [← Category.assoc, V.φ_spec, Category.assoc]; rfl)
  have hαι : ∀ z hz, (algebraMap (V.G.presheaf.stalk z) V.G.functionField).comp (α z hz) = ι₀ := fun z hz =>
    ringHom_ext hU (by
      rw [sp_comp, Category.assoc, hα, ← Category.assoc, gen_eq']
      exact (hα _ hgen).symm)
  have ha : ∀ z (hz : V.j z ∈ U) l, ∃ a, IsCombAtG t (spMap (α z hz) ≫ hU.fromSpec ≫ ρ')
      (fun i => spMap (dualMap (α z hz)) ≫ e i) a (spMap (dualMap (V.π.stalkMap z).hom) ≫ f (V.π z) l) := fun z hz l =>
    (he.2 _ (α z hz) _ (isTan_map _ (by
      rw [hα', ← Category.assoc, ← Category.assoc, ← stalk_eq]; rfl) (hf.tan (V.π z) l))).exists
  choose a ha using ha
  have key : ∀ z (hz : V.j z ∈ U) i, ∃ cf : Fin m → Y.Fn, cf i = d (V.π z) i ∧ (∀ k, i < k → cf k = 0) ∧
      IsCombAtG t (spMap ι₀ ≫ hU.fromSpec ≫ ρ') (fun i => spMap (dualMap ι₀) ≫ e i)
        (∑ l, V.φ (cf l) • fun j => algebraMap (V.G.presheaf.stalk z) V.G.functionField (a z hz l j))
        (spMap (dualMap V.φ) ≫ u₀ i) := by
    intro z hz i
    obtain ⟨cf, h1, h2, h3⟩ := hf.tri (V.π z) i
    have h4 := GlobalTheory.LatDRFree.comb_map t V.φ h3
    refine ⟨cf, h1, h2, comb_comb (fun j => isTan_map _ rfl (he.1 j)) (fun l => ?_) (hι ▸ h4)⟩
    have := coord_map _ (algebraMap (V.G.presheaf.stalk z) V.G.functionField) (ha z hz l)
    rw [hαι, dual_comp, alg_comp_stalkMap] at this
    rw [dual_comp]
    exact this
  choose T hT1 hT2 hT3 using key
  have hA₀ : ∀ i, ∃ b, IsCombAtG t (spMap ι₀ ≫ hU.fromSpec ≫ ρ') (fun i => spMap (dualMap ι₀) ≫ e i) b
      (spMap (dualMap V.φ) ≫ u₀ i) := fun i => ⟨_, hT3 _ hgen i⟩
  choose A₀ hA₀ using hA₀
  have hA : ∀ z hz i, A₀ i = ∑ l, V.φ (T z hz i l) • fun j => algebraMap _ V.G.functionField (a z hz l j) := fun z hz i =>
    (he.2 _ ι₀ _ (comb_tan (fun j => isTan_map _ rfl (he.1 j)) (hT3 z hz i))).unique (hA₀ i) (hT3 z hz i)
  refine ⟨fun σ => pairDet (fun j i => ι₀ (h j i)) A₀ hk σ, fun z hz => ⟨α z hz, a z hz, hα z hz, ha z hz, fun σ => ?_⟩⟩
  have hne : V.φ ((∏ l : Fin k, d (V.π z) (Fin.castLE hk l) : Y.Fnˣ) : Y.Fn) ≠ 0 :=
    (_root_.map_ne_zero V.φ).2 (Units.ne_zero _)
  beta_reduce
  rw [div_eq_iff hne, map_pairDet, pairDet_tri _ _ A₀ (fun i l => V.φ (T z hz i l))
    (fun i l hl => by simp only [hT2 z hz i l hl, map_zero]) (hA z hz), mul_comm, Units.coe_prod, map_prod, ← hαι z hz]
  simp only [hT1]
  rfl
