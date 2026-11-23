import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasPRatio
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniqueIntegralLiftNormPInverseStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTPres

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

theorem bc_bc {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (φ : R →+* R') (ψ : R' →+* R'')
    (w : Sp (DualNumber R) ⟶ t.G.left) :
    spMap (dualMap ψ) ≫ spMap (dualMap φ) ≫ w = spMap (dualMap (ψ.comp φ)) ≫ w := by
  rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← Formalism.L2.Pj.dualMap_comp]

theorem isTanBasis_map {R S : Type} [CommRing R] [CommRing S] {x : Sp R ⟶ X} {g : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (h : GlobalTheory.LineNorm.IsTanBasis t x e) (φ : R →+* S) :
    GlobalTheory.LineNorm.IsTanBasis t (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ e i) := by
  refine ⟨fun i => GlobalTheory.FactorDepth.isTanAtG_map t φ (h.1 i), fun T _ ψ w hw => ?_⟩
  simp only [bc_bc]
  rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap] at hw ⊢
  exact h.2 T (ψ.comp φ) w hw

theorem ext_uniq (hX : X.IsSeparated) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C]
    (x y : Sp ↥(intO C) ⟶ X) (h : spMap (intO C).subtype ≫ y = spMap (intO C).subtype ≫ x) : y = x := by
  have : IsDominant (spMap (intO C).subtype) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (intO C).subtype_injective).le.trans bot_le)⟩
  exact ext_of_isDominant _ h

theorem mem_latDR_iff (hX : X.IsSeparated) {R : Type} [CommRing R] (x : Sp R ⟶ X) {g : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (he : GlobalTheory.LineNorm.IsTanBasis t x e) (C : Type)
    [NontriviallyNormedField C] [IsUltrametricDist C] (φ : R →+* ↥(intO C)) (cf : Fin g → C)
    (w : Sp (DualNumber C) ⟶ t.G.left)
    (hw : IsCombAtG t (spMap (intO C).subtype ≫ spMap φ ≫ x)
      (fun i => spMap (dualMap ((intO C).subtype.comp φ)) ≫ e i) cf w) :
    w ∈ latDR t (spMap (intO C).subtype ≫ spMap φ ≫ x) ↔ ∀ i, ‖cf i‖ ≤ 1 := by
  have hb := isTanBasis_map t he φ
  have hv : ∀ i, IsTanAtG t (spMap (intO C).subtype ≫ spMap φ ≫ x)
      (spMap (dualMap ((intO C).subtype.comp φ)) ≫ e i) := fun i => by
    rw [← bc_bc]; exact GlobalTheory.FactorDepth.isTanAtG_map t (intO C).subtype (hb.1 i)
  have hxC : spMap (intO C).subtype ≫ spMap φ ≫ x = spMap ((intO C).subtype.comp φ) ≫ x := by
    rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
  constructor
  · rintro ⟨xO, hx, vO, hvO, rfl⟩ i
    obtain rfl := ext_uniq hX C _ _ hx
    obtain ⟨a, ha, -⟩ := he.2 (↥(intO C)) φ vO hvO
    have hc := GlobalTheory.LatDRFree.comb_map t (intO C).subtype ha
    simp only [bc_bc] at hc
    have ht := GlobalTheory.FactorDepth.isTanAtG_map t (intO C).subtype hvO
    rw [hxC] at ht hc hw
    have e1 := (he.2 C _ _ ht).unique hw hc
    rw [e1]
    exact (a i).2
  · intro hc
    obtain ⟨wO, hwO, hcO⟩ := GlobalTheory.FlagEmb.exists_comb t hb.1 fun i => (⟨cf i, hc i⟩ : ↥(intO C))
    refine ⟨_, rfl, wO, hwO, ?_⟩
    have hb' := GlobalTheory.LatDRFree.comb_map t (intO C).subtype hcO
    simp only [bc_bc] at hb'
    exact GlobalTheory.FlagEmb.comb_unique t hv hb' hw

theorem sum_single {R C : Type} [CommRing R] [NontriviallyNormedField C] [IsUltrametricDist C] {g : ℕ}
    (φ : R →+* ↥(intO C)) (i : Fin g) (a : R) (cf : Fin g → C) :
    ∑ k, ((φ ((Pi.single i a : Fin g → R) k) : ↥(intO C)) : C) * cf k = (φ a : C) * cf i := by
  rw [Finset.sum_eq_single i (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (by simp)]
  simp

end GlobalTheory.HTPres

namespace GlobalTheory.HTPres

theorem exists_pres : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) [IsLocallyNoetherian X], X.IsSeparated → ∀ (p : ℕ), p.Prime → ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CharZero R] (x : Sp R ⟶ X), (∃ ζ : R, IsPrimitiveRoot ζ p) → GlobalTheory.LineNorm.SplitTors t x p → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)), GlobalTheory.LineNorm.IsTanBasis t x e → ∀ b : Bool, ∃ (M : ℕ) (h : Fin (M + 1) → Fin g → R), Pres t x p b e h := by
  intro hB E _ _ _ H X t _ hX p hp R _ _ _ _ x hζ hS g e he b
  cases b with
  | false =>
    refine ⟨g, Fin.cons 0 (fun i => Pi.single i 1), ⟨0, fun i => ?_⟩, fun C φ cf w hw => ?_⟩
    · rw [pow_zero]
      exact Submodule.subset_span ⟨i.succ, by simp⟩
    · change w ∈ latDR t _ ↔ _
      rw [mem_latDR_iff t hX x he C.S φ cf w hw, Fin.forall_fin_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, sum_single, map_one]
      simp
  | true =>
    obtain ⟨n, h', hh'⟩ := GlobalTheory.T.exists_tangent_presentation_prime E H X t R x g e he p hp hζ hS
    refine ⟨n + g, Fin.cons 0 (Fin.append h' fun i => Pi.single i (p : R)), ⟨1, fun i => ?_⟩, fun C φ cf w hw => ?_⟩
    · rw [pow_one]
      exact Submodule.subset_span ⟨(Fin.natAdd n i).succ, by simp⟩
    · haveI := Fact.mk hp
      have hw' : IsCombAtG t (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ x)
          (fun i => spMap (dualMap (intO ↥C.S).subtype) ≫ spMap (dualMap φ) ≫ e i) cf w := by
        simpa only [bc_bc] using hw
      change w ∈ latHT t p _ ↔ _
      rw [GlobalTheory.T.unique_integral_lift_norm_p_inverse hB E H X t p ↥C.S C.norm_p (spMap φ ≫ x)
        (fun x' hx' => ext_uniq hX _ _ _ hx') g _ (isTanBasis_map t he φ) n (fun j i => φ (h' j i))
        (hh' ↥C.S φ).1 (hh' ↥C.S φ).2 cf w hw', Fin.forall_fin_succ, Fin.forall_fin_add]
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.append_left, Fin.append_right, sum_single, map_natCast]
      simp [norm_mul]

end GlobalTheory.HTPres
