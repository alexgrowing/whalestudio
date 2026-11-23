import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined

noncomputable section
namespace GlobalTheory.ArcPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace SecValue

variable {K R : Type} [CommRing K] [CommRing R] {X Z : Scheme.{0}}

theorem res_constFn (p : X ⟶ Sp K) {U V : X.Opens} (h : V ≤ U) (a : K) :
    (X.presheaf.map (homOfLE h).op).hom (constFn p U a) = constFn p V a := by
  exact congrArg (fun q : Γ(Sp K, ⊤) ⟶ Γ(X, V) => q.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))
    (p.appLE_map (U := ⊤) (V := U) le_top (homOfLE h).op)

theorem valR_constFn (p : X ⟶ Sp K) (f : K →+* R) (q : Sp R ⟶ X) (hq : q ≫ p = spMap f) (U : X.Opens)
    (h : ⊤ ≤ q ⁻¹ᵁ U) (a : K) : valR q U (constFn p U a) = f a := by
  refine (HolHom.valR_appLE q p ⊤ U le_top _ h).trans ?_
  rw [hq, ← Category.comp_id (spMap f),
    HolHom.valR_spMap f (𝟙 _) ⊤ le_rfl, HolHom.valR_eq _ _ le_rfl]
  congr 1
  exact congrArg (fun g : CommRingCat.of K ⟶ CommRingCat.of K => g.hom a)
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv_hom_id

def subComb (p : X ⟶ Sp K) {M : LB X} (s : M.Sec) {n : ℕ} (r : Fin n → K) (σ : Fin n → M.Sec) : M.Sec where
  f j := s.f j - ∑ i, constFn p _ (r i) * (σ i).f j
  compat j k := by
    rw [map_sub, map_sub, map_sum, map_sum, mul_sub, s.compat j k, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, res_constFn, res_constFn, (σ i).compat j k]
    ring

theorem valR_subComb (p : X ⟶ Sp K) {M : LB X} (s : M.Sec) {n : ℕ} (r : Fin n → K) (σ : Fin n → M.Sec)
    (f : K →+* R) (q : Sp R ⟶ X) (hq : q ≫ p = spMap f) (j : M.ι) (h : ⊤ ≤ q ⁻¹ᵁ M.U j) :
    valR q _ ((subComb p s r σ).f j) = valR q _ (s.f j) - ∑ i, f (r i) * valR q _ ((σ i).f j) := by
  simp only [← valR_constFn p f q hq _ h, HolHom.valR_eq _ _ h, subComb, map_sub, map_sum, map_mul]

theorem sval_subComb {L : LB Z} {π : X ⟶ Z} {m : ℕ} (p : X ⟶ Sp K) (s : SecP L π m) {n : ℕ} (r : Fin n → K)
    (σ : Fin n → SecP L π m) (f : K →+* R) (q : Sp R ⟶ X) (hq : q ≫ p = spMap f) (j : L.ι)
    (h : ⊤ ≤ (q ≫ π) ⁻¹ᵁ L.U j) :
    ArcPts.sval (subComb p s r σ : SecP L π m) q j = ArcPts.sval s q j - ∑ i, f (r i) * ArcPts.sval (σ i) q j := by
  have hw : ⊤ ≤ q ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => π) (fun _ => j) :=
    fun z hz => Set.mem_iInter.2 fun _ => h hz
  exact valR_subComb p s r σ f q hq (fun _ => j) hw

theorem sval_eq_zero {L : LB Z} {π : X ⟶ Z} {m : ℕ} (s : SecP L π m) (hs : ∀ i, s.f i = 0) (q : Sp R ⟶ X) (j : L.ι) :
    ArcPts.sval s q j = 0 := by
  refine (congrArg (valR q _) (hs fun _ => j)).trans ?_
  by_cases h : ⊤ ≤ q ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => π) (fun _ => j)
  · exact (HolHom.valR_eq q _ h 0).trans (map_zero _)
  · exact dif_neg h

end SecValue

theorem sval_eq_sum_of_hasVal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (S : Scheme.{0}) (A : AnArc (𝓞 E)) (t : SAB H S) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A t y) (j : ℕ) [NeZero j] (s : SecP t.PP.L (pullback.fst t.G.hom y) j) (n : ℕ) (r : Fin n → ℂ⸨X⸩) (α : Fin n → A.X) (th : Fin n → (Fin A.gB → ℂ) → ℂ), (∀ i, th i ∈ A.Theta j (α i)) → (∀ v, HasVal s (fib (Φ.x v)) (Φ.τ v) (∑ i, r i * A.FSum j (α i) (th i) v)) → ∀ (R : Type) [CommRing R] (f : ℂ⸨X⸩ →+* R) (q : Sp R ⟶ pullback t.G.hom y), q ≫ pullback.snd _ _ = spMap f → ∀ jj, ⊤ ≤ (q ≫ pullback.fst _ _) ⁻¹ᵁ t.PP.L.U jj → sval s q jj = ∑ i, f (r i) * sval (Φ.sig j (α i) (th i)) q jj := by
  intro E _ _ _ H _ S A t y Φ j _ s n r α th hth hs R _ f q hq jj hjj
  have h0 := Φ.sep j (SecValue.subComb (pullback.snd t.G.hom y) s r fun i => Φ.sig j (α i) (th i)) fun v k hk => by
    have hv : fib (Φ.x v) ≫ pullback.snd t.G.hom y = spMap (RingHom.id _) := by
      rw [fib, pullback.lift_snd]
      exact (Spec.map_id _).symm
    rw [SecValue.sval_subComb _ s r _ _ _ hv k hk, hs v k hk, Finset.sum_mul, zero_mul, sub_eq_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Φ.val j (α i) (th i) (hth i) v k hk, RingHom.id_apply, _root_.mul_assoc]
  have h1 := SecValue.sval_eq_zero _ h0 q jj
  rwa [SecValue.sval_subComb _ s r _ f q hq jj hjj, sub_eq_zero] at h1

end GlobalTheory.ArcPts
