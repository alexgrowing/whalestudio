import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FracDescend

variable {p : ℕ} [Fact p.Prime] {R K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K]
  [Algebra R K] [IsFractionRing R K]

theorem bcTate_conv (G : PDivGroup p R) (t : G.Tate) (n : ℕ) :
    (toBaseChange R K (G.A n)).pts K (fun _ => rfl) ((bcTate K t).conv n) =
      ptsPush (G.A n) (Algebra.ofId R K) (t.conv n) :=
  ofConv_injective (AlgHom.ext fun a => by
    rw [SemiBialgHom.pts_apply, toBaseChange_apply]
    exact (bcTate_pt K t n 1 a).trans (one_mul _))

theorem bcTate_add (G : PDivGroup p R) (x y : G.Tate) :
    bcTate K (x + y) = bcTate K x + bcTate K y :=
  TateOver.ext_conv fun n => (toBaseChange_pts_bijective (R := R) K (A := G.A n) K fun _ => rfl).1 (by
    rw [TateOver.add_conv, map_mul, bcTate_conv, bcTate_conv, bcTate_conv, TateOver.add_conv, map_mul])

theorem bcTate_bijective (G : PDivGroup p R) : Function.Bijective (bcTate (G := G) K) := by
  have hi : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  refine ⟨fun x y h => TateOver.ext (funext fun n => AlgHom.ext fun a => hi ?_), fun y => ?_⟩
  · have := congrArg (fun z : (G.baseChange K).Tate => z.pt n (1 ⊗ₜ a)) h
    rw [bcTate_pt, bcTate_pt, _root_.one_mul, _root_.one_mul] at this
    exact this
  · let z : G.TateOver K := ⟨fun n => ((toBaseChange R K (G.A n)).pts K (fun _ => rfl) (y.conv n)).ofConv,
      fun n => AlgHom.ext fun a => by
        change y.pt (n + 1) (1 ⊗ₜ G.mulP n a) = y.pt n (1 ⊗ₜ a)
        rw [← y.pt_mulP n, baseChange_mulP, PDiv.bcMap_tmul]⟩
    obtain ⟨x, hx⟩ := (G.tatePush_bijective K).2 z
    refine ⟨x, TateOver.ext (funext fun n => Algebra.TensorProduct.ext (Subsingleton.elim _ _)
      (AlgHom.ext fun a => ?_))⟩
    have h := congrArg (fun w : G.TateOver K => w.pt n a) hx
    simp only [tatePush_pt] at h
    change (bcTate K x).pt n (1 ⊗ₜ a) = y.pt n (1 ⊗ₜ a)
    rw [bcTate_pt, _root_.one_mul]
    exact h

end GlobalTheory.FracDescend

namespace GlobalTheory.FracDescend

theorem mu_descend {p : ℕ} [Fact p.Prime] {R K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K]
    [Algebra R K] [IsFractionRing R K] (ε₀ : (PDivGroup.mu p K).Tate) :
    ∃ ε : (PDivGroup.mu p R).Tate, ∀ n, muRoot ε₀ n = algebraMap R K (muRoot ε n) := by
  let z : (PDivGroup.mu p R).TateOver K :=
    ⟨fun n => muPoint R (muRoot ε₀ n) (muRoot_pow_self ε₀ n), fun n => mu_algHom_ext (by
      rw [AlgHom.comp_apply]
      erw [mu_mulP_muT]
      rw [map_pow, muPoint_muT, muPoint_muT, muRoot_succ_pow])⟩
  obtain ⟨ε, hε⟩ := ((PDivGroup.mu p R).tatePush_bijective K).2 z
  refine ⟨ε, fun n => ?_⟩
  have h := congrArg (fun w : (PDivGroup.mu p R).TateOver K => w.pt n (muT R (p ^ n))) hε
  simp only [tatePush_pt, z, muPoint_muT] at h
  exact h.symm

theorem descend_tate_and_mu : ∀ (p : ℕ) [Fact p.Prime] (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] (GG : PDivGroup p R) (GG₀ : PDivGroup p K) (e : GG₀ ≅ GG.baseChange K) (L : Type) [AddCommGroup L] (ε₀ : (PDivGroup.mu p K).Tate) (τ₀ : L →+ GG₀.Tate), ∃ (ε : (PDivGroup.mu p R).Tate) (τ : L →+ GG.Tate), (∀ n, muRoot ε₀ n = algebraMap R K (muRoot ε n)) ∧ ∀ x, tateMap _ _ K e.hom (τ₀ x) = bcTate K (τ x) := by
  intro p _ R K _ _ _ _ _ _ GG GG₀ e L _ ε₀ τ₀
  obtain ⟨ε, hε⟩ := mu_descend (R := R) ε₀
  let E := AddEquiv.ofBijective (AddMonoidHom.mk' (bcTate (G := GG) K) (bcTate_add GG)) (bcTate_bijective GG)
  refine ⟨ε, (E.symm : (GG.baseChange K).Tate →+ GG.Tate).comp (((tateMap _ _ K e.hom).toAddMonoidHom).comp τ₀),
    hε, fun x => ?_⟩
  exact (E.apply_symm_apply _).symm

end GlobalTheory.FracDescend
