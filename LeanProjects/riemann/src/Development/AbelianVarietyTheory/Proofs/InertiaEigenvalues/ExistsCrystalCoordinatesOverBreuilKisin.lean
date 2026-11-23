import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CrysExt

theorem exists_ext {A B M N R T ι : Type} [CommRing A] [CommRing B] [CommRing R] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) (J : T → B →+* R)
    (v : M →+ (T → ι → R)) (hv : ∀ (w : A) (x : M) τ i, v (w • x) τ i = J τ (f w) * v x τ i) :
    ∃ lam : N →+ (T → ι → R), (∀ (r : B) (y : N) τ i, lam (r • y) τ i = J τ r * lam y τ i) ∧
      ∀ x, lam (u x) = v x := by
  letI : Module B (T → ι → R) := Module.compHom (T → ι → R)
    (RingHom.pi fun τ => RingHom.pi fun _ : ι => J τ : B →+* (T → ι → R))
  let v' : M →ₛₗ[f] (T → ι → R) :=
    { toFun := v
      map_add' := v.map_add
      map_smul' := fun w x => funext fun τ => funext fun i => hv w x τ i }
  obtain ⟨lam, hlam, -⟩ := h (T → ι → R) v'
  exact ⟨lam.toAddMonoidHom, fun r y τ i => congrFun (congrFun (lam.map_smul r y) τ) i, hlam⟩

theorem frob_toAc {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
    [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (t : Wq l a →ₐ[ℤ_[l]] O)
    (x : (Wq l a)⟦X⟧) (τ : ZMod a) :
    frob K l (toAc t K x (τ - 1) : K⟦X⟧) = (toAc t K (frobS l a x) τ : K⟦X⟧) := by
  ext n
  have : coeff n (frobS l a x) = if l ∣ n then sigma l a (coeff (n / l) x) else 0 := by
    simp only [frobS, RingHom.comp_apply, coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coeff_expand]
    split_ifs <;> simp
  rw [coeff_frob, coeff_toAc, coeff_toAc, this]
  split_ifs
  · rw [emb_sigma]
  · simp

theorem exists_coord : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (J : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (g : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ τ (w : (Wq l a)⟦X⟧), J τ (p.f w) = g (toAc t K (frobS l a w) τ : K⟦X⟧)) → ∃ lam : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧), (∀ (r : PP.A) (y : EE.M PP) τ i, lam (r • y) τ i = J τ r * lam y τ i) ∧ ∀ x τ i, lam (EE.tr p x) τ i = g (frob K l (c x (τ - 1) i)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ EE c hc PP p J g hJ
  let v : EE.M (ϖ.prism a) →+ (ZMod a → ι → K⟦X⟧⟦X⟧) :=
    { toFun := fun x τ i => g (frob K l (c x (τ - 1) i))
      map_zero' := by ext1 τ; ext1 i; simp
      map_add' := fun x y => by ext1 τ; ext1 i; simp }
  obtain ⟨lam, h1, h2⟩ := exists_ext (EE.tr_bc p) J v (fun w x τ i => by
    change g (frob K l (c (w • x) (τ - 1) i)) = J τ (p.f w) * g (frob K l (c x (τ - 1) i))
    have e1 : c (w • x) (τ - 1) i = (toAc t K w (τ - 1) : K⟦X⟧) * c x (τ - 1) i :=
      congrFun (congrFun (hc w x) (τ - 1)) i
    have e2 := hJ τ w
    have e3 := frob_toAc (K := K) t w τ
    rw [e1, map_mul, map_mul]
    exact congrArg (· * _) ((congrArg g e3).trans e2.symm))
  exact ⟨lam, h1, fun x τ i => congrFun (congrFun (h2 x) τ) i⟩

end GlobalTheory.CrysExt
