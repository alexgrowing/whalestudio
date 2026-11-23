import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.InclusionInjective
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.FiniteAdeleRingNontrivial
import Formalism.LocalToGlobal.HermitianForms.TiedTwGen

noncomputable section

namespace Formalism.MainNotions.G.ChF

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

set_option maxHeartbeats 1000000 in

theorem isLattice_of_hat (Lb Lc : Submodule (𝓞 E) (Fin n → E)) (hfin : Module.Finite (𝓞 E) Lb)
    (hspan : Submodule.span E (Lb : Set (Fin n → E)) = ⊤) (y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hy : ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Lc ↔
      (y⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Lb) :
    Submodule.IsLattice E Lc := by
  have hN := Formalism.UG.P.global_lattice_isLattice_holds F E (Fin n) Lb hfin hspan y
  have hle : Lc ≤ Formalism.UG.CS.globLat y Lb := fun z hz => (hy _).1 (Submodule.subset_span ⟨z, hz, rfl⟩)
  have hfg : Lc.FG := by
    have : IsNoetherian (𝓞 E) (Formalism.UG.CS.globLat y Lb) := isNoetherian_of_fg_of_noetherian _ hN.fg
    exact isNoetherian_submodule.1 this Lc hle
  refine ⟨hfg, ?_⟩
  by_contra hne
  obtain ⟨f, hf0, hfk⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  apply hf0
  set ι : E →+* E ⊗[F] FiniteAdeleRing (𝓞 F) F := inclE (F := F) (FiniteAdeleRing (𝓞 F) F) with hι
  set a : Fin n → E := fun i => f (fun j => if i = j then 1 else 0) with ha
  have hfa : ∀ x : Fin n → E, f x = ∑ i, a i * x i := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ f x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm]
  set aA : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F := fun i => ι (a i) with haA
  have hdot : ∀ z : Fin n → E, aA ⬝ᵥ (fun i => ι (z i)) = ι (f z) := by
    intro z
    rw [hfa, map_sum]
    exact Finset.sum_congr rfl fun i _ => (map_mul ι _ _).symm
  have c1 : ∀ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Lc, aA ⬝ᵥ x = 0 := by
    intro x hx
    unfold latS at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      have h0 : f z = 0 := hfk (Submodule.subset_span hz)
      exact (hdot z).trans (by rw [h0, map_zero])
    | zero => exact dotProduct_zero _
    | add x x' _ _ h1 h2 => rw [dotProduct_add, h1, h2, add_zero]
    | smul s x _ h1 =>
      rw [Subring.smul_def, dotProduct_smul, h1, smul_zero]
  have c2 : ∀ z ∈ Lb, (aA ᵥ* y.1) ⬝ᵥ (fun i => ι (z i)) = 0 := by
    intro z hz
    rw [← Matrix.dotProduct_mulVec]
    refine c1 _ ((hy _).2 ?_)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    exact Submodule.subset_span ⟨z, hz, rfl⟩
  have c3 : ∀ z : Fin n → E, (aA ᵥ* y.1) ⬝ᵥ (fun i => ι (z i)) = 0 := by
    intro z
    have hz : z ∈ Submodule.span E (Lb : Set (Fin n → E)) := by rw [hspan]; exact Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz => exact c2 z hz
    | zero =>
      have : (fun i => ι ((0 : Fin n → E) i)) = 0 := by funext i; exact map_zero ι
      rw [this, dotProduct_zero]
    | add z z' _ _ h1 h2 =>
      have : (fun i => ι ((z + z') i)) = (fun i => ι (z i)) + fun i => ι (z' i) := by funext i; exact map_add ι _ _
      rw [this, dotProduct_add, h1, h2, add_zero]
    | smul e z _ h1 =>
      have : (fun i => ι ((e • z) i)) = ι e • fun i => ι (z i) := by funext i; exact map_mul ι _ _
      rw [this, dotProduct_smul, h1, smul_zero]
  have c4 : aA ᵥ* y.1 = 0 := by
    funext j
    have h := c3 (Pi.single j 1)
    have e : (fun i => ι ((Pi.single j (1 : E) : Fin n → E) i)) = Pi.single j 1 := by
      funext i
      by_cases hij : i = j
      · subst hij
        rw [Pi.single_eq_same, Pi.single_eq_same, map_one]
      · rw [Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij, map_zero]
    rw [e, dotProduct_single, mul_one] at h
    exact h
  have c5 : aA = 0 := by
    have h := congrArg (fun r => r ᵥ* (y⁻¹).1) c4
    simp only [Matrix.vecMul_vecMul, Matrix.zero_vecMul] at h
    rwa [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one] at h
  have hnt : Nontrivial (FiniteAdeleRing (𝓞 F) F) := Formalism.L2.GlobalTheoryTheory.Br.finiteAdeleRing_nontrivial (F := F)
  have c6 : ∀ i, a i = 0 := fun i =>
    Formalism.UG.P.inclE_injective F E (FiniteAdeleRing (𝓞 F) F) ((congrFun c5 i).trans (map_zero ι).symm)
  refine LinearMap.ext fun x => ?_
  rw [hfa, LinearMap.zero_apply]
  exact Finset.sum_eq_zero fun i _ => by rw [c6 i, zero_mul]

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isLattice_chart {D : D7} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {i : ℕ} {hi : i ≤ D.R.m} {cl : Type}
    {stab : cl → Type} [∀ c, Group (stab c)] {lat : cl → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)}
    (K : LevelChart D T bad i hi stab lat) (c : cl) : Submodule.IsLattice D.host.E (lat c) :=
  isLattice_of_hat K.lev.Lb (lat c) K.lev.Lb_fin K.lev.Lb_span (K.y c).1 (K.y_lat c)

end Formalism.MainNotions.G.ChF

end
