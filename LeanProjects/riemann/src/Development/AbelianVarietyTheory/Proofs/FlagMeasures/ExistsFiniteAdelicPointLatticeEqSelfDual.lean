import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryMassLatticeEqGenusMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryOfUnimodularLatticesAtPlace
import Formalism.HermitianLattices.HermitianLatticesProofs.LocDual
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.SelfDualPoint

open Formalism.HermitianLatticesTheory Formalism.UG Formalism.UG.CS

theorem mem_genus {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hK : IsCMUnram K) (hs : h.IsSymm) (hn : h.Nondegenerate) {L L' : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hL' : Submodule.IsLattice K L') (hd : dual h L = L) (hd' : dual h L' = L') :
    L' ∈ genus h L := by
  have hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) :=
    fun r => ⟨RingOfIntegers.mapRingHom (starRingEnd K) r, rfl⟩
  have key : ∀ M : Submodule (𝓞 K) V, M.FG → dual h M = M → ∀ P : Ideal (𝓞 K), P.IsPrime →
      IsUnimodularAt h P M := fun M hM hdM P hP => by
    have a := (locDual (𝓞 K) K V h hs hstar M hM).1 P hP
    have b := a.2.trans a.1.symm
    rwa [hdM] at b
  exact ⟨hL', fun P hP => GlobalTheory.Mass.UnimodLoc.exists_isom_of_isUnimodularAt K V h hK hs hn L L' hL hL' P hP
    (key L hL.fg hd P hP.isPrime) (key L' hL'.fg hd' P hP.isPrime)⟩

theorem lamX_eq_globLat (I : AutInst) (xf : I.Gf) : lamX I (1, xf) = globLat xf.1 I.L := by
  have e : I.Lf = latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L := by
    unfold AutInst.Lf lamAf latS
    congr 1
    ext u
    exact ⟨fun ⟨x, hx⟩ => ⟨x, x.2, hx⟩, fun ⟨x, hx, hx'⟩ => ⟨⟨x, hx⟩, hx'⟩⟩
  unfold lamX
  rw [e]
  exact Submodule.span_eq (globLat xf.1 I.L)

theorem exists_lamX_eq : ∀ (I : AutInst) (Λ : Submodule (𝓞 I.E) (Fin I.n → I.E)), Submodule.IsLattice I.E Λ → (∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, Formalism.UG.hform (starRingEnd I.E) I.J y x ∈ (algebraMap (𝓞 I.E) I.E).range) → ∃ xf : I.Gf, lamX I (1, xf) = Λ := by
  intro I Λ hΛ hd
  have hs : ∀ e, (I.cm.sig : I.E →+* I.E) ((I.cm.sig : I.E →+* I.E) e) = e := fun e => star_star e
  have hfix : ∀ e : I.E, I.cm.sig e = e → ∃ a : I.F, algebraMap I.F I.E a = e := fun e he => (I.cm.fixed e).1 he
  let h : (Fin I.n → I.E) →ₗ⋆[I.E] (Fin I.n → I.E) →ₗ[I.E] I.E := formJ (I.cm.sig : I.E →+* I.E) hs I.J 1
  obtain ⟨hsym, hap⟩ := Formalism.UG.P.hermitian_form_symmetry_holds I.E _ hs (Fin I.n) I.J 1 (map_one _) I.J_herm
  replace hsym : h.IsSymm := hsym
  replace hap : ∀ x y, h x y = hform (starRingEnd I.E) I.J x y := fun x y => (hap x y).trans (one_mul _)
  have hr : ∀ y, (∀ x, h x y = 0) → y = 0 := fun y hy => by
    refine Matrix.eq_zero_of_mulVec_eq_zero I.J_det (funext fun i => ?_)
    have := hy (Pi.single i 1)
    rw [hap, hform, Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)] at this
    simpa [Matrix.mulVec, dotProduct] using this
  have hn : h.Nondegenerate := ⟨fun x hx => hr x fun y => by rw [← hsym.eq, hx, map_zero], hr⟩
  have hdual : ∀ M : Submodule (𝓞 I.E) (Fin I.n → I.E),
      (∀ x, x ∈ M ↔ ∀ y ∈ M, hform (starRingEnd I.E) I.J y x ∈ (algebraMap (𝓞 I.E) I.E).range) →
      dual h M = M := fun M hM => by
    ext x
    rw [dualBasic_mem_dual, hM x]
    simp only [hap, Submodule.mem_one, RingHom.mem_range]
  obtain ⟨g, hg, e⟩ := GlobalTheory.Mass.Genus.exists_globLat_eq (J := I.J) hs hfix (Module.Finite.iff_fg.2 I.L_fg)
    I.L_span Λ (mem_genus h I.cm.cmUnram hsym hn ⟨I.L_fg, I.L_span⟩ hΛ (hdual _ I.L_dual) (hdual _ hd))
  exact ⟨⟨g, hg⟩, (lamX_eq_globLat I _).trans e⟩

end GlobalTheory.SelfDualPoint
