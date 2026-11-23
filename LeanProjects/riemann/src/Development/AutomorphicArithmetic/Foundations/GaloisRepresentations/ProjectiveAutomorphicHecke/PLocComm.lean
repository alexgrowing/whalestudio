import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap.LocalCommutativity

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem rel (k : GUf E n) (u : Plc E) :
    ((comp (cj u) k).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) u))ᵀ * (comp u k).val =
      pLoc E u (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim k : AfQˣ) : AfQ)) •
        (1 : Matrix (Fin n) (Fin n) (u.adicCompletion E)) := by
  have h := mem_Sim.1 k.2
  have h2 := congrArg (RingHom.mapMatrix (pLoc E u)) h
  rw [map_mul] at h2
  refine h2.trans ?_
  ext i j
  by_cases hij : i = j <;> simp [hij, Matrix.one_apply, sim]

private theorem gu_ext {a b : GUf E n} (hs : sim a = sim b) (hc : ∀ u, comp u a = comp u b) : a = b := by
  refine Subtype.ext (Prod.ext (Units.ext (GlobalTheory.SplitPts.matAf_ext fun u => ?_)) hs)
  exact congrArg Units.val (hc u)

private theorem comm_scalar {R : Type} [CommRing R] (M X : Matrix (Fin n) (Fin n) R)
    (ho : ∀ i j, i ≠ j → M i j = 0) (hd : ∀ i j, M i i = M j j) : M * X = X * M := by
  have e : M = Matrix.diagonal (fun i => M i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, ho i j hij]
  ext i j
  rw [e, Matrix.diagonal_mul, Matrix.mul_diagonal, hd i j, mul_comm]

end UpperTheory.Gal.CertificateRingHomMap.LocalCommutativity

open UpperTheory.Gal.CertificateRingHomMap.LocalCommutativity in
theorem UpperTheory.Gal.CertificateRingHomMap.pLocComm_of :
    UpperTheory.Gal.CertificateRingHomMap.LocComm := by
  intro E _ _ _ n w hw
  obtain ⟨hne, hund, hover⟩ := GlobalTheory.SplitPts.over_split hw
  have hcc : cj (cj w) = w := GlobalTheory.SplitPts.conjSrc_conjSrc_cm w
  have hap : ∀ u, GlobalTheory.Cong.Apart u w ↔ u ≠ w ∧ u ≠ cj w := by
    intro u
    constructor
    · intro h
      exact ⟨fun e => h (by rw [e]), fun e => h (by rw [e]; exact hund)⟩
    · rintro ⟨h1, h2⟩ h
      rcases hover u h with e | e
      · exact h1 e
      · exact h2 e
  refine ⟨?_, hap, hne, ⟨w, hne.symm, hund.symm⟩, hcc, ?_⟩
  · intro k hk y
    refine gu_ext (by rw [map_mul, map_mul]; exact mul_comm _ _) fun u => ?_
    rw [map_mul, map_mul]
    by_cases h1 : u = w
    · subst h1
      rw [hk, one_mul, mul_one]
    by_cases h2 : u = cj w
    · subst h2
      have r := rel k w
      rw [hk, Units.val_one, Matrix.mul_one] at r
      have r' := congrArg Matrix.transpose r
      rw [Matrix.transpose_transpose, Matrix.transpose_smul, Matrix.transpose_one] at r'
      have hent : ∀ i j, conjLoc (GlobalTheory.SplitPts.conjE E) w ((comp (cj w) k).val i j) = _ :=
        fun i j => congrFun (congrFun r' i) j
      have hinj := (conjLoc (GlobalTheory.SplitPts.conjE E) w).injective
      refine Units.ext ?_
      rw [Units.val_mul, Units.val_mul]
      refine comm_scalar _ _ (fun i j hij => hinj ?_) (fun i j => hinj ?_)
      · rw [hent i j, map_zero]; simp [hij]
      · rw [hent i i, hent j j]; simp
    · rw [comp_loc_of_apart hw ((hap u).2 ⟨h1, h2⟩), mul_one, one_mul]
  · unfold locU
    rw [hund]
