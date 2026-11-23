import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenFinLocE
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenFinSt

noncomputable section

open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta GlobalTheory.AdelicU GlobalTheory.StdUnn IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GenFinLocHf

open PositivityTheory.Rg.Sw.Glob.GenFinLocAH

theorem locRing (hF : LocRedField) (hS : LocRedSplit) {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R)
    (hσ : ∀ a, σ (σ a) = a) (𝔪 : Ideal R) (h𝔪 : 𝔪.IsMaximal)
    (horb : ∀ 𝔫 : Ideal R, 𝔫.IsMaximal → 𝔫 = 𝔪 ∨ 𝔫 = 𝔪.comap σ)
    (g : Matrix (Fin (n + n)) (Fin (n + n)) R) (hg : Uni σ g) (hgu : IsUnit g.det) :
    ∃ (a : Matrix (Fin n) (Fin n) R) (I : Finset (Fin n)), IsUnit a.det ∧
      IsUnit (blkDm (g * GlobalTheory.StdUnn.blk4 a 0 0 (Formalism.UG.cT σ a)⁻¹ * wIm I)).det := by
  by_cases hfix : 𝔪.comap σ = 𝔪
  · obtain ⟨I, hI⟩ := caseA hF σ hσ 𝔪 hfix horb g hg hgu
    refine ⟨1, I, by simp, ?_⟩
    have e : GlobalTheory.StdUnn.blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 (Formalism.UG.cT σ 1)⁻¹ = 1 := by
      rw [Formalism.UG.cT_one, inv_one, block_matrix_one]
    rwa [e, Matrix.mul_one]
  · exact caseB hS σ hσ 𝔪 hfix horb g hg hgu

variable {D : D7} {n : ℕ}

theorem compAt_eq (v : GlobalTheory.FinPl.Pl D) : GlobalTheory.FinPl.compAt D v = compFin D.host.F D.host.E v := by
  apply RingHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | tmul a e => rfl
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, hx, hy]

theorem proj_mat (k : G D n) (v : GlobalTheory.FinPl.Pl D) :
    ((matHom _ D.sp.cm.sig (Jst D n) (proj D.sp.cm.sig (Jst D n) v k)).1 :
      Matrix (Fin (n + n)) (Fin (n + n)) (Ev D v)) = (mat k).map (GlobalTheory.FinPl.compAt D v) := by
  rw [compAt_eq]; rfl

theorem int_of_K (k : G D n) (hk : k ∈ K D n) (v : GlobalTheory.FinPl.Pl D) (i j : Fin (n + n)) :
    (mat k).map (GlobalTheory.FinPl.compAt D v) i j ∈ intLoc D.host.F D.host.E v := by
  have hk' : k ∈ levelAll D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) 1 := hk
  have h := (mem_levelAll.1 hk').1 v
  have hy : (Pi.single j 1 : Fin (n + n) → Ev D v) ∈ latLoc D.host.F (stdLattice D.host.E (n + n)) v := by
    rw [mem_latLoc_stdLattice]
    intro i'
    by_cases hij : i' = j
    · subst hij; simp only [Pi.single_eq_same]; exact one_mem _
    · simp only [Pi.single_eq_of_ne hij]; exact zero_mem _
  have h2 := (mem_stabLoc.1 h _).1 hy
  rw [mem_latLoc_stdLattice] at h2
  have h3 := h2 i
  rw [proj_mat, Matrix.mulVec_single_one] at h3
  exact h3

end PositivityTheory.Rg.Sw.Glob.GenFinLocHf

namespace PositivityTheory.Rg.Sw.Glob.GenFinLocHf

open PositivityTheory.Rg.Sw.Glob.GenFinLocAH

variable {D : D7} {n : ℕ}

theorem sig_apply (x : D.host.E) : D.sp.cm.sig x = star x := rfl

theorem sig_sig (x : D.host.E) : D.sp.cm.sig (D.sp.cm.sig x) = x := by
  rw [sig_apply, sig_apply, star_star]

theorem sig_fix (x : D.host.E) : D.sp.cm.sig x = x ↔ x ∈ (algebraMap D.host.F D.host.E).range := by
  rw [sig_apply]; exact D.sp.cm.fixed x

theorem compFin_sigR (v : GlobalTheory.FinPl.Pl D) (x : AE D) :
    compFin D.host.F D.host.E v (sigR (AF D.host.F) D.sp.cm.sig x) = sigR (Fv D.host.F v) D.sp.cm.sig (compFin D.host.F D.host.E v x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]
  | tmul a e => rfl
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, RingHom.map_add, hx, hy]

theorem JR_Jst_map (v : GlobalTheory.FinPl.Pl D) :
    (JR (AF D.host.F) (Jst D n)).map (compFin D.host.F D.host.E v) = J2 (Ev D v) n := by
  have h1 : (JR (AF D.host.F) (Jst D n)).map (compFin D.host.F D.host.E v) = (Jst D n).map (inclR (Fv D.host.F v)) := by
    ext i j
    simp only [JR, Matrix.map_apply]
    show compFin D.host.F D.host.E v ((1 : AF D.host.F) ⊗ₜ[D.host.F] _) = (1 : Fv D.host.F v) ⊗ₜ[D.host.F] _
    simp [compFin]
  rw [h1, Jst, block_matrix_map]
  unfold J2
  rw [Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_neg _ (map_neg _),
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem uni_comp (k : G D n) (v : GlobalTheory.FinPl.Pl D) :
    Formalism.UG.cT (sigR (Fv D.host.F v) D.sp.cm.sig) ((mat k).map (GlobalTheory.FinPl.compAt D v)) * J2 (Ev D v) n *
      (mat k).map (GlobalTheory.FinPl.compAt D v) = J2 (Ev D v) n := by
  have hk : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (mat k) * JR (AF D.host.F) (Jst D n) * mat k =
      JR (AF D.host.F) (Jst D n) := k.2
  have e := congrArg (fun M => M.map (compFin D.host.F D.host.E v)) hk
  simp only [Matrix.map_mul] at e
  rw [cT_map _ _ _ (compFin_sigR v), JR_Jst_map] at e
  rw [compAt_eq]; exact e

end PositivityTheory.Rg.Sw.Glob.GenFinLocHf

namespace PositivityTheory.Rg.Sw.Glob.GenFinLocHf

open PositivityTheory.Rg.Sw.Glob.GenFinLocAH

theorem unit_sub {S : Type} [CommRing S] (O : Subring S) (z : O) (hz : IsUnit z) : (z : S) ∈ O ∧ ∃ z' ∈ O, (z : S) * z' = 1 := by
  obtain ⟨u, rfl⟩ := hz
  exact ⟨(u : O).2, _, (u⁻¹ : Oˣ).1.2, congrArg Subtype.val u.mul_inv⟩

theorem locSub (hF : LocRedField) (hS : LocRedSplit) {S : Type} [CommRing S] {n : ℕ} (O : Subring S) (τ : S →+* S) (σ : O →+* O)
    (hσ : ∀ a, σ (σ a) = a) (hc : ∀ x, O.subtype (σ x) = τ (O.subtype x)) (𝔪 : Ideal O) (h𝔪 : 𝔪.IsMaximal)
    (horb : ∀ 𝔫 : Ideal O, 𝔫.IsMaximal → 𝔫 = 𝔪 ∨ 𝔫 = 𝔪.comap σ) (M M' : Matrix (Fin (n + n)) (Fin (n + n)) S)
    (hM : ∀ i j, M i j ∈ O) (hM' : ∀ i j, M' i j ∈ O) (hMM : M * M' = 1) (hU : Formalism.UG.cT τ M * J2 S n * M = J2 S n) :
    ∃ (a : Matrix (Fin n) (Fin n) S) (I : Finset (Fin n)), (∀ i j, a i j ∈ O) ∧ (a.det ∈ O ∧ ∃ z' ∈ O, a.det * z' = 1) ∧
      ((blkDm (M * GlobalTheory.StdUnn.blk4 a 0 0 ((a.map τ).transpose)⁻¹ * wIm I)).det ∈ O ∧
        ∃ z' ∈ O, (blkDm (M * GlobalTheory.StdUnn.blk4 a 0 0 ((a.map τ).transpose)⁻¹ * wIm I)).det * z' = 1) := by
  obtain ⟨g, rfl⟩ : ∃ g : Matrix (Fin (n + n)) (Fin (n + n)) O, g.map O.subtype = M :=
    ⟨Matrix.of fun i j => ⟨M i j, hM i j⟩, by ext i j; rfl⟩
  obtain ⟨g', rfl⟩ : ∃ g : Matrix (Fin (n + n)) (Fin (n + n)) O, g.map O.subtype = M' :=
    ⟨Matrix.of fun i j => ⟨M' i j, hM' i j⟩, by ext i j; rfl⟩
  have hinj : Function.Injective (fun M : Matrix (Fin (n + n)) (Fin (n + n)) O => M.map O.subtype) :=
    Matrix.map_injective Subtype.val_injective
  have hUni : Uni σ g := by
    apply hinj
    change (Formalism.UG.cT σ g * J2 O n * g).map O.subtype = (J2 O n).map O.subtype
    rw [Matrix.map_mul, Matrix.map_mul, cT_map _ _ _ hc, standard_symplectic_matrix_map]
    exact hU
  have hdet : IsUnit g.det := by
    have e : g * g' = 1 := by
      apply hinj
      show (g * g').map O.subtype = (1 : Matrix (Fin (n + n)) (Fin (n + n)) O).map O.subtype
      rw [Matrix.map_mul, hMM, Matrix.map_one _ (map_zero _) (map_one _)]
    have e' := congrArg Matrix.det e
    rw [Matrix.det_mul, Matrix.det_one] at e'
    exact ⟨⟨_, _, e', by rw [mul_comm]; exact e'⟩, rfl⟩
  obtain ⟨a, I, ha, hδ⟩ := locRing hF hS σ hσ 𝔪 h𝔪 horb g hUni hdet
  have hca : IsUnit (Formalism.UG.cT σ a).det := by rw [det_cT]; exact ha.map _
  refine ⟨a.map O.subtype, I, fun i j => (a i j).2, ?_, ?_⟩
  · rw [← det_map O.subtype a]; exact unit_sub O a.det ha
  · have e : blkDm (g.map O.subtype * GlobalTheory.StdUnn.blk4 (a.map O.subtype) 0 0 (((a.map O.subtype).map τ).transpose)⁻¹ * wIm I) =
        (blkDm (g * GlobalTheory.StdUnn.blk4 a 0 0 (Formalism.UG.cT σ a)⁻¹ * wIm I)).map O.subtype := by
      rw [blkDm_map, Matrix.map_mul, Matrix.map_mul, block_matrix_map, wIm_map, map_nonsing_inv O.subtype _ hca, cT_map _ _ _ hc a,
        Matrix.map_zero _ (map_zero O.subtype)]
      rfl
    rw [e, ← det_map O.subtype]
    exact unit_sub O _ hδ

end PositivityTheory.Rg.Sw.Glob.GenFinLocHf
