import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentPreservesLatticeHatStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.HeckeTrans

section Abstract

variable {R : Type} [CommRing R] {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem mulVec_mem (S : Subring R) (u : Matrix m m S) (x : m → R) (hx : ∀ i, x i ∈ S) (i : m) :
    (u.map S.subtype).mulVec x i ∈ S := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  exact S.sum_mem fun k _ => S.mul_mem (u i k).2 (hx k)

theorem frame_inv (S : Subring R) (β : GL n R) (β' : GL m R) (c : n ≃ m) (U : GL m R) (u u' : Matrix m m S)
    (hu : U.val = u.map S.subtype) (hu' : (U⁻¹).val = u'.map S.subtype) (j : Matrix m n R)
    (hj : j * β.val = (β' * U).val.submatrix id c) :
    (∃ j' : Matrix n m R, j * j' = 1 ∧ j' * j = 1) ∧
      ∀ x : n → R, (∀ i, (β⁻¹).val.mulVec x i ∈ S) ↔ ∀ i, (β'⁻¹).val.mulVec (j.mulVec x) i ∈ S := by
  have hj2 : j = (β' * U).val.submatrix id c * (β⁻¹).val := by
    rw [← hj, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  refine ⟨⟨β.val * ((β' * U)⁻¹).val.submatrix c id, ?_, ?_⟩, fun x => ?_⟩
  · rw [← Matrix.mul_assoc, hj, Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_id_id]
  · have h1 : ((β' * U)⁻¹).val.submatrix c id * (β' * U).val.submatrix id c = 1 := by
      have := Matrix.submatrix_mul_equiv ((β' * U)⁻¹).val (β' * U).val c (Equiv.refl m) c
      rw [Units.inv_mul, Matrix.submatrix_one_equiv] at this
      exact this
    rw [hj2, Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.submatrix _ _ _), h1, Matrix.one_mul, Units.mul_inv]
  · have h1 : j.mulVec x = (β' * U).val.mulVec ((β⁻¹).val.mulVec x ∘ c.symm) := by
      rw [hj2, ← Matrix.mulVec_mulVec, Matrix.submatrix_mulVec_equiv]
      rfl
    have h2 : (β'⁻¹).val.mulVec (j.mulVec x) = U.val.mulVec ((β⁻¹).val.mulVec x ∘ c.symm) := by
      rw [h1, Matrix.mulVec_mulVec, Units.val_mul, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [h2]
    constructor
    · intro h i
      rw [hu]
      exact mulVec_mem S u _ (fun k => h _) i
    · intro h i
      have h3 := mulVec_mem S u' _ h (c i)
      rw [← hu', Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Function.comp_apply, Equiv.symm_apply_apply] at h3
      exact h3

variable {f : R} {J : Matrix m n R} {J' : Matrix n m R} {M : Matrix n n R} {M' : Matrix m m R}

omit [DecidableEq n] in
theorem conj_eq (h1 : J * J' = 1) (hc : M' * J = J * M) : M' = J * M * J' := by
  rw [← hc, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem conj_inv (h1 : J * J' = 1) (h2 : J' * J = 1) (hc : M' * J = J * M) : M * J' = J' * M' := by
  rw [conj_eq h1 hc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem supp_conj (h1 : J * J' = 1) (hc : M' * J = J * M) (hs : f • (M - 1) = M - 1) : f • (M' - 1) = M' - 1 := by
  have hs2 : M' - 1 = J * (M - 1) * J' := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1, ← conj_eq h1 hc]
  rw [hs2, ← Matrix.smul_mul, ← Matrix.mul_smul, hs]

theorem det_conj (h1 : J * J' = 1) (h2 : J' * J = 1) (hc : M' * J = J * M) : M'.det = M.det := by
  rw [conj_eq h1 hc]
  exact Matrix.det_conj_of_mul_eq_one h1 h2

variable {L : AddSubgroup (n → R)} {L' : AddSubgroup (m → R)}

omit [DecidableEq n] in
theorem lat_inv (h1 : J * J' = 1) (hL : ∀ y, f • y ∈ L ↔ f • J.mulVec y ∈ L') (y : m → R) :
    f • y ∈ L' ↔ f • J'.mulVec y ∈ L := by
  rw [hL, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

omit [DecidableEq n] in
theorem stab_conj (hf : f * f = f) (h1 : J * J' = 1) (hc : M' * J = J * M) (hL : ∀ y, f • y ∈ L ↔ f • J.mulVec y ∈ L')
    (loc' : ∀ y ∈ L', f • y ∈ L') (ha : ∀ y ∈ L, f • M.mulVec y ∈ L) : ∀ y ∈ L', f • M'.mulVec y ∈ L' := by
  intro y hy
  have h3 := ha _ ((lat_inv h1 hL y).1 (loc' y hy))
  rw [hL, Matrix.mulVec_smul, Matrix.mulVec_smul, smul_smul, hf, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    ← conj_eq h1 hc] at h3
  exact h3

omit [DecidableEq n] in
theorem cont_conj {p : R} (hf : f * f = f) (h1 : J * J' = 1) (hc : M' * J = J * M) (hL : ∀ y, f • y ∈ L ↔ f • J.mulVec y ∈ L')
    (loc : ∀ y ∈ L, f • y ∈ L) (loc' : ∀ y ∈ L', f • y ∈ L') (hb : ∀ y ∈ L, ∃ z ∈ L, f • p • y = f • M.mulVec z) :
    ∀ y ∈ L', ∃ z ∈ L', f • p • y = f • M'.mulVec z := by
  intro y hy
  obtain ⟨z, hz, h3⟩ := hb _ ((lat_inv h1 hL y).1 (loc' y hy))
  refine ⟨f • J.mulVec z, (hL z).1 (loc z hz), ?_⟩
  have h4 := congrArg J.mulVec h3
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, h1,
    Matrix.one_mulVec, Matrix.mulVec_mulVec, ← hc, smul_comm p, smul_smul, hf] at h4
  rw [h4, Matrix.mulVec_smul, smul_smul, hf, Matrix.mulVec_mulVec]

variable {R' : Type} [CommRing R']

omit [Fintype n] in
theorem supp_map_iff (φ : R' →+* R) (g : R') (A : Matrix n n R') :
    φ g • (A.map φ - 1) = A.map φ - 1 ↔ ∀ i j, φ (g * (A - 1) i j) = φ ((A - 1) i j) := by
  have h : ∀ i j, φ ((A - 1) i j) = (A.map φ - 1) i j := by
    intro i j
    rw [← Matrix.map_one φ φ.map_zero φ.map_one]
    simp only [Matrix.sub_apply, Matrix.map_apply, map_sub]
  simp only [map_mul, h]
  rw [← Matrix.ext_iff]
  rfl

omit [DecidableEq m] in
theorem map_mul_one (φ : R' →+* R) {A : Matrix n m R'} {B : Matrix m n R'} (h : A * B = 1) : A.map φ * B.map φ = 1 := by
  rw [← Matrix.map_mul, h, Matrix.map_one _ φ.map_zero φ.map_one]

omit [DecidableEq m] [DecidableEq n] in
theorem map_conj (φ : R' →+* R) {A : Matrix m m R'} {B : Matrix m n R'} {C : Matrix n n R'} (h : A * B = B * C) :
    A.map φ * B.map φ = B.map φ * C.map φ := by
  rw [← Matrix.map_mul, ← Matrix.map_mul, h]

omit [DecidableEq m] [DecidableEq n] [Fintype m] in
theorem mulVec_map_inv (φ : R' →+* R) (ψ : R →+* R') (h : ∀ x, ψ (φ x) = x) (j : Matrix m n R') (y : n → R) :
    (j.mulVec fun a => ψ (f * y a)) = fun a => ψ (f * (j.map φ).mulVec y a) := by
  funext a
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.mul_sum, map_sum, map_mul, h]
  exact Finset.sum_congr rfl fun b _ => mul_left_comm _ _ _

theorem map_mul_det (φ : R' →+* R) (e : R') (A : Matrix m m R') (B : Matrix n n R') (h : (A.map φ).det = (B.map φ).det) :
    φ (e * A.det) = φ (e * B.det) := by
  rw [map_mul, map_mul, RingHom.map_det, RingHom.map_det]
  exact congrArg (φ e * ·) h

end Abstract

variable {D : D7}

theorem finMat_eq (V : HSp D) (g : GA D V) : finMat D.sp.cm.sig V.gram g = (mt V g).map (finPart D) := rfl

theorem inf_eq {V : HSp D} {g : GA D V} (hg : g ∈ GfC V) : (mt V g).map (infPart D) = 1 :=
  congrArg Units.val (MonoidHom.mem_ker.1 hg)

theorem idem_det {e : Formalism.L2.Theta.AE D} (he : IsSplitIdem D e) {m n : ℕ} (A : Matrix (Fin m) (Fin m) (Formalism.L2.Theta.AE D))
    (B : Matrix (Fin n) (Fin n) (Formalism.L2.Theta.AE D)) (h : (A.map (finPart D)).det = (B.map (finPart D)).det) :
    e * A.det = e * B.det := by
  refine GlobalTheory.SplitScalar.adele_ext ?_ (map_mul_det (finPart D) e A B h)
  simp only [RingHom.map_mul, GlobalTheory.SplitScalar.infPart_splitIdem he, zero_mul]

theorem suppAt_iff (e : Formalism.L2.Theta.AE D) {V : HSp D} {α : GA D V} (hα : α ∈ GfC V) :
    SuppAt e V α ↔ finPart D (e + cA D e) • (finMat D.sp.cm.sig V.gram α - 1) = finMat D.sp.cm.sig V.gram α - 1 := by
  rw [finMat_eq, supp_map_iff]
  refine ⟨fun hs i j => congrArg (finPart D) (hs i j), fun hs i j => ?_⟩
  have hs4 := (supp_map_iff (infPart D) (e + cA D e) (mt V α)).1 (by rw [inf_eq hα, sub_self, smul_zero])
  exact GlobalTheory.SplitScalar.adele_ext (hs4 i j) (hs i j)

theorem transfer {V V' : HSp D} {e : Formalism.L2.Theta.AE D} (he : IsSplitIdem D e)
    (J : Matrix (Fin V'.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))
    (J' : Matrix (Fin V.rank) (Fin V'.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))
    (h1 : HMul.hMul J J' = 1) (h2 : HMul.hMul J' J = 1) {α : GA D V} {α' : GA D V'} (hα' : α' ∈ GfC V')
    (hc : HMul.hMul (finMat D.sp.cm.sig V'.gram α') J = HMul.hMul J (finMat D.sp.cm.sig V.gram α))
    (hL : ∀ y, finPart D e • y ∈ Formalism.L2.NTheta.LamHat V ↔ finPart D e • J.mulVec y ∈ Formalism.L2.NTheta.LamHat V')
    (loc : ∀ y ∈ Formalism.L2.NTheta.LamHat V, finPart D e • y ∈ Formalism.L2.NTheta.LamHat V)
    (loc' : ∀ y ∈ Formalism.L2.NTheta.LamHat V', finPart D e • y ∈ Formalism.L2.NTheta.LamHat V')
    {ϖ : D.host.E} {k : ℕ} (h : Formalism.L2.NTheta.IsHeckeElt V e ϖ k α) : Formalism.L2.NTheta.IsHeckeElt V' e ϖ k α' := by
  obtain ⟨hα, hs, ha, hb, u, u', hu, hu', huu, hd⟩ := h
  have hf : finPart D e * finPart D e = finPart D e := by rw [← RingHom.map_mul, he.1]
  refine ⟨hα', ?_, stab_conj hf h1 hc hL loc' ha, cont_conj hf h1 hc hL loc loc' hb, u, u', hu, hu', huu, ?_⟩
  · exact (suppAt_iff e hα').2 (supp_conj h1 hc ((suppAt_iff e hα).1 hs))
  · exact (idem_det he _ _ (det_conj h1 h2 hc)).trans hd

def unswap (D : D7) : EAf D →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).symm.toAlgHom.toRingHom

theorem unswap_swap (x) : unswap D (swapAE D x) = x :=
  (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).symm_apply_apply x

theorem swap_unswap (x) : swapAE D (unswap D x) = x :=
  (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).apply_symm_apply x

theorem finE_unswap (V : HSp D) (g : GA D V) : (finE V g).val.map (unswap D) = finMat D.sp.cm.sig V.gram g := by
  ext i j
  exact unswap_swap _

theorem isHeckeAt_iff : ∀ {D : D7} (V V' : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (β' : GL (Fin V'.rank) (EAf D)) (Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)) (N' : ℕ) (Pg : Finset (Pl D.host.E)) (j : Matrix (Fin V'.rank) (Fin V.rank) (EAf D)) (Φ : GfC V ≃ₜ* GfC V') (PP : Pl D.host.E), IsFinIso V V' β β' Pg j Φ → IsBaseFrame V β Λ N → IsBaseFrame V' β' Λ' N' → ((N : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal → ((N' : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal → ∀ k (α : GfC V), IsHeckeAt V PP k α ↔ IsHeckeAt V' PP k (Φ α) := by
  intro D V V' β Λ N β' Λ' N' Pg j Φ PP hI hB hB' hN hN' k α
  obtain ⟨hr, u, hu, -⟩ := hI.frame
  obtain ⟨⟨j', h1, h2⟩, hlat⟩ := frame_inv (Formalism.L2.Herm.intAf D.host.F D.host.E) β β' (finCongr hr)
    (intGL D.host.F D.host.E V'.rank u) u.val (u⁻¹).val rfl rfl j hu
  have h1' := map_mul_one (unswap D) h1
  have h2' := map_mul_one (unswap D) h2
  have hc := map_conj (unswap D) (hI.conj α)
  rw [finE_unswap, finE_unswap] at hc
  have hc' := conj_inv h1' h2' hc
  have hL : ∀ e : Formalism.L2.Theta.AE D, Formalism.L2.NTheta.IsIdemAt e PP → ∀ y, finPart D e • y ∈ Formalism.L2.NTheta.LamHat V ↔
      finPart D e • (j.map (unswap D)).mulVec y ∈ Formalism.L2.NTheta.LamHat V' := by
    intro e he y
    refine ((GlobalTheory.T.idempotent_preserves_lattice_hat V β Λ N PP e hB hN he y).2.trans (hlat _)).trans
      (Iff.trans ?_ (GlobalTheory.T.idempotent_preserves_lattice_hat V' β' Λ' N' PP e hB' hN' he _).2.symm)
    rw [mulVec_map_inv (unswap D) (swapAE D) swap_unswap]
  constructor
  · rintro ⟨e, ϖ, he, hϖ, hϖ2, h⟩
    exact ⟨e, ϖ, he, hϖ, hϖ2, transfer he.1 _ _ h1' h2' (Φ α).2 hc (hL e he)
      (fun y => (GlobalTheory.T.idempotent_preserves_lattice_hat V β Λ N PP e hB hN he y).1) (fun y => (GlobalTheory.T.idempotent_preserves_lattice_hat V' β' Λ' N' PP e hB' hN' he y).1) h⟩
  · rintro ⟨e, ϖ, he, hϖ, hϖ2, h⟩
    exact ⟨e, ϖ, he, hϖ, hϖ2, transfer he.1 _ _ h2' h1' α.2 hc' (lat_inv h1' (hL e he))
      (fun y => (GlobalTheory.T.idempotent_preserves_lattice_hat V' β' Λ' N' PP e hB' hN' he y).1) (fun y => (GlobalTheory.T.idempotent_preserves_lattice_hat V β Λ N PP e hB hN he y).1) h⟩

end GlobalTheory.HeckeTrans

end
