import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStableComplBot
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefTransfer.Loc

theorem smul_conj_iff {A n : Type} [CommRing A] [Fintype n] [DecidableEq n] (f : A) {N N' : Matrix n n A}
    (h : N * N' = 1) (h' : N' * N = 1) (X : Matrix n n A) :
    f • (N * X * N' - 1) = N * X * N' - 1 ↔ f • (X - 1) = X - 1 := by
  have e : N * X * N' - 1 = N * (X - 1) * N' := by rw [mul_sub, sub_mul, mul_one, h]
  rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul]
  refine ⟨fun k => ?_, fun k => by rw [k]⟩
  have := congrArg (fun Y => N' * Y * N) k
  simpa only [← mul_assoc, h', one_mul, mul_assoc _ N' N, mul_one] using this

variable {D : D7}

theorem parts_ext {a b : Formalism.L2.Theta.AE D} (h1 : infPart D a = infPart D b) (h2 : finPart D a = finPart D b) :
    a = b := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have he1 : ∀ z, (e z).1 = infPart D z := fun z => (he z).1
  have he2 : ∀ z, (e z).2 = finPart D z := fun z => (he z).2
  apply e.injective
  exact Prod.ext (by rw [he1, he1, h1]) (by rw [he2, he2, h2])

theorem map_one_apply {A B n : Type} [CommRing A] [CommRing B] [DecidableEq n] (φ : A →+* B) (i j : n) :
    φ ((1 : Matrix n n A) i j) = (1 : Matrix n n B) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact map_one _
  · exact map_zero _

theorem suppF_iff_fin (V : HSp D) (f : Formalism.L2.Theta.AE D) {g : Formalism.L2.Theta.GA D V} (hg : g ∈ GfC V) :
    SuppF V f g ↔ finPart D f • (finMat D.sp.cm.sig V.gram g - 1) = finMat D.sp.cm.sig V.gram g - 1 := by
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  have e2 : finPart D ((Formalism.L2.Theta.mt V g - 1) i j) = (finMat D.sp.cm.sig V.gram g - 1) i j := by
    rw [Matrix.sub_apply, Matrix.sub_apply, RingHom.map_sub, map_one_apply]
    rfl
  have e1 : infPart D ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := by
    rw [Matrix.sub_apply, RingHom.map_sub, map_one_apply, sub_eq_zero]
    have : infHom V g = 1 := hg
    exact congrArg (fun m : GL (Fin V.rank) _ => m.1 i j) this
  rw [Matrix.smul_apply, smul_eq_mul, ← e2]
  refine ⟨fun h => by rw [← RingHom.map_mul, h], fun h => parts_ext ?_ ?_⟩
  · rw [RingHom.map_mul, e1, mul_zero]
  · rw [RingHom.map_mul, h]

theorem comp_of_isPrimeIdem {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : Formalism.L2.Theta.AE D} (h : IsPrimeIdem P e f)
    (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    (Q.under (𝓞 D.host.F) = P.under (𝓞 D.host.F) → GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D f) Q = 1) ∧
    (Q.under (𝓞 D.host.F) ≠ P.under (𝓞 D.host.F) → GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D f) Q = 0) := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨-, ε, ⟨α, rfl, h1, h0⟩, rfl⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ h
  have e : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E
      (finPart D (algebraMap _ (Formalism.L2.Theta.AE D) (pairA D.host.F 0 α))) Q =
      GlobalTheory.AdeleBaseChange.locMap D.host.F Q (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F (Q.under (𝓞 D.host.F)) α) := by
    rw [GlobalTheory.LFun.finAdEquiv_apply rfl]
    change GlobalTheory.LFun.toCompl rfl ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F (Q.under (𝓞 D.host.F)) α) ⊗ₜ[D.host.F]
      (1 : D.host.E)) = _
    rw [GlobalTheory.LFun.toCompl_tmul, map_one, mul_one]
    rfl
  rw [e]
  refine ⟨fun hQ => ?_, fun hQ => by rw [h0 _ hQ, map_zero]⟩
  have h2 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F (Q.under (𝓞 D.host.F)) α = 1 := by
    revert h1
    generalize P.under (𝓞 D.host.F) = v at hQ
    subst hQ
    exact id
  rw [h2, map_one]

theorem supp_iff_loc [IsCMField D.host.E] {n : ℕ} {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : Formalism.L2.Theta.AE D}
    (h : IsPrimeIdem P e f) (x : UA D.host.E n) :
    finPart D f • (((x : GL (Fin n) (Ad D.host.E)) : Matrix (Fin n) (Fin n) (Ad D.host.E)).map
        (fun a => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (pFin D.host.E a)) - 1) =
      ((x : GL (Fin n) (Ad D.host.E)) : Matrix (Fin n) (Fin n) (Ad D.host.E)).map
        (fun a => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (pFin D.host.E a)) - 1 ↔
    ∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) ≠ P.under (𝓞 D.host.F) → cLoc u x = 1 := by
  have key : ∀ i j (u : HeightOneSpectrum (𝓞 D.host.E)), GlobalTheory.LFun.finAdEquiv D.host.F D.host.E
      ((((x : GL (Fin n) (Ad D.host.E)) : Matrix (Fin n) (Fin n) (Ad D.host.E)).map
        (fun a => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (pFin D.host.E a)) - 1) i j) u =
      (cLoc u x).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j := by
    intro i j u
    rw [Matrix.sub_apply, map_sub, Matrix.map_apply, RingEquiv.apply_symm_apply,
      ← map_one_apply ((pLoc D.host.E u).comp (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).toRingHom)]
    rfl
  have ev : ∀ (a b : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) (u : HeightOneSpectrum (𝓞 D.host.E)),
      GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (a * b) u =
        GlobalTheory.LFun.finAdEquiv D.host.F D.host.E a u * GlobalTheory.LFun.finAdEquiv D.host.F D.host.E b u := by
    intro a b u
    rw [map_mul]; rfl
  constructor
  · intro k u hu
    refine Units.ext (Matrix.ext fun i j => ?_)
    have := congrArg (fun m => GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (m i j) u) k
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    rw [ev, (comp_of_isPrimeIdem h u).2 hu, zero_mul, key, eq_comm, sub_eq_zero] at this
    exact this
  · intro k
    refine Matrix.ext fun i j => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective
      (FiniteAdeleRing.ext _ fun u => ?_)
    rw [Matrix.smul_apply, smul_eq_mul, ev]
    by_cases hu : u.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)
    · rw [(comp_of_isPrimeIdem h u).1 hu, one_mul]
    · rw [key, k u hu, Units.val_one, sub_self, mul_zero]

theorem finMat_mul (V : HSp D) (g h : Formalism.L2.Theta.GA D V) :
    finMat D.sp.cm.sig V.gram (g * h) = finMat D.sp.cm.sig V.gram g * finMat D.sp.cm.sig V.gram h := by
  have := congrArg Units.val ((finHom V).map_mul g h)
  rw [Units.val_mul] at this
  exact this

theorem finMat_one (V : HSp D) : finMat D.sp.cm.sig V.gram (1 : Formalism.L2.Theta.GA D V) = 1 :=
  congrArg Units.val (finHom V).map_one

theorem map_mul_inv {K A n : Type} [Field K] [CommRing A] [Fintype n] [DecidableEq n] {T : Type} [FunLike T K A]
    [RingHomClass T K A] (φ : T) {M : Matrix n n K} (hu : IsUnit M.det) : M.map φ * M⁻¹.map φ = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _)]

theorem locU_iff : ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (j : UA D.host.E V.rank ≃ₜ* Formalism.L2.Theta.GA D V) (h₀ : Formalism.L2.Theta.GA D V)
    (M : Matrix (Fin V.rank) (Fin V.rank) D.host.E),
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * M = 1 → h₀ ∈ GfC V → (∀ x, x ∈ finU D.host.E V.rank ↔ j x ∈ GfC V) →
    (∀ x, finMat D.sp.cm.sig V.gram (j x) =
      M.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) *
      ((x : GL (Fin V.rank) (Ad D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (Ad D.host.E)).map
        (fun a => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (pFin D.host.E a)) *
      M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) →
    (∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
      IntVec (Matrix.mulVec (M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (Matrix.mulVec (finMat D.sp.cm.sig V.gram h₀) y))) →
    (∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ e f, IsPrimeIdem P e f) ∧ (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, IsPrimeIdem P e f → ∀ x,
      x ∈ locU V.rank P ↔ cj j h₀ x ∈ GfC V ∧ SuppF V f (cj j h₀ x)) := by
  intro D _ V j h₀ M hM hh hfin hmat _
  refine ⟨fun P => ?_, fun P e f h x => ?_⟩
  · obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
    exact GlobalTheory.IdemSupport.exists_isPrimeIdem hΦ P
  have hu : IsUnit M.det := Matrix.isUnit_det_of_left_inverse hM
  have hG : cj j h₀ x ∈ GfC V ↔ x ∈ finU D.host.E V.rank := by
    rw [hfin, cj_apply, Subgroup.mul_mem_cancel_right _ hh, Subgroup.mul_mem_cancel_left _ (inv_mem hh)]
  have hL : x ∈ locU V.rank P ↔ x ∈ finU D.host.E V.rank ∧ ∀ u : HeightOneSpectrum (𝓞 D.host.E),
      u.under (𝓞 D.host.F) ≠ P.under (𝓞 D.host.F) → cLoc u x = 1 := by
    simp only [locU, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker]
  rw [hL, ← hG]
  refine and_congr_right fun hx => ?_
  have m1 := map_mul_inv (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F]
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) hu
  have m2 := mul_eq_one_comm.1 m1
  have e1 : finMat D.sp.cm.sig V.gram (cj j h₀ x) =
      finMat D.sp.cm.sig V.gram h₀⁻¹ * finMat D.sp.cm.sig V.gram (j x) * finMat D.sp.cm.sig V.gram h₀ := by
    rw [cj_apply, finMat_mul, finMat_mul]
  have k1 : finMat D.sp.cm.sig V.gram h₀⁻¹ * finMat D.sp.cm.sig V.gram h₀ = 1 := by
    rw [← finMat_mul, inv_mul_cancel, finMat_one]
  refine ((suppF_iff_fin V f hx).trans ?_).symm
  rw [e1]
  refine (smul_conj_iff _ k1 (mul_eq_one_comm.1 k1) _).trans ?_
  rw [hmat]
  exact (smul_conj_iff _ m1 m2 _).trans (supp_iff_loc h x)

end GlobalTheory.DefTransfer.Loc
