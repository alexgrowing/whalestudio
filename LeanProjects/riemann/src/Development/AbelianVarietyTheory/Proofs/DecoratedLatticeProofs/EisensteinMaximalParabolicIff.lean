import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.DeterminantHeightFlags
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionIsotropicStabilizerArchimedean
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaDecompositionAdelic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalDecompositionNonsplitPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalDecompositionSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsConjStabilizersSelfDualLatticesUnramified
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddConjEqOneOfFormallyUnramified
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WittTheoremAdelicOneVector

open GlobalTheory GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.Doubling Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField GlobalTheory.EisLine GlobalTheory.Eis
  IsDedekindDomain TensorProduct
open Formalism.UG (cT UJ bc IsInertAt)

namespace GlobalTheory.EisMaxCompare

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField F] [NumberField E] in

theorem coord_map {ι : Type} [DecidableEq ι] (b : Module.Basis ι F E) {R R' : Type} [CommRing R] [Algebra F R]
    [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R') (x : R ⊗[F] E) (i : ι) :
    equivFinsuppOfBasisRight b (Algebra.TensorProduct.map f (AlgHom.id F E) x) i =
      f (equivFinsuppOfBasisRight b x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [equivFinsuppOfBasisRight_apply_tmul_apply]
  | add x y hx hy => simp [hx, hy]

omit [NumberField E] in

theorem tens_ext {x y : AF F ⊗[F] E} (hw : ∀ w, compInf F E w x = compInf F E w y)
    (hv : ∀ v, compFin F E v x = compFin F E v y) : x = y := by
  classical
  let b := Module.Basis.ofVectorSpace F E
  apply (equivFinsuppOfBasisRight (M := AF F) b).injective
  ext i
  refine Prod.ext (funext fun w => ?_) (RestrictedProduct.ext _ _ fun v => ?_)
  · have h1 := coord_map b (evInf F w) x i
    have h2 := coord_map b (evInf F w) y i
    have h3 : Algebra.TensorProduct.map (evInf F w) (AlgHom.id F E) x =
      Algebra.TensorProduct.map (evInf F w) (AlgHom.id F E) y := hw w
    rw [h3, h2] at h1
    exact h1.symm
  · have h1 := coord_map b (evFin F v) x i
    have h2 := coord_map b (evFin F v) y i
    have h3 : Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) x =
      Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) y := hv v
    rw [h3, h2] at h1
    exact h1.symm

theorem keeps_iff {A : Type} [CommRing A] {n j : ℕ} {M : Matrix (Fin n) (Fin n) A} {C : Matrix (Fin n) (Fin j) A}
    {D : Matrix (Fin j) (Fin n) A} (h : D * C = 1) :
    (∃ β : Matrix (Fin j) (Fin j) A, M * C = C * β) ↔ M * C = C * (D * (M * C)) := by
  refine ⟨?_, fun h => ⟨_, h⟩⟩
  rintro ⟨β, hβ⟩
  rw [hβ, ← Matrix.mul_assoc D, h, Matrix.one_mul]

theorem keeps_inv {A : Type} [CommRing A] {n j : ℕ} (M : GL (Fin n) A) {C : Matrix (Fin n) (Fin j) A}
    {β : Matrix (Fin j) (Fin j) A} (h : M.val * C = C * β) :
    ∃ β' : Matrix (Fin j) (Fin j) A, (M⁻¹).val * C = C * β' := by
  have hq : ∀ q : Polynomial A, Polynomial.aeval M.val q * C = C * Polynomial.aeval β q := by
    intro q
    induction q using Polynomial.induction_on with
    | C a => simp [Algebra.algebraMap_eq_smul_one]
    | add p q hp hq => simp [Matrix.add_mul, Matrix.mul_add, hp, hq]
    | monomial k a ih =>
      rw [pow_succ, ← mul_assoc, map_mul, map_mul (Polynomial.aeval β), Polynomial.aeval_X, Polynomial.aeval_X,
        Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]
  have hu : IsUnit (M.val.charpoly.coeff 0) := by
    have h1 := Matrix.det_eq_sign_charpoly_coeff M.val
    have h2 : IsUnit M.val.det := (Matrix.isUnit_iff_isUnit_det _).1 M.isUnit
    rw [h1] at h2
    exact isUnit_of_mul_isUnit_right h2
  obtain ⟨u, hu⟩ := hu
  have h0 := Matrix.aeval_self_charpoly M.val
  rw [← Polynomial.X_mul_divX_add M.val.charpoly, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C,
    ← hu] at h0
  have h1 : (M⁻¹).val = -((u⁻¹).val • Polynomial.aeval M.val M.val.charpoly.divX) := by
    have h2 := congrArg (fun Z => (u⁻¹).val • ((M⁻¹).val * Z)) h0
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Algebra.algebraMap_eq_smul_one,
      Matrix.mul_smul, Matrix.mul_one, smul_add, smul_smul, one_smul, Matrix.mul_zero, smul_zero] at h2
    exact eq_neg_of_add_eq_zero_right h2
  refine ⟨-((u⁻¹).val • Polynomial.aeval β M.val.charpoly.divX), ?_⟩
  rw [h1, Matrix.neg_mul, Matrix.smul_mul, hq, Matrix.mul_neg, Matrix.mul_smul]

def Keeps (R : Type) [CommRing R] [Algebra F R] {σ : E →ₐ[F] E} {n j : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (C : Matrix (Fin n) (Fin j) E) (g : HA R σ J) : Prop :=
  ∃ β : Matrix (Fin j) (Fin j) (R ⊗[F] E),
    (matHom R σ J g).val * C.map (inclR (F := F) R) = C.map (inclR (F := F) R) * β

omit [NumberField F] [NumberField E] in
theorem keeps_one (R : Type) [CommRing R] [Algebra F R] {σ : E →ₐ[F] E} {n j : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (C : Matrix (Fin n) (Fin j) E) : Keeps R C (1 : HA R σ J) :=
  ⟨1, by rw [map_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]⟩

omit [NumberField E] in

theorem mem_parFlag_of_local {σ : E →ₐ[F] E} {n j : ℕ} {J : Matrix (Fin n) (Fin n) E} {C : Matrix (Fin n) (Fin j) E}
    {D : Matrix (Fin j) (Fin n) E} (h : D * C = 1) (p : GAd σ J)
    (hw : ∀ w : InfinitePlace F, Keeps w.Completion C (projArch σ J w p))
    (hv : ∀ v, Keeps (Fv F v) C (proj σ J v p)) : p ∈ parFlag σ J C fun _ => 0 := by
  have key : ∀ {R : Type} [CommRing R] [Algebra F R] (f : AF F →ₐ[F] R),
      Keeps R C (IndefiniteRowSideFullHecke.AdelicUnitaryGroups.mapH σ J f p) →
      ((matHom (AF F) σ J p).val * adMat F C).map
          (Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom =
        (adMat F C * (adMat F D * ((matHom (AF F) σ J p).val * adMat F C))).map
          (Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom := by
    intro R _ _ f hf
    have hm : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E),
        (adMat F Z).map (Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom = Z.map (inclR R) := by
      intro a b Z
      ext i k
      simp [adMat, inclR]
    have hD : D.map (inclR (F := F) R) * C.map (inclR (F := F) R) = 1 := by
      rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
    simp only [Matrix.map_mul, hm]
    exact (keeps_iff hD).1 hf
  have h1 : (matHom (AF F) σ J p).val * adMat F C =
      adMat F C * (adMat F D * ((matHom (AF F) σ J p).val * adMat F C)) := by
    ext i k
    exact tens_ext (fun w => congrFun (congrFun (key (evInf F w) (hw w)) i) k)
      (fun v => congrFun (congrFun (key (evFin F v) (hv v)) i) k)
  obtain ⟨β', h2⟩ := keeps_inv _ h1
  exact ⟨⟨_, fun _ _ hh => absurd hh (lt_irrefl _), h1⟩,
    ⟨β', fun _ _ hh => absurd hh (lt_irrefl _), by rw [map_inv]; exact h2⟩⟩

theorem iwasawa_fin {σ : E →ₐ[F] E} (hc : IsCMExt F E σ) (hu : Algebra.Unramified (𝓞 F) (𝓞 E)) {n j : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) {C C' : Matrix (Fin n) (Fin j) E}
    (hCC : cT (σ : E →+* E) C * J * C = 0) (hCC' : cT (σ : E →+* E) C * J * C' = 1)
    (hC'C : cT (σ : E →+* E) C' * J * C = 1) (hC'C' : cT (σ : E →+* E) C' * J * C' = 0)
    {L : Submodule (𝓞 E) (Fin n → E)} [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F))
    (hL : IsSelfDualAt σ J L v) (y : GLoc σ J v) :
    ∃ q : GLoc σ J v, ∃ k ∈ stabLoc σ J L v, Keeps (Fv F v) C q ∧ y = q * k := by
  have hram : ∀ P : HeightOneSpectrum (𝓞 E), P.asIdeal.ramificationIdx (𝓞 F) = 1 := fun P =>
    Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  rcases LFun.InertChart.isSplit_or_isInertAt (F := F) (E := E) (v := v) (fun P _ => hram P) with hs | ⟨w, hw⟩
  · obtain ⟨P, Q, hPQ, hP, hQ⟩ := hs
    obtain ⟨τ, -, -⟩ := existsUnique_splitPrime_eq (v := v) hc hPQ (HeightOneSpectrum.ext hP)
      (HeightOneSpectrum.ext hQ)
    obtain ⟨k, i, q, hn, hsum⟩ := IwSplitFrame.exists_compl C C' _ _ hC'C hC'C' hCC hCC'
    let ε : Fin n ≃ (Fin j ⊕ Fin k) ⊕ Fin j :=
      (finCongr hn).trans (finSumFinEquiv.symm.trans (Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl _)))
    obtain ⟨B, lv, hB⟩ := Core.Rk.IwFlagSplit.exists_flag_basis τ hJ ε hsum hCC'
    obtain ⟨q, k, hq, hk, hy⟩ := Core.Rk.IwFlagSplit.iwasawa_of_triangular hc hJ τ L hL
      (IwSplitFrame.keepGrp (C.map (inclR (Fv F v)))) B lv (fun g hg => by
        obtain ⟨⟨a, ha⟩, a', ha'⟩ := hB g hg
        exact IwSplitFrame.keeps_of_split hc τ g hC'C ha ha') y
    obtain ⟨β, hβ⟩ := hq
    exact ⟨q, k, hk, ⟨β.val, hβ⟩, hy⟩
  · obtain ⟨c, hc1⟩ := exists_integer_add_conj_eq_one_of_formallyUnramified F E σ hc inferInstance
    obtain ⟨q, k, hk, hy, β, hβ⟩ := InertIwasawaLoc.exists_loc hc hc1 hJ hw (fun P _ => hram P) hL hC'C hCC y
    exact ⟨q, k, hk, ⟨β.val, hβ⟩, hy⟩

theorem iwasawa_arch {σ : E →ₐ[F] E} (hc : IsCMExt F E σ) {n j : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {C : Matrix (Fin n) (Fin j) E} (hCC : cT (σ : E →+* E) C * J * C = 0)
    {a : GL (Fin n) (AF F ⊗[F] E)} (ha : IsMajorantFrame σ J a) (w : InfinitePlace F) (y : GArch σ J w) :
    ∃ q : GArch σ J w, ∃ k ∈ stabArch σ J w (bc (compInf F E w) a), Keeps w.Completion C q ∧ y = q * k := by
  obtain ⟨ε, hε⟩ := ha w
  have h0 : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) (C.map (inclR (F := F) w.Completion)) * JR (F := F) w.Completion J *
      C.map (inclR (F := F) w.Completion) = 0 := by
    rw [IndefiniteRowSideFullHecke.AdelicUnitaryGroups.cT_map (σ : E →+* E) _ _ (fun x => by simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, inclR]), JR,
      ← Matrix.map_mul, ← Matrix.map_mul, hCC, Matrix.map_zero _ (map_zero _)]
  obtain ⟨k, hk, hk', β, hβ⟩ := Core.Rk.IwIso.local_at_arch hc J w _ ε hε _ h0 (matHom w.Completion σ J y) y.2
  let k' : GArch σ J w := ⟨k, hk⟩
  refine ⟨y * k'⁻¹, k', Core.Rk.IwIso.mem_stabArch_of σ J w _ k' hk', ⟨β, ?_⟩, by simp⟩
  rw [map_mul, map_inv]
  exact hβ

theorem iwasawa {σ : E →ₐ[F] E} (hc : IsCMExt F E σ) (hu : Algebra.Unramified (𝓞 F) (𝓞 E)) {n j : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) {C C' : Matrix (Fin n) (Fin j) E}
    (hCC : cT (σ : E →+* E) C * J * C = 0) (hCC' : cT (σ : E →+* E) C * J * C' = 1)
    (hC'C : cT (σ : E →+* E) C' * J * C = 1) (hC'C' : cT (σ : E →+* E) C' * J * C' = 0)
    {L : Submodule (𝓞 E) (Fin n → E)} [Submodule.IsLattice E L] (hL : ∀ v, IsSelfDualAt σ J L v)
    {a : GL (Fin n) (AF F ⊗[F] E)} (ha : IsMajorantFrame σ J a) (g : GAd σ J) :
    ∃ p ∈ parFlag σ J C (fun _ => 0), ∃ k ∈ levelAll σ J L a, g = p * k := by
  classical
  choose q k hk hq hy using fun v => iwasawa_fin hc hu hJ hCC hCC' hC'C hC'C' v (hL v) (proj σ J v g)
  choose q' k' hk' hq' hy' using fun w => iwasawa_arch hc hCC ha w (projArch σ J w g)
  have hfin := Filter.eventually_cofinite.1 (eventually_proj_mem_stabLoc σ J L g)
  obtain ⟨p₁, h₁, h₁'⟩ := AdelicIwasawaGlue.exists_fin_part σ J q hfin.toFinset
  obtain ⟨p₂, h₂, h₂'⟩ := AdelicIwasawaGlue.exists_arch_part σ J q' Finset.univ
  refine ⟨p₁ * p₂, mem_parFlag_of_local hC'C _ (fun w => ?_) (fun v => ?_), (p₁ * p₂)⁻¹ * g, ?_,
    (mul_inv_cancel_left _ _).symm⟩
  · rw [map_mul, h₁, h₂', one_mul, if_pos (Finset.mem_univ _)]
    exact hq' w
  · rw [map_mul, h₁', h₂, mul_one]
    split_ifs
    exacts [hq v, keeps_one _ _]
  · refine mem_levelAll.2 ⟨fun v => ?_, fun w => ?_⟩
    · rw [map_mul, map_inv, map_mul, h₁', h₂, mul_one]
      split_ifs with hv
      · rw [hy v, inv_mul_cancel_left]
        exact hk v
      · rw [inv_one, one_mul]
        simpa using hv
    · rw [map_mul, map_inv, map_mul, h₁, h₂', one_mul, if_pos (Finset.mem_univ _), hy' w, inv_mul_cancel_left]
      exact hk' w

end GlobalTheory.EisMaxCompare
