import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularSemisimpleUnitaryDataOfRegular
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open scoped TensorProduct

namespace GlobalTheory.FactorSplit
open GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt Formalism.UG

variable {F E : Type} [Field F] [Field E] [Algebra F E] {n : ℕ} {σ : E →ₐ[F] E}
  {J : Matrix (Fin n) (Fin n) E} {γ : Matrix (Fin n) (Fin n) E} {k : ℕ} {K : Fin k → Type}
  [∀ i, Field (K i)] [∀ i, Algebra F (K i)]

theorem factorIdem_mul (e : plusAlg σ J γ ≃ₐ[F] ∀ i, K i) (i : Fin k) (p : plusAlg σ J γ) :
    factorIdem e i * ((p : genAlg γ) : Matrix (Fin n) (Fin n) E) =
      ((e.symm (Pi.single i (e p i)) : plusAlg σ J γ) : genAlg γ) := by
  have h : e.symm (Pi.single i 1) * p = e.symm (Pi.single i (e p i)) := by
    apply e.injective
    rw [map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_apply, hj]
  rw [← h]; rfl

theorem factorIdem_mul_self (e : plusAlg σ J γ ≃ₐ[F] ∀ i, K i) (i : Fin k) :
    factorIdem e i * factorIdem e i = factorIdem e i := by
  have := factorIdem_mul e i (e.symm (Pi.single i 1))
  rw [AlgEquiv.apply_symm_apply, Pi.single_eq_same] at this
  exact this

theorem factorIdem_ne_zero (e : plusAlg σ J γ ≃ₐ[F] ∀ i, K i) (i : Fin k) : factorIdem e i ≠ 0 := by
  intro h
  have h1 : e.symm (Pi.single i 1) = 0 := Subtype.ext (Subtype.ext h)
  have h2 := congrFun (e.symm_apply_eq.1 h1) i
  simp at h2

theorem factorIdem_selfAdj (e : plusAlg σ J γ ≃ₐ[F] ∀ i, K i) (i : Fin k) :
    cT (σ : E →+* E) (factorIdem e i) * J = J * factorIdem e i :=
  (e.symm (Pi.single i 1)).2

theorem factorIdem_orth (e : plusAlg σ J γ ≃ₐ[F] ∀ i, K i) (i : Fin k) :
    cT (σ : E →+* E) (1 - factorIdem e i) * J * factorIdem e i = 0 := by
  have hq : cT (σ : E →+* E) (((1 - e.symm (Pi.single i 1) : plusAlg σ J γ) : genAlg γ) : Matrix (Fin n) (Fin n) E) * J =
      J * (((1 - e.symm (Pi.single i 1) : plusAlg σ J γ) : genAlg γ) : Matrix (Fin n) (Fin n) E) :=
    (1 - e.symm (Pi.single i 1)).2
  have hc : (((1 - e.symm (Pi.single i 1) : plusAlg σ J γ) : genAlg γ) : Matrix (Fin n) (Fin n) E) =
      1 - factorIdem e i := rfl
  rw [hc] at hq
  rw [hq, Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, factorIdem_mul_self, sub_self, Matrix.mul_zero]

theorem factorIdem_comm (e : plusAlg σ J γ ≃ₐ[F] ∀ i, K i) (i : Fin k) :
    ∀ l ∈ genAlg γ, l * factorIdem e i = factorIdem e i * l := by
  intro l hl
  exact congrArg Subtype.val (mul_comm (⟨l, hl⟩ : genAlg γ) (e.symm (Pi.single i 1) : plusAlg σ J γ))

end GlobalTheory.FactorSplit

namespace GlobalTheory.FactorSplit
open GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt Formalism.UG Matrix

variable {F E : Type} [Field F] [Field E] [Algebra F E] {n : ℕ} {σ : E →ₐ[F] E}
  {J : Matrix (Fin n) (Fin n) E} {k : ℕ} {K : Fin k → Type}
  [∀ i, Field (K i)] [∀ i, Algebra F (K i)]

theorem rank_factorIdem {γ : GL (Fin n) E} (hA : ClauseAlg σ J γ) (hP : ClausePlus σ J γ)
    (e : plusAlg σ J (γ : Matrix (Fin n) (Fin n) E) ≃ₐ[F] ∀ i, K i) (i : Fin k) :
    (factorIdem e i).rank = Module.finrank E (E ⊗[F] K i) := by
  obtain ⟨-, -, -, ⟨v, hv⟩, -⟩ := hA
  obtain ⟨-, -, hbij⟩ := hP
  let L := genAlg (γ : Matrix (Fin n) (Fin n) E)
  let P := plusAlg σ J (γ : Matrix (Fin n) (Fin n) E)
  let φ : L →ₗ[E] (Fin n → E) :=
    { toFun := fun l => (l : Matrix (Fin n) (Fin n) E) *ᵥ v
      map_add' := fun a b => Matrix.add_mulVec _ _ _
      map_smul' := fun c a => Matrix.smul_mulVec _ _ _ }
  let incl : P →ₗ[F] L := P.val.toLinearMap
  let ψ : E ⊗[F] P →ₗ[E] L := LinearMap.liftBaseChange E incl
  let ι : K i →ₗ[F] P := e.symm.toLinearMap ∘ₗ LinearMap.single F K i
  let Φ : E ⊗[F] K i →ₗ[E] (Fin n → E) := φ ∘ₗ ψ ∘ₗ ι.baseChange E
  have hψ : ∀ t, ψ t = plusTensor σ J (γ : Matrix (Fin n) (Fin n) E) (TensorProduct.comm F E P t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a p =>
      simp [ψ, incl, plusTensor, Algebra.TensorProduct.productMap_apply_tmul, Algebra.smul_def, mul_comm]; rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have hψb : Function.Bijective ψ := by
    have : (ψ : E ⊗[F] P → L) = plusTensor σ J (γ : Matrix (Fin n) (Fin n) E) ∘ TensorProduct.comm F E P :=
      funext hψ
    rw [this]; exact hbij.comp (TensorProduct.comm F E P).bijective
  have hι : Function.Injective (ι.baseChange E) := by
    have h0 : Function.Injective ι := e.symm.injective.comp (Pi.single_injective i)
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap ι h0
  have hΦ : Function.Injective Φ := hv.1.comp (hψb.1.comp hι)
  have hΦt : ∀ (a : E) (x : K i), Φ (a ⊗ₜ x) =
      a • ((((e.symm (Pi.single i x) : P) : L) : Matrix (Fin n) (Fin n) E) *ᵥ v) := by
    intro a x
    simp [Φ, φ, ψ, ι, incl, LinearMap.liftBaseChange_tmul, Matrix.smul_mulVec]
  have hrange : LinearMap.range Φ = LinearMap.range (factorIdem e i).mulVecLin := by
    apply le_antisymm
    · rintro _ ⟨t, rfl⟩
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a x =>
        refine ⟨a • ((((e.symm (Pi.single i x) : P) : L) : Matrix (Fin n) (Fin n) E) *ᵥ v), ?_⟩
        rw [hΦt, Matrix.mulVecLin_apply, Matrix.mulVec_smul, Matrix.mulVec_mulVec, factorIdem_mul]
        simp
      | add x y hx hy => rw [map_add]; exact add_mem hx hy
    · rintro _ ⟨w, rfl⟩
      obtain ⟨l, rfl⟩ := hv.2 w
      obtain ⟨s, rfl⟩ := hψb.2 l
      change (factorIdem e i).mulVecLin (φ (ψ s)) ∈ LinearMap.range Φ
      induction s using TensorProduct.induction_on with
      | zero => simp [φ]
      | tmul a p =>
        refine ⟨a ⊗ₜ (e p i), ?_⟩
        rw [hΦt]
        simp only [ψ, incl, LinearMap.liftBaseChange_tmul, Matrix.mulVecLin_apply]
        have hc : (((a • (p : L)) : L) : Matrix (Fin n) (Fin n) E) = a • ((p : L) : Matrix (Fin n) (Fin n) E) := rfl
        change _ = factorIdem e i *ᵥ ((((a • (p : L)) : L) : Matrix (Fin n) (Fin n) E) *ᵥ v)
        rw [hc, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec, factorIdem_mul]
      | add x y hx hy =>
        rw [map_add, map_add, map_add]; exact add_mem hx hy
  rw [Matrix.rank, ← hrange, LinearMap.finrank_range_of_inj hΦ]

end GlobalTheory.FactorSplit

namespace GlobalTheory.FactorSplit
open GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt Formalism.UG Matrix

variable {F E : Type} [Field F] [Field E] [Algebra F E] {n : ℕ} {σ : E →ₐ[F] E}
  {J : Matrix (Fin n) (Fin n) E} {γ : Matrix (Fin n) (Fin n) E} {k : ℕ} {K : Fin k → Type}
  [∀ i, Field (K i)] [∀ i, Algebra F (K i)]

theorem eq_zero_of_mulVec {M : Matrix (Fin n) (Fin n) E} (h : ∀ w, M *ᵥ w = 0) : M = 0 := by
  ext a b
  have := congrFun (h (Pi.single b 1)) a
  simpa [Matrix.mulVec_single_one] using this

theorem rank_pos_of_ne_zero {M : Matrix (Fin n) (Fin n) E} (hM : M ≠ 0) : 0 < M.rank := by
  refine Nat.pos_of_ne_zero fun h => hM (eq_zero_of_mulVec fun w => ?_)
  rw [Matrix.rank, Submodule.finrank_eq_zero] at h
  have : M.mulVecLin w ∈ LinearMap.range M.mulVecLin := ⟨w, rfl⟩
  rw [h] at this
  exact (Submodule.mem_bot E).1 this

theorem eq_one_of_idem_rank {M : Matrix (Fin n) (Fin n) E} (hM : M * M = M) (hr : M.rank = n) : M = 1 := by
  have htop : LinearMap.range M.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank, hr, Module.finrank_fin_fun]
  have hu : ∀ u, M *ᵥ u = u := by
    intro u
    obtain ⟨w, hw⟩ : u ∈ LinearMap.range M.mulVecLin := htop ▸ Submodule.mem_top
    rw [← hw, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hM]
  have h0 := eq_zero_of_mulVec (M := M - 1) fun w => by rw [Matrix.sub_mulVec, hu, Matrix.one_mulVec, sub_self]
  exact sub_eq_zero.1 h0

theorem two_le_of_decomp {P : Type} [CommRing P] [Algebra F P] {k' : ℕ} {K' : Fin k' → Type}
    [∀ i, Field (K' i)] [∀ i, Algebra F (K' i)] (e' : P ≃ₐ[F] ∀ i, K' i) (hk' : 2 ≤ k')
    (e : P ≃ₐ[F] ∀ i, K i) (i : Fin k) : ∃ j, j ≠ i := by
  by_contra hne
  simp only [not_exists, ne_eq, not_not] at hne
  let a : Fin k' := ⟨0, by omega⟩
  let b : Fin k' := ⟨1, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  let q : P := e'.symm (Pi.single a 1)
  have hqq : q * q = q := by
    apply e'.injective
    rw [map_mul, AlgEquiv.apply_symm_apply, ← Pi.single_mul, one_mul]
  have hq : IsIdempotentElem (e q i) := by
    show e q i * e q i = e q i
    rw [← Pi.mul_apply, ← map_mul, hqq]
  rcases IsIdempotentElem.iff_eq_zero_or_one.1 hq with h | h
  · have : e q = 0 := funext fun j => by rw [hne j]; exact h
    have h2 := congrFun (e'.symm_apply_eq.1 (e.map_eq_zero_iff.1 this)) a
    simp at h2
  · have : e q = 1 := funext fun j => by rw [hne j]; exact h
    have h1 : q = 1 := by rw [← map_one e] at this; exact e.injective this
    have h2 := congrFun (e'.symm_apply_eq.1 h1) b
    simp [Pi.single_apply, hab.symm] at h2

theorem factorIdem_ne_one (e : plusAlg σ J γ ≃ₐ[F] ∀ i, K i) (i : Fin k) (hj : ∃ j, j ≠ i) :
    factorIdem e i ≠ 1 := by
  intro h
  obtain ⟨j, hj⟩ := hj
  have h1 : e.symm (Pi.single i 1) = 1 := Subtype.ext (Subtype.ext h)
  have h2 := congrFun (e.symm_apply_eq.1 h1) j
  simp [Pi.single_apply, hj] at h2

end GlobalTheory.FactorSplit

namespace GlobalTheory.FactorSplit
open GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt

theorem factorIdem_orthSplit_rank : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple → ∀ (D : D7) (V : HSp D) (γ : GF V), IsRegSS γ.1.1 → ∀ (k : ℕ) (Kf : Fin k → Type) [∀ i, Field (Kf i)] [∀ i, Algebra D.host.F (Kf i)] (e : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.plusAlg D.sp.cm.sig V.gram γ.1.1 ≃ₐ[D.host.F] ∀ i, Kf i) (i : Fin k), GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1 → GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.IsOrthSplit D.sp.cm.sig V.gram γ.1.1 (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.factorIdem e i) ∧ (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.factorIdem e i).rank = Module.finrank D.host.E (TensorProduct D.host.F D.host.E (Kf i)) := by
  intro hRS D V γ hss k Kf _ _ e i hnf
  have hreg := GlobalTheory.ConjLevi.RegularData.isRegular_of_isRegSS γ hss
  obtain ⟨hA, hP, -⟩ := hRS.1 D.host.F D.host.E (Fin V.rank) D.sp.cm.sig V.gram γ.1 hreg
  obtain ⟨-, k', K', _, _, ⟨e'⟩, hk', -⟩ := hnf
  have hj := two_le_of_decomp e' hk' e i
  refine ⟨⟨factorIdem_mul_self e i, factorIdem_selfAdj e i, factorIdem_orth e i, factorIdem_comm e i,
    rank_pos_of_ne_zero (factorIdem_ne_zero e i), lt_of_le_of_ne (Matrix.rank_le_width _) fun h =>
      factorIdem_ne_one e i hj (eq_one_of_idem_rank (factorIdem_mul_self e i) h)⟩,
    rank_factorIdem hA hP e i⟩

end GlobalTheory.FactorSplit
