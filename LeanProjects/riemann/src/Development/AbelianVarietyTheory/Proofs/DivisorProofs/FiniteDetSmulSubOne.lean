import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHalfIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussSumNondegenerateFiniteHermitianModuleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexMapNsmulComapEqAbsNormDetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLatticeSelfDualFgFullIndexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralGaussianRealIsometryNoFixedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaTildeHeckeCharSplitMulSignOfNormFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionCommQuasiReflectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalIsometryVacuumScalarGaussSumIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeilRepEqLatticeIntertwinerMulCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSubstitutionThetaHeisenbergUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaThetaFunctionsOrientedPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitCharacter
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryMatrixEqProdQuasiReflections
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryQuasiReflectionLaws
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MapFinNeg
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaFunNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatAut

open GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.SplitScalar

section Abstract

theorem gauss_isometry {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
    {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} (h : IsHeis σ w γ W) {lam : ℕ →* ℂ} (hlam : GoodNorm σ lam)
    {A : Submodule R X} (hA : SelfDual γ A) (u : X →ₗ[R] X) (hu : ∀ x y, γ (u x) (u y) = γ x y)
    (hs : ∀ a, ∃ y, u y - y = a) (n : ℕ) (t : Fin n → X) (ht : ∀ k, u (t k) - t k ∈ A)
    (ht' : ∀ y, u y - y ∈ A → ∃! k, y - t k ∈ A) :
    ∑ k, γ (σ w • (u (t k) - t k)) (t k) = lam n ∧ lam n ^ 2 = n := by
  let β : X → X → ℂ := fun y x => γ (σ w • (u y - y)) x * γ (w • (u y - y)) (u x)
  have hsub : ∀ x y z, γ (x - y) z = γ x z * (γ y z)⁻¹ := fun x y z => by
    rw [sub_eq_add_neg, h.add_left, h.neg_left]
  have hβ : ∀ y x, β y x = γ (σ w • u y) x * (γ (σ w • y) x)⁻¹ * (γ (w • y) x * (γ (w • y) (u x))⁻¹) := fun y x => by
    simp only [β, smul_sub, hsub]
    rw [← map_smul u w y, hu]
  have e1 : ∀ x y, γ (σ w • x) y = (γ (w • y) x)⁻¹ := fun x y => by rw [h.adj, h.sg_sg, h.swap]
  have hsym : ∀ x y, β x y = β y x := fun x y => by
    rw [hβ, hβ, e1, e1, e1, e1]
    simp only [inv_inv]
    ring
  have hβ' : ∀ y x, β y x = γ (u y - y) (w • x + σ w • u x) := fun y x => by
    simp only [β]
    rw [h.add_right, h.adj, h.adj, h.sg_sg]
  have hm : ∀ x, x ∈ A.comap (u - LinearMap.id) ↔ u x - x ∈ A := fun x => Iff.rfl
  have key := GlobalTheory.T.gaussSum_nondegenerate_finite_hermitian_module σ w h.sg_sg h.w_add lam hlam β
    (fun x y z => by
      rw [hβ', hβ', hβ', ← h.add_left, map_add]
      congr 1
      abel)
    hsym
    (fun r x y => by
      rw [hβ', hβ', map_smul, ← smul_sub, h.adj, map_smul, smul_add, smul_comm (σ r) w, smul_comm (σ r) (σ w)])
    (A.comap (u - LinearMap.id)) (A.comap (u - LinearMap.id) ⊓ A) inf_le_left
    (fun x hx => by
      rw [hm] at hx
      have hz : w • x + σ w • u x = x + σ w • (u x - x) := by
        have e : w • x + σ w • x = x := by rw [← add_smul, h.w_add, one_smul]
        rw [smul_sub, ← sub_eq_zero]
        rw [← sub_eq_zero] at e
        rw [← e]
        abel
      constructor
      · rintro ⟨-, hxA⟩ y hy
        rw [hsym, hβ', hz]
        exact h.iso hA hy (A.add_mem hxA (A.smul_mem _ hx))
      · intro hy
        refine ⟨hx, ?_⟩
        have : x + σ w • (u x - x) ∈ A := (hA _).2 fun a ha => by
          obtain ⟨y, rfl⟩ := hs a
          have := hy y ha
          rw [hsym, hβ', hz] at this
          exact h.swap_eq_one this
        exact (A.add_mem_iff_left (A.smul_mem _ hx)).1 this)
    n t (fun k => (hm _).2 (ht k)) (fun y hy => by
      obtain ⟨k, hk, hk'⟩ := ht' y hy
      exact ⟨k, ⟨Submodule.sub_mem _ hy ((hm _).2 (ht k)), hk⟩, fun k' h' => hk' k' h'.2⟩)
  refine ⟨Eq.trans (Finset.sum_congr rfl fun k _ => ?_) key.1, key.2⟩
  have e4 : ∀ (r : R) y, γ (r • (u y - y)) (u y) = γ (σ r • (u y - y)) y := fun r y => by
    rw [smul_sub, smul_sub, hsub, hsub, ← map_smul u r y, hu, h.adj (σ r), h.adj (σ r), h.sg_sg, h.swap (r • y) (u y),
      h.swap (r • y) y, inv_inv, mul_comm]
  simp only [β]
  rw [map_smul, ← smul_sub, smul_smul, smul_smul, e4, ← h.add_left, ← add_smul, map_mul, ← mul_add, h.w_add, mul_one]

theorem exists_transversal {X : Type} [AddCommGroup X] (A B : AddSubgroup X) (h : A.relIndex B ≠ 0) :
    ∃ t : Fin (A.relIndex B) → X, (∀ k, t k ∈ B) ∧ ∀ y ∈ B, ∃! k, y - t k ∈ A := by
  have : Finite (B ⧸ A.addSubgroupOf B) := AddSubgroup.index_ne_zero_iff_finite.1 h
  let e : (B ⧸ A.addSubgroupOf B) ≃ Fin (A.relIndex B) := Finite.equivFinOfCardEq rfl
  refine ⟨fun k => ((e.symm k).out : B), fun k => (e.symm k).out.2, fun y hy => ?_⟩
  have key : ∀ k, y - ((e.symm k).out : B) ∈ A ↔ k = e (QuotientAddGroup.mk ⟨y, hy⟩) := fun k => by
    rw [← Equiv.symm_apply_eq, eq_comm, ← QuotientAddGroup.out_eq' (e.symm k), QuotientAddGroup.eq_iff_sub_mem,
      QuotientAddGroup.out_eq']
    rfl
  exact ⟨_, (key _).2 rfl, fun k hk => (key k).1 hk⟩

theorem finite_det_smul_sub_one {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] (M : Matrix ι ι K) :
    {t : K | (t • M - 1).det = 0}.Finite := by
  have h0 : M.charpolyRev ≠ 0 := fun h => by
    have := Matrix.eval_charpolyRev (M := M)
    rw [h, Polynomial.eval_zero] at this
    exact zero_ne_one this
  refine (Polynomial.finite_setOfPred_isRoot h0).subset fun t ht => ?_
  have e : M.charpolyRev.eval t = (1 - t • M).det := by
    rw [Matrix.charpolyRev, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    rw [map_sub, map_one]
    congr 2
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Polynomial.eval_mul,
      Polynomial.coe_evalRingHom, Polynomial.eval_X, Polynomial.eval_C]
  show M.charpolyRev.eval t = 0
  rw [e, ← neg_sub, Matrix.det_neg, show (t • M - 1).det = 0 from ht, mul_zero]

theorem det_unitary_sub_one {K ι : Type} [Field K] [StarRing K] [Fintype ι] [DecidableEq ι] {M P : Matrix ι ι K}
    (hP : P.det ≠ 0) (h : Mᴴ * P * M = P) :
    M.det * star M.det = 1 ∧ M.det * star (M - 1).det = (-1) ^ Fintype.card ι * (M - 1).det := by
  constructor
  · have := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at this
    refine mul_right_cancel₀ hP ?_
    linear_combination this
  · have e : (M - 1)ᴴ * P * M = P * -(M - 1) := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.sub_mul, Matrix.sub_mul, h, Matrix.one_mul,
        neg_sub, Matrix.mul_sub, Matrix.mul_one]
    have := congrArg Matrix.det e
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_neg] at this
    refine mul_right_cancel₀ hP ?_
    linear_combination this

theorem kronecker_unitary {K : Type} [Field K] [StarRing K] {m n : ℕ} {a G : Matrix (Fin n) (Fin n) K}
    {b H : Matrix (Fin m) (Fin m) K} (hG : IsUnit G.det) (ha : aᴴ * G * a = G) (hb : bᴴ * H * b = H) :
    (b ⊗ₖ aᵀ)ᴴ * (H ⊗ₖ G⁻¹ᵀ) * (b ⊗ₖ aᵀ) = H ⊗ₖ G⁻¹ᵀ := by
  have h1 : (G⁻¹ * aᴴ * G) * a = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc aᴴ, ha, Matrix.nonsing_inv_mul _ hG]
  have h2 : a * G⁻¹ * aᴴ = G⁻¹ := by
    have h3 := mul_eq_one_comm.1 h1
    calc a * G⁻¹ * aᴴ = a * (G⁻¹ * aᴴ * G) * G⁻¹ := by
          simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG, Matrix.mul_one]
      _ = G⁻¹ := by rw [h3, Matrix.one_mul]
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hb]
  congr 1
  conv_rhs => rw [← h2]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  rfl

end Abstract

variable {D : D7}

def IsRat (V : HSp D) (g : GA D V) (a : Matrix (Fin V.rank) (Fin V.rank) D.host.E) : Prop :=
  Formalism.L2.Theta.mt V g = a.map (incA D)

theorem incA_inj : Function.Injective (incA D) := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  intro x y h
  refine (tauE D (D.eTau.symm 1)).injective ?_
  rw [← comp_incA hθ, ← comp_incA hθ, h]

theorem exists_isRat {V : HSp D} {g : GA D V} (hg : g ∈ GQ V) : ∃ a, IsRat V g a := by
  obtain ⟨a, -, ha⟩ := hg
  exact ⟨a.1, (congrArg Units.val ha).symm⟩

theorem mt_unitary (V : HSp D) (g : GA D V) :
    ((Formalism.L2.Theta.mt V g).map (cA D))ᵀ * V.gram.map (incA D) * Formalism.L2.Theta.mt V g = V.gram.map (incA D) := g.2

theorem IsRat.unitary {V : HSp D} {g : GA D V} {a} (h : IsRat V g a) : aᴴ * V.gram * a = V.gram := by
  have e := mt_unitary V g
  rw [show Formalism.L2.Theta.mt V g = _ from h] at e
  refine Matrix.map_injective (incA_inj (D := D)) ?_
  show (aᴴ * V.gram * a).map (incA D) = V.gram.map (incA D)
  rw [Matrix.map_mul, Matrix.map_mul]
  exact e

theorem exists_of_unitary (V : HSp D) {a : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (h : aᴴ * V.gram * a = V.gram) :
    ∃ g ∈ GQ V, IsRat V g a := by
  have hd := (det_unitary_sub_one (GlobalTheory.LatVac.gram_det_isUnit V).ne_zero h).1
  let a' : GL (Fin V.rank) D.host.E := Matrix.GeneralLinearGroup.mkOfDetNeZero a (left_ne_zero_of_mul_eq_one hd)
  refine ⟨⟨Formalism.UG.bc (incA D) a', ?_⟩, ⟨a', h, rfl⟩, rfl⟩
  show ((a.map (incA D)).map (cA D))ᵀ * V.gram.map (incA D) * a.map (incA D) = V.gram.map (incA D)
  conv_rhs => rw [← h, Matrix.map_mul, Matrix.map_mul]
  rfl

theorem IsRat.mul {V : HSp D} {g g' : GA D V} {a a'} (h : IsRat V g a) (h' : IsRat V g' a') : IsRat V (g * g') (a * a') := by
  rw [IsRat, mt_mul, show Formalism.L2.Theta.mt V g = _ from h, show Formalism.L2.Theta.mt V g' = _ from h', Matrix.map_mul]

theorem isRat_one (V : HSp D) : IsRat V 1 1 := by
  rw [IsRat, mt_one, Matrix.map_one _ (incA D).map_zero (incA D).map_one]

theorem IsRat.ext {V : HSp D} {g g' : GA D V} {a} (h : IsRat V g a) (h' : IsRat V g' a) : g = g' :=
  Subtype.ext (Units.ext (h.trans h'.symm))

theorem IsRat.mem {V : HSp D} {g : GA D V} {a} (h : IsRat V g a) : g ∈ GQ V := by
  obtain ⟨g', h1, h2⟩ := exists_of_unitary V h.unitary
  rwa [h.ext h2]

theorem IsRat.compAt {V : HSp D} {g : GA D V} {a} (h : IsRat V g a) {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) :
    compAt θ τ (Formalism.L2.Theta.mt V g) = a.map (tauE D τ) := by
  rw [show Formalism.L2.Theta.mt V g = _ from h]
  funext i j
  exact comp_incA hθ τ _

theorem compAt_mul (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) (g g' : GA D V) :
    compAt θ τ (Formalism.L2.Theta.mt V (g * g')) = compAt θ τ (Formalism.L2.Theta.mt V g) * compAt θ τ (Formalism.L2.Theta.mt V g') :=
  Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem compAt_fin (θ : InfFam D) (τ : D.what₂.Tau) {V : HSp D} {k : GA D V} (hk : k ∈ GfC V) :
    compAt θ τ (Formalism.L2.Theta.mt V k) = 1 := by
  have h : (Formalism.L2.Theta.mt V k).map (infPart D) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hk)
  have : compAt θ τ (Formalism.L2.Theta.mt V k) = ((Formalism.L2.Theta.mt V k).map (infPart D)).map (θ τ) := rfl
  rw [this, h, Matrix.map_one _ (θ τ).map_zero (θ τ).map_one]

theorem map_tau_unitary {V : HSp D} {a : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (h : aᴴ * V.gram * a = V.gram)
    (τ : D.what₂.Tau) : (a.map (tauE D τ))ᴴ * gramAt D V τ * a.map (tauE D τ) = gramAt D V τ := by
  have e : (aᴴ).map (tauE D τ) = (a.map (tauE D τ))ᴴ := by
    funext i j
    exact tauE_star τ _
  have := congrArg (fun m : Matrix (Fin V.rank) (Fin V.rank) D.host.E => m.map (tauE D τ)) h
  simp only [Matrix.map_mul, e] at this
  exact this

theorem infinite_norm_one (D : D7) : {t : D.host.E | t * star t = 1}.Infinite := by
  have h0 : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hs := GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D
  have hne : ∀ n : ℕ, (n : D.host.E) - D.host.xi0 ≠ 0 := fun n h => by
    have e := congrArg star h
    rw [star_sub, star_natCast, hs, star_zero] at e
    apply h0
    linear_combination (e - h) / 2
  have hne' : ∀ n : ℕ, (n : D.host.E) + D.host.xi0 ≠ 0 := fun n h => by
    have e := congrArg star h
    rw [star_add, star_natCast, hs, star_zero] at e
    exact hne n (by rw [← e]; ring)
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n : D.host.E) + D.host.xi0) / (n - D.host.xi0))
    (fun n m h => ?_) fun n => ?_
  · have := (div_eq_div_iff (hne n) (hne m)).1 h
    have e : D.host.xi0 * ((n : D.host.E) - m) = 0 := by linear_combination (-1 / 2) * this
    exact_mod_cast sub_eq_zero.1 ((mul_eq_zero.1 e).resolve_left h0)
  · show _ * star _ = 1
    rw [star_div₀, star_add, star_sub, star_natCast, hs, sub_neg_eq_add, ← sub_eq_add_neg]
    have := hne n
    have := hne' n
    field_simp

theorem rat_induction (V : HSp D) (P : GA D V → Prop) (h1 : P 1) (hm : ∀ g ∈ GQ V, ∀ g' ∈ GQ V, P g → P g' → P (g * g'))
    (hr : ∀ g (x : Fin V.rank → D.host.E) (c : D.host.E), star x ⬝ᵥ V.gram *ᵥ x ≠ 0 →
      IsRat V g (1 + c • Matrix.vecMulVec x (star x ᵥ* V.gram)) → P g) : ∀ g ∈ GQ V, P g := by
  intro g hg
  obtain ⟨a, ha⟩ := exists_isRat hg
  have hc : ∀ x : D.host.E, D.host.conj x = star x := fun x => (GlobalTheory.SplitIdem.star_eq_conj D x).symm
  have hh : ∀ x y, GlobalTheory.UnRep.hermE D.host.conj V.gramᵀ x y = star y ⬝ᵥ V.gram *ᵥ x := fun x y => by
    simp only [GlobalTheory.UnRep.hermE, hc, dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.mul_sum, Pi.star_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hun : ∀ m, GlobalTheory.UnRep.IsUnE D.host.conj V.gramᵀ m ↔ mᴴ * V.gram * m = V.gram := fun m => by
    have e : ∀ x y, star (m *ᵥ y) ⬝ᵥ V.gram *ᵥ m *ᵥ x = star y ⬝ᵥ (mᴴ * V.gram * m) *ᵥ x := fun x y => by
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    simp only [GlobalTheory.UnRep.IsUnE, hh, e]
    refine ⟨fun h => ?_, fun h x y => by rw [h]⟩
    ext i j
    simpa using h (Pi.single j 1) (Pi.single i 1)
  have hG : GlobalTheory.UnRep.IsHermForm D.host.conj V.gramᵀ := by
    refine ⟨fun x => by rw [hc, hc, star_star], fun h => ?_, fun i j => by rw [hc]; exact GlobalTheory.LatVac.gram_star V _ _,
      by rw [Matrix.det_transpose]; exact (GlobalTheory.LatVac.gram_det_isUnit V).ne_zero⟩
    have e := GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D
    rw [← hc, h, AlgEquiv.one_apply] at e
    exact GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero (D := D) (by linear_combination e / 2)
  obtain ⟨l, hl, rfl⟩ := GlobalTheory.UnRep.isUnE_eq_prod_refl ℚ _ D.host.conj _ _ hG a ((hun a).2 ha.unitary)
  clear hg
  induction l generalizing g with
  | nil => exact ha.ext (isRat_one V) ▸ h1
  | cons p l ih =>
    obtain ⟨p1, p2⟩ := hl p List.mem_cons_self
    obtain ⟨g₁, m1, r1⟩ := exists_of_unitary V
      ((hun _).1 ((GlobalTheory.UnRep.ReflLaws.refl_laws ℚ _ D.host.conj _ _ hG p.1 p1).2.2.2 p.2 p2))
    obtain ⟨g₂, m2, r2⟩ := exists_of_unitary V
      ((hun _).1 (GlobalTheory.UnRep.ReflGen.isUnE_prod hG l fun q hq => hl q (List.mem_cons_of_mem _ hq)))
    rw [List.map_cons, List.prod_cons] at ha
    rw [ha.ext (r1.mul r2)]
    refine hm _ m1 _ m2 (hr g₁ p.1 ((p.2 - 1) / GlobalTheory.UnRep.hermE D.host.conj V.gramᵀ p.1 p.1) (hh _ _ ▸ p1) ?_)
      (ih g₂ (fun q hq => hl q (List.mem_cons_of_mem _ hq)) r2)
    rw [← Matrix.mulVec_transpose]
    have e : (fun b => D.host.conj (p.1 b)) = star p.1 := funext fun b => hc _
    rw [← e]
    exact r1

section Operators

variable {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {χS χT : (AE D)ˣ →* Circle} {of oi : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem act_mul (g g' : GA D S) (h h' : GA D T) (u : WO S T) :
    actO S T (g * g') (h * h') u = actO S T g h (actO S T g' h' u) := by
  simp only [actO, _root_.mul_inv_rev, mt_mul, Matrix.mul_assoc]

theorem act_one (u : WO S T) : actO S T 1 1 u = u := by
  rw [actO, inv_one, mt_one, mt_one, Matrix.one_mul, Matrix.mul_one]

def subst (p : GA D S × GA D T) : Module.End ℂ (WO S T → ℂ) := LinearMap.funLeft ℂ ℂ (actO S T p.1⁻¹ p.2⁻¹)

theorem subst_apply (p : GA D S × GA D T) (f : WO S T → ℂ) : subst p f = fun w => f (actO S T p.1⁻¹ p.2⁻¹ w) := rfl

theorem subst_mul (p q : GA D S × GA D T) (f : WO S T → ℂ) : subst (p * q) f = subst p (subst q f) := by
  funext w
  show f (actO S T (p.1 * q.1)⁻¹ (p.2 * q.2)⁻¹ w) = f (actO S T q.1⁻¹ q.2⁻¹ (actO S T p.1⁻¹ p.2⁻¹ w))
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, act_mul]

theorem subst_one (f : WO S T → ℂ) : subst (1 : GA D S × GA D T) f = f := by
  funext w
  show f (actO S T 1⁻¹ 1⁻¹ w) = f w
  rw [inv_one, inv_one, act_one]

theorem exists_parts (p : GA D S × GA D T) : ∃ a k : GA D S × GA D T, a.1 ∈ GinfC S ∧ a.2 ∈ GinfC T ∧ k.1 ∈ GfC S ∧
    k.2 ∈ GfC T ∧ p = a * k ∧ p = k * a := by
  obtain ⟨s1, s2, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D S
  obtain ⟨t1, t2, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D T
  obtain ⟨a, ha, k, hk, e⟩ := s1 p.1
  obtain ⟨a', ha', k', hk', e'⟩ := t1 p.2
  exact ⟨(a, a'), (k, k'), ha, ha', hk, hk', Prod.ext e e',
    Prod.ext (e.trans (s2 a ha k hk)) (e'.trans (t2 a' ha' k' hk'))⟩

def IsScalar (ψ : AddChar (AF D.host.F) ℂ) (of oi : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (p : GA D S × GA D T)
    (c : ℂ) : Prop :=
  ∀ f, IsThetaFunO ψ S T f → of p (oi p f) = c • subst p f

theorem exists_isScalar (hψ : IsStdChar D ψ (-1)) (hf : IsFinWeil ψ S T ΛS ΛT χS χT of) (hi : IsInfWeil ψ θ S T oi)
    {p : GA D S × GA D T} (h1 : p.1 ∈ GQ S) (h2 : p.2 ∈ GQ T) : ∃ c : ℂ, ‖c‖ = 1 ∧ IsScalar ψ of oi p c := by
  have R := GlobalTheory.T.rational_substitution_theta_heisenberg_unitary D ψ hψ S T _ (inv_mem h1) _ (inv_mem h2)
  have R' := GlobalTheory.T.rational_substitution_theta_heisenberg_unitary D ψ hψ S T _ h1 _ h2
  obtain ⟨a, k, a1, a2, k1, k2, e1, e2⟩ := exists_parts p
  have hoi : ∀ f, IsThetaFunO ψ S T f → oi p f = oi a f := fun f h => by
    rw [e1, map_mul, Module.End.mul_apply, hi.triv k.1 k1 k.2 k2 f h]
  have hof : ∀ f, IsThetaFunO ψ S T f → of p f = of k f := fun f h => by
    rw [e2, map_mul, Module.End.mul_apply, hf.triv a.1 a1 a.2 a2 f h]
  have hth : ∀ u f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (heisO ψ S T u f) :=
    fun u f h => by
      have e : u = realIdem D • u + (1 - realIdem D) • u := by rw [← add_smul, add_sub_cancel, one_smul]
      rw [e, heisO_add_of_orth ψ S T (symplO_real_fin S T (real_smul_real u) (fin_smul_fin u))]
      exact GlobalTheory.WeilVacMove.isTheta_heisO_real hψ (real_smul_real u)
        (GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (fin_smul_fin u) h)
  obtain ⟨c, hc, h⟩ := GlobalTheory.T.schurLemma_thetaFunctions_orientedPair D ψ hψ S T (of p * oi p * subst p⁻¹)
    (fun f h => hf.pres _ _ (hi.pres _ _ (R f h).1))
    (fun w f h => by
      have t1 : IsThetaFunO ψ S T (subst p⁻¹ f) := (R f h).1
      have t2 : subst p⁻¹ (heisO ψ S T w f) = heisO ψ S T (actO S T p.1⁻¹ p.2⁻¹ w) (subst p⁻¹ f) := (R f h).2.1 w
      simp only [Module.End.mul_apply]
      rw [t2, hoi _ (hth _ _ t1), hi.Heisenberg₂ a.1 a1 a.2 a2 _ _ t1, hof _ (hth _ _ (hi.pres _ _ t1)),
        hf.Heisenberg₂ k.1 k1 k.2 k2 _ _ (hi.pres _ _ t1), ← act_mul, ← act_mul, ← hof _ (hi.pres _ _ t1), ← hoi _ t1,
        show k.1 * a.1 = p.1 from congrArg Prod.fst e2.symm, show k.2 * a.2 = p.2 from congrArg Prod.snd e2.symm,
        mul_inv_cancel, mul_inv_cancel, act_one])
    (fun μ 𝓕 hμ h𝓕 f h => by
      have t1 : IsThetaFunO ψ S T (subst p⁻¹ f) := (R f h).1
      simp only [Module.End.mul_apply]
      rw [hf.unit μ 𝓕 hμ h𝓕 _ _ (hi.pres _ _ t1), hi.unit μ 𝓕 hμ h𝓕 _ _ t1]
      exact (R f h).2.2 μ 𝓕 hμ h𝓕)
  refine ⟨c, hc, fun f hf' => ?_⟩
  have := h (subst p f) (R' f hf').1
  simp only [Module.End.mul_apply] at this
  rwa [← subst_mul, inv_mul_cancel, subst_one] at this

theorem IsScalar.unique (hψ : IsStdChar D ψ (-1)) {p : GA D S × GA D T} {c c' : ℂ} (h : IsScalar ψ of oi p c)
    (h' : IsScalar ψ of oi p c') : c = c' := by
  obtain ⟨f, hf, f0⟩ := GlobalTheory.Mem.ThetaNonzero.exists_thetaO_ne_zero hψ S T
  refine smul_left_injective ℂ (m := subst p f) (fun e => f0 ?_) ((h f hf).symm.trans (h' f hf))
  rw [← subst_one (S := S) (T := T) f, ← inv_mul_cancel p, subst_mul, e, map_zero]

theorem IsScalar.mul (hψ : IsStdChar D ψ (-1)) (hi : IsInfWeil ψ θ S T oi)
    (hcomm : ∀ p q f, IsThetaFunO ψ S T f → of p (oi q f) = oi q (of p f)) {p q : GA D S × GA D T} {c c' : ℂ}
    (h : IsScalar ψ of oi p c) (h' : IsScalar ψ of oi q c') (h1 : q.1 ∈ GQ S) (h2 : q.2 ∈ GQ T) :
    IsScalar ψ of oi (p * q) (c * c') := fun f hf => by
  have t : IsThetaFunO ψ S T (subst q f) := (GlobalTheory.T.rational_substitution_theta_heisenberg_unitary D ψ hψ S T _ h1 _ h2 f hf).1
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hcomm q p _ (hi.pres _ _ hf), h' f hf, map_smul,
    map_smul, h _ t, smul_smul, mul_comm c', subst_mul]

theorem oi_comm (hψ : IsStdChar D ψ (-1)) (hi : IsInfWeil ψ θ S T oi) {w : 𝓞 D.host.E} {lam : ℕ →* ℂ}
    {Om : GA D S × GA D T →* Module.End ℂ (thetaSub ψ S T)} (h : IsLatRep hψ.1 ΛS ΛT w lam Om)
    (hof : ∀ p, ∃ z : ℂ, ∀ f : thetaSub ψ S T, of p f = z • (Om p f : WO S T → ℂ)) (p q : GA D S × GA D T)
    (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f) : of p (oi q f) = oi q (of p f) := by
  obtain ⟨z, hz⟩ := hof p
  obtain ⟨a, k, a1, a2, k1, k2, e1, -⟩ := exists_parts q
  have hoi : ∀ f, IsThetaFunO ψ S T f → oi q f = oi a f := fun f h => by
    rw [e1, map_mul, Module.End.mul_apply, hi.triv k.1 k1 k.2 k2 f h]
  let L : thetaSub ψ S T →ₗ[ℂ] thetaSub ψ S T := (oi q).restrict fun f hf => hi.pres q f hf
  have hL : ∀ m, (L m : WO S T → ℂ) = oi q m := fun _ => rfl
  have := congrArg Subtype.val (h.comm L (fun x v => Subtype.ext (by
    have e : actO S T a.1 a.2 x = x := congrArg XF.val (rhoF_real a1 a2 x)
    rw [hL, coe_opF, coe_opF, hL, map_smul, hoi _ (GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 x.fin v.2),
      hi.Heisenberg₂ a.1 a1 a.2 a2 _ _ v.2, e, ← hoi _ v.2])) p ⟨f, hf⟩)
  rw [hz ⟨f, hf⟩, map_smul, ← hL, ← this]
  exact hz (L ⟨f, hf⟩)

end Operators

section Finite

variable {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

def finL (S T : HSp D) : Matrix (Fin T.rank) (Fin S.rank) D.host.E →ₗ[𝓞 D.host.E] XF S T where
  toFun x := XF.mk (finRat S T x) (finRat_inf S T x)
  map_add' x y := XF.ext (map_add (finRat S T) x y)
  map_smul' r x := XF.ext (finRat_smul S T (r : D.host.E) x)

theorem isHeis_gamQ (hψ : IsCharAF D.host.F ψ) (S T : HSp D) {w : 𝓞 D.host.E} (hw : w + sgO D w = 1) :
    IsHeis (sgO D) w (gamQ ψ S T) fun x => opF hψ S T w (finL S T x) := by
  have H := isHeis_opF hψ S T hw
  have e : ∀ x y, gamQ ψ S T x y = gamF ψ S T (finL S T x) (finL S T y) := fun _ _ => rfl
  exact ⟨H.sg_sg, H.w_add, fun x y z => by rw [e, e, e, map_add, H.add_left],
    fun x y z => by rw [e, e, e, map_add, H.add_right], fun x => by rw [e, H.alt],
    fun r x y => by rw [e, e, map_smul, map_smul, H.adj], fun v => by rw [map_zero, H.zero],
    fun x y v => by rw [H.comp, e, map_smul, map_add]⟩

theorem finRat_sandw {g : GA D S} {h : GA D T} {a b} (ha : IsRat S g a) (hb : IsRat T h⁻¹ b)
    (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : finRat S T (b * x * a) = actO S T g⁻¹ h⁻¹ (finRat S T x) := by
  rw [finRat_eq, finRat_eq, actO_smul, actO, inv_inv, show Formalism.L2.Theta.mt S g = _ from ha,
    show Formalism.L2.Theta.mt T h⁻¹ = _ from hb, ratW, ratW, Matrix.map_mul, Matrix.map_mul]

theorem finite_data (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {lam : ℕ →* ℂ}
    (hlam : GoodNorm (sgO D) lam) {w : 𝓞 D.host.E} (hw : w + sgO D w = 1) {g : GA D S} {h : GA D T} {a b}
    (ha : IsRat S g a) (hb : IsRat T h⁻¹ b) (hΔ : (b ⊗ₖ aᵀ).det ≠ 0) (hd : (b ⊗ₖ aᵀ - 1).det ≠ 0) :
    Function.Bijective (fun x : Matrix (Fin T.rank) (Fin S.rank) D.host.E => b * x * a - x) ∧
    ∃ (n : ℕ) (t : Fin n → Matrix (Fin T.rank) (Fin S.rank) D.host.E) (c N M : ℕ), n ≠ 0 ∧ c ≠ 0 ∧ N ≠ 0 ∧
      (∀ k, b * t k * a - t k ∈ latQ S T ΛS ΛT) ∧
      (∀ y, b * y * a - y ∈ latQ S T ΛS ΛT → ∃! k, y - t k ∈ latQ S T ΛS ΛT) ∧
      ∑ k, gamQ ψ S T (sgO D w • (b * t k * a - t k)) (t k) = lam n ∧ lam n ^ 2 = n ∧
      ((c * n : ℕ) : ℚ) = |Algebra.norm ℚ ((N : D.host.E) ^ M * (b ⊗ₖ aᵀ - 1).det)| ∧
      ((c * idx (latF S T ΛS ΛT) ((latF S T ΛS ΛT).map (rhoF S T (g, h))) : ℕ) : ℚ) =
        |Algebra.norm ℚ ((N : D.host.E) ^ M * (b ⊗ₖ aᵀ).det)| := by
  obtain ⟨sd, fg, full, hidx⟩ := GlobalTheory.T.rational_lattice_selfDual_fg_full_index D ψ hψ S T ΛS ΛT hS hT
  rw [hidx g h a b ha hb]
  rw [← det_sandw] at hΔ ⊢
  rw [← det_sandw_sub_one] at hd ⊢
  have hbij : Function.Bijective ⇑(sandw b a - 1) :=
    (Module.End.isUnit_iff _).1 ((LinearMap.isUnit_iff_isUnit_det _).2 hd.isUnit)
  refine ⟨hbij, ?_⟩
  set A := (latQ S T ΛS ΛT).toAddSubgroup with hA
  obtain ⟨N, hN, hNA⟩ : ∃ N : ℕ, N ≠ 0 ∧ ∀ x ∈ A, N • sandw b a x ∈ A := by
    obtain ⟨s, hs⟩ := fg
    choose k hk hk' using full
    refine ⟨∏ y ∈ s, k (sandw b a y), Finset.prod_ne_zero_iff.2 fun y _ => (hk _).ne', fun x hx => ?_⟩
    rw [← hs] at hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun y => k (sandw b a y)) hx
      rw [hm, mul_comm, mul_smul]
      exact nsmul_mem (hk' _) m
    | zero => rw [map_zero, smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add, smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg, smul_neg]; exact neg_mem hx
  have i1 := GlobalTheory.T.relIndex_map_nsmul_comap_eq_abs_norm_pow_mul_det _ _ A fg full (sandw b a - 1) N hN hd fun x hx => by
    rw [LinearMap.sub_apply, smul_sub]
    exact sub_mem (hNA x hx) (nsmul_mem hx N)
  have i2 := GlobalTheory.T.relIndex_map_nsmul_comap_eq_abs_norm_pow_mul_det _ _ A fg full (sandw b a) N hN hΔ hNA
  set B₁ := A.comap (sandw b a - 1).toAddMonoidHom with hB₁
  set B₂ := A.comap (sandw b a).toAddMonoidHom with hB₂
  set NA := A.map (N • AddMonoidHom.id _) with hNA'
  have e12 : A ⊓ B₁ = A ⊓ B₂ := by
    ext x
    refine and_congr_right fun hx => ?_
    show sandw b a x - x ∈ A ↔ sandw b a x ∈ A
    exact ⟨fun h => by simpa using add_mem h hx, fun h => sub_mem h hx⟩
  have hle : NA ≤ A ⊓ B₂ := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨nsmul_mem hx N, ?_⟩
    show sandw b a (N • x) ∈ A
    rw [map_nsmul]
    exact hNA x hx
  have m1 := AddSubgroup.relIndex_mul_relIndex NA (A ⊓ B₁) B₁ (e12 ▸ hle) inf_le_right
  have m2 := AddSubgroup.relIndex_mul_relIndex NA (A ⊓ B₂) B₂ hle inf_le_right
  rw [AddSubgroup.inf_relIndex_right] at m1 m2
  rw [e12] at m1
  have h0 : NA.relIndex (A ⊓ B₂) * A.relIndex B₁ ≠ 0 := by
    rw [m1, ← Nat.cast_ne_zero (R := ℚ), i1, abs_ne_zero, Algebra.norm_ne_zero_iff]
    exact mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 hN)) hd
  obtain ⟨t, t1, t2⟩ := exists_transversal A B₁ (right_ne_zero_of_mul h0)
  obtain ⟨g1, g2⟩ := gauss_isometry (isHeis_gamQ hψ.1 S T hw) hlam sd ((sandw b a).restrictScalars (𝓞 D.host.E))
    (fun x y => by
      show ψ (symplO S T (finRat S T (b * x * a)) (finRat S T (b * y * a))) = _
      rw [finRat_sandw ha hb, finRat_sandw ha hb, GlobalTheory.T.symplecticForm_unitaryPairAction]
      rfl) hbij.2 _ t t1 t2
  exact ⟨_, t, _, N, _, right_ne_zero_of_mul h0, left_ne_zero_of_mul h0, hN, t1, t2, g1, g2, m1 ▸ i1, m2 ▸ i2⟩

end Finite

end GlobalTheory.RatAut

end
