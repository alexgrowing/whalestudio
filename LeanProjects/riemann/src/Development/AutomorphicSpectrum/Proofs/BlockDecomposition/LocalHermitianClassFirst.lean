import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonsplitCentraliserNormElement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramKernelSignNonsplitBaseChangeEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormSignatureRealisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinprodNonsplitSignTotallyPositiveEqOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCyclicVectorOfSeparable
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

noncomputable section
namespace GlobalTheory.CompanionTheory.LocalSignInert

section Gram
variable {K : Type} [Field K] (σ : K →+* K) {n : ℕ}

theorem hform_mul_right (H M : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    hform σ (H * M) x y = hform σ H x (M *ᵥ y) := by
  simp only [hform, Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_sum_smul {ι : Type} [Fintype ι] (H : Matrix (Fin n) (Fin n) K) (x : Fin n → K)
    (c : ι → K) (f : ι → Fin n → K) :
    hform σ H x (∑ l, c l • f l) = ∑ l, hform σ H x (f l) * c l := by
  simp only [hform, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

def restr (M : Matrix (Fin n) (Fin n) K) (V : Submodule K (Fin n → K)) (hM : ∀ y ∈ V, M *ᵥ y ∈ V) : V →ₗ[K] V :=
  (Matrix.toLin' M).restrict fun y hy => by rw [Matrix.toLin'_apply]; exact hM y hy

theorem restr_coe (M : Matrix (Fin n) (Fin n) K) (V : Submodule K (Fin n → K)) (hM : ∀ y ∈ V, M *ᵥ y ∈ V) (y : V) :
    (restr M V hM y : Fin n → K) = M *ᵥ (y : Fin n → K) := by
  simp [restr, Matrix.toLin'_apply]

theorem det_gramOn_mul (H M : Matrix (Fin n) (Fin n) K) (V : Submodule K (Fin n → K))
    (hM : ∀ y ∈ V, M *ᵥ y ∈ V) :
    (gramOn σ (H * M) V).det = (gramOn σ H V).det * LinearMap.det (restr M V hM) := by
  set b := Module.finBasis K V
  have hmat : gramOn σ (H * M) V = gramOn σ H V * LinearMap.toMatrix b b (restr M V hM) := by
    ext i j
    have hT : M *ᵥ (b j : Fin n → K) = ∑ l, (LinearMap.toMatrix b b (restr M V hM) l j) • (b l : Fin n → K) := by
      rw [← restr_coe M V hM]
      have h := b.sum_repr (restr M V hM (b j))
      calc ((restr M V hM (b j) : V) : Fin n → K) = ((∑ l, b.repr (restr M V hM (b j)) l • b l : V) : Fin n → K) := by
            rw [h]
        _ = _ := by simp only [AddSubmonoidClass.coe_finset_sum, Submodule.coe_smul, LinearMap.toMatrix_apply]
    simp only [gramOn, Matrix.of_apply, Matrix.mul_apply]
    rw [hform_mul_right, hT, hform_sum_smul]
  rw [hmat, Matrix.det_mul, LinearMap.det_toMatrix]

end Gram

section Core
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Q : SelfRecip E r)
  {k K : Type} [Field k] [Algebra (maximalRealSubfield E) k] [Field K]
  (φ : E →+* K) (cm : k →+* K)
  (hc : ∀ a : maximalRealSubfield E, cm (algebraMap _ k a) = φ (algebraMap _ E a))
  {n : ℕ} (ψ : Fld Q →ₗ[E] (Fin n → E))

include hc in

def vecT : k ⊗[maximalRealSubfield E] Fld Q →+ (Fin n → K) :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun a : k => AddMonoidHom.mk' (fun y : Fld Q => cm a • (φ ∘ ψ y))
        (fun y y' => by
          ext i
          simp [mul_add]))
      (fun a a' => by
        ext y i
        simp [add_mul]))
    (fun s a y => by
      have e1 : s • y = algebraMap (maximalRealSubfield E) E s • y := (algebraMap_smul E s y).symm
      have e2 : cm (s • a) = φ (algebraMap (maximalRealSubfield E) E s) * cm a := by
        rw [Algebra.smul_def, map_mul, hc]
      funext i
      show cm (s • a) * φ (ψ y i) = cm a * φ (ψ (s • y) i)
      rw [e2, e1, map_smul, Pi.smul_apply, smul_eq_mul, map_mul]
      ring)

theorem vecT_tmul (a : k) (y : Fld Q) : vecT Q φ cm hc ψ (a ⊗ₜ y) = cm a • (φ ∘ ψ y) := rfl

theorem vecT_smul (a : k) (t : k ⊗[maximalRealSubfield E] Fld Q) :
    vecT Q φ cm hc ψ (a • t) = cm a • vecT Q φ cm hc ψ t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul b y => rw [TensorProduct.smul_tmul', vecT_tmul, vecT_tmul, smul_eq_mul, map_mul, mul_smul]
  | add s t hs ht => rw [smul_add, map_add, map_add, hs, ht, smul_add]

variable (j : K ≃+* k ⊗[maximalRealSubfield E] E) (hj : ∀ a e, j.symm (a ⊗ₜ e) = cm a * φ e)
  (A₀ : Matrix (Fin n) (Fin n) E) (hψ : ∀ y, ψ (alpha Q * y) = A₀ *ᵥ ψ y)

include hj in
theorem vecT_inclBase (u : k ⊗[maximalRealSubfield E] E) (t : k ⊗[maximalRealSubfield E] Fld Q) :
    vecT Q φ cm hc ψ (inclBase Q k u * t) = j.symm u • vecT Q φ cm hc ψ t := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, add_mul, map_add, ha, hb, map_add, add_smul]
  | tmul a e =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add s t hs ht => rw [mul_add, map_add, hs, ht, map_add, smul_add]
    | tmul b y =>
      have e1 : inclBase Q k (a ⊗ₜ e) = a ⊗ₜ algebraMap E (Fld Q) e := rfl
      rw [e1, Algebra.TensorProduct.tmul_mul_tmul, vecT_tmul, vecT_tmul, hj, ← Algebra.smul_def, map_smul]
      ext i
      simp
      ring

include hψ in
theorem vecT_alpha (t : k ⊗[maximalRealSubfield E] Fld Q) :
    vecT Q φ cm hc ψ (((1 : k) ⊗ₜ alpha Q) * t) = (A₀.map φ) *ᵥ vecT Q φ cm hc ψ t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add s t hs ht => rw [mul_add, map_add, hs, ht, map_add, Matrix.mulVec_add]
  | tmul b y =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, vecT_tmul, vecT_tmul, hψ, Matrix.mulVec_smul]
    congr 1
    ext i
    exact RingHom.map_mulVec φ A₀ (ψ y) i

include hj hψ in

theorem vecT_eval (m : K[X]) : ∀ t : k ⊗[maximalRealSubfield E] Fld Q,
    vecT Q φ cm hc ψ (eval₂RingHom ((inclBase Q k).toRingHom.comp j.toRingHom) ((1 : k) ⊗ₜ alpha Q) m * t) =
      aeval (A₀.map φ) m *ᵥ vecT Q φ cm hc ψ t := by
  induction m using Polynomial.induction_on with
  | C a =>
    intro t
    have e1 : eval₂RingHom ((inclBase Q k).toRingHom.comp j.toRingHom) ((1 : k) ⊗ₜ alpha Q) (C a) =
        inclBase Q k (j a) := by simp
    rw [e1, vecT_inclBase Q φ cm hc ψ j hj, aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
      Matrix.one_mulVec, RingEquiv.symm_apply_apply]
  | add p q hp hq =>
    intro t
    rw [map_add, add_mul, map_add, hp, hq, map_add, Matrix.add_mulVec]
  | monomial d a ih =>
    intro t
    have e1 : (C a * X ^ (d + 1) : K[X]) = (C a * X ^ d) * X := by rw [pow_succ, mul_assoc]
    have e2 : eval₂RingHom ((inclBase Q k).toRingHom.comp j.toRingHom) ((1 : k) ⊗ₜ alpha Q) X = (1 : k) ⊗ₜ alpha Q := by
      simp
    have e3 : eval₂RingHom ((inclBase Q k).toRingHom.comp j.toRingHom) ((1 : k) ⊗ₜ alpha Q) ((C a * X ^ d) * X) * t =
        eval₂RingHom ((inclBase Q k).toRingHom.comp j.toRingHom) ((1 : k) ⊗ₜ alpha Q) (C a * X ^ d) *
          (((1 : k) ⊗ₜ alpha Q) * t) := by
      rw [RingHom.map_mul _ (C a * X ^ d) X, e2, mul_assoc]
    have e4 : aeval (A₀.map φ) ((C a * X ^ d) * X) = aeval (A₀.map φ) (C a * X ^ d) * A₀.map φ := by
      rw [map_mul (aeval (A₀.map φ)) (C a * X ^ d) X, aeval_X]
    rw [e1, e3, ih, e4, ← Matrix.mulVec_mulVec, vecT_alpha Q φ cm hc ψ A₀ hψ]

theorem det_restr_eq (b : Module.Basis (Fin r) (maximalRealSubfield E) (plus Q)) (B : Module.Basis (Fin r) E (Fld Q))
    (hB : ∀ i, B i = b i) (V : Submodule K (Fin n → K)) (cB : Module.Basis (Fin r) K V)
    (hcB : ∀ i, (cB i : Fin n → K) = φ ∘ ψ (B i)) (M : Matrix (Fin n) (Fin n) K) (hM : ∀ y ∈ V, M *ᵥ y ∈ V)
    (x : k ⊗[maximalRealSubfield E] plus Q)
    (hMx : ∀ t, vecT Q φ cm hc ψ (inclPlus Q k x * t) = M *ᵥ vecT Q φ cm hc ψ t) :
    LinearMap.det (restr M V hM) = cm (Algebra.norm k x) := by
  let bb : Module.Basis (Fin r) k (k ⊗[maximalRealSubfield E] plus Q) := Algebra.TensorProduct.basis k b
  let L := Algebra.leftMulMatrix bb x
  have h1 : ∀ i, bb i = (1 : k) ⊗ₜ b i := fun i => Algebra.TensorProduct.basis_apply b i
  have h2 : ∀ j, x * ((1 : k) ⊗ₜ b j) = ∑ i, L i j • ((1 : k) ⊗ₜ[maximalRealSubfield E] b i) := by
    intro j
    simp only [L, Algebra.leftMulMatrix_eq_repr_mul, ← h1]
    exact (bb.sum_repr _).symm
  have h3 : ∀ i, inclPlus Q k ((1 : k) ⊗ₜ b i) = (1 : k) ⊗ₜ B i := fun i => by
    rw [hB]; rfl
  have h4 : ∀ j, inclPlus Q k x * ((1 : k) ⊗ₜ B j) = ∑ i, L i j • ((1 : k) ⊗ₜ[maximalRealSubfield E] B i) := by
    intro j
    rw [← h3, ← map_mul, h2, map_sum]
    simp only [map_smul, h3]
  have h5 : ∀ i, vecT Q φ cm hc ψ ((1 : k) ⊗ₜ B i) = (cB i : Fin n → K) := by
    intro i
    rw [vecT_tmul, map_one, one_smul, hcB]
  have h6 : ∀ j, M *ᵥ (cB j : Fin n → K) = ∑ i, cm (L i j) • (cB i : Fin n → K) := by
    intro j
    rw [← h5, ← hMx, h4, map_sum]
    simp only [vecT_smul, h5]
  have h7 : LinearMap.toMatrix cB cB (restr M V hM) = L.map cm := by
    ext i j
    have e : restr M V hM (cB j) = ∑ l, cm (L l j) • cB l := Subtype.ext (by
      rw [restr_coe, h6]; simp)
    rw [LinearMap.toMatrix_apply, e, Module.Basis.repr_sum_self]
    rfl
  rw [← LinearMap.det_toMatrix cB, h7, Algebra.norm_eq_matrix_det bb, RingHom.map_det]
  rfl

end Core

section Psi
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Q : SelfRecip E r)

theorem exists_psi {n : ℕ} (A : Matrix (Fin n) (Fin n) E) (hs : A.charpoly.Separable) (hQ : Q.1 ∣ A.charpoly) :
    ∃ ψ : Fld Q →ₗ[E] (Fin n → E), Function.Injective ψ ∧ (∀ y, ψ (alpha Q * y) = A *ᵥ ψ y) ∧
      LinearMap.range ψ = LinearMap.ker (Matrix.toLin' (aeval A Q.1)) := by
  obtain ⟨v, hv⟩ := GlobalTheory.CompanionTheory.TorusCh.CyclicVector.exists_cyclic_vector E n A hs
  have hann : ∀ h : E[X], aeval A h *ᵥ v = 0 → A.charpoly ∣ h := by
    intro h hh
    refine GlobalTheory.ClassParam.charpoly_dvd_of_aeval A hs h ?_
    have h1 : ∀ y, aeval A h *ᵥ y = 0 := by
      intro y
      obtain ⟨g, rfl⟩ := hv y
      rw [Matrix.mulVec_mulVec, ← map_mul, mul_comm, map_mul, ← Matrix.mulVec_mulVec, hh, Matrix.mulVec_zero]
    have h2 : Matrix.toLin' (aeval A h) = 0 := LinearMap.ext fun y => by
      rw [Matrix.toLin'_apply, h1 y]; rfl
    exact Matrix.toLin'.injective (by rw [h2, map_zero])
  obtain ⟨R, hR⟩ := hQ
  have hP0 : A.charpoly ≠ 0 := (Matrix.charpoly_monic A).ne_zero
  have hQ0 : Q.1 ≠ 0 := fun h => hP0 (by rw [hR, h, zero_mul])
  have hR0 : R ≠ 0 := fun h => hP0 (by rw [hR, h, mul_zero])
  obtain ⟨e₀, he₀⟩ : ∃ e : Fin n → E, e = aeval A R *ᵥ v := ⟨_, rfl⟩
  have hkill : ∀ u : E[X], aeval A (Q.1 * u) *ᵥ e₀ = 0 := by
    intro u
    rw [he₀, Matrix.mulVec_mulVec, ← map_mul, show Q.1 * u * R = u * (Q.1 * R) by ring, ← hR, map_mul,
      Matrix.aeval_self_charpoly, mul_zero, Matrix.zero_mulVec]
  have hmk : ∀ g g' : E[X], AdjoinRoot.mk Q.1 g = AdjoinRoot.mk Q.1 g' → aeval A g *ᵥ e₀ = aeval A g' *ᵥ e₀ := by
    intro g g' h
    obtain ⟨u, hu⟩ : Q.1 ∣ g - g' := AdjoinRoot.mk_eq_mk.1 h
    have h1 := hkill u
    rw [← hu, map_sub, Matrix.sub_mulVec, sub_eq_zero] at h1
    exact h1
  let rep : Fld Q → E[X] := fun y => (AdjoinRoot.mk_surjective (g := Q.1) y).choose
  have hrep : ∀ y : Fld Q, AdjoinRoot.mk Q.1 (rep y) = y := fun y =>
    (AdjoinRoot.mk_surjective (g := Q.1) y).choose_spec
  have hsm : ∀ (c : E) (g : E[X]), AdjoinRoot.mk Q.1 (c • g) = (c • (AdjoinRoot.mk Q.1 g : Fld Q) : Fld Q) := by
    intro c g
    rw [Polynomial.smul_eq_C_mul, map_mul, AdjoinRoot.mk_C, Algebra.smul_def]
    rfl
  let ψ : Fld Q →ₗ[E] (Fin n → E) :=
    { toFun := fun y => aeval A (rep y) *ᵥ e₀
      map_add' := fun y y' => by
        rw [← Matrix.add_mulVec, ← map_add]
        refine hmk _ _ ?_
        rw [map_add, hrep, hrep, hrep]
        rfl
      map_smul' := fun c y => by
        rw [RingHom.id_apply, ← Matrix.smul_mulVec, ← map_smul]
        refine hmk _ _ ?_
        rw [hsm, hrep, hrep]
        rfl }
  have hψ : ∀ g : E[X], ψ (AdjoinRoot.mk Q.1 g) = aeval A g *ᵥ e₀ := fun g => hmk _ _ (hrep _)
  refine ⟨ψ, (injective_iff_map_eq_zero _).2 fun y hy => ?_, fun y => ?_, ?_⟩
  · obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective (g := Q.1) y
    rw [hψ, he₀, Matrix.mulVec_mulVec, ← map_mul] at hy
    have h1 : A.charpoly ∣ g * R := hann _ hy
    rw [hR] at h1
    exact AdjoinRoot.mk_eq_zero.2 ((mul_dvd_mul_iff_right hR0).1 h1)
  · obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective (g := Q.1) y
    have h1 : ∀ z : Fld Q, z = AdjoinRoot.mk Q.1 g → alpha Q * z = AdjoinRoot.mk Q.1 (X * g) := by
      intro z hz
      rw [hz, map_mul, AdjoinRoot.mk_X]
      rfl
    rw [h1 _ rfl, hψ, hψ, map_mul, aeval_X, ← Matrix.mulVec_mulVec]
  · ext y
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective (g := Q.1) z
      rw [LinearMap.mem_ker, Matrix.toLin'_apply, hψ, Matrix.mulVec_mulVec, ← map_mul]
      exact hkill g
    · intro hy
      obtain ⟨h, rfl⟩ := hv y
      rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← map_mul] at hy
      have h1 : A.charpoly ∣ Q.1 * h := hann _ hy
      rw [hR] at h1
      obtain ⟨g, hg⟩ := (mul_dvd_mul_iff_left hQ0).1 h1
      refine ⟨AdjoinRoot.mk Q.1 g, ?_⟩
      rw [hψ, he₀, Matrix.mulVec_mulVec, ← map_mul, hg, mul_comm]

theorem exists_basis_ker {K : Type} [Field K] (φ : E →+* K) {n : ℕ} (ψ : Fld Q →ₗ[E] (Fin n → E))
    (hinj : Function.Injective ψ) (B : Module.Basis (Fin r) E (Fld Q)) (B₀ : Matrix (Fin n) (Fin n) E)
    (hr : LinearMap.range ψ = LinearMap.ker (Matrix.toLin' B₀)) :
    ∃ cB : Module.Basis (Fin r) K (LinearMap.ker (Matrix.toLin' (B₀.map φ))),
      ∀ i, (cB i : Fin n → K) = φ ∘ ψ (B i) := by
  letI := φ.toAlgebra
  haveI : FaithfulSMul E K := (faithfulSMul_iff_algebraMap_injective E K).2 φ.injective
  set V' := LinearMap.ker (Matrix.toLin' (B₀.map φ)) with hV'
  have hmem : ∀ i, φ ∘ ψ (B i) ∈ V' := fun i =>
    GlobalTheory.UnitaryClasses.BaseChangeSign.mem_ker_map φ (hr ▸ LinearMap.mem_range_self ψ (B i))
  have hfr : Module.finrank K V' = r := by
    rw [hV', GlobalTheory.UnitaryClasses.BaseChangeSign.finrank_ker_map φ B₀, ← hr, LinearMap.finrank_range_of_inj hinj,
      finrank_fld]
  have hr0 : 0 < r := by
    have h1 := Q.2.2.2.1
    have h2 := Irreducible.natDegree_pos Q.2.2.1
    omega
  haveI : Nonempty (Fin r) := ⟨⟨0, hr0⟩⟩
  let u : Fin r → V' := fun i => ⟨φ ∘ ψ (B i), hmem i⟩
  have hli : LinearIndependent K u := by
    apply LinearIndependent.of_comp V'.subtype
    have h0 : LinearIndependent E (fun i => ψ (B i)) :=
      B.linearIndependent.map' ψ (LinearMap.ker_eq_bot.2 hinj)
    exact linearIndependent_algebraMap_comp_iff.2 h0
  let c := basisOfLinearIndependentOfCardEqFinrank hli (by rw [hfr, Fintype.card_fin])
  exact ⟨c, fun i => by simp [c, u]⟩

end Psi

section Sign
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem sign_complMap (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    (hv : w.under (𝓞 (maximalRealSubfield E)) = v) (a : (v.adicCompletion (maximalRealSubfield E))ˣ) :
    (-1 : ℂ) ^ ordL (GlobalTheory.LFun.complMap hv (a : v.adicCompletion (maximalRealSubfield E))) =
      ((GlobalTheory.QuadSymbol.eta (maximalRealSubfield E) E (v.adicCompletion (maximalRealSubfield E)) a : ℤ) : ℂ) := by
  subst hv
  rw [GlobalTheory.TotPosSign.eta_inert (GlobalTheory.TotPosSign.not_isSplit_under hw) (GlobalTheory.TotPosSign.isUnram_of_unr hU _),
    GlobalTheory.TotPosSign.neg_one_zpow_cast]
  congr 1
  refine GlobalTheory.TotPosSign.ordL_congr ?_
  have e := GlobalTheory.LFun.valued_complMap (F := maximalRealSubfield E) (E := E) (w := w) rfl
    (a := (a : (w.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E))) a.ne_zero
  rw [GlobalTheory.LFun.isUnram_iff.1 (GlobalTheory.TotPosSign.isUnram_of_unr hU _) w rfl, pow_one] at e
  exact e

end Sign

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v), ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) → ∀ (m : (w.adicCompletion E)[X]) (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → ∀ x : ((v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q)ˣ, inclPlus Q (v.adicCompletion (maximalRealSubfield E)) (x : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q) = locPhi hU w hw v hv Q m → sgnOn (cj w) ((H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m) (atPl w Q.1) (γ₀.val.map (algebraMap E (w.adicCompletion E))) = ((GlobalTheory.QuadSymbol.eta (maximalRealSubfield E) E (v.adicCompletion (maximalRealSubfield E)) (Units.map (Algebra.norm (v.adicCompletion (maximalRealSubfield E)) : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q →* (v.adicCompletion (maximalRealSubfield E))) x) : ℤ) : ℂ) * sgnOn (cj w) (H₀.map (algebraMap E (w.adicCompletion E))) (atPl w Q.1) (γ₀.val.map (algebraMap E (w.adicCompletion E))) := by
  intro E _ _ _ hU w hw v hv n γ₀ hell H₀ _ _ _ hpos m r Q hQ x hx
  have hsep : γ₀.val.charpoly.Separable := hell.2.2.1
  obtain ⟨ψ, hinj, hαψ, hrange⟩ := exists_psi Q γ₀.val hsep hQ
  obtain ⟨θ, h0, hθ⟩ : ∃ θ : E, θ ≠ 0 ∧ IsCMField.complexConj E θ = -θ := by
    obtain ⟨z, hz⟩ : ∃ z : E, IsCMField.complexConj E z ≠ z := by
      by_contra h
      push_neg at h
      exact IsCMField.complexConj_ne_one E (AlgEquiv.ext h)
    exact ⟨z - IsCMField.complexConj E z, sub_ne_zero.mpr hz.symm, by simp⟩
  obtain ⟨b, B, hB⟩ := GlobalTheory.TraceClasses.exists_bases Q h0 hθ
  have hcm : ∀ a : maximalRealSubfield E, GlobalTheory.LFun.complMap hv (algebraMap _ (v.adicCompletion (maximalRealSubfield E)) a) =
      algebraMap E (w.adicCompletion E) (algebraMap _ E a) := GlobalTheory.LFun.complMap_algebraMap hv
  have hj : ∀ a e, (locJ hU w hw v hv).symm (a ⊗ₜ e) = GlobalTheory.LFun.complMap hv a * algebraMap E (w.adicCompletion E) e :=
    fun a e => GlobalTheory.LFun.toCompl_tmul hv a e
  have hval := aeval_map_mat w γ₀.val Q.1
  unfold sgnOn
  rw [hval]
  set A := γ₀.val.map (algebraMap E (w.adicCompletion E)) with hA
  set V := LinearMap.ker (Matrix.toLin' ((aeval γ₀.val Q.1).map (algebraMap E (w.adicCompletion E)))) with hV
  obtain ⟨cB, hcB⟩ := exists_basis_ker Q (algebraMap E (w.adicCompletion E)) ψ hinj B (aeval γ₀.val Q.1) hrange
  have hM : ∀ y ∈ V, aeval A m *ᵥ y ∈ V := by
    intro y hy
    rw [hV, LinearMap.mem_ker, Matrix.toLin'_apply] at hy ⊢
    rw [← hval] at hy ⊢
    rw [Matrix.mulVec_mulVec, ← map_mul, mul_comm, map_mul, ← Matrix.mulVec_mulVec, hy, Matrix.mulVec_zero]
  have hdet : LinearMap.det (restr (aeval A m) V hM) =
      GlobalTheory.LFun.complMap hv (Algebra.norm (v.adicCompletion (maximalRealSubfield E))
        (x : v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] plus Q)) := by
    refine det_restr_eq Q (algebraMap E (w.adicCompletion E)) (GlobalTheory.LFun.complMap hv) hcm ψ b B hB V cB hcB
      (aeval A m) hM _ fun t => ?_
    rw [hx]
    exact vecT_eval Q (algebraMap E (w.adicCompletion E)) (GlobalTheory.LFun.complMap hv) hcm ψ (locJ hU w hw v hv) hj
      γ₀.val hαψ m t
  have hφ : ∀ y : E, cj w (algebraMap E (w.adicCompletion E) y) =
      algebraMap E (w.adicCompletion E) ((IsCMField.complexConj E).toRingEquiv.toRingHom y) :=
    fun y => ((GlobalTheory.ConjAtPlace.main E hU w).2.2.2.1 hw).1 y
  obtain ⟨t, ht, hg⟩ := GlobalTheory.UnitaryClasses.BaseChangeSign.gram_det_map (IsCMField.complexConj E).toRingEquiv.toRingHom
    (cj w) (algebraMap E (w.adicCompletion E)) hφ H₀ (aeval γ₀.val Q.1)
  have hd0 := (gramOn_det_totallyPositive_of_posDef H₀ hpos (LinearMap.ker (Matrix.toLin' (aeval γ₀.val Q.1)))).1
  have hg0 : (gramOn (cj w) (H₀.map (algebraMap E (w.adicCompletion E))) V).det ≠ 0 := by
    rw [hV, hg]
    exact mul_ne_zero (mul_ne_zero ((_root_.map_ne_zero _).2 ht) ((_root_.map_ne_zero _).2 hd0)) ht
  have hs := sign_complMap hU w hw v hv (Units.map (Algebra.norm (v.adicCompletion (maximalRealSubfield E)) :
    (v.adicCompletion (maximalRealSubfield E)) ⊗[maximalRealSubfield E] plus Q →* (v.adicCompletion (maximalRealSubfield E))) x)
  have hn0 : GlobalTheory.LFun.complMap hv (Algebra.norm (v.adicCompletion (maximalRealSubfield E))
      (x : v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] plus Q)) ≠ 0 :=
    (_root_.map_ne_zero _).2 (Units.ne_zero (Units.map (Algebra.norm (v.adicCompletion (maximalRealSubfield E)) :
      (v.adicCompletion (maximalRealSubfield E)) ⊗[maximalRealSubfield E] plus Q →* (v.adicCompletion (maximalRealSubfield E))) x))
  rw [det_gramOn_mul (cj w) _ (aeval A m) V hM, hdet, GlobalTheory.UnitaryClasses.BaseChangeSign.ordL_mul hg0 hn0,
    zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), mul_comm, ← hs]
  rfl

end GlobalTheory.CompanionTheory.LocalSignInert
