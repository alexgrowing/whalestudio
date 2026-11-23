import Mathlib
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.ConjugateCharacterFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootsReverseProd

noncomputable section

open Polynomial CategoryTheory

namespace GlobalTheory.SerConj

open Formalism.IrreducibleCountingLemmas.TYPES

section Tensor

variable {ι : Type} {V W : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

def semiMap (σ : ℂ →+* ℂ) (j : ∀ i, V i →+ W i) (hj : ∀ i (a : ℂ) v, j i (a • v) = σ a • j i v) :
    PiTensorProduct ℂ V →+ PiTensorProduct ℂ W :=
  PiTensorProduct.liftAddHom (fun p => σ p.1 • PiTensorProduct.tprod ℂ fun i => j i (p.2 i))
    (fun r f i hf => by
      rw [MultilinearMap.map_coord_zero _ i (by simp [hf]), smul_zero])
    (fun f => by simp)
    (fun r f i m₁ m₂ => by
      have e : ∀ m : V i, (fun k => j k (Function.update f i m k)) =
          Function.update (fun k => j k (f k)) i (j i m) := fun m =>
        funext fun k => Function.apply_update (fun k => j k) f i m k
      simp only [e, map_add, MultilinearMap.map_update_add, smul_add])
    (fun r r' f => by simp [add_smul])
    (fun r f i r' => by
      have e : ∀ m : V i, (fun k => j k (Function.update f i m k)) =
          Function.update (fun k => j k (f k)) i (j i m) := fun m =>
        funext fun k => Function.apply_update (fun k => j k) f i m k
      simp only [e, hj, MultilinearMap.map_update_smul, Function.update_eq_self, map_mul, smul_smul, mul_comm])

theorem semiMap_tprod (σ : ℂ →+* ℂ) (j : ∀ i, V i →+ W i) (hj : ∀ i (a : ℂ) v, j i (a • v) = σ a • j i v)
    (a : ℂ) (f : ∀ i, V i) :
    semiMap σ j hj (a • PiTensorProduct.tprod ℂ f) = σ a • PiTensorProduct.tprod ℂ fun i => j i (f i) := by
  rw [← PiTensorProduct.tprodCoeff_eq_smul_tprod]
  rfl

theorem semiMap_smul (σ : ℂ →+* ℂ) (j : ∀ i, V i →+ W i) (hj : ∀ i (a : ℂ) v, j i (a • v) = σ a • j i v)
    (a : ℂ) (x : PiTensorProduct ℂ V) : semiMap σ j hj (a • x) = σ a • semiMap σ j hj x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f => rw [smul_smul, semiMap_tprod, semiMap_tprod, smul_smul, map_mul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

theorem semiMap_map (σ : ℂ →+* ℂ) (j : ∀ i, V i →+ W i) (hj : ∀ i (a : ℂ) v, j i (a • v) = σ a • j i v)
    (A : ∀ i, V i →ₗ[ℂ] V i) (B : ∀ i, W i →ₗ[ℂ] W i) (h : ∀ i v, j i (A i v) = B i (j i v))
    (x : PiTensorProduct ℂ V) :
    semiMap σ j hj (PiTensorProduct.map A x) = PiTensorProduct.map B (semiMap σ j hj x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, PiTensorProduct.map_tprod, semiMap_tprod, semiMap_tprod, map_smul, PiTensorProduct.map_tprod]
    simp only [h]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem symm_smul {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (σ : ℂ ≃+* ℂ)
    (j : A ≃+ B) (hj : ∀ (a : ℂ) v, j (a • v) = σ a • j v) (a : ℂ) (w : B) :
    j.symm (a • w) = σ.symm a • j.symm w := by
  apply j.injective
  rw [hj]; simp

theorem semiMap_injective (σ : ℂ ≃+* ℂ) (j : ∀ i, V i ≃+ W i) (hj : ∀ i (a : ℂ) v, j i (a • v) = σ a • j i v) :
    Function.Injective (semiMap σ.toRingHom (fun i => (j i).toAddMonoidHom) hj) := by
  refine Function.LeftInverse.injective
    (g := semiMap σ.symm.toRingHom (fun i => (j i).symm.toAddMonoidHom) fun i => symm_smul σ (j i) (hj i)) fun x => ?_
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    refine (congrArg _ (semiMap_tprod _ _ _ r f)).trans ((semiMap_tprod _ _ _ _ _).trans ?_)
    simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end Tensor

section Conj

variable {Γ : Type} [Group Γ]

def bcEquiv (σ : ℂ ≃+* ℂ) (τ : FDRep ℂ Γ) : τ ≃+ bc σ τ :=
  (Module.finBasis ℂ τ).equivFun.toAddEquiv.trans (AddEquiv.piCongrRight fun _ => σ.toAddEquiv)

theorem bcEquiv_smul (σ : ℂ ≃+* ℂ) (τ : FDRep ℂ Γ) (a : ℂ) (v : τ) :
    bcEquiv σ τ (a • v) = σ a • bcEquiv σ τ v := by
  refine funext fun i => ?_
  change σ ((Module.finBasis ℂ τ).repr (a • v) i) = σ a * σ ((Module.finBasis ℂ τ).repr v i)
  simp

theorem bcEquiv_ρ (σ : ℂ ≃+* ℂ) (τ : FDRep ℂ Γ) (γ : Γ) (v : τ) :
    bcEquiv σ τ (τ.ρ γ v) = (bc σ τ).ρ γ (bcEquiv σ τ v) := by
  refine funext fun i => ?_
  change σ ((Module.finBasis ℂ τ).repr (τ.ρ γ v) i) =
    (((LinearMap.toMatrix (Module.finBasis ℂ τ) (Module.finBasis ℂ τ) (τ.ρ γ)).map σ).mulVec
      fun k => σ ((Module.finBasis ℂ τ).repr v k)) i
  rw [← LinearMap.toMatrix_mulVec_repr (Module.finBasis ℂ τ) (Module.finBasis ℂ τ)]
  simp [Matrix.mulVec, dotProduct]

theorem character_bc (σ : ℂ ≃+* ℂ) (τ : FDRep ℂ Γ) (γ : Γ) : (bc σ τ).character γ = σ (τ.character γ) :=
  trace_bcRepr σ τ.ρ γ

theorem simple_bc [Fintype Γ] (σ : ℂ ≃+* ℂ) {τ : FDRep ℂ Γ} (h : Simple τ) : Simple (bc σ τ) := by
  rw [FDRep.simple_iff_char_is_norm_one] at h ⊢
  simp only [character_bc]
  rw [← map_natCast σ, ← h, map_sum]
  simp only [map_mul]

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem isCuspidal_bc (σ : ℂ ≃+* ℂ) {τ : FDRep ℂ (GL ι K)} (h : IsCuspidal K τ) : IsCuspidal K (bc σ τ) := by
  intro s b hb hs w hw
  obtain ⟨v, rfl⟩ := (bcEquiv σ τ).surjective w
  rw [h s b hb hs v fun u hu => (bcEquiv σ τ).injective ((bcEquiv_ρ σ τ u v).trans (hw u hu)), map_zero]

theorem isConstituent_bc (σ : ℂ ≃+* ℂ) {s : ℕ} (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
    {τ : FDRep ℂ (GL ι K)} (h : IsConstituent τ (hcRep K b lam)) :
    IsConstituent (bc σ τ) (hcRep K b fun c => bc σ (lam c)) := by
  obtain ⟨φ, hφ, hne⟩ := h
  let J := semiMap σ.toRingHom (fun c => (bcEquiv σ (lam c)).toAddMonoidHom) fun c => bcEquiv_smul σ (lam c)
  have hJ : Function.Injective J := semiMap_injective σ _ _
  let ψ : bc σ τ →ₗ[ℂ] hcSpace K b fun c => bc σ (lam c) :=
    { toFun := fun w => ⟨fun x => J ((φ ((bcEquiv σ τ).symm w)).1 x), fun p x => by
        refine (congrArg J ((φ ((bcEquiv σ τ).symm w)).2 p x)).trans ?_
        exact semiMap_map _ _ _ _ _ (fun c v => bcEquiv_ρ σ (lam c) _ v) _⟩
      map_add' := fun w w' => by
        ext x
        simp
      map_smul' := fun a w => by
        ext x
        change J ((φ ((bcEquiv σ τ).symm (a • w))).1 x) = a • J ((φ ((bcEquiv σ τ).symm w)).1 x)
        rw [symm_smul σ _ (bcEquiv_smul σ τ), map_smul]
        refine (semiMap_smul _ _ _ _ _).trans ?_
        simp [J] }
  refine ⟨ψ, fun γ => ?_, fun h0 => hne ?_⟩
  · refine LinearMap.ext fun w => Subtype.ext (funext fun x => ?_)
    obtain ⟨v, rfl⟩ := (bcEquiv σ τ).surjective w
    change J ((φ ((bcEquiv σ τ).symm ((bc σ τ).ρ γ (bcEquiv σ τ v)))).1 x) =
      J ((φ ((bcEquiv σ τ).symm (bcEquiv σ τ v))).1 (x * γ))
    rw [← bcEquiv_ρ, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
    have := LinearMap.congr_fun (hφ γ) v
    rw [LinearMap.comp_apply] at this
    rw [this]
    rfl
  · refine LinearMap.ext fun v => Subtype.ext (funext fun x => hJ ?_)
    have := congrFun (congrArg Subtype.val (LinearMap.congr_fun h0 (bcEquiv σ τ v))) x
    change J ((φ ((bcEquiv σ τ).symm (bcEquiv σ τ v))).1 x) = 0 at this
    rw [AddEquiv.symm_apply_apply] at this
    rw [this]
    exact (map_zero J).symm

end Conj

section Label

variable {K : Type} [Field K]

theorem normRev_prod {α : Type} (s : Finset α) (P : α → K[X]) :
    C ((∏ c ∈ s, P c).coeff 0)⁻¹ * (∏ c ∈ s, P c).reverse = ∏ c ∈ s, C ((P c).coeff 0)⁻¹ * (P c).reverse := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [reverse]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ← ih, mul_coeff_zero, mul_inv, C_mul, reverse_mul_of_domain]
    ring

theorem normRev_normRev {f : K[X]} (hm : f.Monic) (h0 : f.coeff 0 ≠ 0) :
    C ((C (f.coeff 0)⁻¹ * f.reverse).coeff 0)⁻¹ * (C (f.coeff 0)⁻¹ * f.reverse).reverse = f := by
  have h1 : (C (f.coeff 0)⁻¹ * f.reverse).coeff 0 ≠ 0 := by
    rw [coeff_C_mul, coeff_zero_reverse, hm.leadingCoeff, mul_one]
    exact inv_ne_zero h0
  refine GlobalTheory.DualLabel.eq_of_rootsBar_eq (GlobalTheory.DualLabel.monic_normRev h1) hm ?_
  rw [GlobalTheory.DualLabel.rootsBar_normRev (GlobalTheory.DualLabel.monic_normRev h0) h1, GlobalTheory.DualLabel.rootsBar_normRev hm h0,
    Multiset.map_map]
  simp

variable [Fintype K] [DecidableEq K] {Cv : LabelConv K}

theorem hasLabelO_conj (O : LabelMap K Cv) (hO : LabelMapEquivariant O) {ι : Type} [Fintype ι] [DecidableEq ι]
    {τ : FDRep ℂ (GL ι K)} {f : K[X]} (h : HasLabelO O τ f) :
    HasLabelO O (bc (starRingAut : ℂ ≃+* ℂ) τ) (C (f.coeff 0)⁻¹ * f.reverse) := by
  obtain ⟨s, b, lam, hb, hl, hc, rfl⟩ := h
  refine ⟨s, b, fun c => bc starRingAut (lam c), hb, fun c => ⟨simple_bc _ (hl c).1, isCuspidal_bc _ (hl c).2⟩,
    isConstituent_bc _ b lam hc, ?_⟩
  rw [normRev_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  have hd : 1 ≤ Fintype.card {i // b i = c} := by
    obtain ⟨i, hi⟩ := hb c
    exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
  refine (GlobalTheory.DualLabel.lab_dual O hO _ _ _ hd (Formalism.L2.PT.simple_transp _ (hl c).1)
    (Formalism.L2.PT.isCuspidal_transp _ (hl c).2) (Formalism.L2.PT.simple_transp _ (simple_bc _ (hl c).1))
    (Formalism.L2.PT.isCuspidal_transp _ (isCuspidal_bc _ (hl c).2)) fun γ => ?_).symm
  change (transp _ (bc starRingAut (lam c))).character γ = (transp _ (lam c)).character γ⁻¹
  rw [Formalism.L2.PT.character_transp, Formalism.L2.PT.character_transp, character_bc, map_inv]
  exact PI.SerBridgeGLW.conjugate_character_formula _ _ _

end Label

theorem star_coeff_eSerO : ∀ {g : ℕ} [Fact g.Prime] {C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod g)}
    (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) C), Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O →
    ∀ (r : ℕ) (f : Polynomial (ZMod g)), f.Monic → f.coeff 0 ≠ 0 → ∀ x,
      star ((Formalism.L2.NT.eSerO O r f).coeff x) =
        (Formalism.L2.NT.eSerO O r (Polynomial.C (f.coeff 0)⁻¹ * f.reverse)).coeff x := by
  intro g _ Cv O hO r f hm h0 x
  classical
  let S : MonoidAlgebra ℂ (GL (Fin r) (ZMod g)) ≃+ MonoidAlgebra ℂ (GL (Fin r) (ZMod g)) :=
    MonoidAlgebra.mapAddEquiv _ (starRingAut : ℂ ≃+* ℂ).toAddEquiv
  have hS : ∀ z y, (S z).coeff y = star (z.coeff y) := fun z y => MonoidAlgebra.coeff_mapAddEquiv _ _ _
  have hSS : ∀ z, S (S z) = z := fun z => by
    ext y
    rw [hS, hS, star_star]
  have hz : ∀ τ : FDRep ℂ (GL (Fin r) (ZMod g)), zIdem (bc starRingAut τ) = S (zIdem τ) := fun τ => by
    ext y
    rw [hS]
    exact (galoisConjCentralIdempotent _ starRingAut τ y).symm
  rw [← hS]
  congr 2
  unfold Formalism.L2.NT.eSerO
  rw [S.map_finsum]
  refine finsum_eq_of_bijective S S.bijective fun z => ?_
  have hiff : (∃ τ : FDRep ℂ (GL (Fin r) (ZMod g)), Simple τ ∧ zIdem τ = z ∧ HasLabelO O τ f) ↔
      ∃ τ : FDRep ℂ (GL (Fin r) (ZMod g)), Simple τ ∧ zIdem τ = S z ∧
        HasLabelO O τ (C (f.coeff 0)⁻¹ * f.reverse) := by
    constructor
    · rintro ⟨τ, h1, h2, h3⟩
      exact ⟨_, simple_bc _ h1, by rw [hz, h2], hasLabelO_conj O hO h3⟩
    · rintro ⟨τ, h1, h2, h3⟩
      have h4 := hasLabelO_conj O hO h3
      rw [normRev_normRev hm h0] at h4
      exact ⟨_, simple_bc _ h1, by rw [hz, h2, hSS], h4⟩
  rw [finsum_eq_if, finsum_eq_if, ← hiff]
  split_ifs
  · rfl
  · exact map_zero S

end GlobalTheory.SerConj
