import Formalism.LocalToGlobal.Columns.MtAdWt

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP MvPolynomial

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

section Stab

variable {n : ℕ} {ι : Type} [Fintype ι]

def MtwStable (lam : ι → DomWeight n) (S : Submodule ℂ (VV ℂ lam)) : Prop :=
  ∀ g : ι → GL (Fin n) ℂ, ∀ x ∈ S, rhoK lam g x ∈ S

def HwInStable : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (S : Submodule ℂ (VV ℂ lam)), S ≠ ⊥ → MtwStable lam S →
    mtwHw lam ∈ S

def mtwPerp (lam : ι → DomWeight n) (S : Submodule ℂ (VV ℂ lam)) : Submodule ℂ (VV ℂ lam) where
  carrier := {x | ∀ y ∈ S, pairBK lam x y = 0}
  add_mem' {a b} ha hb y hy := by
    rw [map_add, LinearMap.add_apply, ha y hy, hb y hy, add_zero]
  zero_mem' y _ := by rw [map_zero, LinearMap.zero_apply]
  smul_mem' c x hx y hy := by rw [map_smul, LinearMap.smul_apply, hx y hy, smul_zero]

theorem mtwPerp_stable (lam : ι → DomWeight n) (S : Submodule ℂ (VV ℂ lam)) (hS : MtwStable lam S) :
    MtwStable lam (mtwPerp lam S) := by
  intro g x hx y hy
  have hz : rhoK lam (invTrK g) ((rhoK lam (invTrK g)⁻¹) y) = y := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have e1 := pairingBInvariantK_holds ℂ ι n lam (invTrK g) (x : Pol ℂ ι n) (((rhoK lam (invTrK g)⁻¹) y : VV ℂ lam) : Pol ℂ ι n)
  rw [pb_invTrK_invTrK] at e1
  have e2 : actP lam (invTrK g) (((rhoK lam (invTrK g)⁻¹) y : VV ℂ lam) : Pol ℂ ι n) = (y : Pol ℂ ι n) :=
    congrArg Subtype.val hz
  rw [e2] at e1
  rw [pairBK_apply]
  show pairB lam (actP lam g (x : Pol ℂ ι n)) (y : Pol ℂ ι n) = 0
  rw [e1, ← pairBK_apply]
  exact hx _ (hS _ y hy)

theorem mtwPerp_ne_bot (lam : ι → DomWeight n) (S : Submodule ℂ (VV ℂ lam)) (hS : S ≠ ⊤) : mtwPerp lam S ≠ ⊥ := by
  have : FiniteDimensional ℂ (VV ℂ lam) := Module.Finite.of_basis (bVV ℂ lam)
  obtain ⟨f, hf0, hfS⟩ := Submodule.exists_le_ker_of_lt_top S (lt_top_iff_ne_top.2 hS)
  have hinj : Function.Injective (pairBK (K := ℂ) lam) := by
    intro a b hab
    have := (pairingBNondegenerate_holds ℂ ι n lam).1 (a - b) fun y => by
      rw [map_sub, LinearMap.sub_apply, hab, sub_self]
    exact sub_eq_zero.1 this
  have hsurj : Function.Surjective (pairBK (K := ℂ) lam) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).1 hinj
  obtain ⟨x, hx⟩ := hsurj f
  intro hbot
  have hxP : x ∈ mtwPerp lam S := fun y hy => by
    rw [hx]
    exact hfS hy
  rw [hbot] at hxP
  apply hf0
  rw [← hx, (Submodule.mem_bot ℂ).1 hxP, map_zero]

theorem mtw_bot_or_top (hH : HwInStable) (lam : ι → DomWeight n) (S : Submodule ℂ (VV ℂ lam)) (hS : MtwStable lam S) :
    S = ⊥ ∨ S = ⊤ := by
  by_contra hc
  push_neg at hc
  obtain ⟨h1, h2⟩ := hc
  have hw1 := hH ι n lam S h1 hS
  have hw2 := hH ι n lam (mtwPerp lam S) (mtwPerp_ne_bot lam S h2) (mtwPerp_stable lam S hS)
  have h0 : pairBK lam (mtwHw lam) (mtwHw lam) = 0 := hw2 _ hw1
  have hx := pairingBExtremal_holds ℂ ι n lam 1
  have ha : ∀ F : Pol ℂ ι n, actP lam (1 : ι → GL (Fin n) ℂ) F = F := fun F => by
    have := congrArg (fun φ : Module.End ℂ (Pol ℂ ι n) => φ F) (rhoP (K := ℂ) lam).map_one
    simpa [rhoP] using this
  rw [map_one, ha] at hx
  rw [pairBK_apply] at h0
  exact one_ne_zero (hx.symm.trans h0)

end Stab

section Dens

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι]

open Classical in

def mtwPtOf (emb : ι → L →+* ℂ) (g : ι → GL (Fin n) ℂ) : (L →+* ℂ) × Fin n × Fin n → ℂ := fun p =>
  if h : ∃ τ, emb τ = p.1 then ((g h.choose : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) p.2.1 p.2.2
  else if h' : ∃ τ, ComplexEmbedding.conjugate (emb τ) = p.1 then
    (((g h'.choose)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) p.2.2 p.2.1
  else if p.2.1 = p.2.2 then 1 else 0

variable (emb : ι → L →+* ℂ) (hinj : Function.Injective emb)
  (hcm : ∀ τ τ', emb τ ≠ ComplexEmbedding.conjugate (emb τ'))
include hinj hcm

theorem mtwPtOf_emb (g : ι → GL (Fin n) ℂ) (τ : ι) (a b : Fin n) :
    mtwPtOf emb g (emb τ, a, b) = ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) a b := by
  have h : ∃ τ', emb τ' = emb τ := ⟨τ, rfl⟩
  have hc : h.choose = τ := hinj h.choose_spec
  simp only [mtwPtOf, dif_pos h, hc]

theorem mtwPtOf_conj (g : ι → GL (Fin n) ℂ) (τ : ι) (a b : Fin n) :
    mtwPtOf emb g (ComplexEmbedding.conjugate (emb τ), a, b) = (((g τ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) b a := by
  have h : ¬ ∃ τ', emb τ' = ComplexEmbedding.conjugate (emb τ) := fun ⟨τ', h'⟩ => hcm τ' τ h'
  have h' : ∃ τ', ComplexEmbedding.conjugate (emb τ') = ComplexEmbedding.conjugate (emb τ) := ⟨τ, rfl⟩
  have hc : h'.choose = τ := by
    apply hinj
    have := congrArg ComplexEmbedding.conjugate h'.choose_spec
    simpa using this
  simp only [mtwPtOf, dif_neg h, dif_pos h', hc]

theorem mtwPtOf_other (g : ι → GL (Fin n) ℂ) (σ : L →+* ℂ) (h1 : ∀ τ, emb τ ≠ σ)
    (h2 : ∀ τ, ComplexEmbedding.conjugate (emb τ) ≠ σ) (a b : Fin n) :
    mtwPtOf emb g (σ, a, b) = (1 : Matrix (Fin n) (Fin n) ℂ) a b := by
  have h : ¬ ∃ τ, emb τ = σ := fun ⟨τ, h'⟩ => h1 τ h'
  have h' : ¬ ∃ τ, ComplexEmbedding.conjugate (emb τ) = σ := fun ⟨τ, h''⟩ => h2 τ h''
  simp only [mtwPtOf, dif_neg h, dif_neg h', Matrix.one_apply]

theorem mtwPtOf_inV (g : ι → GL (Fin n) ℂ) : PI.UnitaryGroupMassFormula.HwConjInf.InV (mtwPtOf emb g) := by
  intro σ
  by_cases h1 : ∃ τ, emb τ = σ
  · obtain ⟨τ, rfl⟩ := h1
    exact ⟨g τ, fun i j => ⟨mtwPtOf_emb emb hinj hcm g τ i j, mtwPtOf_conj emb hinj hcm g τ i j⟩⟩
  by_cases h2 : ∃ τ, ComplexEmbedding.conjugate (emb τ) = σ
  · obtain ⟨τ, rfl⟩ := h2
    refine ⟨inside₂ ℂ n (g τ), fun i j => ⟨?_, ?_⟩⟩
    · rw [mtwPtOf_conj emb hinj hcm g τ i j]
      rfl
    · rw [show ComplexEmbedding.conjugate (ComplexEmbedding.conjugate (emb τ)) = emb τ by simp,
        mtwPtOf_emb emb hinj hcm g τ i j]
      rfl
  · push_neg at h1 h2
    refine ⟨1, fun i j => ⟨?_, ?_⟩⟩
    · rw [mtwPtOf_other emb hinj hcm g σ h1 h2]
      rfl
    · have h1' : ∀ τ, emb τ ≠ ComplexEmbedding.conjugate σ := fun τ h' => h2 τ (by
        rw [h']
        simp)
      have h2' : ∀ τ, ComplexEmbedding.conjugate (emb τ) ≠ ComplexEmbedding.conjugate σ := fun τ h' => h1 τ (by
        have := congrArg ComplexEmbedding.conjugate h'
        simpa using this)
      rw [mtwPtOf_other emb hinj hcm g _ h1' h2', inv_one, Units.val_one, Matrix.one_apply, Matrix.one_apply]
      simp [eq_comm]

theorem eval_tensorCoeff_eq_toMatrix (lam : ι → DomWeight n) (g : ι → GL (Fin n) ℂ) :
    (fun i j => MvPolynomial.eval (mtwPtOf emb g) (tenP emb lam i j)) =
      LinearMap.toMatrix (bVV ℂ lam) (bVV ℂ lam) (rhoK lam g) := by
  have hM : (fun τ => (Matrix.of fun a b => mtwPtOf emb g (emb τ, a, b))ᵀ) =
      fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ := by
    funext τ
    congr 1
    ext a b
    exact mtwPtOf_emb emb hinj hcm g τ a b
  have htw : MvPolynomial.eval (mtwPtOf emb g) (mtwTwP emb lam) = detTwK lam g := by
    simp only [mtwTwP, detTwK, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have hd : ((Matrix.GeneralLinearGroup.det (g τ) : ℂˣ) : ℂ) = ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det :=
      Matrix.GeneralLinearGroup.val_det_apply _
    rw [detPow, Units.val_zpow_eq_zpow_val, hd]
    split_ifs with he
    · rw [map_pow, detPolynomial_eval]
      rw [show (Matrix.of fun a b => mtwPtOf emb g (emb τ, a, b)) = ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) by
        ext a b; exact mtwPtOf_emb emb hinj hcm g τ a b]
      rw [← zpow_natCast, Int.toNat_of_nonneg he]
    · rw [map_pow, detPolynomial_eval]
      rw [show (Matrix.of fun a b => mtwPtOf emb g (ComplexEmbedding.conjugate (emb τ), a, b)) =
          (((g τ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ by
        ext a b; exact mtwPtOf_conj emb hinj hcm g τ a b]
      rw [Matrix.det_transpose, ← Matrix.GeneralLinearGroup.val_det_apply, map_inv, Units.val_inv_eq_inv_val,
        Matrix.GeneralLinearGroup.val_det_apply, ← zpow_natCast, Int.toNat_of_nonneg (by omega), inv_zpow', neg_neg]
  ext i j
  rw [eval_tensorCoeff, htw, hM, LinearMap.toMatrix_apply, ← mtwCoord_spec]
  simp only [rhoK, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_restrict_apply, bVV_coe, actP, trAct,
    LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_smul, smul_eq_mul]

omit hinj hcm in
theorem mtw_sum_coord (lam : ι → DomWeight n) (f : VV ℂ lam →ₗ[ℂ] ℂ) (T : Module.End ℂ (VV ℂ lam)) (x : VV ℂ lam) :
    ∑ i, f (bVV ℂ lam i) * ∑ j, LinearMap.toMatrix (bVV ℂ lam) (bVV ℂ lam) T i j * (bVV ℂ lam).repr x j = f (T x) := by
  have h := LinearMap.toMatrix_mulVec_repr (bVV ℂ lam) (bVV ℂ lam) T x
  conv_rhs => rw [← (bVV ℂ lam).sum_repr (T x)]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm, ← h]
  rfl

theorem mtw_stable_of_rat (lam : ι → DomWeight n) (S : Submodule ℂ (VV ℂ lam))
    (hS : ∀ γ : GQ L n, ∀ x ∈ S, tenRep emb lam γ x ∈ S) : MtwStable lam S := by
  classical
  intro g x hx
  by_contra hnot
  have hq : S.mkQ (rhoK lam g x) ≠ 0 := by
    rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hnot
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (VV ℂ lam ⧸ S), φ (S.mkQ (rhoK lam g x)) ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hq ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hall)
  set f : VV ℂ lam →ₗ[ℂ] ℂ := φ.comp S.mkQ with hf
  let F : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ :=
    ∑ i, C (f (bVV ℂ lam i)) * ∑ j, tenP emb lam i j * C ((bVV ℂ lam).repr x j)
  have hF : ∀ y, MvPolynomial.eval y F =
      ∑ i, f (bVV ℂ lam i) * ∑ j, MvPolynomial.eval y (tenP emb lam i j) * (bVV ℂ lam).repr x j := by
    intro y
    simp only [F, map_sum, map_mul, MvPolynomial.eval_C]
  have hrat : ∀ γ₀ ∈ GQ0 L n, MvPolynomial.eval (PI.UnitaryGroupMassFormula.HwConjInf.ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) F = 0 := by
    intro γ₀ hγ
    rw [hF]
    have hm := tenRep_toMatrix emb lam (PI.UnitaryGroupMassFormula.HwConjInf.toGQ γ₀ hγ) γ₀ (PI.UnitaryGroupMassFormula.HwConjInf.toGQ_val γ₀ hγ)
    have := mtw_sum_coord lam f (tenRep emb lam (PI.UnitaryGroupMassFormula.HwConjInf.toGQ γ₀ hγ)) x
    rw [hm] at this
    rw [show PI.UnitaryGroupMassFormula.HwConjInf.ratPt (γ₀ : Matrix (Fin n) (Fin n) L) = fun p => p.1 ((γ₀ : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2)
      from rfl, this, hf, LinearMap.comp_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero S).2 (hS _ x hx),
      map_zero]
  have h0 := PI.UnitaryGroupMassFormula.HwConjInf.density_induction L n F hrat (mtwPtOf emb g) (mtwPtOf_inV emb hinj hcm g)
  rw [hF] at h0
  have := mtw_sum_coord lam f (rhoK lam g) x
  rw [← eval_tensorCoeff_eq_toMatrix emb hinj hcm lam g] at this
  rw [this, hf, LinearMap.comp_apply] at h0
  exact hφ h0

end Dens

section Irr

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι]

theorem mtwConj_injective (emb : ι → L →+* ℂ) (hinj : Function.Injective emb) : Function.Injective (mtwConj emb) :=
  fun a b h => hinj (by
    have := congrArg ComplexEmbedding.conjugate h
    simpa [mtwConj] using this)

theorem mtwConj_cm (emb : ι → L →+* ℂ) (hcm : ∀ τ τ', emb τ ≠ ComplexEmbedding.conjugate (emb τ')) :
    ∀ τ τ', mtwConj emb τ ≠ ComplexEmbedding.conjugate (mtwConj emb τ') := fun τ τ' h => hcm τ τ' (by
  have := congrArg ComplexEmbedding.conjugate h
  simpa [mtwConj] using this)

theorem tenIrr_of (hH : HwInStable) (emb : ι → L →+* ℂ) (hinj : Function.Injective emb)
    (hcm : ∀ τ τ', emb τ ≠ ComplexEmbedding.conjugate (emb τ')) (lam : ι → DomWeight n) : TenIrr emb lam := by
  have hinj' := mtwConj_injective emb hinj
  have hcm' := mtwConj_cm emb hcm
  unfold TenIrr
  rw [mtRep_eq_tenRep]
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · have h1 : mtwHw lam ∈ (⊤ : Subrepresentation (tenRep (mtwConj emb) lam)) := Submodule.mem_top
    rw [← h] at h1
    exact mtwHw_ne lam ((Submodule.mem_bot ℂ).1 h1)
  · have hst := mtw_stable_of_rat (mtwConj emb) hinj' hcm' lam S.toSubmodule
      (fun γ x hx => S.apply_mem_toSubmodule γ hx)
    rcases mtw_bot_or_top hH lam S.toSubmodule hst with h | h
    · left
      exact SetLike.ext fun x => by
        show x ∈ S.toSubmodule ↔ x ∈ (⊥ : Submodule ℂ _)
        rw [h]
    · right
      exact SetLike.ext fun x => by
        show x ∈ S.toSubmodule ↔ x ∈ (⊤ : Submodule ℂ _)
        rw [h]

end Irr

section Cut

def MtwUni {n : ℕ} {ι : Type} (g : ι → GL (Fin n) ℂ) : Prop :=
  ∀ τ, (∀ i j, j < i → ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j = 0) ∧
    ∀ i, ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i i = 1

def HwFixedEx : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (S : Submodule ℂ (VV ℂ lam)), S ≠ ⊥ → MtwStable lam S →
    ∃ v ∈ S, v ≠ 0 ∧ ∀ g : ι → GL (Fin n) ℂ, MtwUni g → rhoK lam g v = v

def HwFixedLine : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (v : VV ℂ lam),
    (∀ g : ι → GL (Fin n) ℂ, MtwUni g → rhoK lam g v = v) → ∃ c : ℂ, v = c • mtwHw lam

theorem hwInStable_of (h1 : HwFixedEx) (h2 : HwFixedLine) : HwInStable := by
  intro ι _ n lam S hS hst
  obtain ⟨v, hv, hv0, hfix⟩ := h1 ι n lam S hS hst
  obtain ⟨c, rfl⟩ := h2 ι n lam v hfix
  have hc : c ≠ 0 := by
    rintro rfl
    exact hv0 (zero_smul _ _)
  have := S.smul_mem c⁻¹ hv
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

theorem tenIrr_of' (h1 : HwFixedEx) (h2 : HwFixedLine) {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {ι : Type} [Fintype ι] (emb : ι → L →+* ℂ) (hinj : Function.Injective emb)
    (hcm : ∀ τ τ', emb τ ≠ ComplexEmbedding.conjugate (emb τ')) (lam : ι → DomWeight n) : TenIrr emb lam :=
  tenIrr_of (hwInStable_of h1 h2) emb hinj hcm lam

def mtWtOf (h1 : HwFixedEx) (h2 : HwFixedLine) {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {ι : Type} [Fintype ι] (emb : ι → L →+* ℂ) (hinj : Function.Injective emb)
    (hcm : ∀ τ τ', emb τ ≠ ComplexEmbedding.conjugate (emb τ')) (lam : ι → DomWeight n) : NG.AlgWt L n :=
  mtWt emb lam (tenIrr_of' h1 h2 emb hinj hcm lam)

theorem mtWtOf_hw_dual (h1 : HwFixedEx) (h2 : HwFixedLine) {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {ι : Type} [Fintype ι] (emb : ι → L →+* ℂ) (hinj : Function.Injective emb)
    (hcm : ∀ τ τ', emb τ ≠ ComplexEmbedding.conjugate (emb τ')) (lam : ι → DomWeight n) (τ : ι) (a : NG.AlgWt L n)
    (lam0 : Fin n → ℤ) (hd : (mtWtOf h1 h2 emb hinj hcm lam).IsDual a) (hw : a.HWAt (emb τ) lam0) : lam0 = (lam τ).w :=
  mtWt_hw_dual emb hinj hcm lam _ (tenIrr_of' h1 h2 (mtwConj emb) (mtwConj_injective emb hinj) (mtwConj_cm emb hcm) lam)
    τ a lam0 hd hw

end Cut

end Formalism.L2.Col
