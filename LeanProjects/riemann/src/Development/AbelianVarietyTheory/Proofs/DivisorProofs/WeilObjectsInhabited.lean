import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplittingSplitOm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenAddSubgroup

noncomputable section

open MeasureTheory Matrix ValuativeRel
open scoped NNReal Topology Kronecker

namespace GlobalTheory.WeilM

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {α β κ : Type}

theorem invariant_comp_mulVec [Fintype κ] [DecidableEq κ] (m : ((κ → F) → ℂ) →ₗ[ℂ] ℂ)
    (hm : ∀ φ ∈ SB (κ → F), ∀ a, m (fun x => φ (x + a)) = m φ) (g : GL κ F) {φ : (κ → F) → ℂ} (hφ : φ ∈ SB (κ → F))
    (hφ' : (fun x => φ (g.val.mulVec x)) ∈ SB (κ → F)) :
    ((distribHaarChar F (GeneralLinearGroup.det g) : ℝ) : ℂ) * m (fun x => φ (g.val.mulVec x)) = m φ := by
  borelize F
  have := SplitWeil.secondCountable F
  have := SplitWeil.t2Space F
  have := nonarch_pi F κ
  obtain ⟨c, hc⟩ := GlobalTheory.WeilM.HaarUniq.exists_eq_mul_integral (κ → F) (Measure.pi fun _ => (Measure.addHaar : Measure F)) m hm
  rw [hc _ hφ, hc _ hφ', mul_left_comm, integral_comp_mulVec]

theorem diag_mem_SB [Fintype κ] {φ : (κ ⊕ κ → F) → ℂ} (hφ : φ ∈ SB (κ ⊕ κ → F)) :
    (fun x : κ → F => φ (Sum.elim x x)) ∈ SB (κ → F) := by
  have := SplitWeil.t2Space F
  have hc : Continuous fun x : κ → F => (Sum.elim x x : κ ⊕ κ → F) :=
    continuous_pi (by rintro (k | k) <;> exact continuous_apply k)
  have hc' : Continuous fun u : κ ⊕ κ → F => u ∘ Sum.inl := continuous_pi fun k => continuous_apply _
  refine ⟨hφ.1.comp_continuous hc, HasCompactSupport.intro (hφ.2.image hc') fun x hx => ?_⟩
  by_contra h
  exact hx ⟨Sum.elim x x, subset_tsupport _ h, rfl⟩

theorem diag_invariant_comp [Invertible (2 : F)] [Fintype κ] [DecidableEq κ] (ψ : AddChar F ℂ) (hψ : Continuous ψ)
    (hψ1 : ψ ≠ 1) (l : ((κ ⊕ κ → F) → ℂ) →ₗ[ℂ] ℂ)
    (hl : ∀ x y : κ → F, ∀ φ ∈ SB (κ ⊕ κ → F), l (schr ψ (Sum.elim x x, Sum.elim y (-y)) φ) = l φ)
    (g : GL κ F) {φ φ' : (κ ⊕ κ → F) → ℂ} (hφ : φ ∈ SB (κ ⊕ κ → F)) (hφ' : φ' ∈ SB (κ ⊕ κ → F))
    (h : ∀ x, φ' (Sum.elim x x) = φ (Sum.elim (g.val.mulVec x) (g.val.mulVec x))) :
    ((distribHaarChar F (GeneralLinearGroup.det g) : ℝ) : ℂ) * l φ' = l φ := by
  classical
  have := SplitWeil.t2Space F
  have := nonarch_field F
  have hlc := isLocallyConstant_addChar ψ hψ

  have hz : ∀ φ ∈ SB (κ ⊕ κ → F), (∀ x, φ (Sum.elim x x) = 0) → l φ = 0 := by
    intro φ hφ h0
    refine eq_zero_of_mul_invariant l (Set.range fun y : κ → F => fun u => ψ (u ⬝ᵥ Sum.elim y (-y))) ?_ ?_ hφ ?_
    · rintro _ ⟨y, rfl⟩
      exact hlc.comp_continuous (continuous_id.dotProduct continuous_const)
    · rintro _ ⟨y, rfl⟩ φ hφ
      rw [← hl 0 y φ hφ]
      congr 1
      funext u
      simp [schr]
    · intro u hu
      obtain ⟨k, hk⟩ : ∃ k, u (Sum.inl k) - u (Sum.inr k) ≠ 0 := by
        by_contra hne
        push Not at hne
        apply hu
        rw [← h0 (u ∘ Sum.inl)]
        congr 1
        ext (k | k)
        · rfl
        · exact (sub_eq_zero.mp (hne k)).symm
      obtain ⟨a, ha⟩ := AddChar.ne_one_iff.mp hψ1
      refine ⟨_, ⟨Pi.single k (a / (u (Sum.inl k) - u (Sum.inr k))), rfl⟩, ?_⟩
      have : u ⬝ᵥ Sum.elim (Pi.single k (a / (u (Sum.inl k) - u (Sum.inr k))))
          (-Pi.single k (a / (u (Sum.inl k) - u (Sum.inr k)))) = a := by
        conv_lhs => rw [← Sum.elim_comp_inl_inr u]
        rw [sumElim_dotProduct_sumElim, dotProduct_neg, dotProduct_single, dotProduct_single, ← sub_eq_add_neg,
          ← sub_mul]
        exact mul_div_cancel₀ _ hk
      show ψ _ ≠ 1
      rwa [this]

  let K : Set (κ → F) := Set.univ.pi fun _ => (𝒪[F] : Set F)
  have hKc : IsCompact K := isCompact_univ_pi fun _ => SplitWeil.isCompact_int F
  have hK : IsClopen K := ⟨hKc.isClosed, isOpen_set_pi Set.finite_univ fun _ _ => SplitWeil.isOpen_int F⟩
  let e : (κ → F) → ℂ := K.indicator 1
  have he : IsLocallyConstant e := (LocallyConstant.indicator (1 : LocallyConstant _ ℂ) hK).isLocallyConstant
  have he0 : e 0 = 1 := Set.indicator_of_mem (show (0 : κ → F) ∈ K from fun _ _ => zero_mem _) _
  let ext : ((κ → F) → ℂ) →ₗ[ℂ] ((κ ⊕ κ → F) → ℂ) :=
    { toFun := fun f u => f (u ∘ Sum.inl) * e (u ∘ Sum.inr - u ∘ Sum.inl)
      map_add' := fun f f' => by funext u; simp [add_mul]
      map_smul' := fun a f => by funext u; simp [mul_assoc] }
  have hext : ∀ f u, ext f u = f (u ∘ Sum.inl) * e (u ∘ Sum.inr - u ∘ Sum.inl) := fun _ _ => rfl
  have c1 : Continuous fun u : κ ⊕ κ → F => u ∘ Sum.inl := continuous_pi fun k => continuous_apply _
  have c2 : Continuous fun u : κ ⊕ κ → F => u ∘ Sum.inr := continuous_pi fun k => continuous_apply _
  have hSB : ∀ f ∈ SB (κ → F), ext f ∈ SB (κ ⊕ κ → F) := by
    intro f hf
    have c3 : Continuous fun p : (κ → F) × (κ → F) => (Sum.elim p.1 (p.2 + p.1) : κ ⊕ κ → F) :=
      continuous_pi (by rintro (k | k) <;> simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply] <;> fun_prop)
    refine ⟨(hf.1.comp_continuous c1).mul (he.comp_continuous (c2.sub c1)),
      HasCompactSupport.intro ((IsCompact.prod hf.2 hKc).image c3) fun u hu => ?_⟩
    by_contra h
    rw [hext] at h
    refine hu ⟨(u ∘ Sum.inl, u ∘ Sum.inr - u ∘ Sum.inl),
      ⟨subset_tsupport _ (left_ne_zero_of_mul h), Set.mem_of_indicator_ne_zero (right_ne_zero_of_mul h)⟩, ?_⟩
    simp
  have hres : ∀ φ ∈ SB (κ ⊕ κ → F), l φ = (l ∘ₗ ext) fun x => φ (Sum.elim x x) := by
    intro φ hφ
    rw [LinearMap.comp_apply, ← sub_eq_zero, ← map_sub]
    refine hz _ (sub_mem hφ (hSB _ (diag_mem_SB hφ))) fun x => ?_
    simp [hext, he0]
  have hinv : ∀ f ∈ SB (κ → F), ∀ a, (l ∘ₗ ext) (fun x => f (x + a)) = (l ∘ₗ ext) f := by
    intro f hf a
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hl a 0 _ (hSB f hf)]
    congr 1
    funext u
    have e1 : (u + Sum.elim a a) ∘ Sum.inl = u ∘ Sum.inl + a := rfl
    have e2 : (u + Sum.elim a a) ∘ Sum.inr = u ∘ Sum.inr + a := rfl
    simp [schr, hext, e1, e2]
  have h' := diag_mem_SB hφ'
  rw [hres φ hφ, hres φ' hφ']
  simp only [h] at h' ⊢
  exact invariant_comp_mulVec _ hinv g (diag_mem_SB hφ) h'

variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] [Invertible (2 : F)]

theorem siegelRule_split (ψ : AddChar F ℂ) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {JA : Matrix α α (F × F)}
    {JB : Matrix β β (F × F)} (hA : IsHerm (swapA F) JA) (hB : IsHerm (swapA F) JB) (σ : κ ≃ α × β)
    (χ : (F × F)ˣ →* Circle) (hχ : ∀ a : Fˣ, χ (Units.map (algebraMap F (F × F) : F →* F × F) a) = 1) :
    SiegelRule (swapA F) (sbClass F) ψ (1, -1) JA (dbl JB) (splitDarboux hA hB.dbl (dblNum σ)) χ (diagCols β)
      (splitOm (distribHaarChar F) χ (dbl JB) (dblNum σ)) := by
  classical
  intro l _ hl p t hp φ hφ
  have hD : ∀ {S : Type} [CommRing S] (z : Matrix α β S), z * (diagCols β : Matrix (β ⊕ β) β S)ᵀ = fromCols z z := by
    intro S _ z
    rw [diagCols, transpose_fromRows, mul_fromCols, transpose_one, Matrix.mul_one]
  have hl' : ∀ x y : κ → F, ∀ φ ∈ SB (κ ⊕ κ → F), l (schr ψ (Sum.elim x x, Sum.elim y (-y)) φ) = l φ := by
    intro x y φ hφ
    have := hl ((splitDarboux hA hB σ).e.symm (x, y)) φ hφ
    rwa [Darboux.rho, hD, isDblCoord_split hA hB σ, LinearEquiv.apply_symm_apply] at this
  obtain ⟨h1, h2⟩ := det_siegel hB p t.val hp
  let t₁ : GL β F := GeneralLinearGroup.map (RingHom.fst F F) t
  let t₂ : GL β F := GeneralLinearGroup.map (RingHom.snd F F) t
  have h2' : GeneralLinearGroup.det (ugFst _ p) = GeneralLinearGroup.det t₁ * (GeneralLinearGroup.det t₂)⁻¹ :=
    eq_mul_inv_of_mul_eq (Units.ext h2)
  have h1' : ((ugFst _ p)⁻¹).val * (diagCols β : Matrix (β ⊕ β) β F) =
      (diagCols β : Matrix (β ⊕ β) β F) * (t₁⁻¹).val := by
    have h3 : (ugFst _ p).val * (diagCols β : Matrix (β ⊕ β) β F) = (diagCols β : Matrix (β ⊕ β) β F) * t₁.val := h1
    have := congrArg (fun N => ((ugFst _ p)⁻¹).val * N * (t₁⁻¹).val) h3
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at this
    rw [this, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  let G : Matrix κ κ F := ((1 : Matrix α α F) ⊗ₖ (t₁⁻¹).val).submatrix σ σ
  have hG : G.det = ((GeneralLinearGroup.det t₁)⁻¹ ^ Fintype.card α : Fˣ) := by
    rw [det_submatrix_equiv_self, det_kronecker, det_one, one_pow, one_mul, ← map_inv, Units.val_pow_eq_pow_val]
    rfl
  let g : GL κ F := GeneralLinearGroup.mkOfDetNeZero G (hG ▸ Units.ne_zero _)
  have hg : GeneralLinearGroup.det g = (GeneralLinearGroup.det t₁)⁻¹ ^ Fintype.card α := Units.ext hG
  have hgx : ∀ X : Matrix α β F, g.val.mulVec (flat σ X) = flat σ (X * (t₁⁻¹).valᵀ) := by
    intro X
    funext k
    show ∑ k', ((1 : Matrix α α F) ⊗ₖ (t₁⁻¹).val) (σ k) (σ k') * X (σ k').1 (σ k').2 = _
    rw [Fintype.sum_equiv σ _ (fun q => ((1 : Matrix α α F) ⊗ₖ (t₁⁻¹).val) (σ k) q * X q.1 q.2) fun _ => rfl,
      Fintype.sum_prod_type, flat_apply, mul_apply]
    simp [kroneckerMap_apply, one_apply, mul_comm]
  set s := splitChar (distribHaarChar F) χ (Fintype.card α) (GeneralLinearGroup.det (ugFst _ p)) with hs
  have key := diag_invariant_comp ψ hψ hψ1 l hl' g ((SB _).smul_mem s hφ)
    (splitOm_mem_SB (distribHaarChar F) χ (dbl JB) (dblNum σ) p hφ) (fun x => by
      obtain ⟨X, rfl⟩ := (flat σ).surjective x
      rw [splitOm_apply, hgx, ← flat_fromCols, ← flat_fromCols, LinearEquiv.symm_apply_apply, ← hD, ← hD,
        Matrix.mul_assoc, Matrix.mul_assoc, ← transpose_mul, ← transpose_mul, h1']
      rfl)
  have hpos : ∀ u : Fˣ, (0 : ℝ) < distribHaarChar F u := fun u => distribHaarChar_pos (A := F) (g := u)
  have hne : ((distribHaarChar F (GeneralLinearGroup.det g) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hpos _).ne'
  refine mul_left_cancel₀ hne ?_
  rw [key, map_smul, smul_eq_mul, ← mul_assoc]
  congr 1
  have hdet : GeneralLinearGroup.det t = Units.map (MonoidHom.inl F F) (GeneralLinearGroup.det (ugFst _ p)) *
      Units.map (algebraMap F (F × F) : F →* F × F) (GeneralLinearGroup.det t₂) := by
    refine Units.ext (Prod.ext ?_ ?_)
    · exact ((RingHom.fst F F).map_det t.val).trans h2.symm
    · exact ((RingHom.snd F F).map_det t.val).trans (one_mul _).symm
  have hN : Units.map (Algebra.norm F : F × F →* F) (GeneralLinearGroup.det t) =
      GeneralLinearGroup.det t₁ * GeneralLinearGroup.det t₂ := by
    refine Units.ext ((norm_pair _).trans ?_)
    exact congrArg₂ (· * ·) ((RingHom.fst F F).map_det t.val) ((RingHom.snd F F).map_det t.val)
  rw [hN, hdet, map_mul χ, hχ, mul_one, hs, mul_left_comm]
  refine congrArg₂ (fun x y : ℂ => x * y) rfl ?_
  show ((_ : ℝ) : ℂ) = _ * (((distribHaarChar F _ : ℝ) ^ _ : ℝ) : ℂ)
  rw [← Complex.ofReal_mul, hg, h2']
  congr 1
  simp only [map_mul, map_pow, map_inv, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_inv]
  have p1 := hpos (GeneralLinearGroup.det t₁)
  have p2 := hpos (GeneralLinearGroup.det t₂)
  generalize (distribHaarChar F (GeneralLinearGroup.det t₁) : ℝ) = a at p1
  generalize (distribHaarChar F (GeneralLinearGroup.det t₂) : ℝ) = b at p2
  rw [Real.mul_rpow p1.le (inv_pos.mpr p2).le, Real.mul_rpow p1.le p2.le, Real.inv_rpow p2.le, ← Real.rpow_neg p2.le,
    inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg p1.le, ← mul_assoc, ← Real.rpow_add p1]
  congr 2 <;> ring

section Pair

variable {R : Type} [CommRing R]

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] in
theorem flat_transpose (σ : κ ≃ α × β) (X : Matrix α β R) : flat (σ.trans (Equiv.prodComm α β)) Xᵀ = flat σ X := rfl

omit [DecidableEq β] [Fintype κ] in
theorem splitOm_swap_apply (m : Rˣ →* ℝ≥0) (χ : (R × R)ˣ →* Circle) (J : Matrix α α (R × R)) (σ : κ ≃ α × β)
    (g : UG (swapA R) J) (φ : (κ → R) → ℂ) (X : Matrix α β R) :
    splitOm m χ J (σ.trans (Equiv.prodComm α β)) g φ (flat σ X) =
      splitChar m χ (Fintype.card β) (GeneralLinearGroup.det (ugFst J g)) * φ (flat σ (((ugFst J g)⁻¹).val * X)) := by
  rw [splitOm_apply, ← flat_transpose σ X, LinearEquiv.symm_apply_apply, ← transpose_mul, flat_transpose]

def splitPair (m : Rˣ →* ℝ≥0) (χA χB : (R × R)ˣ →* Circle) (JA : Matrix α α (R × R)) (JB : Matrix β β (R × R))
    (σ : κ ≃ α × β) : UG (swapA R) JA × UG (swapA R) JB →* Module.End ℂ ((κ → R) → ℂ) :=
  (splitOm m χB JA (σ.trans (Equiv.prodComm α β))).noncommCoprod (splitOm m χA JB σ) fun g h => by
    refine LinearMap.ext fun φ => funext fun u => ?_
    obtain ⟨X, rfl⟩ := (flat σ).surjective u
    rw [Module.End.mul_apply, Module.End.mul_apply, splitOm_swap_apply, splitOm_apply, splitOm_apply,
      LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, splitOm_swap_apply, Matrix.mul_assoc, mul_left_comm]

theorem resEtaPow_split_iff (χ : (R × R)ˣ →* Circle) (n : ℕ) :
    ResEtaPow (⊥ : Subgroup Rˣ) χ n ↔ ∀ a : Rˣ, χ (Units.map (algebraMap R (R × R) : R →* R × R) a) = 1 := by
  refine forall_congr' fun a => ?_
  have : a ∈ (⊥ : Subgroup Rˣ) ⊔ (Units.map (Algebra.norm R : R × R →* R)).range :=
    Subgroup.mem_sup_right ⟨Units.map (MonoidHom.inl R R) a, Units.ext ((norm_pair _).trans (mul_one _))⟩
  rw [if_pos this, Circle.coe_eq_one]

end Pair

end GlobalTheory.WeilM

end
