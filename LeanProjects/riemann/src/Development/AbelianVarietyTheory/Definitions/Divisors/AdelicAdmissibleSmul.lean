import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocallyConstantSplitOm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

noncomputable section

open Matrix
open scoped NNReal Classical

namespace GlobalTheory.WeilM.SplitModel

variable {K : Type} [Field K]

def sw (K : Type) [Field K] : (K × K) →ₐ[K] (K × K) := (AlgHom.snd K K K).prod (AlgHom.fst K K K)

@[simp] lemma sw_apply (z : K × K) : sw K z = (z.2, z.1) := rfl

def xi (K : Type) [Field K] : K × K := (1, -1)

def J₁ (K : Type) [Field K] : Matrix Unit Unit (K × K) := 1

variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma symp_eq (J : Matrix ι ι (K × K)) (hJ : IsHerm (sw K) J) (x y : Matrix Unit ι (K × K)) :
    symp (sw K) (xi K) (J₁ K) J x y =
      (fun j => (x () j).1) ⬝ᵥ (J.map Prod.fst *ᵥ fun j => (y () j).2) -
      (fun j => (y () j).1) ⬝ᵥ (J.map Prod.fst *ᵥ fun j => (x () j).2) := by
  have h2 : ∀ i j, (J i j).2 = (J j i).1 := fun i j => by rw [← hJ.1 i j]; rfl
  simp only [symp, hTens, Algebra.trace_prod_apply, Algebra.trace_self_apply, xi, J₁, Fintype.sum_unique,
    Prod.fst_mul, Prod.snd_mul, Prod.fst_sum, Prod.snd_sum, sw_apply, dotProduct, mulVec, Matrix.map_apply, h2,
    Finset.mul_sum, Matrix.one_apply_eq, Prod.fst_one, Prod.snd_one]
  rw [sub_eq_add_neg, Finset.sum_comm (f := fun i j => (y () i).1 * ((J i j).1 * (x () j).2)), ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => by ring

lemma isUnit_fst (J : Matrix ι ι (K × K)) (hJ : IsHerm (sw K) J) : IsUnit (J.map Prod.fst).det := by
  have := hJ.2.map (RingHom.fst K K)
  rwa [RingHom.map_det] at this

def darb (J : Matrix ι ι (K × K)) (hJ : IsHerm (sw K) J) : Darboux (symp (sw K) (xi K) (J₁ K) J) ι where
  e :=
    { toFun := fun x => (fun j => (x () j).1, J.map Prod.fst *ᵥ fun j => (x () j).2)
      map_add' := fun x y => by
        ext j <;> simp [mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
      map_smul' := fun a x => by
        ext j <;> simp [mulVec, dotProduct, Finset.mul_sum, mul_left_comm]
      invFun := fun p => Matrix.of fun _ j => (p.1 j, ((J.map Prod.fst)⁻¹ *ᵥ p.2) j)
      left_inv := fun x => by
        ext i j
        · rfl
        · simp [mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_fst J hJ)]
      right_inv := fun p => by
        ext j
        · rfl
        · show ((J.map Prod.fst) *ᵥ ((J.map Prod.fst)⁻¹ *ᵥ p.2)) j = p.2 j
          simp [mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_fst J hJ)] }
  form := fun x y => symp_eq J hJ x y

def g₁ (J : Matrix ι ι (K × K)) : UG (sw K) J →* GL ι K :=
  (Matrix.GeneralLinearGroup.map (RingHom.fst K K)).comp (UG (sw K) J).subtype

lemma g₁_val (J : Matrix ι ι (K × K)) (g : UG (sw K) J) :
    ((g₁ J g : GL ι K) : Matrix ι ι K) = ((g : GL ι (K × K)) : Matrix ι ι (K × K)).map Prod.fst := rfl

lemma unit_fst (J : Matrix ι ι (K × K)) (g : UG (sw K) J) :
    ((g₁ J g : GL ι K) : Matrix ι ι K)ᵀ * J.map Prod.fst *
      ((g : GL ι (K × K)) : Matrix ι ι (K × K)).map Prod.snd = J.map Prod.fst := by
  have h : ((g : GL ι (K × K)) : Matrix ι ι (K × K))ᵀ * J * ((g : GL ι (K × K)) : Matrix ι ι (K × K)).map (sw K) = J := g.2
  have h' := congrArg (fun M : Matrix ι ι (K × K) => M.map (RingHom.fst K K)) h
  simp only [Matrix.map_mul] at h'
  exact h'

def om (lam : Kˣ →* ℂ) (J : Matrix ι ι (K × K)) : UG (sw K) J →* Module.End ℂ ((ι → K) → ℂ) where
  toFun g := lam (Matrix.GeneralLinearGroup.det (g₁ J g)) •
    LinearMap.funLeft ℂ ℂ (fun x : ι → K => (((g₁ J g)⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ x)
  map_one' := by
    ext φ x; simp [LinearMap.funLeft_apply]
  map_mul' g h := by
    refine LinearMap.ext fun φ => funext fun x => ?_
    simp only [map_mul, _root_.mul_inv_rev, Units.val_mul, LinearMap.smul_apply, Pi.smul_apply,
      LinearMap.funLeft_apply, Module.End.mul_apply, map_smul, smul_eq_mul, mulVec_mulVec]
    ring

lemma om_apply (lam : Kˣ →* ℂ) (J : Matrix ι ι (K × K)) (g : UG (sw K) J) (φ : (ι → K) → ℂ) (x : ι → K) :
    om lam J g φ x = lam (Matrix.GeneralLinearGroup.det (g₁ J g)) *
      φ ((((g₁ J g)⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ x) := rfl

lemma darb_act (J : Matrix ι ι (K × K)) (hJ : IsHerm (sw K) J) (g : UG (sw K) J) (w : Matrix Unit ι (K × K)) :
    (darb J hJ).e (actB (sw K) g w) = (((g₁ J g : GL ι K) : Matrix ι ι K) *ᵥ ((darb J hJ).e w).1,
      (((g₁ J g)⁻¹ : GL ι K) : Matrix ι ι K)ᵀ *ᵥ ((darb J hJ).e w).2) := by
  have h1 : (fun j => (actB (sw K) g w () j).1) = ((g₁ J g : GL ι K) : Matrix ι ι K) *ᵥ fun j => (w () j).1 := by
    ext j; simp [actB, g₁_val, Matrix.mul_apply, mulVec, dotProduct, Prod.fst_sum, mul_comm]
  have h2 : (fun j => (actB (sw K) g w () j).2) =
      ((g : GL ι (K × K)) : Matrix ι ι (K × K)).map Prod.snd *ᵥ fun j => (w () j).2 := by
    ext j; simp [actB, Matrix.mul_apply, mulVec, dotProduct, Prod.snd_sum, mul_comm]
  show ((fun j => (actB (sw K) g w () j).1), J.map Prod.fst *ᵥ fun j => (actB (sw K) g w () j).2) =
    (_ *ᵥ fun j => (w () j).1, _ *ᵥ (J.map Prod.fst *ᵥ fun j => (w () j).2))
  rw [h1, h2, mulVec_mulVec, mulVec_mulVec]
  congr 2
  conv_rhs => rw [← unit_fst J g]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one,
    Matrix.one_mul]

variable [Invertible (2 : K)]

lemma om_impl (ψ : AddChar K ℂ) (lam : Kˣ →* ℂ) (J : Matrix ι ι (K × K)) (hJ : IsHerm (sw K) J) (g : UG (sw K) J)
    (w : Matrix Unit ι (K × K)) (φ : (ι → K) → ℂ) :
    om lam J g ((darb J hJ).rho ψ w φ) = (darb J hJ).rho ψ (actB (sw K) g w) (om lam J g φ) := by
  funext x
  simp only [om_apply, Darboux.rho, schr, darb_act, mulVec_add, mulVec_mulVec, Units.inv_mul, one_mulVec,
    dotProduct_mulVec, vecMul_transpose]
  ring

omit [Invertible (2 : K)] in
lemma herm_one : IsHerm (sw K) (J₁ K) := ⟨fun i j => by simp [J₁], by simp [J₁]⟩

omit [Invertible (2 : K)] in
lemma herm_dbl : IsHerm (sw K) (dbl (J₁ K)) := by
  refine ⟨?_, ?_⟩
  · rintro (i | i) (j | j) <;> simp [dbl, J₁, Prod.ext_iff]
  · simp [dbl, J₁, Matrix.det_fromBlocks_zero₂₁]

lemma isQuad : IsQuad (sw K) (xi K) where
  unit := IsUnit.of_mul_eq_one (xi K) (by simp [xi, Prod.ext_iff])
  anti := by ext <;> simp [xi]
  basis := by
    have h2 : (2 : K) ≠ 0 := Invertible.ne_zero 2
    refine ⟨Module.Basis.mk (v := ![1, xi K]) ?_ ?_, Module.Basis.mk_apply _ _ 0, Module.Basis.mk_apply _ _ 1⟩
    · rw [LinearIndependent.pair_iff]
      intro s t h
      have h1 := congrArg Prod.fst h
      have h3 := congrArg Prod.snd h
      simp [xi] at h1 h3
      have : (2 : K) * s = 0 := by linear_combination h1 + h3
      have hs : s = 0 := by simpa [h2] using this
      exact ⟨hs, by simpa [hs] using h1⟩
    · intro z _
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨![(z.1 + z.2) / 2, (z.1 - z.2) / 2], ?_⟩
      simp only [xi, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      ext <;> simp <;> field_simp <;> ring

omit [Invertible (2 : K)] in
lemma dbl_coord : IsDblCoord (sw K) (xi K) (J₁ K) (J₁ K) (darb (J₁ K) herm_one) (darb (dbl (J₁ K)) herm_dbl) := by
  intro w₁ w₂
  ext (j | j) <;> simp [darb, dbl, J₁, mulVec, dotProduct]

def lamOf (χ : (K × K)ˣ →* Circle) : Kˣ →* ℂ :=
  Circle.coeHom.comp (χ.comp (Units.map (MonoidHom.inl K K)))

omit [Invertible (2 : K)] in
lemma det_siegel (p : UG (sw K) (dbl (J₁ K))) (t : GL Unit (K × K))
    (h : ((p : GL (Unit ⊕ Unit) (K × K)) : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) (K × K)) * (diagCols Unit : Matrix (Unit ⊕ Unit) Unit (K × K)) =
      (diagCols Unit : Matrix (Unit ⊕ Unit) Unit (K × K)) * (t : Matrix Unit Unit (K × K))) :
    (((g₁ _ p : GL (Unit ⊕ Unit) K) : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) K) *ᵥ fun _ => (1 : K)) = (fun _ => ((t : Matrix Unit Unit (K × K)) () ()).1) ∧
    ((g₁ _ p : GL (Unit ⊕ Unit) K) : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) K).det * ((t : Matrix Unit Unit (K × K)) () ()).2 =
      ((t : Matrix Unit Unit (K × K)) () ()).1 := by
  have u := unit_fst _ p
  rw [g₁_val] at u ⊢
  set P := ((p : GL (Unit ⊕ Unit) (K × K)) : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) (K × K))
  set τ := (t : Matrix Unit Unit (K × K)) () () with hτ
  have a1 := congrFun (congrFun h (Sum.inl ())) ()
  have a2 := congrFun (congrFun h (Sum.inr ())) ()
  rw [Matrix.mul_apply, Matrix.mul_apply] at a1 a2
  simp [diagCols, ← hτ] at a1 a2
  have a11 := congrArg Prod.fst a1
  have a12 := congrArg Prod.snd a1
  have a21 := congrArg Prod.fst a2
  have a22 := congrArg Prod.snd a2
  change _ + _ = τ.1 at a11 a21
  change _ + _ = τ.2 at a12 a22
  have u11 := congrFun (congrFun u (Sum.inl ())) (Sum.inl ())
  have u12 := congrFun (congrFun u (Sum.inl ())) (Sum.inr ())
  have u21 := congrFun (congrFun u (Sum.inr ())) (Sum.inl ())
  have u22 := congrFun (congrFun u (Sum.inr ())) (Sum.inr ())
  simp [dbl, J₁, Matrix.mul_apply] at u11 u12 u21 u22
  constructor
  · ext (j | j) <;> simp [mulVec, dotProduct, a11, a21]
  · have hd : (P.map Prod.fst).det = (P (.inl ()) (.inl ())).1 * (P (.inr ()) (.inr ())).1 -
        (P (.inl ()) (.inr ())).1 * (P (.inr ()) (.inl ())).1 := by
      rw [← Matrix.det_reindex_self ((Equiv.sumCongr finOneEquiv.symm finOneEquiv.symm).trans finSumFinEquiv), Matrix.det_fin_two]
      rfl
    rw [hd]

    have e : τ.2 * ((P (.inl ()) (.inl ())).1 - (P (.inr ()) (.inl ())).1) = 1 := by
      linear_combination u11 + u12 - (P (.inl ()) (.inl ())).1 * a12 + (P (.inr ()) (.inl ())).1 * a22
    linear_combination τ.1 * e + τ.2 * (P (.inl ()) (.inl ())).1 * a21 - τ.2 * (P (.inr ()) (.inl ())).1 * a11

variable [Fintype K]

lemma inv_form (ψ : AddChar K ℂ) (hψ : ψ ≠ 1) (l : ((Unit ⊕ Unit → K) → ℂ) →ₗ[ℂ] ℂ)
    (hl : ∀ (z : Matrix Unit Unit (K × K)) φ, l ((darb (dbl (J₁ K)) herm_dbl).rho ψ (z * (diagCols Unit : Matrix (Unit ⊕ Unit) Unit (K × K))ᵀ) φ) = l φ)
    (g : GL (Unit ⊕ Unit) K) (s : K) (hg : ((g : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) K) *ᵥ fun _ => (1 : K)) = fun _ => s)
    (φ : (Unit ⊕ Unit → K) → ℂ) :
    l (fun x => φ (((g⁻¹ : GL _ K) : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) K) *ᵥ x)) = l φ := by
  have rho : ∀ (a b : K) φ, (darb (dbl (J₁ K)) herm_dbl).rho ψ ((Matrix.of fun _ _ => (a, b) : Matrix Unit Unit (K × K)) * (diagCols Unit : Matrix (Unit ⊕ Unit) Unit (K × K))ᵀ) φ =
      fun x => ψ ((x (.inl ()) - x (.inr ())) * b) * φ (x + fun _ => a) := by
    intro a b φ
    funext x
    have : (darb (dbl (J₁ K)) herm_dbl).e ((Matrix.of fun _ _ => (a, b) : Matrix Unit Unit (K × K)) * (diagCols Unit : Matrix (Unit ⊕ Unit) Unit (K × K))ᵀ) =
        (fun _ => a, Sum.elim (fun _ => b) (fun _ => -b)) := by
      have hz : ((Matrix.of fun _ _ => (a, b) : Matrix Unit Unit (K × K)) * (diagCols Unit : Matrix (Unit ⊕ Unit) Unit (K × K))ᵀ) =
          Matrix.of fun _ _ => (a, b) := by
        ext i (j | j) : 2 <;> rw [Matrix.mul_apply] <;> simp [diagCols]
      rw [hz]
      ext (j | j) <;> simp [darb, dbl, J₁, mulVec, dotProduct]
    simp only [Darboux.rho, schr, this]
    congr 2
    simp [dotProduct]; ring
  set m : (Unit ⊕ Unit → K) → ℂ := fun x => l (Pi.single x 1) with hm
  have off : ∀ x, x (.inl ()) ≠ x (.inr ()) → m x = 0 := by
    intro x hx
    obtain ⟨b, hb⟩ := AddChar.ne_one_iff.mp hψ
    have h := hl (Matrix.of fun _ _ => (0, (x (.inl ()) - x (.inr ()))⁻¹ * b)) (Pi.single x 1)
    rw [rho] at h
    have e : (fun y : Unit ⊕ Unit → K => ψ ((y (.inl ()) - y (.inr ())) * ((x (.inl ()) - x (.inr ()))⁻¹ * b)) *
        (Pi.single x 1 : (Unit ⊕ Unit → K) → ℂ) (y + fun _ => 0)) = ψ b • (Pi.single x 1 : (Unit ⊕ Unit → K) → ℂ) := by
      funext y
      have : (y + fun _ => 0) = y := by ext; simp
      rw [this]
      by_cases hy : y = x
      · subst hy
        rw [mul_inv_cancel_left₀ (sub_ne_zero.mpr hx)]; simp
      · simp [hy]
    rw [e, map_smul, smul_eq_mul] at h
    have : (ψ b - 1) * m x = 0 := by rw [sub_mul, one_mul, sub_eq_zero]; exact h
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hb)
  have dia : ∀ a : K, m (fun _ => a) = m 0 := by
    intro a
    have h := hl (Matrix.of fun _ _ => (a, 0)) (Pi.single (fun _ => a) 1)
    rw [rho] at h
    rw [hm]
    simp only
    rw [← h]
    congr 1
    funext y
    by_cases hy : y = 0
    · subst hy; simp
    · have : (y + fun _ => a) ≠ fun _ => a := fun hh => hy (by simpa using hh)
      simp [hy, this]
  have cst : ∀ x : Unit ⊕ Unit → K, x (.inl ()) = x (.inr ()) → x = fun _ => x (.inl ()) := by
    intro x hx
    ext (j | j)
    · rfl
    · exact hx.symm
  have gc : ∀ a : K, (g : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) K) *ᵥ (fun _ => a) = fun _ => a * s := by
    intro a
    have : (fun _ : Unit ⊕ Unit => a) = a • fun _ => (1 : K) := by ext; simp
    rw [this, mulVec_smul, hg]; ext; simp
  have inj : ∀ x y : Unit ⊕ Unit → K, (g : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) K) *ᵥ x = (g : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) K) *ᵥ y → x = y := by
    intro x y h
    have := congrArg (fun v => ((g⁻¹ : GL _ K) : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) K) *ᵥ v) h
    simpa only [mulVec_mulVec, Units.inv_mul, one_mulVec] using this
  have hs : s ≠ 0 := by
    intro h0
    have := inj (fun _ => 1) (fun _ => 0) (by rw [gc, gc, h0]; simp)
    exact one_ne_zero (congrFun this (.inl ()))
  have mg : ∀ x, m ((g : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) K) *ᵥ x) = m x := by
    intro x
    by_cases hx : x (.inl ()) = x (.inr ())
    · rw [cst x hx, gc, dia, dia]
    · rw [off x hx]
      apply off
      intro h
      have h1 := cst _ h
      set b := ((g : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) K) *ᵥ x) (.inl ())
      have := inj x (fun _ => b / s) (by rw [h1, gc, div_mul_cancel₀ _ hs])
      exact hx (by rw [this])
  have key : l ∘ₗ LinearMap.funLeft ℂ ℂ (fun x : Unit ⊕ Unit → K => ((g⁻¹ : GL _ K) : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) K) *ᵥ x) = l := by
    refine LinearMap.pi_ext' fun x => LinearMap.ext_ring ?_
    have := mg x
    simp only [hm] at this
    simp only [LinearMap.comp_apply, LinearMap.single_apply]
    rw [← this]
    congr 1
    funext y
    simp only [LinearMap.funLeft_apply, Pi.single_apply]
    congr 1
    apply propext
    constructor
    · intro h; rw [← h, mulVec_mulVec, Units.mul_inv, one_mulVec]
    · intro h; rw [h, mulVec_mulVec, Units.inv_mul, one_mulVec]
  exact LinearMap.congr_fun key φ

variable [TopologicalSpace K] [DiscreteTopology K] [IsTopologicalRing K]

omit [Invertible (2 : K)] in
lemma mem_sp (κ : Type) [Fintype κ] (φ : (κ → K) → ℂ) : φ ∈ (sbClass K).sp κ :=
  ⟨IsLocallyConstant.of_discrete φ, HasCompactSupport.of_compactSpace φ⟩

omit [Invertible (2 : K)] in
lemma modu_one (u : Kˣ) : (sbClass K).modu u = 1 := by
  have h : (sbClass K).modu u ^ Fintype.card Kˣ = 1 := by rw [← map_pow, pow_card_eq_one, map_one]
  exact (pow_eq_one_iff_of_nonneg zero_le' Fintype.card_ne_zero).mp h

lemma om_split (ψ : AddChar K ℂ) (lam : Kˣ →* ℂ) (J : Matrix ι ι (K × K)) (hJ : IsHerm (sw K) J) :
    IsSplitting (sbClass K) ψ (darb J hJ) (actB (sw K)) (om lam J) :=
  ⟨fun _ _ _ => mem_sp _ _, fun g w φ _ => om_impl ψ lam J hJ g w φ, fun _ _ _ => Set.mem_univ _⟩

omit [Invertible (2 : K)] [Fintype K] [TopologicalSpace K] [DiscreteTopology K] [IsTopologicalRing K] in

lemma norm_onto (a : Kˣ) : a ∈ (⊥ : Subgroup Kˣ) ⊔ (Units.map (Algebra.norm K : K × K →* K)).range := by
  rw [bot_sup_eq]
  refine ⟨Units.map (MonoidHom.inl K K) a, ?_⟩
  ext
  show Algebra.norm K (((a : K), (1 : K)) : K × K) = a
  rw [Algebra.norm_eq_matrix_det (Module.Basis.finTwoProd K), Matrix.det_fin_two]
  simp [Algebra.leftMulMatrix_eq_repr_mul, Module.Basis.finTwoProd]

theorem isWeilB (ψ : AddChar K ℂ) (hψ : ψ ≠ 1) (χ : (K × K)ˣ →* Circle) (hχ : ResEtaPow (R := K) (E := K × K) ⊥ χ 1) :
    IsWeilB (sw K) (sbClass K) ψ (xi K) (J₁ K) (J₁ K) (darb (J₁ K) herm_one) χ (om (lamOf χ) (J₁ K)) := by
  refine ⟨om_split _ _ _ _, darb (dbl (J₁ K)) herm_dbl, om (lamOf χ) _, dbl_coord, om_split _ _ _ _, ?_, ?_⟩
  · intro l _ hl p t hp φ _
    obtain ⟨h1, h2⟩ := det_siegel p t hp
    have hi := inv_form ψ hψ l (fun z φ => hl z φ (mem_sp _ _)) _ _ h1 φ
    have e : om (lamOf χ) _ p φ = lamOf χ (Matrix.GeneralLinearGroup.det (g₁ _ p)) •
      (fun x => φ ((((g₁ _ p)⁻¹ : GL _ K) : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) K) *ᵥ x)) := rfl
    rw [e, map_smul, hi, modu_one, smul_eq_mul]
    congr 1
    set a : Kˣ := Units.map (MonoidHom.snd K K) (Matrix.GeneralLinearGroup.det t)
    have ha := hχ a
    rw [if_pos (norm_onto a)] at ha
    have e2 : Matrix.GeneralLinearGroup.det t = Units.map (MonoidHom.inl K K) (Matrix.GeneralLinearGroup.det (g₁ _ p)) *
        Units.map (algebraMap K (K × K) : K →* K × K) a := by
      ext
      · simp [a, ← h2]
      · simp [a]
    rw [e2, map_mul, Circle.coe_mul, ha]
    simp [lamOf]
    rfl
  · intro g gd hg φ₁ _ φ₂ _
    have hm : ((g₁ _ gd : GL (Unit ⊕ Unit) K) : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) K) =
        Matrix.fromBlocks ((g₁ _ g : GL Unit K) : Matrix Unit Unit K) 0 0 1 := by
      rw [g₁_val, hg, g₁_val]
      ext (i | i) (j | j) <;> simp
    have hi : (((g₁ _ gd)⁻¹ : GL (Unit ⊕ Unit) K) : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) K) =
        Matrix.fromBlocks (((g₁ _ g)⁻¹ : GL Unit K) : Matrix Unit Unit K) 0 0 1 := by
      apply Units.inv_eq_of_mul_eq_one_right
      rw [hm, Matrix.fromBlocks_multiply]
      simp only [Units.mul_inv]
      simp
    have hd : Matrix.GeneralLinearGroup.det (g₁ _ gd) = Matrix.GeneralLinearGroup.det (g₁ _ g) := by
      ext
      simp only [Matrix.GeneralLinearGroup.val_det_apply, hm, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
    funext x
    simp only [om_apply, boxFun, hi, hd, Matrix.fromBlocks_mulVec, mul_assoc]
    simp

omit [Invertible (2 : K)] [Fintype K] [TopologicalSpace K] [DiscreteTopology K] [IsTopologicalRing K] in
lemma om_comm (lam lam' : Kˣ →* ℂ) (g h : UG (sw K) (J₁ K)) : Commute (om lam (J₁ K) g) (om lam' (J₁ K) h) := by
  refine LinearMap.ext fun φ => funext fun x => ?_
  simp only [Module.End.mul_apply, om_apply, mulVec_mulVec]
  have : ∀ M N : Matrix Unit Unit K, M * N = N * M := fun M N => by
    ext i j; simp [Matrix.mul_apply, mul_comm]
  rw [this]; ring

theorem isWeilPair (ψ : AddChar K ℂ) (hψ : ψ ≠ 1) (χA χB : (K × K)ˣ →* Circle)
    (hA : ResEtaPow (R := K) (E := K × K) ⊥ χA 1) (hB : ResEtaPow (R := K) (E := K × K) ⊥ χB 1) :
    IsWeilPair (sw K) (sbClass K) ψ (xi K) (J₁ K) (J₁ K) (darb (J₁ K) herm_one) χA χB
      ((om (lamOf χB) (J₁ K)).noncommCoprod (om (lamOf χA) (J₁ K)) (om_comm _ _)) := by
  refine ⟨?_, darb (J₁ K) herm_one, fun x => ?_, ?_⟩
  · rw [MonoidHom.noncommCoprod_comp_inr]; exact isWeilB ψ hψ χA hA
  · congr 1
  · rw [MonoidHom.noncommCoprod_comp_inl]; exact isWeilB ψ hψ χB hB

end GlobalTheory.WeilM.SplitModel

namespace GlobalTheory.WeilM.SplitModel

theorem schr_mul {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add, add_assoc, ← mul_assoc,
    ← AddChar.map_add_eq_mul, add_dotProduct, dotProduct_add]
  congr 2
  have h : ⅟(2 : R) * 2 = 1 := invOf_mul_self 2
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * h

theorem exists_three : ∃ (_ : Invertible (2 : ZMod 3)) (ψ : AddChar (ZMod 3) ℂ) (χ : (ZMod 3 × ZMod 3)ˣ →* Circle),
    ψ ≠ 1 ∧ ResEtaPow (R := ZMod 3) (E := ZMod 3 × ZMod 3) ⊥ χ 1 := by
  refine ⟨⟨2, by decide, by decide⟩, ZMod.stdAddChar, 1, ?_, fun a => ?_⟩
  · have h := ZMod.isPrimitive_stdAddChar 3 (a := 1) one_ne_zero
    rwa [AddChar.mulShift_one] at h
  · rw [if_pos (norm_onto a)]; simp

theorem isQuad_complex : IsQuad (Complex.conjAe : ℂ →ₐ[ℝ] ℂ) Complex.I where
  unit := IsUnit.mk0 _ Complex.I_ne_zero
  anti := by simp
  basis := ⟨Complex.basisOneI, by simp, by simp⟩

theorem om_split_real {ι : Type} [Fintype ι] [DecidableEq ι] [Invertible (2 : ℝ)] (ψ : AddChar ℝ ℂ) (lam : ℝˣ →* ℂ)
    (J : Matrix ι ι (ℝ × ℝ)) (hJ : IsHerm (sw ℝ) J) :
    IsSplitting realClass ψ (darb J hJ) (actB (sw ℝ)) (om lam J) := by
  have key : ∀ g : UG (sw ℝ) J, ∃ T : SchwartzMap (ι → ℝ) ℂ →L[ℂ] SchwartzMap (ι → ℝ) ℂ,
      ∀ f : SchwartzMap (ι → ℝ) ℂ, om lam J g (f : (ι → ℝ) → ℂ) = T f := by
    intro g
    let e : (ι → ℝ) ≃L[ℝ] (ι → ℝ) := (Matrix.GeneralLinearGroup.toLin (g₁ J g)⁻¹).toLinearEquiv.toContinuousLinearEquiv
    refine ⟨lam (Matrix.GeneralLinearGroup.det (g₁ J g)) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e, fun f => ?_⟩
    funext x
    rfl
  refine ⟨fun g φ hφ => ?_, fun g w φ _ => om_impl ψ lam J hJ g w φ, fun g l hl => ?_⟩
  · obtain ⟨T, hT⟩ := key g
    refine Submodule.span_induction (p := fun φ _ => om lam J g φ ∈ schFun (ι → ℝ)) ?_ ?_ ?_ ?_ hφ
    · rintro _ ⟨f, rfl⟩
      exact Submodule.subset_span ⟨T f, (hT f).symm⟩
    · simp
    · intro a b _ _ ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb
    · intro a b _ hb; rw [map_smul]; exact Submodule.smul_mem _ _ hb
  · obtain ⟨T, hT⟩ := key g
    obtain ⟨S, hS⟩ := hl
    exact ⟨S.comp T, fun f => by rw [LinearMap.comp_apply, hT, hS]; rfl⟩

end GlobalTheory.WeilM.SplitModel

end

noncomputable section

open MeasureTheory Matrix ValuativeRel NumberField
open scoped NNReal Topology

namespace GlobalTheory.WeilM.SiegelModel

section Alg

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]

theorem det_siegel {JB : Matrix β β E} (hB : IsHerm c JB) (p : UG c (dbl JB)) (t : Matrix β β E)
    (h : ((p : GL (β ⊕ β) E) : Matrix (β ⊕ β) (β ⊕ β) E) * (diagCols β : Matrix (β ⊕ β) β E) =
      (diagCols β : Matrix (β ⊕ β) β E) * t) :
    ((p : GL (β ⊕ β) E) : Matrix (β ⊕ β) (β ⊕ β) E).det * c t.det = t.det := by
  have hp : ((p : GL (β ⊕ β) E) : Matrix (β ⊕ β) (β ⊕ β) E)ᵀ * dbl JB *
    ((p : GL (β ⊕ β) E) : Matrix (β ⊕ β) (β ⊕ β) E).map c = dbl JB := p.2
  have d1 : (diagCols β : Matrix (β ⊕ β) β E).map c = diagCols β := by
    ext (i | i) j <;> by_cases hij : i = j <;> simp [diagCols, hij]
  have h2 : ((p : GL (β ⊕ β) E) : Matrix (β ⊕ β) (β ⊕ β) E).map c * (diagCols β : Matrix (β ⊕ β) β E) =
      (diagCols β : Matrix (β ⊕ β) β E) * t.map c := by
    have := congrArg (fun M : Matrix (β ⊕ β) β E => M.map c.toRingHom) h
    simp only [Matrix.map_mul] at this
    rw [← d1]; exact this
  have h3 := congrArg (· * (diagCols β : Matrix (β ⊕ β) β E)) hp
  simp only [Matrix.mul_assoc, h2] at h3
  generalize ((p : GL (β ⊕ β) E) : Matrix (β ⊕ β) (β ⊕ β) E) = P at h h3
  obtain ⟨a, b, e, d, rfl⟩ : ∃ a b e d, P = fromBlocks a b e d := ⟨_, _, _, _, (fromBlocks_toBlocks P).symm⟩
  simp only [dbl, diagCols, fromBlocks_transpose, fromRows_mul, fromBlocks_mul_fromRows, Matrix.mul_one, Matrix.one_mul,
    Matrix.zero_mul, add_zero, zero_add, fromRows_ext_iff] at h h3
  have h4 : (d - b)ᵀ * JB * t.map c = JB := by
    rw [transpose_sub, Matrix.mul_assoc, Matrix.sub_mul, ← neg_inj, ← h3.2, Matrix.neg_mul, Matrix.mul_neg]; abel
  have h5 : (d - b).det * c t.det = 1 := by
    have := congrArg det h4
    rw [det_mul, det_mul, det_transpose, show (t.map c).det = c t.det from (c.toRingHom.map_det _).symm] at this
    exact hB.2.mul_left_cancel (by linear_combination this)
  have h6 : fromBlocks a b e d * fromBlocks 1 0 1 1 =
      fromBlocks (1 : Matrix β β E) 0 (1 : Matrix β β E) (1 : Matrix β β E) * fromBlocks t b 0 (d - b) := by
    simp [fromBlocks_multiply, h.1, h.2]
  have h7 := congrArg det h6
  rw [det_mul, det_mul, det_fromBlocks_zero₁₂, det_fromBlocks_zero₂₁, det_one] at h7
  linear_combination c t.det * h7 + t.det * h5

variable [Invertible (2 : R)]

omit [DecidableEq α] in

theorem rho_diag (ψ : AddChar R ℂ) {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {d : Darboux (symp c ξ JA JB) κ}
    {dd : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ)} (h : IsDblCoord c ξ JA JB d dd) (z : Matrix α β E)
    (φ : (κ ⊕ κ → R) → ℂ) (u : κ → R) :
    dd.rho ψ (z * (diagCols β : Matrix (β ⊕ β) β E)ᵀ) φ (Sum.elim u u) = φ (Sum.elim (u + (d.e z).1) (u + (d.e z).1)) := by
  rw [diagCols, transpose_fromRows, mul_fromCols, transpose_one, Matrix.mul_one, Darboux.rho, h, schr]
  have e : (Sum.elim u u + Sum.elim (d.e z).1 (d.e z).1 : κ ⊕ κ → R) = Sum.elim (u + (d.e z).1) (u + (d.e z).1) := by
    ext (k | k) <;> rfl
  simp [sumElim_dotProduct_sumElim, e]

theorem exists_levi {ξ : E} (hq : IsQuad c ξ) (JB : Matrix Unit Unit E) (t : Eˣ) :
    ∃ (p : UG c (dbl JB)) (T : GL Unit E), GeneralLinearGroup.det T = t ∧
      ((p : GL (Unit ⊕ Unit) E) : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) E) * (diagCols Unit : Matrix (Unit ⊕ Unit) Unit E) =
      (diagCols Unit : Matrix (Unit ⊕ Unit) Unit E) * (T : Matrix Unit Unit E) := by
  set h : E := algebraMap R E (⅟(2 : R)) with hh
  have h2 : h * 2 = 1 := by rw [hh, ← map_ofNat (algebraMap R E) 2, ← map_mul, invOf_mul_self, map_one]
  have hc : c h = h := c.commutes _
  let M : E → E → Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) E := fun x y =>
    fromBlocks (of fun _ _ => h * (x + y)) (of fun _ _ => h * (x - y)) (of fun _ _ => h * (x - y)) (of fun _ _ => h * (x + y))
  have hM : ∀ x y x' y', x * x' = 1 → y * y' = 1 → M x y * M x' y' = 1 := fun x y x' y' hx hy => by
    ext (i | i) (j | j) <;> simp [M, mul_apply]
    · linear_combination (h * 2 * h) * hx + (h * 2 * h) * hy + (h * 2 + 1) * h2
    · linear_combination (h * 2 * h) * hx - (h * 2 * h) * hy
    · linear_combination (h * 2 * h) * hx - (h * 2 * h) * hy
    · linear_combination (h * 2 * h) * hx + (h * 2 * h) * hy + (h * 2 + 1) * h2
  have a1 : (t : E) * (t⁻¹ : Eˣ) = 1 := t.mul_inv
  have a2 : c (t : E) * c (t⁻¹ : Eˣ) = 1 := by rw [← map_mul, a1, map_one]
  refine ⟨⟨⟨M t (c (t⁻¹ : Eˣ)), M (t⁻¹ : Eˣ) (c t), hM _ _ _ _ a1 (by rw [mul_comm, a2]),
    hM _ _ _ _ (by rw [mul_comm, a1]) a2⟩, ?_⟩,
    ⟨of fun _ _ => (t : E), of fun _ _ => ((t⁻¹ : Eˣ) : E), ?_, ?_⟩, ?_, ?_⟩
  · show (M t (c (t⁻¹ : Eˣ)))ᵀ * dbl JB * (M t (c (t⁻¹ : Eˣ))).map c = dbl JB
    generalize ((t⁻¹ : Eˣ) : E) = s at a1 a2
    ext (i | i) (j | j) <;> simp [M, mul_apply, dbl, hc, hq.invol]
    · linear_combination (h * 2 * h * JB () ()) * a1 + (h * 2 * h * JB () ()) * a2 + JB () () * (h * 2 + 1) * h2
    · linear_combination -(h * 2 * h * JB () ()) * a1 + (h * 2 * h * JB () ()) * a2
    · linear_combination (h * 2 * h * JB () ()) * a1 - (h * 2 * h * JB () ()) * a2
    · linear_combination -(h * 2 * h * JB () ()) * a1 - (h * 2 * h * JB () ()) * a2 - JB () () * (h * 2 + 1) * h2
  · ext; simp [mul_apply]
  · ext; simp [mul_apply]
  · ext; simp
  · ext (i | i) j <;> simp [M, mul_apply, diagCols] <;> linear_combination (t : E) * h2

end Alg

section Forms

variable {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]

def HasDiagForm (C : TestClass R) (κ : Type) [Fintype κ] : Prop :=
  ∃ l ∈ C.adm (κ ⊕ κ), (∃ φ ∈ C.sp (κ ⊕ κ), l φ ≠ 0) ∧ ∀ φ ∈ C.sp (κ ⊕ κ), ∀ (φ' : (κ ⊕ κ → R) → ℂ) (a : κ → R),
    (∀ u, φ' (Sum.elim u u) = φ (Sum.elim (u + a) (u + a))) → l φ' = l φ

omit [Invertible (2 : R)] in

theorem hasDiagForm_of (C : TestClass R) (S : Submodule ℂ ((κ → R) → ℂ)) (m : S →ₗ[ℂ] ℂ)
    (hS : ∀ φ ∈ C.sp (κ ⊕ κ), (fun u => φ (Sum.elim u u)) ∈ S)
    (hT : ∀ (f : S) (a : κ → R), ∃ h : (fun u => f.1 (u + a)) ∈ S, m ⟨_, h⟩ = m f)
    (h0 : ∃ φ, ∃ h : φ ∈ C.sp (κ ⊕ κ), m ⟨_, hS φ h⟩ ≠ 0)
    (hadm : ∀ l : ((κ ⊕ κ → R) → ℂ) →ₗ[ℂ] ℂ, (∀ φ (h : φ ∈ C.sp (κ ⊕ κ)), l φ = m ⟨_, hS φ h⟩) → l ∈ C.adm (κ ⊕ κ)) :
    HasDiagForm C κ := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend m
  have hg' : ∀ f (h : f ∈ S), g f = m ⟨f, h⟩ := fun f h => LinearMap.congr_fun hg ⟨f, h⟩
  let l := g ∘ₗ LinearMap.funLeft ℂ ℂ fun u : κ → R => (Sum.elim u u : κ ⊕ κ → R)
  have hl : ∀ φ (h : φ ∈ C.sp (κ ⊕ κ)), l φ = m ⟨_, hS φ h⟩ := fun φ h => hg' _ _
  obtain ⟨φ₀, h₀, h₁⟩ := h0
  refine ⟨l, hadm l hl, ⟨φ₀, h₀, by rwa [hl _ h₀]⟩, fun φ hφ φ' a h => ?_⟩
  obtain ⟨h1, h2⟩ := hT ⟨_, hS φ hφ⟩ a
  rw [hl φ hφ, ← h2, ← hg']
  exact congrArg g (funext h)

omit [DecidableEq α] in

theorem siegel_scalar_unique {C : TestClass R} (hC : HasDiagForm C κ) {ψ : AddChar R ℂ} {ξ : E} {JA : Matrix α α E}
    {JB : Matrix β β E} {d : Darboux (symp c ξ JA JB) κ} {dd : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ)}
    (h : IsDblCoord c ξ JA JB d dd) {χ χ' : Eˣ →* Circle} {om : UG c (dbl JB) →* Module.End ℂ ((κ ⊕ κ → R) → ℂ)}
    (h1 : SiegelRule c C ψ ξ JA (dbl JB) dd χ (diagCols β) om) (h2 : SiegelRule c C ψ ξ JA (dbl JB) dd χ' (diagCols β) om)
    (p : UG c (dbl JB)) (t : GL β E)
    (hp : ((p : GL (β ⊕ β) E) : Matrix (β ⊕ β) (β ⊕ β) E) * (diagCols β : Matrix (β ⊕ β) β E) =
      (diagCols β : Matrix (β ⊕ β) β E) * (t : Matrix β β E)) :
    χ (GeneralLinearGroup.det t) = χ' (GeneralLinearGroup.det t) := by
  obtain ⟨l, hl, ⟨φ, hφ, h0⟩, hi⟩ := hC
  have hi' := fun (z : Matrix α β E) φ hφ => hi φ hφ _ _ (rho_diag ψ h z φ)
  have e := (h1 l hl hi' p t hp φ hφ).symm.trans (h2 l hl hi' p t hp φ hφ)
  have hpos : ∀ u : Rˣ, (0 : ℝ) < C.modu u := fun u => by
    have : C.modu u * C.modu u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one this))
  exact Circle.ext (mul_right_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (hpos _) _).ne')
    (mul_right_cancel₀ h0 e))

omit [DecidableEq α] in

theorem siegel_char_unique {C : TestClass R} (hC : HasDiagForm C κ) {ψ : AddChar R ℂ} {ξ : E} (hq : IsQuad c ξ)
    {JA : Matrix α α E} {JB : Matrix Unit Unit E} {d : Darboux (symp c ξ JA JB) κ}
    {dd : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ)} (h : IsDblCoord c ξ JA JB d dd) {χ χ' : Eˣ →* Circle}
    {om : UG c (dbl JB) →* Module.End ℂ ((κ ⊕ κ → R) → ℂ)}
    (h1 : SiegelRule c C ψ ξ JA (dbl JB) dd χ (diagCols Unit) om)
    (h2 : SiegelRule c C ψ ξ JA (dbl JB) dd χ' (diagCols Unit) om) : χ = χ' := by
  ext1 t
  obtain ⟨p, T, rfl, hp⟩ := exists_levi hq JB t
  exact siegel_scalar_unique hC h h1 h2 p T hp

end Forms

theorem hasDiagForm_sb (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (κ : Type) [Fintype κ] : HasDiagForm (sbClass F) κ := by
  have := SplitWeil.t2Space F
  have := SplitWeil.secondCountable F
  borelize (κ → F)
  let μ : Measure (κ → F) := Measure.addHaar
  have hi : ∀ f : SB (κ → F), Integrable f.1 μ := fun f => f.2.1.continuous.integrable_of_hasCompactSupport f.2.2
  let m : SB (κ → F) →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ x, f.1 x ∂μ
      map_add' := fun f g => integral_add (hi f) (hi g)
      map_smul' := fun a f => integral_smul a f.1 }
  let K : ∀ ι : Type, Set (ι → F) := fun ι => Set.univ.pi fun _ => (𝒪[F] : Set F)
  have hKc : ∀ ι, IsCompact (K ι) := fun ι => isCompact_univ_pi fun _ => SplitWeil.isCompact_int F
  have hK : ∀ ι [Fintype ι], IsClopen (K ι) := fun ι _ =>
    ⟨(hKc ι).isClosed, isOpen_set_pi Set.finite_univ fun _ _ => SplitWeil.isOpen_int F⟩
  refine hasDiagForm_of _ (SB (κ → F)) m (fun φ h => diag_mem_SB h) (fun f a => ⟨⟨f.2.1.comp_continuous (by fun_prop),
    f.2.2.comp_homeomorph (Homeomorph.addRight a)⟩, integral_add_right_eq_self f.1 a⟩) ⟨(K (κ ⊕ κ)).indicator 1,
    ⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) (hK _)).isLocallyConstant,
      HasCompactSupport.intro (hKc _) fun x hx => Set.indicator_of_notMem hx _⟩, ?_⟩ fun _ _ => Set.mem_univ _
  show ∫ x, (K (κ ⊕ κ)).indicator (1 : (κ ⊕ κ → F) → ℂ) (Sum.elim x x) ∂μ ≠ 0
  have e : (fun x : κ → F => (K (κ ⊕ κ)).indicator (1 : (κ ⊕ κ → F) → ℂ) (Sum.elim x x)) = (K κ).indicator fun _ => 1 := by
    funext x
    have : Sum.elim x x ∈ K (κ ⊕ κ) ↔ x ∈ K κ := by simp [K]
    by_cases hx : x ∈ K κ <;> simp [hx, this]
  rw [e, integral_indicator_const _ (hK κ).isOpen.measurableSet]
  have h1 := ((hK κ).isOpen.measure_pos μ ⟨0, fun _ _ => zero_mem _⟩).ne'
  have h2 := ((hKc κ).measure_lt_top (μ := μ)).ne
  simp [Measure.real, ENNReal.toReal_eq_zero_iff, h1, h2]

theorem mem_schFun {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {φ : V → ℂ} :
    φ ∈ schFun V ↔ ∃ f : SchwartzMap V ℂ, (f : V → ℂ) = φ := by
  refine ⟨fun h => ?_, fun ⟨f, hf⟩ => Submodule.subset_span ⟨f, hf⟩⟩
  refine Submodule.span_induction (p := fun φ _ => ∃ f : SchwartzMap V ℂ, (f : V → ℂ) = φ) (fun _ h => h) ⟨0, rfl⟩ ?_ ?_ h
  · rintro _ _ _ _ ⟨f, rfl⟩ ⟨g, rfl⟩; exact ⟨f + g, rfl⟩
  · rintro a _ _ ⟨f, rfl⟩; exact ⟨a • f, rfl⟩

theorem hasDiagForm_real (κ : Type) [Fintype κ] : HasDiagForm realClass κ := by
  let D : (κ → ℝ) →L[ℝ] (κ ⊕ κ → ℝ) := ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj (k.elim id id)
  have hD : ∀ u, D u = Sum.elim u u := fun u => by ext (k | k) <;> rfl
  have hanti : AntilipschitzWith 1 D := AddMonoidHomClass.antilipschitz_of_bound D fun u => by
    rw [NNReal.coe_one, one_mul]
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun k => norm_le_pi_norm (D u) (Sum.inl k)
  let T := SchwartzMap.compCLMOfAntilipschitz ℂ (F := ℂ) D.hasTemperateGrowth hanti
  have hT : ∀ f, (T f : (κ → ℝ) → ℂ) = fun u => f (Sum.elim u u) := fun f => funext fun u => congrArg f (hD u)
  have hi : ∀ f : schFun (κ → ℝ), Integrable f.1 := fun f => by
    obtain ⟨g, hg⟩ := mem_schFun.mp f.2
    exact hg ▸ g.integrable
  let m : schFun (κ → ℝ) →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ x, f.1 x
      map_add' := fun f g => integral_add (hi f) (hi g)
      map_smul' := fun a f => integral_smul a f.1 }
  refine hasDiagForm_of _ (schFun (κ → ℝ)) m (fun φ h => ?_) (fun f a => ⟨?_, integral_add_right_eq_self f.1 a⟩) ?_
    fun l hl => ⟨(SchwartzMap.integralCLM ℂ volume).comp T, fun f => ?_⟩
  · obtain ⟨f, rfl⟩ := mem_schFun.mp h
    exact mem_schFun.mpr ⟨T f, hT f⟩
  · obtain ⟨g, hg⟩ := mem_schFun.mp f.2
    refine mem_schFun.mpr ⟨SchwartzMap.compCLMOfAntilipschitz ℂ (F := ℂ) (g := fun u => u + a) (K := 1) (by fun_prop)
      (isometry_add_right a).antilipschitz g, ?_⟩
    rw [← hg]; rfl
  · let b : ContDiffBump (0 : κ ⊕ κ → ℝ) := default
    have hb : HasCompactSupport fun x => (b x : ℂ) := b.hasCompactSupport.comp_left (g := Complex.ofReal) rfl
    refine ⟨_, mem_schFun.mpr ⟨hb.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff), rfl⟩, ?_⟩
    show ∫ x, (b (Sum.elim x x) : ℂ) ≠ 0
    rw [integral_complex_ofReal, Complex.ofReal_ne_zero]
    simp only [← hD]
    have hs : HasCompactSupport fun x => b (D x) :=
      b.hasCompactSupport.comp_isClosedEmbedding (hanti.isClosedEmbedding D.uniformContinuous)
    refine (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0) (b.continuous.comp D.continuous) hs
      (fun x => b.nonneg) ?_).ne'
    rw [Function.comp, map_zero, b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]
    exact one_ne_zero
  · rw [hl _ (mem_schFun.mpr ⟨f, rfl⟩), ContinuousLinearMap.comp_apply, SchwartzMap.integralCLM_apply, hT]
    rfl

section RankZero

variable {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]

def darbZero (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (κ : Type) [Fintype κ] [IsEmpty κ] [IsEmpty (α × β)] :
    Darboux (R := R) (symp c ξ JA JB) κ :=
  haveI : Subsingleton (Matrix α β E) := ⟨fun _ _ => by ext i j; exact isEmptyElim (i, j)⟩
  { e := LinearEquiv.ofSubsingleton _ _
    form := fun w w' => by
      rw [Subsingleton.elim w 0]
      simp [symp, hTens, dotProduct] }

def detOm (lam : Eˣ →* Circle) (J : Matrix β β E) (X : Type) : UG c J →* Module.End ℂ (X → ℂ) :=
  (algebraMap ℂ (Module.End ℂ (X → ℂ)) : ℂ →* _).comp
    (Circle.coeHom.comp (lam.comp (GeneralLinearGroup.det.comp (UG c J).subtype)))

omit [Invertible (2 : R)] in
theorem detOm_apply (lam : Eˣ →* Circle) (J : Matrix β β E) (X : Type) (g : UG c J) (φ : X → ℂ) :
    detOm lam J X g φ = (lam (GeneralLinearGroup.det (g : GL β E)) : ℂ) • φ := rfl

variable [TopologicalSpace R] [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology R E] {C : TestClass R}

omit [IsModuleTopology R E] [DecidableEq α] in
theorem isUSplitting_detOm (hC : ∀ (κ : Type) [Fintype κ] (a : ℂ), ∀ l ∈ C.adm κ, a • l ∈ C.adm κ) (ψ : AddChar R ℂ) {ξ : E}
    {JA : Matrix α α E} {JB : Matrix β β E} [IsEmpty κ] (d : Darboux (symp c ξ JA JB) κ) {lam : Eˣ →* Circle}
    (hl : Continuous lam) : IsUSplitting C ψ d (actB c) (detOm lam JB _) := by
  refine ⟨⟨fun g φ h => Submodule.smul_mem _ _ h, fun g w φ _ => ?_, fun g l h => ?_⟩, fun μ _ g φ _ => ?_, fun l _ φ _ => ?_⟩
  · funext x
    simp [detOm_apply, Darboux.rho, schr, dotProduct, Subsingleton.elim (x + _) x]
  · convert hC κ (lam (GeneralLinearGroup.det (g : GL β E))) l h using 1
    exact LinearMap.ext fun φ => map_smul l _ φ
  · have : ∀ u : Circle, ‖(u : ℂ)‖ₑ = 1 := fun u => by rw [← ofReal_norm, u.norm_coe, ENNReal.ofReal_one]
    simp [detOm_apply, this]
  · have c1 : Continuous fun g : UG c JB => GeneralLinearGroup.det (g : GL β E) :=
      Units.continuous_iff.mpr ⟨(Units.continuous_val.comp continuous_subtype_val).matrix_det,
        (Units.continuous_val.comp continuous_subtype_val.inv).matrix_det⟩
    simp only [detOm_apply, map_smul]
    exact (continuous_subtype_val.comp (hl.comp c1)).smul continuous_const

omit [DecidableEq α] in

theorem isUWeilB_rank_zero (hC : ∀ (κ : Type) [Fintype κ] (a : ℂ), ∀ l ∈ C.adm κ, a • l ∈ C.adm κ) (ψ : AddChar R ℂ) {ξ : E}
    {JA : Matrix α α E} {JB : Matrix β β E} (hB : IsHerm c JB) [IsEmpty α] [IsEmpty κ] (d : Darboux (symp c ξ JA JB) κ)
    {lam : Eˣ →* Circle} (hl : Continuous lam) : IsUWeilB c C ψ ξ JA JB d (lam.comp (h90 c)) (detOm lam JB _) := by
  refine ⟨isUSplitting_detOm hC ψ d hl, darbZero ξ JA (dbl JB) _, detOm lam _ _, fun _ _ => Subsingleton.elim _ _,
    ⟨isLagr_diagCols c JB, isUSplitting_detOm hC ψ _ hl, fun l _ _ p t hp φ _ => ?_⟩, fun g gd h φ₁ _ φ₂ _ => ?_⟩
  · have e : h90 c (GeneralLinearGroup.det t) = GeneralLinearGroup.det (p : GL (β ⊕ β) E) :=
      hilbertNinetyQuotientHom_eq_iff.mpr (det_siegel hB p t hp)
    simp [detOm_apply, e]
  · have e : GeneralLinearGroup.det (gd : GL (β ⊕ β) E) = GeneralLinearGroup.det (g : GL β E) := by
      ext; simp only [GeneralLinearGroup.val_det_apply, h, det_fromBlocks_zero₂₁, det_one, mul_one]
    funext x
    simp [detOm_apply, e, boxFun, mul_assoc]

end RankZero

theorem real_admissible_smul (κ : Type) [Fintype κ] (a : ℂ) : ∀ l ∈ realClass.adm κ, a • l ∈ realClass.adm κ :=
  fun _ ⟨T, hT⟩ => ⟨a • T, fun f => congrArg (a • ·) (hT f)⟩

theorem adelic_admissible_smul (F : Type) [Field F] [NumberField F] [LocallyCompactSpace (AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (a : ℂ) : ∀ l ∈ (adeleClass F).adm κ, a • l ∈ (adeleClass F).adm κ :=
  fun _ h g hg => (h g hg).elim fun T hT => ⟨a • T, fun f => congrArg (a • ·) (hT f)⟩

def argC : ℂˣ →* Circle where
  toFun z := ⟨z / ‖(z : ℂ)‖, by simp [Submonoid.unitSphere, z.ne_zero]⟩
  map_one' := Circle.ext (by simp)
  map_mul' z w := Circle.ext (by
    show ((z * w : ℂˣ) : ℂ) / ‖((z * w : ℂˣ) : ℂ)‖ = z / ‖(z : ℂ)‖ * (w / ‖(w : ℂ)‖)
    simp [mul_div_mul_comm])

theorem argC_apply (z : ℂˣ) : (argC z : ℂ) = z / ‖(z : ℂ)‖ := rfl

theorem continuous_argC : Continuous argC :=
  Continuous.subtype_mk (Units.continuous_val.div (Complex.continuous_ofReal.comp Units.continuous_val.norm)
    fun z => by simp) _

theorem argC_h90_conj_eq_sq (z : ℂˣ) : argC (h90 (Complex.conjAe : ℂ →ₐ[ℝ] ℂ) z) = argC z ^ 2 := by
  apply Circle.ext
  have h := Complex.mul_conj' (z : ℂ)
  have h1 : (starRingEnd ℂ) (z : ℂ) ≠ 0 := by simp
  have h2 : (‖(z : ℂ)‖ : ℂ) ≠ 0 := by simp
  simp [argC_apply, h90]
  field_simp
  linear_combination -h

theorem isUWeilB_complex [Invertible (2 : ℝ)] [IsModuleTopology ℝ ℂ] (ψ : AddChar ℝ ℂ) {β : Type} [Fintype β] [DecidableEq β]
    {JB : Matrix β β ℂ} (hB : IsHerm (Complex.conjAe : ℂ →ₐ[ℝ] ℂ) JB) (k : ℤ) :
    IsUWeilB (Complex.conjAe : ℂ →ₐ[ℝ] ℂ) realClass ψ Complex.I (1 : Matrix Empty Empty ℂ) JB (darbZero _ _ _ Empty)
      (argC ^ (2 * k)) (detOm (argC ^ k) JB _) := by
  have e : argC ^ (2 * k) = (argC ^ k).comp (h90 (Complex.conjAe : ℂ →ₐ[ℝ] ℂ)) := by
    ext1 z
    rw [MonoidHom.comp_apply, MonoidHom.zpow_apply, MonoidHom.zpow_apply, argC_h90_conj_eq_sq, _root_.zpow_mul, zpow_ofNat]
  rw [e]
  exact isUWeilB_rank_zero real_admissible_smul ψ hB _ (continuous_argC.zpow k)

theorem resEtaPow_argC : ResEtaPow (⊥ : Subgroup ℝˣ) argC 1 := by
  intro a
  have : a ∈ (⊥ : Subgroup ℝˣ) ⊔ (Units.map (Algebra.norm ℝ : ℂ →* ℝ)).range ↔ 0 < (a : ℝ) := by
    rw [bot_sup_eq]
    constructor
    · rintro ⟨z, rfl⟩
      simp [Algebra.norm_complex_apply, Complex.normSq_pos]
    · intro h
      refine ⟨Units.mk0 (√a : ℝ) (by simp [Real.sqrt_ne_zero', h]), Units.ext ?_⟩
      simp [Algebra.norm_complex_apply, h.le]
  rw [this]
  have h0 : ((a : ℝ) : ℂ) ≠ 0 := by simp
  split_ifs with h
  · simp [argC_apply, abs_of_pos h]
  · simp [argC_apply, abs_of_nonpos (not_lt.mp h)]

open scoped Pointwise in

theorem real_modu (a : ℝˣ) : (realClass.modu a : ℝ) = |(a : ℝ)| := by
  show ((distribHaarChar ℝ a : ℝ≥0) : ℝ) = _
  rw [distribHaarChar_eq_of_measure_smul_eq_mul (μ := volume) (s := Set.Icc (0 : ℝ) 1) (r := ‖(a : ℝ)‖₊) (by simp) (by simp)
    (by
      rw [show a • Set.Icc (0 : ℝ) 1 = (a : ℝ) • Set.Icc (0 : ℝ) 1 from rfl, Measure.addHaar_smul]
      simp [← Real.enorm_eq_ofReal_abs, enorm_eq_nnnorm])]
  rfl

theorem isUWeilB_adele (F : Type) [Field F] [NumberField F] :
    ∃ (_ : LocallyCompactSpace (AdeleRing (𝓞 F) F)) (_ : Invertible (2 : AdeleRing (𝓞 F) F)),
      IsQuad (swapA (AdeleRing (𝓞 F) F)) (1, -1) ∧ ∀ (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
      (lam : (AdeleRing (𝓞 F) F × AdeleRing (𝓞 F) F)ˣ →* Circle), Continuous lam →
      IsUWeilB (swapA (AdeleRing (𝓞 F) F)) (adeleClass F) ψ (1, -1) (1 : Matrix Empty Empty _) (1 : Matrix Unit Unit _)
        (darbZero _ _ _ Empty) (lam.comp (h90 (swapA _))) (detOm lam _ _) := by
  have hL := AdelicUnitaryTop.locallyCompact_adele (F := F)
  have h2 : IsUnit (2 : AdeleRing (𝓞 F) F) := by
    simpa [map_ofNat] using (Ne.isUnit (two_ne_zero : (2 : F) ≠ 0)).map (algebraMap F (AdeleRing (𝓞 F) F))
  let _ := h2.invertible
  exact ⟨hL, inferInstance, isQuad_split, fun ψ lam hl =>
    isUWeilB_rank_zero (adelic_admissible_smul F) ψ ⟨fun i j => by simp, by simp⟩ _ hl⟩

theorem split_char_unique {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Invertible (2 : F)] {α κ : Type} [Fintype α] [DecidableEq α] [Fintype κ] (ψ : AddChar F ℂ) (hψ : Continuous ψ)
    (hψ1 : ψ ≠ 1) {JA : Matrix α α (F × F)} {JB : Matrix Unit Unit (F × F)} (hA : IsHerm (swapA F) JA)
    (hB : IsHerm (swapA F) JB) (σ : κ ≃ α × Unit) (χ χ' : (F × F)ˣ →* Circle) (hc : Continuous χ)
    (hχ : ResEtaPow (⊥ : Subgroup Fˣ) χ (Fintype.card α)) :
    IsUWeilSplit (swapA F) (sbClass F) ψ (1, -1) JA (dbl JB) (splitDarboux hA hB.dbl (dblNum σ)) χ' (diagCols Unit)
      (splitOm (distribHaarChar F) χ (dbl JB) (dblNum σ)) ↔ χ' = χ :=
  ⟨fun h => siegel_char_unique (hasDiagForm_sb F κ) isQuad_split (isDblCoord_split hA hB σ) h.2.2
    (isUWeilSplit_split ψ hψ hψ1 hA hB σ χ hc hχ).2.2, fun h => h ▸ isUWeilSplit_split ψ hψ hψ1 hA hB σ χ hc hχ⟩

end GlobalTheory.WeilM.SiegelModel
end
