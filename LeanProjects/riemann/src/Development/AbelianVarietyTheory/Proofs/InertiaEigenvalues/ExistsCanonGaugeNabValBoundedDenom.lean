import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.SigCancel
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CanonGaugeDmonOfHLIntegral
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BilinPartCanonGaugeCongr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsSymmBalancedCongrOfSeparability
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsSepDiscr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BilinearLogFormEvalZeroRightEqZero

set_option autoImplicit false

noncomputable section

open MvPowerSeries NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory.QuadDeriv GlobalTheory.GaugeInt

namespace GlobalTheory.GaugeBoundedDenom

theorem exists_symm_balanced {k : Type} [CommRing k] [Algebra ℚ k] (S : Subring k) (E : Type) [Field E]
    [NumberField E] [StarRing (𝓞 E)] {d : ℕ} (A : 𝓞 E →+* Matrix (Fin d) (Fin d) k)
    (hA : ∀ a i j, A a i j ∈ S) (β : Matrix (Fin d) (Fin d) k) (hsym : ∀ i j, (βᵀ - β) i j ∈ S)
    (hbal : ∀ a i j, ((A a)ᵀ * β - β * A (star a)) i j ∈ S) :
    ∃ β' : Matrix (Fin d) (Fin d) k, β'ᵀ = β' ∧ (∀ a, (A a)ᵀ * β' = β' * A (star a)) ∧
      ∀ i j, ((2 * discr E : ℤ) : k) * (β - β') i j ∈ S := by
  obtain ⟨x, y, h1, hc⟩ := GlobalTheory.IntSepElement.exists_sep_discr E
  obtain ⟨u, hu⟩ : ∃ u : k, ((2 * discr E : ℤ) : k) * u = 1 := by
    refine ⟨algebraMap ℚ k (((2 * discr E : ℤ) : ℚ)⁻¹), ?_⟩
    rw [← map_intCast (algebraMap ℚ k), ← map_mul, mul_inv_cancel₀, map_one]
    exact_mod_cast mul_ne_zero two_ne_zero (discr_ne_zero E)
  obtain ⟨g, hg⟩ := GlobalTheory.exists_addHom_tensor_int_of_biadditive
    (fun a b : 𝓞 E => (A a)ᵀ * β * A (star b))
    (fun m m' n => by simp only [map_add, transpose_add, Matrix.add_mul])
    (fun m n n' => by simp only [star_add, map_add, Matrix.mul_add])
  have hT : ∀ a b : 𝓞 E, (A (a * b))ᵀ = (A a)ᵀ * (A b)ᵀ := fun a b => by
    rw [mul_comm a b, map_mul, transpose_mul]
  set γ : Matrix (Fin d) (Fin d) k := ∑ i, (A (x i))ᵀ * β * A (star (y i)) with hγ
  have hγbal : ∀ a, (A a)ᵀ * γ = γ * A (star a) := fun a => by
    have := congrArg g (hc a)
    simp only [map_sum, hg] at this
    rw [hγ, Finset.mul_sum, Finset.sum_mul]
    convert this using 2 with i _ i _
    · rw [hT]; simp only [Matrix.mul_assoc]
    · rw [star_mul, map_mul]; simp only [Matrix.mul_assoc]
  have hβ : ((discr E : ℤ) : k) • β = ∑ i, (A (x i))ᵀ * ((A (y i))ᵀ * β) := by
    have := congrArg (fun a => (A a)ᵀ * β) h1
    simp only [map_sum, transpose_sum, Finset.sum_mul, hT, Matrix.mul_assoc, map_intCast,
      transpose_intCast] at this
    rw [this, Int.cast_smul_eq_zsmul, zsmul_eq_mul]
  have hdiff : ∀ i j, (((discr E : ℤ) : k) • β - γ) i j ∈ S := fun i j => by
    have e : ((discr E : ℤ) : k) • β - γ =
        ∑ l, (A (x l))ᵀ * ((A (y l))ᵀ * β - β * A (star (y l))) := by
      rw [hβ, hγ, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Matrix.mul_sub, Matrix.mul_assoc]
    rw [e, Matrix.sum_apply]
    refine Subring.sum_mem _ fun l _ => ?_
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun m _ => Subring.mul_mem _ (hA _ _ _) (hbal _ _ _)
  refine ⟨u • (γ + γᵀ), ?_, fun a => ?_, fun i j => ?_⟩
  · rw [transpose_smul, transpose_add, transpose_transpose, add_comm]
  · have h := congrArg transpose (hγbal (star a))
    rw [transpose_mul, transpose_mul, transpose_transpose, star_star] at h
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, hγbal, h]
  · have h := sub_mem (add_mem (hdiff i j) (hdiff j i)) (mul_mem (intCast_mem S (discr E)) (hsym i j))
    convert h using 1
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, transpose_apply, smul_eq_mul]
    rw [mul_sub, ← mul_assoc, hu]
    push_cast
    ring

section Ring

variable {R k : Type} [CommRing R] [CommRing k] [Algebra ℚ k] {φ : R →+* k} {d : ℕ}

theorem pow_mul_const_dmonOf_mem {F : Pt k 2 d} (iF : IP φ F) {ι : Type} [Fintype ι] (U : ι → Fin d → k)
    (hu : ∀ l i, U l i ∈ φ.range) (δ : k) (hδ : δ ∈ φ.range) (q : PS k 1 d) (q0 : constantCoeff q = 0)
    (q1 : ∀ l, constantCoeff (Dof F (U l) q) = 0)
    (q2 : ∀ l l', C δ * Dof F (U l) (Dof F (U l') q) ∈ IntS φ 1 d) (m : ℕ) (f : PS k 1 d)
    (hf : f ∈ IntS φ 1 d) (α : ι →₀ ℕ) :
    δ ^ α.degree * constantCoeff (DmonOf F U α (f * FB.expS k ((m : k) • q))) ∈ φ.range := by
  let M : Subring (PS k 1 d) :=
    Subring.closure ((IntS φ 1 d : Set (PS k 1 d)) ∪ Set.range fun l => C δ * Dof F (U l) q)
  have hI : ∀ g ∈ IntS φ 1 d, g ∈ M := fun g hg => Subring.subset_closure (Or.inl hg)
  have hp : ∀ l, C δ * Dof F (U l) q ∈ M := fun l => Subring.subset_closure (Or.inr ⟨l, rfl⟩)
  have hc : ∀ g ∈ M, constantCoeff g ∈ φ.range := by
    intro g hg
    have : M ≤ φ.range.comap (constantCoeff (σ := Fin 1 × Fin d) (R := k)) := by
      refine Subring.closure_le.2 ?_
      rintro x (hx | ⟨l, rfl⟩)
      · exact int_const hx
      · show constantCoeff (C δ * Dof F (U l) q) ∈ φ.range
        rw [map_mul, q1, mul_zero]
        exact zero_mem _
    exact this hg
  have hD : ∀ l, ∀ g ∈ M, C δ * Dof F (U l) g ∈ M := by
    intro l g hg
    induction hg using Subring.closure_induction with
    | mem x hx =>
      rcases hx with hx | ⟨l', rfl⟩
      · exact hI _ (mul_mem (int_C hδ) (dof_int iF (hu l) hx))
      · rw [GE.dof_C_mul]
        exact hI _ (mul_mem (int_C hδ) (q2 l l'))
    | zero => simp [Dof]
    | one => simp [Dof]
    | add x y _ _ hx hy => rw [GE.dof_add, mul_add]; exact add_mem hx hy
    | neg x _ hx => rw [← GE.dofD_apply, map_neg, GE.dofD_apply, mul_neg]; exact neg_mem hx
    | mul x y h1 h2 hx hy =>
      have := add_mem (mul_mem hx h2) (mul_mem h1 hy)
      convert this using 1
      rw [GE.dof_mul]
      ring
  have hmq : constantCoeff ((m : k) • q) = 0 := by rw [smul_eq_C_mul, map_mul, q0, mul_zero]
  let P : ℕ → PS k 1 d → Prop := fun n x => ∃ g ∈ M, C δ ^ n * x = g * FB.expS k ((m : k) • q)
  have step : ∀ l n x, P n x → P (n + 1) (Dof F (U l) x) := by
    rintro l n x ⟨g, hg, e⟩
    refine ⟨C δ * Dof F (U l) g + g * (m : PS k 1 d) * (C δ * Dof F (U l) q),
      add_mem (hD l g hg) (mul_mem (mul_mem hg (natCast_mem M m)) (hp l)), ?_⟩
    have e' := congrArg (Dof F (U l)) e
    rw [← map_pow, GE.dof_C_mul, GE.dof_mul, Nab.dof_expS F _ hmq] at e'
    have e2 : Dof F (U l) ((m : k) • q) = (m : PS k 1 d) * Dof F (U l) q := by
      rw [smul_eq_C_mul, GE.dof_C_mul, map_natCast]
    rw [e2, map_pow] at e'
    rw [pow_succ', mul_assoc, e']
    ring
  have iter : ∀ l (j : ℕ) n x, P n x → P (j + n) ((Dof F (U l))^[j] x) := by
    intro l j n x hx
    induction j with
    | zero => simpa using hx
    | succ j ih =>
      rw [Function.iterate_succ_apply', add_right_comm]
      exact step l _ _ ih
  have fold : ∀ L : List ι, P (L.map α).sum
      (L.foldr (fun l g => (Dof F (U l))^[α l] g) (f * FB.expS k ((m : k) • q))) := by
    intro L
    induction L with
    | nil => exact ⟨f, hI f hf, by simp⟩
    | cons a L ih => exact iter a _ _ _ ih
  obtain ⟨g, hg, e⟩ := fold (Finset.univ : Finset ι).toList
  have e' := congrArg constantCoeff e
  have hE : constantCoeff (FB.expS k ((m : k) • q)) = 1 := by
    unfold FB.expS
    rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hmq),
      finsum_eq_single _ 0]
    · simp
    · intro j hj
      rw [map_pow, hmq, zero_pow hj, smul_zero]
  rw [map_mul, map_mul, map_pow, constantCoeff_C, Finset.sum_map_toList, hE, mul_one] at e'
  rw [Finsupp.degree_eq_sum, DmonOf, e']
  exact hc g hg

end Ring

theorem dpolyOf_monomial_one {k : Type} [CommRing k] {d : ℕ} (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι]
    (u : ι → Fin d → k) (mo : ι →₀ ℕ) (g : PS k 1 d) :
    DpolyOf F u (MvPolynomial.monomial mo (1 : k)) g = DmonOf F u mo g := by
  classical
  have e : DpolyOf F u (MvPolynomial.monomial mo (1 : k)) g =
      ∑ m ∈ ({mo} : Finset (ι →₀ ℕ)), C ((MvPolynomial.monomial mo (1 : k)).coeff m) * DmonOf F u m g := by
    unfold DpolyOf
    refine Finset.sum_subset MvPolynomial.support_monomial_subset fun x _ hx => ?_
    rw [MvPolynomial.notMem_support_iff.1 hx, map_zero, zero_mul]
  rw [e, Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl, map_one, one_mul]

theorem pow_mul_nabVal_mem {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (k : Type)
    [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (g : PS k 2 d) (hg : B.IsCanonGauge k g) (δ : k)
    (hδ : δ ∈ (algebraMap R k).range) (hβ : ∀ i j, δ * bilinPart k g i j ∈ (algebraMap R k).range)
    (w0 : O) (m : ℕ) (f : PS R 1 d) (ι : Type) [Fintype ι] (u : ι → Fin d → R) (α : ι →₀ ℕ) :
    δ ^ α.degree * B.nabVal k g w0 m (FB.toK k f) (fun l i => algebraMap R k (u l i))
      (MvPolynomial.monomial α 1) ∈ (algebraMap R k).range := by
  have iF : IP (algebraMap R k) (B.FK k) := ⟨B.G.F, B.G.const, rfl⟩
  have iw : IP (algebraMap R k) (B.actK k w0) := ⟨B.A.act w0, B.A.const w0, rfl⟩
  have hF := iF.gp
  have hw := iw.gp
  have hU : evP (n := 1) ![pt k d 0, 0] (B.FK k) = pt k d 0 := by
    have := congrArg (mapP (algebraMap R k)) (unit_right B.G)
    rw [baseChange_addOf _ _ _ _ (gp_pt 0) gp_zero₂, baseChange_pt,
      show mapP (algebraMap R k) (0 : Pt R 1 d) = 0 from funext fun i => map_zero _] at this
    exact this
  have hom : comp1 (B.actK k w0) (B.FK k) = addOf (B.FK k) (comp1 (B.actK k w0) (pt k (n := 2) d 0))
      (comp1 (B.actK k w0) (pt k (n := 2) d 1)) := by
    have := congrArg (mapP (algebraMap R k)) (B.A.hom w0)
    rw [FGLaw.add, FGLaw.add, addOf_pt, baseChange_comp1 _ _ _ B.G.const,
      baseChange_addOf _ _ _ _ (gp_comp1 _ _ (B.A.const w0) (gp_pt 0))
        (gp_comp1 _ _ (B.A.const w0) (gp_pt 1)),
      baseChange_comp1 _ _ _ (gp_pt 0), baseChange_comp1 _ _ _ (gp_pt 1), baseChange_pt, baseChange_pt] at this
    exact this
  have c0 : constantCoeff g = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact coeff_eq_zero_of_axes g hg.ax0 hg.ax1 0 (by simp)
  have c1 : ∀ s, constantCoeff (pderiv k s g) = 0 := fun s => by
    rw [const_pderiv]
    exact coeff_eq_zero_of_axes g hg.ax0 hg.ax1 _ (by simp)
  have hp : ∀ j : Fin 3, GP (pt k d j) := gp_pt
  have hl : DI (algebraMap R k) (defL (B.FK k) g) := by
    refine di_of_exp B.ph1 ?_ _ ?_ hg.ph1
    · rw [← gt_const_ev_eq _ (triple_points_zero_constant (n := 2) gp_zero₂ (gp_pt 0) (gp_pt 1)), B.cocycleLeft_zero_fst, map_one]
    · rw [defL, map_sub, map_add, gt_const_ev _ (pair_points_zero_constant (hp _) (hp _)) _ c0,
        gt_const_ev _ (pair_points_zero_constant (hp _) (hp _)) _ c0,
        gt_const_ev _ (pair_points_zero_constant (gp_addOf _ hF _ _ (hp _) (hp _)) (hp _)) _ c0]
      simp
  have hr : DI (algebraMap R k) (defR (B.FK k) g) := by
    refine di_of_exp B.ph2 ?_ _ ?_ hg.ph2
    · rw [← gt_const_ev_eq _ (triple_points_zero_constant (n := 2) gp_zero₂ (gp_pt 0) (gp_pt 1)), B.cocycleRight_zero_fst, map_one]
    · rw [defR, map_sub, map_add, gt_const_ev _ (pair_points_zero_constant (hp _) (hp _)) _ c0,
        gt_const_ev _ (pair_points_zero_constant (hp _) (hp _)) _ c0,
        gt_const_ev _ (pair_points_zero_constant (hp _) (gp_addOf _ hF _ _ (hp _) (hp _))) _ c0]
      simp
  have hu : ∀ l i, algebraMap R k (u l i) ∈ (algebraMap R k).range := fun l i => ⟨u l i, rfl⟩
  have hq : B.hL k g w0 = ev (n := 1) ![pt k d 0, B.actK k w0] g := by
    rw [FB.hL, gt_comp1_pt_right]
  have hW : ∀ l j, coeff (Finsupp.single ((0 : Fin 1), l) 1) (B.actK k w0 j) ∈ (algebraMap R k).range :=
    fun l j => ⟨coeff (Finsupp.single ((0 : Fin 1), l) 1) (B.A.act w0 j), by simp only [FB.actK, coeff_map]⟩
  rw [FB.nabVal, dpolyOf_monomial_one, hq]
  refine pow_mul_const_dmonOf_mem iF _ hu δ hδ _ (gt_const_ev _ (pair_points_zero_constant (gp_pt 0) hw) _ c0)
    (fun l => ?_) (fun l l' => ?_) m _ ⟨f, rfl⟩ α
  · rw [Dof]
    simp only [map_sum, map_mul, constantCoeff_pderiv_formalSubst_two _ _ (gp_pt 0) hw, c1, zero_mul,
      Finset.sum_const_zero, add_zero, mul_zero]
  · have h := mul_mem (int_C (n := 1) (d := d) hδ) (quad_int iF hU iw hom g c1 hl hr (hu l) (hu l'))
    rw [mul_sub, ← map_mul] at h
    have h' := add_mem h (int_C (n := 1) (d := d) (add_mem
      (sum_mem (t := Finset.univ) fun j _ => mul_mem
        (sum_mem (t := Finset.univ) fun a _ => mul_mem (hu l' a) (hW a j))
        (sum_mem (t := Finset.univ) fun i _ => mul_mem (hu l i) (hβ i j)))
      (sum_mem (t := Finset.univ) fun i _ => mul_mem (hu l' i)
        (sum_mem (t := Finset.univ) fun a _ => mul_mem (hu l a)
          (sum_mem (t := Finset.univ) fun j _ => mul_mem (hβ i j) (hW a j))))))
    convert h' using 1
    rw [sub_add_eq_add_sub, eq_sub_iff_add_eq]
    congr 2
    simp only [bilinPart, mul_add, Finset.mul_sum, Finset.sum_mul]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun l _ => by ring
    · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun l _ => by ring

theorem exists_canonGauge_nabVal_bounded_denom :
    ∀ (V k : Type) [CommRing V] [CommRing k] [Algebra ℚ k] [Algebra V k] (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (d : ℕ) (B : FB V d (𝓞 E)) (h : PS k 2 d), B.IsCanonGauge k h → ∃ h' : PS k 2 d, B.IsCanonGauge k h' ∧ ∀ (w0 : 𝓞 E) (m : ℕ) (f : PS V 1 d) (ι : Type) [Fintype ι] (u : ι → Fin d → V) (α : ι →₀ ℕ), ((2 * NumberField.discr E : ℤ) : k) ^ α.degree * B.nabVal k h' w0 m (FB.toK k f) (fun l i => algebraMap V k (u l i)) (MvPolynomial.monomial α 1) ∈ (algebraMap V k).range := by
  intro V k _ _ _ _ E _ _ _ d B h hc
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := GlobalTheory.bilinPart_canonGauge_congr V d (𝓞 E) k B h hc
  let A : 𝓞 E →+* Matrix (Fin d) (Fin d) k :=
    { toFun := dAct k B
      map_one' := c4
      map_mul' := c6
      map_add' := c5
      map_zero' := by
        have e := c5 0 0
        rw [add_zero] at e
        exact left_eq_add.1 e }
  obtain ⟨β, b1, b2, b3⟩ := exists_symm_balanced (algebraMap V k).range E A c3 (bilinPart k h) c1 c2
  obtain ⟨h', hc', e⟩ := GlobalTheory.GaugeShift.canon_sub_bilin V d (𝓞 E) k B h hc β b1 b2
  exact ⟨h', hc', fun w0 m f ι _ u α =>
    pow_mul_nabVal_mem k B h' hc' _ (intCast_mem _ _) (e ▸ b3) w0 m f ι u α⟩

end GlobalTheory.GaugeBoundedDenom
