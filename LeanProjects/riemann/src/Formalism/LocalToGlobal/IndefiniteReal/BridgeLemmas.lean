import Formalism.LocalToGlobal.IndefiniteReal.Bridge

open NumberField

noncomputable section

namespace Formalism.IndefR.Bridge

open Formalism.L2.DIV

section Avg

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def clsAvg (S : CSD K) (c : S.Cl) (x : S.V) : S.V := ((S.wt c : K))⁻¹ • ∑ g : S.Gam c, S.ρ c g x

theorem clsAvg_fixed (S : CSD K) (c : S.Cl) (x : S.V) (g : S.Gam c) : S.ρ c g (clsAvg S c x) = clsAvg S c x := by
  unfold clsAvg
  rw [map_smul, map_sum]
  congr 1
  have hm : ∀ g' : S.Gam c, S.ρ c g (S.ρ c g' x) = S.ρ c (g * g') x := by
    intro g'
    rw [map_mul]
    rfl
  simp_rw [hm]
  exact Equiv.sum_comp (Equiv.mulLeft g) (fun g' => S.ρ c g' x)

open Classical in

def clsSingle (S : CSD K) (c : S.Cl) (x : S.V) : S.Forms :=
  ⟨Pi.single c (clsAvg S c x), by
    intro c' g
    by_cases h : c' = c
    · subst h
      simp [clsAvg_fixed]
    · simp [h]⟩

end Avg

namespace ClassPres

variable {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G}
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
  (P : ClassPres ι S σ ρ J χ)

private theorem eq_decG_mul_y_decC_mul_decK (h : G) : h = ι (P.decG h) * P.y (P.decC h) * (P.decK h : G) :=
  (P.reps h).exists.choose_spec.choose_spec.choose_spec

theorem decC_eq (γ : Γ) (c : S.Cl) (k : J) : P.decC (ι γ * P.y c * k) = c := by
  exact (P.reps (ι γ * P.y c * k)).unique (P.reps (ι γ * P.y c * k)).exists.choose_spec ⟨γ, k, rfl⟩

theorem coef_fixed (f : S.Forms) (c : S.Cl) (δ : stab ι J (P.y c)) :
    (χ (stabK ι δ) : ℂ) • ρ (δ : Γ) (P.coef ((f : S.Cl → S.V) c)) = P.coef ((f : S.Cl → S.V) c) := by
  have hf : ∀ c (g : S.Gam c), S.ρ c g ((f : S.Cl → S.V) c) = (f : S.Cl → S.V) c := f.2
  have h1 := P.coef_act c ((P.stabI c).symm δ) ((f : S.Cl → S.V) c)
  rw [MulEquiv.apply_symm_apply, hf c] at h1
  exact h1.symm

private theorem coef_smul_eq_of_double_coset_eq (f : S.Forms) (γ γ' : Γ) (c : S.Cl) (k k' : J)
    (hs : ι γ * P.y c * (k : G) = ι γ' * P.y c * (k' : G)) :
    (χ k' : ℂ) • ρ γ' (P.coef ((f : S.Cl → S.V) c)) = (χ k : ℂ) • ρ γ (P.coef ((f : S.Cl → S.V) c)) := by
  have e2 : (P.y c)⁻¹ * ι (γ'⁻¹ * γ) * P.y c = (k' : G) * (k : G)⁻¹ := by
    rw [map_mul, map_inv]
    calc (P.y c)⁻¹ * ((ι γ')⁻¹ * ι γ) * P.y c
        = (P.y c)⁻¹ * (ι γ')⁻¹ * (ι γ * P.y c * (k : G)) * (k : G)⁻¹ := by group
      _ = (P.y c)⁻¹ * (ι γ')⁻¹ * (ι γ' * P.y c * (k' : G)) * (k : G)⁻¹ := by rw [hs]
      _ = (k' : G) * (k : G)⁻¹ := by group
  have hmem : γ'⁻¹ * γ ∈ stab ι J (P.y c) := by
    rw [mem_stab, e2]
    exact J.mul_mem k'.2 (J.inv_mem k.2)
  have hK : stabK ι (⟨γ'⁻¹ * γ, hmem⟩ : stab ι J (P.y c)) = k * k'⁻¹ := by
    apply Subtype.ext
    show ((P.y c)⁻¹ * ι (γ'⁻¹ * γ) * P.y c)⁻¹ = ((k * k'⁻¹ : J) : G)
    rw [e2]
    simp
  have hfix : (χ (k * k'⁻¹) : ℂ) • ρ (γ'⁻¹ * γ) (P.coef ((f : S.Cl → S.V) c)) =
      P.coef ((f : S.Cl → S.V) c) := by
    have h1 := P.coef_fixed f c ⟨γ'⁻¹ * γ, hmem⟩
    rw [hK] at h1
    exact h1
  have hχ : χ k' * χ (k * k'⁻¹) = χ k := by
    rw [map_mul, map_inv, mul_comm (χ k), mul_inv_cancel_left]
  conv_lhs => rw [← hfix]
  rw [map_smul, smul_smul, ← Units.val_mul, hχ]
  congr 1
  show (ρ γ' * ρ (γ'⁻¹ * γ)) (P.coef _) = _
  rw [← map_mul, mul_inv_cancel_left]

theorem ext_eq (f : S.Forms) (γ : Γ) (c : S.Cl) (k : J) :
    P.ext f (ι γ * P.y c * k) = (χ k : ℂ) • ρ γ (P.coef ((f : S.Cl → S.V) c)) := by
  have hc := P.decC_eq γ c k
  have hs := eq_decG_mul_y_decC_mul_decK P (ι γ * P.y c * k)
  unfold ClassPres.ext
  rw [hc] at hs ⊢
  exact coef_smul_eq_of_double_coset_eq P f γ _ c k _ hs

theorem extMem_holds (P : ClassPres ι S σ ρ J χ) : P.ExtMem := by
  unfold ClassPres.ExtMem
  intro f
  show ∀ (γ : Γ) (h : G) (k : J), P.ext f (ι γ * h * k) = (χ k : ℂ) • ρ γ (P.ext f h)
  intro γ h k
  obtain ⟨c, ⟨γ0, k0, rfl⟩, -⟩ := P.reps h
  have e1 : ι γ * (ι γ0 * P.y c * (k0 : G)) * (k : G) = ι (γ * γ0) * P.y c * ((k0 * k : J) : G) := by
    rw [map_mul ι, Subgroup.coe_mul]
    simp only [mul_assoc]
  rw [e1, P.ext_eq f (γ * γ0) c (k0 * k), P.ext_eq f γ0 c k0, map_smul, smul_smul, map_mul χ, map_mul ρ,
    Units.val_mul, mul_comm ((χ k0 : ℂ))]
  rfl

theorem card_stab (c : S.Cl) : Nat.card (stab ι J (P.y c)) = S.wt c := by
  rw [Nat.card_congr (P.stabI c).toEquiv.symm, Nat.card_eq_fintype_card]
  rfl

theorem ext_rep (f : S.Forms) (c : S.Cl) : P.ext f (P.y c) = P.coef ((f : S.Cl → S.V) c) := by
  simpa using P.ext_eq f 1 c 1

theorem sigma_csum (f f' : S.Forms) :
    σ (S.csum f f') = ∑ c, ((S.wt c : ℂ))⁻¹ *
      inner ℂ (P.coef ((f : S.Cl → S.V) c)) (P.coef ((f' : S.Cl → S.V) c)) := by
  simp only [CSD.csum, map_sum, map_mul, map_inv₀, map_natCast, P.coef_pair]

theorem isom_holds (P : ClassPres ι S σ ρ J χ) : P.Isom := by
  unfold ClassPres.Isom
  intro f f'
  rw [P.sigma_csum f f']
  unfold adInner
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [P.card_stab c, P.ext_rep f c, P.ext_rep f' c]

theorem coef_inj {x : S.V} (hx : P.coef x = 0) : x = 0 := by
  have h1 : ∑ i, σ (S.bV.repr x i) • P.coef (S.bV i) = 0 := by
    rw [← hx]
    conv_rhs => rw [← S.bV.sum_repr x]
    rw [map_sum]
    simp only [map_smulₛₗ]
  have h2 := Fintype.linearIndependent_iff.1 P.coef_li _ h1
  apply S.bV.repr.injective
  ext i
  simpa using h2 i

private theorem re_natCast_inv_mul' (n : ℕ) (z : ℂ) : (((n : ℂ))⁻¹ * z).re = ((n : ℝ))⁻¹ * z.re := by
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul]

private theorem inner_self_re_eq_norm_sq (x : W) : (inner ℂ x x).re = ‖x‖ ^ 2 :=
  inner_self_eq_norm_sq (𝕜 := ℂ) x

theorem eq_zero_of_wsum {w : S.Cl → W}
    (h : ∑ c, ((S.wt c : ℂ))⁻¹ * inner ℂ (w c) (w c) = 0) (c : S.Cl) : w c = 0 := by
  have hr := congrArg Complex.re h
  rw [Complex.re_sum, Complex.zero_re] at hr
  simp only [re_natCast_inv_mul', inner_self_re_eq_norm_sq] at hr
  have hnn : ∀ c ∈ Finset.univ, 0 ≤ ((S.wt c : ℝ))⁻¹ * ‖w c‖ ^ 2 := fun c _ => by positivity
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hr c (Finset.mem_univ c)
  have hw : (S.wt c : ℝ) ≠ 0 := by
    have hpos : 0 < S.wt c := Fintype.card_pos
    exact_mod_cast hpos.ne'
  rcases mul_eq_zero.1 h0 with h1 | h1
  · exact absurd (inv_eq_zero.1 h1) hw
  · simpa using h1

theorem mulVec_eq (a : Fin S.dim → ℂ) (j : Fin S.dim) :
    ((S.H.map σ).mulVec a) j = ∑ c, ((S.wt c : ℂ))⁻¹ * inner ℂ (P.coef ((S.basis j : S.Cl → S.V) c))
      (∑ i, a i • P.coef ((S.basis i : S.Cl → S.V) c)) := by
  show ∑ i, σ (S.H j i) * a i = _
  simp only [CSD.H, Matrix.of_apply, P.sigma_csum, inner_sum, inner_smul_right, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem comb_zero_of_mulVec (a : Fin S.dim → ℂ) (h : (S.H.map σ).mulVec a = 0) (c : S.Cl) :
    ∑ i, a i • P.coef ((S.basis i : S.Cl → S.V) c) = 0 := by
  have key : ∑ c', ((S.wt c' : ℂ))⁻¹ * inner ℂ (∑ i, a i • P.coef ((S.basis i : S.Cl → S.V) c'))
      (∑ i, a i • P.coef ((S.basis i : S.Cl → S.V) c')) = 0 := by
    have h0 : ∑ j, starRingEnd ℂ (a j) * ((S.H.map σ).mulVec a) j = 0 := by simp [h]
    rw [← h0]
    simp only [P.mulVec_eq, sum_inner, inner_smul_left, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c' _ => ?_
    ring
  exact eq_zero_of_wsum key c

theorem det_ne (P : ClassPres ι S σ ρ J χ) : (S.H.map σ).det ≠ 0 := by
  have hH : S.H.det ≠ 0 := by
    intro hdet
    obtain ⟨v, hv, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    apply hv
    have hmulσ : (S.H.map σ).mulVec (fun i => σ (v i)) = 0 := by
      funext j
      have h3 : σ ((S.H.mulVec v) j) = ((S.H.map σ).mulVec (fun i => σ (v i))) j := by
        show σ (∑ i, S.H j i * v i) = ∑ i, σ (S.H j i) * σ (v i)
        rw [map_sum]
        simp only [map_mul]
      rw [← h3, congrFun hmul j]
      simp
    have hc := P.comb_zero_of_mulVec (fun i => σ (v i)) hmulσ
    have hzero : ∑ i, v i • S.basis i = 0 := by
      apply Subtype.ext
      funext c
      show ((∑ i, v i • S.basis i : S.Forms) : S.Cl → S.V) c = 0
      apply P.coef_inj
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, map_sum, map_smulₛₗ]
      exact hc c
    funext i
    exact Fintype.linearIndependent_iff.1 S.basis.linearIndependent v hzero i
  have e : (S.H.map σ).det = σ S.H.det := (RingHom.map_det σ S.H).symm
  rw [e]
  exact (map_ne_zero σ).2 hH

theorem linInd (P : ClassPres ι S σ ρ J χ) : LinearIndependent ℂ (fun i => P.extL (S.basis i)) := by
  have hL : ∀ f : S.Forms, P.extL f = P.ext f := fun f => rfl
  rw [Fintype.linearIndependent_iff]
  intro a ha
  have hc : ∀ c, ∑ i, a i • P.coef ((S.basis i : S.Cl → S.V) c) = 0 := by
    intro c
    have h1 := congrFun ha (P.y c)
    simpa [Finset.sum_apply, Pi.smul_apply, hL, P.ext_rep] using h1
  have hmul : (S.H.map σ).mulVec a = 0 := by
    funext j
    rw [P.mulVec_eq]
    simp [hc]
  intro i
  by_contra hi
  exact P.det_ne (Matrix.exists_mulVec_eq_zero_iff.1 ⟨a, fun h0 => hi (by simp [h0]), hmul⟩)

theorem coef_avg (c : S.Cl) (x : S.V) :
    P.coef (clsAvg S c x) = ((S.wt c : ℂ))⁻¹ •
      ∑ g : S.Gam c, (χ (stabK ι (P.stabI c g)) : ℂ) • ρ (P.stabI c g : Γ) (P.coef x) := by
  simp only [clsAvg, map_smulₛₗ, map_inv₀, map_natCast, map_sum, P.coef_act]

theorem adForms_fixed {F : G → W} (hF : F ∈ AdForms ι ρ J χ) (c : S.Cl) (g : S.Gam c) :
    (χ (stabK ι (P.stabI c g)) : ℂ) • ρ (P.stabI c g : Γ) (F (P.y c)) = F (P.y c) := by
  have hm : ∀ (γ : Γ) (h : G) (k : J), F (ι γ * h * k) = (χ k : ℂ) • ρ γ (F h) := hF
  have e : ∀ δ : stab ι J (P.y c), ι (δ : Γ) * P.y c * ((stabK ι δ : J) : G) = P.y c := by
    intro δ
    show ι (δ : Γ) * P.y c * ((P.y c)⁻¹ * ι (δ : Γ) * P.y c)⁻¹ = P.y c
    group
  rw [← hm, e]

theorem adForms_val {F : G → W} (hF : F ∈ AdForms ι ρ J χ) (h : G) :
    F h = (χ (P.decK h) : ℂ) • ρ (P.decG h) (F (P.y (P.decC h))) := by
  have hm : ∀ (γ : Γ) (h : G) (k : J), F (ι γ * h * k) = (χ k : ℂ) • ρ γ (F h) := hF
  conv_lhs => rw [eq_decG_mul_y_decC_mul_decK P h]
  exact hm _ _ _

theorem adForms_ext {F F' : G → W} (hF : F ∈ AdForms ι ρ J χ) (hF' : F' ∈ AdForms ι ρ J χ)
    (h : ∀ c, F (P.y c) = F' (P.y c)) : F = F' := by
  funext x
  rw [P.adForms_val hF x, P.adForms_val hF' x, h]

theorem span_eq (P : ClassPres ι S σ ρ J χ) : Submodule.span ℂ (Set.range P.extL) = AdForms ι ρ J χ := by
  have hL : ∀ f : S.Forms, P.extL f = P.ext f := fun f => rfl
  have hle : Submodule.span ℂ (Set.range P.extL) ≤ AdForms ι ρ J χ := by
    rw [Submodule.span_le]
    rintro _ ⟨f, rfl⟩
    exact P.extMem_holds f
  refine le_antisymm hle ?_
  intro F hF
  have hw : ∀ c, ∃ β : S.ιV → ℂ, ∑ l, β l • P.coef (S.bV l) = F (P.y c) := by
    intro c
    have hmem : F (P.y c) ∈ Submodule.span ℂ (Set.range fun l => P.coef (S.bV l)) := by
      rw [P.coef_span]
      exact Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hmem
    exact hmem
  choose β hβ using hw
  obtain ⟨F', hF'def⟩ : ∃ F' : G → W, F' = ∑ c, ∑ l, β c l • P.extL (clsSingle S c (S.bV l)) := ⟨_, rfl⟩
  have hF'mem : F' ∈ Submodule.span ℂ (Set.range P.extL) := by
    rw [hF'def]
    apply Submodule.sum_mem
    intro c _
    apply Submodule.sum_mem
    intro l _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  have heq : F = F' := by
    refine P.adForms_ext hF (hle hF'mem) (fun c => ?_)
    have hz : ∀ c', c' ≠ c → ∀ l, P.extL (clsSingle S c' (S.bV l)) (P.y c) = 0 := by
      intro c' hc l
      rw [hL, P.ext_rep]
      classical
      simp [clsSingle, Pi.single_apply, hc, Ne.symm hc]
    have hs : ∀ l, P.extL (clsSingle S c (S.bV l)) (P.y c) = P.coef (clsAvg S c (S.bV l)) := by
      intro l
      rw [hL, P.ext_rep]
      simp [clsSingle]
    have hF'c : F' (P.y c) = ∑ l, β c l • P.coef (clsAvg S c (S.bV l)) := by
      rw [hF'def]
      simp only [Finset.sum_apply, Pi.smul_apply]
      rw [Finset.sum_eq_single c]
      · exact Finset.sum_congr rfl fun l _ => by rw [hs l]
      · intro c' _ hc'
        exact Finset.sum_eq_zero fun l _ => by rw [hz c' hc' l, smul_zero]
      · intro hc
        exact absurd (Finset.mem_univ c) hc
    have hwt : ((S.wt c : ℂ)) ≠ 0 := by
      have hpos : 0 < S.wt c := Fintype.card_pos
      exact_mod_cast hpos.ne'
    have hA : ((S.wt c : ℂ))⁻¹ • ∑ g : S.Gam c, (χ (stabK ι (P.stabI c g)) : ℂ) • ρ (P.stabI c g : Γ) (F (P.y c))
        = F (P.y c) := by
      rw [Finset.sum_congr rfl (fun g _ => P.adForms_fixed hF c g), Finset.sum_const, Finset.card_univ]
      change ((S.wt c : ℂ))⁻¹ • (S.wt c • F (P.y c)) = F (P.y c)
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hwt, one_smul]
    have hB : ∑ l, β c l • P.coef (clsAvg S c (S.bV l)) = ((S.wt c : ℂ))⁻¹ •
        ∑ g : S.Gam c, (χ (stabK ι (P.stabI c g)) : ℂ) • ρ (P.stabI c g : Γ) (∑ l, β c l • P.coef (S.bV l)) := by
      simp only [P.coef_avg, map_sum, map_smul, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun l _ => ?_
      congr 1
      ring
    rw [hF'c, hB, hβ c, hA]
  rw [heq]
  exact hF'mem

theorem extBij_holds (P : ClassPres ι S σ ρ J χ) : P.ExtBij := by
  unfold ClassPres.ExtBij
  exact ⟨P.linInd, P.span_eq⟩

end ClassPres

end Formalism.IndefR.Bridge

noncomputable section

namespace Formalism.IndefR.Bridge

section

variable {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G}
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem mem_stab_translate (J : Subgroup G) (y : G) (γ : Γ) (k : J) (δ : Γ) :
    δ ∈ stab ι J (ι γ * y * k) ↔ γ⁻¹ * δ * γ ∈ stab ι J y := by
  rw [mem_stab, mem_stab, map_mul ι, map_mul ι, map_inv]
  have e : (ι γ * y * (k : G))⁻¹ * ι δ * (ι γ * y * (k : G)) =
      (k : G)⁻¹ * (y⁻¹ * ((ι γ)⁻¹ * ι δ * ι γ) * y) * (k : G) := by group
  rw [e]
  constructor
  · intro h
    have e2 : y⁻¹ * ((ι γ)⁻¹ * ι δ * ι γ) * y =
        (k : G) * ((k : G)⁻¹ * (y⁻¹ * ((ι γ)⁻¹ * ι δ * ι γ) * y) * (k : G)) * (k : G)⁻¹ := by group
    rw [e2]
    exact J.mul_mem (J.mul_mem k.2 h) (J.inv_mem k.2)
  · intro h
    exact J.mul_mem (J.mul_mem (J.inv_mem k.2) h) k.2

theorem card_stab_translate (J : Subgroup G) (y : G) (γ : Γ) (k : J) :
    Nat.card (stab ι J (ι γ * y * k)) = Nat.card (stab ι J y) := by
  refine Nat.card_congr
    { toFun := fun δ => ⟨γ⁻¹ * δ * γ, (mem_stab_translate J y γ k δ).1 δ.2⟩
      invFun := fun δ => ⟨γ * δ * γ⁻¹, (mem_stab_translate J y γ k _).2 (by simpa [mul_assoc] using δ.2)⟩
      left_inv := fun δ => by ext; simp [mul_assoc]
      right_inv := fun δ => by ext; simp [mul_assoc] }

theorem adInnerIndep_holds (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) :
    AdInnerIndep ι ρ J χ := by
  unfold AdInnerIndep
  intro hρ hχ I I' instI instI' y y' hy hy' F hF F' hF'
  have hm : ∀ (γ : Γ) (h : G) (k : J), F (ι γ * h * k) = (χ k : ℂ) • ρ γ (F h) := hF
  have hm' : ∀ (γ : Γ) (h : G) (k : J), F' (ι γ * h * k) = (χ k : ℂ) • ρ γ (F' h) := hF'
  choose e he using fun i => (hy' (y i)).exists
  have hbij : Function.Bijective e := by
    constructor
    · intro i j hij
      obtain ⟨γ1, k1, h1⟩ := he i
      obtain ⟨γ2, k2, h2⟩ := he j
      rw [hij] at h1
      refine (hy (y j)).unique ⟨γ2 * γ1⁻¹, k1⁻¹ * k2, ?_⟩ ⟨1, 1, by simp⟩
      rw [h1, h2, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    · intro i'
      obtain ⟨i, ⟨γ, k, hi⟩, -⟩ := hy (y' i')
      refine ⟨i, (hy' (y i)).unique (he i) ⟨γ⁻¹, k⁻¹, ?_⟩⟩
      rw [hi, map_inv, Subgroup.coe_inv]
      group
  have hu : ∀ k : J, starRingEnd ℂ (χ k : ℂ) * (χ k : ℂ) = 1 := by
    intro k
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hχ k]
    norm_num
  unfold adInner
  refine Fintype.sum_bijective e hbij _ _ (fun i => ?_)
  obtain ⟨γ, k, hi⟩ := he i
  rw [hi, hm, hm', inner_smul_left, inner_smul_right, hρ, card_stab_translate,
    ← mul_assoc (starRingEnd ℂ (χ k : ℂ)), hu, one_mul]

theorem lift_independent_action_holds (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ)
    {Q : Subgroup G} {G0 : Type} [Group G0] (red : Q →* G0) (ch : Q →* ℂˣ) :
    LiftIndependentAction ι ρ J χ red ch := by
  unfold LiftIndependentAction
  intro hJ hred hch κ κ' hκ F hF h
  have hm : ∀ (γ : Γ) (h : G) (k : J), F (ι γ * h * k) = (χ k : ℂ) • ρ γ (F h) := hF
  have hk : ((κ⁻¹ * κ' : Q) : G) ∈ J := (hred _).1 (by rw [map_mul, map_inv, hκ]; group)
  have e1 : h * (κ' : G) = ι 1 * (h * (κ : G)) * (((⟨((κ⁻¹ * κ' : Q) : G), hk⟩ : J)) : G) := by
    simp [mul_assoc]
  have e2 : χ ⟨((κ⁻¹ * κ' : Q) : G), hk⟩ = (ch κ)⁻¹ * ch κ' := by
    rw [← hch, ← map_inv, ← map_mul]
    try rfl
  rw [e1, hm, e2, map_one]
  change _ = (((ch κ')⁻¹ : ℂˣ) : ℂ) • (((ch κ)⁻¹ * ch κ' : ℂˣ) : ℂ) • F (h * (κ : G))
  rw [smul_smul, ← Units.val_mul, mul_comm ((ch κ')⁻¹), mul_inv_cancel_right]

end

end Formalism.IndefR.Bridge

noncomputable section

namespace Formalism.IndefR.Bridge

structure IPOnG {N : Type} [AddCommGroup N] [Module ℂ N] (C : Submodule ℂ N) (ip : N → N → ℂ) : Prop where
  fd : FiniteDimensional ℂ C
  add : ∀ x x' y : C, ip ((x : N) + x') y = ip x y + ip x' y
  smul : ∀ (s : ℂ) (x y : C), ip (s • (x : N)) y = starRingEnd ℂ s * ip x y
  herm : ∀ x y : C, starRingEnd ℂ (ip x y) = ip y x
  pos : ∀ x : C, x ≠ 0 → 0 < (ip x x).re

section IPV

variable {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G}
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
variable {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
variable {I : Type} [Fintype I] {y : I → G}

theorem adForms_ext (hy : IsReps ι J y) {F F' : G → W} (hF : F ∈ AdForms ι ρ J χ)
    (hF' : F' ∈ AdForms ι ρ J χ) (h : ∀ i, F (y i) = F' (y i)) : F = F' := by
  have hm : ∀ (γ : Γ) (h : G) (k : J), F (ι γ * h * k) = (χ k : ℂ) • ρ γ (F h) := hF
  have hm' : ∀ (γ : Γ) (h : G) (k : J), F' (ι γ * h * k) = (χ k : ℂ) • ρ γ (F' h) := hF'
  funext x
  obtain ⟨i, ⟨γ, k, rfl⟩, -⟩ := hy x
  rw [hm, hm', h i]

def adEval (y : I → G) : AdForms ι ρ J χ →ₗ[ℂ] (I → W) where
  toFun F i := (F : G → W) (y i)
  map_add' F F' := by funext i; rfl
  map_smul' s F := by funext i; rfl

theorem adEval_injective (hy : IsReps ι J y) :
    Function.Injective (adEval (ι := ι) (ρ := ρ) (χ := χ) y) := by
  intro F F' hEq
  exact Subtype.ext (adForms_ext hy F.2 F'.2 fun i => congrFun hEq i)

theorem adForms_fd (hy : IsReps ι J y) [FiniteDimensional ℂ W] :
    FiniteDimensional ℂ (AdForms ι ρ J χ) := FiniteDimensional.of_injective (adEval (ι := ι) (ρ := ρ) (χ := χ) y) (adEval_injective hy)

theorem adInner_add_left (F F' F'' : G → W) :
    adInner ι J y (F + F') F'' = adInner ι J y F F'' + adInner ι J y F' F'' := by
  simp only [adInner, Pi.add_apply, inner_add_left, mul_add, Finset.sum_add_distrib]

theorem adInner_smul_left (s : ℂ) (F F' : G → W) :
    adInner ι J y (s • F) F' = starRingEnd ℂ s * adInner ι J y F F' := by
  simp only [adInner, Pi.smul_apply, inner_smul_left, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem adInner_conj (F F' : G → W) :
    starRingEnd ℂ (adInner ι J y F F') = adInner ι J y F' F := by
  simp only [adInner, map_sum, map_mul, map_inv₀, map_natCast, inner_conj_symm]

theorem re_natCast_inv_mul (n : ℕ) (z : ℂ) : (((n : ℂ))⁻¹ * z).re = ((n : ℝ))⁻¹ * z.re := by
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul]

theorem adInner_pos (hy : IsReps ι J y) (hst : ∀ i, Nat.card (stab ι J (y i)) ≠ 0) {F : G → W}
    (hF : F ∈ AdForms ι ρ J χ) (hne : F ≠ 0) : 0 < (adInner ι J y F F).re := by
  have hex : ∃ i, F (y i) ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hne (adForms_ext hy hF (Submodule.zero_mem _) (fun i => by rw [hall i]; rfl))
  have hre : ∀ x : W, (inner ℂ x x).re = ‖x‖ ^ 2 := fun x => inner_self_eq_norm_sq (𝕜 := ℂ) x
  unfold adInner
  rw [Complex.re_sum]
  simp only [re_natCast_inv_mul, hre]
  obtain ⟨i0, hi0⟩ := hex
  apply Finset.sum_pos'
  · intro i _
    positivity
  · refine ⟨i0, Finset.mem_univ _, ?_⟩
    have h1 : (0 : ℝ) < (Nat.card (stab ι J (y i0)) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (hst i0)
    have h2 : 0 < ‖F (y i0)‖ := norm_pos_iff.2 hi0
    positivity

theorem adInner_ipOn (hy : IsReps ι J y) (hst : ∀ i, Nat.card (stab ι J (y i)) ≠ 0)
    [FiniteDimensional ℂ W] : IPOnG (AdForms ι ρ J χ) (adInner ι J y) where
  fd := adForms_fd hy
  add _ _ _ := adInner_add_left _ _ _
  smul _ _ _ := adInner_smul_left _ _ _
  herm _ _ := adInner_conj _ _
  pos x hx := adInner_pos hy hst x.2 (fun h => hx (Subtype.ext h))

end IPV

end Formalism.IndefR.Bridge
