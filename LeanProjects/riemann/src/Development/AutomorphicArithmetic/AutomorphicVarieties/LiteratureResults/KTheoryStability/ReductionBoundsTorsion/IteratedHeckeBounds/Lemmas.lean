import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.IteratedHeckeBounds.HkIterContOn

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.JoinReconstruction

open PositivityTheory.KB

section Lemmas

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

theorem actL_cont (h : HS L N) : Continuous fun x : Gp L N => actL x h := by
  unfold actL actM
  refine continuous_induced_rng.2 ?_
  have hi : Continuous fun x : Gp L N => fun w => (((x w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) :=
    continuous_pi fun w => Units.continuous_coe_inv.comp (continuous_apply w)
  refine continuous_pi fun w => ?_
  have hw := (continuous_apply w).comp hi
  exact ((hw.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul hw

theorem ofS_cont : Continuous (ofS L N) := by
  unfold ofS
  refine continuous_pi fun w => ?_
  simp only [MonoidHom.coe_comp, Function.comp_def, MonoidHom.pi_apply, Pi.evalMonoidHom_apply]
  rw [Units.continuous_iff]
  have hv : Continuous fun a : Sp L N => ((a w : Matrix.SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) :=
    continuous_subtype_val.comp (continuous_apply w)
  refine ⟨hv, ?_⟩
  have hi : ∀ A : Matrix.SpecialLinearGroup (Fin N) ℂ,
      ((SpecialLinearGroup.toGL A)⁻¹ : GL (Fin N) ℂ).val = Matrix.adjugate (A : Matrix (Fin N) (Fin N) ℂ) := by
    intro A
    rw [← map_inv]
    exact Matrix.SpecialLinearGroup.coe_inv A
  simp only [hi]
  exact hv.matrix_adjugate

theorem fr_comp_cont {q : ℕ} {ω : Form (HS L N) q} (hω : ContinuousOn ω (Pos L N)) (u : Fin q → HS L N) :
    Continuous fun x => fr ω x u := by
  unfold fr
  have hp : Continuous fun x : Gp L N => actL x ↑(one L N) := actL_cont _
  have hw : Continuous fun x : Gp L N => ω (actL x ↑(one L N)) :=
    hω.comp_continuous hp fun x => (x • one L N).2
  have hu : Continuous fun x : Gp L N => fun i => actL x (u i) :=
    continuous_pi fun i => actL_cont (u i)
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  exact hw.eval hu

theorem fr_inv {q : ℕ} {ω : Form (HS L N) q} {g : Gp L N} (hω : FInv ω g) (x : Gp L N) :
    fr ω (g * x) = fr ω x := by
  unfold fr
  have hm : actL x ↑(one L N) ∈ Pos L N := (x • one L N).2
  have h1 := hω _ hm
  have hc : actL (g * x) = (actL g).comp (actL x) :=
    ContinuousLinearMap.ext fun h => actL_mul g x h
  rw [hc, ← h1]
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousLinearMap.comp_apply,
    Function.comp_def]

theorem fr_sub {q : ℕ} (ω ω' : Form (HS L N) q) (x : Gp L N) : fr (ω - ω') x = fr ω x - fr ω' x := by
  ext v; simp [fr]

theorem finv_sub {q : ℕ} {ω ω' : Form (HS L N) q} {g : Gp L N} (hω : FInv ω g) (hω' : FInv ω' g) :
    FInv (ω - ω') g := by
  unfold FInv at hω hω' ⊢
  intro h hh
  ext v
  have a := congrArg (fun f => f v) (hω h hh)
  have b := congrArg (fun f => f v) (hω' h hh)
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply] at a b
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Pi.sub_apply,
    ContinuousAlternatingMap.sub_apply, a, b]

theorem dC_sub {Y : Type} {m : ℕ} (F G : (Fin (m + 1) → Y) → ℝ) :
    dC (fun y => F y - G y) = fun y => dC F y - dC G y := by
  unfold dC
  funext y
  rw [← Finset.sum_sub_distrib]
  simp only [mul_sub]

theorem ev_sub {G H Y : Type} [Group G] [Group H] [MulAction H Y] (ρ : G →* H) {m : ℕ}
    (F F' : (Fin (m + 1) → Y) → ℝ) (y : Y) (z : Chn G m) :
    ev ρ (fun y => F y - F' y) y z = ev ρ F y z - ev ρ F' y z := by
  unfold ev
  simp only [mul_sub, Finsupp.sum_sub]

theorem ev_toK {m : ℕ} (G : (Fin (m + 1) → GK L N) → ℝ) (Φ : (Fin (m + 1) → Pos L N) → ℝ)
    (hG : ∀ y, G y = Φ fun j => toP L N (y j) • one L N) (z : Chn (Gm L N) m) :
    ev (toK L N) G 1 z = ev (emb L N) Φ (one L N) z := by
  unfold ev
  refine Finsupp.sum_congr fun g _ => ?_
  rw [hG]
  congr 2
  funext j
  rw [smul_eq_mul, mul_one]
  rfl

private theorem pb_actL_compContinuousLinearMap_eq_pb_mul {k : ℕ} (ω : Form (HS L N) k) (g e : Gp L N) (h : HS L N) :
    (pb g ω (actL e h)).compContinuousLinearMap (actL e) = pb (g * e) ω h := by
  unfold pb
  have hc : actL (g * e) = (actL g).comp (actL e) :=
    ContinuousLinearMap.ext fun x => actL_mul g e x
  rw [hc]
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousLinearMap.comp_apply,
    Function.comp_def]

private theorem pb_mul_eq_pb_of_fInv_of_mem_Pos {k : ℕ} {ω : Form (HS L N) k} {a : Gp L N} (ha : FInv ω a) (g : Gp L N)
    {h : HS L N} (hh : h ∈ Pos L N) : pb (a * g) ω h = pb g ω h := by
  have hm : actL g h ∈ Pos L N := (g • (⟨h, hh⟩ : Pos L N)).2
  have h1 : pb a ω (actL g h) = ω (actL g h) := by
    unfold pb
    exact ha _ hm
  rw [← pb_actL_compContinuousLinearMap_eq_pb_mul, h1]
  unfold pb
  rfl

private theorem mn_compContinuousLinearMap_actL {k : ℕ} (S : Subgroup (Gm L N))
    (F : Quotient (QuotientGroup.rightRel S) → (HS L N [⋀^Fin k]→L[ℝ] ℝ)) (e : Gp L N) :
    (mn S F).compContinuousLinearMap (actL e) = mn S fun c => (F c).compContinuousLinearMap (actL e) := by
  unfold mn
  by_cases hfin : Finite (Quotient (QuotientGroup.rightRel S))
  · haveI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel S))
    simp only [finsum_eq_sum_of_fintype]
    ext v
    simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  · have hinf : Infinite (Gm L N ⧸ S) := by
      rw [← not_finite_iff_infinite]
      intro hf
      exact hfin (Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel S).symm)
    have h0 : S.index = 0 := Subgroup.index_eq_zero_iff_infinite.2 hinf
    simp only [h0, Nat.cast_zero, _root_.inv_zero, zero_smul]
    ext v
    simp

theorem Hk_finv_emb {k : ℕ} (q : GK L N) {ω : Form (HS L N) k} (hω : ∀ γ, FInv ω (emb L N γ)) (γ : Gm L N) :
    FInv (Hk q ω) (emb L N γ) := by
  unfold FInv Hk
  intro h hh
  rw [mn_compContinuousLinearMap_actL]
  simp only [pb_actL_compContinuousLinearMap_eq_pb_mul]
  let σ : Quotient (QuotientGroup.rightRel (Sg q)) ≃ Quotient (QuotientGroup.rightRel (Sg q)) :=
    { toFun := Quotient.map' (fun x => x * γ) (fun a b hab => by
        rw [QuotientGroup.rightRel_apply] at hab ⊢
        simpa [_root_.mul_inv_rev, mul_assoc] using hab)
      invFun := Quotient.map' (fun x => x * γ⁻¹) (fun a b hab => by
        rw [QuotientGroup.rightRel_apply] at hab ⊢
        simpa [_root_.mul_inv_rev, mul_assoc] using hab)
      left_inv := by
        intro c
        induction c using Quotient.inductionOn' with
        | h a => simp only [Quotient.map'_mk'', mul_inv_cancel_right]
      right_inv := by
        intro c
        induction c using Quotient.inductionOn' with
        | h a => simp only [Quotient.map'_mk'', inv_mul_cancel_right] }
  have key : ∀ c, pb (toP L N (q * toK L N (σ c).out)) ω h =
      pb (toP L N (q * toK L N c.out) * emb L N γ) ω h := by
    intro c
    have e1 : σ c = Quotient.mk'' (c.out * γ) := by
      conv_lhs => rw [← Quotient.out_eq' c]
      rfl
    have e2 : (Quotient.mk'' (σ c).out : Quotient (QuotientGroup.rightRel (Sg q))) =
        Quotient.mk'' (c.out * γ) := by
      rw [Quotient.out_eq', e1]
    have hr := Quotient.exact' e2
    rw [QuotientGroup.rightRel_apply] at hr
    have hs : (σ c).out * (c.out * γ)⁻¹ ∈ Sg q := by
      have := (Sg q).inv_mem hr
      simpa [_root_.mul_inv_rev, mul_assoc] using this
    unfold Sg at hs
    obtain ⟨x, ⟨t, rfl⟩, hx⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hs)
    have eq : q * toK L N (σ c).out = toK L N t * ((q * toK L N c.out) * toK L N γ) := by
      have hsplit : (σ c).out = ((σ c).out * (c.out * γ)⁻¹) * (c.out * γ) := by group
      rw [hsplit, map_mul (toK L N) _ (c.out * γ), ← hx]
      simp [MulAut.conj_apply, mul_assoc]
    have ht : FInv ω (toP L N (toK L N t)) := hω t
    rw [eq, map_mul, map_mul, pb_mul_eq_pb_of_fInv_of_mem_Pos ht _ hh]
    rfl
  unfold mn
  congr 1
  rw [← finsum_comp_equiv σ (f := fun c => pb (toP L N (q * toK L N c.out)) ω h)]
  exact finsum_congr fun c => (key c).symm

theorem Hk_finv_scal {k : ℕ} (q : GK L N) {ω : Form (HS L N) k} (hω : ∀ s, FInv ω (scal L N s))
    (s : InfinitePlace L → ℂˣ) : FInv (Hk q ω) (scal L N s) := by
  have hcomm : ∀ g : Gp L N, g * scal L N s = scal L N s * g := by
    intro g
    unfold scal
    funext w
    exact (GeneralLinearGroup.scalar_commute (s w) (g w)).symm
  unfold FInv Hk
  intro h hh
  rw [mn_compContinuousLinearMap_actL]
  simp only [pb_actL_compContinuousLinearMap_eq_pb_mul]
  unfold mn
  congr 1
  refine finsum_congr fun c => ?_
  show pb (toP L N (q * toK L N c.out) * scal L N s) ω h = pb (toP L N (q * toK L N c.out)) ω h
  rw [hcomm, pb_mul_eq_pb_of_fInv_of_mem_Pos (hω s) _ hh]

theorem Hk_iter_props {k : ℕ} (q : GK L N) {ω : Form (HS L N) (k + 1)} (hG : Good ω)
    (hγ : ∀ γ, FInv ω (emb L N γ)) (hs : ∀ s, FInv ω (scal L N s)) (r : ℕ) :
    Good ((Hk q)^[r] ω) ∧ (∀ γ, FInv ((Hk q)^[r] ω) (emb L N γ)) ∧ ∀ s, FInv ((Hk q)^[r] ω) (scal L N s) := by
  induction r with
  | zero => exact ⟨hG, hγ, hs⟩
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨Hk_good q ih.1, Hk_finv_emb q ih.2.1, Hk_finv_scal q ih.2.2⟩

private theorem continuousOn_Hk_of_continuousOn {k : ℕ} (q : GK L N) {ω : Form (HS L N) k} (hc : ContinuousOn ω (Pos L N)) :
    ContinuousOn (Hk q ω) (Pos L N) := by
  have hpb : ∀ g : Gp L N, ContinuousOn (pb g ω) (Pos L N) := by
    intro g
    have ha : ContinuousOn (fun h => ω (actL g h)) (Pos L N) :=
      hc.comp (actL g).continuous.continuousOn fun h hh => (g • (⟨h, hh⟩ : Pos L N)).2
    unfold pb
    exact (ContinuousAlternatingMap.compContinuousLinearMapCLM (actL g)).continuous.comp_continuousOn ha
  unfold Hk mn
  by_cases hfin : Finite (Quotient (QuotientGroup.rightRel (Sg q)))
  · haveI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel (Sg q)))
    simp only [finsum_eq_sum_of_fintype]
    exact ContinuousOn.const_smul (continuousOn_finset_sum _ fun c _ => hpb _) ((((Sg q).index : ℕ) : ℝ)⁻¹)
  · have hinf : Infinite (Gm L N ⧸ Sg q) := by
      rw [← not_finite_iff_infinite]
      intro hf
      exact hfin (Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel (Sg q)).symm)
    have h0 : (Sg q).index = 0 := Subgroup.index_eq_zero_iff_infinite.2 hinf
    simp only [h0, Nat.cast_zero, _root_.inv_zero, zero_smul]
    exact continuousOn_const

theorem hecke_iter {k : ℕ} (q : GK L N) {ω : Form (HS L N) (k + 1)} (hω : ContinuousOn ω (Pos L N)) (r : ℕ)
    (y : Fin (k + 2) → GK L N) :
    (hecke (toK L N) (MonoidHom.id (GK L N)) q)^[r] (fun y => intP ω fun j => toP L N (y j) • one L N) y =
      intP ((Hk q)^[r] ω) fun j => toP L N (y j) • one L N := by
  have step : ∀ ω' : Form (HS L N) (k + 1), ContinuousOn ω' (Pos L N) →
      hecke (toK L N) (MonoidHom.id (GK L N)) q
          (fun y : Fin (k + 2) → GK L N => intP ω' fun j => toP L N (y j) • one L N) =
        fun y : Fin (k + 2) → GK L N => intP (Hk q ω') fun j => toP L N (y j) • one L N := by
    intro ω' hc
    funext y
    rw [intP_Hk q hc]
    unfold hecke mn Sg
    congr 1
    refine finsum_congr fun c => ?_
    simp only [MonoidHom.id_apply]
    rw [intP_pb]
    congr 1
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_smul]
  have hcont : ∀ n, ContinuousOn ((Hk q)^[n] ω) (Pos L N) := by
    intro n
    induction n with
    | zero => exact hω
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact continuousOn_Hk_of_continuousOn q ih
  have hall : ∀ n, (hecke (toK L N) (MonoidHom.id (GK L N)) q)^[n]
        (fun y : Fin (k + 2) → GK L N => intP ω fun j => toP L N (y j) • one L N) =
      fun y : Fin (k + 2) → GK L N => intP ((Hk q)^[n] ω) fun j => toP L N (y j) • one L N := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [Function.iterate_succ_apply']
      rw [ih, step _ (hcont n)]
  exact congrFun (hall r) y

end Lemmas

end PositivityTheory.KB.JoinReconstruction

end
