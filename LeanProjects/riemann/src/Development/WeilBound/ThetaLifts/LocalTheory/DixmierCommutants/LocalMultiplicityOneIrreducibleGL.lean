import Development.WeilBound.ThetaLifts.LocalTheory.DixmierCommutants.KilEmpty

noncomputable section

namespace PositivityTheory.ThKG.LocalRamifiedLeviRestriction

open GlobalTheory.WeilM Filter Topology ValuativeRel Matrix PositivityTheory.KCo GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]
  {n d d₁ : ℕ} (e : Fin d₁ ⊕ Bool ≃ Fin d) {W : Type} [AddCommGroup W] [Module ℂ W]

def tn (ψ : Matrix (Fin n) (Fin d₁) k → ℂ) (f f' : (Fin n → k) → ℂ) : Matrix (Fin n) (Fin d) k → ℂ :=
  fun Y => ψ (mid e Y) * f (cl e false Y) * f' (cl e true Y)

def tn₁ (f f' : (Fin n → k) → ℂ) : (Matrix (Fin n) (Fin d₁) k → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ) where
  toFun ψ := tn e ψ f f'
  map_add' _ _ := funext fun _ => by simp [tn, add_mul]
  map_smul' _ _ := funext fun _ => by simp [tn, mul_assoc]

def tn₃ (ψ : Matrix (Fin n) (Fin d₁) k → ℂ) (f : (Fin n → k) → ℂ) : ((Fin n → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ) where
  toFun f' := tn e ψ f f'
  map_add' _ _ := funext fun _ => by simp [tn, mul_add]
  map_smul' _ _ := funext fun _ => by simp [tn, mul_left_comm]

def one (n : ℕ) : (Fin n → k) → ℂ := cs (bx (Fin n) (1 : k)) 0

def blk (g : Matrix (Fin d₁) (Fin d₁) k) : Matrix (Fin d) (Fin d) k := reindex e e (fromBlocks g 0 0 1)

variable {e} {ν : kˣ →* ℂˣ} {L : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] W}

theorem one_sb : (one n : (Fin n → k) → ℂ) ∈ SB (Fin n → k) := by
  unfold one
  exact cs_mem (V := Fin n → k) (H := bx (Fin n) (1 : k)) (bx_open (one_ne_zero' k)) (bx_compact (1 : k)) 0

theorem cm : Continuous (mid e : Matrix (Fin n) (Fin d) k → _) := continuous_id.matrix_submatrix _ _

theorem cc (t : Bool) : Continuous (cl e t : Matrix (Fin n) (Fin d) k → _) := continuous_pi fun i => continuous_id.matrix_elem i _

theorem tn_mem {ψ : Matrix (Fin n) (Fin d₁) k → ℂ} {f f' : (Fin n → k) → ℂ} (h : ψ ∈ SB _) (hf : f ∈ SB _) (hf' : f' ∈ SB _) :
    tn e ψ f f' ∈ SB _ := by
  refine ⟨((h.1.comp_continuous cm).mul (hf.1.comp_continuous (cc false))).mul (hf'.1.comp_continuous (cc true)), ?_⟩
  let a : Matrix (Fin n) (Fin d₁) k × (Fin n → k) × (Fin n → k) → Matrix (Fin n) (Fin d) k := fun x =>
    Matrix.of fun i j => Sum.elim (x.1 i) (fun t => cond t (x.2.2 i) (x.2.1 i)) (e.symm j)
  have ca : Continuous a := continuous_matrix fun i j => by
    simp only [a, Matrix.of_apply]
    rcases e.symm j with s | _ | _
    · exact continuous_fst.matrix_elem i s
    · exact (continuous_apply i).comp (continuous_fst.comp continuous_snd)
    · exact (continuous_apply i).comp (continuous_snd.comp continuous_snd)
  refine HasCompactSupport.intro ((h.2.isCompact.prod (hf.2.isCompact.prod hf'.2.isCompact)).image ca) fun Y hY => ?_
  by_contra h0
  refine hY ⟨(mid e Y, cl e false Y, cl e true Y), ⟨subset_tsupport _ (left_ne_zero_of_mul (left_ne_zero_of_mul h0)),
    subset_tsupport _ (right_ne_zero_of_mul (left_ne_zero_of_mul h0)), subset_tsupport _ (right_ne_zero_of_mul h0)⟩, ?_⟩
  ext i j
  obtain ⟨j, rfl⟩ := e.surjective j
  rcases j with s | _ | _ <;> simp [a, mid, cl]

theorem sum_e (a : Fin d → k) : ∑ j, a j = ∑ s, a (e (.inl s)) + (a (e (.inr true)) + a (e (.inr false))) := by
  rw [← e.sum_comp, Fintype.sum_sum_type, Fintype.sum_bool]

theorem trans_inv (hL : Inv e ν L) {ψ : Matrix (Fin n) (Fin d₁) k → ℂ} (h : Full ψ) {f f' : (Fin n → k) → ℂ} (hf : f ∈ SB _)
    (hf' : f' ∈ SB _) (v : Fin n → k) : L (tn e ψ f fun x => f' (x + v)) = L (tn e ψ f f') := by
  obtain ⟨U, hU, hi⟩ := exists_invar hf'
  have : Kil (LinearMap.ker (L ∘ₗ (tn₁ e f (fun x => f' (x + v)) - tn₁ e f f'))) {Z | RI Z} := by
    refine kil_loc hV_mat fun Z₀ ⟨R, hR⟩ => ⟨{Z | v - Z *ᵥ (R *ᵥ v) ∈ U}, ?_, fun φ hφ hs => ?_⟩
    · exact (continuous_const.sub (continuous_id.matrix_mulVec continuous_const)).continuousAt.preimage_mem_nhds (by
        simpa [mulVec_mulVec, hR] using hU)
    let w : Fin d → k := fun j => Sum.elim (R *ᵥ v) 0 (e.symm j)
    let g : Matrix (Fin d) (Fin d) k := 1 + vecMulVec w (Pi.single (e (.inr true)) 1)
    have hg : InP e g := by
      refine ⟨fun r hr => ?_, ?_, ?_, fun s s' => ?_, fun s => ?_⟩ <;> simp [g, w, vecMulVec_apply, Matrix.one_apply, *]
    have e1 := (hL.right g hg _ (tn_mem (e := e) hφ hf hf')).2
    rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.sub_apply, map_sub, sub_eq_zero]
    refine Eq.trans (congrArg L (funext fun Y => ?_)) e1
    have yw : Y *ᵥ w = mid e Y *ᵥ (R *ᵥ v) := funext fun i => by
      simp only [mulVec, dotProduct]; rw [sum_e (e := e)]; simp [w, mid, mulVec, dotProduct]
    have yg : Y * g = Y + vecMulVec (mid e Y *ᵥ (R *ᵥ v)) (Pi.single (e (.inr true)) 1) := by
      rw [Matrix.mul_add, Matrix.mul_one, mul_vecMulVec, yw]
    have m1 : mid e (Y * g) = mid e Y := by ext i s; rw [yg]; simp [mid, vecMulVec_apply]
    have m2 : cl e false (Y * g) = cl e false Y := by ext i; rw [yg]; simp [cl, vecMulVec_apply]
    have m3 : cl e true (Y * g) = cl e true Y + mid e Y *ᵥ (R *ᵥ v) := by ext i; rw [yg]; simp [cl, vecMulVec_apply]
    change φ _ * f _ * f' _ = φ _ * f _ * f' _
    rw [m1, m2, m3]
    by_cases h0 : φ (mid e Y) = 0
    · simp [h0]
    · rw [← hi _ (hs _ h0) (cl e true Y + mid e Y *ᵥ (R *ᵥ v))]
      congr 2
      abel
  have := this ψ h.1 fun Z hZ => ri_iff.2 (by by_contra h'; exact hZ (h.2 Z h'))
  rwa [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.sub_apply, map_sub, sub_eq_zero] at this

theorem comp_mem {f : (Fin n → k) → ℂ} (hf : f ∈ SB _) (g : GL (Fin n) k) : (fun x => f (g.val *ᵥ x)) ∈ SB (Fin n → k) := by
  let H : (Fin n → k) ≃ₜ (Fin n → k) :=
    { toFun := fun x => g.val *ᵥ x, invFun := fun x => (g⁻¹).val *ᵥ x, left_inv := fun x => by simp [mulVec_mulVec],
      right_inv := fun x => by simp [mulVec_mulVec], continuous_toFun := continuous_const.matrix_mulVec continuous_id,
      continuous_invFun := continuous_const.matrix_mulVec continuous_id }
  exact ⟨hf.1.comp_continuous H.continuous, hf.2.comp_homeomorph H⟩

theorem mod_inv (hL : Inv e ν L) {ψ : Matrix (Fin n) (Fin d₁) k → ℂ} (h : Full ψ) {f f' : (Fin n → k) → ℂ} (hf : f ∈ SB _)
    (hf' : f' ∈ SB _) (g : GL (Fin n) k) :
    ((GlobalTheory.SplitWeil.nabs k (GeneralLinearGroup.det g) : ℝ) : ℂ) • L (tn e ψ f fun x => f' (g.val *ᵥ x)) = L (tn e ψ f f') := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro m
  rw [map_sub, map_smul, sub_eq_zero]
  exact invariant_comp_mulVec (m ∘ₗ L ∘ₗ tn₃ e ψ f) (fun φ hφ a => congrArg m (trans_inv hL h hf hφ a)) g hf' (comp_mem hf' g)

theorem swap_mid (hL : Inv e ν L) {l : kˣ} (hl : valuation k (l : k) = 1) (hν : ν l ≠ 1) {ψ : Matrix (Fin n) (Fin d₁) k → ℂ}
    (h : ψ ∈ SB _) {f f₁ f' : (Fin n → k) → ℂ} (hf : f ∈ SB _) (hf₁ : f₁ ∈ SB _) (hf' : f' ∈ SB _) (c : ℂ) (h0 : f 0 = c * f₁ 0) :
    L (tn e ψ f f') = c • L (tn e ψ f₁ f') := by
  have := kil_one hL hl hν (tn e ψ f f' - c • tn e ψ f₁ f') (sub_mem (tn_mem h hf hf') ((SB _).smul_mem _ (tn_mem h hf₁ hf')))
    fun Y hY h1 => hY (by simp only [Pi.sub_apply, Pi.smul_apply, tn, h1, h0, smul_eq_mul]; ring)
  rwa [LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero] at this

theorem one_zero : (one n : (Fin n → k) → ℂ) 0 = 1 := Set.indicator_of_mem (by simp [zero_mem]) _

theorem red (hL : Inv e ν L) (hu : USm ν) {l : kˣ} (hl : valuation k (l : k) = 1) (hν : ν l ≠ 1)
    (h : ∀ ψ, Full ψ → L (tn e ψ (one n) (one n)) = 0) : ∀ Φ ∈ SB (Matrix (Fin n) (Fin d) k), L Φ = 0 := by
  have h2 : Kil (LinearMap.ker L) {Y | RI (mid e Y)} := by
    refine kil_loc hV_mat fun X₀ ⟨R, hR⟩ => ?_
    obtain ⟨r, r0, hr⟩ := mb_small (nhds_sub (det_nhds hR))
    refine ⟨{Y | mid e Y - mid e X₀ ∈ mb _ _ r}, ((mb_open r0).preimage (cm.sub continuous_const)).mem_nhds (by simp [zero_mem]),
      fun Φ hΦ hs => ?_⟩
    obtain ⟨U, hU, hi⟩ := exists_invar hΦ
    obtain ⟨c, c0, hc⟩ := mb_small (inter_mem hU (cm (e := e).continuousAt.preimage_mem_nhds ((mb_open r0).mem_nhds (zero_mem _))))
    refine mem_of_cs (mb_open c0) hΦ (fun S hS => hi S (hc hS).1) _ fun y hy => ?_
    have e1 : cs (mb _ _ c) y = tn e (cs (mb _ _ c ⊓ mb _ _ r) (mid e y)) (cs (bx _ c) (cl e false y)) (cs (bx _ c) (cl e true y)) := by
      funext Y
      classical
      have : Y - y ∈ mb _ _ c ↔ (mid e Y - mid e y ∈ mb _ _ c ⊓ mb _ _ r ∧ cl e false Y - cl e false y ∈ bx _ c) ∧
          cl e true Y - cl e true y ∈ bx _ c := by
        refine ⟨fun h => ⟨⟨⟨fun i s => h i _, (hc h).2⟩, fun i => h i _⟩, fun i => h i _⟩, fun h i j => ?_⟩
        obtain ⟨j, rfl⟩ := e.surjective j
        rcases j with s | _ | _
        exacts [h.1.1.1 i s, h.1.2 i, h.2 i]
      simp only [tn, cs, Set.indicator_apply, Set.mem_setOf_eq, this, Pi.one_apply]
      split_ifs <;> simp_all
    have o : IsOpen ((mb (Fin n) (Fin d₁) c ⊓ mb _ _ r : AddSubgroup _) : Set (Matrix (Fin n) (Fin d₁) k)) := (mb_open c0).inter (mb_open r0)
    have fu : Full (cs (mb (Fin n) (Fin d₁) c ⊓ mb _ _ r) (mid e y)) := by
      refine ⟨cs_mem o ((mb_compact c).inter_right (AddSubgroup.isClosed_of_isOpen _ (mb_open r0))) _, fun Z hZ => ?_⟩
      by_contra h'
      have := hr (add_mem (cs_ne h').2 (hs y hy))
      exact hZ (ri_iff.1 (ri_of_det (R := R) (by simpa using this)))
    have s1 := fun x : Fin n → k => cs_mem (bx_open (S := Fin n) c0) (bx_compact c) x
    rw [LinearMap.mem_ker, e1, swap_mid hL hl hν fu.1 (s1 _) one_sb (s1 _) (cs (bx _ c) (cl e false y) 0) (by rw [one_zero, mul_one])]
    let g : GL (Fin n) k := GeneralLinearGroup.scalar _ (Units.mk0 c c0)⁻¹
    have e2 := mod_inv hL fu one_sb one_sb g
    have e3 : cs (bx _ c) (cl e true y) = fun x => (fun x => one n (g.val *ᵥ x)) (x + -cl e true y) := by
      funext x
      classical
      have : g.val *ᵥ (x + -cl e true y) - 0 ∈ bx (Fin n) (1 : k) ↔ x - cl e true y ∈ bx _ c := by
        refine forall_congr' fun i => ?_
        have : (g.val *ᵥ (x + -cl e true y) - 0) i = c⁻¹ * (x - cl e true y) i := by
          have gv : g.val = diagonal fun _ => c⁻¹ := by
            change Matrix.scalar _ ((Units.mk0 c c0)⁻¹).val = _
            simp [Matrix.scalar_apply]
          rw [gv]
          rw [sub_zero, mulVec_diagonal, sub_eq_add_neg]
        rw [this, map_mul, map_inv₀, map_one, inv_mul_le_iff₀ (zero_lt_iff.2 (by simpa using c0)), mul_one]
      simp only [one, cs, Set.indicator_apply, Set.mem_setOf_eq, this, Pi.one_apply]
    rw [h _ fu, smul_eq_zero] at e2
    rw [e3, trans_inv hL fu one_sb (comp_mem one_sb g), e2.resolve_left (by simpa [apow] using apow_ne_zero (GeneralLinearGroup.det g) 1), smul_zero]
  intro Φ hΦ
  obtain ⟨Φ₀, h0, ha⟩ := surjectivity_statement k n d ν 1 hu (fun h => hν (by simp [h])) Φ hΦ
  have h3 : aug n d ν 1 ≤ LinearMap.ker L := Submodule.span_le.2 (by
    rintro _ ⟨g, Ψ, hΨ, rfl⟩
    exact LinearMap.mem_ker.2 (by rw [map_sub, hL.left g Ψ hΨ, sub_self]))
  have h4 := kil_full hL hl hν h2 Φ₀ h0.1 fun Y hY => ri_iff.2 (by by_contra h'; exact hY (h0.2 Y h'))
  have := add_mem (h3 ha) h4
  rwa [sub_add_cancel] at this

theorem full_omB {m : ℕ} {ψ : Matrix (Fin n) (Fin m) k → ℂ} (h : Full ψ) (g : GL (Fin n) k) (g' : GL (Fin m) k) :
    Full fun Z : Matrix (Fin n) (Fin m) k => ψ (g.val * Z * g'.val) := by
  let H : Matrix (Fin n) (Fin m) k ≃ₜ Matrix (Fin n) (Fin m) k :=
    { toFun := fun x => g.val * x * g'.val, invFun := fun x => (g⁻¹).val * x * (g'⁻¹).val,
      left_inv := fun x => by simp [Matrix.mul_assoc], right_inv := fun x => by simp [Matrix.mul_assoc],
      continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const,
      continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
  refine ⟨⟨h.1.1.comp_continuous H.continuous, h.1.2.comp_homeomorph H⟩, fun Z hZ => h.2 _ fun h' => hZ ?_⟩
  obtain ⟨R, hR⟩ := ri_iff.2 h'
  refine ri_iff.1 ⟨g'.val * R * g.val, ?_⟩
  have := congrArg (fun A => (g⁻¹).val * A * g.val) hR
  simpa [Matrix.mul_assoc] using this

theorem aug_ker (hL : Inv e ν L) {l : kˣ} (hl : valuation k (l : k) = 1) (hν : ν l ≠ 1) :
    augF n d₁ ν 1 ≤ LinearMap.ker (L ∘ₗ tn₁ e (one n) (one n)) := Submodule.span_le.2 (by
  rintro _ ⟨g, ψ, h, rfl⟩
  have hd : (d : ℂ) = d₁ + 2 := by
    have := Fintype.card_congr e
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_bool] at this
    exact_mod_cast this.symm
  let g' := invT g⁻¹
  have hg : g'.val = g.valᵀ := by simp [g', invT]
  have dg : GeneralLinearGroup.det g' = gdet g := Units.ext (by simp [hg, gdet])
  have fu := full_omB h g' 1
  have e1 := hL.left g _ (tn_mem (e := e) h.1 one_sb one_sb)
  have e2 : omB ν 1 g 1 (tn e ψ (one n) (one n)) = ((ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2)) •
      tn e (fun Z : Matrix (Fin n) (Fin d₁) k => ψ (g'.val * Z * (1 : GL (Fin d₁) k).val)) (fun x => one n (g'.val *ᵥ x)) fun x => one n (g'.val *ᵥ x) := by
    funext Y
    have m1 : mid e (g.valᵀ * Y) = g.valᵀ * mid e Y := rfl
    have m2 : ∀ t, cl e t (g.valᵀ * Y) = g.valᵀ *ᵥ cl e t Y := fun t => rfl
    simp [omB, tn, hg, m1, m2]
  have e3 : omB ν 1 g 1 ψ = ((ν (gdet g) : ℂ) * apow (gdet g) ((d₁ : ℂ) / 2)) • fun Z : Matrix (Fin n) (Fin d₁) k => ψ (g'.val * Z * (1 : GL (Fin d₁) k).val) := by
    funext Y
    simp [omB, hg]
  have e4 := mod_inv hL fu one_sb one_sb g'
  rw [e2, map_smul, swap_mid hL hl hν fu.1 (comp_mem one_sb g') one_sb (comp_mem one_sb g') 1 (by simp)] at e1
  refine LinearMap.mem_ker.2 ?_
  rw [map_sub, e3, map_smul, sub_eq_zero]
  refine Eq.trans ?_ e1
  have e5 : (L ∘ₗ tn₁ e (one n) (one n)) (fun Z : Matrix (Fin n) (Fin d₁) k => ψ (g'.val * Z * (1 : GL (Fin d₁) k).val)) = _ := e4.symm
  rw [e5, dg, smul_smul, one_smul, hd, add_div, apow_add]
  congr 1
  simp [apow, mul_assoc])

theorem local_multiplicity_one_irreducible_GL (hB : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) {L' : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] W} (hL : Inv e ν L)
    (hL' : Inv e ν L') (hu : USm ν) {l : kˣ} (hl : valuation k (l : k) = 1) (hν : ν l ≠ 1) (hn : n ≤ d₁)
    (ρ : GL (Fin d₁) k → Module.End ℂ W) (hr : Module.rank ℂ W ≤ Cardinal.aleph0)
    (hi : ∀ N : Submodule ℂ W, (∀ g, ∀ x ∈ N, ρ g x ∈ N) → N = ⊥ ∨ N = ⊤)
    (hM : ∀ g, ∀ Φ ∈ SB (Matrix (Fin n) (Fin d) k), L (fun Y : Matrix (Fin n) (Fin d) k => Φ (Y * blk e g.val)) = ρ g (L Φ))
    (hM' : ∀ g, ∀ Φ ∈ SB (Matrix (Fin n) (Fin d) k), L' (fun Y : Matrix (Fin n) (Fin d) k => Φ (Y * blk e g.val)) = ρ g (L' Φ))
    (h0 : ∃ Φ ∈ SB (Matrix (Fin n) (Fin d) k), L Φ ≠ 0) : ∃ c : ℂ, ∀ Φ ∈ SB (Matrix (Fin n) (Fin d) k), L' Φ = c • L Φ := by
  let S : Submodule ℂ (Matrix (Fin n) (Fin d₁) k → ℂ) :=
    { carrier := {ψ | Full ψ}, add_mem' := fun ha hb => ⟨add_mem ha.1 hb.1, fun Y h => by simp [ha.2 Y h, hb.2 Y h]⟩,
      zero_mem' := ⟨zero_mem _, fun _ _ => rfl⟩, smul_mem' := fun c a ha => ⟨(SB _).smul_mem c ha.1, fun Y h => by simp [ha.2 Y h]⟩ }
  let j := tn₁ e (one n) (one n : (Fin n → k) → ℂ)
  let A : GL (Fin d₁) k → S → S := fun g ψ => ⟨_, full_omB ψ.2 1 g⟩
  have jA : ∀ (g : GL (Fin d₁) k) (ψ : Matrix (Fin n) (Fin d₁) k → ℂ), j (fun Z : Matrix (Fin n) (Fin d₁) k => ψ ((1 : GL (Fin n) k).val * Z * g.val)) =
      fun Y : Matrix (Fin n) (Fin d) k => j ψ (Y * blk e g.val) := fun (g : GL (Fin d₁) k) ψ => funext fun Y => by
    have m1 : mid e (Y * blk e g.val) = mid e Y * g.val := by
      ext i s; simp only [mid, submatrix_apply, Matrix.mul_apply, id]; rw [sum_e (e := e)]; simp [blk]
    have m2 : ∀ t, cl e t (Y * blk e g.val) = cl e t Y := fun t => by
      ext i; simp only [cl, Matrix.mul_apply]; rw [sum_e (e := e)]; cases t <;> simp [blk]
    simp [j, tn₁, tn, m1, m2]
  let μ := L ∘ₗ j ∘ₗ S.subtype
  let μ' := L' ∘ₗ j ∘ₗ S.subtype
  have eA : ∀ g ψ, μ (A g ψ) = ρ g (μ ψ) := fun g ψ => (congrArg L (jA g ψ)).trans (hM g _ (tn_mem ψ.2.1 one_sb one_sb))
  have eA' : ∀ g ψ, μ' (A g ψ) = ρ g (μ' ψ) := fun g ψ => (congrArg L' (jA g ψ)).trans (hM' g _ (tn_mem ψ.2.1 one_sb one_sb))
  have ne : ¬ ∀ ψ, Full ψ → L (tn e ψ (one n) (one n)) = 0 := fun h => let ⟨Φ, h1, h2⟩ := h0; h2 (red hL hu hl hν h Φ h1)
  have ker : ∀ ψ, μ ψ = 0 → μ' ψ = 0 := by
    rcases irrF' hB (α := 1) hn hu (LinearMap.ker (L ∘ₗ j) ⊓ S) (le_inf (aug_ker hL hl hν) (Submodule.span_le.2 (by
      rintro _ ⟨g, ψ, h, rfl⟩
      refine sub_mem ?_ h
      have := S.smul_mem ((ν (gdet g) : ℂ) * apow (gdet g) ((d₁ : ℂ) / 2)) (full_omB h (invT g⁻¹) 1)
      convert this using 1
      funext Y
      simp [omB, invT]))) (fun g ψ h _ => by
        have e1 : omB ν 1 1 g ψ = apow (gdet g) ((n : ℂ) / 2) • (A g ⟨ψ, h.2⟩).1 := by
          funext Y
          simp [omB, A]
        rw [e1]
        refine Submodule.smul_mem _ _ ⟨?_, (A g ⟨ψ, h.2⟩).2⟩
        have : μ ⟨ψ, h.2⟩ = 0 := h.1
        exact (eA g ⟨ψ, h.2⟩).trans (by rw [this, map_zero])) with h | h
    · exact absurd (fun ψ hψ => (h ψ hψ).1) ne
    · exact fun ψ hψ => aug_ker hL' hl hν (h ψ.1 ⟨hψ, ψ.2⟩ ψ.2)
  have top : LinearMap.range μ = ⊤ := (hi _ (by rintro g _ ⟨ψ, rfl⟩; exact ⟨A g ψ, eA g ψ⟩)).resolve_left fun h =>
    ne fun ψ hψ => by
      have : μ ⟨ψ, hψ⟩ ∈ LinearMap.range μ := ⟨_, rfl⟩
      rwa [h, Submodule.mem_bot] at this
  obtain ⟨s, hs⟩ := μ.exists_rightInverse_of_surjective top
  have th : ∀ ψ, (μ' ∘ₗ s) (μ ψ) = μ' ψ := fun ψ => by
    have := ker (s (μ ψ) - ψ) (by rw [map_sub, ← LinearMap.comp_apply μ s, hs, LinearMap.id_apply, sub_self])
    rwa [map_sub, sub_eq_zero] at this
  obtain ⟨c, hc⟩ := dixmier_commutant_scalar _ W ρ hr hi (μ' ∘ₗ s) fun g => LinearMap.ext fun x => by
    obtain ⟨ψ, rfl⟩ := LinearMap.range_eq_top.1 top x
    rw [Module.End.mul_apply, Module.End.mul_apply, ← eA, th, th, eA']
  refine ⟨c, fun Φ hΦ => sub_eq_zero.1 (red (L := L' - c • L) (e := e) ⟨fun g Ψ h => ?_, fun g hg Ψ h => ⟨(hL.right g hg Ψ h).1, ?_⟩⟩
    hu hl hν (fun ψ hψ => ?_) Φ hΦ)⟩
  · simp [hL.left g Ψ h, hL'.left g Ψ h]
  · simp only [LinearMap.sub_apply, LinearMap.smul_apply, (hL.right g hg Ψ h).2, (hL'.right g hg Ψ h).2]
  · have := th ⟨ψ, hψ⟩
    rw [hc] at this
    exact sub_eq_zero.2 this.symm

end PositivityTheory.ThKG.LocalRamifiedLeviRestriction
