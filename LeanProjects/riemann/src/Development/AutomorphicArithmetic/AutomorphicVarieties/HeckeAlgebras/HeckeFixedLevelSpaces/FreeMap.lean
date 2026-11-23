import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.HeckeFixedLevelSpaces.SpIntMulVec
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CtrlOrd
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.ClFinMulVec
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.OrdBCMapOrd
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.FnIndep
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UOpNat

open IsLocalRing Matrix UpperTheory.V.Hi

namespace UpperTheory.V.Hi.Sp

variable {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp)

theorem free_map {A B : Type} [CommRing A] [CommRing B] (x : A →+* B) {m : ℕ} (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ)
    (U : Subgroup X.Ub) (h : X.Free τ θ U) :
    X.Free ((Matrix.GeneralLinearGroup.map x).comp τ) ((Units.map x.toMonoidHom).comp θ) U := by
  intro g γ u hu b hb he
  obtain ⟨hc, hb', h1⟩ := h g γ u hu b hb he
  refine ⟨hc, hb', ?_⟩
  ext i j
  have := congrArg (fun M : Matrix (Fin m) (Fin m) A => x (M i j)) h1
  simpa [Matrix.one_apply, apply_ite x] using this

theorem mapFn_ra {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {m : ℕ} (τ : X.Ub →* GL (Fin m) A) (u : X.Ub)
    (f : X.Fn A m) : X.mapFn (B := B) (X.ra τ u f) =
      X.ra ((Matrix.GeneralLinearGroup.map (algebraMap A B)).comp τ) u (X.mapFn f) := by
  funext g i
  simp only [Frame.mapFn, Frame.ra, LinearMap.coe_mk, AddHom.coe_mk, MonoidHom.coe_comp, Function.comp_apply,
    MonoidHom.coe_mk, OneHom.coe_mk]
  rw [RingHom.map_mulVec]
  rfl

private theorem iwahori_decomposition_N_T_Nm {G : Type} [Group G] (I : Iwa G) (b : G) (hb : b ∈ I.Iw 0) :
    ∃ x ∈ I.N, ∃ t ∈ I.T, ∃ y ∈ I.Nm 0, b = x * t * y := by
  have hI : I.Iw 0 = Subgroup.closure ((I.N : Set G) ∪ I.T ∪ I.Nm 0) := by
    simp only [Iwa.Iw, Subgroup.closure_union, Subgroup.closure_eq]
  have step : ∀ g ∈ ((I.N : Set G) ∪ I.T ∪ I.Nm 0), ∀ y : G,
      (∃ x ∈ I.N, ∃ t ∈ I.T, ∃ y' ∈ I.Nm 0, y = x * t * y') →
      ∃ x ∈ I.N, ∃ t ∈ I.T, ∃ y' ∈ I.Nm 0, g * y = x * t * y' := by
    intro g hg y ⟨x, hx, t, ht, y', hy', hyeq⟩
    subst hyeq
    rcases hg with (hg | hg) | hg
    · exact ⟨g * x, I.N.mul_mem hg hx, t, ht, y', hy', by group⟩
    · refine ⟨g * x * g⁻¹, I.T_N g hg x hx, g * t, I.T.mul_mem hg ht, y', hy', by group⟩
    · obtain ⟨x2, hx2, t2, ht2, y2, hy2, h2⟩ := I.swap 0 g hg x hx
      refine ⟨x2, hx2, t2 * t, I.T.mul_mem (I.Tc_le 0 ht2) ht, t⁻¹ * y2 * t * y', ?_, ?_⟩
      · refine (I.Nm 0).mul_mem ?_ hy'
        have := I.T_Nm 0 t⁻¹ (I.T.inv_mem ht) y2 hy2
        simpa using this
      · calc g * (x * t * y') = (g * x) * t * y' := by group
          _ = x2 * t2 * y2 * t * y' := by rw [h2]
          _ = x2 * (t2 * t) * (t⁻¹ * y2 * t * y') := by group
  rw [hI] at hb
  induction hb using Subgroup.closure_induction_left with
  | one => exact ⟨1, I.N.one_mem, 1, I.T.one_mem, 1, (I.Nm 0).one_mem, by group⟩
  | mul_left g hg y _ ih => exact step g hg y ih
  | inv_mul_cancel g hg y _ ih =>
    apply step g⁻¹ _ y ih
    rcases hg with (hg | hg) | hg
    · exact Or.inl (Or.inl (I.N.inv_mem hg))
    · exact Or.inl (Or.inr (I.T.inv_mem hg))
    · exact Or.inr ((I.Nm 0).inv_mem hg)

private theorem exists_finite_coset_reps_Nm {G : Type} [Group G] (I : Iwa G) (e : ℕ) :
    ∃ R : Set G, R.Finite ∧ ∀ y ∈ I.Nm 0, ∃ r ∈ R, ∃ y' ∈ I.Nm e, y = r * y' := by
  have hfi : ((I.Nm e).subgroupOf (I.Nm 0)).FiniteIndex := ⟨I.fin_Nm e⟩
  refine ⟨Set.range (fun q : (I.Nm 0) ⧸ (I.Nm e).subgroupOf (I.Nm 0) => ((Quotient.out q : I.Nm 0) : G)),
    Set.finite_range _, ?_⟩
  intro y hy
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ((I.Nm e).subgroupOf (I.Nm 0)) (⟨y, hy⟩ : I.Nm 0)
  refine ⟨_, ⟨(QuotientGroup.mk (⟨y, hy⟩ : I.Nm 0) : (I.Nm 0) ⧸ (I.Nm e).subgroupOf (I.Nm 0)), rfl⟩,
    ((h⁻¹ : (I.Nm e).subgroupOf (I.Nm 0)) : I.Nm 0), ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.mp (h⁻¹).2
  · show y = ((Quotient.out _ : I.Nm 0) : G) * _
    rw [hh]
    simp

private theorem hecke_eigenvalue_isIntegral {A O Ω : Type} [CommRing A] [CommRing O] [IsDomain O] [IsCNL O] [Field Ω]
    [Algebra A O] [Algebra O Ω] [Algebra A Ω] [IsScalarTower A O Ω] (W : WtRep X.I O Ω) {m : ℕ}
    (τ : X.Ub →* GL (Fin m) A) (φ : X.I.T →* Oˣ) (U : Subgroup X.Ub) (hfin : X.FinLevel U) (e : ℕ) (he : W.c0 ≤ e)
    (F : Fin m → X.Fn Ω (W.d + 1))
    (hF : F ∈ X.Cl ((Matrix.GeneralLinearGroup.map (algebraMap A Ω)).comp τ) W.ξ U e
      ((Units.map (algebraMap O Ω).toMonoidHom).comp φ)) (hF0 : F ≠ 0)
    (κ : Type) [Fintype κ] (u : κ → X.Ub) (μ : Ω)
    (hμ : (∑ q, X.raF (W.d + 1) ((Matrix.GeneralLinearGroup.map (algebraMap A Ω)).comp τ) (u q)) F = μ • F) :
    IsIntegral O μ := by
  set τ' := (Matrix.GeneralLinearGroup.map (algebraMap A Ω)).comp τ with hτ'
  set φ' := (Units.map (algebraMap O Ω).toMonoidHom).comp φ with hφ'
  obtain ⟨⟨hAF, hfix⟩, hE⟩ := Submodule.mem_inf.mp hF |>.imp_left Submodule.mem_inf.mp
  have hAF' : ∀ i γ g, F i (X.glob γ * g) = (W.ξ (X.glob γ).2 : Matrix _ _ Ω) *ᵥ F i g := by
    intro i γ g
    exact (Submodule.mem_pi.mp hAF) i (Set.mem_univ _) γ g
  have hU : ∀ v ∈ U, ∀ i g, F i (g * ((v : Ga), 1)) = ∑ j, (τ' v⁻¹ : Matrix _ _ Ω) i j • F j g := by
    intro v hv i g
    have h := hfix v⁻¹ (U.inv_mem hv)
    have h2 := congrFun (congrFun h i) (g * ((v : Ga), 1))
    rw [← h2]
    funext k
    simp [Frame.raF, Frame.ra, Matrix.mulVec, dotProduct, mul_assoc, Finset.sum_apply,
      show ((1 : Ga), (1 : Gp)) = 1 from rfl]
  have hN : ∀ y ∈ X.I.N, ∀ i g, F i (g * (1, y)) = F i g := by
    intro y hy i g
    have h := hE.1 y hy
    exact congrFun (congrFun h i) g
  have hNm : ∀ y ∈ X.I.Nm e, ∀ i g, F i (g * (1, y)) = F i g := by
    intro y hy i g
    have h := hE.2.1 y hy
    exact congrFun (congrFun h i) g
  have hT : ∀ t : X.I.T, ∀ i g, F i (g * (1, (t : Gp))) = ((φ' t)⁻¹ : Ωˣ).1 • F i g := by
    intro t i g
    have h := hE.2.2 t
    exact congrFun (congrFun h i) g
  obtain ⟨Gv, hGv⟩ : ∃ Gv : Ga × Gp → Fin m → Fin (W.d + 1) → Ω, ∀ g i,
      Gv g i = (↑(W.ξ g.2)⁻¹ : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) *ᵥ F i g :=
    ⟨fun g i => (↑(W.ξ g.2)⁻¹ : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) *ᵥ F i g, fun _ _ => rfl⟩
  obtain ⟨Np, hNp⟩ : ∃ Np : Ga × Gp → Submodule O Ω, ∀ g,
      Np g = Submodule.span O (Set.range fun ik : Fin m × Fin (W.d + 1) => Gv g ik.1 ik.2) := ⟨_, fun _ => rfl⟩
  have memNp : ∀ g i k, Gv g i k ∈ Np g := fun g i k => hNp g ▸ Submodule.subset_span ⟨(i, k), rfl⟩
  have smulNp : ∀ g (c : Ω), c ∈ (algebraMap O Ω).range → ∀ x ∈ Np g, c * x ∈ Np g := by
    rintro g c ⟨o, rfl⟩ x hx
    rw [← Algebra.smul_def]
    exact (Np g).smul_mem o hx
  have leNp : ∀ g g', (∀ i k, Gv g' i k ∈ Np g) → Np g' ≤ Np g := by
    intro g g' h
    rw [hNp g']
    exact Submodule.span_le.mpr (by rintro _ ⟨⟨i, k⟩, rfl⟩; exact h i k)
  have mvG : ∀ γ g, Gv (X.glob γ * g) = Gv g := by
    intro γ g
    funext i
    rw [hGv, hGv, hAF', Prod.snd_mul, map_mul, _root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec,
      Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have mvU : ∀ v ∈ U, ∀ g i k, Gv (g * ((v : Ga), 1)) i k ∈ Np g := by
    intro v hv g i k
    have h1 : Gv (g * ((v : Ga), 1)) i = ∑ j, (τ' v⁻¹ : Matrix _ _ Ω) i j • Gv g j := by
      rw [hGv, hU v hv]
      simp only [Prod.snd_mul, mul_one, Matrix.mulVec_sum, Matrix.mulVec_smul, hGv]
    rw [h1, Finset.sum_apply]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    refine smulNp g _ ?_ _ (memNp g j k)
    refine ⟨algebraMap A O ((τ v⁻¹ : Matrix _ _ A) i j), ?_⟩
    rw [← IsScalarTower.algebraMap_apply, hτ']
    rfl
  have mvB : ∀ g (b : Gp) (c : Ω), c ∈ (algebraMap O Ω).range →
      (∀ k l, (↑(W.ξ b⁻¹) : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) k l ∈ (algebraMap O Ω).range) →
      (∀ i, F i (g * (1, b)) = c • F i g) → ∀ i k, Gv (g * (1, b)) i k ∈ Np g := by
    intro g b c hc hb hFb i k
    have h1 : Gv (g * (1, b)) i = c • ((↑(W.ξ b⁻¹) : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) *ᵥ Gv g i) := by
      rw [hGv, hGv, hFb]
      simp only [Prod.snd_mul, map_mul, _root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec,
        Matrix.mulVec_smul, map_inv]
    rw [h1, Pi.smul_apply, smul_eq_mul]
    refine smulNp g c hc _ ?_
    simp only [Matrix.mulVec, dotProduct]
    exact Submodule.sum_mem _ fun l _ => smulNp g _ (hb k l) _ (memNp g i l)
  have mvN : ∀ y ∈ X.I.N, ∀ g, Np (g * (1, y)) ≤ Np g := by
    intro y hy g
    refine leNp g _ (mvB g y 1 ⟨1, map_one _⟩ (fun k l => W.int_N y⁻¹ (X.I.N.inv_mem hy) k l) ?_)
    intro i
    rw [hN y hy i g, one_smul]
  have mvNm : ∀ y ∈ X.I.Nm e, ∀ g, Np (g * (1, y)) ≤ Np g := by
    intro y hy g
    refine leNp g _ (mvB g y 1 ⟨1, map_one _⟩
      (fun k l => W.int_Nm y⁻¹ (X.I.Nm_anti he ((X.I.Nm e).inv_mem hy)) k l) ?_)
    intro i
    rw [hNm y hy i g, one_smul]
  have mvT : ∀ t ∈ X.I.T, ∀ g, Np (g * (1, t)) ≤ Np g := by
    intro t ht g
    refine leNp g _ (mvB g t _ ⟨(((φ ⟨t, ht⟩)⁻¹ : Oˣ) : O), ?_⟩
      (fun k l => W.integral_torusCharacter t⁻¹ (X.I.T.inv_mem ht) k l) (fun i => hT ⟨t, ht⟩ i g))
    simp [hφ']
  have mvU' : ∀ v ∈ U, ∀ g, Np (g * ((v : Ga), 1)) ≤ Np g := fun v hv g => leNp g _ (mvU v hv g)
  obtain ⟨R, hRfin, hR⟩ := exists_finite_coset_reps_Nm X.I e
  obtain ⟨s, hs⟩ := hfin
  have cover : ∀ g, ∃ x ∈ s, ∃ r ∈ R, Np g ≤ Np (x * (1, r)) := by
    intro g
    obtain ⟨γ, x, hx, v, hv, b, hb, rfl⟩ := hs g
    obtain ⟨xN, hxN, t, ht, y, hy, hbeq⟩ := iwahori_decomposition_N_T_Nm X.I b⁻¹ ((X.I.Iw 0).inv_mem hb)
    obtain ⟨r, hr, y', hy', hyeq⟩ := hR y⁻¹ ((X.I.Nm 0).inv_mem hy)
    refine ⟨x, hx, r, hr, ?_⟩
    have hb' : b = r * y' * t⁻¹ * xN⁻¹ := by
      rw [← inv_inv b, hbeq, ← hyeq]
      group
    have hg : X.glob γ * x * ((v : Ga), b) =
        X.glob γ * (x * (1, r) * (1, y') * (1, t⁻¹) * (1, xN⁻¹) * ((v : Ga), 1)) := by
      rw [hb']
      simp only [Prod.mk_mul_mk, mul_one, one_mul, mul_assoc]
    rw [hg, hNp (X.glob γ * _), mvG, ← hNp]
    refine (mvU' v hv _).trans ?_
    refine (mvN _ (X.I.N.inv_mem hxN) _).trans ?_
    refine (mvT _ (X.I.T.inv_mem ht) _).trans ?_
    exact mvNm _ hy' _
  obtain ⟨N0, hN0⟩ : ∃ N0 : Submodule O Ω, N0 = Submodule.span O
      (Set.range fun x : (Ga × Gp) × Fin m × Fin (W.d + 1) => Gv x.1 x.2.1 x.2.2) := ⟨_, rfl⟩
  have genN0 : ∀ g i k, Gv g i k ∈ N0 := fun g i k => hN0 ▸ Submodule.subset_span ⟨(g, i, k), rfl⟩
  have hPfin : ((fun p : (Ga × Gp) × Gp => p.1 * (1, p.2)) '' ((s : Set (Ga × Gp)) ×ˢ R)).Finite :=
    (s.finite_toSet.prod hRfin).image _
  have hfg : N0.FG := by
    refine Submodule.fg_def.mpr ⟨(fun x : (Ga × Gp) × Fin m × Fin (W.d + 1) => Gv x.1 x.2.1 x.2.2) ''
      (((fun p : (Ga × Gp) × Gp => p.1 * (1, p.2)) '' ((s : Set (Ga × Gp)) ×ˢ R)) ×ˢ Set.univ),
      (hPfin.prod Set.finite_univ).image _, le_antisymm ?_ ?_⟩
    · rw [hN0]
      exact Submodule.span_mono (by rintro _ ⟨x, -, rfl⟩; exact ⟨x, rfl⟩)
    · rw [hN0]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨⟨g, i, k⟩, rfl⟩
      obtain ⟨x, hx, r, hr, hle⟩ := cover g
      have h1 := hle (memNp g i k)
      rw [hNp] at h1
      refine Submodule.span_mono ?_ h1
      rintro _ ⟨⟨i', k'⟩, rfl⟩
      exact ⟨(x * (1, r), i', k'), ⟨⟨(x, r), ⟨hx, hr⟩, rfl⟩, Set.mem_univ _⟩, rfl⟩
  have hRa : ∀ v i g, (X.raF (W.d + 1) τ' v F) i g =
      ∑ j, (τ' v : Matrix _ _ Ω) i j • F j (g * ((v : Ga), 1)) := by
    intro v i g
    funext k
    simp [Frame.raF, Frame.ra, Matrix.mulVec, dotProduct, Finset.sum_apply]
  have hgen : ∀ g i k, μ * Gv g i k ∈ N0 := by
    intro g i k
    have h0 : μ • F i g = ∑ q, ∑ j, (τ' (u q) : Matrix _ _ Ω) i j • F j (g * (((u q : X.Ub) : Ga), 1)) := by
      have h2 := congrFun (congrFun hμ i) g
      rw [LinearMap.sum_apply, Finset.sum_apply, Finset.sum_apply, Pi.smul_apply, Pi.smul_apply] at h2
      rw [← h2]
      exact Finset.sum_congr rfl (fun q _ => hRa _ _ _)
    have h1 : μ • Gv g i = ∑ q, ∑ j, (τ' (u q) : Matrix _ _ Ω) i j • Gv (g * (((u q : X.Ub) : Ga), 1)) j := by
      rw [hGv, ← Matrix.mulVec_smul, h0]
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, hGv, Prod.snd_mul, mul_one]
    have h3 := congrFun h1 k
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at h3
    rw [h3]
    refine Submodule.sum_mem _ fun q _ => Submodule.sum_mem _ fun j _ => ?_
    have hc : (τ' (u q) : Matrix _ _ Ω) i j = algebraMap O Ω (algebraMap A O ((τ (u q) : Matrix _ _ A) i j)) := by
      rw [← IsScalarTower.algebraMap_apply, hτ']
      rfl
    rw [hc, ← Algebra.smul_def]
    exact N0.smul_mem _ (genN0 _ _ _)
  have hstep : ∀ n ∈ N0, μ • n ∈ N0 := by
    intro n hn
    rw [hN0] at hn
    induction hn using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨g, i, k⟩, rfl⟩ := hx
      exact hgen g i k
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact N0.add_mem hx hy
    | smul o x _ hx => rw [smul_comm]; exact N0.smul_mem o hx
  have hne : N0 ≠ ⊥ := by
    intro hbot
    apply hF0
    funext i g
    have h1 : F i g = (W.ξ g.2 : Matrix _ _ Ω) *ᵥ Gv g i := by
      rw [hGv, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have h2 : Gv g i = 0 := by
      funext k
      have := genN0 g i k
      rw [hbot, Submodule.mem_bot] at this
      exact this
    rw [h1, h2, Matrix.mulVec_zero]
    rfl
  exact isIntegral_of_smul_mem_submodule N0 hne hfg μ hstep

private theorem cl_mono {Ω : Type} [Field Ω] {d m : ℕ} (τ : X.Ub →* GL (Fin m) Ω)
    (ξ : Gp →* GL (Fin d) Ω) {U1 U2 : Subgroup X.Ub} {e1 e2 : ℕ} (φ : X.I.T →* Ωˣ) (hU : U2 ≤ U1)
    (he : e1 ≤ e2) : X.Cl τ ξ U1 e1 φ ≤ X.Cl τ ξ U2 e2 φ := by
  intro F hF
  simp only [Frame.Cl, Submodule.mem_inf] at hF ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := hF
  refine ⟨⟨h1, fun u hu => h2 u (hU hu)⟩, ?_⟩
  exact ⟨h3.1, fun y hy => h3.2.1 y (X.I.Nm_anti he hy), h3.2.2⟩

private theorem ctrl_raF_comm {O Ω : Type} [Field Ω] [CommRing O] [IsLocalRing O] [Algebra O Ω]
    (W : WtRep X.I O Ω) {m : ℕ} (τ : X.Ub →* GL (Fin m) Ω) (u : X.Ub) (F : Fin m → X.Fn Ω (W.d + 1)) :
    X.ctrl m W (X.raF (W.d + 1) τ u F) = X.ra τ u (X.ctrl m W F) := by
  funext g i
  simp only [Frame.ctrl, Frame.raF, Frame.ra, LinearMap.coe_mk, AddHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Prod.snd_mul, mul_one]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

private theorem wtRep_inv_mulVec_zero_eq_chi_inv {O Ω : Type} [Field Ω] [CommRing O] [IsLocalRing O] [Algebra O Ω]
    (W : WtRep X.I O Ω) (x : Gp) (hx : x ∈ X.I.Nf) (t : X.I.Tf) (w : Fin (W.d + 1) → Ω) :
    ((↑((W.ξ (x * t))⁻¹) : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) *ᵥ w) 0 = ↑(W.χ t)⁻¹ * w 0 := by
  have h1 : (W.ξ (x * t))⁻¹ = W.ξ ((t⁻¹ : X.I.Tf) : Gp) * W.ξ x⁻¹ := by
    rw [← map_inv, _root_.mul_inv_rev, map_mul]; rfl
  rw [h1, Units.val_mul, ← Matrix.mulVec_mulVec]
  simp only [Matrix.mulVec, dotProduct]
  simp only [W.torusAction, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [W.row_N _ (X.I.Nf.inv_mem hx), ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp [map_inv]

private theorem ctrl_UF_eq_U_ctrl {O Ω : Type} [Field Ω] [CommRing O] [IsLocalRing O] [Algebra O Ω]
    (W : WtRep X.I O Ω) {m : ℕ} (a : X.I.P) (F : Fin m → X.Fn Ω (W.d + 1)) :
    X.ctrl m W (X.UF m W a F) = X.U Ω m a (X.ctrl m W F) := by
  haveI : ((X.I.Nconj a).subgroupOf X.I.N).FiniteIndex := ⟨X.I.fin_N a a.2⟩
  haveI := Fintype.ofFinite (X.I.N ⧸ (X.I.Nconj a).subgroupOf X.I.N)
  have key : ∀ q : X.I.N ⧸ (X.I.Nconj a).subgroupOf X.I.N,
      X.ctrl m W (X.rpF Ω (W.d + 1) m ((Quotient.out q : X.I.N) * a) F) =
        (W.χ ⟨a, X.I.P_le a a.2⟩ : Ω) • X.rp Ω m ((Quotient.out q : X.I.N) * a) (X.ctrl m W F) := by
    intro q
    funext g i
    have := wtRep_inv_mulVec_zero_eq_chi_inv X W ((Quotient.out q : X.I.N) : Gp) (X.I.N_le (Quotient.out q).2) ⟨a, X.I.P_le a a.2⟩
      ((↑((W.ξ g.2)⁻¹) : Matrix _ _ Ω) *ᵥ F i (g * (1, (Quotient.out q : X.I.N) * (a : Gp))))
    simp only [Frame.ctrl, Frame.rpF, Frame.rp, rtr, LinearMap.coe_mk, AddHom.coe_mk, MonoidHom.coe_comp,
      MonoidHom.coe_mk, OneHom.coe_mk, Function.comp_apply, LinearMap.compLeft, LinearMap.funLeft,
      Pi.smul_apply, smul_eq_mul, MonoidHom.inr_apply] at this ⊢
    rw [Prod.snd_mul, map_mul, _root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, this]
    simp [mul_inv_cancel_left₀]
  simp only [Frame.UF, Frame.U, Iwa.uOp, finsum_eq_sum_of_fintype, LinearMap.smul_apply, map_smul,
    LinearMap.sum_apply, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [key q, smul_smul]
  simp

private theorem raF_rpF_comm {Ω : Type} [Field Ω] (d : ℕ) {m : ℕ} (τ : X.Ub →* GL (Fin m) Ω) (u : X.Ub)
    (b : Gp) (F : Fin m → X.Fn Ω d) :
    X.raF d τ u (X.rpF Ω d m b F) = X.rpF Ω d m b (X.raF d τ u F) := by
  funext i g k
  simp [Frame.raF, Frame.rpF, Frame.ra, Frame.rp, rtr, Matrix.mulVec, dotProduct, mul_assoc]

private theorem mapFn_of_mem_P {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {m : ℕ} (a : Gp)
    (ha : a ∈ X.I.P) (f : X.Fn A m) : X.mapFn (B := B) (X.U A m a f) = X.U B m a (X.mapFn f) := by
  unfold Frame.U
  exact uOpNat Gp X.I A (X.Fn A m) (X.rp A m) B (X.Fn B m) (X.rp B m) (X.mapFn (B := B)).toAddMonoidHom a ha f
    (fun u _ => by funext g i; simp [Frame.mapFn, Frame.rp, rtr])

private theorem UF_comm_on_N_fixed {O Ω : Type} [Field Ω] [CommRing O] [IsLocalRing O] [Algebra O Ω]
    (W : WtRep X.I O Ω) {m : ℕ} (a b : X.I.P) (F : Fin m → X.Fn Ω (W.d + 1))
    (hF : F ∈ fixd (X.rpF Ω (W.d + 1) m) X.I.N) :
    X.UF m W a (X.UF m W b F) = X.UF m W b (X.UF m W a F) := by
  have h1 := (uOpMul Gp X.I Ω _ (X.rpF Ω (W.d + 1) m) a b a.2 b.2 F hF).2.1
  have h2 := (uOpMul Gp X.I Ω _ (X.rpF Ω (W.d + 1) m) b a b.2 a.2 F hF).2.1
  have hc : (a : Gp) * b = b * a := X.I.comm _ (X.I.P_le a a.2) _ (X.I.P_le b b.2)
  simp only [Frame.UF, LinearMap.smul_apply, map_smul, smul_smul]
  rw [h1, h2, hc, mul_comm]

private theorem UF_maps_clOrd_of_maps_cl {O Ω : Type} [Field Ω] [CommRing O] [IsLocalRing O] [Algebra O Ω]
    (W : WtRep X.I O Ω) {m : ℕ} (τ : X.Ub →* GL (Fin m) Ω) (U : Subgroup X.Ub) (e : ℕ) (φ : X.I.T →* Ωˣ)
    (hCl : ∀ a : X.I.P, ∀ F ∈ X.Cl τ W.ξ U e φ, X.UF m W a F ∈ X.Cl τ W.ξ U e φ) (a : X.I.P) :
    ∀ F ∈ X.ClOrd W τ U e φ, X.UF m W a F ∈ X.ClOrd W τ U e φ := by
  have hN : ∀ F ∈ X.Cl τ W.ξ U e φ, F ∈ fixd (X.rpF Ω (W.d + 1) m) X.I.N := fun F hF => hF.2.1
  intro F hF
  induction hF using Submodule.iSup_induction' with
  | mem μ x hx =>
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
    refine Submodule.mem_iSup_of_mem μ (Submodule.mem_inf.mpr ⟨hCl a x hx1, ?_⟩)
    rw [Module.End.mem_maxGenEigenspace] at hx2 ⊢
    obtain ⟨k, hk⟩ := hx2
    refine ⟨k, ?_⟩
    have key : ∀ n : ℕ, ∀ y ∈ X.Cl τ W.ξ U e φ,
        ((X.UF m W ⟨X.I.z, X.I.z_mem⟩ - (μ : Ω) • 1) ^ n) (X.UF m W a y) =
          X.UF m W a (((X.UF m W ⟨X.I.z, X.I.z_mem⟩ - (μ : Ω) • 1) ^ n) y) := by
      intro n
      induction n with
      | zero => intro y _; simp
      | succ n ih =>
        intro y hy
        rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply]
        have hy' : (X.UF m W ⟨X.I.z, X.I.z_mem⟩ - (μ : Ω) • 1) y ∈ X.Cl τ W.ξ U e φ := by
          simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
          exact Submodule.sub_mem _ (hCl _ y hy) (Submodule.smul_mem _ _ hy)
        rw [← ih _ hy']
        congr 1
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul]
        rw [UF_comm_on_N_fixed X W _ _ y (hN y hy)]
    rw [key k x hx1, hk, map_zero]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

private theorem sum_raF_rpF_comm {Ω : Type} [Field Ω] (d : ℕ) {m : ℕ} (τ : X.Ub →* GL (Fin m) Ω)
    (κ : Type) [Fintype κ] (u : κ → X.Ub) (b : Gp) (F : Fin m → X.Fn Ω d) :
    (∑ q, X.raF d τ (u q)) (X.rpF Ω d m b F) = X.rpF Ω d m b ((∑ q, X.raF d τ (u q)) F) := by
  simp only [LinearMap.sum_apply, map_sum, raF_rpF_comm]

private theorem raF_mem_pi_AF {Ω : Type} [Field Ω] {d m : ℕ} (τ : X.Ub →* GL (Fin m) Ω)
    (ξ : Gp →* GL (Fin d) Ω) (u : X.Ub) (F : Fin m → X.Fn Ω d)
    (hF : F ∈ Submodule.pi Set.univ fun _ => X.AF ξ) :
    X.raF d τ u F ∈ Submodule.pi Set.univ fun _ => X.AF ξ := by
  intro i _ γ g
  have h := fun j => hF j (Set.mem_univ j) γ (g * ((u : Ga), (1 : Gp)))
  funext k
  simp only [Frame.raF, Frame.ra, LinearMap.coe_mk, AddHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk] at h ⊢
  simp only [Matrix.mulVec, dotProduct, mul_assoc] at h ⊢
  simp only [h]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

private theorem sum_raF_maps_clOrd_of_maps_fixd {O Ω : Type} [Field Ω] [CommRing O] [IsLocalRing O] [Algebra O Ω]
    (W : WtRep X.I O Ω) {m : ℕ} (τ : X.Ub →* GL (Fin m) Ω) (U U' : Subgroup X.Ub) (e : ℕ) (φ : X.I.T →* Ωˣ)
    (κ : Type) [Fintype κ] (u : κ → X.Ub)
    (hS : ∀ F ∈ fixd (X.raF (W.d + 1) τ) U, (∑ q, X.raF (W.d + 1) τ (u q)) F ∈ fixd (X.raF (W.d + 1) τ) U') :
    ∀ F ∈ X.ClOrd W τ U e φ, (∑ q, X.raF (W.d + 1) τ (u q)) F ∈ X.ClOrd W τ U' e φ := by
  set S := ∑ q, X.raF (W.d + 1) τ (u q) with hSe
  have hcomm : ∀ b F, S (X.rpF Ω (W.d + 1) m b F) = X.rpF Ω (W.d + 1) m b (S F) :=
    fun b F => sum_raF_rpF_comm X (W.d + 1) τ κ u b F
  have hCl : ∀ F ∈ X.Cl τ W.ξ U e φ, S F ∈ X.Cl τ W.ξ U' e φ := by
    intro F hF
    simp only [Frame.Cl, Submodule.mem_inf] at hF ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hF
    refine ⟨⟨?_, hS F h2⟩, ?_⟩
    · rw [hSe, LinearMap.sum_apply]
      exact Submodule.sum_mem _ fun q _ => raF_mem_pi_AF X τ W.ξ (u q) F h1
    · refine ⟨fun y hy => ?_, fun y hy => ?_, fun t => ?_⟩
      · rw [← hcomm, h3.1 y hy]
      · rw [← hcomm, h3.2.1 y hy]
      · rw [← hcomm, h3.2.2 t, map_smul]
  have hUF : Commute (X.UF m W ⟨X.I.z, X.I.z_mem⟩) S := by
    refine LinearMap.ext fun F => ?_
    simp only [Module.End.mul_apply, Frame.UF, LinearMap.smul_apply, map_smul]
    congr 1
    exact (uOpNat Gp X.I Ω _ (X.rpF Ω (W.d + 1) m) Ω _ (X.rpF Ω (W.d + 1) m) S.toAddMonoidHom X.I.z X.I.z_mem F
      (fun v _ => hcomm _ F)).symm
  intro F hF
  induction hF using Submodule.iSup_induction' with
  | mem μ x hx =>
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
    exact Submodule.mem_iSup_of_mem μ (Submodule.mem_inf.mpr
      ⟨hCl x hx1, Module.End.mapsTo_maxGenEigenspace_of_comm hUF μ hx2⟩)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

theorem absSpec {A O Ω : Type} [CommRing A] [IsCNL A] [CommRing O] [IsDomain O] [IsCNL O] [Field Ω] [IsAlgClosed Ω]
    [Algebra A O] [Algebra O Ω] [Algebra A Ω] [IsScalarTower A O Ω] [IsLocalHom (algebraMap A O)]
    (hinj : Function.Injective (algebraMap O Ω)) (W : WtRep X.I O Ω) {m : ℕ} (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ)
    (hθ : X.I.ContChar θ) (φ : X.I.T →* Oˣ) (c : ℕ) (hc : W.c0 ≤ c) (hφ : ∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c → φ t = 1)
    (hχ : ∀ t : X.I.T, algebraMap A Ω (θ t) = algebraMap O Ω (φ t) * W.χ ⟨t, X.I.T_le t.2⟩)
    {Λ : Type} (U : Λ → Subgroup X.Ub) (hdir : ∀ a b, ∃ k, U k ≤ U a ∧ U k ≤ U b) (hfin : ∀ a, X.FinLevel (U a))
    (hfree : ∀ a, X.Free τ θ (U a)) (τ' : X.Ub →* GL (Fin m) Ω)
    (hτ' : τ' = (Matrix.GeneralLinearGroup.map (algebraMap A Ω)).comp τ) (φ' : X.I.T →* Ωˣ)
    (hφ' : φ' = (Units.map (algebraMap O Ω).toMonoidHom).comp φ) :
    (∀ K e, c ≤ e → FiniteDimensional Ω (X.Cl τ' W.ξ (U K) e φ') ∧
      (∀ a : X.I.P, (∀ F ∈ X.Cl τ' W.ξ (U K) e φ', X.UF m W a F ∈ X.Cl τ' W.ξ (U K) e φ') ∧
        ∀ F ∈ X.Cl τ' W.ξ (U K) e φ', F ≠ 0 → ∀ μ : Ω, X.UF m W a F = μ • F → IsIntegral O μ) ∧
      ∀ (κ : Type) [Fintype κ] (u : κ → X.Ub), ∀ F ∈ X.Cl τ' W.ξ (U K) e φ', F ≠ 0 → ∀ μ : Ω,
        (∑ q, X.raF (W.d + 1) τ' (u q)) F = μ • F → IsIntegral O μ) ∧
    ∃ sp : X.Fn A m → Fin m → X.Fn Ω (W.d + 1),
      (∀ K, ∀ f ∈ X.Ord τ θ (U K), ∀ f' ∈ X.Ord τ θ (U K), sp (f + f') = sp f + sp f') ∧
      (∀ K, ∀ f ∈ X.Ord τ θ (U K), ∀ b : A, sp (b • f) = algebraMap A Ω b • sp f) ∧
      (∀ K e, c ≤ e → Submodule.span Ω (sp '' X.Ord τ θ (U K)) = X.ClOrd W τ' (U K) e φ') ∧
      (∀ K (κ : Type) (b : Module.Basis κ A (X.Ord τ θ (U K))), LinearIndependent Ω fun i => sp (b i)) ∧
      (∀ K (a : X.I.P), ∀ f ∈ X.Ord τ θ (U K), sp (X.U A m a f) = X.UF m W a (sp f)) ∧
      ∀ K K' (κ : Type) [Fintype κ] (u : κ → X.Ub),
        (∀ F ∈ fixd (X.raF (W.d + 1) τ') (U K), (∑ q, X.raF (W.d + 1) τ' (u q)) F ∈ fixd (X.raF (W.d + 1) τ') (U K')) →
        ∀ f ∈ X.Ord τ θ (U K), sp ((∑ q, X.ra τ (u q)) f) = (∑ q, X.raF (W.d + 1) τ' (u q)) (sp f) := by
  subst hτ' hφ'
  classical
  set τ' := (Matrix.GeneralLinearGroup.map (algebraMap A Ω)).comp τ with hτ'e
  set φ' := (Units.map (algebraMap O Ω).toMonoidHom).comp φ with hφ'e
  set τO : X.Ub →* GL (Fin m) O := (Matrix.GeneralLinearGroup.map (algebraMap A O)).comp τ with hτO
  set θO : X.I.T →* Oˣ := (Units.map (algebraMap A O).toMonoidHom).comp θ with hθO
  have hτ'' : τ' = (Matrix.GeneralLinearGroup.map (algebraMap O Ω)).comp τO := by
    ext u i j
    simp [τ', τO, IsScalarTower.algebraMap_apply A O Ω]
  have hχO : ∀ t : X.I.T, algebraMap O Ω (θO t) = algebraMap O Ω (φ t) * W.χ ⟨t, X.I.T_le t.2⟩ := by
    intro t
    rw [← hχ t]
    simp [θO, IsScalarTower.algebraMap_apply A O Ω]
  have hφe : ∀ e, c ≤ e → ∀ t : X.I.T, (t : Gp) ∈ X.I.Tc e → φ t = 1 :=
    fun e he t ht => hφ t (X.I.Tc_anti he ht)
  have hfreeO : ∀ a, X.Free τO θO (U a) := fun a => free_map X (algebraMap A O) τ θ (U a) (hfree a)
  have hCF : ∀ K e, c ≤ e → FiniteDimensional Ω (X.Cl τ' W.ξ (U K) e φ') ∧
      ∀ a : X.I.P, (∀ F ∈ X.Cl τ' W.ξ (U K) e φ', X.UF m W a F ∈ X.Cl τ' W.ξ (U K) e φ') ∧
        ∀ F ∈ X.Cl τ' W.ξ (U K) e φ', F ≠ 0 → ∀ μ : Ω, X.UF m W a F = μ • F → IsIntegral O μ := by
    intro K e he
    rw [hτ'']
    exact clFin Γ Ga Gp X O Ω hinj W m τO θO φ e (hc.trans he) (hφe e he) hχO (U K) (hfin K) (hfreeO K)
  have hCO : ∀ K e, c ≤ e → (∀ F ∈ X.ClOrd W τ' (U K) e φ', X.ctrl m W F = 0 → F = 0) ∧
      Submodule.map (X.ctrl m W) (X.ClOrd W τ' (U K) e φ') =
        Submodule.span Ω (X.mapFn (B := Ω) '' (X.Ord τO θO (U K) : Set (X.Fn O m))) := by
    intro K e he
    rw [hτ'']
    exact ctrlOrd Γ Ga Gp X O Ω hinj W m τO θO φ e (hc.trans he) (hφe e he) hχO (U K) (hfin K) (hfreeO K)
  have hBC := fun K => ordBC Γ Ga Gp X A m τ θ hθ O (U K) (hfin K) (hfree K)
  have hmap2 : ∀ f : X.Fn A m, X.mapFn (B := Ω) (X.mapFn (B := O) f) = X.mapFn (B := Ω) f := by
    intro f
    funext g i
    simp [Frame.mapFn, IsScalarTower.algebraMap_apply A O Ω]
  have hClOmono : ∀ {U1 U2 : Subgroup X.Ub} {e1 e2 : ℕ}, U2 ≤ U1 → e1 ≤ e2 →
      X.ClOrd W τ' U1 e1 φ' ≤ X.ClOrd W τ' U2 e2 φ' :=
    fun hU he => iSup_mono fun μ => inf_le_inf_right _ (cl_mono X τ' W.ξ φ' hU he)
  let Good : (Fin m → X.Fn Ω (W.d + 1)) → X.Fn A m → Prop := fun F f =>
    (∃ K e, c ≤ e ∧ F ∈ X.ClOrd W τ' (U K) e φ') ∧ X.ctrl m W F = X.mapFn (B := Ω) f
  have huniq : ∀ F1 F2 f, Good F1 f → Good F2 f → F1 = F2 := by
    rintro F1 F2 f ⟨⟨K1, e1, he1, h1⟩, hc1⟩ ⟨⟨K2, e2, he2, h2⟩, hc2⟩
    obtain ⟨k, hk1, hk2⟩ := hdir K1 K2
    have m1 := hClOmono hk1 (le_max_left e1 e2) h1
    have m2 := hClOmono hk2 (le_max_right e1 e2) h2
    have h0 := (hCO k (max e1 e2) (he1.trans (le_max_left _ _))).1 (F1 - F2) (Submodule.sub_mem _ m1 m2)
      (by rw [map_sub, hc1, hc2, sub_self])
    exact sub_eq_zero.mp h0
  have hex : ∀ K e, c ≤ e → ∀ f ∈ X.Ord τ θ (U K),
      ∃ F ∈ X.ClOrd W τ' (U K) e φ', X.ctrl m W F = X.mapFn (B := Ω) f := by
    intro K e he f hf
    obtain ⟨j, hj, -⟩ := hBC K
    have h1 : X.mapFn (B := Ω) f ∈ Submodule.map (X.ctrl m W) (X.ClOrd W τ' (U K) e φ') := by
      rw [(hCO K e he).2]
      refine Submodule.subset_span ⟨(j ⟨f, hf⟩ : X.Fn O m), (j ⟨f, hf⟩).2, ?_⟩
      rw [hj]
      exact hmap2 f
    obtain ⟨F, hF, hFe⟩ := h1
    exact ⟨F, hF, hFe⟩
  let sp : X.Fn A m → Fin m → X.Fn Ω (W.d + 1) := fun f => if h : ∃ F, Good F f then h.choose else 0
  have hsp : ∀ F f, Good F f → sp f = F := by
    intro F f hG
    have h : ∃ F, Good F f := ⟨F, hG⟩
    simp only [sp, dif_pos h]
    exact huniq _ _ _ h.choose_spec hG
  have hspec : ∀ K e, c ≤ e → ∀ f ∈ X.Ord τ θ (U K),
      sp f ∈ X.ClOrd W τ' (U K) e φ' ∧ X.ctrl m W (sp f) = X.mapFn (B := Ω) f := by
    intro K e he f hf
    obtain ⟨F, hF, hFe⟩ := hex K e he f hf
    rw [hsp F f ⟨⟨K, e, he, hF⟩, hFe⟩]
    exact ⟨hF, hFe⟩
  refine ⟨?_, sp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro K e he
    obtain ⟨hfd, hUF⟩ := hCF K e he
    refine ⟨hfd, fun a => hUF a, ?_⟩
    intro κ _ u F hF hF0 μ hμ
    exact hecke_eigenvalue_isIntegral X W τ φ (U K) (hfin K) e (hc.trans he) F hF hF0 κ u μ hμ
  · intro K f hf f' hf'
    obtain ⟨h1, h2⟩ := hspec K c le_rfl f hf
    obtain ⟨h1', h2'⟩ := hspec K c le_rfl f' hf'
    exact hsp _ _ ⟨⟨K, c, le_rfl, Submodule.add_mem _ h1 h1'⟩, by rw [map_add, h2, h2', map_add]⟩
  · intro K f hf b
    obtain ⟨h1, h2⟩ := hspec K c le_rfl f hf
    exact hsp _ _ ⟨⟨K, c, le_rfl, Submodule.smul_mem _ _ h1⟩, by rw [map_smul, h2, map_smul, algebraMap_smul]⟩
  · intro K e he
    have hle : Submodule.span Ω (sp '' X.Ord τ θ (U K)) ≤ X.ClOrd W τ' (U K) e φ' := by
      rw [Submodule.span_le]
      rintro _ ⟨f, hf, rfl⟩
      exact (hspec K e he f hf).1
    refine le_antisymm hle ?_
    intro F hF
    obtain ⟨j, hj, hbc⟩ := hBC K
    have hsub : Submodule.span Ω (X.mapFn (B := Ω) '' (X.Ord τO θO (U K) : Set (X.Fn O m))) ≤
        Submodule.map (X.ctrl m W) (Submodule.span Ω (sp '' X.Ord τ θ (U K))) := by
      rw [Submodule.span_le]
      rintro _ ⟨g, hg, rfl⟩
      refine hbc.inductionOn (⟨g, hg⟩ : X.Ord τO θO (U K))
        (fun n => X.mapFn (B := Ω) (n : X.Fn O m) ∈
          Submodule.map (X.ctrl m W) (Submodule.span Ω (sp '' X.Ord τ θ (U K)))) ?_ ?_ ?_ ?_
      · simp
      · intro f
        refine ⟨sp f, Submodule.subset_span ⟨f, f.2, rfl⟩, ?_⟩
        rw [(hspec K c le_rfl f f.2).2, hj, hmap2]
      · intro s n hn
        rw [Submodule.coe_smul, map_smul, ← algebraMap_smul Ω s]
        exact Submodule.smul_mem _ _ hn
      · intro n1 n2 h1 h2
        rw [Submodule.coe_add, map_add]
        exact Submodule.add_mem _ h1 h2
    have h1 : X.ctrl m W F ∈ Submodule.map (X.ctrl m W) (X.ClOrd W τ' (U K) e φ') := ⟨F, hF, rfl⟩
    rw [(hCO K e he).2] at h1
    obtain ⟨F0, hF0, hF0e⟩ := hsub h1
    have h0 := (hCO K e he).1 (F - F0) (Submodule.sub_mem _ hF (hle hF0)) (by rw [map_sub, hF0e, sub_self])
    rw [sub_eq_zero.mp h0]
    exact hF0
  · intro K κ b
    obtain ⟨j, hj, hbc⟩ := hBC K
    have hv : LinearIndependent O (fun i => ((j (b i) : X.Ord τO θO (U K)) : X.Fn O m)) := by
      have hfun : (fun i => ((j (b i) : X.Ord τO θO (U K)) : X.Fn O m)) =
          (X.Ord τO θO (U K)).subtype ∘ (hbc.basis b) := by
        funext i
        simp only [Function.comp_apply, IsBaseChange.basis_apply, Submodule.subtype_apply]
      rw [hfun]
      exact (hbc.basis b).linearIndependent.map' (X.Ord τO θO (U K)).subtype (Submodule.ker_subtype _)
    have hw := fnIndep O Ω (Ga × Gp) κ hinj m _ hv
    refine LinearIndependent.of_comp (X.ctrl m W) ?_
    convert hw using 1
    funext i
    simp only [Function.comp_apply, (hspec K c le_rfl _ (b i).2).2]
    rw [← hmap2]
    simp only [hj]
    rfl
  · intro K a f hf
    obtain ⟨h1, h2⟩ := hspec K c le_rfl f hf
    refine hsp _ _ ⟨⟨K, c, le_rfl, UF_maps_clOrd_of_maps_cl X W τ' (U K) c φ' (fun a => ((hCF K c le_rfl).2 a).1) a _ h1⟩, ?_⟩
    rw [ctrl_UF_eq_U_ctrl, h2, mapFn_of_mem_P X (a : Gp) a.2]
  · intro K K' κ _ u hS f hf
    obtain ⟨h1, h2⟩ := hspec K c le_rfl f hf
    refine hsp _ _ ⟨⟨K', c, le_rfl, sum_raF_maps_clOrd_of_maps_fixd X W τ' (U K) (U K') c φ' κ u hS _ h1⟩, ?_⟩
    rw [LinearMap.sum_apply, map_sum, LinearMap.sum_apply, map_sum]
    simp only [ctrl_raF_comm, h2, mapFn_ra]
    all_goals rfl

end UpperTheory.V.Hi.Sp
