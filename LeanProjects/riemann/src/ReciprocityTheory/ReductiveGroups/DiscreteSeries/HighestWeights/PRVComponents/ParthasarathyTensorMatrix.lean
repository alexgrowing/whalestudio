import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PRVComponents.TensorActionLieRelations

noncomputable section

open Matrix Finset

open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 Formalism.REAL

variable {n : ℕ} {ε : Fin n → Bool}

section Graph

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [FiniteDimensional ℂ P]
  {M : Type*} [AddCommGroup M] [Module ℂ M]

def prodEndomorphismFamily (E : Fin n → Fin n → Module.End ℂ P) (F : Fin n → Fin n → Module.End ℂ M) :
    Fin n → Fin n → Module.End ℂ (P × M) :=
  fun a b => LinearMap.prodMap (E a b) (F a b)

lemma product_action_apply (E : Fin n → Fin n → Module.End ℂ P) (F : Fin n → Fin n → Module.End ℂ M) (a b : Fin n)
    (y : P × M) : prodEndomorphismFamily E F a b y = (E a b y.1, F a b y.2) := rfl

lemma product_action_lie_relations {E : Fin n → Fin n → Module.End ℂ P} {F : Fin n → Fin n → Module.End ℂ M}
    (hE : KRel ε E) (hF : KRel ε F) : KRel ε (prodEndomorphismFamily E F) := by
  intro a b c d h1 h2
  apply LinearMap.ext
  intro y
  have hE' := LinearMap.congr_fun (hE a b c d h1 h2) y.1
  have hF' := LinearMap.congr_fun (hF a b c d h1 h2) y.2
  refine Prod.ext ?_ ?_
  · split_ifs at hE' ⊢ <;> simpa [product_action_apply] using hE'
  · split_ifs at hF' ⊢ <;> simpa [product_action_apply] using hF'

theorem highest_weight_graph_submodule {E : Fin n → Fin n → Module.End ℂ P} {F : Fin n → Fin n → Module.End ℂ M}
    (hE : KRel ε E) (hEu : KUnit ε E) (hF : KRel ε F) {Λ : Fin n → ℝ} {V : Submodule ℂ M}
    (hV : IsKIrrHW ε F Λ V) {x0 : P} (hx0 : KHighest ε E Λ x0) (hx00 : x0 ≠ 0) {w : M} (hwV : w ∈ V)
    (hw0 : w ≠ 0) (hw : IsKHWVec ε F Λ w) :
    ∃ Γ : Submodule ℂ (P × M), (∀ a b, ε a = ε b → ∀ y ∈ Γ, prodEndomorphismFamily E F a b y ∈ Γ) ∧
      (∀ y : P, ∃ v, (y, v) ∈ Γ) ∧ (∀ v, ((0 : P), v) ∈ Γ → v = 0) ∧ (∀ y ∈ Γ, y.2 ∈ V) ∧ (x0, w) ∈ Γ := by
  classical
  have hQ : KRel ε (prodEndomorphismFamily E F) := product_action_lie_relations hE hF
  set Z := kSpan ε E x0 with hZ
  set Γ0 := kSpan ε (prodEndomorphismFamily E F) (x0, w) with hΓ0def
  have hZst : KStable ε E Z := uq_kSpan_stable ε E x0
  have hZo : KStable ε E Zᗮ := by
    intro a b hab y hy
    rw [Submodule.mem_orthogonal] at hy ⊢
    intro u hu
    rw [← hEu b a hab.symm u y]
    exact hy _ (hZst b a hab.symm u hu)
  have hΓ0st : KStable ε (prodEndomorphismFamily E F) Γ0 := uq_kSpan_stable ε _ _
  have hΓ0 : Γ0 ≤ Z.prod V := by
    refine uq_kSpan_le ε _ (Submodule.mem_prod.2 ⟨uq_mem_kSpan ε E x0, hwV⟩) ?_
    intro a b hab y hy
    rw [Submodule.mem_prod] at hy ⊢
    exact ⟨hZst a b hab _ hy.1, hV.2.1 a b hab _ hy.2⟩
  have hfst : ∀ z ∈ Z, ∃ v, (z, v) ∈ Γ0 := by
    intro z hz
    have hle : Z ≤ Γ0.map (LinearMap.fst ℂ P M) := by
      refine uq_kSpan_le ε E (Submodule.mem_map.2 ⟨(x0, w), uq_mem_kSpan ε _ _, rfl⟩) ?_
      intro a b hab u hu
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hu
      exact Submodule.mem_map.2 ⟨prodEndomorphismFamily E F a b y, hΓ0st a b hab y hy, rfl⟩
    obtain ⟨y, hy, hyz⟩ := Submodule.mem_map.1 (hle hz)
    refine ⟨y.2, ?_⟩
    rw [← hyz]
    exact hy
  have hN : ∀ v, ((0 : P), v) ∈ Γ0 → v = 0 := by
    set N := Γ0.comap (LinearMap.inr ℂ P M) with hNdef
    have hNV : N ≤ V := fun v hv => (Submodule.mem_prod.1 (hΓ0 hv)).2
    have hNst : IsKStableSub ε F N := by
      intro a b hab v hv
      have h1 := hΓ0st a b hab _ hv
      rw [Submodule.mem_comap]
      simpa [product_action_apply] using h1
    rcases hV.2.2.1 N hNV hNst with h | h
    · intro v hv
      have hvN : v ∈ N := hv
      rw [h] at hvN
      exact (Submodule.mem_bot ℂ).1 hvN
    · exfalso
      have hwN : w ∈ N := h ▸ hwV
      have hkh : KHighest ε (prodEndomorphismFamily E F) Λ (x0, w) :=
        ⟨fun a => Prod.ext (hx0.1 a) (hw.1 a), fun a b hab he => Prod.ext (hx0.2 a b hab he) (hw.2 a b hab he)⟩
      have hwt : IsWeight (prodEndomorphismFamily E F) Λ ((0 : P), w) := fun a => Prod.ext (by simp [product_action_apply]) (hw.1 a)
      have hmem : ((0 : P), w) ∈ lowSpan ε (prodEndomorphismFamily E F) (x0, w) := by
        rw [← compact_span_eq_lowering hQ hkh]
        exact hwN
      obtain ⟨c, hc⟩ := lowering_span_weight_scalar hQ hkh hmem hwt
      have h1 : c • x0 = 0 := (congrArg Prod.fst hc).symm
      have hc0 : c = 0 := (smul_eq_zero.1 h1).resolve_right hx00
      have h2 : w = c • w := congrArg Prod.snd hc
      rw [hc0, zero_smul] at h2
      exact hw0 h2
  refine ⟨Γ0 ⊔ Zᗮ.prod ⊥, ?_, ?_, ?_, ?_, Submodule.mem_sup_left (uq_mem_kSpan ε _ _)⟩
  · intro a b hab y hy
    obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.1 hy
    rw [map_add]
    refine Submodule.add_mem_sup (hΓ0st a b hab y1 hy1) ?_
    rw [Submodule.mem_prod] at hy2 ⊢
    refine ⟨hZo a b hab _ hy2.1, ?_⟩
    show F a b y2.2 ∈ (⊥ : Submodule ℂ M)
    rw [(Submodule.mem_bot ℂ).1 hy2.2, map_zero]
    exact Submodule.zero_mem _
  · intro y
    have htop : Z ⊔ Zᗮ = ⊤ := Submodule.sup_orthogonal_of_hasOrthogonalProjection
    have hy : y ∈ Z ⊔ Zᗮ := htop ▸ Submodule.mem_top
    obtain ⟨z, hz, z', hz', rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨v, hv⟩ := hfst z hz
    refine ⟨v + 0, ?_⟩
    have : ((z + z' : P), v + 0) = (z, v) + (z', 0) := rfl
    rw [this]
    exact Submodule.add_mem_sup hv (Submodule.mem_prod.2 ⟨hz', Submodule.zero_mem _⟩)
  · intro v hv
    obtain ⟨γ, hγ, ζ, hζ, hsum⟩ := Submodule.mem_sup.1 hv
    have hζ' := Submodule.mem_prod.1 hζ
    have hζ2 : ζ.2 = 0 := (Submodule.mem_bot ℂ).1 hζ'.2
    have h1 : γ.1 + ζ.1 = 0 := congrArg Prod.fst hsum
    have h2 : γ.2 + ζ.2 = v := congrArg Prod.snd hsum
    have hγZ : γ.1 ∈ Z := (Submodule.mem_prod.1 (hΓ0 hγ)).1
    have hγZo : γ.1 ∈ Zᗮ := by
      have : γ.1 = -ζ.1 := eq_neg_of_add_eq_zero_left h1
      rw [this]
      exact Zᗮ.neg_mem hζ'.1
    have hγ0 : γ.1 = 0 := by
      have : γ.1 ∈ Z ⊓ Zᗮ := ⟨hγZ, hγZo⟩
      rw [Submodule.inf_orthogonal_eq_bot] at this
      exact (Submodule.mem_bot ℂ).1 this
    have hγ' : ((0 : P), γ.2) ∈ Γ0 := by
      have : ((0 : P), γ.2) = γ := Prod.ext hγ0.symm rfl
      rw [this]
      exact hγ
    rw [← h2, hN _ hγ', hζ2, add_zero]
  · intro y hy
    have hle : Γ0 ⊔ Zᗮ.prod ⊥ ≤ (⊤ : Submodule ℂ P).prod V :=
      sup_le (hΓ0.trans (Submodule.prod_mono le_top le_rfl)) (Submodule.prod_mono le_top bot_le)
    exact (Submodule.mem_prod.1 (hle hy)).2

end Graph

theorem parthasarathy_tensor_matrix_alt (ε : Fin n → Bool) {M : Type*} [AddCommGroup M] [Module ℂ M]
    {F : Fin n → Fin n → Module.End ℂ M} (hF : Formalism.REAL.KRel ε F)
    {Λ : Fin n → ℝ} {V : Submodule ℂ M} (hV : IsKIrrHW ε F Λ V)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Fin n → Fin n → Matrix ι ι ℂ} (hG : Formalism.REAL.KRel ε G)
    (hGu : ∀ a b, ε a = ε b → G b a = (G a b)ᴴ)
    {ν : Fin n → ℝ} {f : ι → ℂ} (hf0 : f ≠ 0) (hfw : ∀ a, G a a *ᵥ f = ((ν a : ℝ) : ℂ) • f)
    (hfl : ∀ a b, b < a → ε a = ε b → G a b *ᵥ f = 0)
    (hdom : ∀ a b, a < b → ε a = ε b → (Λ + ν) b ≤ (Λ + ν) a) :
    ∃ x : ι → M, (∀ i, x i ∈ V) ∧ x ≠ 0 ∧
      (∀ a i, F a a (x i) + ∑ j, G a a i j • x j = (((Λ + ν) a : ℝ) : ℂ) • x i) ∧
      ∀ a b, a < b → ε a = ε b → ∀ i, F a b (x i) + ∑ j, G a b i j • x j = 0 := by
  classical
  obtain ⟨w, hwV, hw0, hw⟩ := hV.2.2.2
  have : FiniteDimensional ℂ V := hV.1
  have hint := block_weights_integral hF V hV.2.1 hwV hw0 hw hG hf0 hfw hfl
  set μ : Fin n → ℝ := Λ + ν with hμ
  set t : Fin n → ℝ := fun a => Int.fract (μ a) with htdef
  have ht : ∀ a b, ε a = ε b → t a = t b := fun a b h => Int.fract_eq_fract.2 (hint a b h)
  obtain ⟨T⟩ := kType_exists_of_dom ε (fun a => ((⌊μ a⌋ : ℤ) : ℝ)) (fun a => ⟨⌊μ a⌋, rfl⟩)
    (fun a b hab he => by exact_mod_cast Int.floor_le_floor (hdom a b hab he))
  set A := endomorphismFamilyShift (kunits T) t with hAdef
  have hA : KRel ε A := ext1Shift_kRel (KType.kRel T) ht
  have hAu : KUnit ε A := ext1Shift_kUnit (KType.kUnit T) t
  have hp : KHighest ε A μ T.w := by
    have h := ext1Shift_kHighest (t := t) (KType.kHighest_w T)
    have e : (fun a => ((⌊μ a⌋ : ℤ) : ℝ)) + t = μ := by
      funext a
      simp [htdef, Int.floor_add_fract]
    rwa [e] at h
  set D := matrixFamilyDual G with hDdef
  set g : ι → ℂ := star f with hgdef
  have hgw : ∀ a, D a a *ᵥ g = (((-ν) a : ℝ) : ℂ) • g := by
    intro a
    rw [hDdef, hgdef, ext1Dual_mulVec_star hGu rfl, hfw a]
    ext i
    simp
  have hgh : ∀ a b, a < b → ε a = ε b → D a b *ᵥ g = 0 := by
    intro a b hab he
    rw [hDdef, hgdef, ext1Dual_mulVec_star hGu he, hfl b a hab he.symm]
    simp
  set x0 : PiLp 2 (fun _ : ι => T.V) := WithLp.toLp 2 (fun i => g i • T.w) with hx0def
  have hx0 : KHighest ε (tensAct A D) Λ x0 := by
    have h := tensor_pure_highest_weight (ε := ε) (A := A) (D := D) hp hgw hgh
    have e : μ + -ν = Λ := by rw [hμ]; abel
    rwa [e] at h
  have hx00 : x0 ≠ 0 := by
    have hg0 : g ≠ 0 := by
      intro h
      apply hf0
      have : star g = star (0 : ι → ℂ) := by rw [h]
      simpa [hgdef] using this
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hg0
    intro h
    have h1 : x0 i = (0 : PiLp 2 (fun _ : ι => T.V)) i := by rw [h]
    simp only [hx0def, PiLp.toLp_apply, PiLp.zero_apply] at h1
    exact hi ((smul_eq_zero.1 h1).resolve_right (KType.w_ne_zero T))
  have hE : KRel ε (tensAct A D) := tensor_action_lie_relations hA (ext1Dual_kRel hG)
  have hEu : KUnit ε (tensAct A D) := tensor_action_unitary hAu (ext1Dual_conjT hGu)
  obtain ⟨Γ, hΓst, hΓex, hΓ0, hΓV, hx0w⟩ := highest_weight_graph_submodule hE hEu hF hV hx0 hx00 hwV hw0 hw
  have huniq : ∀ y v v', (y, v) ∈ Γ → (y, v') ∈ Γ → v = v' := by
    intro y v v' h1 h2
    have h3 := Γ.sub_mem h1 h2
    have e : (y, v) - (y, v') = ((0 : PiLp 2 (fun _ : ι => T.V)), v - v') := by simp
    rw [e] at h3
    exact sub_eq_zero.1 (hΓ0 _ h3)
  choose xv hxv using hΓex
  set si : ι → PiLp 2 (fun _ : ι => T.V) := fun i => WithLp.toLp 2 (Pi.single i T.w) with hsidef

  have key : ∀ a b, ε a = ε b → ∀ c : ℂ, A a b T.w = c • T.w → ∀ i,
      F a b (xv (si i)) = c • xv (si i) - ∑ j, G a b i j • xv (si j) := by
    intro a b hab c hc i
    have h1 : prodEndomorphismFamily (tensAct A D) F a b (si i, xv (si i)) ∈ Γ := hΓst a b hab _ (hxv _)
    rw [product_action_apply] at h1
    have h2 : c • (si i, xv (si i)) - ∑ j, G a b i j • (si j, xv (si j)) ∈ Γ :=
      Γ.sub_mem (Γ.smul_mem c (hxv _)) (Γ.sum_mem fun j _ => Γ.smul_mem _ (hxv _))
    have e : c • (si i, xv (si i)) - ∑ j, G a b i j • (si j, xv (si j)) =
        (c • si i - ∑ j, G a b i j • si j, c • xv (si i) - ∑ j, G a b i j • xv (si j)) := by
      refine Prod.ext ?_ ?_ <;> simp [Prod.fst_sum, Prod.snd_sum]
    rw [e] at h2
    have hsi : tensAct A D a b (si i) = c • si i - ∑ j, G a b i j • si j :=
      tensor_action_single A G a b hc i
    rw [hsi] at h1
    exact huniq _ _ _ h1 h2
  refine ⟨fun i => xv (si i), fun i => hΓV _ (hxv _), ?_, ?_, ?_⟩
  · intro h0
    have hs : (x0, ∑ i, g i • xv (si i)) ∈ Γ := by
      have h1 : ∑ i, g i • (si i, xv (si i)) ∈ Γ := Γ.sum_mem fun i _ => Γ.smul_mem _ (hxv _)
      have e : ∑ i, g i • (si i, xv (si i)) = (x0, ∑ i, g i • xv (si i)) := by
        refine Prod.ext ?_ ?_
        · rw [Prod.fst_sum]
          refine PiLp.ext fun k => ?_
          simp [hsidef, hx0def, Pi.single_apply]
        · rw [Prod.snd_sum]
          rfl
      rwa [e] at h1
    have h2 := huniq _ _ _ hs hx0w
    apply hw0
    rw [← h2]
    have h3 : ∀ i, xv (si i) = 0 := fun i => congrFun h0 i
    simp [h3]
  · intro a i
    have h := key a a rfl (μ a) (hp.1 a) i
    rw [h]
    simp [hμ]
  · intro a b hab he i
    have h := key a b he 0 (by rw [hp.2 a b hab he, zero_smul]) i
    rw [h, zero_smul, zero_sub, neg_add_cancel]

end ReciprocityTheory.ChartRestriction.DS.HW
