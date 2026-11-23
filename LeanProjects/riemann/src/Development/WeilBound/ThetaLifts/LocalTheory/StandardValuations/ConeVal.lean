import Development.WeilBound.ThetaLifts.LocalTheory.StandardValuations.AdelicInclusionMapPlaceSection
import Development.WeilBound.ThetaLifts.LocalTheory.StandardValuations.IdeleInt

noncomputable section

namespace PositivityTheory.ThKG.Std

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix
open PositivityTheory.KCo PositivityTheory.ThK.SplitDict PositivityTheory.ThKG.StdDict PositivityTheory.ThKG.Loc MeasureTheory ValuativeRel Topology GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E}

  {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {B : Base F E}
  {b : GL (Fin n) (Fv F v)} {c : GL (Fin d) (Fv F v)} {b₁ : GL (Fin n₁) (Fv F v)} {c₁ : GL (Fin d₁) (Fv F v)}
  [SecondCountableTopology (Fv F v)] [MeasurableSpace (Fv F v)] [BorelSpace (Fv F v)] {m : Measure (Fv F v)}

theorem ext_neg {k : Type} [Field k] (jr : Fin n₁ → Fin n) (jc : Fin d₁ → Fin d) (y : Matrix (Fin n₁) (Fin d₁) k) :
    -(emb k jr * y * (emb k jc)ᵀ) = emb k jr * (-y) * (emb k jc)ᵀ := by simp

theorem lin_uniq {M : Model σ X W} (hm : IsVol m) (hB : B.IsGood σ) (hu : PsiUnr B.ψ v) (g : M.IsGood B.ψ) {c₁ c₂ ι ι'}
    (L : Lin M B.ψ v c₁ c₂ ι) (L' : Lin M B.ψ v c₁ c₂ ι') {φ : Fl F v n d} (hφ : φ ∈ SB _) : ι' φ = ι φ := by
  haveI := hm.haar
  obtain ⟨f, hf⟩ := exists_sinf F (Fin n × Fin d)
  have hl : IsEvLoc M M LinearMap.id (ContinuousLinearMap.id _ _) fun _ => LinearMap.id :=
    ⟨fun e => by
      have : f = 0 := DFunLike.congr_fun e f
      simp [this] at hf, fun _ => ⟨rfl, Submodule.map_id _⟩, fun _ _ _ _ => rfl⟩
  have o : ∀ k, incM F (1 : Matrix (Fin k) (Fin k) E) = 1 := fun k => Matrix.map_one _ (map_zero _) (map_one _)
  have he : IsEv B M M 1 1 ∅ LinearMap.id := ⟨fun _ h => h, fun z Φ _ => by simp [o], fun _ h => h.elim, _, _, hl.ne, hl.vac, hl.pure⟩
  have x : ∀ y : Matrix (Fin n) (Fin d) (Fv F v), ext id id y = y := fun y =>
    Matrix.ext fun i j => ext_mid Function.injective_id Function.injective_id y i j
  funext y
  refine (ev_model hm hB.std hu g g he hl L L' id id ∅ (fun z => by simp [o, x]) (fun _ h => by simp at h)
    (fun p _ => Or.inl ⟨p.1, p.2, rfl⟩) hφ y).trans ?_
  have : ∀ Z : Fin n × Fin d → Fv F v, tm (cut ∅ Z) = 0 := fun Z => by ext i j; simp [tm, cut]
  simp only [this, zero_add, x, wt, Finset.notMem_empty, if_false]
  rw [integral_const_mul, integral_fintype_prod_eq_prod (fun _ : Fin n × Fin d => ind (1 : Fv F v))]
  simp [int_ind_one hm]

section
variable {X₀ : Spc F E n} {b₀ : GL (Fin n) (Fv F v)} {M : Model σ X W} {M₁ : Model σ X₀ W₁} {H' : Plane E d d₁} {jc : Fin d₁ → Fin d}
  {j₀ j₁ : Fin d}

theorem ev0W (hm : IsVol m) (hB : B.IsGood σ) (hu : PsiUnr B.ψ v) (h : IsSec σ t sec) (g : M.IsGood B.ψ) (g₁ : M₁.IsGood B.ψ) {e ei ev}
    (he : IsEv B M M₁ 1 H'.ι (iso0 n H') e) (hl : IsEvLoc M M₁ e ei ev) {ι ι₁} (L : Lin M B.ψ v (cW t b c) (cB σ t X W b c) ι)
    (L₁ : Lin M₁ B.ψ v (cW t b₀ c₁) (cB σ t X₀ W₁ b₀ c₁) ι₁) (hJ : IsUnit (X.J.map t)) (pe : PE σ t X.J X₀.J b b₀ 1 id)
    (pe' : PE σ t W.J W₁.J c c₁ H'.ι jc) (px' : PX σ t W.J c H'.x H'.y j₀ j₁ (-1)) (hc : ∀ i, i = j₀ ∨ i = j₁ ∨ ∃ j, i = jc j)
    {φ : Fl F v n d} (hφ : φ ∈ SB _) (y) : ι₁ (ev v φ) y = ∫ Z, ι φ (tm (cut (Finset.univ.filter fun p => p.2 = j₀) Z) + ext id jc y) *
      wt (Finset.univ.filter fun p => p.2 = j₀) Z ∂(Measure.pi fun _ => m) := by
  have el : ∀ i s s', ∃ u ∈ iso0 (F := F) n H', At (evFin F v) u ∧ cW t b c u = single i j₀ s ∧ cB σ t X W b c u = single i j₁ s' :=
    fun i s s' => let ⟨p, a, x, y⟩ := vec_ex (b := b) h hJ (Pi.single i s) (Pi.single i s'); ⟨_, ⟨p, rfl⟩, at_l a _, col_el h px' x y⟩
  refine ev_model hm hB.std hu g g₁ he hl L L₁ id jc _ (emb_c h pe pe') (fun p hp s => ?_) (fun p hp => ?_) hφ y
  · simpa [(Finset.mem_filter.1 hp).2] using el p.1 s 0
  · rcases hc p.2 with a | a | ⟨j, a⟩
    · exact absurd (by simp [a]) hp
    · exact Or.inr fun s => by simpa [a] using el p.1 0 s
    · exact Or.inl ⟨p.1, j, Prod.ext rfl a⟩

theorem ev0B (hm : IsVol m) (hB : B.IsGood σ) (hu : PsiUnr B.ψ v) (h : IsSec σ t sec) (g : M.IsGood B.ψ) (g₁ : M₁.IsGood B.ψ) {e ei ev}
    (he : IsEv B M M₁ 1 H'.ι (iso0 n H') e) (hl : IsEvLoc M M₁ e ei ev) {ι ι₁}
    (L : Lin M B.ψ v (cB σ t X W b c) (fun u => -cW t b c u) ι)
    (L₁ : Lin M₁ B.ψ v (cB σ t X₀ W₁ b₀ c₁) (fun u => -cW t b₀ c₁ u) ι₁) (hJ : IsUnit (X.J.map t)) (pe : PE σ t X.J X₀.J b b₀ 1 id)
    (pe' : PE σ t W.J W₁.J c c₁ H'.ι jc) (px' : PX σ t W.J c H'.x H'.y j₀ j₁ (-1)) (hc : ∀ i, i = j₀ ∨ i = j₁ ∨ ∃ j, i = jc j)
    {φ : Fl F v n d} (hφ : φ ∈ SB _) (y) : ι₁ (ev v φ) y = ∫ Z, ι φ (tm (cut (Finset.univ.filter fun p => p.2 = j₁) Z) + ext id jc y) *
      wt (Finset.univ.filter fun p => p.2 = j₁) Z ∂(Measure.pi fun _ => m) := by
  have el : ∀ i s s', ∃ u ∈ iso0 (F := F) n H', At (evFin F v) u ∧ cB σ t X W b c u = single i j₁ s' ∧ -cW t b c u = single i j₀ s :=
    fun i s s' => let ⟨p, a, x, y⟩ := vec_ex (b := b) h hJ (Pi.single i (-s)) (Pi.single i s')
      ⟨_, ⟨p, rfl⟩, at_l a _, (col_el h px' x y).2, by rw [(col_el h px' x y).1, sneg, neg_neg]⟩
  refine ev_model hm hB.std hu g g₁ he hl L L₁ id jc _ (fun z => ⟨(emb_c h pe pe' z).2, by
    rw [(emb_c h pe pe' z).1]; exact ext_neg _ _ _⟩) (fun p hp s => ?_) (fun p hp => ?_) hφ y
  · simpa [(Finset.mem_filter.1 hp).2] using el p.1 0 s
  · rcases hc p.2 with a | a | ⟨j, a⟩
    · exact Or.inr fun s => by simpa [a] using el p.1 s 0
    · exact absurd (by simp [a]) hp
    · exact Or.inl ⟨p.1, j, Prod.ext rfl a⟩

end

section
variable {M : Model σ X W} {M₁ : Model σ X₁ W₁} {H : Plane E n n₁} {H' : Plane E d d₁} {jr : Fin n₁ → Fin n} {jc : Fin d₁ → Fin d}
  {i₀ i₁ : Fin n} {j₀ j₁ : Fin d}

theorem evA (hm : IsVol m) (hB : B.IsGood σ) (hu : PsiUnr B.ψ v) (h : IsSec σ t sec) (g : M.IsGood B.ψ) (g₁ : M₁.IsGood B.ψ) {e ei ev}
    (he : IsEv B M M₁ H.ι H'.ι (isoA H H') e) (hl : IsEvLoc M M₁ e ei ev) {ι ι₁} (L : Lin M B.ψ v (cW t b c) (cB σ t X W b c) ι)
    (L₁ : Lin M₁ B.ψ v (cW t b₁ c₁) (cB σ t X₁ W₁ b₁ c₁) ι₁) (hJ : IsUnit (X.J.map t)) (hJ' : IsUnit (W₁.J.map t))
    (pe : PE σ t X.J X₁.J b b₁ H.ι jr) (px : PX σ t X.J b H.x H.y i₀ i₁ 1) (hr : ∀ i, i = i₀ ∨ i = i₁ ∨ ∃ j, i = jr j)
    (pe' : PE σ t W.J W₁.J c c₁ H'.ι jc) (px' : PX σ t W.J c H'.x H'.y j₀ j₁ (-1)) (hc : ∀ i, i = j₀ ∨ i = j₁ ∨ ∃ j, i = jc j)
    (P : Finset (Fin n × Fin d)) (hP : ∀ p, p ∈ P ↔ p.2 = j₀ ∨ p.1 = i₀ ∧ p.2 ≠ j₁)
    {φ : Fl F v n d} (hφ : φ ∈ SB _) (y) :
    ι₁ (ev v φ) y = ∫ Z, ι φ (tm (cut P Z) + ext jr jc y) * wt P Z ∂(Measure.pi fun _ => m) := by
  have el : ∀ i s s', ∃ u ∈ isoA (F := F) H H', At (evFin F v) u ∧ cW t b c u = single i j₀ s ∧ cB σ t X W b c u = single i j₁ s' :=
    fun i s s' => let ⟨p, a, x, y⟩ := vec_ex (b := b) h hJ (Pi.single i s) (Pi.single i s')
      ⟨_, Or.inl ⟨p, rfl⟩, at_l a _, col_el h px' x y⟩
  have el' : ∀ j s s', ∃ u ∈ isoA (F := F) H H', At (evFin F v) u ∧ cW t b c u = single i₀ (jc j) s ∧
      cB σ t X W b c u = single i₁ (jc j) s' :=
    fun j s s' => let ⟨p, a, x, y⟩ := vec_ex' h pe' hJ' j s (-s')
      ⟨_, Or.inr ⟨p, rfl⟩, at_r _ a, (row_el h px x y).1, by rw [(row_el h px x y).2, neg_neg]⟩
  refine ev_model hm hB.std hu g g₁ he hl L L₁ jr jc _ (emb_c h pe pe') (fun p hp s => ?_) (fun p hp => ?_) hφ y
  · rcases hc p.2 with a | a | ⟨j, a⟩
    · simpa [a] using el p.1 s 0
    · rcases (hP p).1 hp with x | x
      · simpa [x] using el p.1 s 0
      · exact absurd a x.2
    · rcases (hP p).1 hp with x | x
      · simpa [x] using el p.1 s 0
      · simpa [x.1, a] using el' j s 0
  · by_cases a1 : p.2 = j₁
    · exact Or.inr fun s => by simpa [a1] using el p.1 0 s
    rcases hc p.2 with a | a | ⟨j, a⟩
    · exact absurd ((hP p).2 (Or.inl a)) hp
    · exact absurd a a1
    · rcases hr p.1 with x | x | ⟨i, x⟩
      · exact absurd ((hP p).2 (Or.inr ⟨x, a1⟩)) hp
      · exact Or.inr fun s => by simpa [a, x] using el' j 0 s
      · exact Or.inl ⟨i, j, Prod.ext x a⟩

theorem evB (hm : IsVol m) (hB : B.IsGood σ) (hu : PsiUnr B.ψ v) (h : IsSec σ t sec) (g : M.IsGood B.ψ) (g₁ : M₁.IsGood B.ψ) {e ei ev}
    (he : IsEv B M M₁ H.ι H'.ι (isoB H H') e) (hl : IsEvLoc M M₁ e ei ev) {ι ι₁}
    (L : Lin M B.ψ v (cB σ t X W b c) (fun u => -cW t b c u) ι)
    (L₁ : Lin M₁ B.ψ v (cB σ t X₁ W₁ b₁ c₁) (fun u => -cW t b₁ c₁ u) ι₁) (hJ : IsUnit (X₁.J.map t)) (hJ' : IsUnit (W.J.map t))
    (pe : PE σ t X.J X₁.J b b₁ H.ι jr) (px : PX σ t X.J b H.x H.y i₀ i₁ 1) (hr : ∀ i, i = i₀ ∨ i = i₁ ∨ ∃ j, i = jr j)
    (pe' : PE σ t W.J W₁.J c c₁ H'.ι jc) (px' : PX σ t W.J c H'.x H'.y j₀ j₁ (-1)) (hc : ∀ i, i = j₀ ∨ i = j₁ ∨ ∃ j, i = jc j)
    (P : Finset (Fin n × Fin d)) (hP : ∀ p, p ∈ P ↔ p.1 = i₁ ∨ p.2 = j₁ ∧ p.1 ≠ i₀)
    {φ : Fl F v n d} (hφ : φ ∈ SB _) (y) :
    ι₁ (ev v φ) y = ∫ Z, ι φ (tm (cut P Z) + ext jr jc y) * wt P Z ∂(Measure.pi fun _ => m) := by
  have el : ∀ j s s', ∃ u ∈ isoB (F := F) H H', At (evFin F v) u ∧ cB σ t X W b c u = single i₁ j s' ∧ -cW t b c u = single i₀ j s :=
    fun j s s' => let ⟨p, a, x, y⟩ := vec_ex (b := c) h hJ' (Pi.single j (-s)) (Pi.single j (-s'))
      ⟨_, Or.inl ⟨p, rfl⟩, at_r _ a, by rw [(row_el h px x y).2, neg_neg], by rw [(row_el h px x y).1, sneg, neg_neg]⟩
  have el' : ∀ i s s', ∃ u ∈ isoB (F := F) H H', At (evFin F v) u ∧ cB σ t X W b c u = single (jr i) j₁ s' ∧
      -cW t b c u = single (jr i) j₀ s :=
    fun i s s' => let ⟨p, a, x, y⟩ := vec_ex' h pe hJ i (-s) s'
      ⟨_, Or.inr ⟨p, rfl⟩, at_l a _, (col_el h px' x y).2, by rw [(col_el h px' x y).1, sneg, neg_neg]⟩
  refine ev_model hm hB.std hu g g₁ he hl L L₁ jr jc _ (fun z => ⟨(emb_c h pe pe' z).2, by
    rw [(emb_c h pe pe' z).1]; exact ext_neg _ _ _⟩) (fun p hp s => ?_) (fun p hp => ?_) hφ y
  · rcases (hP p).1 hp with x | x
    · simpa [x] using el p.2 0 s
    · rcases hr p.1 with a | a | ⟨i, a⟩
      · exact absurd a x.2
      · simpa [a] using el p.2 0 s
      · simpa [x.1, a] using el' i 0 s
  · by_cases a1 : p.1 = i₀
    · exact Or.inr fun s => by simpa [a1] using el p.2 s 0
    rcases hr p.1 with a | a | ⟨i, a⟩
    · exact absurd a a1
    · exact absurd ((hP p).2 (Or.inl a)) hp
    · rcases hc p.2 with x | x | ⟨j, x⟩
      · exact Or.inr fun s => by simpa [a, x] using el' i s 0
      · exact absurd ((hP p).2 (Or.inr ⟨x, a1⟩)) hp
      · exact Or.inl ⟨i, j, Prod.ext a x⟩

end

theorem cone_val {β : ℕ} {X : Spc F E (β + 2)} {X₁ : Spc F E β} {M : Model σ X W} {M₁ : Model σ X₁ W₁} (hm : IsVol m) (hB : B.IsGood σ)
    (hu : PsiUnr B.ψ v) {c₁ c₂ ι c₁' c₂' ι₁} (L : Lin M B.ψ v c₁ c₂ ι) (L₁ : Lin M₁ B.ψ v c₁' c₂' ι₁)
    {ev : Fl F v (β + 2) d →ₗ[ℂ] Fl F v β d₁} (em : (SB _).map ev = SB _) {jc : Fin d₁ → Fin d} {P : Finset (Fin (β + 2) × Fin d)}
    (hev : ∀ φ ∈ SB _, ∀ y, ι₁ (ev φ) y = ∫ Z, ι φ (tm (cut P Z) + ext mid jc y) * wt P Z ∂(Measure.pi fun _ => m))
    {ϖ : (Fv F v)ˣ} (hϖ : IsUnif ϖ) (χ : Chr F E) (hχ : ∀ x, chrW χ (t.comp σ) x = (chrW χ t x)⁻¹) {κ : ℕ}
    (hν : CondLE ϖ (κ + 1) (chrW χ t)) (hν' : ¬ CondLE ϖ κ (chrW χ t)) {e : Fin (β + 2) → Fin d} {e₁ : Fin β → Fin d₁}
    {φ φ₁} (hφ : φ ∈ SB _) (hφ₁ : φ₁ ∈ SB _) (a : ι φ = std (chrW χ t) ϖ (κ + 1) e) (a₁ : ι₁ φ₁ = std (chrW χ t) ϖ (κ + 1) e₁)
    {om : Rep σ X W} {K : Subgroup (UA σ X.J)} {μ : LocMeas K} (hμ : μ.Is)
    (hK : ∀ k ∈ kAt K (evFin F v), Acts (evFin F v) (om (k, 1)) φ φ) {u : (AE F E)ˣ → Matrix (Fin (β + 2)) (Fin d) (AE F E)}
    (hs : ∀ l, c₁ (idem F v • u l) = single 0 (e (Fin.last _)) (piW t l) ∧
      c₂ (idem F v • u l) = single (Fin.last _) (e 0) (-piW (t.comp σ) l))
    (hc : Function.Injective jc) (hei : Function.Injective e) (he : ∀ i, jc (e₁ i) = e (mid i))
    (h0 : ∀ j, e 0 ≠ jc j) (h1 : ∀ j, e (Fin.last _) ≠ jc j) (hP : ∀ i j, (mid i, jc j) ∉ P)
    (ha : (Fin.last _, e 0) ∈ P) (hb : (0, e (Fin.last _)) ∉ P)
    (hAB : ((∀ j, j ≠ Fin.last _ → (0, e j) ∉ P) ∧ ∀ i, (mid i, e 0) ∉ P) ∨
      ((∀ i, i ≠ 0 → (i, e (Fin.last _)) ∉ P) ∧ ∀ j, (Fin.last _, e (mid j)) ∉ P)) {r : ℕ}
    (g : Fin r → Fin (β + 2) × Fin d) (hg : Function.Injective g) (h : ∀ p, p ∈ Set.range g ↔ p ∈ P ∧ p.2 ∉ Set.range e) (z : ℕ) :
    coneF B M om μ v ev u χ z φ = (gI m (psiV B.ψ v) (chrW χ t) (((ϖ : Fv F v) ^ (κ + 1))⁻¹) * (chrW χ t ϖ : ℂ) ^ (κ + 1) *
      ((GlobalTheory.SplitWeil.resCard (Fv F v) : ℂ) ^ (κ + 1)) ^ z * (((GlobalTheory.SplitWeil.resCard (Fv F v) : ℂ) ^ (κ + 1))⁻¹) ^ r) • φ₁ := by
  have dms : ∀ (Y : Matrix (Fin (β + 2)) (Fin d) (Fv F v)) i j s, dm Y (single i j s) = Y i j * s := fun Y i j s => by
    simp [dm, dotProduct, ofM, single_apply, Fintype.sum_prod_type, ite_and]
  have l0 : (0 : Fin (β + 2)) ≠ Fin.last _ := by simp [Fin.ext_iff]
  have key : ∀ k ∈ kAt K (evFin F v), ∀ l, ev (opF v (fun Φ => M.co.rho B.ψ (idem F v • u l) (om (k, 1) Φ)) φ) =
      ((((GlobalTheory.SplitWeil.resCard (Fv F v) : ℂ) ^ (κ + 1))⁻¹) ^ r *
        (dl (chrW χ t) (piW t l) * gI m (psiV B.ψ v) (chrW χ t) (piW (t.comp σ) l))) • φ₁ := fun k hk l => by
    have at' : At (evFin F v) (idem F v • u l) := at_sgl_smul 1 _
    have sb := Hv_mem (M := M) hB.std (idem F v • u l) hφ
    rw [opF_eq hφ sb fun r hr => by
      show M.co.rho B.ψ _ (om (k, 1) _) = _
      rw [hK k hk r hr]; exact acts_Hv at' φ r hr]
    refine L₁.bij.2.1 (em ▸ Submodule.mem_map_of_mem sb) ((SB _).smul_mem _ hφ₁) (funext fun y => ?_)
    rw [hev _ sb, L.act _ at' (by rw [(hs l).1, (hs l).2, dms, single_apply_of_ne _ _ _ _ _ fun h => l0 h.1, zero_mul]) φ hφ,
      (hs l).1, (hs l).2, a, map_smul, a₁, Pi.smul_apply, smul_eq_mul,
      ← int_cone hm hϖ hc hei he h0 h1 P hP ha hb hAB g hg h]
    congr 1
    funext Z
    beta_reduce
    rw [dms, add_assoc, Matrix.add_apply, ext_off y (Or.inr h0), add_zero, mul_neg, mul_comm (tm _ _ _)]
    simp [tm, cut, ha]
  funext y
  have i1 := idele_int (t := t) hB.cm hm (isPsi hB.std hu) hϖ χ hχ hν hν' (μ.xf v) (hμ.xf v).1 (hμ.xf v).2
    ((((GlobalTheory.SplitWeil.resCard (Fv F v) : ℂ) ^ (κ + 1))⁻¹) ^ r * φ₁ y) z
  rw [coneF, integral_congr_ae (Filter.Eventually.of_forall fun k => (congrArg _ (funext fun l => by
    rw [key k.1 k.2, Pi.smul_apply, smul_eq_mul]; ring)).trans i1), integral_const, Measure.real, (hμ.kf v).2]
  simp [mul_assoc]

end PositivityTheory.ThKG.Std
