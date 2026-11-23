import Development.WeilBound.CoreStatements.VolumeEquality.BallVolDefs
import Development.WeilBound.CoreStatements.VolumeEquality.LocInj
import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.RmulScalOne

noncomputable section

namespace SheetDecomposition

open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.Dict
  GlobalTheory.CompanionTheory.Ar.Cusp.DictMeas GlobalTheory.CompanionTheory.Ar.Cmp PositivityTheory.EqVol

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem sgU_of_iso {j j' N : ℕ} (s : E →+* ℂ) {G G' a : Matrix (Fin N) (Fin N) E} (ha : aᵀ * G * a.map (ccH E) = G')
    {A A' : Matrix (Fin N) (Sg j j') ℂ} {Ai : Matrix (Sg j j') (Fin N) ℂ} (hA : Aᴴ * (G.map s)ᵀ * A = sgI j j')
    (hA' : A'ᴴ * (G'.map s)ᵀ * A' = sgI j j') (hi : A * Ai = 1) : IsSgU (Ai * (a.map s * A')) := by
  have e2 : ((a.map (ccH E)).map s)ᵀ = (a.map s)ᴴ := by
    ext i k
    exact IsCMField.complexEmbedding_complexConj E s _
  have e3 : (a.map s)ᴴ * (G.map s)ᵀ * a.map s = (G'.map s)ᵀ := by
    rw [← ha, Matrix.map_mul, Matrix.map_mul, transpose_mul, transpose_mul, e2, Matrix.transpose_map, transpose_transpose,
      Matrix.mul_assoc]
  have e4 : A * (Ai * (a.map s * A')) = a.map s * A' := by rw [← Matrix.mul_assoc, hi, Matrix.one_mul]
  unfold IsSgU
  calc _ = (A * (Ai * (a.map s * A')))ᴴ * (G.map s)ᵀ * (A * (Ai * (a.map s * A'))) := by
        rw [← hA, conjTranspose_mul A]
        simp only [Matrix.mul_assoc]
    _ = A'ᴴ * ((a.map s)ᴴ * (G.map s)ᵀ * a.map s) * A' := by
        rw [e4, conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [e3, hA']

theorem InLevel.form {H : Host E} {l : Level H} {D : Datum H} {γ : D.La ≃ₗ[𝓞 E] D.La} (h : InLevel l D γ)
    {form : D.La →ₗ[ℤ] D.La →ₗ[ℤ] ℤ} (hF : form = D.EF ∨ form = -D.EF) (u v : D.La) : form (γ u) (γ v) = form u v := by
  rcases hF with e | e
  · rw [e]
    exact h.1 u v
  · rw [e]
    exact congrArg Neg.neg (h.1 u v)

theorem InLevel.free {H : Host E} {l : Level H} {D : Datum H} {γ : D.La ≃ₗ[𝓞 E] D.La} (h : InLevel l D γ) {g : ℕ}
    (R : RiemLat E g D.La) (hF : R.form = D.EF ∨ R.form = -D.EF) (he : R.EqvBy R γ) (v : D.La) : γ v = v := by
  refine rigid_of_congr (reForm R) (reForm_pos _) (fun C => ?_) γ.toLinearMap.toAddMonoidHom
    (reForm_eqv (h.form hF) he) l.M l.three_le h.congr v
  obtain ⟨S, hS₁, hS₂⟩ := short_finite (fun _ : Unit => R) (fun _ => continuous_const) continuous_const () C
  exact hS₁.subset hS₂.self_of_nhds

theorem mfund_of {H : Host E} {l : Level H} {D : Datum H} {Ψ : Type} [Fintype Ψ] {j j' n g N : ℕ}
    {F : UnivFam E Ψ j j' n g D.La} {Γ : Subgroup (D.La ≃ₗ[𝓞 E] D.La)} {FF : Set (Fin n → ℂ)}
    (hF : F.form = D.EF ∨ F.form = -D.EF) (hΓ : ∀ γ, γ ∈ Γ ↔ InLevel l D γ) (hFF : F.IsFundSet Γ FF)
    {e : D.La →ₗ[𝓞 E] (Fin N → E)} (hL : IsLat (LinearMap.range e)) {Γm : Subgroup (GL (Fin N) E)}
    {ρ : GL (Fin N) E → Ψ → Matrix (Sg j j') (Sg j j') ℂ} {Z : (Fin n → ℂ) → Fin n → ℂ}
    (hZ : Set.BijOn Z (ballDom F.q) (ballDom F.q)) (hm : MeasurableSet (Z '' FF))
    (hq : ∀ γ ∈ Γm, ∀ δ : D.La ≃ₗ[𝓞 E] D.La, (∀ x, e (δ x) = (γ : Matrix (Fin N) (Fin N) E) *ᵥ e x) →
      ∀ t ∈ ballDom F.q, ∀ t' ∈ ballDom F.q, ((F.R t).EqvBy (F.R t') δ ↔ Z t' = moebBall F.q (ρ γ) (Z t)))
    (h1 : ∀ γ ∈ Γm, ∃ δ, InLevel l D δ ∧ ∀ x, e (δ x) = (γ : Matrix (Fin N) (Fin N) E) *ᵥ e x)
    (h2 : ∀ δ, InLevel l D δ → ∃ γ ∈ Γm, ∀ x, e (δ x) = (γ : Matrix (Fin N) (Fin N) E) *ᵥ e x) :
    MFund F.q ρ Γm (Z '' FF) := by
  refine ⟨hm, ?_, fun s hs => ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact hZ.mapsTo (hFF.2.1 ht)
  · obtain ⟨t, ht, rfl⟩ := hZ.surjOn hs
    obtain ⟨t', ht', δ, hδ, he⟩ := hFF.2.2.1 t ht
    obtain ⟨γ, hγ, hx⟩ := h2 δ ((hΓ δ).1 hδ)
    exact ⟨γ, hγ, t', ht', (hq γ hγ δ hx t ht t' (hFF.2.1 ht')).1 he⟩
  · rintro _ ⟨t, ht, rfl⟩ γ hγ ⟨t', ht', he⟩
    obtain ⟨δ, hδ, hx⟩ := h1 γ hγ
    have h3 := (hq γ hγ δ hx t (hFF.2.1 ht) t' (hFF.2.1 ht')).2 he
    obtain rfl := hFF.2.2.2 t ht t' ht' ⟨δ, (hΓ δ).2 hδ, h3⟩
    have h4 := hδ.free (F.R t) (by rw [F.form_eq]; exact hF) h3
    have h5 : Matrix.toLin' (γ : Matrix (Fin N) (Fin N) E) = LinearMap.id := by
      refine LinearMap.ext_on hL.2 ?_
      rintro _ ⟨x, rfl⟩
      rw [Matrix.toLin'_apply, ← hx, h4]
      rfl
    exact Units.ext (Matrix.toLin'.injective (h5.trans Matrix.toLin'_one.symm))

theorem famVol_of (h1 : MoebVol) (h2 : StdModel) (h3 : ArithIdx) (h4 : LevelDict) : FamVol := by
  intro E _ _ _ H l D D' Ψ _ j j' n g F F' Γ Γ' FF FF' c₀ hj hj' hr hc hσ hrt hF hF' hΓ hΓ' hFF hFF'
  have := H.unram
  have hemb : ∀ (u : 𝓞 E →+* ℂ) (x : 𝓞 E), embOf u (x : E) = u x := fun u x => IsFractionRing.lift_algebraMap _ x
  have hext : ∀ u : E →+* ℂ, embOf (u.comp (algebraMap (𝓞 E) E)) = u := fun u =>
    IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun x => hemb _ x)
  have hcov : ∀ u : E →+* ℂ, u ∈ Set.range (fun τ => embOf (F.σ τ)) ∨
      ComplexEmbedding.conjugate u ∈ Set.range (fun τ => embOf (F.σ τ)) := fun u => by
    by_cases h : ∃ τ, F.σ τ = (starRingEnd ℂ).comp (u.comp (algebraMap (𝓞 E) E))
    · obtain ⟨τ, hτ⟩ := h
      exact Or.inr ⟨τ, (congrArg embOf hτ).trans (hext (ComplexEmbedding.conjugate u))⟩
    · obtain ⟨τ, hτ⟩ := (F.cm.2 _).2 h
      exact Or.inl ⟨τ, (congrArg embOf hτ).trans (hext u)⟩
  have hne : Nonempty Ψ := by
    obtain ⟨u⟩ : Nonempty (E →+* ℂ) := inferInstance
    rcases hcov u with ⟨τ, -⟩ | ⟨τ, -⟩ <;> exact ⟨τ⟩
  have hξ : ∀ τ, embOf (F.σ τ) (H.rt : E) = Complex.I * (c₀ : ℂ) := fun τ => (hemb _ _).trans (hrt τ)
  obtain ⟨τ₀⟩ := hne
  have : Nonempty Ψ := ⟨τ₀⟩
  have hξ0 : -(H.rt : E) ≠ 0 := neg_ne_zero.2 fun h => by
    have := hξ τ₀
    rw [h, map_zero] at this
    exact mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.2 hc.ne') this.symm
  have hξc : cc (-(H.rt : E)) = - -(H.rt : E) := (embOf (F.σ τ₀)).injective (by
    rw [cc, IsCMField.complexEmbedding_complexConj, neg_neg, map_neg, hξ]
    simp)
  obtain ⟨G, e, A, Ai, Z, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h2 E Ψ j j' n g _ H F _ c₀ hc hξ
  obtain ⟨G', e', A', Ai', Z', b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := h2 E Ψ j j' n g _ H F' _ c₀ hc (hσ ▸ hξ)
  rw [hσ] at b6 b9
  obtain ⟨c1, c2, c3⟩ := h4 E H l D _ G e _ _ hF a3 a4 hξ0 a5
  obtain ⟨d1, d2, d3⟩ := h4 E H l D' _ G' e' _ _ hF' b3 b4 hξ0 b5
  have hne : levIdeal l ≠ ⊥ :=
    inf_span_ne_bot l.prod (Nat.cast_ne_zero.2 (by have := l.three_le; omega)) (Nat.cast_ne_zero.2 l.A_pos.ne')
  obtain ⟨a, ha, hle, hidx⟩ := h3 E Ψ j j' _ G G' _ _ _ (levIdeal l) hcov hj hj' hr a1 b1 a2 b2 (fun τ => ⟨_, (a6 τ).1⟩)
    (fun τ => ⟨_, (b6 τ).1⟩) a4 b4 hξ0 hξc c1 d1 hne
    (neat_mono inf_le_left (neat_of_split E H.bar H.bar_eq l.M l.Mb l.three_le l.prod l.coprime))
  obtain ⟨m1, m2⟩ := a8 FF hFF.1 hFF.2.1
  obtain ⟨m3, m4⟩ := b8 FF' hFF'.1 hFF'.2.1
  have f1 := mfund_of (Γm := levelGrp (ccH E) G (LinearMap.range e) (levIdeal l)) hF hΓ hFF a4 a7 m1
    (fun γ hγ => a9 γ (Subgroup.mem_inf.1 hγ).1) c2 c3
  have f2 := mfund_of (Γm := levelGrp (ccH E) G' (LinearMap.range e') (levIdeal l)) hF' hΓ' hFF' b4 b7 m3
    (fun γ hγ => b9 γ (Subgroup.mem_inf.1 hγ).1) d2 d3
  have : Countable (Matrix (Fin (j + j')) (Fin (j + j')) E) := by
    have : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.countable_iff.2 inferInstance
    exact inferInstanceAs (Countable (Fin (j + j') → Fin (j + j') → E))
  have : Countable (GL (Fin (j + j')) E) :=
    (Units.val_injective.countable : Countable (Matrix (Fin (j + j')) (Fin (j + j')) E)ˣ)
  have canc : ∀ τ (X : Matrix (Fin (j + j')) (Sg j j') ℂ), A τ * (Ai τ * X) = X := fun τ X => by
    rw [← Matrix.mul_assoc, (a6 τ).2.2, Matrix.one_mul]
  have canc' : ∀ τ (X : Matrix (Fin (j + j')) (Sg j j') ℂ), A' τ * (Ai' τ * X) = X := fun τ X => by
    rw [← Matrix.mul_assoc, (b6 τ).2.2, Matrix.one_mul]
  rw [← m2, ← m4]
  refine h1 Ψ j j' n F.q F'.q _ (rho (fun τ => embOf (F.σ τ)) A Ai) (rho (fun τ => embOf (F.σ τ)) A' Ai')
    (fun τ => Ai τ * ((a : Matrix (Fin (j + j')) (Fin (j + j')) E).map (embOf (F.σ τ)) * A' τ)) (uGrp (ccH E) G)
    (levelGrp (ccH E) G (LinearMap.range e) (levIdeal l)) (levelGrp (ccH E) G' (LinearMap.range e') (levIdeal l)) a _ _
    (fun τ => ?_) (fun x y τ => ?_) (fun γ hγ τ => sgU_of_iso _ hγ (a6 τ).1 (a6 τ).1 (a6 τ).2.2)
    (fun γ hγ τ => sgU_of_iso _ (Subgroup.mem_inf.1 hγ).1 (b6 τ).1 (b6 τ).1 (b6 τ).2.2) (fun τ => sgU_of_iso _ ha (a6 τ).1 (b6 τ).1 (a6 τ).2.2)
    (fun γ τ => ?_) inf_le_left hle hidx f1 f2
  · rw [rho, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, (a6 τ).2.1]
  · simp only [rho, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc, canc]
  · have : ((a⁻¹ : GL (Fin (j + j')) E) : Matrix (Fin (j + j')) (Fin (j + j')) E).map (embOf (F.σ τ)) *
        ((a : Matrix (Fin (j + j')) (Fin (j + j')) E).map (embOf (F.σ τ)) * A' τ) = A' τ := by
      rw [← Matrix.mul_assoc, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
    simp only [rho, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc, canc, canc', this]

end SheetDecomposition
