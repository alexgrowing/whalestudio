import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.CjApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.IsModel
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.RiEntries
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.OrdInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.RootsNormLe
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem model_small {l : ℕ} [Fact l.Prime] {ι : Type} [Finite ι] (x : ι → Qbar l) :
    ∃ b : Qbar l, b ≠ 0 ∧ ‖b‖ ≤ 1 ∧ ∀ i, ‖b * x i‖ ≤ 1 := by
  obtain ⟨M, hM⟩ := (Set.finite_range fun i => ‖x i‖).bddAbove
  have h1 : (0 : ℝ) < max M 1 := lt_max_of_lt_right one_pos
  obtain ⟨b, hb0, hb⟩ := NormedField.exists_norm_lt (Qbar l) (inv_pos.2 h1)
  refine ⟨b, norm_pos_iff.1 hb0, hb.le.trans (inv_le_one_of_one_le₀ (le_max_right _ _)), fun i => ?_⟩
  rw [norm_mul, ← inv_mul_cancel₀ h1.ne']
  exact mul_le_mul hb.le ((hM ⟨i, rfl⟩).trans (le_max_left _ _)) (norm_nonneg _) (inv_pos.2 h1).le

private theorem model_ordAt {l : ℕ} [Fact l.Prime] {n : ℕ} {F : GFrame l} {K : Type} [CommRing K]
    {ρ : F.G₀ →* GL (Fin n) K} {v : F.Vl} {ψ : Fin n → F.Gv v →* Kˣ} {z : F.G₀ → Matrix (Fin n) (Fin n) K}
    {w : GL (Fin n) K} {Y : Matrix (Fin n) (Fin n) K} (h : OrdAt F ρ v ψ z w Y) (a : K) :
    OrdAt F ρ v ψ (fun g => a • z g) w (a • Y) := by
  intro g
  obtain ⟨h1, h2, h3, h4⟩ := h g
  have e : ((w⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (a • z (F.φ v g) - dY F (mat ρ) (a • Y) (F.φ v g)) * (w : Matrix (Fin n) (Fin n) K) =
      a • (((w⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (z (F.φ v g) - dY F (mat ρ) Y (F.φ v g)) * (w : Matrix (Fin n) (Fin n) K)) := by
    unfold dY
    rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, ← smul_sub, Matrix.mul_smul, Matrix.smul_mul]
  refine ⟨h1, h2, fun i j hij => ?_, fun hg i => ?_⟩
  · rw [e, Matrix.smul_apply, h3 i j hij, smul_zero]
  · rw [e, Matrix.smul_apply, h4 hg i, smul_zero]

private theorem model_coc {l : ℕ} [Fact l.Prime] {n : ℕ} {F : GFrame l} {ρ : F.G₀ →* GL (Fin n) (Qbar l)}
    {P : GL (Fin n) (Qbar l)} {I : F.St → Subgroup F.G₀} {ψ : ∀ v, Fin n → F.Gv v →* (Qbar l)ˣ}
    {z : F.G₀ → Matrix (Fin n) (Fin n) (Qbar l)} (h : IsOrdCoc F ρ P I ψ z) (a : Qbar l) :
    IsOrdCoc F ρ P I ψ fun g => a • z g where
  cont := h.cont.const_smul a
  coc g g' := by rw [h.coc, smul_add, Matrix.mul_smul, Matrix.smul_mul]
  pol g := by rw [Matrix.mul_smul, h.pol, Matrix.transpose_smul, Matrix.smul_mul, smul_neg]
  ine u g hg := by rw [h.ine u g hg, smul_zero]
  ord v := by
    obtain ⟨w, Y, hw⟩ := h.ord v
    exact ⟨w, a • Y, model_ordAt (F := F) (ψ := ψ v) hw a⟩

theorem UpperTheory.V.Th.Nm.model :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (c : Coef l) (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l)) (ψ : ∀ v, Fin n → F.Gv v →* (Qbar l)ˣ) (z : F.G₀ → Matrix (Fin n) (Fin n) (Qbar l)) (q : ℕ) (sg : Fin q → F.G₀), Continuous ρ → Submodule.span (Qbar l) (Set.range (mat ρ)) = ⊤ → F.IsForm c.O n ρ P → ((P : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = P ∨ (P : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = -P) → (∀ u, ∀ g ∈ F.Iu u, ρ g = 1) → (∀ v, ∃ g, Function.Injective fun i => ψ v i g) → (∀ v i j, i < j → ψ v i ≠ ψ v j * (F.eps c.O (Qbar l)).comp (F.φ v)) → IsOrdCoc F ρ P F.Iu ψ z → (∀ g, IntM (mat ρ g)) → IntM (P : Matrix (Fin n) (Fin n) (Qbar l)) → IntM ((P⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) → (∀ j, (mat ρ (sg j)).charpoly.Separable) → ∀ c₁ : Coef l, ∃ (c' : Coef l) (y : Pt F c'.O n) (z₀ : F.G₀ → Matrix (Fin n) (Fin n) c'.O) (a : Qbar l) (al : Fin q → Fin n → c'.O), c₁.O ≤ c'.O ∧ IsModel y ρ P ψ ∧ a ≠ 0 ∧ (∀ g, (z₀ g).map (algebraMap c'.O (Qbar l)) = a • z g) ∧ OCoc y z₀ ∧ ∀ j, Function.Injective (al j) ∧ (mat y.ρ (sg j)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (al j i)) := by
  intro l _ n F c ρ P ψ z q sg hc hsp hF hs hI hreg hN hz hρ hP hPi hsep c₁
  choose w₀ Y hw₀ using hz.ord
  choose w hw hwi hwo using fun v => ordInt F ρ v (ψ v) z (w₀ v) (Y v) (hw₀ v)
  choose r hri hrn hrc using fun j => roots _ (hρ (sg j)) (hsep j)
  obtain ⟨c₂, a, h12, ha, hρ₂, hz₂⟩ := repIn F c₁ ρ z hc hρ hz.cont hz.coc
  obtain ⟨b, hb0, hb1, hb⟩ := model_small fun p : F.Vl × Fin n × Fin n => a * Y p.1 p.2.1 p.2.2
  obtain ⟨c₃, h23, k3⟩ := (inOf c₂).1 Unit (fun _ => b) fun _ => hb1
  obtain ⟨c₄, h34, k4⟩ := (inOf c₃).1 _ _ hb
  obtain ⟨c₅, h45, k5⟩ := (inOf c₄).1 (Fin n × Fin n) _ fun p => hP p.1 p.2
  obtain ⟨c₆, h56, k6⟩ := (inOf c₅).1 (Fin n × Fin n) _ fun p => hPi p.1 p.2
  obtain ⟨c₇, h67, k7⟩ := (inOf c₆).1 (F.Vl × Fin n × Fin n) _ fun p => hw p.1 p.2.1 p.2.2
  obtain ⟨c₈, h78, k8⟩ := (inOf c₇).1 (F.Vl × Fin n × Fin n) _ fun p => hwi p.1 p.2.1 p.2.2
  obtain ⟨c', h8, k9⟩ := (inOf c₈).1 (Fin q × Fin n) _ fun p => hrn p.1 p.2
  have h7 := h78.trans h8
  have h6 := h67.trans h7
  have h5 := h56.trans h6
  have h4 := h45.trans h5
  have h3 := h34.trans h4
  have h2 := h23.trans h3
  obtain ⟨y, z₀, hy, hz₀, ho⟩ := mkPt F c c' ρ P ψ (fun g => (b * a) • z g) w (fun v => (b * a) • Y v) hc hsp hF hs hI
    hreg hN (model_coc hz _) (fun v => model_ordAt (hwo v) _) (fun g i j => h2 (hρ₂ g i j)) (fun i j => h5 (k5 (i, j)))
    (fun i j => h6 (k6 (i, j)))
    (fun v => ⟨fun i j => h7 (k7 (v, i, j)), fun i j => h8 (k8 (v, i, j)), fun i j => by
      rw [Matrix.smul_apply, smul_eq_mul, mul_assoc]
      exact h4 (k4 (v, i, j))⟩)
    (fun g i j => by
      rw [Matrix.smul_apply, smul_eq_mul, mul_assoc]
      exact mul_mem (h3 (k3 ())) (h2 (hz₂ g i j)))
  refine ⟨c', y, z₀, b * a, fun j i => ⟨r j i, k9 (j, i)⟩, h12.trans h2, hy, mul_ne_zero hb0 ha, hz₀, ho, fun j =>
    ⟨fun i i' h => hri j (congrArg Subtype.val h), ?_⟩⟩
  apply Polynomial.map_injective (algebraMap c'.O (Qbar l)) Subtype.val_injective
  have e : (mat y.ρ (sg j)).map (algebraMap c'.O (Qbar l)) = mat ρ (sg j) := by
    rw [← hy.1]
    rfl
  rw [← Matrix.charpoly_map, e, hrc j, Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rfl
