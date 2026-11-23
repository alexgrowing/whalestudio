import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIntegralEqSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsThetaInvolution
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousMapGL

noncomputable section

open NumberField MeasureTheory Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.Desc
open PositivityTheory.Rg.BcB (thetaA thetaR)
open scoped InnerProductSpace ComplexConjugate

namespace UpperTheory.V.Z.GSp4Splitting

private theorem integral_invol {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    (p : X → Set X) (hm : ∀ a, a ∈ p a) (he : ∀ a b, b ∈ p a → p b = p a) (ho : ∀ a, IsOpen (p a))
    (hfin : ∀ a, μ (p a) ≠ ⊤) (hpos : ∀ a, μ (p a) ≠ 0) (t : X → X) (ht : ∀ a, t (t a) = a)
    (hpt : ∀ a b, b ∈ p a → t b ∈ p (t a)) (C : Set X) (hC : IsCompact C) (F : X → ℂ) (hz : ∀ x, x ∉ C → F x = 0)
    (hF : ∀ a b, b ∈ p a → F b = F a) :
    ∫ x, F x ∂μ = ∫ x, (((μ.real (p (t x)) / μ.real (p x) : ℝ)) : ℂ) * F (t x) ∂μ := by
  classical
  obtain ⟨T, -, hT⟩ := hC.elim_nhds_subcover p (fun a _ => (ho a).mem_nhds (hm a))
  let Q : Finset (Set X) := T.image p
  have hQ : ∀ S ∈ Q, ∃ a, p a = S := fun S hS => by
    obtain ⟨a, -, ha⟩ := Finset.mem_image.1 hS
    exact ⟨a, ha⟩
  have hsum : ∀ x, F x = ∑ S ∈ Q, S.indicator F x := by
    intro x
    by_cases hx : p x ∈ Q
    · rw [Finset.sum_eq_single (p x), Set.indicator_of_mem (hm x)]
      · intro S hS hne
        obtain ⟨a, rfl⟩ := hQ S hS
        exact Set.indicator_of_notMem (fun h => hne (he a x h).symm) _
      · exact fun h => (h hx).elim
    · have h0 : F x = 0 := hz x fun hc => by
        obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (hT hc)
        exact hx (Finset.mem_image.2 ⟨a, ha, (he a x hxa).symm⟩)
      rw [h0]
      exact (Finset.sum_eq_zero fun S _ => Set.indicator_apply_eq_zero.2 fun _ => h0).symm
  have e1 : ∀ a, (p a).indicator F = (p a).indicator (fun _ => F a) := fun a =>
    Set.indicator_congr fun b hb => hF a b hb
  have e2 : ∀ a, (fun x => (((μ.real (p (t x)) / μ.real (p x) : ℝ)) : ℂ) * (p a).indicator F (t x)) =
      (p (t a)).indicator (fun _ => (((μ.real (p a) / μ.real (p (t a)) : ℝ)) : ℂ) * F a) := by
    intro a
    funext x
    by_cases hx : x ∈ p (t a)
    · have hx' : t x ∈ p a := by simpa [ht] using hpt _ _ hx
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx', he _ _ hx, he _ _ hx', hF _ _ hx']
    · have hx' : t x ∉ p a := fun h => hx (by simpa [ht] using hpt _ _ h)
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx', mul_zero]
  have hi : ∀ a (c : ℂ), Integrable ((p a).indicator (fun _ => c)) μ := fun a c =>
    (integrable_indicator_iff (ho a).measurableSet).2 (integrableOn_const (hfin a))
  have l : ∫ x, F x ∂μ = ∑ S ∈ Q, ∫ x, S.indicator F x ∂μ := by
    rw [← integral_finset_sum]
    · exact integral_congr_ae (Filter.Eventually.of_forall hsum)
    · intro S hS
      obtain ⟨a, rfl⟩ := hQ S hS
      rw [e1]
      exact hi a _
  have r : ∫ x, (((μ.real (p (t x)) / μ.real (p x) : ℝ)) : ℂ) * F (t x) ∂μ =
      ∑ S ∈ Q, ∫ x, (((μ.real (p (t x)) / μ.real (p x) : ℝ)) : ℂ) * S.indicator F (t x) ∂μ := by
    rw [← integral_finset_sum]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only []
      rw [← Finset.mul_sum, ← hsum]
    · intro S hS
      obtain ⟨a, rfl⟩ := hQ S hS
      rw [e2]
      exact hi _ _
  rw [l, r]
  refine Finset.sum_congr rfl fun S hS => ?_
  obtain ⟨a, rfl⟩ := hQ S hS
  rw [e2, e1, integral_indicator_const _ (ho a).measurableSet, integral_indicator_const _ (ho _).measurableSet]
  have hne : (μ.real (p (t a)) : ℂ) ≠ 0 := by
    have : μ.real (p (t a)) ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hpos _, hfin _⟩
    exact_mod_cast this
  simp only [Complex.real_smul]
  push_cast
  field_simp

section Grp

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

private def dc (K : Subgroup G) (a : G) : Set G := {g | ∃ k₁ ∈ K, ∃ k₂ ∈ K, g = k₁ * a * k₂}

omit [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] in
private theorem dc_mul (K : Subgroup G) {k₁ k₂ : G} (h₁ : k₁ ∈ K) (h₂ : k₂ ∈ K) (a : G) :
    dc K (k₁ * a * k₂) = dc K a := by
  ext g
  constructor
  · rintro ⟨l₁, m₁, l₂, m₂, rfl⟩
    exact ⟨l₁ * k₁, K.mul_mem m₁ h₁, k₂ * l₂, K.mul_mem h₂ m₂, by group⟩
  · rintro ⟨l₁, m₁, l₂, m₂, rfl⟩
    exact ⟨l₁ * k₁⁻¹, K.mul_mem m₁ (K.inv_mem h₁), k₂⁻¹ * l₂, K.mul_mem (K.inv_mem h₂) m₂, by group⟩

private theorem integral_inv (μ : Measure G) [μ.IsHaarMeasure] (K : Subgroup G) (hKo : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) : ∃ δ : G → ℂ, (∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ g, δ (k₁ * g * k₂) = δ g) ∧
      ∀ (C : Set G), IsCompact C → ∀ F : G → ℂ, (∀ x, x ∉ C → F x = 0) →
        (∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ g, F (k₁ * g * k₂) = F g) → ∫ g, F g ∂μ = ∫ g, δ g * F g⁻¹ ∂μ := by
  refine ⟨fun g => ((μ.real (dc K g⁻¹) / μ.real (dc K g) : ℝ) : ℂ), fun k₁ h₁ k₂ h₂ g => ?_, fun C hC F hz hF => ?_⟩
  · have e : (k₁ * g * k₂)⁻¹ = k₂⁻¹ * g⁻¹ * k₁⁻¹ := by group
    simp only []
    rw [e, dc_mul K h₁ h₂, dc_mul K (K.inv_mem h₂) (K.inv_mem h₁)]
  · have hm : ∀ a, a ∈ dc K a := fun a => ⟨1, K.one_mem, 1, K.one_mem, by simp⟩
    have ho : ∀ a, IsOpen (dc K a) := fun a => by
      have e : dc K a = ⋃ k ∈ K, (fun x => (k * a)⁻¹ * x) ⁻¹' (K : Set G) := by
        ext g
        simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]
        constructor
        · rintro ⟨l₁, m₁, l₂, m₂, rfl⟩
          exact ⟨l₁, m₁, by rwa [inv_mul_cancel_left]⟩
        · rintro ⟨l₁, m₁, m₂⟩
          exact ⟨l₁, m₁, _, m₂, by group⟩
      rw [e]
      exact isOpen_biUnion fun k _ => hKo.preimage (continuous_const.mul continuous_id)
    have hc : ∀ a, IsCompact (dc K a) := fun a => by
      have e : dc K a = (fun x : G × G => x.1 * a * x.2) '' ((K : Set G) ×ˢ (K : Set G)) := by
        ext g
        constructor
        · rintro ⟨l₁, m₁, l₂, m₂, rfl⟩
          exact ⟨(l₁, l₂), ⟨m₁, m₂⟩, rfl⟩
        · rintro ⟨⟨l₁, l₂⟩, ⟨m₁, m₂⟩, rfl⟩
          exact ⟨l₁, m₁, l₂, m₂, rfl⟩
      rw [e]
      exact (hKc.prod hKc).image (by fun_prop)
    refine integral_invol μ (dc K) hm ?_ ho (fun a => (hc a).measure_lt_top.ne)
      (fun a => ((ho a).measure_pos μ ⟨a, hm a⟩).ne') (fun g => g⁻¹) inv_inv ?_ C hC F hz ?_
    · rintro a b ⟨l₁, m₁, l₂, m₂, rfl⟩
      exact dc_mul K m₁ m₂ a
    · rintro a b ⟨l₁, m₁, l₂, m₂, rfl⟩
      exact ⟨l₂⁻¹, K.inv_mem m₂, l₁⁻¹, K.inv_mem m₁, by group⟩
    · rintro a b ⟨l₁, m₁, l₂, m₂, rfl⟩
      exact hF _ m₁ _ m₂ a

private theorem integral_aut (μ : Measure G) [μ.IsHaarMeasure] (K : Subgroup G) (hKo : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) (t : G →* G) (ht : ∀ g, t (t g) = g) (hK : ∀ k ∈ K, t k ∈ K)
    (C : Set G) (hC : IsCompact C) (F : G → ℂ) (hz : ∀ x, x ∉ C → F x = 0) (hF : ∀ g, ∀ k ∈ K, F (g * k) = F g) :
    ∫ g, F g ∂μ = ∫ g, F (t g) ∂μ := by
  have hv : ∀ a, μ ((fun x => a⁻¹ * x) ⁻¹' (K : Set G)) = μ K := fun a => measure_preimage_mul μ _ _
  have h0 : μ K ≠ 0 := (hKo.measure_pos μ ⟨1, K.one_mem⟩).ne'
  have h1 : μ K ≠ ⊤ := hKc.measure_lt_top.ne
  have h2 : μ.real K ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨h0, h1⟩
  rw [integral_invol μ (fun a => (fun x => a⁻¹ * x) ⁻¹' (K : Set G)) (fun a => by simp [K.one_mem]) ?_
    (fun a => hKo.preimage (continuous_const.mul continuous_id)) (fun a => by rw [hv]; exact h1)
    (fun a => by rw [hv]; exact h0) t ht ?_ C hC F hz ?_]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [Measure.real, hv]
    rw [div_self (by exact h2)]
    simp
  · intro a b hb
    ext g
    simp only [Set.mem_preimage, SetLike.mem_coe] at hb ⊢
    constructor
    · intro h
      simpa [mul_assoc] using K.mul_mem hb h
    · intro h
      simpa [mul_assoc] using K.mul_mem (K.inv_mem hb) h
  · intro a b hb
    simp only [Set.mem_preimage, SetLike.mem_coe] at hb ⊢
    simpa using hK _ hb
  · intro a b hb
    have := hF a _ hb
    rwa [mul_inv_cancel_left] at this

end Grp

section Conc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem thetaF_eq (g : GL (Fin n) (Af E)) : thetaF E n g = thetaR (GlobalTheory.ThetaPull.cFin E) n g := by
  unfold thetaF finOf
  rw [PositivityTheory.Rg.BcB.thetaA, GlobalTheory.CompanionTheory.TwY.ThInv.map_thetaR _ _ _ GlobalTheory.ThetaPull.pFin_conjAd, pFin_finGL]

private theorem thetaF_thetaF (g : GL (Fin n) (Af E)) : thetaF E n (thetaF E n g) = g := by
  have h := GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol (finGL E n g)
  rw [GlobalTheory.CompanionTheory.TwY.ThInv.thetaA_finGL, GlobalTheory.CompanionTheory.TwY.ThInv.thetaA_finGL] at h
  have h2 := congrArg (GeneralLinearGroup.map (pFin E)) h
  rwa [pFin_finGL, pFin_finGL] at h2

private theorem continuous_thetaF : Continuous (thetaF E n) := by
  rw [funext (thetaF_eq (E := E) (n := n))]
  exact Units.continuous_iff.2 ⟨(Units.continuous_coe_inv.matrix_map (continuous_conjFin _)).matrix_transpose,
    (Units.continuous_val.matrix_map (continuous_conjFin _)).matrix_transpose⟩

private def tr (π : CuspSub E n) (g : GL (Fin n) (Af E)) (φ : π.V) : π.V :=
  ⟨finRep E n g φ.1, π.stable (.fin g) φ.1 φ.2⟩

private theorem tr_apply (π : CuspSub E n) (g : GL (Fin n) (Af E)) (φ : π.V) (x : GA E n) :
    (tr π g φ).1.1 x = φ.1.1 (x * finGL E n g) := rfl

private theorem tr_mul (π : CuspSub E n) (g g' : GL (Fin n) (Af E)) (φ : π.V) :
    tr π (g * g') φ = tr π g (tr π g' φ) :=
  Subtype.ext (by simp [tr])

private theorem form_R {π : CuspSub E n} {K : Subgroup (GL (Fin n) (Af E))} (hKo : IsOpen (K : Set (GL (Fin n) (Af E))))
    (hKc : IsCompact (K : Set (GL (Fin n) (Af E)))) [MeasurableSpace (GL (Fin n) (Af E))]
    [BorelSpace (GL (Fin n) (Af E))] {μf : Measure (GL (Fin n) (Af E))} [μf.IsHaarMeasure] (D : Rl π K μf)
    (h : {h : GL (Fin n) (Af E) → ℂ // IsHeckeF K h}) (u : D.U) (L : π.V →ₗ[ℂ] ℂ) :
    L (D.i (D.R h u)) = ∫ g, h.1 g * L (tr π g (D.i u)) ∂μf := by
  obtain ⟨S, hS⟩ := GlobalTheory.CompanionTheory.HeckeStabY.exists_integral_eq_sum μf K hKo hKc h.1 h.2.1
  have hfix : ∀ k ∈ K, tr π k (D.i u) = D.i u := fun k hk => Subtype.ext ((D.rng _).1 ⟨u, rfl⟩ k hk)
  have hr : ∀ g, ∀ k ∈ K, h.1 (g * k) = h.1 g := fun g k hk => by simpa using h.2.2 1 K.one_mem k hk g
  have key : ∀ M : π.V →ₗ[ℂ] ℂ, ∫ g, h.1 g * M (tr π g (D.i u)) ∂μf =
      M (∑ s ∈ S, (((μf.real (K : Set (GL (Fin n) (Af E))) : ℝ) : ℂ) * h.1 s) • tr π s (D.i u)) := by
    intro M
    rw [hS _ (fun g k hk => by simp only [hr g k hk, tr_mul, hfix k hk]) (fun g hg => by simp [hg]), map_sum,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by rw [map_smul, smul_eq_mul, mul_assoc]
  rw [key]
  congr 1
  refine Subtype.ext (Subtype.ext ?_)
  rw [D.hR]
  funext x
  exact key
    { toFun := fun φ => φ.1.1 x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

end Conc

theorem rlHecke :
    HeckeMem → RlHecke := by
  intro _ E _ _ _ n _ π _ K hKo hKc hKθ _ _ μf _ D
  have hfix : ∀ u, ∀ k ∈ K, tr π k (D.i u) = D.i u := fun u k hk => Subtype.ext ((D.rng _).1 ⟨u, rfl⟩ k hk)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨δ, hδ, hint⟩ := integral_inv μf K hKo hKc
    have hsym := D.pet.1
    have htr : ∀ g φ ψ, D.H (tr π g φ) (tr π g ψ) = D.H φ ψ := fun g φ ψ =>
      D.pet.2.2.2.1 (finGL E n g) φ ψ _ _ (tr_apply π g φ) (tr_apply π g ψ)
    have hone : ∀ φ, tr π 1 φ = φ := fun φ => Subtype.ext (by simp [tr])
    have hmove : ∀ g φ ψ, D.H (tr π g φ) ψ = D.H φ (tr π g⁻¹ ψ) := fun g φ ψ => by
      rw [← htr g φ, ← tr_mul, mul_inv_cancel, hone]
    have hh' : IsHeckeF K (fun g => δ g * conj (h.1 g⁻¹)) := by
      refine ⟨HasCompactSupport.mul_left (f := δ) (f' := fun g => conj (h.1 g⁻¹)) ?_, fun k₁ h₁ k₂ h₂ g => ?_⟩
      · exact (h.2.1.comp_homeomorph (Homeomorph.inv _)).comp_left (g := fun z : ℂ => conj z) (map_zero _)
      · have e : (k₁ * g * k₂)⁻¹ = k₂⁻¹ * g⁻¹ * k₁⁻¹ := by group
        simp only []
        rw [hδ _ h₁ _ h₂, e, h.2.2 _ (K.inv_mem h₂) _ (K.inv_mem h₁)]
    refine ⟨⟨_, hh'⟩, fun x y => ?_⟩
    rw [D.inner_eq, D.inner_eq, ← hsym, form_R hKo hKc D h x (D.H (D.i y)), form_R hKo hKc D _ y (D.H (D.i x)),
      ← integral_conj, hint (tsupport h.1) h.2.1]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      simp only []
      rw [map_mul, hsym, hmove, inv_inv, mul_assoc]
    · intro g hg
      simp [image_eq_zero_of_notMem_tsupport hg]
    · intro k₁ h₁ k₂ h₂ g
      have e := hmove k₁⁻¹ (D.i y) (tr π g (D.i x))
      rw [hfix y _ (K.inv_mem h₁), inv_inv] at e
      rw [h.2.2 _ h₁ _ h₂, tr_mul, tr_mul, hfix x _ h₂, ← e]
  · have hh' : IsHeckeF K (fun g => h.1 (thetaF E n g)) := by
      refine ⟨h.2.1.comp_homeomorph ⟨⟨thetaF E n, thetaF E n, thetaF_thetaF, thetaF_thetaF⟩,
        continuous_thetaF, continuous_thetaF⟩, fun k₁ h₁ k₂ h₂ g => ?_⟩
      have e := h.2.2 _ (hKθ _ h₁) _ (hKθ _ h₂) (thetaF E n g)
      simpa only [thetaF_eq, map_mul] using e
    refine ⟨⟨_, hh'⟩, rfl, LinearMap.ext fun u => D.inj (Subtype.ext (Subtype.ext (funext fun x => ?_)))⟩
    rw [Module.End.mul_apply, Module.End.mul_apply, D.hΘ, D.hR, D.hR]
    unfold heckeOp
    rw [integral_aut μf K hKo hKc (MonoidHom.mk' (thetaF E n) fun a b => by simp only [thetaF_eq, map_mul])
      thetaF_thetaF hKθ
      (tsupport h.1) h.2.1]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      simp only []
      rw [D.hΘ, map_mul, GlobalTheory.CompanionTheory.TwY.ThInv.thetaA_finGL]
      rfl
    · intro g hg
      simp [image_eq_zero_of_notMem_tsupport hg]
    · intro g k hk
      have e : h.1 (g * k) = h.1 g := by simpa using h.2.2 1 K.one_mem k hk g
      rw [e, ← tr_apply, ← tr_apply, tr_mul, hfix u k hk]

end UpperTheory.V.Z.GSp4Splitting
