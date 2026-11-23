import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces

noncomputable section

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

namespace MeanNormSquaredBound

section Abstract

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma inner_sum_sum {ι κ : Type} (S : Finset ι) (S' : Finset κ) (c : ι → ℂ) (d : κ → ℂ)
    (v : ι → E) (v' : κ → E) :
    inner ℂ (∑ j ∈ S', d j • v' j) (∑ i ∈ S, c i • v i) =
      ∑ i ∈ S, ∑ j ∈ S', c i * conj (d j) * inner ℂ (v' j) (v i) := by
  rw [inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_smul_right]
  ring

lemma normSq_sum {ι : Type} (S : Finset ι) (c : ι → ℂ) (v : ι → E) :
    ((‖∑ i ∈ S, c i • v i‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, c i * conj (c j) * inner ℂ (v j) (v i) := by
  rw [← inner_sum_sum, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

lemma sum_sum_sum_sum_comm {α β M : Type} [AddCommMonoid M] (P : Finset α) (H : Finset β)
    (f : α → α → β → β → M) :
    ∑ p ∈ P, ∑ p' ∈ P, ∑ h ∈ H, ∑ h' ∈ H, f p p' h h' =
      ∑ h ∈ H, ∑ h' ∈ H, ∑ p ∈ P, ∑ p' ∈ P, f p p' h h' := by
  calc ∑ p ∈ P, ∑ p' ∈ P, ∑ h ∈ H, ∑ h' ∈ H, f p p' h h'
      = ∑ p ∈ P, ∑ h ∈ H, ∑ p' ∈ P, ∑ h' ∈ H, f p p' h h' :=
        Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ h ∈ H, ∑ p ∈ P, ∑ p' ∈ P, ∑ h' ∈ H, f p p' h h' := Finset.sum_comm
    _ = ∑ h ∈ H, ∑ p ∈ P, ∑ h' ∈ H, ∑ p' ∈ P, f p p' h h' :=
        Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ h ∈ H, ∑ h' ∈ H, ∑ p ∈ P, ∑ p' ∈ P, f p p' h h' :=
        Finset.sum_congr rfl fun h _ => Finset.sum_comm

lemma normSq_mean {X α : Type} (L : E →ₗ[ℂ] E) (k : ℂ) (hk : conj k = k) (P : Finset α)
    (c : α → ℂ) (F : Finset X) (a : X → ℂ) (u : X → α → E) :
    ((‖L (k • ∑ p ∈ P, c p • ∑ h ∈ F, a h • u h p)‖ ^ 2 : ℝ) : ℂ) =
      ∑ h ∈ F, ∑ h' ∈ F, a h * conj (a h') *
        (k ^ 2 * ∑ p ∈ P, ∑ p' ∈ P, c p * conj (c p') * inner ℂ (L (u h' p')) (L (u h p))) := by
  have h1 : L (k • ∑ p ∈ P, c p • ∑ h ∈ F, a h • u h p) =
      ∑ p ∈ P, (k * c p) • ∑ h ∈ F, a h • L (u h p) := by
    simp only [map_smul, map_sum, Finset.smul_sum, smul_smul, mul_assoc]
  rw [h1, normSq_sum]
  simp only [inner_sum_sum, Finset.mul_sum]
  rw [sum_sum_sum_sum_comm]
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun h' _ =>
    Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => ?_
  rw [map_mul, hk]
  ring

lemma sum_sub_prod {α β M : Type} [AddCommMonoid M] (A : Finset α) (B : Finset β)
    (f : α × β → M) : ∑ p : ↥A × ↥B, f (p.1.1, p.2.1) = ∑ p ∈ A ×ˢ B, f p := by
  rw [Fintype.sum_prod_type, Finset.sum_product, ← Finset.sum_coe_sort A]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [← Finset.sum_coe_sort B]

lemma abstract_bound (AB : AvgBound) {X Y : Type} (F : Finset X) (a : X → ℂ) (A B : Finset Y)
    (u : X → Y × Y → E) (T : E →ₗ[ℂ] E) (hT : ∀ v, ‖T v‖ ≤ ‖v‖) (e₁ e₂ : Y → ℂ)
    (he₁ : ∀ ρ ∈ A, ‖e₁ ρ‖ = 1)
    (horth : ∀ h ∈ F, ∀ h' ∈ F, ∀ ρ ∈ A, ∀ ρ' ∈ A, ∀ b ∈ B, ∀ b' ∈ B, ρ ≠ ρ' →
      inner ℂ (u h (ρ, b)) (u h' (ρ', b')) = 0) :
    ∃ r₁ r₂ : ℝ, r₁ ≤ r₂ ∧
      (r₁ : ℂ) = ∑ h ∈ F, ∑ h' ∈ F, a h * conj (a h') *
        ((((A.card : ℂ) * (B.card : ℂ))⁻¹) ^ 2 * ∑ p ∈ A ×ˢ B, ∑ p' ∈ A ×ˢ B,
          (e₁ p.1 * e₂ p.2) * conj (e₁ p'.1 * e₂ p'.2) * inner ℂ (T (u h' p')) (T (u h p))) ∧
      (r₂ : ℂ) = ∑ h ∈ F, ∑ h' ∈ F, a h * conj (a h') *
        ((A.card : ℂ)⁻¹ * ((A.card : ℂ)⁻¹ * ∑ ρ ∈ A, ((B.card : ℂ)⁻¹) ^ 2 * ∑ b ∈ B, ∑ b' ∈ B,
          e₂ b * conj (e₂ b') * inner ℂ (u h' (ρ, b')) (u h (ρ, b)))) := by
  set w : Y × Y → E := fun p => ∑ h ∈ F, a h • u h p with hw
  have key := AB E ↥A ↥B (fun p => w (p.1.1, p.2.1)) T (fun ρ => e₁ ρ.1) (fun b => e₂ b.1) hT
    (fun ρ => he₁ ρ.1 ρ.2) (by
      intro ρ ρ' b b' hne
      have hne' : ρ.1 ≠ ρ'.1 := fun h => hne (Subtype.ext h)
      simp only [hw]
      rw [inner_sum_sum]
      refine Finset.sum_eq_zero fun h hh => Finset.sum_eq_zero fun h' hh' => ?_
      rw [horth h' hh' h hh ρ.1 ρ.2 ρ'.1 ρ'.2 b.1 b.2 b'.1 b'.2 hne', mul_zero])
  simp only [Fintype.card_coe] at key
  have e1 : (∑ p : ↥A × ↥B, (e₁ p.1.1 * e₂ p.2.1) • w (p.1.1, p.2.1)) =
      ∑ p ∈ A ×ˢ B, (e₁ p.1 * e₂ p.2) • w p :=
    sum_sub_prod A B (fun p => (e₁ p.1 * e₂ p.2) • w p)
  have e2 : (∑ ρ : ↥A, ‖(B.card : ℂ)⁻¹ • ∑ b : ↥B, e₂ b.1 • w (ρ.1, b.1)‖ ^ 2) =
      ∑ ρ ∈ A, ‖(B.card : ℂ)⁻¹ • ∑ b ∈ B, e₂ b • w (ρ, b)‖ ^ 2 := by
    rw [← Finset.sum_coe_sort A]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [← Finset.sum_coe_sort B]
  rw [e1, e2] at key
  refine ⟨_, _, key, ?_, ?_⟩
  · exact normSq_mean T _ (by simp) (A ×ˢ B) (fun p => e₁ p.1 * e₂ p.2) F a u
  · have h3 : ∀ ρ, ((‖(B.card : ℂ)⁻¹ • ∑ b ∈ B, e₂ b • w (ρ, b)‖ ^ 2 : ℝ) : ℂ) =
        ∑ h ∈ F, ∑ h' ∈ F, a h * conj (a h') * (((B.card : ℂ)⁻¹) ^ 2 * ∑ b ∈ B, ∑ b' ∈ B,
          e₂ b * conj (e₂ b') * inner ℂ (u h' (ρ, b')) (u h (ρ, b))) := fun ρ =>
      normSq_mean LinearMap.id _ (by simp) B e₂ F a (fun h b => u h (ρ, b))
    rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_sum]
    simp only [h3, Complex.ofReal_inv, Complex.ofReal_natCast]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h' _ => Finset.sum_congr rfl fun ρ _ =>
      Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
    ring

end Abstract

lemma norm_psi {K : Type} [CommRing K] (ψ : AddChar K ℂ) (hu : ∀ x : K, conj (ψ x) = ψ (-x))
    (x : K) : ‖ψ x‖ = 1 := by
  have h1 : ψ x * conj (ψ x) = 1 := by
    rw [hu, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h1
  have h2 : ‖ψ x‖ ^ 2 = 1 := by exact_mod_cast h1
  have h3 : (‖ψ x‖ - 1) * (‖ψ x‖ + 1) = 0 := by ring_nf; rw [h2]; ring
  rcases mul_eq_zero.mp h3 with h | h
  · linarith
  · have := norm_nonneg (ψ x); linarith

end MeanNormSquaredBound

open MeanNormSquaredBound in
theorem thetaAverageLower : Formalism.FourierDecayAlt.A6.ThxLower := by
  intro GI A2V UGE ExponentialIntegralMeasures CSA MM CPSD KG GRC AB CNE CM PL K _ _ _ R ψ hD hchar m hm n₀ F Om Lc hF hOm D
  classical
  set Sg : Finset K := (D.A ×ˢ D.B).image (fun p => p.1 + p.2) with hSg
  have hLat : IsLat (perp ψ D.L₂) := (PL K R ψ hD hchar D.L₂ D.lat₂).1
  have hAL : ∀ ρ ∈ D.A, ρ ∈ D.L₂ := D.repsA.1
  have hBR : ∀ b ∈ D.B, b ∈ R.toAddSubgroup := D.repsB.1
  have hmemSg : ∀ ρ ∈ D.A, ∀ b ∈ D.B, ρ + b ∈ Sg := by
    intro ρ hρ b hb
    exact Finset.mem_image.mpr ⟨(ρ, b), Finset.mem_product.mpr ⟨hρ, hb⟩, rfl⟩
  have hSgL : ∀ σ ∈ Sg, σ ∈ D.L₂ := by
    intro σ hσ
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hσ
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    exact D.L₂.add_mem (hAL _ hp1) (D.le₂ (hBR _ hp2))
  obtain ⟨V, hV, hGI⟩ := GI K R ψ hD hchar m hm n₀ F hF Om Sg (perp ψ D.L₂) hOm hLat D.omStable
    D.nsInv (by
      intro σ hσ σ' hσ' l hl
      exact hl _ (D.L₂.sub_mem (hSgL σ hσ) (hSgL σ' hσ')))
  refine ⟨V, hV, ?_⟩
  intro t τ cr ht hcr hsh z₁ hz₁ a

  set F' : Finset (Point K × Kˣ) := F ×ˢ Sg.image τ with hF'
  have hmemF' : ∀ h ∈ F, ∀ ρ ∈ D.A, ∀ b ∈ D.B, (h, τ (ρ + b)) ∈ F' := by
    intro h hh ρ hρ b hb
    exact Finset.mem_product.mpr ⟨hh, Finset.mem_image_of_mem τ (hmemSg ρ hρ b hb)⟩
  obtain ⟨hc1, hc2⟩ := CPSD KG ExponentialIntegralMeasures MM K R ψ hD m cr (cutSet m Om t) F' hcr (by
    intro p hp p' hp'
    rw [hF _ (Finset.mem_product.mp hp).1, hF _ (Finset.mem_product.mp hp').1])
  obtain ⟨n, u₀, T, hT, hG, hGc⟩ := GRC (Point K × Kˣ) F'
    (fun p p' => uGram R ψ m cr Set.univ p.1 p'.1 p.2 p'.2)
    (fun p p' => uGram R ψ m cr (cutSet m Om t) p.1 p'.1 p.2 p'.2) hc1 hc2

  obtain ⟨r₁, r₂, hr, hr₁, hr₂⟩ := abstract_bound AB F a D.A D.B
    (fun h p => u₀ (h, τ (p.1 + p.2))) T hT (fun ρ => ψ (-(z₁ * ρ))) (fun b => ψ (-(z₁ * b)))
    (fun ρ _ => norm_psi ψ hD.unitary _) (by
      intro h hh h' hh' ρ hρ ρ' hρ' b hb b' hb' hne
      simp only
      rw [hG _ (hmemF' h' hh' ρ' hρ' b' hb') _ (hmemF' h hh ρ hρ b hb)]
      simp only
      rw [UGE ExponentialIntegralMeasures CSA MM K R ψ hD m h' h _ _ cr (by rw [hF h hh, hF h' hh']) hcr]
      by_contra hcon
      have hNs : Ns R ψ m h' h (τ (ρ' + b')) (τ (ρ + b)) ≠ 0 := fun h0 => hcon (by rw [h0, mul_zero])
      have hmem := A2V K R ψ hD m hm h' h _ _ (by rw [hF h hh, hF h' hh']) hNs
      rw [hsh ρ' hρ' b' hb', hsh ρ hρ b hb] at hmem
      have h5 : ρ' - ρ ∈ R.toAddSubgroup := by
        have h6 : ρ' - ρ = (((t⁻¹ : Kˣ) : K) + (ρ' + b') - (((t⁻¹ : Kˣ) : K) + (ρ + b))) + (b - b') := by
          ring
        rw [h6]
        exact R.toAddSubgroup.add_mem hmem (R.toAddSubgroup.sub_mem (hBR b hb) (hBR b' hb'))
      obtain ⟨x, _, hx⟩ := D.repsA.2 ρ' (hAL ρ' hρ')
      have e1 := hx ρ ⟨hρ, h5⟩
      have e2 := hx ρ' ⟨hρ', by rw [sub_self]; exact R.toAddSubgroup.zero_mem⟩
      exact hne (e1.trans e2.symm))
  have hr₁' : (r₁ : ℂ) = ∑ h ∈ F, ∑ h' ∈ F, a h * conj (a h') *
      ((D.A.card : ℂ)⁻¹ * NsK R ψ (m + 1) h h' z₁) := by
    rw [hr₁]
    refine Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun h' hh' => ?_
    congr 1
    rw [← CNE CM PL K R ψ hD hchar (m + 1) F Om Lc D hOm.2.1 z₁ hz₁ h hh h' hh']
    congr 1
    refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun p' hp' => ?_
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    obtain ⟨hp1', hp2'⟩ := Finset.mem_product.mp hp'
    rw [hGc _ (hmemF' h hh p.1 hp1 p.2 hp2) _ (hmemF' h' hh' p'.1 hp1' p'.2 hp2')]
    simp only
    rw [hGI t _ _ cr ht hcr _ (hmemSg p.1 hp1 p.2 hp2) _ (hmemSg p'.1 hp1' p'.2 hp2')
      (hsh p.1 hp1 p.2 hp2) (hsh p'.1 hp1' p'.2 hp2') h hh h' hh']
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    have q1 : -(z₁ * p.1) + -(z₁ * p.2) = -(z₁ * (p.1 + p.2)) := by ring
    have q2 : -(z₁ * p'.1) + -(z₁ * p'.2) = -(z₁ * (p'.1 + p'.2)) := by ring
    rw [q1, q2]
  have hr₂' : (r₂ : ℂ) = ∑ h ∈ F, ∑ h' ∈ F, a h * conj (a h') *
      ((D.A.card : ℂ)⁻¹ * thx R ψ m cr D.A D.B τ z₁ h h') := by
    rw [hr₂]
    refine Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun h' hh' => ?_
    congr 2
    unfold thx
    congr 1
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    congr 1
    refine Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun b' hb' => ?_
    simp only
    rw [hG _ (hmemF' h hh ρ hρ b hb) _ (hmemF' h' hh' ρ hρ b' hb')]
  have hApos : 0 < (D.A.card : ℝ) := by
    obtain ⟨x, hx, _⟩ := D.repsA.2 0 D.L₂.zero_mem
    exact_mod_cast Finset.card_pos.mpr ⟨x, hx.1⟩
  have hAne : (D.A.card : ℂ) ≠ 0 := by
    exact_mod_cast hApos.ne'
  have hfin : ∑ h ∈ F, ∑ h' ∈ F, a h * conj (a h') *
      (thx R ψ m cr D.A D.B τ z₁ h h' - NsK R ψ (m + 1) h h' z₁) =
      (((D.A.card : ℝ) * (r₂ - r₁) : ℝ) : ℂ) := by
    push_cast
    rw [hr₁', hr₂', ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h' _ => ?_
    field_simp
  rw [hfin]
  refine ⟨Complex.ofReal_im _, ?_⟩
  rw [Complex.ofReal_re]
  exact mul_nonneg hApos.le (sub_nonneg.mpr hr)

end Formalism.FourierDecayAlt.P
