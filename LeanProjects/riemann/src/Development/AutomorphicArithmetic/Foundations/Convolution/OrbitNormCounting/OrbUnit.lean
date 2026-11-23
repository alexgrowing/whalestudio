import Development.AutomorphicArithmetic.Foundations.Convolution.OrbitNormCounting.NormCount

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

private theorem avg_const' {H : Type} [Group H] (c : ℂ) : avg (fun _ : H => c) = c := by
  have htop : rStab (fun _ : H => c) = ⊤ := by
    rw [eq_top_iff]
    intro k _ x
    rfl
  unfold avg
  rw [htop, Subgroup.index_top, Nat.cast_one, inv_one, one_mul]
  rw [finsum_eq_single (fun _ => c) ((1 : H) : H ⧸ (⊤ : Subgroup H))]
  intro x hx
  exact absurd (QuotientGroup.subsingleton_quotient_top.elim x _) hx

private theorem cptPart_conj {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (T : Subgroup G) {t c : G} (ht : t ∈ T) (hc : c ∈ cptPart T) : t⁻¹ * c * t ∈ cptPart T := by
  unfold cptPart at hc ⊢
  induction hc using Subgroup.closure_induction with
  | mem x hx =>
    apply Subgroup.subset_closure
    refine ⟨T.mul_mem (T.mul_mem (T.inv_mem ht) hx.1) ht, ?_⟩
    let e : G ≃ₜ G := (Homeomorph.mulLeft t⁻¹).trans (Homeomorph.mulRight t)
    have he : ∀ y, e y = t⁻¹ * y * t := fun y => rfl
    have hz : ∀ n : ℤ, (t⁻¹ * x * t) ^ n = t⁻¹ * x ^ n * t := by
      intro n
      simpa using (conj_zpow (a := t⁻¹) (b := x) (i := n))
    have himg : (Subgroup.zpowers (t⁻¹ * x * t) : Set G) = e '' (Subgroup.zpowers x : Set G) := by
      ext y
      constructor
      · rintro ⟨n, rfl⟩
        exact ⟨x ^ n, ⟨n, rfl⟩, (hz n).symm⟩
      · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
        exact ⟨n, hz n⟩
    rw [himg, ← e.image_closure]
    exact hx.2.image e.continuous
  | one => simp
  | mul x y _ _ hx hy =>
    have : t⁻¹ * (x * y) * t = (t⁻¹ * x * t) * (t⁻¹ * y * t) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : t⁻¹ * x⁻¹ * t = (t⁻¹ * x * t)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hx

theorem UpperTheory.ConvolutionTheory.G3.orbUnit :
    UpperTheory.ConvolutionTheory.G3.OrbUnit := by
  intro G _ _ _ θ K δ hθ hδ horb hcpt
  unfold twOrb
  rw [finsum_eq_single _ (DoubleCoset.mk (twCent θ δ) K 1)]
  · obtain ⟨t, k, ht, hk, hx⟩ := DoubleCoset.mk_out_eq_mul (twCent θ δ) K (1 : G)
    generalize hxx : Quotient.out (DoubleCoset.mk (twCent θ δ) K 1) = x at hx ⊢
    rw [mul_one] at hx
    have ht' : t * δ = δ * θ t := ht
    have h1 : (twCent θ δ ⊓ K.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent θ δ)) = 1 := by
      rw [Subgroup.relIndex_eq_one]
      intro c hc
      have hc' := cptPart_conj _ ht hc
      rw [hcpt] at hc hc'
      refine ⟨hc.1, k⁻¹ * (t⁻¹ * c * t) * k, K.mul_mem (K.mul_mem (K.inv_mem hk) hc'.2) hk, ?_⟩
      rw [hx]
      simp [mul_assoc]
    have h2 : (fun k' : K => (K : Set G).indicator (1 : G → ℂ) ((x * k')⁻¹ * δ * θ (x * k'))) = fun _ => 1 := by
      funext k'
      have e : (x * k')⁻¹ * δ * θ (x * k') = (k * k')⁻¹ * δ * θ (k * k') := by
        have : δ * θ (x * k') = t * δ * θ (k * k') := by
          rw [ht', hx, mul_assoc t k, map_mul θ t, mul_assoc]
        rw [mul_assoc, this, hx]
        group
      have hkk : k * k' ∈ K := K.mul_mem hk k'.2
      rw [e, Set.indicator_of_mem]
      · rfl
      · exact K.mul_mem (K.mul_mem (K.inv_mem hkk) hδ) (hθ _ hkk)
    rw [h1, h2, avg_const']
    simp
  · intro q hq
    have h2 : (fun k' : K => (K : Set G).indicator (1 : G → ℂ)
        ((Quotient.out q * k')⁻¹ * δ * θ (Quotient.out q * k'))) = fun _ => 0 := by
      funext k'
      apply Set.indicator_of_notMem
      intro hy
      apply hq
      obtain ⟨k, hk, e⟩ := horb _ hy ⟨_, rfl⟩
      rw [← DoubleCoset.out_eq' (twCent θ δ) K q]
      symm
      rw [DoubleCoset.eq]
      refine ⟨Quotient.out q * k' * k⁻¹, ?_, k * (k' : G)⁻¹, K.mul_mem hk (K.inv_mem k'.2), ?_⟩
      · generalize Quotient.out q * (k' : G) = g at e
        show g * k⁻¹ * δ = δ * θ (g * k⁻¹)
        rw [map_mul, map_inv]
        calc g * k⁻¹ * δ = g * (k⁻¹ * δ * θ k) * (θ k)⁻¹ := by group
          _ = δ * (θ g * (θ k)⁻¹) := by rw [← e]; group
      · show Quotient.out q = _
        group
    rw [h2, avg_const', mul_zero]
