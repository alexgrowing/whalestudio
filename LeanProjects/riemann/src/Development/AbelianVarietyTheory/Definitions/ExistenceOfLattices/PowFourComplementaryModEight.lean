import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst

noncomputable section

namespace GlobalTheory.FrameUnif.Tests

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem perFr_add (X : Data E r) (x : Frame X.Ψ r) (v w : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    perFr X x (v + w) τ i = perFr X x v τ i + perFr X x w τ i := by
  have he : ∀ τ : E →+* ℂ, Data.emb τ (v + w) = Data.emb τ v + Data.emb τ w := fun τ => by
    funext a; simp [Data.emb]
  unfold perFr
  split_ifs
  · rw [he, Matrix.mulVec_add]; rfl
  · simp
  · rw [he]; simp [hermC, mul_add, Finset.sum_add_distrib]
  · simp
  · simp

theorem exists_isPerFr {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) (k : Fin F.n) : ∃ Pf, IsPerFr e F M k Pf :=
  ⟨fun x => AddMonoidHom.mk' (fun a j => perFr (M.X k) x (M.φ k a : Fin r → E) (relab c σ (e j).1) (e j).2)
    (fun a b => by funext j; simp [perFr_add]), fun _ _ _ => rfl⟩

theorem normConst_pos {g : ℕ} (ty : Fin g → (E →+* ℂ)) {ξ₀ : E} (h : ξ₀ ≠ 0) : 0 < normConst ty ξ₀ := by
  unfold normConst
  refine Real.sqrt_pos.2 (div_pos (by positivity) (Finset.prod_pos fun j _ => ?_))
  have : ty j ξ₀ ≠ 0 := (map_ne_zero _).2 h
  positivity

theorem isNormUn_ne {g : ℕ} {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
    {M : ModelsOf F r} {k : Fin F.n} (T : ThetaData e F M k) (un : (M.X k).dom → FrPt Xo c (CAt σ))
    (h : IsNormUn T un) (x : (M.X k).dom) : ∃ κ : ℂ, κ ≠ 0 ∧ IsThetaPt T (T.co.symm x.1) κ (un x) := by
  obtain ⟨κ, h1, h2⟩ := h x
  refine ⟨κ, fun h0 => ?_, h2⟩
  have hd := (T.norm (T.co.symm x.1) (by simpa using x.2)).1.ne_zero
  have hc := normConst_pos (fun j => relab c σ (e j).1) (M.X k).ξ0_ne
  rw [h0] at h1
  have : (normConst (fun j => relab c σ (e j).1) (M.X k).ξ0 : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  exact mul_ne_zero this hd (by simpa using h1.symm)

theorem pow_four_complementary_modEight (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    (∃ v : 𝓞 E, H.w0 ^ 4 + (1 - H.w0) ^ 4 = 1 + 8 * v) ∧ ∃ v : 𝓞 E, H.w0 ^ 4 * (1 - H.w0) ^ 4 = 8 * v := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, H.d = 16 * k + 7 := ⟨H.d / 16, by have := H.d_mod; omega⟩
  have h1 := H.rt_sq
  have h2 := H.two_weight_eq_one_add_root
  rw [hk] at h1
  push_cast at h1
  have h4 : (4 : 𝓞 E) * (H.w0 ^ 2 - H.w0 + (4 * k + 2)) = 0 := by
    have : H.rt = 2 * H.w0 - 1 := by linear_combination -h2
    rw [this] at h1
    linear_combination h1
  have hq : H.w0 ^ 2 - H.w0 + (4 * k + 2) = 0 := (mul_eq_zero.1 h4).resolve_left (by norm_num)
  refine ⟨⟨2 * k + 4 * k ^ 2, ?_⟩, ⟨2 * (2 * k + 1) ^ 4, ?_⟩⟩
  · linear_combination (2 * (H.w0 ^ 2 - H.w0) + 4 - 2 * (4 * k + 2)) * hq
  · have : H.w0 * (1 - H.w0) = 4 * k + 2 := by linear_combination -hq
    rw [← mul_pow, this]; ring

theorem sign_genus_one (t : ℂ) (ht : 0 < t.im) :
    (hermForm (g := 1) (fun _ _ => ((t.im⁻¹ : ℝ) : ℂ)) (fun _ => 1) (fun _ => t)).im =
      -(omegaStd (h := 1) (Pi.single (Sum.inl 0) 1) (Pi.single (Sum.inr 0) 1) : ℤ) := by
  simp [hermForm, omegaStd, Matrix.mulVec, dotProduct, ← Complex.ofReal_inv, ht.ne']

open Classical in

theorem models_of_latModel {g : ℕ} {ty : Fin g → (E →+* ℂ)} {σ' : KA l →+* ℂ} (F : FamilyUnif Xo σ' ty)
    (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0)
    (hcm : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ)
    (Gm : Matrix (Fin r) (Fin r) E) (hG : ∀ a b, cc (Gm a b) = Gm b a) (hdet : Gm.det ≠ 0)
    (hrk : r = Dw.p + Dw.q)
    (hsig : ∀ τ : Ψ, ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧
      gram τ.1 Gm P = Matrix.diagonal fun a : Fin r => ((sgn Dw.q (a : ℕ) : ℝ) : ℂ))
    (ξ₀ : E) (hξ : cc ξ₀ = -ξ₀) (hξ0 : ξ₀ ≠ 0) (hneg : ∀ τ ∈ Ψ, (τ ξ₀).im < 0)
    (hL : ∀ i, LatModel l Ψ Gm ξ₀ Dw.q (F.Di i)) :
    ∃ M : ModelsOf F r, ModelBase M ∧ NegXi M := by
  choose φ0 h1 h2 h3 h4 h5 h6 h7 using hL
  choose den hd1 hd2 using h4
  choose m hm1 hm2 using h7
  let X : Fin F.n → Data E r := fun i =>
    { Ψ := Ψ, cmType := hcm, Gm := Gm, Gm_herm := hG, Gm_det := hdet, p0 := Dw.q, p0_le := by omega
      signature := hsig
      Λ := LinearMap.range (φ0 i)
      Λ_fg := by
        have := (F.Di i).fin
        rw [LinearMap.range_eq_map]
        exact (Module.Finite.fg_top).map _
      Λ_span := h3 i, den := den i, den_ne := hd1 i, Λ_int := hd2 i
      Γ := princ l Gm (F.Di i) (φ0 i)
      Γ_stab := fun _ hγ => hγ.1
      Γ_index := h5 i, Γ_free := h6 i
      χ := fun _ _ => 1
      χ_mul := fun _ _ _ _ _ => (mul_one 1).symm
      χ_add := fun _ _ _ _ => (mul_one 1).symm
      χ_fin := fun _ => ⟨1, one_pos, fun _ _ => one_pow 1⟩
      ξ0 := ξ₀, ξ0_im := hξ, ξ0_ne := hξ0, κ0 := 2 * ξ₀, κ0_xi := Or.inl rfl
      κ0_sign := fun τ => by
        have := hneg τ.1 τ.2
        rw [map_mul, map_ofNat]
        simp
        linarith
      m := m i, m_pos := hm1 i
      transv := fun ξ hξ' h0 s hs hsi => hm2 i _ (Or.inl rfl) ξ hξ' h0 s hs hsi }
  refine ⟨⟨X, fun i => LinearEquiv.ofInjective (φ0 i) (h1 i)⟩, ?_, fun _ τ hτ => hneg τ hτ⟩
  exact
    { rank := hrk
      type := fun k => ⟨rfl, hΨ⟩
      chi := fun _ _ _ => rfl
      ef := fun k a b => h2 k a b
      gam := fun k γ => Iff.rfl
      domStab := fun k _ hx => ⟨fun _ hb => dom_rmul (X k) hx hb, fun _ hγ => dom_lact (X k) hx hγ.1⟩ }

theorem thetaData_of {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) (k : Fin F.n) (Pf : Frame (M.X k).Ψ r → ((F.Di k).La →+ (Fin g → ℂ)))
    (per : IsPerFr e F M k Pf) (m : ℕ) (co : (Fin m → ℂ) ≃L[ℂ] Frame (M.X k).Ψ r)
    (ho : IsOpen (M.X k).dom) (hc : IsPreconnected (M.X k).dom)
    (holPer : IsHolPeriods (F.Di k) (fun j => relab c σ (e j).1) (co ⁻¹' (M.X k).dom) (fun b => Pf (co b)))
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (F.Di k).La)
    (sympl : ∀ a a', (F.Di k).EF (bas a) (bas a') = -omegaStd a a')
    (adapt : (∀ i, ∃ v, H.w0 ^ 4 • bas (Pi.single (Sum.inl i) 1) = bas (Pi.single (Sum.inl i) 1) + (8 : ℕ) • v) ∧
      ∀ i, ∃ v, H.w0 ^ 4 • bas (Pi.single (Sum.inr i) 1) = (8 : ℕ) • v)
    (h ta : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (norm : ∀ b ∈ co ⁻¹' (M.X k).dom, IsUnit (h b).det ∧ (ta b).IsSymm ∧ ((ta b).map Complex.im).PosDef ∧ ∀ i,
      h b *ᵥ Pf (co b) (bas (Pi.single (Sum.inl i) 1)) = Pi.single i 1 ∧
      h b *ᵥ Pf (co b) (bas (Pi.single (Sum.inr i) 1)) = ta b *ᵥ Pi.single i 1)
    (hol : ∀ i j, DifferentiableOn ℂ (fun b => h b i j) (co ⁻¹' (M.X k).dom) ∧
      DifferentiableOn ℂ (fun b => ta b i j) (co ⁻¹' (M.X k).dom)) :
    Nonempty (ThetaData e F M k) := by
  have hc' : IsPreconnected (co ⁻¹' (M.X k).dom) := co.toHomeomorph.isPreconnected_preimage.2 hc
  obtain ⟨c₁, c₂, h1, h2, fr, f1, f2, f3, f4, f5⟩ := F.theta k m _ (fun b => Pf (co b)) bas (-1) h ta
    (ho.preimage co.continuous) hc' holPer (fun a b => by simp [sympl])
    (fun b hb => ⟨(norm b hb).2.2.1, (norm b hb).2.2.2⟩)
  exact ⟨⟨Pf, per, fun x hx => by simpa using holPer.1 (co.symm x) (by simpa using hx), m, co, holPer, bas, sympl,
    adapt, h, ta, norm, hol, c₁, c₂, h1, h2, fr, f1, f2, f3, f4, f5⟩⟩

end GlobalTheory.FrameUnif.Tests
