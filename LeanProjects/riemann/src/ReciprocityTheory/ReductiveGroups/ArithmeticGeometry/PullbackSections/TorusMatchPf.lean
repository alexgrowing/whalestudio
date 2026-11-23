import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.TorusPin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.EmbeddingHermitianPairs

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Complex ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexConjugate

section Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def hLin (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u : Fin r → ℂ) : (Fin r → ℂ) →ₗ[ℂ] ℂ where
  toFun v := hermC τ G v u
  map_add' v w := by simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [hermC, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring

theorem hermC_mulVec (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) (y v : Fin r → ℂ) :
    hermC τ G (x.mulVec y) v = ∑ a, y a * hermC τ G (col x a) v := by
  simp only [hermC, Matrix.mulVec, dotProduct, col, Finset.sum_mul, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => ?_
  ring

theorem hermC_symm (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (hG : ∀ a b, cc (G a b) = G b a) (u v : Fin r → ℂ) :
    hermC τ G u v = conj (hermC τ G v u) :=
  (ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs.hermC_conj τ G hG v u).symm

variable (X : Data E r) (x : Frame X.Ψ r)

theorem ortho_gram (hx : X.IsOrtho x) (τ : X.Ψ) (a b : Fin r) :
    hermC τ.1 X.Gm (col (mat x τ) a) (col (mat x τ) b) = if a = b then ((sgn X.p0 a : ℝ) : ℂ) else 0 := by
  have := congrFun (congrFun (hx τ) a) b
  simp only [gram, Matrix.of_apply, Matrix.diagonal_apply] at this
  rw [this]

theorem sgn_sq (a : ℕ) : (sgn X.p0 a : ℂ) * (sgn X.p0 a : ℂ) = 1 := by
  unfold sgn
  split_ifs <;> norm_num

theorem inv_coord (hx : X.IsOrtho x) (τ : X.Ψ) (hdet : (mat x τ).det ≠ 0) (w : Fin r → ℂ) (b : Fin r) :
    ((mat x τ)⁻¹.mulVec w) b = (sgn X.p0 b : ℂ) * hermC τ.1 X.Gm w (col (mat x τ) b) := by
  have hw : w = (mat x τ).mulVec ((mat x τ)⁻¹.mulVec w) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]
  conv_rhs => rw [hw, hermC_mulVec]
  simp only [ortho_gram X x hx, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← mul_assoc, mul_comm _ (sgn X.p0 b : ℂ), ← mul_assoc, sgn_sq, one_mul]

end Frame

section Torus

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {x : Frame X.Ψ r}

theorem e_mul (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt X x) (hx : X.IsOrtho x) (hdet : ∀ τ : X.Ψ, (mat x τ).det ≠ 0)
    (τ : X.Ψ) (a : Fin r) :
    A.e τ a = ((sgn X.p0 a : ℂ) * hermC τ.1 X.Gm (A.e τ a) (col (mat x τ) a)) • col (mat x τ) a := by
  have hzero : ∀ b, b ≠ a → hermC τ.1 X.Gm (A.e τ a) (col (mat x τ) b) = 0 := by
    intro b hb
    rcases lt_or_gt_of_ne hb with hlt | hgt
    · have hmem : col (mat x τ) b ∈
          Submodule.span ℂ (Set.range fun c : Fin a => A.e τ (Fin.castLE a.2.le c)) := by
        rw [A.e_flag τ a a.2.le]
        exact Submodule.subset_span ⟨⟨b, hlt⟩, rfl⟩
      have hker : Submodule.span ℂ (Set.range fun c : Fin a => A.e τ (Fin.castLE a.2.le c)) ≤
          LinearMap.ker (hLin τ.1 X.Gm (A.e τ a)) := by
        rw [Submodule.span_le]
        rintro _ ⟨c, rfl⟩
        show hermC τ.1 X.Gm (A.e τ (Fin.castLE a.2.le c)) (A.e τ a) = 0
        rw [A.e_orth, if_neg]
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_castLE] at this
        omega
      have h0 : hermC τ.1 X.Gm (col (mat x τ) b) (A.e τ a) = 0 := hker hmem
      rw [hermC_symm τ.1 X.Gm X.Gm_herm, h0, map_zero]
    · have hle : (a : ℕ) + 1 ≤ r := a.2
      have hmem : A.e τ a ∈
          Submodule.span ℂ (Set.range fun c : Fin ((a : ℕ) + 1) => col (mat x τ) (Fin.castLE hle c)) := by
        rw [← A.e_flag τ ((a : ℕ) + 1) hle]
        exact Submodule.subset_span ⟨⟨a, by omega⟩, rfl⟩
      have hker : Submodule.span ℂ (Set.range fun c : Fin ((a : ℕ) + 1) => col (mat x τ) (Fin.castLE hle c)) ≤
          LinearMap.ker (hLin τ.1 X.Gm (col (mat x τ) b)) := by
        rw [Submodule.span_le]
        rintro _ ⟨c, rfl⟩
        show hermC τ.1 X.Gm (col (mat x τ) (Fin.castLE hle c)) (col (mat x τ) b) = 0
        rw [ortho_gram X x hx, if_neg]
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_castLE] at this
        have := c.2
        omega
      exact hker hmem
  have hw := inv_coord X x hx τ (hdet τ) (A.e τ a)
  have he : A.e τ a = (mat x τ).mulVec ((mat x τ)⁻¹.mulVec (A.e τ a)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hdet τ)), Matrix.one_mulVec]
  obtain ⟨y, hy⟩ : ∃ y, y = (mat x τ)⁻¹.mulVec (A.e τ a) := ⟨_, rfl⟩
  rw [← hy] at hw he
  conv_lhs => rw [he]
  funext k
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, col]
  rw [Finset.sum_eq_single a]
  · rw [hw a]
    ring
  · intro b _ hb
    rw [hw b, hzero b hb]
    ring
  · simp

end Torus

section Relab

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) (σ : c.F →+* ℂ)

theorem relab_inj : Function.Injective (relab c σ) := by
  intro τ₁ τ₂ h
  ext a
  have := congrArg (fun f : E →+* ℂ => f a) h
  exact congrArg Subtype.val (σ.injective this)

theorem relab_rt (hσ : GoodEmb c σ) (τ' : E →+* ℂ) :
    relab c σ τ' (H.rt : E) = H.rt0 ↔ τ' (H.rt : E) = H.rt0 := by
  have h0 : H.rt0 ≠ 0 := by
    intro h
    have := H.sqrt_neg_disc_sq
    rw [h] at this
    have hd : (H.d : ℂ) = 0 := by linear_combination this
    exact H.d_prime.ne_zero (by exact_mod_cast hd)
  have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
  have hE : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (fun z : 𝓞 E => (z : E)) H.rt_sq
    simpa using this
  have hsq : (τ' (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
    rw [H.sqrt_neg_disc_sq, ← map_pow, hE, map_neg, map_natCast]
  have hval : relab c σ τ' (H.rt : E) = σ ⟨τ' (H.rt : E), c.conj τ' _⟩ := rfl
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with hx | hx
  · refine ⟨fun _ => hx, fun _ => ?_⟩
    rw [hval, ← hσ0]
    exact congrArg σ (Subtype.ext hx)
  · have h1 : σ ⟨τ' (H.rt : E), c.conj τ' _⟩ = -σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ := by
      rw [← map_neg]
      exact congrArg σ (Subtype.ext hx)
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exfalso
      rw [← hval, h, hσ0] at h1
      exact h0 (by linear_combination h1 / 2)
    · exfalso
      exact h0 (by linear_combination (h.symm.trans hx) / 2)

def relabE : (E →+* ℂ) ≃ (E →+* ℂ) :=
  Equiv.ofBijective (relab c σ) (Finite.injective_iff_bijective.mp (relab_inj c σ))

theorem conjEmb_conjEmb (τ : E →+* ℂ) : conjEmb (conjEmb τ) = τ :=
  RingHom.ext fun a => Complex.conj_conj _

theorem conjugate_eq (τ : E →+* ℂ) : ComplexEmbedding.conjugate τ = conjEmb τ := rfl

def conjE : (E →+* ℂ) ≃ (E →+* ℂ) :=
  ⟨conjEmb, conjEmb, conjEmb_conjEmb, conjEmb_conjEmb⟩

end Relab

section Letters

attribute [local instance] Classical.propDecidable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
  {U : Unf Xo c σ r} (hU : IsUnf U) (hσ : GoodEmb c σ) {k : U.Comp} {x : (U.X k).dom}
  (W : UnfAt U k x) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt (U.X k) x.1)

theorem conj_mem_iff {X : Data E r} (ρ : E →+* ℂ) : conjEmb ρ ∈ X.Ψ ↔ ρ ∉ X.Ψ := by
  have := X.cmType (conjEmb ρ)
  rw [conjugate_eq, conjEmb_conjEmb] at this
  exact this

include hU in
theorem dim_of (ρ : E →+* ℂ) :
    A.T.dim ρ = if ρ ∈ (U.X k).Ψ then (U.X k).p0 else r - (U.X k).p0 := by
  split_ifs with h
  · exact A.dim_pos ⟨ρ, h⟩
  · have hc : conjEmb ρ ∈ (U.X k).Ψ := (conj_mem_iff ρ).mpr h
    have := A.dim_neg ⟨conjEmb ρ, hc⟩
    rwa [conjugate_eq, conjEmb_conjEmb] at this

include hU hσ in
theorem mult_of (ρ : E →+* ℂ) :
    Dw.mult ((relabE c σ).symm (conjEmb ρ)) = if ρ ∈ (U.X k).Ψ then (U.X k).p0 else r - (U.X k).p0 := by
  have hrel : relab c σ ((relabE c σ).symm (conjEmb ρ)) = conjEmb ρ := (relabE c σ).apply_symm_apply _
  have hiff : ((relabE c σ).symm (conjEmb ρ)) (H.rt : E) = H.rt0 ↔ ρ ∉ (U.X k).Ψ := by
    rw [← relab_rt c σ hσ, hrel, ← (hU.2.1 k).2, conj_mem_iff]
  have hr := hU.1
  unfold Datum.mult
  rw [(hU.2.1 k).1]
  split_ifs with h1 h2 h2
  · exact absurd h2 (hiff.mp h1)
  · omega
  · rfl
  · exact absurd (hiff.mpr h2) h1

include hU hσ in

def fibE (ρ : E →+* ℂ) : Fin (A.T.dim ρ) ≃ Fin (Dw.mult ((relabE c σ).symm (conjEmb ρ))) :=
  if h : ρ ∈ (U.X k).Ψ then
    (finCongr (by rw [dim_of hU A, if_pos h])).trans
      (Fin.revPerm.trans (finCongr (by rw [mult_of hU hσ, if_pos h])))
  else finCongr (by rw [dim_of hU A, mult_of hU hσ, if_neg h])

include hU hσ in

def letT : ReciprocityTheory.ChartRestriction.G.I2.Idx A.T.dim ≃ Fin W.g :=
  (Equiv.sigmaCongr ((conjE).trans (relabE c σ).symm) (fun ρ => fibE hU hσ A ρ)).trans W.e.symm

include hU hσ in
theorem letT_e (ρ : E →+* ℂ) (a : Fin (A.T.dim ρ)) :
    W.e (letT hU hσ W A ⟨ρ, a⟩) = ⟨(relabE c σ).symm (conjEmb ρ), fibE hU hσ A ρ a⟩ := by
  rw [letT, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

end Letters

section Map

attribute [local instance] Classical.propDecidable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
  {U : Unf Xo c σ r} (hU : IsUnf U) (hσ : GoodEmb c σ) {k : U.Comp} {x : (U.X k).dom}
  (W : UnfAt U k x) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt (U.X k) x.1)

def yf (τ : (U.X k).Ψ) (b : Fin r) : ℂ :=
  (sgn (U.X k).p0 b : ℂ) * hermC τ.1 (U.X k).Gm (A.e τ b) (col (mat x.1 τ) b)

include hU in
theorem index_lt_signature_of_mem {ρ : E →+* ℂ} (h : ρ ∈ (U.X k).Ψ) (a : Fin (A.T.dim ρ)) : (a : ℕ) < (U.X k).p0 := by
  have h1 := dim_of hU A ρ
  rw [if_pos h] at h1
  have := a.2
  omega

include hU in
theorem index_lt_complementSignature_of_not_mem {ρ : E →+* ℂ} (h : ρ ∉ (U.X k).Ψ) (a : Fin (A.T.dim ρ)) : (a : ℕ) < r - (U.X k).p0 := by
  have h1 := dim_of hU A ρ
  rw [if_neg h] at h1
  have := a.2
  omega

include hU in

def wt (i : ReciprocityTheory.ChartRestriction.G.I2.Idx A.T.dim) : ℂ :=
  if h : i.1 ∈ (U.X k).Ψ then
    (Real.sqrt ((U.X k).c ⟨i.1, h⟩) : ℂ) *
      conj (yf A ⟨i.1, h⟩ ⟨i.2, lt_of_lt_of_le (index_lt_signature_of_mem hU A h i.2) (U.X k).p0_le⟩)
  else
    (Real.sqrt ((U.X k).c ⟨conjEmb i.1, (conj_mem_iff _).mpr h⟩) : ℂ) *
      yf A ⟨conjEmb i.1, (conj_mem_iff _).mpr h⟩
        ⟨(U.X k).p0 + i.2, by have := index_lt_complementSignature_of_not_mem hU A h i.2; have := (U.X k).p0_le; omega⟩

include hU hσ in

def Lmap : (Fin W.g → ℂ) →ₗ[ℂ] ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim where
  toFun z := WithLp.toLp 2 fun i => wt hU A i * z (letT hU hσ W A i)
  map_add' z z' := by
    ext i
    simp [mul_add]
  map_smul' a z := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, PiLp.toLp_apply, PiLp.smul_apply]
    ring

theorem Lmap_apply (z : Fin W.g → ℂ) (i : ReciprocityTheory.ChartRestriction.G.I2.Idx A.T.dim) :
    Lmap hU hσ W A z i = wt hU A i * z (letT hU hσ W A i) := rfl

end Map

section Pin1

attribute [local instance] Classical.propDecidable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
  {U : Unf Xo c σ r} (hU : IsUnf U) (hσ : GoodEmb c σ) {k : U.Comp} {x : (U.X k).dom}
  (W : UnfAt U k x) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt (U.X k) x.1)

theorem fibE_val (ρ : E →+* ℂ) (a : Fin (A.T.dim ρ)) :
    ((fibE hU hσ A ρ a : Fin _) : ℕ) = if ρ ∈ (U.X k).Ψ then (U.X k).p0 - 1 - a else a := by
  unfold fibE
  split_ifs with h
  · simp only [Equiv.trans_apply, finCongr_apply, Fin.val_cast, Fin.revPerm_apply, Fin.val_rev]
    have := index_lt_signature_of_mem hU A h a
    omega
  · simp only [finCongr_apply, Fin.val_cast]

theorem perFr_conj (X : Data E r) (y : Frame X.Ψ r) (v : Fin r → E) {ρ : E →+* ℂ} (h : ρ ∈ X.Ψ) (i : ℕ)
    (hi : i < X.p0) :
    perFr X y v (conjEmb ρ) i = hermC ρ X.Gm (col (mat y ⟨ρ, h⟩) ⟨X.p0 - 1 - i, by have := X.p0_le; omega⟩)
      (Data.emb ρ v) := by
  have hc : conjEmb ρ ∉ X.Ψ := fun hc => (conj_mem_iff ρ).mp hc h
  have hcc : conjEmb (conjEmb ρ) ∈ X.Ψ := by rw [conjEmb_conjEmb]; exact h
  unfold perFr
  rw [dif_neg hc, dif_pos hcc, dif_pos (by have := X.p0_le; omega)]
  have key : ∀ (ρ' : E →+* ℂ) (h' : ρ' ∈ X.Ψ), ρ' = ρ →
      hermC ρ' X.Gm (col (mat y ⟨ρ', h'⟩) ⟨X.p0 - 1 - i, by have := X.p0_le; omega⟩) (Data.emb ρ' v) =
        hermC ρ X.Gm (col (mat y ⟨ρ, h⟩) ⟨X.p0 - 1 - i, by have := X.p0_le; omega⟩) (Data.emb ρ v) := by
    rintro _ _ rfl
    rfl
  exact key _ hcc (conjEmb_conjEmb ρ)

theorem perFr_self (X : Data E r) (y : Frame X.Ψ r) (v : Fin r → E) {τ : E →+* ℂ} (h : τ ∈ X.Ψ) (i : ℕ)
    (hi : X.p0 + i < r) :
    perFr X y v τ i = ((mat y ⟨τ, h⟩)⁻¹.mulVec (Data.emb τ v)) ⟨X.p0 + i, hi⟩ := by
  unfold perFr
  rw [dif_pos h, dif_pos hi]

end Pin1

end ReciprocityTheory.ChartRestriction.G.PullbackSections
