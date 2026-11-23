import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBasisOnZetaPowMulQPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupKummerDlogModPrimePowLevelLStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricLevelH1CoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EdgeClassCupProductGeometricStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCocycleValueExpansionEqLogDerivSmulStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.EdgeLoc

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem pow_chain (f : ℕ → Ω) (hf : ∀ k, f (k + 1) ^ p = f k) (m k : ℕ) : f (m + k) ^ (p ^ k) = f m := by
  induction k with
  | zero => simp
  | succ k ih => rw [← add_assoc, pow_succ', pow_mul, hf, ih]

theorem zeta_le (T : Tower p Ω) {n L : ℕ} (h : n ≤ L) : T.ζ L ^ (p ^ (L - n)) = T.ζ n := by
  have := pow_chain T.ζ T.ζpow n (L - n)
  rwa [Nat.add_sub_cancel' h] at this

theorem gn_fix_zeta (T : Tower p Ω) {n L : ℕ} (h : n ≤ L) {g : Gal p Ω} (hg : g ∈ Gn T L) :
    g (T.ζ n) = T.ζ n := by
  rw [← zeta_le T h, map_pow, ((Basic.mem_gn T L g).1 hg).1]

theorem kum_add (T : Tower p Ω) {n L : ℕ} (h : n ≤ L) {r : Ω} (hr : r ≠ 0) {x : Gal p Ω → ZMod (p ^ n)}
    (hx : IsKum T n (Gn T L) r x) {g g' : Gal p Ω} (hg : g ∈ Gn T L) (hg' : g' ∈ Gn T L) :
    x (g * g') = x g + x g' := by
  obtain ⟨χ, hχ⟩ := Basic.exists_isCyc T n
  rw [Basic.isKum_mul hχ hr hx hg hg', (Basic.isCyc_eq_one_iff hχ g).2 (gn_fix_zeta T h hg), one_mul]

variable (p) in
theorem adjoin_top (L : ℕ) : Algebra.adjoin (O0 p) {xn p L, yn p L} = ⊤ := by
  obtain ⟨b, hb⟩ := GlobalTheory.K5.OnFree.on_free p L
  rw [eq_top_iff]
  intro s _
  have hs : s ∈ Submodule.span (O0 p) (Set.range b) := b.span_eq ▸ Submodule.mem_top
  refine (Submodule.span_le (p := (Algebra.adjoin (O0 p) {xn p L, yn p L}).toSubmodule)).2 ?_ hs
  rintro _ ⟨⟨i, j⟩, rfl⟩
  rw [hb]
  show _ ∈ Algebra.adjoin (O0 p) {xn p L, yn p L}
  have hx : xn p L ∈ Algebra.adjoin (O0 p) {xn p L, yn p L} := Algebra.subset_adjoin (by simp)
  have hy : yn p L ∈ Algebra.adjoin (O0 p) {xn p L, yn p L} := Algebra.subset_adjoin (by simp)
  exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hx _) (Subalgebra.pow_mem _ hy _)

theorem emb_int (L : ℕ) (ι : On p L →ₐ[O0 p] Ω) (z : On p L) : IsInt p (ι z) := by
  obtain ⟨b, -⟩ := GlobalTheory.K5.OnFree.on_free p L
  haveI : Module.Finite (O0 p) (On p L) := Module.Finite.of_basis b
  haveI : Algebra.IsIntegral (O0 p) (On p L) := Algebra.IsIntegral.of_finite _ _
  exact IsIntegral.map ι (Algebra.IsIntegral.isIntegral z)

theorem emb_fix (T : Tower p Ω) {L : ℕ} {ι : On p L →ₐ[O0 p] Ω} (hι : IsEmb T L ι) {g : Gal p Ω}
    (hg : g ∈ Gn T L) (z : On p L) : g (ι z) = ι z := by
  have h := AlgHom.ext_of_adjoin_eq_top (adjoin_top p L) (φ₁ := (g : Ω →ₐ[O0 p] Ω).comp ι) (φ₂ := ι) (by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · simp [hι.1, ((Basic.mem_gn T L g).1 hg).1]
    · simp [hι.2, ((Basic.mem_gn T L g).1 hg).2])
  exact congrArg (fun φ : On p L →ₐ[O0 p] Ω => φ z) h

theorem pint (k : ℕ) : IsInt p ((p : Ω) ^ k) := by
  have := Basic.isInt_intCast (p := p) (Ω := Ω) ((p : ℤ) ^ k)
  push_cast at this
  exact this

theorem qq_int (T : Tower p Ω) (L : ℕ) : IsInt p (T.qq L) := by
  refine ⟨Polynomial.X ^ (p ^ L) - Polynomial.C (qO p),
    Polynomial.monic_X_pow_sub_C _ (pow_ne_zero _ hp.out.ne_zero), ?_⟩
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, Basic.qq_pow, sub_self]

theorem reb_mem {T : Tower p Ω} {L : ℕ} {ψ : O0 p →+* Ω} (hψ : IsReb T L ψ) (y : O0 p) :
    ψ y ∈ Algebra.adjoin (O0 p) {T.qq L} := by
  have h := ψ.mem_range_self y
  rw [hψ.rng] at h
  exact h

theorem reb_int {T : Tower p Ω} {L : ℕ} {ψ : O0 p →+* Ω} (hψ : IsReb T L ψ) (y : O0 p) :
    IsInt p (ψ y) := by
  have h : Algebra.adjoin (O0 p) {T.qq L} ≤ integralClosure (O0 p) Ω :=
    Algebra.adjoin_le (by rw [Set.singleton_subset_iff, SetLike.mem_coe, mem_integralClosure_iff]; exact qq_int T L)
  exact h (reb_mem hψ y)

theorem reb_fix {T : Tower p Ω} {L : ℕ} {ψ : O0 p →+* Ω} (hψ : IsReb T L ψ) {g : Gal p Ω}
    (hg : g (T.qq L) = T.qq L) (y : O0 p) : g (ψ y) = ψ y := by
  have h : Algebra.adjoin (O0 p) {T.qq L} ≤ AlgHom.equalizer (g : Ω →ₐ[O0 p] Ω) (AlgHom.id (O0 p) Ω) :=
    Algebra.adjoin_le (by
      rw [Set.singleton_subset_iff, SetLike.mem_coe, AlgHom.mem_equalizer]
      simpa using hg)
  have h2 := h (reb_mem hψ y)
  rw [AlgHom.mem_equalizer] at h2
  simpa using h2

theorem ev_int {T : Tower p Ω} {L : ℕ} {ψ : O0 p →+* Ω} (hψ : IsReb T L ψ) {c : ℤ → Ω} {x x' : Ω}
    (h : Ev ψ c x x') : IsInt p x ∧ IsInt p x' := by
  obtain ⟨d, e, a, he, -, rfl, rfl⟩ := h
  exact ⟨(integralClosure (O0 p) Ω).sum_mem fun t _ => (he t).1.mul (reb_int hψ _),
    (integralClosure (O0 p) Ω).sum_mem fun t _ => (he t).1.mul (reb_int hψ _)⟩

theorem ev_fix {T : Tower p Ω} {L : ℕ} {ψ : O0 p →+* Ω} (hψ : IsReb T L ψ) {c : ℤ → Ω} {x x' : Ω}
    (h : Ev ψ c x x') {g : Gal p Ω} (hg : g ∈ Ggeo p Ω ⊓ Gn T L) : g x = x ∧ g x' = x' := by
  obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.1 hg
  have hq : g (T.qq L) = T.qq L := ((Basic.mem_gn T L g).1 hg2).2
  obtain ⟨d, e, a, he, -, rfl, rfl⟩ := h
  constructor <;>
  · rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_mul, hg1 _ (he t).2, reb_fix hψ hq]

theorem conj_mem {T : Tower p Ω} {L : ℕ} {σ g : Gal p Ω} (hσ : σ ∈ Gn T L) (hg : g ∈ Ggeo p Ω ⊓ Gn T L) :
    σ * g * σ⁻¹ ∈ Ggeo p Ω ⊓ Gn T L := by
  obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.1 hg
  refine Subgroup.mem_inf.2 ⟨fun z hz => ?_, (Gn T L).mul_mem ((Gn T L).mul_mem hσ hg2) ((Gn T L).inv_mem hσ)⟩
  have h1 : IsAlgZp p (σ⁻¹ z) := by
    obtain ⟨P, hP, e⟩ := hz
    refine ⟨P, hP, ?_⟩
    have := Polynomial.aeval_algHom_apply ((σ⁻¹ : Gal p Ω) : Ω →ₐ[O0 p] Ω) z (P.map (algebraMap ℤ_[p] (O0 p)))
    rw [e, map_zero] at this
    simpa using this
  show σ (g (σ⁻¹ z)) = z
  rw [hg1 _ h1, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

theorem algZp_root {κ ρ : Ω} (hκ : IsAlgZp p κ) {m : ℕ} (hm : 0 < m) (h : ρ ^ m = κ) : IsAlgZp p ρ := by
  obtain ⟨P, hP, e⟩ := hκ
  refine ⟨Polynomial.expand ℤ_[p] m P, (Polynomial.expand_ne_zero hm).2 hP, ?_⟩
  rw [Polynomial.map_expand, Polynomial.expand_aeval, h, e]

theorem kum_rel (T : Tower p Ω) {n : ℕ} {H : Subgroup (Gal p Ω)} {θ ρ ra rb : Ω}
    {e ka kb : Gal p Ω → ZMod (p ^ n)}
    (hθ : IsKum T n H θ e) (ha : IsKum T n H ra ka) (hb : IsKum T n H rb kb)
    (hρ : ∀ g ∈ H, g ρ = ρ) (hrel : θ * rb = ρ * ra) (hne : θ * rb ≠ 0) {g : Gal p Ω} (hg : g ∈ H) :
    Cong p n (((e g).val : Ω) + ((kb g).val : Ω)) ((ka g).val : Ω) := by
  have h1 := congrArg g hrel
  rw [map_mul, map_mul, hθ g hg, hb g hg, hρ g hg, ha g hg] at h1
  have h2 : T.ζ n ^ ((e g).val + (kb g).val) * (θ * rb) = T.ζ n ^ (ka g).val * (θ * rb) := by
    rw [pow_add]; linear_combination h1 - T.ζ n ^ (ka g).val * hrel
  have h3 := mul_right_cancel₀ hne h2
  rw [Basic.zeta_pow_eq_iff] at h3
  have := Basic.cong_natCast (Ω := Ω) h3
  push_cast at this
  exact this

end GlobalTheory.EdgeLoc

namespace GlobalTheory.EdgeLoc

theorem edge_dlog : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (L n : ℕ), n ≤ L → 1 ≤ n → ∀ (ψ : O0 p →+* Ω), IsReb T L ψ → ∀ ι : On p L →ₐ[O0 p] Ω, IsEmb T L ι →
  ∀ (u v : (On p L)ˣ) (α β α' β' : On p L), IsDlog p L (u : On p L) α β → IsDlog p L (v : On p L) α' β' →
  ∀ r s : Ω, r ^ (p ^ n) = ι u → s ^ (p ^ n) = ι v →
  ∀ x y lz η : Gal p Ω → ZMod (p ^ n), IsKum T n (Gn T L) r x → IsKum T n (Gn T L) s y → IsKum T n (Gn T L) (T.ζ (L + n)) lz →
  (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), ∀ h ∈ (Ggeo p Ω ⊓ Gn T L), x g * y h = η h - η (g * h) + η g) →
  (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), ∃ S : Finset Ω, ∀ h ∈ (Ggeo p Ω ⊓ Gn T L), (∀ z ∈ S, h z = g z) → η h = η g) →
  ∃ o : Ω, IsInt p o ∧ (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), g o = o) ∧ ∀ σ ∈ Gn T L, ∀ (θ κ a a' b b' : Ω) (ca cb : ℤ → Ω),
    IsKum T n (Ggeo p Ω ⊓ Gn T L) θ (fun h => η (σ * h * σ⁻¹) - η h - x h * y σ + x σ * y h) →
    κ ≠ 0 → IsAlgZp p κ → θ ^ (p ^ n) * b = κ * a → Ev ψ ca a a' → Ev ψ cb b b' → a ≠ 0 → IsInt p a⁻¹ → b ≠ 0 → IsInt p b⁻¹ →
    Cong p n ((p : Ω) ^ c * (a' / a - b' / b)) (σ⁻¹ o - o - (p : Ω) ^ c * ι (α * β' - β * α') * ((lz σ).val : Ω)) := by
  intro p _ hp2
  obtain ⟨c₁, h53⟩ := GlobalTheory.T.cup_kummer_dlog_mod_primePow_levelL p hp2
  obtain ⟨c₂, hed⟩ := GlobalTheory.T.edge_class_cup_product_geometric p hp2 c₁
  obtain ⟨c₃, hgeo⟩ := GlobalTheory.T.kummerCocycle_value_expansion_eq_logDeriv_smul p hp2
  obtain ⟨c₄, h71⟩ := GlobalTheory.T.geometric_level_h1_coboundary p hp2
  refine ⟨c₂ + c₃ + c₄, ?_⟩
  intro Ω _ _ hΩ T L n hnL hn1 ψ hψ ι hι u v α β α' β' hu hv r s hr hs x y lz η hx hy hlz hcup hloc
  haveI := hΩ.clo
  have hpn : p ^ n ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have hr0 : r ≠ 0 := by
    rintro rfl; rw [zero_pow hpn] at hr; exact (u.isUnit.map ι).ne_zero hr.symm
  have hs0 : s ≠ 0 := by
    rintro rfl; rw [zero_pow hpn] at hs; exact (v.isUnit.map ι).ne_zero hs.symm
  obtain ⟨lq, hlq⟩ := Basic.exists_isKum T n (Gn T L) (Basic.qq_ne_zero T (L + n)) (fun g hg => by
    rw [pow_chain T.qq T.qpow L n, ((Basic.mem_gn T L g).1 hg).2])
  have hcob := h53 Ω hΩ T L n hnL hn1 ι hι u v α β α' β' hu hv r s hr hs x y lz lq hx hy hlz hlq
  have hadd : ∀ g ∈ Gn T L, ∀ h ∈ Gn T L, x (g * h) = x g + x h ∧ y (g * h) = y g + y h :=
    fun g hg h hh => ⟨kum_add T hnL hr0 hx hg hh, kum_add T hnL hs0 hy hg hh⟩
  obtain ⟨o₁, ho₁i, ho₁f, hE⟩ := hed Ω hΩ T L n hnL x y lz lq η (ι (α * β' - β * α')) hadd hlz hlq
    (emb_int L ι _) (fun g hg => emb_fix T hι hg _) hcup hloc hcob
  have hlqΔ : IsKum T n (Ggeo p Ω ⊓ Gn T L) (T.qq (L + n)) lq := fun g hg => hlq g (Subgroup.mem_inf.1 hg).2
  obtain ⟨-, h71k⟩ := h71 Ω hΩ T L n hnL lq hlqΔ
  refine ⟨(p : Ω) ^ (c₃ + c₄) * o₁, (pint _).mul ho₁i, fun g hg => by rw [map_mul, map_pow, map_natCast, ho₁f g hg], ?_⟩
  intro σ hσ θ κ a a' b b' ca cb hθ hκ0 hκ hrel hea heb ha0 hai hb0 hbi
  have hpn0 : 0 < p ^ n := Nat.pos_of_ne_zero hpn
  obtain ⟨ra, hra⟩ := IsAlgClosed.exists_pow_nat_eq a hpn0
  obtain ⟨rb, hrb⟩ := IsAlgClosed.exists_pow_nat_eq b hpn0
  have hra0 : ra ≠ 0 := by rintro rfl; rw [zero_pow hpn] at hra; exact ha0 hra.symm
  have hrb0 : rb ≠ 0 := by rintro rfl; rw [zero_pow hpn] at hrb; exact hb0 hrb.symm
  obtain ⟨ka, hka⟩ := Basic.exists_isKum T n (Ggeo p Ω ⊓ Gn T L) hra0 (fun g hg => by
    rw [hra, (ev_fix hψ hea hg).1])
  obtain ⟨kb, hkb⟩ := Basic.exists_isKum T n (Ggeo p Ω ⊓ Gn T L) hrb0 (fun g hg => by
    rw [hrb, (ev_fix hψ heb hg).1])
  obtain ⟨xa, hxai, hxa⟩ := hgeo Ω hΩ T L n hnL hn1 ψ hψ ca a a' ra hea ha0 hai hra ka lq hka hlqΔ
  obtain ⟨xb, hxbi, hxb⟩ := hgeo Ω hΩ T L n hnL hn1 ψ hψ cb b b' rb heb hb0 hbi hrb kb lq hkb hlqΔ
  have hθ0 : θ ≠ 0 := by
    rintro rfl; rw [zero_pow hpn, zero_mul] at hrel; exact mul_ne_zero hκ0 ha0 hrel.symm
  set ρ : Ω := θ * rb / ra with hρdef
  have hρpow : ρ ^ (p ^ n) = κ := by
    rw [hρdef, div_pow, mul_pow, hra, hrb, hrel, mul_div_assoc, div_self ha0, mul_one]
  have hρalg : IsAlgZp p ρ := algZp_root hκ hpn0 hρpow
  have hρfix : ∀ g ∈ Ggeo p Ω ⊓ Gn T L, g ρ = ρ := fun g hg => (Subgroup.mem_inf.1 hg).1 ρ hρalg
  have hrel' : θ * rb = ρ * ra := by rw [hρdef]; field_simp
  have hK := fun g (hg : g ∈ Ggeo p Ω ⊓ Gn T L) =>
    kum_rel T hθ hka hkb hρfix hrel' (mul_ne_zero hθ0 hrb0) hg
  obtain ⟨we, hwei, hwe⟩ := hE σ hσ
  have hθ0 : θ ≠ 0 := by
    rintro rfl; rw [zero_pow hpn, zero_mul] at hrel; exact mul_ne_zero hκ0 ha0 hrel.symm
  set ρ : Ω := θ * rb / ra with hρdef
  have hρpow : ρ ^ (p ^ n) = κ := by
    rw [hρdef, div_pow, mul_pow, hra, hrb, hrel, mul_div_assoc, div_self ha0, mul_one]
  have hρalg : IsAlgZp p ρ := algZp_root hκ hpn0 hρpow
  have hρfix : ∀ g ∈ Ggeo p Ω ⊓ Gn T L, g ρ = ρ := fun g hg => (Subgroup.mem_inf.1 hg).1 ρ hρalg
  have hrel' : θ * rb = ρ * ra := by rw [hρdef]; field_simp
  have hK := fun g (hg : g ∈ Ggeo p Ω ⊓ Gn T L) =>
    kum_rel T hθ hka hkb hρfix hrel' (mul_ne_zero hθ0 hrb0) hg
  obtain ⟨we, hwei, hwe⟩ := hE σ hσ
  have key : ∀ w, σ⁻¹ (σ w) = w := fun w => by
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have hσo : ∀ g ∈ Ggeo p Ω ⊓ Gn T L, g (σ⁻¹ o₁) = σ⁻¹ o₁ := fun g hg => by
    have h1 := ho₁f _ (conj_mem hσ hg)
    calc g (σ⁻¹ o₁) = σ⁻¹ (σ (g (σ⁻¹ o₁))) := (key _).symm
      _ = σ⁻¹ ((σ * g * σ⁻¹) o₁) := rfl
      _ = σ⁻¹ o₁ := by rw [h1]
  obtain ⟨X, hXd⟩ : ∃ X : Ω, X = (p : Ω) ^ c₃ * (σ⁻¹ o₁ - o₁ - (p : Ω) ^ c₂ * ι (α * β' - β * α') * ((lz σ).val : Ω))
      - (p : Ω) ^ (c₂ + c₃) * (a' / a - b' / b) := ⟨_, rfl⟩
  have hXi : IsInt p X := by
    have ha' := (ev_int hψ hea).2
    have hb' := (ev_int hψ heb).2
    have hfi : IsInt p (ι (α * β' - β * α')) := emb_int L ι _
    have hσi : IsInt p (σ⁻¹ o₁) := Basic.isInt_gal _ ho₁i
    have hlzi : IsInt p (((lz σ).val : Ω)) := by
      have := Basic.isInt_intCast (p := p) (Ω := Ω) ((lz σ).val : ℤ)
      exact_mod_cast this
    rw [hXd, div_eq_mul_inv, div_eq_mul_inv]
    exact ((pint _).mul (((hσi.sub ho₁i).sub (((pint _).mul hfi).mul hlzi)))).sub
      ((pint _).mul ((ha'.mul hai).sub (hb'.mul hbi)))
  have hXf : ∀ g ∈ Ggeo p Ω ⊓ Gn T L, g X = X := fun g hg => by
    have hg2 := (Subgroup.mem_inf.1 hg).2
    rw [hXd]
    simp only [map_sub, map_mul, map_div₀, map_pow, map_natCast, hσo g hg, ho₁f g hg,
      emb_fix T hι hg2, (ev_fix hψ hea hg).1, (ev_fix hψ hea hg).2, (ev_fix hψ heb hg).1, (ev_fix hψ heb hg).2]
  have hXcob : Cob1 n (Ggeo p Ω ⊓ Gn T L) (fun g => X * ((lq g).val : Ω)) := by
    refine ⟨(p : Ω) ^ c₂ * (xa - xb) - (p : Ω) ^ c₃ * we,
      ((pint _).mul (hxai.sub hxbi)).sub ((pint _).mul hwei), fun g hg => ?_⟩
    obtain ⟨z1, hz1, e1⟩ := hwe g hg
    obtain ⟨z2, hz2, e2⟩ := hxa g hg
    obtain ⟨z3, hz3, e3⟩ := hxb g hg
    obtain ⟨z4, hz4, e4⟩ := hK g hg
    refine ⟨(p : Ω) ^ (c₂ + c₃) * z4 + (p : Ω) ^ c₂ * (z2 - z3) - (p : Ω) ^ c₃ * z1,
      (((pint _).mul hz4).add ((pint _).mul (hz2.sub hz3))).sub ((pint _).mul hz1), ?_⟩
    rw [hXd]
    simp only [map_sub, map_mul, map_pow, map_natCast] at e1 e2 e3 e4 ⊢
    linear_combination -(p : Ω) ^ c₃ * e1 + (p : Ω) ^ c₂ * e2 - (p : Ω) ^ c₂ * e3 + (p : Ω) ^ (c₂ + c₃) * e4
  obtain ⟨z, hz, ez⟩ := h71k X hXi hXf hXcob
  refine ⟨-z, hz.neg, ?_⟩
  rw [map_mul, map_pow, map_natCast]
  rw [hXd] at ez
  linear_combination -ez
end GlobalTheory.EdgeLoc
