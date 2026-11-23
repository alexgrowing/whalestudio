import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.PrimAn
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TraceMulConjIntIffMemOfMulDifferentEqOne
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FinrankInt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramePeriodsAlongIsotropicFlowAndBlockChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicIndexSums
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM.SplitLat

open GlobalTheory.CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_pair (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : FD.DataX E r) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (hr : 0 < r) (h𝔄 : 𝔄 ≠ 0) (hΨ : ∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0)
    (hΛ : X.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ X.L', v = a • u}) :
    ∃ (D₁ : Bool → Datum H) (e : ∀ b, (D₁ b).La ≃ₗ[𝓞 E] (𝔄 : Submodule (𝓞 E) E)) (s : Bool → ℤ),
      ((D₁ true).p = 1 ∧ (D₁ true).q = 0) ∧ ((D₁ false).p = 0 ∧ (D₁ false).q = 1) ∧ (∀ b, s b = 1 ∨ s b = -1) ∧
      ∀ b x y, (((D₁ b).EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (s b * X.ξ0 * (e b x : E) * FD.cc (e b y : E)) := by
  obtain ⟨t, ht, hκ⟩ : ∃ t : ℤ, (t = 1 ∨ t = -1) ∧ X.κ0 = 2 * (t * X.ξ0) := by
    rcases X.κ0_xi with h | h
    · exact ⟨1, Or.inl rfl, by rw [h]; simp⟩
    · exact ⟨-1, Or.inr rfl, by rw [h]; simp⟩
  have hd := GlobalTheory.trace_xi_mul_conj_int_iff_mem E r X 𝔄 hr h𝔄 hΛ
  obtain ⟨D, e, hp, hq, he⟩ := SelfDualDatum.exists_datum E H (𝔄 : Submodule (𝓞 E) E) (t * X.ξ0)
    (FractionalIdeal.fg_of_isUnit _ (IsUnit.mk0 _ h𝔄)) (FractionalIdeal.coeToSubmodule_ne_bot.2 h𝔄)
    (by
      have := X.ξ0_im
      rw [FD.cc] at this
      rw [map_mul, map_intCast, this, mul_neg])
    (fun τ hτ => by
      have := X.κ0_sign ⟨τ, (hΨ τ).2 hτ⟩
      rw [hκ, map_mul, map_ofNat] at this
      simp only [Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, zero_mul, add_zero] at this
      linarith)
    (fun x => by
      refine Iff.trans ?_ (hd x)
      refine forall₂_congr fun y _ => ?_
      rcases ht with rfl | rfl
      · simp [FD.cc]
      · simp only [Int.cast_neg, Int.cast_one, neg_mul, _root_.one_mul, map_neg, FD.cc]
        exact ⟨fun ⟨n, h⟩ => ⟨-n, by rw [Int.cast_neg, ← h, neg_neg]⟩, fun ⟨n, h⟩ => ⟨-n, by rw [h, Int.cast_neg]⟩⟩)
  refine ⟨fun b => match b with | true => D | false => oppDatum D,
    fun b => match b with | true => e | false => e, fun b => match b with | true => t | false => -t,
    ⟨hp, hq⟩, ⟨hq, hp⟩, ?_, ?_⟩
  · rintro (_ | _)
    · rcases ht with rfl | rfl <;> simp
    · exact ht
  · rintro (_ | _) x y
    · change D.La at x y
      change ((-(D.EF x y) : ℤ) : ℚ) = Algebra.trace ℚ E (((-t : ℤ) : E) * X.ξ0 * (e x : E) * FD.cc (e y : E))
      rw [Int.cast_neg, he, ← map_neg]
      congr 1
      simp [FD.cc]
    · exact he x y

omit [IsCMField E] in

theorem exists_nsmul_mem (𝔄 : Submodule (𝓞 E) E) (h : 𝔄 ≠ ⊥) {J : Type} [Fintype J] (c : J → E) :
    ∃ n : ℕ, 0 < n ∧ ∀ i, (n : E) * c i ∈ 𝔄 := by
  classical
  obtain ⟨a, ha, h0⟩ := (Submodule.ne_bot_iff _).1 h
  obtain ⟨n, hn, hi⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image fun i => c i / a)
  refine ⟨n.natAbs, Int.natAbs_pos.2 hn, fun i => ?_⟩
  have h1 := 𝔄.smul_mem (⟨n • (c i / a), hi _ (by simp)⟩ : 𝓞 E) ha
  have h2 : (n : E) * c i ∈ 𝔄 := by
    convert h1 using 1
    change _ = (n • (c i / a)) * a
    rw [zsmul_eq_mul, _root_.mul_assoc, div_mul_cancel₀ _ h0]
  rcases Int.natAbs_eq n with h | h
  · rwa [h, Int.cast_natCast] at h2
  · rw [h, Int.cast_neg, Int.cast_natCast, neg_mul] at h2
    exact 𝔄.neg_mem_iff.1 h2

omit [NumberField E] [IsCMField E] in
theorem emb_smul' (τ : E →+* ℂ) (a : E) (v : Fin r → E) :
    FD.Data.emb τ (a • v) = τ a • FD.Data.emb τ v := by
  funext k
  simp [FD.Data.emb]

theorem inv_mulVec_eq_zero {p : ℕ} (hp : p ≤ r) (M : Matrix (Fin r) (Fin r) ℂ) (hM : M.det ≠ 0)
    {u : Fin r → ℂ}
    (hu : u ∈ Submodule.span ℂ (Set.range fun a : Fin p => FD.col M (Fin.castLE hp a)))
    (k : Fin r) (hk : p ≤ (k : ℕ)) : (M⁻¹.mulVec u) k = 0 := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a, rfl⟩ := hu
    have h1 : (M⁻¹.mulVec (FD.col M (Fin.castLE hp a))) k = (M⁻¹ * M) k (Fin.castLE hp a) := by
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, FD.col]
    have hne : k ≠ Fin.castLE hp a := by
      intro h
      have h2 := congrArg Fin.val h
      have h3 := a.isLt
      simp at h2
      omega
    show (M⁻¹.mulVec (FD.col M (Fin.castLE hp a))) k = 0
    rw [h1, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hM), Matrix.one_apply_ne hne]
  | zero => simp
  | add a b _ _ ha hb => rw [Matrix.mulVec_add, Pi.add_apply, ha, hb, add_zero]
  | smul c a _ ha => rw [Matrix.mulVec_smul, Pi.smul_apply, ha, smul_zero]

theorem herm_smul_smul (G : Matrix (Fin r) (Fin r) E) (a b : E) (u w : Fin r → E) :
    herm G (a • u) (b • w) = a * cc b * herm G u w := by
  simp only [FD.herm, FD.cc, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem herm_smul_left (G : Matrix (Fin r) (Fin r) E) (a : E) (u w : Fin r → E) :
    herm G (a • u) w = a * herm G u w := by
  have := herm_smul_smul G a 1 u w
  simpa [FD.cc] using this

theorem perFr_flow (X : Data E r) {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (h0 : 0 < X.p0) (s : X.Ψ → ℂ)
    (x : Frame X.Ψ r) {v : Fin r → E} (hv : herm X.Gm v ξ = 0) (τ : E →+* ℂ) (i : ℕ) :
    perFr X (X.flow ξ s x) v τ i = perFr X x v τ i := by
  by_cases hτ : τ ∈ X.Ψ
  · rw [PerFlow.flow_mem X hξ s x v ⟨τ, hτ⟩ i, hv]; simp
  · have h' : conjEmb τ ∈ X.Ψ := by
      by_contra h
      exact hτ ((X.cmType τ).2 h)
    have hc : τ = conjEmb (conjEmb τ) := by ext a; simp [conjEmb]
    have hlt : X.p0 - 1 - (X.p0 - 1 - (X.p0 - 1 - i)) < r := by have := X.p0_le; omega
    have key : ∀ y : Frame X.Ψ r, perFr X y v (conjEmb (conjEmb τ)) i =
        perFr X y v (conjEmb (conjEmb τ)) (X.p0 - 1 - (X.p0 - 1 - i)) := fun y => by
      rw [PerFlow.perFr_conj X y v ⟨_, h'⟩ i ⟨_, hlt⟩ (by simp only; omega),
        PerFlow.perFr_conj X y v ⟨_, h'⟩ _ ⟨_, hlt⟩ rfl]
    rw [hc, key, key, PerFlow.flow_conj X ξ s x v ⟨_, h'⟩ _ (by omega), hv]
    simp

theorem perFr_pos (X : Data E r) (ξ : Fin r → E) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (v : Fin r → E)
    (hv : X.Jz x (X.ucomp x ξ (X.embV v)) = Complex.I • X.ucomp x ξ (X.embV v)) (a : E) {τ : E →+* ℂ}
    (hτ : τ ∈ X.Ψ) : ∃ c : ℂ, ∀ i, perFr X x (a • v) τ i = c * perFr X x ξ τ i := by
  obtain ⟨c, u, hu, hp⟩ : ∃ (c : ℂ) (u : Fin r → ℂ), Data.emb τ v = u + c • Data.emb τ ξ ∧ X.ppos x ⟨τ, hτ⟩ u = u := by
    refine ⟨_, X.ucomp x ξ (X.embV v) ⟨τ, hτ⟩, (sub_add_cancel _ _).symm, ?_⟩
    have := congrFun hv ⟨τ, hτ⟩
    funext k
    have h2 := mul_left_cancel₀ Complex.I_ne_zero (congrFun this k)
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h2
    linear_combination h2 / 2
  refine ⟨τ a * c, fun i => ?_⟩
  rw [PerFlow.perFr_mem X x _ ⟨τ, hτ⟩, PerFlow.perFr_mem X x _ ⟨τ, hτ⟩]
  split_ifs with hi
  · have h0 := inv_mulVec_eq_zero X.p0_le _ (hx ⟨τ, hτ⟩).1 (u := u) (by
      rw [← hp]
      exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩))
      ⟨X.p0 + i, hi⟩ (by simp)
    simp only [emb_smul', hu, Matrix.mulVec_smul, Matrix.mulVec_add, Pi.smul_apply, Pi.add_apply, h0,
      smul_eq_mul]
    ring
  · simp

theorem perFr_neg (X : Data E r) (h0 : 0 < X.p0) (ξ : Fin r → E) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (v : Fin r → E)
    (hv : X.Jz x (X.ucomp x ξ (X.embV v)) = -(Complex.I • X.ucomp x ξ (X.embV v))) (a : E) {τ : E →+* ℂ}
    (hτ : τ ∉ X.Ψ) : ∃ c : ℂ, ∀ i, perFr X x (a • v) τ i = c * perFr X x ξ τ i := by
  have h' : conjEmb τ ∈ X.Ψ := by
    by_contra h
    exact hτ ((X.cmType τ).2 h)
  have hc : τ = conjEmb (conjEmb τ) := by ext a; simp [conjEmb]
  generalize conjEmb τ = ρ at h' hc
  subst hc
  obtain ⟨c, u, hu, hp⟩ : ∃ (c : ℂ) (u : Fin r → ℂ), Data.emb ρ v = u + c • Data.emb ρ ξ ∧ X.ppos x ⟨ρ, h'⟩ u = 0 := by
    refine ⟨_, X.ucomp x ξ (X.embV v) ⟨ρ, h'⟩, (sub_add_cancel _ _).symm, ?_⟩
    have := congrFun hv ⟨ρ, h'⟩
    funext k
    have h1 := congrFun this k
    simp only [Data.Jz, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at h1
    apply mul_left_cancel₀ Complex.I_ne_zero
    simp only [Pi.zero_apply]
    linear_combination h1 / 2
  refine ⟨starRingEnd ℂ (ρ a) * starRingEnd ℂ c, fun i => ?_⟩
  have hlt : X.p0 - 1 - i < X.p0 := by omega
  rw [PerFlow.perFr_conj X x _ ⟨ρ, h'⟩ i (Fin.castLE X.p0_le ⟨_, hlt⟩) rfl,
    PerFlow.perFr_conj X x _ ⟨ρ, h'⟩ i (Fin.castLE X.p0_le ⟨_, hlt⟩) rfl]
  have h1 := X.hermC_ppos_colP hx ⟨ρ, h'⟩ u ⟨_, hlt⟩
  rw [hp, hermC_zero_left, ← hermC_conj _ X.Gm_herm, eq_comm, map_eq_zero] at h1
  simp only [Data.colP] at h1
  simp only [emb_smul', hu, hermC_smul_right, hermC_add_right, h1]
  ring

theorem exists_coords (X : Data E r) {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (hne : ξ ≠ 0) (hr : 2 ≤ r)
    (lam : Fin (r - 2) → Fin r → E) (hl : ∀ j, herm X.Gm (lam j) ξ = 0)
    (hli : LinearIndependent E (Fin.cons ξ lam : Fin (r - 2 + 1) → Fin r → E)) {v : Fin r → E}
    (hv : herm X.Gm v ξ = 0) : ∃ (c₀ : E) (c : Fin (r - 2) → E), v = c₀ • ξ + ∑ j, c j • lam j := by
  let f : (Fin r → E) →ₗ[E] E := { X.hermL ξ with map_smul' := fun a u => herm_smul_left _ a u ξ }
  have hf : ∀ u, f u = herm X.Gm u ξ := fun _ => rfl
  have hne' : LinearMap.ker f ≠ ⊤ := fun h => by
    have h1 : X.Gm.mulVec (fun b => cc (ξ b)) = 0 := by
      funext a
      have : f (Pi.single a 1) = 0 := LinearMap.mem_ker.1 (h ▸ Submodule.mem_top)
      simpa [hf, herm, Pi.single_apply, Matrix.mulVec, dotProduct] using this
    have h2 := Matrix.eq_zero_of_mulVec_eq_zero X.Gm_det h1
    exact hne (funext fun b => by simpa [cc] using congrFun h2 b)
  have hlt := Submodule.finrank_lt hne'
  have hle : Submodule.span E (Set.range (Fin.cons ξ lam : Fin (r - 2 + 1) → Fin r → E)) ≤ LinearMap.ker f := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) j
    · exact hξ
    · exact hl j
  have heq := Submodule.eq_of_le_of_finrank_le hle (by
    rw [finrank_span_eq_card hli]
    simp at hlt ⊢
    omega)
  have hm : v ∈ LinearMap.ker f := hv
  rw [← heq, Submodule.mem_span_range_iff_exists_fun] at hm
  obtain ⟨c, hc⟩ := hm
  exact ⟨c 0, fun j => c j.succ, by rw [← hc, Fin.sum_univ_succ]; simp⟩

omit [IsCMField E] in
theorem eq_zero_of_trace {z : E} (h : ∀ b : 𝓞 E, Algebra.trace ℚ E ((b : E) * z) = 0) : z = 0 := by
  by_contra hz
  obtain ⟨n, hn, hi⟩ := exists_integral_multiples ℤ ℚ ({z⁻¹} : Finset E)
  have := h ⟨n • z⁻¹, hi _ (by simp)⟩
  change Algebra.trace ℚ E ((n • z⁻¹) * z) = 0 at this
  rw [smul_mul_assoc, inv_mul_cancel₀ hz, map_zsmul, ← map_one (algebraMap ℚ E), Algebra.trace_algebraMap] at this
  simp [hn, Module.finrank_pos.ne'] at this

omit [IsCMField E] in

theorem eq_zero_of_rank_one {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [Module (𝓞 E) X]
    (hrk : Module.finrank (𝓞 E) X = 1) (ξ : Module.Dual ℤ X) (hξ : ξ ≠ 0) {y : X} (hy : ∀ b : 𝓞 E, ξ (b • y) = 0) :
    y = 0 := by
  have hdvd : ∀ s : 𝓞 E, s ≠ 0 → ∃ (n : ℕ) (t : 𝓞 E), n ≠ 0 ∧ (n : 𝓞 E) = t * s := fun s hs => by
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {s}))
    exact ⟨_, t, by simpa [Ideal.absNorm_eq_zero_iff] using hs, ht.symm⟩
  haveI : Module.Finite (𝓞 E) X := Module.Finite.of_restrictScalars_finite ℤ _ _
  obtain ⟨x, hx⟩ : ∃ x, ξ x ≠ 0 := by
    by_contra h
    push Not at h
    exact hξ (LinearMap.ext h)
  have hn : ¬ LinearIndependent (𝓞 E) ![y, x] := fun hi => by
    have := hi.fintype_card_le_finrank
    simp [hrk] at this
  rw [LinearIndependent.pair_iff] at hn
  push Not at hn
  obtain ⟨s, t, e, hne⟩ := hn
  by_cases ht : t = 0
  · obtain ⟨n, u, hn, hu⟩ := hdvd s fun hs => hne hs ht
    rw [ht, zero_smul, add_zero] at e
    have : (n : ℤ) • y = 0 := by
      rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E), hu, mul_smul, e, smul_zero]
    exact (smul_eq_zero.1 this).resolve_left (by exact_mod_cast hn)
  · obtain ⟨n, u, hn, hu⟩ := hdvd t ht
    have h1 : n • x = (-(u * s)) • y := by
      rw [← Nat.cast_smul_eq_nsmul (𝓞 E), hu, mul_smul, eq_neg_of_add_eq_zero_right e, smul_neg, neg_smul, mul_smul]
    have h2 := hy (-(u * s))
    rw [← h1, map_nsmul] at h2
    simp [hn, hx] at h2

omit [IsCMField E] in

theorem apply_eq_zero {g g' : ℕ} {M : Type} (ty : Fin g → (E →+* ℂ)) (ty' : Fin g' → (E →+* ℂ))
    (π : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (P : M → Fin g → ℂ) (hP : Submodule.span ℝ (Set.range P) = ⊤)
    (hπ : ∀ (a : 𝓞 E) m i, π (fun j => ty j a * P m j) i = ty' i a * π (P m) i) (i : Fin g') (z t : Fin g → ℂ)
    (ht : π t i = 0) (c : ℂ) (hz : ∀ j, ty j = ty' i → z j = c * t j) : π z i = 0 := by
  classical
  have h1 : ∀ (a : 𝓞 E) (w : Fin g → ℂ), π (fun j => ty j a * w j) i = ty' i a * π w i := fun a w => by
    have hw : w ∈ Submodule.span ℝ (Set.range P) := hP ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem w hw => obtain ⟨m, rfl⟩ := hw; exact hπ a m i
    | zero =>
      have : (fun j => ty j a * (0 : Fin g → ℂ) j) = 0 := by funext j; simp
      rw [this, map_zero]; simp
    | add u w _ _ hu hw =>
      have : (fun j => ty j a * (u + w) j) = (fun j => ty j a * u j) + fun j => ty j a * w j := by
        funext j; simp [mul_add]
      rw [this, map_add, map_add, Pi.add_apply, Pi.add_apply, hu, hw, mul_add]
    | smul s w _ hw =>
      have : (fun j => ty j a * (s • w) j) = (s : ℂ) • fun j => ty j a * w j := by
        funext j; simp; ring
      rw [this, ← Complex.coe_smul, map_smul, map_smul, Pi.smul_apply, Pi.smul_apply, hw, smul_eq_mul, smul_eq_mul]
      ring
  have h2 : ∀ j, ty j ≠ ty' i → π (Pi.single j 1) i = 0 := fun j hj => by
    by_contra h
    apply hj
    refine IsFractionRing.ringHom_ext (A := 𝓞 E) fun a => ?_
    have h3 := h1 a (Pi.single j 1)
    have : (fun k => ty k a * (Pi.single j 1 : Fin g → ℂ) k) = ty j a • (Pi.single j 1 : Fin g → ℂ) := by
      funext k
      by_cases hk : k = j
      · simp [hk]
      · simp [hk]
    rw [this, map_smul, Pi.smul_apply, smul_eq_mul] at h3
    exact mul_right_cancel₀ h h3
  have h4 : ∀ w : Fin g → ℂ, π w i = ∑ j, w j * π (Pi.single j 1) i := fun w => by
    conv_lhs => rw [pi_eq_sum_univ' w]
    simp [map_sum, Finset.sum_apply]
  have h5 : π z i = c * π t i := by
    rw [h4, h4 t, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : ty j = ty' i
    · rw [hz j hj, _root_.mul_assoc]
    · simp [h2 j hj]
  rw [h5, ht, mul_zero]

theorem exists_cmLat (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {p q : ℕ} (Y : Data E r) (x : Frame Y.Ψ r) (hx : x ∈ Y.dom)
    (X : DataX E r) (hX : X.toData = Y) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (h𝔄 : 𝔄 ≠ 0)
    (h0 : 0 < Y.p0) (hrk : r = p + q + 2) (hp0 : Y.p0 = q + 1) (hΨ : ∀ τ : E →+* ℂ, τ ∈ Y.Ψ ↔ τ (H.rt : E) = H.rt0)
    (hΛ : X.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ X.L', v = a • u})
    (D : Datum H) {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe)
    (L : Y.Λ →ₗ[𝓞 E] D.La) (ξ : Fin r → E) (hξ : Y.IsIso ξ) (hL : L ⟨ξ, hξ.1⟩ = 0)
    (isom : ∀ a b : Y.Λ, herm Y.Gm a ξ = 0 → herm Y.Gm b ξ = 0 →
      ((D.EF (L a) (L b) : ℤ) : ℚ) = Algebra.trace ℚ E (-Y.ξ0 * herm Y.Gm a b))
    (onto : ∀ z, ∃ a : Y.Λ, herm Y.Gm a ξ = 0 ∧ L a = z)
    (pm : ∀ a : Y.Λ, herm Y.Gm a ξ = 0 → ∀ i, (∃ c : ℂ, ∀ n, perFr Y x a (ty i) n = c * perFr Y x ξ (ty i) n) →
      Pe (L a) i = 0)
    (La : ℝ) (lam : Fin (r - 2) → Fin r → E) (hl : SplitData X ξ La (hX ▸ x) lam) :
    ∃ Z : CMLat hP p q, ∀ j (τ : E →+* ℂ), ‖τ (Z.hh j : E)‖ ≤ La ^ 2 := by
  classical
  subst hX
  obtain ⟨D₁, e, s, h1, h2, hs, he⟩ := exists_pair H X 𝔄 (by omega) h𝔄 hΨ hΛ
  obtain ⟨hL', hli, -, hpos, hneg, hbd⟩ := hl
  let σ : Fin p ⊕ Fin q ≃ Fin (r - 2) := (Equiv.sumComm _ _).trans (finSumFinEquiv.trans (finCongr (by omega)))
  have hσl : ∀ j, X.p0 - 1 ≤ (σ (.inl j) : ℕ) := fun j => by simp [σ, hp0]
  have hσr : ∀ j, (σ (.inr j) : ℕ) < X.p0 - 1 := fun j => by simp [σ, hp0]
  have hmem : ∀ (a : (𝔄 : Submodule (𝓞 E) E)) j, (a : E) • lam j ∈ X.Λ := fun a j =>
    hΛ ▸ Submodule.subset_span ⟨a, a.2, _, (hL' j).1, rfl⟩
  have hperp : ∀ (a : E) j, herm X.Gm (a • lam j) ξ = 0 := fun a j => by rw [herm_smul_left, (hL' j).2, mul_zero]
  let m : Fin (r - 2) → (𝔄 : Submodule (𝓞 E) E) →ₗ[𝓞 E] X.Λ := fun j =>
    { toFun := fun a => ⟨_, hmem a j⟩
      map_add' := fun a b => Subtype.ext (add_smul _ _ _)
      map_smul' := fun c a => Subtype.ext (smul_assoc _ _ _) }
  let f : ∀ j : Fin p ⊕ Fin q, (D₁ j.isLeft).La →ₗ[𝓞 E] D.La := fun j => L ∘ₗ m (σ j) ∘ₗ (e _).toLinearMap
  have hf : ∀ j a, f j a = L ⟨(e _ a : E) • lam (σ j), hmem _ _⟩ := fun j a => rfl
  let hh : Fin p ⊕ Fin q → 𝓞 E := fun j =>
    -(s j.isLeft : 𝓞 E) * ⟨herm X.Gm (lam (σ j)) (lam (σ j)), X.L'_int _ (hL' _).1 _ (hL' _).1⟩
  have hhh : ∀ j, (hh j : E) = -(s j.isLeft : E) * herm X.Gm (lam (σ j)) (lam (σ j)) := fun j => by
    simp only [hh]
    rfl
  have hsq : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := fun τ => by
    refine sq_eq_sq_iff_eq_or_eq_neg.1 ?_
    rw [← map_pow, HostModel.coe_sq_eq_neg H.rt_sq, H.sqrt_neg_disc_sq, map_neg, map_natCast]
  refine ⟨⟨D₁, h1, h2, f, ?_, hh, fun j a b => ?_, ?_⟩, fun j τ => ?_⟩
  · rintro (j | j) a k hk
    · have hk' : ty k (H.rt : E) ≠ H.rt0 := by simpa using hk
      exact pm ⟨(e _ a : E) • lam (σ (.inl j)), hmem _ _⟩ (hperp _ _) k (perFr_neg X.toData h0 ξ hx _ (hneg _ (hσl j)).2 _ fun h => hk' ((hΨ _).1 h))
    · have hk' : ty k (H.rt : E) ≠ -H.rt0 := by simpa using hk
      exact pm ⟨(e _ a : E) • lam (σ (.inr j)), hmem _ _⟩ (hperp _ _) k (perFr_pos X.toData ξ hx _ (hpos _ (hσr j)).2 _
        ((hΨ _).2 ((hsq _).resolve_right hk')))
  · apply Int.cast_injective (α := ℚ)
    rw [hf, hf, isom ⟨(e _ a : E) • lam (σ j), hmem _ _⟩ ⟨(e _ b : E) • lam (σ j), hmem _ _⟩ (hperp _ _) (hperp _ _),
      he, map_smul, Submodule.coe_smul, Algebra.smul_def (hh j),
      ← RingOfIntegers.coe_eq_algebraMap, hhh]
    congr 1
    rw [herm_smul_smul]
    rcases hs j.isLeft with h | h <;> rw [h] <;> push_cast <;> ring
  · let N : Submodule (𝓞 E) D.La := LinearMap.range (∑ j, f j ∘ₗ LinearMap.proj j)
    have hN : ∀ a, a ∈ N ↔ ∃ x : ∀ j : Fin p ⊕ Fin q, (D₁ j.isLeft).La, a = ∑ j, f j (x j) := fun a => by
      simp only [N, LinearMap.mem_range, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
      exact exists_congr fun _ => eq_comm
    obtain ⟨S, hS⟩ := D.fin.fg_top
    choose v hv hLv using onto
    choose c₀ c hc using fun z => exists_coords X.toData hξ.2.1 hξ.2.2 (by omega) lam (fun j => (hL' j).2) hli (hv z)
    obtain ⟨n, hn, hnc⟩ := exists_nsmul_mem (𝔄 : Submodule (𝓞 E) E) (FractionalIdeal.coeToSubmodule_ne_bot.2 h𝔄)
      (fun i : S × Fin (r - 2) => c i.1 i.2)
    obtain ⟨n', hn', hnc'⟩ := exists_nsmul_mem (1 : Submodule (𝓞 E) E) one_ne_zero (fun i : S => c₀ i.1)
    refine ⟨n' * n, by positivity, fun a => (hN _).1 ?_⟩
    have : (⊤ : Submodule (𝓞 E) D.La) ≤ N.comap ((n' * n) • LinearMap.id) := by
      rw [← hS, Submodule.span_le]
      intro a ha
      obtain ⟨b, hb⟩ := Submodule.mem_one.1 (hnc' ⟨a, ha⟩)
      refine (hN _).2 ⟨fun j => n' • (e _).symm ⟨_, hnc (⟨a, ha⟩, σ j)⟩, ?_⟩
      have h5 : (n' * n) • v a = (n • b) • (⟨ξ, hξ.1⟩ : X.Λ) +
          ∑ j, n' • (⟨((n : E) * c a (σ j)) • lam (σ j), hmem ⟨_, hnc (⟨a, ha⟩, σ j)⟩ _⟩ : X.Λ) := by
        apply Subtype.ext
        simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_add, AddSubmonoidClass.coe_nsmul,
          Submodule.coe_smul]
        rw [Equiv.sum_comp σ (fun j => n' • ((n : E) * c a j) • lam j), hc a, smul_add, Finset.smul_sum,
          ← algebraMap_smul E (n • b), map_nsmul, hb]
        congr 1
        · funext k; simp; ring
        · refine Finset.sum_congr rfl fun j _ => ?_
          funext k; simp; ring
      have h6 := congrArg L h5
      rw [map_nsmul, hLv, map_add, map_smul, hL, smul_zero, zero_add, map_sum] at h6
      refine h6.trans (Finset.sum_congr rfl fun j _ => ?_)
      rw [map_nsmul, map_nsmul, hf]
      simp only [LinearEquiv.apply_symm_apply]
    exact this Submodule.mem_top
  · change ‖τ (hh j : E)‖ ≤ _
    have h4 : ‖τ (hh j : E)‖ = ‖τ (herm X.Gm (lam (σ j)) (lam (σ j)))‖ := by
      rw [hhh]
      rcases hs j.isLeft with h | h <;> rw [h] <;> simp
    rw [h4]
    by_cases hτ : τ ∈ X.Ψ
    · exact hbd _ ⟨τ, hτ⟩
    · have := hbd (σ j) ⟨ComplexEmbedding.conjugate τ, by
        by_contra h
        exact hτ ((X.cmType τ).2 h)⟩
      simpa [ComplexEmbedding.conjugate_coe_eq] using this

theorem exists_cmLat_abelianPart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (Xx : DataX E r) (hX : Xx.toData = U.X k) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (La : ℝ) (lam : Fin (r - 2) → Fin r → E), GoodEmb c σ → IsUnf U → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → 𝔄 ≠ 0 → Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} → SplitData Xx ξ' La (hX ▸ x) lam → letI := H.starRing; ∀ (A : AnArc (𝓞 E)) (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] A.La) (ξ : Module.Dual ℤ A.X) (DB : Datum H) (tyB : Fin A.gB → (E →+* ℂ)) (eB : DB.La ≃+ A.abelian₂), OnOrbit Uw k ξ' x A gam ξ → Module.finrank (𝓞 E) A.X = 1 → DB.p = Dw.p - 1 → DB.q = Dw.q - 1 → ∀ hB : AbDat H A DB tyB eB, ∃ Z : GlobalTheory.CM.CMLat hB.2.2.2.2 DB.p DB.q, ∀ j (τ : E →+* ℂ), ‖τ (Z.hh j : E)‖ ≤ La ^ 2 := by
  intro E _ _ _ H Dw l Xo c _ _ σ r U Uw k ξ' x Xx hX 𝔄 La lam _ hU hξ hx h𝔄 hΛ hl
  letI := H.starRing
  intro A gam ξ DB tyB eB hO hrk hp hq hB
  obtain ⟨hr, h2, -⟩ := hU
  obtain ⟨hp0, hΨ⟩ := h2 k
  obtain ⟨hEF, ⟨t, ht, htξ⟩, T₀, hT⟩ := hO
  obtain ⟨s, hs, h, hh⟩ := hT (((T₀ + 1 : ℝ) : ℂ) * Complex.I) (by simp)
  obtain ⟨τ₀⟩ : Nonempty (U.X k).Ψ := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases hτ : τ ∈ (U.X k).Ψ
    · exact ⟨⟨τ, hτ⟩⟩
    · exact ⟨⟨ComplexEmbedding.conjugate τ, by
        by_contra h'
        exact hτ (((U.X k).cmType τ).2 h')⟩⟩
  obtain ⟨hb1, hb2⟩ := IsotropicIndexSums.isotropicIndex_bounds (U.X k) hξ.2.1 hξ.2.2 τ₀
  have hξy : ∀ v, ((ξ (gam v).y : ℤ) : ℚ) =
      Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (Uw.φ k v : Fin r → E) ξ') := fun v => by
    rw [← htξ, LinearMap.IsAlt.neg (Uw.F.Di (Uw.ik k)).alt, Uw.iso, ht]
  have hξb : ∀ (b : 𝓞 E) v, ((ξ (b • (gam v).y) : ℤ) : ℚ) =
      Algebra.trace ℚ E ((b : E) * (-(U.X k).ξ0 * herm (U.X k).Gm (Uw.φ k v : Fin r → E) ξ')) := fun b v => by
    rw [← AnArc.La.smul_y, ← map_smul, hξy, map_smul, Submodule.coe_smul, ← algebraMap_smul E, herm_smul_left,
      mul_left_comm]
  have hξ0 : ξ ≠ 0 := fun h0 => by
    have : (Uw.F.Di (Uw.ik k)).EF t = (Uw.F.Di (Uw.ik k)).EF 0 := LinearMap.ext fun v => by
      simpa [h0] using htξ v
    apply hξ.2.2
    rw [← ht, (Uw.F.Di (Uw.ik k)).unimod.1 this]
    simp
  have hy : ∀ v, herm (U.X k).Gm (Uw.φ k v : Fin r → E) ξ' = 0 → (gam v).y = 0 := fun v hv =>
    eq_zero_of_rank_one hrk ξ hξ0 fun b => by
      have := hξb b v
      rw [hv] at this
      simpa using this
  have hty : (gam t).y = 0 := hy t (ht ▸ ht ▸ hξ.2.1)
  have htl : (gam t).l = 0 := by
    refine A.Ef_bij.1 (LinearMap.ext fun m => ?_)
    have h1 := htξ (gam.symm (AnArc.La.mk 0 0 m))
    rw [← hEF, gam.apply_symm_apply, AnArc.EF_apply] at h1
    simpa using h1
  let L₀ : A.La →ₗ[𝓞 E] DB.La :=
    { toFun := fun v => eB.symm v.l
      map_add' := fun _ _ => by simp
      map_smul' := fun a v => eB.injective (by simp [hB.2.2.1]) }
  let L : (U.X k).Λ →ₗ[𝓞 E] DB.La := L₀ ∘ₗ gam.toLinearMap ∘ₗ (Uw.φ k).symm.toLinearMap
  have hL : ∀ v, eB (L (Uw.φ k v)) = (gam v).l := fun v => by simp [L, L₀]
  refine exists_cmLat H (U.X k) x hx Xx hX 𝔄 h𝔄 hb1 (by omega) (by omega) hΨ hΛ DB hB.2.2.2.2 L ξ' hξ ?_ ?_ ?_ ?_
    La lam hl
  · have : (⟨ξ', hξ.1⟩ : (U.X k).Λ) = Uw.φ k t := Subtype.ext ht.symm
    apply eB.injective
    rw [this, hL, htl, map_zero]
  · intro a b ha hb
    obtain ⟨a, rfl⟩ := (Uw.φ k).surjective a
    obtain ⟨b, rfl⟩ := (Uw.φ k).surjective b
    rw [← Uw.iso, ← hEF, hB.2.2.2.1, hL, hL, AnArc.EF_apply, hy a ha, hy b hb]
    simp
  · intro z
    refine ⟨Uw.φ k (gam.symm (AnArc.La.mk 0 0 (eB z))), ?_, eB.injective (by rw [hL]; simp)⟩
    have := eq_zero_of_trace fun b => (hξb b (gam.symm (AnArc.La.mk 0 0 (eB z)))).symm.trans (by simp)
    exact (mul_eq_zero.1 this).resolve_left (neg_ne_zero.2 (U.X k).ξ0_ne)
  · rintro a ha i ⟨c', hc'⟩
    obtain ⟨a, rfl⟩ := (Uw.φ k).surjective a
    let π : (Fin Uw.g → ℂ) →ₗ[ℂ] (Fin A.gB → ℂ) := LinearMap.snd ℂ _ _ ∘ₗ h.toLinearMap
    have hπ : ∀ v, π (Uw.Pm k ⟨_, hs⟩ v) = A.ct (gam v).y + (gam v).l := fun v => by
      simp [π, hh]
    have hper := Uw.period k ⟨_, hs⟩
    have key := apply_eq_zero _ tyB π (Uw.Pm k ⟨_, hs⟩) hper.2.2.2.1 (fun b m j => by
      rw [← funext (hper.1 b m), hπ, hπ, map_smul, AnArc.La.smul_y, AnArc.La.smul_l, A.ct_smul, AnArc.coe_FLam,
        ← map_add, hB.1]) i (Uw.Pm k ⟨_, hs⟩ a) (Uw.Pm k ⟨_, hs⟩ t) (by simp [hπ, hty, htl]) c' (fun j hj => by
      rw [Uw.Pm_eq, Uw.Pm_eq, ht, perFr_flow _ hξ.2.1 hb1 _ _ ha, perFr_flow _ hξ.2.1 hb1 _ _ hξ.2.1, hj, hc'])
    rw [hπ, hy a ha, map_zero, zero_add, ← hL] at key
    exact key

end GlobalTheory.ArcCM.SplitLat
