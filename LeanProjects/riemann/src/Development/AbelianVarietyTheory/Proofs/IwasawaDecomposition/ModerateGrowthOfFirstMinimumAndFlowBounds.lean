import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FirstMinimumEqZeroOfRankZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicThreshold
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowDomainCriterionHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.HermLinApply
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.FirstMinimumInvariantContinuousPos

noncomputable section

namespace GlobalTheory.CuspDescent

section Count

variable {G : Type} [AddCommGroup G]

theorem exists_class (G : Type) [AddCommGroup G] [Module.Finite ℤ G] :
    ∃ n : ℕ, ∀ M : ℕ, ∃ cl : G → Fin n → ZMod M, ∀ v w, cl v = cl w → ∃ u, v - w = (M : ℤ) • u := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' ℤ G
  refine ⟨n, fun M => ?_⟩
  choose c hc using hf
  refine ⟨fun v i => (c v i : ZMod M), fun v w h => ?_⟩
  have h1 : ∀ i, ∃ k : ℤ, c v i - c w i = (M : ℤ) * k := fun i =>
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (congrFun h i).symm
  choose k hk using h1
  refine ⟨f k, ?_⟩
  rw [← map_smul, ← hc v, ← hc w, ← map_sub]
  congr 1
  funext i
  simpa using hk i

theorem card_le_of_class {n M : ℕ} (hM : 0 < M) (cl : G → Fin n → ZMod M)
    (hcl : ∀ v w, cl v = cl w → ∃ u, v - w = (M : ℤ) • u) (Q : G → ℝ)
    (hsub : ∀ v w, Q (v - w) ≤ 2 * Q v + 2 * Q w) (hsm : ∀ (k : ℤ) v, Q (k • v) = (k : ℝ) ^ 2 * Q v)
    (δ η : ℝ) (hη : 4 * δ ≤ (M : ℝ) ^ 2 * η) (hT : {v | Q v < η}.Finite) :
    {v | Q v < δ}.Finite ∧ {v | Q v < δ}.ncard ≤ M ^ n * {v | Q v < η}.ncard := by
  classical
  haveI : NeZero M := ⟨hM.ne'⟩
  have h1 : ∀ a : Fin n → ZMod M, ∃ w, (∃ v, Q v < δ ∧ cl v = a) → Q w < δ ∧ cl w = a := by
    intro a
    by_cases h : ∃ v, Q v < δ ∧ cl v = a
    · obtain ⟨v, hv⟩ := h
      exact ⟨v, fun _ => hv⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose rep hrep using h1
  have h2 : ∀ v, ∃ u, Q v < δ → v - rep (cl v) = (M : ℤ) • u ∧ Q u < η := by
    intro v
    by_cases hv : Q v < δ
    · obtain ⟨ha, hb⟩ := hrep (cl v) ⟨v, hv, rfl⟩
      obtain ⟨u, hu⟩ := hcl v _ hb.symm
      refine ⟨u, fun _ => ⟨hu, ?_⟩⟩
      have h3 := hsub v (rep (cl v))
      rw [hu, hsm] at h3
      have hM' : (0 : ℝ) < (M : ℝ) ^ 2 := by positivity
      push_cast at h3
      exact lt_of_mul_lt_mul_left (a := (M : ℝ) ^ 2) (by linarith) hM'.le
    · exact ⟨0, fun h => absurd h hv⟩
  choose g hg using h2
  have hfin : ((Set.univ : Set (Fin n → ZMod M)) ×ˢ {v | Q v < η}).Finite := Set.finite_univ.prod hT
  have hmap : Set.MapsTo (fun v => (cl v, g v)) {v | Q v < δ}
      ((Set.univ : Set (Fin n → ZMod M)) ×ˢ {v | Q v < η}) := fun v hv => ⟨trivial, (hg v hv).2⟩
  have hinj : Set.InjOn (fun v => (cl v, g v)) {v | Q v < δ} := by
    intro v hv w hw h
    have ha : cl v = cl w := congrArg Prod.fst h
    have hb : g v = g w := congrArg Prod.snd h
    have h1 := (hg v hv).1
    have h2 := (hg w hw).1
    rw [ha, hb, ← h2] at h1
    exact sub_left_injective h1
  refine ⟨Set.Finite.of_injOn hmap hinj hfin, ?_⟩
  have := Set.ncard_le_ncard_of_injOn _ hmap hinj hfin
  rwa [Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_pi, Finset.prod_const,
    ZMod.card, Finset.card_univ, Fintype.card_fin] at this

theorem mul_card_le (Q Q' : G → ℝ)
    (hsub : ∀ v w, Q (v - w) ≤ 2 * Q v + 2 * Q w) (hsm : ∀ (k : ℤ) v, Q (k • v) = (k : ℝ) ^ 2 * Q v)
    (hsub' : ∀ v w, Q' (v - w) ≤ 2 * Q' v + 2 * Q' w) (hsm' : ∀ (k : ℤ) v, Q' (k • v) = (k : ℝ) ^ 2 * Q' v)
    (δ : ℝ) (K : ℕ) (ξ : G) (h0 : 0 < Q ξ) (hξ : 16 * (K : ℝ) ^ 2 * Q ξ < δ)
    (hξ' : Q' ξ = 16 * (K : ℝ) ^ 2 * Q ξ) (hK : 0 < K)
    (hle : ∀ v, Q' v < δ → Q v ≤ Q' v) (hS : {v | Q v < δ}.Finite) :
    K * {v | Q' v < δ / 4}.ncard ≤ {v | Q v < δ}.ncard := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  set a : ℝ := 16 * (K : ℝ) ^ 2 * Q ξ with ha
  have ha0 : 0 < a := by positivity
  have hδ : 0 < δ := ha0.trans hξ
  set y : ℝ := Real.sqrt (δ / a) with hy
  have hy2 : y ^ 2 = δ / a := Real.sq_sqrt (by positivity)
  have hy1 : 1 ≤ y := Real.one_le_sqrt.mpr ((one_le_div ha0).mpr hξ.le)
  set L : ℕ := ⌈y⌉₊ with hL
  have hL1 : y ≤ L := Nat.le_ceil y
  have hL2 : (L : ℝ) ≤ 2 * y := by
    have := Nat.ceil_lt_add_one (show 0 ≤ y by linarith)
    linarith
  have hA : δ ≤ (L : ℝ) ^ 2 * a := by
    have : y ^ 2 ≤ (L : ℝ) ^ 2 := by gcongr
    rw [hy2, div_le_iff₀ ha0] at this
    exact this
  have hB : (L : ℝ) ^ 2 * a ≤ 4 * δ := by
    have : (L : ℝ) ^ 2 ≤ (2 * y) ^ 2 := by gcongr
    rw [mul_pow, hy2] at this
    calc (L : ℝ) ^ 2 * a ≤ 2 ^ 2 * (δ / a) * a := by gcongr
      _ = 4 * δ := by field_simp; norm_num
  have hmap : ∀ p ∈ (Set.univ : Set (Fin K)) ×ˢ {v | Q' v < δ / 4},
      p.2 - (((p.1 : ℕ) : ℤ) * L) • ξ ∈ {v | Q v < δ} := by
    rintro ⟨j, v⟩ ⟨-, hv⟩
    have hv' : Q' v < δ / 4 := hv
    have h1 := hsub v ((((j : ℕ) : ℤ) * L) • ξ)
    have h2 := hle v (by linarith)
    rw [hsm] at h1
    have hj : ((j : ℕ) : ℝ) ≤ K := by exact_mod_cast j.2.le
    have h3 : ((((j : ℕ) : ℤ) * L : ℤ) : ℝ) ^ 2 * Q ξ ≤ δ / 4 := by
      push_cast
      calc (((j : ℕ) : ℝ) * L) ^ 2 * Q ξ ≤ ((K : ℝ) * L) ^ 2 * Q ξ := by gcongr
        _ = (L : ℝ) ^ 2 * a / 16 := by rw [ha]; ring
        _ ≤ δ / 4 := by linarith
    show Q _ < δ
    linarith
  have hinj : Set.InjOn (fun p : Fin K × G => p.2 - (((p.1 : ℕ) : ℤ) * L) • ξ)
      ((Set.univ : Set (Fin K)) ×ˢ {v | Q' v < δ / 4}) := by
    rintro ⟨j, v⟩ ⟨-, hv⟩ ⟨i, w⟩ ⟨-, hw⟩ h
    have hv' : Q' v < δ / 4 := hv
    have hw' : Q' w < δ / 4 := hw
    have h' : v - (((j : ℕ) : ℤ) * L) • ξ = w - (((i : ℕ) : ℤ) * L) • ξ := h
    have h1 : v - w = ((((j : ℕ) : ℤ) - (i : ℕ)) * L) • ξ := by
      rw [sub_mul, sub_smul]
      rw [sub_eq_sub_iff_sub_eq_sub] at h'
      exact h'
    have h2 := hsub' v w
    rw [h1, hsm', hξ'] at h2
    have hji : ((j : ℕ) : ℤ) - (i : ℕ) = 0 := by
      by_contra hne
      have h3 : (1 : ℤ) ≤ (((j : ℕ) : ℤ) - (i : ℕ)) ^ 2 := by
        have := sq_pos_of_ne_zero hne
        omega
      have h4 : (1 : ℝ) ≤ ((((j : ℕ) : ℤ) - (i : ℕ) : ℤ) : ℝ) ^ 2 := by exact_mod_cast h3
      rw [Int.cast_mul, mul_pow, Int.cast_natCast, mul_assoc] at h2
      have h5 : (L : ℝ) ^ 2 * a ≤ ((((j : ℕ) : ℤ) - (i : ℕ) : ℤ) : ℝ) ^ 2 * ((L : ℝ) ^ 2 * a) :=
        le_mul_of_one_le_left (by positivity) h4
      linarith
    rw [hji, zero_mul, zero_smul, sub_eq_zero] at h1
    have : j = i := Fin.ext (by omega)
    rw [this, h1]
  have := Set.ncard_le_ncard_of_injOn _ hmap hinj hS
  rwa [Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at this

end Count

section Lattice

open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def sqLen (x : Frame X.Ψ r) (v : X.Λ) : ℝ := ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 (v : Fin r → E))

theorem maj_parallelogram (x : Frame X.Ψ r) (τ : X.Ψ) (u v : Fin r → ℂ) :
    X.maj x τ (u - v) + X.maj x τ (u + v) = 2 * X.maj x τ u + 2 * X.maj x τ v := by
  have h : X.posPart x τ (u - v) + X.posPart x τ (u + v) = 2 * X.posPart x τ u + 2 * X.posPart x τ v := by
    unfold Data.posPart
    rw [two_mul, two_mul, ← add_re, ← add_re, ← add_re, ← add_re]
    congr 1
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [hermC_add_left, hermC_sub_left, map_add, map_sub]
    ring
  unfold Data.maj
  simp only [hermC_add_left, hermC_sub_left, hermC_add_right, hermC_sub_right, add_re, sub_re]
  linarith

theorem sqLen_nonneg {x : Frame X.Ψ r} (hx : x ∈ X.dom) (v : X.Λ) : 0 ≤ sqLen X x v :=
  Finset.sum_nonneg fun τ _ => mul_nonneg (IsotropicThreshold.c_pos X τ).le (MajorantOperators.maj_nonneg hx τ _)

theorem sqLen_sub {x : Frame X.Ψ r} (hx : x ∈ X.dom) (v w : X.Λ) :
    sqLen X x (v - w) ≤ 2 * sqLen X x v + 2 * sqLen X x w := by
  unfold sqLen
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun τ _ => ?_
  have e : Data.emb τ.1 ((v - w : X.Λ) : Fin r → E) = Data.emb τ.1 (v : Fin r → E) - Data.emb τ.1 (w : Fin r → E) := by
    funext a
    simp [Data.emb]
  have h1 := maj_parallelogram X x τ (Data.emb τ.1 (v : Fin r → E)) (Data.emb τ.1 (w : Fin r → E))
  have h2 := MajorantOperators.maj_nonneg hx τ (Data.emb τ.1 (v : Fin r → E) + Data.emb τ.1 (w : Fin r → E))
  have h3 := IsotropicThreshold.c_pos X τ
  rw [e]
  nlinarith

theorem sqLen_smul (x : Frame X.Ψ r) (k : ℤ) (v : X.Λ) : sqLen X x (k • v) = (k : ℝ) ^ 2 * sqLen X x v := by
  unfold sqLen
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have e : Data.emb τ.1 ((k • v : X.Λ) : Fin r → E) = (k : ℂ) • Data.emb τ.1 (v : Fin r → E) := by
    funext a
    simp [Data.emb]
  rw [e, UnipMove.DeltaValuation.maj_smul, Complex.normSq_intCast]
  ring

theorem firstMinimumSq_le_latticeVectorSqLengthAtFrame {x : Frame X.Ψ r} (hx : x ∈ X.dom) {v : X.Λ} (hv : v ≠ 0) : X.firstMinimumSq x ≤ sqLen X x v := by
  refine csInf_le ⟨0, ?_⟩ ⟨v, v.2, fun h => hv (Subtype.ext h), rfl⟩
  rintro t ⟨u, hu, -, rfl⟩
  exact sqLen_nonneg X hx ⟨u, hu⟩

theorem exists_short (hr : 0 < r) {x : Frame X.Ψ r} {ε : ℝ} (h : X.firstMinimumSq x < ε) :
    ∃ v : X.Λ, v ≠ 0 ∧ sqLen X x v < ε := by
  obtain ⟨u, hu, hu0⟩ := AR.Inst.lam_ne X hr
  obtain ⟨t, ⟨v, hv, hv0, rfl⟩, ht⟩ := exists_lt_of_csInf_lt (by exact ⟨_, ⟨u, hu, hu0, rfl⟩⟩) h
  exact ⟨⟨v, hv⟩, fun h => hv0 (congrArg Subtype.val h), ht⟩

theorem orth_threshold (hF : FlowMajSt) : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ X.dom, ∀ v w : X.Λ,
    sqLen X x v < δ → sqLen X x w < δ → herm X.Gm (v : Fin r → E) w = 0 := by
  classical
  set D : ℝ := ∑ σ : E →+* ℂ, ‖σ (X.den : E)‖ + 1 with hD
  have hD0 : 0 < D := by positivity
  have hDσ : ∀ σ : E →+* ℂ, ‖σ (X.den : E)‖ < D := by
    intro σ
    have := Finset.single_le_sum (f := fun σ : E →+* ℂ => ‖σ (X.den : E)‖)
      (fun σ _ => norm_nonneg _) (Finset.mem_univ σ)
    linarith
  obtain ⟨cm, hcm0, hcm⟩ : ∃ cm : ℝ, 0 < cm ∧ ∀ τ, cm ≤ X.c τ := by
    rcases isEmpty_or_nonempty X.Ψ with h | h
    · exact ⟨1, one_pos, fun τ => h.elim τ⟩
    · obtain ⟨τ0, hτ0⟩ := Finite.exists_min (fun τ : X.Ψ => X.c τ)
      exact ⟨_, IsotropicThreshold.c_pos X τ0, hτ0⟩
  refine ⟨cm / D, by positivity, fun x hx v w hv hw => ?_⟩
  have hden : (X.den : E) ≠ 0 := fun h => X.den_ne (by exact_mod_cast h)
  have hmaj : ∀ u : X.Λ, sqLen X x u < cm / D → ∀ τ : X.Ψ, X.maj x τ (Data.emb τ.1 (u : Fin r → E)) < 1 / D := by
    intro u hu τ
    have h1 : X.c τ * X.maj x τ (Data.emb τ.1 (u : Fin r → E)) ≤ sqLen X x u :=
      Finset.single_le_sum (f := fun τ' : X.Ψ => X.c τ' * X.maj x τ' (Data.emb τ'.1 (u : Fin r → E)))
        (fun τ' _ => mul_nonneg (IsotropicThreshold.c_pos X τ').le (MajorantOperators.maj_nonneg hx τ' _)) (Finset.mem_univ τ)
    have h2 := mul_le_mul_of_nonneg_right (hcm τ) (MajorantOperators.maj_nonneg hx τ (Data.emb τ.1 (u : Fin r → E)))
    rw [div_eq_mul_one_div] at hu
    exact lt_of_mul_lt_mul_left (a := cm) (by linarith) hcm0.le
  have key : ∀ τ : X.Ψ, ‖τ.1 ((X.den : E) * herm X.Gm (v : Fin r → E) w)‖ < 1 := by
    intro τ
    rw [map_mul, norm_mul, ← hermC_emb]
    have h1 := ((hF E r X).2 x hx τ (Data.emb τ.1 (v : Fin r → E)) (Data.emb τ.1 (w : Fin r → E))).1
    have h2 : ‖hermC τ.1 X.Gm (Data.emb τ.1 (v : Fin r → E)) (Data.emb τ.1 (w : Fin r → E))‖ ≤ 1 / D := by
      refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp (h1.trans ?_)
      rw [sq]
      exact mul_le_mul (hmaj v hv τ).le (hmaj w hw τ).le (MajorantOperators.maj_nonneg hx τ _) (by positivity)
    calc _ ≤ ‖τ.1 (X.den : E)‖ * (1 / D) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ < D * (1 / D) := mul_lt_mul_of_pos_right (hDσ τ.1) (by positivity)
      _ = 1 := by field_simp
  have hall : ∀ σ : E →+* ℂ, ‖σ ((X.den : E) * herm X.Gm (v : Fin r → E) w)‖ < 1 := by
    intro σ
    by_cases hσ : σ ∈ X.Ψ
    · exact key ⟨σ, hσ⟩
    · have hcc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
        RingHom.ext fun a => by simp
      have hc : ComplexEmbedding.conjugate σ ∈ X.Ψ := by
        rw [X.cmType, hcc]
        exact hσ
      have h := key ⟨_, hc⟩
      simpa [ComplexEmbedding.conjugate_coe_eq] using h
  have h0 := UnipotentCoefficientShift.eq_zero_of_conj_lt_one (X.Λ_int v v.2 w w.2) hall
  exact (mul_eq_zero.mp h0).resolve_left hden

theorem flow_shrink {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {q : ℝ} (hq : 0 < q)
    (s : X.Ψ → ℝ) :
    X.flow ξ (fun τ => (s τ : ℂ) + I * (((q - 1) * X.tt ξ x τ : ℝ) : ℂ)) x ∈ X.dom ∧
    ∀ τ, X.maj (X.flow ξ (fun τ => (s τ : ℂ) + I * (((q - 1) * X.tt ξ x τ : ℝ) : ℂ)) x) τ (Data.emb τ.1 ξ) =
      q⁻¹ * X.maj x τ (Data.emb τ.1 ξ) := by
  have hiso : X.IsIsoV (fun τ => Data.emb τ.1 ξ) := fun τ =>
    ⟨by rw [hermC_emb, hξ.2.1, map_zero], emb_ne_zero τ.1 hξ.2.2⟩
  obtain ⟨h1, h2⟩ := flowDomainCriterion_holds r X _ hiso x hx (fun τ => (s τ : ℂ) + I * (((q - 1) * X.tt ξ x τ : ℝ) : ℂ))
  have him : ∀ τ, ((s τ : ℂ) + I * (((q - 1) * X.tt ξ x τ : ℝ) : ℂ)).im = (q - 1) * X.tt ξ x τ := by
    intro τ
    rw [add_im, ofReal_im, I_mul_im, ofReal_re, zero_add]
  have hm : ∀ τ, 0 < X.maj x τ (Data.emb τ.1 ξ) := fun τ => X.maj_pos hx τ (hiso τ).2
  have ht : ∀ τ, 0 < X.tt ξ x τ := fun τ => one_div_pos.mpr (mul_pos (IsotropicThreshold.c_pos X τ) (hm τ))
  have hd := h1.mpr fun τ => by
    rw [him]
    show 0 < 1 + (q - 1) * X.tt ξ x τ / X.tt ξ x τ
    rw [mul_div_assoc, div_self (ht τ).ne']
    linarith
  refine ⟨hd, fun τ => ?_⟩
  have h3 := h2 hd τ
  rw [him] at h3
  have h4 := X.maj_pos hd τ (hiso τ).2
  have h5 := IsotropicThreshold.c_pos X τ
  have h6 := hm τ
  change 1 / (X.c τ * X.maj (X.flow ξ _ x) τ (Data.emb τ.1 ξ)) = 1 / (X.c τ * X.maj x τ (Data.emb τ.1 ξ)) +
    (q - 1) * (1 / (X.c τ * X.maj x τ (Data.emb τ.1 ξ))) at h3
  change 0 < X.maj (X.flow ξ _ x) τ (Data.emb τ.1 ξ) at h4
  generalize X.maj (X.flow ξ _ x) τ (Data.emb τ.1 ξ) = a at h3 h4 ⊢
  field_simp at h3 ⊢
  linarith

theorem card_short_le (hr : 0 < r) {n : ℕ}
    (hn : ∀ M : ℕ, ∃ cl : X.Λ → Fin n → ZMod M, ∀ v w, cl v = cl w → ∃ u, v - w = (M : ℤ) • u)
    {δ : ℝ} (hδ : 0 < δ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    {v | sqLen X x v < δ}.Finite ∧
      ({v | sqLen X x v < δ}.ncard : ℝ) ≤ ((2 * Real.sqrt δ + X.la1 x) / X.la1 x) ^ n := by
  have hl := AR.Inst.la1_pos_of_mem_dom X hr hx
  have hl2 : X.la1 x ^ 2 = X.firstMinimumSq x := Real.sq_sqrt (Real.sqrt_pos.1 hl).le
  have hs := Real.sqrt_pos.mpr hδ
  set M : ℕ := ⌈2 * Real.sqrt δ / X.la1 x⌉₊ with hM
  have hM0 : 0 < M := Nat.ceil_pos.mpr (by positivity)
  have hM1 : 2 * Real.sqrt δ / X.la1 x ≤ M := Nat.le_ceil _
  have hM2 : (M : ℝ) ≤ (2 * Real.sqrt δ + X.la1 x) / X.la1 x := by
    rw [add_div, div_self hl.ne']
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have hη : 4 * δ ≤ (M : ℝ) ^ 2 * X.firstMinimumSq x := by
    rw [div_le_iff₀ hl] at hM1
    have : (2 * Real.sqrt δ) ^ 2 ≤ (M * X.la1 x) ^ 2 := by gcongr
    rw [mul_pow, mul_pow, Real.sq_sqrt hδ.le, hl2] at this
    linarith
  have hsub : {v | sqLen X x v < X.firstMinimumSq x} ⊆ {0} := fun v hv => by
    by_contra h
    exact absurd (firstMinimumSq_le_latticeVectorSqLengthAtFrame X hx h) (not_le.mpr hv)
  obtain ⟨cl, hcl⟩ := hn M
  obtain ⟨h1, h2⟩ := card_le_of_class hM0 cl hcl (sqLen X x) (sqLen_sub X hx) (sqLen_smul X x) δ _ hη
    ((Set.finite_singleton _).subset hsub)
  have h3 := Set.ncard_le_ncard hsub (Set.finite_singleton _)
  rw [Set.ncard_singleton] at h3
  refine ⟨h1, ?_⟩
  have h4 : {v | sqLen X x v < δ}.ncard ≤ M ^ n := h2.trans (by simpa using Nat.mul_le_mul_left (M ^ n) h3)
  calc ({v | sqLen X x v < δ}.ncard : ℝ) ≤ (M : ℝ) ^ n := by exact_mod_cast h4
    _ ≤ _ := by gcongr

theorem card_short_step (hF : FlowMajSt) (hr : 0 < r) {n : ℕ}
    (hn : ∀ M : ℕ, ∃ cl : X.Λ → Fin n → ZMod M, ∀ v w, cl v = cl w → ∃ u, v - w = (M : ℤ) • u)
    {δ : ℝ} (hδ : 0 < δ) (horth : ∀ x ∈ X.dom, ∀ v w : X.Λ,
      sqLen X x v < δ → sqLen X x w < δ → herm X.Gm (v : Fin r → E) w = 0)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) {ξ : X.Λ} (hξ : X.IsIso (ξ : Fin r → E))
    (hshort : 16 * ((2 * 4 ^ n : ℕ) : ℝ) ^ 2 * sqLen X x ξ < δ) {s : X.Ψ → ℂ} (hy : X.flow ξ s x ∈ X.dom)
    (hm : ∀ τ, X.maj (X.flow ξ s x) τ (Data.emb τ.1 ξ) =
      16 * ((2 * 4 ^ n : ℕ) : ℝ) ^ 2 * X.maj x τ (Data.emb τ.1 ξ)) :
    2 * {v | sqLen X (X.flow ξ s x) v < δ}.ncard ≤ {v | sqLen X x v < δ}.ncard := by
  have hK : 0 < 2 * 4 ^ n := by positivity
  have hK1 : (1 : ℝ) ≤ ((2 * 4 ^ n : ℕ) : ℝ) := by exact_mod_cast hK
  have hξ0 : ξ ≠ 0 := fun h => hξ.2.2 (congrArg Subtype.val h)
  have h0 : 0 < sqLen X x ξ := (Real.sqrt_pos.1 (AR.Inst.la1_pos_of_mem_dom X hr hx)).trans_le (firstMinimumSq_le_latticeVectorSqLengthAtFrame X hx hξ0)
  have hξ' : sqLen X (X.flow ξ s x) ξ = 16 * ((2 * 4 ^ n : ℕ) : ℝ) ^ 2 * sqLen X x ξ := by
    unfold sqLen
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hm]
    ring
  have hle : ∀ v, sqLen X (X.flow ξ s x) v < δ → sqLen X x v ≤ sqLen X (X.flow ξ s x) v := by
    intro v hv
    have h1 := horth _ hy v ξ hv (hξ' ▸ hshort)
    refine Finset.sum_le_sum fun τ _ => mul_le_mul_of_nonneg_left ?_ (IsotropicThreshold.c_pos X τ).le
    rw [(hF E r X).1 ξ hξ x hx s hy τ _ (by rw [hermC_emb, h1, map_zero]), hm]
    refine le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) ?_)
    have h2 := MajorantOperators.maj_nonneg hx τ (Data.emb τ.1 (ξ : Fin r → E))
    exact sub_nonneg.mpr (le_mul_of_one_le_left h2 (by nlinarith))
  have h1 := mul_card_le (sqLen X x) (sqLen X (X.flow ξ s x)) (sqLen_sub X hx) (sqLen_smul X x) (sqLen_sub X hy)
    (sqLen_smul X _) δ (2 * 4 ^ n) ξ h0 hshort hξ' hK hle (card_short_le X hr hn hδ hx).1
  obtain ⟨cl, hcl⟩ := hn 4
  have h2 := (card_le_of_class (by norm_num) cl hcl (sqLen X (X.flow ξ s x)) (sqLen_sub X hy) (sqLen_smul X _) δ (δ / 4)
    (by push_cast; linarith) (card_short_le X hr hn (by positivity) hy).1).2
  calc _ ≤ 2 * (4 ^ n * {v | sqLen X (X.flow ξ s x) v < δ / 4}.ncard) := Nat.mul_le_mul_left 2 h2
    _ ≤ _ := by rwa [← mul_assoc]

theorem moderate_of_stepBound (hF : FlowMajSt) (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (w : ℝ) (φ : Frame X.Ψ r → ℝ) (hw : 0 ≤ w) (hφ : ∀ x ∈ X.dom, 0 ≤ φ x) (hT : ThickBdd X φ)
    (hS : StepBound X w φ) : ∃ C A : ℝ, ∀ x ∈ X.dom, φ x ≤ C * X.la1 x ^ (-(A * w)) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · refine ⟨φ 0, 0, fun x _ => ?_⟩
    rw [zero_mul, neg_zero, Real.rpow_zero, mul_one, Subsingleton.elim x 0]
  haveI : Module.Finite (𝓞 E) X.Λ := Module.Finite.iff_fg.mpr X.Λ_fg
  haveI : Module.Finite ℤ X.Λ := Module.Finite.trans (𝓞 E) X.Λ
  obtain ⟨n, hn⟩ := exists_class X.Λ
  obtain ⟨δ, hδ, horth⟩ := orth_threshold X hF
  obtain ⟨B, hB0, hB⟩ := GlobalTheory.FJZero.firstMinimum_bounded_on_domain X
  set p : ℝ := 16 * ((2 * 4 ^ n : ℕ) : ℝ) ^ 2 with hp
  set b : ℕ := (4 * n + 6) * Fintype.card X.Ψ with hb
  have hp2 : p = 2 ^ (4 * n + 6) := by
    rw [hp, pow_add, pow_mul]
    push_cast
    rw [mul_pow, ← pow_mul, mul_comm n 2, pow_mul]
    ring
  have hp1 : 1 ≤ p := hp2 ▸ one_le_pow₀ one_le_two
  have hp0 : 0 < p := one_pos.trans_le hp1
  obtain ⟨S0, hS0⟩ := hT (Real.sqrt (δ / p)) (by positivity)
  set S := max S0 0 with hSdef
  have hSn : 0 ≤ S := le_max_right _ _
  have hβ : 0 ≤ (b : ℝ) * w := by positivity
  have hpos : ∀ x ∈ X.dom, 1 ≤ {v | sqLen X x v < δ}.ncard := fun x hx => by
    refine (Set.ncard_pos (card_short_le X hr hn hδ hx).1).mpr ⟨0, ?_⟩
    have := sqLen_smul X x 0 0
    rw [zero_smul, Int.cast_zero, zero_pow two_ne_zero, zero_mul] at this
    show sqLen X x 0 < δ
    rwa [this]
  have main : ∀ m : ℕ, ∀ x ∈ X.dom, {v | sqLen X x v < δ}.ncard = m → φ x ≤ S * (m : ℝ) ^ ((b : ℝ) * w) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro x hx hm
    have hm1 : 1 ≤ m := hm ▸ hpos x hx
    rcases le_or_gt (δ / p) (X.firstMinimumSq x) with h | h
    · have h1 : φ x ≤ S := (hS0 x hx (Real.sqrt_le_sqrt h)).trans (le_max_left _ _)
      exact h1.trans (le_mul_of_one_le_right hSn (Real.one_le_rpow (by exact_mod_cast hm1) hβ))
    obtain ⟨ξ, hξ0, hξ⟩ := exists_short X hr h
    have hshort : p * sqLen X x ξ < δ := by rwa [lt_div_iff₀' hp0] at hξ
    have hξδ : sqLen X x ξ < δ := (le_mul_of_one_le_left (sqLen_nonneg X hx ξ) hp1).trans_lt hshort
    have hiso : X.IsIso (ξ : Fin r → E) := ⟨ξ.2, horth x hx ξ ξ hξδ hξδ, fun h => hξ0 (Subtype.ext h)⟩
    have h1 := hS ξ hiso x hx (fun _ => p⁻¹) (fun _ => ⟨inv_pos.mpr hp0, inv_le_one_of_one_le₀ hp1⟩)
      (S * ((m : ℝ) / 2) ^ ((b : ℝ) * w)) (fun s => by
        obtain ⟨hy, hmaj⟩ := flow_shrink X hiso hx (inv_pos.mpr hp0) s
        rw [inv_inv] at hmaj
        have h2 := card_short_step X hF hr hn hδ horth hx hiso hshort hy hmaj
        rw [hm] at h2
        refine (ih _ (by omega) _ hy rfl).trans (mul_le_mul_of_nonneg_left ?_ hSn)
        refine Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ hβ
        rw [le_div_iff₀' two_pos]
        exact_mod_cast h2)
    refine h1.trans_eq ?_
    have e : ∏ _τ : X.Ψ, p⁻¹ ^ (-w) = (2 : ℝ) ^ ((b : ℝ) * w) := by
      rw [Finset.prod_const, Finset.card_univ, Real.inv_rpow hp0.le, Real.rpow_neg hp0.le, inv_inv, hp2,
        ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul two_pos.le, ← Real.rpow_mul two_pos.le, hb]
      congr 1
      push_cast
      ring
    rw [e, mul_assoc, ← Real.mul_rpow (by positivity) two_pos.le, div_mul_cancel₀ _ two_ne_zero]
  refine ⟨S * (2 * Real.sqrt δ + B) ^ ((n : ℝ) * b * w), n * b, fun x hx => (main _ x hx rfl).trans ?_⟩
  have hl := AR.Inst.la1_pos_of_mem_dom X hr hx
  have h1 : ({v | sqLen X x v < δ}.ncard : ℝ) ≤ ((2 * Real.sqrt δ + B) / X.la1 x) ^ n :=
    (card_short_le X hr hn hδ hx).2.trans (by gcongr; exact hB x hx)
  rw [mul_assoc S]
  refine mul_le_mul_of_nonneg_left ((Real.rpow_le_rpow (Nat.cast_nonneg _) h1 hβ).trans_eq ?_) hSn
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.div_rpow (by positivity) hl.le,
    Real.rpow_neg hl.le, div_eq_mul_inv, mul_assoc]

end Lattice

end GlobalTheory.CuspDescent
