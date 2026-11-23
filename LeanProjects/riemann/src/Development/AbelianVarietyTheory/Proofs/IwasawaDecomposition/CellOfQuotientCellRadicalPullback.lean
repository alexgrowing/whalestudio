import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullLinInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim

noncomputable section

namespace GlobalTheory.PolFan.CarDim

theorem projective_quot_orad (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    [Module.Finite (𝓞 E) X] (β : LinearMap.BilinForm ℤ X) :
    Module.Projective (𝓞 E) (X ⧸ (orad β : Submodule (𝓞 E) X)) := by
  classical
  have hZ : ∀ n : ℤ, n ≠ 0 → ∀ y : X, n • y ∈ (orad β : Submodule (𝓞 E) X) → y ∈ (orad β : Submodule (𝓞 E) X) :=
    fun n hn y hy a z => by
      have h := hy a z
      rw [smul_comm, map_zsmul, LinearMap.smul_apply, smul_eq_mul] at h
      exact (mul_eq_zero.1 h).resolve_left hn
  have hO : ∀ a : 𝓞 E, a ≠ 0 → ∀ y : X, a • y ∈ (orad β : Submodule (𝓞 E) X) → y ∈ (orad β : Submodule (𝓞 E) X) := by
    intro a ha y hy
    have hne : (Ideal.span {a}).comap (algebraMap ℤ (𝓞 E)) ≠ ⊥ :=
      Ideal.comap_ne_bot_of_integral_mem ha (Ideal.mem_span_singleton_self a) (Algebra.IsIntegral.isIntegral a)
    obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hn)
    refine hZ n hn0 y fun b z => ?_
    have h := hy (b * a') z
    rw [mul_smul, smul_smul a' a y, ha', algebraMap_int_eq, eq_intCast, Int.cast_smul_eq_zsmul] at h
    exact h
  have htor : Submodule.torsion (𝓞 E) (X ⧸ (orad β : Submodule (𝓞 E) X)) = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun u hu => ?_
    obtain ⟨⟨a, ha⟩, hau⟩ := (Submodule.mem_torsion_iff u).1 hu
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    rw [Submonoid.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hau
    rw [Submodule.Quotient.mk_eq_zero]
    exact hO a (nonZeroDivisors.ne_zero ha) y hau
  have : Module.Flat (𝓞 E) (X ⧸ (orad β : Submodule (𝓞 E) X)) := IsDedekindDomain.flat_iff_torsion_eq_bot.2 htor
  have : Module.FinitePresentation (𝓞 E) (X ⧸ (orad β : Submodule (𝓞 E) X)) := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

theorem genRank_le_of_smul_mem_span {X : Type} [AddCommGroup X] {m m' : ℕ} (A : Fin m' → LinearMap.BilinForm ℤ X)
    (B : Fin m → LinearMap.BilinForm ℤ X)
    (h : ∀ j, ∃ k : ℕ, 0 < k ∧ k • A j ∈ Submodule.span ℤ (Set.range B)) : genRank A ≤ genRank B := by
  classical
  unfold genRank
  choose k hk hkm using h
  set P : ℕ := ∏ j, k j with hPdef
  have hP : 0 < P := Finset.prod_pos fun j _ => hk j
  have hmem : ∀ x ∈ Submodule.span ℤ (Set.range A), (P : ℤ) • x ∈ Submodule.span ℤ (Set.range B) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      have e : P = (∏ i ∈ Finset.univ.erase j, k i) * k j := (Finset.prod_erase_mul _ _ (Finset.mem_univ j)).symm
      rw [natCast_zsmul, e, mul_smul]
      exact nsmul_mem (hkm j) _
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx
  have : Module.Finite ℤ (Submodule.span ℤ (Set.range B)) :=
    Module.Finite.span_of_finite ℤ (Set.finite_range B)
  let f : Submodule.span ℤ (Set.range A) →ₗ[ℤ] Submodule.span ℤ (Set.range B) :=
    ((P : ℤ) • (Submodule.span ℤ (Set.range A)).subtype).codRestrict _ fun x => hmem x x.2
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hx' : (P : ℤ) • (x : LinearMap.BilinForm ℤ X) = 0 := congrArg Subtype.val hx
    have hP' : (P : ℤ) ≠ 0 := by exact_mod_cast hP.ne'
    ext a b
    have := LinearMap.congr_fun₂ hx' a b
    simp only [LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply] at this
    simpa using (mul_eq_zero.1 this).resolve_left hP'
  exact LinearMap.finrank_le_finrank_of_injective hf

theorem intLin_eq_sum_of_toReal {X : Type} [AddCommGroup X] {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ)
    (β : LinearMap.BilinForm ℤ X) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) (h : toReal β = ∑ i, c i • toReal (γ i)) :
    (ℓ β : ℝ) = ∑ i, c i * (ℓ (γ i) : ℝ) := by
  have h0 : ∑ o : Option (Fin m), (o.elim (-1) c) • toReal (LinearMap.id (R := ℤ) (o.elim β γ)) = 0 := by
    rw [Fintype.sum_option]
    simp only [Option.elim, LinearMap.id_apply, h, neg_one_smul, neg_add_cancel]
  have := sum_mul_eq_zero_of_sum_toReal (j := LinearMap.id) (fun _ _ h => h) ℓ h0
  rw [Fintype.sum_option] at this
  simp only [Option.elim] at this
  linarith

theorem exists_radical_test {O : Type} [CommRing O] [IsNoetherianRing O] (bar : O → O) {X : Type} [AddCommGroup X]
    [Module O X] [Module.Finite O X] (K : Submodule O X) :
    ∃ hK : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) →
      0 ≤ hK β ∧ (hK β = 0 ↔ ∀ k ∈ K, ∀ y, β k y = 0) := by
  classical
  obtain ⟨G, hG⟩ := IsNoetherian.noetherian K
  refine ⟨∑ k ∈ G, LinearMap.applyₗ k ∘ₗ LinearMap.applyₗ k, fun β hβ hp => ?_⟩
  have hv : (∑ k ∈ G, (LinearMap.applyₗ k ∘ₗ LinearMap.applyₗ k : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ)) β = ∑ k ∈ G, β k k := by
    simp
  rw [hv]
  refine ⟨Finset.sum_nonneg fun k _ => hp k, fun h0 => ?_, fun h0 => Finset.sum_eq_zero fun k hk => h0 k ?_ k⟩
  · have hk0 : ∀ k ∈ G, β k k = 0 := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => hp k).1 h0
    rw [← hG]
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact fun y => ConeSub.eq_zero_of_self_eq_zero β hβ.1 hp (hk0 x hx) y
    | zero => simp
    | add x x' _ _ h1 h2 => intro y; rw [map_add, LinearMap.add_apply, h1, h2, add_zero]
    | smul a x _ h1 => intro y; rw [hβ.2 a x y]; exact h1 _
  · rw [← hG]
    exact Submodule.subset_span hk

end GlobalTheory.PolFan.CarDim

namespace GlobalTheory.PolFan.CarDim

theorem intLin_eq_of_inCone {O : Type} [CommRing O] (φ : InvFun O) {Y : Type} [AddCommGroup Y] [Module O Y]
    [Module.Finite O Y] {n : ℕ} {γ : Fin n → LinearMap.BilinForm ℤ Y} (hl : φ.LinearOn γ) {N : ℕ}
    {ℓ : LinearMap.BilinForm ℤ Y →ₗ[ℤ] ℤ} (h1 : ∀ i, (ℓ (γ i) : ℝ) = N * φ.evalZ (γ i)) {c : Fin n → ℝ}
    (hc : ∀ i, 0 ≤ c i) {b : LinearMap.BilinForm ℤ Y} (hb : toReal b = ∑ i, c i • toReal (γ i)) :
    (ℓ b : ℝ) = N * φ.evalZ b := by
  have e1 : φ.evalZ b = ∑ i, c i * φ.evalZ (γ i) := by
    rw [← hl c hc]
    unfold InvFun.evalZ
    congr 1
    funext a a'
    have := LinearMap.congr_fun₂ hb a a'
    simpa [LinearMap.sum_apply] using this
  rw [intLin_eq_sum_of_toReal γ c b ℓ hb, e1, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [h1 i]; ring

theorem cell_of_quot_cell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ψ : InvFun (𝓞 E)) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], IsPolyFanOn H.bar ψ X → (∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell H.bar ψ γ → IsFaceCut γ s h → IsCell H.bar ψ (fun i => γ (s i))) → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∀ (m' : ℕ) (δ : Fin m' → LinearMap.BilinForm ℤ (X ⧸ (orad β : Submodule (𝓞 E) X))), IsCell H.bar ψ δ → InRCone (fun i => pull (orad β : Submodule (𝓞 E) X).mkQ (δ i)) β → ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧ InRCone γ β ∧ genRank γ ≤ genRank δ := by
  intro E _ _ _ H ψ X _ _ _ _ hfan hface β hβ hp m' δ hδ hin
  classical
  have : Module.Projective (𝓞 E) (X ⧸ (orad (O := 𝓞 E) β)) := projective_quot_orad E X β
  obtain ⟨t, ht⟩ := Module.projective_lifting_property (orad (O := 𝓞 E) β).mkQ LinearMap.id (orad (O := 𝓞 E) β).mkQ_surjective
  have htt : ∀ u, (orad (O := 𝓞 E) β).mkQ (t u) = u := fun u => LinearMap.congr_fun ht u
  have htt' : ∀ u, (Submodule.Quotient.mk (t u) : X ⧸ (orad (O := 𝓞 E) β)) = u := htt
  have hπ : Function.Surjective (orad (O := 𝓞 E) β).mkQ := (orad (O := 𝓞 E) β).mkQ_surjective

  have desc : ∀ β' : LinearMap.BilinForm ℤ X, β' ∈ balForms H.bar X → (∀ k ∈ (orad (O := 𝓞 E) β), ∀ y, β' k y = 0) →
      pull (orad (O := 𝓞 E) β).mkQ (pull t β') = β' := by
    intro β' hb hv
    refine LinearMap.ext₂ fun a b => ?_
    have ha : a - t ((orad (O := 𝓞 E) β).mkQ a) ∈ (orad (O := 𝓞 E) β) := by
      rw [← Submodule.Quotient.mk_eq_zero (orad (O := 𝓞 E) β), ← Submodule.mkQ_apply, map_sub, htt, sub_self]
    have hb' : b - t ((orad (O := 𝓞 E) β).mkQ b) ∈ (orad (O := 𝓞 E) β) := by
      rw [← Submodule.Quotient.mk_eq_zero (orad (O := 𝓞 E) β), ← Submodule.mkQ_apply, map_sub, htt, sub_self]
    have e1 := hv _ ha b
    have e2 := hv _ hb' (t ((orad (O := 𝓞 E) β).mkQ a))
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at e1 e2
    rw [pull_apply, pull_apply, hb.1 (t _) (t _), ← e2, hb.1 b (t ((orad (O := 𝓞 E) β).mkQ a)), ← e1]
  have hbK : ∀ k ∈ (orad (O := 𝓞 E) β), ∀ y, β k y = 0 := fun k hk y => by simpa using (mem_orad.1 hk) 1 y

  have hmem : toReal β ∈ psdCone H.bar X := by
    have := ConeSub.sum_smul_toReal_mem_psdCone (𝓞 E) H.bar X 1 ![β] ![1] (fun i => by fin_cases i; exact hβ)
      (fun i y => by fin_cases i; exact hp y) (fun i => by fin_cases i; norm_num)
    simpa using this
  obtain ⟨S, -, hS⟩ := hfan.finite
  obtain ⟨e, m, γ, d, hγ, -, hd, he⟩ := hS _ hmem
  set σ : Fin m → LinearMap.BilinForm ℤ X := fun i => pull e.symm.toLinearMap (γ i) with hσdef
  have hσ : IsCell H.bar ψ σ := isCell_pull_equiv hγ e.symm
  have hβσ : toReal β = ∑ i, d i • toReal (σ i) := LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ he (e.symm a) (e.symm b)
    simpa [LinearMap.sum_apply, hσdef] using this

  obtain ⟨Nδ, ℓδ, hNδ, hℓδ1, hℓδ2, hℓδ3⟩ := hδ.strict
  obtain ⟨Nσ, ℓσ, hNσ, hℓσ1, hℓσ2, hℓσ3⟩ := hσ.strict
  obtain ⟨hK, hKt⟩ := exists_radical_test H.bar (orad (O := 𝓞 E) β)
  let g : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := (Nσ : ℤ) • (ℓδ ∘ₗ pullLin t) - (Nδ : ℤ) • ℓσ
  have hg : ∀ β', g β' = Nσ * ℓδ (pull t β') - Nδ * ℓσ β' := fun β' => by simp [g]
  set M : ℤ := ∑ j, |g (σ j)| + 1 with hM
  have hMj : ∀ j, |g (σ j)| < M := fun j => by
    have := Finset.single_le_sum (f := fun j => |g (σ j)|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
    linarith
  let hh : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := g + M • hK
  have hhv : ∀ β', hh β' = g β' + M * hK β' := fun β' => by simp [hh]
  have factA : ∀ j, hK (σ j) = 0 →
      (g (σ j) : ℝ) = Nσ * ((ℓδ (pull t (σ j)) : ℝ) - Nδ * ψ.evalZ (pull t (σ j))) := by
    intro j hj
    have hv := (hKt _ (hσ.mem j) (hσ.nonneg j)).2.1 hj
    have e1 : ψ.evalZ (σ j) = ψ.evalZ (pull t (σ j)) := by
      rw [← evalZ_pull ψ hπ (pull t (σ j)), desc _ (hσ.mem j) hv]
    rw [hg]
    push_cast
    rw [hℓσ1 j, e1]
    ring
  have hpos : ∀ j, hK (σ j) ≠ 0 → 0 < hh (σ j) := by
    intro j hj
    rw [hhv]
    have h0 := (hKt _ (hσ.mem j) (hσ.nonneg j)).1
    have h1 : 1 ≤ hK (σ j) := by omega
    have h2 := hMj j
    have hM0 : 0 ≤ M := (abs_nonneg _).trans h2.le
    have h3 := mul_le_mul_of_nonneg_left h1 hM0
    have h4 := neg_abs_le (g (σ j))
    linarith
  have hnn : ∀ j, 0 ≤ hh (σ j) := by
    intro j
    by_cases hj : hK (σ j) = 0
    · rw [hhv, hj, mul_zero, add_zero]
      have hA := factA j hj
      have h2 := hℓδ2 (pull t (σ j)) (pull_mem t (hσ.mem j)) (fun y => hσ.nonneg j _)
      have h3 : (0 : ℝ) ≤ g (σ j) := by
        rw [hA]
        exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
      exact_mod_cast h3
    · exact (hpos j hj).le

  set F : Finset (Fin m) := Finset.univ.filter fun j => hh (σ j) = 0 with hF
  let s : Fin F.card ↪ Fin m := (F.orderEmbOfFin rfl).toEmbedding
  have hs : ∀ j, j ∈ Set.range s ↔ hh (σ j) = 0 := fun j => by
    have : Set.range s = (F : Set (Fin m)) := Finset.range_orderEmbOfFin F rfl
    rw [this]
    simp [hF]
  have hcut : IsFaceCut σ s hh := ⟨hnn, fun j => (hs j).symm⟩
  have hσs : IsCell H.bar ψ (fun i => σ (s i)) := hface m F.card σ s hh hσ hcut

  have hKb : hK β = 0 := (hKt β hβ hp).2.2 hbK
  have hψβ : ψ.evalZ β = ψ.evalZ (pull t β) := by
    rw [← evalZ_pull ψ hπ (pull t β), desc β hβ hbK]
  obtain ⟨c, hc, hcβ⟩ := hin
  have hcβ1 : toReal (pull t β) = ∑ i, c i • toReal (δ i) := LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ hcβ (t a) (t b)
    simpa [LinearMap.sum_apply, htt, htt'] using this
  have hgβ : g β = 0 := by
    have e1 := intLin_eq_of_inCone ψ hσ.linear hℓσ1 hd hβσ
    have e2 := intLin_eq_of_inCone ψ hδ.linear hℓδ1 hc hcβ1
    have : (g β : ℝ) = 0 := by
      rw [hg]
      push_cast
      rw [e1, e2, hψβ]
      ring
    exact_mod_cast this
  have hhβ : hh β = 0 := by rw [hhv, hgβ, hKb]; simp
  have hsum := intLin_eq_sum_of_toReal σ d β hh hβσ
  rw [hhβ, Int.cast_zero] at hsum
  have hzero : ∀ j, d j * (hh (σ j) : ℝ) = 0 := by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (hd j) (by exact_mod_cast hnn j))).1 hsum.symm
    exact fun j => this j (Finset.mem_univ j)
  have hdz : ∀ j, j ∉ Set.range s → d j = 0 := fun j hj => by
    have h0 : (hh (σ j) : ℝ) ≠ 0 := by exact_mod_cast fun h => hj ((hs j).2 h)
    exact (mul_eq_zero.1 (hzero j)).resolve_right h0
  have hcone : InRCone (fun i => σ (s i)) β := by
    refine ⟨fun i => d (s i), fun i => hd _, ?_⟩
    rw [hβσ]
    exact (Fintype.sum_of_injective s s.injective _ _ (fun j hj => by rw [hdz j hj, zero_smul]) fun i => rfl).symm

  have hspan : ∀ i, ∃ k : ℕ, 0 < k ∧ k • σ (s i) ∈ Submodule.span ℤ (Set.range fun i => pull (orad (O := 𝓞 E) β).mkQ (δ i)) := by
    intro i
    have hj0 : hh (σ (s i)) = 0 := (hs (s i)).1 ⟨i, rfl⟩
    have hKj : hK (σ (s i)) = 0 := by
      by_contra hne
      exact (hpos _ hne).ne' hj0
    have hgj : g (σ (s i)) = 0 := by
      rw [hhv, hKj, mul_zero, add_zero] at hj0
      exact hj0
    have hA := factA _ hKj
    rw [hgj, Int.cast_zero] at hA
    have heq : (Nδ : ℝ) * ψ.evalZ (pull t (σ (s i))) = ℓδ (pull t (σ (s i))) := by
      have hN : (Nσ : ℝ) ≠ 0 := by exact_mod_cast hNσ.ne'
      have := (mul_eq_zero.1 hA.symm).resolve_left hN
      linarith
    obtain ⟨k, c', hk, hkc⟩ := hℓδ3 _ (pull_mem t (hσ.mem (s i))) (fun y => hσ.nonneg (s i) _) heq
    refine ⟨k, hk, ?_⟩
    have hv := (hKt _ (hσ.mem (s i)) (hσ.nonneg (s i))).2.1 hKj
    have e3 : k • σ (s i) = ∑ l, c' l • pull (orad (O := 𝓞 E) β).mkQ (δ l) := by
      have e := congrArg (pullLin (orad (O := 𝓞 E) β).mkQ) hkc
      simp only [map_nsmul, map_sum, pullLin_apply] at e
      rw [desc _ (hσ.mem (s i)) hv] at e
      exact e
    rw [e3]
    exact Submodule.sum_mem _ fun l _ => nsmul_mem (Submodule.subset_span (Set.mem_range_self l)) _
  refine ⟨F.card, fun i => σ (s i), hσs, hcone, ?_⟩
  calc genRank (fun i => σ (s i)) ≤ genRank (fun i => pull (orad (O := 𝓞 E) β).mkQ (δ i)) :=
        genRank_le_of_smul_mem_span _ _ hspan
    _ = genRank δ := genRank_pull hπ δ

end GlobalTheory.PolFan.CarDim
