import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCellQuotientByRadicalOfMemCone
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullLinInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.QuotientCellRadical

theorem exists_cell_quot_orad_of_inRCone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (ψ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X], (∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell bar ψ γ → IsFaceCut γ s h → IsCell bar ψ (fun i => γ (s i))) → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → InRCone γ β → ∃ (m' : ℕ) (δ : Fin m' → LinearMap.BilinForm ℤ (X ⧸ (orad β : Submodule O X))), IsCell bar ψ δ ∧ InRCone (fun i => pull (orad β : Submodule O X).mkQ (δ i)) β ∧ genRank δ ≤ genRank γ := by
  intro O _ _ _ _ bar _hCM ψ X _ _ _ hface β _hβ _hβpsd m γ hcell hcone
  classical
  have mem_bal : ∀ {Y : Type} [AddCommGroup Y] [Module O Y] (f : LinearMap.BilinForm ℤ Y),
      f ∈ GlobalTheory.PolFan.balForms bar Y ↔
        ((∀ y z, f y z = f z y) ∧ ∀ (a : O) (y z : Y), f (a • y) z = f y (bar a • z)) :=
    fun _ => Iff.rfl
  have psd_zero : ∀ f : LinearMap.BilinForm ℤ X, f ∈ GlobalTheory.PolFan.balForms bar X →
      (∀ y, 0 ≤ f y y) → ∀ x, f x x = 0 → ∀ y, f x y = 0 := by
    intro f hf hfp x hx y
    have hsym : f y x = f x y := ((mem_bal f).1 hf).1 y x
    by_contra hne
    have expand : ∀ n : ℤ, f (n • x + y) (n • x + y) =
        n * n * f x x + n * f x y + n * f y x + f y y := by
      intro n
      simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      ring
    have key := hfp ((-(f y y + 1) * f x y) • x + y)
    rw [expand, hx, hsym] at key
    have h1 : 0 < f x y * f x y := mul_self_pos.2 hne
    have h2 : 1 ≤ f x y * f x y := by simpa using Int.add_one_le_iff.2 h1
    have h0 := hfp y
    nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ f y y + 1) (by linarith : (0:ℤ) ≤ f x y * f x y - 1)]
  obtain ⟨c, hc0, hcsum⟩ := hcone
  have hval : ∀ x y, ((β x y : ℤ) : ℝ) = ∑ i, c i * ((γ i x y : ℤ) : ℝ) := by
    intro x y
    have := congrArg (fun L : X →ₗ[ℤ] X →ₗ[ℤ] ℝ => L x y) hcsum
    simpa [GlobalTheory.PolFan.toReal] using this
  set K : Submodule O X := GlobalTheory.PolFan.CarDim.orad β with hK
  have hKβ : ∀ x ∈ K, β x x = 0 := by
    intro x hx
    have := (GlobalTheory.PolFan.CarDim.mem_orad (O := O)).1 hx 1 x
    simpa using this
  let P : Fin m → Prop := fun j => ∀ x ∈ K, ∀ y, γ j x y = 0
  have hpos : ∀ j, 0 < c j → P j := by
    intro j hcj x hx
    apply psd_zero (γ j) (hcell.mem j) (hcell.nonneg j) x
    have hsum : ∑ i, c i * ((γ i x x : ℤ) : ℝ) = 0 := by
      rw [← hval, hKβ x hx]
      simp
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ c i * ((γ i x x : ℤ) : ℝ) := fun i _ =>
      mul_nonneg (hc0 i) (by exact_mod_cast hcell.nonneg i x)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum j (Finset.mem_univ j)
    rcases mul_eq_zero.1 hz with h | h
    · exact absurd h hcj.ne'
    · exact_mod_cast h
  have hw : ∀ j, ∃ x ∈ K, (¬ P j → 0 < γ j x x) := by
    intro j
    by_cases hj : P j
    · exact ⟨0, K.zero_mem, fun h => absurd hj h⟩
    · simp only [P, not_forall] at hj
      obtain ⟨x, hx, y, hxy⟩ := hj
      refine ⟨x, hx, fun _ => ?_⟩
      rcases (hcell.nonneg j x).lt_or_eq with h | h
      · exact h
      · exact absurd (psd_zero (γ j) (hcell.mem j) (hcell.nonneg j) x h.symm y) hxy
  choose w hwK hwpos using hw
  let h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ :=
    { toFun := fun f => ∑ j, f (w j) (w j)
      map_add' := fun f g => by simp [Finset.sum_add_distrib]
      map_smul' := fun a f => by simp [Finset.mul_sum] }
  have hh : ∀ f, h f = ∑ j, f (w j) (w j) := fun _ => rfl
  let T : Finset (Fin m) := Finset.univ.filter P
  let s : Fin T.card ↪ Fin m := (T.orderEmbOfFin rfl).toEmbedding
  have hsT : ∀ j, j ∈ Set.range s ↔ P j := by
    intro j
    have hr : Set.range s = (T : Set (Fin m)) := Finset.range_orderEmbOfFin T rfl
    rw [hr]
    simp [T]
  have hPs : ∀ i, P (s i) := fun i => (hsT (s i)).1 ⟨i, rfl⟩
  have hfc : GlobalTheory.PolFan.IsFaceCut γ s h := by
    refine ⟨fun j => ?_, fun j => ?_⟩
    · rw [hh]
      exact Finset.sum_nonneg fun i _ => hcell.nonneg j (w i)
    · rw [hsT, hh]
      constructor
      · intro h0
        by_contra hj
        have hnn : ∀ i ∈ Finset.univ, 0 ≤ γ j (w i) (w i) := fun i _ => hcell.nonneg j (w i)
        have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 j (Finset.mem_univ j)
        exact (hwpos j hj).ne' this
      · intro hj
        exact Finset.sum_eq_zero fun i _ => hj (w i) (hwK i) (w i)
  have hcell' := hface m T.card γ s h hcell hfc
  have hvanl : ∀ i, ∀ x ∈ K, ∀ y, γ (s i) x y = 0 := fun i => hPs i
  have hvanr : ∀ i, ∀ x y, y ∈ K → γ (s i) x y = 0 := by
    intro i x y hy
    rw [((mem_bal _).1 (hcell.mem (s i))).1 x y]
    exact hPs i y hy x
  choose δ hδ using fun i =>
    GlobalTheory.PolFan.CarDim.exists_pull_mkQ_eq_of_vanish K (γ (s i)) (hvanl i) (hvanr i)
  have hr : Function.Surjective K.mkQ := K.mkQ_surjective
  have hδap : ∀ i x y, δ i (K.mkQ x) (K.mkQ y) = γ (s i) x y := by
    intro i x y
    rw [← hδ i]
    rfl
  have heZ : ∀ f : LinearMap.BilinForm ℤ (X ⧸ K),
      ψ.evalZ (GlobalTheory.PolFan.pull K.mkQ f) = ψ.evalZ f := by
    intro f
    exact ψ.eval_comp hr (fun a b => ((f a b : ℤ) : ℝ))
  have hpullbal : ∀ f ∈ GlobalTheory.PolFan.balForms bar (X ⧸ K),
      GlobalTheory.PolFan.pull K.mkQ f ∈ GlobalTheory.PolFan.balForms bar X := by
    intro f hf
    obtain ⟨hs, hb⟩ := (mem_bal f).1 hf
    refine (mem_bal _).2 ⟨fun y z => hs (K.mkQ y) (K.mkQ z), fun a y z => ?_⟩
    show f (K.mkQ (a • y)) (K.mkQ z) = f (K.mkQ y) (K.mkQ (bar a • z))
    rw [LinearMap.map_smul, LinearMap.map_smul]
    exact hb a (K.mkQ y) (K.mkQ z)
  have hpullpsd : ∀ f : LinearMap.BilinForm ℤ (X ⧸ K), (∀ q, 0 ≤ f q q) →
      ∀ y, 0 ≤ GlobalTheory.PolFan.pull K.mkQ f y y :=
    fun f hf y => hf (K.mkQ y)
  have hfun : (fun i => GlobalTheory.PolFan.pull K.mkQ (δ i)) = fun i => γ (s i) := funext hδ
  refine ⟨T.card, δ, ?_, ?_, ?_⟩
  · refine ⟨fun i => ?_, fun i q => ?_, ?_, ?_⟩
    · refine (mem_bal _).2 ⟨fun a b => ?_, fun a u v => ?_⟩
      · obtain ⟨x, rfl⟩ := hr a
        obtain ⟨y, rfl⟩ := hr b
        rw [hδap, hδap]
        exact ((mem_bal _).1 (hcell.mem (s i))).1 x y
      · obtain ⟨x, rfl⟩ := hr u
        obtain ⟨y, rfl⟩ := hr v
        rw [← LinearMap.map_smul, ← LinearMap.map_smul, hδap, hδap]
        exact ((mem_bal _).1 (hcell.mem (s i))).2 a x y
    · obtain ⟨y, rfl⟩ := hr q
      rw [hδap]
      exact hcell.nonneg (s i) y
    · intro c hc
      have key := hcell'.linear.eval_eq_sum (X₁ := X ⧸ K) hr
        (B := fun a b => ∑ i, c i * ((δ i a b : ℤ) : ℝ)) hc (fun a b => by simp only [hδap])
      rw [key]
      refine Finset.sum_congr rfl fun i _ => ?_
      show c i * ψ.evalZ (γ (s i)) = c i * ψ.evalZ (δ i)
      rw [← hδ i, heZ]
    · obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hcell'.strict
      refine ⟨N, ℓ.comp (GlobalTheory.PolFan.CarDim.pullLin K.mkQ), hN, fun i => ?_,
        fun β' hb hp => ?_, fun β' hb hp heq => ?_⟩
      · have h1i : ((ℓ (γ (s i)) : ℤ) : ℝ) = (N : ℝ) * ψ.evalZ (γ (s i)) := h1 i
        rw [LinearMap.comp_apply, GlobalTheory.PolFan.CarDim.pullLin_apply, hδ i, h1i, ← hδ i, heZ]
      · rw [LinearMap.comp_apply, GlobalTheory.PolFan.CarDim.pullLin_apply, ← heZ]
        exact h2 _ (hpullbal β' hb) (hpullpsd β' hp)
      · rw [LinearMap.comp_apply, GlobalTheory.PolFan.CarDim.pullLin_apply, ← heZ] at heq
        obtain ⟨k, c', hk, hkc⟩ := h3 _ (hpullbal β' hb) (hpullpsd β' hp) heq
        refine ⟨k, c', hk, ?_⟩
        have hkc' : k • GlobalTheory.PolFan.pull K.mkQ β' = ∑ i, c' i • γ (s i) := hkc
        apply GlobalTheory.PolFan.CarDim.pullLin_injective hr
        simp only [map_nsmul, map_zsmul, LinearMap.map_smul_of_tower, map_sum,
          GlobalTheory.PolFan.CarDim.pullLin_apply]
        rw [hkc']
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hδ i]
  · rw [hfun]
    simp only [GlobalTheory.PolFan.InRCone]
    refine ⟨fun i => c (s i), fun i => hc0 _, ?_⟩
    rw [hcsum]
    have hmap : Finset.univ.map s = T := Finset.map_orderEmbOfFin_univ T rfl
    have e1 : (∑ i, c (s i) • GlobalTheory.PolFan.toReal (γ (s i))) =
        ∑ j ∈ T, c j • GlobalTheory.PolFan.toReal (γ j) := by
      exact (Finset.sum_map Finset.univ s (fun j => c j • GlobalTheory.PolFan.toReal (γ j))).symm.trans
        (by rw [hmap])
    rw [e1]
    symm
    apply Finset.sum_filter_of_ne
    intro j _ hne
    by_contra hj
    apply hne
    have hcj : c j = 0 := by
      rcases (hc0 j).lt_or_eq with h' | h'
      · exact absurd (hpos j h') hj
      · exact h'.symm
    rw [hcj, zero_smul]
  · rw [← GlobalTheory.PolFan.CarDim.genRank_pull hr δ, hfun]
    unfold GlobalTheory.PolFan.genRank
    haveI : Module.Finite ℤ (Submodule.span ℤ (Set.range γ)) :=
      Module.Finite.span_of_finite ℤ (Set.finite_range γ)
    exact Submodule.finrank_mono
      (Submodule.span_mono (Set.range_comp_subset_range s γ))

end GlobalTheory.CompanionTheory.Ar.Fan.QuotientCellRadical
