import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMulVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClopenCoset
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZpowMulVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeVolumeScalingLawsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingLatticeRefinementCardStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenStandardLatticeStabilizerStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalOrbitGLNearOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MaximumPrincipleLatticeFunctionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzFunctionLatticeIndicatorSumStatement
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.BZCore

theorem exists_gl_mulVec_eq {k : Type} [Field k] {d : ℕ} (e x : Fin d → k) (he : e ≠ 0) (hx : x ≠ 0) :
    ∃ g : GL (Fin d) k, (g : Matrix (Fin d) (Fin d) k).mulVec e = x := by
  obtain ⟨u, hu⟩ := Submodule.exists_linearEquiv_restrict_eq
    ((LinearEquiv.toSpanNonzeroSingleton k (Fin d → k) e he).symm.trans
      (LinearEquiv.toSpanNonzeroSingleton k (Fin d → k) x hx))
  have h1 := hu ⟨e, Submodule.mem_span_singleton_self e⟩
  rw [← LinearEquiv.toSpanNonzeroSingleton_one k (Fin d → k) e he, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, LinearEquiv.toSpanNonzeroSingleton_one,
    LinearEquiv.toSpanNonzeroSingleton_one] at h1
  have hAB : LinearMap.toMatrix' u.toLinearMap * LinearMap.toMatrix' u.symm.toLinearMap = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    simp
  have hBA : LinearMap.toMatrix' u.symm.toLinearMap * LinearMap.toMatrix' u.toLinearMap = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    simp
  refine ⟨⟨LinearMap.toMatrix' u.toLinearMap, LinearMap.toMatrix' u.symm.toLinearMap, hAB, hBA⟩, ?_⟩
  show (LinearMap.toMatrix' u.toLinearMap).mulVec e = x
  rw [LinearMap.toMatrix'_mulVec]
  exact h1.symm

theorem exists_bilin_eventual {V V' ι : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (l : Filter ι) [l.NeBot] (G : V → V' → ι → ℂ)
    (h1 : ∀ a b a' i, G (a + b) a' i = G a a' i + G b a' i)
    (h2 : ∀ a a' b' i, G a (a' + b') i = G a a' i + G a b' i)
    (h3 : ∀ (t : ℂ) a a' i, G (t • a) a' i = t * G a a' i)
    (h4 : ∀ (t : ℂ) a a' i, G a (t • a') i = t * G a a' i)
    (H : ∀ a a', ∃ v : ℂ, ∀ᶠ i in l, G a a' i = v) :
    ∃ β : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ, ∀ a a', ∀ᶠ i in l, G a a' i = β a a' := by
  choose v hv using H
  have f1 : ∀ a b a', v (a + b) a' = v a a' + v b a' := by
    intro a b a'
    obtain ⟨i, e1, e2, e3⟩ := ((hv (a + b) a').and ((hv a a').and (hv b a'))).exists
    rw [← e1, ← e2, ← e3, h1]
  have f2 : ∀ (t : ℂ) a a', v (t • a) a' = t • v a a' := by
    intro t a a'
    obtain ⟨i, e1, e2⟩ := ((hv (t • a) a').and (hv a a')).exists
    rw [← e1, ← e2, h3, smul_eq_mul]
  have f3 : ∀ a a' b', v a (a' + b') = v a a' + v a b' := by
    intro a a' b'
    obtain ⟨i, e1, e2, e3⟩ := ((hv a (a' + b')).and ((hv a a').and (hv a b'))).exists
    rw [← e1, ← e2, ← e3, h2]
  have f4 : ∀ (t : ℂ) a a', v a (t • a') = t • v a a' := by
    intro t a a'
    obtain ⟨i, e1, e2⟩ := ((hv a (t • a')).and (hv a a')).exists
    rw [← e1, ← e2, h4, smul_eq_mul]
  exact ⟨LinearMap.mk₂ ℂ v f1 f2 f3 f4, fun a a' => hv a a'⟩

theorem refines_const_on_coset {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {d : ℕ} (z : GL (Fin d) k) (ϖ : k) (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (F : COSub k d → (Fin d → k) → ℂ) (hF : Refines F)
    (s₀ : ℕ) (x : Fin d → k)
    (H : ∀ (r : ℕ) (y : Fin d → k), y - x ∈ (latZ z (s₀ : ℤ)).sub → F (latZ z (r : ℤ)) y = F (latZ z (r : ℤ)) x)
    (y : Fin d → k) (hy : y - x ∈ (latZ z (s₀ : ℤ)).sub) (L : COSub k d) (hL : L.sub ≤ (latZ z (s₀ : ℤ)).sub) :
    F L y = F (latZ z (s₀ : ℤ)) x := by
  classical
  obtain ⟨r, hr⟩ := latZ_basis z ϖ hz hϖ hϖ0 L
  have key : ∀ (M : COSub k d), (latZ z (r : ℤ)).sub ≤ M.sub → M.sub ≤ (latZ z (s₀ : ℤ)).sub →
      ∀ w : Fin d → k, w - x ∈ (latZ z (s₀ : ℤ)).sub → F M w = F (latZ z (r : ℤ)) x := by
    intro M hM hM' w hw
    obtain ⟨S, hS⟩ := exists_reps _ M hM
    have hcard : (S.card : ℂ) ≠ 0 := by
      obtain ⟨s, hs, -⟩ := hS.2 0 M.sub.zero_mem
      exact_mod_cast (Finset.card_pos.2 ⟨s, hs.1⟩).ne'
    have h1 := hF _ M S hM hS w
    have h2 : ∑ s ∈ S, F (latZ z (r : ℤ)) (w + s) = ∑ _s ∈ S, F (latZ z (r : ℤ)) x := by
      refine Finset.sum_congr rfl fun s hs => H r (w + s) ?_
      have e : w + s - x = (w - x) + s := by abel
      rw [e]
      exact AddSubgroup.add_mem _ hw (hM' (hS.1 s hs))
    rw [h2, Finset.sum_const, nsmul_eq_mul] at h1
    exact mul_left_cancel₀ hcard h1
  rw [key L hr hL y hy, key _ (hr.trans hL) le_rfl x (by rw [sub_self]; exact AddSubgroup.zero_mem _)]

theorem shift_invariant_of_exact_twist : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d : ℕ) (hd : 0 < d) {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (X : Representation ℂ (GL (Fin d) k) V) (Y : Representation ℂ (GL (Fin d) k) V') (hX : IsSmooth X) (hY : IsSmooth Y)
    (P : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ)
    (hP : ∀ g a a', P (X g a) (Y g a') = ((dpow d (-2) g : ℂˣ) : ℂ) * P a a')
    (e : Fin d → k) (he : e ≠ 0)
    (hU : ∀ β : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ,
      (∀ g : GL (Fin d) k, (g : Matrix (Fin d) (Fin d) k).mulVec e = e → ∀ a a', β (X g a) (Y g a') =
        ((dpow d (-2) g : ℂˣ) : ℂ) * β a a') → ∃ c : ℂ, ∀ a a', β a a' = c * P a a')
    (z : GL (Fin d) k) (ϖ : k) (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (ω ω' : ℂ) (hω : ∀ a, X z a = ω • a) (hω' : ∀ a, Y z a = ω' • a)
    (hωω : ω * ω' = ((dpow d (-2) z : ℂˣ) : ℂ))
    (B : SchF k d V →ₗ[ℂ] SchF k d V' →ₗ[ℂ] ℂ)
    (hT : ∀ x f f', B (shiftF x f) (shiftF x f') = B f f')
    (hG : ∀ g f f', B (actF X g f) (actF Y g f') = B f f'),
    ∀ f f' x, B f (shiftF x f') = B f f' := by
  intro k _ _ _ _ d hd V V' _ _ _ _ X Y hX hY P hP e he hU z ϖ hz hϖ hϖ0 ω ω' hω hω' hωω B hT hG
  obtain ⟨vol, hv0, hvR, hvG⟩ := GlobalTheory.T.lattice_volume_scaling_laws (k := k) d
  have hvC : ∀ L, ((vol L : ℝ) : ℂ) ≠ 0 := fun L => by exact_mod_cast (hv0 L).ne'

  let F : V → V' → COSub k d → (Fin d → k) → ℂ := fun a a' L x => mL B L x a a' / ((vol L : ℝ) : ℂ) ^ 2
  have hFdef : ∀ a a' L x, F a a' L x = mL B L x a a' / ((vol L : ℝ) : ℂ) ^ 2 := fun _ _ _ _ => rfl
  have hRef : ∀ a a', Refines (F a a') := by
    intro a a' L' L S h hS x
    have hcard : (S.card : ℂ) ≠ 0 := by
      obtain ⟨s, hs, -⟩ := hS.2 0 L.sub.zero_mem
      exact_mod_cast (Finset.card_pos.2 ⟨s, hs.1⟩).ne'
    have hv : ((vol L : ℝ) : ℂ) = (S.card : ℂ) * ((vol L' : ℝ) : ℂ) := by
      rw [hvR L' L S h hS]; push_cast; rfl
    simp only [hFdef]
    rw [GlobalTheory.T.pairing_lattice_refinement_card B hT L' L S h hS x a a', hv, ← Finset.sum_div]
    have := hvC L'
    field_simp
  have hPer : ∀ a a' (L : COSub k d) (x l : Fin d → k), l ∈ L.sub → F a a' L (x + l) = F a a' L x := by
    intro a a' L x l hl
    simp only [hFdef, mL_add_mem B L x hl]
  have hAct : ∀ (g : GL (Fin d) k) a a' (L : COSub k d) (x : Fin d → k),
      F (X g a) (Y g a') (L.act g) ((g : Matrix (Fin d) (Fin d) k).mulVec x) =
        ((dpow d (-2) g : ℂˣ) : ℂ) * F a a' L x := by
    intro g a a' L x
    simp only [hFdef]
    rw [mL_act X Y B hG, ← hvG g L]
    have h1 := hvC (L.act g)
    have h2 := (dpow d (-2) g : ℂˣ).ne_zero
    field_simp
  have hScale : ∀ a a' (L : COSub k d) (x : Fin d → k),
      F a a' (L.act z) ((z : Matrix (Fin d) (Fin d) k).mulVec x) = F a a' L x := by
    intro a a' L x
    have h := hAct z a a' L x
    rw [hω, hω', ← hωω] at h
    have h0 : ω * ω' ≠ 0 := by rw [hωω]; exact (dpow d (-2) z : ℂˣ).ne_zero
    simp only [hFdef, mL_smul_left, mL_smul_right] at h ⊢
    apply mul_left_cancel₀ h0
    rw [← h]
    ring
  have hComm : ∀ (g : GL (Fin d) k) (r : ℤ), g * z ^ r = z ^ r * g := by
    intro g r
    have : Commute g z := by
      apply Units.ext
      show (g : Matrix (Fin d) (Fin d) k) * (z : Matrix (Fin d) (Fin d) k) = (z : Matrix (Fin d) (Fin d) k) * g
      rw [hz]
      simp
    exact (this.zpow_right r).eq
  have hLat : ∀ (g : GL (Fin d) k), (lat0 : COSub k d).act g = lat0 → ∀ r : ℤ, (latZ z r).act g = latZ z r := by
    intro g hg r
    rw [latZ, COSub.act_act, hComm, ← COSub.act_act, hg]

  have hLoc : ∀ a a' (x : Fin d → k), x ≠ 0 → ∃ s : ℕ, ∀ y : Fin d → k, y - x ∈ (latZ z (s : ℤ)).sub →
      ∀ L : COSub k d, L.sub ≤ (latZ z (s : ℤ)).sub → F a a' L y = F a a' (latZ z (s : ℤ)) x := by
    intro a a' x hx
    have hU1 : {g : GL (Fin d) k | (lat0 : COSub k d).act g = lat0} ∩ ({g | X g a = a} ∩ {g | Y g a' = a'}) ∈
        𝓝 (1 : GL (Fin d) k) := by
      refine ((GlobalTheory.T.isOpen_standard_lattice_stabilizer (k := k) (d := d)).inter ((hX a).inter (hY a'))).mem_nhds ?_
      exact ⟨COSub.act_one _, by simp, by simp⟩
    obtain ⟨s, hs⟩ := GlobalTheory.T.local_orbit_GL_near_one z ϖ hz hϖ hϖ0 _ hU1 x hx
    refine ⟨s, refines_const_on_coset z ϖ hz hϖ hϖ0 (F a a') (hRef a a') s x fun r y hy => ?_⟩
    obtain ⟨g, ⟨hg, hga, hga'⟩, rfl⟩ := hs y hy
    have hd1 : ((dpow d (-2) g : ℂˣ) : ℂ) = 1 := by
      have h := hvG g lat0
      rw [hg] at h
      have h1 := hvC lat0
      exact mul_left_cancel₀ (pow_ne_zero 2 h1) (by rw [h, mul_one])
    have h := hAct g a a' (latZ z (r : ℤ)) x
    rw [hga, hga', hLat g hg, hd1, one_mul] at h
    exact h
  have hβ : ∀ x : Fin d → k, x ≠ 0 → ∃ β : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ, ∀ a a', ∃ s : ℕ, ∀ y : Fin d → k,
      y - x ∈ (latZ z (s : ℤ)).sub → ∀ L : COSub k d, L.sub ≤ (latZ z (s : ℤ)).sub → F a a' L y = β a a' := by
    intro x hx
    obtain ⟨β, hb⟩ := exists_bilin_eventual (Filter.atTop : Filter ℕ) (fun a a' r => F a a' (latZ z (r : ℤ)) x)
      (fun a b a' r => by simp only [hFdef, mL_add_left, add_div])
      (fun a a' b' r => by simp only [hFdef, mL_add_right, add_div])
      (fun t a a' r => by simp only [hFdef, mL_smul_left, mul_div_assoc])
      (fun t a a' r => by simp only [hFdef, mL_smul_right, mul_div_assoc])
      (fun a a' => by
        obtain ⟨s, hs⟩ := hLoc a a' x hx
        refine ⟨F a a' (latZ z (s : ℤ)) x, Filter.eventually_atTop.2 ⟨s, fun r hr => ?_⟩⟩
        exact hs x (by simp) _ (latZ_anti z ϖ hz hϖ hϖ0 _ _ (by exact_mod_cast hr)))
    refine ⟨β, fun a a' => ?_⟩
    obtain ⟨s, hs⟩ := hLoc a a' x hx
    obtain ⟨r, hr⟩ := Filter.eventually_atTop.1 (hb a a')
    refine ⟨s, fun y hy L hL => ?_⟩
    rw [hs y hy L hL, ← hr (max r s) (le_max_left _ _)]
    exact (hs x (by simp) _ (latZ_anti z ϖ hz hϖ hϖ0 _ _ (by exact_mod_cast le_max_right r s))).symm
  choose! β hβ using hβ
  have hEq : ∀ (g : GL (Fin d) k) (x : Fin d → k), x ≠ 0 → ∀ a a',
      β ((g : Matrix (Fin d) (Fin d) k).mulVec x) (X g a) (Y g a') = ((dpow d (-2) g : ℂˣ) : ℂ) * β x a a' := by
    intro g x hx a a'
    have hgx : (g : Matrix (Fin d) (Fin d) k).mulVec x ≠ 0 := by
      intro h0
      apply hx
      have := congrArg (fun y => ((g⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y) h0
      simpa [mulVec_mulVec, ← Units.val_mul] using this
    obtain ⟨s₁, h₁⟩ := hβ x hx a a'
    obtain ⟨s₂, h₂⟩ := hβ _ hgx (X g a) (Y g a')
    obtain ⟨r, hr⟩ := latZ_basis z ϖ hz hϖ hϖ0 ((latZ z (s₂ : ℤ)).act g⁻¹)
    let t : ℕ := max r s₁
    have ht₁ : (latZ z (t : ℤ)).sub ≤ (latZ z (s₁ : ℤ)).sub :=
      latZ_anti z ϖ hz hϖ hϖ0 _ _ (by exact_mod_cast le_max_right r s₁)
    have ht₂ : ((latZ z (t : ℤ)).act g).sub ≤ (latZ z (s₂ : ℤ)).sub := by
      have ht : (latZ z (t : ℤ)).sub ≤ (latZ z (r : ℤ)).sub :=
        latZ_anti z ϖ hz hϖ hϖ0 _ _ (by exact_mod_cast le_max_left r s₁)
      have h := COSub.act_mono (ht.trans hr) g
      rwa [COSub.act_act, mul_inv_cancel, COSub.act_one] at h
    rw [← h₂ ((g : Matrix (Fin d) (Fin d) k).mulVec x) (by rw [sub_self]; exact AddSubgroup.zero_mem _) _ ht₂, hAct,
      h₁ x (by rw [sub_self]; exact AddSubgroup.zero_mem _) _ ht₁]
  obtain ⟨c₀, hc₀⟩ := hU (β e) (fun g hg a a' => by
    have := hEq g e he a a'
    rwa [hg] at this)
  have hβc : ∀ x : Fin d → k, x ≠ 0 → ∀ a a', β x a a' = c₀ * P a a' := by
    intro x hx a a'
    obtain ⟨g, rfl⟩ := exists_gl_mulVec_eq e x he hx
    have h := hEq g e he (X g⁻¹ a) (Y g⁻¹ a')
    have e1 : ∀ b, X g (X g⁻¹ b) = b := fun b => by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have e2 : ∀ b, Y g (Y g⁻¹ b) = b := fun b => by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [e1, e2, hc₀, hP] at h
    rw [h]
    have h3 : ((dpow d (-2) g : ℂˣ) : ℂ) * ((dpow d (-2) g⁻¹ : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    calc _ = (((dpow d (-2) g : ℂˣ) : ℂ) * ((dpow d (-2) g⁻¹ : ℂˣ) : ℂ)) * (c₀ * P a a') := by ring
      _ = _ := by rw [h3, one_mul]
  have hAll : ∀ (r : ℕ) (x : Fin d → k) a a', mL B (latZ z (r : ℤ)) x a a' =
      c₀ * P a a' * ((vol (latZ z (r : ℤ)) : ℝ) : ℂ) ^ 2 := by
    intro r x a a'
    have h := GlobalTheory.T.maximum_principle_lattice_functions hd z ϖ hz hϖ hϖ0 (F a a') (c₀ * P a a') (hRef a a') (hPer a a') (hScale a a')
      (fun x hx => by
        obtain ⟨s, hs⟩ := hβ x hx a a'
        refine ⟨s, fun y hy r hr => ?_⟩
        rw [hs y hy _ (latZ_anti z ϖ hz hϖ hϖ0 _ _ (by exact_mod_cast hr)), hβc x hx]) r x
    rw [hFdef, div_eq_iff (pow_ne_zero 2 (hvC _))] at h
    exact h
  intro f f' x
  obtain ⟨r₁, h₁⟩ := GlobalTheory.T.schwartz_function_lattice_indicator_sum z ϖ hz hϖ hϖ0 f
  obtain ⟨r₂, h₂⟩ := GlobalTheory.T.schwartz_function_lattice_indicator_sum z ϖ hz hϖ hϖ0 f'
  obtain ⟨I, hI⟩ := h₁ (max r₁ r₂) (le_max_left _ _)
  obtain ⟨I', hI'⟩ := h₂ (max r₁ r₂) (le_max_right _ _)
  rw [hI, hI']
  simp only [map_sum, LinearMap.sum_apply, shiftF_ind, B_ind_ind B hT, hAll]

end GlobalTheory.CompanionTheory.BZCore

end
