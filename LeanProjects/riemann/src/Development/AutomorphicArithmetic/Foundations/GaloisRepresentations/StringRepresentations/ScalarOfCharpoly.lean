import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.WeightsConj
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilRepEquivOfCharpolyEq

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial Module
open GlobalTheory GlobalTheory.WeilDeligne

namespace UpperTheory.GalN

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem scalar_of_charpoly {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] {f : End ℂ V}
    (hf : f.IsSemisimple) {c : ℂ} {t : ℕ} (e : f.charpoly = (X - C c) ^ t) (v : V) : f v = c • v := by
  have h1 : IsNilpotent (f - algebraMap ℂ (End ℂ V) c) := ⟨t, by
    have := LinearMap.aeval_self_charpoly f
    rw [e] at this
    simpa using this⟩
  have h2 : (f - algebraMap ℂ (End ℂ V) c).IsSemisimple := End.isSemisimple_sub_algebraMap_iff.2 hf
  have h3 := sub_eq_zero.1 (End.eq_zero_of_isNilpotent_isSemisimple h1 h2)
  rw [h3]; rfl

theorem exists_sum {W Va Vb : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    [AddCommGroup Va] [Module ℂ Va] [FiniteDimensional ℂ Va] [AddCommGroup Vb] [Module ℂ Vb] [FiniteDimensional ℂ Vb]
    (x : WDRep h W) (a : WDRep h Va) (b : WDRep h Vb) (g : W ≃ₗ[ℂ] Va × Vb)
    (hg : ∀ σ v, g (x.ρ σ v) = (a.sum b).ρ σ (g v)) (hb : b.N = 0) (γ : Weil h) (hγ : deg γ = 0) (c : ℂ)
    (hbγ : ∀ v, b.ρ γ v = c • v) (haγ : ∀ v, a.ρ γ v = c • v → v = 0) (h0 : ∀ v, x.N (g.symm (0, v)) = 0) :
    ∃ a' : WDRep h Va, WD.mk x = WD.mk (a'.sum b) := by
  let M : End ℂ (Va × Vb) := g.conj x.N
  have hM : ∀ v, M (g v) = g (x.N v) := fun v => by simp [M, LinearEquiv.conj_apply]
  have hc : ∀ σ z, (a.sum b).ρ σ (M z) = ((normV w : ℕ) : ℂ) ^ deg σ • M ((a.sum b).ρ σ z) := fun σ z => by
    obtain ⟨v, rfl⟩ := g.surjective z
    have := LinearMap.congr_fun (x.comm σ) v
    simp only [End.mul_apply, LinearMap.smul_apply] at this
    rw [hM, ← hg, ← hg, hM, this, map_smul]
  have hs : Function.Surjective (a.ρ γ - c • (1 : End ℂ Va)) := by
    rw [← LinearMap.injective_iff_surjective, injective_iff_map_eq_zero]
    intro v hv
    exact haγ v (by simpa [sub_eq_zero] using hv)
  have h1 : ∀ v, M (0, v) = 0 := fun v => by
    rw [← g.apply_symm_apply (0, v), hM, h0, map_zero]
  have h2 : ∀ v, (M (v, 0)).2 = 0 := fun v => by
    obtain ⟨u, rfl⟩ := hs v
    have e : (((a.ρ γ - c • (1 : End ℂ Va)) u, 0) : Va × Vb) = (a.sum b).ρ γ (u, 0) - c • (u, 0) := by simp
    have k := hc γ (u, 0)
    rw [hγ, zpow_zero, one_smul] at k
    rw [e, map_sub, map_smul, ← k]
    simp [hbγ]
  let Na : End ℂ Va := LinearMap.fst ℂ Va Vb ∘ₗ M ∘ₗ LinearMap.inl ℂ Va Vb
  have h3 : ∀ v, M (v, 0) = (Na v, 0) := fun v => Prod.ext rfl (h2 v)
  have h4 : ∀ (k : ℕ) v, (M ^ k) (v, 0) = ((Na ^ k) v, 0) := fun k => by
    induction k with
    | zero => intro v; simp
    | succ k ih => intro v; rw [pow_succ', pow_succ', End.mul_apply, End.mul_apply, ih, h3]
  have h5 : ∀ (k : ℕ) v, (M ^ k) (g v) = g ((x.N ^ k) v) := fun k => by
    induction k with
    | zero => intro v; simp
    | succ k ih => intro v; rw [pow_succ', pow_succ', End.mul_apply, End.mul_apply, ih, hM]
  refine ⟨{ ρ := a.ρ, N := Na, smooth := a.smooth, semisimple := a.semisimple, nilpotent := ?_, comm := fun σ => ?_ },
    WD.sound ⟨g, hg, fun v => ?_⟩⟩
  · obtain ⟨k, hk⟩ := x.nilpotent
    refine ⟨k, LinearMap.ext fun v => ?_⟩
    have := h4 k v
    rw [← g.apply_symm_apply (v, 0), h5, hk] at this
    simpa using (congrArg Prod.fst this).symm
  · refine LinearMap.ext fun v => ?_
    have k := hc σ (v, 0)
    have e : (a.sum b).ρ σ (v, 0) = (a.ρ σ v, 0) := by simp
    rw [e, h3, h3] at k
    simpa using congrArg Prod.fst k
  · rw [← hM]
    obtain ⟨p, q⟩ := g v
    have e : ((p, q) : Va × Vb) = (p, 0) + (0, q) := by simp
    conv_lhs => rw [e, map_add, h1, h3, add_zero]
    simp [hb]

theorem aw_of_eigen {x y : WD h} (hp : ∀ g : Weil h, x.charPol g = y.charPol g) (h0 : y.mono0 → x = y)
    (hi : ∀ (n : ℕ) (x' y' : WDRep h (Fin n → ℂ)), WD.mk x' = x → WD.mk y' = y →
      ∀ χ : ↥(Ine (F := E) A) → ℂ, (∀ v, (∀ s, y'.ρ (ineIncl h s) v = χ s • v) → y'.N v = 0) →
        ∀ v, (∀ s, x'.ρ (ineIncl h s) v = χ s • v) → x'.N v = 0) : Aw x y := by
  refine ⟨hp, h0, fun u c t γ hγ hm ⟨a, b, e, d, m, p⟩ => ?_⟩
  obtain ⟨n, x, rfl⟩ := x.exists_rep
  obtain ⟨n', y, rfl⟩ := y.exists_rep
  obtain rfl : n = n' := by
    have h1 := WD.charPol_natDegree (WD.mk x) 1
    rw [hp, WD.charPol_natDegree] at h1
    simpa using h1.symm
  obtain ⟨k, u, rfl⟩ := u.exists_rep
  obtain ⟨i, a, rfl⟩ := a.exists_rep
  obtain ⟨j, b, rfl⟩ := b.exists_rep
  obtain ⟨ε, hε⟩ := GlobalTheory.AboveL.weil_rep_equiv_of_charpoly_eq E Ω A w h n n x y fun σ => by simpa using hp σ
  rw [e, WD.inePol_of_mem_Ine _ hγ, WD.lpSum_mk, WD.charPol_mk] at hm
  rw [WD.lpSum_mk, WD.lpSum_mk, WD.mk_eq_mk] at e
  obtain ⟨f, f1, f2⟩ := e
  have hbN : b.N = 0 := (WD.monodromyZero_ofWeilDeligneRepClass_iff b).1 m
  have hbc : ∀ s : ↥(Ine (F := E) A), (b.ρ (ineIncl h s)).charpoly = (X - C (c s)) ^ t := fun s => by
    have := p s s.2
    rwa [WD.inePol_of_mem_Ine _ s.2, WD.charPol_mk] at this
  have hb : ∀ (s : ↥(Ine (F := E) A)) v, b.ρ (ineIncl h s) v = c s • v :=
    fun s => scalar_of_charpoly (b.semisimple _) (hbc s)
  have ha : ∀ v, a.ρ (ineIncl h ⟨γ, hγ⟩) v = c γ • v → v = 0 := fun v hv => by
    by_contra hv0
    have hev : End.HasEigenvalue (a.ρ (ineIncl h ⟨γ, hγ⟩)) (c γ) :=
      End.hasEigenvalue_of_hasEigenvector ⟨End.mem_eigenspace_iff.2 hv, hv0⟩
    have hr := (End.hasEigenvalue_iff_isRoot_charpoly _ _).1 hev
    have hne := (LinearMap.charpoly_monic (a.ρ (ineIncl h ⟨γ, hγ⟩))).ne_zero
    rw [WDRep.sum_ρ, LinearMap.charpoly_prodMap, hbc ⟨γ, hγ⟩,
      rootMultiplicity_mul (mul_ne_zero hne ((monic_X_sub_C _).pow _).ne_zero), rootMultiplicity_X_sub_C_pow] at hm
    have := (rootMultiplicity_pos hne).2 hr
    omega

  have hz : ∀ z, (y.sum u).ρ (ineIncl h ⟨γ, hγ⟩) z = c γ • z → (y.sum u).N z = 0 := fun z hz => by
    apply f.injective
    have k1 := f1 (ineIncl h ⟨γ, hγ⟩) z
    rw [hz, map_smul] at k1
    have k2 : (f z).1 = 0 := ha _ (congrArg Prod.fst k1).symm
    rw [f2, map_zero]
    exact Prod.ext (by simp [k2]) (by simp [hbN])
  have hy : ∀ v, (∀ s, y.ρ (ineIncl h s) v = c s • v) → y.N v = 0 := fun v hv =>
    congrArg Prod.fst (hz (v, 0) (Prod.ext (hv ⟨γ, hγ⟩) (by simp)))
  have hx := hi n x y rfl rfl (fun s => c s) hy
  let g := (ε.prodCongr (LinearEquiv.refl ℂ (Fin k → ℂ))).trans f
  have hg : ∀ σ v, g ((x.sum u).ρ σ v) = (a.sum b).ρ σ (g v) := fun σ v => by
    show f _ = (a.sum b).ρ σ (f _)
    rw [← f1]
    exact congrArg f (Prod.ext (hε σ v.1) rfl)
  obtain ⟨a', e'⟩ := exists_sum (x.sum u) a b g hg hbN (ineIncl h ⟨γ, hγ⟩) (deg_ineIncl _) (c γ) (hb ⟨γ, hγ⟩) ha fun v => by
    have q : ∀ s : ↥(Ine (F := E) A), (x.sum u).ρ (ineIncl h s) (g.symm (0, v)) = c s • g.symm (0, v) := fun s => by
      apply g.injective
      rw [hg, map_smul, g.apply_symm_apply]
      exact Prod.ext (by simp) (hb s v)
    refine Prod.ext (hx _ fun s => congrArg Prod.fst (q s)) ?_
    have q2 := congrArg Prod.snd (q ⟨γ, hγ⟩)
    have q3 := congrArg Prod.snd (hz (0, (g.symm (0, v)).2) (Prod.ext (by simp) q2))
    exact q3
  exact ⟨WD.mk a', WD.mk b, by rw [WD.lpSum_mk, WD.lpSum_mk, e'], d, m, p⟩

end UpperTheory.GalN
