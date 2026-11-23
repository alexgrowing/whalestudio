import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RootsCharpolySmulMatrix
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyDualTamePart
import Formalism.LocalToGlobal.NormalizedHeckeFactors.ValLeOneOfIsIntegral

noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

namespace UpperTheory.Zero.LLC.WDB

section LinAlg

variable {G V V' : Type*} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

private theorem irr_iff (ρ : Representation ℂ G V) :
    ρ.IsIrreducible ↔ Nontrivial V ∧
      ∀ S : Submodule ℂ V, (∀ g, ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤ := by
  constructor
  · intro hρ
    refine ⟨?_, fun S hS => ?_⟩
    · obtain ⟨x, y, hxy⟩ := hρ.toNontrivial.exists_pair_ne
      by_contra hV
      rw [not_nontrivial_iff_subsingleton] at hV
      exact hxy (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
    · rcases hρ.eq_bot_or_eq_top ⟨S, fun g v hv => hS g v hv⟩ with h | h
      · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
      · exact Or.inr (congrArg Subrepresentation.toSubmodule h)
  · rintro ⟨hV, H⟩
    have hne : (⊥ : Subrepresentation ρ) ≠ ⊤ := fun h =>
      bot_ne_top (α := Submodule ℂ V) (congrArg Subrepresentation.toSubmodule h)
    refine { exists_pair_ne := ⟨⊥, ⊤, hne⟩, eq_bot_or_eq_top := fun S => ?_ }
    rcases H S.toSubmodule (fun g v hv => S.apply_mem_toSubmodule g hv) with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective h)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h)

private theorem irr_of_equiv {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'} (e : V ≃ₗ[ℂ] V')
    (he : ∀ g v, e (ρ g v) = ρ' g (e v)) (hρ : ρ.IsIrreducible) : ρ'.IsIrreducible := by
  obtain ⟨hV, H⟩ := (irr_iff ρ).1 hρ
  refine (irr_iff ρ').2 ⟨e.injective.nontrivial, fun S hS => ?_⟩
  have hinv : ∀ g, ∀ v ∈ S.comap (e : V →ₗ[ℂ] V'), ρ g v ∈ S.comap (e : V →ₗ[ℂ] V') := by
    intro g v hv
    have hv' : e v ∈ S := hv
    show e (ρ g v) ∈ S
    rw [he]
    exact hS g _ hv'
  rcases H _ hinv with h | h
  · left
    rw [eq_bot_iff]
    intro v hv
    have : e.symm v ∈ S.comap (e : V →ₗ[ℂ] V') := by simpa using hv
    rw [h, Submodule.mem_bot] at this
    simpa using this
  · right
    rw [eq_top_iff]
    intro v _
    have : e.symm v ∈ S.comap (e : V →ₗ[ℂ] V') := by rw [h]; trivial
    simpa using this

private theorem irr_dual [FiniteDimensional ℂ V] {ρ : Representation ℂ G V} (hρ : ρ.IsIrreducible) :
    ρ.dual.IsIrreducible := by
  obtain ⟨hV, H⟩ := (irr_iff ρ).1 hρ
  refine (irr_iff ρ.dual).2 ⟨inferInstance, fun S hS => ?_⟩
  have hT := H S.dualCoannihilator (fun g v hv => ?_)
  · rcases hT with h | h
    · right
      have := Subspace.dualCoannihilator_dualAnnihilator_eq (W := S)
      rw [h] at this
      rw [← this]
      simp
    · left
      have := Subspace.dualCoannihilator_dualAnnihilator_eq (W := S)
      rw [h] at this
      rw [← this]
      simp
  · rw [Submodule.mem_dualCoannihilator] at hv ⊢
    intro f hf
    have := hv _ (hS g⁻¹ f hf)
    simpa [Representation.dual_apply, Module.Dual.transpose_apply] using this

private theorem prod_roots [FiniteDimensional ℂ V] (f : Module.End ℂ V) :
    f.charpoly.roots.prod = LinearMap.det f := by
  rw [← LinearMap.charpoly_toMatrix f (Module.finBasis ℂ V), ← Matrix.det_eq_prod_roots_charpoly,
    LinearMap.det_toMatrix]

private theorem charpoly_inv_prod {n : ℕ} (f g : Module.End ℂ (Fin n → ℂ)) (hfg : f * g = 1)
    (s : Multiset ℂ) (hs : f.charpoly = (s.map fun μ => X - C μ).prod) :
    g.charpoly = (s.map fun μ => X - C μ⁻¹).prod := by
  have e : ∀ k : Module.End ℂ (Fin n → ℂ), (LinearMap.toMatrix' k).charpoly = k.charpoly := fun k => by
    rw [← LinearMap.toMatrix_eq_toMatrix', LinearMap.charpoly_toMatrix]
  have hM : LinearMap.toMatrix' f * LinearMap.toMatrix' g = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have : f ∘ₗ g = LinearMap.id := hfg
    rw [this, LinearMap.toMatrix'_id]
  have h1 := Formalism.L2.NR.charpoly_inv_of_eq (LinearMap.toMatrix' f) (IsUnit.of_mul_eq_one _ hM) s
    (by rw [← hs]; exact e f)
  rw [Matrix.inv_eq_right_inv hM] at h1
  rw [← h1]
  exact (e g).symm

end LinAlg

section WDFacts

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

private theorem isIrrWD_mk (a : WDRep h V) (ha : a.ρ.IsIrreducible) : IsIrrWD (WD.mk a) := by
  obtain ⟨e, he, -⟩ := WD.iso_std a
  exact ⟨(WD.std a).1, (WD.std a).2, WD.sound (WD.iso_std a).symm, irr_of_equiv e he ha⟩

private theorem isTameWD_mk (a : WDRep h V)
    (ha : ∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → a.ρ σ = 1) : IsTameWD (WD.mk a) :=
  ⟨(WD.std a).1, (WD.std a).2, WD.sound (WD.iso_std a).symm,
    fun σ hσ => (WD.iso_std a).ρ_eq_one (ha σ hσ)⟩

private theorem monodromy_zero_of_irreducible (a : WDRep h V) (ha : a.ρ.IsIrreducible) : a.N = 0 := by
  obtain ⟨hV, H⟩ := (irr_iff a.ρ).1 ha
  have hq : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot
  have hinv : ∀ σ, ∀ v ∈ LinearMap.ker a.N, a.ρ σ v ∈ LinearMap.ker a.N := by
    intro σ v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have := a.comm_apply σ v
    rw [hv, map_zero] at this
    exact (smul_eq_zero.mp this.symm).resolve_left (zpow_ne_zero _ hq)
  rcases H _ hinv with h0 | h0
  · exfalso
    have hu : IsUnit a.N := (LinearMap.isUnit_iff_ker_eq_bot _).2 h0
    obtain ⟨k, hk⟩ := a.nilpotent
    have := hu.pow k
    rw [hk] at this
    exact not_isUnit_zero this
  · exact LinearMap.ker_eq_top.mp h0

private theorem irr_twist (b : WDRep h V) (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ)
    (hb : b.ρ.IsIrreducible) : (b.twist ξ hξ).ρ.IsIrreducible := by
  obtain ⟨hV, H⟩ := (irr_iff b.ρ).1 hb
  refine (irr_iff _).2 ⟨hV, fun S hS => H S fun σ v hv => ?_⟩
  have h1 := S.smul_mem ((ξ σ : ℂ)⁻¹) (hS σ v hv)
  simpa [smul_smul] using h1

end WDFacts

end UpperTheory.Zero.LLC.WDB

open UpperTheory.Zero.LLC.WDB in
theorem UpperTheory.Zero.LLC.wDBasic :
    UpperTheory.Zero.LLC.WDBasic := by
  intro E Ω _ _ _ _ _ A w h V
  obtain ⟨n, a, rfl⟩ := V.exists_rep
  have hcoe : ∀ (t : Ine (F := E) A) (x : WD h), x.inePol (t : G E Ω) = x.charPol (ineIncl h t) :=
    fun t x => WD.inePol_of_mem_Ine x t.2
  refine ⟨?_, ?_, ⟨frob h, deg_frob⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨(Units.map (LinearMap.det : Module.End ℂ (Fin n → ℂ) →* ℂ)).comp a.ρ.toHomUnits, fun σ => ?_⟩
    rw [WD.eig_mk, prod_roots]
    rfl
  · intro φ δ δ' hφ h1 h2
    refine MonoidHom.ext fun σ => ?_
    obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul hφ σ
    rw [hτ, map_mul, map_mul, map_zpow, map_zpow, h1, h2]
  · rintro ⟨m, b, hb, hirr⟩
    rw [← hb]
    obtain ⟨hV, -⟩ := (irr_iff b.ρ).1 hirr
    refine ⟨(WD.monodromyZero_ofWeilDeligneRepClass_iff b).2 (monodromy_zero_of_irreducible b hirr), ?_, ?_⟩
    · rw [WD.lpDim_mk]
      exact Module.finrank_pos
    · rw [WD.lpDual_mk]
      exact isIrrWD_mk _ (irr_dual hirr)
  · rintro ⟨m, b, hb, hw⟩
    rw [← hb, WD.lpDual_mk]
    refine isTameWD_mk _ fun σ hσ => ?_
    have h1 : b.ρ σ⁻¹ = 1 := by
      rw [← one_mul (b.ρ σ⁻¹), ← hw σ hσ, ← map_mul, mul_inv_cancel, map_one, hw σ hσ]
    rw [WDRep.dual_ρ, h1]
    ext
    simp
  · rw [WD.lpDual_mk, WD.lpDim_mk, WD.lpDim_mk, Subspace.dual_finrank_eq]
  · intro σ
    rw [WD.lpDual_mk, WD.eig_mk, WD.eig_mk, WDRep.dual_ρ, GlobalTheory.WeilDeligne.LabDual.charpoly_dualMap,
      prod_roots, prod_roots]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
  · intro t m hm
    rw [hcoe, WD.charPol_mk] at hm
    have hm' : (a.ρ (ineIncl h t)).charpoly = ((m.map fun z : ℂˣ => (z : ℂ)).map fun z => X - C z).prod := by
      have hb : (do let x ← m; pure (x : ℂ) : Multiset ℂ) = m.map fun z : ℂˣ => (z : ℂ) :=
        Multiset.bind_singleton _ _
      rw [hm, hb]
    refine ⟨?_, ?_, fun ξ hξ => ?_⟩
    · rw [WD.eig_mk, hm', roots_multiset_prod_X_sub_C]
      exact (map_multiset_prod (Units.coeHom ℂ) m).symm
    · rw [hcoe, WD.lpDual_mk, WD.charPol_mk, WDRep.dual_ρ, GlobalTheory.WeilDeligne.LabDual.charpoly_dualMap,
        charpoly_inv_prod (a.ρ (ineIncl h t)) (a.ρ (ineIncl h t)⁻¹) (by rw [← map_mul, mul_inv_cancel, map_one]) _ hm',
        Multiset.map_map]
      simp
    · rw [hcoe, WD.lpTwist_mk, WD.charPol_mk, WDRep.twist_ρ]
      rw [(IsAlgClosed.splits _).eq_prod_roots_of_monic (LinearMap.charpoly_monic _),
        GlobalTheory.RowTie.EigTwist.roots_charpoly_smul, hm', roots_multiset_prod_X_sub_C,
        Multiset.map_map, Multiset.map_map]
      simp
  · intro ξ hξ
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · rintro ⟨m, b, hb, hirr⟩
      rw [← hb, WD.lpTwist_mk]
      exact isIrrWD_mk _ (irr_twist b ξ hξ hirr)
    · intro σ
      rw [WD.lpTwist_mk, WD.eig_mk, WD.eig_mk, WDRep.twist_ρ, prod_roots, prod_roots, LinearMap.det_smul,
        WD.lpDim_mk, mul_comm]
    · intro ξ' hξ' h''
      rw [WD.lpTwist_mk, WD.lpTwist_mk, WD.lpTwist_mk]
      refine WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => rfl⟩
      simp [smul_smul, mul_comm]
    · rintro rfl
      rw [WD.lpTwist_mk]
      exact WD.sound ⟨.refl _ _, fun σ v => by simp, fun v => rfl⟩
    · intro hξ'
      rw [WD.lpTwist_mk, WD.lpDual_mk, WD.lpDual_mk, WD.lpTwist_mk]
      refine WD.sound ⟨.refl _ _, fun σ f => ?_, fun f => rfl⟩
      ext v
      simp
    · rintro hw ⟨m, b, hb, hb1⟩
      rw [← hb, WD.lpTwist_mk]
      refine isTameWD_mk _ fun σ hσ => ?_
      simp [hw σ hσ, hb1 σ hσ]
    · rintro hpos ⟨m, b, hb, hb1⟩ ⟨m', c, hc, hc1⟩ σ hσ
      rw [← hb, WD.lpTwist_mk] at hc
      rw [← hb, WD.lpDim_mk] at hpos
      have h1 := (WD.mk_eq_mk.mp hc).ρ_eq_one (hc1 σ hσ)
      rw [WDRep.twist_ρ, hb1 σ hσ] at h1
      have hV : Nontrivial (Fin m → ℂ) := Module.nontrivial_of_finrank_pos hpos
      obtain ⟨v, hv⟩ := exists_ne (0 : Fin m → ℂ)
      have h2 : ((ξ σ : ℂ) - 1) • v = 0 := by
        rw [sub_smul, one_smul, sub_eq_zero]
        simpa using LinearMap.congr_fun h1 v
      exact Units.ext (sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hv))
