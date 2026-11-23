import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeIsobaric
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLLocalComponentIsUnitaris
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.UnitaryBC

namespace GlobalTheory.BaseChangeBridge

section General

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem exists_equiv_of_isSubquotient {σ : Representation ℂ G W} {ρ : Representation ℂ G V}
    (hσ : σ.IsIrreducible) (hρ : ρ.IsIrreducible) (h : GlobalTheory.SmGL.IsSubquotient σ ρ) :
    ∃ e : W ≃ₗ[ℂ] V, ∀ g x, e (σ g x) = ρ g (e x) := by
  obtain ⟨S, f, hf⟩ := h
  obtain ⟨hW, -⟩ := (GlobalTheory.CuspRep.isIrreducible_iff σ).1 hσ
  obtain ⟨-, hρ'⟩ := (GlobalTheory.CuspRep.isIrreducible_iff ρ).1 hρ
  have hS : S.toSubmodule = ⊤ := by
    rcases hρ' S.toSubmodule (fun g v hv => S.apply_mem_toSubmodule g hv) with e | e
    · exfalso
      obtain ⟨x, hx⟩ := exists_ne (0 : W)
      obtain ⟨v, rfl⟩ := hf x
      have hv : v = 0 := by
        exact Subtype.ext ((Submodule.eq_bot_iff _).1 e v v.2)
      subst hv
      exact hx (map_zero f.toLinearMap)
    · exact e
  let g : V →ₗ[ℂ] W := f.toLinearMap ∘ₗ (LinearEquiv.ofTop S.toSubmodule hS).symm.toLinearMap
  have hg : ∀ x v, g (ρ x v) = σ x (g v) := fun x v => by
    have := LinearMap.congr_fun (f.isIntertwining' x) ((LinearEquiv.ofTop S.toSubmodule hS).symm v)
    exact this
  have gsurj : Function.Surjective g := fun y => by
    obtain ⟨v, rfl⟩ := hf y
    refine ⟨(v : V), ?_⟩
    change f ((LinearEquiv.ofTop S.toSubmodule hS).symm (v : V)) = f v
    congr 1
  have ginj : Function.Injective g := by
    rcases hρ' (LinearMap.ker g) (fun x v hv => by
        rw [LinearMap.mem_ker] at hv ⊢
        rw [hg, hv, map_zero]) with e | e
    · exact LinearMap.ker_eq_bot.1 e
    · exfalso
      obtain ⟨y, hy⟩ := exists_ne (0 : W)
      obtain ⟨v, rfl⟩ := gsurj y
      exact hy (LinearMap.mem_ker.1 (e ▸ Submodule.mem_top))
  let e0 := LinearEquiv.ofBijective g ⟨ginj, gsurj⟩
  refine ⟨e0.symm, fun x y => e0.injective ?_⟩
  rw [LinearEquiv.apply_symm_apply]
  change σ x y = g (ρ x (e0.symm y))
  rw [hg]
  change σ x y = σ x (e0 (e0.symm y))
  rw [LinearEquiv.apply_symm_apply]

variable {H : Type} [Group H]

theorem isSpherical_of_equiv {σ : Representation ℂ H W} {ρ : Representation ℂ H V} (e : W ≃ₗ[ℂ] V)
    (he : ∀ g x, e (σ g x) = ρ g (e x)) {K : Subgroup H} (h : GlobalTheory.LGrp.IsSpherical σ K) :
    GlobalTheory.LGrp.IsSpherical ρ K := by
  obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 h
  exact (Submodule.ne_bot_iff _).2 ⟨e x, GlobalTheory.LGrp.mem_fixed.2 fun k hk => by rw [← he, GlobalTheory.LGrp.mem_fixed.1 hx k hk],
    by simpa using h0⟩

theorem symm_equivariant {σ : Representation ℂ H W} {ρ : Representation ℂ H V} (e : W ≃ₗ[ℂ] V)
    (he : ∀ g x, e (σ g x) = ρ g (e x)) (g : H) (y : V) : e.symm (ρ g y) = σ g (e.symm y) :=
  e.injective (by rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply])

end General

section Local

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem hasSatGL_of_equiv {σ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W}
    {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} (e : W ≃ₗ[ℂ] V) (he : ∀ g x, e (σ g x) = ρ g (e x))
    {B : Multiset ℂˣ} (h : GlobalTheory.LFun.HasSatGL w σ B) : GlobalTheory.LFun.HasSatGL w ρ B := by
  refine ⟨isSpherical_of_equiv e he h.1, fun y hy h0 => ?_⟩
  have hx : e.symm y ∈ GlobalTheory.PRep.fixed σ (GlobalTheory.LFun.KGL w n) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
    rw [← symm_equivariant e he, GlobalTheory.LGrp.mem_fixed.1 hy k hk]
  have h0' : e.symm y ≠ 0 := by simpa using h0
  have := (h.2 _ hx h0').map e.toLinearMap he (by simpa using h0)
  simpa using this

end Local

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isCompAlong_of_equiv {π : Submodule ℂ (UA E n → ℂ)} {Gv : Subgroup (UA E n)} {H : Type} [Group H]
    {p : Gv →* H} {σ : Representation ℂ H W} {ρ : Representation ℂ H V} (e : W ≃ₗ[ℂ] V)
    (he : ∀ g x, e (σ g x) = ρ g (e x)) (hρ : ρ.IsIrreducible) (h : IsCompAlong π Gv p σ) :
    IsCompAlong π Gv p ρ := by
  obtain ⟨-, f, h0, hf, hfi⟩ := h
  refine ⟨hρ, f ∘ₗ e.symm.toLinearMap, fun h1 => h0 ?_, fun v => hf _, fun x v => ?_⟩
  · refine LinearMap.ext fun y => ?_
    simpa using LinearMap.congr_fun h1 (e y)
  · simp [symm_equivariant e he, hfi]

end CM

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem main : GlobalTheory.Published.BaseChangeIsobaric → GlobalTheory.Published.BernsteinUnitaryProductIrreducible →
    GlobalTheory.Published.BaseChangeDefiniteUnitary := by
  intro hBC hB E _ _ _ hun n hn π hπ
  obtain ⟨c, N, h, V, σ, m, P, H⟩ := hBC E hun n hn π hπ
  refine ⟨c, N, h, V, σ, m, ?_⟩
  have hirr : ∀ w, (locProd h w (σ · w)).IsIrreducible := fun w =>
    ((GlobalTheory.SmGL.MultiIrr.products_irreducible hB (w.adicCompletion E)).1 c N (Fin n) (GlobalTheory.SmGL.stdBlocks N h)
      (fun i => (σ i w).V) (fun i => (σ i w).ρ) (fun i => (σ i w).smooth) (fun i => (σ i w).irred)
      (fun i => GlobalTheory.DiscreteUnit.isUnitarisable_of_isLocCompGL E (N i) (V i) (H.discrete i) w (σ i w)
        (H.loc i w))).2.1
  exact
    { pos := H.pos
      discrete := H.discrete
      csd := H.csd
      loc := H.loc
      inf := H.inf
      unram := fun w hw => by
        obtain ⟨e, he⟩ := exists_equiv_of_isSubquotient (P w).irred (hirr w) (H.sub w)
        exact isSpherical_of_equiv e he (H.unram w hw)
      inert := fun w s ϖ q hs hq α hα => by
        obtain ⟨e, he⟩ := exists_equiv_of_isSubquotient (P w).irred (hirr w) (H.sub w)
        exact hasSatGL_of_equiv e he (H.inert w s ϖ q hs hq α hα)
      split := fun w hw => by
        obtain ⟨e, he⟩ := exists_equiv_of_isSubquotient (P w).irred (hirr w) (H.sub w)
        exact isCompAlong_of_equiv e he (hirr w) (H.split w hw)
      weight := H.weight }

end GlobalTheory.BaseChangeBridge
