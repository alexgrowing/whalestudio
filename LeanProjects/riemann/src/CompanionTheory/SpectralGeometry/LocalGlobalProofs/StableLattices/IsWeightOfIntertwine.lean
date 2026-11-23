import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.SimpleDistinctness.ScalarCharacterOfL2Embedding

noncomputable section

namespace GlobalTheory.CompanionTheory.RgIso

open CompanionTheory.RgExh
open Formalism.REAL (GlRel qdet qminor Tm KHighest IsWeight)
open CompanionTheory.D.LK (LocFin IsMin)
open CompanionTheory.D.DSIC (KStab)

variable {n : ℕ}

theorem iso_refl (X : GMod n) : Iso X X := by
  exact ⟨LinearEquiv.refl ℂ X.V, fun a b x => rfl⟩

theorem intertwine_symm {X Y : GMod n} (e : X.V ≃ₗ[ℂ] Y.V) (he : ∀ a b x, e (X.E a b x) = Y.E a b (e x))
    (a b : Fin n) (y : Y.V) : e.symm (Y.E a b y) = X.E a b (e.symm y) := by
  apply e.injective
  rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]

theorem iso_symm {X Y : GMod n} : Iso X Y → Iso Y X := by
  rintro ⟨e, he⟩
  exact ⟨e.symm, intertwine_symm e he⟩

theorem iso_trans {X Y Z : GMod n} : Iso X Y → Iso Y Z → Iso X Z := by
  rintro ⟨e, he⟩ ⟨f, hf⟩
  exact ⟨e.trans f, fun a b x => by rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, he, hf]⟩

def cj {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W) :
    Module.End ℂ V →+* Module.End ℂ W where
  toFun f := e.toLinearMap ∘ₗ f ∘ₗ e.symm.toLinearMap
  map_one' := by ext; simp
  map_mul' f g := by ext; simp
  map_zero' := by ext; simp
  map_add' f g := by ext; simp

theorem cj_apply {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W)
    (f : Module.End ℂ V) (w : W) : cj e f w = e (f (e.symm w)) := rfl

theorem cj_smul_one {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W)
    (c : ℂ) : cj e (c • (1 : Module.End ℂ V)) = c • (1 : Module.End ℂ W) := by
  refine LinearMap.ext fun w => ?_
  rw [cj_apply]
  simp

theorem cj_algebraMap {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W)
    (c : ℂ) : cj e (algebraMap ℂ (Module.End ℂ V) c) = algebraMap ℂ (Module.End ℂ W) c := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, cj_smul_one]

theorem cj_E {X Y : GMod n} (e : X.V ≃ₗ[ℂ] Y.V) (he : ∀ a b x, e (X.E a b x) = Y.E a b (e x)) (a b : Fin n) :
    cj e (X.E a b) = Y.E a b := by
  refine LinearMap.ext fun w => ?_
  rw [cj_apply, he, LinearEquiv.apply_symm_apply]

theorem cj_Tm {X Y : GMod n} (e : X.V ≃ₗ[ℂ] Y.V) (he : ∀ a b x, e (X.E a b x) = Y.E a b (e x)) (u : ℂ)
    (a b : Fin n) : cj e (Tm X.E u a b) = Tm Y.E u a b := by
  unfold Formalism.REAL.Tm
  rw [map_add, cj_E e he]
  split_ifs
  · rw [cj_algebraMap]
  · rw [map_zero]

theorem cj_qdet {X Y : GMod n} (e : X.V ≃ₗ[ℂ] Y.V) (he : ∀ a b x, e (X.E a b x) = Y.E a b (e x)) (u : ℂ) :
    cj e (qdet X.E u) = qdet Y.E u := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor
  simp only [map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn, Function.comp_def, cj_Tm e he]

theorem scalChar_of_iso {X Y : GMod n} (h : Iso X Y) (χ : Fin n → ℂ) (hX : ScalChar X χ) : ScalChar Y χ := by
  obtain ⟨e, he⟩ := h
  intro t
  rw [← cj_qdet e he, hX t, cj_smul_one]

theorem hasChar_of_iso {X Y : GMod n} (h : Iso X Y) (χ : Fin n → ℂ) (hX : HasChar X χ) : HasChar Y χ := by
  obtain ⟨e, he⟩ := h
  obtain ⟨k, hk⟩ := hX
  refine ⟨k, fun t => ?_⟩
  rw [← cj_qdet e he, ← cj_smul_one e, ← map_sub, ← map_pow, hk t, map_zero]

theorem isSimple_of_iso {X Y : GMod n} (h : Iso X Y) (hX : IsSimple X) : IsSimple Y := by
  obtain ⟨e, he⟩ := h
  refine ⟨?_, fun S hS => ?_⟩
  · haveI := hX.1
    exact e.symm.toEquiv.nontrivial
  · have hS' : ∀ a b, ∀ x ∈ S.comap (e : X.V →ₗ[ℂ] Y.V), X.E a b x ∈ S.comap (e : X.V →ₗ[ℂ] Y.V) := by
      intro a b x hx
      simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at hx ⊢
      rw [he]
      exact hS a b _ hx
    rcases hX.2 _ hS' with h0 | h1
    · left
      rw [eq_bot_iff]
      intro y hy
      rw [Submodule.mem_bot]
      have hy' : e.symm y ∈ S.comap (e : X.V →ₗ[ℂ] Y.V) := by simpa using hy
      rw [h0, Submodule.mem_bot] at hy'
      simpa using hy'
    · right
      rw [eq_top_iff]
      intro y _
      have hy' : e.symm y ∈ S.comap (e : X.V →ₗ[ℂ] Y.V) := by
        rw [h1]
        trivial
      simpa using hy'

theorem locFin_of_iso {X Y : GMod n} (ε : Fin n → Bool) (h : Iso X Y) (hX : LocFin ε X.E) : LocFin ε Y.E := by
  obtain ⟨e, he⟩ := h
  intro y
  obtain ⟨S, hfd, hst, hx⟩ := hX (e.symm y)
  refine ⟨S.map (e : X.V →ₗ[ℂ] Y.V), ?_, ?_, ?_⟩
  · haveI := hfd
    exact Module.Finite.map S _
  · intro a b hab v hv
    obtain ⟨x, hxS, rfl⟩ := Submodule.mem_map.mp hv
    have hm := Submodule.mem_map_of_mem (f := (e : X.V →ₗ[ℂ] Y.V)) (hst a b hab x hxS)
    simpa [he] using hm
  · exact ⟨e.symm y, hx, by simp⟩

theorem isWeight_of_intertwine {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (e : V ≃ₗ[ℂ] W) (E : Fin n → Fin n → Module.End ℂ V) (F : Fin n → Fin n → Module.End ℂ W)
    (he : ∀ a b x, e (E a b x) = F a b (e x)) {μ : Fin n → ℝ} {x : V} (h : IsWeight E μ x) :
    IsWeight F μ (e x) := by
  intro a
  rw [← he, h a, map_smul]

theorem kHighest_of_intertwine {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (e : V ≃ₗ[ℂ] W) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (F : Fin n → Fin n → Module.End ℂ W)
    (he : ∀ a b x, e (E a b x) = F a b (e x)) {μ : Fin n → ℝ} {x : V} (h : KHighest ε E μ x) :
    KHighest ε F μ (e x) := by
  exact ⟨isWeight_of_intertwine e E F he h.1, fun a b hab hε => by rw [← he, h.2 a b hab hε, map_zero]⟩

theorem intWt_of_iso {X Y : GMod n} (h : Iso X Y) (hX : IntWt X) : IntWt Y := by
  obtain ⟨e, he⟩ := h
  intro μ y hy hw
  have hx : e.symm y ≠ 0 := by simpa using hy
  exact hX μ (e.symm y) hx (isWeight_of_intertwine e.symm Y.E X.E (fun a b z => intertwine_symm e he a b z) hw)

theorem algDS_of_iso {X Y : GMod n} (ε : Fin n → Bool) (h : Iso X Y) (s : Equiv.Perm (Fin n)) (mu : Fin n → ℝ)
    (hX : AlgDS ε X s mu) : AlgDS ε Y s mu := by
  obtain ⟨e, he⟩ := h
  obtain ⟨h1, h2, h3, v, hv, hk⟩ := hX
  refine ⟨h1, h2, ?_, e v, by simpa using hv,
    kHighest_of_intertwine e _ (fun a b => X.E (s a) (s b)) (fun a b => Y.E (s a) (s b))
      (fun a b x => he (s a) (s b) x) hk⟩
  intro μ y hy hky
  exact h3 μ (e.symm y) (by simpa using hy)
    (kHighest_of_intertwine e.symm _ (fun a b => Y.E (s a) (s b)) (fun a b => X.E (s a) (s b))
      (fun a b z => intertwine_symm e he (s a) (s b) z) hky)

theorem coneDS_of_iso {X Y : GMod n} (ε : Fin n → Bool) (h : Iso X Y) (s : Equiv.Perm (Fin n)) (mu : Fin n → ℝ)
    (hX : CompanionTheory.RgExh.Fin.ConeDS ε X s mu) : CompanionTheory.RgExh.Fin.ConeDS ε Y s mu := by
  obtain ⟨e, he⟩ := h
  intro ν y hy hky
  exact hX ν (e.symm y) (by simpa using hy)
    (kHighest_of_intertwine e.symm _ (fun a b => Y.E (s a) (s b)) (fun a b => X.E (s a) (s b))
      (fun a b z => intertwine_symm e he (s a) (s b) z) hky)

theorem isoFacts : CompanionTheory.RgExh.Fin.IsoFacts := by
  intro n ε X Y Z
  exact ⟨iso_refl X, iso_symm, iso_trans, fun h => ⟨isSimple_of_iso h, isSimple_of_iso (iso_symm h)⟩,
    fun h χ => ⟨scalChar_of_iso h χ, scalChar_of_iso (iso_symm h) χ⟩,
    fun h χ => ⟨hasChar_of_iso h χ, hasChar_of_iso (iso_symm h) χ⟩,
    fun h => ⟨locFin_of_iso ε h, locFin_of_iso ε (iso_symm h)⟩,
    fun h => ⟨intWt_of_iso h, intWt_of_iso (iso_symm h)⟩,
    fun h s mu => ⟨algDS_of_iso ε h s mu, algDS_of_iso ε (iso_symm h) s mu⟩,
    fun h s mu => ⟨coneDS_of_iso ε h s mu, coneDS_of_iso ε (iso_symm h) s mu⟩⟩

end GlobalTheory.CompanionTheory.RgIso
