import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
import Mathlib.RingTheory.SimpleModule.Isotypic

namespace UpperTheory.TP

theorem absIso : AbsIso := by
  intro G V T _ _ _ _ _ ρ U H τ hG hinv hU hτ f hf0 hfU hfe u hu
  classical
  let ρH : Representation ℂ H V := ρ.comp H.subtype
  let R := MonoidAlgebra ℂ H
  haveI : IsSimpleModule R τ.asModule := (Representation.irreducible_iff_isSimpleModule_asModule τ).1 hτ
  let Z : Set G := {z | ∀ h' ∈ H, Commute z h'}
  let S : Set V := {v | ∃ z ∈ Z, ∃ x, v = ρ z (f x)}
  have hmul : ∀ (a b : G) v, ρ (a * b) v = ρ a (ρ b v) := fun a b v => by rw [map_mul]; rfl
  have hze : ∀ z ∈ Z, ∀ (h : H) y, ρ z (f (τ h y)) = ρ h (ρ z (f y)) := fun z hz h y => by
    rw [hfe, ← hmul, ← hmul, (hz h h.2).eq]
  have hS : Submodule.span ℂ S = U := by
    have hle : Submodule.span ℂ S ≤ U := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨z, -, x, rfl⟩
      exact hinv z _ (hfU x)
    refine (hU _ hle ?_).resolve_left ?_
    · intro g v hv
      obtain ⟨h, hh, hc⟩ := hG g
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨z, hz, x, rfl⟩ := hv
        have hw : h⁻¹ * g * z ∈ Z := fun h' hh' => (hc h' hh').mul_left (hz h' hh')
        refine Submodule.subset_span ⟨_, hw, τ ⟨h, hh⟩ x, ?_⟩
        rw [hfe, ← hmul, ← hmul]
        have e : g * z = h⁻¹ * g * z * h := by rw [(hw h hh).eq]; group
        change ρ (g * z) (f x) = ρ (h⁻¹ * g * z * h) (f x)
        rw [← e]
      | zero => simp
      | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
      | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha
    · intro h0
      apply hf0
      ext x
      have : ρ 1 (f x) ∈ Submodule.span ℂ S := Submodule.subset_span ⟨1, fun h' _ => Commute.one_left h', x, rfl⟩
      rw [h0, Submodule.mem_bot] at this
      simpa using this
  refine ⟨?_, fun hu0 => ?_⟩
  · rw [← hS] at hu
    obtain ⟨m, a, g, rfl⟩ := Submodule.mem_span_set'.1 hu
    choose z hz x hx using fun i => (g i).2
    refine ⟨m, fun i => ρ (z i) ∘ₗ f, fun i => a i • x i, fun i y => hinv _ _ (hfU y), fun i h y => hze _ (hz i) h y, ?_⟩
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hx i]
  · let M := ρH.asModule
    let I := isotypicComponent R M τ.asModule
    let I' : Submodule ℂ V := (I.restrictScalars ℂ).comap ρH.asModuleEquiv.symm.toLinearMap
    have hUI : U ≤ I' := by
      rw [← hS]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨z, hz, x, rfl⟩
      let F : τ.asModule →ₗ[R] M := Representation.IntertwiningMap.equivLinearMapAsModule τ ρH
        ⟨ρ z ∘ₗ f, fun h => LinearMap.ext fun y => hze z hz h y⟩
      have h1 : LinearMap.range F ≤ I := by
        rcases LinearMap.injective_or_eq_zero F with hf | hf
        · exact le_sSup ⟨(LinearEquiv.ofInjective F hf).symm⟩
        · simp [hf]
      exact h1 ⟨τ.asModuleEquiv.symm x, rfl⟩
    obtain ⟨ι, ⟨e⟩⟩ := (IsIsotypicOfType.isotypicComponent R M τ.asModule).linearEquiv_finsupp
    have hne : e ⟨ρH.asModuleEquiv.symm u, hUI hu⟩ ≠ 0 := by
      intro h0
      have := e.injective (h0.trans (map_zero e).symm)
      apply hu0
      simpa using congrArg Subtype.val this
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hne
    let Q : I →ₗ[R] τ.asModule := Finsupp.lapply i ∘ₗ e.toLinearMap
    let q0 : I' →ₗ[ℂ] T :=
      { toFun := fun v => τ.asModuleEquiv (Q ⟨ρH.asModuleEquiv.symm v.1, v.2⟩)
        map_add' := fun a b => by
          rw [← map_add]; congr 1; rw [← map_add]; congr 1
        map_smul' := fun c a => by
          rw [RingHom.id_apply, ← map_smul, ← LinearMap.map_smul_of_tower]; congr 2 }
    obtain ⟨p, hp⟩ := LinearMap.exists_extend q0
    have hpv : ∀ (v : V) (hv : v ∈ I'), p v = τ.asModuleEquiv (Q ⟨ρH.asModuleEquiv.symm v, hv⟩) :=
      fun v hv => LinearMap.congr_fun hp ⟨v, hv⟩
    refine ⟨p, ?_, fun h y hy => ?_⟩
    · rw [hpv u (hUI hu)]
      intro h0
      exact hi (τ.asModuleEquiv.injective (h0.trans (map_zero _).symm))
    · have hy' := hUI hy
      have hhy := hUI (hinv h y hy)
      rw [hpv _ hy', hpv _ hhy]
      have e1 : (⟨ρH.asModuleEquiv.symm (ρ h y), hhy⟩ : I) = MonoidAlgebra.of ℂ H h • (⟨ρH.asModuleEquiv.symm y, hy'⟩ : I) := by
        ext
        exact Representation.asModuleEquiv_symm_map_rho ρH h y
      rw [e1, map_smul]
      exact (Representation.asModuleEquiv_map_smul τ _ _).trans (by simp)

end UpperTheory.TP
