import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LimitPairSpaces.TypeBOfMemTypSp
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PTypes

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.LV

open PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.KTypeSlices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_sep {α : Type} (X : Submodule ℂ (α → ℂ)) [FiniteDimensional ℂ X] :
    ∃ S : Finset α, ∀ w ∈ X, (∀ a ∈ S, w a = 0) → w = 0 := by
  classical
  let Ker : Finset α → Submodule ℂ (α → ℂ) := fun S =>
    X ⊓ ⨅ a ∈ S, LinearMap.ker (LinearMap.proj a : (α → ℂ) →ₗ[ℂ] ℂ)
  have hmem : ∀ S w, w ∈ Ker S ↔ w ∈ X ∧ ∀ a ∈ S, w a = 0 := by
    intro S w
    simp only [Ker, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.proj_apply]
  have hfd : ∀ S, FiniteDimensional ℂ (Ker S) := fun S => Submodule.finiteDimensional_of_le inf_le_left
  have hex : ∃ d, ∃ S, Module.finrank ℂ (Ker S) = d := ⟨_, ∅, rfl⟩
  obtain ⟨S, hS0⟩ := Nat.find_spec hex
  have hS : ∀ S', Module.finrank ℂ (Ker S) ≤ Module.finrank ℂ (Ker S') := fun S' => by
    rw [hS0]
    exact Nat.find_min' hex ⟨S', rfl⟩
  refine ⟨S, fun w hw h0 => ?_⟩
  by_contra hne
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hne
  have hlt : Ker (insert a S) < Ker S := by
    refine lt_of_le_of_ne (fun v hv => ?_) (fun he => ?_)
    · rw [hmem] at hv ⊢
      exact ⟨hv.1, fun b hb => hv.2 b (Finset.mem_insert_of_mem hb)⟩
    · have hwS : w ∈ Ker S := (hmem S w).2 ⟨hw, h0⟩
      rw [← he, hmem] at hwS
      exact ha (hwS.2 a (Finset.mem_insert_self a S))
  have := hfd S
  exact absurd (hS (insert a S)) (not_le.2 (Submodule.finrank_lt_finrank_of_lt hlt))

theorem typSp_tw_le {n : ℕ} {K' : Subgroup (GL (Fin n) (Af E))} (hK : K' ≤ detKer n)
    (W' : Submodule ℂ (Kinf E n → ℂ)) (U : Submodule ℂ (Sm E n)) (z : ℂ) :
    TypSp K' W' (tw U z) ≤ (TypSp K' W' U).map (mulChi n (Model.absC E z)).toLinearMap := by
  refine Submodule.span_le.2 ?_
  rintro φ ⟨hφ, hT⟩
  obtain ⟨χ, hχ, rfl⟩ := hφ
  refine ⟨χ, Submodule.subset_span ⟨hχ, ?_⟩, rfl⟩
  have e : χ = mulChi n (Model.absC E (-z)) (mulChi n (Model.absC E z) χ) :=
    (ParabolicProjection.mulChi_absC_neg n z χ).symm
  rw [e]
  exact t_typeB_mulChi hT hK (-z)

theorem finiteDimensional_type_space_of_disc (hA : AdmDisc) {N : ℕ} (K : Subgroup (GL (Fin N) (Af E)))
    (hK : IsOpen (K : Set (GL (Fin N) (Af E)))) (W : Submodule ℂ (Kinf E N → ℂ)) [hW : FiniteDimensional ℂ W] :
    ∀ {n : ℕ} (t : Tr E n), n ≤ N → t.Disc → FiniteDimensional ℂ (TypSp (Kf N K n) (Wf N W n) t.space) := by
  intro n t
  induction t with
  | leaf V z =>
    intro _ ht
    show FiniteDimensional ℂ (TypSp (Kf N K _) (Wf N W _) (tw V z))
    rcases ht with ⟨rfl, -, -⟩ | ⟨-, hV⟩
    · have : Subsingleton (GA E 0) := ⟨fun a b => Units.ext (Matrix.ext fun i => Fin.elim0 i)⟩
      infer_instance
    · have : FiniteDimensional ℂ (TypSp (Kf N K _) (Wf N W _) V) :=
        hA E _ _ _ (isOpen_Kf hK _) (fd_Wf hW _) V hV
      exact Submodule.finiteDimensional_of_le (typSp_tw_le (Kf_le_det _) (Wf N W _) V z)
  | @node r s t₁ t₂ ih₁ ih₂ =>
    intro hN ht
    obtain ⟨ht₁, ht₂⟩ := ht
    have : FiniteDimensional ℂ (TypSp (Kf N K r) (Wf N W r) (tw t₁.space ((s : ℂ) / 2))) := by
      have := ih₁ (by omega) ht₁
      exact Submodule.finiteDimensional_of_le (typSp_tw_le (Kf_le_det _) _ _ _)
    have : FiniteDimensional ℂ (TypSp (Kf N K s) (Wf N W s) (tw t₂.space (-(r : ℂ) / 2))) := by
      have := ih₂ (by omega) ht₂
      exact Submodule.finiteDimensional_of_le (typSp_tw_le (Kf_le_det _) _ _ _)
    set Y := tens2 (TypSp (Kf N K r) (Wf N W r) (tw t₁.space ((s : ℂ) / 2)))
      (TypSp (Kf N K s) (Wf N W s) (tw t₂.space (-(r : ℂ) / 2))) with hY
    have : FiniteDimensional ℂ Y := fd_tens2 _ _
    set X := TypSp (Kf N K (r + s)) (Wf N W (r + s)) (Tr.node t₁ t₂).space with hX
    have : FiniteDimensional ℂ (Wf N W (r + s)) := fd_Wf hW _
    obtain ⟨S, hS⟩ := exists_sep (Wf N W (r + s))
    set T := Tset r s (Kf N K (r + s)) with hTdef
    have hI : ∀ φ ∈ X, MemInd2 (tw t₁.space ((s : ℂ) / 2)) (tw t₂.space (-(r : ℂ) / 2)) φ := by
      intro φ hφ
      have hf : φ ∈ (Tr.node t₁ t₂).space := typSp_le _ _ _ hφ
      rw [Tr.space] at hf
      exact memInd2_of_span (Submodule.span_mono (fun φ h => h.1) hf)
    have key : ∀ φ ∈ X, ∀ t ∈ T, ∀ k : Kinf E (r + s),
        (fun m : GA E r × GA E s =>
          φ.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) t))) ∈ Y := by
      intro φ hφ t ht k
      have hT := typeB_of_mem_typSp hφ
      refine tens_typ ((hI φ hφ).2 k t) (fun y => ⟨fun u hu x₁ => ?_, fun x₁ => ?_⟩)
        (fun x => ⟨fun u hu x₂ => ?_, fun x₂ => ?_⟩)
      · have h1 : lev (Ad E) r s (x₁ * finGL E r u, y) =
            lev (Ad E) r s (x₁, y) * finGL E (r + s) (lev (Af E) r s (u, 1)) := by
          rw [← Slice1.lev_finGL, map_one, ← map_mul, Prod.mk_mul_mk, mul_one]
        have hc := infGL_comm (Unitary.toUnits k) (lev (Af E) r s (u, 1))
        have e : lev (Ad E) r s (x₁ * finGL E r u, y) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) t) =
            lev (Ad E) r s (x₁, y) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) t) *
              finGL E (r + s) (t⁻¹ * lev (Af E) r s (u, 1) * t) := by
          rw [h1, map_mul, map_mul, map_inv]
          simp only [mul_assoc]
          rw [← mul_assoc (finGL E (r + s) (lev (Af E) r s (u, 1))), ← hc]
          group
        show φ.1 _ = φ.1 _
        rw [e, hT.1 _ (Kf_left hN ht hu)]
      · have hw := typeB_lt hT (lev (Ad E) r s (x₁, y) * finGL E (r + s) t)
        have hW₁ := Wf_left (W := W) hN hw k
        convert hW₁ using 1
        funext k₁
        show φ.1 _ = _
        rw [infGL_comm, ← mul_assoc, Slice1.lev_infGL_right]
        simp only [map_mul, Slice1.toUnits_levK]
      · have h1 : lev (Ad E) r s (x, x₂ * finGL E s u) =
            lev (Ad E) r s (x, x₂) * finGL E (r + s) (lev (Af E) r s (1, u)) := by
          rw [← Slice2.lev_finGL_one, ← map_mul, Prod.mk_mul_mk, mul_one]
        have hc := infGL_comm (Unitary.toUnits k) (lev (Af E) r s (1, u))
        have e : lev (Ad E) r s (x, x₂ * finGL E s u) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) t) =
            lev (Ad E) r s (x, x₂) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) t) *
              finGL E (r + s) (t⁻¹ * lev (Af E) r s (1, u) * t) := by
          rw [h1, map_mul, map_mul, map_inv]
          simp only [mul_assoc]
          rw [← mul_assoc (finGL E (r + s) (lev (Af E) r s (1, u))), ← hc]
          group
        show φ.1 _ = φ.1 _
        rw [e, hT.1 _ (Kf_right hN ht hu)]
      · have hw := typeB_lt hT (lev (Ad E) r s (x, x₂) * finGL E (r + s) t)
        have hW₂ := Wf_right (W := W) hN hw k
        convert hW₂ using 1
        funext k₂
        show φ.1 _ = _
        have h1 : lev (Ad E) r s (x, x₂ * infGL E s (Unitary.toUnits k₂)) =
            lev (Ad E) r s (x, x₂) * infGL E (r + s) (lev (Cinf E) r s (1, Unitary.toUnits k₂)) := by
          rw [← Slice2.lev_infGL_one, ← map_mul, Prod.mk_mul_mk, mul_one]
        rw [h1]
        simp only [map_mul, Slice2.toUnits_levK]
        rw [infGL_comm (Unitary.toUnits k) t]
        simp only [← mul_assoc]
        rw [mul_assoc (lev (Ad E) r s (x, x₂)) (infGL E (r + s) (lev (Cinf E) r s (1, Unitary.toUnits k₂))),
          infGL_comm (lev (Cinf E) r s (1, Unitary.toUnits k₂)) t, ← mul_assoc]
    have inj : ∀ φ ∈ X, (∀ t ∈ T, ∀ k ∈ S, ∀ m : GA E r × GA E s,
        φ.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) t)) = 0) → φ = 0 := by
      intro φ hφ h0
      have hT := typeB_of_mem_typSp hφ
      refine Subtype.ext (funext fun g => ?_)
      obtain ⟨x, m, t, k, l, ht, hl, hg⟩ := Tset_spec (isOpen_Kf hK (r + s)) g
      have hw := hT.2 (lev (Ad E) r s m * finGL E (r + s) t)
      have hz := hS _ hw (fun κ hκ => by
        show φ.1 (lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)) = 0
        rw [mul_assoc, ← infGL_comm]
        exact h0 t ht κ hκ m)
      have e : g = unip x * (lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k)) *
          finGL E (r + s) l := by
        rw [hg]
        simp only [mul_assoc]
      show φ.1 g = 0
      rw [e, hT.1 l hl, (hI φ hφ).1]
      exact congrFun hz k
    let f : X →ₗ[ℂ] (↥T × ↥S → Y) :=
      { toFun := fun φ p => ⟨fun m => φ.1.1 (lev (Ad E) r s m *
            (infGL E (r + s) (Unitary.toUnits p.2.1) * finGL E (r + s) p.1.1)),
          key φ.1 φ.2 p.1.1 p.1.2 p.2.1⟩
        map_add' := fun φ ψ => funext fun p => Subtype.ext (funext fun m => rfl)
        map_smul' := fun c φ => funext fun p => Subtype.ext (funext fun m => rfl) }
    refine FiniteDimensional.of_injective f ?_
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro φ hφ
    have h0 := inj φ.1 φ.2 fun t ht k hk m => by
      have := congrArg (fun F => (F (⟨t, ht⟩, ⟨k, hk⟩)).1 m) hφ
      exact this
    exact Subtype.ext h0

theorem fd_typSp (hA : AdmDisc) {N : ℕ} (t : Tr E N) (ht : t.Disc) (K : Subgroup (GL (Fin N) (Af E)))
    (hK : IsOpen (K : Set (GL (Fin N) (Af E)))) (W : Submodule ℂ (Kinf E N → ℂ)) [FiniteDimensional ℂ W] :
    FiniteDimensional ℂ (TypSp K W t.space) := by
  have := finiteDimensional_type_space_of_disc hA K hK W t le_rfl ht
  refine Submodule.finiteDimensional_of_le (S₂ := TypSp (Kf N K N) (Wf N W N) t.space) (Submodule.span_le.2 ?_)
  rintro φ ⟨hφ, hT⟩
  exact Submodule.subset_span ⟨hφ, fun u hu g => hT.1 u (Kf_top hu) g, fun g => lt_le_Wf (typeB_lt hT g)⟩

end PositivityTheory.Rg.BcB.SpectralAccumulation.LV

end
