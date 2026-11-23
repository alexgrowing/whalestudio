import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassTwistNeg
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil

namespace PositivityTheory.RgGu.NR

namespace ConjDual

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem irrAdm' : GlobalTheory.Published.IrreducibleAdmissibleGL := by
  intro k _ _ _ _ n V _ _ π hs hi
  exact GlobalTheory.CompanionTheory.SmGLBridge.irreducibleAdmissible k (Fin n) V π hs hi

theorem conj_chi (n : ℕ) (s : ℝ) (g : GL (Fin n) k) :
    starRingEnd ℂ ((detChar (Fin n) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) =
      ((detChar (Fin n) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) := by
  simp only [detChar, absPow, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_toHomUnits,
    MonoidHom.coe_mk, OneHom.coe_mk]
  rw [← Complex.ofReal_cpow (GlobalTheory.SmGL.nabs_pos' k _).le, Complex.conj_ofReal]

end ConjDual

open ConjDual in
theorem conjDual (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    ConjDual k := by
  intro n V _ _ ρ hs hi hu s
  obtain ⟨B, -, hBpos, hBinv⟩ := hu
  have hinv : ∀ (g : GL (Fin n) k) (w : V), ρ g (ρ g⁻¹ w) = w := by
    intro g w
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  let L : V → Module.Dual ℂ V := fun v =>
    { toFun := fun w => B w v
      map_add' := by intro a b; simp
      map_smul' := by intro c a; simp }
  have hL : ∀ v w, L v w = B w v := fun v w => rfl
  have hmem : ∀ v, L v ∈ smoothPart ρ.dual := by
    intro v
    apply GlobalTheory.SmGL.mem_smoothPart_of_nhds
    apply Filter.mem_of_superset ((hs v).mem_nhds (by simp))
    intro g hg
    simp only [Set.mem_setOf_eq] at hg ⊢
    have hv' : ρ g⁻¹ v = v := by
      conv_lhs => rw [← hg]
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    ext w
    rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, hL, hL]
    rw [← hBinv g⁻¹ w v, hv']
  let φ : V →ₗ⋆[ℂ] smoothPart ρ.dual :=
    { toFun := fun v => ⟨L v, hmem v⟩
      map_add' := by
        intro a b
        ext w
        simp [hL]
      map_smul' := by
        intro c a
        ext w
        simp [hL] }
  have hφ : ∀ v w, (φ v : Module.Dual ℂ V) w = B w v := fun v w => rfl
  have hint : ∀ (g : GL (Fin n) k) (v : V), φ (ρ g v) = contra ρ g (φ v) := by
    intro g v
    ext w
    rw [contra_apply, hφ, hφ, ← hBinv g (ρ g⁻¹ w) v, hinv]
  refine ⟨φ, ⟨?_, ?_⟩, fun g v => ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra hne
    have h0 := hBpos v hne
    have : B v v = 0 := by
      rw [← hφ, hv]
      rfl
    rw [this] at h0
    simp at h0
  · have hadm := irrAdm' k n V ρ hs hi
    have hbasis : ∀ U ∈ nhds (1 : GL (Fin n) k), ∃ K : Subgroup (GL (Fin n) k),
        IsOpen (K : Set (GL (Fin n) k)) ∧ IsCompact (K : Set (GL (Fin n) k)) ∧ (K : Set (GL (Fin n) k)) ⊆ U := by
      intro U hU
      obtain ⟨J, hJo, hJU, hJK, -⟩ := GlobalTheory.SmGL.exists_open_normalised_subgroup_subset k (Fin n) U hU
      exact ⟨J, hJo, GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen hJo)
        (fun x hx => hJK hx), hJU⟩
    have hci := GlobalTheory.ContraRefl.contra_isIrreducible hbasis hadm hi
    let S : Subrepresentation (contra ρ) :=
      ⟨LinearMap.range φ, by
        rintro g x ⟨v, rfl⟩
        exact ⟨ρ g v, hint g v⟩⟩
    haveI := GlobalTheory.SmGL.nontrivial_of_irreducible hi
    rcases eq_bot_or_eq_top S with h | h
    · exfalso
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      have hm : φ v ∈ S.toSubmodule := LinearMap.mem_range_self φ v
      rw [h] at hm
      have hz : φ v = 0 := (Submodule.mem_bot ℂ).1 hm
      have h0 := hBpos v hv
      have : B v v = 0 := by
        rw [← hφ, hz]
        rfl
      rw [this] at h0
      simp at h0
    · have hr : LinearMap.range φ = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact LinearMap.range_eq_top.1 hr
  · rw [twist_apply, twist_apply, map_smulₛₗ, conj_chi, hint]

end PositivityTheory.RgGu.NR

end
