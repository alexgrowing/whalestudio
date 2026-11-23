import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalKTypeFiniteStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsOpenIsCompact

noncomputable section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.IrredMod

section Hilbert

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X] {K : Type*} [Group K]

theorem inner_map_map (π : K →* (X →L[ℂ] X)) (hn : ∀ g v, ‖π g v‖ = ‖v‖) (g : K) (v w : X) :
    ⟪π g v, π g w⟫_ℂ = ⟪v, w⟫_ℂ :=
  (⟨(π g : X →ₗ[ℂ] X), hn g⟩ : X →ₗᵢ[ℂ] X).inner_map_map v w

theorem map_map_inv (π : K →* (X →L[ℂ] X)) (g : K) (v : X) : π g (π g⁻¹ v) = v := by
  have : π g * π g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact congrArg (fun S : X →L[ℂ] X => S v) this

theorem orthogonal_stable (π : K →* (X →L[ℂ] X)) (hn : ∀ g v, ‖π g v‖ = ‖v‖) {N : Submodule ℂ X}
    (hN : ∀ g, ∀ v ∈ N, π g v ∈ N) (g : K) {v : X} (hv : v ∈ Nᗮ) : π g v ∈ Nᗮ := by
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro u hu
  rw [← map_map_inv π g u, inner_map_map π hn]
  exact hv _ (hN _ u hu)

theorem starProjection_map (π : K →* (X →L[ℂ] X)) (hn : ∀ g v, ‖π g v‖ = ‖v‖) {N : Submodule ℂ X}
    [N.HasOrthogonalProjection] (hN : ∀ g, ∀ v ∈ N, π g v ∈ N) (g : K) (v : X) :
    N.starProjection (π g v) = π g (N.starProjection v) := by
  refine Submodule.eq_starProjection_of_mem_orthogonal (hN g _ (Submodule.starProjection_apply_mem _ _)) ?_
  rw [← map_sub]
  exact orthogonal_stable π hn hN g (Submodule.sub_starProjection_mem_orthogonal v)

theorem exists_decomp {W : Type*} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ K W)
    (π : K →* (X →L[ℂ] X)) (hn : ∀ g v, ‖π g v‖ = ‖v‖) (P : X → Prop) (Y : Submodule ℂ X) [FiniteDimensional ℂ Y]
    (hY : ∀ g, ∀ v ∈ Y, π g v ∈ Y) (hP : ∀ v ∈ Y, P v) {v : X} (hv : v ∈ Y) :
    ∃ x ∈ Y ⊓ (⨆ (T : W →ₗ[ℂ] X) (_ : (∀ k w, T (ρ k w) = π k (T w)) ∧ ∀ w, P (T w)), LinearMap.range T),
      v - x ∈ (⨆ (T : W →ₗ[ℂ] X) (_ : (∀ k w, T (ρ k w) = π k (T w)) ∧ ∀ w, P (T w)), LinearMap.range T)ᗮ := by
  set M : Submodule ℂ X := ⨆ (T : W →ₗ[ℂ] X) (_ : (∀ k w, T (ρ k w) = π k (T w)) ∧ ∀ w, P (T w)), LinearMap.range T
    with hMdef
  have hmem : ∀ (T : W →ₗ[ℂ] X), ((∀ k w, T (ρ k w) = π k (T w)) ∧ ∀ w, P (T w)) → ∀ w, T w ∈ M :=
    fun T hT w => (le_iSup₂_of_le (f := fun (T : W →ₗ[ℂ] X)
      (_ : (∀ k w, T (ρ k w) = π k (T w)) ∧ ∀ w, P (T w)) => LinearMap.range T) T hT le_rfl) ⟨w, rfl⟩
  have hM : ∀ g, ∀ v ∈ M, π g v ∈ M := by
    intro g v hv
    have : M ≤ M.comap (π g : X →ₗ[ℂ] X) := by
      refine iSup₂_le fun T hT => ?_
      rintro _ ⟨w, rfl⟩
      change π g (T w) ∈ M
      rw [← hT.1]
      exact hmem T hT _
    exact this hv
  set N : Submodule ℂ X := Y ⊓ M with hN
  have hNs : ∀ g, ∀ v ∈ N, π g v ∈ N := fun g v hv => ⟨hY g v hv.1, hM g v hv.2⟩
  haveI : FiniteDimensional ℂ N := Submodule.finiteDimensional_inf_left Y M
  set Y₂ : Submodule ℂ X := Y ⊓ Nᗮ with hY₂
  haveI : FiniteDimensional ℂ Y₂ := Submodule.finiteDimensional_inf_left Y Nᗮ
  have hY₂s : ∀ g, ∀ v ∈ Y₂, π g v ∈ Y₂ := fun g v hv => ⟨hY g v hv.1, orthogonal_stable π hn hNs g hv.2⟩
  have hle : M ≤ Y₂ᗮ := by
    refine iSup₂_le fun T hT => ?_
    rintro _ ⟨w, rfl⟩
    let T' : W →ₗ[ℂ] X := (Y₂.starProjection : X →ₗ[ℂ] X) ∘ₗ T
    have hT' : (∀ k w, T' (ρ k w) = π k (T' w)) ∧ ∀ w, P (T' w) :=
      ⟨fun k w => by
        change Y₂.starProjection (T (ρ k w)) = π k (Y₂.starProjection (T w))
        rw [hT.1, starProjection_map π hn hY₂s], fun w => hP _ (show _ ∈ Y₂ from Submodule.starProjection_apply_mem _ _).1⟩
    have h1 : Y₂.starProjection (T w) ∈ Y₂ := Submodule.starProjection_apply_mem _ _
    have h2 : Y₂.starProjection (T w) ∈ N := ⟨h1.1, hmem T' hT' w⟩
    have h3 : Y₂.starProjection (T w) = 0 := by
      have := (Submodule.mem_orthogonal _ _).1 h1.2 _ h2
      exact inner_self_eq_zero.1 this
    exact (Submodule.starProjection_apply_eq_zero_iff _).1 h3
  refine ⟨N.starProjection v, Submodule.starProjection_apply_mem _ _, ?_⟩
  have h4 : v - N.starProjection v ∈ Y₂ :=
    ⟨Y.sub_mem hv (Submodule.starProjection_apply_mem N v).1, Submodule.sub_starProjection_mem_orthogonal v⟩
  exact Submodule.orthogonal_le hle (Submodule.le_orthogonal_orthogonal _ h4)

theorem exists_average [TopologicalSpace K] [IsTopologicalGroup K] (π : K →* (X →L[ℂ] X)) (hn : ∀ g v, ‖π g v‖ = ‖v‖)
    (U : Subgroup K) (hU : IsCompact (U : Set K)) {F : X} (hF : IsOpen {g | π g F = F}) (A : Submodule ℂ X)
    (hA : ∀ g, ∀ v ∈ A, π g v ∈ A) (hFA : F ∈ A) :
    ∃ F' ∈ A, (∀ u ∈ U, π u F' = F') ∧ ∀ m, (∀ u ∈ U, π u m = m) → ⟪m, F'⟫_ℂ = ⟪m, F⟫_ℂ := by
  classical
  have hfin : ((fun u => π u F) '' (U : Set K)).Finite := by
    obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun u : K => (fun g => u⁻¹ * g) ⁻¹' {g | π g F = F})
      (fun u => hF.preimage (continuous_const.mul continuous_id)) (fun u _ => Set.mem_iUnion.2 ⟨u, show π (u⁻¹ * u) F = F by simp⟩)
    refine (t.image fun u => π u F).finite_toSet.subset ?_
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨s, hs, e⟩ := Set.mem_iUnion₂.1 (ht hu)
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨s, hs, ?_⟩)
    have e' : π (s⁻¹ * u) F = F := e
    change π s F = π u F
    calc π s F = π s (π (s⁻¹ * u) F) := by rw [e']
      _ = π u F := by rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel_left]
  set O := hfin.toFinset with hO
  have hOm : ∀ f, f ∈ O ↔ ∃ u ∈ U, π u F = f := fun f => by simp [hO]
  have hO0 : (O.card : ℂ) ≠ 0 := by
    have : F ∈ O := (hOm F).2 ⟨1, U.one_mem, by simp⟩
    exact Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨F, this⟩)
  refine ⟨(O.card : ℂ)⁻¹ • ∑ f ∈ O, f, A.smul_mem _ (A.sum_mem fun f hf => ?_), fun u hu => ?_, fun m hm => ?_⟩
  · obtain ⟨u, -, rfl⟩ := (hOm f).1 hf
    exact hA u F hFA
  · rw [map_smul, map_sum]
    congr 1
    refine Finset.sum_nbij' (π u) (π u⁻¹) ?_ ?_ ?_ ?_ fun _ _ => rfl
    · intro f hf
      obtain ⟨s, hs, rfl⟩ := (hOm f).1 hf
      exact (hOm _).2 ⟨u * s, U.mul_mem hu hs, by rw [map_mul]; rfl⟩
    · intro f hf
      obtain ⟨s, hs, rfl⟩ := (hOm f).1 hf
      exact (hOm _).2 ⟨u⁻¹ * s, U.mul_mem (U.inv_mem hu) hs, by rw [map_mul]; rfl⟩
    · intro f _
      simpa using map_map_inv π u⁻¹ f
    · intro f _
      exact map_map_inv π u f
  · have h1 : ∀ f ∈ O, ⟪m, f⟫_ℂ = ⟪m, F⟫_ℂ := fun f hf => by
      obtain ⟨s, hs, rfl⟩ := (hOm f).1 hf
      conv_lhs => rw [← hm s hs]
      exact inner_map_map π hn s m F
    rw [inner_smul_right, inner_sum, Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hO0, one_mul]

end Hilbert

section Orbit

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {K : Type*} [Group K]

theorem span_orbit_stable (π : K →* (X →L[ℂ] X)) (F : X) (g : K) :
    ∀ v ∈ Submodule.span ℂ (Set.range fun k => π k F), π g v ∈ Submodule.span ℂ (Set.range fun k => π k F) := by
  intro v hv
  have : Submodule.span ℂ (Set.range fun k => π k F) ≤
      (Submodule.span ℂ (Set.range fun k => π k F)).comap (π g : X →ₗ[ℂ] X) :=
    Submodule.span_le.2 (by
      rintro _ ⟨k, rfl⟩
      exact Submodule.subset_span ⟨g * k, show π (g * k) F = π g (π k F) by rw [map_mul]; rfl⟩)
  exact this hv

def subRep (π : K →* (X →L[ℂ] X)) (Y : Submodule ℂ X) (hY : ∀ g, ∀ v ∈ Y, π g v ∈ Y) : Representation ℂ K Y where
  toFun g := (π g : X →ₗ[ℂ] X).restrict (hY g)
  map_one' := by ext v; simp
  map_mul' g h := by ext v; simp

end Orbit

section Adelic

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
  {μ : Measure (GA E a)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

variable (E a μ) in

def piInf : Kinf E a →* (L2 (latticeGL E a) μ →L[ℂ] L2 (latticeGL E a) μ) :=
  (R (latticeGL E a) μ).comp ((infGL E a).comp Unitary.toUnits)

variable (E a μ) in

def piFin : GL (Fin a) (Af E) →* (L2 (latticeGL E a) μ →L[ℂ] L2 (latticeGL E a) μ) :=
  (R (latticeGL E a) μ).comp (finGL E a)

theorem piFin_piInf (u : GL (Fin a) (Af E)) (k : Kinf E a) (v : L2 (latticeGL E a) μ) :
    piFin E a μ u (piInf E a μ k v) = piInf E a μ k (piFin E a μ u v) := by
  have e := congrArg (fun g => R (latticeGL E a) μ g v) (infGL_comm (E := E) (a := a) (Unitary.toUnits k) u)
  simp only [map_mul, ContinuousLinearMap.mul_apply] at e
  exact e.symm

theorem finiteDimensional_span_inf {φ : Sm E a} (hφ : IsAutForm φ) (h : MemL2Quotient (latticeGL E a) μ φ.1) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : Kinf E a => piInf E a μ k h.toL2)) := by
  have hk := hφ.kfin
  have hm : ∀ ψ ∈ Submodule.span ℂ (Set.range fun k => cptRep E a k φ), MemL2Quotient (latticeGL E a) μ ψ.1 := by
    intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact h.mul_right _
    | zero => exact ⟨fun _ _ _ => rfl, MemLp.zero⟩
    | add x y _ _ hx hy =>
      exact ⟨fun γ hγ g => congrArg₂ (· + ·) (hx.1 γ hγ g) (hy.1 γ hγ g), hx.2.add hy.2⟩
    | smul c x _ hx => exact ⟨fun γ hγ g => congrArg (c • ·) (hx.1 γ hγ g), hx.2.const_smul c⟩
  refine Submodule.finiteDimensional_of_le (S₂ := (⊤ : Submodule ℂ _).map (toL2ₗ μ _ hm)) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  exact ⟨⟨_, Submodule.subset_span ⟨k, rfl⟩⟩, trivial, (right_translate_toL2 h _).symm⟩

def fixedBy (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (U : Subgroup (GL (Fin a) (Af E))) :
    Submodule ℂ (L2 (latticeGL E a) μ) where
  carrier := {v | ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) v = v}
  zero_mem' := fun _ _ => map_zero _
  add_mem' := fun {x y} hx hy u hu => by rw [map_add, hx u hu, hy u hu]
  smul_mem' := fun c x hx u hu => by rw [map_smul, hx u hu]

theorem span_inf_le {H : Submodule ℂ (L2 (latticeGL E a) μ)} (hH : ∀ g, ∀ v ∈ H, R (latticeGL E a) μ g v ∈ H)
    {U : Subgroup (GL (Fin a) (Af E))} {F : L2 (latticeGL E a) μ} (hF : F ∈ H) (hU : F ∈ fixedBy μ U) :
    Submodule.span ℂ (Set.range fun k : Kinf E a => piInf E a μ k F) ≤ H ⊓ fixedBy μ U :=
  Submodule.span_le.2 (by
    rintro _ ⟨k, rfl⟩
    refine ⟨hH _ _ hF, fun u hu => ?_⟩
    exact (piFin_piInf u k F).trans (congrArg (piInf E a μ k) (hU u hu)))

end Adelic

theorem mem_of_toL2_mem : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)), H ≤ L2cusp μ → IsIrredSubrep (R (latticeGL E a) μ) H → ∀ W : Submodule ℂ (Sm E a), IsStable W → (∀ φ ∈ W, IsAutForm φ ∧ ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H) → (classes W μ).topologicalClosure = H → ∀ φ : Sm E a, IsAutForm φ → ∀ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H → φ ∈ W := by
  intro E _ _ _ a μ _ _ H hcusp hirr W hW hWH hcl φ hφ h hH
  have hn : ∀ k v, ‖piInf E a μ k v‖ = ‖v‖ := fun k v => norm_R _ v
  have hnF : ∀ k v, ‖piFin E a μ k v‖ = ‖v‖ := fun k v => norm_R _ v
  have hHs : ∀ g, ∀ v ∈ H, R (latticeGL E a) μ g v ∈ H := hirr.1.2
  have hWm : ∀ ψ ∈ W, MemL2Quotient (latticeGL E a) μ ψ.1 := fun ψ hψ => (hWH ψ hψ).2.choose
  have hWa : ∀ ψ ∈ W, IsAutForm ψ := fun ψ hψ => (hWH ψ hψ).1
  obtain ⟨U₀, hU₀o, hU₀c⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact E a
  let S : Subgroup (GL (Fin a) (Af E)) :=
    { carrier := {k | finRep E a k φ = φ}
      mul_mem' := fun {x y} hx hy => by
        change finRep E a (x * y) φ = φ
        rw [map_mul, Module.End.mul_apply, show finRep E a y φ = φ from hy, show finRep E a x φ = φ from hx]
      one_mem' := by
        change finRep E a 1 φ = φ
        rw [map_one, Module.End.one_apply]
      inv_mem' := fun {x} hx => by
        change finRep E a x⁻¹ φ = φ
        conv_lhs => rw [← show finRep E a x φ = φ from hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hSo : IsOpen (S : Set (GL (Fin a) (Af E))) := hφ.level
  let U : Subgroup (GL (Fin a) (Af E)) := U₀ ⊓ S
  have hUo : IsOpen (U : Set (GL (Fin a) (Af E))) := hU₀o.inter hSo
  have hUc : IsCompact (U : Set (GL (Fin a) (Af E))) := hU₀c.inter_right (S.isClosed_of_isOpen hSo)
  have hfix : h.toL2 ∈ fixedBy μ U := fun u hu =>
    (right_translate_toL2 h _).trans (((h.mul_right _).toL2_eq_iff_ae_eq h).2 (.of_forall fun x => congrFun (congrArg Subtype.val hu.2) x))
  set Y₀ := Submodule.span ℂ (Set.range fun k : Kinf E a => piInf E a μ k h.toL2) with hY₀def
  haveI : FiniteDimensional ℂ Y₀ := finiteDimensional_span_inf hφ h
  have hY₀s : ∀ g, ∀ v ∈ Y₀, piInf E a μ g v ∈ Y₀ := span_orbit_stable _ _
  have hY₀ : Y₀ ≤ H ⊓ fixedBy μ U := span_inf_le hHs hH hfix
  have hF0Y : h.toL2 ∈ Y₀ := Submodule.subset_span ⟨1, by simp⟩
  let ρ : Representation ℂ (Kinf E a) Y₀ := subRep (piInf E a μ) Y₀ hY₀s
  let P : L2 (latticeGL E a) μ → Prop := fun v => v ∈ H ∧ ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) v = v
  let M : Submodule ℂ (L2 (latticeGL E a) μ) :=
    ⨆ (T : Y₀ →ₗ[ℂ] L2 (latticeGL E a) μ) (_ : (∀ k w, T (ρ k w) = piInf E a μ k (T w)) ∧ ∀ w, P (T w)), LinearMap.range T
  haveI hMf : FiniteDimensional ℂ M := GlobalTheory.T.cuspidal_K_type_finite E a μ H hcusp hirr U hUo Y₀ ρ
  have hMP : M ≤ H ⊓ fixedBy μ U := iSup₂_le fun T hT => by
    rintro _ ⟨w, rfl⟩
    exact hT.2 w
  have hF0M : h.toL2 ∈ M :=
    (le_iSup₂_of_le (f := fun (T : Y₀ →ₗ[ℂ] L2 (latticeGL E a) μ)
      (_ : (∀ k w, T (ρ k w) = piInf E a μ k (T w)) ∧ ∀ w, P (T w)) => LinearMap.range T) Y₀.subtype
      ⟨fun k w => rfl, fun w => hY₀ w.2⟩ le_rfl) ⟨⟨_, hF0Y⟩, rfl⟩
  let M' : Submodule ℂ (L2 (latticeGL E a) μ) := M ⊓ classes W μ
  haveI : FiniteDimensional ℂ M' := Submodule.finiteDimensional_inf_left M _
  have hpm : M'.starProjection h.toL2 ∈ M' := Submodule.starProjection_apply_mem _ _
  obtain ⟨m, hmdef⟩ : ∃ m, m = h.toL2 - M'.starProjection h.toL2 := ⟨_, rfl⟩
  have hmM : m ∈ M := hmdef ▸ M.sub_mem hF0M hpm.1
  have hm' : m ∈ M'ᗮ := hmdef ▸ Submodule.sub_starProjection_mem_orthogonal _
  have key : ∀ F ∈ classes W μ, ⟪m, F⟫_ℂ = 0 := by
    intro F hF
    obtain ⟨ψ, rfl⟩ := (range_toL2ₗ hWm).ge hF
    have hi := toL2ₗ_injective hWm fun ψ hψ => ContAut.continuous_of_isOpen_stab E a ψ (hWa ψ hψ).level
    have hop : IsOpen {g | piFin E a μ g (toL2ₗ μ W hWm ψ) = toL2ₗ μ W hWm ψ} := by
      convert (hWa ψ ψ.2).level using 1
      ext k
      exact (R_toL2ₗ hWm ψ (hW (.fin k) _ ψ.2)).congr_left.trans (hi.eq_iff.trans Subtype.ext_iff)
    obtain ⟨F', hF'c, hF'f, hF'i⟩ := exists_average (piFin E a μ) hnF U hUc hop (classes W μ)
      (fun g v hv => R_mem_classes (fun χ hχ => hW (.fin g) χ hχ) hv) hF
    rw [← hF'i m (fun u hu => (hMP hmM).2 u hu)]
    have hF'H : F' ∈ H := by
      have : classes W μ ≤ H := hcl ▸ Submodule.le_topologicalClosure _
      exact this hF'c
    have hF'U : F' ∈ fixedBy μ U := hF'f
    obtain ⟨ψ', rfl⟩ := (range_toL2ₗ hWm).ge hF'c
    haveI := finiteDimensional_span_inf (hWa ψ' ψ'.2) (hWm ψ' ψ'.2)
    obtain ⟨Y₁, hY₁⟩ : ∃ Y₁, Y₁ = Submodule.span ℂ (Set.range fun k : Kinf E a => piInf E a μ k (toL2ₗ μ W hWm ψ')) := ⟨_, rfl⟩
    haveI : FiniteDimensional ℂ Y₁ := hY₁ ▸ this
    have hY₁s : ∀ g, ∀ v ∈ Y₁, piInf E a μ g v ∈ Y₁ := hY₁ ▸ span_orbit_stable _ _
    have hY₁P : Y₁ ≤ H ⊓ fixedBy μ U := hY₁ ▸ span_inf_le hHs hF'H hF'U
    have hY₁c : Y₁ ≤ classes W μ := hY₁ ▸ Submodule.span_le.2 (by
      rintro _ ⟨k, rfl⟩
      exact R_mem_classes (fun χ hχ => hW (.cpt k) χ hχ) hF'c)
    have hFY : toL2ₗ μ W hWm ψ' ∈ Y₁ := hY₁ ▸ Submodule.subset_span ⟨1, by simp⟩
    obtain ⟨x, ⟨hx1, hx2⟩, hx3⟩ := exists_decomp ρ (piInf E a μ) hn P Y₁ hY₁s (fun v hv => hY₁P hv) hFY
    have e1 : ⟪m, x⟫_ℂ = 0 := (Submodule.mem_orthogonal' _ _).1 hm' x ⟨hx2, hY₁c hx1⟩
    have e2 : ⟪m, toL2ₗ μ W hWm ψ' - x⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).1 hx3 m hmM
    rw [inner_sub_right, e1, sub_zero] at e2
    exact e2
  have hm0 : m = 0 := by
    have h1 : m ∈ (classes W μ)ᗮ := (Submodule.mem_orthogonal' _ _).2 key
    rw [← Submodule.orthogonal_closure, hcl] at h1
    exact inner_self_eq_zero.1 ((Submodule.mem_orthogonal' _ _).1 h1 m (hMP hmM).1)
  have hF0c : h.toL2 ∈ classes W μ := by
    have h1 : h.toL2 = M'.starProjection h.toL2 := sub_eq_zero.1 (hmdef.symm.trans hm0)
    rw [h1]
    exact hpm.2
  obtain ⟨ψ, hψ, e⟩ := hF0c
  rwa [show φ = ψ from Subtype.ext ((Continuous.ae_eq_iff_eq μ (ContAut.continuous_of_isOpen_stab E a φ hφ.level)
    (ContAut.continuous_of_isOpen_stab E a ψ (hWa ψ hψ).level)).1 (h.lift_toL2_ae_eq.symm.trans e))]

end GlobalTheory.CompanionTheory.IrredMod

end
