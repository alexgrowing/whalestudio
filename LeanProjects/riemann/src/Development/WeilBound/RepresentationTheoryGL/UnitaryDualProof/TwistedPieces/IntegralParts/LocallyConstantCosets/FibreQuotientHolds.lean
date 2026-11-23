import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.LocallyConstantCosets.ExistsLiftOfLatticeAverage
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.LocallyConstantCosets.Imports

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil
open scoped Pointwise

namespace PositivityTheory.RgUd.TP.Nil.Fib2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Nil PositivityTheory.RgUd.TP.Nil.Fib1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

theorem lemB (hZ : CR Z) {ζ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (hg : Good Z ζ) {L : AddSubgroup (Matrix (Fin n) (Fin n) k)}
    (hL : IsLat Z L) {t : kˣ} (ht : nabs k t < 1)
    (h0 : ∀ h ∈ supportedIn (UU : Set (Sp k n)), ∀ f ∈ supportedIn (UU : Set (Sp k n)),
      (∀ p ∈ OO Z, f p = psi Z (L : Set (Matrix (Fin n) (Fin n) k)) h p) → ζ f = 0) :
    ∀ F ∈ supportedIn (UU : Set (Sp k n)), ζ F = 0 := by
  classical
  intro F hFm
  obtain ⟨j, S, hSZ, hF⟩ := dec hZ hL ht hFm
  have hM : IsLat Z (((t ^ j : kˣ) : k) • L) := isLat_smul hL (t ^ j)
  have hML : ((t ^ j : kˣ) : k) • L ≤ L := lat_smul_le hL ht j
  have hex : ∀ c, c ∈ S → ∃ g ∈ supportedIn (UU : Set (Sp k n)), ∀ p ∈ OO Z,
      g p = psi Z ((((t ^ j : kˣ) : k) • L : AddSubgroup _) : Set (Matrix (Fin n) (Fin n) k))
        (fun q => F (tr c q)) p := fun c _ => exists_lift_of_lattice_average hZ hM (tr_mem hFm c)
  choose! g hgm hge using hex
  have hz : ∀ c ∈ S, ζ (g c) = 0 := by
    intro c hc
    obtain ⟨fL, hfL, efL⟩ := exists_lift_of_lattice_average hZ hL (tr_mem hFm c)
    have e := ind hZ hg hL hM hML (tr_mem hFm c) hfL (hgm c hc) efL (hge c hc)
    rw [h0 _ (tr_mem hFm c) fL hfL efL] at e
    have hne : ((((t ^ j : kˣ) : k) • L).relIndex L : ℂ) ≠ 0 := by
      exact_mod_cast lat_index_pos hL hM hML
    exact ((mul_eq_zero.1 e.symm).resolve_left hne)
  let G : Sp k n → ℂ := ∑ c ∈ S, fun p => g c (tr (-c) p)
  have hGm : G ∈ supportedIn (UU : Set (Sp k n)) := Submodule.sum_mem _ fun c hc => tr_mem (hgm c hc) _
  have e1 : ζ F = ζ G := by
    refine agree hg.2 hFm hGm fun p hp => ?_
    rw [hF p hp]
    simp only [G, Finset.sum_apply]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hcZ : -c ∈ Z := Z.neg_mem (hSZ c hc)
    rw [hge c hc _ (tr_OO hZ hcZ hp)]
    have := congrFun (psi_tr hZ ((((t ^ j : kˣ) : k) • L : AddSubgroup _) : Set (Matrix (Fin n) (Fin n) k))
      (fun q => F (tr c q)) hcZ) p
    rw [this]
    congr 2
    funext a
    rw [sub_neg_eq_add]
  rw [e1, map_sum]
  refine Finset.sum_eq_zero fun c hc => ?_
  rw [good_tr hg (Z.neg_mem (hSZ c hc)) (hgm c hc)]
  exact hz c hc

theorem good_sub {ζ ζ' : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (h : Good Z ζ) (h' : Good Z ζ') : Good Z (ζ - ζ') :=
  ⟨fun z hz f hf => by simp [h.1 z hz f hf, h'.1 z hz f hf],
    fun f hf h0 => by simp [h.2 f hf h0, h'.2 f hf h0]⟩

theorem good_smul {ζ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (h : Good Z ζ) (c : ℂ) : Good Z (c • ζ) :=
  ⟨fun z hz f hf => by simp [h.1 z hz f hf], fun f hf h0 => by simp [h.2 f hf h0]⟩

theorem good_pull (hZ : CR Z) {ζ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (h : Good Z ζ) (t : kˣ) : Good Z (pullH t ζ) := by
  refine ⟨fun z hz f hf => ?_, fun f hf h0 => ?_⟩
  · show ζ (fun p => f ((t : k) • p.1 + z, p.2)) = ζ (fun p => f ((t : k) • p.1, p.2))
    have hz' : ((t⁻¹ : kˣ) : k) • z ∈ Z := Z.smul_mem hz _
    have hf' : (fun p : Sp k n => f ((t : k) • p.1, p.2)) ∈ supportedIn (Set.univ : Set (Sp k n)) :=
      comp_mem_univ (e := homH t) hf
    have := h.1 _ hz' _ hf'
    rw [← this]
    congr 1
    funext p
    congr 2
    rw [smul_add, smul_smul, Units.mul_inv, one_smul]
  · show ζ (fun p => f (hom t p)) = 0
    refine h.2 _ (hom_mem hf t) fun p hp => h0 _ ⟨(cc_smul hZ (t : k) hp.1).1, Set.mem_univ _⟩

theorem polyH_nil (t : kˣ) (ζ : (Sp k n → ℂ) →ₗ[ℂ] ℂ) : polyH t [] ζ = ζ := by
  simp [polyH]

theorem polyH_cons (t : kˣ) (x : ℝ) (a : List ℝ) (ζ : (Sp k n → ℂ) →ₗ[ℂ] ℂ) :
    polyH t (x :: a) ζ = pullH t (polyH t a ζ) - ((((nabs k t)⁻¹ : ℝ) ^ x : ℝ) : ℂ) • polyH t a ζ := by
  simp [polyH, List.map_cons, List.prod_cons, Module.End.mul_apply]

theorem fibre_quotient_holds : FibQ k := by
  classical
  intro n Z hZ η _ hInv hTr hSU
  have hg0 : Good Z η := ⟨hTr, hSU⟩
  obtain ⟨L, hL⟩ := exists_lat Z
  have hlift : ∀ h : supportedIn (UU : Set (Sp k n)), ∃ f ∈ supportedIn (UU : Set (Sp k n)),
      ∀ p ∈ OO Z, f p = psi Z (L : Set (Matrix (Fin n) (Fin n) k)) h p := fun h => exists_lift_of_lattice_average hZ hL h.2
  choose F0 hF0 hF0e using hlift
  have K0 : ∀ (h : supportedIn (UU : Set (Sp k n))) (f : Sp k n → ℂ), f ∈ supportedIn (UU : Set (Sp k n)) →
      (∀ p ∈ OO Z, f p = psi Z (L : Set (Matrix (Fin n) (Fin n) k)) h p) → η (F0 h) = η f :=
    fun h f hf ef => agree hg0.2 (hF0 h) hf fun p hp => by rw [hF0e h p hp, ef p hp]
  let η0 : supportedIn (UU : Set (Sp k n)) →ₗ[ℂ] ℂ :=
    { toFun := fun h => η (F0 h)
      map_add' := fun h h' => by
        rw [K0 (h + h') (F0 h + F0 h') (Submodule.add_mem _ (hF0 h) (hF0 h')) fun p hp => by
          rw [Pi.add_apply, hF0e h p hp, hF0e h' p hp, Submodule.coe_add, psi_add, Pi.add_apply], map_add]
      map_smul' := fun c h => by
        rw [K0 (c • h) (c • F0 h) (Submodule.smul_mem _ c (hF0 h)) fun p hp => by
          rw [Pi.smul_apply, hF0e h p hp, Submodule.coe_smul, psi_smul, Pi.smul_apply], map_smul]
        rfl }
  obtain ⟨η', hη'⟩ := LinearMap.exists_extend η0
  have E0 : ∀ h (hh : h ∈ supportedIn (UU : Set (Sp k n))) (f : Sp k n → ℂ), f ∈ supportedIn (UU : Set (Sp k n)) →
      (∀ p ∈ OO Z, f p = psi Z (L : Set (Matrix (Fin n) (Fin n) k)) h p) → η' h = η f := by
    intro h hh f hf ef
    have := congrArg (fun φ => φ ⟨h, hh⟩) hη'
    simp only [LinearMap.coe_comp, Submodule.coe_subtype, Function.comp_apply] at this
    rw [this]
    exact K0 ⟨h, hh⟩ f hf ef
  refine ⟨η', fun h hh h0 => ?_, fun g hg h hh => ?_, fun t ht a hK => ?_⟩
  ·
    rw [E0 h hh 0 (Submodule.zero_mem _) fun p _ => by rw [psi_zero hZ _ h0], map_zero]
  ·
    have hOO : ∀ p ∈ OO Z, act g p ∈ OO Z := fun p hp => ⟨(cc_conj hZ hg hp.1).1, fun h0 => hp.2 (by
      have := congrArg (fun v => (g⁻¹ : GL (Fin n) k).val *ᵥ v) h0
      simpa [act, Matrix.mulVec_mulVec] using this)⟩
    rw [E0 _ (act_mem hh g) (fun p => F0 ⟨h, hh⟩ (act g p)) (act_mem (hF0 _) g) fun p hp => by
      rw [hF0e _ _ (hOO p hp), ← psi_act hZ _ h hg]]
    rw [hInv g hg _ (supportedIn_mono (Set.subset_univ _) (hF0 _)), E0 h hh (F0 ⟨h, hh⟩) (hF0 _) (hF0e ⟨h, hh⟩)]
  ·
    set N : ℂ := (((nabs k t)⁻¹ ^ Module.finrank k Z : ℝ) : ℂ) with hN
    have hpos : 0 < (nabs k t)⁻¹ := inv_pos.2 (NNReal.coe_pos.mpr MeasureTheory.distribHaarChar_pos)
    have claim : ∀ b : List ℝ, Good Z (polyH t (b.map (· + (Module.finrank k Z : ℝ))) η) ∧
        ∀ h ∈ supportedIn (UU : Set (Sp k n)), ∀ f ∈ supportedIn (UU : Set (Sp k n)),
          (∀ p ∈ OO Z, f p = psi Z (L : Set (Matrix (Fin n) (Fin n) k)) h p) →
          polyH t (b.map (· + (Module.finrank k Z : ℝ))) η f = N ^ b.length * polyH t b η' h := by
      intro b
      induction b with
      | nil =>
        refine ⟨by simpa [polyH_nil] using hg0, fun h hh f hf ef => ?_⟩
        simp only [List.map_nil, polyH_nil, List.length_nil, pow_zero, one_mul]
        exact (E0 h hh f hf ef).symm
      | cons x b ih =>
        obtain ⟨hgb, hb⟩ := ih
        simp only [List.map_cons]
        refine ⟨?_, fun h hh f hf ef => ?_⟩
        · rw [show polyH t ((x + (Module.finrank k Z : ℝ)) :: b.map (· + (Module.finrank k Z : ℝ))) η =
            pullH t _ - _ from polyH_cons t _ _ η]
          exact good_sub (good_pull hZ hgb t) (good_smul hgb _)
        · rw [polyH_cons, polyH_cons, LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.smul_apply,
            LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
          obtain ⟨f', hf', ef'⟩ := exists_lift_of_lattice_average hZ hL (hom_mem hh t)
          have e1 : pullH t (polyH t (b.map (· + (Module.finrank k Z : ℝ))) η) f =
              N * (N ^ b.length * polyH t b η' (fun q => h (hom t q))) := by
            show polyH t (b.map (· + (Module.finrank k Z : ℝ))) η (fun p => f (hom t p)) = _
            rw [scale hZ hgb hL ht hh hf hf' ef ef', hb _ (hom_mem hh t) f' hf' ef']
          rw [e1, hb h hh f hf ef]
          show _ = N ^ (b.length + 1) * (polyH t b η' (fun q => h (hom t q)) - _ * polyH t b η' h)
          have hc : ((((nabs k t)⁻¹ : ℝ) ^ (x + (Module.finrank k Z : ℝ)) : ℝ) : ℂ) =
              ((((nabs k t)⁻¹ : ℝ) ^ x : ℝ) : ℂ) * N := by
            rw [Real.rpow_add hpos, Real.rpow_natCast, hN]; push_cast; ring
          rw [hc]
          ring
    obtain ⟨hgA, hA⟩ := claim a
    refine lemB hZ hgA hL ht fun h hh f hf ef => ?_
    rw [hA h hh f hf ef, hK h hh, mul_zero]

theorem fibQ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : FibQ k :=
  fibre_quotient_holds

end PositivityTheory.RgUd.TP.Nil.Fib2

end
