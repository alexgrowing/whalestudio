import Formalism.SharpRestriction.GrowthBounds.ChartComparison.LocCore

noncomputable section

namespace Formalism.MainNotions.G.ChF

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {i : ℕ} (hi : i + 1 ≤ D.R.m)
  {Uloc : ∀ v : HeightOneSpectrum (𝓞 D.host.F),
    Subgroup (GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F))}
  {ψ : awayG D.sp.cm.sig (D.sp.X (i + 1)).gram Uloc (D.what₂.places.resChar w) →* (D.gat u w hg).Oˣ}
  {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (S : StepLevel D.host.F D.host.E (sigD D) (gramN D (i + 1) hi) T D.R.f bad)

set_option maxHeartbeats 4000000 in

theorem chiUnit_of (hU : SameUlocJ hi S Uloc) (e : D.what₂.LL →+* (D.gat u w hg).Kf) (hψ : UnitCharacterChartCompatibility hi S e ψ)
    (hbad : ∀ w' ∈ bad, ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∉ w'.asIdeal)
    (hR0 : ∀ x, x ∈ intW D.what₂.places w ↔ e x ∈ Set.range (algebraMap (D.gat u w hg).O (D.gat u w hg).Kf)) (κ : S.U) :
    ∃ r ∈ intW D.what₂.places w, r⁻¹ ∈ intW D.what₂.places w ∧ D.what₂.embLL r = (S.chi κ : ℂ) := by
  have hκU := (S.U_eq κ.1).1 κ.2
  obtain ⟨y, hy⟩ : ∃ y : UPts (sigD D) (gramN D (i + 1) hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F), y.1 = κ.1 := ⟨⟨κ.1, hκU.1⟩, rfl⟩
  obtain ⟨y', hover, hoff⟩ : ∃ y' : UPts (sigD D) (gramN D (i + 1) hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      (∀ v : HeightOneSpectrum (𝓞 D.host.F), ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal →
        bc (prV (E := D.host.E) v) y'.1 = 1) ∧
      (∀ v : HeightOneSpectrum (𝓞 D.host.F), ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal →
        bc (prV (E := D.host.E) v) y'.1 = bc (prV (E := D.host.E) v) κ.1) :=
    ⟨trivG (sigD D) (gramN D (i + 1) hi) (D.what₂.places.resChar w) y,
      fun v hv => trivG_over (sigD D) (gramN D (i + 1) hi) (D.what₂.places.resChar w) y v hv,
      fun v hv => by rw [← hy]; exact trivG_off (sigD D) (gramN D (i + 1) hi) (D.what₂.places.resChar w) y v hv⟩
  have hy'U : y'.1 ∈ S.U := (S.U_eq _).2 ⟨y'.2, fun v => by
    by_cases hv : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal
    · rw [hover v hv]; exact Subgroup.one_mem _
    · rw [hoff v hv]; exact hκU.2 v⟩
  have hchi : S.chi κ = S.chi ⟨y'.1, hy'U⟩ := by
    have h1 : S.chi (κ⁻¹ * ⟨y'.1, hy'U⟩) = 1 := S.chi_triv _ (fun v hv => by
      show bc (prV (E := D.host.E) v) (κ.1⁻¹ * y'.1) = 1
      rw [map_mul, map_inv, hoff v (hbad v hv)]
      exact inv_mul_cancel _)
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1
  have ha : (reGL (rankN D (i + 1) hi) _).symm y'.1 ∈
      awayG D.sp.cm.sig (D.sp.X (i + 1)).gram Uloc (D.what₂.places.resChar w) := by
    refine (mem_awayG _ _ _ _ _).2 ⟨reGL_symm_mem_UPts (rankN D (i + 1) hi) D.sp.cm.sig (D.sp.X (i + 1)).gram _
      (gramN_apply D (i + 1) hi) _ _ y'.2, fun v _ => ?_⟩
    have h2 : bc (prV (E := D.host.E) v) y'.1 ∈ S.Uloc v := ((S.U_eq _).1 hy'U).2 v
    rw [hU v] at h2
    obtain ⟨b, hb, hbe⟩ := Subgroup.mem_map.1 h2
    have e1 : bc (prV (E := D.host.E) v) ((reGL (rankN D (i + 1) hi) _).symm y'.1) = b := by
      apply (reGL (rankN D (i + 1) hi) _).injective
      rw [← bc_reGL, MulEquiv.apply_symm_apply]
      exact hbe.symm
    rw [e1]
    exact hb
  obtain ⟨r, hr, hr1⟩ := hψ ⟨_, ha⟩ ⟨y'.1, hy'U⟩ (fun v hv => hover v hv) (fun w' _ => by rw [MulEquiv.apply_symm_apply])
  have h3 : algebraMap (D.gat u w hg).O (D.gat u w hg).Kf ((ψ ⟨_, ha⟩ : (D.gat u w hg).Oˣ) : (D.gat u w hg).O) *
      algebraMap (D.gat u w hg).O (D.gat u w hg).Kf (((ψ ⟨_, ha⟩)⁻¹ : (D.gat u w hg).Oˣ) : (D.gat u w hg).O) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hne := left_ne_zero_of_mul_eq_one hr1
  have h4 : algebraMap (D.gat u w hg).O (D.gat u w hg).Kf ((ψ ⟨_, ha⟩ : (D.gat u w hg).Oˣ) : (D.gat u w hg).O) = e r⁻¹ := by
    rw [map_inv₀]
    exact (inv_eq_of_mul_eq_one_left hr1).symm
  exact ⟨r, (hR0 r).2 ⟨_, (mul_left_cancel₀ hne (hr1.trans h3.symm)).symm⟩, (hR0 r⁻¹).2 ⟨_, h4⟩, by rw [hr, hchi]⟩

end Formalism.MainNotions.G.ChF

end
