import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullOmApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullPbD
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullHomForm
open UpperTheory.V.Lit.Geo UpperTheory.V.Lit
open scoped ContDiff

private theorem hom_congr_on {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {Y : Set V} {W : V → V} (hW : IsField Y W) {q : ℕ} {w w' : V → V [⋀^Fin (q + 1)]→L[ℝ] F}
    (h : ∀ x ∈ Y, w x = w' x) {p : V} (hp : p ∈ Y) : hom W w p = hom W w' p := by
  unfold hom
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  simp only [hk]
  rw [h _ (hW.2 p hp t ht)]

private theorem om_ext {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ}
    {G : Dr.Geo Γ V S d} {q : ℕ} {w w' : G.Om q} (h : ∀ s, ∀ p ∈ G.Y, w.1 s p = w'.1 s p) : w = w' := by
  refine Subtype.ext (funext fun s => funext fun p => ?_)
  by_cases hp : p ∈ G.Y
  · exact h s p hp
  · rw [(w.2 s).2 p hp, (w'.2 s).2 p hp]

private theorem extDeriv_congr_on {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {Y : Set V} (hY : IsOpen Y) {q : ℕ} {w w' : V → V [⋀^Fin q]→L[ℝ] F}
    (h : ∀ x ∈ Y, w x = w' x) {p : V} (hp : p ∈ Y) : extDeriv w p = extDeriv w' p := by
  have hev : w =ᶠ[nhds p] w' := by
    filter_upwards [hY.mem_nhds hp] with y hy using h y hy
  exact hev.extDeriv_eq

theorem UpperTheory.V.Lit.Geo.omHom :
    OmHom := by
  intro Γ V S _ _ _ _ d G W hW
  have hA := omApply Γ V S d G W hW
  have h1 : ∀ s, ∀ p ∈ G.Y, flow (W s) 1 p ∈ G.Y := fun s p hp =>
    (hW.field s).2 p hp 1 ⟨zero_le_one, le_rfl⟩
  refine ⟨fun q w => om_ext fun s p hp => ?_, fun q w => om_ext fun s p hp => ?_,
    fun w => om_ext fun s p hp => ?_, fun q w => om_ext fun s p hp => ?_⟩
  · have hH : ContDiffAt ℝ ∞ (flow (W s) 1) p :=
      contDiffAt_id.add (((hW.field s).1.contDiffAt (G.isOpen.mem_nhds hp)).const_smul (1 : ℝ))
    rw [G.dOm_apply _ s hp, (hA (q + 1)).1 _ s p hp,
      extDeriv_congr_on G.isOpen ((hA q).1 w s) hp,
      (pbD V V (Fin d → ℂ) q (flow (W s) 1) (w.1 s) p hH (Dr.Geo.contDiffAt_Om w s (h1 s p hp))).2]
    unfold pb
    rw [G.dOm_apply w s (h1 s p hp)]
  · rw [G.dOm_apply _ s hp, extDeriv_congr_on G.isOpen (fun x hx => G.dOm_apply w s hx) hp]
    exact extDeriv_extDeriv_apply (Dr.Geo.contDiffAt_Om w s hp) (by
      rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)
  · change (pbOm G W w).1 s p - w.1 s p = _
    rw [(hA 0).1 w s p hp, (hA 0).2 _ s p hp,
      hom_congr_on (hW.field s) (fun x hx => G.dOm_apply w s hx) hp]
    exact (homForm V (Fin d → ℂ) G.Y G.isOpen (W s) (hW.field s) p hp).1 _ (w.2 s).1
  · change (pbOm G W w).1 s p - w.1 s p =
      (G.dOm q (homOm G W w)).1 s p + (homOm G W (G.dOm (q + 1) w)).1 s p
    rw [(hA (q + 1)).1 w s p hp, (hA (q + 1)).2 _ s p hp, G.dOm_apply _ s hp,
      extDeriv_congr_on G.isOpen ((hA q).2 w s) hp,
      hom_congr_on (hW.field s) (fun x hx => G.dOm_apply w s hx) hp]
    exact (homForm V (Fin d → ℂ) G.Y G.isOpen (W s) (hW.field s) p hp).2 q _ (w.2 s).1
