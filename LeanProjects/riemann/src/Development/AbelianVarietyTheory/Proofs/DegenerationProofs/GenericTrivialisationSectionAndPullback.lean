import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsHomOpenPart
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {H : LB M.Z} {d : H.ι → Ω}

theorem GenTriv.exists_sec_hasVal (h : M.GenTriv H d) (x : Ω) (hx : ∀ k, ∀ z ∈ H.U k, x / d k ∈ M.O z) :
    ∃ σ : H.Sec, M.HasVal d σ x := by
  have hf : ∀ k, ∃ f : Γ(M.Z, H.U k), (H.U k : Set M.Z).Nonempty → valF M.pt (H.U k) f = x / d k := fun k => by
    by_cases hk : (H.U k : Set M.Z).Nonempty
    · obtain ⟨f, hf⟩ := (mem_ringOn_iff_exists hk).1 (mem_ringOn.2 (hx k))
      exact ⟨f, fun _ => hf⟩
    · exact ⟨0, fun h => (hk h).elim⟩
  choose f hf using hf
  refine ⟨⟨f, fun i j => ?_⟩, hf⟩
  by_cases hij : ((H.U i ⊓ H.U j : M.Z.Opens) : Set M.Z).Nonempty
  · refine M.res_injective _ hij ?_
    have h1 := (M.res_apply _ hij _).trans ((M.valF_resG inf_le_left hij (f i)).trans
      (hf i (hij.mono (fun _ hz => hz.1))))
    have h2 := (M.res_apply _ hij _).trans ((M.valF_resG inf_le_right hij (f j)).trans
      (hf j (hij.mono (fun _ hz => hz.2))))
    have h3 := (M.res_apply _ hij _).trans (h.g_eq i j hij)
    rw [map_mul, h3]
    refine h1.trans (Eq.trans ?_ (congrArg (d j / d i * ·) h2.symm))
    have := h.ne i
    have := h.ne j
    field_simp
  · have e : (H.U i ⊓ H.U j : M.Z.Opens) = ⊥ :=
      SetLike.coe_injective (Set.not_nonempty_iff_eq_empty.1 hij)
    have : Subsingleton Γ(M.Z, H.U i ⊓ H.U j) := by
      rw [e]; infer_instance
    exact Subsingleton.elim _ _

theorem GenTriv.pull (h : M.GenTriv H d) {Ω' : Type} [Field Ω'] [Algebra o Ω'] {φ : Ω →ₐ[o] Ω'}
    {N : RatModel o Ω'} {a : N.Z ⟶ M.Z} (ha : M.IsHom N φ a) :
    N.GenTriv (H.pull a) fun k => φ (d (k PUnit.unit)) := by
  refine ⟨fun k => (map_ne_zero φ).2 (h.ne _), fun k k' hk => ?_⟩
  have hle : (H.pull a).U k ⊓ (H.pull a).U k' ≤ a ⁻¹ᵁ (H.U (k PUnit.unit) ⊓ H.U (k' PUnit.unit)) :=
    le_inf (inf_le_left.trans (LB.wchart_le H (fun _ => a) k PUnit.unit))
      (inf_le_right.trans (LB.wchart_le H (fun _ => a) k' PUnit.unit))
  have hne : ((H.U (k PUnit.unit) ⊓ H.U (k' PUnit.unit) : M.Z.Opens) : Set M.Z).Nonempty := by
    obtain ⟨z, hz⟩ := hk
    exact ⟨a z, hle hz⟩
  have e : ((H.pull a).g k k' : Γ(N.Z, (H.pull a).U k ⊓ (H.pull a).U k')) =
      resG N.Z hle (a.app _ (H.g (k PUnit.unit) (k' PUnit.unit) : Γ(M.Z, _))) := by
    have e0 : (H.pull a).g k k' = Semi.res hle (pullU a _ (H.g (k PUnit.unit) (k' PUnit.unit))) :=
      (Fintype.prod_unique (ι := PUnit) fun _ =>
        Semi.res hle (pullU a _ (H.g (k PUnit.unit) (k' PUnit.unit))) ^ (1 : ℤ)).trans (zpow_one _)
    exact congrArg Units.val e0
  rw [e, N.valF_resG hle hk, ha.valF_app hne, h.g_eq _ _ hne, map_div₀]

theorem genTriv_sec_and_pull : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (H : LB M.Z)
    (d : H.ι → Ω), M.GenTriv H d →
    (∀ x : Ω, (∀ k, ∀ z ∈ H.U k, x / d k ∈ M.O z) → ∃ σ : H.Sec, M.HasVal d σ x) ∧
    ∀ (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') (N : RatModel o Ω') (a : N.Z ⟶ M.Z),
      M.IsHom N φ a → N.GenTriv (H.pull a) fun k => φ (d (k PUnit.unit)) :=
  fun _ _ _ _ _ _ _ _ h => ⟨h.exists_sec_hasVal, fun _ _ _ _ _ _ ha => h.pull ha⟩

end GlobalTheory.ZH.RatModel
end
