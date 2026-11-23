import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.EUInvApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.OrbMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.ModelG
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.TwistedOrbitalIntegralGL3Formula
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.TauOfRoots
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.IsIntegralOfEv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.StabFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.UnitaryDoubleCosetIndicator
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.FinFacts

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi

namespace UpperTheory.V.Z.Sym.Sig

open Loc Glob

private theorem theta_theta {K : Type} [Field K] {Δ : K} (g : U3 Δ) : theta Δ (theta Δ g) = g := by
  apply Subtype.ext
  change ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).map star).map star = _
  exact Matrix.ext fun i j => by simp

private theorem hasTau_conj {K : Type} [Field K] {Δ τ : K} {δ : U3 Δ} (h : HasTau δ τ) (y : U3 Δ) :
    HasTau (y⁻¹ * δ * theta Δ y) τ := by
  unfold HasTau at h ⊢
  have e : y⁻¹ * δ * theta Δ y * theta Δ (y⁻¹ * δ * theta Δ y) = y⁻¹ * (δ * theta Δ δ) * y := by
    simp only [map_mul, map_inv, theta_theta]
    group
  rw [e, ← h, Submonoid.coe_mul, Submonoid.coe_mul, mul_assoc, Matrix.charpoly_mul_comm, mul_assoc,
    ← Submonoid.coe_mul, mul_inv_cancel, Submonoid.coe_one, mul_one]

private theorem val_unif_lt (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    valuation k (unif k : k) < 1 := by
  rw [GlAx.unif_spec]
  exact uniformizer_lt_one

private theorem uc_relIndex (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) :
    (Uc k m).relIndex (Uo k) ≠ 0 := by
  have h1 := (finFacts k (Lev.deep k m)).1
  have hle : Uc k (m + 1) ≤ Uc k m := by
    intro u hu
    rw [mem_Uc] at hu ⊢
    exact ⟨hu.1, hu.2.trans (GlAx.zpow_le (by push_cast; omega))⟩
  intro h
  apply h1
  have := Subgroup.relIndex_dvd_of_le_left (Uo k) hle
  rw [h, zero_dvd_iff] at this
  exact this

end UpperTheory.V.Z.Sym.Sig

private theorem relIndex_comap_stabilizer_ne_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (V : UpperTheory.V.Z.Sym.Sig.Lev k) {T : Type} [CommGroup T]
    (r : T →* kˣ) (hr : Function.Surjective r) (ι' : T →* GL (Fin 3) k) (g₀ w : GL (Fin 3) k)
    (hι : ∀ s, ι' s = g₀ * UpperTheory.V.Z.Sym.Sig.dg ![r s, 1, (r s)⁻¹] * g₀⁻¹) :
    (Subgroup.comap ι' (MulAction.stabilizer (GL (Fin 3) k)
      ((w : GL (Fin 3) k) : GL (Fin 3) k ⧸ V.J 3))).relIndex (Subgroup.comap r (Uo k)) ≠ 0 := by
  obtain ⟨M, hM⟩ := UpperTheory.V.Z.Sym.Sig.stabFin k V 3 (g₀⁻¹ * w)
  have hle : Subgroup.comap r (Uc k M)
      ≤ Subgroup.comap ι' (MulAction.stabilizer (GL (Fin 3) k) ((w : GL (Fin 3) k) : GL (Fin 3) k ⧸ V.J 3)) := by
    intro s hs
    rw [Subgroup.mem_comap] at hs ⊢
    rw [MulAction.mem_stabilizer_iff]
    change ((ι' s * w : GL (Fin 3) k) : GL (Fin 3) k ⧸ V.J 3) = w
    rw [QuotientGroup.eq]
    have hu : ∀ i, (![r s, 1, (r s)⁻¹] : Fin 3 → kˣ) i ∈ Uc k M := by
      intro i
      fin_cases i
      · exact hs
      · exact one_mem _
      · exact inv_mem hs
    have := inv_mem (hM _ hu)
    rw [hι]
    convert this using 1
    group
  have hidx : (Subgroup.comap r (Uc k M)).relIndex (Subgroup.comap r (Uo k)) ≠ 0 := by
    rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hr]
    exact UpperTheory.V.Z.Sym.Sig.uc_relIndex k M
  intro h0
  apply hidx
  have := Subgroup.relIndex_dvd_of_le_left (Subgroup.comap r (Uo k)) hle
  rw [h0, zero_dvd_iff] at this
  exact this

open ValuativeRel UpperTheory.V.Hi UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob in
theorem UpperTheory.V.Z.Sym.Sig.okGOrb :
    UpperTheory.V.Z.Sym.Sig.OkGOrb := by
  intro k _ _ _ _ O _ _ hO h2 Δ s hs hs0 V Ry hRy χ hχ t ht S τ c d m δ ι Q hD hM
  obtain ⟨hτ, hfix⟩ := (Sig.modelG k O hO h2 Δ s hs hs0).1 τ c d m δ ι Q hD hM
  obtain ⟨-, -, hind⟩ := Sig.okG k O hO h2 Δ s hs hs0 V Ry hRy χ hχ t ht
  by_cases hI : Ind (V.data hs Ry χ).H τ t
  swap
  · have hz : ∀ y : U3 Δ, (V.data hs Ry χ).fG t (y⁻¹ * δ * theta Δ y) = 0 := fun y => by
      by_contra hne
      exact hI (hind _ τ (Sig.hasTau_conj hτ y) hne)
    refine ⟨⟨∅, fun y hy => absurd (hz y) hy⟩, ?_, fun h => absurd h hI⟩
    simp [S, orb, wcount, hz, Glob.one, hI]
  have hI' := hI
  obtain ⟨h, hH, rfl⟩ := hI
  have hva : valuation k ((t * h : kˣ) : k) < 1 := by
    have ht' : valuation k (t : k) < valuation k (unif k : k) ^ 2 := ht
    have hh : valuation k (h : k) = 1 := V.H_le hH
    rw [Units.val_mul, Valuation.map_mul, hh, mul_one]
    exact ht'.trans (pow_lt_one₀ zero_le' (Sig.val_unif_lt k) (by norm_num))
  obtain ⟨g₀, x, y, z, hδ, hxz, hι⟩ := (Sig.modelG k O hO h2 Δ s hs hs0).2 (t * h) hva c d m δ ι Q hD hM
  obtain ⟨hsurj, hC, -⟩ := Sig.roots k O hO (t * h) hva
  obtain ⟨hbij, hcomm, -, -⟩ := Sig.eU_facts k O hO h2 Δ s hs hs0
  have hfinv : ∀ u ∈ V.J 3, ∀ g : GL (Fin 3) k,
      V.unitaryHeckeTestSum Ry t (u⁻¹ * g * Sig.th k 3 u) = V.unitaryHeckeTestSum Ry t g := by
    intro u hu g
    unfold Sig.Lev.unitaryHeckeTestSum
    refine Finset.sum_congr rfl fun e _ => ?_
    exact ((Sig.eqG k V χ Ry Ry t t _).1 u⁻¹ (inv_mem hu) u hu g).1
  have hnorm : (Cint O (((t * h : kˣ) : k) + ((t * h : kˣ)⁻¹ : kˣ))).Normal := Subgroup.normal_of_comm _
  have hOM := Sig.orbMap _ _ _ (Sig.eU hs) hbij ι (Cint O _) (theta Δ) (Sig.th k 3) hcomm (V.J 3)
    (V.unitaryHeckeTestSum Ry t) δ hfinv hfix hnorm
  have hxz1 : valuation k ((x / z : kˣ) : k) < 1 := by
    rw [hxz]
    exact hva
  have hG := Sig.orbital_integral_over_extended_group k V Ry hRy t ht _ _ hsurj g₀ ((Sig.eU hs).comp ι) (fun s => hι s) x y z hxz1
  rw [← hδ, ← hC] at hG
  refine ⟨hOM.2.1.mpr hG.1, hOM.1.trans (hG.2.trans ?_), fun _ yq => ?_⟩
  · have hm : x / z / t ∈ V.H := by
      rw [hxz, mul_div_cancel_left]
      exact hH
    rw [show Glob.one (x / z / t ∈ V.H) = 1 from if_pos hm,
      show Glob.one (Ind S.H (((t * h : kˣ) : k) + ((t * h : kˣ)⁻¹ : kˣ)) t) = 1 from if_pos hI']
    show _ = (((V.H.relIndex (Uo k) : ℝ) * (V.H.relIndex V.H2 : ℝ) : ℝ) : ℂ) * 1
    push_cast
    rfl
  · obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective yq
    have key := relIndex_comap_stabilizer_ne_zero V _ hsurj ((Sig.eU hs).comp ι) g₀ (Sig.eU hs w) (fun s => hι s)
    rw [← hOM.2.2 w, ← hC] at key
    exact key
