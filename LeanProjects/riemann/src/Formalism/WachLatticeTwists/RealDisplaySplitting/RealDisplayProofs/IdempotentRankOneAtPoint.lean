import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.ChainWithExtensionOfSplit
import Formalism.WachLatticeTwists.RealDisplaySplitting.RealDisplayProofs.SurjectionOfRankOneIdempotent

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.SF

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.ringDataObjects

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X d G : Type}
  [Fintype d] [DecidableEq d] [Group G] {t : ℕ} {bl : d → Fin (t + 1)} {T : Subalgebra O (X → O)}
  {r₀ : G →* (X → Matrix d d O)} {π : X} {χ₁ ε : G →* Oˣ} {g₀ : G} {eB e₁ s : X → Matrix d d O}
  {D : RingData O X d G t bl}

theorem deltaO_eq (hD : RingDef O T r₀ π χ₁ ε g₀ eB e₁ s D) :
    D.δO = ∏ i ∈ Finset.Ioo 0 t, ((χ₁ g₀ : O) - (χ₁ g₀ : O) * (((ε g₀)⁻¹ ^ i : Oˣ) : O)) := by
  obtain ⟨-, -, -, -, -, hrr, -⟩ := hD
  have h2 : D.δO = ∏ i ∈ Finset.Ioo 0 t,
      ((D.rr 0 : D.X' → O) D.π' - (D.rr i : D.X' → O) D.π') := by
    show ((Pi.evalRingHom (fun _ : D.X' => O) D.π').comp D.T'.val.toRingHom) D.δ = _
    unfold RingData.δ
    rw [map_prod]; rfl
  rw [h2]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Finset.mem_Ioo] at hi
  rw [hrr 0 (by omega), hrr i hi.2]
  simp

theorem rr_act (hD : RingDef O T r₀ π χ₁ ε g₀ eB e₁ s D) (c : Fin (t + 1)) (i : ℕ) (hi : i < t)
    (m : blockRestrictedRepresentationType bl D.ρk c) : D.rr i • m = ((χ₁ g₀ : O) * (((ε g₀)⁻¹ ^ i : Oˣ) : O)) • m := by
  obtain ⟨-, -, -, -, -, hrr, -, -, -, -, hTB, -⟩ := hD
  rw [hTB, hrr i hi]

theorem blk_act (hP : PrimHyp O T r₀ π bl χ₁ ε) (hD : RingDef O T r₀ π χ₁ ε g₀ eB e₁ s D)
    [∀ k, IsScalarTower D.T' D.R' (blockRestrictedRepresentationType bl D.ρk k)] (c : Fin (t + 1)) (hc : c ≠ 0) (g : G)
    (m : blockRestrictedRepresentationType bl D.ρk c) :
    uElt D.r D.χ g • m = ((((ε g) ^ ((c : ℕ) - 1))⁻¹ : Oˣ) : O) • m := by
  obtain ⟨-, -, -, -, hpπ, -, hr, -, -, -, hTB, hχ, -, -, -, -, hρπ, hρk, -⟩ := hD
  obtain ⟨-, -, -, -, hc1, hdiag⟩ := hP
  have hι : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective O _
  have hρr : D.ρπ (D.r g) = r₀ g π := by
    ext i j
    apply hι
    have h := congrFun (congrFun (hρπ (D.r g)) i) j
    rw [hr, hpπ] at h
    exact h
  have hs : Subsingleton {a // bl a = c} :=
    Fintype.card_le_one_iff_subsingleton.mp (le_of_eq (hc1 c hc))
  have hra : D.r g • m = ((χ₁ g : O) * (((ε g)⁻¹ ^ ((c : ℕ) - 1) : Oˣ) : O)) • m := by
    funext i
    show ∑ j, D.ρk c (D.r g) i j • (m j : KO O) =
      ((χ₁ g : O) * (((ε g)⁻¹ ^ ((c : ℕ) - 1) : Oˣ) : O)) • (m i : KO O)
    rw [Fintype.sum_subsingleton _ i, ← hρk, hρr]
    show (r₀ g π i.1 i.1) • (m i : KO O) = _
    rw [hdiag g i.1 (by rw [i.2]; exact hc), i.2]
  have hχinv : ((((D.χ g)⁻¹ : (D.T')ˣ) : D.T') : D.X' → O) D.π' = (((χ₁ g)⁻¹ : Oˣ) : O) := by
    have h1 : (((D.χ g)⁻¹ : (D.T')ˣ) : D.T') * ((D.χ g : (D.T')ˣ) : D.T') = 1 := Units.inv_mul _
    have h2 : ((((D.χ g)⁻¹ : (D.T')ˣ) : D.T') : D.X' → O) D.π' *
        (((D.χ g : (D.T')ˣ) : D.T') : D.X' → O) D.π' = 1 :=
      congrArg (fun f : D.T' => (f : D.X' → O) D.π') h1
    rw [hχ] at h2
    exact Units.eq_inv_of_mul_eq_one_right h2
  show ((((D.χ g)⁻¹ : (D.T')ˣ) : D.T') • D.r g) • m = _
  rw [smul_assoc, hTB, hχinv, hra, smul_smul, ← mul_assoc, Units.inv_mul, one_mul, inv_pow]

theorem idempotent_rank_one_at_point (hI : IdemHyp O T r₀ π bl eB e₁) (hD : RingDef O T r₀ π χ₁ ε g₀ eB e₁ s D) :
    ((D.ρk 0 D.e₁).map (algebraMap O (FractionRing O))).rank = 1 := by
  obtain ⟨-, -, -, -, hpπ, -, -, -, -, -, -, -, -, he1, -, -, hρπ, hρk, -⟩ := hD
  obtain ⟨-, -, -, -, -, -, -, hrk1, -, he1π⟩ := hI
  have h2 : (D.ρk 0 D.e₁).map (algebraMap O (FractionRing O)) =
      ((e₁ π).map (algebraMap O (FractionRing O))).toSquareBlock bl 0 := by
    rw [← hρk]
    ext i j
    have h := congrFun (congrFun (hρπ D.e₁) i.1) j.1
    rw [he1, hpπ] at h
    exact h
  rw [h2, rank_block bl 0 _ (fun a b hab => by
    show algebraMap O (FractionRing O) (e₁ π a b) = 0
    rw [he1π a b hab, map_zero])]
  exact hrk1 π

theorem blk_scalar (D : RingData O X d G t bl) (c : Fin (t + 1)) (hc : Fintype.card {a // bl a = c} = 1) (a : D.R') :
    ∃ y : O, ∀ m : blockRestrictedRepresentationType bl D.ρk c, a • m = y • m := by
  have hs : Subsingleton {a // bl a = c} := Fintype.card_le_one_iff_subsingleton.mp (le_of_eq hc)
  obtain ⟨i0⟩ : Nonempty {a // bl a = c} := Fintype.card_pos_iff.mp (by rw [hc]; norm_num)
  refine ⟨D.ρk c a i0 i0, fun m => funext fun i => ?_⟩
  show ∑ j, D.ρk c a i j • (m j : KO O) = D.ρk c a i0 i0 • (m i : KO O)
  rw [Fintype.sum_subsingleton _ i, hs.elim i i0]

end Formalism.RepresentationBoundsCohomology.SF
