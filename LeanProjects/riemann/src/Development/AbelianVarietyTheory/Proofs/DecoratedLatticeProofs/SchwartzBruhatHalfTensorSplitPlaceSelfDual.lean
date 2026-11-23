import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorOneApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatTensorHalfAddPlaceIdempotent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNatMulSplitHalfLatticeCoordinatesIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulMemHomLatticeOfIntegralFrameCoords
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmVacuumEqSplitFacSmulSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.TensorLatO

theorem isSBHalf_tensorAt_of_bounds {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : Place D k) {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y']
    [DecidableEq Y'] (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (L : AddSubgroup (WO S T))
    (e : AE D) (he : e * p.e = 0) (hMap : ∀ u ∈ L, u.map (fun a => p.e * a) ∈ L)
    (A B : ℕ) (hA : 0 < A) (hB : 0 < B)
    (hAL : ∀ X : Matrix Y Y' k, (∀ r q, X r q ∈ 𝒪[k]) → A • p.up FS FT X ∈ L)
    (hBL : ∀ u ∈ L, ∀ r q, (B : k) * p.down FS FT u r q ∈ 𝒪[k])
    (Φ : WO S T → ℂ) (hΦ : IsSBHalf e L Φ) (Ψ : Matrix Y Y' k → ℂ) (hΨ : Ψ ∈ SB (Matrix Y Y' k)) :
    IsSBHalf (e + p.e) L (p.tensorAt FS FT Φ Ψ) := by
  classical
  unfold IsSBHalf at hΦ ⊢
  obtain ⟨hΦs, kΦ, hkΦ, hΦi, hΦl⟩ := hΦ
  obtain ⟨N, hN, hΨi, hΨl⟩ := GlobalTheory.SBUnif.uniform k Y Y' Ψ hΨ
  have hud : ∀ u : WO S T, p.up FS FT (p.down FS FT u) = u.map (fun a => p.e * a) := by
    intro u
    unfold Place.down Place.up
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, FT.βγ, Matrix.one_mul, Matrix.mul_assoc, FS.βγ, Matrix.mul_one]
    ext i j
    exact p.ι_π _
  have hupn : ∀ (n : ℕ) (X : Matrix Y Y' k), p.up FS FT (n • X) = n • p.up FS FT X :=
    fun n X => map_nsmul (Witness.upH p FS FT) n X
  have hdownn : ∀ (n : ℕ) (u : WO S T), p.down FS FT (n • u) = n • p.down FS FT u :=
    fun n u => map_nsmul (Witness.downH p FS FT) n u
  have hsupp : ∀ t, p.tensorAt FS FT Φ Ψ t ≠ 0 →
      Φ (t - p.up FS FT (p.down FS FT t)) ≠ 0 ∧ Ψ (p.down FS FT t) ≠ 0 := fun t ht =>
    ⟨left_ne_zero_of_mul ht, right_ne_zero_of_mul ht⟩
  refine ⟨fun t ht => ?_, kΦ * (N * B * A), Nat.mul_pos hkΦ (Nat.mul_pos (Nat.mul_pos hN hB) hA),
    fun u hu hhu t => ?_, fun t ht => ?_⟩
  · obtain ⟨h1, -⟩ := hsupp t ht
    have hs := hΦs _ h1
    have hw := Witness.up_half p FS FT (p.down FS FT t)
    intro i j
    have a1 := hs i j
    have a2 := hw i j
    have e1 : t i j = (t - p.up FS FT (p.down FS FT t)) i j + p.up FS FT (p.down FS FT t) i j := by
      rw [Matrix.sub_apply, sub_add_cancel]
    rw [e1]
    linear_combination (1 - p.e) * a1 + (1 - e) * a2 +
      (p.up FS FT (p.down FS FT t) i j + (t - p.up FS FT (p.down FS FT t)) i j) * he
  · set X := p.down FS FT u with hX
    have hXL : p.up FS FT X ∈ L := by rw [hX, hud]; exact hMap u hu
    have hYi : ∀ r q, (((kΦ * A : ℕ) : k) • ((B : k) • X)) r q ∈ 𝒪[k] := fun r q => by
      rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
      exact mul_mem (natCast_mem _ _) (hBL u hu r q)
    have hd : p.down FS FT (t + (kΦ * (N * B * A)) • u) = p.down FS FT t + (kΦ * (N * B * A)) • X := by
      rw [Witness.down_add, hdownn]
    have e3 : p.down FS FT t + (kΦ * (N * B * A)) • X =
        p.down FS FT t + (N : k) • (((kΦ * A : ℕ) : k) • ((B : k) • X)) := by
      congr 1
      rw [← Nat.cast_smul_eq_nsmul k, smul_smul, smul_smul]
      congr 1
      push_cast; ring
    set w : WO S T := (N * B * A) • (u - p.up FS FT X) with hw
    have e2 : t + (kΦ * (N * B * A)) • u - p.up FS FT (p.down FS FT t + (kΦ * (N * B * A)) • X) =
        (t - p.up FS FT (p.down FS FT t)) + kΦ • w := by
      rw [Witness.up_add, hupn, hw, smul_smul, nsmul_sub]
      abel
    have hwL : w ∈ L := nsmul_mem (sub_mem hu hXL) _
    have hwH : IsHalf e w := by
      intro i j
      rw [hw, hX, hud, Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, nsmul_eq_mul]
      linear_combination ((N * B * A : ℕ) : AE D) * hhu i j - ((N * B * A : ℕ) : AE D) * u i j * he
    show Φ (t + (kΦ * (N * B * A)) • u - p.up FS FT (p.down FS FT (t + (kΦ * (N * B * A)) • u))) *
        Ψ (p.down FS FT (t + (kΦ * (N * B * A)) • u)) =
      Φ (t - p.up FS FT (p.down FS FT t)) * Ψ (p.down FS FT t)
    rw [hd, e2, e3, hΦi w hwL hwH, hΨi _ _ hYi]
  · obtain ⟨h1, h2⟩ := hsupp t ht
    have a1 := hΦl _ h1
    have a2 : A • p.up FS FT (N • p.down FS FT t) ∈ L := hAL _ fun r q => by
      rw [Matrix.smul_apply, nsmul_eq_mul]; exact hΨl _ h2 r q
    rw [hupn] at a2
    have e1 : (kΦ * (N * B * A)) • t = (N * B * A) • (kΦ • (t - p.up FS FT (p.down FS FT t))) +
        kΦ • (B • (A • (N • p.up FS FT (p.down FS FT t)))) := by
      rw [smul_smul, smul_smul, smul_smul, smul_smul, mul_comm (N * B * A) kΦ,
        show kΦ * B * A * N = kΦ * (N * B * A) by ring, ← nsmul_add, sub_add_cancel]
    rw [e1]
    exact add_mem (nsmul_mem a1 _) (nsmul_mem (nsmul_mem a2 B) kΦ)

end GlobalTheory.TensorLatO
end

noncomputable section

namespace GlobalTheory.TensorLatO

theorem isSBHalf_tensorAt_latO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (M : Lat S) (M' : Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (P : LocPl ψ S T M M') (e : AE D), e * P.q.e = 0 → ∀ Φ : WO S T → ℂ, IsSBHalf e (latO S T (M : Set _) (M' : Set _) fun _ => True) Φ → ∀ Ψ ∈ SB (Matrix P.Y P.Y' P.k), IsSBHalf (e + P.q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) ((ofSplit P.q).tensorAt P.FS P.FT Φ Ψ) := by
  classical
  intro D ψ S T M M' hS hT P e he Φ hΦ Ψ hΨ
  set L := latO S T (M : Set (Fin S.rank → D.host.E)) (M' : Set (Fin T.rank → D.host.E)) fun _ => True with hL
  set q := P.q with hq
  have hee : q.e * q.e = q.e := q.split.1

  have hMap : ∀ u ∈ L, u.map (fun a => (ofSplit q).e * a) ∈ L := fun u hu => by
    have h := GlobalTheory.SplitScalar.idem_smul_mem (LS := (M : Set (Fin S.rank → D.host.E)))
      (LT := (M' : Set (Fin T.rank → D.host.E))) hee u hu
    convert h using 1
    ext i j
    rfl

  obtain ⟨N₀, hN₀, h₀⟩ := GlobalTheory.FinPl.RdInt.exists_nat_mul_mem_fin
    (Sum.elim (fun x : Fin T.rank × P.Y => P.FT.β x.1 x.2) (fun x : P.Y' × Fin S.rank => P.FS.γ x.1 x.2))
  obtain ⟨K, hK, hmul⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T) hS.1 hT.1
  have hAL : ∀ X : Matrix P.Y P.Y' P.k, (∀ r q, X r q ∈ 𝒪[P.k]) →
      (K * (N₀ * N₀)) • (ofSplit q).up P.FS P.FT X ∈ L := by
    intro X hX
    have hent := GlobalTheory.FinPl.RdInt.entry_mem P.FT.β P.FS.γ (fun i a => h₀ (Sum.inl (i, a)))
      (fun a j => h₀ (Sum.inr (a, j))) X hX
    have hh : IsHalf q.e ((N₀ * N₀) • (ofSplit q).up P.FS P.FT X) := fun i j => by
      rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm]
      exact congrArg _ (Witness.up_half (ofSplit q) P.FS P.FT X i j)
    have hui : ∀ i j, toEAf D (((N₀ * N₀) • (ofSplit q).up P.FS P.FT X) i j) ∈
        Formalism.L2.Herm.intAf D.host.F D.host.E := by
      intro i j
      have h1 : ((N₀ * N₀) • (ofSplit q).up P.FS P.FT X) i j =
          q.sec (((N₀ * N₀ : ℕ) : P.k) * (P.FT.β * X * P.FS.γ) i j) := by
        rw [← nsmul_eq_mul, map_nsmul]
        rfl
      rw [h1]
      exact GlobalTheory.PlaceCoord.toEAf_mem ((q.int_iff _).1 (hent i j))
    have h1 := hmul _ (GlobalTheory.PlaceDatum.infPart_of_half (GlobalTheory.PlaceCoord.infPart_split q.split) hh) hui
    rwa [mul_nsmul']

  obtain ⟨M₀, hM₀, hden⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T) hS.1.fg hT.1.fg
  obtain ⟨K₁, hK₁, h₁⟩ := GlobalTheory.FinPl.RdBound.exists_nat_mul_mem_family
    (fun x : P.Y × Fin T.rank => P.FT.γ x.1 x.2)
  obtain ⟨K₂, hK₂, h₂⟩ := GlobalTheory.FinPl.RdBound.exists_nat_mul_mem_family
    (fun x : Fin S.rank × P.Y' => P.FS.β x.1 x.2)
  have hBL : ∀ u ∈ L, ∀ i j, ((K₁ * M₀ * K₂ : ℕ) : P.k) * (ofSplit q).down P.FS P.FT u i j ∈ 𝒪[P.k] := by
    intro u hu i j
    have heu := GlobalTheory.SplitScalar.idem_smul_mem (LS := (M : Set (Fin S.rank → D.host.E)))
      (LT := (M' : Set (Fin T.rank → D.host.E))) hee u hu
    have hint : ∀ a b, (M₀ : P.k) * q.pr (u a b) ∈ 𝒪[P.k] := fun a b => by
      rw [q.int_iff]
      have h1 : q.sec ((M₀ : P.k) * q.pr (u a b)) = (M₀ : AE D) * (q.e • u) a b := by
        rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, q.sec_pr]
        rfl
      rw [h1]
      refine GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_
      rw [RingHom.map_mul, map_natCast]
      exact hden _ heu a b
    change (_ : P.k) * (P.FT.γ * Matrix.map u q.pr * P.FS.β) i j ∈ 𝒪[P.k]
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine sum_mem fun b _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    refine sum_mem fun a _ => ?_
    have e : ((K₁ * M₀ * K₂ : ℕ) : P.k) * (P.FT.γ i a * Matrix.map u q.pr a b * P.FS.β b j) =
        ((K₁ : P.k) * P.FT.γ i a) * ((M₀ : P.k) * q.pr (u a b)) * ((K₂ : P.k) * P.FS.β b j) := by
      rw [Matrix.map_apply]; push_cast; ring
    rw [e]
    exact mul_mem (mul_mem (h₁ (i, a)) (hint a b)) (h₂ (b, j))
  exact isSBHalf_tensorAt_of_bounds (ofSplit q) P.FS P.FT L e he hMap (K * (N₀ * N₀)) (K₁ * M₀ * K₂)
    (Nat.mul_pos hK (Nat.mul_pos hN₀ hN₀)) (Nat.mul_pos (Nat.mul_pos hK₁ hM₀) hK₂) hAL hBL Φ hΦ Ψ hΨ

end GlobalTheory.TensorLatO
end
