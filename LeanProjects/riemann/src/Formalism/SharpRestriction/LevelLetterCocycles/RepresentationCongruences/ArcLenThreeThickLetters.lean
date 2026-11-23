import Formalism.SharpRestriction.LevelLetterCocycles.AdmBoundsBOfAdm
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcGamLiftCore
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Pi0MemADelta

open scoped TensorProduct

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

namespace ArcLengthThreeFiltration

theorem φVB_inj (T : LocLat G Qp LL O) : Function.Injective (φVB PD (LL := LL) (V := T.V)) := by
  have hφ : Function.Injective (PD.φ.toLinearMap) := by simpa using PD.φ_inj
  have h : ⇑(φVB PD (LL := LL) (V := T.V)) = ⇑(LinearMap.lTensor T.V PD.φ.toLinearMap) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a c => simp [φVB]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [h]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ hφ

theorem crisMap_φ {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (x : T₁.V ⊗[Qp] B) :
    Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (φVB PD (LL := LL) (V := T₁.V) x) =
      φVB PD (LL := LL) (V := T₂.V) (Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a c => simp [φVB, Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap]
  | add x y hx hy => simp only [map_add, hx, hy]

variable (W : LocWach PD LL O v n)

theorem dv_succ (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → LL) :
    dv W T (e + 1) b c₀ = φVB PD (LL := LL) (V := T.V) (dv W T e b c₀) := by
  first
  | (simp only [dv, pow_succ', Module.End.mul_apply, map_sum, map_smul]; done)
  | (simp only [dv, pow_succ', LinearMap.mul_apply, map_sum, map_smul]; done)
  | (simp [dv, LinearMap.pow_apply, Function.iterate_succ_apply']; done)
  | (simp [dv, pow_succ']; exact (trivial : True))

theorem dv_add (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ c₁ : Fin d → LL) :
    dv W T e b (c₀ + c₁) = dv W T e b c₀ + dv W T e b c₁ := by
  simp only [dv, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem dv_smul (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (t : LL) (c₀ : Fin d → LL) :
    dv W T e b (t • c₀) = t • dv W T e b c₀ := by
  simp only [dv, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem dv_sum (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) {ι : Type*} (s : Finset ι)
    (c₀ : ι → Fin d → LL) : dv W T e b (∑ i ∈ s, c₀ i) = ∑ i ∈ s, dv W T e b (c₀ i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simpa using dv_smul W T e b 0 0
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, dv_add, ih]

theorem dv_eq_sum (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → LL) :
    dv W T e b c₀ = ∑ m, c₀ m • dv W T e b (Pi.single m 1) := by
  have h : c₀ = ∑ m, c₀ m • (Pi.single m 1 : Fin d → LL) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [h]
  rw [dv_sum]
  simp only [dv_smul]

theorem dvO_eq (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → O) :
    dvO W T e b c₀ = ∑ m, algebraMap O LL (c₀ m) • dv W T e b (Pi.single m 1) := by
  first
  | (unfold dvO; exact dv_eq_sum W T e b _)
  | (simp only [dvO]; exact dv_eq_sum W T e b _)

theorem dvO_single (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (k : Fin d) :
    dvO W T e b (Pi.single k 1) = dv W T e b (Pi.single k 1) := by
  rw [dvO_eq]
  simp [Pi.single_apply, apply_ite (algebraMap O LL), ite_smul]

theorem filS_anti (T : LocLat G Qp LL O) (a : ZMod n) (s : ℕ) {u u' : ℤ} (h : u ≤ u') :
    FilS W T a s u' ≤ FilS W T a s u := by
  unfold FilS
  apply Submodule.map_mono
  apply inf_le_inf_right
  unfold FilCris
  apply inf_le_inf_left
  apply Submodule.comap_mono
  unfold FilV
  have hF : PD.Fil u' ≤ PD.Fil u := antitone_int_of_succ_le PD.Fil_anti h
  intro y hy
  rw [LinearMap.mem_range] at hy
  obtain ⟨z, rfl⟩ := hy
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a c => exact LinearMap.mem_range.mpr ⟨a ⊗ₜ ⟨c.1, hF c.2⟩, by simp⟩
  | add z w hz hw => rw [map_add]; exact Submodule.add_mem _ hz hw

theorem filS_zero_iff (T : LocLat G Qp LL O) (a : ZMod n) (u : ℤ) (x : T.V ⊗[Qp] B) :
    x ∈ FilS W T a 0 u ↔ x ∈ FilCris PD T.ρ u ⊓ DcrisL PD T.ρ (W.emb a) := by
  unfold FilS
  simp [pow_zero, Submodule.map_id]
  try rfl

theorem filS_one_of (T : LocLat G Qp LL O) (a : ZMod n) (u : ℤ) (x : T.V ⊗[Qp] B)
    (hx : x ∈ FilS W T a 0 u) : φVB PD (LL := LL) (V := T.V) x ∈ FilS W T (a + 1) 1 u := by
  rw [filS_zero_iff] at hx
  unfold FilS
  rw [pow_one, Nat.cast_one, add_sub_cancel_right]
  exact Submodule.mem_map_of_mem hx

theorem filS_zero_of (T : LocLat G Qp LL O) (a : ZMod n) (u : ℤ) (x : T.V ⊗[Qp] B)
    (hx : φVB PD (LL := LL) (V := T.V) x ∈ FilS W T (a + 1) 1 u) : x ∈ FilS W T a 0 u := by
  rw [filS_zero_iff]
  unfold FilS at hx
  rw [pow_one, Nat.cast_one, add_sub_cancel_right, Submodule.mem_map] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  rw [← φVB_inj T hyx]
  exact hy

theorem repVV_smulA {T : LocLat G Qp LL O} {c' : ZMod n} {e M : ℕ} {Λ : LetA O n} {d : ℕ}
    {b : Fin d → W.DD T} {sol : Fin d → ℕ → Fin d → LL} {x : W.DD T} {f : Fin d → W.EE}
    (h : RepVV W T c' e M Λ b sol x f) {t : LetA O n} (ht : t ∈ W.AΔ) :
    RepVV W T c' e M Λ b sol (t • x) (fun k => algebraMap (LetA O n) W.EE t * f k) := by
  unfold RepVV at h ⊢
  obtain ⟨κ, κ', Hh, a, hH, ha, hIn⟩ := h
  refine ⟨κ, κ', Hh, fun k => t * a k, hH, fun k => ⟨mul_mem ht (ha k).1, ?_⟩, ?_⟩
  · dsimp only
    rw [map_mul, ← (ha k).2]
    ring
  · have he : lA W ^ κ' • (lA W ^ κ • Λ • (t • x) - ∑ k, (t * a k) • ((W.φD T) ^ e) (Hh k)) =
        t • (lA W ^ κ' • (lA W ^ κ • Λ • x - ∑ k, a k • ((W.φD T) ^ e) (Hh k))) := by
      simp only [smul_sub, Finset.smul_sum, smul_smul, mul_comm, mul_assoc, mul_left_comm]
    rw [he]
    exact Formalism.MainNotions.N.FrobeniusPowerSeries.TypesA.inMultiple_smul (ha := ht) (h := hIn)

section ThetaShiftProofs
variable {b w S η : ℕ} {up : ZMod n → Bool} {size : ZMod n → ℕ}

theorem arc_ty [NeZero n] (i : ZMod n) :
    (arcOf b w S η up size).ty i = if up i then .up (size i) else .down (size i) := rfl

theorem arc_thick [NeZero n] (i : ZMod n) : ((arcOf b w S η up size).ty i).thick := by
  rw [arc_ty]
  split <;> rfl

theorem arc_len_three_thick_letters [NeZero n] {c : ZMod n} (hlen : (arcOf b w S η up size).len c = 3) :
    Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size c ∧ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - 1) ∧
      ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - 2) := by
  unfold arcOf at hlen
  dsimp only at hlen
  have hpos : 0 < sInf {d : ℕ | 1 ≤ d ∧ ¬Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} := by
    rw [hlen]; norm_num
  have hne := Nat.nonempty_of_pos_sInf hpos
  have h3 := Nat.sInf_mem hne
  rw [hlen] at h3
  have hlt : ∀ d : ℕ, 1 ≤ d → d < 3 → Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1) := by
    intro d hd1 hd3
    by_contra hT
    have hle := Nat.sInf_le
      (show d ∈ {d : ℕ | 1 ≤ d ∧ ¬Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} from ⟨hd1, hT⟩)
    rw [hlen] at hle
    omega
  refine ⟨?_, ?_, ?_⟩
  · have h1 := hlt 1 le_rfl (by norm_num)
    rwa [show c - ((1 : ℕ) : ZMod n) + 1 = c by push_cast; ring] at h1
  · have h1 := hlt 2 (by norm_num) (by norm_num)
    rwa [show c - ((2 : ℕ) : ZMod n) + 1 = c - 1 by push_cast; ring] at h1
  · have h1 := h3.2
    rwa [show c - ((3 : ℕ) : ZMod n) + 1 = c - 2 by push_cast; ring] at h1

theorem arc_types [NeZero n] {c : ZMod n} (halt : Alt b η up size) (hD : up (c - 2) = false) :
    up (c - 1) = true ∧ up c = false := by
  unfold Alt at halt
  have h1 := (halt (c - 2)).1
  have h2 := (halt (c - 1)).1
  rw [show c - 2 + 1 = c - 1 by ring, hD] at h1
  rw [show c - 1 + 1 = c by ring] at h2
  have e1 : up (c - 1) = true := by simpa using h1
  refine ⟨e1, ?_⟩
  rw [e1] at h2
  simpa using h2

theorem lam_inner [NeZero n] {c : ZMod n} (hlen : (arcOf b w S η up size).len c = 3) :
    abelian₂ W (arcOf b w S η up size) (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n) + ((2 : ℕ) : ZMod n)) 2 =
      ps W 0 ^ (arcOf b w S η up size).h * ps W 1 ^ (arcOf b w S η up size).G₀ := by
  unfold abelian₂
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  have hs0 : ∀ a : ZMod n, (arcOf b w S η up size).Hs a 2 0 = (arcOf b w S η up size).h := by
    intro a
    unfold Formalism.MainNotions.ArcLiftingSetup.ArcP.Hs
    rw [if_neg]
    rintro (hc | hc)
    · simp only [arcOf] at hc
      split at hc <;> simp at hc
    · norm_num [arcOf] at hc
  have hs1 : ∀ a : ZMod n, (arcOf b w S η up size).Hs a 2 1 = (arcOf b w S η up size).G₀ := by
    intro a
    unfold Formalism.MainNotions.ArcLiftingSetup.ArcP.Hs
    rw [if_pos (Or.inr (by simp [arcOf]))]
  rw [hs0, hs1]

end ThetaShiftProofs

end ArcLengthThreeFiltration
end Formalism.MainNotions.N.FrobeniusPowerSeries
