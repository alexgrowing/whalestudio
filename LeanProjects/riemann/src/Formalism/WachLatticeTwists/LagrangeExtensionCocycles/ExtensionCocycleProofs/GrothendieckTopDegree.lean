import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.StatementTop
import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.MemSpanOfFrobeniusMemSpan
import Formalism.CoboundaryTransfers.WachBridges

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

open Polynomial Formalism.CoboundaryTransfers

theorem lift_to_subgroup_exists : StatLiftSub := by
  unfold StatLiftSub
  intro ℓ _ H₁ H₂ H₁' H₂' _ _ _ _ _ _ _ _ Hf₁ Hf₂ Hf₁' Hf₂' h h' res₂ cor₁ cor₂ g E hg hcr hcomm hres hcor hlift κ' hκ'
  obtain ⟨κ₁, hκ₁, he⟩ := hlift (res₂ κ') (hres κ' hκ')
  set v := padicValNat ℓ g with hv
  obtain ⟨m, hm⟩ : ℓ ^ v ∣ g := pow_padicValNat_dvd
  have hcop : ¬ ℓ ∣ m := by
    intro hdvd
    have h5 : ℓ ^ (v + 1) ∣ g := by
      rw [hm, pow_succ]
      exact mul_dvd_mul_left _ hdvd
    exact pow_succ_padicValNat_not_dvd (by omega) h5
  have hu : IsUnit (m : ℤ_[ℓ]) := by
    rw [PadicInt.isUnit_iff]
    have h1 : ‖((m : ℤ) : ℤ_[ℓ])‖ ≤ 1 := PadicInt.norm_le_one _
    have h2 : ¬ ‖((m : ℤ) : ℤ_[ℓ])‖ < 1 := by
      rw [PadicInt.norm_int_lt_one_iff_dvd]
      exact_mod_cast hcop
    have h3 : ((m : ℤ) : ℤ_[ℓ]) = (m : ℤ_[ℓ]) := Int.cast_natCast m
    rw [← h3]
    exact le_antisymm h1 (not_lt.1 h2)
  refine ⟨(↑hu.unit⁻¹ : ℤ_[ℓ]) • cor₁ κ₁, Hf₁'.smul_mem _ (hcor κ₁ hκ₁), ?_⟩
  rw [map_smul, hcomm, he, map_smul, hcr, smul_smul, smul_smul]
  congr 1
  have hg' : (g : ℤ_[ℓ]) = (ℓ : ℤ_[ℓ]) ^ v * (m : ℤ_[ℓ]) := by
    rw [hm]
    push_cast
    ring
  have hum : (↑hu.unit⁻¹ : ℤ_[ℓ]) * (m : ℤ_[ℓ]) = 1 := hu.val_inv_mul
  rw [hg', pow_add]
  linear_combination (ℓ : ℤ_[ℓ]) ^ E * (ℓ : ℤ_[ℓ]) ^ v * hum

theorem regulator_bound_for_x : StatRegX := by
  unfold StatRegX
  intro ℓ _ A _ _ B M D _ _ _ _ W hreg y hy hX
  unfold RegXQ at hreg
  have hy' : B.Q ^ M • y ∈ W.N := hy
  have key : ∀ z : D, B.Q • z ∈ W.N → B.X • z ∈ W.N → z ∈ W.N := by
    intro z hQ hXz
    obtain ⟨m', hm', he⟩ := hreg (B.X • z) hXz ⟨B.Q • z, hQ, by rw [smul_smul, smul_smul, mul_comm]⟩
    have h0 : B.X • (z - m') = 0 := by rw [smul_sub, he, sub_self]
    have hz : z - m' = 0 := W.X_inj _ h0
    rw [sub_eq_zero] at hz
    rw [hz]
    exact hm'
  suffices h : ∀ j : ℕ, B.Q ^ j • y ∈ W.N → y ∈ W.N from h M hy'
  intro j
  induction j with
  | zero => intro h; simpa using h
  | succ j ih =>
    intro h
    apply ih
    apply key
    · rw [smul_smul, ← pow_succ']
      exact h
    · rw [smul_comm]
      exact W.N.smul_mem _ hX

theorem regulator_bound_for_l : StatRegL := by
  unfold StatRegL
  intro ℓ _ A _ _ B M D _ _ _ _ W hreg htor y hy hX
  unfold RegLQ at hreg
  unfold NoTors at htor
  have hy' : B.Q ^ M • y ∈ W.N := hy
  have key : ∀ z : D, B.Q • z ∈ W.N → (ℓ : ℤ_[ℓ]) • z ∈ W.N → z ∈ W.N := by
    intro z hQ hXz
    obtain ⟨m', hm', he⟩ := hreg ((ℓ : ℤ_[ℓ]) • z) hXz ⟨B.Q • z, hQ, smul_comm _ _ _⟩
    have h0 : (ℓ : ℤ_[ℓ]) • (z - m') = 0 := by rw [smul_sub, he, sub_self]
    have hz : z - m' = 0 := htor _ h0
    rw [sub_eq_zero] at hz
    rw [hz]
    exact hm'
  suffices h : ∀ j : ℕ, B.Q ^ j • y ∈ W.N → y ∈ W.N from h M hy'
  intro j
  induction j with
  | zero => intro h; simpa using h
  | succ j ih =>
    intro h
    apply ih
    apply key
    · rw [smul_smul, ← pow_succ']
      exact h
    · rw [smul_comm]
      exact W.N.smul_mem _ hX

theorem extension_class_is_cocycle : StatExtCocycle := by
  unfold StatExtCocycle
  intro ℓ _ A _ _ B M D _ _ _ _ W H _ _ cl κ E e hD hlift
  obtain ⟨x, hxN, hx⟩ := hlift E.e E.e_mem
  have hπφ : E.S.π.f (E.Wp.φ x - x) = 0 := by
    rw [map_sub, E.S.π.φ_comm, hx, map_smul, E.φe, sub_self]
  have hπγ : E.S.π.f (E.Wp.γ x - x) = 0 := by
    rw [map_sub, E.S.π.γ_comm, hx, map_smul, E.γe, sub_self]
  obtain ⟨y, hy⟩ := (E.S.exact _).1 hπφ
  obtain ⟨z, hz⟩ := (E.S.exact _).1 hπγ
  have hd : (W.γ y - y) - (W.φ z - z) = 0 := by
    apply E.S.ι_inj
    simp only [map_sub, map_zero, E.S.ι.γ_comm, E.S.ι.φ_comm, hy, hz, E.Wp.comm]
    abel
  have hZ : ((y, z) : D × D) ∈ W.Z1 := by
    show ((y, z) : D × D) ∈ LinearMap.ker ((W.γ - LinearMap.id).coprod (-(W.φ - LinearMap.id)))
    simp only [LinearMap.mem_ker, LinearMap.coprod_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.neg_apply]
    calc _ = (W.γ y - y) - (W.φ z - z) := by abel
      _ = 0 := hd
  have hQ : B.Q ^ M • y ∈ W.N := by
    apply E.S.sat
    rw [map_smul, hy, smul_sub]
    exact E.Wp.N.sub_mem (E.Wp.φ_N x hxN) (E.Wp.N.smul_mem _ hxN)
  obtain ⟨x', hx'N, hx'⟩ := E.Wp.γ_N x hxN
  have hπx' : E.S.π.f x' = 0 := by
    apply E.Wt.X_inj
    rw [← map_smul, ← hx', map_sub, E.S.π.γ_comm, hx, map_smul, E.γe, sub_self]
  obtain ⟨x₀, hx₀⟩ := (E.S.exact x').1 hπx'
  have hx₀N : x₀ ∈ W.N := E.S.sat x₀ (by rw [hx₀]; exact hx'N)
  have hzX : z = B.X • x₀ := by
    apply E.S.ι_inj
    rw [map_smul, hx₀, hz, hx']
  refine ⟨⟨(y, z), hZ⟩, ?_, ?_⟩
  · unfold WachMod.Cocycle WachMod.C1 WachMod.QInv WachMod.XN WachMod.d1
    exact ⟨⟨hQ, x₀, hx₀N, hzX⟩, hd⟩
  · exact hD ((ℓ : ℤ_[ℓ]) ^ e) x ⟨(y, z), hZ⟩ hx hy hz

theorem rational_points_map_surjective : StatRatSurj := by
  unfold StatRatSurj
  intro ℓ _ A _ _ B M D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ S H₁ H₂ _ _ _ _ cl₁ cl₂ Hf₁ Hf₂ g e₁ hp hnat hcoc hherr honto hlift
  unfold Formalism.CoboundaryTransfers.RatSurj
  intro y z hyz
  have memZ : ∀ a b : D₂, W₂.γ a - a - (W₂.φ b - b) = 0 → ((a, b) : D₂ × D₂) ∈ W₂.Z1 := by
    intro a b h
    show ((a, b) : D₂ × D₂) ∈ LinearMap.ker ((W₂.γ - LinearMap.id).coprod (-(W₂.φ - LinearMap.id)))
    simp only [LinearMap.mem_ker, LinearMap.coprod_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.neg_apply]
    calc _ = W₂.γ a - a - (W₂.φ b - b) := by abel
      _ = 0 := h
  have hyz' := hyz
  unfold WachMod.Cocycle WachMod.C1 WachMod.QInv WachMod.XN WachMod.d1 at hyz'
  obtain ⟨⟨hQ₂, n₂, hn₂, hz₂⟩, hd₂⟩ := hyz'
  have hκ : cl₂ ⟨(y, z), memZ y z hd₂⟩ ∈ Hf₂ := hcoc _ hyz
  obtain ⟨k, κ₁, hκ₁, hgk⟩ := honto _ hκ
  obtain ⟨⟨⟨y₁, z₁⟩, hZ₁⟩, hpr₁c, hpr₁⟩ := hlift κ₁ hκ₁
  have hc₁ := hpr₁c
  unfold WachMod.Cocycle WachMod.C1 WachMod.QInv WachMod.XN WachMod.d1 at hc₁
  obtain ⟨⟨hQ₁', n₁, hn₁, hz₁'⟩, hd₁'r⟩ := hc₁
  have hz₁ : z₁ = B.X • n₁ := hz₁'
  have hd₁ : W₁.γ y₁ - y₁ - (W₁.φ z₁ - z₁) = 0 := hd₁'r
  have hQ₁ : B.Q ^ M • y₁ ∈ W₁.N := hQ₁'
  have hd₁' : W₂.γ (S.π.f y₁) - S.π.f y₁ - (W₂.φ (S.π.f z₁) - S.π.f z₁) = 0 := by
    have h := congrArg S.π.f hd₁
    simpa [map_sub, S.π.γ_comm, S.π.φ_comm] using h
  obtain ⟨c, hc⟩ : ∃ c : ℤ_[ℓ], c = (ℓ : ℤ_[ℓ]) ^ (e₁ + k) := ⟨_, rfl⟩
  have hcP : W₂.Cocycle (S.π.f y₁ - c • y) (S.π.f z₁ - c • z) := by
    unfold WachMod.Cocycle WachMod.C1 WachMod.QInv WachMod.XN WachMod.d1
    refine ⟨⟨?_, S.π.f n₁ - c • n₂, W₂.N.sub_mem (S.π.N_le _ hn₁) (W₂.N.smul_of_tower_mem c hn₂), ?_⟩, ?_⟩
    · rw [smul_sub, ← map_smul, smul_comm (B.Q ^ M) c y]
      exact W₂.N.sub_mem (S.π.N_le _ hQ₁) (W₂.N.smul_of_tower_mem c hQ₂)
    · rw [hz₁, hz₂, map_smul, smul_sub, smul_comm c B.X n₂]
    · calc W₂.γ (S.π.f y₁ - c • y) - (S.π.f y₁ - c • y) - (W₂.φ (S.π.f z₁ - c • z) - (S.π.f z₁ - c • z))
          = (W₂.γ (S.π.f y₁) - S.π.f y₁ - (W₂.φ (S.π.f z₁) - S.π.f z₁)) -
              c • (W₂.γ y - y - (W₂.φ z - z)) := by
            rw [map_sub, map_sub, map_smul, map_smul]
            simp only [smul_sub]
            abel
        _ = 0 := by rw [hd₁', hd₂, smul_zero, sub_zero]
  have hcl : cl₂ (⟨(S.π.f y₁, S.π.f z₁), memZ _ _ hd₁'⟩ - c • ⟨(y, z), memZ y z hd₂⟩) = 0 := by
    rw [map_sub, map_smul, ← hnat ⟨(y₁, z₁), hZ₁⟩ ⟨(S.π.f y₁, S.π.f z₁), memZ _ _ hd₁'⟩
      (by first | rfl | simp [Formalism.CoboundaryTransfers.Hom.f2]), hpr₁, map_smul, hgk, hc, pow_add, mul_smul, sub_self]
  have hcob := hherr _ hcP hcl
  unfold WachMod.IsCob1 at hcob
  obtain ⟨x, hxN, hx1, hx2⟩ := hcob
  change S.π.f y₁ - c • y = W₂.φ x - x at hx1
  change S.π.f z₁ - c • z = W₂.γ x - x at hx2
  refine ⟨e₁ + k, y₁, z₁, hpr₁c, x, hxN, ?_, ?_⟩
  · rw [hp, ← hc, ← hx1]
    abel
  · rw [hp, ← hc, ← hx2]
    abel

end Formalism.RepresentationBoundsCohomology.N2
