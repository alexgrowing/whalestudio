import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.XLeSpanEXLam

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.Full

namespace Formalism.L2.SG.Pf.FinXP

section MoveB

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem scal_move_rev {Λ : Submodule (𝓞 E) S.V} {F : LFlag S r T} {G₁ G₂ K₁ K₂ : LFlag S r T'}
    {n₁ n₂ m₁ m₂ β τ : S.V ≃ₗ[E] S.V}
    (hn₁ : n₁ ∈ NLam Λ F) (hn₂ : n₂ ∈ NLam Λ F) (hm₁ : m₁ ∈ NLam Λ G₁) (hm₂ : m₂ ∈ NLam Λ G₂)
    (hf₁ : ∀ a, frame K₁ a = n₁ (m₁ (frame G₁ a))) (hz₁ : K₁.zt = n₁ (m₁ G₁.zt))
    (hf₂ : ∀ a, frame K₂ a = n₂ (m₂ (frame G₂ a))) (hz₂ : K₂.zt = n₂ (m₂ G₂.zt))
    (hLF : IsLift Λ F) (hL₁ : IsLift Λ G₁) (hL₂ : IsLift Λ G₂)
    (hβ : β ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hβX : (Xsp G₁).map (β : S.V →ₗ[E] S.V) = Xsp G₂)
    (hτX : ∀ x ∈ Xsp G₁, τ x ∈ Xsp G₁) (hτ : ∀ x ∈ orth S (Xsp G₁), τ x - x ∈ Xsp G₁)
    (hS : IsScalar Λ F K₁ K₂ (n₂ * m₂ * β * τ * m₁⁻¹ * n₁⁻¹)) : IsScalar Λ F G₁ G₂ β := by
  have hU₁ := UUE_move hn₁ hm₁ hf₁ hz₁ hLF hL₁
  have hU₂ := UUE_move hn₂ hm₂ hf₂ hz₂ hLF hL₂
  have hX₁ : Xsp K₁ = (Xsp G₁).map (n₁ : S.V →ₗ[E] S.V) := Xsp_DC hm₁ hf₁
  have hX₂ : Xsp K₂ = (Xsp G₂).map (n₂ : S.V →ₗ[E] S.V) := Xsp_DC hm₂ hf₂
  have hzK : ∀ {G K : LFlag S r T'} {n m : S.V ≃ₗ[E] S.V}, m ∈ NLam Λ G → IsLift Λ G →
      Xsp K = (Xsp G).map (n : S.V →ₗ[E] S.V) → K.zt = n (m G.zt) → K.zt - n G.zt ∈ Xsp K := by
    intro G K n m hm hL hX hz
    rw [hz, ← map_sub, hX]
    refine Submodule.mem_map_of_mem ?_
    rw [hL.2]; exact hm.2.2 _ (isotropicSpan_orthogonal_anisotropicVector G)

  have hpF : ∀ {n : S.V ≃ₗ[E] S.V}, n ∈ NLam Λ F → ∀ {y : S.V}, y ∈ orth S (Xplus F) → n y ∈ orth S (Xplus F) := by
    intro n hn y hy
    have hi := nlam_inv hn
    have := orth_pull hi.1.1 _ (fun w hw => xplus_nlam hi hw) hy
    have e : n⁻¹.symm y = n y := rfl
    rwa [e] at this
  have hpG : ∀ {G K : LFlag S r T'} {n m : S.V ≃ₗ[E] S.V}, n ∈ NLam Λ F → m ∈ NLam Λ G →
      (∀ a, frame K a = n (m (frame G a))) → ∀ {y : S.V}, y ∈ orth S (Xplus G) → n y ∈ orth S (Xplus K) := by
    intro G K n m hn hm hf y hy
    rw [mem_orth'] at hy ⊢
    intro w hw

    have hfi : ∀ a, frame G a = (m⁻¹ * n⁻¹) (frame K a) := fun a => by
      rw [hf a]; show _ = m.symm (n.symm (n (m _))); rw [n.symm_apply_apply, m.symm_apply_apply]
    have hw0 := xplus_frame (φ := m⁻¹ * n⁻¹) hfi hw
    have hw1 : n.symm w ∈ Xplus G := by
      have := xplus_nlam hm hw0
      have e : m ((m⁻¹ * n⁻¹) w) = n.symm w := by
        show m (m.symm (n.symm w)) = _; rw [m.apply_symm_apply]
      rwa [e] at this
    have := hy _ hw1
    rw [← Formalism.L2.SG.Saturated.isom_apply hn.1.1, n.apply_symm_apply] at this
    exact this
  have hoX : orth S (Xplus F) ≤ orth S (Xsp F) := orth_anti le_sup_left
  have hoX' : ∀ (G : LFlag S r T'), orth S (Xplus G) ≤ orth S (Xsp G) := fun G => orth_anti le_sup_left
  intro y1 hy1 y2 hy2 y1' hy1' y2'' hy2'' h12 h2'' al al'
  have hY1 : n₁ y1 ∈ Ylift Λ F K₁ := ⟨hU₁ ▸ Submodule.mem_map_of_mem hy1.1, hpF hn₁ hy1.2⟩
  have hY2 : n₂ y2 ∈ Ylift Λ F K₂ := ⟨hU₂ ▸ Submodule.mem_map_of_mem hy2.1, hpF hn₂ hy2.2⟩
  have hY1' : n₁ y1' ∈ Ylift' Λ F K₁ := ⟨hU₁ ▸ Submodule.mem_map_of_mem hy1'.1, hpG hn₁ hm₁ hf₁ hy1'.2⟩
  have hY2'' : n₂ y2'' ∈ Ylift' Λ F K₂ := ⟨hU₂ ▸ Submodule.mem_map_of_mem hy2''.1, hpG hn₂ hm₂ hf₂ hy2''.2⟩
  have hc12 : n₁ y1 - n₂ y2 ∈ Xsp F := by
    have a := hn₁.2.2 y1 (hoX hy1.2)
    have b := hn₂.2.2 y2 (hoX hy2.2)
    have : n₁ y1 - n₂ y2 = (n₁ y1 - y1) - (n₂ y2 - y2) + (y1 - y2) := by abel
    rw [this]; exact add_mem (sub_mem a b) h12
  have hc2 : n₂ y2'' - (n₂ * m₂ * β * τ * m₁⁻¹ * n₁⁻¹) (n₁ y1') ∈ Xsp K₂ := by
    have happ : (n₂ * m₂ * β * τ * m₁⁻¹ * n₁⁻¹) (n₁ y1') = n₂ (m₂ (β (τ (m₁.symm y1')))) := by
      show n₂ (m₂ (β (τ (m₁.symm (n₁.symm (n₁ y1')))))) = _
      rw [n₁.symm_apply_apply]
    rw [happ, hX₂, ← map_sub]
    refine Submodule.mem_map_of_mem ?_
    have hk := key_mod hm₁ hm₂ hβ hβX hτX hτ (hoX' _ hy1'.2)
    have : y2'' - m₂ (β (τ (m₁.symm y1'))) = (y2'' - β y1') - (m₂ (β (τ (m₁.symm y1'))) - β y1') := by abel
    rw [this]; exact sub_mem h2'' hk
  have key := hS _ hY1 _ hY2 _ hY1' _ hY2'' hc12 hc2 al al'
  have s1 := sg_move hn₁ hX₁ (hzK hm₁ hL₁ hX₁ hz₁) hLF y1 y1' al al'
  have s2 := sg_move hn₂ hX₂ (hzK hm₂ hL₂ hX₂ hz₂) hLF y2 y2'' al al'
  exact s1.symm.trans (key.trans s2)

theorem mem_gmap_iff' (δ : S.V ≃ₗ[E] S.V) (M : Submodule (𝓞 E) S.V) (x : S.V) :
    x ∈ Formalism.HermitianLatticesTheory.gmap δ M ↔ δ.symm x ∈ M := by

  unfold Formalism.HermitianLatticesTheory.gmap
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨δ.symm x, h, by simp⟩

theorem Th_map {Λ : Submodule (𝓞 E) S.V} {F : LFlag S r T} {F' F'' : LFlag S r T'} (δ B : S.V ≃ₗ[E] S.V)
    (hδ : δ ∈ Formalism.HermitianLatticesTheory.isom S.hT) :
    Th (Formalism.HermitianLatticesTheory.gmap δ Λ) (Formalism.L2.SG.Saturated.mapL δ hδ F) (Formalism.L2.SG.Saturated.mapL δ hδ F')
      (Formalism.L2.SG.Saturated.mapL δ hδ F'') (δ * B * δ⁻¹) = (Th Λ F F' F'' B).map (δ : S.V →ₗ[E] S.V) := by
  have hH : ∀ G : LFlag S r T', Hp (Formalism.HermitianLatticesTheory.gmap δ Λ) (Formalism.L2.SG.Saturated.mapL δ hδ F)
      (Formalism.L2.SG.Saturated.mapL δ hδ G) = (Hp Λ F G).map (δ : S.V →ₗ[E] S.V) := fun G => by
    unfold Hp
    rw [UUE_mapL δ hδ Λ F G, orth_map_sat δ hδ]
  have happ : ∀ x, (δ * B * δ⁻¹) (δ x) = δ (B x) := fun x => by
    show δ (B (δ.symm (δ x))) = _; rw [δ.symm_apply_apply]
  ext y
  rw [mem_Th, Submodule.mem_map]
  constructor
  · rintro ⟨y₂, hp⟩
    rw [mem_ThPairs, hH, hH, Xsp_mapL δ hδ, Xsp_mapL δ hδ, mem_map_iff, mem_map_iff, mem_map_iff, mem_map_iff] at hp
    obtain ⟨h1, h2, h3, h4⟩ := hp
    refine ⟨δ.symm y, ?_, δ.apply_symm_apply y⟩
    rw [mem_Th]
    refine ⟨δ.symm y₂, ?_⟩
    rw [mem_ThPairs]
    refine ⟨h1, h2, by rwa [map_sub] at h3, ?_⟩
    have e : δ.symm ((δ * B * δ⁻¹) y - y₂) = B (δ.symm y) - δ.symm y₂ := by
      rw [map_sub]; show δ.symm (δ (B (δ.symm y))) - _ = _; rw [δ.symm_apply_apply]
    rwa [e] at h4
  · rintro ⟨x, hx, rfl⟩
    rw [mem_Th] at hx
    obtain ⟨x₂, hp⟩ := hx
    rw [mem_ThPairs] at hp
    obtain ⟨h1, h2, h3, h4⟩ := hp
    refine ⟨δ x₂, ?_⟩
    rw [mem_ThPairs, hH, hH, Xsp_mapL δ hδ, Xsp_mapL δ hδ]
    refine ⟨Submodule.mem_map_of_mem h1, Submodule.mem_map_of_mem h2, ?_, ?_⟩
    · show δ x - δ x₂ ∈ _
      rw [← map_sub]; exact Submodule.mem_map_of_mem h3
    · show (δ * B * δ⁻¹) (δ x) - δ x₂ ∈ _
      rw [happ, ← map_sub]; exact Submodule.mem_map_of_mem h4

theorem s0_gmap_mapL_conj_eq_s0 {Λ : Submodule (𝓞 E) S.V} {F : LFlag S r T} {F' F'' : LFlag S r T'} (δ B : S.V ≃ₗ[E] S.V)
    (hδ : δ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (k : ℕ) :
    Lat.s0 (Formalism.HermitianLatticesTheory.gmap δ Λ) (Formalism.L2.SG.Saturated.mapL δ hδ F) (Formalism.L2.SG.Saturated.mapL δ hδ F')
      (Formalism.L2.SG.Saturated.mapL δ hδ F'') (δ * B * δ⁻¹) k = Lat.s0 Λ F F' F'' B k := by

  unfold Formalism.MainNotions.S.Lat.s0
  rw [Th_map δ B hδ, LinearEquiv.finrank_map_eq]

end MoveB

section MoveC

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem aut_mem {Λ : Submodule (𝓞 E) S.V} {φ : S.V ≃ₗ[E] S.V} (h : IsAutLam S Λ φ) {x : S.V} (hx : x ∈ Λ) : φ x ∈ Λ := by

  have h2 : Formalism.HermitianLatticesTheory.gmap φ Λ = Λ := h.2
  rw [← h2]
  exact (mem_gmap_iff' φ Λ (φ x)).2 (by simpa using hx)

theorem aut_symm_mem {Λ : Submodule (𝓞 E) S.V} {φ : S.V ≃ₗ[E] S.V} (h : IsAutLam S Λ φ) {x : S.V} (hx : x ∈ Λ) :
    φ.symm x ∈ Λ := by

  have h2 : Formalism.HermitianLatticesTheory.gmap φ Λ = Λ := h.2
  have hx' : x ∈ Formalism.HermitianLatticesTheory.gmap φ Λ := by rw [h2]; exact hx
  exact (mem_gmap_iff' φ Λ x).1 hx'

theorem mapL_inv_mapL (δ : S.V ≃ₗ[E] S.V) (hδ : δ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hδi : δ⁻¹ ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    {T₀ : E} (F : LFlag S r T₀) :
    Formalism.L2.SG.Saturated.mapL δ⁻¹ hδi (Formalism.L2.SG.Saturated.mapL δ hδ F) = F := by

  have hinv : ∀ x, δ⁻¹ (δ x) = x := fun x => δ.symm_apply_apply x
  cases F with
  | mk fl zt =>
    cases fl
    simp only [Formalism.L2.SG.Saturated.mapL, Formalism.L2.SG.Saturated.mapFlag, hinv]

theorem sg_map (δ : S.V ≃ₗ[E] S.V) (hδ : δ ∈ Formalism.HermitianLatticesTheory.isom S.hT) {F : LFlag S r T} {G : LFlag S r T'}
    (y y' : S.V) (al al' : E) :
    SgRel (Formalism.L2.SG.Saturated.mapL δ hδ F) (Formalism.L2.SG.Saturated.mapL δ hδ G) y y' al al' ↔
      SgRel F G (δ.symm y) (δ.symm y') al al' := by

  unfold Formalism.MainNotions.S.Lat.SgRel
  simp only [Formalism.L2.SG.Pf.Xsp_mapL, Submodule.mem_map]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨x', hx', rfl⟩, h⟩
    refine ⟨x, hx, x', hx', ?_⟩
    have h2 := congrArg δ.symm h
    simpa [Formalism.L2.SG.Saturated.mapL, map_add, map_sub, map_smul] using h2
  · rintro ⟨x, hx, x', hx', h⟩
    refine ⟨δ x, ⟨x, hx, rfl⟩, δ x', ⟨x', hx', rfl⟩, ?_⟩
    have h2 := congrArg δ h
    simpa [Formalism.L2.SG.Saturated.mapL, map_add, map_sub, map_smul] using h2

theorem scal_map_fwd {Λ : Submodule (𝓞 E) S.V} {F : LFlag S r T} {F' F'' : LFlag S r T'} (δ B : S.V ≃ₗ[E] S.V)
    (hδ : δ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hS : IsScalar Λ F F' F'' B) :
    IsScalar (Formalism.HermitianLatticesTheory.gmap δ Λ) (Formalism.L2.SG.Saturated.mapL δ hδ F) (Formalism.L2.SG.Saturated.mapL δ hδ F')
      (Formalism.L2.SG.Saturated.mapL δ hδ F'') (δ * B * δ⁻¹) := by
  have hfr : ∀ {T₀ : E} (G : LFlag S r T₀), ∀ a, frame (Formalism.L2.SG.Saturated.mapL δ hδ G) a = δ (frame G a) :=
    fun G a => congrFun (frame_mapL' δ hδ G) a
  have hY : ∀ G : LFlag S r T', ∀ {y : S.V},
      y ∈ Ylift (Formalism.HermitianLatticesTheory.gmap δ Λ) (Formalism.L2.SG.Saturated.mapL δ hδ F) (Formalism.L2.SG.Saturated.mapL δ hδ G) →
      δ.symm y ∈ Ylift Λ F G := by
    intro G y hy
    refine ⟨?_, ?_⟩
    · have := hy.1; rw [UUE_mapL δ hδ] at this; exact (mem_map_iff δ _ _).1 this
    · exact orth_pull hδ _ (fun w hw => xplus_frame (hfr F) hw) hy.2
  have hY' : ∀ G : LFlag S r T', ∀ {y : S.V},
      y ∈ Ylift' (Formalism.HermitianLatticesTheory.gmap δ Λ) (Formalism.L2.SG.Saturated.mapL δ hδ F) (Formalism.L2.SG.Saturated.mapL δ hδ G) →
      δ.symm y ∈ Ylift' Λ F G := by
    intro G y hy
    refine ⟨?_, ?_⟩
    · have := hy.1; rw [UUE_mapL δ hδ] at this; exact (mem_map_iff δ _ _).1 this
    · exact orth_pull hδ _ (fun w hw => xplus_frame (hfr G) hw) hy.2
  intro y1 hy1 y2 hy2 y1' hy1' y2'' hy2'' h12 h2'' al al'
  have c12 : δ.symm y1 - δ.symm y2 ∈ Xsp F := by
    rw [Xsp_mapL δ hδ, mem_map_iff, map_sub] at h12; exact h12
  have c2 : δ.symm y2'' - B (δ.symm y1') ∈ Xsp F'' := by
    rw [Xsp_mapL δ hδ, mem_map_iff, map_sub] at h2''
    have e : δ.symm ((δ * B * δ⁻¹) y1') = B (δ.symm y1') := by
      show δ.symm (δ (B (δ.symm y1'))) = _; rw [δ.symm_apply_apply]
    rwa [e] at h2''
  have key := hS _ (hY F' hy1) _ (hY F'' hy2) _ (hY' F' hy1') _ (hY' F'' hy2'') c12 c2 al al'
  rw [sg_map δ hδ, sg_map δ hδ]; exact key

theorem scal_map {Λ : Submodule (𝓞 E) S.V} {F : LFlag S r T} {F' F'' : LFlag S r T'} (δ B : S.V ≃ₗ[E] S.V)
    (hδ : δ ∈ Formalism.HermitianLatticesTheory.isom S.hT) :
    IsScalar (Formalism.HermitianLatticesTheory.gmap δ Λ) (Formalism.L2.SG.Saturated.mapL δ hδ F) (Formalism.L2.SG.Saturated.mapL δ hδ F')
      (Formalism.L2.SG.Saturated.mapL δ hδ F'') (δ * B * δ⁻¹) ↔ IsScalar Λ F F' F'' B := by

  constructor
  · intro h
    have hδi : δ⁻¹ ∈ Formalism.HermitianLatticesTheory.isom S.hT := Subgroup.inv_mem _ hδ
    have h2 := scal_map_fwd δ⁻¹ (δ * B * δ⁻¹) hδi h
    have hg : Formalism.HermitianLatticesTheory.gmap δ⁻¹ (Formalism.HermitianLatticesTheory.gmap δ Λ) = Λ := by
      ext x
      rw [mem_gmap_iff', mem_gmap_iff']
      show δ.symm (δ x) ∈ Λ ↔ x ∈ Λ
      rw [LinearEquiv.symm_apply_apply]
    have hb : δ⁻¹ * (δ * B * δ⁻¹) * δ⁻¹⁻¹ = B := by group
    rw [hg, hb, mapL_inv_mapL, mapL_inv_mapL, mapL_inv_mapL] at h2
    exact h2
  · exact scal_map_fwd δ B hδ

theorem isPair_map_fwd {Λ : Submodule (𝓞 E) S.V} {F : LFlag S r T} {F' F'' : LFlag S r T'} (δ B : S.V ≃ₗ[E] S.V)
    (hδ : δ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (g : ℕ) (h : IsPair Λ F F' F'' B g) :
    IsPair (Formalism.HermitianLatticesTheory.gmap δ Λ) (Formalism.L2.SG.Saturated.mapL δ hδ F) (Formalism.L2.SG.Saturated.mapL δ hδ F')
      (Formalism.L2.SG.Saturated.mapL δ hδ F'') (δ * B * δ⁻¹) g := by

  have hinv : ∀ x, δ⁻¹ (δ x) = x := fun x => δ.symm_apply_apply x
  obtain ⟨hA, hX, hz, hI⟩ := h
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hδ hA.1) (Subgroup.inv_mem _ hδ)
  · ext x
    rw [mem_gmap_iff', mem_gmap_iff', mem_gmap_iff']
    have e : δ.symm ((δ * B * δ⁻¹).symm x) = B.symm (δ.symm x) := by
      show δ.symm (δ (B.symm (δ.symm x))) = _
      exact δ.symm_apply_apply _
    rw [e]
    constructor
    · intro hy
      have h3 := aut_mem hA hy
      simpa using h3
    · intro hy
      exact aut_symm_mem hA hy
  · intro j
    rw [Formalism.L2.SG.Pf.Xflag_mapL, Formalism.L2.SG.Pf.Xflag_mapL, ← hX j, ← Submodule.map_comp, ← Submodule.map_comp]
    congr 1
    ext y
    change δ (B (δ⁻¹ (δ y))) = δ (B y)
    rw [hinv]
  · change δ (B (δ⁻¹ (δ F'.fl.z))) = δ F''.fl.z
    rw [hinv, hz]
  · intro x' hx' l hl
    rw [Formalism.L2.SG.Pf.Lrep_mapL, mem_gmap_iff'] at hx' hl
    rw [Formalism.L2.SG.Pf.NgX_mapL, Formalism.L2.SG.Pf.NgX_mapL, mem_gmap_iff', mem_gmap_iff']
    have e2 : δ.symm (l - (δ * B * δ⁻¹) x') = δ.symm l - B (δ.symm x') := by
      have h4 : (δ * B * δ⁻¹) x' = δ (B (δ.symm x')) := rfl
      rw [map_sub, h4, LinearEquiv.symm_apply_apply]
    rw [map_sub, e2]
    exact hI _ hx' _ hl

theorem iota_move {Λ : Submodule (𝓞 E) S.V} {F : LFlag S r T} {G₁ G₂ K₁ K₂ : LFlag S r T'}
    {n₁ n₂ m₁ m₂ β : S.V ≃ₗ[E] S.V} (g : ℕ)
    (hn₁ : n₁ ∈ NLam Λ F) (hn₂ : n₂ ∈ NLam Λ F) (hm₁ : m₁ ∈ NLam Λ G₁) (hm₂ : m₂ ∈ NLam Λ G₂)
    (hf₁ : ∀ a, frame K₁ a = n₁ (m₁ (frame G₁ a))) (hf₂ : ∀ a, frame K₂ a = n₂ (m₂ (frame G₂ a)))
    (hβ : IsAutLam S Λ β) (hβX : (Xsp G₁).map (β : S.V →ₗ[E] S.V) = Xsp G₂)
    (h : IotaCompat Λ F G₁ G₂ β g) : IotaCompat Λ F K₁ K₂ (n₂ * m₂ * β * m₁⁻¹ * n₁⁻¹) g := by
  have hX₁ : Xsp K₁ = (Xsp G₁).map (n₁ : S.V →ₗ[E] S.V) := Xsp_DC hm₁ hf₁
  have hX₂ : Xsp K₂ = (Xsp G₂).map (n₂ : S.V →ₗ[E] S.V) := Xsp_DC hm₂ hf₂
  have hXL : ∀ {G K : LFlag S r T'} {n : S.V ≃ₗ[E] S.V}, n ∈ NLam Λ F →
      Xsp K = (Xsp G).map (n : S.V →ₗ[E] S.V) → XLam Λ K = Formalism.HermitianLatticesTheory.gmap n (XLam Λ G) := by
    intro G K n hn hX
    rw [XLam, XLam, gmap_inf', gmap_toO, hn.1.2, hX]
  have hN : ∀ {G K : LFlag S r T'} {n : S.V ≃ₗ[E] S.V}, n ∈ NLam Λ F →
      Xsp K = (Xsp G).map (n : S.V →ₗ[E] S.V) → NgX Λ g F K = Formalism.HermitianLatticesTheory.gmap n (NgX Λ g F G) := by
    intro G K n hn hX
    rw [NgX, NgX, gmap_sup', gmap_sup', gmap_ideal_smul, hn.1.2, NLam_XLam hn, hXL hn hX]
  have hLrep : ∀ {G K : LFlag S r T'} {n : S.V ≃ₗ[E] S.V}, n ∈ NLam Λ F →
      Xsp K = (Xsp G).map (n : S.V →ₗ[E] S.V) → Lrep Λ K = Formalism.HermitianLatticesTheory.gmap n (Lrep Λ G) := by
    intro G K n hn hX
    rw [Lrep, Lrep, gmap_inf', gmap_toO, hn.1.2, hX, orth_map_sat n hn.1.1]
  have hF1 : ∀ (G : LFlag S r T'), XLam Λ F ≤ NgX Λ g F G := fun G => by
    unfold NgX; exact le_sup_right.trans le_sup_left
  have hG1 : ∀ (G : LFlag S r T'), XLam Λ G ≤ NgX Λ g F G := fun G => by
    unfold NgX; exact le_sup_right
  have hshift : ∀ {n : S.V ≃ₗ[E] S.V}, n ∈ NLam Λ F → ∀ {l : S.V}, l ∈ Lrep Λ F → n.symm l - l ∈ XLam Λ F := by
    intro n hn l hl
    have hni := nlam_inv hn
    exact ⟨Λ.sub_mem (aut_symm_mem hn.1 hl.1) hl.1, hni.2.2 l hl.2⟩
  intro x' hx' l hl
  rw [hLrep hn₁ hX₁, mem_gmap_iff'] at hx'
  have hy := h _ hx' l hl
  rw [hN hn₁ hX₁, hN hn₂ hX₂, mem_gmap_iff', mem_gmap_iff', map_sub, map_sub]
  have e : n₂.symm ((n₂ * m₂ * β * m₁⁻¹ * n₁⁻¹) x') = m₂ (β (m₁.symm (n₁.symm x'))) := by
    show n₂.symm (n₂ (m₂ (β (m₁.symm (n₁.symm x'))))) = _; rw [n₂.symm_apply_apply]
  rw [e]
  have s1 := hshift hn₁ hl
  have s2 := hshift hn₂ hl
  have hk : m₂ (β (m₁.symm (n₁.symm x'))) - β (n₁.symm x') ∈ XLam Λ G₂ := by
    refine ⟨Λ.sub_mem (aut_mem hm₂.1 (aut_mem hβ (aut_symm_mem hm₁.1 hx'.1))) (aut_mem hβ hx'.1), ?_⟩
    have := key_mod hm₁ hm₂ hβ.1 hβX (τ := (1 : S.V ≃ₗ[E] S.V)) (fun x hx => hx) (fun x _ => by simp) hx'.2
    exact this
  constructor
  · intro h1
    have h2 := hy.1 (by
      have : l - n₁.symm x' = (n₁.symm l - n₁.symm x') - (n₁.symm l - l) := by abel
      rw [this]; exact sub_mem h1 (hF1 _ s1))
    have : n₂.symm l - m₂ (β (m₁.symm (n₁.symm x'))) =
        (l - β (n₁.symm x')) + (n₂.symm l - l) - (m₂ (β (m₁.symm (n₁.symm x'))) - β (n₁.symm x')) := by abel
    rw [this]; exact sub_mem (add_mem h2 (hF1 _ s2)) (hG1 _ hk)
  · intro h1
    have h2 := hy.2 (by
      have : l - β (n₁.symm x') = (n₂.symm l - m₂ (β (m₁.symm (n₁.symm x')))) - (n₂.symm l - l) +
          (m₂ (β (m₁.symm (n₁.symm x'))) - β (n₁.symm x')) := by abel
      rw [this]; exact add_mem (sub_mem h1 (hF1 _ s2)) (hG1 _ hk))
    have : n₁.symm l - n₁.symm x' = (l - n₁.symm x') + (n₁.symm l - l) := by abel
    rw [this]; exact add_mem h2 (hF1 _ s1)

end MoveC

def IotaRowC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (s₁ s₂ : TT Y u u'),
    rowOf Y.TR (Y.cs u) (Y.cs u') s₁ = rowOf Y.TR (Y.cs u) (Y.cs u') s₂ →
    IotaCompat s₁.lam (lf D (X.Fu u)) s₁.frame s₂.frame (s₂.lin * s₁.lin⁻¹) (gS D)

section Rec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

open Formalism.L2.SG.TermTieOf in
theorem dc_rep {s : TT Y u u'} {t : RT Y u u'} (h : s.toTerm = t) :
    s.lam = t.lam ∧ TermDef.DCRel s.lam (lf D (X.Fu u)) s.frame (repF t) := by
  subst h
  refine ⟨rfl, ?_⟩
  have hrow : IsRowLat D (X.Fu u) s.lam := (Y.rowsOK u).1 s.lam s.mem
  exact (Formalism.L2.SG.Closed.TermEqIff_holds D u u' (X.Fu u) s.lam hrow ⟨s.frame, s.rep.2.2.2.2⟩
    (Quot.out s.toTerm.cls)).1 (Quot.out_eq _).symm

open Formalism.L2.SG.TermTieOf in
theorem mv_spec {s : TT Y u u'} {t : RT Y u u'} (h : s.toTerm = t) :
    s.lam = t.lam ∧ ∃ n ∈ NLam t.lam (lf D (X.Fu u)), ∃ m ∈ NLam t.lam s.frame,
      (∀ a, frame (repF t) a = n (m (frame s.frame a))) ∧ (repF t).zt = n (m s.frame.zt) ∧
      mvOf t.lam (lf D (X.Fu u)) s.frame (repF t) = n * m := by
  obtain ⟨hl, hdc⟩ := dc_rep h
  have hdc' : TermDef.DCRel t.lam (lf D (X.Fu u)) s.frame (repF t) := hl ▸ hdc
  refine ⟨hl, hdc'.choose, hdc'.choose_spec.1, hdc'.choose_spec.2.choose, hdc'.choose_spec.2.choose_spec.1,
    hdc'.choose_spec.2.choose_spec.2.1, hdc'.choose_spec.2.choose_spec.2.2, ?_⟩
  unfold mvOf
  rw [dif_pos hdc']

theorem beta_Xsp (s₁ s₂ : TT Y u u') :
    (Xsp s₁.frame).map ((s₂.lin * s₁.lin⁻¹ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V) =
      Xsp s₂.frame := by
  rw [Xsp_frame, Xsp_frame]
  ext y
  simp only [Submodule.mem_map, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨_, ⟨x0, hx0, rfl⟩, rfl⟩
    refine ⟨x0, hx0, ?_⟩
    show s₂.lin x0 = s₂.lin (s₁.lin.symm (s₁.lin x0))
    rw [LinearEquiv.symm_apply_apply]
  · rintro ⟨x0, hx0, rfl⟩
    refine ⟨s₁.lin x0, ⟨x0, hx0, rfl⟩, ?_⟩
    show s₂.lin (s₁.lin.symm (s₁.lin x0)) = s₂.lin x0
    rw [LinearEquiv.symm_apply_apply]

theorem beta_frame (s₁ s₂ : TT Y u u') (a : Fin (D.R.rS + 1)) :
    (s₂.lin * s₁.lin⁻¹) (frame s₁.frame a) = frame s₂.frame a := by
  rw [frame_apply, frame_apply]
  show s₂.lin (s₁.lin.symm (s₁.lin _)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem beta_aut (s₁ s₂ : TT Y u u') (hl : s₁.lam = s₂.lam) (hl' : s₁.lam' = s₂.lam') :
    IsAutLam (VS D) s₁.lam (s₂.lin * s₁.lin⁻¹) := by
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem (lin_isom s₂) ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem (lin_isom s₁)), ?_⟩
  rw [gmap_mul, gmap_inv (lin_lam s₁), hl', lin_lam s₂, hl]

theorem xflag_map_of_frame {T₀ T₁ : D.host.E} {K : LFlag (VS D) D.R.rS T₀} {K' : LFlag (VS D) D.R.rS T₁}
    {φ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (h : ∀ a, φ (frame K a) = frame K' a) (j : ℕ) :
    (Xflag K j).map (φ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xflag K' j := by

  have he : ∀ i, φ (K.fl.e i) = K'.fl.e i := by
    intro i
    have h1 := h (Fin.castSucc i)
    simpa [Formalism.MainNotions.S.Lat.frame, Formalism.MainNotions.S.FlagG.fvec] using h1
  show (K.fl.Xa j).map (φ : (VS D).V →ₗ[D.host.E] (VS D).V) = K'.fl.Xa j
  unfold Formalism.MainNotions.S.FlagG.Xa
  rw [Submodule.map_span, ← Set.image_comp]
  congr 1
  apply Set.image_congr
  intro i _
  exact he i

theorem rp_data (q : RP Y u u') :
    q.l1.toTerm = q.1.1 ∧ q.l2.toTerm = q.1.2 ∧
      rowOf Y.TR (Y.cs u) (Y.cs u') q.l1 = rowOf Y.TR (Y.cs u) (Y.cs u') q.l2 :=
  ⟨q.2.choose.2, q.2.choose_spec.choose.2, q.2.choose_spec.choose_spec⟩

open Formalism.L2.SG.TermTieOf in

def Bof (q : RP Y u u') : (VS D).V ≃ₗ[D.host.E] (VS D).V :=
  mvOf q.1.2.lam (lf D (X.Fu u)) q.l2.frame (repF q.1.2) * (q.l2.lin * q.l1.lin⁻¹) *
    (mvOf q.1.1.lam (lf D (X.Fu u)) q.l1.frame (repF q.1.1))⁻¹

open Formalism.L2.SG.TermTieOf in

theorem rp_moves (q : RP Y u u') :
    ∃ n₁ n₂ m₁ m₂ : (VS D).V ≃ₗ[D.host.E] (VS D).V,
      n₁ ∈ NLam q.l1.lam (lf D (X.Fu u)) ∧ n₂ ∈ NLam q.l1.lam (lf D (X.Fu u)) ∧
      m₁ ∈ NLam q.l1.lam q.l1.frame ∧ m₂ ∈ NLam q.l1.lam q.l2.frame ∧
      (∀ a, frame (repF q.1.1) a = n₁ (m₁ (frame q.l1.frame a))) ∧ (repF q.1.1).zt = n₁ (m₁ q.l1.frame.zt) ∧
      (∀ a, frame (repF q.1.2) a = n₂ (m₂ (frame q.l2.frame a))) ∧ (repF q.1.2).zt = n₂ (m₂ q.l2.frame.zt) ∧
      Bof q = n₂ * m₂ * (q.l2.lin * q.l1.lin⁻¹) * 1 * m₁⁻¹ * n₁⁻¹ ∧
      q.1.1.lam = q.l1.lam ∧ q.l1.lam = q.l2.lam ∧ q.l1.lam' = q.l2.lam' ∧
      rowOf Y.TR (Y.cs u) (Y.cs u') q.l1 = rowOf Y.TR (Y.cs u) (Y.cs u') q.l2 := by
  obtain ⟨h1, h2, hr⟩ := rp_data q
  obtain ⟨e1, n₁, hn₁, m₁, hm₁, hf₁, hz₁, hmv₁⟩ := mv_spec h1
  obtain ⟨e2, n₂, hn₂, m₂, hm₂, hf₂, hz₂, hmv₂⟩ := mv_spec h2
  have hl : q.l1.lam = q.l2.lam := congrArg (fun r => r.1.1) hr
  have hl' : q.l1.lam' = q.l2.lam' := congrArg (fun r => r.2.1.1) hr
  have E1 : q.1.1.lam = q.l1.lam := e1.symm
  have E2 : q.1.2.lam = q.l1.lam := e2.symm.trans hl.symm
  refine ⟨n₁, n₂, m₁, m₂, E1 ▸ hn₁, E2 ▸ hn₂, E1 ▸ hm₁, E2 ▸ hm₂, hf₁, hz₁, hf₂, hz₂, ?_, E1, hl, hl', hr⟩
  unfold Bof
  rw [hmv₁, hmv₂]
  group

open Formalism.L2.SG.TermTieOf in
theorem representative_s0_eq (q : RP Y u u') :
    Lat.s0 q.1.1.lam (lf D (X.Fu u)) (repF q.1.1) (repF q.1.2) (Bof q) D.R.k = s0T q.l1 q.l2 := by
  obtain ⟨n₁, n₂, m₁, m₂, hn₁, hn₂, hm₁, hm₂, hf₁, hz₁, hf₂, hz₂, hB, E1, hl, hl', hr⟩ := rp_moves q
  have hL₂ : IsLift q.l1.lam q.l2.frame := by rw [hl]; exact lift_frame q.l2
  have hsF := X_le_spanE_XLam (X.Fu u) q.l1.lam ((Y.rowsOK u).1 _ q.l1.mem)
  have hβ := (beta_aut q.l1 q.l2 hl hl').1
  have hT := Th_move hn₁ hn₂ hm₁ hm₂ hf₁ hz₁ hf₂ hz₂ (lift_F q.l1) (lift_frame q.l1) hL₂ hsF (hs_frame q.l1) hβ
    (beta_Xsp q.l1 q.l2) (τ := 1) (fun x hx => hx) (fun x _ => by simp)
  unfold s0T
  rw [if_pos ⟨hl, hl'⟩, E1, hB]
  unfold Lat.s0
  exact congrArg (fun q : ℕ => D.R.k - q) ((congrArg (fun M : Submodule D.host.E (VS D).V => Module.finrank D.host.E M)
    hT).trans (LinearEquiv.finrank_map_eq n₁ _))

open Formalism.L2.SG.TermTieOf in
theorem rp_scal (q : RP Y u u') :
    IsScalar q.1.1.lam (lf D (X.Fu u)) (repF q.1.1) (repF q.1.2) (Bof q) ↔ liftScalar q.l1 q.l2 := by
  obtain ⟨n₁, n₂, m₁, m₂, hn₁, hn₂, hm₁, hm₂, hf₁, hz₁, hf₂, hz₂, hB, E1, hl, hl', hr⟩ := rp_moves q
  have hL₂ : IsLift q.l1.lam q.l2.frame := by rw [hl]; exact lift_frame q.l2
  have hβ := (beta_aut q.l1 q.l2 hl hl').1
  unfold liftScalar
  rw [E1, hB]
  constructor
  · exact scal_move_rev hn₁ hn₂ hm₁ hm₂ hf₁ hz₁ hf₂ hz₂ (lift_F q.l1) (lift_frame q.l1) hL₂ hβ
      (beta_Xsp q.l1 q.l2) (τ := 1) (fun x hx => hx) (fun x _ => by simp)
  · exact scal_move hn₁ hn₂ hm₁ hm₂ hf₁ hz₁ hf₂ hz₂ (lift_F q.l1) (lift_frame q.l1) hL₂ hβ
      (beta_Xsp q.l1 q.l2) (τ := 1) (fun x hx => hx) (fun x _ => by simp)

open Formalism.L2.SG.TermTieOf in
theorem rp_pair (hι : IotaRowC) (q : RP Y u u') :
    IsPair q.1.1.lam (lf D (X.Fu u)) (repF q.1.1) (repF q.1.2) (Bof q) (gS D) := by
  obtain ⟨n₁, n₂, m₁, m₂, hn₁, hn₂, hm₁, hm₂, hf₁, hz₁, hf₂, hz₂, hB, E1, hl, hl', hr⟩ := rp_moves q
  have hA := beta_aut q.l1 q.l2 hl hl'
  rw [E1, hB]
  have hBf : ∀ a, (n₂ * m₂ * (q.l2.lin * q.l1.lin⁻¹) * 1 * m₁⁻¹ * n₁⁻¹) (frame (repF q.1.1) a) = frame (repF q.1.2) a := by
    intro a
    rw [hf₁ a, hf₂ a, ← beta_frame q.l1 q.l2 a]
    show n₂ (m₂ ((q.l2.lin * q.l1.lin⁻¹) (m₁.symm (n₁.symm (n₁ (m₁ _)))))) = _
    rw [n₁.symm_apply_apply, m₁.symm_apply_apply]
  have hAut : IsAutLam (VS D) q.l1.lam (n₂ * m₂ * (q.l2.lin * q.l1.lin⁻¹) * 1 * m₁⁻¹ * n₁⁻¹) := by
    refine ⟨?_, ?_⟩
    · have hI := Formalism.HermitianLatticesTheory.isom (VS D).hT
      exact (Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem ((Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem
        ((Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem ((Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem
          ((Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem hn₂.1.1 hm₂.1.1) hA.1) (Formalism.HermitianLatticesTheory.isom (VS D).hT).one_mem)
        ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hm₁.1.1)) ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hn₁.1.1)
    · rw [gmap_mul, gmap_mul, gmap_mul, gmap_mul, gmap_mul, gmap_inv hn₁.1.2, gmap_inv hm₁.1.2, gmap_one, hA.2,
        hm₂.1.2, hn₂.1.2]
  refine ⟨hAut, fun j => xflag_map_of_frame hBf j, ?_, ?_⟩
  · have := hBf (Fin.last _)
    rwa [frame_last_sat, frame_last_sat] at this
  · have := iota_move (gS D) hn₁ hn₂ hm₁ hm₂ hf₁ hf₂ hA (beta_Xsp q.l1 q.l2) (hι D X Y u u' q.l1 q.l2 hr)
    rwa [show n₂ * m₂ * (q.l2.lin * q.l1.lin⁻¹) * 1 * m₁⁻¹ * n₁⁻¹ = n₂ * m₂ * (q.l2.lin * q.l1.lin⁻¹) * m₁⁻¹ * n₁⁻¹ by
      group]

end Rec

open Formalism.L2.SG.TermTieOf in
set_option maxHeartbeats 800000 in

theorem pairTies_of (hι : IotaRowC) : Formalism.L2.SG.TermTieOf.PairTiesAll := by
  intro D X Y hF W hI
  have hlf : ∀ u, lf D (FlagOfWord W u) = Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) (lf D (X.Fu u)) := fun u => rfl
  have key : ∀ {u u' : D.what₂.Word} (p : D.s.Pair u u'),
      lamOf W hI (D.s.pfst p) = Formalism.HermitianLatticesTheory.gmap (W.δ u) (hI.eP u u' p).1.1.lam ∧
      fl'Of W hI (D.s.pfst p) = Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) (repF (hI.eP u u' p).1.1) ∧
      fl'Of W hI (D.s.psnd p) = Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) (repF (hI.eP u u' p).1.2) ∧
      betaOf W hI p = W.δ u * Bof (hI.eP u u' p) * (W.δ u)⁻¹ := by
    intro u u' p
    have e1 : tc hI (D.s.pfst p) = (hI.eP u u' p).1.1 := hI.pfst p
    have e2 : tc hI (D.s.psnd p) = (hI.eP u u' p).1.2 := hI.psnd p
    refine ⟨?_, ?_, ?_, rfl⟩
    · show Formalism.HermitianLatticesTheory.gmap (W.δ u) (tc hI (D.s.pfst p)).lam = _; rw [e1]
    · show Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) (repF (tc hI (D.s.pfst p))) = _; rw [e1]
    · show Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) (repF (tc hI (D.s.psnd p))) = _; rw [e2]
  refine ⟨fun {u u'} p => ?_, fun {u u'} p => ?_, fun {u u'} p _ => ?_⟩
  · obtain ⟨k1, k2, k3, k4⟩ := key p
    rw [k1, k2, k3, k4, hlf]
    exact isPair_map_fwd (W.δ u) (Bof (hI.eP u u' p)) (W.isom u) (gS D) (rp_pair hι (hI.eP u u' p))
  · obtain ⟨k1, k2, k3, k4⟩ := key p
    rw [k1, k2, k3, k4, hlf, hI.s0 p]
    exact (representative_s0_eq (hI.eP u u' p)).symm.trans (s0_gmap_mapL_conj_eq_s0 (W.δ u) (Bof (hI.eP u u' p)) (W.isom u) D.R.k).symm
  · obtain ⟨k1, k2, k3, k4⟩ := key p
    rw [k1, k2, k3, k4, hlf, hI.scalarPair p]
    exact (rp_scal (hI.eP u u' p)).symm.trans (scal_map (W.δ u) (Bof (hI.eP u u' p)) (W.isom u)).symm

end Formalism.L2.SG.Pf.FinXP

end
