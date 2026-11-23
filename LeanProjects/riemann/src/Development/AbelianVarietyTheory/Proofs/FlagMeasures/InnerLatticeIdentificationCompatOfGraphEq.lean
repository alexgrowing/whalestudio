import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IotaGraph

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ}

theorem mem_gmap_iff (ψ : S.V ≃ₗ[E] S.V) (Λ : Submodule (𝓞 E) S.V) (x : S.V) :
    x ∈ Formalism.HermitianLatticesTheory.gmap ψ Λ ↔ ψ.symm x ∈ Λ := by
  unfold Formalism.HermitianLatticesTheory.gmap
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨ψ.symm x, h, by simp⟩

theorem mem_map_iff (ψ : S.V ≃ₗ[E] S.V) (U : Submodule E S.V) (x : S.V) :
    x ∈ U.map (ψ : S.V →ₗ[E] S.V) ↔ ψ.symm x ∈ U := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨ψ.symm x, h, by simp⟩

theorem mem_orth_iff (U : Submodule E S.V) (x : S.V) :
    x ∈ orth S U ↔ ∀ y ∈ U, S.hT y x = 0 := by
  unfold orth
  simp [Submodule.mem_iInf]

theorem mem_orth_map (ψ : S.V ≃ₗ[E] S.V) (hψ : ψ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (U : Submodule E S.V)
    (x : S.V) : x ∈ orth S (U.map (ψ : S.V →ₗ[E] S.V)) ↔ ψ.symm x ∈ orth S U := by
  have hi : ∀ a b, S.hT (ψ a) (ψ b) = S.hT a b := hψ
  rw [mem_orth_iff, mem_orth_iff]
  constructor
  · intro h y hy
    have := h (ψ y) ⟨y, hy, rfl⟩
    rw [← hi y (ψ.symm x)]
    simpa using this
  · rintro h _ ⟨y, hy, rfl⟩
    have := h y hy
    rw [← hi y (ψ.symm x)] at this
    simpa using this

variable {T T' : E}

theorem mem_Lrep_map (ψ : S.V ≃ₗ[E] S.V) (hψ : ψ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (Λ : Submodule (𝓞 E) S.V)
    (F G : LFlag S r T) (hF : (Xsp F).map (ψ : S.V →ₗ[E] S.V) = Xsp G) (x : S.V) :
    x ∈ Lrep (Formalism.HermitianLatticesTheory.gmap ψ Λ) G ↔ ψ.symm x ∈ Lrep Λ F := by
  unfold Lrep
  rw [Submodule.mem_inf, Submodule.mem_inf, mem_gmap_iff, toO, toO, Submodule.restrictScalars_mem,
    Submodule.restrictScalars_mem, ← hF, mem_orth_map ψ hψ]

theorem gmap_eq (ψ : S.V ≃ₗ[E] S.V) (Λ : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap ψ Λ = Λ.map (ψ.restrictScalars (𝓞 E) : S.V →ₗ[𝓞 E] S.V) := by
  ext x
  rw [mem_gmap_iff, Submodule.mem_map_equiv]
  rfl

theorem XLam_map (ψ : S.V ≃ₗ[E] S.V) (Λ : Submodule (𝓞 E) S.V)
    (F G : LFlag S r T) (hF : (Xsp F).map (ψ : S.V →ₗ[E] S.V) = Xsp G) :
    XLam (Formalism.HermitianLatticesTheory.gmap ψ Λ) G = (XLam Λ F).map (ψ.restrictScalars (𝓞 E) : S.V →ₗ[𝓞 E] S.V) := by
  ext x
  rw [Submodule.mem_map_equiv]
  unfold XLam
  rw [Submodule.mem_inf, Submodule.mem_inf, mem_gmap_iff, toO, toO, Submodule.restrictScalars_mem,
    Submodule.restrictScalars_mem, ← hF, mem_map_iff]
  rfl

theorem mem_NgX_map (ψ : S.V ≃ₗ[E] S.V) (Λ : Submodule (𝓞 E) S.V) (g : ℕ)
    (F G : LFlag S r T) (F' G' : LFlag S r T') (hF : (Xsp F).map (ψ : S.V →ₗ[E] S.V) = Xsp G)
    (hF' : (Xsp F').map (ψ : S.V →ₗ[E] S.V) = Xsp G') (x : S.V) :
    x ∈ NgX (Formalism.HermitianLatticesTheory.gmap ψ Λ) g G G' ↔ ψ.symm x ∈ NgX Λ g F F' := by
  have h : NgX (Formalism.HermitianLatticesTheory.gmap ψ Λ) g G G' =
      (NgX Λ g F F').map (ψ.restrictScalars (𝓞 E) : S.V →ₗ[𝓞 E] S.V) := by
    unfold NgX
    rw [Submodule.map_sup, Submodule.map_sup, Submodule.map_smul'', XLam_map ψ Λ F G hF,
      XLam_map ψ Λ F' G' hF', gmap_eq]
  rw [h, Submodule.mem_map_equiv]
  rfl

end Gen

end GlobalTheory.IotaGraph

namespace GlobalTheory.IotaGraph

section Dv

variable {D : D7} {T T' : D.host.E}

theorem mem_graph_iff (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (Λ : LV D)
    {x' l : (VS D).V} (hx' : x' ∈ Lrep Λ F') (hl : l ∈ Lrep Λ F) :
    (x', l) ∈ (gdat F F' Λ).2.2 ↔ l - x' ∈ NgX Λ (gS D) F F' := by
  simp only [gdat, Set.mem_setOf_eq]
  constructor
  · rintro ⟨l', hl', l₀, hl₀, h1, h2, h3⟩
    have hx'Λ : x' ∈ Λ := (Submodule.mem_inf.1 hx').1
    have hlΛ : l ∈ Λ := (Submodule.mem_inf.1 hl).1
    have hl'Λ : l' ∈ Λ := (Submodule.mem_inf.1 hl').1
    have hl₀Λ : l₀ ∈ Λ := (Submodule.mem_inf.1 hl₀).1
    have a1 : x' - l' ∈ XLam Λ F' := Submodule.mem_inf.2 ⟨Λ.sub_mem hx'Λ hl'Λ, h1⟩
    have a2 : l - l₀ ∈ XLam Λ F := Submodule.mem_inf.2 ⟨Λ.sub_mem hlΛ hl₀Λ, h2⟩
    have b1 : x' - l' ∈ NgX Λ (gS D) F F' := by
      unfold NgX; exact Submodule.mem_sup_right a1
    have b2 : l - l₀ ∈ NgX Λ (gS D) F F' := by
      unfold NgX; exact Submodule.mem_sup_left (Submodule.mem_sup_right a2)
    have e : l - x' = (l - l₀) + (l₀ - l') - (x' - l') := by abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.add_mem _ b2 h3) b1
  · intro h
    exact ⟨x', hx', l, hl, by simp, by simp, h⟩

theorem mem_graph_of_sub (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (Λ : LV D)
    {p q : (VS D).V × (VS D).V} (h1 : q.1 - p.1 ∈ Xsp F') (h2 : q.2 - p.2 ∈ Xsp F)
    (hp : p ∈ (gdat F F' Λ).2.2) : q ∈ (gdat F F' Λ).2.2 := by
  simp only [gdat, Set.mem_setOf_eq] at hp ⊢
  obtain ⟨l', hl', l, hl, k1, k2, k3⟩ := hp
  refine ⟨l', hl', l, hl, ?_, ?_, k3⟩
  · have e : q.1 - l' = (q.1 - p.1) + (p.1 - l') := by abel
    rw [e]; exact Submodule.add_mem _ h1 k1
  · have e : q.2 - l = (q.2 - p.2) + (p.2 - l) := by abel
    rw [e]; exact Submodule.add_mem _ h2 k2

theorem mem_graph_congr (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (Λ : LV D)
    {p q : (VS D).V × (VS D).V} (h1 : q.1 - p.1 ∈ Xsp F') (h2 : q.2 - p.2 ∈ Xsp F) :
    p ∈ (gdat F F' Λ).2.2 ↔ q ∈ (gdat F F' Λ).2.2 := by
  refine ⟨mem_graph_of_sub F F' Λ h1 h2, mem_graph_of_sub F F' Λ ?_ ?_⟩
  · rw [← neg_sub]; exact Submodule.neg_mem _ h1
  · rw [← neg_sub]; exact Submodule.neg_mem _ h2

theorem mem_graph_map (ψ : GV D) (hψ : ψ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (F G : LFlag (VS D) D.R.rS T) (F' G' : LFlag (VS D) D.R.rS T')
    (hF : (Xsp F).map (ψ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp G)
    (hF' : (Xsp F').map (ψ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp G') (Λ : LV D) (x y : (VS D).V) :
    (x, y) ∈ (gdat F F' Λ).2.2 ↔ (ψ x, ψ y) ∈ (gdat G G' (Formalism.HermitianLatticesTheory.gmap ψ Λ)).2.2 := by
  simp only [gdat, Set.mem_setOf_eq]
  constructor
  · rintro ⟨l', hl', l, hl, h1, h2, h3⟩
    refine ⟨ψ l', ?_, ψ l, ?_, ?_, ?_, ?_⟩
    · rw [mem_Lrep_map ψ hψ Λ F' G' hF']; simpa using hl'
    · rw [mem_Lrep_map ψ hψ Λ F G hF]; simpa using hl
    · rw [← hF', mem_map_iff]; simpa using h1
    · rw [← hF, mem_map_iff]; simpa using h2
    · rw [mem_NgX_map ψ Λ (gS D) F G F' G' hF hF']; simpa using h3
  · rintro ⟨l', hl', l, hl, h1, h2, h3⟩
    refine ⟨ψ.symm l', (mem_Lrep_map ψ hψ Λ F' G' hF' l').1 hl', ψ.symm l,
      (mem_Lrep_map ψ hψ Λ F G hF l).1 hl, ?_, ?_, ?_⟩
    · rw [← hF', mem_map_iff] at h1; simpa using h1
    · rw [← hF, mem_map_iff] at h2; simpa using h2
    · rw [mem_NgX_map ψ Λ (gS D) F G F' G' hF hF'] at h3; simpa using h3

end Dv

end GlobalTheory.IotaGraph

namespace GlobalTheory

open GlobalTheory.IotaGraph

theorem iotaCompat_of_graph_eq : ∀ (D : D7) (T T' : D.host.E) (F₀ B : LFlag (VS D) D.R.rS T) (P₁ P₂ B' : LFlag (VS D) D.R.rS T') (Λ : LV D) (ψ₀ ψ₁ β : GV D), ψ₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → ψ₁ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → (Xsp F₀).map (ψ₀ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp B → (Xsp F₀).map (ψ₁ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp B → (Xsp P₁).map (ψ₀ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp B' → (Xsp P₂).map (ψ₁ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp B' → (gdat B B' (Formalism.HermitianLatticesTheory.gmap ψ₀ Λ)).2.2 = (gdat B B' (Formalism.HermitianLatticesTheory.gmap ψ₁ Λ)).2.2 → β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → Formalism.HermitianLatticesTheory.gmap β Λ = Λ → (Xsp P₁).map (β : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp P₂ → (∀ l ∈ Lrep Λ F₀, (ψ₁⁻¹ * ψ₀) l - l ∈ Xsp F₀) → (∀ x' ∈ Lrep Λ P₁, (ψ₁⁻¹ * ψ₀) x' - β x' ∈ Xsp P₂) → IotaCompat Λ F₀ P₁ P₂ β (gS D) := by
  intro D T T' F₀ B P₁ P₂ B' Λ ψ₀ ψ₁ β h0 h1 hF0 hF1 hP1 hP2 hgr hβ hβΛ hβP hml hmx x' hx' l hl
  have hc : ∀ y, ψ₁ ((ψ₁⁻¹ * ψ₀) y) = ψ₀ y := fun y => ψ₁.apply_symm_apply (ψ₀ y)

  have hβx : β x' ∈ Lrep Λ P₂ := by
    have := (mem_Lrep_map (S := VS D) β hβ Λ P₁ P₂ hβP (β x')).2 (by simpa using hx')
    rwa [hβΛ] at this
  have e1 := mem_graph_iff F₀ P₁ Λ hx' hl
  have e2 := mem_graph_map ψ₀ h0 F₀ B P₁ B' hF0 hP1 Λ x' l
  have e3 := mem_graph_map ψ₁ h1 F₀ B P₂ B' hF1 hP2 Λ ((ψ₁⁻¹ * ψ₀) x') ((ψ₁⁻¹ * ψ₀) l)
  rw [hc, hc] at e3
  have e4 := mem_graph_congr F₀ P₂ Λ (p := ((ψ₁⁻¹ * ψ₀) x', (ψ₁⁻¹ * ψ₀) l)) (q := (β x', l))
    (by rw [← neg_sub]; exact Submodule.neg_mem _ (hmx x' hx'))
    (by rw [← neg_sub]; exact Submodule.neg_mem _ (hml l hl))
  have e5 := mem_graph_iff F₀ P₂ Λ hβx hl
  rw [← e1, ← e5, e2, hgr, ← e3, e4]

end GlobalTheory
