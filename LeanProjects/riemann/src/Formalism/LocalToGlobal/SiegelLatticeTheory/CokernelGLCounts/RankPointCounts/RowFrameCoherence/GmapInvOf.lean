import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RowForm.ScalT

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem gmap_mul (a b : S.V ≃ₗ[E] S.V) (L : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap (a * b) L = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b L) := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨b y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem gmap_one (L : Submodule (𝓞 E) S.V) : Formalism.HermitianLatticesTheory.gmap (1 : S.V ≃ₗ[E] S.V) L = L := by
  ext x
  simp [Formalism.HermitianLatticesTheory.gmap]

theorem gmap_inv_of {a : S.V ≃ₗ[E] S.V} {L L' : Submodule (𝓞 E) S.V} (h : Formalism.HermitianLatticesTheory.gmap a L' = L) :
    Formalism.HermitianLatticesTheory.gmap a⁻¹ L = L' := by
  rw [← h, ← gmap_mul, inv_mul_cancel, gmap_one]

theorem xflag_mapLF {T : E} (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (j : ℕ) :
    Xflag (mapLF γ F) j = (Xflag F j).map (γ : S.V →ₗ[E] S.V) := by
  simp only [Xflag, mapLF, dif_pos hγ, Formalism.MainNotions.S.FlagG.Xa, mapFlag, Submodule.map_span, Set.image_image]
  rfl

theorem z_mapLF {T : E} (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) :
    (mapLF γ F).fl.z = γ F.fl.z := by
  simp only [mapLF, dif_pos hγ, mapFlag]

theorem isPair_quot {T T' : E} (Λ Λ' : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T')
    (γ₁ γ₂ : S.V ≃ₗ[E] S.V) (h₁ : γ₁ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (h₂ : γ₂ ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (hl₁ : Formalism.HermitianLatticesTheory.gmap γ₁ Λ' = Λ) (hl₂ : Formalism.HermitianLatticesTheory.gmap γ₂ Λ' = Λ)
    (hι : IotaCompat Λ F (mapLF γ₁ F') (mapLF γ₂ F') (γ₂ * γ₁⁻¹) g) :
    IsPair Λ F (mapLF γ₁ F') (mapLF γ₂ F') (γ₂ * γ₁⁻¹) g := by
  refine ⟨⟨(Formalism.HermitianLatticesTheory.isom S.hT).mul_mem h₂ ((Formalism.HermitianLatticesTheory.isom S.hT).inv_mem h₁), ?_⟩, fun j => ?_, ?_, hι⟩
  · rw [gmap_mul, gmap_inv_of hl₁, hl₂]
  · rw [xflag_mapLF γ₁ h₁, xflag_mapLF γ₂ h₂, ← Submodule.map_comp]
    congr 1
    ext x
    simp
  · rw [z_mapLF γ₁ h₁, z_mapLF γ₂ h₂]
    simp

end Gen

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)

def LiftIotaC : Prop :=
  ∀ s₁ s₂ : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'),
    s₁.G ≠ 0 → s₂.G ≠ 0 → s₁.generic → s₂.generic →
    (Y.tO u u').rowOf s₁ = (Y.tO u u').rowOf s₂ →
      IotaCompat s₁.lam (lf D (X.Fu u)) s₁.frame s₂.frame (s₂.lin * s₁.lin⁻¹) (gS D)

variable (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

theorem scalTC_of (hκ : Formalism.L2.SG.DataInst.RowLabel κ) (hι : LiftIotaC X Y u u')
    (hg : ∀ i, 3 ≤ D.host.g i ∧ Formalism.L2.SG.LemmaN.Unram D.host.E (D.host.g i)) :
    ScalTC X Y u u' κ := by
  intro s₁ s₂ hG₁ hG₂ hn₁ hn₂ hrow
  have hG₁' : s₁.G ≠ 0 := fun h => hG₁ (by show Formalism.L2.SG.TermOp.Gt s₁ = 0; simp [Formalism.L2.SG.TermOp.Gt, h])
  have hG₂' : s₂.G ≠ 0 := fun h => hG₂ (by show Formalism.L2.SG.TermOp.Gt s₂ = 0; simp [Formalism.L2.SG.TermOp.Gt, h])
  have hι' := hι s₁ s₂ hG₁' hG₂' hn₁ hn₂ hrow
  rw [hκ _ _ ⟨hn₁, hG₁'⟩ ⟨hn₂, hG₂'⟩]
  change (s0T s₁ s₂ = 1 ∧ scalT s₁ s₂) ↔ _
  have hrow' : rowOf Y.TR (Y.cs u) (Y.cs u') s₁ = rowOf Y.TR (Y.cs u) (Y.cs u') s₂ := hrow
  obtain ⟨l₁, m₁, l₁', m₁', c₁⟩ := s₁
  obtain ⟨l₂, m₂, l₂', m₂', c₂⟩ := s₂
  have hl : l₁ = l₂ := congrArg (fun q => q.1.1) hrow'
  have hl' : l₁' = l₂' := congrArg (fun q => q.2.1.1) hrow'
  subst hl hl'
  set s₁ : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') := ⟨l₁, m₁, l₁', m₁', c₁⟩ with hs₁
  set s₂ : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') := ⟨l₁, m₂, l₁', m₂', c₂⟩ with hs₂
  have hRL : IsRowLat D (X.Fu u) l₁ := (Y.rowsOK u).1 l₁ m₁
  have hP : IsPair l₁ (lf D (X.Fu u)) s₁.frame s₂.frame (s₂.lin * s₁.lin⁻¹) (gS D) :=
    isPair_quot l₁ l₁' (gS D) (lf D (X.Fu u)) (lf D (X.Fu u')) s₁.lin s₂.lin s₁.rep.2.2.1 s₂.rep.2.2.1
      s₁.rep.2.2.2.1 s₂.rep.2.2.2.1 hι'
  have hEq := Formalism.L2.SG.Closed.TermEqIff_holds D u u' (X.Fu u) l₁ hRL
  have hGF := (Formalism.L2.SG.Closed.TermFun_holds D u u' (X.Fu u) l₁ hRL).1
  let x₁ : Carrier (PD D l₁ (lf D (X.Fu u)) u') := ⟨s₁.frame, s₁.rep.2.2.2.2⟩
  let x₂ : Carrier (PD D l₁ (lf D (X.Fu u)) u') := ⟨s₂.frame, s₂.rep.2.2.2.2⟩
  have gv : ∀ x : Carrier (PD D l₁ (lf D (X.Fu u)) u'),
      Gt l₁ (lf D (X.Fu u)) (PD D l₁ (lf D (X.Fu u)) u') (TermDef.mk _ _ _ x) = Gval (lf D (X.Fu u)) x.1 := by
    intro x
    exact hGF _ _ ((hEq _ _).1 (Quot.out_eq (TermDef.mk l₁ (lf D (X.Fu u)) (PD D l₁ (lf D (X.Fu u)) u') x)))
  have hx₁ : Gval (lf D (X.Fu u)) x₁.1 ≠ 0 := by rw [← gv]; exact hG₁'
  have hx₂ : Gval (lf D (X.Fu u)) x₂.1 ≠ 0 := by rw [← gv]; exact hG₂'
  have hs0 : s0T s₁ s₂ = Lat.s0 l₁ (lf D (X.Fu u)) s₁.frame s₂.frame (s₂.lin * s₁.lin⁻¹) D.R.k := by
    unfold s0T
    exact if_pos ⟨rfl, rfl⟩
  have hsc : scalT s₁ s₂ ↔ (Lat.s0 l₁ (lf D (X.Fu u)) s₁.frame s₂.frame (s₂.lin * s₁.lin⁻¹) D.R.k = 1 ∧
      IsScalar l₁ (lf D (X.Fu u)) s₁.frame s₂.frame (s₂.lin * s₁.lin⁻¹)) := by
    unfold scalT
    exact ⟨fun h => h.2, fun h => ⟨⟨rfl, rfl⟩, h⟩⟩
  rw [hs0, hsc]
  constructor
  · rintro ⟨h1, -, h2⟩
    exact ⟨⟨l₁, m₁, x₁, x₂, hx₁, hx₂, s₂.lin * s₁.lin⁻¹, hP⟩, rfl, rfl, h1, h2⟩
  · rintro ⟨⟨pl, pm, y₁, y₂, hy₁, hy₂, β, hβ⟩, hp₁, hp₂, hsp⟩
    have hp₁' : (Term.mk pl pm (TermDef.mk _ _ _ y₁) : Term D u u' (X.Fu u) (Y.what₂ u)) =
        Term.mk l₁ m₁ (TermDef.mk _ _ _ x₁) := hp₁
    obtain ⟨hpl, e₁⟩ := Term.mk.inj hp₁'
    subst pl
    have hp₂' : (Term.mk l₁ pm (TermDef.mk _ _ _ y₂) : Term D u u' (X.Fu u) (Y.what₂ u)) =
        Term.mk l₁ m₂ (TermDef.mk _ _ _ x₂) := hp₂
    obtain ⟨-, e₂⟩ := Term.mk.inj hp₂'
    have r₁ := (hEq y₁ x₁).1 (eq_of_heq e₁)
    have r₂ := (hEq y₂ x₂).1 (eq_of_heq e₂)
    have hSE := Formalism.L2.SG.Closed.ScalarEquiv_holds D u u' (X.Fu u) l₁ hRL
    have hRF := Formalism.L2.SG.Closed.ScalarRepFree_holds D u u' (X.Fu u) l₁ hRL
    have a1 : Formalism.L2.SG.Corank.ScalRelD D u' (X.Fu u) l₁ ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩ := ⟨β, hβ, hsp.1, hsp.2⟩
    have a2 := hRF ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩ ⟨x₂, hx₂⟩ r₂ a1
    have a3 := hRF ⟨x₂, hx₂⟩ ⟨y₁, hy₁⟩ ⟨x₁, hx₁⟩ r₁ (hSE.symm a2)
    obtain ⟨β', hβ', h1, h2⟩ := hSE.symm a3
    have hB := Formalism.L2.SG.Closed.BetaFree_holds D u u' hg (X.Fu u) l₁ hRL x₁ x₂ hx₁ hx₂ β' _ hβ' hP
    have e0 : Lat.s0 l₁ (lf D (X.Fu u)) s₁.frame s₂.frame (s₂.lin * s₁.lin⁻¹) D.R.k = 1 := hB.1 ▸ h1
    exact ⟨e0, e0, hB.2.1 h2⟩

end Formalism.L2.SG.Pf.RowForm.ScalT
