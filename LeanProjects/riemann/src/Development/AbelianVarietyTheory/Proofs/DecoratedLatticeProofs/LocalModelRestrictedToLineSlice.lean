import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionProductsSlicesOrthogonalDecompositi
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdFnMemSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SliceLine

open GlobalTheory.MixModel.OrthDec GlobalTheory.LocFlat.CFac

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

theorem ι_mul (x : k) (b : AE D) : p.ι x * b = p.ι (x * p.π b) := by
  have h : p.ι (x * p.π b) = p.e * (p.ι x * b) := by
    calc p.ι (x * p.π b) = p.ι (p.π (p.ι x) * p.π b) := by rw [p.π_ι]
      _ = p.ι (p.π (p.ι x * b)) := by rw [p.π.map_mul]
      _ = p.e * (p.ι x * b) := p.ι_π _
  rw [h, ← mul_assoc, GlobalTheory.LocMod.Witness.e_ι]

theorem map_ι_mul {a b c : Type} [Fintype b] (M : Matrix a b k) (N : Matrix b c (AE D)) :
    M.map p.ι * N = (M * N.map p.π).map p.ι := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, ι_mul]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem frame_card {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k N Y) : Fintype.card Y = N := by
  have e : (Y → k) ≃ₗ[k] (Fin N → k) := LinearEquiv.ofLinear (Matrix.toLin' F.β) (Matrix.toLin' F.γ)
    (by rw [← Matrix.toLin'_mul, F.βγ, Matrix.toLin'_one]) (by rw [← Matrix.toLin'_mul, F.γβ, Matrix.toLin'_one])
  simpa using e.finrank_eq

def splitCols (n n' : Type) : Matrix n (n' ⊕ Unit) k ≃ₜ Matrix n n' k × Matrix n Unit k where
  toFun x := (x.toCols₁, x.toCols₂)
  invFun q := fromCols q.1 q.2
  left_inv x := fromCols_toCols x
  right_inv q := by simp
  continuous_toFun := by
    refine Continuous.prodMk ?_ ?_
    · exact continuous_matrix fun i j => continuous_id.matrix_elem i (Sum.inl j)
    · exact continuous_matrix fun i j => continuous_id.matrix_elem i (Sum.inr j)
  continuous_invFun := by
    refine continuous_matrix fun i j => ?_
    cases j with
    | inl a => exact continuous_fst.matrix_elem i a
    | inr u => exact continuous_snd.matrix_elem i u

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def box (Ξ : SB (Matrix n n' k)) : SB (Matrix n Unit k) →ₗ[ℂ] SB (Matrix n (n' ⊕ Unit) k) where
  toFun c := comapH (splitCols n n') (prodSB Ξ c)
  map_add' c c' := Subtype.ext (funext fun x => by simp [splitCols, mul_add])
  map_smul' a c := Subtype.ext (funext fun x => by simp [splitCols]; ring)

theorem box_apply (Ξ : SB (Matrix n n' k)) (c : SB (Matrix n Unit k)) (x : Matrix n (n' ⊕ Unit) k) :
    (box Ξ c).1 x = Ξ.1 x.toCols₁ * c.1 x.toCols₂ := rfl

end GlobalTheory.SliceLine

namespace GlobalTheory.SliceLine

open GlobalTheory.MixModel.OrthDec GlobalTheory.LocFlat.CFac

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

theorem heis_slice {S A L T : HSp D} (d : OrthDec S A L) (ψ : AddChar (AF D.host.F) ℂ) (f : WO S T → ℂ)
    (u : WO A T) (w v : WO L T) :
    heisO ψ S T ((d.resS T).symm (0, v)) f ((d.resS T).symm (u, w)) =
      heisO ψ L T v (fun w => f ((d.resS T).symm (u, w))) w := by
  simp only [heisO]
  rw [d.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, zero_add,
    ← map_add, Prod.mk_add_mk, add_zero]

theorem symplO_zero_right' (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  simp [symplO, hO]

theorem isHalf_slice {S A L T : HSp D} (d : OrthDec S A L) {a : AE D} {y : WO L T} (hy : IsHalf a y) :
    IsHalf a ((d.resS T).symm (0, y)) := by
  intro i j
  rw [resS_symm_apply, Matrix.zero_mul, zero_add, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← mul_assoc, hy i l]

variable {ρ : ℕ} {B : BesLev D ρ} {s : k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {FA : Frame k B.A.rank n'} {F₀ : Frame k B.V₀.rank (n' ⊕ Unit)} {FL : Frame k B.L.rank Unit}

theorem beta_eq (h : p.IsCoreFrame B s FA F₀) (hL : ∀ r, FL.β r () = s * p.pr (B.ζ r)) :
    F₀.β = fromCols (B.o.iA.map (p.π.comp (incA D)) * FA.β) (B.o.iB.map (p.π.comp (incA D)) * FL.β) := by
  ext r (a | u)
  · exact h.1 r a
  · cases u
    rw [h.2 r, fromCols_apply_inr, Matrix.mul_apply]
    simp only [vecB, Matrix.mulVec, dotProduct, Place.pr, map_sum, map_mul, Matrix.map_apply, hL, RingHom.comp_apply,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

end GlobalTheory.SliceLine

namespace GlobalTheory.SliceLine

open GlobalTheory.MixModel.OrthDec GlobalTheory.LocFlat.CFac

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
variable {ρ : ℕ} {B : BesLev D ρ} {s : k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {FA : Frame k B.A.rank n'} {F₀ : Frame k B.V₀.rank (n' ⊕ Unit)} {FL : Frame k B.L.rank Unit}

theorem rat_map_π {a b : ℕ} (M : Matrix (Fin a) (Fin b) D.host.E) : (rat M).map p.π = M.map (p.π.comp (incA D)) := rfl

theorem up_fromCols (h : p.IsCoreFrame B s FA F₀) (hL : ∀ r, FL.β r () = s * p.pr (B.ζ r)) {S : HSp D}
    (FS : Frame k S.rank n) (x : Matrix n Unit k) :
    p.up F₀ FS (fromCols 0 x) = (B.o.resS S).symm (0, p.up FL FS x) := by
  have k1 : x * FL.γ * B.o.qB.map (p.π.comp (incA D)) * F₀.β = fromCols (0 : Matrix n n' k) x := by
    rw [beta_eq p h hL, Matrix.mul_fromCols]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (B.o.qB.map _) (B.o.iA.map _), ← Matrix.map_mul, B.o.qB_iA,
      ← Matrix.mul_assoc (B.o.qB.map _) (B.o.iB.map _), ← Matrix.map_mul, B.o.qB_iB]
    simp [FL.γβ]
  have k2 : fromCols (0 : Matrix n n' k) x * F₀.γ = x * FL.γ * B.o.qB.map (p.π.comp (incA D)) := by
    rw [← k1, Matrix.mul_assoc (x * FL.γ * B.o.qB.map (p.π.comp (incA D))) F₀.β F₀.γ, F₀.βγ, Matrix.mul_one]
  rw [resS_symm_apply, Matrix.zero_mul, zero_add]
  unfold Place.up
  rw [pB, map_ι_mul, rat_map_π]
  congr 1
  rw [Matrix.mul_assoc FS.β (fromCols 0 x) F₀.γ, k2]
  simp only [Matrix.mul_assoc]

theorem resS_up_snd (h : p.IsCoreFrame B s FA F₀) (hL : ∀ r, FL.β r () = s * p.pr (B.ζ r)) {S : HSp D}
    (FS : Frame k S.rank n) (t : Matrix n (n' ⊕ Unit) k) :
    (B.o.resS S (p.up F₀ FS t)).2 = p.up FL FS t.toCols₂ := by
  have k1 : t * F₀.γ * B.o.iB.map (p.π.comp (incA D)) * FL.β = t.toCols₂ := by
    calc t * F₀.γ * B.o.iB.map (p.π.comp (incA D)) * FL.β
        = ((t * F₀.γ) * fromCols (B.o.iA.map (p.π.comp (incA D)) * FA.β)
            (B.o.iB.map (p.π.comp (incA D)) * FL.β)).toCols₂ := by
          rw [Matrix.mul_fromCols, toCols₂_fromCols, Matrix.mul_assoc (t * F₀.γ)]
      _ = ((t * F₀.γ) * F₀.β).toCols₂ := by rw [← beta_eq p h hL]
      _ = t.toCols₂ := by rw [Matrix.mul_assoc, F₀.γβ, Matrix.mul_one]
  have k2 : t * F₀.γ * B.o.iB.map (p.π.comp (incA D)) = t.toCols₂ * FL.γ := by
    rw [← k1, Matrix.mul_assoc (t * F₀.γ * B.o.iB.map (p.π.comp (incA D))) FL.β FL.γ, FL.βγ, Matrix.mul_one]
  rw [resS_apply]
  dsimp only
  unfold Place.up
  rw [jB, map_ι_mul, rat_map_π]
  simp only [Matrix.mul_assoc] at k2 ⊢
  rw [k2]

end GlobalTheory.SliceLine

namespace GlobalTheory.SliceLine

open GlobalTheory.MixModel.OrthDec GlobalTheory.LocFlat.CFac

theorem toCols_add {k n n' : Type} [Field k] (t : Matrix n (n' ⊕ Unit) k) (x : Matrix n Unit k) :
    (t + fromCols (0 : Matrix n n' k) x).toCols₁ = t.toCols₁ ∧ (t + fromCols (0 : Matrix n n' k) x).toCols₂ = t.toCols₂ + x :=
  ⟨by ext i j; simp, by ext i j; simp⟩

theorem slice_line : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ T₀, p.IsModel ψ F₀ FS T₀ → ∃ FL : Frame k B.L.rank Unit, (∀ r, FL.β r () = s * p.pr (B.ζ r)) ∧ ∀ (Ξ : SB (Matrix n n' k)) (u₀ : WO B.A S), ∃ T', p.IsModel ψ FL FS T' ∧ ∀ (c : SB (Matrix n Unit k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), (∀ x, Ψ.1 x = Ξ.1 x.toCols₁ * c.1 (Matrix.of fun r _ => x r (Sum.inr ()))) → ∀ w, T' c w = T₀ Ψ ((B.o.resS S).symm (u₀, w)) := by
  intro D k _ _ _ _ p ψ ρ B S s n n' _ _ _ _ FA F₀ FS h T₀ hT
  have hA := frame_card FA
  have h0 := frame_card F₀
  have hr := B.o.rank_add
  rw [Fintype.card_sum, Fintype.card_unit] at h0
  have hL1 : B.L.rank = 1 := by omega
  have hsub : ∀ r r' : Fin B.L.rank, r = r' := fun r r' => Fin.ext (by have := r.isLt; have := r'.isLt; omega)
  have hv : ∀ r, s * p.pr (B.ζ r) ≠ 0 := by
    intro r₀ h₀
    have hz : ∀ r, s * p.pr (B.ζ r) = 0 := fun r => by rw [hsub r r₀]; exact h₀
    have hcol : ∀ r, F₀.β r (Sum.inr ()) = 0 := by
      intro r
      rw [h.2 r]
      simp only [vecB, Matrix.mulVec, dotProduct, Place.pr, map_sum, map_mul, Finset.mul_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      have := hz j
      simp only [Place.pr] at this
      rw [mul_left_comm, this, mul_zero]
    have := congrFun (congrFun F₀.γβ (Sum.inr ())) (Sum.inr ())
    simp [Matrix.mul_apply, hcol] at this
  obtain ⟨FL, hFL⟩ : ∃ FL : Frame k B.L.rank Unit, ∀ r, FL.β r () = s * p.pr (B.ζ r) := by
    refine ⟨⟨Matrix.of fun r _ => s * p.pr (B.ζ r), Matrix.of fun _ r => (s * p.pr (B.ζ r))⁻¹, ?_, ?_⟩, fun r => rfl⟩
    · ext r r'
      obtain rfl := hsub r r'
      simp [Matrix.mul_apply]
      rw [← _root_.mul_inv_rev]
      exact mul_inv_cancel₀ (hv r)
    · ext u u'
      simp [Matrix.mul_apply]
      rw [Finset.sum_congr rfl (g := fun _ => (1 : k)) fun j _ => by rw [← _root_.mul_inv_rev]; exact inv_mul_cancel₀ (hv j)]
      simp [hL1]
  refine ⟨FL, hFL, fun Ξ u₀ => ?_⟩
  let T' : SB (Matrix n Unit k) →ₗ[ℂ] (WO B.L S → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (fun w : WO B.L S => (B.o.resS S).symm (u₀, w))).comp (T₀.comp (box Ξ))
  have hT' : ∀ c w, T' c w = T₀ (box Ξ c) ((B.o.resS S).symm (u₀, w)) := fun _ _ => rfl
  refine ⟨T', ⟨fun Φ => ?_, fun x Φ Φ' hΦ => ?_, fun y hy Φ Φ' hΦ => ?_⟩, fun c Ψ hΨ w => ?_⟩
  · exact GlobalTheory.BoxSlice.isThetaFunO_slice_right B.o (hT.theta (box Ξ Φ)) u₀
  · have e := hT.trans (fromCols 0 x) (box Ξ Φ) (box Ξ Φ') (fun t => by
      rw [box_apply, box_apply, hΦ, (toCols_add t x).1, (toCols_add t x).2])
    funext w
    rw [hT', e, up_fromCols p h hFL, heis_slice]
    rfl
  · have e := hT.modul ((B.o.resS S).symm (0, y)) (isHalf_slice B.o hy) (box Ξ Φ) (box Ξ Φ') (fun t => by
      simp only [box_apply, hΦ, B.o.symplO_resS, AddEquiv.apply_symm_apply, resS_up_snd p h hFL, symplO_zero_right',
        zero_add]
      ring)
    funext w
    rw [hT', e, heis_slice]
    rfl
  · have e : Ψ = box Ξ c := Subtype.ext (funext fun x => by rw [hΨ, box_apply]; rfl)
    rw [hT', e]

end GlobalTheory.SliceLine
