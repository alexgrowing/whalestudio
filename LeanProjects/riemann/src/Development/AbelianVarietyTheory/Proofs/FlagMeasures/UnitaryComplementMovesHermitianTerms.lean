import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotField
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportUnitaryMassStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerDataStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermOverFrameCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermOverFrameCoordinates
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.ComplMove

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}

lemma bbne_img (g : V ≃ₗ[E] V) (f f' : Fin (r + 1) → V) (hfix : ∀ b, g (f b) = f b ∧ g (f' b) = f' b)
    (Λ : Submodule M.L.O V) (T T' : F) :
    LocNG.BBne (H := H) (⟨LocNG.img g Λ, f, f', T, T'⟩ : Term V M r) ↔
      LocNG.BBne (H := H) (⟨Λ, f, f', T, T'⟩ : Term V M r) := by
  have hfam : ∀ i, g (H.MMfam (⟨Λ, f, f', T, T'⟩ : Term V M r) i) = H.MMfam (⟨Λ, f, f', T, T'⟩ : Term V M r) i := by
    intro i
    unfold HermSp.MMfam
    rcases hs : M.split with _ | gg <;> rcases i with i | i <;>
      simp [map_smul, map_sub, (hfix i).1, (hfix i).2]
  have hspan : ∀ v ∈ Submodule.span E (Set.range (H.MMfam (⟨Λ, f, f', T, T'⟩ : Term V M r))), g v = v := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hfam i
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul s x _ hx => rw [map_smul, hx]
  have e : H.MMfam (⟨LocNG.img g Λ, f, f', T, T'⟩ : Term V M r) = H.MMfam (⟨Λ, f, f', T, T'⟩ : Term V M r) := rfl
  unfold LocNG.BBne
  simp only [e]
  constructor
  · rintro ⟨v, hv, hs, hns⟩
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hv
    have ew : g w = w := g.injective (hspan _ hs)
    change g w ∈ _ at hs
    change g w ∉ _ at hns
    rw [ew] at hs hns
    exact ⟨w, hw, hs, hns⟩
  · rintro ⟨v, hv, hs, hns⟩
    exact ⟨v, Submodule.mem_map.2 ⟨v, hv, hspan v hs⟩, hs, hns⟩

lemma fwd (hM : M.OK) (P : LocNG.FPair H r) (S : Frames M.L r k) (c : Coord P S) (g : V ≃ₗ[E] V)
    (hg : c.grp g ∈ S.H0) (d d' : LocNG.Datum P) (hmv : c.grp g • c.dat d = c.dat d')
    (f f' : Fin (r + 1) → V) (Λ : Submodule M.L.O V)
    (hT : LocNG.IsTermOver P d (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)) :
    LocNG.IsTermOver P d' (⟨LocNG.img g Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) := by
  letI := hM.loc
  haveI := hM.char0
  have hT0 := hT
  obtain ⟨-, -, ⟨n, hn, hf, hΛn⟩, ⟨n', hn', hf', hΛn'⟩, -⟩ := hT
  change f = _ at hf
  change f' = _ at hf'
  change Λ = _ at hΛn
  change Λ = _ at hΛn'
  subst hf hf'
  have hW := (GlobalTheory.T.term_over_frame_coordinates M hM H r k P S c d n n' Λ).1 ⟨hT0, hn, hn', hΛn, hΛn'⟩
  obtain ⟨m, m', hW', hm, hm'⟩ := GlobalTheory.HL.ComplAct.termW S hW hg
  rw [hmv, ← GlobalTheory.HL.CoordTerm.lat_img c] at hW'
  have e1 : c.grp (c.grp.symm m) = m := c.grp.apply_symm_apply m
  have e2 : c.grp (c.grp.symm m') = m' := c.grp.apply_symm_apply m'
  rw [← e1, ← e2] at hW'
  have hR := ((GlobalTheory.T.term_over_frame_coordinates M hM H r k P S c d' (c.grp.symm m) (c.grp.symm m') (LocNG.img g Λ)).2 hW').1
  have k1 : (fun b => c.grp.symm m (P.A.f b)) = fun b => n (P.A.f b) := by
    funext b
    apply c.e.injective
    rw [← GlobalTheory.HL.CoordTerm.grp_e c, ← GlobalTheory.HL.CoordTerm.grp_e c, ← c.f_eq, e1, hm b]
  have k2 : (fun b => c.grp.symm m' (P.B.f b)) = fun b => n' (P.B.f b) := by
    funext b
    apply c.e.injective
    rw [← GlobalTheory.HL.CoordTerm.grp_e c, ← GlobalTheory.HL.CoordTerm.grp_e c, ← c.f'_eq, e2, hm' b]
  rw [k1, k2] at hR
  exact hR

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (f f' : Fin (r + 1) → V), (∃ n ∈ P.A.N, f = fun b => n (P.A.f b)) → (∃ n' ∈ P.B.N, f' = fun b => n' (P.B.f b)) → ∀ g ∈ P.UW0, ∀ d d' : LocNG.Datum P, LocNG.Datum.Moves g d d' → (∀ b, g (f b) = f b ∧ g (f' b) = f' b) ∧ LocNG.img g '' {Λ | LocNG.IsTermOver P d (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧ ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)} = {Λ | LocNG.IsTermOver P d' (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧ ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)} := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hk hP f f' ⟨n, hn, hf⟩ ⟨n', hn', hf'⟩ g hg d d' hmv
  obtain ⟨S, ⟨c⟩⟩ := GlobalTheory.HL.CoordExist.exists_coord M hM H r k P hk hP
  obtain ⟨hU, -⟩ := GlobalTheory.T.framePairCoordinates_transport_unitary_mass M hM H r k P S c
  obtain ⟨-, hMv, -⟩ := GlobalTheory.T.hermitianFramePairCoordinates_transport_innerData M hM H r k P S c
  obtain ⟨-, hNA, hNB, -⟩ := GlobalTheory.HL.CoordUnip.transport M hM H r k P S c
  have hh := (hU g).1 hg
  have hmv' := (hMv g hg d d').1 hmv
  have fixv : ∀ x : V, c.e x ∈ S.ME → g x = x := by
    intro x hx
    apply c.e.injective
    rw [← GlobalTheory.HL.CoordTerm.grp_e c]
    exact GlobalTheory.HL.ComplAct.hermitianFrames_complementUnitary_fixes_ME S hh _ hx
  have hfix : ∀ b, g (f b) = f b ∧ g (f' b) = f' b := by
    intro b
    subst hf hf'
    refine ⟨fixv _ ?_, fixv _ ?_⟩
    · rw [← GlobalTheory.HL.CoordTerm.grp_e c, ← c.f_eq]
      exact Submodule.mem_sup_left (GlobalTheory.HL.ComplAct.nof_mem S (Or.inl ⟨rfl, rfl⟩) ((hNA n).1 hn)
        (GlobalTheory.HL.ComplAct.mem_spanTo S S.f b))
    · rw [← GlobalTheory.HL.CoordTerm.grp_e c, ← c.f'_eq]
      exact Submodule.mem_sup_right (GlobalTheory.HL.ComplAct.nof_mem S (Or.inr ⟨rfl, rfl⟩) ((hNB n').1 hn')
        (GlobalTheory.HL.ComplAct.mem_spanTo S S.f' b))
  have hginv : c.grp g⁻¹ ∈ S.H0 := by rw [map_inv]; exact S.H0.inv_mem hh
  have hmvinv : c.grp g⁻¹ • c.dat d' = c.dat d := by
    rw [← hmv', map_inv, inv_smul_smul]
  have hback : ∀ Λ : Submodule M.L.O V, LocNG.img g (LocNG.img g⁻¹ Λ) = Λ := by
    intro Λ
    rw [← GlobalTheory.HL.CoordTerm.lat_inj c, GlobalTheory.HL.CoordTerm.lat_img, GlobalTheory.HL.CoordTerm.lat_img, map_inv,
      smul_inv_smul]
  refine ⟨hfix, ?_⟩
  ext Λ
  constructor
  · rintro ⟨Λ0, ⟨hT, hB⟩, rfl⟩
    exact ⟨fwd hM P S c g hh d d' hmv' f f' Λ0 hT, by rwa [bbne_img g f f' hfix]⟩
  · rintro ⟨hT, hB⟩
    refine ⟨LocNG.img g⁻¹ Λ, ⟨fwd hM P S c g⁻¹ hginv d' d hmvinv f f' Λ hT, ?_⟩, hback Λ⟩
    rw [← bbne_img g f f' hfix, hback Λ]
    exact hB

end GlobalTheory.HL.ComplMove
