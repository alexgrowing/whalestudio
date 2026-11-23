import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotField
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCharactersAgreeCommonStabiliser

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver GlobalTheory.HL
open scoped Classical

namespace GlobalTheory.RelGPoint

open GlobalTheory.HL.CoordExist

theorem exists_coord_of_point {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E) (hM : M.OK) {V : Type}
    [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r)
    (hrk : Module.finrank E V = k + 2 * r + 1) (hpt : P.IsPoint) (hN : P.NormsOK) (hG : P.Gv ≠ 0) :
    ∃ S : Frames M.L r k, Nonempty (Coord P S) := by
  obtain ⟨w, hw⟩ := hpt
  obtain ⟨hTo, hT, hTo', hT', hgg⟩ := hN
  have := hM.loc
  have := nontriv M.L
  have := H.free
  have := H.fin
  let b := Module.finBasisOfFinrankEq E V hrk
  obtain ⟨ϖ, hϖ, hϖg⟩ : ∃ ϖ : 𝒪[F], Irreducible ϖ ∧ ∀ g, M.split = some g → ϖ = g.q := by
    rcases h : M.split with _ | g
    · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
      exact ⟨ϖ, hϖ, fun g hg => by cases hg⟩
    · exact ⟨g.q, g.q_irr, fun g' hg => by cases hg; rfl⟩
  refine ⟨
    { ϖ := ϖ
      ϖ_irr := hϖ
      Hm := Matrix.of fun i j => H.h (b i) (b j)
      herm := hermND H b
      T := Units.mk0 _ hT
      T' := Units.mk0 _ hT'
      f := fun a => b.equivFun (P.A.f a)
      f' := fun a => b.equivFun (P.B.f a)
      es := fun a => b.equivFun (P.A.es a)
      es' := fun a => b.equivFun (P.B.es a)
      gram := fun a c => by rw [hf_basis]; exact gram_eq _ _ _
      gram' := fun a c => by rw [hf_basis]; exact gram_eq _ _ _
      dual := fun a c => by rw [hf_basis]; exact dual_eq _ _ _
      dual' := fun a c => by rw [hf_basis]; exact dual_eq _ _ _
      iso := fun a c => by rw [hf_basis]; exact P.A.h_ss _ _
      iso' := fun a c => by rw [hf_basis]; exact P.B.h_ss _ _
      w := w
      relevant := fun a c => ?_
      G_ne := ?_
      gg := M.split.isSome
      gg_ok := fun h => ?_ }, ⟨
    { e := b.equivFun
      h_eq := fun x y => hf_basis H b x y
      f_eq := fun _ => rfl
      f'_eq := fun _ => rfl
      es_eq := fun _ => rfl
      es'_eq := fun _ => rfl
      T_eq := rfl
      T'_eq := rfl
      gg_none := fun h => by simp only [h, Option.isSome_none]
      gg_some := fun g h => ⟨by simp only [h, Option.isSome_some], hϖg g h⟩ }⟩⟩
  · rw [hf_basis, ← hw, mul_right_comm, ← mul_pow]
    simp [HermSp.Zhat]
  · simp only [hf_basis]
    have h1 : H.Dl P.A.f P.B.f (r + 1) =
        lead (Matrix.of fun a c => H.h (P.B.f c) (P.A.f a)) (Fin.last (r + 1)) := by
      unfold HermSp.Dl; rw [dif_pos le_rfl]; rfl
    have h2 : H.Dl P.A.f P.B.f r =
        lead (Matrix.of fun a c => H.h (P.B.f c) (P.A.f a)) (Fin.last r).castSucc := by
      unfold HermSp.Dl; rw [dif_pos (Nat.le_succ r)]; rfl
    rw [← h1, ← h2]
    exact hG
  · obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 h
    obtain ⟨⟨u, v, hu, hv⟩, -⟩ := hgg g hg
    exact ⟨not_field M.L g, unit_of hTo u hu, unit_of hTo' v hv⟩

theorem relG_of_point : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (k : ℕ) (P : FPair H r), Module.finrank E V = k + 2 * r + 1 → P.IsPoint → P.NormsOK → P.Gv ≠ 0 → P.RelG (theta M) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hrk hpt hN hG
  obtain ⟨S, ⟨c⟩⟩ := exists_coord_of_point M hM H r k P hrk hpt hN hG
  haveI := hM.loc
  haveI := hM.char0
  obtain ⟨hli, -, -, hD, hDl, -⟩ := GlobalTheory.FrameBasic.main M.L r k S
  obtain ⟨-, -, -, hSt, hpsi, -⟩ := GlobalTheory.HL.CoordUnip.transport M hM H r k P S c
  have hZm : S.Zh = H.Zhat P.A.f P.B.f := by
    ext a b
    show S.h (S.f' b) (S.f a) = H.h (P.B.f b) (P.A.f a)
    rw [c.f_eq, c.f'_eq, c.h_eq]
  have hDm : ∀ l (hl : l ≤ r + 1), P.Dm l = S.D ⟨l, Nat.lt_succ_of_le hl⟩ := by
    intro l hl
    unfold FPair.Dm HermSp.Dl
    rw [dif_pos hl]
    unfold Frames.D lead
    rw [hZm]
  have hmap : ∀ (f : Fin (r + 1) → V) (g : Fin (r + 1) → S.V), (∀ a, g a = c.e (f a)) →
      ∀ x ∈ H.Xp f, c.e x ∈ Submodule.span E (Set.range g) := by
    intro f g hg x hx
    have hgf : g = (c.e : V →ₗ[E] S.V) ∘ f := funext hg
    rw [hgf, Set.range_comp, ← Submodule.map_span]
    exact Submodule.mem_map_of_mem hx
  have hdisj := (linearIndependent_sum.1 hli).2.2
  refine ⟨?_, ?_, hG, ?_, ?_, hpt, hN⟩
  · rw [eq_bot_iff]
    intro x hx
    have h0 : c.e x = 0 :=
      (Submodule.disjoint_def.1 hdisj) _ (hmap _ _ c.f_eq x hx.1) (hmap _ _ c.f'_eq x hx.2)
    rw [Submodule.mem_bot]
    exact c.e.map_eq_zero_iff.1 h0
  · rw [hDm (r + 1) le_rfl]
    exact hD
  · intro l hl
    rw [hDm l hl]
    by_cases h : S.D ⟨l, Nat.lt_succ_of_le hl⟩ = 0
    · exact Or.inl h
    · exact Or.inr (hDl _ h)
  · intro g hg
    rw [(hpsi g).1, (hpsi g).2]
    exact GlobalTheory.HL.CharAgree.psi_eq_psi' M.L r k S _ ((hSt g).1 hg)

end GlobalTheory.RelGPoint
