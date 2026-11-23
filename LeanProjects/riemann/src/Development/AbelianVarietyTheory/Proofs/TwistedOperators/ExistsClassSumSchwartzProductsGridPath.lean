import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PathArgsOfNotMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped Pointwise

noncomputable section

namespace GlobalTheory.FlipRun

open GlobalTheory.FunObj.LocTensor
open scoped ValuativeRel

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem locArg_eq_locM (B : Frames G) {t : T} {a : Arrow T} (ha : IsGridArrow D.R.m t a) :
    ∃ (β : GL (Fin (G.pT a.pair).rank) (Lev.EAf D)) (β' : GL (Fin (G.pS a.pair).rank) (Lev.EAf D)), ∀ w,
      ∃ (f : Fin ((locGrid G t w).rank (edgeOf a).tgt) → Fin (G.pS a.pair).rank)
        (g : Fin ((locGrid G t w).rank (edgeOf a).src) → Fin (G.pT a.pair).rank),
        f.Surjective ∧ g.Surjective ∧ ∀ x r c, locArg B t w a x r c = locM β β' w x (g c) (f r) := by
  have sur : ∀ {m n : ℕ} (h : m = n), (Fin.cast h).Surjective := fun h y => ⟨Fin.cast h.symm y, by simp⟩
  rcases ha with ⟨i, j, hi, hj, rfl⟩ | ⟨i, j, hi, hj, rfl⟩
  · refine ⟨B.β i j, B.β (i + 1) j, fun w => ⟨Fin.cast (rank_vertex G t w (X := (i + 1, j)) ⟨hi, hj⟩),
      Fin.cast (rank_vertex G t w (X := (i, j)) ⟨hi.le, hj⟩), sur _, sur _, fun x r c => ?_⟩⟩
    have e : locArg B t w (.right i j) x = B.coord t w (X := (i, j)) (Y := (i + 1, j)) ⟨hi.le, hj⟩ ⟨hi, hj⟩
        (x.map fun c => cpt w (toEAf D c)) := dif_pos ⟨hi, hj⟩
    rw [e]
    rfl
  · refine ⟨B.β i (j + 1), B.β i j, fun w => ⟨Fin.cast (rank_vertex G t w (X := (i, j)) ⟨hi, hj.le⟩),
      Fin.cast (rank_vertex G t w (X := (i, j + 1)) ⟨hi, hj⟩), sur _, sur _, fun x r c => ?_⟩⟩
    have e : locArg B t w (.down t i j) x = B.coord t w (X := (i, j + 1)) (Y := (i, j)) ⟨hi, hj⟩ ⟨hi, hj.le⟩
        (x.map fun c => cpt w (toEAf D c)) := dif_pos ⟨hi, hj⟩
    rw [e]
    rfl

theorem locArg_add (B : Frames G) {t : T} {a : Arrow T} (ha : IsGridArrow D.R.m t a) (w : Pl D.host.E)
    (x u : WO (G.pS a.pair) (G.pT a.pair)) : locArg B t w a (x + u) = locArg B t w a x + locArg B t w a u := by
  obtain ⟨β, β', h⟩ := locArg_eq_locM B ha
  obtain ⟨f, g, -, -, h⟩ := h w
  ext r c
  rw [Matrix.add_apply, h, h, h, locM_add, Matrix.add_apply]

theorem arrow_sb {W : G.Weil} (B : Frames G) (ρ : RealMatch W) {μ₀ : T} (hL : L.Is μ₀) {t : T} {e : AE D}
    (he : IsIdemSum e (locPl G t)) (n : Pl D.host.E → ℕ) {a : Arrow T} (ha : IsGridArrow D.R.m t a) {Y : Type}
    (F : WO (G.pS a.pair) (G.pT a.pair) → Y → ℂ)
    (h1 : ∀ x u y, (∀ w ∈ locPl G t, GivenAdm.CongM (unifAt w ^ n w) (locArg B t w a u)) → F (x + u) y = F x y)
    (h2 : ∀ x y, F x y ≠ 0 → ∀ w ∈ locPl G t, ∀ r c, locArg B t w a x r c ∈ 𝒪[Kw w]) :
    ∃ (ι : Type) (s : Finset ι) (φ : ι → Sch G a) (r : ι → WO (G.pS a.pair) (G.pT a.pair)),
      (∀ i ∈ s, IsSBHalf e (latA G a) (φ i)) ∧ ∀ x y, IsHalf e x → F x y = ∑ i ∈ s, φ i x * F (r i) y := by
  obtain ⟨hS, hT, -⟩ := arrow_data ρ hL ha
  obtain ⟨β, β', hβ⟩ := locArg_eq_locM B ha
  obtain ⟨k, hk, k1, k2⟩ := exists_mult hS.1 hT.1 he β β' n
  exact exists_sb hS.1.fg hT.1.fg (GlobalTheory.PlaceVec.idemSum_mul_self he) F hk
    (fun u hu x y => h1 x (k • u) y fun w hw r c => by
      obtain ⟨f, g, -, -, h⟩ := hβ w
      rw [h]
      exact k1 u hu w hw _ _)
    fun x y hx h0 => k2 x hx fun w hw i j => by
      obtain ⟨f, g, hf, hg, h⟩ := hβ w
      obtain ⟨c, rfl⟩ := hg i
      obtain ⟨r, rfl⟩ := hf j
      rw [← h]
      exact h2 x y h0 w hw r c

theorem exists_classSum_schwartzProducts_pathInduction {μ₀ : T} (hL : L.Is μ₀) {W : G.Weil} (B : Frames G) (ρ : RealMatch W) (t : T) {e : AE D}
    (he : IsIdemSum e (locPl G t)) (n : Pl D.host.E → ℕ) {X : Node} : ∀ {Y : Node} (p : Path T X Y), OnGrid D.R.m t p →
    (edges p).Nodup → ∀ {U : Type} (K : (∀ w, (locGrid G t w).Args) → U → ℂ),
    (∀ (x z : ∀ w, (locGrid G t w).Args) (y : U), (∀ w ∈ locPl G t, ∀ b,
      z w b ∈ GlobalTheory.SplitFlip.matLat _ (unifAt w ^ n w • GlobalTheory.SplitFlip.stdLat (Kw w) _)) → K (x + z) y = K x y) →
    (∀ (x : ∀ w, (locGrid G t w).Args) (y : U), K x y ≠ 0 → ∀ w ∈ locPl G t, ∀ b ∈ edges p,
      x w b ∈ GlobalTheory.SplitFlip.matLat _ (GlobalTheory.SplitFlip.stdLat (Kw w) _)) →
    ∃ (ι : Type) (s : Finset ι) (φ d : ι → PureT G p) (r : ι → ArgT G p), (∀ κ ∈ s, VecAll ρ e p (φ κ) (d κ)) ∧
      ∀ (x : ArgT G p) (y : U), HalfAll e p x →
        K (fun w => pathArgs B t w p x) y = ∑ κ ∈ s, famProd p (φ κ) x * K (fun w => pathArgs B t w p (r κ)) y
  | _, .nil, _, _, U, K, _, _ => ⟨Unit, {()}, fun _ => (), fun _ => (), fun _ => (), fun _ _ => trivial, fun x y _ => by
      rw [Finset.sum_singleton]
      exact (one_mul _).symm⟩
  | _, .snoc a p, hg, hnd, U, K, hK1, hK2 => by
    rw [edges_snoc] at hnd
    obtain ⟨hnd1, -, hdis⟩ := List.nodup_append.1 hnd
    have hnot : edgeOf a ∉ edges p := fun h => hdis _ h _ (List.mem_singleton_self _) rfl
    have ha := hg.last
    obtain ⟨ι₁, s₁, φa, r₁, hφa, hexp⟩ := arrow_sb B ρ hL he n ha
      (fun x (z : ArgT G p × U) => K (fun w => Function.update (pathArgs B t w p z.1) (edgeOf a) (locArg B t w a x)) z.2)
      (fun x u (z : ArgT G p × U) hu => by
        have e1 : (fun w => Function.update (pathArgs B t w p z.1) (edgeOf a) (locArg B t w a (x + u))) =
            (fun w => Function.update (pathArgs B t w p z.1) (edgeOf a) (locArg B t w a x)) +
              fun w => Function.update (0 : (locGrid G t w).Args) (edgeOf a) (locArg B t w a u) := by
          funext w b
          rcases eq_or_ne b (edgeOf a) with rfl | hb
          · simp only [Pi.add_apply, Function.update_self, locArg_add B ha]
          · simp only [Pi.add_apply, Function.update_of_ne hb, Pi.zero_apply, add_zero]
        show K _ z.2 = K _ z.2
        rw [e1]
        refine hK1 _ _ _ fun w hw b => ?_
        rcases eq_or_ne b (edgeOf a) with rfl | hb
        · rw [Function.update_self]
          exact GivenAdm.mem_matLat_smul.2 (hu w hw)
        · rw [Function.update_of_ne hb]
          exact zero_mem _)
      (fun x (z : ArgT G p × U) h0 w hw r c => by
        have h := hK2 _ z.2 h0 w hw (edgeOf a) (by rw [edges_snoc]; exact List.mem_append_right _ (List.mem_singleton_self _))
        rw [Function.update_self] at h
        exact GlobalTheory.SplitFlip.mem_matLat_stdLat.1 h r c)
    obtain ⟨ι₂, s₂, φ₂, d₂, r₂, hv, hexp₂⟩ := exists_classSum_schwartzProducts_pathInduction hL B ρ t he n p hg.init hnd1 (U := ι₁ × U)
      (fun Xa (z : ι₁ × U) => K (fun w => Function.update (Xa w) (edgeOf a) (locArg B t w a (r₁ z.1))) z.2)
      (fun x z y hz => by
        have e1 : (fun w => Function.update ((x + z) w) (edgeOf a) (locArg B t w a (r₁ y.1))) =
            (fun w => Function.update (x w) (edgeOf a) (locArg B t w a (r₁ y.1))) +
              fun w => Function.update (z w) (edgeOf a) 0 := by
          funext w b
          rcases eq_or_ne b (edgeOf a) with rfl | hb
          · simp only [Pi.add_apply, Function.update_self, add_zero]
          · simp only [Pi.add_apply, Function.update_of_ne hb]
        show K _ y.2 = K _ y.2
        rw [e1]
        refine hK1 _ _ _ fun w hw b => ?_
        rcases eq_or_ne b (edgeOf a) with rfl | hb
        · rw [Function.update_self]
          exact zero_mem _
        · rw [Function.update_of_ne hb]
          exact hz w hw b)
      (fun x y h0 w hw b hb => by
        have h := hK2 _ y.2 h0 w hw b (by rw [edges_snoc]; exact List.mem_append_left _ hb)
        rwa [Function.update_of_ne (ne_of_mem_of_not_mem hb hnot)] at h)
    obtain ⟨Tm, hTm, -, -⟩ := exists_arrowModel ρ hL he ha
    refine ⟨ι₂ × ι₁, s₂ ×ˢ s₁, fun κ => (φ₂ κ.1, φa κ.2), fun κ => (d₂ κ.1, Tm (φa κ.2)), fun κ => (r₂ κ.1, r₁ κ.2),
      fun κ hκ => ?_, fun x y hx => ?_⟩
    · obtain ⟨h1, h2⟩ := Finset.mem_product.1 hκ
      exact ⟨hv _ h1, (hTm _ _).2 ⟨hφa _ h2, rfl⟩⟩
    · have hx' : HalfAll e p x.1 ∧ IsHalf e x.2 := hx
      have e1 : (fun w => pathArgs B t w (.snoc a p) x) =
          fun w => Function.update (pathArgs B t w p x.1) (edgeOf a) (locArg B t w a x.2) :=
        funext fun w => pathArgs_snoc B t w a p x
      calc K (fun w => pathArgs B t w (.snoc a p) x) y
          = ∑ i ∈ s₁, φa i x.2 * K (fun w => Function.update (pathArgs B t w p x.1) (edgeOf a) (locArg B t w a (r₁ i))) y := by
            rw [e1]
            exact hexp x.2 (x.1, y) hx'.2
        _ = ∑ i ∈ s₁, φa i x.2 * ∑ κ ∈ s₂, famProd p (φ₂ κ) x.1 *
              K (fun w => Function.update (pathArgs B t w p (r₂ κ)) (edgeOf a) (locArg B t w a (r₁ i))) y :=
            Finset.sum_congr rfl fun i _ => congrArg _ (hexp₂ x.1 (i, y) hx'.1)
        _ = _ := by
            rw [Finset.sum_product_right]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun κ _ => ?_
            have e2 : (fun w => pathArgs B t w (.snoc a p) ((r₂ κ, r₁ i) : ArgT G (.snoc a p))) =
                fun w => Function.update (pathArgs B t w p (r₂ κ)) (edgeOf a) (locArg B t w a (r₁ i)) :=
              funext fun w => pathArgs_snoc B t w a p _
            show _ = famProd p (φ₂ κ) x.1 * φa i x.2 * K (fun w => pathArgs B t w (.snoc a p) ((r₂ κ, r₁ i) : ArgT G (.snoc a p))) y
            rw [e2]
            ring

theorem exists_classes_path : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ {W : G.Weil} (B : Frames G) (ρ : RealMatch W) (t : T) {e : AE D}, IsIdemSum e (locPl G t) → ∀ (n : Pl D.host.E → ℕ) {X Y : Node} (p : Path T X Y), GlobalTheory.FlipRun.OnGrid D.R.m t p → (GlobalTheory.FlipRun.edges p).Nodup → ∀ {U : Type} (K : (∀ w, (locGrid G t w).Args) → U → ℂ), (∀ (x z : ∀ w, (locGrid G t w).Args) (y : U), (∀ w ∈ locPl G t, ∀ b, z w b ∈ GlobalTheory.SplitFlip.matLat _ (unifAt w ^ n w • GlobalTheory.SplitFlip.stdLat (Kw w) _)) → K (x + z) y = K x y) → (∀ (x : ∀ w, (locGrid G t w).Args) (y : U), K x y ≠ 0 → ∀ w ∈ locPl G t, ∀ b ∈ GlobalTheory.FlipRun.edges p, x w b ∈ GlobalTheory.SplitFlip.matLat _ (GlobalTheory.SplitFlip.stdLat (Kw w) _)) → ∃ (ι : Type) (s : Finset ι) (φ d : ι → PureT G p) (r : ι → GlobalTheory.FlipRun.ArgT G p), (∀ κ ∈ s, GlobalTheory.FlipRun.VecAll ρ e p (φ κ) (d κ)) ∧ ∀ (x : GlobalTheory.FlipRun.ArgT G p) (y : U), GlobalTheory.FlipRun.HalfAll e p x → K (fun w => GlobalTheory.FlipRun.pathArgs B t w p x) y = ∑ κ ∈ s, GlobalTheory.FlipRun.famProd p (φ κ) x * K (fun w => GlobalTheory.FlipRun.pathArgs B t w p (r κ)) y :=
  by
  intro D T L sc G μ₀ hL W B ρ t e he n X Y p hg hnd U K hK1 hK2
  exact exists_classSum_schwartzProducts_pathInduction hL B ρ t he n p hg hnd K hK1 hK2

end GlobalTheory.FlipRun

end
