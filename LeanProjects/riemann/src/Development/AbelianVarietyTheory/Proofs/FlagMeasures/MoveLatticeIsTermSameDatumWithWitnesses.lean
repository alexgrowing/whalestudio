import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryOfSameTrace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EichlerMapMemUnipotentCharacterStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetFramesDatumMovePropertiesStatement

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.MoveWit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem h_add_l (x y z : S.V) : S.h (x + y) z = S.h x z + S.h y z := by
  simp [Frames.h, hf, add_mul, Finset.sum_add_distrib]
theorem h_add_r (x y z : S.V) : S.h x (y + z) = S.h x y + S.h x z := by
  simp [Frames.h, hf, mul_add, Finset.sum_add_distrib]
theorem h_smul_l (c : E) (x y : S.V) : S.h (c • x) y = c * S.h x y := by
  simp [Frames.h, hf, Finset.mul_sum, mul_assoc]
theorem h_smul_r (c : E) (x y : S.V) : S.h x (c • y) = L.cj c * S.h x y := by
  simp only [Frames.h, hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
theorem h_neg_r (x y : S.V) : S.h x (-y) = - S.h x y := by
  simp [Frames.h, hf]
theorem h_zero_l (y : S.V) : S.h 0 y = 0 := by simp [Frames.h, hf]
theorem h_zero_r (y : S.V) : S.h y 0 = 0 := by simp [Frames.h, hf]
theorem h_symm (v w : S.V) : S.h w v = L.cj (S.h v w) := by
  have h' : ∀ i j, L.cj (S.Hm j i) = S.Hm i j := fun i j => congrFun (congrFun S.herm.1 i) j
  simp only [Frames.h, hf, map_sum, map_mul, L.cj_cj, h']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
theorem h_swap0 {v w : S.V} (h : S.h v w = 0) : S.h w v = 0 := by rw [h_symm, h, map_zero]

theorem eich_def (x u : S.V) (s : E) (v : S.V) :
    eich L S.Hm x u s v = v + S.h v u • x - S.h v x • (u + s • x) := rfl

theorem th_mem : algebraMap F E S.th ∈ L.O := by
  unfold Frames.th
  split_ifs
  · rw [L.O_def]
    have h : IsIntegral 𝒪[F] (S.ϖ : F) := isIntegral_algebraMap (R := 𝒪[F]) (A := F) (x := S.ϖ)
    exact h.map (IsScalarTower.toAlgHom 𝒪[F] F E)
  · rw [map_one]; exact L.O.one_mem

theorem smulO {Λ : Submodule L.O S.V} {c : E} (hc : c ∈ L.O) {v : S.V} (hv : v ∈ Λ) : c • v ∈ Λ :=
  Λ.smul_mem (⟨c, hc⟩ : L.O) hv

theorem inTh_mem {Λ : Submodule L.O S.V} {v : S.V} (h : S.InTh Λ v) : v ∈ Λ := by
  obtain ⟨y, hy, rfl⟩ := h
  exact smulO S (th_mem S) hy

theorem inTh_add {Λ : Submodule L.O S.V} {v w : S.V} (h : S.InTh Λ v) (h' : S.InTh Λ w) :
    S.InTh Λ (v + w) := by
  obtain ⟨y, hy, rfl⟩ := h
  obtain ⟨z, hz, rfl⟩ := h'
  exact ⟨y + z, Λ.add_mem hy hz, by rw [smul_add]⟩

theorem mem_smul (g : S.GLV) (Λ : Submodule L.O S.V) (v : S.V) : v ∈ g • Λ ↔ g⁻¹ v ∈ Λ := by
  rw [Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨b, hb, rfl⟩
    have : g⁻¹ (g • b) = b := g.symm_apply_apply b
    rwa [this]
  · intro h
    exact ⟨_, h, g.apply_symm_apply v⟩

theorem inv_app (g : S.GLV) (v : S.V) : g⁻¹ (g v) = v := g.symm_apply_apply v
theorem app_inv (g : S.GLV) (v : S.V) : g (g⁻¹ v) = v := g.apply_symm_apply v

theorem inTh_tr {Λ Λ₁ : Submodule L.O S.V} {a : S.GLV} (ha : ∀ v, v ∈ Λ₁ ↔ a v ∈ Λ) {v : S.V}
    (h : S.InTh Λ (a v)) : S.InTh Λ₁ v := by
  obtain ⟨y, hy, e⟩ := h
  refine ⟨a⁻¹ y, (ha _).2 (by rwa [app_inv]), ?_⟩
  rw [← map_smul, ← e, inv_app]

theorem isSD_smul {g : S.GLV} (hg : g ∈ isomG L S.Hm) {Λ : Submodule L.O S.V} (h : IsSD L S.Hm Λ) :
    IsSD L S.Hm (g • Λ) := by
  refine ⟨⟨?_, ?_⟩, fun y => ?_⟩
  · exact h.1.1.map _
  · rw [eq_top_iff]
    intro v _
    have h1 : g⁻¹ v ∈ Submodule.span E (Λ : Set S.V) := by rw [h.1.2]; trivial
    have h2 := Submodule.apply_mem_span_image_of_mem_span (g : S.V →ₗ[E] S.V) h1
    have h3 : (g : S.V →ₗ[E] S.V) (g⁻¹ v) = v := app_inv S g v
    rw [h3] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨w, hw, rfl⟩
    exact (mem_smul S g Λ _).2 (by
      have : g⁻¹ ((g : S.V →ₗ[E] S.V) w) = w := inv_app S g w
      rw [this]; exact hw)
  · rw [mem_smul, ← h.2]
    constructor
    · intro H x hx
      have := H (g x) ((mem_smul S g Λ _).2 (by rwa [inv_app]))
      rwa [← app_inv S g y, hg] at this
    · intro H x hx
      have := H _ ((mem_smul S g Λ _).1 hx)
      rwa [(isomG L S.Hm).inv_mem hg] at this

theorem cong {Λ : Submodule L.O S.V} (hΛ : IsSD L S.Hm Λ) {x x' u : S.V} {s t : E}
    (hb : S.InTh Λ (x + x')) (hu : u ∈ Λ) (hs : s • x ∈ Λ)
    (hc : ∃ c ∈ L.O, S.h x' x = algebraMap F E S.th * c) (hx'u : S.h x' u = 0)
    {v : S.V} (hv : v ∈ Λ) (hv' : S.h v x' = 0) :
    S.InTh Λ (eich L S.Hm x u s (eich L S.Hm x' u t v) - v) := by
  obtain ⟨c, hc, ec⟩ := hc
  obtain ⟨y, hy, ey⟩ := hb
  have hint : ∀ a ∈ Λ, ∀ b ∈ Λ, S.h a b ∈ L.O := fun a ha b hb => (hΛ.2 b).2 hb a ha
  have e1 : S.h v x = algebraMap F E S.th * S.h v y := by
    have : S.h v (x + x') = S.h v x := by rw [h_add_r, hv', add_zero]
    rw [← this, ey, h_smul_r, L.cj.commutes]
  refine ⟨S.h v u • y - (S.h v y + S.h v u * c) • (u + s • x),
    Λ.sub_mem (smulO S (hint _ hv _ hu) hy) (smulO S (L.O.add_mem (hint _ hv _ hy)
      (L.O.mul_mem (hint _ hv _ hu) hc)) (Λ.add_mem hu hs)), ?_⟩
  rw [eich_def S x', hv', zero_smul, sub_zero, eich_def, h_add_l, h_add_l, h_smul_l, h_smul_l, hx'u, ec, e1,
    smul_sub, smul_comm (algebraMap F E S.th) (S.h v u) y, ← ey]
  module

theorem graph_sub {Λ Λ₁ : Submodule L.O S.V} {a a' : S.GLV} (ha : ∀ v, v ∈ Λ₁ ↔ a v ∈ Λ)
    (hN : a ∈ S.N) (hN' : a' ∈ S.N')
    (H : ∀ v ∈ Λ, v ∈ perp L S.Hm S.X' → S.InTh Λ (a (a' v) - v)) : S.graphOf Λ ⊆ S.graphOf Λ₁ := by
  rintro p ⟨y', hy', y, hy, h1, h2, h3, h4, h5⟩
  have hi := (S.N.inv_mem hN).2
  have hi' := hN'.2
  refine ⟨a' y', (ha _).2 ?_, a⁻¹ y, (ha _).2 (by rwa [app_inv]), (hi'.1 _).2 h1, (hi.1 _).2 h2, ?_, ?_, ?_⟩
  · have := Λ.add_mem (inTh_mem S (H _ hy' h1)) hy'
    rwa [sub_add_cancel] at this
  · have := S.X'.add_mem (hi'.2 _ h1) h3
    rwa [sub_add_sub_cancel] at this
  · have := S.X.add_mem (hi.2 _ h2) h4
    rwa [sub_add_sub_cancel] at this
  · apply inTh_tr S ha
    have := inTh_add S (H _ hy' h1) h5
    rwa [sub_add_sub_cancel, ← app_inv S a y, ← map_sub] at this

theorem mem_unipOn_of_fix {g : S.GLV} {A B : Submodule E S.V} (h : ∀ v ∈ A, g v = v) : g ∈ unipOn A B := by
  refine ⟨fun v => ⟨fun hv => ?_, fun hv => by rwa [h v hv]⟩, fun v hv => by rw [h v hv, sub_self]; exact B.zero_mem⟩
  have := g.injective (h _ hv)
  rwa [this] at hv

theorem X'_eq : Submodule.span E (Set.range fun j : Fin r => S.f' j.castSucc) = S.X' := by
  unfold Frames.X' Frames.spanTo
  congr 1
  ext v
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨j.castSucc, j.2, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩

theorem f'_perp (b : Fin (r + 1)) : S.f' b ∈ perp L S.Hm S.X' := by
  rw [← X'_eq]
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    rw [S.gram', if_neg]
    exact fun h => (Fin.castSucc_lt_last j).ne h.2
  | zero => exact h_zero_r S _
  | add y z _ _ h1 h2 => exact (h_add_r S _ _ _).trans (by unfold Frames.h; rw [h1, h2, add_zero])
  | smul c y _ h1 => exact (h_smul_r S _ _ _).trans (by unfold Frames.h; rw [h1, mul_zero])

theorem spanTo_le_perp (j : ℕ) : S.spanTo S.f' j ≤ perp L S.Hm S.X' := by
  unfold Frames.spanTo
  rw [Submodule.span_le]
  rintro _ ⟨i, _, rfl⟩
  exact f'_perp S i

theorem mem_N'_of_fix {g : S.GLV} (hg : g ∈ isomG L S.Hm) (h : ∀ v ∈ perp L S.Hm S.X', g v = v) :
    g ∈ S.N' := by
  refine ⟨⟨hg, ?_⟩, mem_unipOn_of_fix S h⟩
  change g ∈ ⨅ j : Fin r, unipOn (S.spanTo S.f' (j + 1)) (S.spanTo S.f' j)
  rw [Subgroup.mem_iInf]
  exact fun j => mem_unipOn_of_fix S fun v hv => h v (spanTo_le_perp S _ hv)

theorem f'_li : LinearIndependent E fun j : Fin r => S.f' j.castSucc := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h1 : S.h (∑ j, c j • S.f' j.castSucc) (S.es' i) = ∑ j, c j * S.h (S.f' j.castSucc) (S.es' i) := by
    induction (Finset.univ : Finset (Fin r)) using Finset.induction_on with
    | empty => simp [h_zero_l]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h_add_l, ih, h_smul_l]
  rw [hc, h_zero_l] at h1
  simp only [Frames.h, S.dual', Fin.castSucc_inj] at h1
  simpa using h1.symm

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x x' u s, S.IsMove (j + 1) d Λ x x' u s → ∃ n₀ ∈ S.N, ∃ n₀' ∈ S.N', ∃ n'' ∈ S.N', (∀ v, n₀ v = eich L S.Hm x u s v) ∧ (∀ v, n₀⁻¹ v = eich L S.Hm x (-u) (L.cj s) v) ∧ (∀ v, n₀' v = eich L S.Hm x' u s v) ∧ (∀ v ∈ perp L S.Hm S.X', n'' v = v) ∧ ((n₀⁻¹ • Λ : Submodule L.O S.V) : Set S.V) = S.moved Λ x u s ∧ S.IsTermW d (n₀⁻¹ • Λ) (n₀⁻¹ * (S.wit d Λ).1) (n'' * n₀' * (S.wit d Λ).2) := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hF x x' u s hM
  obtain ⟨hs1, hs2, -, -, hc, hxx, -, hux, hux', -, hx'X⟩ := GlobalTheory.T.hermitianDoubleCosetFrames_datum_move_properties L r k S j β βJ d Λ hT hF x x' u s hM
  obtain ⟨hx, hx', hb, -, hu, hup, -, hss⟩ := hM
  obtain ⟨n₀, hn₀, e₀, ei₀, -, -⟩ := GlobalTheory.T.eichler_map_mem_unipotent_character L r k S S.f S.es (Or.inl ⟨rfl, rfl⟩) j x u s hx
    (fun y hy => hup y (Submodule.mem_sup_left hy)) hss
  obtain ⟨n₀', hn₀', e₀', ei₀', -, -⟩ := GlobalTheory.T.eichler_map_mem_unipotent_character L r k S S.f' S.es' (Or.inr ⟨rfl, rfl⟩) j x' u s hx'
    (fun y hy => hup y (Submodule.mem_sup_right hy)) hss
  obtain ⟨hSD, hW, -, -, hfr', -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  obtain ⟨hI, hI', hn, hn', hL, hL', had, hgr⟩ := hW
  have hxu := h_swap0 S hux
  have hx'u := h_swap0 S hux'
  have hm : ∀ v, v ∈ n₀⁻¹ • Λ ↔ n₀ v ∈ Λ := fun v => by rw [mem_smul, inv_inv]
  have hm' : ∀ v, v ∈ Λ ↔ n₀⁻¹ v ∈ n₀⁻¹ • Λ := fun v => by rw [hm, app_inv]
  have hSD₁ : IsSD L S.Hm (n₀⁻¹ • Λ) := isSD_smul S ((isomG L S.Hm).inv_mem hn₀.1.1) hSD
  have H : ∀ v ∈ Λ, v ∈ perp L S.Hm S.X' → S.InTh Λ (n₀ (n₀' v) - v) := fun v hv hp => by
    rw [e₀, e₀']
    exact cong S hSD hb hu hs1 hc hx'u hv (hp _ hx'X)
  have hfx : n₀ x = x := by rw [e₀, eich_def, hxu, hxx]; simp
  have hb₁ : S.InTh (n₀⁻¹ • Λ) (x + x') := by
    apply inTh_tr S hm
    obtain ⟨c, hc, ec⟩ := hc
    have e : n₀ (x + x') = (x + x') + algebraMap F E S.th • (-(c • (u + s • x))) := by
      rw [map_add, hfx, e₀, eich_def, hx'u, ec]; module
    rw [e]
    exact inTh_add S hb ⟨_, Λ.neg_mem (smulO S hc (Λ.add_mem hu hs1)), rfl⟩
  have hu₁ : -u ∈ n₀⁻¹ • Λ := by
    apply Submodule.neg_mem
    rw [hm, e₀, eich_def, hux, ← hss, zero_smul, sub_zero, add_smul]
    exact Λ.add_mem hu (Λ.add_mem hs1 hs2)
  have hs₁ : L.cj s • x ∈ n₀⁻¹ • Λ := by rw [hm, map_smul, hfx]; exact hs2
  have H₁ : ∀ v ∈ n₀⁻¹ • Λ, v ∈ perp L S.Hm S.X' → S.InTh (n₀⁻¹ • Λ) (n₀⁻¹ (n₀'⁻¹ v) - v) := fun v hv hp => by
    rw [ei₀, ei₀']
    exact cong S hSD₁ hb₁ hu₁ hs₁ hc (by rw [h_neg_r, hx'u, neg_zero]) hv (hp _ hx'X)
  obtain ⟨g, hg, hfix, hgL⟩ := GlobalTheory.HL.SameTrace.exists_isometry_of_same_trace L S.Hm S.herm (n₀' • Λ) (n₀⁻¹ • Λ)
    (isSD_smul S hn₀'.1.1 hSD) hSD₁ r (fun j : Fin r => S.f' j.castSucc) (f'_li S)
    (fun i j => f'_perp S _ _ (by rw [← X'_eq]; exact Submodule.subset_span ⟨j, rfl⟩)) (by
      rw [X'_eq]
      intro v hv
      rw [mem_smul]
      constructor
      · intro h
        have h1 := Λ.add_mem (inTh_mem S (H _ h (((S.N'.inv_mem hn₀').2.1 _).2 hv))) h
        rw [sub_add_cancel, app_inv] at h1
        exact (hm _).2 h1
      · intro h
        have h1 := (n₀⁻¹ • Λ).add_mem (inTh_mem S (H₁ _ h hv)) h
        rw [sub_add_cancel] at h1
        exact (hm' _).2 h1)
  rw [X'_eq] at hfix
  have hgN := mem_N'_of_fix S hg hfix
  refine ⟨n₀, hn₀, n₀', hn₀', g, hgN, e₀, ei₀, e₀', hfix, ?_, hI, hI', S.N.mul_mem (S.N.inv_mem hn₀) hn,
    S.N'.mul_mem (S.N'.mul_mem hgN hn₀') hn', ?_, ?_, fun b => ?_, ?_⟩
  · ext v
    change v ∈ n₀⁻¹ • Λ ↔ eich L S.Hm x u s v ∈ Λ
    rw [hm, e₀]
  · rw [mul_smul, ← hL]
  · rw [mul_smul, mul_smul, ← hL', hgL]
  · apply inTh_tr S hm
    have hp : (S.wit d Λ).2 (S.f' b) ∈ perp L S.Hm S.X' := (hn'.2.1 _).2 (f'_perp S b)
    have hl : (S.wit d Λ).2 (S.f' b) ∈ Λ :=
      ((hfr' (r + 1) le_rfl _).2 (Submodule.subset_span ⟨b, b.2, rfl⟩)).1
    have h1 := inTh_add S (H _ hl hp) (had b)
    rw [sub_add_sub_cancel] at h1
    have e1 : (g * n₀' * (S.wit d Λ).2) (S.f' b) = n₀' ((S.wit d Λ).2 (S.f' b)) :=
      hfix _ ((hn₀'.2.1 _).2 hp)
    have e2 : n₀ ((n₀⁻¹ * (S.wit d Λ).1) (S.f b)) = (S.wit d Λ).1 (S.f b) := app_inv S n₀ _
    rw [map_sub, e1, e2]
    exact h1
  · rw [hgr]
    exact Set.Subset.antisymm (graph_sub S hm hn₀ hn₀' H)
      (graph_sub S hm' (S.N.inv_mem hn₀) (S.N'.inv_mem hn₀') H₁)

end GlobalTheory.HL.MoveWit
