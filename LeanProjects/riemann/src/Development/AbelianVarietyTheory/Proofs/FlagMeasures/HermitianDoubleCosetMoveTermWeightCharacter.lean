import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EichlerIsometry
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormAdditiveCharacterTypePrimeEqOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EichlerMapMemUnipotentCharacter
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetFramesDatumMovePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MoveLatticeIsTermSameDatumWithWitnessesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianMovePreservesFrameLatticeLevelsStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.MoveTerm
open GlobalTheory.HL.Eichler

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem cj_mem_O {c : E} (hc : c ∈ L.O) : L.cj c ∈ L.O := by
  rw [L.O_def] at hc ⊢
  exact hc.map (L.cj.toAlgHom.restrictScalars 𝒪[F])

theorem top_coord (g : Fin (r + 1) → S.V) (gs : Fin r → S.V)
    (hd : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (w : S.GLV) (hw : w ∈ S.Nof g) (j : Fin r) (x : S.V) (hx : x ∈ S.spanTo g (j + 1))
    (al : Fin (r + 1) → E) (e : x = ∑ i, al i • w (g i)) :
    S.h x (gs j) = al j.castSucc := by
  simp only [Frames.Nof, Subgroup.mem_inf, Subgroup.mem_iInf] at hw
  obtain ⟨⟨-, h1⟩, -⟩ := hw
  have e' : x = w (∑ i, al i • g i) := by simp [e]
  have hz : ∑ i, al i • g i ∈ S.spanTo g (j + 1) := ((h1 j).1 _).1 (e' ▸ hx)
  have hB := (h1 j).2 _ hz
  have hK : S.spanTo g j ≤ LinearMap.ker (FramePsi.pairL L S.Hm (gs j)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    change hf L S.Hm (g i) (gs j) = 0
    rw [hd, if_neg]
    rintro rfl
    simp at hi
  have h2 := LinearMap.mem_ker.1 (hK hB)
  rw [← e', map_sub, map_sum, sub_eq_zero] at h2
  have h3 : ∀ i, FramePsi.pairL L S.Hm (gs j) (al i • g i) = if i = j.castSucc then al i else 0 := by
    intro i
    rw [map_smul]
    change al i * hf L S.Hm (g i) (gs j) = _
    rw [hd]
    split_ifs <;> simp
  simp only [h3, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
  exact h2

theorem psi'_eq_one (n : S.GLV) (hn : ∀ v ∈ perp L S.Hm S.X', n v = v) : S.psi' n = 1 := by
  have h : ∀ j, S.coef S.f' S.es' n j = 0 := by
    intro j
    have hp : S.f' j.succ ∈ perp L S.Hm S.X' := by
      refine FramePsi.hf_span_right L S.Hm _ _ ?_
      rintro _ ⟨i, hi, rfl⟩
      rw [S.gram', if_neg]
      rintro ⟨-, rfl⟩
      simp at hi
    rw [Frames.coef, hn _ hp, Frames.h, S.dual', if_neg]
    intro h
    have := congrArg Fin.val h
    simp at this
  simp [Frames.psi', Frames.psiOf, h]

theorem perp_left {A B : Submodule E S.V} {u : S.V} (hu : u ∈ perp L S.Hm (A ⊔ B)) :
    u ∈ perp L S.Hm A := fun y hy => hu y (Submodule.mem_sup_left hy)

theorem perp_right {A B : Submodule E S.V} {u : S.V} (hu : u ∈ perp L S.Hm (A ⊔ B)) :
    u ∈ perp L S.Hm B := fun y hy => hu y (Submodule.mem_sup_right hy)

end

theorem move_term : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x x' u s, S.IsMove (j + 1) d Λ x x' u s → ∃ Λ₁ : Submodule L.O S.V, (Λ₁ : Set S.V) = S.moved Λ x u s ∧ S.IsTerm d Λ₁ ∧ S.moved Λ₁ x (-u) (L.cj s) = Λ ∧ (S.InFF β (j + 1) βJ d Λ₁ → S.IsMove (j + 1) d Λ₁ x x' (-u) (L.cj s)) ∧ ∀ al al' : Fin (r + 1) → E, x = ∑ i, al i • S.fr d Λ i → x' = ∑ i, al' i • S.fr' d Λ i → S.om d Λ₁ = S.om d Λ * L.psi0 (-(algebraMap F E S.th⁻¹ * S.h (al j.castSucc • S.fr d Λ j.succ + al' j.castSucc • S.fr' d Λ j.succ) u)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hFF x x' u s hM
  obtain ⟨n₀, hn₀, n₀', hn₀', n'', hn'', e₀, e₀i, e₀', f'', hset, hW⟩ :=
    GlobalTheory.T.move_lattice_isTerm_same_datum_with_witnesses L r k S j β βJ d Λ hT hFF x x' u s hM
  obtain ⟨t1, t2, -, -, -, -, -, hux, -, -, -⟩ := GlobalTheory.T.hermitianDoubleCosetFrames_datum_move_properties L r k S j β βJ d Λ hT hFF x x' u s hM
  obtain ⟨hT₁, hY⟩ := GlobalTheory.T.hermitianMove_preserves_frameLattice_levels L r k S j β βJ d Λ hT hFF x x' u s hM _ hset
  obtain ⟨hx, hx', hth, hlev, hu, hup, ⟨c, hc, hsc⟩, hs⟩ := hM
  have hb : x + x' ∈ S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1) := Submodule.add_mem_sup hx hx'
  have hmem : ∀ v, v ∈ (n₀⁻¹ • Λ : Submodule L.O S.V) ↔ eich L S.Hm x u s v ∈ Λ := fun v =>
    Set.ext_iff.1 hset v
  refine ⟨n₀⁻¹ • Λ, hset, hT₁, ?_, fun _ => ⟨hx, hx', ?_, ?_, ?_, (perp L S.Hm _).neg_mem hup, ?_, ?_⟩,
    fun al al' ex ex' => ?_⟩
  · ext v
    change eich L S.Hm x (-u) (L.cj s) v ∈ (n₀⁻¹ • Λ : Submodule L.O S.V) ↔ v ∈ Λ
    rw [hmem, ← e₀, ← e₀i]
    rw [show n₀ (n₀⁻¹ v) = v from n₀.apply_symm_apply v]
  · obtain ⟨y, hy, e⟩ := hth
    refine ⟨y, (hY y ?_).1 hy, e⟩
    have : y = algebraMap F E S.th⁻¹ • (x + x') := by
      rw [e, smul_smul, WitIndep.th_mul, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ hb
  · rw [(hY _ hb).2.2, hlev]
  · refine Submodule.neg_mem _ ((hmem u).2 ?_)
    have : eich L S.Hm x u s u = u + s • x + L.cj s • x := by
      have h1 : hf L S.Hm u x = 0 := hux
      have h2 : hf L S.Hm u u = s + L.cj s := hs.symm
      rw [eich, h1, h2]
      module
    rw [this]
    exact Λ.add_mem (Λ.add_mem hu t1) t2
  · exact ⟨L.cj c, cj_mem_O hc, by rw [hsc, map_mul, AlgEquiv.commutes]⟩
  · rw [L.cj_cj, Frames.h, hf_neg_l, hf_neg_r, neg_neg, add_comm]
    exact hs
  · have K := (TermBasic.term_basic L r k S d Λ hT).2.1
    have hw := K.2.2.1
    have hw' := K.2.2.2.1
    obtain ⟨p1, p2, p3, p4⟩ := FramePsi.psi_unitary_character L r k S
    obtain ⟨m, -, em, -, -, pm⟩ := EichlerUnip.eichler_mem_unip L r k S S.f S.es (.inl ⟨rfl, rfl⟩) j x u s
      hx (perp_left S hup) hs
    obtain ⟨m', -, em', -, -, pm'⟩ := EichlerUnip.eichler_mem_unip L r k S S.f' S.es' (.inr ⟨rfl, rfl⟩)
      j x' u s hx' (perp_right S hup) hs
    obtain rfl : m = n₀ := LinearEquiv.ext fun v => (em v).trans (e₀ v).symm
    obtain rfl : m' = n₀' := LinearEquiv.ext fun v => (em' v).trans (e₀' v).symm
    have q := pm _ hw
    have q' := pm' _ hw'
    rw [top_coord S S.f S.es S.dual _ hw j x hx al ex] at q
    rw [top_coord S S.f' S.es' S.dual' _ hw' j x' hx' al' ex'] at q'
    have a1 := p1 m hn₀ _ (mul_mem (inv_mem hn₀) hw)
    rw [mul_inv_cancel_left] at a1
    have a2 := p2 _ (mul_mem hn'' hn₀') _ hw'
    rw [p2 _ hn'' _ hn₀', psi'_eq_one S n'' f'', one_mul] at a2
    have z1 : S.psi m ≠ 0 := fun h => by simpa [h] using (p3 m).1
    have z2 : S.psi' m' ≠ 0 := fun h => by simpa [h] using (p3 m').2
    have hchi : L.psi0 (-(algebraMap F E S.th⁻¹ * S.h (al j.castSucc • S.fr d Λ j.succ +
        al' j.castSucc • S.fr' d Λ j.succ) u)) = (S.psi m * S.psi' m')⁻¹ := by
      rw [AddChar.map_neg_eq_inv]
      congr 1
      change _ = S.psiOf S.f S.es m * S.psiOf S.f' S.es' m'
      rw [q, q', ← AddChar.map_add_eq_mul, Frames.h, hf_add_l, hf_smul_l, hf_smul_l, mul_add]
      rfl
    rw [(WitIndep.witness_independence L r k S _ _ _ _ hW).1, hchi, a2, Frames.om, a1]
    field_simp

end GlobalTheory.HL.MoveTerm
