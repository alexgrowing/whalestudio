import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardLatticeQuotientHalfLevel
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValCAlpha
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.AnChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaWeightBounds
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory

section

variable {E : Type} [Field E] [NumberField E] {dim : (E →+* ℂ) → ℕ}

theorem levReps_act_mul (a b : 𝓞 E) (v : I2.Vsp dim) : I2.act a (I2.act b v) = I2.act (a * b) v := by
  ext i
  simp only [I2.act, RingOfIntegers.coe_eq_algebraMap, map_mul]
  exact (mul_assoc _ _ _).symm

theorem levReps_act_nat (m : ℕ) (v : I2.Vsp dim) : I2.act (m : 𝓞 E) v = (m : ℂ) • v := by
  ext i
  simp [I2.act]

theorem levReps_act_smul (a : 𝓞 E) (c : ℂ) (v : I2.Vsp dim) : I2.act a (c • v) = c • I2.act a v := by
  ext i
  simp [I2.act]
  ring

theorem levReps_act_add (a : 𝓞 E) (v w : I2.Vsp dim) : I2.act a (v + w) = I2.act a v + I2.act a w := by
  ext i
  simp [I2.act, mul_add]

theorem levReps_act_neg (a : 𝓞 E) (v : I2.Vsp dim) : I2.act a (-v) = -I2.act a v := by
  ext i
  simp [I2.act]

end

theorem isReps_level_translates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (T : I2.PT E) (mk : Dw.La →+ I2.Vsp T.dim) (α : 𝓞 E), α * H.bar α = (l.M : 𝓞 E) → l.Mb = Ideal.span {H.bar α} → (∀ a, mk a ∈ T.L) → (∀ (β : 𝓞 E) a, mk (β • a) = I2.act β (mk a)) → (∀ a, (∃ v ∈ T.L, mk a = (l.M : ℂ) • v) → ∃ b, a = l.M • b) → (∀ v ∈ T.L, ∃ a, ∃ v' ∈ T.L, v = mk a + (l.M : ℂ) • v') → ∀ x2 : LevQ Dw l → Dw.La, (∀ q, x2 q ∈ (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ q, x2 q - levRep q ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → ∀ n : ℕ, ∃ K : Finset (Fin n → I2.Vsp T.dim), I2.IsReps T l.M n (vspActL α) K ∧ ∀ b ∈ K, ∃ q : Fin n → LevQ Dw l, b = fun i => I2.act (H.bar α) (-(((l.M : ℂ) ^ 2)⁻¹ • mk (x2 (q i)))) := by
  intro E _ _ _ H Dw l T mk α hα hMb hL hlin hinj hsurj x2 hx2 hrep n
  classical
  haveI : Finite (LevQ Dw l) := (card_levQ E H Dw l).1
  haveI : Fintype (LevQ Dw l) := Fintype.ofFinite _
  have hM : (l.M : ℂ) ≠ 0 := by
    have := l.three_le
    exact Nat.cast_ne_zero.2 (by omega)
  have hbb : H.bar (H.bar α) = α := by
    apply Subtype.ext
    change ((H.bar (H.bar α) : 𝓞 E) : E) = (α : E)
    rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]
  have hmap : l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {α} := by
    rw [hMb, Ideal.map_span, Set.image_singleton]
    exact congrArg (fun z => Ideal.span {z}) hbb
  have hsm : ∀ (c : 𝓞 E) (y : Dw.La), y ∈ Ideal.span {c} • (⊤ : Submodule (𝓞 E) Dw.La) ↔ ∃ z, y = c • z := by
    intro c y
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨fun ⟨z, _, h⟩ => ⟨z, h.symm⟩, fun ⟨z, h⟩ => ⟨z, trivial, h.symm⟩⟩
  have hu : ∀ q, ∃ u : Dw.La, x2 q = α • α • u := by
    intro q
    have h := hx2 q
    rw [hmap, Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton, hsm] at h
    obtain ⟨z, hz⟩ := h
    refine ⟨(2 : 𝓞 E) • z, ?_⟩
    rw [hz, smul_smul, smul_smul]
    congr 1
    ring
  have hcls : ∀ q, (Submodule.Quotient.mk (x2 q) : LevQ Dw l) = q := by
    intro q
    rw [(Submodule.Quotient.eq _).2 (hrep q)]
    exact Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)
  obtain ⟨r, s, hrs⟩ : ∃ r s : 𝓞 E, r * H.bar α + s * α = 1 := by
    have h := l.coprime
    rw [hmap, hMb, Ideal.eq_top_iff_one, ← Ideal.span_insert, Ideal.mem_span_pair] at h
    exact h
  set t : LevQ Dw l → I2.Vsp T.dim := fun q => I2.act (H.bar α) (-(((l.M : ℂ) ^ 2)⁻¹ • mk (x2 q))) with ht
  have hαt : ∀ q, I2.act α (t q) = -((l.M : ℂ)⁻¹ • mk (x2 q)) := by
    intro q
    simp only [ht]
    rw [levReps_act_mul, hα, levReps_act_nat, smul_neg, smul_smul]
    congr 2
    field_simp
  have hMt : ∀ q, (l.M : ℂ) • t q ∈ T.L := by
    intro q
    obtain ⟨u, hq⟩ := hu q
    have : (l.M : ℂ) • t q = -mk (α • u) := by
      simp only [ht]
      rw [hq, hlin α (α • u), levReps_act_neg, levReps_act_smul, levReps_act_mul, mul_comm (H.bar α), hα,
        levReps_act_nat, smul_neg, smul_smul, smul_smul]
      have : (l.M : ℂ) * ((l.M : ℂ) ^ 2)⁻¹ * l.M = 1 := by field_simp
      rw [this, one_smul]
    rw [this]
    exact T.L.neg_mem (hL _)
  have hsub : ∀ (b : I2.Vsp T.dim) q, vspActL α (b - t q) = I2.act α b + (l.M : ℂ)⁻¹ • mk (x2 q) := by
    intro b q
    rw [map_sub]
    change I2.act α b - I2.act α (t q) = _
    rw [hαt, sub_neg_eq_add]
  have hex : ∀ b : I2.Vsp T.dim, (l.M : ℂ) • b ∈ T.L → ∃ q, vspActL α (b - t q) ∈ T.L := by
    intro b hb
    obtain ⟨a, v', hv', hab⟩ := hsurj _ hb
    refine ⟨Submodule.Quotient.mk (-(α • a)), ?_⟩
    set q : LevQ Dw l := Submodule.Quotient.mk (-(α • a)) with hq
    have h1 : x2 q - -(α • a) ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) :=
      (Submodule.Quotient.eq _).1 ((hcls q).trans hq)
    rw [hMb, hsm] at h1
    obtain ⟨d, hd⟩ := h1
    obtain ⟨u, hqu⟩ := hu q
    have h2 : x2 q + α • a = (l.M : 𝓞 E) • (r • (α • u + a) + s • d) := by
      have e1 : x2 q + α • a = α • (α • u + a) := by rw [hqu, smul_add]
      have e2 : x2 q + α • a = H.bar α • d := by rw [← hd, sub_neg_eq_add]
      calc x2 q + α • a = (r * H.bar α + s * α) • (x2 q + α • a) := by rw [hrs, one_smul]
        _ = (r * H.bar α) • α • (α • u + a) + (s * α) • H.bar α • d := by rw [add_smul, ← e1, ← e2]
        _ = _ := by
          rw [← hα, smul_add (α * H.bar α)]
          simp only [smul_smul (r * H.bar α), smul_smul (s * α), smul_smul (α * H.bar α)]
          congr 2 <;> ring
    have hb' : b = (l.M : ℂ)⁻¹ • mk a + v' := by
      calc b = (l.M : ℂ)⁻¹ • (l.M : ℂ) • b := by rw [smul_smul, inv_mul_cancel₀ hM, one_smul]
        _ = _ := by rw [hab, smul_add, smul_smul, inv_mul_cancel₀ hM, one_smul]
    have h3 : vspActL α (b - t q) = mk (r • (α • u + a) + s • d) + I2.act α v' := by
      rw [hsub, hb', levReps_act_add, levReps_act_smul, ← hlin, add_right_comm, ← smul_add, ← map_add,
        add_comm (α • a), h2, hlin, levReps_act_nat, smul_smul, inv_mul_cancel₀ hM, one_smul]
    rw [h3]
    exact T.L.add_mem (hL _) (T.stable _ _ hv')
  have huniq : ∀ (b : I2.Vsp T.dim) q q', vspActL α (b - t q) ∈ T.L → vspActL α (b - t q') ∈ T.L → q = q' := by
    intro b q q' h h'
    have h1 := T.L.sub_mem h h'
    rw [hsub, hsub, add_sub_add_left_eq_sub, ← smul_sub, ← map_sub] at h1
    obtain ⟨z, hz⟩ := hinj (x2 q - x2 q') ⟨_, h1, by rw [smul_smul, mul_inv_cancel₀ hM, one_smul]⟩
    rw [← hcls q, ← hcls q']
    refine (Submodule.Quotient.eq _).2 ?_
    rw [hMb, hsm]
    exact ⟨α • z, by rw [hz, smul_smul, mul_comm, hα, Nat.cast_smul_eq_nsmul]⟩
  refine ⟨Finset.univ.image (fun q : Fin n → LevQ Dw l => fun i => t (q i)), ⟨?_, ?_⟩, ?_⟩
  · intro b hb k
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hb
    exact hMt _
  · intro b hb
    choose q hq using fun k => hex (b k) (hb k)
    refine ⟨fun i => t (q i), ⟨Finset.mem_image.2 ⟨q, Finset.mem_univ _, rfl⟩, hq⟩, ?_⟩
    rintro b' ⟨hb', h'⟩
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hb'
    funext k
    rw [huniq (b k) _ _ (h' k) (hq k)]
  · intro b hb
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hb
    exact ⟨q, rfl⟩

end GlobalTheory
