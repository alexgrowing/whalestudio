import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelActionMemCuspFormsOfActionLawsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelActionCuspFormRepresentationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteGroupRightActionComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCocycleCoboundaryOfTrivialOnStabilisers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidualCharacterDetValuesMemCoeffFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightTranslationLiftEqLevelMoveUnitConstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMoveStabiliserCharacterDetStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EquivConst

theorem exists_unit_constants {X G H C : Type} [Group G] [Finite G] [Group H] (L : G → H → Prop) (cp : H → X)
    (ρ : G → C → C) (r : C → H → ℂ) (mu : H → ℂ) (s : G → ℂ) (mv : X → G → X) (z : X → G → ℂ)
    (hex : ∀ g, ∃ k, L g k) (hL : ∀ g g' k k', L g k → L g' k' → L (g * g') (k * k'))
    (hρ1 : ∀ f, ρ 1 f = f) (hρ : ∀ g g' f, ρ (g * g') f = ρ g (ρ g' f))
    (hmu : ∀ h k, mu (h * k) = mu h * mu k) (hmu1 : ∀ h, ‖mu h‖ = 1)
    (hs1 : s 1 = 1) (hs : ∀ g g', s (g * g') = s g * s g')
    (hmv1 : ∀ x, mv x 1 = x) (hmv : ∀ x g g', mv x (g * g') = mv (mv x g) g')
    (hcp : ∀ g k, L g k → ∀ h, cp (h * k) = mv (cp h) g)
    (hz1 : ∀ x g, ‖z x g‖ = 1) (hz : ∀ g k, L g k → ∀ f h, r (ρ g f) h = z (cp h) g * r f (h * k))
    (hst : ∀ g k, L g k → ∀ h, cp (h * k) = cp h → ∀ f, mu h * r (ρ g f) h = s g * (mu (h * k) * r f (h * k))) :
    ∃ c : X → ℂ, (∀ x, ‖c x‖ = 1) ∧ ∀ g k, L g k → ∀ f h,
      c (cp h) * mu h * r (ρ g f) h = s g * (c (cp (h * k)) * mu (h * k) * r f (h * k)) := by
  classical
  choose l hl using hex
  have hsn : ∀ g, ‖s g‖ = 1 := by
    intro g
    let S : G →* ℂ := ⟨⟨s, hs1⟩, hs⟩
    have h1 : s g ^ Nat.card G = 1 := by
      show S g ^ Nat.card G = 1
      rw [← map_pow, pow_card_eq_one', map_one]
    have h2 : ‖s g‖ ^ Nat.card G = 1 := by rw [← norm_pow, h1, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) Nat.card_pos.ne').1 h2
  have ne : ∀ {a : ℂ}, ‖a‖ = 1 → a ≠ 0 := fun {a} h h0 => by simp [h0] at h
  let good : X → Prop := fun x => ∃ f h, cp h = x ∧ r f h ≠ 0
  have hinv : ∀ g f, ρ g (ρ g⁻¹ f) = f := fun g f => by rw [← hρ, mul_inv_cancel, hρ1]
  have hgood : ∀ x g, good x → good (mv x g) := by
    rintro _ g ⟨f, h, rfl, hf⟩
    refine ⟨ρ g⁻¹ f, h * l g, hcp g _ (hl g) h, fun h0 => hf ?_⟩
    rw [← hinv g f, hz g _ (hl g), h0, mul_zero]
  have hgood' : ∀ x g, good (mv x g) → good x := fun x g h => by
    have := hgood _ g⁻¹ h
    rwa [← hmv, mul_inv_cancel, hmv1] at this
  have hone : ∀ x, good x → ∀ k, L 1 k → mu k = z x 1 := by
    rintro _ ⟨f, h, rfl, hf⟩ k hk
    have e1 := hz 1 k hk f h
    have e2 := hst 1 k hk h (by rw [hcp 1 k hk, hmv1]) f
    rw [hρ1] at e1 e2
    have h0 : r f (h * k) ≠ 0 := fun h0 => hf (by rw [e1, h0, mul_zero])
    rw [e1, hs1, hmu, one_mul] at e2
    have : mu h * r f (h * k) * mu k = mu h * r f (h * k) * z (cp h) 1 := by linear_combination -e2
    exact mul_left_cancel₀ (mul_ne_zero (ne (hmu1 h)) h0) this
  have hlift : ∀ x, good x → ∀ g k, L g k → mu k = mu (l g) := by
    intro x hx g k hk
    have e1 := hone x hx (k * l g⁻¹) (by simpa using hL _ _ _ _ hk (hl g⁻¹))
    have e2 := hone x hx (l g * l g⁻¹) (by simpa using hL _ _ _ _ (hl g) (hl g⁻¹))
    rw [hmu] at e1 e2
    exact mul_right_cancel₀ (ne (hmu1 _)) (e1.trans e2.symm)
  let w : X → G → ℂ := fun x g => if good x then z x g / (s g * mu (l g)) else 1
  have hw1 : ∀ x g, ‖w x g‖ = 1 := fun x g => by
    simp only [w]
    split_ifs
    · rw [norm_div, norm_mul, hz1, hsn, hmu1]; norm_num
    · exact norm_one
  have key : ∀ g k, L g k → ∀ f h, mu h * r (ρ g f) h = w (cp h) g * s g * (mu (h * k) * r f (h * k)) := by
    intro g k hk f h
    by_cases hg : good (cp h)
    · simp only [w, if_pos hg]
      rw [hz g k hk, hmu, hlift _ hg g k hk]
      have := ne (hsn g)
      have := ne (hmu1 (l g))
      field_simp
    · have h0 : r (ρ g f) h = 0 := by
        by_contra h0
        exact hg ⟨_, h, rfl, h0⟩
      have h1 : r f (h * k) = 0 := by
        have := hz g k hk f h
        rw [h0] at this
        exact (mul_eq_zero.1 this.symm).resolve_left (ne (hz1 _ _))
      rw [h0, h1]; simp
  obtain ⟨c, hc1, hc⟩ := GlobalTheory.unitary_cocycle_coboundary_of_trivial_on_stabilisers mv w hmv1 hmv hw1 (by
    intro x g g'
    by_cases hg : good x
    · obtain ⟨f, h, rfl, hf⟩ := hg
      have e1 := key (g * g') (l g * l g') (hL _ _ _ _ (hl g) (hl g')) (ρ (g * g')⁻¹ f) h
      have e2 := key g (l g) (hl g) (ρ g' (ρ (g * g')⁻¹ f)) h
      have e3 := key g' (l g') (hl g') (ρ (g * g')⁻¹ f) (h * l g)
      rw [← hρ, e3, hcp g _ (hl g), mul_assoc h] at e2
      rw [hinv] at e1 e2
      rw [hs] at e1
      set P := mu (h * (l g * l g')) * r (ρ (g * g')⁻¹ f) (h * (l g * l g')) with hP
      have hP0 : P ≠ 0 := fun h0 => mul_ne_zero (ne (hmu1 h)) hf (by rw [e1, h0, mul_zero])
      have : s g * s g' * P * w (cp h) (g * g') = s g * s g' * P * (w (cp h) g * w (mv (cp h) g) g') := by
        linear_combination e2 - e1
      exact mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (ne (hsn g)) (ne (hsn g'))) hP0) this
    · simp only [w, if_neg hg, if_neg (fun h => hg (hgood' x g h)), mul_one]) (by
    intro x g hx
    by_cases hg : good x
    · obtain ⟨f, h, rfl, hf⟩ := hg
      have e1 := key g (l g) (hl g) (ρ g⁻¹ f) h
      have e2 := hst g (l g) (hl g) h (by rw [hcp g _ (hl g), hx]) (ρ g⁻¹ f)
      rw [hinv] at e1 e2
      set P := mu (h * l g) * r (ρ g⁻¹ f) (h * l g) with hP
      have hP0 : P ≠ 0 := fun h0 => mul_ne_zero (ne (hmu1 h)) hf (by rw [e1, h0, mul_zero])
      have : s g * P * w (cp h) g = s g * P * 1 := by linear_combination e2 - e1
      exact mul_left_cancel₀ (mul_ne_zero (ne (hsn g)) hP0) this
    · simp only [w, if_neg hg])
  refine ⟨c, hc1, fun g k hk f h => ?_⟩
  rw [mul_assoc, key g k hk, hcp g k hk, ← hc]
  ring

end GlobalTheory.EquivConst

namespace GlobalTheory.EquivConst

theorem isLift_mul {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}
    {g g' : G0 L.Pg L.r} {k k' : GA D V} (hk : Lev.IsLevelLift V β L g k) (hk' : Lev.IsLevelLift V β L g' k') :
    Lev.IsLevelLift V β L (g * g') (k * k') := by
  refine ⟨(GfC V).mul_mem hk.1 hk'.1, ?_, ?_⟩
  · rw [map_mul]; exact Subgroup.mul_mem _ hk.2.1 hk'.2.1
  · rw [map_mul, Formalism.L2.DIV.rTup_mul hk.2.1 hk'.2.1, hk.2.2, hk'.2.2]

theorem muVal_cast {D : D7} {V W : HSp D} (hV : V = W) {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ} (h : MuVal V χ mu) :
    (∀ g g', castDict hV mu (g * g') = castDict hV mu g * castDict hV mu g') ∧ ∀ g, ‖castDict hV mu g‖ = 1 := by
  subst hV
  refine ⟨fun g g' => ?_, fun g => h.norm g⟩
  show mu (g * g') = mu g * mu g'
  obtain ⟨x, hx⟩ := h.1 g
  obtain ⟨x', hx'⟩ := h.1 g'
  have hxx : IsDetRoot V (g * g') (x * x') := by
    unfold IsDetRoot at *
    rw [Units.val_mul, (matHom V).map_mul, Units.val_mul, Matrix.det_mul, RingHom.map_mul]
    conv_lhs => rw [hx, hx']
    ring
  rw [h.2 _ _ hxx, h.2 _ _ hx, h.2 _ _ hx', map_mul, Circle.coe_mul]

theorem phiAt_apply {D : D7} (T : CoreJ D) (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i)
    (c : (T.U ((i : ℕ) + 1) σ).Comp → ℂ) (f : T.R ((i : ℕ) + 1)) (h : GA D (Wc D i)) :
    phiAt T i σ hV c f h = c (castDict hV (T.dict ((i : ℕ) + 1) σ) h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h *
      rdU (T.U ((i : ℕ) + 1) σ) f (castDict hV (T.dict ((i : ℕ) + 1) σ) h).1 (castDict hV (T.dict ((i : ℕ) + 1) σ) h).2 := rfl

set_option maxHeartbeats 1000000 in

theorem exists_equivariant_constants : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, OMPins T R κ v₀ O i) → ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i, ∃ c', CUnit c' ∧ EqAt T R κ (O i) σ hV c' := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hI hT hpb hO i σ hσ hV
  have hact := (hO i).2.act.1
  have hkeep := fun g => GlobalTheory.T.levelAction_mem_cuspForms_of_action_laws T κ i (O i).lev2 hT.laws hact g (fun _ => rfl)
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_level_action_cusp_form_representation T κ i (O i).lev2 hT.laws hact hkeep
  have hex : ∀ g, ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k :=
    fun g => ((hO i).2.lift.lev g).imp fun _ h => h.1
  obtain ⟨mv, hmv1, hmv, -, hcp⟩ := GlobalTheory.T.exists_finiteGroup_rightAction_components T R κ v₀ hI hT hpb i σ hσ hV hex
  choose y hy using GlobalTheory.T.residual_character_det_values_mem_coeff_field T R κ v₀ hI hT i
  obtain ⟨z, hz1, hz⟩ := GlobalTheory.T.rightTranslation_lift_eq_levelMove_unit_const T R κ v₀ O hI hT hpb hO i σ hσ hV
  have hst := GlobalTheory.T.levelMove_stabiliser_character_det T R κ v₀ O hI hT hpb hO i σ hσ hV
  have hmu := muVal_cast hV (hT.laws.muVal _ (inR i) σ hσ)
  have hinj : Function.Injective fun a : T.Q.c.F => D.what₂.embLL (algebraMap T.Q.c.F D.what₂.LL a) :=
    D.what₂.embLL.injective.comp (algebraMap T.Q.c.F D.what₂.LL).injective
  have hy1 : y 1 = 1 := hinj (by
    show D.what₂.embLL _ = D.what₂.embLL _
    have : chiC R i 1 = 1 := by
      have := chiC_mul R i 1 1
      rw [mul_one] at this
      exact left_eq_mul.1 this
    rw [hy, this, map_one, map_one, Units.val_one])
  have hym : ∀ g g', y (g * g') = y g * y g' := fun g g' => hinj (by
    show D.what₂.embLL _ = D.what₂.embLL _
    rw [map_mul, map_mul, hy, hy, hy, chiC_mul, Units.val_mul])
  obtain ⟨c, hc1, hc⟩ := exists_unit_constants (C := Cu T κ i)
    (fun g k => Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k)
    (fun h => (castDict hV (T.dict ((i : ℕ) + 1) σ) h).1) (fun g f => ρ g f)
    (fun f h => rdU (T.U ((i : ℕ) + 1) σ) (f : T.R ((i : ℕ) + 1)) (castDict hV (T.dict ((i : ℕ) + 1) σ) h).1
      (castDict hV (T.dict ((i : ℕ) + 1) σ) h).2)
    (castDict hV (T.mu ((i : ℕ) + 1) σ)) (fun g => σ (y g)) mv z hex
    (fun g g' k k' hk hk' => by
      have := isLift_mul hk hk'
      show Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG (g * g')) _
      rw [map_mul]
      exact this)
    (fun f => by rw [map_one]; rfl) (fun g g' f => by rw [map_mul]; rfl) hmu.1 hmu.2
    (by rw [hy1, map_one]) (fun g g' => by rw [hym, map_mul]) hmv1 hmv hcp hz1
    (fun g k hk f h => by
      have := hz g k hk f f.2 h
      rw [← hρ] at this
      exact this)
    (fun g k hk h hh f => by
      have := hst g k hk (y g) (hy g) h hh f f.2
      rw [phiAt_apply, phiAt_apply, ← hρ, one_mul, one_mul] at this
      exact this)
  refine ⟨c, hc1, fun g k hk f hf => ⟨hkeep g f hf, y g, ?_, fun h => ?_⟩⟩
  · rw [hy, chiC, Units.coe_prod]
  · have := hc g k hk ⟨f, hf⟩ h
    rw [hρ] at this
    rw [phiAt_apply, phiAt_apply]
    exact this

end GlobalTheory.EquivConst
