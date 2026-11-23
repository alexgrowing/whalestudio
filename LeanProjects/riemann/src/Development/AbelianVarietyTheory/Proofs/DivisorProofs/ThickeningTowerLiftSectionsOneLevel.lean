import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ProjectiveNotIsUnit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartCocycleOfPullbackPowerStandardStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftSectionsNextThickeningStandardChartsStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section
namespace GlobalTheory.FormalAlg

theorem glue_chart {X X' : Scheme.{0}} (φ : X' ⟶ X) {M L' : LB X} {L : LB X'} (ω : LB.Iso L' M)
    (hω : ω.IsGen) (u : LB.Iso L (L'.pull φ)) (hu : PGen u) (hM : M.IsLB) (hL' : L'.IsLB) (hL : L.IsLB)
    (σ : LB.Sec L) (i : M.ι) :
    ∃ a : Γ(X', φ ⁻¹ᵁ M.U i), ∀ z b c, φ z ∈ M.U i → φ z ∈ L'.U b → z ∈ L.U c →
      gs (𝟙 _) z _ a = (gv ω φ z i b).val * ((gw u (𝟙 _) z b c).val * gs (𝟙 _) z _ (σ.f c)) := by
  let W : L'.ι × L.ι → X'.Opens := fun p => φ ⁻¹ᵁ (M.U i ⊓ L'.U p.1) ⊓ L.U p.2
  have l₀ : ∀ p, W p ≤ φ ⁻¹ᵁ M.U i := fun p x hx => hx.1.1
  have l₁ : ∀ p, W p ≤ φ ⁻¹ᵁ (M.U i ⊓ L'.U p.1) := fun p x hx => hx.1
  have l₂ : ∀ p, W p ≤ (L'.pull φ).U (fun _ => p.1) ⊓ L.U p.2 := fun p x hx => ⟨mem_pull.2 hx.1.2, hx.2⟩
  have l₃ : ∀ p, W p ≤ L.U p.2 := fun p x hx => hx.2
  have key : ∀ (y : X') (b b' : L'.ι) (c c' : L.ι), φ y ∈ M.U i → φ y ∈ L'.U b → φ y ∈ L'.U b' →
      y ∈ L.U c → y ∈ L.U c' →
      (gv ω φ y i b).val * ((gw u (𝟙 _) y b c).val * gs (𝟙 _) y _ (σ.f c)) =
        (gv ω φ y i b').val * ((gw u (𝟙 _) y b' c').val * gs (𝟙 _) y _ (σ.f c')) := by
    intro y b b' c c' hi hb hb' hc hc'
    have h1 := gm_isGen hω φ y i i b b' hi hi hb hb'
    have h2 := hu X' (𝟙 _) y b b' c c' hb hb' hc hc'
    have h3 := GlobalTheory.SecPullIso.gs_sec_trans σ (𝟙 _) y hc hc'
    rw [gm_self hM φ y hi, one_mul] at h1
    rw [Category.id_comp] at h2
    rw [h1, h2, h3]
    generalize gm φ y _ (L'.g b b') = B
    generalize gm (𝟙 X') y _ (L.g c c') = C
    generalize gv ω φ y i b' = D
    generalize gw u (𝟙 _) y b' c' = E
    generalize gs (𝟙 X') y _ (σ.f c') = s
    simp only [Units.val_mul]
    have hB := B.inv_mul
    have hC := C.inv_mul
    linear_combination ((D : _) * E * s * (C⁻¹ : _ˣ) * C) * hB + ((D : _) * E * s) * hC
  obtain ⟨v, hv⟩ : ∃ v : ∀ p, Γ(X', W p), ∀ z p, z ∈ W p →
      gs (𝟙 _) z (W p) (v p) = (gv ω φ z i p.1).val * ((gw u (𝟙 _) z p.1 p.2).val * gs (𝟙 _) z _ (σ.f p.2)) :=
    ⟨fun p => (res (l₁ p) (pullU φ _ (ω.s (i, p.1)))).val * ((res (l₂ p) (u.s (fun _ => p.1, p.2))).val *
        (X'.presheaf.map (homOfLE (l₃ p)).op).hom (σ.f p.2)), fun z p hz => by
      rw [gs_mul _ z _ hz, gs_mul _ z _ hz, gs_unit _ z _ hz, gs_unit _ z _ hz, gm_res (𝟙 X') z (l₁ p) hz,
        show gm (𝟙 X') z (W p) (res (l₂ p) (u.s (fun _ => p.1, p.2))) = gw u (𝟙 _) z p.1 p.2 from gm_res (𝟙 X') z (l₂ p) hz _, gs_res (𝟙 X') z (l₃ p) hz, show gm (𝟙 X') z (φ ⁻¹ᵁ (M.U i ⊓ L'.U p.1)) (pullU φ _ (ω.s (i, p.1))) = gv ω φ z i p.1 from
          (gm_pull (𝟙 _) φ z _ (l₁ p hz) _).trans (by rw [Category.id_comp]; rfl)]⟩
  obtain ⟨a, ha, -⟩ := X'.sheaf.existsUnique_gluing' W (φ ⁻¹ᵁ M.U i) (fun p => homOfLE (l₀ p)) (fun y hy => by
      obtain ⟨b, hb⟩ := exists_chart hL' (φ y)
      obtain ⟨c, hc⟩ := exists_chart hL y
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(b, c), ⟨hy, hb⟩, hc⟩) v
    (fun p q => fn_ext (V := W p ⊓ W q) fun y hy => by
      refine (gs_res (𝟙 _) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 _) y inf_le_right hy _).symm)
      rw [hv y p hy.1, hv y q hy.2]
      exact key y p.1 q.1 p.2 q.2 hy.1.1.1 hy.1.1.2 hy.2.1.2 hy.1.2 hy.2.2)
  refine ⟨a, fun z b c h₁ h₂ h₃ => ?_⟩
  have hz : z ∈ W (b, c) := ⟨⟨h₁, h₂⟩, h₃⟩
  exact (gs_res (𝟙 _) z (l₀ (b, c)) hz a).symm.trans ((congrArg (gs (𝟙 _) z (W (b, c))) (ha (b, c))).trans
    (hv z (b, c) hz))

theorem lift_step : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (H₀ : LB (Y 0).left) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → ((∀ i, C.D 0 i = nonzeroLocus (s₀ i)) ∧ ∀ i j (m : H₀.ι), rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ j).f m) = rs (Y 0).left (inf_le_left : C.D 0 i ⊓ H₀.U m ≤ C.D 0 i) (C.ρ 0 i j) * rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ i).f m)) → ∀ γ : ∀ e, (Y 0).left ⟶ (Y e).left, γ 0 = 𝟙 _ → (∀ e, γ e ≫ β e = γ (e + 1)) → ∀ (e k : ℕ), (∀ c : ∀ i j, Γ((Y (e + 1)).left, C.D (e + 1) i ⊓ C.D (e + 1) j), (∀ i j, c i j ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) _) → (∀ i j l, rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) j) (c i j) + rs (Y (e + 1)).left (inf_le_left.trans inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) j ⊓ C.D (e + 1) l) (c j l) = rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) l) (c i l)) → ∃ a : ∀ i, Γ((Y (e + 1)).left, C.D (e + 1) i), (∀ i, a i ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) _) ∧ ∀ i j, c i j = rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (a i) - rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (a j)) → ∀ (L : LB (Y e).left) (L' : LB (Y (e + 1)).left) (u : LB.Iso L (L'.pull (β e))), L.IsLB → L'.IsLB → u.IsGen → LBIso (L'.pull (γ (e + 1))) (GlobalTheory.AbLaw.pw H₀ k) → ∀ σ : LB.Sec L, ∃ σ' : LB.Sec L', Rel (β e) u σ' σ := by
  intro R _ I Y β hβ n C H₀ s₀ hH₀ hs₀ γ hγ0 hγ e k hc L L' u hL hL' hu hpw σ
  obtain ⟨g, hMLB, ⟨ω, hω⟩, hcong⟩ := GlobalTheory.T.exists_chart_cocycle_of_pullback_power_standard R I Y β hβ n C H₀ s₀ hH₀ hs₀ γ hγ0 hγ (e + 1) k L' hL' hpw
  have hup : PGen u := (isGen_iff u).1 hu
  choose σi hσi using fun i => glue_chart (M := (⟨Fin (n + 1), C.D (e + 1), g⟩ : LB (Y (e + 1)).left)) (β e) ω hω u
    hup hMLB hL' hL σ i
  have hcoc : ∀ z i j, β e z ∈ C.D (e + 1) i → β e z ∈ C.D (e + 1) j →
      gs (𝟙 _) z _ (σi i) = gs (β e) z _ (g i j).val * gs (𝟙 _) z _ (σi j) := by
    intro z i j hi hj
    obtain ⟨b, hb⟩ := exists_chart hL' (β e z)
    obtain ⟨c, hc'⟩ := exists_chart hL z
    rw [hσi i z b c hi hb hc', hσi j z b c hj hb hc']
    have h1 := gm_isGen hω (β e) z i j b b hi hj hb hb
    rw [gm_self hL' (β e) z hb, inv_one, mul_one] at h1
    rw [h1, gs_unit (β e) z (C.D (e + 1) i ⊓ C.D (e + 1) j) ⟨hi, hj⟩, Units.val_mul, mul_assoc]
  obtain ⟨σ'', hσ''⟩ := GlobalTheory.T.lift_sections_next_thickening_standardCharts R I Y β hβ n C e k hc g hMLB hcong σi hcoc
  let w := isoPullId ω (F := 𝟙 _) rfl
  have hw : w.IsGen := (isGen_iff w).2 (isoPullId_pgen hω rfl)
  obtain ⟨σ', hσ'⟩ := GlobalTheory.SecPullIso.exists_pull (𝟙 _) _ L' w hMLB hL' hw σ''
  refine ⟨σ', fun z b c hb hc' => ?_⟩
  obtain ⟨i, hi⟩ := exists_chart hMLB (β e z)
  have hR : Rel (𝟙 _) w σ'' σ' := hσ'
  have e1 := hR.pull (β e) z i b hi hb
  rw [Category.comp_id, gw_isoPullId ω rfl (β e) z i b hi hb] at e1
  have e2 : gs (β e) z _ (σ''.f i) = gs (𝟙 _) z _ (σi i) := by
    rw [← hσ'' i, gs_pull (𝟙 _) (β e) z _ hi, Category.id_comp]
  rw [e2, hσi i z b c hi hb hc'] at e1
  exact ((Units.mul_right_inj (gv ω (β e) z i b)).1 e1).symm

end GlobalTheory.FormalAlg
