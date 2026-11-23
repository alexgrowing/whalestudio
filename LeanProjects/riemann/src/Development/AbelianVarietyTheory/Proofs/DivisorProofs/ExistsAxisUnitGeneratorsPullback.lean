import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpSchemeMonHomSquareLiftOneRight
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT.Hecke.PullInj

noncomputable section
namespace GlobalTheory.UPel.HT.Hecke.PullInj

theorem mul_inv_axis_comm_identity {G : Type*} [CommGroup G] (a b W R₁ R₂ : G) :
    a * b⁻¹ * W * (b * R₁) * (a * R₂)⁻¹ = W * R₁ * R₂⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem axis_unit : ∀ (A₀ A₀' X X' : Scheme.{0}) (ψ : A₀ ⟶ A₀') (e : A₀ ⟶ X) (e' : A₀' ⟶ X') (π : X ⟶ X'),
    e ≫ π = ψ ≫ e' → ∀ (Q₁ Q₂ : LB X'), Q₁.IsLB → Q₂.IsLB → ∀ (w : LB.Iso (Q₁.pull π) (Q₂.pull π)), w.IsGen →
    ∀ (ρ₁ : LB.Gen (Q₁.pull e')) (ρ₂ : LB.Gen (Q₂.pull e')), ρ₁.IsGen → ρ₂.IsGen →
    ∃ g : Γ(A₀, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ A₀) (z : Z) (k : (PUnit → Q₂.ι) × (PUnit → Q₁.ι)),
      e (r z) ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k →
      gm (r ≫ e) z _ (w.s k) * gm (r ≫ ψ) z _ (ρ₁.s k.2) = gm r z ⊤ g * gm (r ≫ ψ) z _ (ρ₂.s k.1) := by
  intro A₀ A₀' X X' ψ e e' π h Q₁ Q₂ hQ₁ hQ₂ w hw ρ₁ ρ₂ hρ₁ hρ₂
  have hpt : ∀ x : A₀, π (e x) = e' (ψ x) := fun x => by
    have := congrArg (fun f : A₀ ⟶ X' => f x) h
    simpa using this
  set D := LB.div (Q₂.pull π) (Q₁.pull π)
  let W : D.ι → A₀.Opens := fun k => e ⁻¹ᵁ D.U k
  have h₁ : ∀ k : D.ι, W k ≤ ψ ⁻¹ᵁ (Q₁.pull e').U k.2 := fun k x hx => by
    have hb := (mem_divPull.1 (show e x ∈ D.U k from hx)).2
    rw [hpt] at hb
    exact mem_pull.2 hb
  have h₂ : ∀ k : D.ι, W k ≤ ψ ⁻¹ᵁ (Q₂.pull e').U k.1 := fun k x hx => by
    have hb := (mem_divPull.1 (show e x ∈ D.U k from hx)).1
    rw [hpt] at hb
    exact mem_pull.2 hb
  let u : ∀ k, Γ(A₀, W k)ˣ := fun k =>
    pullU e _ (w.s k) * res (h₁ k) (pullU ψ _ (ρ₁.s k.2)) * (res (h₂ k) (pullU ψ _ (ρ₂.s k.1)))⁻¹
  have hu : ∀ (Z : Scheme.{0}) (r : Z ⟶ A₀) (z : Z) (k : D.ι) (hz : r z ∈ W k),
      gm r z (W k) (u k) = gm (r ≫ e) z _ (w.s k) * gm (r ≫ ψ) z _ (ρ₁.s k.2) * (gm (r ≫ ψ) z _ (ρ₂.s k.1))⁻¹ := by
    intro Z r z k hz
    simp only [u, map_mul, map_inv]
    rw [gm_res r z (h₁ k) hz, gm_res r z (h₂ k) hz, gm_pull r e z _ hz, gm_pull r ψ z _ (h₁ k hz),
      gm_pull r ψ z _ (h₂ k hz)]
  have hcov : (⊤ : A₀.Opens) ≤ iSup W := fun x _ => by
    obtain ⟨i, hi⟩ := exists_chart hQ₂ (π (e x))
    obtain ⟨j, hj⟩ := exists_chart hQ₁ (π (e x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨((fun _ => i), (fun _ => j)), mem_divPull.2 ⟨hi, hj⟩⟩
  have hcomp : ∀ k l, ∀ x ∈ W k ⊓ W l, gm (𝟙 A₀) x (W k) (u k) = gm (𝟙 A₀) x (W l) (u l) := by
    intro k l x hx
    rw [hu _ _ x k hx.1, hu _ _ x l hx.2]
    simp only [Category.id_comp]
    have hk : e x ∈ D.U k := hx.1
    have hl : e x ∈ D.U l := hx.2
    have hk' := mem_divPull.1 hk
    have hl' := mem_divPull.1 hl
    have hk₁ : ψ x ∈ (Q₁.pull e').U k.2 := h₁ k hx.1
    have hl₁ : ψ x ∈ (Q₁.pull e').U l.2 := h₁ l hx.2
    have hk₂ : ψ x ∈ (Q₂.pull e').U k.1 := h₂ k hx.1
    have hl₂ : ψ x ∈ (Q₂.pull e').U l.1 := h₂ l hx.2
    have E := gen_germ hw e x hk hl
    rw [germ_div_g _ _ e x hk hl] at E
    rw [show e = 𝟙 A₀ ≫ e from (Category.id_comp e).symm] at E
    rw [gm_pull_g Q₂ π (𝟙 A₀ ≫ e) x hk'.1 hl'.1, gm_pull_g Q₁ π (𝟙 A₀ ≫ e) x hk'.2 hl'.2] at E
    simp only [Category.id_comp] at E
    have R₁ := gen_germ hρ₁ ψ x hk₁ hl₁
    have R₂ := gen_germ hρ₂ ψ x hk₂ hl₂
    rw [show ψ = 𝟙 A₀ ≫ ψ from (Category.id_comp ψ).symm] at R₁ R₂
    rw [gm_pull_g Q₁ e' (𝟙 A₀ ≫ ψ) x (mem_pull.1 hk₁) (mem_pull.1 hl₁)] at R₁
    rw [gm_pull_g Q₂ e' (𝟙 A₀ ≫ ψ) x (mem_pull.1 hk₂) (mem_pull.1 hl₂)] at R₂
    simp only [Category.id_comp, ← h] at E R₁ R₂
    rw [E, R₁, R₂]
    exact mul_inv_axis_comm_identity _ _ _ _ _
  obtain ⟨g, hg⟩ := glue_unit (⊤ : A₀.Opens) W (fun _ => le_top) hcov u hcomp
  refine ⟨g, fun Z r z k hk => ?_⟩
  have hz : r z ∈ W k := hk
  have e₁ : gm r z ⊤ g = gm r z (W k) (u k) := by rw [← hg k, gm_res r z le_top hz]
  rw [e₁, hu Z r z k hz, inv_mul_cancel_right]

end GlobalTheory.UPel.HT.Hecke.PullInj
