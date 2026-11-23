import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ProjectiveNotIsUnit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section

namespace GlobalTheory.Div.FramePull

variable {X X₀ : Scheme.{0}}

theorem isUnit_res_of_le {V U : X₀.Opens} (f : Γ(X₀, U)) (h : V ≤ X₀.basicOpen f) :
    IsUnit ((X₀.presheaf.map (homOfLE (h.trans (X₀.basicOpen_le f))).op).hom f) := by
  have e : (X₀.presheaf.map (homOfLE (h.trans (X₀.basicOpen_le f))).op).hom f =
      (X₀.presheaf.map (homOfLE h).op).hom ((X₀.presheaf.map (homOfLE (X₀.basicOpen_le f)).op).hom f) := by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
  rw [e]
  exact (X₀.toRingedSpace.isUnit_res_basicOpen f).map _

theorem le_basicOpen {H : LB X₀} (s : LB.Sec H) (a : H.ι) :
    nonzeroLocus s ⊓ H.U a ≤ X₀.basicOpen (s.f a) := by
  rintro z ⟨hz, ha⟩
  obtain ⟨a', ha'⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
  have e := congrArg X₀.basicOpen (s.compat a a')
  rw [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (H.g a a').isUnit, Scheme.basicOpen_res,
    Scheme.basicOpen_res] at e
  have hm : z ∈ H.U a ⊓ H.U a' ⊓ X₀.basicOpen (s.f a) := by
    rw [e]; exact ⟨⟨ha, X₀.basicOpen_le _ ha'⟩, ⟨ha, X₀.basicOpen_le _ ha'⟩, ha'⟩
  exact hm.2

theorem gm_gen_div {M L' : LB X₀} {w : LB.Iso L' M} (hw : w.IsGen) (z : X₀) (p q : M.ι × L'.ι)
    (hp : z ∈ M.U p.1 ⊓ L'.U p.2) (hq : z ∈ M.U q.1 ⊓ L'.U q.2) :
    gm (𝟙 X₀) z _ (w.s p) = gm (𝟙 X₀) z (M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1) *
      (gm (𝟙 X₀) z (L'.U p.2 ⊓ L'.U q.2) (L'.g p.2 q.2))⁻¹ * gm (𝟙 X₀) z _ (w.s q) := by
  have hm : z ∈ (LB.div M L').U p ⊓ (LB.div M L').U q := ⟨hp, hq⟩
  have := congrArg (gm (𝟙 X₀) z _) (hw p q)
  rw [gm_res _ z _ hm, map_mul, gm_res _ z _ hm] at this
  rw [this]
  refine congrArg (· * _) ?_
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ z _ hm _)
    ((map_inv _ _).trans (congrArg _ (gm_res _ z _ hm _))))

theorem gm_pull_g (L : LB X) (γ : X₀ ⟶ X) (z : X₀) (m m' : L.ι) (hm : γ z ∈ L.U m) (hm' : γ z ∈ L.U m') :
    gm (𝟙 X₀) z ((L.pull γ).U (fun _ => m) ⊓ (L.pull γ).U (fun _ => m'))
      ((L.pull γ).g (fun _ => m) (fun _ => m')) = gm γ z _ (L.g m m') := by
  have hp : z ∈ (L.pull γ).U (fun _ => m) ⊓ (L.pull γ).U (fun _ => m') := ⟨mem_pull.2 hm, mem_pull.2 hm'⟩
  show gm (𝟙 X₀) z _ (∏ _k : PUnit, (res _ (pullU γ _ (L.g m m'))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  refine (gm_res _ z _ hp _).trans ((gm_pull (𝟙 X₀) γ z (L.U m ⊓ L.U m') ⟨hm, hm'⟩ _).trans ?_)
  rw [Category.id_comp]

theorem grp₁ {M : Type} [CommGroup M] (G S W : M) (k : ℕ) :
    (G * S) ^ k * (G ^ (k : ℤ) * 1⁻¹ * W)⁻¹ = S ^ k * W⁻¹ := by
  rw [zpow_natCast, inv_one, mul_one, mul_pow, mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]

theorem grp₂ {M : Type} [CommGroup M] (S Γ W : M) (k : ℕ) :
    S ^ k * ((1 : M) ^ (k : ℤ) * Γ⁻¹ * W)⁻¹ = Γ * (S ^ k * W⁻¹) := by
  rw [one_zpow, one_mul, mul_inv, inv_inv, mul_left_comm]

theorem frame_pull : ∀ (X X₀ : Scheme.{0}) (γ : X₀ ⟶ X) (H₀ : LB X₀) (s : LB.Sec H₀) (k : ℕ) (L : LB X), L.IsLB →
    H₀.IsLB → ∀ (w : LB.Iso (L.pull γ) (pw H₀ k)), w.IsGen → ∀ (D : X.Opens), γ ⁻¹ᵁ D = nonzeroLocus s →
    ∃ u : ∀ m : L.ι, Γ(X₀, γ ⁻¹ᵁ (D ⊓ L.U m))ˣ, (∀ z m m', γ z ∈ D ⊓ L.U m → γ z ∈ D ⊓ L.U m' →
      gm (𝟙 X₀) z _ (u m) = gm γ z _ (L.g m m') * gm (𝟙 X₀) z _ (u m')) ∧
      ∀ z m a, γ z ∈ D ⊓ L.U m → z ∈ H₀.U a →
        gs (𝟙 X₀) z _ (s.f a) ^ k = (gm (𝟙 X₀) z _ (u m)).val * (gm (𝟙 X₀) z _ (w.s (a, fun _ => m))).val := by
  intro X X₀ γ H₀ s k L hL hH w hw D hD
  let W : L.ι → H₀.ι → X₀.Opens := fun m a => γ ⁻¹ᵁ (D ⊓ L.U m) ⊓ H₀.U a
  have hWb : ∀ m a, W m a ≤ X₀.basicOpen (s.f a) := fun m a z hz =>
    le_basicOpen s a ⟨hD ▸ (show z ∈ γ ⁻¹ᵁ D from hz.1.1), hz.2⟩
  have hWw : ∀ m a, W m a ≤ (LB.div (pw H₀ k) (L.pull γ)).U (a, fun _ => m) := fun m a z hz =>
    ⟨hz.2, mem_pull.2 hz.1.2⟩
  let S : ∀ m a, Γ(X₀, W m a)ˣ := fun m a => (isUnit_res_of_le (s.f a) (hWb m a)).unit
  let v : ∀ m a, Γ(X₀, W m a)ˣ := fun m a => S m a ^ k * (res (hWw m a) (w.s (a, fun _ => m)))⁻¹
  have hS : ∀ m a z (hz : z ∈ W m a), (gm (𝟙 X₀) z _ (S m a)).val = gs (𝟙 X₀) z _ (s.f a) := by
    intro m a z hz
    rw [← gs_unit _ z _ hz, IsUnit.unit_spec]
    exact gs_res _ z _ hz _
  have hv : ∀ m a z (hz : z ∈ W m a), gm (𝟙 X₀) z _ (v m a) =
      gm (𝟙 X₀) z _ (S m a) ^ k * (gm (𝟙 X₀) z _ (w.s (a, fun _ => m)))⁻¹ := by
    intro m a z hz
    simp only [v, map_mul, map_pow, map_inv]
    rw [gm_res _ z _ hz]

  have hwg : ∀ z a a' m m', z ∈ H₀.U a → z ∈ H₀.U a' → γ z ∈ L.U m → γ z ∈ L.U m' →
      gm (𝟙 X₀) z _ (w.s (a, fun _ => m)) = gm (𝟙 X₀) z (H₀.U a ⊓ H₀.U a') (H₀.g a a') ^ (k : ℤ) *
        (gm γ z _ (L.g m m'))⁻¹ * gm (𝟙 X₀) z _ (w.s (a', fun _ => m')) := by
    intro z a a' m m' ha ha' hm hm'
    rw [gm_gen_div hw z (a, fun _ => m) (a', fun _ => m') ⟨ha, mem_pull.2 hm⟩ ⟨ha', mem_pull.2 hm'⟩,
      gm_pull_g L γ z m m' hm hm']
    exact congrArg (fun t => t * _ * _) (map_zpow _ _ _)
  have hSg : ∀ m m' a a' z (hz : z ∈ W m a) (hz' : z ∈ W m' a'),
      gm (𝟙 X₀) z _ (S m a) = gm (𝟙 X₀) z (H₀.U a ⊓ H₀.U a') (H₀.g a a') * gm (𝟙 X₀) z _ (S m' a') := by
    intro m m' a a' z hz hz'
    apply Units.ext
    rw [Units.val_mul, hS m a z hz, hS m' a' z hz']
    exact gs_sec_chart s (𝟙 X₀) z hz.2 hz'.2
  have glue : ∀ m, ∃ t : Γ(X₀, γ ⁻¹ᵁ (D ⊓ L.U m))ˣ, ∀ a, res (inf_le_left : W m a ≤ _) t = v m a := by
    intro m
    refine glue_unit (γ ⁻¹ᵁ (D ⊓ L.U m)) (W m) (fun a => inf_le_left) (fun z hz => ?_) (v m) ?_
    · obtain ⟨a, ha⟩ := exists_chart hH z
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, hz, ha⟩
    · intro a a' z hz
      rw [hv m a z hz.1, hv m a' z hz.2, hSg m m a a' z hz.1 hz.2,
        hwg z a a' m m hz.1.2 hz.2.2 hz.1.1.2 hz.1.1.2, gm_self hL γ z hz.1.1.2]
      exact grp₁ _ _ _ k
  choose u hu using glue
  have hug : ∀ m a z (hz : z ∈ W m a), gm (𝟙 X₀) z _ (u m) = gm (𝟙 X₀) z _ (v m a) := by
    intro m a z hz
    rw [← hu m a, gm_res _ z _ hz]
  refine ⟨u, fun z m m' hm hm' => ?_, fun z m a hm ha => ?_⟩
  · obtain ⟨a, ha⟩ := exists_chart hH z
    have hz : z ∈ W m a := ⟨hm, ha⟩
    have hz' : z ∈ W m' a := ⟨hm', ha⟩
    rw [hug m a z hz, hug m' a z hz', hv m a z hz, hv m' a z hz', hSg m m' a a z hz hz',
      gm_self hH (𝟙 X₀) z ha, one_mul, hwg z a a m m' ha ha hm.2 hm'.2, gm_self hH (𝟙 X₀) z ha]
    exact grp₂ _ _ _ k
  · have hz : z ∈ W m a := ⟨hm, ha⟩
    rw [hug m a z hz, hv m a z hz, ← hS m a z hz, ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_mul_cancel_right]

end GlobalTheory.Div.FramePull
