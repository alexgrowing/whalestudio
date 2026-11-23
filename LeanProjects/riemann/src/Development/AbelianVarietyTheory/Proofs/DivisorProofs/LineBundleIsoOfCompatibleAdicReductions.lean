import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ProjectiveNotIsUnit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorAlgebraisationReductionsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

namespace GlobalTheory.FormalAlg

theorem lbIso_of_compatible_reductions : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), IsProper X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (A A' : LB X.left), A.IsLB → A'.IsLB → ∀ c : ∀ e, LB.Iso (A.pull (b e)) (A'.pull (b e)), (∀ e, (c e).IsGen) → (∀ e z k k', b e z ∈ A.U k → b e z ∈ A'.U k' → Geo.Tor.gw (c (e + 1)) (β e) z k' (fun _ => k) = Geo.Tor.gw (c e) (𝟙 _) z k' (fun _ => k)) → LBIso A A' := by
  intro R _ _ I hI X hX Y β b hpb hβ A A' hA hA' c hc hcomp
  have hle : ∀ e (p : (LB.div A' A).ι), b e ⁻¹ᵁ (LB.div A' A).U p ≤
      (LB.div (A'.pull (b e)) (A.pull (b e))).U (fun _ => p.1, fun _ => p.2) :=
    fun e p x hx => ⟨Set.mem_iInter.2 fun _ => hx.1, Set.mem_iInter.2 fun _ => hx.2⟩
  let s : ∀ e (i : (LB.div A' A).ι), Γ((Y e).left, b e ⁻¹ᵁ (LB.div A' A).U i)ˣ :=
    fun e p => res (hle e p) ((c e).s (fun _ => p.1, fun _ => p.2))
  have hs : ∀ e (z : (Y e).left) (p : (LB.div A' A).ι), b e z ∈ (LB.div A' A).U p →
      gm (𝟙 _) z _ (s e p) = gw (c e) (𝟙 _) z p.1 (fun _ => p.2) :=
    fun e z p h => gm_res (𝟙 (Y e).left) z (hle e p) (by simpa using h) _
  have hg : ∀ e (z : (Y e).left) (p p' : (LB.div A' A).ι), b e z ∈ (LB.div A' A).U p →
      b e z ∈ (LB.div A' A).U p' →
      gm (b e) z _ ((LB.div A' A).g p p') =
        gm (b e) z _ (A'.g p.1 p'.1) * (gm (b e) z _ (A.g p.2 p'.2))⁻¹ := by
    intro e z p p' h h'
    have hm : b e z ∈ (LB.div A' A).U p ⊓ (LB.div A' A).U p' := ⟨h, h'⟩
    show gm (b e) z _ (res _ (A'.g p.1 p'.1) * (res _ (A.g p.2 p'.2))⁻¹) = _
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ _ _ hm _)
      ((map_inv _ _).trans (congrArg _ (gm_res _ _ _ hm _))))
  have hpg : ∀ e (z : (Y e).left) (k k' : A.ι), b e z ∈ A.U k → b e z ∈ A.U k' →
      gm (𝟙 (Y e).left) z _ ((A.pull (b e)).g (fun _ => k) (fun _ => k')) =
        gm (b e) z _ (A.g k k') := by
    intro e z k k' hk hk'
    have hp : (𝟙 (Y e).left) z ∈ (A.pull (b e)).U (fun _ => k) ⊓ (A.pull (b e)).U (fun _ => k') :=
      ⟨mem_pull.2 hk, mem_pull.2 hk'⟩
    show gm _ z _ (∏ _k : PUnit, (res _ (pullU (b e) _ (A.g k k'))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    exact (gm_res _ z _ hp _).trans ((gm_pull (𝟙 _) (b e) z (A.U k ⊓ A.U k') ⟨hk, hk'⟩ _).trans
      (by rw [Category.id_comp]))
  refine (GlobalTheory.T.exists_generator_algebraisation_reductions R I hI X hX Y β b hpb hβ (LB.div A' A) (LB.isLB_div hA' hA) s ?_ ?_ :
    ∃ t : LB.Gen (LB.div A' A), t.IsGen)
  · intro e z p p' h h'
    rw [hs e z p h, hs e z p' h', hg e z p p' h h']
    have := (isGen_iff (c e)).1 (hc e) _ (𝟙 _) z p.1 p'.1 (fun _ => p.2) (fun _ => p'.2) h.1 h'.1
      (mem_pull.2 h.2) (mem_pull.2 h'.2)
    rw [this, hpg e z p.2 p'.2 h.2 h'.2, Category.id_comp]
  · intro e z p h
    have h1 : b (e + 1) (β e z) = b e z := by rw [← hβ e]; rfl
    have hz : β e z ∈ b (e + 1) ⁻¹ᵁ (LB.div A' A).U p := show b (e + 1) (β e z) ∈ _ from h1 ▸ h
    rw [show gm (β e) z _ (s (e + 1) p) = gw (c (e + 1)) (β e) z p.1 (fun _ => p.2) from
      gm_res _ z (hle (e + 1) p) hz _, hcomp e z p.2 p.1 h.2 h.1, hs e z p h]

end GlobalTheory.FormalAlg
