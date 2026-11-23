import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenRatio

variable {X : Scheme.{0}}

theorem comm_identity {M : Type} [CommGroup M] (B G G' Q Q' : M) :
    G' * G⁻¹ * B * (G * Q) * (G' * Q')⁻¹ = B * Q * Q'⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem gm_isGenOn {L : LB X} {W : X.Opens} {τ : ∀ m : L.ι, Γ(X, W ⊓ L.U m)ˣ} (hτ : IsGenOn L W τ)
    {x : X} {m n : L.ι} (hx : x ∈ W) (hm : x ∈ L.U m) (hn : x ∈ L.U n) :
    gm (𝟙 X) x _ (τ m) = gm (𝟙 X) x _ (L.g m n) * gm (𝟙 X) x _ (τ n) := by
  have hmem : x ∈ W ⊓ L.U m ⊓ L.U n := ⟨⟨hx, hm⟩, hn⟩
  have := congrArg (gm (𝟙 X) x _) (hτ m n)
  rwa [map_mul, gm_res _ x _ hmem, gm_res _ x _ hmem, gm_res _ x _ hmem] at this

def isoAt {L L' : LB X} (w : LB.Iso L L') (m' : L'.ι) (m : L.ι) : Γ(X, L'.U m' ⊓ L.U m)ˣ := w.s (m', m)

theorem isoAt_compat {L L' : LB X} {w : LB.Iso L L'} (hw : w.IsGen) (m n : L.ι) (m' n' : L'.ι) :
    res (inf_le_left : L'.U m' ⊓ L.U m ⊓ (L'.U n' ⊓ L.U n) ≤ L'.U m' ⊓ L.U m) (isoAt w m' m) =
      res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
        L'.U m' ⊓ L.U m ⊓ (L'.U n' ⊓ L.U n) ≤ L'.U m' ⊓ L'.U n') (L'.g m' n') *
      (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
        L'.U m' ⊓ L.U m ⊓ (L'.U n' ⊓ L.U n) ≤ L.U m ⊓ L.U n) (L.g m n))⁻¹ *
      res (inf_le_right : L'.U m' ⊓ L.U m ⊓ (L'.U n' ⊓ L.U n) ≤ L'.U n' ⊓ L.U n) (isoAt w n' n) :=
  hw (m', m) (n', n)

theorem gm_iso {L L' : LB X} {w : LB.Iso L L'} (hw : w.IsGen) {x : X} {m n : L.ι} {m' n' : L'.ι}
    (hm : x ∈ L.U m) (hn : x ∈ L.U n) (hm' : x ∈ L'.U m') (hn' : x ∈ L'.U n') :
    gm (𝟙 X) x _ (isoAt w m' m) =
      gm (𝟙 X) x _ (L'.g m' n') * (gm (𝟙 X) x _ (L.g m n))⁻¹ * gm (𝟙 X) x _ (isoAt w n' n) := by
  have hmem : x ∈ L'.U m' ⊓ L.U m ⊓ (L'.U n' ⊓ L.U n) := ⟨⟨hm', hm⟩, ⟨hn', hn⟩⟩
  have := congrArg (gm (𝟙 X) x _) (isoAt_compat hw m n m' n')
  rwa [map_mul, map_mul, map_inv, gm_res _ x _ hmem, gm_res _ x _ hmem, gm_res _ x _ hmem,
    gm_res _ x _ hmem] at this

def ratioLoc (L L' : LB X) (W : X.Opens) (w : LB.Iso L L') (τ : ∀ m : L.ι, Γ(X, W ⊓ L.U m)ˣ)
    (τ' : ∀ m : L'.ι, Γ(X, W ⊓ L'.U m)ˣ) (m' : L'.ι) (m : L.ι) : Γ(X, W ⊓ (L'.U m' ⊓ L.U m))ˣ :=
  res (inf_le_right : W ⊓ (L'.U m' ⊓ L.U m) ≤ L'.U m' ⊓ L.U m) (isoAt w m' m) *
    res (inf_le_inf_left W inf_le_right : W ⊓ (L'.U m' ⊓ L.U m) ≤ W ⊓ L.U m) (τ m) *
    (res (inf_le_inf_left W inf_le_left : W ⊓ (L'.U m' ⊓ L.U m) ≤ W ⊓ L'.U m') (τ' m'))⁻¹

theorem gm_ratioLoc (L L' : LB X) (W : X.Opens) (w : LB.Iso L L') (τ : ∀ m : L.ι, Γ(X, W ⊓ L.U m)ˣ)
    (τ' : ∀ m : L'.ι, Γ(X, W ⊓ L'.U m)ˣ) (m : L.ι) (m' : L'.ι) {x : X} (hx : x ∈ W ⊓ (L'.U m' ⊓ L.U m)) :
    gm (𝟙 X) x _ (ratioLoc L L' W w τ τ' m' m) =
      gm (𝟙 X) x _ (isoAt w m' m) * gm (𝟙 X) x _ (τ m) * (gm (𝟙 X) x _ (τ' m'))⁻¹ := by
  rw [ratioLoc, map_mul, map_mul, map_inv, gm_res _ x _ hx, gm_res _ x _ hx, gm_res _ x _ hx]

theorem exists_unique_ratio : ∀ (X : Scheme.{0}) (L L' : LB X) (W : X.Opens) (w : LB.Iso L L') (τ : ∀ m : L.ι, Γ(X, W ⊓ L.U m)ˣ) (τ' : ∀ m : L'.ι, Γ(X, W ⊓ L'.U m)ˣ), L.IsLB → L'.IsLB → w.IsGen → IsGenOn L W τ → IsGenOn L' W τ' → ∃! t : Γ(X, W)ˣ, ∀ (m : L.ι) (m' : L'.ι), res (inf_le_left : W ⊓ (L'.U m' ⊓ L.U m) ≤ W) t * res (inf_le_inf_left W inf_le_left : W ⊓ (L'.U m' ⊓ L.U m) ≤ W ⊓ L'.U m') (τ' m') = res (inf_le_right : W ⊓ (L'.U m' ⊓ L.U m) ≤ L'.U m' ⊓ L.U m) (w.s (m', m)) * res (inf_le_inf_left W inf_le_right : W ⊓ (L'.U m' ⊓ L.U m) ≤ W ⊓ L.U m) (τ m) := by
  intro X L L' W w τ τ' hL hL' hw hτ hτ'
  have hc : W ≤ ⨆ p : L'.ι × L.ι, W ⊓ (L'.U p.1 ⊓ L.U p.2) := by
    intro x hx
    obtain ⟨i, hi⟩ := exists_chart hL x
    obtain ⟨i', hi'⟩ := exists_chart hL' x
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i', i), hx, hi', hi⟩
  have hagree : ∀ (p q : L'.ι × L.ι), ∀ x ∈ (W ⊓ (L'.U p.1 ⊓ L.U p.2)) ⊓ (W ⊓ (L'.U q.1 ⊓ L.U q.2)),
      gm (𝟙 X) x _ (ratioLoc L L' W w τ τ' p.1 p.2) = gm (𝟙 X) x _ (ratioLoc L L' W w τ τ' q.1 q.2) := by
    rintro ⟨m', m⟩ ⟨n', n⟩ x ⟨⟨hx, hm', hm⟩, ⟨-, hn', hn⟩⟩
    rw [gm_ratioLoc L L' W w τ τ' m m' ⟨hx, hm', hm⟩, gm_ratioLoc L L' W w τ τ' n n' ⟨hx, hn', hn⟩,
      gm_iso hw hm hn hm' hn', gm_isGenOn hτ hx hm hn, gm_isGenOn hτ' hx hm' hn']
    exact comm_identity _ _ _ _ _
  obtain ⟨t, ht⟩ := glue_unit W (fun p : L'.ι × L.ι ↦ W ⊓ (L'.U p.1 ⊓ L.U p.2)) (fun p ↦ inf_le_left) hc
    (fun p ↦ ratioLoc L L' W w τ τ' p.1 p.2) hagree
  refine ⟨t, fun m m' ↦ ?_, fun t' ht' ↦ ?_⟩
  · rw [ht (m', m)]
    exact inv_mul_cancel_right _ _
  · apply unit_ext
    intro x hx
    obtain ⟨m, hm⟩ := exists_chart hL x
    obtain ⟨m', hm'⟩ := exists_chart hL' x
    have hmem : x ∈ W ⊓ (L'.U m' ⊓ L.U m) := ⟨hx, hm', hm⟩
    have e0 : res (inf_le_left : W ⊓ (L'.U m' ⊓ L.U m) ≤ W) t' *
        res (inf_le_inf_left W inf_le_left : W ⊓ (L'.U m' ⊓ L.U m) ≤ W ⊓ L'.U m') (τ' m') =
        res (inf_le_right : W ⊓ (L'.U m' ⊓ L.U m) ≤ L'.U m' ⊓ L.U m) (isoAt w m' m) *
        res (inf_le_inf_left W inf_le_right : W ⊓ (L'.U m' ⊓ L.U m) ≤ W ⊓ L.U m) (τ m) := ht' m m'
    have e1 := congrArg (gm (𝟙 X) x _) e0
    rw [map_mul, map_mul, gm_res _ x _ hmem, gm_res _ x _ hmem, gm_res _ x _ hmem, gm_res _ x _ hmem] at e1
    have e2 := congrArg (gm (𝟙 X) x _) (ht (m', m))
    dsimp only at e2
    rw [gm_res _ x _ hmem, gm_ratioLoc L L' W w τ τ' m m' hmem] at e2
    rw [e2]
    exact eq_mul_inv_of_mul_eq e1

end GlobalTheory.GenRatio
