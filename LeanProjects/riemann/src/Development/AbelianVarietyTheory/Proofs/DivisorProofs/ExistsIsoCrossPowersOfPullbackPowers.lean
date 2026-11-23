import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ProjectiveNotIsUnit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section
namespace GlobalTheory.FormalAlg.CrossIso

variable {X Y Z : Scheme.{0}}

theorem gm_pw_g (L : LB X) (t : ℤ) (f : Y ⟶ X) (y : Y) (i j : L.ι) :
    gm f y ((GlobalTheory.AbLaw.pw L t).U i ⊓ (GlobalTheory.AbLaw.pw L t).U j) ((GlobalTheory.AbLaw.pw L t).g i j) =
      gm f y (L.U i ⊓ L.U j) (L.g i j) ^ t :=
  map_zpow (gm f y (L.U i ⊓ L.U j)) (L.g i j) t

theorem gm_pull_g (L : LB X) (F : Y ⟶ X) (f : Z ⟶ Y) (z : Z) (J J' : PUnit → L.ι)
    (hj : F (f z) ∈ L.U (J PUnit.unit)) (hj' : F (f z) ∈ L.U (J' PUnit.unit)) :
    gm f z ((L.pull F).U J ⊓ (L.pull F).U J') ((L.pull F).g J J') =
      gm (f ≫ F) z _ (L.g (J PUnit.unit) (J' PUnit.unit)) := by
  have hp : f z ∈ (L.pull F).U J ⊓ (L.pull F).U J' := ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
  show gm f z _ (∏ _k : PUnit, (res _ (pullU F _ (L.g (J PUnit.unit) (J' PUnit.unit)))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res f z _ hp _).trans
    (gm_pull f F z (L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit)) ⟨hj, hj'⟩ _)

theorem gw_chart {b : Y ⟶ X} {A : LB X} {N : LB Y} {p : ℤ} (w : LB.Iso (GlobalTheory.AbLaw.pw N p) (A.pull b))
    (hw : w.IsGen) (r : Z ⟶ Y) (z : Z) (k k' : A.ι) (l l' : N.ι) (hk : b (r z) ∈ A.U k) (hk' : b (r z) ∈ A.U k')
    (hl : r z ∈ N.U l) (hl' : r z ∈ N.U l') :
    gw w r z k l = gm (r ≫ b) z _ (A.g k k') * (gm r z _ (N.g l l') ^ p)⁻¹ * gw w r z k' l' := by
  have := (isGen_iff w).1 hw Z r z k k' l l' hk hk' hl hl'
  rw [gm_pw_g] at this
  exact this

theorem cross_alg {G : Type} [CommGroup G] (p q : ℤ) (a a' n u u' : G) :
    (a' * (n ^ q)⁻¹ * u') ^ p * ((a * (n ^ p)⁻¹ * u) ^ q)⁻¹ = a' ^ p * (a ^ q)⁻¹ * (u' ^ p * (u ^ q)⁻¹) := by
  simp only [mul_zpow, inv_zpow, ← zpow_mul, mul_comm q p, mul_inv, inv_inv]
  generalize n ^ (p * q) = m
  generalize a' ^ p = A'
  generalize a ^ q = A
  generalize u' ^ p = U'
  generalize u ^ q = U
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem cross_chart {b : Y ⟶ X} {A A' : LB X} {N : LB Y} {p q : ℤ} (w : LB.Iso (GlobalTheory.AbLaw.pw N p) (A.pull b))
    (w' : LB.Iso (GlobalTheory.AbLaw.pw N q) (A'.pull b)) (hw : w.IsGen) (hw' : w'.IsGen) (r : Z ⟶ Y) (z : Z)
    (k₁ k₂ : A.ι) (j₁ j₂ : A'.ι) (l₁ l₂ : N.ι) (hk₁ : b (r z) ∈ A.U k₁) (hk₂ : b (r z) ∈ A.U k₂)
    (hj₁ : b (r z) ∈ A'.U j₁) (hj₂ : b (r z) ∈ A'.U j₂) (hl₁ : r z ∈ N.U l₁) (hl₂ : r z ∈ N.U l₂) :
    gw w' r z j₁ l₁ ^ p * (gw w r z k₁ l₁ ^ q)⁻¹ =
      gm (r ≫ b) z _ (A'.g j₁ j₂) ^ p * (gm (r ≫ b) z _ (A.g k₁ k₂) ^ q)⁻¹ *
        (gw w' r z j₂ l₂ ^ p * (gw w r z k₂ l₂ ^ q)⁻¹) := by
  rw [gw_chart w hw r z k₁ k₂ l₁ l₂ hk₁ hk₂ hl₁ hl₂, gw_chart w' hw' r z j₁ j₂ l₁ l₂ hj₁ hj₂ hl₁ hl₂]
  exact cross_alg _ _ _ _ _ _ _

end GlobalTheory.FormalAlg.CrossIso

namespace GlobalTheory.FormalAlg
open CrossIso

theorem exists_crossIso : ∀ (X Y : Scheme.{0}) (b : Y ⟶ X) (A A' : LB X) (N : LB Y) (p q : ℤ) (w : LB.Iso (GlobalTheory.AbLaw.pw N p) (A.pull b)) (w' : LB.Iso (GlobalTheory.AbLaw.pw N q) (A'.pull b)), A.IsLB → A'.IsLB → N.IsLB → w.IsGen → w'.IsGen → ∃ c : LB.Iso ((GlobalTheory.AbLaw.pw A q).pull b) ((GlobalTheory.AbLaw.pw A' p).pull b), c.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (k : A.ι) (k' : A'.ι) (l : N.ι), b (r z) ∈ A.U k → b (r z) ∈ A'.U k' → r z ∈ N.U l → Geo.Tor.gw c r z k' (fun _ => k) = Geo.Tor.gw w' r z k' l ^ p * (Geo.Tor.gw w r z k l ^ q)⁻¹ := by
  intro X Y b A A' N p q w w' hA hA' hN hw hw'
  have glue : ∀ (j : A'.ι) (k : A.ι), ∃ s : Γ(Y, ((GlobalTheory.AbLaw.pw A' p).pull b).U (fun _ => j) ⊓
      ((GlobalTheory.AbLaw.pw A q).pull b).U (fun _ => k))ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (l : N.ι), b (r z) ∈ A.U k → b (r z) ∈ A'.U j → r z ∈ N.U l →
        gm r z _ s = gw w' r z j l ^ p * (gw w r z k l ^ q)⁻¹ := by
    intro j k
    obtain ⟨W, hW⟩ : ∃ W : N.ι → Y.Opens, ∀ l x, x ∈ W l ↔ b x ∈ A.U k ∧ b x ∈ A'.U j ∧ x ∈ N.U l :=
      ⟨fun l => b ⁻¹ᵁ A.U k ⊓ (b ⁻¹ᵁ A'.U j ⊓ N.U l), fun _ _ => Iff.rfl⟩
    have l₀ : ∀ l, W l ≤ ((GlobalTheory.AbLaw.pw A' p).pull b).U (fun _ => j) ⊓
        ((GlobalTheory.AbLaw.pw A q).pull b).U (fun _ => k) := fun l x hx =>
      ⟨mem_pull.2 ((hW l x).1 hx).2.1, mem_pull.2 ((hW l x).1 hx).1⟩
    have l₁ : ∀ l, W l ≤ (A'.pull b).U (fun _ => j) ⊓ (GlobalTheory.AbLaw.pw N q).U l := fun l x hx =>
      ⟨mem_pull.2 ((hW l x).1 hx).2.1, ((hW l x).1 hx).2.2⟩
    have l₂ : ∀ l, W l ≤ (A.pull b).U (fun _ => k) ⊓ (GlobalTheory.AbLaw.pw N p).U l := fun l x hx =>
      ⟨mem_pull.2 ((hW l x).1 hx).1, ((hW l x).1 hx).2.2⟩
    obtain ⟨u, hu⟩ : ∃ u : ∀ l, Γ(Y, W l)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (l : N.ι), r z ∈ W l →
        gm r z (W l) (u l) = gw w' r z j l ^ p * (gw w r z k l ^ q)⁻¹ :=
      ⟨fun l => res (l₁ l) (w'.s (fun _ => j, l)) ^ p * (res (l₂ l) (w.s (fun _ => k, l)) ^ q)⁻¹,
        fun Z r z l hy => (map_mul _ _ _).trans (congrArg₂ (· * ·)
          ((map_zpow _ _ _).trans (congrArg (· ^ p) (gm_res r z (l₁ l) hy _)))
          ((map_inv _ _).trans (congrArg (·⁻¹)
            ((map_zpow _ _ _).trans (congrArg (· ^ q) (gm_res r z (l₂ l) hy _))))))⟩
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
        obtain ⟨l, hl⟩ := exists_chart hN x
        exact Opens.mem_iSup.2 ⟨l, (hW l x).2 ⟨mem_pull.1 hx.2, mem_pull.1 hx.1, hl⟩⟩) u (fun l l' x hx => by
        have h₁ := (hW l x).1 hx.1
        have h₂ := (hW l' x).1 hx.2
        have e := cross_chart w w' hw hw' (𝟙 Y) x k k j j l l' h₁.1 h₁.1 h₁.2.1 h₁.2.1 h₁.2.2 h₂.2.2
        rw [gm_self hA (𝟙 Y ≫ b) x h₁.1, gm_self hA' (𝟙 Y ≫ b) x h₁.2.1, one_zpow, one_zpow, inv_one, one_mul,
          one_mul] at e
        exact (hu _ (𝟙 Y) x l hx.1).trans (e.trans (hu _ (𝟙 Y) x l' hx.2).symm))
    refine ⟨s, fun Z r z l hk hj hl => ?_⟩
    have hy := (hW l (r z)).2 ⟨hk, hj, hl⟩
    exact (gm_res r z (l₀ l) hy s).symm.trans ((congrArg (gm r z (W l)) (hs l)).trans (hu Z r z l hy))
  choose s hs using glue
  let c : LB.Iso ((GlobalTheory.AbLaw.pw A q).pull b) ((GlobalTheory.AbLaw.pw A' p).pull b) :=
    ⟨fun P => s (P.1 PUnit.unit) (P.2 PUnit.unit)⟩
  have hc : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (K : PUnit → A.ι) (j : A'.ι) (l : N.ι),
      b (r z) ∈ A.U (K PUnit.unit) → b (r z) ∈ A'.U j → r z ∈ N.U l →
      gw c r z j K = gw w' r z j l ^ p * (gw w r z (K PUnit.unit) l ^ q)⁻¹ :=
    fun Z r z K j l hk hj hl => hs j (K PUnit.unit) Z r z l hk hj hl
  refine ⟨c, (isGen_iff c).2 ?_, fun Z r z k j l hk hj hl => hc Z r z (fun _ => k) j l hk hj hl⟩
  intro Z r z j j' K K' hj hj' hK hK'
  obtain ⟨l, hl⟩ := exists_chart hN (r z)
  have hk := mem_pull.1 hK
  have hk' := mem_pull.1 hK'
  have e := cross_chart w w' hw hw' r z (K PUnit.unit) (K' PUnit.unit) j j' l l hk hk' hj hj' hl hl
  refine (hc Z r z K j l hk hj hl).trans (e.trans ?_)
  refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (gm_pw_g A' p _ z j j').symm (congrArg (·⁻¹) ?_))
    (hc Z r z K' j' l hk' hj' hl).symm
  exact ((gm_pull_g (GlobalTheory.AbLaw.pw A q) b r z K K' hk hk').trans (gm_pw_g A q _ z _ _)).symm

end GlobalTheory.FormalAlg
