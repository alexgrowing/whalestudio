import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RatTors
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsCoordPtFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

namespace GlobalTheory.Ex.Trait.LevelFour

theorem exists_image {C : Type} [Field C] {N N' : NumD C} (J : NumD.Iso N N') {k : ℕ} (p : N.QT k) :
    ∃ q : N'.QT k, q.1.1.toAdd = J.e p.1.1.toAdd ∧ J.Rel p.1.2 q.1.2 := by
  obtain ⟨h₁, h₂, h₃, -⟩ := NumD.hom_transport C C (RingHom.id C) N N' (TateInh.homOfIso J)
  obtain ⟨g, hg, -⟩ := h₁ p.1.2
  have hp : ∀ n : ℕ, J.Rel (p.1.2 ^ n) (g ^ n) := fun n => by
    induction n with
    | zero => rw [pow_zero, pow_zero]; exact J.rel_one
    | succ n ih => rw [pow_succ, pow_succ]; exact h₂ _ _ _ _ ih hg
  refine ⟨⟨(Multiplicative.ofAdd (J.e p.1.1.toAdd), g), ?_⟩, rfl, hg⟩
  have a := hp k
  rw [N.mem_QT.1 p.2] at a
  exact (h₁ _).unique a (h₃ _)

theorem ev_iso {C : Type} [NormedField C] {N N' : NumD C} (J : NumD.Iso N N') {m : ℕ} (hm : Odd m)
    {p : N.QT (m ^ 2)} {p' : N'.QT (m ^ 2)} (h₁ : p'.1.1.toAdd = J.e p.1.1.toAdd) (h₂ : J.Rel p.1.2 p'.1.2)
    {g : N.Gt} {g' : N'.Gt} (hg : J.Rel g g') :
    N'.ev m p' g' = (J.lam * J.h g.b ^ (m ^ 2) : Cˣ) * N.ev m p g := by
  have H := (NumD.hom_transport C C (RingHom.id C) N N' (TateInh.homOfIso J)).2.2.2.2 m hm p p' h₁ h₂
  rw [NumD.ev, NumD.ev, ← J.e.toEquiv.tsum_eq, ← tsum_mul_left]
  exact tsum_congr fun χ => (H χ).2 g g' hg

theorem labels_of_four_le : GlobalTheory.UT.LL → EVSt → BrGtSt → AllS fun {_} _ _ _ {_} {_} {_} {_} {_} _ {_} {_} _ _ {_} _ {_} _ _ A u r {o} M _ {_} ν' J => M.P.TorsionIso → Realises o A.arc A.be u r → ∀ n : ℕ, Odd n → 3 ≤ n → Labels A u r M ν' J (n ^ 2) → ∀ k, 4 ≤ k → Labels A u r M ν' J k := by
  intro hL hE hB E _ _ _ H D l c O _ β O' _ _ _ b a C _ _ _ _ _ _ A u r o M f N' ν' J hr _ hT hR n hn h3 hl k hk
    x p q' p' z hp e₁ e₂ hq hz
  have hn2 : 0 < n ^ 2 := pow_pos hn.pos 2
  have B := hB M.W M.P.D.toPre M.P.D.psi_even M.P.D.tau_bimult C N' ν'
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv M.cart (baseOver (Sp C)) (jFK (R := M.W) C) (Category.id_comp _).symm
  choose pt hpt using fun i : D.La => (existsUnique_twRel A.be u (r (n ^ 2)) (hr.pow hn2) (A.q (n ^ 2) i)).exists
  choose qt hq₁ hq₂ using fun i => exists_image J (pt i)
  choose pp hpp using fun i => (B.2.2.2.2 (n ^ 2)).2.1 (qt i)
  have hA : ∀ i, M.P.ToA C (n ^ 2) (pp i) (e (o.I.ev (n ^ 2) i)) := fun i =>
    hl i (pt i) (qt i) (pp i) _ (hpt i) (hq₁ i) (hq₂ i) (hpp i) (he _)
  obtain ⟨F, hF, -⟩ := hT C k (by omega)
  obtain ⟨y, hy⟩ := e.surjective (F p')
  have Q := hE M.W _ M.cdv rfl M.P.D M.P.A M.t.G M.t.semi M.P.U C M.ext N' ν' n hn D.La pp qt _ hA hpp
    k hk p' q' (F p') ((hF _ _).2 rfl) hq
  let τ : (baseOver (Sp C)).left ⟶ (TFK (R := M.W) C).left := 𝟙 (Sp C)
  have : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp C)))
  have hτ : τ ≫ (TFK (R := M.W) C).hom = (baseOver (Sp C)).hom ≫ jFK (R := M.W) C := rfl
  have ht : ∀ i, o.I.ev (n ^ 2) i ^ (n ^ 2) = 1 := fun i => (o.I.onto _ hn2 _).2 ⟨i, rfl⟩
  have Q₁ : IsCoordPt o.P n (T := baseOver (Sp C)) (o.I.ev (n ^ 2)) y fun i => fnOf (N'.ev n (qt i) q'.1.2) :=
    FullExtend.isCoordPt_move τ M.cart M.lb τ (𝟙 _) (Category.comp_id _) hτ (fun th h s => by
      obtain ⟨c, hc⟩ := h s
      have e := VVRank.pullM_id M.P.A.A M.P.A.isLB 1 (SecM.ofSec M.P.A.A th)
      exact ⟨c, fun j => (hc j).trans (congrArg (_ * ·) (congrArg (fun q => q.1 j) e).symm)⟩)
      (fun i => (Category.id_comp _).trans (he _)) ht (z := y)
      ((Category.id_comp _).trans ((congrArg (fun w => w.left) hy).symm.trans (he _))) Q
  have Q₂ := ((hR.2.2.2 n hn pt hpt).2.2 k (by omega) x p hp).2
  obtain ⟨-, s₂, -, s₄⟩ := CoordSep.coord_exists_unique_separate hL.1 C (Sp C) o.P (𝟙 _) n hn
    (Nat.cast_ne_zero.2 hn.pos.ne') D.La (o.I.ev (n ^ 2)) ht
  have Q₃ := (s₂ _ _ (fun i => N'.ev n (qt i) q'.1.2) Q₂).2
    ⟨J.lam * J.h p.1.2.b ^ (n ^ 2), funext fun i => ev_iso J hn (hq₁ i) (hq₂ i) e₂⟩
  obtain rfl := (s₄ h3 (fun w hw => (o.I.onto _ hn2 w).1 hw) _ _ _ Q₃ Q₁).1
  exact (hF _ _).2 ((Over.OverMorphism.ext (hz.trans (he _).symm)).trans hy)

end GlobalTheory.Ex.Trait.LevelFour
