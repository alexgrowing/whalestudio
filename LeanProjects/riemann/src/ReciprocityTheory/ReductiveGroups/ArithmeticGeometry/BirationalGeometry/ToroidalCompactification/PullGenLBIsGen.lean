import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OverExtOfPoints
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

def isoInv {X : Scheme.{0}} {L M : LB X} (t : LB.Iso L M) : LB.Iso M L :=
  ⟨fun p => (res (fun _ hx => ⟨hx.2, hx.1⟩ : L.U p.1 ⊓ M.U p.2 ≤ M.U p.2 ⊓ L.U p.1) (t.s (p.2, p.1)))⁻¹⟩

private theorem res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V)
    (x : Γ(X, U)ˣ) : res h2 (res h1 x) = res (h2.trans h1) x := by
  ext
  change (X.presheaf.map (homOfLE h1).op ≫ X.presheaf.map (homOfLE h2).op).hom (x : Γ(X, U)) = _
  rw [← Functor.map_comp]
  rfl

private theorem inv_of_eq_mul_inv_mul {G : Type*} [CommGroup G] {a b l m : G} (e : a = m * l⁻¹ * b) :
    a⁻¹ = l * m⁻¹ * b⁻¹ := by
  subst e
  rw [mul_inv_rev, mul_inv_rev, inv_inv, mul_comm]

theorem isoInv_isGen {X : Scheme.{0}} {L M : LB X} {t : LB.Iso L M} (ht : t.IsGen) : (isoInv t).IsGen := by
  unfold LB.Gen.IsGen at ht ⊢
  rintro (p : L.ι × M.ι) (q : L.ι × M.ι)
  have key : ∀ (a : Γ(X, M.U p.2 ⊓ L.U p.1)ˣ) (b : Γ(X, M.U q.2 ⊓ L.U q.1)ˣ),
      res (inf_le_left : M.U p.2 ⊓ L.U p.1 ⊓ (M.U q.2 ⊓ L.U q.1) ≤ M.U p.2 ⊓ L.U p.1) a =
        res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
            M.U p.2 ⊓ L.U p.1 ⊓ (M.U q.2 ⊓ L.U q.1) ≤ M.U p.2 ⊓ M.U q.2) (M.g p.2 q.2) *
          (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
            M.U p.2 ⊓ L.U p.1 ⊓ (M.U q.2 ⊓ L.U q.1) ≤ L.U p.1 ⊓ L.U q.1) (L.g p.1 q.1))⁻¹ *
        res (inf_le_right : M.U p.2 ⊓ L.U p.1 ⊓ (M.U q.2 ⊓ L.U q.1) ≤ M.U q.2 ⊓ L.U q.1) b →
      res (inf_le_left : L.U p.1 ⊓ M.U p.2 ⊓ (L.U q.1 ⊓ M.U q.2) ≤ L.U p.1 ⊓ M.U p.2)
          (res (inf_comm (L.U p.1) (M.U p.2)).le a)⁻¹ =
        res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
            L.U p.1 ⊓ M.U p.2 ⊓ (L.U q.1 ⊓ M.U q.2) ≤ L.U p.1 ⊓ L.U q.1) (L.g p.1 q.1) *
          (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
            L.U p.1 ⊓ M.U p.2 ⊓ (L.U q.1 ⊓ M.U q.2) ≤ M.U p.2 ⊓ M.U q.2) (M.g p.2 q.2))⁻¹ *
        res (inf_le_right : L.U p.1 ⊓ M.U p.2 ⊓ (L.U q.1 ⊓ M.U q.2) ≤ L.U q.1 ⊓ M.U q.2)
          (res (inf_comm (L.U q.1) (M.U q.2)).le b)⁻¹ := by
    intro a b e
    have hW : L.U p.1 ⊓ M.U p.2 ⊓ (L.U q.1 ⊓ M.U q.2) ≤ M.U p.2 ⊓ L.U p.1 ⊓ (M.U q.2 ⊓ L.U q.1) :=
      fun _ hx => ⟨⟨hx.1.2, hx.1.1⟩, ⟨hx.2.2, hx.2.1⟩⟩
    have e' := congrArg (res hW) e
    simp only [map_mul, map_inv, res_res_lemma] at e' ⊢
    exact inv_of_eq_mul_inv_mul e'
  exact key _ _ (ht (p.2, p.1) (q.2, q.1))

def pullGenLB {X Y : Scheme.{0}} {L : LB X} (c : LB.Gen L) (h : Y ⟶ X) : LB.Gen (L.pull h) :=
  ⟨fun j => res (fun _ hy => Set.mem_iInter.1 hy PUnit.unit : (L.pull h).U j ≤ h ⁻¹ᵁ L.U (j PUnit.unit))
    (pullU h _ (c.s (j PUnit.unit)))⟩

private theorem pullU_res_lemma_2 {X Y : Scheme.{0}} (f : Y ⟶ X) {U V : X.Opens} (h : V ≤ U)
    (x : Γ(X, U)ˣ) : pullU f V (res h x) = res ((TopologicalSpace.Opens.map f.base).monotone h : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U) (pullU f U x) := by
  ext
  change (X.presheaf.map (homOfLE h).op ≫ f.app V).hom (x : Γ(X, U)) =
    (f.app U ≫ Y.presheaf.map (homOfLE ((TopologicalSpace.Opens.map f.base).monotone h : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U)).op).hom (x : Γ(X, U))
  rw [f.naturality]
  rfl

theorem pullGenLB_isGen {X Y : Scheme.{0}} {L : LB X} {c : LB.Gen L} (hc : c.IsGen) (h : Y ⟶ X) :
    (pullGenLB c h).IsGen := by
  unfold LB.Gen.IsGen at hc ⊢
  rintro (j : PUnit → L.ι) (j' : PUnit → L.ι)
  have key : ∀ (a : Γ(X, L.U (j PUnit.unit))ˣ) (b : Γ(X, L.U (j' PUnit.unit))ˣ),
      res (inf_le_left : L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit) ≤ L.U (j PUnit.unit)) a =
        L.g (j PUnit.unit) (j' PUnit.unit) *
          res (inf_le_right : L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit) ≤ L.U (j' PUnit.unit)) b →
      res (inf_le_left : LB.wchart L (fun _ : PUnit => h) j ⊓ LB.wchart L (fun _ : PUnit => h) j' ≤ LB.wchart L (fun _ : PUnit => h) j)
          (res (LB.wchart_le L (fun _ : PUnit => h) j PUnit.unit : LB.wchart L (fun _ : PUnit => h) j ≤ h ⁻¹ᵁ L.U (j PUnit.unit))
            (pullU h (L.U (j PUnit.unit)) a)) =
        (∏ k : PUnit, (res (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : PUnit => h) j k))
            (inf_le_right.trans (LB.wchart_le L (fun _ : PUnit => h) j' k)) :
              LB.wchart L (fun _ : PUnit => h) j ⊓ LB.wchart L (fun _ : PUnit => h) j' ≤ h ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)))
            (pullU h (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)))) ^ (1 : ℤ)) *
        res (inf_le_right : LB.wchart L (fun _ : PUnit => h) j ⊓ LB.wchart L (fun _ : PUnit => h) j' ≤ LB.wchart L (fun _ : PUnit => h) j')
          (res (LB.wchart_le L (fun _ : PUnit => h) j' PUnit.unit : LB.wchart L (fun _ : PUnit => h) j' ≤ h ⁻¹ᵁ L.U (j' PUnit.unit))
            (pullU h (L.U (j' PUnit.unit)) b)) := by
    intro a b e
    have hW : LB.wchart L (fun _ : PUnit => h) j ⊓ LB.wchart L (fun _ : PUnit => h) j' ≤ h ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)) :=
      fun _ hx => ⟨LB.wchart_le L (fun _ : PUnit => h) j PUnit.unit hx.1,
        LB.wchart_le L (fun _ : PUnit => h) j' PUnit.unit hx.2⟩
    have e' := congrArg (fun x => res hW (pullU h (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)) x)) e
    simp only [map_mul, pullU_res_lemma_2, res_res_lemma] at e'
    simp only [res_res_lemma, Fintype.prod_unique, zpow_one]
    exact e'
  exact key _ _ (hc (j PUnit.unit) (j' PUnit.unit))

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
