import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.TeichmullerRootsUnity.RootsUnityPullback.MmPull

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.crystallineComparison.PinP

section
variable {O : Type} [CommRing O] (F : B.Fn O) {b₀ b₁ : Base} {h₀ : b₀.t = 1} {h₁ : b₁.t = 1} {κ₀ : O →+* b₀.R ⧸ b₀.I}
  {κ₁ κm : O →+* b₁.R ⧸ b₁.I} {Λ₀ Λ₁ : Type} [CommRing Λ₀] [CommRing Λ₁] {c₀ : Λ₀ →+* b₀.R} {c₁ : Λ₁ →+* b₁.R} {w : Λ₀ →+* Λ₁}

def IsMuG (wn : b₀.R →+* b₁.R) (e : ℕ) (m : CH.Mor (B.OM (F.cr b₀ h₀ κ₀) c₀) (B.OM (F.cr b₁ h₁ κ₁) c₁) w) : Prop :=
  ∃ η : ∀ T, (m.G.obj T).B ≃+* T.B, (∀ T (x : (m.G.obj T).B), (show T.B from m.τ T x) = η T x) ∧
    (∀ T, IsDPMorphism (m.G.obj T).δ T.δ (η T).toRingHom) ∧ (∀ T, (m.G.obj T).J.map (η T).toRingHom = T.J) ∧
    (∀ T w, η T ((m.G.obj T).i w) = T.i (wn w)) ∧
    ∀ T (h : (m.G.obj T).J ≤ T.J.comap (η T).toRingHom) (φ : T.B ⧸ T.J →+* T.B ⧸ T.J), (∀ x, φ x = x ^ e) →
      F.Pt.map (CommRingCat.ofHom (Ideal.quotientMap T.J (η T).toRingHom h)) (m.G.obj T).y.1.2 =
        F.Pt.map (CommRingCat.ofHom φ) T.y.1.2

theorem isMuG (wn : b₀.R →+* b₁.R) (e : ℕ) (m₁ : Mor (F.cr b₀ h₀ κ₀) (F.cr b₁ h₁ κm) wn)
    (m₂ : Mor (F.cr b₁ h₁ κm) (F.cr b₁ h₁ κ₁) (RingHom.id _)) (k₁ : ∀ a, wn (c₀ a) = c₁ (w a))
    (k₂ : ∀ a, RingHom.id _ (c₁ a) = c₁ (RingHom.id _ a))
    (p₁ : ∀ (B₀ : CommRingCat.{0}) (y : (F.ptK κm).obj B₀), (show (F.ptK κ₀).obj B₀ from m₁.pt.app B₀ y).1.2 = y.1.2)
    (p₂ : ∀ (B₀ : CommRingCat.{0}) (y : (F.ptK κ₁).obj B₀) (φ : B₀ →+* B₀), (∀ x, φ x = x ^ e) →
      (show (F.ptK κm).obj B₀ from m₂.pt.app B₀ y).1.2 = F.Pt.map (CommRingCat.ofHom φ) y.1.2) :
    IsMuG F wn e ((B.omMor m₁ w k₁).comp (σ'' := w) (B.omMor m₂ (RingHom.id _) k₂)) := by
  refine ⟨fun T => RingEquiv.refl T.B, fun _ _ => rfl, fun T => ⟨le_of_eq (Ideal.map_id _), fun _ _ => rfl⟩,
    fun T => Ideal.map_id _, fun _ _ => rfl, fun T h φ hφ => ?_⟩
  have e1 : Ideal.quotientMap T.J (RingEquiv.refl T.B).toRingHom h = RingHom.id _ :=
    Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)
  have e2 := (p₁ _ (m₂.pt.app _ T.y)).trans (p₂ _ T.y φ hφ)
  refine Eq.trans ?_ e2
  refine (congrArg (fun g => F.Pt.map (CommRingCat.ofHom g) _) e1).trans ?_
  exact congrFun (congrArg (fun t => (ConcreteCategory.hom t : _ → _)) (F.Pt.map_id (CommRingCat.of (T.B ⧸ T.J)))) _

end

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem isMu_mmG (r : Res l K) (M : Model l K) (n : ℕ) {N : ℕ} (hT : Pb.Mid.TeichmullerCongruence r N) :
    IsMu r M n N (mm r M n hT) :=
  isMuG (B.schFn M.p) (b₀ := Wc.bs l r.k n) (b₁ := B.bs l true n) (h₀ := rfl) (h₁ := rfl) (Pb.Mid.wn r n) (l ^ N) _
    (Pb.Mid.mIn r M n hT) (Pb.Mid.wn_mk r n) (fun _ => rfl) (fun _ _ => rfl) (fun B₀ y φ hφ =>
      congrArg (fun g => (B.schFn M.p).Pt.map (CommRingCat.ofHom g) y.1.2)
        (RingHom.ext fun x => (Pb.Mid.frbN_apply _ N x).trans (hφ x).symm))

end CrystallineSemistableComparison.crystallineComparison.PinP

end
