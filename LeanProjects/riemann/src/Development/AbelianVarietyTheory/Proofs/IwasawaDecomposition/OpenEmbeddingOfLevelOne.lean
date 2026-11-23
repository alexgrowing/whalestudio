import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeDescentSmoothDimension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPAdicArcBase
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.DomGrpDescent

theorem descends_of_dominates_of_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (s : Sys Xo) (l : Level H) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (c : Coeff l) (Z : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), l.A = 1 → DomAll s hg Z → (∃ (XK : Scheme.{0}) (sK : XK ⟶ Sp (KA l)) (jK : (Xo l).X ⟶ XK) (e : pullback Z.s (spMap (algebraMap (𝓞 c.F) c.F)) ⟶ XK), IsOpenImmersion jK ∧ jK ≫ sK = (Xo l).s ∧ IsPullback e (pullback.snd _ _) sK (spMap (IntermediateField.inclusion c.le).toRingHom) ∧ Z.jQ ≫ e = pullback.fst _ _ ≫ jK ∧ ∀ (T : Scheme.{0}) [T.IsSeparated] (g : pullback Z.s (spMap (algebraMap (𝓞 c.F) c.F)) ⟶ T) (g₀ : (Xo l).X ⟶ T), Z.jQ ≫ g = pullback.fst _ _ ≫ g₀ → ∃ h : XK ⟶ T, e ≫ h = g ∧ jK ≫ h = g₀) → Z.Descends := by
  intro E _ _ _ H D Xo s l hg c Z hA hdom hX
  obtain ⟨XK, sK, jK, e, hjK, hsK, he, hje, huniv⟩ := hX
  obtain ⟨W, hW⟩ := GlobalTheory.ArcBaseFactor.exists_place 2 Nat.prime_two
  have hS : ∀ x : 𝓞 c.F, algebraMap (𝓞 c.F) c.F x ∈ c.V W := fun x =>
    GlobalTheory.ArcBaseFactor.ringOfIntegers_mem c.F.val.toRingHom W x
  let b : 𝓞 c.F →+* c.V W := RingHom.codRestrict (algebraMap (𝓞 c.F) c.F) (c.V W) hS
  have hb : ∀ x, ((b x : c.V W) : c.F) = (x : c.F) := fun x => rfl
  obtain ⟨f, t, m₁, m₂, hf, hfj, hfφ⟩ := hdom 2 W Nat.prime_two hW b hb
  obtain ⟨XK₀, sK₀, GK₀, iK₀, jK₀, φK₀, e₀, GQ₀, iQ₀, φ₁₀, φ₂₀, ψ₀, -, -, hK₀, he₀, hje₀, hQ₀, hQK₀, hψ₁₀, hψh₀,
    hψ₂₀⟩ := ((s.clauses 2 W Nat.prime_two hW).1.1 ⟨l, c, hg 2 Nat.prime_two⟩).2.1 hA
  have hsp : spMap (algebraMap (𝓞 c.F) c.F) = spMap (c.V W).subtype ≫ spMap b := by
    have e1 : algebraMap (𝓞 c.F) c.F = (c.V W).subtype.comp b := RingHom.ext fun x => rfl
    rw [e1]; show Spec.map _ = Spec.map _ ≫ Spec.map _; rw [← Spec.map_comp]; rfl
  let a : pullback Z.s (spMap (algebraMap (𝓞 c.F) c.F)) ⟶ pullback Z.s (spMap b) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap (c.V W).subtype)
      (pullback.condition.trans (by rw [Category.assoc, ← hsp]))
  have ha₁ : a ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have ha₂ : a ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (c.V W).subtype := pullback.lift_snd _ _ _
  let k : pullback Z.s (spMap (algebraMap (𝓞 c.F) c.F)) ⟶
      pullback (s.Y 2 W Nat.prime_two hW ⟨l, c, hg 2 Nat.prime_two⟩).s (spMap (c.V W).subtype) :=
    pullback.lift (a ≫ f) (pullback.snd _ _) (by rw [Category.assoc, hf, ha₂])
  have hk₁ : k ≫ pullback.fst _ _ = a ≫ f := pullback.lift_fst _ _ _
  have hk₂ : k ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hjk : Z.jQ ≫ k = (s.Y 2 W Nat.prime_two hW ⟨l, c, hg 2 Nat.prime_two⟩).jQ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hk₁, ← Category.assoc]
      exact hfj _ (by rw [Category.assoc, ha₁]; rfl)
    · rw [Category.assoc, hk₂, Z.jQ_over, Model.jQ_over]
  have hg' : Z.jQ ≫ k ≫ e₀ = pullback.fst _ _ ≫ jK₀ := by rw [← Category.assoc, hjk, hje₀]
  have hYp : IsProper (s.Y 2 W Nat.prime_two hW ⟨l, c, hg 2 Nat.prime_two⟩).s := by
    obtain ⟨N, i, hi, e'⟩ := (s.Y 2 W Nat.prime_two hW ⟨l, c, hg 2 Nat.prime_two⟩).proj
    have := isProper_str (c.V W) N
    rw [← e']; infer_instance
  have hsK₀ : IsSeparated sK₀ := GlobalTheory.FieldDescentAb.isSeparated_of_isPullback he₀ (GlobalTheory.FieldDescentAb.fpqc_spMap _)
  haveI : XK₀.IsSeparated := ⟨by rw [← terminal.comp_from sK₀]; infer_instance⟩
  obtain ⟨h, heh, hjh⟩ := huniv XK₀ (k ≫ e₀) jK₀ hg'
  have gK := isGrpPullback_pullback GK₀ h
  let φK := gK.1.lift φK₀ ((Xo l).univ.t.G.hom ≫ jK) (by rw [hK₀.1.w, ← hjh, Category.assoc])
  have a₁ : φK ≫ _ = φK₀ := gK.1.lift_fst _ _ _
  have a₂ : φK ≫ _ = (Xo l).univ.t.G.hom ≫ jK := gK.1.lift_snd _ _ _
  have hKK := gK.cancel (by rw [a₁, hjh]; exact hK₀) a₂
  have gA := isGrpPullback_pullback t.G a
  have hQ := gA.comp m₁.cart
  rw [ha₁] at hQ
  let ψ := hQ.1.lift Z.m.φ (Z.oF.t.G.hom ≫ Z.jQ) (by rw [Z.m.cart.1.w, Category.assoc])
  have c₁ : ψ ≫ _ = Z.m.φ := hQ.1.lift_fst _ _ _
  have c₂ : ψ ≫ _ = Z.oF.t.G.hom ≫ Z.jQ := hQ.1.lift_snd _ _ _

  have hχw : (pullback.fst t.G.hom a ≫ m₂.φ) ≫ (s.Y 2 W Nat.prime_two hW ⟨l, c, hg 2 Nat.prime_two⟩).t.G.hom =
      (((Over.pullback a).obj t.G).hom ≫ k) ≫ pullback.fst _ _ := by
    rw [Category.assoc, m₂.cart.1.w, Category.assoc, hk₁, ← Category.assoc, pullback.condition, Category.assoc]
    rfl
  let χ := hQ₀.1.lift (pullback.fst t.G.hom a ≫ m₂.φ) (((Over.pullback a).obj t.G).hom ≫ k) hχw
  have hχ₁ : χ ≫ φ₁₀ = pullback.fst t.G.hom a ≫ m₂.φ := hQ₀.1.lift_fst _ _ _
  have hχ₂ : χ ≫ GQ₀.hom = ((Over.pullback a).obj t.G).hom ≫ k := hQ₀.1.lift_snd _ _ _
  have nQ : IsGrpPullback ((Over.pullback a).obj t.G) (s.Y 2 W Nat.prime_two hW ⟨l, c, hg 2 Nat.prime_two⟩).t.G
      (k ≫ pullback.fst _ _) (χ ≫ φ₁₀) := by
    rw [hχ₁, hk₁]; exact gA.comp m₂.cart
  have hQQ₀ := hQ₀.cancel nQ hχ₂
  have hQK := hQQ₀.comp hQK₀
  let φ₂ := gK.1.lift (χ ≫ φ₂₀) (((Over.pullback a).obj t.G).hom ≫ e) (by rw [hQK.1.w, ← heh, Category.assoc])
  have b₁ : φ₂ ≫ _ = χ ≫ φ₂₀ := gK.1.lift_fst _ _ _
  have b₂ : φ₂ ≫ _ = ((Over.pullback a).obj t.G).hom ≫ e := gK.1.lift_snd _ _ _
  have nK : IsGrpPullback ((Over.pullback a).obj t.G) GK₀ (e ≫ h) (φ₂ ≫ pullback.fst GK₀.hom h) := by
    rw [b₁, heh]; exact hQK
  have hQK' := gK.cancel nK b₂
  let g₂ := (s.Y 2 W Nat.prime_two hW ⟨l, c, hg 2 Nat.prime_two⟩).m0.toSABMap.cart.1.lift Z.m0.toSABMap.φ
    Z.oF.t.G.hom Z.m0.toSABMap.cart.1.w
  have d₁ : g₂ ≫ _ = Z.m0.toSABMap.φ := IsPullback.lift_fst _ _ _ _
  have d₂ : g₂ ≫ _ = Z.oF.t.G.hom := IsPullback.lift_snd _ _ _ _
  let gg := m₁.cart.1.lift Z.m.φ (Z.oF.t.G.hom ≫ Z.jQ ≫ a)
    (by rw [Z.m.cart.1.w, Category.assoc, Category.assoc, ha₁])
  have f₁ : gg ≫ m₁.φ = Z.m.φ := m₁.cart.1.lift_fst _ _ _
  have f₂ : gg ≫ t.G.hom = Z.oF.t.G.hom ≫ Z.jQ ≫ a := m₁.cart.1.lift_snd _ _ _
  have hd := hfφ _ gg (𝟙 _) g₂ (by rw [f₁, Category.id_comp]) (by rw [Category.id_comp, d₁])
    (by rw [Category.id_comp, d₂])
  have hψ : ψ ≫ pullback.fst t.G.hom a = gg := by
    apply m₁.cart.1.hom_ext
    · rw [Category.assoc, c₁, f₁]
    · rw [Category.assoc, pullback.condition (f := t.G.hom) (g := a), f₂, ← Category.assoc]
      exact (congrArg (· ≫ a) c₂).trans (Category.assoc _ _ _)
  have hψχ : ψ ≫ χ = g₂ ≫ ψ₀ := by
    apply hQ₀.1.hom_ext
    · rw [Category.assoc, hχ₁, ← Category.assoc, hψ, hd, Category.assoc, hψ₁₀]
    · rw [Category.assoc, hχ₂, ← Category.assoc, c₂, Category.assoc, Category.assoc, hψh₀, hjk,
        ← Category.assoc, d₂]
  refine ⟨XK, sK, (Over.pullback h).obj GK₀, inferInstance, jK, φK, e, (Over.pullback a).obj t.G, inferInstance, _,
    φ₂, ψ, hjK, hsK, hKK, he, hje, hQ, hQK', c₁, c₂, ?_⟩
  apply gK.1.hom_ext
  · rw [Category.assoc, b₁, ← Category.assoc, hψχ, Category.assoc, hψ₂₀, ← Category.assoc, d₁, Category.assoc, a₁]
  · rw [Category.assoc, b₂, ← Category.assoc, c₂, Category.assoc, hje]
    simp only [Category.assoc]
    rw [a₂, ← Category.assoc Z.m0.toSABMap.φ, Z.m0.toSABMap.cart.1.w, Category.assoc]

end GlobalTheory.DomGrpDescent
