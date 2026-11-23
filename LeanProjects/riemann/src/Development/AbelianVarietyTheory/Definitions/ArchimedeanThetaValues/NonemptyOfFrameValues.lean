import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.NonemptyGtAnOfToric
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsPrimitiveRootArcRoot
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.AnalyticTorusPointBaseEqHolUnifEx
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SectionsEquivAnArcTheta

noncomputable section
namespace GlobalTheory.ArcDictModel
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HostModel

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
  (bF : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]

theorem nonempty_toric : Nonempty (GtAn (arcIn c ℂ bF)) :=
  nonempty_gtAn_of_toric _ (𝓞 E) (arcIn_D₀ c ℂ bF)

end

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]
  {b : O →+* ℂ} {a : ArcIn D l β ℂ b} (Λ : GtAn₀ a)

theorem y_of_lifts {k : ℕ} [NeZero k] (p : Out.QkPt a.D₀ (FractionRing ℂ) k) : letI := H.starRing
    ∀ la : Λ.A.La, Λ.Lifts p la → ∃ z, p.y = Λ.y la + k • z := by
  intro la h
  obtain ⟨q, hq, -⟩ := TorusExt.existsUnique_qkExt a.bimult (algebraMap (FractionRing ℂ) ℂ) (RingHom.comp_id _) p
  obtain ⟨z, hz, -⟩ := h q hq
  exact ⟨z, hq.1.symm.trans hz⟩

end

theorem exists_closed : ∃ (_ : Algebra (FractionRing ℂ) ℂ) (_ : IsScalarTower ℂ (FractionRing ℂ) ℂ),
    Nonempty (GtAn (arcIn (coeff (level host 5 (by norm_num))) ℂ (coeff _).F.val.toRingHom)) :=
  letI := FractionRing.liftAlgebra ℂ ℂ
  haveI := FractionRing.isScalarTower_liftAlgebra ℂ ℂ
  ⟨_, this, nonempty_toric _ _⟩

section Bridge
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]
  {b : O →+* ℂ} {a : ArcIn D l β ℂ b}

theorem nonempty_of_frameValues (Λ : letI := H.starRing; ArcPts.GtAn a) : Nonempty (GtAn a) := by
  letI := H.starRing
  have h := fun (j : ℕ) (hj : NeZero j) (α : Λ.A.X) =>
    TwistedTheta.sections_equiv_anArc_theta Λ.A a.D₀ Λ.u _ Λ.lam (fun _ _ e => congrArg Λ.A.chi (Subtype.ext e)) Λ.ah j
      (Nat.one_le_iff_ne_zero.2 hj.out) (fun θ hθ => ((Λ.pow j).2 θ hθ).exists) (Λ.ε α) α (Λ.ct α)
  choose e _ he using h
  refine ⟨⟨⟨GtAnModel.toDict Λ, fun x y => (Λ.be_eq x y).symm⟩, ⟨fun j hj α => (e j hj α).toEquiv, ?_⟩⟩⟩
  intro j hj α s z i hi
  refine (he j hj α s z i hi).trans (congrArg (_ * ·) ?_)
  refine Eq.trans ?_ (Fin.prod_univ_four _).symm
  exact congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) rfl (zpow_one _).symm) (zpow_neg_one _).symm)
    (zpow_one _).symm

end Bridge

section Determined
variable {O : Type} [CommRing O] [StarRing O] [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]
  {D₀ : Out.DegPre ℂ} [Module O D₀.X] {oa : D₀.OAct O} (d : GtDict D₀ oa)

theorem subsingleton_secFn : Subsingleton d.SecFn := ⟨fun ⟨f, hf⟩ ⟨g, hg⟩ => by
  obtain rfl : @f = @g := by
    funext j hj α
    exact Equiv.ext fun s => Subtype.ext (GtDict.IsFamFn.unique d (hf j α s) (hg j α s))
  rfl⟩

theorem psi_eq (x : d.A.X) : ∃ j : PUnit → D₀.P.L.ι, (d.A.psi x : ℂ) =
    valAt' (Out.jFK (R := ℂ) ℂ) _ ((D₀.psi (d.eX x)).s j).val * d.u.fr (j PUnit.unit) (d.A.ct x) := by
  obtain ⟨i, hi⟩ := exists_chart_complexPoint D₀.P.isLB (d.u.ex (d.A.ct x)).left
  refine ⟨fun _ => i, ?_⟩
  rw [d.psi_val x (fun _ => i) hi, inv_mul_cancel_right₀ (d.u.fr_ne i _ hi)]

theorem isZero_torus_iff (w : d.A.X →+ ℂ) : (d.ex₀ (w, 0)).IsZero ↔ ∃ n : d.A.X →+ ℤ, ∀ x, w x = n x := by
  rw [d.ker]
  constructor
  · rintro ⟨la, hy, e⟩
    have hl : la.l = 0 := Subtype.ext (by simpa [hy] using (congrArg Prod.snd e).symm)
    exact ⟨la.n, fun x => by simpa [hy, hl] using congrArg (fun v : d.A.V => v.1 x) e⟩
  · rintro ⟨n, hn⟩
    exact ⟨AnArc.La.mk 0 n 0, rfl, Prod.ext (AddMonoidHom.ext fun x => by simp [hn]) (by simp)⟩

end Determined

theorem exists_not_isZero {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} [Algebra (FractionRing ℂ) ℂ]
    [IsScalarTower ℂ (FractionRing ℂ) ℂ] {b : O →+* ℂ} {a : ArcIn D l β ℂ b} (Λ : GtAn₀ a) :
    letI := H.starRing; ∃ v, ¬ (Λ.ex₀ v).IsZero := by
  letI := H.starRing
  haveI := a.nontriv
  haveI : Nontrivial Λ.A.X := Λ.eX.toEquiv.nontrivial
  obtain ⟨y, hy⟩ := exists_ne (0 : Λ.A.X)
  refine ⟨(Complex.I • (Int.castAddHom ℂ).comp (Λ.A.be y).toAddMonoidHom, 0), fun h => ?_⟩
  obtain ⟨n, hn⟩ := (isZero_torus_iff Λ.toGtDict _).1 h
  have h1 := congrArg Complex.im (hn y)
  have h2 := Λ.A.be_pos y hy
  simp at h1
  omega

end GlobalTheory.ArcDictModel
