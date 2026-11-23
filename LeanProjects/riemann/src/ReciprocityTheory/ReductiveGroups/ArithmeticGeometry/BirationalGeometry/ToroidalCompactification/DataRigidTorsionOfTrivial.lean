import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {c : Coeff l}

def RigidIn {k : Type} [Field k] {bF : c.F →+* k} (a : ArcIn D l (RingHom.id c.F) k bF) {t : SAB H (Sp (PowerSeries k))}
    (P : PELUnif (Ideal.span {PowerSeries.X}) t) (φ₁ φ₂ : P.D.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he₁ : eSec P.D.toPre.P.A ≫ φ₁ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (he₂ : eSec P.D.toPre.P.A ≫ φ₂ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w₁ : LB.Iso P.D.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.D.toPre.P.L (a.D₀.P.L.pull φ₂))
    (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.D.toPre.X) : Prop :=
  WitData a P.D P.oD φ₁ he₁ w₁ e₁ ∧ WitData a P.D P.oD φ₂ he₂ w₂ e₂ ∧
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing (PowerSeries k)) F] [Algebra (FractionRing k) F]
      (uF : F),
      (∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) =
        algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C x))) →
      uF = algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ PowerSeries.X) →
      ∀ (n : ℕ) (p₀ : Out.QkPt a.D₀ (FractionRing k) n),
        ((n = l.A ∧ ∃ v, HEq p₀ (a.etaA v)) ∨
          (n = l.M ∧ ∃ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), HEq p₀ (a.eta v))) →
        ∀ (q₀ : Out.QkPt a.D₀ F n) (q₁ q₂ : Out.QkPt P.D.toPre F n),
          QkExt (algebraMap _ F) p₀ q₀ → q₁.y = e₁ q₀.y → q₂.y = e₂ q₀.y →
          (∀ z, GenRel w₁ (q₁.g.s (e₁ z)) (q₀.g.s z) (uF ^ (a.be q₀.y z / n))) →
          (∀ z, GenRel w₂ (q₂.g.s (e₂ z)) (q₀.g.s z) (uF ^ (a.be q₀.y z / n))) →
          Out.QkPt.Equiv P.D.toPre F q₁ q₂

def GammaTrivSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l)
    (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (t : SAB H (Sp (PowerSeries k)))
    (P : PELUnif (Ideal.span {PowerSeries.X}) t), P.TorsionIso →
    ∀ (φ₁ φ₂ : P.D.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he₁ : eSec P.D.toPre.P.A ≫ φ₁ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (he₂ : eSec P.D.toPre.P.A ≫ φ₂ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w₁ : LB.Iso P.D.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.D.toPre.P.L (a.D₀.P.L.pull φ₂))
    (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.D.toPre.X), RigidIn a P φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ → e₁ = e₂

def ThetaTrivSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l)
    (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (t : SAB H (Sp (PowerSeries k)))
    (P : PELUnif (Ideal.span {PowerSeries.X}) t), P.TorsionIso →
    ∀ (φ₁ φ₂ : P.D.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he₁ : eSec P.D.toPre.P.A ≫ φ₁ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (he₂ : eSec P.D.toPre.P.A ≫ φ₂ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w₁ : LB.Iso P.D.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.D.toPre.P.L (a.D₀.P.L.pull φ₂))
    (e₁ : a.D₀.X ≃ₗ[𝓞 E] P.D.toPre.X), RigidIn a P φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₁ → φ₁ = φ₂

def WTrivSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l)
    (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF)
    (P : Out.DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) [Module (𝓞 E) P.toPre.X]
    (oP : letI := H.starRing; P.toPre.OAct (𝓞 E)) (φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w₁ w₂ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)) (e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X),
    WitData a P oP φ he w₁ e → WitData a P oP φ he w₂ e → w₁ = w₂

def GammaBetaSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l)
    (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF)
    (P : Out.DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) [Module (𝓞 E) P.toPre.X]
    (oP : letI := H.starRing; P.toPre.OAct (𝓞 E)) (φ₁ φ₂ : P.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he₁ : eSec P.toPre.P.A ≫ φ₁ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (he₂ : eSec P.toPre.P.A ≫ φ₂ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w₁ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₂))
    (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X),
    WitData a P oP φ₁ he₁ w₁ e₁ → WitData a P oP φ₂ he₂ w₂ e₂ →
    ∀ y z, a.be (e₂.symm (e₁ y)) (e₂.symm (e₁ z)) = a.be y z

def GammaModMSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l)
    (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (t : SAB H (Sp (PowerSeries k)))
    (P : PELUnif (Ideal.span {PowerSeries.X}) t), P.TorsionIso →
    ∀ (φ₁ φ₂ : P.D.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he₁ : eSec P.D.toPre.P.A ≫ φ₁ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (he₂ : eSec P.D.toPre.P.A ≫ φ₂ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w₁ : LB.Iso P.D.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.D.toPre.P.L (a.D₀.P.L.pull φ₂))
    (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.D.toPre.X), RigidIn a P φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ →
    ∀ y, ∃ z, e₂.symm (e₁ y) = y + (l.M : ℤ) • z

theorem dataRigid_torsion_of_trivial (hΓ : GammaTrivSt) (hΘ : ThetaTrivSt) (hW : WTrivSt) : DataRigidTorsion := by
  intro E _ _ _ H D l c k _ bF a t P hP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ hw₁ hw₂ hq
  have hR : RigidIn a P φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ := And.intro hw₁ (And.intro hw₂ hq)

  have he : e₁ = e₂ := hΓ E H D l c k bF a t P hP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ hR
  subst he

  have hφ : φ₁ = φ₂ := hΘ E H D l c k bF a t P hP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ hR
  subst hφ

  exact ⟨rfl, rfl, heq_of_eq (hW E H D l c k bF a P.D P.oD φ₁ he₁ w₁ w₂ e₁ hw₁ hw₂)⟩

theorem gammaTriv (hBe : GammaBetaSt) (hMo : GammaModMSt) (hF : LatFinOrdSt) (hK : LatMinkowskiSt) : GammaTrivSt := by
  intro E _ _ _ H D l c k _ bF a t P hP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ hR
  have hR0 := hR
  obtain ⟨hw₁, hw₂, -⟩ := hR0
  have hβ := hBe E H D l c k bF a P.D P.oD φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ hw₁ hw₂
  have hM := hMo E H D l c k bF a t P hP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ hR

  let σ : a.D₀.X ≃ₗ[ℤ] a.D₀.X := (e₁.trans e₂.symm).toAddEquiv.toIntLinearEquiv
  have hσapp : ∀ y, σ y = e₂.symm (e₁ y) := fun y => rfl
  obtain ⟨n, hn, hσn⟩ := hF a.D₀.X a.be a.be_symm a.be_pos σ
    (fun y z => by rw [hσapp, hσapp]; exact hβ y z)
  have hσ : σ = 1 := by
    refine hK a.D₀.X σ n l.M hn hσn l.three_le (fun y => ?_)
    obtain ⟨z, hz⟩ := hM y
    refine ⟨z, ?_⟩
    rw [hσapp, hz]
    simp
  ext y
  have h1 : σ y = y := by rw [hσ]; rfl
  rw [hσapp] at h1
  exact (LinearEquiv.symm_apply_eq e₂).mp h1

def ThetaFixMbSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l)
    (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (t : SAB H (Sp (PowerSeries k)))
    (P : PELUnif (Ideal.span {PowerSeries.X}) t), P.TorsionIso →
    ∀ (φ₁ φ₂ : P.D.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he₁ : eSec P.D.toPre.P.A ≫ φ₁ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (he₂ : eSec P.D.toPre.P.A ≫ φ₂ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w₁ : LB.Iso P.D.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.D.toPre.P.L (a.D₀.P.L.pull φ₂))
    (e₁ : a.D₀.X ≃ₗ[𝓞 E] P.D.toPre.X), RigidIn a P φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₁ →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing (PowerSeries k)) F]
      (x : Over.mk (Out.jFK (R := PowerSeries k) F ≫ Out.jK (PowerSeries k)) ⟶ P.D.toPre.P.A),
      (letI := H.starRing; ∀ m ∈ l.Mb, x ≫ P.oD.onB.act m = 1) → x.left ≫ φ₁ = x.left ≫ φ₂

def ThetaWeilSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l)
    (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF)
    (P : Out.DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) [Module (𝓞 E) P.toPre.X]
    (oP : letI := H.starRing; P.toPre.OAct (𝓞 E)) (φ₁ φ₂ : P.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he₁ : eSec P.toPre.P.A ≫ φ₁ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (he₂ : eSec P.toPre.P.A ≫ φ₂ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w₁ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₂))
    (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X),
    WitData a P oP φ₁ he₁ w₁ e₁ → WitData a P oP φ₂ he₂ w₂ e₂ →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing (PowerSeries k)) F],
      (∀ x : Over.mk (Out.jFK (R := PowerSeries k) F ≫ Out.jK (PowerSeries k)) ⟶ P.toPre.P.A,
        (letI := H.starRing; ∀ m ∈ l.Mb, x ≫ oP.onB.act m = 1) → x.left ≫ φ₁ = x.left ≫ φ₂) →
      ∀ x : Over.mk (Out.jFK (R := PowerSeries k) F ≫ Out.jK (PowerSeries k)) ⟶ P.toPre.P.A,
        x ^ l.M = 1 → x.left ≫ φ₁ = x.left ≫ φ₂

def SerreAllSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l)
    (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF)
    (P : Out.DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) [Module (𝓞 E) P.toPre.X]
    (oP : letI := H.starRing; P.toPre.OAct (𝓞 E)) (φ₁ φ₂ : P.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he₁ : eSec P.toPre.P.A ≫ φ₁ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (he₂ : eSec P.toPre.P.A ≫ φ₂ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w₁ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₂))
    (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X),
    WitData a P oP φ₁ he₁ w₁ e₁ → WitData a P oP φ₂ he₂ w₂ e₂ →
    (∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing (PowerSeries k)) F]
      (x : Over.mk (Out.jFK (R := PowerSeries k) F ≫ Out.jK (PowerSeries k)) ⟶ P.toPre.P.A),
        x ^ l.M = 1 → x.left ≫ φ₁ = x.left ≫ φ₂) → φ₁ = φ₂

def WeilRosatiSt : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : Out.PolAV S) (O : Type) [Ring O] [StarRing O] (o : P.OAct O)
    (k : ℕ) (T : Over S) (x y : T ⟶ P.A) (a : O) (c : Γ(T.left, ⊤)ˣ), x ^ k = 1 → y ^ k = 1 →
    (Out.WeilIs P.A P.L k (x ≫ o.act a) y c ↔ Out.WeilIs P.A P.L k x (y ≫ o.act (star a)) c)

theorem thetaTriv (h1 : ThetaFixMbSt) (h2 : ThetaWeilSt) (h3 : SerreAllSt) : ThetaTrivSt := by
  intro E _ _ _ H D l c k _ bF a t P hP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ hR
  have hR0 := hR
  obtain ⟨hw₁, hw₂, -⟩ := hR0

  have hMb := h1 E H D l c k bF a t P hP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ hR
  refine h3 E H D l c k bF a P.D P.oD φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₁ hw₁ hw₂ ?_
  intro F _ _ _ x hx
  exact h2 E H D l c k bF a P.D P.oD φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₁ hw₁ hw₂ F (hMb F) x hx

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
