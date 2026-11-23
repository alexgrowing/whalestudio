import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointEigenbasisBaseChange

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FrameEig

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem epsMul_eq {R : Type} [CommRing R] (a : R) :
    GlobalTheory.CompanionTheory.Ar.epsMul a = ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a := by
  ext x <;> simp [GlobalTheory.CompanionTheory.Ar.epsMul, ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul]

theorem isTanAt_iff {R : Type} [CommRing R] {x : Sp R ⟶ Xo.X} (v : epsAt x ⟶ Xo.univ.t.G) :
    GlobalTheory.CompanionTheory.Ar.IsTanAt Xo.univ.t.G x v ↔ Formalism.L2.Pj.IsTanAt x v.left :=
  ⟨fun h => ⟨Over.w v, h⟩, fun h => h.2⟩

theorem isEigVec_iff {R : Type} [CommRing R] [Algebra c.F R] {x : Sp R ⟶ Xo.X} (τ : E →+* ℂ)
    (v : epsAt x ⟶ Xo.univ.t.G) :
    IsEigVec Xo.univ.t.act x ((algebraMap c.F R).comp (tauIn c τ)) v ↔
      Formalism.L2.Pj.IsTanAt x v.left ∧ Formalism.L2.Pj.IsEigAt c τ v.left := by
  refine and_congr (isTanAt_iff v) (forall_congr' fun a => ?_)
  rw [epsMul_eq]
  exact Iff.rfl

theorem isComb_iff {R : Type} [CommRing R] {x : Sp R ⟶ Xo.X} {n : ℕ} (a : Fin n → R)
    (v : Fin n → (epsAt x ⟶ Xo.univ.t.G)) (w : epsAt x ⟶ Xo.univ.t.G) :
    IsComb a v w ↔ Formalism.L2.Pj.IsCombAt x (fun i => (v i).left) a w.left := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, fun i => by rw [hu i, epsMul_eq], rfl⟩
  · rintro ⟨u, hu, hw⟩
    exact ⟨u, fun i => by rw [hu i, epsMul_eq], Over.OverMorphism.ext hw.symm⟩

theorem exists_frame {S : Type} [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) {F : Type} [Field F]
    (ψ : S →+* F) (x : Sp F ⟶ Xo.X) (hx : x = spMap ψ ≫ z.x) (τ : E →+* ℂ) (n : ℕ) (h : D.mult τ = n) :
    ∃ v : Fin n → (epsAt x ⟶ Xo.univ.t.G),
      (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast h.symm)) ∧
        IsEigFrame Xo.univ.t.act x ((ψ.comp (algebraMap c.F S)).comp (tauIn c τ)) v := by
  subst hx
  subst h
  letI : Algebra c.F F := (ψ.comp (algebraMap c.F S)).toAlgebra
  let ψa : S →ₐ[c.F] F := { ψ with commutes' := fun _ => rfl }
  have htan : ∀ i, Formalism.L2.Pj.IsTanAt (spMap ψ ≫ z.x) (spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ i) :=
    fun i => GlobalTheory.Frames.EigenBaseChange.isTanAt_baseChange ψ (z.tan τ i)
  have heig : ∀ i, Formalism.L2.Pj.IsEigAt c τ (spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ i) :=
    fun i => GlobalTheory.Frames.EigenBaseChange.isEigAt_baseChange ψa τ (z.eig τ i)
  let v : Fin (D.mult τ) → (epsAt (spMap ψ ≫ z.x) ⟶ Xo.univ.t.G) :=
    fun i => Over.homMk (spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ i) (htan i).1
  refine ⟨v, fun i => rfl, fun i => (isEigVec_iff τ (v i)).2 ⟨htan i, heig i⟩, fun w hw => ?_⟩
  obtain ⟨h1, h2⟩ := (isEigVec_iff τ w).1 hw
  obtain ⟨a, ha, hu⟩ := GlobalTheory.Frames.eigenbasis_baseChange E H D l Xo c S F ψa z τ w.left h1 h2
  exact ⟨a, (isComb_iff a v w).2 ha, fun b hb => hu b ((isComb_iff b v w).1 hb)⟩

end GlobalTheory.CompanionTheory.Ar.FrameEig

open GlobalTheory.CompanionTheory.Ar.FrameEig in

theorem GlobalTheory.CompanionTheory.Ar.FrameEig.isFramed_frPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ : E →+* ℂ) (S : Type) [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) (F : Type) [Field F] (ψ : S →+* F) (y : Sp F ⟶ Xo.XF c) (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q), under y = spMap ψ ≫ z.x → y ≫ pullback.snd _ _ = spMap (ψ.comp (algebraMap c.F S)) → ∃ (v : Vecs y D.p) (w : Vecs y D.q), (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast hp.symm)) ∧ (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) ∧ ∀ U : Set (Xo.XF c), Set.range y ⊆ U → IsFramed U τ (ψ.comp (algebraMap c.F S)) y v w := by
  intro E _ _ _ H D l Xo c τ S _ _ z F _ ψ y hp hq hx hs
  obtain ⟨v, hv, fv⟩ := exists_frame z ψ (under y) hx τ D.p hp
  obtain ⟨w, hw, fw⟩ := exists_frame z ψ (under y) hx (ComplexEmbedding.conjugate τ) D.q hq
  exact ⟨v, w, hv, hw, fun U hU => ⟨hs, hU, fv, fw⟩⟩
