import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.RigidAndInjective

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped Pointwise

noncomputable section

namespace GlobalTheory.LevelMove

open GlobalTheory.TorusExt

attribute [local instance] gtGroup

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {c : Coeff l} {k : Type} [Field k] {bF : c.F →+* k} (a : ArcIn D l (RingHom.id c.F) k bF)

section Identification

variable (P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) [Module (𝓞 E) P.toPre.X]
  (oP : letI := H.starRing; P.toPre.OAct (𝓞 E))

theorem exists_move (φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)) (e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X) (d : WitData a P oP φ he w e)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing (PowerSeries k)) F] [Algebra (FractionRing k) F]
    (uF : F) (hF : ∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) =
      algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C x)))
    (hu : uF = algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ PowerSeries.X))
    (n : ℕ) (hn : n ∣ l.M') (q₀ : QkPt a.D₀ F n) :
    ∃ q : QkPt P.toPre F n, q.y = e q₀.y ∧ ∀ z, GenRel w (q.g.s (e z)) (q₀.g.s z) (uF ^ (a.be q₀.y z / n)) := by
  have W : GlobalTheory.LN.Match a PowerSeries.C PowerSeries.X P.toPre oP φ he w e := d
  exact GlobalTheory.MatchRigid.exists_transport W hF hu GlobalTheory.abelianSchemeLaws_all.1.globalFns hn q₀

theorem levelAgree_transition_congruent_mod_level (φ₁ φ₂ : P.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he₁ : eSec P.toPre.P.A ≫ φ₁ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (he₂ : eSec P.toPre.P.A ≫ φ₂ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w₁ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₂))
    (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X) (d₁ : WitData a P oP φ₁ he₁ w₁ e₁) (d₂ : WitData a P oP φ₂ he₂ w₂ e₂)
    (h : GlobalTheory.HostModel.LevelAgree a P w₁ w₂ e₁ e₂) :
    (∀ y ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) a.D₀.X), ∃ z, e₂.symm (e₁ y) = y + (l.M : ℤ) • z) ∧
      ∀ y, e₂.symm (e₁ y) - y ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) a.D₀.X) := by
  obtain ⟨-, rfl, -⟩ := GlobalTheory.DataRigid.dataRigid E H D l c k bF a P oP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ d₁ d₂ h
  exact ⟨fun y _ => ⟨0, by simp⟩, fun y => by simp⟩

end Identification

theorem exists_lattice_part {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (hB : D.TauBimult) (F : Type) [Field F]
    [IsAlgClosed F] [Algebra (FractionRing R) F] (n : ℕ) (hn : 0 < n) (y : D.X) : ∃ p : QkPt D F n, p.y = y :=
  exists_qkPt GlobalTheory.abelianSchemeLaws_all.1.mulN (Or.inr GlobalTheory.abelianSchemeLaws_all.1.polBaseChange) hB hn.ne' y

theorem exists_extension {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F F' : Type) [Field F]
    [Algebra (FractionRing R) F] [Field F'] [Algebra (FractionRing R) F'] (f : F →+* F')
    (hf : ∀ r : FractionRing R, f (algebraMap _ F r) = algebraMap _ F' r) (n : ℕ) (p : QkPt D F n) :
    ∃ p' : QkPt D F' n, QkExt f p p' := by
  have hf' : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' := RingHom.ext hf
  obtain ⟨h, h₁, h₂⟩ := p.eq
  refine ⟨⟨p.y, gtExt D f hf' p.g, gtExt D f hf' h, (isNsmul_iff_eq _ _ _).2 ?_, ?_⟩, rfl,
    (eq_gtExt_iff f hf' _ _).1 rfl⟩
  · rw [(isNsmul_iff_eq _ _ _).1 h₁, map_nsmul]
  · refine (isIota_iff_val _ _).2 ⟨?_, fun χ y J hJ => ?_⟩
    · rw [gtExt_b, ((isIota_iff_val _ _).1 h₂).1, comp_cP]
    · rw [gtExt_val f hf' _ χ hJ, tauVal, ← extMap_jFK f hf']
      exact (val_corr hJ (h₂.2 χ) _).trans (val_pull hJ _ _ _)

theorem mem_closure_level (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing k) F]
    (x : TF (R := k) F ⟶ a.D₀.P.A) (hx : letI := H.starRing; ∀ m ∈ l.Mb, x ≫ a.oa.onB.act m = 1) :
    x ∈ Subgroup.closure ({z | ∃ χ, z = toUnit _ ≫ a.D₀.c χ} ∪
      {z | ∃ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ q₀ : QkPt a.D₀ F l.M,
        QkExt (algebraMap (FractionRing k) F) (a.eta v) q₀ ∧ z = q₀.g.b}) := by
  let _ := H.starRing
  have hG := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have h₀ : 0 < l.M := lt_of_lt_of_le three_pos l.three_le
  obtain ⟨m, hm, mb, hb, hsum⟩ := Submodule.mem_sup.1 (l.coprime ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ l.Mb ⊔ _)
  have xM : x ^ l.M = 1 := by
    have e := hx _ (Ideal.mul_le_left (l.prod.ge (Ideal.subset_span rfl)) : (l.M : 𝓞 E) ∈ l.Mb)
    rwa [← _root_.mul_one (l.M : 𝓞 E), act_nsmul, a.oa.onB.map_one, MonObj.comp_pow, Category.comp_id] at e
  have ex : x ≫ a.oa.onB.act mb = x := by
    have e₁ : x ≫ a.oa.onB.act (m + mb) = x := by rw [hsum, a.oa.onB.map_one, Category.comp_id]
    rw [a.oa.onB.map_add] at e₁
    exact ((_root_.one_mul _).symm.trans (congrArg (· * _) (hx m hm).symm)).trans ((MonObj.comp_mul _ _ _).symm.trans e₁)
  obtain ⟨p, -, hp⟩ := exists_qkPt_of_torsion a.bimult h₀.ne' xM
  obtain ⟨-, I, -, -, hI⟩ := a.geom F ⟨H.rt0, c.le (IntermediateField.subset_adjoin _ _ (by simp))⟩
    ⟨zeta l.A, c.le (IntermediateField.subset_adjoin _ _ (by simp))⟩ rfl rfl _ rfl
  obtain ⟨v, hv⟩ := I.onto _ h₀ p
  have hmv : mb • v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) := Submodule.smul_mem_smul hb trivial
  obtain ⟨q, hq, -⟩ := existsUnique_qkExt a.bimult (algebraMap (FractionRing k) F) (RingHom.comp_id _) (a.eta (mb • v))
  have e : QkPt.Equiv a.D₀ F q (qkSmul a.bimult hG a.oa mb p) :=
    equiv_trans a.bimult (hI _ hmv q hq) (equiv_trans a.bimult
      (equiv_symm a.bimult ((qkAct_iff a.bimult hG a.oa _ _ _).1 (I.lin _ h₀ mb v))) (qkSmul_congr a.bimult hG a.oa mb hv))
  obtain ⟨z, -, hz⟩ := (equiv_iff a.bimult _ _).1 e
  have hb' : x = q.g.b * cP a.D₀ _ z := by
    have := congrArg GtPtF.b hz
    rw [add_b, iota_b] at this
    rw [← this, ← ex, ← hp]
    exact (gtSmul_b hG a.oa mb p.g).symm
  rw [hb']
  exact Subgroup.mul_mem _ (Subgroup.subset_closure (.inr ⟨_, hmv, q, hq, rfl⟩)) (Subgroup.subset_closure (.inl ⟨z, rfl⟩))

end GlobalTheory.LevelMove
