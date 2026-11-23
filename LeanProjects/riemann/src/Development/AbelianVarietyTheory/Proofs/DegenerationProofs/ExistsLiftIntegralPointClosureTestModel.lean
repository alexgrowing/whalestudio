import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIntegralOfWeightZeroCoordinateDominatesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LePreimageOpenPartIffTestCoordinatesStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ClosLift

theorem isDominant_gPt (p : ℕ) [Fact p.Prime] : IsDominant (gPt p) := by
  refine ⟨?_⟩
  change DenseRange (PrimeSpectrum.comap (OO p).subtype)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot _).1 (OO p).subtype_injective]
  exact bot_le

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real}

theorem big (ρ : S.Real) (h : S.Big) : Big S.g S.N (S.r * S.N) := by
  refine ⟨?_, h.1, h.2.1⟩
  rw [ρ.N_eq]
  have h1 : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
  nlinarith

theorem gPt_j {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) :
    gPt p ≫ spMap u.j = spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V :=
  (spMap_comp' _ _).trans (spMap_comp' (algebraMap u.V (FractionRing u.V)) (algebraMap (FractionRing u.V) (PadicAlgCl p))).symm

theorem exists_generic {M : RatModel o Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} {Q : Clos ρ M U₀ EE} {p : ℕ}
    [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} {y₀ : S.R →+* PadicAlgCl p} {t : ρ.GeoTest p y₀} {c : Q.Fac y t.u}
    (tm : Q.TMap t c) (x : Sp (PadicAlgCl p) ⟶ Q.P.left) (hx : x ≫ Q.P.hom = gPt p ≫ y) :
    ∃ a : Sp (PadicAlgCl p) ⟶ t.u.G.left, a ≫ t.u.G.hom = gPt p ≫ spMap t.u.j ∧
      a ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = x := by
  set κ := spMap (algebraMap (FractionRing t.u.V) (PadicAlgCl p)) with hκ
  have h1 : x ≫ Q.P.hom = (κ ≫ c.yK) ≫ U₀.ι := by
    rw [hx, Category.assoc, c.yK_fac, ← Category.assoc, ← gPt_j, Category.assoc, c.fac]
  let a1 := Q.cart.lift x (κ ≫ c.yK) h1
  have e1 : a1 ≫ Q.a₀ = x := Q.cart.lift_fst _ _ _
  have e2 : a1 ≫ pullback.snd _ _ = κ ≫ c.yK := Q.cart.lift_snd _ _ _
  have h2 : (a1 ≫ pullback.fst _ _) ≫ ρ.P.A.hom = κ ≫ spMap t.u.yK := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, e2, Category.assoc, c.yK_u]
  let a2 := t.u.cart.1.lift (a1 ≫ pullback.fst _ _) κ h2
  have e3 : a2 ≫ t.u.φ = a1 ≫ pullback.fst _ _ := t.u.cart.1.lift_fst _ _ _
  have e4 : a2 ≫ t.u.A.A.hom = κ := t.u.cart.1.lift_snd _ _ _
  let a3 : Sp (PadicAlgCl p) ⟶ pullback t.u.G.hom (jK t.u.V) := a2 ≫ t.u.U.gen.inv.left
  have e5 : a3 ≫ pullback.snd _ _ = κ := by
    rw [← e4]
    exact (Category.assoc _ _ _).trans (congrArg (a2 ≫ ·) (Over.w t.u.U.gen.inv))
  have e6 : a3 ≫ t.u.U.gen.hom.left = a2 := by
    refine (Category.assoc _ _ _).trans ((congrArg (a2 ≫ ·) ?_).trans (Category.comp_id _))
    exact congrArg CommaMorphism.left t.u.U.gen.inv_hom_id
  have e7 : a3 ≫ tm.φ = a1 := by
    apply pullback.hom_ext
    · rw [Category.assoc, tm.φ_fst, ← e3, ← e6]
      exact (Category.assoc _ _ _).symm
    · rw [Category.assoc, tm.φ_snd, ← Category.assoc, e5, e2]
  refine ⟨a3 ≫ pullback.fst _ _, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, e5, gPt_j]
  · rw [Category.assoc, ← tm.φ_f, ← Category.assoc, e7, e1]

theorem exists_lift : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ∀ b : Sp (OO p) ⟶ Q.P.left, b ≫ Q.P.hom = y → ⊤ ≤ b ⁻¹ᵁ Q.G → ∃ c' : Sp (OO p) ⟶ t.u.G.left, c' ≫ t.u.G.hom = spMap t.u.j ∧ c' ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = b := by
  intro _ o Ω _ _ _ _ S ρ M U₀ EE hB Q p _ y y₀ t c tm hbig b hb hG
  have hW : ⊤ ≤ b ⁻¹ᵁ (Q.P.hom ⁻¹ᵁ Q.W tm.l) := by
    rw [← Scheme.Hom.comp_preimage, hb]
    exact (CrdCalc.top_le_iff y _).2 tm.mem
  obtain ⟨b', hb'⟩ : ∃ b' : Sp (OO p) ⟶ (Q.P.hom ⁻¹ᵁ Q.W tm.l).toScheme, b' ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = b :=
    ⟨IsOpenImmersion.lift _ b (by
      rw [Scheme.Opens.range_ι]; exact (top_le_preimage_iff _ _).1 hW), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨w', hw'⟩ := CrdCalc.crd_exists (pull_isLB Q.isLB (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) (Q.σ tm.l) b'
  have hdet : ∀ {R : Type} [CommRing R] (ψ : t.u.V →+* R), IsUnit (tm.m.map ψ).det := fun ψ => by
    have := tm.unit.map ψ
    rwa [RingHom.map_det] at this
  obtain ⟨w, rfl⟩ : ∃ w, w' = (tm.m.map t.u.j).mulVec w :=
    ⟨(tm.m.map t.u.j)⁻¹.mulVec w', by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hdet _), Matrix.one_mulVec]⟩
  have hmap : ∀ {R : Type} [CommRing R] (ψ : OO p →+* R), Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) (Q.σ tm.l)
      (spMap ψ ≫ b') ((tm.m.map (ψ.comp t.u.j)).mulVec fun i => ψ (w i)) := fun ψ => by
    have := CrdCalc.crd_map ψ hw'
    refine (congrArg _ (funext fun i => ?_)).mp this
    exact RingHom.map_mulVec ψ _ _ i
  obtain ⟨i₀, hi₀, hne⟩ := (GlobalTheory.T.le_preimage_openPart_iff_testCoordinates o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hbig (rPt p ≫ b')
    (fun i => IsLocalRing.residue (OO p) (w i))
    (by rw [Category.assoc, ← Category.assoc b', hb', hb]) (hmap _)).1 (by
      rw [Category.assoc, hb']
      exact fun z _ => hG (Set.mem_univ (rPt p z)))
  have hu : IsUnit (w i₀) := (IsLocalRing.residue_ne_zero_iff_isUnit _).1 hne
  have hn : 1 ≤ ‖(w i₀ : PadicAlgCl p)‖ := not_lt.1 fun h => (not_isUnit_OO_iff _).2 h hu
  obtain ⟨a, ha, haf⟩ := exists_generic tm (gPt p ≫ b) (by rw [Category.assoc, hb])
  have haf' : a ≫ tm.f = gPt p ≫ b' := by
    rw [← cancel_mono (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι, Category.assoc, haf, Category.assoc, hb']
  obtain ⟨v, hv⟩ := CrdCalc.crd_exists t.mod.isLB t.σ a
  have h1 := tm.crd _ ((OO p).subtype.comp t.u.j) a v (ha.trans (spMap_comp' _ _)) hv
  rw [haf'] at h1
  obtain ⟨κ, hκ⟩ := CrdCalc.crd_unique h1 (hmap (OO p).subtype)
  have h2 : (fun i => (OO p).subtype (w i)) = fun i => (κ : PadicAlgCl p) * v i := by
    refine Matrix.mulVec_injective_iff_isUnit.2
      ((Matrix.isUnit_iff_isUnit_det _).2 (hdet ((OO p).subtype.comp t.u.j))) ?_
    have : (fun i => (κ : PadicAlgCl p) * v i) = (κ : PadicAlgCl p) • v := rfl
    rw [this, Matrix.mulVec_smul]
    exact funext hκ
  have h3 := CrdCalc.crd_smul κ hv
  rw [← h2] at h3
  obtain ⟨c', hc', hc''⟩ := GlobalTheory.T.isIntegral_of_weightZeroCoordinate_dominates p t.u.V t.u.j t.u.G S.g S.N (S.r * S.N) _ t.l.q _ S.J t.σ t.cls t.mod
    (big ρ hbig) a _ ha h3 ⟨i₀, hi₀, fun i => ((mem_OO_iff _).1 (w i).2).trans hn⟩
  refine ⟨c', hc', ?_⟩
  have := isDominant_gPt p
  have := Q.proper
  refine ext_of_isDominant_of_isSeparated Q.P.hom ?_ (gPt p) ?_
  · rw [Category.assoc, Category.assoc, tm.f_over, ← Category.assoc, hc', c.fac, hb]
  · rw [← Category.assoc, hc'', haf]

end GlobalTheory.ZH.ClosLift
end
