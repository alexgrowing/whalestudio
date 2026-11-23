import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.CanonicalLiftFrobenius
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.QkActPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  IsLocalRing NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftFiniteOrder

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem val_scaleGen {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (c : Γ(Y, ⊤)ˣ) (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) :
    val (scaleGen c t) r z J = gm r z ⊤ c * val t r z J := by
  unfold val
  show gm r z _ (res le_top c * t.s _) = gm r z ⊤ c * gm r z _ (t.s _)
  refine (MonoidHom.map_mul (gm r z _) _ _).trans ?_
  congr 1
  exact gm_res r z le_top (hJ.mem φ r) c

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]

def zUnit (ζ : F) (hζ : ζ ≠ 0) : Γ((TF (R := V) F).left, ⊤)ˣ :=
  ((Ne.isUnit hζ).map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom).unit

theorem phiRel_scale (hG : GlobalFnsSt) {k : ℕ} (p : QkPt D.toPre F k)
    (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))) (hw : w.IsGen)
    (Φ : Fam D.toPre F k →ₗ[F] Fam D.toPre F k) (hΦr : ∀ s t, PhiRel D.toPre F k p w s t ↔ t = Φ s)
    (ζ : F) (hζ : ζ ≠ 0) (s t : Fam D.toPre F k) :
    PhiRel D.toPre F k p (scaleGen (zUnit (V := V) ζ hζ) w) s t ↔ t = ζ • Φ s := by
  have hw' := scaleGen_isGen (zUnit (V := V) ζ hζ) w hw
  have key : ∀ s : Fam D.toPre F k, PhiVal p (scaleGen (zUnit (V := V) ζ hζ) w) s.s (ζ • Φ s).s := by
    intro s a' β hβ T ρ z' J hJ
    have h1 := (phiRel_iff hG p w hw s (Φ s)).1 ((hΦr s (Φ s)).2 rfl) a' β hβ T ρ z' J hJ
    have hu : gs (ρ.left ≫ (fst (TF (R := V) F) D.toPre.P.A).left) z' ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) =
        (gm (ρ ≫ fst (TF (R := V) F) D.toPre.P.A).left z' ⊤ (zUnit (V := V) ζ hζ)).val :=
      gs_unit _ z' ⊤ trivial (zUnit (V := V) ζ hζ)
    rw [sval_smul ζ (Φ s) β ρ.left z' hJ, h1, val_mul hJ, val_mul hJ, val_scaleGen hJ, hu]
    simp only [Units.val_mul]
    ring
  constructor
  · intro h
    exact phi_unique p _ ((phiRel_iff hG p _ hw' s t).1 h) (key s)
  · rintro rfl
    exact (phiRel_iff hG p _ hw' s _).2 (key s)

theorem finOrd_of_pow {k : ℕ} (hk : 1 ≤ k) (p : QkPt D.toPre F k)
    (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k)))
    (Ψ : Fam D.toPre F k →ₗ[F] Fam D.toPre F k) (hΨ : ∀ s t, PhiRel D.toPre F k p w s t ↔ t = Ψ s)
    (hpow : ∀ s, (Ψ ^ k) s = s) : FinOrd D F k p w 1 := by
  have hext : ∀ a b : Fam D.toPre F k, (∀ α j, (a.s α).f j = (b.s α).f j) → a = b := by
    rintro ⟨sa, fa⟩ ⟨sb, fb⟩ h
    have hs : sa = sb := by
      funext α
      have h1 : (sa α).f = (sb α).f := funext (h α)
      rcases hx : sa α with ⟨xf, xc⟩
      rcases hy : sb α with ⟨yf, yc⟩
      rw [hx, hy] at h1
      simp only at h1
      subst h1
      rfl
    subst hs
    rfl
  have hone : ∀ W, DegPre.constBF D.toPre F (1 : F) W = 1 := by
    intro W
    simp [DegPre.constBF]
  refine ⟨k, hk, fun ss ts h α j => ?_⟩
  have hstep : ∀ i : Fin k, ss i.succ = Ψ (ss i.castSucc) := by
    intro i
    obtain ⟨h1, h2⟩ := h i
    rw [← (hΨ _ _).mp h1]
    apply hext
    intro α j
    rw [h2 α j, hone, _root_.one_mul]
  have hall : ∀ n (hn : n ≤ k), ss ⟨n, by omega⟩ = (Ψ ^ n) (ss 0) := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [pow_zero, Module.End.one_apply]
      rfl
    | succ n ih =>
      intro hn
      have h3 := hstep ⟨n, by omega⟩
      rw [pow_succ', Module.End.mul_apply, ← ih (by omega)]
      exact h3
  have hlast : ss (Fin.last k) = ss 0 := by
    rw [show Fin.last k = ⟨k, by omega⟩ from rfl, hall k le_rfl]
    exact hpow (ss 0)
  rw [hlast]

end ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftFiniteOrder
