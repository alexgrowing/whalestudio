import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TopLeWchartNsmul

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor CategoryTheory.MonObj GlobalTheory.AbelianLetters

namespace GlobalTheory.AbelianLetters.TorusRatio

theorem valR_of_corr_one {A : Type} [CommRing A] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {ε : K → ℤ}
    {φ : K → (Y ⟶ X)} {t : LB.Gen (LB.LinComb L φ ε)} (h : LB.Gen.Corr L _ _ _ _ t (LB.oneGen L))
    (x : Sp A ⟶ Y) (j : K → L.ι) (hj : LB.Coh L φ j) (hx : ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ j) :
    valR x (LB.wchart L φ j) (t.s j).val = 1 := by
  have e := h j PEmpty.elim hj (fun k => k.elim) (fun _ k => k.elim)
  have hx' : ⊤ ≤ x ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim) :=
    fun y hy => ⟨hx hy, Set.mem_iInter.2 fun k => k.elim⟩
  have e1 : res (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim ≤ _)
      (t.s j) = 1 := e.trans (map_one _)
  refine (HolHom.valR_res x inf_le_left _ hx').symm.trans ?_
  refine (congrArg (fun q => valR x _ q.val) e1).trans ?_
  exact (HolHom.valR_eq x _ hx' _).trans (map_one _)

theorem isZero_of_isAdd {R : Type} [CommRing R] [IsDomain R] {D : Out.DegPre R} {T : Over (Sp R)}
    {g : Out.GtPt D T} (hb : g.b = 1) (h : Out.GtPt.IsAdd g g g) (χ : D.X) :
    LB.Gen.Corr D.P.L _ _ _ _ (g.s χ) (LB.oneGen D.P.L) := by
  refine corr_of_val D.P.isLB fun y J hJ => ?_
  have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm.trans
    ((val_corr hJ (h.2 χ) (𝟙 _)).trans (val_mul hJ _ _ _))
  have c1 : TorusCoord.cubVal (𝟙 _ ≫ (lift (Out.DegPre.cT D T χ) (lift g.b g.b)).left) y J = 1 := by
    rw [Category.id_comp, hb]
    exact (isCub_cubV D.cub hJ).face₂ _ _
  have e2 := (congrArg (val (g.s χ) (𝟙 _) y J * ·) c1).symm.trans e
  rw [_root_.mul_one] at e2
  exact (mul_eq_left.1 e2.symm).trans (val_one _).symm

theorem ratio_eq_torus_coord [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (D : Out.DegPre ℂ)
    (g n : ℕ) (ex : (Fin g → ℂ) → Out.GtPtF D ℂ) (sB : ∀ Tt : Over (Sp ℂ), (Tt ⟶ D.P.A) → Out.GtPt D Tt)
    (hb : ∀ Tt b, (sB Tt b).b = b ^ n)
    (hadd : ∀ Tt b b', Out.GtPt.IsAdd (sB Tt b) (sB Tt b') (sB Tt (b * b')))
    (hpull : ∀ (Tt Tt' : Over (Sp ℂ)) (h : Tt' ⟶ Tt) b, Out.GtPt.IsPull h.left (sB Tt b) (sB Tt' (h ≫ b)))
    (hex : ∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) :
    (∀ p : Out.GtPtF D ℂ, p.IsZero → IsTorusPt p (fun _ => 1)) ∧
      ∀ u : D.X → (Fin g → ℂ) → ℂ, IsRatio ex n (sB D.P.A (𝟙 _)) u → ∀ (z : Fin g → ℂ) (xv : D.X → ℂ),
        (ex z).b = Out.DegPre.zeroF D ℂ → IsTorusPt (ex ((n : ℂ) • z)) xv → ∀ x, u x z = xv x := by
  refine ⟨fun p hp => ⟨hp.1, fun χ j hj hc => valR_of_corr_one (hp.2 χ) (𝟙 (Sp ℂ)) j hj hc⟩,
    fun u hu z xv hz ht x => ?_⟩
  have hz1 : (ex z).b = 1 := hz
  obtain ⟨J, hJ⟩ := TorusCoord.exists_good' D.P.isLB (Z := Sp ℂ) (IsLocalRing.closedPoint ℂ)
  have hs : (sB (Out.TF (R := ℂ) ℂ) 1).b = (ex ((n : ℂ) • z)).b := by
    rw [hb, b_nsmul hex, hz1]
  let j : Fin 4 → D.P.L.ι := fun k => J (Out.DegPre.gtφ D ℂ (ex ((n : ℂ) • z)).b x k)
  have hj : LB.Coh D.P.L (Out.DegPre.gtφ D ℂ (ex ((n : ℂ) • z)).b x) j := fun _ _ e => congrArg J e
  have hc : ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφ D ℂ (ex ((n : ℂ) • z)).b x) j := fun y _ =>
    Set.mem_iInter.2 fun k => by
      obtain rfl : y = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
      exact hJ _
  have h1 := hu x z j hc
  rw [ht.2 x j hj hc] at h1
  have hp := hpull D.P.A (Out.TF (R := ℂ) ℂ) (ex z).b (𝟙 _)
  have ha := hadd (Out.TF (R := ℂ) ℂ) 1 1
  rw [_root_.mul_one] at ha
  have e1 : (ex z).b ≫ 𝟙 D.P.A = 1 := (Category.comp_id _).trans hz1
  rw [e1] at hp
  have h2 := valR_of_isPull (A := ℂ) (p := (Out.TF (R := ℂ) ℂ).hom) hp x j
  have h3 := valR_of_corr_one (isZero_of_isAdd ((hb _ _).trans (one_pow n)) ha x) (𝟙 (Sp ℂ)) j
    (by rw [hs]; exact hj) (by rw [hs]; exact hc)
  have h4 := h2.symm.trans h3
  exact ((congrArg (u x z * ·) h4).trans (_root_.mul_one _)).symm.trans h1.symm

end GlobalTheory.AbelianLetters.TorusRatio
