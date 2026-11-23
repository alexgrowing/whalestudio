import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GtPtAct
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.RatBase

theorem nsmul_b' {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {k : ℕ} {g h : GtPtF D F} (H : GtPtF.IsNsmul k g h) : h.b = g.b ^ k := by
  obtain ⟨gs, h0, hs, rfl⟩ := H
  have : ∀ i : Fin (k + 1), (gs i).b = g.b ^ (i : ℕ) := fun i => by
    induction i using Fin.induction with
    | zero => rw [Fin.val_zero, pow_zero]; exact h0.1
    | succ i ih => rw [(hs i).1, ih, Fin.val_succ, pow_succ]; rfl
  exact this _

theorem pow_comp' {S : Scheme.{0}} {G H Z : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H) [IsMonHom φ]
    (x : Z ⟶ G) (n : ℕ) : (x ^ n) ≫ φ = (x ≫ φ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

theorem ratBase : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (p₀ p : QkPt D'.toPre (AlgebraicClosure (FractionRing R)) n), p.y = F.e • p₀.y → GtPtAct F.o F.e p₀.g p.g → ∃ b : TF (R := R) (FractionRing R) ⟶ D'.toPre.P.A, p.g.b.left = spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ b.left := by
  intro o W _ _ _ T R _ _ _ iw I _ s ε n _ hn _ ζ _ Q e hD hT D' F p₀ p hy hg
  haveI := F.inc_hom
  haveI := F.pr_hom
  set L := AlgebraicClosure (FractionRing R)
  set a := F.xp p₀.y
  let b₀ : TF (R := R) L ⟶ Q.B := p₀.g.b ≫ F.pr
  have hpb : p.g.b = b₀ ≫ F.inc := by rw [hg.1, ← F.pr_inc, Category.assoc]
  obtain ⟨h, h1, h2⟩ := p₀.eq
  have hn1 : p₀.g.b ^ n = toUnit _ ≫ D'.toPre.c p₀.y := (nsmul_b' h1).symm.trans h2.1
  have hcpr : D'.toPre.c p₀.y ≫ F.pr = Q.c a := by
    have h3 : D'.toPre.c p₀.y ≫ F.pr ≫ F.inc = Q.c a ≫ F.inc := by
      rw [F.pr_inc, ← F.o.c_lin, ← F.xi_xp, F.c_xi]
    have h4 := congrArg (· ≫ F.pr) h3
    simpa only [Category.assoc, F.inc_pr, Category.comp_id] using h4
  have hb₀ : b₀ ^ n = toUnit _ ≫ Q.c a := by
    rw [← pow_comp', hn1, Category.assoc, hcpr]
  obtain ⟨β, β₂, w, hpb', hsq, hw, hc, htau⟩ := hD

  have hcomm : (spMap iw ≫ (T.c₀ (e a)).left) ≫ T.B.hom = 𝟙 (Sp R) ≫ spMap iw := by
    rw [Category.assoc, Over.w (T.c₀ (e a))]; simp
  let d : 𝟙_ (Over (Sp R)) ⟶ Q.B := Over.homMk (hpb'.1.lift _ _ hcomm) (by simpa using hpb'.1.lift_snd _ _ hcomm)
  have hd : d.left ≫ β = spMap iw ≫ (T.c₀ (e a)).left := hpb'.1.lift_fst _ _ hcomm
  have hdn : d ^ n = Q.c a := by
    refine Over.OverMorphism.ext (hpb'.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    rw [GlobalTheory.FrameMove.pow_comm hpb' hd n, hc a]
    congr 2
    have key : ∀ k : ℕ, T.c₀ ((k : ℤ) • e a) = T.c₀ (e a) ^ k := fun k => by
      induction k with
      | zero => rw [Nat.cast_zero, zero_smul, pow_zero, T.c₀_zero]
      | succ k ih => rw [Nat.cast_succ, add_smul, one_smul, T.c₀_add, ih, pow_succ]
    exact (key n).symm

  let κ := algebraMap (FractionRing R) L
  let x : TF (R := R) L ⟶ Q.B := b₀ * (toUnit _ ≫ d)⁻¹
  have hx : x ^ n = 1 := by
    simp only [x]
    rw [mul_pow, inv_pow, hb₀, ← GlobalTheory.FrameMove.comp_pow, hdn, mul_inv_cancel]
  obtain ⟨x₀, hx₀⟩ := hT L κ x hx
  let ρ : TF (R := R) L ⟶ TK R := Over.homMk (spMap κ) rfl
  have hxρ : x = ρ ≫ x₀ := Over.OverMorphism.ext hx₀
  have hb₀' : b₀ = ρ ≫ (x₀ * (toUnit _ ≫ d)) := by
    rw [MonObj.comp_mul, ← hxρ, ← Category.assoc, toUnit_unique (ρ ≫ toUnit _) (toUnit _)]
    simp only [x, inv_mul_cancel_right]
  let σ : TF (R := R) (FractionRing R) ⟶ TK R := Over.homMk (jFK (R := R) (FractionRing R)) rfl
  refine ⟨σ ≫ (x₀ * (toUnit _ ≫ d)) ≫ F.inc, ?_⟩
  rw [hpb, hb₀']
  simp only [Over.comp_left]

  have hj : jFK (R := R) (FractionRing R) = 𝟙 _ := by
    simp only [jFK, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  have hσ : σ.left = 𝟙 _ := hj
  rw [hσ, Category.id_comp, Category.assoc]
  rfl

end GlobalTheory.Mum.RatBase
