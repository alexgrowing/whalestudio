import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FourierSeriesProductEqProductSeriesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SummableFourierCoefficientsFamilyFiniteExtensionStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MeetsOpensOfSeparatesSections
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsSecKIsUnit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section

namespace GlobalTheory.ParameterRoot

section Sections

variable {X Y : Scheme.{0}} {L : LB X} {f : Y ⟶ X}

def mulPow {k k' : ℕ} (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => f) (fun _ => (k : ℤ))))
    (t : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => f) (fun _ => (k' : ℤ)))) :
    LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => f) (fun _ => ((k + k' : ℕ) : ℤ))) where
  f j := @id Γ(Y, LB.wchart L (fun _ : Fin 1 => f) j) (s.f j) * @id Γ(Y, LB.wchart L (fun _ : Fin 1 => f) j) (t.f j)
  compat i j := by
    let W : Y.Opens := LB.wchart L (fun _ : Fin 1 => f) i ⊓ LB.wchart L (fun _ : Fin 1 => f) j
    let gg : ℕ → Γ(Y, W)ˣ := fun d => (LB.LinComb L (K := Fin 1) (fun _ => f) (fun _ => (d : ℤ))).g i j
    have e : gg (k + k') = gg k * gg k' := by
      simp only [gg, LB.LinComb, Fin.prod_univ_one, Nat.cast_add, zpow_add]
    let r₁ := (Y.presheaf.map (homOfLE (inf_le_left : W ≤ LB.wchart L (fun _ : Fin 1 => f) i)).op).hom
    let r₂ := (Y.presheaf.map (homOfLE (inf_le_right : W ≤ LB.wchart L (fun _ : Fin 1 => f) j)).op).hom
    have hs : r₁ (s.f i) = (gg k).val * r₂ (s.f j) := s.compat i j
    have ht : r₁ (t.f i) = (gg k').val * r₂ (t.f j) := t.compat i j
    have key : ∀ a a' b b', r₁ a = (gg k).val * r₂ b → r₁ a' = (gg k').val * r₂ b' →
        r₁ (a * a') = (gg (k + k')).val * r₂ (b * b') := by
      intro a a' b b' h h'
      rw [map_mul, map_mul, h, h', e, Units.val_mul]
      ring
    exact key _ _ _ _ hs ht

end Sections

section Algebra

theorem cancel {F T : Type} [Field F] (x v : T → F) (t₀ : T) (κ κ' : F) (m : ℕ) (hκ : κ ≠ 0) (hκ' : κ' ≠ 0)
    (h₀ : v t₀ ≠ 0) (h : ∀ t, κ * x t * x t₀ ^ m = κ' * (v t * v t₀ ^ m)) :
    ∃ c : F, c ≠ 0 ∧ ∀ t, x t = c * v t := by
  have hx : x t₀ ≠ 0 := by
    intro e
    have := h t₀
    rw [e, MulZeroClass.mul_zero, MulZeroClass.zero_mul] at this
    exact mul_ne_zero hκ' (mul_ne_zero h₀ (pow_ne_zero m h₀)) this.symm
  refine ⟨κ' * v t₀ ^ m / (κ * x t₀ ^ m), div_ne_zero (mul_ne_zero hκ' (pow_ne_zero m h₀))
    (mul_ne_zero hκ (pow_ne_zero m hx)), fun t => ?_⟩
  have := h t
  field_simp
  linear_combination this

end Algebra

section Point

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  (U : UnifPre I D A G) {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem exists_val_ne_zero (hA : AmpleSt) {N : ℕ} (hN : 4 ≤ N) (x : Sp F ⟶ (UnifPre.GF (G := G) F).left)
    (l : U.LG.L.ι) (hl : ⊤ ≤ x ⁻¹ᵁ LB.wchart U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) (fun _ => l)) :
    ∃ σ : U.SecGF F N, valF x _ (σ.f (fun _ => l)) ≠ 0 := by
  have hm := MatchCoord.mem_of_le hl
  obtain ⟨J, hJ, e⟩ := exists_good U.LG.L U.LG.isLB (MatchCoord.pt F)
    (fun _ : Fin 1 => x ≫ UnifPre.gFK (G := G) F) (fun _ => l) (fun _ _ _ => rfl)
    (fun k => Set.mem_iInter.1 hm k)
  obtain ⟨s, hs⟩ := GenericGenerated.exists_secK_isUnit hA R I D A G U N hN _
    (x ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) (MatchCoord.pt F) J hJ
  let σ : U.SecGF F N := H1.SectionArithmetic.pullSec s (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left
  have h₁ : sval σ x (MatchCoord.pt F) J = _ := H1.SectionArithmetic.sval_pullSec s _ x (MatchCoord.pt F) hJ
  have h₂ := sval_of σ x (MatchCoord.pt F) J (fun _ => l) e
  refine ⟨σ, fun h0 => ?_⟩
  have h₃ := MatchCoord.stk_valF hl (σ.f (fun _ => l))
  have h₄ : gs x (MatchCoord.pt F) _ (σ.f (fun _ => l)) = 0 :=
    h₃.symm.trans ((congrArg _ h0).trans (map_zero _))
  exact not_isUnit_zero ((congrArg IsUnit (h₁.symm.trans (h₂.trans h₄))).mp hs)

end Point

theorem parAt_of_parAt_mul : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (N k : ℕ) (a : u.PtC) (g : GtPtF u.D.toPre (PadicAlgCl p)), 4 ≤ N → 1 ≤ k → u.ParAt (N * k) a g → u.ParAt N a g := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u lab N k a g hN hk H w hw l hl
  let x : Sp (PadicAlgCl p) ⟶ (UnifPre.GF (G := u.G) (PadicAlgCl p)).left :=
    (lift (𝟙 (TFK (R := u.V) (PadicAlgCl p))) a).left
  have hx : x ≫ UnifPre.gFK (G := u.G) (PadicAlgCl p) = u.toG a := by
    have : x ≫ (snd (TFK (R := u.V) (PadicAlgCl p)) ((Over.pullback (jK u.V)).obj u.G)).left = a.left :=
      congrArg (fun q => q.left) (lift_snd (𝟙 (TFK (R := u.V) (PadicAlgCl p))) a)
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ pullback.fst u.G.hom (jK u.V)) this)
  have hl' : ⊤ ≤ x ⁻¹ᵁ LB.wchart u.U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := u.G) (PadicAlgCl p)) (fun _ => l) := by
    intro z _
    refine Set.mem_iInter.2 fun _ => ?_
    have : (x ≫ UnifPre.gFK (G := u.G) (PadicAlgCl p)) z ∈ u.U.LG.L.U l := by
      rw [hx]; exact hl (Set.mem_univ z)
    exact this
  let v : ∀ d : ℕ, u.U.toUnifPre.SecGF (PadicAlgCl p) d → PadicAlgCl p := fun d σ =>
    valF x (LB.wchart u.U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := u.G) (PadicAlgCl p)) (fun _ => l))
      (σ.f (fun _ => l))
  have expd : ∀ d : ℕ, 1 ≤ d → ∀ σ : u.U.toUnifPre.SecGF (PadicAlgCl p) d,
      ∃ s, u.U.toUnifPre.ExpandsG (PadicAlgCl p) d σ s := fun d hd σ =>
    ((FieldBaseChange.expandsG_bijective u.U.toUnifPre (PadicAlgCl p) hL.1.globalFns hd (u.U.expand d hd)).1 σ).exists
  have summ : ∀ s : Fam u.D.toPre (PadicAlgCl p) N,
      HasSum (fun χ => GlobalTheory.UT.coef s g w χ) (∑' χ, GlobalTheory.UT.coef s g w χ) := fun s =>
    (GlobalTheory.T.summable_fourierCoefficients_family_finite_extension hL o Ω S ρ p y₀ u lab N (by omega) s g w hw).1.hasSum
  obtain ⟨σ₀, h₀⟩ : ∃ σ, v N σ ≠ 0 := exists_val_ne_zero u.U.toUnifPre hL.1.ample hN x l hl'
  obtain ⟨s₀, hs₀⟩ := expd N (by omega) σ₀
  have key : ∀ (m d : ℕ), d = N * (m + 1) → ∃ w' : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) d g.b, w'.IsGen ∧
      ∃ κ : PadicAlgCl p, κ ≠ 0 ∧ ∀ σ s, u.U.toUnifPre.ExpandsG (PadicAlgCl p) N σ s →
        ∃ τ t, u.U.toUnifPre.ExpandsG (PadicAlgCl p) d τ t ∧ v d τ = v N σ * v N σ₀ ^ m ∧
          HasSum (fun χ => GlobalTheory.UT.coef t g w' χ)
            (κ * (∑' χ, GlobalTheory.UT.coef s g w χ) * (∑' χ, GlobalTheory.UT.coef s₀ g w χ) ^ m) := by
    intro m
    induction m with
    | zero =>
      intro d hd
      obtain rfl : N = d := by omega
      refine ⟨w, hw, 1, one_ne_zero, fun σ s hs => ⟨σ, s, hs, by simp, ?_⟩⟩
      simpa using summ s
    | succ m ih =>
      intro d hd
      obtain ⟨w', hw', κ, hκ, h⟩ := ih _ rfl
      obtain rfl : d = N * (m + 1) + N := hd
      have h1 : 1 ≤ N * (m + 1) := Nat.mul_pos (by omega) (by omega)
      obtain ⟨w'', hw''⟩ : ∃ w : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) (N * (m + 1) + N) g.b, w.IsGen :=
        DVR.exists_gen_of_local (V := PadicAlgCl p) u.D.toPre.P.L u.D.toPre.P.isLB _ _
      obtain ⟨c, hc, hp⟩ := GlobalTheory.T.fourierSeries_product_eq_product_series hL o Ω S ρ p y₀ u lab (N * (m + 1)) N g w' w w'' h1 (by omega) hw' hw hw''
      refine ⟨w'', hw'', c * κ, mul_ne_zero hc hκ, fun σ s hs => ?_⟩
      obtain ⟨τ, t, hτ, e, hsum⟩ := h σ s hs
      obtain ⟨t', ht'⟩ := expd (N * (m + 1) + N) (by omega) (mulPow τ σ₀)
      refine ⟨mulPow τ σ₀, t', ht', ?_, ?_⟩
      · have : v _ (mulPow τ σ₀) = v _ τ * v _ σ₀ := MatchCoord.valF_mul hl' _ _
        rw [this, e]; ring
      · convert hp τ σ₀ (mulPow τ σ₀) t s₀ t' hτ hs₀ ht' (fun _ => rfl) _ _ hsum (summ s₀) using 1
        ring
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  obtain ⟨w', hw', κ, hκ, h⟩ := key m _ rfl
  obtain ⟨κ', hκ', h'⟩ := H w' hw' l hl
  obtain ⟨c, hc, e⟩ := cancel (T := {q : u.U.toUnifPre.SecGF (PadicAlgCl p) N × Fam u.D.toPre (PadicAlgCl p) N //
      u.U.toUnifPre.ExpandsG (PadicAlgCl p) N q.1 q.2}) (fun q => ∑' χ, GlobalTheory.UT.coef q.1.2 g w χ)
    (fun q => v N q.1.1) ⟨(σ₀, s₀), hs₀⟩ κ κ' m hκ hκ' h₀ (fun q => by
      obtain ⟨τ, t, hτ, e, hsum⟩ := h q.1.1 q.1.2 q.2
      exact (hsum.unique (h' τ t hτ)).trans (congrArg (κ' * ·) e))
  refine ⟨c, hc, fun σ s hs => ?_⟩
  have := summ s
  rw [e ⟨(σ, s), hs⟩] at this
  exact this

end GlobalTheory.ParameterRoot
