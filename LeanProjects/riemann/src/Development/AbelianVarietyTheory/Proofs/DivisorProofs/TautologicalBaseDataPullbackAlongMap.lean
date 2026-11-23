import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTransportMumfordBundleIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCancelGrpPullbackWithSquaresStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoCancelValuesMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdZpowMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusEndOfPadd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum
noncomputable section

namespace GlobalTheory.PullFrom

theorem spMap_comp_ring {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap]

theorem good_exists {X Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (z : Z) : ∃ J, Good L z J := by
  obtain ⟨J, hJ, -⟩ := exists_good L hL z (K := Empty) Empty.elim Empty.elim (fun a => a.elim) (fun k => k.elim)
  exact ⟨J, hJ⟩

private theorem sq_ext_lemma {S Z : Scheme.{0}} {G : Over S} {f g : Z ⟶ (G2 G).left}
    (h₁ : f ≫ (fst G G).left = g ≫ (fst G G).left) (h₂ : f ≫ (snd G G).left = g ≫ (snd G G).left) : f = g :=
  Over.tensorObj_ext _ _ h₁ h₂

theorem pullData_of_dataFrom : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)) (Q' : Data V) (e' : Q'.X ≃+ (Fin T.r → ℤ)), (∀ i, θ (s i) ≠ 0) → DataFrom T iw s ε n Q e → DataFrom T (θ.comp iw) (fun i => θ (s i)) ε n Q' e' → PullData Q θ Q' (e'.trans e.symm) := by
  intro o W _ _ _ T R V _ _ _ _ θ iw I _ s ε n Q e Q' e' hs hQ hQ'
  obtain ⟨β₀, β₀₂, w₀, hpb₀, hsq₀, hw₀, hc₀, hτ₀⟩ := hQ
  obtain ⟨β₁, β₁₂, w₁, hpb₁, hsq₁, hw₁, hc₁, hτ₁⟩ := hQ'
  have hcomp : spMap θ ≫ spMap iw = spMap (θ.comp iw) := (spMap_comp_ring iw θ).symm

  obtain ⟨β, β₂, hpb, hsq, hβ, hβ₂⟩ := GlobalTheory.T.exists_cancel_grpPullback_with_squares (Sp V) (Sp R) (Sp W) Q'.B Q.B T.B (spMap θ) (spMap iw)
    β₁ β₀ β₁₂ β₀₂ (hcomp ▸ hpb₁) hpb₀ hsq₁ hsq₀

  obtain ⟨w, hw, hrel⟩ := GlobalTheory.T.mumfordBundleIso_cancel_values_mul (Sp V) (Sp R) (Sp W) Q'.B Q.B T.B Q'.M.L Q.M.L T.M.L Q'.M.isLB Q.M.isLB
    T.M.isLB β₂ β₀₂ β₁₂ hβ₂ w₀ hw₀ w₁ hw₁

  have hcc : ∀ a, (Q'.c a).left ≫ β = spMap θ ≫ (Q.c ((e'.trans e.symm) a)).left := by
    intro a
    apply hpb₀.1.hom_ext
    · simp only [Category.assoc, hβ, hc₁, hc₀, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
      rw [← hcomp, Category.assoc]
    · simp only [Category.assoc, hpb.1.w]
      simp

  have hsqT : ∀ a b : Q.X, (lift (Q.c a) (Q.c b)).left ≫ β₀₂ =
      spMap iw ≫ (lift (T.c₀ ((n : ℤ) • e a)) (T.c₀ ((n : ℤ) • e b))).left := by
    intro a b
    apply sq_ext_lemma
    · rw [Category.assoc, hsq₀.1, ← Category.assoc, ← Over.comp_left, lift_fst, hc₀, Category.assoc,
        ← Over.comp_left, lift_fst]
    · rw [Category.assoc, hsq₀.2, ← Category.assoc, ← Over.comp_left, lift_snd, hc₀, Category.assoc,
        ← Over.comp_left, lift_snd]
  refine ⟨β, β₂, w, hpb, hsq, hw, hcc, ?_⟩
  intro a b
  set a₀ := (e'.trans e.symm) a with ha₀def
  set b₀ := (e'.trans e.symm) b with hb₀def
  have ha₀ : e a₀ = e' a := by simp [a₀]
  have hb₀ : e b₀ = e' b := by simp [b₀]

  have hsqQ : (lift (toUnit (TK V) ≫ Q'.c a) (toUnit (TK V) ≫ Q'.c b)).left ≫ β₂ =
      ((TK V).hom ≫ spMap θ) ≫ (lift (Q.c a₀) (Q.c b₀)).left := by
    have h₁ : (lift (Q.c a₀) (Q.c b₀)).left ≫ (fst Q.B Q.B).left = (Q.c a₀).left := by
      rw [← Over.comp_left, lift_fst]
    have h₂ : (lift (Q.c a₀) (Q.c b₀)).left ≫ (snd Q.B Q.B).left = (Q.c b₀).left := by
      rw [← Over.comp_left, lift_snd]
    apply sq_ext_lemma
    · rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Over.comp_left, Category.assoc,
        hcc, Category.assoc, Category.assoc, h₁]
      rfl
    · rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Over.comp_left, Category.assoc,
        hcc, Category.assoc, Category.assoc, h₂]
      rfl
  obtain ⟨k₀, hk₀, hv₀⟩ := hτ₀ a₀ b₀
  obtain ⟨k₁, hk₁, hv₁⟩ := hτ₁ a b
  obtain ⟨x, y, hy, hxy, hxy'⟩ :=
    GlobalTheory.LaurentFrac.exists_frac R V θ s (fun i => (n : ℤ) * ε i (e' a) (e' b)) hs

  obtain ⟨u, hu, hvu⟩ := GlobalTheory.T.exists_generator_transport_mumfordBundleIso (Sp R) (Sp W) Q.B T.B Q.M.L T.M.L Q.M.isLB T.M.isLB β₀₂ w₀ hw₀
    (𝟙_ (Over (Sp R))) (𝟙_ (Over (Sp W))) (Q.c a₀) (Q.c b₀) (T.c₀ ((n : ℤ) • e a₀))
    (T.c₀ ((n : ℤ) • e b₀)) (spMap iw) (hsqT a₀ b₀) (T.τ₀ _ _) (T.τ₀_gen _ _)
  refine ⟨u, x, y, k₀, k₁, hu, hy, ?_, ?_, ?_, ?_⟩
  · rw [hk₀, ha₀, hb₀]
    exact hxy
  · rw [hk₁]
    exact hxy'
  · intro z J hJ
    obtain ⟨J₀, hJ₀⟩ := good_exists T.M.isLB z
    have hl : (toUnit (TK R)).left ≫ (lift (Q.c a₀) (Q.c b₀)).left =
        (lift (toUnit (TK R) ≫ Q.c a₀) (toUnit (TK R) ≫ Q.c b₀)).left := by
      rw [← Over.comp_left, comp_lift]
    rw [hv₀ z J₀ J hJ₀ hJ, hvu _ _ z J₀ J hJ₀ hJ, hl]
    rfl
  · intro z J J' hJ hJ'
    obtain ⟨J₀, hJ₀⟩ := good_exists T.M.isLB z
    rw [ha₀, hb₀] at hvu
    rw [hv₁ z J₀ J' hJ₀ hJ', hrel _ _ z J' J J₀ hJ' hJ hJ₀, hvu _ ((TK V).hom ≫ spMap θ) z J₀ J hJ₀ hJ, hsqQ,
      Category.assoc ((TK V).hom) (spMap θ) (spMap iw), hcomp, _root_.mul_assoc]

end GlobalTheory.PullFrom

end
