import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section
namespace GlobalTheory.Mum.TensTor.PsiVal

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem stalk_gm {Z Y : Scheme.{0}} (f : Z ⟶ Y) {X : Scheme.{0}} (r : Y ⟶ X) (z : Z) (U : X.Opens) (h : r (f z) ∈ U)
    (a : Γ(X, U)ˣ) : (f.stalkMap z).hom (gm r (f z) U a).val = (gm (f ≫ r) z U a).val := by
  rw [gm_val r (f z) U h, gm_val (f ≫ r) z U h]
  have := Scheme.Hom.germ_stalkMap_apply f (r ⁻¹ᵁ U) z h ((r.app U).hom a.val)
  rw [this]
  rfl

theorem stalk_val {Z Y X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (f : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι)
    (h : f z ∈ LB.wchart L φ (fun k => J (f ≫ φ k))) :
    (f.stalkMap z).hom (val t (𝟙 Y) (f z) (fun ψ => J (f ≫ ψ))).val = (val t f z J).val := by
  rw [val_of t (𝟙 Y) (f z) _ (fun k => J (f ≫ φ k)) (fun k => by simp only [Category.id_comp])]
  refine (stalk_gm f (𝟙 Y) z _ h _).trans ?_
  rw [Category.comp_id]
  rfl

theorem toStk_vF {F : Type} [Field F] {Y X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) (z : Sp F) (J : (Sp F ⟶ X) → L.ι) (hJ : Good L z J) :
    toStk z (vF t r J) = (val t r z J).val :=
  toStk_valF r _ z (hJ.mem φ r) _

theorem toUnit_left {S : Scheme.{0}} (X : Over S) : (toUnit X).left = X.hom := by
  simpa using Over.w (toUnit X)

theorem stalkU {Z Y X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (f : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) :
    Units.map (f.stalkMap z).hom.toMonoidHom (val t (𝟙 Y) (f z) (fun ψ => J (f ≫ ψ))) = val t f z J :=
  Units.ext (stalk_val t f z J (hJ.mem φ f))

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
  {F : Type} [Field F] [Algebra (FractionRing R) F] {N N' : NumD F}

theorem good_of (ν : NumOf D F N) (z : Sp F) : Good D.P.L z ν.J := fun ψ => (top_le_iff_mem ψ _ z).1 (ν.good ψ)

theorem goodK_of (ν : NumOf D F N) (z : Sp F) : Good D.P.L (jFK (R := R) F z) (fun ψ => ν.J (jFK (R := R) F ≫ ψ)) :=
  fun ψ => (top_le_iff_mem (jFK (R := R) F ≫ ψ) _ z).1 (ν.good _)

theorem wv_toStk (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (x : N'.A) (z : Sp F)
    (p : Sp F ⟶ D'.P.A.left) (hp : (ν'.eA x).left = p) :
    toStk z (wv T ν ν' x) = (gm p z _ (T.w.s (fun k => ν.J (p ≫ tensφ T.pr k), ν'.J p))).val := by
  subst hp
  exact toStk_valF _ _ z (show (ν'.eA x).left z ∈ LB.wchart D.P.L (tensφ T.pr) (fun k => ν.J ((ν'.eA x).left ≫ tensφ T.pr k)) ⊓
    D'.P.L.U (ν'.J (ν'.eA x).left) from ⟨(good_of ν z).mem _ _, good_of ν' z _⟩) _

example : True := trivial

theorem rig_val (ν : NumOf D F N) (z : Sp F) :
    val (LB.pullGen D.P.L _ _ D.rig (toUnit (TK R)).left) (jFK (R := R) F) z ν.J = val D.rig (jFK (R := R) F ≫ jK R) z ν.J := by
  rw [val_pull (good_of ν z), toUnit_left]
  rfl

theorem psi_m (ν : NumOf D F N) (z : Sp F) (χ : N.X) :
    Units.map (toStk z).toMonoidHom (N.ψ χ) = val (D.psi (ν.eX χ)) (jFK (R := R) F) z ν.J * val D.rig (jFK (R := R) F ≫ jK R) z ν.J := by
  apply Units.ext
  change toStk z (N.ψ χ : F) = _
  rw [ν.ψ_eq χ, map_mul, toStk_vF _ _ z _ (good_of ν z), toStk_vF _ _ z _ (good_of ν z)]
  rfl

theorem tau_m (ν : NumOf D F N) (z : Sp F) (a b : N.X) :
    val (D.tau (ν.eX a) (ν.eX b)) (jFK (R := R) F) z ν.J = Units.map (toStk z).toMonoidHom (N.τ a b) := by
  have hG := good_of ν z
  unfold DegPre.tau DegPre.rigK
  rw [val_mul hG, val_mul hG, val_mul hG, val_inv, val_inv, val_inv, rig_val ν z]
  rw [NumD.τ, map_div, map_div, psi_m ν z, psi_m ν z, psi_m ν z, map_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_inv]
  abel

theorem pt_eq (ν' : NumOf D' F N') (χ : N'.X) : (ν'.eA (N'.c χ)).left = jFK (R := R) F ≫ D'.xK (ν'.eX χ) := by
  rw [ν'.c_eq]
  simp only [DegPre.cF, DegPre.xK, ptK, Over.comp_left, toUnit_left]
  rfl

theorem w_stalk (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (z : Sp F) (y : D'.X) :
    Units.map (Scheme.Hom.stalkMap (jFK (R := R) F) z).hom.toMonoidHom
      (gm (D'.xK y) (jFK (R := R) F z) _ (T.w.s (fun k => ν.J (jFK (R := R) F ≫ D'.xK y ≫ tensφ T.pr k),
        ν'.J (jFK (R := R) F ≫ D'.xK y)))) =
    gm (jFK (R := R) F ≫ D'.xK y) z _ (T.w.s (fun k => ν.J ((jFK (R := R) F ≫ D'.xK y) ≫ tensφ T.pr k),
        ν'.J (jFK (R := R) F ≫ D'.xK y))) := by
  have e : (fun k => ν.J ((jFK (R := R) F ≫ D'.xK y) ≫ tensφ T.pr k)) =
      (fun k => ν.J (jFK (R := R) F ≫ D'.xK y ≫ tensφ T.pr k)) := funext fun k => by rw [Category.assoc]
  rw [e]
  apply Units.ext
  refine stalk_gm (jFK (R := R) F) (D'.xK y) z _ ?_ _
  exact (show (jFK (R := R) F ≫ D'.xK y) z ∈ LB.wchart D.P.L (tensφ T.pr) (fun k => ν.J (jFK (R := R) F ≫ D'.xK y ≫ tensφ T.pr k)) ⊓
    D'.P.L.U (ν'.J (jFK (R := R) F ≫ D'.xK y)) from ⟨Set.mem_iInter.2 fun k => by
      have := good_of ν z ((jFK (R := R) F ≫ D'.xK y) ≫ tensφ T.pr k)
      rwa [Category.assoc] at this, good_of ν' z _⟩)

theorem psi_stk (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (z : Sp F) (χ' : N'.X) :
    toStk z (N'.ψ χ' : F) = toStk z (wv T ν ν' (N'.c χ')) *
      toStk z ((∏ i, ∏ j, N.τ (chi T ν ν' χ' i) (chi T ν ν' χ' j) ^ W i j : Fˣ) : F) *
      (val D'.rig (jFK (R := R) F ≫ jK R) z ν'.J).val := by
  have key := T.psi (ν'.eX χ') (jFK (R := R) F z) (fun ψ => ν.J (jFK (R := R) F ≫ ψ)) (fun ψ => ν'.J (jFK (R := R) F ≫ ψ))
    (goodK_of ν z) (goodK_of ν' z)
  have key2 := congrArg (Units.map (Scheme.Hom.stalkMap (jFK (R := R) F) z).hom.toMonoidHom) key
  rw [map_mul, stalkU _ _ z _ (good_of ν' z), w_stalk] at key2
  simp only [map_prod, map_zpow, stalkU _ _ z ν.J (good_of ν z)] at key2
  have hL : toStk z (N'.ψ χ' : F) = (Units.map (toStk z).toMonoidHom (N'.ψ χ')).val := rfl
  have hP : toStk z ((∏ i, ∏ j, N.τ (chi T ν ν' χ' i) (chi T ν ν' χ' j) ^ W i j : Fˣ) : F) =
      (∏ i, ∏ j, val (D.tau (T.xe (ν'.eX χ') i) (T.xe (ν'.eX χ') j)) (jFK (R := R) F) z ν.J ^ W i j).val := by
    change (Units.map (toStk z).toMonoidHom _).val = _
    congr 1
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_zpow, ← tau_m ν z, show ν.eX (chi T ν ν' χ' i) = T.xe (ν'.eX χ') i from ν.eX.apply_symm_apply _,
      show ν.eX (chi T ν ν' χ' j) = T.xe (ν'.eX χ') j from ν.eX.apply_symm_apply _]
  rw [hL, psi_m ν' z χ', hP, wv_toStk T ν ν' _ z _ (pt_eq ν' χ'), key2]
  simp only [Units.val_mul]
  try ring

theorem psi_main (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (χ' : N'.X) :
    (N'.ψ χ' : F) * wv T ν ν' 1 = wv T ν ν' (N'.c χ') * ((∏ i, ∏ j, N.τ (chi T ν ν' χ' i) (chi T ν ν' χ' j) ^ W i j : Fˣ) : F) := by
  obtain ⟨z⟩ : Nonempty (Sp F) := ⟨(default : PrimeSpectrum F)⟩
  have h0 := psi_stk T ν ν' z 0
  have hc : chi T ν ν' 0 = 0 := funext fun i => by
    show ν.eX.symm (T.xe (ν'.eX 0) i) = 0
    rw [map_zero, map_zero, Pi.zero_apply, map_zero]
  have hp : (∏ i, ∏ j, N.τ (chi T ν ν' 0 i) (chi T ν ν' 0 j) ^ W i j : Fˣ) = 1 := by
    rw [hc]
    exact Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => by
      rw [Pi.zero_apply, NumD.τ_zero_left, one_zpow]
  rw [NumD.ψ_zero, NumD.c_zero, hp, Units.val_one, map_one, _root_.mul_one] at h0
  apply (toStk z).injective
  rw [map_mul, map_mul, psi_stk T ν ν' z χ']
  linear_combination (-(toStk z (wv T ν ν' (N'.c χ')) *
      toStk z ((∏ i, ∏ j, N.τ (chi T ν ν' χ' i) (chi T ν ν' χ' j) ^ W i j : Fˣ) : F))) * h0

end GlobalTheory.Mum.TensTor.PsiVal

open GlobalTheory.Mum.TensTor.PsiVal in

theorem GlobalTheory.Mum.TensTor.tensFacts_psi : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N'), ∀ χ', (N'.ψ χ' : F) * wv T ν ν' 1 = wv T ν ν' (N'.c χ') * ((∏ i, ∏ j, N.τ (chi T ν ν' χ' i) (chi T ν ν' χ' j) ^ W i j : Fˣ) : F) := by
  intro R _ _ _ _ D D' r W T F _ _ _ N N' ν ν' χ'
  exact psi_main T ν ν' χ'
