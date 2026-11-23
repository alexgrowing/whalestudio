import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AgreeOfCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtIffStalks
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFamFieldPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFamOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSecPull
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralOfPullAl

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigidSections

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FamFieldPull

section General

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {Φ : X' ⟶ X} {K : Type} [Fintype K]

theorem exists_invIso (w : LB.Iso L' (L.pull Φ)) (hw : PGen w) (Ψ : X ⟶ X') (hΨ : Ψ ≫ Φ = 𝟙 X) :
    ∃ v : LB.Iso L (L'.pull Ψ), PGen v ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (j : L.ι) (k : L'.ι),
      Ψ (r z) ∈ L'.U k → r z ∈ L.U j → Geo.Tor.gw v r z k j = (Geo.Tor.gw w (r ≫ Ψ) z j k)⁻¹ := by
  have hp : ∀ x : X, Φ (Ψ x) = x := fun x => congrArg (fun q : X ⟶ X => q x) hΨ
  have le : ∀ (j : L.ι) (k : L'.ι), (L'.pull Ψ).U (fun _ => k) ⊓ L.U j ≤
      Ψ ⁻¹ᵁ ((L.pull Φ).U (fun _ => j) ⊓ L'.U k) := fun j k x hx =>
    ⟨mem_pull.2 (by rw [hp]; exact hx.2), mem_pull.1 hx.1⟩
  let v : LB.Iso L (L'.pull Ψ) :=
    ⟨fun p => (res (le p.2 (p.1 PUnit.unit)) (pullU Ψ _ (w.s (fun _ => p.2, p.1 PUnit.unit))))⁻¹⟩
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (j : L.ι) (k : L'.ι),
      Ψ (r z) ∈ L'.U k → r z ∈ L.U j → Geo.Tor.gw v r z k j = (Geo.Tor.gw w (r ≫ Ψ) z j k)⁻¹ :=
    fun Z r z j k hk hj => by
      have hm : r z ∈ (L'.pull Ψ).U (fun _ => k) ⊓ L.U j := ⟨mem_pull.2 hk, hj⟩
      exact (map_inv _ _).trans (congrArg (·⁻¹) ((gm_res r z (le j k) hm _).trans (gm_pull r Ψ z _ (le j k hm) _)))
  refine ⟨v, fun Z r z k k' j j' hk hk' hj hj' => ?_, hv⟩
  have e := hw Z (r ≫ Ψ) z j j' k k' (show Φ (Ψ (r z)) ∈ _ by rw [hp]; exact hj)
    (show Φ (Ψ (r z)) ∈ _ by rw [hp]; exact hj') hk hk'
  rw [Category.assoc, hΨ, Category.comp_id] at e
  rw [hv Z r z j k hk hj, hv Z r z j' k' hk' hj', e]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_secPush (w : LB.Iso L' (L.pull Φ)) (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) [IsIso Φ]
    (φ' : K → (Y' ⟶ X')) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y) [IsIso h] (hc : ∀ κ, φ' κ ≫ Φ = h ≫ φ κ)
    (a : LB.Sec (LB.LinComb L' φ' ε)) : ∃ s, IsSecPull w φ' φ ε h a s := by
  obtain ⟨v, hv, e⟩ := exists_invIso w ((isGen_iff w).1 hw) (inv Φ) (IsIso.inv_hom_id Φ)
  have hc' : ∀ κ, φ κ ≫ inv Φ = inv h ≫ φ' κ := fun κ => by
    rw [IsIso.comp_inv_eq, Category.assoc, hc, IsIso.inv_hom_id_assoc]
  have hc'' : ∀ κ, h ≫ φ κ ≫ inv Φ = φ' κ := fun κ => by rw [hc', IsIso.hom_inv_id_assoc]
  obtain ⟨s, hs, -⟩ := SecPull.existsUnique_secPull X' X Y' Y L' L (inv Φ) hL' hL v ((isGen_iff v).2 hv) K φ φ' ε
    (inv h) hc' a
  refine ⟨s, fun Z r z p q hp hq => ?_⟩
  have m₁ : ∀ κ, (inv Φ) (φ κ ((r ≫ h) z)) ∈ L'.U (q κ) := fun κ => by
    show (h ≫ φ κ ≫ inv Φ) (r z) ∈ _
    rw [hc'']; exact hq κ
  have m₂ : ∀ κ, φ κ ((r ≫ h) z) ∈ L.U (p κ) := fun κ => by
    show (h ≫ φ κ) (r z) ∈ _
    rw [← hc]; exact hp κ
  have e₁ := hs Z (r ≫ h) z q p m₁ m₂
  rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id,
    Finset.prod_congr rfl fun κ _ => congrArg (· ^ ε κ) (e Z ((r ≫ h) ≫ φ κ) z (p κ) (q κ) (m₁ κ) (m₂ κ))] at e₁
  simp only [Category.assoc, hc'', inv_zpow, Finset.prod_inv_distrib] at e₁
  rw [e₁, Units.mul_inv_cancel_left]

end General

section Fam

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} (hD : IsPullDeg (RingHom.id R) D D')

instance isIso_prA : IsIso (prA hD) := by
  have : IsIso (specOf (RingHom.id R)) := by rw [specOf_id]; infer_instance
  have : IsIso hD.e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map hD.e.hom))
  infer_instance

theorem prA_over : prA hD ≫ D.P.A.hom = D'.P.A.hom ≫ specOf (RingHom.id R) := by
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (· ≫ _) (Over.w hD.e.hom)

def prO : D'.P.A ⟶ D.P.A := Over.homMk (prA hD) (by rw [prA_over, specOf_id]; exact Category.comp_id _)

instance isIso_prO : IsIso (prO hD) := by
  have : IsIso ((Over.forget _).map (prO hD)) := isIso_prA hD
  exact isIso_of_reflects_iso _ (Over.forget _)

theorem famφB_pr (x : D'.X) (a : Fin 4) : D'.famφB x a ≫ prA hD = prA hD ≫ D.famφB (hD.xe x) a := by
  have e : (𝟙 D'.P.A : D'.P.A ⟶ D'.P.A).left ≫ prA hD = prA hD ≫ (𝟙 D.P.A : D.P.A ⟶ D.P.A).left :=
    (Category.id_comp _).trans (Category.comp_id _).symm
  fin_cases a
  · exact e
  · exact mul_left_pr hD _ (prA_over hD) e (cPoint_left_pr hD _ (prA_over hD) x)
  · exact cPoint_left_pr hD _ (prA_over hD) x
  · exact one_left_pr hD _ (prA_over hD)

variable (F : Type) [Field F] [Algebra (FractionRing R) F]

def prF : (DegPre.BF D' F).left ⟶ (DegPre.BF D F).left := (TF (R := R) F ◁ prO hD).left

instance isIso_prF : IsIso (prF hD F) := inferInstanceAs (IsIso ((Over.forget _).map (TF (R := R) F ◁ prO hD)))

theorem prF_fst : prF hD F ≫ (fst (TF (R := R) F) D.P.A).left = (fst (TF (R := R) F) D'.P.A).left :=
  congrArg (fun q => q.left) (whiskerLeft_fst (TF (R := R) F) (prO hD))

theorem prF_snd : prF hD F ≫ (DegPre.prB D F).left = (DegPre.prB D' F).left ≫ prA hD :=
  congrArg (fun q => q.left) (whiskerLeft_snd (TF (R := R) F) (prO hD))

theorem tf_over : (TF (R := R) F).hom ≫ specOf (RingHom.id R) = (TF (R := R) F).hom := by
  rw [specOf_id]; exact Category.comp_id _

def FamRel {k : ℕ} (s' : ∀ x : D'.X, LB.Sec (LB.LinComb D'.P.L (DegPre.famφ D' F x) (DegPre.famε k)))
    (s : ∀ x : D.X, LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F x) (DegPre.famε k))) : Prop :=
  ∀ x, IsSecPull hD.w (DegPre.famφ D' F x) (DegPre.famφ D F (hD.xe x)) (DegPre.famε k) (prF hD F) (s' x)
    (s (hD.xe x))

theorem push_fe (hG : GlobalFnsSt) (k : ℕ) (s' : Fam D' F k)
    (s : ∀ x : D.X, LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F x) (DegPre.famε k)))
    (hs : FamRel hD F s'.s s) : DegPre.FamFE D F k s := by
  have hT := tf_over (R := R) F
  have h₁ := prF_fst hD F
  have h₂ := prF_snd hD F
  intro mu₀ α₀
  obtain ⟨mu, rfl⟩ := hD.xe.surjective mu₀
  obtain ⟨α, rfl⟩ := hD.xe.surjective α₀
  intro u hu hc
  obtain ⟨u', hu', hc'⟩ := (gen_fe (D := D') (F := F) hG k mu α).1
  refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
  obtain ⟨J', hJ'⟩ := BoxFamily.exists_good_at (Z := (DegPre.BF D F).left) D'.P.isLB y
  have e₁ := (hs (α + k • mu)).val (famφ_pr hD F hT h₁ h₂ _) (inv (prF hD F)) y hJ hJ'
  have e₂ := (hs α).val (famφ_pr hD F hT h₁ h₂ _) (inv (prF hD F) ≫ (DegPre.trF D' F mu).left) y hJ hJ'
  have e₃ := gen_pr hD F hT h₁ h₂ hG k α mu u' hu' hc' u hu hc (inv (prF hD F)) y hJ hJ'
  have e₄ := (secRel_iff D'.P.isLB _ _ _ _ _ _ _ _ _ u').1 (s'.fe _ _ u' hu' hc') _ (inv (prF hD F)) y J' hJ'
  have e₅ : (∏ a, wGerm hD.w y J J' (inv (prF hD F) ≫ DegPre.deltaφ D' F k α mu a) ^ DegPre.deltaε k a) =
      (∏ a, wGerm hD.w y J J' (inv (prF hD F) ≫ DegPre.famφ D' F (α + k • mu) a) ^ DegPre.famε k a) *
      (∏ a, wGerm hD.w y J J' ((inv (prF hD F) ≫ (DegPre.trF D' F mu).left) ≫ DegPre.famφ D' F α a) ^
        DegPre.famε k a)⁻¹ := by
    simp only [Category.assoc]
    exact prod_sum₂ (K := Fin 4) (K' := Fin 4) _ rfl (prod_neg _ _ rfl)
  rw [Category.assoc (inv _) _ (prF hD F), trF_pr hD F hT h₁ h₂, IsIso.inv_hom_id_assoc] at e₂
  rw [IsIso.inv_hom_id] at e₁ e₃
  rw [← map_nsmul, ← map_add, e₁, e₄, Category.id_comp, e₂, e₃, e₅]
  exact (BoxFamily.unit_shuffle _ _ _ _).symm

theorem exists_pull (hG : GlobalFnsSt) (k : ℕ) (s : Fam D F k) : ∃ s' : Fam D' F k, FamRel hD F s'.s s.s :=
  exists_fam_field_pull hG R R _ D D' hD F (fun _ => rfl) _ (prF_fst hD F) (prF_snd hD F) k s

theorem exists_push (hG : GlobalFnsSt) (k : ℕ) (s' : Fam D' F k) : ∃ s : Fam D F k, FamRel hD F s'.s s.s := by
  have ex : ∀ y : D.X, ∃ t : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F y) (DegPre.famε k)), ∀ x, hD.xe x = y →
      IsSecPull hD.w (DegPre.famφ D' F x) (DegPre.famφ D F y) (DegPre.famε k) (prF hD F) (s'.s x) t := fun y => by
    obtain ⟨x, rfl⟩ := hD.xe.surjective y
    obtain ⟨t, ht⟩ := exists_secPush hD.w hD.w_gen D.P.isLB D'.P.isLB _ _ (DegPre.famε k) (prF hD F)
      (famφ_pr hD F (tf_over F) (prF_fst hD F) (prF_snd hD F) x) (s'.s x)
    refine ⟨t, fun x' e => ?_⟩
    obtain rfl := hD.xe.injective e
    exact ht
  choose s hs using ex
  exact ⟨⟨s, push_fe hD F hG k s' s fun x => hs _ x rfl⟩, fun x => hs _ x rfl⟩

theorem integral_rel {k : ℕ} {s' : ∀ x : D'.X, LB.Sec (LB.LinComb D'.P.L (DegPre.famφ D' F x) (DegPre.famε k))}
    {s : ∀ x : D.X, LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F x) (DegPre.famε k))} (hs : FamRel hD F s' s)
    {r r' : R} {f : ∀ α, D.SecB k α} {f' : ∀ α, D'.SecB k α}
    (hf : ∀ α, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) (s α) (D.famφB α) (DegPre.famε k) (f α)
      (DegPre.prB D F).left (scal (DegPre.BF D F).hom r))
    (hf' : ∀ α, GeneratorPullback.SecScal D'.P.L (DegPre.famφ D' F α) (DegPre.famε k) (s' α) (D'.famφB α) (DegPre.famε k) (f' α)
      (DegPre.prB D' F).left (scal (DegPre.BF D' F).hom r')) (x : D'.X) :
    IsSecPull hD.w (D'.famφB x) (D.famφB (hD.xe x)) (DegPre.famε k) (prA hD)
      (SecOps.secScale (scal D'.P.A.hom r) (f' x)) (SecOps.secScale (scal D.P.A.hom r') (f (hD.xe x))) := by
  obtain ⟨g, hg, -⟩ := SecPull.existsUnique_secPull _ _ _ _ D.P.L D'.P.L _ D.P.isLB D'.P.isLB hD.w hD.w_gen _
    (D'.famφB x) (D.famφB (hD.xe x)) (DegPre.famε k) (prA hD) (famφB_pr hD x)
    (SecOps.secScale (scal D.P.A.hom r') (f (hD.xe x)))
  have sc : ∀ {X Y Z : Scheme.{0}} {L : LB X} {φ : Fin 4 → (Y ⟶ X)} {ε : Fin 4 → ℤ} (p : Y ⟶ Spec (CommRingCat.of R))
      (c : R) (t : LB.Sec (LB.LinComb L φ ε)) (q : Z ⟶ Y) (z : Z) {J}, Good L z J →
      sval (SecOps.secScale (scal p c) t) q z J = cst (q ≫ p) z c * sval t q z J := fun p c t q z J hJ =>
    (gs_mul q z _ (hJ.mem _ q) _ _).trans (congrArg (· * _)
      ((gs_res q z le_top (hJ.mem _ q) _).trans (ExpInt.gs_scal p q z c)))
  have e : SecOps.secScale (scal D'.P.A.hom r) (f' x) = g := by
    refine SecOps.sec_ext (PullIntegral.sec_ext_of_inj D'.P.isLB (DegPre.prB D' F).left
      (PullIntegral.prB_app_injective D' F) fun y J' hJ' => ?_)
    obtain ⟨J, hJ⟩ := BoxFamily.exists_good_at (Z := (DegPre.BF D' F).left) D.P.isLB y
    have e₁ := IsSecPull.val hg (famφB_pr hD x) (𝟙 _ ≫ (DegPre.prB D' F).left) y hJ hJ'
    have e₂ := (hs x).val (famφ_pr hD F (tf_over F) (prF_fst hD F) (prF_snd hD F) x) (𝟙 _) y hJ hJ'
    have e₃ := ExpInt.secScal_sval (hf (hD.xe x)) (𝟙 _ ≫ prF hD F) y hJ
    have e₄ := ExpInt.secScal_sval (hf' x) (𝟙 _) y hJ'
    have a₁ : (𝟙 _ ≫ (DegPre.prB D' F).left) ≫ prA hD = (𝟙 _ ≫ prF hD F) ≫ (DegPre.prB D F).left := by
      rw [Category.assoc, Category.assoc, prF_snd]
    have a₂ : ∀ κ, (𝟙 _ ≫ (DegPre.prB D' F).left) ≫ D'.famφB x κ = 𝟙 _ ≫ DegPre.famφ D' F x κ := fun κ => by
      rw [Category.id_comp, Category.id_comp, FamPull.comp_famφB]
      fin_cases κ
      exacts [rfl, congrArg (fun q : DegPre.BF D' F ⟶ D'.P.A => q.left) (mul_comm (cP D' _ x) (DegPre.prB D' F)), rfl, rfl]
    have b₀ : prF hD F ≫ (DegPre.BF D F).hom = (DegPre.BF D' F).hom := Over.w (TF (R := R) F ◁ prO hD)
    have b₁ : ((𝟙 _ ≫ prF hD F) ≫ (DegPre.prB D F).left) ≫ D.P.A.hom = (DegPre.BF D' F).hom := by
      rw [Category.id_comp, Category.assoc, Over.w, b₀]
    have b₂ : (𝟙 _ ≫ prF hD F) ≫ (DegPre.BF D F).hom = (DegPre.BF D' F).hom := by rw [Category.id_comp, b₀]
    have b₃ : (𝟙 _ ≫ (DegPre.prB D' F).left) ≫ D'.P.A.hom = (DegPre.BF D' F).hom := by
      rw [Category.id_comp, Over.w]
    rw [a₁, sc _ _ _ _ _ hJ, e₃, e₂, ExpInt.gs_scal, b₁, b₂] at e₁
    simp only [a₂] at e₁
    rw [sc _ _ _ _ _ hJ', e₄, ExpInt.gs_scal, b₃, Category.id_comp (DegPre.BF D' F).hom]
    refine (Units.mul_right_inj (∏ κ, wGerm hD.w y J J' (𝟙 _ ≫ DegPre.famφ D' F x κ) ^ DegPre.famε k κ)).1
      (Eq.trans ?_ e₁)
    ring
  rw [e]
  exact hg

end Fam

section Level

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G G' : Over (Spec (CommRingCat.of R))}
  [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (U : UnifPre I D A G) (U' : UnifPre I D' A' G')
  (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre)

theorem prod_fam_coord (e k : ℕ) (x : D.toPre.X) {V : Type} [CommGroup V]
    (h : ((thickObj R I e G).left ⟶ D.toPre.P.A.left) → V) :
    (∏ a, h (pGl U e ≫ D.toPre.famφB x a) ^ DegPre.famε k a) * ∏ a, h (Oφl U e x a) ^ Oinvε a = h (pGl U e) ^ k := by
  have p := FamPull.prod_famB D.toPre (U.gt e).pG x k h
  have q : ∏ a, h (Oφl U e x a) ^ Oinvε a = h ((U.gt e).pG * cP D.toPre _ x).left ^ (-1 : ℤ) *
      h (cP D.toPre ((Over.map (thick R I e)).obj (thickObj R I e G)) x).left ^ (1 : ℤ) * h (pGl U e) ^ (1 : ℤ) *
      h (1 : (Over.map (thick R I e)).obj (thickObj R I e G) ⟶ D.toPre.P.A).left ^ (-1 : ℤ) := Fin.prod_univ_four _
  refine (congrArg₂ (· * ·) p q).trans ?_
  rw [mul_comm (U.gt e).pG]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
  module

def Agree (e k : ℕ) (j : (thickObj R I e G').left ⟶ (thickObj R I e G).left) (σ : H0 U.LG.L k) (σ' : H0 U'.LG.L k) :
    Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι)
    (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), prA hD (pGl U' e (r z)) ∈ D.toPre.P.L.U jM → pGl U' e (r z) ∈ D'.toPre.P.L.U jM' →
    fGl I G e (j (r z)) ∈ U.LG.L.U jL → fGl I G' e (r z) ∈ U'.LG.L.U jL' →
    (wv U e (r ≫ j) z jM jL ^ k).val * sv U k σ (r ≫ j ≫ fGl I G e) z jL =
      ((Geo.Tor.gw hD.w (r ≫ pGl U' e) z jM jM' * wv U' e r z jM' jL') ^ k).val * sv U' k σ' (r ≫ fGl I G' e) z jL'

theorem agree_of_expandsAt (e k : ℕ) (j : (thickObj R I e G').left ⟶ (thickObj R I e G).left)
    (hp : pGl U' e ≫ prA hD = j ≫ pGl U e)
    (hO : ∀ x κ, Oφl U' e x κ ≫ prA hD = j ≫ Oφl U e (hD.xe x) κ)
    (ht : ∀ x, PMaps hD.w (Oφl U' e x) (Oφl U e (hD.xe x)) Oinvε (tG U' e x) (tG U e (hD.xe x)) j)
    {σ : H0 U.LG.L k} {σ' : H0 U'.LG.L k} {f : ∀ α, D.toPre.SecB k α} {f' : ∀ α, D'.toPre.SecB k α}
    (hE : U.ExpandsAt e k σ f) (hE' : U'.ExpandsAt e k σ' f')
    (hf : ∀ x, IsSecPull hD.w (D'.toPre.famφB x) (D.toPre.famφB (hD.xe x)) (DegPre.famε k) (prA hD) (f' x)
      (f (hD.xe x))) : Agree U U' hD e k j σ σ' := by
  classical
  intro Z r z jM jM' jL jL' hM hM' hL hL'
  obtain ⟨J, hJ, eJ⟩ := exists_good D.toPre.P.L D.toPre.P.isLB z (fun _ : Unit => (r ≫ pGl U' e) ≫ prA hD)
    (fun _ => jM) (fun _ _ _ => rfl) (fun _ => hM)
  obtain ⟨J', hJ', eJ'⟩ := exists_good D'.toPre.P.L D'.toPre.P.isLB z (fun _ : Unit => r ≫ pGl U' e)
    (fun _ => jM') (fun _ _ _ => rfl) (fun _ => hM')
  obtain rfl := eJ ()
  obtain rfl := eJ' ()
  obtain ⟨S, H⟩ := expandsAt_val U e k σ f hE
  obtain ⟨S', H'⟩ := expandsAt_val U' e k σ' f' hE'
  obtain ⟨z₁, s₁⟩ := H Z (r ≫ j) z J hJ
  obtain ⟨z₂, s₂⟩ := H' Z r z J' hJ'
  have a : (r ≫ j) ≫ pGl U e = (r ≫ pGl U' e) ≫ prA hD := by rw [Category.assoc, Category.assoc, hp]
  have vf : ∀ x, sval (f (hD.xe x)) ((r ≫ j) ≫ pGl U e) z J =
      (∏ κ, wGerm hD.w z J J' (r ≫ pGl U' e ≫ D'.toPre.famφB x κ) ^ DegPre.famε k κ).val *
        sval (f' x) (r ≫ pGl U' e) z J' := fun x => by
    rw [a, (hf x).val (famφB_pr hD x) _ z hJ hJ']
    simp only [Category.assoc]
  have term : ∀ x, sval (f (hD.xe x)) ((r ≫ j) ≫ pGl U e) z J * (val (tG U e (hD.xe x)) (r ≫ j) z J).val =
      (wGerm hD.w z J J' (r ≫ pGl U' e) ^ k).val *
        (sval (f' x) (r ≫ pGl U' e) z J' * (val (tG U' e x) r z J').val) := fun x => by
    rw [vf, pmaps_val (ht x) (hO x) r z hJ hJ',
      ← prod_fam_coord U' e k x (fun q => wGerm hD.w z J J' (r ≫ q)), Units.val_mul, Units.val_mul]
    ring
  have e₁ := s₁ jL hL
  have e₂ := s₂ jL' hL'
  rw [a, Category.assoc r j (fGl I G e)] at e₁
  rw [e₁, mul_pow, Units.val_mul, _root_.mul_assoc, e₂, ← a, Finset.mul_sum]
  let T : Finset D'.toPre.X := S' ∪ S.map hD.xe.symm.toEquiv.toEmbedding
  have t₁ : S ⊆ T.map hD.xe.toEquiv.toEmbedding := fun y hy =>
    Finset.mem_map.2 ⟨hD.xe.symm y, Finset.mem_union_right _ (Finset.mem_map.2 ⟨y, hy, rfl⟩), hD.xe.apply_symm_apply y⟩
  rw [Finset.sum_subset t₁ (fun y _ hy => by rw [z₁ y hy, zero_mul]),
    Finset.sum_subset (Finset.subset_union_left : S' ⊆ T) (fun x _ hx => by rw [z₂ x hx, zero_mul, mul_zero]),
    Finset.sum_map]
  refine Finset.sum_congr rfl fun x _ => (term x).trans ?_
  rw [a]; rfl

theorem expandsAt_scale {e k : ℕ} {σ : H0 U.LG.L k} {f : ∀ α, D.toPre.SecB k α} (h : U.ExpandsAt e k σ f) (c : R) :
    U.ExpandsAt e k (SecOps.secScale (scal G.hom c) σ)
      (fun α => SecOps.secScale (scal D.toPre.P.A.hom c) (f α)) :=
  expandsAt_linear R I D A G U k e 1 (fun _ => c) (fun _ => σ) (fun _ => f) _ _ (fun _ => h)
    (fun _ => by rw [Fin.sum_univ_one]; rfl) (fun _ _ => by rw [Fin.sum_univ_one]; rfl)

theorem exists_restrict (k : ℕ) (σ : H0 U.LG.L k) : ∃ s : U.SecK k,
    GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ)) s
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ (pullback.fst G.hom (jK R)) 1 := by
  obtain ⟨s, hs⟩ := exists_sec U.LG.isLB (φ' := fun _ : Fin 1 => pullback.fst G.hom (jK R)) (ε' := fun _ => (k : ℤ))
    (fun V _ h => by simp only [Category.comp_id]) (pullSec U.LG.L _ _ σ (pullback.fst G.hom (jK R)))
  exact ⟨s, SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J hJ =>
    ((hs _ _ y J hJ).trans (SectionScalarValuation.sval_pullSec _ _ _ _ _ y hJ)).symm⟩

theorem scale_of_restrict {k : ℕ} {σ₀ σ : H0 U.LG.L k} {s : U.SecK k} {r : R}
    (h₀ : GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ)) s
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ₀ (pullback.fst G.hom (jK R)) 1)
    (h : GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ)) s
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ (pullback.fst G.hom (jK R))
      (scal (pullback.snd G.hom (jK R) ≫ jK R) r)) (c : R) (i) :
    (SecOps.secScale (scal G.hom c) σ).f i = resTop _ (scal G.hom (c * r)) * σ₀.f i := by
  have := U.smooth
  have : Flat G.hom := inferInstance
  exact ExpInt.secIsMul_trans (p := G.hom) (a := c) (ρ := SecOps.secScale (scal G.hom c) σ) (fun _ => rfl)
    (ExpInt.secIsMul_of_generic G U.LG.isLB k σ₀ σ s r h₀ h) i

end Level

end GlobalTheory.RigidSections

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.RigidSections in

theorem integral_sections_correspond : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (I : Ideal R), AdmBase R I → I = IsLocalRing.maximalIdeal R → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G), (∀ e : ℕ, IsMonHom (j e).hom ∧ thickMap R I e G' ≫ (j (e + 1)).hom.left = (j e).hom.left ≫ thickMap R I e G ∧ (U'.gt e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧ PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((U'.gt e).t x) ((U.gt e).t (hD.xe x)) (j e).hom.left) → ∀ (k : ℕ), 1 ≤ k → (∀ σ₀ : H0 U.LG.L k, ∃ (c : R) (σ' : H0 U'.LG.L k) (σ : H0 U.LG.L k), c ≠ 0 ∧ (∀ i, σ.f i = resTop _ (scal G.hom c) * σ₀.f i) ∧ (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left ((j e).hom.left (r z)) ∈ U.LG.L.U jL → (fstG I e G').left (r z) ∈ U'.LG.L.U jL' → (Geo.Tor.gw (U.w e) (r ≫ (j e).hom.left) z jM (fun _ => jL) ^ k).val * gs (r ≫ (j e).hom.left ≫ (fstG I e G).left) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (σ.f (fun _ => jL)) = ((Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL')) ^ k).val * gs (r ≫ (fstG I e G').left) z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL')) (σ'.f (fun _ => jL')))) ∧ ∀ σ₀ : H0 U'.LG.L k, ∃ (c : R) (σ' : H0 U'.LG.L k) (σ : H0 U.LG.L k), c ≠ 0 ∧ (∀ i, σ'.f i = resTop _ (scal G'.hom c) * σ₀.f i) ∧ (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left ((j e).hom.left (r z)) ∈ U.LG.L.U jL → (fstG I e G').left (r z) ∈ U'.LG.L.U jL' → (Geo.Tor.gw (U.w e) (r ≫ (j e).hom.left) z jM (fun _ => jL) ^ k).val * gs (r ≫ (j e).hom.left ≫ (fstG I e G).left) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (σ.f (fun _ => jL)) = ((Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL')) ^ k).val * gs (r ≫ (fstG I e G').left) z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL')) (σ'.f (fun _ => jL'))) := by
  intro hL _ R _ _ _ I _ _ D D' A A' G G' _ _ _ _ _ _ U U' hD j hj k hk
  have ag : ∀ {σ : H0 U.LG.L k} {σ' : H0 U'.LG.L k} {r r' : R} {f : ∀ α, D.toPre.SecB k α}
      {f' : ∀ α, D'.toPre.SecB k α} {F : Fam D.toPre (FractionRing R) k} {F' : Fam D'.toPre (FractionRing R) k},
      FamRel hD _ F'.s F.s →
      (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre _ α) (DegPre.famε k) (F.s α) (D.toPre.famφB α)
        (DegPre.famε k) (f α) (DegPre.prB D.toPre _).left (scal (DegPre.BF D.toPre _).hom r)) →
      (∀ α, GeneratorPullback.SecScal D'.toPre.P.L (DegPre.famφ D'.toPre _ α) (DegPre.famε k) (F'.s α) (D'.toPre.famφB α)
        (DegPre.famε k) (f' α) (DegPre.prB D'.toPre _).left (scal (DegPre.BF D'.toPre _).hom r')) →
      (∀ e, U.ExpandsAt e k σ f) → (∀ e, U'.ExpandsAt e k σ' f') → ∀ e,
      Agree U.toUnifPre U'.toUnifPre hD e k (j e).hom.left (SecOps.secScale (scal G.hom r') σ)
        (SecOps.secScale (scal G'.hom r) σ') := fun hF hf hf' hE hE' e =>
    agree_of_expandsAt _ _ hD e k _ (hj e).2.2.1 (fun x => ((hj e).2.2.2 x).1) (fun x => ((hj e).2.2.2 x).2)
      (expandsAt_scale _ (hE e) _) (expandsAt_scale _ (hE' e) _) (integral_rel hD _ hF hf hf')
  constructor
  · intro σ₀
    obtain ⟨s, hs⟩ := exists_restrict U.toUnifPre k σ₀
    obtain ⟨F, ⟨r, hr, σ, f, h₁, h₂, h₃⟩, -⟩ := (U.expand k hk).1 s
    obtain ⟨F', hF⟩ := exists_pull hD _ hL.globalFns k F
    obtain ⟨s', ⟨r', hr', σ', f', h₁', h₂', h₃'⟩, -⟩ := (U'.expand k hk).2 F'
    exact ⟨r' * r, _, _, mul_ne_zero hr' hr, scale_of_restrict _ hs h₁ r', ag hF h₂ h₂' h₃ h₃'⟩
  · intro σ₀
    obtain ⟨s', hs⟩ := exists_restrict U'.toUnifPre k σ₀
    obtain ⟨F', ⟨r', hr', σ', f', h₁', h₂', h₃'⟩, -⟩ := (U'.expand k hk).1 s'
    obtain ⟨F, hF⟩ := exists_push hD _ hL.globalFns k F'
    obtain ⟨s, ⟨r, hr, σ, f, h₁, h₂, h₃⟩, -⟩ := (U.expand k hk).2 F
    exact ⟨r * r', _, _, mul_ne_zero hr hr', scale_of_restrict _ hs h₁' r, ag hF h₂ h₂' h₃ h₃'⟩

end GlobalTheory
