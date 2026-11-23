import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSumPolAV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsumLeftPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastExtra
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValPsiZeroMulRigK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialSumInsertKilledCoordinateComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeInclusionFirstFactorOverAbelianInclusion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialSumCompMonHomEqPartialSum

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd.SumTau

theorem prod_subsets_two {M : Type} [CommMonoid M] (F : ULift.{0} (Finset (Fin 2)) → M) :
    ∏ I, F I = F ⟨∅⟩ * F ⟨{0}⟩ * F ⟨{1}⟩ * F ⟨{0, 1}⟩ := by
  have h : (Finset.univ : Finset (ULift.{0} (Finset (Fin 2)))) = {⟨∅⟩, ⟨{0}⟩, ⟨{1}⟩, ⟨{0, 1}⟩} := by decide
  rw [h, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton, _root_.mul_assoc, _root_.mul_assoc]

def unitAt {X X₁ X₂ Z : Scheme.{0}} {L : LB X} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : X ⟶ X₁} {f₂ : X ⟶ X₂}
    (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) (z : Z) (J : (Z ⟶ X) → L.ι) (J₁ : (Z ⟶ X₁) → L₁.ι)
    (J₂ : (Z ⟶ X₂) → L₂.ι) (f : Z ⟶ X) : (Z.presheaf.stalk z)ˣ :=
  gm f z _ (w.s (extIdx (f₁ := f₁) (f₂ := f₂) (J₁ (f ≫ f₁)) (J₂ (f ≫ f₂)), J f))

theorem unitAt_of {X X₁ X₂ Z : Scheme.{0}} {L : LB X} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : X ⟶ X₁} {f₂ : X ⟶ X₂}
    (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) (z : Z) (J : (Z ⟶ X) → L.ι) (J₁ : (Z ⟶ X₁) → L₁.ι)
    (J₂ : (Z ⟶ X₂) → L₂.ι) (f g : Z ⟶ X) (j : L.ι) (j₁ : L₁.ι) (j₂ : L₂.ι) (hg : g = f) (h : J f = j)
    (h₁ : J₁ (f ≫ f₁) = j₁) (h₂ : J₂ (f ≫ f₂) = j₂) :
    gm g z _ (w.s (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂, j)) = unitAt w z J J₁ J₂ f := by
  subst hg h h₁ h₂
  rfl

theorem mapsAt_unitAt {Y X X₁ X₂ Z : Scheme.{0}} {L : LB X} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : X ⟶ X₁} {f₂ : X ⟶ X₂}
    {w : LB.Iso L (extLB L₁ L₂ f₁ f₂)} {p : Y ⟶ X} {n : ℤ}
    {a : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n))}
    {b₁ : LB.Gen (LB.LinComb L₁ (K := PUnit) (fun _ => p ≫ f₁) (fun _ => n))}
    {b₂ : LB.Gen (LB.LinComb L₂ (K := PUnit) (fun _ => p ≫ f₂) (fun _ => n))} (h : MapsAt₂ w p n a b₁ b₂)
    (r : Z ⟶ Y) {z : Z} {J : (Z ⟶ X) → L.ι} {J₁ : (Z ⟶ X₁) → L₁.ι} {J₂ : (Z ⟶ X₂) → L₂.ι}
    (hJ : Good L z J) (hJ₁ : Good L₁ z J₁) (hJ₂ : Good L₂ z J₂) :
    val b₁ r z J₁ * val b₂ r z J₂ = unitAt w z J J₁ J₂ (r ≫ p) ^ n * val a r z J :=
  (GlobalTheory.MumProd.mapsAt₂_val _ _ _ _ _ _ _ _ _ _ w p n a b₁ b₂ h r z J J₁ J₂ hJ hJ₁ hJ₂).trans
    (congrArg (· ^ n * val a r z J) (unitAt_of w z J J₁ J₂ _ _ _ _ _ rfl rfl
      (by rw [Category.assoc]) (by rw [Category.assoc])))

theorem val_tau {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (D : DegData R I) (a b : D.toPre.X)
    {z : (TK R).left} {J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι} (hJ : Good D.toPre.P.L z J) :
    val ((pol D).tau a b) (𝟙 _) z J = val (D.toPre.psi (a + b)) (𝟙 _) z J * (val (D.toPre.psi a) (𝟙 _) z J)⁻¹ *
      (val (D.toPre.psi b) (𝟙 _) z J)⁻¹ * (val D.toPre.rigK (𝟙 _) z J)⁻¹ := by
  refine ((GlobalTheory.PolDeg.Wit.exists_tau D.toPre a b).choose_spec.2 _ (𝟙 _) z J hJ).trans ?_
  unfold DegPre.tau
  rw [val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_inv]

section Psum

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] {T : Over S} (x : Fin 2 → (T ⟶ G))

theorem psum_empty : psum G x ∅ = toUnit T ≫ η[G] := rfl

theorem psum_zero : psum G x {0} = x 0 := by
  show lift (x 0) (toUnit T ≫ η[G]) ≫ μ[G] = x 0
  exact lift_comp_one_right _ _

theorem psum_one : psum G x {1} = x 1 := by
  show lift (x 1) (toUnit T ≫ η[G]) ≫ μ[G] = x 1
  exact lift_comp_one_right _ _

theorem psum_pair : psum G x {0, 1} = padd G (x 0) (x 1) := by
  show padd G (x 0) (lift (x 1) (toUnit T ≫ η[G]) ≫ μ[G]) = _
  rw [lift_comp_one_right]

theorem comp_padd' {T' : Over S} (g : T' ⟶ T) (a b : T ⟶ G) : g ≫ padd G a b = padd G (g ≫ a) (g ≫ b) := by
  unfold padd
  rw [comp_lift_assoc]

end Psum

end GlobalTheory.MumProd.SumTau

namespace GlobalTheory.MumProd

open SumTau in

theorem tau_sum_fst : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₁ D₂ : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → ∀ (i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A) (j₁ : D₁.toPre.X →+ D.toPre.X), i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[D₂.toPre.P.A] → (∀ y, q₁ (j₁ y) = y) → (∀ y, q₂ (j₁ y) = 0) → ∀ (wM : LB.Iso D.toPre.P.L (extLB D₁.toPre.P.L D₂.toPre.P.L p₁.left p₂.left)), wM.IsGen → (∃ b₁ b₂, MapsAt₂ wM (eSec D.toPre.P.A) 1 D.toPre.rig b₁ b₂ ∧ LB.Gen.Corr D₁.toPre.P.L _ _ _ _ b₁ D₁.toPre.rig ∧ LB.Gen.Corr D₂.toPre.P.L _ _ _ _ b₂ D₂.toPre.rig) → (∀ x, ∃ b₁ b₂, MapsAt₂ wM (D.toPre.xK x) (-1) (D.toPre.psi x) b₁ b₂ ∧ LB.Gen.Corr D₁.toPre.P.L _ _ _ _ b₁ (D₁.toPre.psi (q₁ x)) ∧ LB.Gen.Corr D₂.toPre.P.L _ _ _ _ b₂ (D₂.toPre.psi (q₂ x))) → ∀ (w : LB.Iso (cubeLB D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] D.toPre.P.L) (cubeLB D₁.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A, snd D₁.toPre.P.A D.toPre.P.A ≫ p₁] D₁.toPre.P.L)), (∀ (Z : Scheme.{0}) (f : Z ⟶ (D₁.toPre.P.A ⊗ D.toPre.P.A).left) (z : Z) (jC : ULift.{0} (Finset (Fin 2)) → D₁.toPre.P.L.ι) (jA : ULift.{0} (Finset (Fin 2)) → D.toPre.P.L.ι) (β : ULift.{0} (Finset (Fin 2)) → D₂.toPre.P.L.ι), f z ∈ (cubeLB D₁.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A, snd D₁.toPre.P.A D.toPre.P.A ≫ p₁] D₁.toPre.P.L).U jC → f z ∈ (cubeLB D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] D.toPre.P.L).U jA → (∀ I, (f ≫ (psum D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] I.down).left ≫ p₂.left) z ∈ D₂.toPre.P.L.U (β I)) → (∀ I, β I = β ⟨insert 0 I.down⟩) → gm f z _ (w.s (jC, jA)) = ∏ I, gm (f ≫ (psum D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] I.down).left) z _ (wM.s (extIdx (f₁ := p₁.left) (f₂ := p₂.left) (jC I) (β I), jA I)) ^ ((-1 : ℤ) ^ (2 - I.down.card))) → ∀ (y : D₁.toPre.X) (y' : D.toPre.X) (z : (TK R).left) (J₁ : ((TK R).left ⟶ D₁.toPre.P.A.left) → D₁.toPre.P.L.ι) (J₂ : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good D₁.toPre.P.L z J₁ → Good D.toPre.P.L z J₂ → val ((pol D).tau (j₁ y) y') (𝟙 _) z J₂ = adjVal w (lift (toUnit (TK R) ≫ D₁.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y')).left z J₁ J₂ * val ((pol D₁).tau y (q₁ y')) (𝟙 _) z J₁ := by
  intro R _ _ I D D₁ D₂ p₁ p₂ q₁ q₂ hS i₁ j₁ hi₁ hi₂ hj₁ hj₂ wM _ hrig hpsi w hw y y' z J₁ J₂ hJ₁ hJ₂
  obtain ⟨J₃, hJ₃⟩ := GlobalTheory.ChartCmp.CarryCalc.exists_good' D₂.toPre.P.isLB z
  have ψ : ∀ x, val (D₁.toPre.psi (q₁ x)) (𝟙 _) z J₁ * val (D₂.toPre.psi (q₂ x)) (𝟙 _) z J₃ =
      (unitAt wM z J₂ J₁ J₃ (D.toPre.xK x))⁻¹ * val (D.toPre.psi x) (𝟙 _) z J₂ := by
    intro x
    obtain ⟨b₁, b₂, hm, c₁, c₂⟩ := hpsi x
    have e := mapsAt_unitAt hm (𝟙 _) hJ₂ hJ₁ hJ₃
    rw [val_corr hJ₁ c₁, val_corr hJ₃ c₂, Category.id_comp, zpow_neg_one] at e
    exact e
  have ρ : val D₁.toPre.rigK (𝟙 _) z J₁ * val D₂.toPre.rigK (𝟙 _) z J₃ =
      unitAt wM z J₂ J₁ J₃ (toUnit (TK R) ≫ η[D.toPre.P.A]).left * val D.toPre.rigK (𝟙 _) z J₂ := by
    obtain ⟨b₁, b₂, hm, c₁, c₂⟩ := hrig
    have e := mapsAt_unitAt hm (toUnit (TK R)).left hJ₂ hJ₁ hJ₃
    rw [val_corr hJ₁ c₁, val_corr hJ₃ c₂, zpow_one] at e
    unfold DegPre.rigK
    rw [val_pull hJ₁, val_pull hJ₃, val_pull hJ₂, Category.id_comp]
    exact e
  have z₂ := GlobalTheory.MumFam.val_psi_zero_mul_rigK R D₂.toPre D₂.tau_bimult z J₃ hJ₃
  have hc := GlobalTheory.MumProd.c_inc_fst R D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ hS i₁ j₁ hi₁ hi₂ hj₁ hj₂ y
  have h1 := GlobalTheory.MumProd.PsumMap.psum_comp_hom _ D.toPre.P.A D₁.toPre.P.A _ 2 p₁
    ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A]
    ![fst D₁.toPre.P.A D.toPre.P.A, snd D₁.toPre.P.A D.toPre.P.A ≫ p₁] hS.hom₁
    (by intro i; fin_cases i <;> simp [hi₁])
  have h2 := GlobalTheory.MumProd.PsumCancel.psum_insert_zero_comp _ D.toPre.P.A D₂.toPre.P.A _ p₂
    ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] hS.hom₂
    (by
      show (fst D₁.toPre.P.A D.toPre.P.A ≫ i₁) ≫ p₂ = _
      rw [Category.assoc, hi₂, ← Category.assoc, comp_toUnit])
  have K : adjVal w (lift (toUnit (TK R) ≫ D₁.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y')).left z J₁ J₂ =
      unitAt wM z J₂ J₁ J₃ (toUnit (TK R) ≫ η[D.toPre.P.A]).left * (unitAt wM z J₂ J₁ J₃ (D.toPre.xK (j₁ y)))⁻¹ *
        (unitAt wM z J₂ J₁ J₃ (D.toPre.xK y'))⁻¹ * unitAt wM z J₂ J₁ J₃ (D.toPre.xK (j₁ y + y')) := by
    have s₀ : lift (toUnit (TK R) ≫ D₁.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y') ≫
        fst D₁.toPre.P.A D.toPre.P.A ≫ i₁ = toUnit (TK R) ≫ D.toPre.c (j₁ y) := by
      rw [lift_fst_assoc, hc, Category.assoc]
    have s₁ : lift (toUnit (TK R) ≫ D₁.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y') ≫
        snd D₁.toPre.P.A D.toPre.P.A = toUnit (TK R) ≫ D.toPre.c y' := lift_snd _ _
    generalize lift (toUnit (TK R) ≫ D₁.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y') = P at s₀ s₁ ⊢
    have mC := Good.mem hJ₁ (fun I : ULift.{0} (Finset (Fin 2)) => (psum D₁.toPre.P.A
      ![fst D₁.toPre.P.A D.toPre.P.A, snd D₁.toPre.P.A D.toPre.P.A ≫ p₁] I.down).left) P.left
    have mA := Good.mem hJ₂ (fun I : ULift.{0} (Finset (Fin 2)) => (psum D.toPre.P.A
      ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] I.down).left) P.left
    have e := hw _ P.left z _ _ (fun I => J₃ (P.left ≫ (psum D.toPre.P.A
      ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] I.down).left ≫ p₂.left)) mC mA
      (fun I => hJ₃ _) (fun I => by
        show J₃ _ = J₃ _
        rw [← Over.comp_left, ← Over.comp_left, h2 I.down]
        rfl)
    refine e.trans ?_
    have e' : ∀ I : ULift.{0} (Finset (Fin 2)), gm (P.left ≫ (psum D.toPre.P.A
        ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] I.down).left) z _
        (wM.s (extIdx (f₁ := p₁.left) (f₂ := p₂.left) (J₁ (P.left ≫ (psum D₁.toPre.P.A
          ![fst D₁.toPre.P.A D.toPre.P.A, snd D₁.toPre.P.A D.toPre.P.A ≫ p₁] I.down).left))
          (J₃ (P.left ≫ (psum D.toPre.P.A
            ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] I.down).left ≫ p₂.left)),
          J₂ (P.left ≫ (psum D.toPre.P.A
            ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] I.down).left))) =
        unitAt wM z J₂ J₁ J₃ (P ≫ psum D.toPre.P.A
          ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] I.down).left := fun I =>
      unitAt_of wM z J₂ J₁ J₃ _ _ _ _ _ rfl rfl
        (by rw [← h1 I.down, Over.comp_left, Over.comp_left, Category.assoc])
        (by rw [Over.comp_left, Category.assoc])
    refine (Finset.prod_congr rfl fun I _ => congrArg (· ^ ((-1 : ℤ) ^ (2 - I.down.card))) (e' I)).trans ?_
    rw [prod_subsets_two]
    have t₀ : P ≫ psum D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] ∅ =
        toUnit (TK R) ≫ η[D.toPre.P.A] := by
      rw [psum_empty, ← Category.assoc, comp_toUnit]
    have t₁ : P ≫ psum D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] {0} =
        toUnit (TK R) ≫ D.toPre.c (j₁ y) := by
      rw [psum_zero]; exact s₀
    have t₂ : P ≫ psum D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] {1} =
        toUnit (TK R) ≫ D.toPre.c y' := by
      rw [SumTau.psum_one]; exact s₁
    have t₃ : P ≫ psum D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] {0, 1} =
        toUnit (TK R) ≫ D.toPre.c (j₁ y + y') := by
      rw [psum_pair, D.toPre.c_add, comp_padd', comp_padd']
      exact congrArg₂ (padd D.toPre.P.A) s₀ s₁
    have c₀ : ((-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card)) = 1 := by decide
    have c₁ : ((-1 : ℤ) ^ (2 - ({0} : Finset (Fin 2)).card)) = -1 := by decide
    have c₂ : ((-1 : ℤ) ^ (2 - ({1} : Finset (Fin 2)).card)) = -1 := by decide
    have c₃ : ((-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card)) = 1 := by decide
    simp only []
    rw [t₀, t₁, t₂, t₃, c₀, c₁, c₂, c₃, zpow_one, zpow_one, zpow_neg_one, zpow_neg_one]
  have ψa := ψ (j₁ y)
  have ψb := ψ y'
  have ψab := ψ (j₁ y + y')
  rw [hj₁, hj₂] at ψa
  rw [map_add, map_add, hj₁, hj₂, zero_add] at ψab
  rw [K, val_tau D _ _ hJ₂, val_tau D₁ _ _ hJ₁, ← inv_mul_eq_iff_eq_mul.2 ψa, ← inv_mul_eq_iff_eq_mul.2 ψb,
    ← inv_mul_eq_iff_eq_mul.2 ψab, ← inv_mul_eq_iff_eq_mul.2 ρ, eq_inv_of_mul_eq_one_left z₂]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.MumProd
