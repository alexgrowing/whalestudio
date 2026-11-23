import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FinrankOfExpBij
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PsiInOfComponent
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPowPolAVPowPolOf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NonemptyTorusExtensionOfIsPowGrp
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfCoord
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistedPrincipalPolarisationSectionsBaseChange
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.BoxCubicalUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftCompSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizationEighthPowerExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TauCoordinateEqUnitMulPsiQuotient
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerProjectionsExtendUniformisedGroupsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerPsiOrdersProjectionLatticeCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixActsOnTorsionLabelsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.EighthTorsion
open MonObj

def precomp {S : Scheme.{0}} {T T' G : Over S} [GrpObj G] (x : T' ⟶ T) : (T ⟶ G) →* (T' ⟶ G) where
  toFun g := x ≫ g
  map_one' := by simp
  map_mul' a b := by simp [MonObj.comp_mul]

def postcomp {S : Scheme.{0}} {T G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H) [IsMonHom f] :
    (T ⟶ G) →* (T ⟶ H) where
  toFun g := g ≫ f
  map_one' := by simp
  map_mul' a b := by simp [MonObj.mul_comp]

theorem prod_comp {S : Scheme.{0}} {T G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H) [IsMonHom f]
    (l : List (T ⟶ G)) : l.prod ≫ f = (l.map (· ≫ f)).prod :=
  (map_list_prod (postcomp (T := T) f) l)

theorem zpow_comp' {S : Scheme.{0}} {T G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H) [IsMonHom f]
    (g : T ⟶ G) (n : ℤ) : (g ^ n) ≫ f = (g ≫ f) ^ n :=
  map_zpow (postcomp (T := T) f) g n

theorem ident_pow {g n : ℕ} (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (T : Trait F)
    (P : PolAV (Sp (FractionRing T.V))) (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)) (hD : IsDiagEnd F W P T.y ε)
    (A8 : PolAV (Sp (FractionRing T.V))) (pA : IsPowPolAV A8 T.A 8) :
    ∃ φ : P.A ≅ A8.A, IsMonHom φ.hom ∧
      LBIso P.L (LB.LinComb (abelian₂ T.A.A T.A.L) (K := Fin 8 × Fin 8)
        (fun ab => (lift (φ.hom ≫ pA.pr ab.1) (φ.hom ≫ pA.pr ab.2)).left) (fun ab => W ab.1 ab.2)) ∧
      ∀ E a, ε E ≫ φ.hom ≫ pA.pr a = ((List.finRange 8).map fun b => (φ.hom ≫ pA.pr b) ^ E a b).prod := by
  obtain ⟨c, ⟨φc, φ₂, hc, hsq, ⟨w, hw⟩, -⟩, pr, hpr, huniv, hL, hε⟩ := hD
  obtain ⟨e, he, hee⟩ := grpPullback_iso hc T.cart
  let p : IsPowGrp P.A T.A.A 8 :=
    { pr := fun a => pr a ≫ e.hom
      hom := fun a => by have := hpr a; infer_instance
      lim := Fan.IsLimit.mk _ (fun s => (huniv s.pt fun a => s.proj a ≫ e.inv).choose)
        (fun s a => by
          have h := (huniv s.pt fun a => s.proj a ≫ e.inv).choose_spec.1 a
          change _ ≫ pr a ≫ e.hom = _
          rw [← Category.assoc, h, Category.assoc, e.inv_hom_id, Category.comp_id])
        (fun s m hm => (huniv s.pt fun a => s.proj a ≫ e.inv).choose_spec.2 m fun a => by
          have h : m ≫ pr a ≫ e.hom = s.proj a := hm a
          rw [← h, Category.assoc, Category.assoc, e.hom_inv_id, Category.comp_id]) }
  obtain ⟨φ, hφ, hφp⟩ := GlobalTheory.PowerExamples.pow_unique p pA.toIsPowGrp
  have hφp' : ∀ a, φ.hom ≫ pA.pr a = pr a ≫ e.hom := hφp
  refine ⟨φ, hφ, ?_, ?_⟩
  · have hpt : ∀ a, (pr a).left ≫ φc = (φ.hom ≫ pA.pr a).left ≫ T.α := fun a => by
      rw [hφp' a, Over.comp_left, Category.assoc, hee]
    have hΛ : (abelian₂ T.A.A T.A.L).IsLB := LB.isLB_linComb T.A.isLB _ _
    obtain ⟨w', hw'⟩ := T.lb
    have i₁ := iso_linComb ((isGen_iff w).1 hw) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left)
      (fun ab => W ab.1 ab.2)
    have i₂ := iso_linComb ((isGen_iff w').1 hw') (K := Fin 8 × Fin 8)
      (fun ab => (lift (φ.hom ≫ pA.pr ab.1) (φ.hom ≫ pA.pr ab.2)).left) (fun ab => W ab.1 ab.2)
    have hm : (fun ab : Fin 8 × Fin 8 => (lift (pr ab.1) (pr ab.2)).left ≫ φ₂) =
        fun ab => (lift (φ.hom ≫ pA.pr ab.1) (φ.hom ≫ pA.pr ab.2)).left ≫ T.α₂ :=
      funext fun ab => GlobalTheory.Poinc.SharpIdent.lift_comp_square hsq T.sq _ _ _ _ (hpt ab.1) (hpt ab.2)
    rw [hm] at i₁
    exact LBIso.trans P.isLB (LB.isLB_linComb c.isLB _ _) (LB.isLB_linComb hΛ _ _) hL
      (LBIso.trans (LB.isLB_linComb c.isLB _ _) (LB.isLB_linComb F.univ.isLB _ _) (LB.isLB_linComb hΛ _ _) i₁ i₂.symm)
  · intro E a
    haveI := he
    rw [hφp' a, ← Category.assoc, hε E a, prod_comp, List.map_map]
    congr 1
    refine List.map_congr_left fun b _ => ?_
    simp only [Function.comp_apply, hφp' b]
    exact zpow_comp' e.hom (pr b) (E a b)

theorem exists_proj {g n : ℕ} (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (T : Trait F)
    (P : PolAV (Sp (FractionRing T.V))) (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)) (hD : IsDiagEnd F W P T.y ε) :
    ∃ pr : Fin 8 → (P.A ⟶ T.A.A), (∀ a, IsMonHom (pr a)) ∧
      (∀ (T' : Over (Sp (FractionRing T.V))) (y : Fin 8 → (T' ⟶ T.A.A)), ∃! z : T' ⟶ P.A, ∀ a, z ≫ pr a = y a) ∧
      LBIso P.L (LB.LinComb (abelian₂ T.A.A T.A.L) (K := Fin 8 × Fin 8)
        (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) ∧
      ∀ E a, ε E ≫ pr a = (List.ofFn fun b => pr b ^ E a b).prod := by
  obtain ⟨A8, pA, -⟩ := GlobalTheory.exists_powPolAV _ T.A 8
  obtain ⟨φ, hφ, hL, hε⟩ := ident_pow F W T P ε hD A8 pA
  refine ⟨fun a => φ.hom ≫ pA.pr a, fun a => by have := pA.hom a; infer_instance, fun T' y => ?_, hL,
    fun E a => by rw [List.ofFn_eq_map]; exact hε E a⟩
  refine ⟨pA.lim.lift (Fan.mk T' y) ≫ φ.inv, fun a => ?_, fun z hz => ?_⟩
  · rw [Category.assoc, φ.inv_hom_id_assoc]
    exact pA.lim.fac (Fan.mk T' y) ⟨a⟩
  · rw [Iso.eq_comp_inv]
    exact pA.lim.uniq (Fan.mk T' y) _ fun a => (Category.assoc _ _ _).trans (hz a.as)

theorem tau_coord {g n : ℕ} {o : Type} [CommRing o] {ζ : o} {F : SFam g n ζ} (T : Trait F) (a b' : T.D.toPre.X)
    (x : (FractionRing T.V)ˣ) (hx : GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord T.D.toPre a b' x) :
    ∃ u : T.Vˣ, (x : FractionRing T.V) =
      algebraMap T.V (FractionRing T.V) (u : T.V) * algebraMap T.V (FractionRing T.V) T.ϖ ^ (T.β a b') := by
  obtain ⟨x₁, h₁⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.exists_isPsiCoord T.D.toPre (a + b')
  obtain ⟨x₂, h₂⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.exists_isPsiCoord T.D.toPre a
  obtain ⟨x₃, h₃⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.exists_isPsiCoord T.D.toPre b'
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.TauCoordQuot.main T.V T.D.toPre a b' x x₁ x₂ x₃ hx h₁ h₂ h₃
  obtain ⟨r₁, c₁, e₁⟩ :=
    GlobalTheory.PeriodFormCompare.exists_psiCoord_of_isPsiCoord (GlobalTheory.PeriodFormCompare.psiIn_top T.D _) h₁
  obtain ⟨r₂, c₂, e₂⟩ :=
    GlobalTheory.PeriodFormCompare.exists_psiCoord_of_isPsiCoord (GlobalTheory.PeriodFormCompare.psiIn_top T.D _) h₂
  obtain ⟨r₃, c₃, e₃⟩ :=
    GlobalTheory.PeriodFormCompare.exists_psiCoord_of_isPsiCoord (GlobalTheory.PeriodFormCompare.psiIn_top T.D _) h₃
  obtain ⟨u, hu⟩ := T.mono.tau (fun i y z => by fin_cases i; exact T.symm y z)
    (Fin.forall_fin_one.2 T.irr.ne_zero) c₂ c₃ c₁
  simp only [Fin.prod_univ_one, Matrix.cons_val_zero] at hu
  refine ⟨u₀ * u, ?_⟩
  have key : algebraMap T.V (FractionRing T.V) (u₀ : T.V) * algebraMap T.V (FractionRing T.V) r₁ *
      (algebraMap T.V (FractionRing T.V) r₂)⁻¹ * (algebraMap T.V (FractionRing T.V) r₃)⁻¹ =
      algebraMap T.V (FractionRing T.V) (u₀ : T.V) * (algebraMap T.V (FractionRing T.V) r₁ /
        (algebraMap T.V (FractionRing T.V) r₂ * algebraMap T.V (FractionRing T.V) r₃)) := by
    rw [div_eq_mul_inv, mul_inv]; ring
  rw [hu₀, e₁, e₂, e₃, key, hu]
  simp only [Units.val_mul, map_mul]
  ring

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (T : Trait F) (P : PolAV (Sp (FractionRing T.V))) (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)), IsDiagEnd F W P T.y ε → ∃ (G' : Over (Sp T.V)) (_ : GrpObj G') (_ : IsCommMonObj G'), IsSemiAbelian G' ∧ ∃ (D' : DegData T.V (maximalIdeal T.V)) (U' : Unif (maximalIdeal T.V) D' P G') (j : D'.toPre.X ≃+ (Fin 8 → T.D.toPre.X)), (∀ y, ∃ v : T.Vˣ, PsiCoord D'.toPre y (v * T.ϖ ^ (qW W T.β (j y)).toNat)) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing T.V) K] (m : ℕ) (pk pk' : QkPt D'.toPre K m) (x x' : TFK (R := T.V) K ⟶ P.A) (E : Matrix (Fin 8) (Fin 8) ℤ), 1 ≤ m → QkToAkU U'.toUnifPre K m pk x → QkToAkU U'.toUnifPre K m pk' x' → x' = x ≫ ε E → CongMod m (j pk'.y) (fun a => ∑ b, E a b • j pk.y b) := by
  intro g n F W hW T P ε hD
  have hCN : GlobalTheory.TorRef.IsCN T.V := ⟨inferInstance, inferInstance, T.complete, T.char⟩
  have hB : GlobalTheory.Mum.Base T.V := ⟨⟨inferInstance, inferInstance, inferInstance, T.complete⟩, T.char⟩
  have hS : SharpOver F W P T.y := by
    obtain ⟨c, hc, pr, h₁, h₂, h₃, -⟩ := hD
    exact ⟨c, hc, pr, h₁, h₂, h₃⟩
  haveI : IsCommMonObj (powObj T.G 8) := GlobalTheory.PowerExamples.comm_of_pow (powIsPowGrp T.G 8)
  have hG' : IsSemiAbelian (powObj T.G 8) := GlobalTheory.PowGrp.isSemiAbelian_pow _ _ T.G 8 (powIsPowGrp T.G 8) T.semi
  obtain ⟨D', ⟨U'⟩⟩ := GlobalTheory.PowE8.exists_unif_pow8 g n _ _ F W hW T.V hCN T.D T.G T.A T.U T.y T.α T.α₂ T.semi T.cart
    T.sq T.lb P hS
  obtain ⟨pr, hpr, huniv, hL, hε⟩ := exists_proj F W T P ε hD
  obtain ⟨pG, c, e, hpG, hgen, hc, he⟩ := GlobalTheory.T.eighthPower_projections_extend_uniformisedGroups T.V hB T.dvr T.G T.semi T.D T.A T.U _ hG' D' P U' W hW pr hpr
    huniv hL
  have hnn : ∀ a, 0 ≤ T.β a a := fun a => by
    by_cases ha : a = 0
    · simp [ha]
    · exact (GlobalTheory.Poinc.Trait.beta_pos g n _ _ F T a ha).le
  refine ⟨powObj T.G 8, inferInstance, inferInstance, hG', D', U', e, fun y => ?_, ?_⟩
  · obtain ⟨r, hr⟩ := (GlobalTheory.PeriodFormCompare.exists_psiCoord_iff _ y).2 (GlobalTheory.PeriodFormCompare.psiIn_top D' y)
    obtain ⟨-, h⟩ := GlobalTheory.T.eighthPower_psiOrders_projectionLatticeCoordinates T.V hB T.dvr T.G T.semi T.D T.A T.U _ hG' D' P U' W hW pr hpr huniv hL pG hpG hgen c hc
      e he T.ϖ T.β T.symm hnn (tau_coord T) y r hr
    obtain ⟨v, hv⟩ := h.symm
    exact ⟨v, by rw [mul_comm, hv]; exact hr⟩
  · rintro K _ _ _ m pk pk' x x' E hm h h' rfl
    exact GlobalTheory.T.matrix_acts_on_torsion_labels_alt T.V hB T.dvr T.G T.semi T.D T.A T.U _ hG' D' P U' W hW pr hpr huniv hL pG hpG hgen c hc e he E (ε E)
      (hε E) K m pk pk' x hm h h'

end GlobalTheory.EighthTorsion
