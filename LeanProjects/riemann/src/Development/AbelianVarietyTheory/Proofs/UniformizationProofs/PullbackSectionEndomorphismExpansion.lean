import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdNeg
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValueAtUnitSection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.PullInt

theorem oneLeft {S : Scheme.{0}} {X M : Over S} [GrpObj M] : (1 : X ⟶ M).left = X.hom ≫ eSec M := by
  have h : (toUnit X).left = X.hom := by simpa using Over.w (toUnit X)
  rw [Hom.one_def, Over.comp_left, h]; rfl

theorem exists_zpow {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (a b : ℕ) :
    ∃ t' : LB.Gen (LB.LinComb L φ (fun i => ((a : ℤ) - b) * ε i)), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → val t' r z J = val t r z J ^ ((a : ℤ) - b) := by
  obtain ⟨t', h₁, h₂⟩ := exists_gen hL (φ' := φ) (ε' := fun i => ((a : ℤ) - b) * ε i) (fun U _ h => by
      rw [Fintype.prod_sum_type, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [← zpow_add]; congr 1; ring)
    (LB.mulGen L _ _ _ _ (GeneratorPullback.powGen L φ ε t a) (LB.invGen L _ _ (GeneratorPullback.powGen L φ ε t b)))
    (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ ht a) (invGen_isGen _ _ _ _ (powGen_isGen _ _ _ _ ht b)))
  refine ⟨t', h₁, fun Z r z J hJ => (h₂ Z r z J hJ).trans ((val_mul hJ _ _ _).trans ?_)⟩
  rw [val_inv, zpow_sub, zpow_natCast, zpow_natCast]
  exact congrArg₂ (fun u v => u * v⁻¹) (map_pow _ _ _) (map_pow _ _ _)

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

theorem rig_val (e : ℕ) {Z : Scheme.{0}} (s : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) {z : Z}
    {N : (Z ⟶ G.left) → U.LG.L.ι} {J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    (hN : Good U.LG.L z N) (hJ : Good D.toPre.P.L z J) (o : Z ⟶ (thickObj R I e G).left)
    (ho : o = s ≫ eSec (thickObj R I e G)) :
    rigV D.toPre (s ≫ thick R I e) z J =
      wv U e o z (J (o ≫ pGl U e)) (N (o ≫ fGl I G e)) *
        val (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rig (s ≫ thick R I e) z N := by
  subst ho
  have hp : (s ≫ eSec (thickObj R I e G)) ≫ pGl U e = (s ≫ thick R I e) ≫ eSec D.toPre.P.A :=
    (Category.assoc _ _ _).trans ((congrArg (s ≫ ·) (UnitValue.eSec_pGl U e)).trans
      (Category.assoc _ _ _).symm)
  have hf : (s ≫ eSec (thickObj R I e G)) ≫ fGl I G e = (s ≫ thick R I e) ≫ eSec G :=
    (Category.assoc _ _ _).trans ((congrArg (s ≫ ·) (UnitValue.eSec_fGl (G := G) e)).trans
      (Category.assoc _ _ _).symm)
  rw [hp, hf, rigV]
  obtain ⟨j, hj⟩ : ∃ j, J ((s ≫ thick R I e) ≫ eSec D.toPre.P.A) = j := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, N ((s ≫ thick R I e) ≫ eSec G) = k := ⟨_, rfl⟩
  have mj : ((s ≫ thick R I e) ≫ eSec D.toPre.P.A) z ∈ D.toPre.P.L.U j := hj ▸ hJ _
  have mk : ((s ≫ thick R I e) ≫ eSec G) z ∈ U.LG.L.U k := hk ▸ hN _
  rw [val_of _ _ z J (fun _ => j) (fun _ => hj), val_of _ _ z N (fun _ => k) (fun _ => hk), hj, hk]
  have m₁ : s z ∈ eSec (thickObj R I e G) ⁻¹ᵁ
      ((D.toPre.P.L.pull (U.gt e).pG.left).U (fun _ => j) ⊓ (U.LG.L.pull (fstG I e G).left).U (fun _ => k)) :=
    ⟨mem_pull.2 ((congrArg (fun q => q z ∈ D.toPre.P.L.U j) hp).mpr mj),
      mem_pull.2 ((congrArg (fun q => q z ∈ U.LG.L.U k) hf).mpr mk)⟩
  have m₂ : s z ∈ thick R I e ⁻¹ᵁ (U.LG.L.pull (eSec G)).U (fun _ => k) := mem_pull.2 mk
  have m₃ : s z ∈ thick R I e ⁻¹ᵁ (D.toPre.P.L.pull (eSec D.toPre.P.A)).U (fun _ => j) := mem_pull.2 mj
  have W := congrArg (gm s z _) (U.w_rig e (fun _ => j, fun _ => k) (_ ⊓ _ ⊓ _) (inf_le_left.trans inf_le_left)
    (inf_le_left.trans inf_le_right) inf_le_right)
  exact ((gm_res _ z _ (by exact ⟨⟨m₁, m₂⟩, m₃⟩) _).trans (gm_pull _ _ z _ m₃ _)).symm.trans (W.symm.trans
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ z _ (by exact ⟨⟨m₁, m₂⟩, m₃⟩) _).trans (gm_pull _ _ z _ m₁ _))
      ((gm_res _ z _ (by exact ⟨⟨m₁, m₂⟩, m₃⟩) _).trans (gm_pull _ _ z _ m₂ _)))))

variable {U} (E : EndU U)

theorem act_fGl (e : ℕ) :
    ((Over.pullback (thick R I e)).map E.aG).left ≫ fGl I G e = fGl I G e ≫ E.aG.left :=
  pullback.lift_fst _ _ _

theorem act_pGl (e : ℕ) :
    ((Over.pullback (thick R I e)).map E.aG).left ≫ pGl U e = pGl U e ≫ E.aB.left := by
  have h1 := congrArg (fun f => f.left) (E.q_lin e)
  simp only [Over.comp_left] at h1
  simp only [GtCoord.pG, Over.comp_left, Over.map_map_left, DegPre.prBe, Over.homMk_left]
  rw [← Category.assoc, h1, Category.assoc, Category.assoc]
  congr 1
  simp only [Over.pullback_map_left]
  exact pullback.lift_fst _ _ _

theorem exists_secG (k' k : ℕ) (β : LB.Gen (LB.LinComb U.LG.L (K := Fin 3) ![𝟙 _, E.aG.left, (1 : G ⟶ G).left]
    ![(k' : ℤ), -(k : ℤ), (k : ℤ) - k'])) (hβ : β.IsGen) (σ : H0 U.LG.L k) :
    ∃ σ' : H0 U.LG.L k', ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J), Good U.LG.L z J →
      sval σ' r z J = sval σ (r ≫ E.aG.left) z J * (val β r z J * val (L := U.LG.L) (φ := fun _ : PUnit => eSec G)
        (ε := fun _ => 1) U.LG.rig (r ≫ G.hom) z J ^ ((k' : ℤ) - k)).val := by
  obtain ⟨ρ, hρ, vρ⟩ := exists_zpow U.LG.isLB (LB.pullGen U.LG.L (fun _ : PUnit => eSec G) (fun _ => 1) U.LG.rig G.hom)
    (pullGen_isGen _ _ _ _ U.LG.rigGen _) k' k
  obtain ⟨s, hs⟩ := exists_sec U.LG.isLB (φ' := fun _ : Fin 1 => 𝟙 G.left) (ε' := fun _ => (k' : ℤ)) (fun V _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_three, Matrix.cons_val, Category.comp_id,
        Fintype.prod_unique, oneLeft]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      module)
    (pullMulSec σ E.aG.left (LB.mulGen U.LG.L _ _ _ _ β ρ) (mulGen_isGen _ _ _ _ _ _ _ hβ hρ))
  refine ⟨s, fun Z r z J hJ => (hs Z r z J hJ).trans ((sval_pullMulSec _ _ _ _ r z hJ).trans ?_)⟩
  rw [val_mul hJ, vρ Z r z J hJ, val_pull hJ]

theorem exists_secB (k' k : ℕ) (κ : LB.Gen (kapLB D.toPre E.aB k' k)) (hκ : κ.IsGen) (χ : D.toPre.X)
    (f : D.toPre.SecB k χ) :
    ∃ g : D.toPre.SecB k' (E.h χ), ∀ (Z : Scheme.{0}) (r : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J →
      sval g r z J = sval f (r ≫ E.aB.left) z J * (val κ r z J *
        rigV D.toPre (r ≫ D.toPre.P.A.hom) z J ^ ((k' : ℤ) - k) * val (E.u χ) r z J).val := by
  obtain ⟨ρ, hρ, vρ⟩ := exists_zpow D.toPre.P.isLB (LB.pullGen D.toPre.P.L (fun _ : PUnit => eSec D.toPre.P.A)
    (fun _ => 1) D.toPre.rig D.toPre.P.A.hom) (pullGen_isGen _ _ _ _ D.toPre.rig_gen _) k' k
  obtain ⟨s, hs⟩ := exists_sec D.toPre.P.isLB (φ' := D.toPre.famφB (E.h χ)) (ε' := DegPre.famε k') (fun V _ h => by
      have p₁ := SectionScalarValuation.prod_famB D.toPre E.aB χ k h
      have p₂ := SectionScalarValuation.prod_famB D.toPre (𝟙 _) (E.h χ) k' h
      have e₃ : ∀ i, Over.Hom.left (𝟙 D.toPre.P.A) ≫ D.toPre.famφB (E.h χ) i = D.toPre.famφB (E.h χ) i :=
        fun i => by simp
      simp only [e₃] at p₂
      have p₃ : ∏ i, h (D.toPre.Oφ (𝟙 _) (E.h χ) i) ^ Oε i =
          h (𝟙 D.toPre.P.A * SectionScalarValuation.cQ D.toPre _ (E.h χ)).left ^ (1 : ℤ) * h (SectionScalarValuation.cQ D.toPre _ (E.h χ)).left ^ (-1 : ℤ) *
            h (Over.Hom.left (𝟙 D.toPre.P.A)) ^ (-1 : ℤ) * h (1 : D.toPre.P.A ⟶ D.toPre.P.A).left ^ (1 : ℤ) := by
        rw [Fin.prod_univ_four]; rfl
      have p₄ : ∏ i, h (D.toPre.Oφ E.aB χ i) ^ Oinvε i =
          h (E.aB * SectionScalarValuation.cQ D.toPre _ χ).left ^ (-1 : ℤ) * h (SectionScalarValuation.cQ D.toPre _ χ).left ^ (1 : ℤ) *
            h E.aB.left ^ (1 : ℤ) * h (1 : D.toPre.P.A ⟶ D.toPre.P.A).left ^ (-1 : ℤ) := by
        rw [Fin.prod_univ_four]; rfl
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [p₁, p₂, p₃, p₄]
      simp only [Fin.prod_univ_three, Matrix.cons_val, Fintype.prod_unique, oneLeft, Over.id_left]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      module)
    (pullMulSec f E.aB.left (LB.mulGen D.toPre.P.L _ _ _ _ (LB.mulGen D.toPre.P.L _ _ _ _ κ ρ) (E.u χ))
      (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hκ hρ) (E.u_norm χ).1))
  refine ⟨s, fun Z r z J hJ => (hs Z r z J hJ).trans ((sval_pullMulSec _ _ _ _ r z hJ).trans ?_)⟩
  rw [val_mul hJ, val_mul hJ, vρ Z r z J hJ, val_pull hJ, rigV]

theorem alg {Γ : Type} [CommRing Γ] (k' k : ℕ) (wx wa wo β κ ρG ρB : Γˣ) (s : Γ)
    (h₁ : κ = β * wx ^ (k' : ℤ) * wa ^ (-(k : ℤ)) * wo ^ ((k : ℤ) - k')) (h₂ : ρB = wo * ρG) :
    (wx ^ k').val * (s * (β * ρG ^ ((k' : ℤ) - k)).val) = (κ * ρB ^ ((k' : ℤ) - k)).val * ((wa ^ k).val * s) := by
  have : wx ^ k' * (β * ρG ^ ((k' : ℤ) - k)) = κ * ρB ^ ((k' : ℤ) - k) * wa ^ k := by
    rw [h₁, h₂]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_pow]
    module
  rw [mul_comm s, ← _root_.mul_assoc, ← Units.val_mul, this, Units.val_mul, _root_.mul_assoc]

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (E : EndU U), Function.Injective E.h → ∀ (k' k : ℕ) (β : LB.Gen (LB.LinComb U.LG.L (K := Fin 3) ![𝟙 _, E.aG.left, (1 : G ⟶ G).left] ![(k' : ℤ), -(k : ℤ), (k : ℤ) - k'])), β.IsGen → ∀ κ : LB.Gen (kapLB D.toPre E.aB k' k), κ.IsGen → (∀ (e : ℕ) (Z : Scheme.{0}) (x o : Z ⟶ (thickObj R I e G).left) (z : Z) (JG) (J), Good U.LG.L z JG → Good D.toPre.P.L z J → o = x ≫ (1 : thickObj R I e G ⟶ thickObj R I e G).left → ∀ W : (Z ⟶ (thickObj R I e G).left) → (Z.presheaf.stalk z)ˣ, (∀ y, W y = gw (U.w e) y z (J (y ≫ (U.gt e).pG.left)) (fun _ => JG (y ≫ (fstG I e G).left))) → val κ (x ≫ (U.gt e).pG.left) z J = val β (x ≫ (fstG I e G).left) z JG * W x ^ (k' : ℤ) * W (x ≫ ((Over.pullback (thick R I e)).map E.aG).left) ^ (-(k : ℤ)) * W o ^ ((k : ℤ) - k')) → ∀ (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ e, U.ExpandsAt e k σ f) → ∃ (σ' : H0 U.LG.L k') (f' : ∀ α : D.toPre.X, D.toPre.SecB k' α), (∀ e, U.ExpandsAt e k' σ' f') ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J), Good U.LG.L z J → sval σ' r z J = sval σ (r ≫ E.aG.left) z J * (val β r z J * val (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rig (r ≫ G.hom) z J ^ ((k' : ℤ) - k)).val) ∧ (∀ (χ : D.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J → sval (f' (E.h χ)) r z J = sval (f χ) (r ≫ E.aB.left) z J * (val κ r z J * rigV D.toPre (r ≫ D.toPre.P.A.hom) z J ^ ((k' : ℤ) - k) * val (E.u χ) r z J).val) ∧ ∀ b, b ∉ Set.range E.h → ∀ j, (f' b).f j = 0 := by
  classical
  intro R _ _ I D A G _ _ U E hinj k' k β hβ κ hκ H σ f hf
  obtain ⟨σ', hσ'⟩ := exists_secG E k' k β hβ σ
  have key : ∀ b, ∃ s : D.toPre.SecB k' b, (∀ χ, b = E.h χ → ∀ (Z : Scheme.{0}) (r : Z ⟶ D.toPre.P.A.left) (z : Z) (J),
      Good D.toPre.P.L z J → sval s r z J = sval (f χ) (r ≫ E.aB.left) z J * (val κ r z J *
        rigV D.toPre (r ≫ D.toPre.P.A.hom) z J ^ ((k' : ℤ) - k) * val (E.u χ) r z J).val) ∧
      (b ∉ Set.range E.h → ∀ j, s.f j = 0) := by
    intro b
    by_cases hb : b ∈ Set.range E.h
    · obtain ⟨χ, rfl⟩ := hb
      obtain ⟨g, hg⟩ := exists_secB E k' k κ hκ χ (f χ)
      refine ⟨g, fun χ' e => ?_, fun h => (h ⟨χ, rfl⟩).elim⟩
      obtain rfl := hinj e
      exact hg
    · exact ⟨SecOps.secZero, fun χ e => (hb ⟨χ, e.symm⟩).elim, fun _ _ => rfl⟩
  choose f' hf₁ hf₂ using key
  refine ⟨σ', f', fun e => ?_, hσ', fun χ => hf₁ _ χ rfl, hf₂⟩
  obtain ⟨S, hS⟩ := expandsAt_val U e k σ f (hf e)
  refine expandsAt_of_val U e k' σ' f' (S.image E.h) fun y J hJ => ?_
  obtain ⟨b₁, b₂⟩ := hS _ ((Over.pullback (thick R I e)).map E.aG).left y J hJ
  simp only [act_pGl E e, act_fGl E e] at b₁
  refine ⟨fun α hα => ?_, fun jL hL => ?_⟩
  · by_cases hb : α ∈ Set.range E.h
    · obtain ⟨χ, rfl⟩ := hb
      rw [hf₁ _ χ rfl _ _ y J hJ, b₁ χ fun h => hα (Finset.mem_image_of_mem _ h), zero_mul]
    · exact (congrArg (gs _ y _) (hf₂ α hb _)).trans (gs_zero _ y _ (hJ.mem _ _))
  · obtain ⟨JG, hJG, eJ⟩ := exists_good U.LG.L U.LG.isLB y (fun _ : Unit => fGl I G e) (fun _ => jL)
      (fun _ _ _ => rfl) (fun _ => hL)
    obtain rfl : JG (fGl I G e) = jL := eJ ()
    have c₁ := b₂ _ (hJG (((Over.pullback (thick R I e)).map E.aG).left ≫ fGl I G e))
    have c₂ := H e _ (𝟙 _) _ y JG J hJG hJ rfl
      (fun x => wv U e x y (J (x ≫ pGl U e)) (JG (x ≫ fGl I G e))) (fun _ => rfl)
    have c₃ := rig_val U e (thickObj R I e G).hom hJG hJ _ oneLeft
    have c₄ := hσ' _ (fGl I G e) y JG hJG
    have sv_eq : ∀ (n : ℕ) (τ : H0 U.LG.L n) (q : (thickObj R I e G).left ⟶ G.left),
        sval τ q y JG = sv U n τ q y (JG q) := fun n τ q =>
      sval_of τ q y JG (fun _ => JG q) (fun _ => by rw [Category.comp_id])
    have w₁ : fGl I G e ≫ G.hom = (thickObj R I e G).hom ≫ thick R I e := Over.w (fstG I e G)
    have w₂ : pGl U e ≫ D.toPre.P.A.hom = (thickObj R I e G).hom ≫ thick R I e := Over.w (U.gt e).pG
    simp only [Category.id_comp] at c₂
    rw [sv_eq, sv_eq, w₁, ← act_fGl E e] at c₄
    rw [c₄, Finset.sum_image fun _ _ _ _ h => hinj h]
    refine (alg k' k _ _ _ _ _ _ _ _ c₂ c₃).trans ?_
    rw [c₁, Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    have t := E.t_lin e χ _ (𝟙 _) y J hJ
    simp only [Category.id_comp] at t
    rw [hf₁ _ χ rfl _ _ y J hJ, w₂, act_pGl E e]
    refine (congrArg (fun u : ((thickObj R I e G).left.presheaf.stalk y)ˣ => _ * (_ * u.val)) t).trans ?_
    simp only [Units.val_mul]
    ring

end GlobalTheory.PullInt
