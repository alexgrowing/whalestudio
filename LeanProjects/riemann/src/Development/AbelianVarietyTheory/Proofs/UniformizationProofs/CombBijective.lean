import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsAffineHomOfIsPullbackSpecMap
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPullSecSval
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalSecComb
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFOfExpT
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsExpansionSectionLineBundlePowerStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU.ExpExt

section Decomp
open GlobalTheory.QCoh.Qcqs TopologicalSpace
variable {V W : Type} [CommRing V] [CommRing W] [Algebra V W] {n : ℕ} (b : Module.Basis (Fin n) V W)
  {X Y : Scheme.{0}} {p : X ⟶ Spec (.of V)} {q : Y ⟶ Spec (.of W)} {π : Y ⟶ X}

abbrev cst (w : W) : Γ(Spec (.of W), ⊤) := (Scheme.ΓSpecIso (.of W)).inv.hom w

def comb (q : Y ⟶ Spec (.of W)) (π : Y ⟶ X) (U : X.Opens) (a : Fin n → Γ(X, U)) : Γ(Y, π ⁻¹ᵁ U) :=
  ∑ i, (π.app U).hom (a i) * (baseRingHom q (π ⁻¹ᵁ U)).hom (b i)

theorem gs_comb (U : X.Opens) (a : Fin n → Γ(X, U)) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (h : r z ∈ π ⁻¹ᵁ U) :
    gs r z _ (comb b q π U a) = ∑ i, gs (r ≫ q) z ⊤ (cst (b i)) * gs (r ≫ π) z U (a i) := by
  have e : ∀ i, gs r z _ ((π.app U).hom (a i) * (baseRingHom q (π ⁻¹ᵁ U)).hom (b i)) =
      gs (r ≫ q) z ⊤ (cst (b i)) * gs (r ≫ π) z U (a i) := fun i => by
    rw [gs_mul r z _ h, gs_pull r π z U h, mul_comm]
    refine congrArg (· * _) ?_
    exact (gs_res r z (U := q ⁻¹ᵁ ⊤) le_top h ((q.app ⊤).hom (cst (b i)))).trans (gs_pull r q z ⊤ trivial _)
  rw [← Finset.sum_congr rfl fun i _ => e i]
  simp only [comb, gs_eq r z _ h, map_sum]

variable (H : IsPullback π q p (Spec.map (CommRingCat.ofHom (algebraMap V W))))
include H

theorem comb_bijective {U : X.Opens} (hU : IsAffineOpen U) : Function.Bijective (comb b q π U) := by
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := π ⁻¹ᵁ U) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  have po' : IsPushout (baseRingHom p U) (CommRingCat.ofHom (algebraMap V W)) (π.app U)
      (baseRingHom q (π ⁻¹ᵁ U)) := by
    refine po.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [baseRingHom]
    · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    · simp [Scheme.Hom.app_eq_appLE]
    · simp [baseRingHom]
  let := (π.app U).hom.toAlgebra
  let := (baseRingHom p U).hom.toAlgebra
  let := (baseRingHom q (π ⁻¹ᵁ U)).hom.toAlgebra
  let := (baseRingHom (π ≫ p) (π ⁻¹ᵁ U)).hom.toAlgebra
  have : IsScalarTower V Γ(X, U) Γ(Y, π ⁻¹ᵁ U) :=
    .of_algebraMap_eq fun r ↦ (app_baseRingHom π p U r).symm
  have : IsScalarTower V W Γ(Y, π ⁻¹ᵁ U) :=
    .of_algebraMap_eq fun r ↦ (baseRingHom_algebraMap (R := .of V) (L := .of W) H _ r).symm
  have hP : Algebra.IsPushout V Γ(X, U) W Γ(Y, π ⁻¹ᵁ U) := CommRingCat.isPushout_iff_isPushout.mp po'
  let b' := hP.out.basis b
  have : comb b q π U = b'.equivFun.symm := by
    funext v
    rw [Module.Basis.equivFun_symm_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [IsBaseChange.basis_apply, Algebra.smul_def]
    rfl
  rw [this]
  exact b'.equivFun.symm.bijective

theorem comb_inj {U : X.Opens} {a a' : Fin n → Γ(X, U)}
    (h : ∀ y ∈ π ⁻¹ᵁ U, ∑ i, gs (𝟙 Y ≫ q) y ⊤ (cst (b i)) * gs (𝟙 Y ≫ π) y U (a i) =
      ∑ i, gs (𝟙 Y ≫ q) y ⊤ (cst (b i)) * gs (𝟙 Y ≫ π) y U (a' i)) : a = a' := by
  funext i
  refine fn_ext fun x hx => ?_
  obtain ⟨_, ⟨O, hO, rfl⟩, hxO, hle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  have hle' : O ≤ U := hle
  have e : (fun i => (X.presheaf.map (homOfLE hle').op).hom (a i)) =
      fun i => (X.presheaf.map (homOfLE hle').op).hom (a' i) := (comb_bijective b H hO).1 (fn_ext fun y hy => by
    rw [gs_comb b O _ (𝟙 Y) y hy, gs_comb b O _ (𝟙 Y) y hy]
    simp only [gs_res (𝟙 Y ≫ π) y hle' hy]
    exact h y (hle' hy))
  exact (gs_res (𝟙 X) x hle' hxO _).symm.trans ((congrArg _ (congrFun e i)).trans (gs_res (𝟙 X) x hle' hxO _))

theorem comb_surj {U : X.Opens} (s : Γ(Y, π ⁻¹ᵁ U)) : ∃ a : Fin n → Γ(X, U),
    ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ π ⁻¹ᵁ U →
      gs r z _ s = ∑ i, gs (r ≫ q) z ⊤ (cst (b i)) * gs (r ≫ π) z U (a i) := by
  let I := {O : X.Opens // IsAffineOpen O ∧ O ≤ U}
  have cov : ∀ x ∈ U, ∃ O : I, x ∈ O.1 := fun x hx => by
    obtain ⟨_, ⟨O, hO, rfl⟩, hxO, hle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
    exact ⟨⟨O, hO, hle⟩, hxO⟩
  choose u hu using fun O : I => (comb_bijective b H O.2.1).2
    ((Y.presheaf.map (homOfLE (π.preimage_mono O.2.2)).op).hom s)
  have hv : ∀ (O : I) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ π ⁻¹ᵁ O.1 →
      gs r z _ s = ∑ i, gs (r ≫ q) z ⊤ (cst (b i)) * gs (r ≫ π) z O.1 (u O i) := fun O Z r z hz => by
    rw [← gs_comb b O.1 _ r z hz, hu, gs_res r z _ hz]
  have hc : ∀ O O' : I, (fun i => (X.presheaf.map (homOfLE (inf_le_left : O.1 ⊓ O'.1 ≤ O.1)).op).hom (u O i)) =
      fun i => (X.presheaf.map (homOfLE (inf_le_right : O.1 ⊓ O'.1 ≤ O'.1)).op).hom (u O' i) := fun O O' =>
    comb_inj b H fun y hy => by
      simp only [gs_res (𝟙 Y ≫ π) y (inf_le_left : O.1 ⊓ O'.1 ≤ O.1) hy,
        gs_res (𝟙 Y ≫ π) y (inf_le_right : O.1 ⊓ O'.1 ≤ O'.1) hy]
      exact (hv O _ (𝟙 Y) y hy.1).symm.trans (hv O' _ (𝟙 Y) y hy.2)
  choose a ha using fun i => (X.sheaf.existsUnique_gluing' (fun O : I => O.1) U (fun O => homOfLE O.2.2)
    (fun x hx => Opens.mem_iSup.2 (cov x hx)) (fun O => u O i) (fun O O' => congrFun (hc O O') i)).exists
  refine ⟨a, fun Z r z hz => ?_⟩
  obtain ⟨O, hO⟩ := cov _ hz
  rw [hv O Z r z hO]
  refine Finset.sum_congr rfl fun i _ => congrArg _ ?_
  exact (congrArg (gs (r ≫ π) z O.1) (ha i O)).symm.trans (gs_res (r ≫ π) z O.2.2 hO _)

theorem sec_decomp {X₀ : Scheme.{0}} {L : LB X₀} {K : Type} [Fintype K] (φ : K → (X ⟶ X₀)) {ε : K → ℤ}
    {φ' : K → (Y ⟶ X₀)} (hφ : ∀ k, π ≫ φ k = φ' k) (σ : LB.Sec (LB.LinComb L φ' ε)) :
    ∃ τ : Fin n → LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      sval σ r z J = ∑ i, gs (r ≫ q) z ⊤ (cst (b i)) * sval (τ i) (r ≫ π) z J := by
  obtain rfl : (fun k => π ≫ φ k) = φ' := funext hφ
  have l : ∀ j, π ⁻¹ᵁ LB.wchart L φ j ≤ LB.wchart L (fun k => π ≫ φ k) j :=
    fun j y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  choose a ha using fun j => comb_surj b H ((Y.presheaf.map (homOfLE (l j)).op).hom (σ.f j))
  have hv : ∀ j (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ π ⁻¹ᵁ LB.wchart L φ j →
      gs r z (LB.wchart L (fun k => π ≫ φ k) j) (σ.f j) =
        ∑ i, gs (r ≫ q) z ⊤ (cst (b i)) * gs (r ≫ π) z _ (a j i) := fun j Z r z hz =>
    (gs_res r z (l j) hz _).symm.trans (ha j Z r z hz)
  have hc : ∀ j j', (fun i => (X.presheaf.map (homOfLE (inf_le_left :
        LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j)).op).hom (a j i)) =
      fun i => @id Γ(X, LB.wchart L φ j ⊓ LB.wchart L φ j') ((LB.LinComb L φ ε).g j j').val * (X.presheaf.map (homOfLE (inf_le_right :
        LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j')).op).hom (a j' i) := fun j j' =>
    comb_inj b H fun y hy => by
      have e : ∀ i, gs (𝟙 Y ≫ π) y (LB.wchart L φ j ⊓ LB.wchart L φ j') (@id Γ(X, LB.wchart L φ j ⊓ LB.wchart L φ j') ((LB.LinComb L φ ε).g j j').val *
          (X.presheaf.map (homOfLE (inf_le_right :
            LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j')).op).hom (a j' i)) =
          (trF (fun k => π ≫ φ k) ε (𝟙 Y) y j j').val * gs (𝟙 Y ≫ π) y _ (a j' i) := fun i =>
        (gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit _ y _ hy _).trans
          (congrArg Units.val (gm_linComb L φ ε (𝟙 Y ≫ π) y j j' hy.1 hy.2))) (gs_res _ y _ hy _))
      refine (Finset.sum_congr rfl fun i _ => congrArg _ (gs_res (𝟙 Y ≫ π) y inf_le_left hy _)).trans
        (Eq.trans ?_ (Finset.sum_congr rfl fun i _ => congrArg _ (e i)).symm)
      rw [← hv j _ (𝟙 Y) y hy.1, sec_trans σ (𝟙 Y) y (l j hy.1) (l j' hy.2), hv j' _ (𝟙 Y) y hy.2, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _
  refine ⟨fun i => ⟨fun j => a j i, fun j j' => congrFun (hc j j') i⟩, fun Z r z J hJ => ?_⟩
  refine (hv _ Z r z (Set.mem_iInter.2 fun k => hJ (r ≫ π ≫ φ k))).trans
    (Finset.sum_congr rfl fun i _ => congrArg _ ?_)
  exact (sval_of (L := L) (φ := φ) (ε := ε) ⟨fun j => a j i, fun j j' => congrFun (hc j j') i⟩ (r ≫ π) z J
    (fun k => J (r ≫ π ≫ φ k)) (fun k => by rw [Category.assoc])).symm

end Decomp

theorem gs_scal {W F : Type} [CommRing W] [CommRing F] {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z)
    (p : Y ⟶ Spec (.of F)) (φ : Spec (.of F) ⟶ Spec (.of W)) (w : W) :
    gs r z ⊤ (scal p ((Scheme.ΓSpecIso (.of F)).hom.hom (φ.appTop.hom (cst w)))) = gs (r ≫ p ≫ φ) z ⊤ (cst w) := by
  have e : scal p ((Scheme.ΓSpecIso (.of F)).hom.hom (φ.appTop.hom (cst w))) = (p ≫ φ).appTop.hom (cst w) := by
    rw [scal, Iso.hom_inv_id_apply]; rfl
  rw [e]
  exact gs_pull r (p ≫ φ) z ⊤ trivial _

theorem main : Laws → Laws2 → (AllPre fun {V} _ _ _ {_} {_} {_} _ _ U => ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], FinExt V W → ∀ k, 1 ≤ k → ∀ σ, ∃ f, U.ExpT (TA V W) k σ f ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (φ : TF (R := V) F ⟶ TA V W) t s, U.PullG F φ k σ t → PullB _ F φ k f s → U.ExpF F k t s) := by
  classical
  intro hL hL2 V _ _ _ hV D A G _ _ U W _ _ _ hW k hk σ
  have := hW.1
  have := hW.2.1
  let b := Module.finBasis V W
  obtain ⟨τ, hτ⟩ := sec_decomp b (p := G.hom) (q := (fst (TA V W) G).left) (π := (snd (TA V W) G).left)
    (IsPullback.of_hasPullback (TA V W).hom G.hom).flip (fun _ : Fin 1 => 𝟙 G.left) (fun _ => Category.comp_id _) σ
  choose σ' hσ' using fun i => exists_pullSec_sval (τ i) (snd (𝟙_ _) G).left (fun _ => (snd (𝟙_ _) G).left)
    (fun _ => Category.comp_id _)
  have hσ : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TA V W ⊗ G).left) (r' : Z ⟶ (𝟙_ _ ⊗ G).left) (z : Z) (J),
      Good U.P.L.L z J → r' ≫ (snd _ G).left = r ≫ (snd _ G).left →
      sval σ r z J = ∑ i, gs (r ≫ (fst (TA V W) G).left) z ⊤ (cst (b i)) * sval (σ' i) r' z J :=
    fun Z r r' z J hJ h => (hτ Z r z J hJ).trans (Finset.sum_congr rfl fun i _ => by rw [hσ' i Z r' z J hJ, h])
  choose g hg using fun i => GlobalTheory.T.exists_expansion_section_lineBundle_power hL hL2 V hV D A G U k hk (σ' i)
  choose g' hg' using fun i α => exists_pullSec_sval (g i α) (toUnit (TA V W) ▷ D.P.A).left (famφT D (TA V W) α)
    (whisker_famφT D _ α)
  have s1 : ∀ (T B : Over (Spec (CommRingCat.of V))), (toUnit T ▷ B).left ≫ (snd (𝟙_ _) B).left = (snd T B).left :=
    fun T B => congrArg CommaMorphism.left (whiskerRight_snd (toUnit T) B)
  have s2 : ∀ {T T' : Over (Spec (CommRingCat.of V))} (ρ : T' ⟶ T) (B : Over (Spec (CommRingCat.of V))),
      (ρ ▷ B).left ≫ (fst T B).left = (fst T' B).left ≫ ρ.left := fun ρ B =>
    congrArg CommaMorphism.left (whiskerRight_fst ρ B)
  let f : ∀ α, SecBT D (TA V W) k α := fun α =>
    ExpLin.secComb (fun i => (fst (TA V W) D.P.A).left.appTop.hom (cst (b i))) (fun i => g' i α)
  have hf : ∀ α (Z : Scheme.{0}) (r : Z ⟶ (TA V W ⊗ D.P.A).left) (z : Z) (J), Good D.P.L z J →
      sval (f α) r z J = ∑ i, gs (r ≫ (fst (TA V W) D.P.A).left) z ⊤ (cst (b i)) *
        sval (g i α) (r ≫ (toUnit (TA V W) ▷ D.P.A).left) z J := fun α Z r z J hJ =>
    (ExpLin.sval_secComb (fst (TA V W) D.P.A).left (fun i => cst (b i)) (fun i => g' i α) r z hJ).trans
      (Finset.sum_congr rfl fun i _ => congrArg _ (hg' i α Z r z J hJ))
  refine ⟨f, fun e => ?_, fun F _ _ φ t s hG hB => ?_⟩
  · choose s hs using fun i => hg i e
    refine ⟨Finset.univ.biUnion s, fun Z x rG rB h₁ h₂ h₃ z JG J hG hJ => ?_⟩
    have H := fun i => hs i Z x (rG ≫ (toUnit (TA V W) ▷ G).left) (rB ≫ (toUnit (TA V W) ▷ D.P.A).left)
      (by rw [Category.assoc, s1, h₁]) (by rw [Category.assoc, s1, h₂])
      (by rw [Category.assoc, s2, Category.assoc, s2, ← Category.assoc, h₃, Category.assoc]) z JG J hG hJ
    refine ⟨fun α hα => ?_, ?_⟩
    · rw [hf α Z rB z J hJ]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [(H i).1 α (fun hi => hα (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hi⟩)), mul_zero]
    · rw [hσ Z rG (rG ≫ (toUnit (TA V W) ▷ G).left) z JG hG (by rw [Category.assoc, s1])]
      refine Eq.trans ?_ (Finset.sum_congr rfl fun α _ => (congrArg (· * _) (hf α Z rB z J hJ)).symm)
      rw [h₃]
      exact ExpLin.sum_comb _ _ _ s (fun i α => sval (g i α) (rB ≫ (toUnit (TA V W) ▷ D.P.A).left) z J) _
        (fun i => (H i).1) (fun i => (H i).2)
  · refine ⟨_, fun i => (Scheme.ΓSpecIso (.of F)).hom.hom (φ.left.appTop.hom (cst (b i))), σ', g, hg, ?_, ?_⟩
    · intro Z rA y rG h₁ h₂ z JA JG hJA hJG
      have e₂ : φ.left ≫ (TA V W).hom = jFK (R := V) F ≫ jK V := Over.w φ
      have e₃ : (fst (TFK (R := V) F) A.A).left ≫ jFK (R := V) F = (snd (TFK (R := V) F) A.A).left ≫ A.A.hom :=
        (Over.w (fst (TFK (R := V) F) A.A)).trans (Over.w (snd (TFK (R := V) F) A.A)).symm
      have e₄ : U.gen.hom.left ≫ A.A.hom = pullback.snd G.hom (jK V) := Over.w U.gen.hom
      have w : (rA ≫ (fst (TFK (R := V) F) A.A).left ≫ φ.left) ≫ (TA V W).hom =
          (y ≫ pullback.fst G.hom (jK V)) ≫ G.hom := (calc
        (y ≫ pullback.fst G.hom (jK V)) ≫ G.hom = y ≫ pullback.fst G.hom (jK V) ≫ G.hom := Category.assoc _ _ _
        _ = y ≫ (U.gen.hom.left ≫ A.A.hom) ≫ jK V := by rw [e₄]; exact congrArg (y ≫ ·) pullback.condition
        _ = (rA ≫ (snd (TFK (R := V) F) A.A).left) ≫ A.A.hom ≫ jK V := by rw [h₁]; simp only [Category.assoc]
        _ = rA ≫ ((fst (TFK (R := V) F) A.A).left ≫ jFK (R := V) F) ≫ jK V := by rw [e₃]; simp only [Category.assoc]
        _ = rA ≫ (fst (TFK (R := V) F) A.A).left ≫ φ.left ≫ (TA V W).hom := by
          rw [e₂]; exact congrArg (rA ≫ ·) (Category.assoc _ _ _)
        _ = _ := (congrArg (rA ≫ ·) (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm).symm
      let r : Z ⟶ (TA V W ⊗ G).left := pullback.lift _ _ w
      have r₁ : r ≫ (fst (TA V W) G).left = rA ≫ (fst (TFK (R := V) F) A.A).left ≫ φ.left := pullback.lift_fst _ _ _
      have r₂ : r ≫ (snd (TA V W) G).left = y ≫ pullback.fst G.hom (jK V) := pullback.lift_snd _ _ _
      refine (hG Z rA y r h₁ r₂ r₁ z JA JG hJA hJG).trans ((hσ Z r rG z JG hJG (h₂.trans r₂.symm)).trans ?_)
      refine Finset.sum_congr rfl fun i _ => congrArg (· * _) ?_
      rw [r₁]
      exact (gs_scal rA z (fst (TFK (R := V) F) A.A).left φ.left (b i)).symm
    · intro α Z rF rB h z J hJ
      have e : rB = (rF ≫ (φ ▷ D.P.A).left) ≫ (toUnit (TA V W) ▷ D.P.A).left := by
        have w : (φ ▷ D.P.A).left ≫ (snd _ D.P.A).left = (snd _ D.P.A).left :=
          congrArg CommaMorphism.left (whiskerRight_snd φ D.P.A)
        have i : IsIso (snd (𝟙_ (Over (Spec (CommRingCat.of V)))) D.P.A).left := by
          rw [← leftUnitor_hom]; exact inferInstanceAs (IsIso ((Over.forget _).map (λ_ D.P.A).hom))
        rw [← cancel_mono (snd (𝟙_ (Over (Spec (CommRingCat.of V)))) D.P.A).left, Category.assoc, s1,
          Category.assoc, w, h]
      have e' : sval (s α) rF z J = sval (f α) (rF ≫ (φ ▷ D.P.A).left) z J := by
        rw [IntExp.sval_comp (f α) _ rF z J hJ, ← hB α (rF z) _ (fun ψ => hJ (rF ≫ ψ)),
          ← IntExp.sval_comp (s α) _ rF z J hJ, Category.comp_id]
      rw [e', hf α Z _ z J hJ, e]
      refine Finset.sum_congr rfl fun i _ => congrArg (· * _) ?_
      rw [Category.assoc, s2]
      exact (gs_scal rF z (fst (TF (R := V) F) D.P.A).left φ.left (b i)).symm

end GlobalTheory.UU.ExpExt
end
