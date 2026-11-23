import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingExistsOfCubeTheorem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingAdjointEndomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdivisibleBaseChangeIsoSemiabelian
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsIffOfIsGrpPullbackComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullbackBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualAbelianSchemeExistsBiduality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundlePullbackGrpPullback
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RosatiAdjOfPoints

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open GlobalTheory.DeRham (spOver)
open GlobalTheory.AbDual GlobalTheory.PDiv GlobalTheory.PDivGroup
open GlobalTheory.BadPt (IsWeilHom)
open GlobalTheory.PerfdLat (dualBaseChange)
open GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin (IsPolarisation)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SerreTateDef

section Notions

variable {S S₀ : Scheme.{0}} {A B : Over S} {A₀ B₀ : Over S₀}

def IsPairRed (i : A₀.left ⟶ A.left) (j : B₀.left ⟶ B.left) (P : LB (A ⊗ B).left) (P₀ : LB (A₀ ⊗ B₀).left) :
    Prop :=
  ∃ l : (A₀ ⊗ B₀).left ⟶ (A ⊗ B).left, l ≫ (fst A B).left = (fst A₀ B₀).left ≫ i ∧
    l ≫ (snd A B).left = (snd A₀ B₀).left ≫ j ∧ LBIso P₀ (P.pull l)

abbrev polBundle (P : LB (A ⊗ B).left) (lam : A ⟶ B) : LB (A ⊗ A).left := ev P (fst A A) (snd A A ≫ lam)

end Notions

section Clauses

variable (p : ℕ) [Fact p.Prime] (R R₀ : Type) [CommRing R] [CommRing R₀] [Algebra R R₀]

abbrev red : Sp R₀ ⟶ Sp R := spMap (algebraMap R R₀)

def HasTower : Prop :=
  ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∃ G : PDivGroup p R, Nonempty (G.TorsionTower A) ∧
      ∀ g : ℕ, SmoothOfRelativeDimension g A.hom → G.height = 2 * g

def DualTower : Prop :=
  ∀ (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), IsAbelianScheme A → IsAbelianScheme B →
    IsDual A B P → ∀ (G H : PDivGroup p R) (t : G.TorsionTower A) (u : H.TorsionTower B),
      ∃ w : G ⟶ H.dual, IsWeilHom t u P w ∧ IsIso w

def LiftObj : Prop :=
  ∀ (A₀ : Over (Sp R₀)) [GrpObj A₀], IsAbelianScheme A₀ →
    ∀ (G : PDivGroup p R) (t₀ : (G.baseChange R₀).TorsionTower A₀),
      ∃ (A : Over (Sp R)) (_ : GrpObj A) (i : A₀.left ⟶ A.left) (h : IsGrpPullback A₀ A (red R R₀) i)
        (t : G.TorsionTower A), IsAbelianScheme A ∧ t.baseChange h = t₀ ∧
        ∀ g : ℕ, SmoothOfRelativeDimension g A₀.hom → SmoothOfRelativeDimension g A.hom

def LiftHom : Prop :=
  ∀ (A : Over (Sp R)) [GrpObj A] (A₀ : Over (Sp R₀)) [GrpObj A₀] (i : A₀.left ⟶ A.left)
    (h : IsGrpPullback A₀ A (red R R₀) i), IsAbelianScheme A →
  ∀ (B : Over (Sp R)) [GrpObj B] (B₀ : Over (Sp R₀)) [GrpObj B₀] (j : B₀.left ⟶ B.left)
    (k : IsGrpPullback B₀ B (red R R₀) j), IsAbelianScheme B →
  ∀ (G H : PDivGroup p R) (t : G.TorsionTower A) (u : H.TorsionTower B) (f₀ : A₀ ⟶ B₀) [IsMonHom f₀] (φ : G ⟶ H),
    PDivGroup.baseChangeMap R₀ φ = (t.baseChange h).map (u.baseChange k) f₀ →
      ∃! f : A ⟶ B, ∃ _ : IsMonHom f, i ≫ f.left = f₀.left ≫ j ∧ t.map u f = φ

def RigidAbelian : Prop :=
  ∀ (A : Over (Sp R)) [GrpObj A] (A₀ : Over (Sp R₀)) [GrpObj A₀] (i : A₀.left ⟶ A.left),
    IsGrpPullback A₀ A (red R R₀) i → IsAbelianScheme A →
  ∀ (B : Over (Sp R)) [GrpObj B], IsAbelianScheme B →
  ∀ f f' : A ⟶ B, IsMonHom f → IsMonHom f' → i ≫ f.left = i ≫ f'.left → f = f'

def RigidPDiv : Prop :=
  ∀ (G H : PDivGroup p R) (φ φ' : G ⟶ H), PDivGroup.baseChangeMap R₀ φ = PDivGroup.baseChangeMap R₀ φ' → φ = φ'

def LiftAct : Prop :=
  ∀ (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (A₀ : Over (Sp R₀)) [GrpObj A₀] [IsCommMonObj A₀]
    (i : A₀.left ⟶ A.left) (h : IsGrpPullback A₀ A (red R R₀) i), IsAbelianScheme A →
  ∀ (G : PDivGroup p R) (t : G.TorsionTower A) (Λ : Type) [Ring Λ] (a₀ : RingAct A₀ Λ) (ρ : Action Λ G),
    (∀ x, PDivGroup.baseChangeMap R₀ (ρ x : G ⟶ G) = ((t.baseChange h).ringAct a₀ x : _ ⟶ _)) →
      ∃! a : RingAct A Λ, (∀ x, i ≫ (a.act x).left = (a₀.act x).left ≫ i) ∧ t.ringAct a = ρ

def LiftDual : Prop :=
  ∀ (A : Over (Sp R)) [GrpObj A] (A₀ : Over (Sp R₀)) [GrpObj A₀] (i : A₀.left ⟶ A.left),
    IsGrpPullback A₀ A (red R R₀) i → IsAbelianScheme A →
  ∀ (B₀ : Over (Sp R₀)) [GrpObj B₀] (P₀ : LB (A₀ ⊗ B₀).left), IsAbelianScheme B₀ → IsDual A₀ B₀ P₀ →
    ∃ (B : Over (Sp R)) (_ : GrpObj B) (j : B₀.left ⟶ B.left) (P : LB (A ⊗ B).left),
      IsAbelianScheme B ∧ IsGrpPullback B₀ B (red R R₀) j ∧ IsDual A B P ∧ IsPairRed i j P P₀

def LiftPol : Prop :=
  ∀ (A : Over (Sp R)) [GrpObj A] (A₀ : Over (Sp R₀)) [GrpObj A₀] (i : A₀.left ⟶ A.left)
    (h : IsGrpPullback A₀ A (red R R₀) i), IsAbelianScheme A →
  ∀ (B : Over (Sp R)) [GrpObj B] (B₀ : Over (Sp R₀)) [GrpObj B₀] (j : B₀.left ⟶ B.left),
    IsGrpPullback B₀ B (red R R₀) j → IsAbelianScheme B →
  ∀ (P : LB (A ⊗ B).left) (P₀ : LB (A₀ ⊗ B₀).left), IsDual A B P → IsDual A₀ B₀ P₀ → IsPairRed i j P P₀ →
  ∀ (G : PDivGroup p R) (t : G.TorsionTower A) (lam₀ : A₀ ⟶ B₀) (ψ : G ⟶ G.dual), IsPolarisation A₀ B₀ P₀ lam₀ →
    IsWeilHom (t.baseChange h) (t.baseChange h) (polBundle P₀ lam₀)
      (PDivGroup.baseChangeMap R₀ ψ ≫ (dualBaseChange R₀ G).inv) →
      ∃! lam : A ⟶ B, IsPolarisation A B P lam ∧ i ≫ lam.left = lam₀.left ≫ j ∧ IsWeilHom t t (polBundle P lam) ψ

def RigidBundle : Prop :=
  ∀ (A : Over (Sp R)) [GrpObj A] (A₀ : Over (Sp R₀)) [GrpObj A₀] (i : A₀.left ⟶ A.left),
    IsGrpPullback A₀ A (red R R₀) i → IsAbelianScheme A →
  ∀ (C : Over (Sp R)) [GrpObj C] (C₀ : Over (Sp R₀)) [GrpObj C₀] (j : C₀.left ⟶ C.left),
    IsGrpPullback C₀ C (red R R₀) j → IsAbelianScheme C →
  ∀ (Q Q' : LB (A ⊗ C).left) (Q₀ : LB (A₀ ⊗ C₀).left), Q.IsLB → Q'.IsLB → Q₀.IsLB →
    IsAdditive Q → IsAdditive (swap Q) → IsAdditive Q' → IsAdditive (swap Q') →
    IsPairRed i j Q Q₀ → IsPairRed i j Q' Q₀ → LBIso Q Q'

def At : Prop :=
  HasTower p R ∧ DualTower p R ∧ LiftObj p R R₀ ∧ LiftHom p R R₀ ∧ RigidAbelian R R₀ ∧ RigidPDiv p R R₀ ∧
    LiftAct p R R₀ ∧ LiftDual R R₀ ∧ LiftPol p R R₀ ∧ RigidBundle R R₀

end Clauses

def SerreTateSt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsArtinianRing R] [IsLocalRing R]
    [CharP (IsLocalRing.ResidueField R) p] [PerfectField (IsLocalRing.ResidueField R)]
    (R₀ : Type) [CommRing R₀] [Algebra R R₀], Function.Surjective (algebraMap R R₀) →
    IsNilpotent (RingHom.ker (algebraMap R R₀)) → At p R R₀

section Functor

variable {p : ℕ} [Fact p.Prime] {R R₀ : Type} [CommRing R] [CommRing R₀] [Algebra R R₀]
  {A B : Over (Sp R)} [GrpObj A] [GrpObj B] {A₀ B₀ : Over (Sp R₀)} [GrpObj A₀] [GrpObj B₀]
  {i : A₀.left ⟶ A.left} {j : B₀.left ⟶ B.left} {G H : PDivGroup p R}

theorem weilIs_push {S S' : Scheme.{0}} {X : Over S} {X' : Over S'} [GrpObj X] [GrpObj X'] [IsCommMonObj X]
    {f : S' ⟶ S} {φ : X'.left ⟶ X.left} {L : LB X.left} {L' : LB X'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (hp : IsGrpPullback X' X f φ) (hw : LBIso L' (L.pull φ)) (T : Over S') (g : T.left ⟶ S) (hg : g = T.hom ≫ f)
    (k : ℤ) (x y : T ⟶ X') (x₀ y₀ : Over.mk g ⟶ X) (c : Γ(T.left, ⊤)ˣ) (ex : x₀.left = x.left ≫ φ)
    (ey : y₀.left = y.left ≫ φ) (h : Out.WeilIs X L k x₀ y₀ c) : Out.WeilIs X' L' k x y c := by
  subst hg
  exact (weilIs_iff_of_isGrpPullback_comm _ _ _ _ _ _ _ _ hL hL' hp hw T k x y x₀ y₀ c ex ey).2 h

omit [Algebra R R₀] [GrpObj A] [GrpObj B] [GrpObj A₀] [GrpObj B₀] in

theorem IsPairRed.polBundle {P : LB (A ⊗ B).left} {P₀ : LB (A₀ ⊗ B₀).left} (hP : P.IsLB) (hP₀ : P₀.IsLB)
    (r : IsPairRed i j P P₀) {lam : A ⟶ B} {lam₀ : A₀ ⟶ B₀} (e : i ≫ lam.left = lam₀.left ≫ j)
    {l : (A₀ ⊗ A₀).left ⟶ (A ⊗ A).left} (l₁ : l ≫ (fst A A).left = (fst A₀ A₀).left ≫ i)
    (l₂ : l ≫ (snd A A).left = (snd A₀ A₀).left ≫ i) : IsPairRed i i (polBundle P lam) (polBundle P₀ lam₀) := by
  obtain ⟨m, m₁, m₂, hm⟩ := r
  refine ⟨l, l₁, l₂, (CechPic.cls_eq_iff (pull_isLB hP₀ _) (pull_isLB (pull_isLB hP _) _)).1 ?_⟩
  rw [CechPic.cls_pull hP₀, CechPic.cls_pull (pull_isLB hP _), CechPic.cls_pull hP,
    (CechPic.cls_eq_iff hP₀ (pull_isLB hP _)).2 hm, CechPic.cls_pull hP, ← CechPic.pull_comp, ← CechPic.pull_comp]
  congr 2
  apply pullback.hom_ext
  · change (_ ≫ m) ≫ (fst A B).left = (l ≫ _) ≫ (fst A B).left
    rw [Category.assoc, m₁, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
      lift_fst, l₁]
  · change (_ ≫ m) ≫ (snd A B).left = (l ≫ _) ≫ (snd A B).left
    rw [Category.assoc, m₂, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
      lift_snd, Over.comp_left, Over.comp_left, Category.assoc, ← e, ← Category.assoc, ← l₂, Category.assoc]

omit [Fact p.Prime] in

theorem exists_isWeilHom (hA : IsAbelianScheme A) {P : LB (A ⊗ B).left} (hP : IsDual A B P) (lam : A ⟶ B)
    (t : G.TorsionTower A) : ∃ ψ : G ⟶ G.dual, IsWeilHom t t (polBundle P lam) ψ := by
  have hAA := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have := hAA.comm
  have hQ : (polBundle P lam).IsLB := pull_isLB hP.isLB _
  obtain ⟨r, hr⟩ : AbLaw.Triv ((polBundle P lam).pull (eSec (A ⊗ A))) := by
    have e' : CartesianMonoidalCategory.lift (1 : 𝟙_ (Over (Sp R)) ⟶ A) (1 : 𝟙_ (Over (Sp R)) ⟶ A) = η[A ⊗ A] := by
      ext <;> simp [Hom.one_def]
    have e := (AbDual.triv_ev_iff hQ (1 : 𝟙_ (Over (Sp R)) ⟶ A) (1 : 𝟙_ (Over (Sp R)) ⟶ A)).2 (by
      rw [evc_ev hP.isLB, lift_fst]
      exact hP.additive.evc_one hP.isLB _)
    rw [AbDual.ev, e'] at e
    exact e
  obtain ⟨τ, hτ⟩ := WeilHom.triv_theta CubeTop.cubeTheorem hAA hQ
  obtain ⟨τ', hτ', hn⟩ := AbLaw.Cube.exists_normalised hQ τ hτ
  exact WeilHom.exists_of_cubical hAA
    (AbLaw.Cube.cubicalOfNormalised globalFns_holds hAA ⟨polBundle P lam, r, hQ, hr⟩ τ' hτ' hn) t t

theorem isWeilHom_baseChange (hA : IsAbelianScheme A) (h : IsGrpPullback A₀ A (red R R₀) i) {Q : LB (A ⊗ A).left}
    {Q₀ : LB (A₀ ⊗ A₀).left} (hQ : Q.IsLB) (hQ₀ : Q₀.IsLB) (r : IsPairRed i i Q Q₀) (t : G.TorsionTower A)
    {ψ : G ⟶ G.dual} (hψ : IsWeilHom t t Q ψ) :
    IsWeilHom (t.baseChange h) (t.baseChange h) Q₀
      (PDivGroup.baseChangeMap R₀ ψ ≫ (dualBaseChange R₀ G).inv) := by
  intro n
  obtain ⟨l, l₁, l₂, hl⟩ := r
  obtain ⟨U, hU, e⟩ := hψ n
  have hAA := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have := hAA.comm
  let α := WeilIntegral.twoMap (R := R) (K := R₀) (G.A n)
  refine ⟨Units.map (α : G.A n ⊗[R] G.A n →+* _).toMonoidHom U, ?_, fun χ => ?_⟩
  · have hg : spMap (algebraMap R ((R₀ ⊗[R] G.A n) ⊗[R₀] (R₀ ⊗[R] G.A n))) =
        (SpAlg R₀ ((R₀ ⊗[R] G.A n) ⊗[R₀] (R₀ ⊗[R] G.A n))).hom ≫ red R R₀ := by
      rw [IsScalarTower.algebraMap_eq R R₀, Cris.spMap_comp]
      rfl
    have hy : ∀ (bb : R₀ ⊗[R] G.A n →ₐ[R₀] (R₀ ⊗[R] G.A n) ⊗[R₀] (R₀ ⊗[R] G.A n))
        (gg : G.A n →ₐ[R] G.A n ⊗[R] G.A n), (∀ a, α (gg a) = bb (1 ⊗ₜ a)) →
        (spOver bb ≫ (t.baseChange h).y n).left ≫ i =
          spMap (α : G.A n ⊗[R] G.A n →+* _) ≫ (spOver gg ≫ t.y n).left := fun bb gg hβ => by
      rw [Over.comp_left, Over.comp_left, Category.assoc, ← t.toBase_y h n, spOver_left, spOver_left,
        ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp]
      exact congrArg (fun q => spMap q ≫ (t.y n).left) (RingHom.ext fun a => (hβ a).symm)
    have hτ : spMap (α : G.A n ⊗[R] G.A n →+* _) ≫ (SpAlg R (G.A n ⊗[R] G.A n)).hom =
        (SpAlg R₀ ((R₀ ⊗[R] G.A n) ⊗[R₀] (R₀ ⊗[R] G.A n))).hom ≫ red R R₀ := (Over.w (spOver α)).trans hg
    have o := WeilIntegral.one_left_comm h (T := SpAlg R (G.A n ⊗[R] G.A n))
      (T' := SpAlg R₀ ((R₀ ⊗[R] G.A n) ⊗[R₀] (R₀ ⊗[R] G.A n))) _ hτ
    refine weilIs_push hQ hQ₀ (WeilIntegral.isGrpPullback_prod h h l₁ l₂) hl _ _ hg _ _ _ _ _ _ ?_ ?_
      (WeilAdjoint.weilIs_algHom hAA hQ α rfl rfl hU)
    · refine (WeilIntegral.lift_left_comm l₁ l₂ _ (hy _ _ fun a => ?_) o).symm
      simp only [α, Algebra.TensorProduct.includeLeft_apply, WeilIntegral.twoMap_tmul]
      rfl
    · refine (WeilIntegral.lift_left_comm l₁ l₂ _ o (hy _ _ fun a => ?_)).symm
      simp only [α, Algebra.TensorProduct.includeRight_apply,
        WeilIntegral.twoMap_tmul]
      rfl
  · have key : ∀ x : R₀ ⊗[R] CartierDual R (G.A n), bcMap R₀ (ψ.app n) x = TensorProduct.rid R₀ _
        ((CartierDual.baseChange R R₀ (G.A n) x).ofConv.lTensor _ (α U.val)) := fun x => by
      induction x with
      | zero => simp
      | add x y hx hy =>
        rw [map_add, map_add, hx, hy, ← map_add, ← LinearMap.add_apply, ← LinearMap.lTensor_add]
        rfl
      | tmul c χ =>
        have ec : c ⊗ₜ[R] χ = c • ((1 : R₀) ⊗ₜ[R] χ) := by rw [smul_tmul', smul_eq_mul, _root_.mul_one]
        rw [ec, map_smul, map_smul]
        refine Eq.trans ?_ (congrArg (fun q => TensorProduct.rid R₀ _ (q (α U.val)))
          (LinearMap.lTensor_smul _ c (CartierDual.baseChange R R₀ (G.A n) ((1 : R₀) ⊗ₜ χ)).ofConv)).symm
        rw [LinearMap.smul_apply, map_smul, WeilIntegral.contract_twoMap, ← e]
        rfl
    have hx : (CartierDual.baseChange R R₀ (G.A n)) ((dualBaseChange R₀ G).inv.app n χ) = χ :=
      (CartierDual.baseChange R R₀ (G.A n)).apply_symm_apply χ
    refine (key _).trans ?_
    erw [hx]
    rfl

end Functor

section Consequences

variable {p : ℕ} [Fact p.Prime] {R R₀ : Type} [CommRing R] [CommRing R₀] [Algebra R R₀]

theorem At.exists_lift (H : At p R R₀) (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀] [IsCommMonObj A₀]
    (hA₀ : IsAbelianScheme A₀) (hB₀ : IsAbelianScheme B₀) {P₀ : LB (A₀ ⊗ B₀).left} (hP₀ : IsDual A₀ B₀ P₀)
    {Λ : Type} [Ring Λ] (a₀ : RingAct A₀ Λ) {lam₀ : A₀ ⟶ B₀} (hl : IsPolarisation A₀ B₀ P₀ lam₀)
    (G : PDivGroup p R) (t₀ : (G.baseChange R₀).TorsionTower A₀) (ρ : Action Λ G)
    (hρ : ∀ x, PDivGroup.baseChangeMap R₀ (ρ x : G ⟶ G) = (t₀.ringAct a₀ x : _ ⟶ _)) (ψ : G ⟶ G.dual)
    (hψ : IsWeilHom t₀ t₀ (polBundle P₀ lam₀) (PDivGroup.baseChangeMap R₀ ψ ≫ (dualBaseChange R₀ G).inv)) :
    ∃ (A B : Over (Sp R)) (_ : GrpObj A) (_ : GrpObj B) (_ : IsCommMonObj A) (i : A₀.left ⟶ A.left)
      (j : B₀.left ⟶ B.left) (h : IsGrpPullback A₀ A (red R R₀) i) (t : G.TorsionTower A) (P : LB (A ⊗ B).left)
      (a : RingAct A Λ) (lam : A ⟶ B), IsAbelianScheme A ∧ IsAbelianScheme B ∧ IsGrpPullback B₀ B (red R R₀) j ∧
      IsDual A B P ∧ IsPairRed i j P P₀ ∧ t.baseChange h = t₀ ∧
      (∀ x, i ≫ (a.act x).left = (a₀.act x).left ≫ i) ∧ t.ringAct a = ρ ∧
      IsPolarisation A B P lam ∧ i ≫ lam.left = lam₀.left ≫ j ∧ IsWeilHom t t (polBundle P lam) ψ := by
  obtain ⟨-, -, H₁, -, -, -, H₂, H₃, H₄, -⟩ := H
  obtain ⟨A, _, i, h, t, hA, rfl, -⟩ := H₁ A₀ hA₀ G t₀
  have := hA.comm
  obtain ⟨B, _, j, P, hB, k, hP, r⟩ := H₃ A A₀ i h hA B₀ P₀ hB₀ hP₀
  obtain ⟨a, ⟨a₁, a₂⟩, -⟩ := H₂ A A₀ i h hA G t Λ a₀ ρ hρ
  obtain ⟨lam, ⟨l₁, l₂, l₃⟩, -⟩ := H₄ A A₀ i h hA B B₀ j k hB P P₀ hP hP₀ r G t lam₀ ψ hl hψ
  exact ⟨A, B, _, _, this, i, j, h, t, P, a, lam, hA, hB, k, hP, r, rfl, a₁, a₂, l₁, l₂, l₃⟩

end Consequences

section Base

abbrev Zmod4 : Type := ZMod (2 ^ 2)

instance : Fact (1 < 2 ^ 2) := ⟨by norm_num⟩

instance : IsLocalRing Zmod4 := IsLocalRing.of_surjective' (PadicInt.toZModPow 2) (ZMod.ringHom_surjective _)

instance : Finite (IsLocalRing.ResidueField Zmod4) :=
  Finite.of_surjective _ (IsLocalRing.residue_surjective (R := Zmod4))

theorem two_mem : ((2 : ℕ) : Zmod4) ∈ IsLocalRing.maximalIdeal Zmod4 := fun h => by
  have h4 := h.mul h
  rw [show ((2 : ℕ) : Zmod4) * ((2 : ℕ) : Zmod4) = 0 by decide] at h4
  exact not_isUnit_zero h4

instance : CharP (IsLocalRing.ResidueField Zmod4) 2 := by
  refine (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 ?_
  rw [← map_natCast (IsLocalRing.residue Zmod4)]
  exact (IsLocalRing.residue_eq_zero_iff _).2 two_mem

end Base

section Elliptic

open GlobalTheory.WeierstrassCurve (ellPolAV)

def curve : _root_.WeierstrassCurve ℤ_[2] := ⟨0, 0, 1, 0, 0⟩

instance : curve.IsElliptic := by
  refine ⟨?_⟩
  have e : curve.Δ = ((-27 : ℤ) : ℤ_[2]) := by
    simp [curve, _root_.WeierstrassCurve.Δ, _root_.WeierstrassCurve.b₂, _root_.WeierstrassCurve.b₄,
      _root_.WeierstrassCurve.b₆, _root_.WeierstrassCurve.b₈]
  rw [e, PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => ?_)
  have := (PadicInt.norm_int_lt_one_iff_dvd (-27)).1 h
  omega

variable (R R₀ : Type) [CommRing R] [CommRing R₀] [Algebra R R₀] [IsNoetherianRing R] [IsNoetherianRing R₀]

theorem elliptic_hyps (f : ℤ_[2] →+* R) : ∃ (A : Over (Sp R)) (_ : GrpObj A) (A₀ : Over (Sp R₀)) (_ : GrpObj A₀)
    (i : A₀.left ⟶ A.left) (h : IsGrpPullback A₀ A (red R R₀) i) (G : PDivGroup 2 R) (t : G.TorsionTower A)
    (P : LB (A ⊗ A).left) (P₀ : LB (A₀ ⊗ A₀).left) (ψ : G ⟶ G.dual),
    IsAbelianScheme A ∧ IsAbelianScheme A₀ ∧ SmoothOfRelativeDimension 1 A.hom ∧ G.height = 2 ∧
    IsDual A A P ∧ IsDual A₀ A₀ P₀ ∧ IsPairRed i i P P₀ ∧ IsPolarisation A A P (𝟙 A) ∧
    IsPolarisation A₀ A₀ P₀ (𝟙 A₀) ∧ IsWeilHom t t (polBundle P (𝟙 A)) ψ ∧
    IsWeilHom (t.baseChange h) (t.baseChange h) (polBundle P₀ (𝟙 A₀))
      (PDivGroup.baseChangeMap R₀ ψ ≫ (dualBaseChange R₀ G).inv) := by
  let _ : Algebra ℤ_[2] R := f.toAlgebra
  let W := curve.map f
  let E := ellPolAV W
  let E₀ := ellPolAV (W.map (algebraMap R R₀))
  let i := WeierstrassCurve.mapHom W (algebraMap R R₀) rfl
  have h : IsGrpPullback E₀.A E.A (red R R₀) i :=
    WeierstrassCurve.isGrpPullback_ellPolAV W (algebraMap R R₀) rfl
  have hO := WeierstrassCurve.isGrpPullback_ellPolAV curve f rfl
  obtain ⟨GO, hGO, ⟨tO⟩⟩ := AbelianPDiv.exists_pDivGroup 2 ℤ_[2] (by norm_num) (ellPolAV curve).A
    (ellPolAV curve).isAb 1 ((WeierstrassCurve.ellPolAV_g curve) ▸ (ellPolAV curve).smoothDim)
  let t := tO.baseChange (A' := E.A) hO
  obtain ⟨-, hA, hP, hl⟩ := CompanionTheory.Hypotheses₂.Zarhin.hyp_elliptic dualAbelianScheme W
  obtain ⟨-, hA₀, hP₀, hl₀⟩ := CompanionTheory.Hypotheses₂.Zarhin.hyp_elliptic dualAbelianScheme (W.map (algebraMap R R₀))
  have := hA.comm
  have := hA₀.comm
  obtain ⟨β₂, ⟨b₁, b₂⟩, hβ⟩ := Mum.lbIso_lam_pull_of_isGrpPullback _ _ _ E.A E₀.A _ h
  have hΛ : (abelian₂ E.A E.L).IsLB := LB.isLB_linComb E.isLB _ _
  have r : IsPairRed i i (abelian₂ E.A E.L) (abelian₂ E₀.A E₀.L) := by
    refine ⟨β₂, b₁, b₂, ?_⟩
    have k := hβ E.L E₀.L _ (abelian₂ E.A E.L) (𝟙 _) E.isLB E₀.isLB hΛ
      (WeierstrassCurve.lbIso_ellPolAV W (algebraMap R R₀) rfl)
      ((CechPic.cls_eq_iff hΛ (pull_isLB hΛ _)).1 (by rw [CechPic.cls_pull hΛ, CechPic.pull_id]))
    rwa [Category.comp_id] at k
  obtain ⟨ψ, hψ⟩ := exists_isWeilHom hA hP (𝟙 E.A) t
  obtain ⟨l, l₁, l₂⟩ := exists_prod_pullback h h
  refine ⟨E.A, inferInstance, E₀.A, inferInstance, i, h, _, t, _, _, ψ, hA, hA₀,
    (WeierstrassCurve.ellPolAV_g W) ▸ E.smoothDim, hGO, hP, hP₀, r, hl, hl₀, hψ, ?_⟩
  exact isWeilHom_baseChange hA h (pull_isLB hΛ _) (pull_isLB (LB.isLB_linComb E₀.isLB _ _) _)
    (r.polBundle hΛ (LB.isLB_linComb E₀.isLB _ _)
      (by rw [Over.id_left, Over.id_left]; exact (Category.comp_id _).trans (Category.id_comp _).symm) l₁ l₂) t hψ

example : True := by
  have := elliptic_hyps Zmod4 (IsLocalRing.ResidueField Zmod4) (PadicInt.toZModPow 2)
  trivial

end Elliptic

end GlobalTheory.SerreTateDef
