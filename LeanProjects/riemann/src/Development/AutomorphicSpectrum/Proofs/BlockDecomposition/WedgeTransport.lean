import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.HodgeO

section Transport

variable {R : Type} [CommRing R]

theorem finrank_of_vb {k M : Type} [Field k] [AddCommGroup M] [Module k M] {g : ℕ} (h : VB k M g) :
    Module.finrank k M = g := by
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum k) := inferInstance
  have e := congrFun (Module.rankAtStalk_eq_finrank_of_free (R := k) (M := M)) p
  exact e.symm.trans (h.2.2 p)

theorem vb_of_equiv {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {g : ℕ}
    (e : M ≃ₗ[R] N) (h : VB R M g) : VB R N g :=
  have := h.1
  have := h.2.1
  ⟨Module.Finite.equiv e, Module.Projective.of_equiv e, fun p ↦
    (congrFun (Module.rankAtStalk_eq_of_equiv e) p).symm.trans (h.2.2 p)⟩

def wedgeEquiv {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    ⋀[R]^2 M ≃ₗ[R] ⋀[R]^2 N :=
  LinearEquiv.ofLinear (exteriorPower.map 2 e.toLinearMap) (exteriorPower.map 2 e.symm.toLinearMap)
    (by rw [← exteriorPower.map_comp]; simp)
    (by rw [← exteriorPower.map_comp]; simp)

theorem wedge_transport {M M' N N' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N'] (e₁ : M ≃ₗ[R] M') (e₂ : N ≃ₗ[R] N')
    (B : M → M → N) (B' : M' → M' → N') (hB : ∀ a b, e₂ (B a b) = B' (e₁ a) (e₁ b))
    (h : ∃ e : ⋀[R]^2 M ≃ₗ[R] N, ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = B a b) :
    ∃ e : ⋀[R]^2 M' ≃ₗ[R] N', ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = B' a b := by
  obtain ⟨e, he⟩ := h
  refine ⟨(wedgeEquiv e₁.symm).trans (e.trans e₂), fun a b ↦ ?_⟩
  have k : wedgeEquiv e₁.symm (exteriorPower.ιMulti R 2 ![a, b]) =
      exteriorPower.ιMulti R 2 ![e₁.symm a, e₁.symm b] := by
    refine (exteriorPower.map_apply_ιMulti _ _).trans (congrArg _ ?_)
    funext i
    fin_cases i <;> rfl
  simp only [LinearEquiv.trans_apply]
  rw [k, he, hB, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

variable {C C' : Type} [Category.{0} C] [Category.{0} C'] {F : C ⥤ CommAlgCat.{0} R}
  {F' : C' ⥤ CommAlgCat.{0} R}

theorem wedge_of_bij (m : CoefMap (RingHom.id R) F F') (h₁ : Function.Bijective m.pull1)
    (h₂ : Function.Bijective m.pull2) (h : Wedge F) : Wedge F' :=
  wedge_transport (LinearEquiv.ofBijective m.pull1 h₁) (LinearEquiv.ofBijective m.pull2 h₂)
    (fun a b ↦ cup F a b) (fun a b ↦ cup F' a b) (fun a b ↦ m.pullCohomologyTwo_cup a b) h

theorem wedge_of_bij' (m : CoefMap (RingHom.id R) F F') (h₁ : Function.Bijective m.pull1)
    (h₂ : Function.Bijective m.pull2) (h : Wedge F') : Wedge F :=
  wedge_transport (LinearEquiv.ofBijective m.pull1 h₁).symm (LinearEquiv.ofBijective m.pull2 h₂).symm
    (fun a b ↦ cup F' a b) (fun a b ↦ cup F a b) (fun a b ↦ by
      refine (LinearEquiv.symm_apply_eq _).2 ?_
      refine Eq.trans ?_ (m.pullCohomologyTwo_cup _ _).symm
      change _ = cup F' (LinearEquiv.ofBijective m.pull1 h₁ _) (LinearEquiv.ofBijective m.pull1 h₁ _)
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]) h

theorem hopf_false {b : Prop} (h : Hopf F b) : Hopf F False := by
  obtain ⟨D, _, G, π, m, h₁, h₂, -⟩ := h
  exact ⟨D, _, G, π, m, h₁, h₂, False.elim⟩

end Transport

theorem pack {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) {R' : Type} [CommRing R'] [Algebra R R'] (A' : Over (Sp R'))
    {i : GrpObj A'} (φ : A'.left ⟶ A.left) (hφ : IsGrpPullback A' A (spMap (algebraMap R R')) φ) :
    ∃ (A' : Over (Sp R')) (_ : GrpObj A') (φ : A'.left ⟶ A.left),
      IsPullback φ A'.hom A.hom (spMap (algebraMap R R')) ∧ IsAbelianScheme A' ∧
        SmoothOfRelativeDimension g A'.hom :=
  ⟨A', i, φ, hφ.1, GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hφ,
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hφ.1 hg⟩

theorem exists_base {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) (R' : Type) [CommRing R'] [Algebra R R'] :
    ∃ (A' : Over (Sp R')) (_ : GrpObj A') (φ : A'.left ⟶ A.left),
      IsPullback φ A'.hom A.hom (spMap (algebraMap R R')) ∧ IsAbelianScheme A' ∧
        SmoothOfRelativeDimension g A'.hom :=
  pack A g hA hg _ _ (isGrpPullback_pullback A (spMap (algebraMap R R')))

theorem low (hD : DescentSt) (hL : LowSt) {P : Type} [SemilatticeInf P] (R' : Type) [CommRing R'] (A' : Over (Sp R'))
    [GrpObj A'] (ha : IsAbelianScheme A') (S' : Sys A'.left P) :
    Function.Bijective (resSys A'.hom S').pull1 ∧ Function.Bijective (resSys A'.hom S').pull2 ∧
      (Stein (OAff A'.hom) ↔ Stein (OSys A'.hom S')) := by
  have := ha.proper
  exact hL R' _ _ (OAff A'.hom) (OSys A'.hom S') (resSys A'.hom S') (hD R' A'.left A'.hom inferInstance P S')

theorem base (hS : SysBCSt) {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) {P : Type} [SemilatticeInf P] (S : Sys A.left P) (R' : Type)
    [CommRing R'] [Algebra R R'] : ∃ (A' : Over (Sp R')) (_ : GrpObj A') (S' : Sys A'.left P)
      (_ : BC (OSys A.hom S) (OSys A'.hom S')), IsAbelianScheme A' ∧ SmoothOfRelativeDimension g A'.hom := by
  have pr := hA.proper
  have sep : IsSeparated A.hom := inferInstance
  obtain ⟨A', _, φ, h, ha, hg'⟩ := exists_base A g hA hg R'
  obtain ⟨S', m, -⟩ := hS R R' A.left A'.left A.hom A'.hom φ h sep P S
  exact ⟨A', _, S', m, ha, hg'⟩

theorem steinU (hD : DescentSt) (hL : LowSt) (hS : SysBCSt) (hSt : SteinSt) {R : Type} [CommRing R]
    (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    {P : Type} [SemilatticeInf P] (S : Sys A.left P) : SteinU (OSys A.hom S) := fun R' _ _ ↦ by
  obtain ⟨A', _, S', m, ha, hg'⟩ := base hS A g hA hg S R'
  exact ⟨_, m, (low hD hL R' A' ha S').2.2.1 (hSt R' A' g ha hg')⟩

theorem vbSys (hD : DescentSt) (hL : LowSt) (hH1 : H1StructureBundle) {R : Type} [CommRing R]
    (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    {P : Type} [SemilatticeInf P] (S : Sys A.left P) : VB R (H1 (OSys A.hom S)) g :=
  vb_of_equiv (LinearEquiv.ofBijective _ (low hD hL R A hA S).1) (hH1 R A g hA hg)

theorem finFib (hD : DescentSt) (hL : LowSt) (hS : SysBCSt) (hH1 : H1StructureBundle) {R : Type} [CommRing R]
    (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    {P : Type} [SemilatticeInf P] (S : Sys A.left P) (k : Type) [Field k] [Algebra R k] :
    ∃ (F' : Pᵒᵖ ⥤ CommAlgCat.{0} k) (_ : BC (OSys A.hom S) F'), Module.finrank k (H1 F') = g := by
  obtain ⟨A', _, S', m, ha, hg'⟩ := base hS A g hA hg S k
  exact ⟨_, m, finrank_of_vb (vbSys hD hL hH1 A' g ha hg' S')⟩

theorem wedgeFib (hD : DescentSt) (hL : LowSt) (hS : SysBCSt) (hWF : WedgeFieldSt) {R : Type} [CommRing R]
    (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    {P : Type} [SemilatticeInf P] (S : Sys A.left P) (k : Type) [Field k] [Algebra R k] :
    ∃ (F' : Pᵒᵖ ⥤ CommAlgCat.{0} k) (_ : BC (OSys A.hom S) F'), Wedge F' := by
  obtain ⟨A', _, S', m, ha, hg'⟩ := base hS A g hA hg S k
  have b := low hD hL k A' ha S'
  exact ⟨_, m, wedge_of_bij (resSys A'.hom S') b.1 b.2.1 (hWF k A' g ha hg' (Field.toIsField k))⟩

theorem coreSys (hD : DescentSt) (hL : LowSt) (hS : SysBCSt) (hSt : SteinSt) (hH1 : H1StructureBundle)
    (hWF : WedgeFieldSt) (hHopf : HopfSt) (hPH1 : PerfectH1BaseChange) (hPH2 : PerfectH2FromFibres) (hWO : WedgeOfSt)
    {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) {P : Type} [SemilatticeInf P] [Finite P] (S : Sys A.left P)
    (hPf : Perf (OSys A.hom S)) : H1CommutesBaseChange (OSys A.hom S) ∧ Wedge (OSys A.hom S) := by
  have hSU := steinU hD hL hS hSt A g hA hg S
  have hV := vbSys hD hL hH1 A g hA hg S
  have hB : H1CommutesBaseChange (OSys A.hom S) := hPH1 R P (OSys A.hom S) g hPf hSU hV fun k _ _ ↦
    finFib hD hL hS hH1 A g hA hg S k
  obtain ⟨h2, hs⟩ := hPH2 R P (OSys A.hom S) g hPf hSU hV hB fun k _ _ ↦
    wedgeFib hD hL hS hWF A g hA hg S k
  exact ⟨hB, hWO R P (OSys A.hom S) g (hopf_false (hHopf R A g hA hg P S)) hV hB h2 hs⟩

theorem oBC_wedge : DescentSt → LowSt → SysBCSt → PerfSt → SteinSt → H1StructureBundle → WedgeFieldSt → HopfSt → PerfectH1BaseChange →
    PerfectH2FromFibres → WedgeOfSt → OBCSt ∧ WedgeSt := by
  intro hD hL hS hP hSt hH1 hWF hHopf hPH1 hPH2 hWO
  refine ⟨?_, ?_⟩
  · intro R _ A _ g hA hg R' _ _ X' s' φ h
    have pr := hA.proper
    have sep : IsSeparated A.hom := inferInstance
    have sep' : IsSeparated s' := MorphismProperty.of_isPullback h sep
    obtain ⟨P, _, _, S, hPf⟩ := hP R A.left A.hom hA.smooth pr
    have hB := (coreSys hD hL hS hSt hH1 hWF hHopf hPH1 hPH2 hWO A g hA hg S hPf).1
    obtain ⟨S', m, hc⟩ := hS R R' A.left X' A.hom s' φ h sep P S
    obtain ⟨e₀, he₀⟩ := hB R' _ m
    have b₁ := (hL R _ _ _ _ (resSys A.hom S) (hD R A.left A.hom sep P S)).1
    have b₂ := (hL R' _ _ _ _ (resSys s' S') (hD R' X' s' sep' P S')).1
    let e₁ := LinearEquiv.ofBijective _ b₁
    let e₂ := LinearEquiv.ofBijective _ b₂
    refine ⟨(LinearEquiv.baseChange R R' _ _ e₁).trans (e₀.trans e₂.symm), fun c ↦ hc c _ ?_⟩
    refine (he₀ _).symm.trans ?_
    exact (e₂.apply_symm_apply _).symm
  · intro R _ A _ g hA hg
    have pr := hA.proper
    obtain ⟨P, _, _, S, hPf⟩ := hP R A.left A.hom hA.smooth pr
    have hW := (coreSys hD hL hS hSt hH1 hWF hHopf hPH1 hPH2 hWO A g hA hg S hPf).2
    have b := low hD hL R A hA S
    exact wedge_of_bij' (resSys A.hom S) b.1 b.2.1 hW

end GlobalTheory.CompanionTheory.HodgeO
