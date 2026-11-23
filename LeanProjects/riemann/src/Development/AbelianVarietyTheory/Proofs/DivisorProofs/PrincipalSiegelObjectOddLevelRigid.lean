import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidCube
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidFiniteOrder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidSeparated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidSerreAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidLevelRigid

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegRigid

open GlobalTheory.CechPic GlobalTheory.AmpleRigid

theorem serreAmple : SerreAmpleSt :=
  serreAmple_of_finiteOrder_of_separated (GlobalTheory.AmpleFiniteOrder.finiteOrder_of_const_of_cube constSt GlobalTheory.AmpleCube.cubeSt)
    (separatedSt_of_const_cube constSt GlobalTheory.AmpleCube.cubeSt)

theorem exists_aut {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ φ' : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) (h' : IsGrpPullback A' A f φ') :
    ∃ σ : A' ≅ A', IsMonHom σ.hom ∧ σ.hom.left ≫ φ' = φ := by
  let ψ : A'.left ⟶ A'.left := h'.1.lift φ A'.hom h.1.w
  have e₁ : ψ ≫ φ' = φ := h'.1.lift_fst _ _ _
  have e₂ : ψ ≫ A'.hom = A'.hom := h'.1.lift_snd _ _ _
  have hψ : IsGrpPullback A' A' (𝟙 _) ψ :=
    IsGrpPullback.cancel h' (by rw [Category.id_comp, e₁]; exact h) (by rw [e₂, Category.comp_id])
  haveI : IsIso ψ := hψ.1.isIso_fst_of_isIso
  let σ : A' ≅ A' := Over.isoMk (asIso ψ) e₂
  exact ⟨σ, isMonHom_of_mul_comp σ.hom fun T x y => mul_comp_of_grpPullback_id σ.hom hψ x y, e₁⟩

theorem eq_of_field {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) (hamp : Out.RelAmple A L)
    {K : Type} [Field K] [IsAlgClosed K] {A' : Over (Sp K)} [GrpObj A'] (hA' : IsAbelianScheme A') {z : Sp K ⟶ S}
    {φ φ' : A'.left ⟶ A.left} (h : IsGrpPullback A' A z φ) (h' : IsGrpPullback A' A z φ')
    (hc : pull φ (cls L hL) = pull φ' (cls L hL)) {N : ℕ} (hN : 3 ≤ N) (hNK : (N : K) ≠ 0)
    (hfix : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Sp K) (x : Over.mk t ⟶ A'), x ^ N = 1 →
      x.left ≫ φ = x.left ≫ φ') : φ = φ' := by
  obtain ⟨σ, hσ, e⟩ := exists_aut h h'
  have := hA'.comm
  have hL' := pull_isLB hL φ'
  obtain ⟨w, hw⟩ := (cls_eq_iff hL' hL').1 rfl
  obtain ⟨U, hU, hcl, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤)
    (x := z (IsLocalRing.closedPoint K)) trivial
  have hy : ∀ y, z y ∈ U := fun y =>
    (congrArg (fun V => y ∈ V) (Scheme.preimage_eq_top_of_closedPoint_mem z hcl)).mpr trivial
  have key := serreAmple K A' hA' (L.pull φ') hL'
    (relAmple_pull h'.1 hL hL' ((isGen_iff w).1 hw) U hU hy hamp) N hN hNK σ hσ
    (by rw [cls_pull hL, ← pull_comp, e, hc]) fun Ω _ _ t x hx => by
      apply Over.OverMorphism.ext
      apply h'.1.hom_ext
      · rw [Over.comp_left, Category.assoc, e]
        exact hfix Ω t x hx
      · rw [Over.w, Over.w]
  rw [← e, key, Over.id_left, Category.id_comp]

variable {h n n' : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'} {S S' : Scheme.{0}}
  {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'}

theorem pull_cls_diag {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {φ : c'.A.left ⟶ c.A.left}
    {φ₂ : (G2 c'.A).left ⟶ (G2 c.A).left} (hs : IsSquare φ φ₂) (hw : LBIso c'.P (c.P.pull φ₂)) :
    pull φ (cls c.diag (pull_isLB c.isLB _)) = cls c'.diag (pull_isLB c'.isLB _) := by
  have e : (lift (𝟙 c'.A) (𝟙 c'.A)).left ≫ φ₂ = φ ≫ (lift (𝟙 c.A) (𝟙 c.A)).left := by
    have a₁ := congrArg (fun q => q.left) (lift_fst (𝟙 c.A) (𝟙 c.A))
    have a₂ := congrArg (fun q => q.left) (lift_snd (𝟙 c.A) (𝟙 c.A))
    have b₁ := congrArg (fun q => q.left) (lift_fst (𝟙 c'.A) (𝟙 c'.A))
    have b₂ := congrArg (fun q => q.left) (lift_snd (𝟙 c'.A) (𝟙 c'.A))
    simp only [Over.comp_left, Over.id_left] at a₁ a₂ b₁ b₂
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst c.A c.A).left = (_ ≫ _) ≫ (fst c.A c.A).left
      rw [Category.assoc, hs.1, ← Category.assoc, b₁, Category.assoc, a₁]; simp
    · show (_ ≫ _) ≫ (snd c.A c.A).left = (_ ≫ _) ≫ (snd c.A c.A).left
      rw [Category.assoc, hs.2, ← Category.assoc, b₂, Category.assoc, a₂]; simp
  have h1 : pull φ₂ (cls c.P c.isLB) = cls c'.P c'.isLB :=
    ((cls_eq_iff c'.isLB (pull_isLB c.isLB φ₂)).2 hw).symm
  unfold SiegPre.diag
  rw [cls_pull c.isLB, cls_pull c'.isLB, ← pull_comp, ← e, pull_comp, h1]

theorem eq_on_torsion (hζ : IsUnit ζ) (c : SiegPre h n ζ s) {A' : Over S'} [GrpObj A'] {f : S' ⟶ S}
    {φ φ' : A'.left ⟶ c.A.left} (hφ : IsGrpPullback A' c.A f φ)
    (lv : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S') ⟶ A'))
    (h₁ : ∀ a, (lv a).left ≫ φ = f ≫ (c.lev a).left) (h₂ : ∀ a, (lv a).left ≫ φ' = f ≫ (c.lev a).left)
    (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S') (y : Over.mk x ⟶ A') (hy : y ^ n = 1) :
    y.left ≫ φ = y.left ≫ φ' := by
  let β : B →+* k := (Spec.preimage ((x ≫ f) ≫ s)).hom
  obtain ⟨-, hs, -⟩ := c.geom k (x ≫ f) β (hζ.map β).unit (Spec.map_preimage _).symm rfl
  have hy₁ : pushHom hφ (Over.mk x) y ^ n = 1 := by rw [← map_pow, hy, map_one]
  obtain ⟨a, ha⟩ := hs _ hy₁
  have hu : (toUnit (Over.mk (x ≫ f))).left = x ≫ f := (Category.comp_id _).symm.trans (Over.w (toUnit _))
  have e : (x ≫ f) ≫ (c.lev a).left = y.left ≫ φ := by
    rw [← hu]
    exact congrArg (fun q => q.left) ha
  have e₁ : y.left = x ≫ (lv a).left := by
    apply hφ.1.hom_ext
    · rw [Category.assoc]
      exact e.symm.trans ((Category.assoc _ _ _).trans (congrArg (x ≫ ·) (h₁ a).symm))
    · rw [Over.w, Category.assoc, Over.w]
      exact (Category.comp_id _).symm
  rw [e₁, Category.assoc, Category.assoc]
  exact congrArg (x ≫ ·) ((h₁ a).trans (h₂ a).symm)

theorem eq_of_sRelBy : ∀ (h n n' d' : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (b : TBase B n) (ζ' : B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (c : SiegPre h n (b.ζ : B) s) (c' : SiegPre h n' ζ' s') (f : S' ⟶ S) (φ φ' : c'.A.left ⟶ c.A.left), 3 ≤ n → Odd n → c.Principal → SRelBy c' c d' 1 f φ → SRelBy c' c d' 1 f φ' → φ = φ' := by
  intro h n n' d' B B' _ _ b ζ' S S' s s' c c' f φ φ' hn _ hc ⟨g, ⟨φ₂, q, w⟩, l⟩ ⟨g', ⟨φ₂', q', w'⟩, l'⟩
  simp only [pow_one] at l l'
  obtain ⟨σ, hσ, e⟩ := exists_aut g g'
  have key : σ.hom = 𝟙 _ := by
    refine eq_id_of_forall_geometric_fibre laws_without_cohomology.1 c'.A c'.ab σ.hom (IsMonHom.one_hom σ.hom)
      fun t => ?_
    let K : Type := AlgebraicClosure (S'.residueField t)
    let j : Sp K ⟶ S' := Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField t) K)) ≫ S'.fromSpecResidueField t
    have hp := isGrpPullback_pullback c'.A j
    have := c'.ab.smooth
    have := c'.ab.proper
    have := c'.ab.geomConnected
    have hab : IsAbelianScheme ((Over.pullback j).obj c'.A) :=
      { comm := Functor.isCommMonObj_obj
        smooth := by change Smooth (pullback.snd c'.A.hom j); infer_instance
        proper := by change IsProper (pullback.snd c'.A.hom j); infer_instance
        geomConnected := by change GeometricallyConnected (pullback.snd c'.A.hom j); infer_instance }
    have hNK : (n : K) ≠ 0 := by
      have hu := b.unit.map (Spec.preimage ((j ≫ f) ≫ s)).hom
      rw [map_natCast] at hu
      exact hu.ne_zero
    have e' := eq_of_field (pull_isLB c.isLB _) hc.1 hab (hp.comp g) (hp.comp g')
      (by rw [pull_comp, pull_comp]; exact congrArg _ ((pull_cls_diag q w).trans (pull_cls_diag q' w').symm)) hn hNK
      fun Ω _ _ x y hy => by
        have hy₁ : pushHom hp (Over.mk x) y ^ n = 1 := by rw [← map_pow, hy, map_one]
        have e₁ := eq_on_torsion b.ζ.isUnit c g _ l l' Ω (x ≫ j) _ hy₁
        rw [← Category.assoc, ← Category.assoc]
        exact e₁
    refine ⟨_, _, j, _, _, (default : PrimeSpectrum K), ?_, hp.1, ?_⟩
    · exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply t _)
    · apply g'.1.hom_ext
      · rw [Category.assoc, e]
        exact e'
      · rw [Category.assoc, Over.w]
  rw [← e, key, Over.id_left, Category.id_comp]

end GlobalTheory.SiegRigid
