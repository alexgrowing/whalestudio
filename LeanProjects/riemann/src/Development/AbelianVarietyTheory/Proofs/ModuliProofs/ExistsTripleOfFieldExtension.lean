import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleTrivialIsoDescendFieldStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TripleDescent

variable {S S' : Scheme.{0}} {f : S' ⟶ S}

theorem lift_left_fst {T X Y : Over S} (a : T ⟶ X) (b : T ⟶ Y) : (lift a b).left ≫ (fst X Y).left = a.left :=
  congrArg (fun q => q.left) (lift_fst a b)

theorem lift_left_snd {T X Y : Over S} (a : T ⟶ X) (b : T ⟶ Y) : (lift a b).left ≫ (snd X Y).left = b.left :=
  congrArg (fun q => q.left) (lift_snd a b)

theorem isPullback_tensor {X Y : Over S} {X' Y' : Over S'} {a : X'.left ⟶ X.left} {b : Y'.left ⟶ Y.left}
    (ha : IsPullback a X'.hom X.hom f) (hb : IsPullback b Y'.hom Y.hom f) (c : (X' ⊗ Y').left ⟶ (X ⊗ Y).left)
    (c₁ : c ≫ (fst X Y).left = (fst X' Y').left ≫ a) (c₂ : c ≫ (snd X Y).left = (snd X' Y').left ≫ b) :
    IsPullback c (X' ⊗ Y').hom (X ⊗ Y).hom f := by
  have p : IsPullback (snd X Y).left (fst X Y).left Y.hom X.hom := (IsPullback.of_hasPullback X.hom Y.hom).flip
  have p' : IsPullback (snd X' Y').left (fst X' Y').left Y'.hom X'.hom :=
    (IsPullback.of_hasPullback X'.hom Y'.hom).flip
  have q := p'.paste_horiz hb
  rw [← c₂, ← ha.w] at q
  have r := (IsPullback.of_right q c₁ p).paste_vert ha
  rwa [Over.w, Over.w] at r

variable {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left}

theorem lbIso_cubeLB_pull (h : IsGrpPullback G' G f φ) (hw : LBIso L' (L.pull φ)) {T' : Over S'} {T : Over S} {n : ℕ}
    (x' : Fin n → (T' ⟶ G')) (x : Fin n → (T ⟶ G)) (U : Over.mk (T'.hom ≫ f) ⟶ T)
    (hx : ∀ i, pushPt h.1.w (x' i) = U ≫ x i) :
    LBIso (cubeLB G' x' L') ((cubeLB G x L).pull U.left) := by
  obtain ⟨w, hw⟩ := hw
  exact (iso_linComb ((isGen_iff w).1 hw) _ _).chartPull (chartPullId _)
    (chartPullOut L _ _ U.left _ fun I => psum_push h x' x U hx I.down)

theorem exists_gen_cubeLB_pull (h : IsGrpPullback G' G f φ) (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ))
    {T' : Over S'} {T : Over S} {n : ℕ} (x' : Fin n → (T' ⟶ G')) (x : Fin n → (T ⟶ G))
    (U : Over.mk (T'.hom ≫ f) ⟶ T) (hx : ∀ i, pushPt h.1.w (x' i) = U ≫ x i) (t : (cubeLB G' x' L').Gen)
    (ht : t.IsGen) : ∃ t : ((cubeLB G x L).pull U.left).Gen, t.IsGen := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨c, hc, -⟩ := exists_up ((isGen_iff w).1 hw) hL hL' t ht
  exact gen_chartPull (chartPullOut L _ _ U.left _ fun I => psum_push h x' x U hx I.down) c hc

end GlobalTheory.TripleDescent

open GlobalTheory.TripleDescent in

theorem GlobalTheory.exists_triple_of_fieldExtension : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (τ : SAB H (Sp K)) (A₀ : Over (Sp K₀)) [GrpObj A₀] (φ : τ.G.left ⟶ A₀.left) (L₀ : LB A₀.left) (r : OAct (𝓞 E) A₀), IsAbelianScheme A₀ → IsGrpPullback τ.G A₀ (spMap i) φ → L₀.IsLB → LBIso τ.PP.L (L₀.pull φ) → (∀ c, (τ.act.act c).left ≫ φ = φ ≫ (r.act c).left) → ∃ (τ₀ : SAB H (Sp K₀)) (e : τ₀.G ≅ A₀), IsMonHom e.hom ∧ LBIso τ₀.PP.L (L₀.pull e.hom.left) ∧ ∀ c, τ₀.act.act c ≫ e.hom = e.hom ≫ r.act c := by
  intro hLaws E _ _ _ H K₀ K _ _ i τ A₀ _ φ L₀ r hA h hL₀ hw hact
  have := hA.comm
  have A₂ := AbelianSchemeGerms.isAbelianScheme_tensor A₀ A₀ hA hA
  have A₃ := AbelianSchemeGerms.isAbelianScheme_tensor A₀ _ hA A₂
  have lb : ∀ {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ B))
      {L : LB B.left}, L.IsLB → (cubeLB B x L).IsLB := fun x L hL => DVR.linComb_isLB _ hL _ _
  have pa : ∀ {T : Over (Sp K)} (x : T ⟶ τ.G) a,
      pushPt h.1.w (x ≫ τ.act.act a) = pushPt h.1.w x ≫ r.act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc])
  have hP := τ.PP.isLB
  let U₁ := pushPt h.1.w (𝟙 τ.G)
  have e₁ : U₁.left = φ := Category.id_comp _
  let U₂ := lift (pushPt h.1.w (fst τ.G τ.G)) (pushPt h.1.w (snd τ.G τ.G))
  let U₃ := lift (pushPt h.1.w (x3 τ.G 0)) (lift (pushPt h.1.w (x3 τ.G 1)) (pushPt h.1.w (x3 τ.G 2)))
  have u₁ : U₂.left ≫ (fst A₀ A₀).left = (fst τ.G τ.G).left ≫ φ := lift_left_fst _ _
  have u₂ : U₂.left ≫ (snd A₀ A₀).left = (snd τ.G τ.G).left ≫ φ := lift_left_snd _ _
  have P₂ : IsPullback U₂.left (τ.G ⊗ τ.G).hom (A₀ ⊗ A₀).hom (spMap i) := isPullback_tensor h.1 h.1 _ u₁ u₂
  have P₃ : IsPullback U₃.left (τ.G ⊗ τ.G ⊗ τ.G).hom (A₀ ⊗ A₀ ⊗ A₀).hom (spMap i) := by
    refine isPullback_tensor h.1 P₂ _ (lift_left_fst _ _) ?_
    refine (lift_left_snd _ _).trans ?_
    apply pullback.hom_ext
    · refine (lift_left_fst _ _).trans (Eq.symm ?_)
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) u₁).trans (Category.assoc _ _ _).symm)
    · refine (lift_left_snd _ _).trans (Eq.symm ?_)
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) u₂).trans (Category.assoc _ _ _).symm)
  have D₁ := GlobalTheory.T.lineBundle_trivial_iso_descend_field K₀ K i _ _ A₀.hom _ _ hA.smooth hA.proper hA.geomConnected h.1
  have D₂ := GlobalTheory.T.lineBundle_trivial_iso_descend_field K₀ K i _ _ (A₀ ⊗ A₀).hom _ _ A₂.smooth A₂.proper A₂.geomConnected P₂
  have D₃ := GlobalTheory.T.lineBundle_trivial_iso_descend_field K₀ K i _ _ (A₀ ⊗ A₀ ⊗ A₀).hom _ _ A₃.smooth A₃.proper A₃.geomConnected P₃
  have hT : ∃ t : LB.Gen (Theta A₀ L₀), t.IsGen := D₃.1 _ (lb _ hL₀)
    (exists_gen_cubeLB_pull h hL₀ hP hw (x3 τ.G) (x3 A₀) U₃ (fun j => by fin_cases j <;> simp [x3, U₃])
      τ.cub.t τ.cub.isGen)
  have ha : ∀ a, LBIso (cubeLB A₀ ![fst A₀ A₀ ≫ r.act a, snd A₀ A₀] L₀)
      (cubeLB A₀ ![fst A₀ A₀, snd A₀ A₀ ≫ r.act (H.bar a)] L₀) := fun a => by
    have k₁ := lbIso_cubeLB_pull h hw ![fst τ.G τ.G ≫ τ.act.act a, snd τ.G τ.G]
      ![fst A₀ A₀ ≫ r.act a, snd A₀ A₀] U₂ (fun j => by
        fin_cases j
        · exact (pa _ a).trans (by simp [U₂])
        · simp [U₂])
    have k₂ := lbIso_cubeLB_pull h hw ![fst τ.G τ.G, snd τ.G τ.G ≫ τ.act.act (H.bar a)]
      ![fst A₀ A₀, snd A₀ A₀ ≫ r.act (H.bar a)] U₂ (fun j => by
        fin_cases j
        · simp [U₂]
        · exact (pa _ _).trans (by simp [U₂]))
    exact D₂.2 _ _ (lb _ hL₀) (lb _ hL₀) (LBIso.trans (pull_isLB (lb _ hL₀) _) (by exact lb _ hP) (pull_isLB (lb _ hL₀) _)
      k₁.symm (LBIso.trans (by exact lb _ hP) (by exact lb _ hP) (pull_isLB (lb _ hL₀) _) (τ.adj a) k₂))
  have hp : LBIso L₀ (cubeLB A₀ ![𝟙 A₀, r.act H.w0] L₀) := by
    have k := lbIso_cubeLB_pull h hw ![𝟙 τ.G, τ.act.act H.w0] ![𝟙 A₀, r.act H.w0] U₁ (fun j => by
      fin_cases j
      · simp [U₁]
      · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _))
    rw [e₁] at k
    exact D₁.2 _ _ hL₀ (lb _ hL₀) (LBIso.trans (pull_isLB hL₀ _) hP (pull_isLB (lb _ hL₀) _)
      hw.symm (LBIso.trans hP (by exact lb _ hP) (pull_isLB (lb _ hL₀) _) τ.prim k))
  obtain ⟨PP, cub, sym, iso, -, prim, adj⟩ :=
    GlobalTheory.PrimNorm.exists_primitive_normalisation hLaws.globalFns E H _ A₀ r L₀ hA hL₀ hT ha
  refine ⟨⟨A₀, GlobalTheory.isSemiAbelian_of_isAbelianScheme A₀ hA, r, PP, cub, sym, adj, prim⟩, Iso.refl _,
    inferInstanceAs (IsMonHom (𝟙 A₀)), ?_, fun c => (Category.comp_id _).trans (Category.id_comp _).symm⟩
  exact (LBIso.trans PP.isLB (lb _ hL₀) hL₀ iso hp.symm).chartPull (chartPullId _) (chartPullPull L₀ _ (𝟙 _) rfl)
