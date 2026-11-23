import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolBaseChange

theorem lbIso_refl {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L L := by
  refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_)))
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show gm (𝟙 X) y _ (L.g p.1 q.1) * (gm (𝟙 X) y _ (L.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (L.g q.1 q.2) =
    gm (𝟙 X) y _ (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
  {φ : A'.left ⟶ A.left} {L : LB A.left}

theorem eSec_comm (h : IsGrpPullback A' A f φ) : eSec A' ≫ φ = f ≫ eSec A := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  have e₁ : (1 : 𝟙_ (Over S') ⟶ A') = η[A'] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[A]).left = _
  simp [eSec]

theorem inv_comm (h : IsGrpPullback A' A f φ) :
    (GrpObj.inv : A' ⟶ A').left ≫ φ = φ ≫ (GrpObj.inv : A ⟶ A).left := by
  have e := congrArg (fun z => z.left) (map_inv (pushHom h A') (𝟙 A'))
  rw [Hom.inv_def, Hom.inv_def, Category.id_comp] at e
  refine e.trans ?_
  show (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]

theorem rigidified_pull (h : IsGrpPullback A' A f φ) (hr : Rigidified A L) : Rigidified A' (L.pull φ) := by
  obtain ⟨t, ht⟩ := hr
  exact gen_chartPull (chartPullLinComb L φ (fun _ : PUnit => eSec A') (fun _ => eSec A) (fun _ => 1) f
    fun _ => eSec_comm h) t ht

theorem sym_pull (h : IsGrpPullback A' A f φ) (hs : Sym A L) : Sym A' (L.pull φ) := by
  intro s
  obtain ⟨U, hU, t, ht⟩ := hs (f s)
  refine ⟨f ⁻¹ᵁ U, hU, ?_⟩
  have le' : A'.hom ⁻¹ᵁ (f ⁻¹ᵁ U) ≤ φ ⁻¹ᵁ (A.hom ⁻¹ᵁ U) := fun y hy =>
    (congrArg (fun q => q y ∈ U) h.1.w).mpr hy
  have hψ : φ.resLE _ _ le' ≫ (A.hom ⁻¹ᵁ U).ι = (A'.hom ⁻¹ᵁ (f ⁻¹ᵁ U)).ι ≫ φ := Scheme.Hom.resLE_comp_ι φ le'
  refine gen_chartPull (chartPullLinComb L φ _ _ _ (φ.resLE _ _ le') fun k => ?_) t ht
  fin_cases k
  · show (_ ≫ _) ≫ φ = _ ≫ _ ≫ _
    rw [Category.assoc, inv_comm h, ← Category.assoc, ← hψ, Category.assoc]
  · exact hψ.symm

omit [GrpObj A] [GrpObj A'] in

theorem relAmple_restrict (h : IsPullback φ A'.hom A.hom f) (hL : L.IsLB) (hA : RelAmple A L)
    (V : S.Opens) (hV : IsAffineOpen V) :
    RelAmple (Over.mk (A'.hom ∣_ (f ⁻¹ᵁ V))) ((L.pull φ).pull (A'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι) := by
  have H : IsPullback ((A'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι ≫ φ) (A'.hom ∣_ (f ⁻¹ᵁ V)) A.hom ((f ⁻¹ᵁ V).ι ≫ f) :=
    (isPullback_morphismRestrict A'.hom (f ⁻¹ᵁ V)).flip.paste_horiz h
  obtain ⟨w, hw⟩ : LBIso ((L.pull φ).pull (A'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι) (L.pull ((A'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι ≫ φ)) :=
    LBIso.chartPull (chartPullLinComb L φ (fun _ : PUnit => (A'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι)
      (fun _ => (A'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι ≫ φ) (fun _ => 1) (𝟙 _) fun _ => (Category.id_comp _).symm)
      (chartPullId _) (lbIso_refl (pull_isLB hL _))
  exact relAmple_pull (A' := Over.mk (A'.hom ∣_ (f ⁻¹ᵁ V))) H hL (pull_isLB (pull_isLB hL _) _)
    ((isGen_iff w).1 hw) V hV (fun y => y.2) hA

end GlobalTheory.PolBaseChange

namespace GlobalTheory

open PolBaseChange

theorem polBaseChange_of_relAmple_local :
    (∀ (S : Scheme.{0}) (A : Over S) (L : LB A.left), L.IsLB → QuasiCompact A.hom → QuasiSeparated A.hom →
      (∀ s : S, ∃ (U : S.Opens) (_ : s ∈ U), RelAmple (Over.mk (A.hom ∣_ U)) (L.pull (A.hom ⁻¹ᵁ U).ι)) →
      RelAmple A L) → PolBaseChangeSt := by
  intro hloc S S' f P
  have h := isGrpPullback_pullback P.A f
  have hab := TLinPf.isAb_pullback f P.A P.isAb
  have hL' := pull_isLB P.isLB (pullback.fst P.A.hom f)
  obtain ⟨w, hw⟩ := lbIso_refl hL'
  have := hab.proper
  have hamp : RelAmple ((Over.pullback f).obj P.A) (P.L.pull (pullback.fst P.A.hom f)) := by
    refine hloc S' _ _ hL' inferInstance inferInstance fun s => ?_
    obtain ⟨V, hV, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := f s) trivial
    exact ⟨f ⁻¹ᵁ V, hs, relAmple_restrict h.1 P.isLB P.ample V hV⟩
  refine ⟨{ A := (Over.pullback f).obj P.A
            isAb := hab
            g := P.g
            smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
            L := P.L.pull (pullback.fst P.A.hom f)
            isLB := hL'
            rigid := rigidified_pull h P.rigid
            sym := sym_pull h P.sym
            ample := hamp
            ktriv := kTriv_pull h P.isLB hL' ((isGen_iff w).1 hw) P.ktriv },
    pullback.fst P.A.hom f, h.1, rfl, fun T x y => ?_, w, hw⟩
  exact Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm

end GlobalTheory
