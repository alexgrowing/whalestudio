import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.TorusExtensionPoints

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GtRestrictCompare

section General

variable {X Y Y' Z Z' : Scheme.{0}} {L : LB X}

theorem corr_pull_of_fac (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ' : K' → (Y' ⟶ X)} {ε' : K' → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    {a : Z ⟶ Y} {a' : Z ⟶ Y'} (H : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t a) (LB.pullGen L _ _ t' a'))
    (l : Z' ⟶ Z) {r : Z' ⟶ Y} {r' : Z' ⟶ Y'} (h : l ≫ a = r) (h' : l ≫ a' = r') :
    LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t r) (LB.pullGen L _ _ t' r') := by
  subst h h'
  exact corr_trans hL (corr_symm (corr_pullGen_comp t a l))
    (corr_trans hL (corr_pullGen H l) (corr_pullGen_comp t' a' l))

theorem corr_of_isEmpty [IsEmpty Y] {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) :
    LB.Gen.Corr L _ _ _ _ t t' := by
  intro j j' _ _ _
  have h : ∀ U : Y.Opens, Subsingleton Γ(Y, U) := fun U => by
    obtain rfl : U = ⊥ := by ext x; exact isEmptyElim x
    infer_instance
  exact Units.ext (Subsingleton.elim _ _)

theorem gen_eq_of_pull {φ : PUnit → (Y ⟶ X)} {ε : PUnit → ℤ} (t t' : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y)
    (hinj : ∀ U : Y.Opens, Function.Injective (h.app U))
    (H : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t h) (LB.pullGen L _ _ t' h)) : t = t' := by
  obtain ⟨s⟩ := t
  obtain ⟨s'⟩ := t'
  congr 1
  funext j
  have e := H j j (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  have hle : h ⁻¹ᵁ (LB.wchart L φ j) ≤
      LB.wchart L (fun k => h ≫ φ k) j ⊓ LB.wchart L (fun k => h ≫ φ k) j := fun _ hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k, Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k⟩
  have key : ∀ {U : Y.Opens} {A B : Z.Opens} (h₁ : h ⁻¹ᵁ U ≤ A) (h₂ : A ≤ B)
      (h₃ : B ≤ h ⁻¹ᵁ U) (s : Γ(Y, U)ˣ),
      ((res h₁ (res h₂ (res h₃ (pullU h U s))) : Γ(Z, h ⁻¹ᵁ U)ˣ) : Γ(Z, h ⁻¹ᵁ U)) = (h.app U).hom s := by
    intro U A B h₁ h₂ h₃ s
    change (h.app U ≫ Z.presheaf.map (homOfLE h₃).op ≫ Z.presheaf.map (homOfLE h₂).op ≫
      Z.presheaf.map (homOfLE h₁).op).hom s.1 = (h.app U).hom s.1
    rw [← Functor.map_comp, ← Functor.map_comp]
    erw [Z.presheaf.map_id]
    rw [Category.comp_id]
  refine Units.ext (hinj _ ?_)
  exact (key hle _ _ _).symm.trans ((congrArg (fun u => (res hle u).1) e).trans (key hle _ _ _))

end General

variable {R : Type} [CommRing R] [IsDomain R]

section Points

variable (D : DegPre R) (T : Over (Spec (CommRingCat.of R)))

def gtEquiv : GtPt D T ≃ IndefiniteRowSideFullHecke.TorusExtensionPoints.GtPt D T where
  toFun g := ⟨g.b, g.s, g.isGen, g.s_zero, g.mult⟩
  invFun g := ⟨g.b, g.s, g.isGen, g.s_zero, g.mult⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {D T}

theorem isNsmul_iff (k : ℕ) (g h : GtPt D T) :
    GtPt.IsNsmul k g h ↔ IndefiniteRowSideFullHecke.TorusExtensionPoints.GtPt.IsNsmul k (gtEquiv D T g) (gtEquiv D T h) :=
  ⟨fun ⟨gs, a, b, c⟩ => ⟨fun i => gtEquiv D T (gs i), a, b, congrArg (gtEquiv D T) c⟩,
    fun ⟨gs, a, b, c⟩ => ⟨fun i => (gtEquiv D T).symm (gs i), a, b, congrArg (gtEquiv D T).symm c⟩⟩

variable {F : Type} [Field F] [Algebra (FractionRing R) F]

end Points

section OnOpen

variable {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens}

theorem psi_eq_iff (χ : D.X)
    (t : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (toUnit (TW W) ≫ D.c χ).left) (fun _ => -1))) :
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ t (jK R ∣_ W))
      (LB.pullGen D.P.L _ _ (D.psi χ) (jK R ⁻¹ᵁ W).ι) ↔
    ∀ j : TK R ⟶ IndefiniteRowSideFullHecke.TorusExtensionPoints.TU W, LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ t j.left) (D.psi χ) := by
  constructor
  · intro H j
    have h : j.left ≫ W.ι = 𝟙 _ ≫ jK R := (Over.w j).trans (Category.id_comp _).symm
    exact corr_trans D.P.isLB (corr_pull_of_fac D.P.isLB H ((isPullback_morphismRestrict (jK R) W).lift _ _ h)
      ((isPullback_morphismRestrict (jK R) W).lift_fst _ _ _)
      ((isPullback_morphismRestrict (jK R) W).lift_snd _ _ _)) (corr_pullGen_id _)
  · intro H
    rcases isEmpty_or_nonempty (jK R ⁻¹ᵁ W).toScheme with h | ⟨⟨y, hy⟩⟩
    · exact corr_of_isEmpty _ _
    · have hr : Set.range (jK R) ⊆ Set.range W.ι := by
        rintro _ ⟨z, rfl⟩
        rw [Scheme.Opens.range_ι, Subsingleton.elim z y]
        exact hy
      have hj : IsOpenImmersion.lift W.ι (jK R) hr ≫ W.ι = jK R := IsOpenImmersion.lift_fac _ _ _
      have H' := corr_trans D.P.isLB (H (Over.homMk (IsOpenImmersion.lift W.ι (jK R) hr) hj))
        (corr_symm (corr_pullGen_id _))
      refine corr_pull_of_fac D.P.isLB H' (jK R ⁻¹ᵁ W).ι ?_ (Category.comp_id _)
      change (jK R ⁻¹ᵁ W).ι ≫ IsOpenImmersion.lift W.ι (jK R) hr = _
      rw [← cancel_mono W.ι, Category.assoc, hj, morphismRestrict_ι]

variable (D W) in

def psiEquiv : PsiOn D W ≃ {ψ' : IndefiniteRowSideFullHecke.TorusExtensionPoints.PsiFam D W // IndefiniteRowSideFullHecke.TorusExtensionPoints.IsPsiExt D W ψ'} where
  toFun ψ := ⟨ψ.psi, fun χ => ⟨ψ.psi_gen χ, (psi_eq_iff χ _).1 (ψ.psi_eq χ)⟩⟩
  invFun ψ := ⟨ψ.1, fun χ => (ψ.2 χ).1, fun χ => (psi_eq_iff χ _).2 (ψ.2 χ).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem psiOn_unique (ψ ψ' : PsiOn D W) : ψ = ψ' := by
  have hd : IsDominant (jK R) := by
    refine ⟨?_⟩
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap R (FractionRing R))).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]
      exact bot_le)
  have : IsSchemeTheoreticallyDominant (jK R) := .of_isDominant _
  have : IsSchemeTheoreticallyDominant (jK R ∣_ W) :=
    IsSchemeTheoreticallyDominant.of_isPullback (isPullback_morphismRestrict (jK R) W).flip
  have e : ψ.psi = ψ'.psi := funext fun χ => gen_eq_of_pull _ _ (jK R ∣_ W) (Scheme.Hom.app_injective _)
    (corr_trans D.P.isLB (ψ.psi_eq χ) (corr_symm (ψ'.psi_eq χ)))
  obtain ⟨a, _, _⟩ := ψ
  obtain ⟨b, _, _⟩ := ψ'
  obtain rfl : a = b := e
  rfl

theorem isIota_iff (ψ : PsiOn D W) {T : Over W.toScheme} (y : D.X) (g : GtPt D (overW W T)) :
    GtPt.IsIotaW ψ y g ↔ IndefiniteRowSideFullHecke.TorusExtensionPoints.GtPt.IsIota W y (gtEquiv D _ g) := by
  refine and_congr_right' ⟨fun h => ⟨Over.homMk T.hom rfl, ψ.psi, (psiEquiv D W ψ).2, h⟩, ?_⟩
  rintro ⟨u, ψ', h', h⟩
  obtain rfl : ψ = (psiEquiv D W).symm ⟨ψ', h'⟩ := psiOn_unique _ _
  have e : u.left = T.hom := (cancel_mono W.ι).1 (Over.w u)
  intro χ
  have := h χ
  rw [e] at this
  exact this

def qkEquiv (ψ : PsiOn D W) (k : ℕ) (T : Over W.toScheme) :
    QkPtW D W ψ k T ≃ IndefiniteRowSideFullHecke.TorusExtensionPoints.QkPtT D W (overW W T) k where
  toFun p := ⟨p.y, gtEquiv D _ p.g, by
    obtain ⟨h, a, b⟩ := p.eq
    exact ⟨gtEquiv D _ h, (isNsmul_iff k _ _).1 a, (isIota_iff ψ _ _).1 b⟩⟩
  invFun p := ⟨p.y, (gtEquiv D _).symm p.g, by
    obtain ⟨h, a, b⟩ := p.eq
    exact ⟨(gtEquiv D _).symm h, (isNsmul_iff k _ _).2 a, (isIota_iff ψ _ _).2 b⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {ψ : PsiOn D W} {k : ℕ} {T : Over W.toScheme}

variable {F : Type} [Field F] [Algebra (FractionRing R) F]

end OnOpen

end GlobalTheory.GtRestrictCompare
