import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinOfIsPull
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DegenerationDataCoordsNeZeroLatticesIsomorphic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LN GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorRef.ZeroPow

section Sections

variable {S : Scheme.{0}} {G : Over S} {L : LB G.left}

theorem linComb_g_zero {X Y : Scheme.{0}} (M : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (j j' : K → M.ι) :
    (LB.LinComb M φ (fun _ => ((0 : ℕ) : ℤ))).g j j' = 1 := by
  have aux : ∀ x : K → Γ(Y, LB.wchart M φ j ⊓ LB.wchart M φ j')ˣ, ∏ k, x k ^ ((0 : ℕ) : ℤ) = 1 := fun x => by simp
  exact aux _

def oneSec (T : Over S) : LB.Sec (LPow G L ((0 : ℕ) : ℤ) T) where
  f := fun _ => 1
  compat := fun j j' => by
    rw [map_one, map_one, mul_one]
    exact (congrArg Units.val (linComb_g_zero L _ j j')).symm

theorem sval_oneSec (T : Over S) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ G).left) (z : Z) {J : (Z ⟶ G.left) → L.ι}
    (hJ : Good L z J) :
    sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => ((0 : ℕ) : ℤ)) (oneSec T) r z J = 1 := by
  have hm : r z ∈ LB.wchart L (fun _ : Fin 1 => (snd T G).left) (fun _ => J (r ≫ (snd T G).left)) := hJ.mem _ r
  exact (gs_eq r z _ hm 1).trans (by rw [map_one, map_one])

theorem exists_fn (hL : L.IsLB) {T : Over S} (s : LB.Sec (LPow G L ((0 : ℕ) : ℤ) T)) :
    ∃ a : Γ((T ⊗ G).left, ⊤), ∀ (z : (T ⊗ G).left) (J), Good L z J →
      sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => ((0 : ℕ) : ℤ)) s (𝟙 _) z J =
        gs (𝟙 _) z ⊤ a := by
  obtain ⟨s', hs'⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_sec hL
    (φ' := (Fin.elim0 : Fin 0 → ((T ⊗ G).left ⟶ G.left))) (ε' := (Fin.elim0 : Fin 0 → ℤ))
    (fun U _ h => by simp) s
  have hle : (⊤ : (T ⊗ G).left.Opens) ≤ LB.wchart L (Fin.elim0 : Fin 0 → ((T ⊗ G).left ⟶ G.left)) Fin.elim0 :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim0
  refine ⟨((T ⊗ G).left.presheaf.map (homOfLE hle).op).hom (s'.f Fin.elim0), fun z J hJ => ?_⟩
  exact (hs' _ (𝟙 _) z J hJ).symm.trans ((sval_of s' (𝟙 _) z J _ (fun k => k.elim0)).trans
    (gs_res (𝟙 _) z hle trivial _).symm)

end Sections

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem bijective_fst {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)} (U : PELUnif I t)
    {F : Type} [Field F] (g : FractionRing R →+* F) :
    Function.Bijective (fst (Over.mk (spMap (g.comp (algebraMap R (FractionRing R))))) t.G).left.appTop.hom := by
  have hp : IsProper (pullback.snd t.G.hom (Out.jK R)) := (GlobalTheory.DatUniq.polAt_of_unif U).1
  have := t.semi.smooth
  have := t.semi.geomConnected
  have : GeometricallyIntegral t.G.hom := GlobalTheory.geometricallyIntegral_of_smooth _
  have hχ : spMap (g.comp (algebraMap R (FractionRing R))) = spMap g ≫ Out.jK R := by
    show Spec.map (CommRingCat.ofHom (g.comp (algebraMap R (FractionRing R)))) =
      Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    rw [← Spec.map_comp]; rfl
  generalize hc : spMap (g.comp (algebraMap R (FractionRing R))) = χ at hχ
  have H : IsPullback (snd (Over.mk χ) t.G).left (fst (Over.mk χ) t.G).left t.G.hom χ :=
    (IsPullback.of_hasPullback χ t.G.hom).flip
  have : Smooth (fst (Over.mk χ) t.G).left := MorphismProperty.of_isPullback H ‹_›
  have : GeometricallyIntegral (fst (Over.mk χ) t.G).left := MorphismProperty.of_isPullback H ‹_›
  have H2 : IsPullback (pullback.lift (snd (Over.mk χ) t.G).left ((fst (Over.mk χ) t.G).left ≫ spMap g)
      (by rw [H.w, hχ, Category.assoc]))
      (fst (Over.mk χ) t.G).left (pullback.snd t.G.hom (Out.jK R)) (spMap g) :=
    IsPullback.of_right (by rw [pullback.lift_fst, ← hχ]; exact H) (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback t.G.hom (Out.jK R))
  have : IsProper (fst (Over.mk χ) t.G).left := MorphismProperty.of_isPullback H2 hp
  have : IsAffine (Over.mk χ).left := inferInstanceAs (IsAffine (Sp F))
  have : IsLocallyNoetherian (Over.mk χ).left := inferInstanceAs (IsLocallyNoetherian (Sp F))
  have := ProperFunctions.isIso_appTop_of_isAffine (fst (Over.mk χ) t.G).left
  exact ConcreteCategory.bijective_of_isIso _

theorem span_of_basisAlong_zero :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] (t : SAB H (Sp R)) (_ : PELUnif (maximalIdeal R) t) (N n : ℕ)
    (b : Fin n → LB.Sec (LPow t.G t.PP.L (N : ℤ) (Over.mk (𝟙 (Sp R))))), N = 0 →
    BasisAlong t.G t.PP.L N (toBase (algebraMap R (FractionRing R))) b →
    ∀ (F : Type) [Field F] (ψ : R →+* F), Function.Injective ψ →
    ∀ s : LB.Sec (LPow t.G t.PP.L (N : ℤ) (Over.mk (spMap ψ))), ∃ c, Lin t.G t.PP.L N (toBase ψ) b c s := by
  intro E _ _ _ H R _ _ _ t U N n b hN hB F _ ψ hψ s
  subst hN
  obtain ⟨g, rfl⟩ : ∃ g : FractionRing R →+* F, ψ = g.comp (algebraMap R (FractionRing R)) :=
    ⟨IsFractionRing.lift hψ, RingHom.ext fun r => (IsFractionRing.lift_algebraMap hψ r).symm⟩
  obtain ⟨cK, hcK, -⟩ := hB (oneSec _)
  have h1 : Lin t.G t.PP.L 0 (jC (algebraMap R (FractionRing R)) g) (fun _ : Fin 1 => oneSec _) (fun _ => 1)
      (oneSec _) := by
    intro z J hJ
    rw [Fin.sum_univ_one, sval_oneSec _ _ z hJ, sval_oneSec _ _ z hJ, GlobalTheory.FramePull.gs_one, _root_.one_mul]
  have H1 := lin_comp _ _ hcK h1
  rw [jC_toBase] at H1
  obtain ⟨a, ha⟩ := exists_fn t.PP.isLB s
  obtain ⟨f, rfl⟩ := (bijective_fst U g).2 a
  refine ⟨fun i => f * (jC (algebraMap R (FractionRing R)) g).left.appTop.hom (cK i), fun z J hJ => ?_⟩
  have e1 := H1 z J hJ
  rw [sval_oneSec _ _ z hJ] at e1
  have gv : gs (𝟙 _) z ⊤ ((fst (Over.mk (spMap (g.comp (algebraMap R (FractionRing R))))) t.G).left.appTop.hom f) =
      gs (fst (Over.mk (spMap (g.comp (algebraMap R (FractionRing R))))) t.G).left z ⊤ f :=
    (gs_pull (𝟙 _) _ z ⊤ trivial f).trans (by rw [Category.id_comp])
  rw [ha z J hJ, gv]
  calc _ = gs (fst (Over.mk (spMap (g.comp (algebraMap R (FractionRing R))))) t.G).left z ⊤ f * 1 := (mul_one _).symm
    _ = _ := by
      rw [e1, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [gs_mul _ z ⊤ trivial, mul_assoc]

end GlobalTheory.TorRef.ZeroPow
