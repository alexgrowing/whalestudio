import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SvalUpSec
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.LN GlobalTheory.TorRef GlobalTheory.IntegralCombination
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ClosedIndep
open GlobalTheory.FieldBaseChange

variable {X Y Z : Scheme.{0}}

theorem gs_comp (ψ : Z ⟶ Y) (r : Y ⟶ X) (y : Z) (W : X.Opens) (a : Γ(X, W)) :
    gs (ψ ≫ r) y W a = (ψ.stalkMap y).hom (gs r (ψ y) W a) := by
  by_cases h : r (ψ y) ∈ W
  · rw [gs_eq r (ψ y) W h, gs_eq (ψ ≫ r) y W h]
    have := Scheme.Hom.germ_stalkMap_apply ψ (r ⁻¹ᵁ W) y h ((r.app W).hom a)
    rw [this]
    simp [Scheme.Hom.comp_app]
    rfl
  · have h' : ¬ (ψ ≫ r) y ∈ W := h
    simp [gs, h, h']

theorem sval_comp {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {Y' : Scheme.{0}}
    (s : LB.Sec (LB.LinComb L φ ε)) (ψ : Z ⟶ Y') (r : Y' ⟶ Y) (y : Z) (J : (Z ⟶ X) → L.ι) :
    sval s (ψ ≫ r) y J = (ψ.stalkMap y).hom (sval s r (ψ y) (fun χ => J (ψ ≫ χ))) := by
  rw [sval_of s (ψ ≫ r) y J (fun k => J (ψ ≫ r ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gs_comp ψ r y _ _

theorem Good.comp {L : LB X} {Y' : Scheme.{0}} (ψ : Z ⟶ Y') {y : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L y J) :
    Good L (ψ y) (fun χ => J (ψ ≫ χ)) := fun χ => hJ (ψ ≫ χ)

theorem exists_lift (R : Type) [CommRing R] [IsLocalRing R] (e : Γ(Sp (ResidueField R), ⊤)) :
    ∃ a : R, scal (spMap (residue R)) a = e ∧ (e ≠ 0 → a ∉ maximalIdeal R) := by
  obtain ⟨a, ha⟩ := residue_surjective ((Scheme.ΓSpecIso (CommRingCat.of (ResidueField R))).hom.hom e)
  have key : scal (spMap (residue R)) a = e := by
    have h1 := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (residue R)))
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of (ResidueField R))).inv.hom (residue R a) = e := by
      rw [ha]
      exact congrArg (fun q => q.hom e) (Scheme.ΓSpecIso (CommRingCat.of (ResidueField R))).hom_inv_id
    exact (h1.symm.trans h2)
  refine ⟨a, key, fun he ha' => he ?_⟩
  have h0 : residue R a = 0 := (residue_eq_zero_iff a).2 ha'
  have : (Scheme.ΓSpecIso (CommRingCat.of (ResidueField R))).hom.hom e = 0 := by rw [← ha, h0]
  have h3 := congrArg (fun q => q.hom e) (Scheme.ΓSpecIso (CommRingCat.of (ResidueField R))).hom_inv_id
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, this, map_zero] at h3
  exact h3.symm

theorem exists_thick_closed (R : Type) [CommRing R] [IsLocalRing R] :
    ∃ y : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1))), thick R (maximalIdeal R) 0 y = closedPoint R := by
  have h := _root_.range_comap_of_surjective (R ⧸ maximalIdeal R ^ (0 + 1)) (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1)))
    Ideal.Quotient.mk_surjective
  have hm : closedPoint R ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1)))) := by
    rw [h, Ideal.mk_ker]
    rw [PrimeSpectrum.mem_zeroLocus]
    intro x hx
    exact (by simpa using hx : x ∈ maximalIdeal R)
  obtain ⟨y, hy⟩ := hm
  exact ⟨y, hy⟩

def toRes (R : Type) [CommRing R] [IsLocalRing R] : ResidueField R →+* R ⧸ maximalIdeal R ^ (0 + 1) :=
  Ideal.Quotient.lift (maximalIdeal R) (Ideal.Quotient.mk _) (fun a ha => by
    rw [Ideal.Quotient.eq_zero_iff_mem]; simpa using ha)

theorem toRes_comp (R : Type) [CommRing R] [IsLocalRing R] :
    spMap (toRes R) ≫ spMap (residue R) = thick R (maximalIdeal R) 0 := by
  rw [spMap, spMap, ← Spec.map_comp]
  rfl

theorem sum_eq_zero_of_lin {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Sp R)) (L : LB G.left) (N n : ℕ)
    (σ : Fin n → H0 L N) (c c' : Fin n → Γ((Over.mk (spMap (residue R))).left, ⊤)) (s)
    (h : Lin G L N (toBase (residue R)) (fun i => upSec G (σ i)) c s)
    (h' : Lin G L N (toBase (residue R)) (fun i => upSec G (σ i)) c' s)
    {Z : Scheme.{0}} (ψ : Z ⟶ (Over.mk (spMap (residue R)) ⊗ G).left) (y : Z) (J : (Z ⟶ G.left) → L.ι) (hJ : Good L y J) :
    ∑ i, gs (ψ ≫ (fst (Over.mk (spMap (residue R))) G).left) y ⊤ (c i - c' i) *
      sval (σ i) (ψ ≫ (snd (Over.mk (spMap (residue R))) G).left) y J = 0 := by
  have hJ' := Good.comp ψ hJ
  have e1 := h (ψ y) _ hJ'
  have e2 := h' (ψ y) _ hJ'
  have key : ∀ i, sval (upSec G (σ i)) (toBase (residue R) ▷ G).left (ψ y) (fun χ => J (ψ ≫ χ)) =
      sval (σ i) (snd (Over.mk (spMap (residue R))) G).left (ψ y) (fun χ => J (ψ ≫ χ)) := fun i =>
    (sval_upSec G (σ i) _ (ψ y) hJ').trans (by rw [← Over.comp_left, whiskerRight_snd])
  have hsub : ∀ i, gs (fst (Over.mk (spMap (residue R))) G).left (ψ y) ⊤ (c i - c' i) =
      gs (fst (Over.mk (spMap (residue R))) G).left (ψ y) ⊤ (c i) -
        gs (fst (Over.mk (spMap (residue R))) G).left (ψ y) ⊤ (c' i) := fun i => by
    rw [eq_sub_iff_add_eq, ← gs_add _ _ _ (by trivial), sub_add_cancel]
  have e3 : ∑ i, gs (fst (Over.mk (spMap (residue R))) G).left (ψ y) ⊤ (c i - c' i) *
      sval (σ i) (snd (Over.mk (spMap (residue R))) G).left (ψ y) (fun χ => J (ψ ≫ χ)) = 0 := by
    simp only [hsub, sub_mul, Finset.sum_sub_distrib, ← key]
    exact sub_eq_zero.2 (e1.symm.trans e2)
  have e4 := congrArg (ψ.stalkMap y).hom e3
  rw [map_sum, map_zero] at e4
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) e4
  rw [map_mul, ← gs_comp, ← sval_comp]

end GlobalTheory.ClosedIndep

open GlobalTheory.ClosedIndep GlobalTheory.FieldBaseChange in
theorem GlobalTheory.ClosedIndep.main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G]
      [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (N : ℕ), 1 ≤ N →
    ∀ (n : ℕ) (σ : Fin n → H0 U.LG.L N) (f : Fin n → ∀ α, SecAb D.toPre N α),
      (∀ i, U.ExpandsAt 0 N (σ i) (f i)) →
      (∀ c : Fin n → R, (∃ i, c i ∉ maximalIdeal R) →
        ∃ (α : D.toPre.X) (j : Fin 4 → D.toPre.P.L.ι) (b : D.toPre.P.A.left),
          D.toPre.P.A.hom b = closedPoint R ∧
          b ∈ D.toPre.P.A.left.basicOpen ((∑ i, c i • f i α).f j)) →
      IndepAlong G U.LG.L N (toBase (residue R)) (fun i => upSec G (σ i)) := by
  intro R _ _ _ hR D A G _ _ hG U N hN n σ f hE hc c c' s h h'
  by_contra hne
  choose a ha ha' using fun i => exists_lift R (c i - c' i)
  obtain ⟨i₀, hi₀⟩ : ∃ i, c i - c' i ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact hne (funext fun i => sub_eq_zero.1 (hh i))
  obtain ⟨α, j, b, hb, hbo⟩ := hc a ⟨i₀, ha' i₀ hi₀⟩
  let a₁ : (Over.map (thick R (maximalIdeal R) 0)).obj (thickObj R (maximalIdeal R) 0 G) ⟶ Over.mk (spMap (residue R)) :=
    Over.homMk (pullback.snd G.hom (thick R (maximalIdeal R) 0) ≫ spMap (toRes R)) (by
      simp [toRes_comp])
  let ψ := lift a₁ (fstG (maximalIdeal R) 0 G)
  have hs : ψ.left ≫ (snd (Over.mk (spMap (residue R))) G).left = (fstG (maximalIdeal R) 0 G).left := by
    rw [← Over.comp_left, lift_snd]
  have hf : ψ.left ≫ (fst (Over.mk (spMap (residue R))) G).left =
      pullback.snd G.hom (thick R (maximalIdeal R) 0) ≫ spMap (toRes R) := by
    rw [← Over.comp_left, lift_fst]
    rfl
  have hp : (fstG (maximalIdeal R) 0 G).left ≫ G.hom =
      (pullback.snd G.hom (thick R (maximalIdeal R) 0) ≫ spMap (toRes R)) ≫ spMap (residue R) := by
    rw [Category.assoc, toRes_comp]
    exact pullback.condition
  let τ : SecG U.toUnifPre N := ∑ p, a p • (show SecG U.toUnifPre N from σ p)
  have hval : ∀ (y : (thickObj R (maximalIdeal R) 0 G).left) J, Good U.LG.L y J →
      sval (show H0 U.LG.L N from τ) (fstG (maximalIdeal R) 0 G).left y J = 0 := by
    intro y J hJ
    have e := sum_eq_zero_of_lin G U.LG.L N n σ c c' s h h' ψ.left y J hJ
    refine Eq.trans ?_ e
    refine (sval_sum' hJ _ _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
    refine (sval_smul' hJ _ _ _).trans ?_
    rw [hs, hf, ← ha i, GlobalTheory.FieldBaseChange.gs_scal, hp]
  have hzero : ∀ j, ((fstG (maximalIdeal R) 0 G).left.app _).hom ((show H0 U.LG.L N from τ).f j) = 0 := by
    intro j
    refine fn_ext fun y hy => ?_
    have hmem : ∀ k, ((fun _ : Fin 1 => (fstG (maximalIdeal R) 0 G).left ≫ 𝟙 G.left) k) y ∈ U.LG.L.U (j k) := fun k =>
      Set.mem_iInter.1 hy k
    obtain ⟨J, hJ, e⟩ := exists_good U.LG.L U.LG.isLB y (fun _ : Fin 1 => (fstG (maximalIdeal R) 0 G).left ≫ 𝟙 G.left) j
      (fun a b _ => by rw [Subsingleton.elim a b]) hmem
    have e2 := hval y J hJ
    rw [sval_of _ _ y J j (fun k => e k)] at e2
    refine (gs_pull (𝟙 _) _ y _ hy _).trans ?_
    rw [Category.id_comp]
    exact e2.trans (GlobalTheory.FieldBaseChange.gs_zero' _ y _ hy).symm
  have WI := GlobalTheory.allSixLaws.2.2.2.1.weightIndep R (maximalIdeal R) D A G U.toUnifPre 0 N τ
    (fun α => (∑ p, a p • f p α : SecAb D.toPre N α)) hzero (expandsAt_comb U.toUnifPre 0 N σ f hE a) α j
  obtain ⟨y₀, hy₀⟩ := exists_thick_closed R
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := D.toPre.P.A.hom)
    (g := thick R (maximalIdeal R) 0) b y₀ (hb.trans hy₀.symm)
  obtain ⟨g, hg⟩ := (U.gt 0).q_surj.surj w
  have hgb : (U.gt 0).pG.left g = b := by
    rw [← hw, ← hg]
    rfl
  have hmem : g ∈ (U.gt 0).pG.left ⁻¹ᵁ D.toPre.P.A.left.basicOpen ((∑ i, a i • f i α).f j) := by
    show (U.gt 0).pG.left g ∈ D.toPre.P.A.left.basicOpen ((∑ i, a i • f i α).f j)
    rw [hgb]
    exact hbo
  rw [Scheme.preimage_basicOpen, WI, Scheme.basicOpen_zero] at hmem
  exact hmem
