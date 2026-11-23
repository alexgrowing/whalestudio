import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HasBasisOfBasis
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueCombOfIndependentSpecialFibre

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.GenericSectionBasis

namespace GlobalTheory.TraitBasis

theorem toStk_valF_eq_gs {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F)
    (h : x z ∈ U) (a : Γ(X, U)) : toStk z (valF x U a) = gs x z U a := by
  rw [valF, dif_pos ((top_le_iff_mem x U z).2 h), gs_eq x z U h]
  show ((Sp F).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom _)) = _
  rw [Iso.hom_inv_id_apply]
  exact TopCat.Presheaf.germ_res_apply (Sp F).presheaf (homOfLE ((top_le_iff_mem x U z).2 h)) z trivial _

theorem toStk_eq_cst {F : Type} [Field F] (z : Sp F) (a : F) : toStk z a = cst (𝟙 (Sp F)) z a := by
  rw [cst, gs_eq _ z ⊤ trivial]; rfl

theorem gs_eq_zero_of_notMem {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F)
    (h : x z ∈ U) (a : Γ(X, U)) (ha : x z ∉ X.basicOpen a) : gs x z U a = 0 := by
  by_cases h0 : valF x U a = 0
  · rw [← toStk_valF_eq_gs x U z h, h0, map_zero]
  · refine (ha ?_).elim
    have u : IsUnit (gs x z U a) := by
      rw [← toStk_valF_eq_gs x U z h]; exact (IsUnit.mk0 _ h0).map _
    rw [gs_stalkMap x z U h, isUnit_map_iff, gs_eq (𝟙 X) (x z) U h] at u
    exact (X.mem_basicOpen a (x z) h).2 u

theorem map_eq_zero_of_points {X B Y : Scheme.{0}} {M : LB X} (π : X ⟶ B) {n : ℕ} (b : Fin n → LB.Sec M)
    {K : Type} [Field K]
    (H : ∀ (x : Sp K ⟶ B) (c : Fin n → K),
      (∀ (g : Sp K ⟶ X) j, g ≫ π = x → ∑ i, c i * valF g _ ((b i).f j) = 0) → c = 0)
    {R : Type} [CommRing R] {χ : Sp R ⟶ B} {p : Y ⟶ Sp R} {r : Y ⟶ X} (hp : IsPullback r p π χ)
    (κ : R →+* K) (c : Fin n → R)
    (h0 : ∀ (g : Sp K ⟶ Y) (z : Sp K) j, g ≫ p = spMap κ → (g ≫ r) z ∈ M.U j →
      ∑ i, cst (g ≫ p) z (c i) * gs (g ≫ r) z (M.U j) ((b i).f j) = 0) (i : Fin n) : κ (c i) = 0 := by
  refine congrFun (H (spMap κ ≫ χ) (fun i => κ (c i)) fun g j hg => ?_) i
  obtain ⟨g', rfl, h₂⟩ : ∃ g' : Sp K ⟶ Y, g' ≫ r = g ∧ g' ≫ p = spMap κ :=
    ⟨hp.lift g (spMap κ) hg, hp.lift_fst _ _ _, hp.lift_snd _ _ _⟩
  let z : Sp K := (default : PrimeSpectrum K)
  by_cases hz : (g' ≫ r) z ∈ M.U j
  · apply (toStk z).injective
    rw [map_zero, ← h0 g' z j h₂ hz, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, toStk_valF_eq_gs _ _ z hz, toStk_eq_cst, h₂, H1.gs_spec]
  · refine Finset.sum_eq_zero fun i _ => ?_
    rw [valF, dif_neg (fun h => hz ((top_le_iff_mem _ _ z).1 h)), mul_zero]

theorem exists_comb_of_independent {F : Type} [Field F] {Y : Scheme.{0}} {M : LB Y} {p : Y ⟶ Sp F} {n : ℕ}
    (H : HasBasis M p n) (β : Fin n → LB.Sec M)
    (ind : ∀ c : Fin n → F, (∀ j, ∑ i, Out.resTop _ (Out.scal p (c i)) * (β i).f j = 0) → c = 0)
    (s : LB.Sec M) : ∃ c, IsComb p β c s := by
  obtain ⟨e, he⟩ := H
  choose m hm using fun i => (he (β i)).exists
  have key : ∀ (c : Fin n → F) j, ∑ i, Out.resTop _ (Out.scal p (c i)) * (β i).f j =
      ∑ k, Out.resTop _ (Out.scal p (Matrix.vecMul c (Matrix.of m) k)) * (e k).f j := fun c j => by
    simp only [fun i => hm i j, SaturatedSections.cst_eq, Matrix.vecMul, dotProduct, map_sum, map_mul,
      Finset.mul_sum, Finset.sum_mul, Matrix.of_apply, _root_.mul_assoc]
    exact Finset.sum_comm
  have inj : Function.Injective (Matrix.vecMulLinear (Matrix.of m)) := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    refine ind c fun j => ?_
    have hc' : Matrix.vecMul c (Matrix.of m) = 0 := hc
    rw [key, hc']
    simp only [SaturatedSections.cst_eq, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero]
  obtain ⟨d, hd, -⟩ := he s
  obtain ⟨c, hc⟩ := LinearMap.injective_iff_surjective.1 inj d
  refine ⟨c, fun j => ?_⟩
  have hc' : Matrix.vecMul c (Matrix.of m) = d := hc
  rw [key, hc']
  exact hd j

theorem existsUnique_comb {X B Y A G : Scheme.{0}} {L : LB G} (hL : L.IsLB) (q : X ⟶ G) (π : X ⟶ B) (N : ℤ)
    {n : ℕ} (b : Fin n → LB.Sec (LB.LinComb L (fun _ : Fin 1 => q) (fun _ => N)))
    (H : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ B) (c : Fin n → K),
      (∀ (g : Sp K ⟶ X) j, g ≫ π = x → ∑ i, c i * valF g _ ((b i).f j) = 0) → c = 0)
    {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] {χ : Sp W ⟶ B} {p : Y ⟶ Sp W} [Flat p]
    {r : Y ⟶ X} (hp : IsPullback r p π χ) {a : A ⟶ Sp (FractionRing W)} {ρ : A ⟶ Y}
    (hρ : IsPullback ρ a p (Out.jK W)) {q' : Y ⟶ G} (hq : r ≫ q = q') {φ : A ⟶ G} (hφ : ρ ≫ q' = φ)
    (hb : HasBasis (LB.LinComb L (fun _ : Fin 1 => φ) (fun _ => N)) a n)
    (s : Fin n → LB.Sec (LB.LinComb L (fun _ : Fin 1 => q') (fun _ => N)))
    (hs : ∀ i (Z : Scheme.{0}) (u : Z ⟶ Y) (z : Z) j, u z ∈ LB.wchart L (fun _ : Fin 1 => q') j →
      gs u z (LB.wchart L (fun _ : Fin 1 => q') j) ((s i).f j) =
        gs (u ≫ r) z (LB.wchart L (fun _ : Fin 1 => q) j) ((b i).f j))
    (t : LB.Sec (LB.LinComb L (fun _ : Fin 1 => q') (fun _ => N))) : ∃! c : Fin n → W, IsComb p s c t := by
  subst hq hφ
  refine existsUnique_comb_of_independent_special_fibre W Y p _ (DVR.linComb_isLB L hL _ _) n s
    (fun c hc i => ?_) t ?_
  · let k := IsLocalRing.ResidueField W
    let κ : W →+* AlgebraicClosure k := (algebraMap k (AlgebraicClosure k)).comp (IsLocalRing.residue W)
    have hκ : ∀ w, κ w = 0 ↔ w ∈ IsLocalRing.maximalIdeal W := fun w =>
      (map_eq_zero_iff _ (algebraMap k (AlgebraicClosure k)).injective).trans (IsLocalRing.residue_eq_zero_iff w)
    refine (hκ _).1 (map_eq_zero_of_points π b (H _) hp κ c (fun g z j hg hz => ?_) i)
    have hz' : g z ∈ LB.wchart L (fun _ : Fin 1 => r ≫ q) j :=
      Set.mem_iInter.2 fun k => Set.mem_iInter.1 hz k
    have hcl : p (g z) = IsLocalRing.closedPoint W := by
      have e : p (g z) = spMap κ z := congrArg (fun u : Sp (AlgebraicClosure k) ⟶ Sp W => u z) hg
      rw [e]
      refine PrimeSpectrum.ext (Ideal.ext fun w => ?_)
      have e₂ : z = (⊥ : PrimeSpectrum (AlgebraicClosure k)) :=
        Subsingleton.elim (α := PrimeSpectrum (AlgebraicClosure k)) _ _
      subst e₂
      exact hκ w
    have e := gs_eq_zero_of_notMem g _ z hz' _ (hc j (g z) hz' hcl)
    refine Eq.trans ?_ ((gs_comb p s c g z j hz').symm.trans e)
    exact Finset.sum_congr rfl fun i _ => congrArg _ (hs i _ g z j hz').symm
  · choose s' hs' using fun i => exists_pull_gs (s i) ρ (fun _ : Fin 1 => ρ ≫ r ≫ q) (fun _ => rfl)
    obtain ⟨t', ht'⟩ := exists_pull_gs t ρ (fun _ : Fin 1 => ρ ≫ r ≫ q) (fun _ => rfl)
    obtain ⟨c, hc⟩ := exists_comb_of_independent hb s' (fun c hc => funext fun i => by
      let κ := algebraMap (FractionRing W) (AlgebraicClosure (FractionRing W))
      refine κ.injective ((map_eq_zero_of_points π b (H _) (hρ.paste_horiz hp) κ c
        (fun g z j hg hz => ?_) i).trans (map_zero κ).symm)
      have hz' : g z ∈ LB.wchart L (fun _ : Fin 1 => ρ ≫ r ≫ q) j :=
        Set.mem_iInter.2 fun k => Set.mem_iInter.1 hz k
      have hz₂ : (g ≫ ρ) z ∈ LB.wchart L (fun _ : Fin 1 => r ≫ q) j :=
        Set.mem_iInter.2 fun k => Set.mem_iInter.1 hz k
      have e := gs_comb a s' c g z j hz'
      rw [hc j] at e
      refine Eq.trans ?_ (e.symm.trans ((gs_eq g z _ hz' _).trans ((congrArg _ (map_zero _)).trans (map_zero _))))
      refine Finset.sum_congr rfl fun i _ => congrArg _ (Eq.symm ?_)
      exact (hs' i _ g z j hz').trans ((hs i _ (g ≫ ρ) z j hz₂).trans (by rw [Category.assoc]; rfl))) t'
    obtain ⟨⟨w, hw⟩, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors W) c
    choose d hd using hd
    refine ⟨w, d, nonZeroDivisors.ne_zero hw, fun j => ?_⟩
    have : IsDominant (Out.jK W) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective W (FractionRing W))).le.trans bot_le)⟩
    have := IsSchemeTheoreticallyDominant.of_isDominant (Out.jK W)
    have : IsSchemeTheoreticallyDominant ρ := IsSchemeTheoreticallyDominant.of_isPullback hρ.flip
    have : QuasiCompact ρ := MorphismProperty.of_isPullback (P := @QuasiCompact) hρ.flip inferInstance
    refine ρ.app_injective _ (fn_ext fun y hy => ?_)
    refine (gs_pull (𝟙 _) ρ y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 _) ρ y _ hy _).symm)
    have hy' : (𝟙 A : A ⟶ A) y ∈ LB.wchart L (fun _ : Fin 1 => ρ ≫ r ≫ q) j :=
      Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
    have cc : ∀ v : W, cst ((𝟙 A ≫ ρ) ≫ p) y v = cst (𝟙 A ≫ a) y (algebraMap W (FractionRing W) v) := fun v => by
      rw [Category.assoc, hρ.w, ← Category.assoc]
      exact cst_comp _ _ y v
    refine Eq.trans ?_ (gs_comb p s d (𝟙 A ≫ ρ) y j hy).symm
    refine (gs_mul (𝟙 A ≫ ρ) y _ hy _ _).trans ?_
    refine (congrArg₂ (· * ·) (GlobalTheory.IndivisibleSection.gs_scal p (𝟙 A ≫ ρ) y _ hy w)
      ((ht' _ (𝟙 A) y j hy').symm.trans ((congrArg (gs (𝟙 A) y _) (hc j)).trans
        (gs_comb a s' c (𝟙 A) y j hy')))).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cc, cc, hd i, Algebra.smul_def, H1.cst_mul, _root_.mul_assoc]
    exact congrArg (fun v => _ * (_ * v)) (hs' i _ (𝟙 A) y j hy')

end GlobalTheory.TraitBasis

open GlobalTheory.TraitBasis in

theorem GlobalTheory.basisAlong_of_independent_fibres : Out.Laws → ∀ (Z : Scheme.{0}) (G : Over Z) [GrpObj G] (L : LB G.left) (N n : ℕ) (T : Over Z) (b : Fin n → LB.Sec (Out.LPow G L (N : ℤ) T)), L.IsLB → IsSemiAbelian G → 1 ≤ N → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ T.left) (c : Fin n → K), (∀ (g : Sp K ⟶ (T ⊗ G).left) j, g ≫ (fst T G).left = x → ∑ i, c i * valF g _ ((b i).f j) = 0) → c = 0) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (χ : Sp W ⟶ T.left) (A : Out.PolAV (Sp (FractionRing W))) (φ : A.A.left ⟶ G.left), IsGrpPullback A.A G (Out.jK W ≫ χ ≫ T.hom) φ → LBIso A.L (L.pull φ) → n = N ^ A.g → GlobalTheory.LN.BasisAlong G L N (Over.homMk χ rfl : Over.mk (χ ≫ T.hom) ⟶ T) b := by
  intro laws Z G _ L N n T b hL hG hN H W _ _ _ hW χ A φ hφ hiso hn t
  have := hW.1
  have := hG.smooth
  let T' : Over Z := Over.mk (χ ≫ T.hom)
  let h : T' ⟶ T := Over.homMk χ rfl
  have P₀ : IsPullback (snd T G).left (fst T G).left G.hom T.hom := (IsPullback.of_hasPullback T.hom G.hom).flip
  have P₁ : IsPullback (snd T' G).left (fst T' G).left G.hom (χ ≫ T.hom) :=
    (IsPullback.of_hasPullback T'.hom G.hom).flip
  have e₁ : (h ▷ G).left ≫ (snd T G).left = (snd T' G).left := congrArg CommaMorphism.left (whiskerRight_snd h G)
  have e₂ : (h ▷ G).left ≫ (fst T G).left = (fst T' G).left ≫ χ :=
    congrArg CommaMorphism.left (whiskerRight_fst h G)
  have hp : IsPullback (h ▷ G).left (fst T' G).left (fst T G).left χ :=
    IsPullback.of_right (by rw [e₁]; exact P₁) e₂ P₀
  let ρ : A.A.left ⟶ (T' ⊗ G).left := P₁.lift φ (A.A.hom ≫ Out.jK W) (hφ.1.w.trans (Category.assoc _ _ _).symm)
  have r₁ : ρ ≫ (snd T' G).left = φ := P₁.lift_fst _ _ _
  have hρ : IsPullback ρ A.A.hom (fst T' G).left (Out.jK W) :=
    IsPullback.of_right (by rw [r₁]; exact hφ.1) (P₁.lift_snd _ _ _) P₁
  have : Flat (X := (T' ⊗ G).left) (Y := Sp W) (fst T' G).left :=
    MorphismProperty.of_isPullback (P := @Flat) P₁ inferInstance
  have hb : HasBasis (LB.LinComb L (fun _ : Fin 1 => φ) (fun _ => (N : ℤ))) A.A.hom n := by
    obtain ⟨w, hw⟩ := hiso
    have i := iso_linComb ((isGen_iff w).1 hw) (fun _ : Fin 1 => 𝟙 A.A.left) (fun _ => (N : ℤ))
    simp only [Category.id_comp] at i
    rw [hn]
    exact (hasBasis_field A N laws.secBaseChange hN).of_iso (DVR.linComb_isLB L hL _ _)
      (DVR.linComb_isLB _ A.isLB _ _) i.symm
  choose s hs using fun i => exists_pull_gs (b i) (h ▷ G).left (fun _ : Fin 1 => (snd T' G).left) (fun _ => e₁)
  have main := TraitBasis.existsUnique_comb hL (snd T G).left (fst T G).left (N : ℤ) b H hp hρ e₁ r₁ hb s hs t
  let ε : W ≃+* Γ(Sp W, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of W)).symm.commRingCatIsoToRingEquiv
  have key : ∀ c : Fin n → W, IsComb (fst T' G).left s c t ↔ GlobalTheory.LN.Lin G L N h b (fun i => ε (c i)) t := fun c => by
    obtain ⟨u, hu⟩ := GenericSectionBasis.exists_comb (F := W) (fst T' G).left s c
    have ev : ∀ (z : (T' ⊗ G).left) J, Good L z J →
        sval (L := L) (φ := fun _ : Fin 1 => (snd T' G).left) (ε := fun _ => (N : ℤ)) u (𝟙 _) z J =
        ∑ i, gs (fst T' G).left z ⊤ (ε (c i)) *
          sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) (b i) (h ▷ G).left z J := by
      intro z J hJ
      have hm := hJ.mem (fun _ : Fin 1 => (snd T' G).left) (𝟙 _)
      refine (congrArg (gs (𝟙 _) z _) (hu _)).trans ((gs_comb (F := W) (fst T' G).left s c (𝟙 _) z _ hm).trans ?_)
      refine Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) ?_ ?_
      · rw [Category.id_comp]; rfl
      · refine (hs i _ (𝟙 _) z _ hm).trans ?_
        rw [sval_of (b i) (h ▷ G).left z J (fun _ => J (𝟙 _ ≫ (snd T' G).left))
          (fun _ => by rw [e₁, Category.id_comp]), Category.id_comp (h ▷ G).left]
    constructor
    · intro hc z J hJ
      refine Eq.trans ?_ (ev z J hJ)
      exact congrArg (gs (𝟙 _) z _) ((hc _).trans (hu _).symm)
    · intro hc j
      exact (sec_ext_val hL (fun y J hJ => (hc y J hJ).trans (ev y J hJ).symm) j).trans (hu j)
  obtain ⟨c, hc, hu⟩ := main
  refine ⟨fun i => ε (c i), (key c).1 hc, fun c' hc' => ?_⟩
  obtain ⟨d, rfl⟩ : ∃ d : Fin n → W, c' = fun i => ε (d i) :=
    ⟨fun i => ε.symm (c' i), funext fun i => (ε.apply_symm_apply _).symm⟩
  rw [hu d ((key d).2 hc')]
